module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowMulEqThetaWitt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsGrpPullbackGenericFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDvdBound
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.BetaBd

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem θ_σA_ev (bk : BK K) (g : ↥(GK K)) (s : bk.S) :
    Per.θ l (Per.σA (g : GQ l) (bk.ev s)) = Per.θ l (bk.ev s) := by
  obtain ⟨r, hr⟩ := bk.str.surjective (Ideal.Quotient.mk _ s)
  rw [GlobalTheory.RingBasics.θ_σA, bk.θ_ev r s hr.symm]
  apply Subtype.ext
  rw [GlobalTheory.RingIface.sigO_coe]
  change Per.σC (g : GQ l) (((r : ↥K.1) : Om l) : ℂ_[l]) = (((r : ↥K.1) : Om l) : ℂ_[l])
  rw [GlobalTheory.RingBasics.σC_coe, (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (r : ↥K.1).2]

theorem dvd_σA_ev_sub (bk : BK K) (g : ↥(GK K)) (s : bk.S) :
    bk.ev bk.E ∣ Per.σA (g : GQ l) (bk.ev s) - bk.ev s := by
  rw [← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, map_sub, θ_σA_ev, sub_self]

theorem exists_dvd_bound (u : OC l) (hu : u ≠ 0) : ∃ a : ℕ, ∀ (x y : OC l) (n : ℕ),
    x * u = (l : OC l) ^ n * y → a ≤ n → ∃ y' : OC l, x = (l : OC l) ^ (n - a) * y' := by
  have hu' : 0 < ‖(u : ℂ_[l])‖ := norm_pos_iff.2 (fun h => hu (Subtype.ext h))
  obtain ⟨a, ha⟩ : ∃ a : ℕ, ‖(l : ℂ_[l])‖ ^ a < ‖(u : ℂ_[l])‖ :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) GlobalTheory.RingBasics.norm_p_lt).eventually
      (gt_mem_nhds hu')).exists
  refine ⟨a, fun x y n h han => ?_⟩
  have hl0 : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  have hy : ‖(y : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 y.2
  have h1 : ‖(x : ℂ_[l])‖ * ‖(u : ℂ_[l])‖ = ‖(l : ℂ_[l])‖ ^ n * ‖(y : ℂ_[l])‖ := by
    have := congrArg (fun t : OC l => ‖(t : ℂ_[l])‖) h
    simpa [norm_mul, norm_pow] using this
  have hn : ‖(l : ℂ_[l])‖ ^ n = ‖(l : ℂ_[l])‖ ^ (n - a) * ‖(l : ℂ_[l])‖ ^ a := by
    rw [← pow_add, Nat.sub_add_cancel han]
  have hx : ‖(x : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ (n - a) := by
    have hpa : 0 < ‖(l : ℂ_[l])‖ ^ a := pow_pos hl0 a
    have hpn : 0 ≤ ‖(l : ℂ_[l])‖ ^ (n - a) := pow_nonneg hl0.le _
    by_contra hc
    push_neg at hc
    have : ‖(l : ℂ_[l])‖ ^ (n - a) * ‖(l : ℂ_[l])‖ ^ a < ‖(x : ℂ_[l])‖ * ‖(u : ℂ_[l])‖ :=
      mul_lt_mul'' hc ha hpn hpa.le
    have h2 : ‖(l : ℂ_[l])‖ ^ n * ‖(y : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ n := mul_le_of_le_one_right (pow_nonneg hl0.le n) hy
    linarith
  have hm := (GlobalTheory.RingBasics.mem_span_pow_OC (n - a) x).2 hx
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hm
  obtain ⟨b, hb⟩ := hm
  exact ⟨b, by rw [← hb, mul_comm]⟩

end GlobalTheory.BKLim.BetaBd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaBoundedDenominators
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinIsBetaSubOfLpowSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinIsBetaSubOfLpowSmul
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

theorem GlobalTheory.BKLim.BetaDiv.isBeta_div : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (m k n : ℕ) (β γ : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β → 1 ≤ m → n ≤ k → (∀ p q, bk.E ^ m ∣ (β - (l : bk.S) ^ n • γ) p q) → F.IsBeta m (k - n) γ := by
  intro l _ K bk N d ρ F m k n β γ hβ hm hnk hd
  have hT := GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk
  have strip : ∀ (r n : ℕ) (a : Ainf l), bk.ev bk.E ^ r ∣ (l : Ainf l) ^ n * a → bk.ev bk.E ^ r ∣ a := by
    intro r n
    induction n with
    | zero => intro a h; simpa using h
    | succ n ih =>
      intro a h
      refine ih a ((hT r).1 _ ?_)
      rw [pow_succ', mul_assoc] at h
      exact h
  have hk : (l : bk.S) ^ k = (l : bk.S) ^ n * (l : bk.S) ^ (k - n) := by
    rw [← pow_add, Nat.add_sub_cancel' hnk]
  refine ⟨fun i j => ?_, fun g i j => ?_⟩
  · have h1 := hβ.1 i j
    have h2 : bk.E ∣ (β - (l : bk.S) ^ n • γ) i j := (dvd_pow_self _ (by omega : m ≠ 0)).trans (hd i j)
    have h3 : bk.E ∣ (l : bk.S) ^ n * (γ - (l : bk.S) ^ (k - n) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j := by
      have : (l : bk.S) ^ n * (γ - (l : bk.S) ^ (k - n) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j =
          (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) i j - (β - (l : bk.S) ^ n • γ) i j := by
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hk]
        ring
      rw [this]
      exact dvd_sub h1 h2
    obtain ⟨c, hc⟩ := h3
    have h4 : bk.ev bk.E ^ 1 ∣ (l : Ainf l) ^ n * bk.ev ((γ - (l : bk.S) ^ (k - n) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) :=
      ⟨bk.ev c, by rw [pow_one, ← map_mul, ← hc, map_mul, map_pow, map_natCast]⟩
    simpa using (hT 1).2.1 _ (strip 1 n _ h4)
  · set Φ := (F.ε g).map WittVector.frobenius with hΦ
    set σ := Per.σA (g : GQ l) with hσ
    set δ := β - (l : bk.S) ^ n • γ with hδ
    have hev : ∀ p q, bk.ev bk.E ^ m ∣ (δ.map bk.ev) p q := fun p q => by
      obtain ⟨c, hc⟩ := hd p q
      exact ⟨bk.ev c, by rw [Matrix.map_apply, hc, map_mul, map_pow]⟩
    have hσE : bk.ev bk.E ∣ σ (bk.ev bk.E) := by
      have := GlobalTheory.BKLim.BetaBd.dvd_σA_ev_sub bk g bk.E
      simpa using dvd_add this (dvd_refl (bk.ev bk.E))
    have hevσ : ∀ p q, bk.ev bk.E ^ m ∣ ((δ.map bk.ev).map σ) p q := fun p q => by
      obtain ⟨c, hc⟩ := hd p q
      rw [Matrix.map_apply, Matrix.map_apply, hc, map_mul, map_mul, map_pow, map_pow]
      exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hσE m) _
    have hβeq : β = (l : bk.S) ^ n • γ + δ := by rw [hδ]; abel
    have hmap : (β.map bk.ev) = (l : Ainf l) ^ n • γ.map bk.ev + δ.map bk.ev := by
      rw [hβeq]; ext p q; simp
    have hmapσ : (β.map bk.ev).map σ = (l : Ainf l) ^ n • (γ.map bk.ev).map σ + (δ.map bk.ev).map σ := by
      rw [hmap]; ext p q; simp
    have hD := hβ.2 g i j
    rw [hmapσ, hmap] at hD
    have hsplit : (Φ * ((l : Ainf l) ^ n • (γ.map bk.ev).map σ + (δ.map bk.ev).map σ) -
        ((l : Ainf l) ^ n • γ.map bk.ev + δ.map bk.ev)) i j =
        (l : Ainf l) ^ n * (Φ * (γ.map bk.ev).map σ - γ.map bk.ev) i j +
          ((Φ * (δ.map bk.ev).map σ) i j - (δ.map bk.ev) i j) := by
      simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hsplit] at hD
    have hrest : bk.ev bk.E ^ m ∣ (Φ * (δ.map bk.ev).map σ) i j - (δ.map bk.ev) i j := by
      refine dvd_sub ?_ (hev i j)
      rw [Matrix.mul_apply]
      exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (hevσ k j) _
    exact strip m n _ ((dvd_add_left hrest).1 hD)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinIsBetaSubOfLpowSmulStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_isBeta_sub_of_lpow_smul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (m k n : ℕ) (β γ : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β → 1 ≤ m → n ≤ k → (∀ p q, bk.E ^ m ∣ (β - (l : bk.S) ^ n • γ) p q) → F.IsBeta m (k - n) γ := by
  first | (exact @GlobalTheory.BKLim.BetaDiv.isBeta_div) | (exact GlobalTheory.BKLim.BetaDiv.isBeta_div) | (intros; apply GlobalTheory.BKLim.BetaDiv.isBeta_div  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaNextCoeffThetaMem
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaNextCoeffThetaMem
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.BetaStep

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem evE_ne_zero : bk.ev bk.E ≠ 0 := fun h =>
  bk.E_ne_zero (bk.ev_injective (by rw [h, map_zero]))

theorem theta_eq_zero_iff (a : Ainf l) : Per.θ l a = 0 ↔ bk.ev bk.E ∣ a := by
  rw [← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton]

theorem dvd_of_dvd_lpow_mul (n : ℕ) (c : Ainf l) (h : bk.ev bk.E ∣ (l : Ainf l) ^ n * c) :
    bk.ev bk.E ∣ c := by
  rw [← theta_eq_zero_iff] at h ⊢
  rw [map_mul, map_pow, map_natCast] at h
  have hne : ((l : OC l)) ^ n ≠ 0 := pow_ne_zero _ (fun h0 =>
    GlobalTheory.RingBasics.p_ne_zero (p := l) (by simpa using congrArg Subtype.val h0))
  exact (mul_eq_zero.mp h).resolve_left hne

theorem pow_dvd_of_l_mul (m : ℕ) : ∀ a : Ainf l,
    bk.ev bk.E ^ m ∣ (l : Ainf l) * a → bk.ev bk.E ^ m ∣ a := by
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a h
    have h1 : bk.ev bk.E ∣ (l : Ainf l) ^ 1 * a := by
      rw [pow_one]; exact dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero m)) h
    obtain ⟨a', rfl⟩ := dvd_of_dvd_lpow_mul bk 1 a h1
    rw [pow_succ']
    apply mul_dvd_mul_left
    apply ih
    rw [pow_succ', mul_left_comm] at h
    exact (mul_dvd_mul_iff_left (evE_ne_zero bk)).mp h

theorem pow_dvd_of_lpow (i n : ℕ) (a : Ainf l) (h : bk.ev bk.E ^ i ∣ (l : Ainf l) ^ n * a) :
    bk.ev bk.E ^ i ∣ a := by
  induction n generalizing a with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply pow_dvd_of_l_mul bk i
    rw [← mul_assoc, ← pow_succ']
    exact h

end GlobalTheory.BKLim.BetaStep


open GlobalTheory.BKLim.BetaStep in
theorem GlobalTheory.BKLim.beta_step : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (g : ↥(GK K)) (w : Ainf l), Per.σA (g : GQ l) (bk.ev bk.E) = bk.ev bk.E * w → ∀ (m k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β → ∀ (i n : ℕ), i + 1 ≤ m → ∀ γ : Matrix (Fin d) (Fin d) bk.S, (∀ p q, bk.E ^ i ∣ (β - (l : bk.S) ^ n • γ) p q) → ∃ δ : Matrix (Fin d) (Fin d) bk.S, (∀ p q, bk.E ^ (i + 1) ∣ (β - (l : bk.S) ^ n • γ - bk.E ^ i • δ) p q) ∧ ∀ p q, ∃ y : OC l, Per.θ l (bk.ev (δ p q)) * (Per.θ l w ^ i - 1) = (l : OC l) ^ n * y := by
  intro l _ K bk N d ρ F g w hw m k β hβ i n him γ hγ
  haveI : IsDomain (Ainf l) := inclW_injective.isDomain (inclW l)
  choose δ hδ using hγ
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hδ
  refine ⟨Matrix.of δ, fun p q => ?_, fun p q => ?_⟩
  · simp [Matrix.sub_apply, Matrix.smul_apply, hδ]
  set P : Fin d → Fin d → Ainf l := fun a c => WittVector.frobenius (F.ε g a c) with hPdef
  set σ := Per.σA (g : GQ l)
  have hent : ∀ a b, bk.ev bk.E ^ m ∣ ∑ c, P a c * σ (bk.ev (β c b)) - bk.ev (β a b) := by
    intro a b
    have := hβ.2 g a b
    simpa [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, hPdef] using this
  have hm : 0 < m := by omega
  have hθβ : ∀ c b, Per.θ l (bk.ev (β c b)) = (l : OC l) ^ k * (if c = b then 1 else 0) := by
    intro c b
    have h2 : Per.θ l (bk.ev ((β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) c b)) = 0 :=
      (theta_eq_zero_iff bk _).2 (map_dvd bk.ev (hβ.1 c b))
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_sub, map_mul, map_pow,
      map_natCast] at h2
    rw [sub_eq_zero] at h2
    rw [h2]; split_ifs <;> simp
  have hlOC : ((l : ℕ) : OC l) ≠ 0 := fun h =>
    GlobalTheory.RingBasics.p_ne_zero (p := l) (by simpa using congrArg Subtype.val h)
  have hP : ∀ a c, Per.θ l (P a c) = if a = c then 1 else 0 := by
    intro a b
    have h := (theta_eq_zero_iff bk _).2 ((dvd_pow_self _ hm.ne').trans (hent a b))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [σ, map_sub, map_sum, map_mul, GlobalTheory.BKLim.BetaBd.θ_σA_ev, hθβ, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    rw [sub_eq_zero] at h
    have hl := pow_ne_zero k hlOC
    apply mul_right_cancel₀ hl
    rw [h]; split_ifs <;> simp

  have hβe : ∀ c b, β c b = (l : bk.S) ^ n * γ c b + bk.E ^ i * δ c b := fun c b => by
    rw [← hδ c b]; ring
  have hσE : σ (bk.ev bk.E) ^ i = bk.ev bk.E ^ i * w ^ i := by rw [hw, mul_pow]
  have hD : ∀ a b, ∑ c, P a c * σ (bk.ev (β c b)) - bk.ev (β a b) =
      (l : Ainf l) ^ n * (∑ c, P a c * σ (bk.ev (γ c b)) - bk.ev (γ a b)) +
      bk.ev bk.E ^ i * (w ^ i * ∑ c, P a c * σ (bk.ev (δ c b)) - bk.ev (δ a b)) := by
    intro a b
    have e1 : ∀ c, P a c * σ (bk.ev (β c b)) = (l : Ainf l) ^ n * (P a c * σ (bk.ev (γ c b))) +
        bk.ev bk.E ^ i * (w ^ i * (P a c * σ (bk.ev (δ c b)))) := by
      intro c
      rw [hβe]
      simp only [map_add (f := _), map_mul, map_pow, map_natCast, hσE]
      ring
    rw [Finset.sum_congr rfl (fun c _ => e1 c), Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, hβe a b]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  have hDγ : ∀ a b, bk.ev bk.E ^ i ∣ ∑ c, P a c * σ (bk.ev (γ c b)) - bk.ev (γ a b) := by
    intro a b
    apply pow_dvd_of_lpow bk i n
    have h1 : bk.ev bk.E ^ i ∣ ∑ c, P a c * σ (bk.ev (β c b)) - bk.ev (β a b) :=
      (pow_dvd_pow _ (by omega)).trans (hent a b)
    rw [hD] at h1
    exact (dvd_add_left (dvd_mul_right _ _)).1 h1
  choose η hη using hDγ
  have hX : bk.ev bk.E ∣ (l : Ainf l) ^ n * η p q +
      (w ^ i * ∑ c, P p c * σ (bk.ev (δ c q)) - bk.ev (δ p q)) := by
    have e : bk.ev bk.E ^ i * ((l : Ainf l) ^ n * η p q +
        (w ^ i * ∑ c, P p c * σ (bk.ev (δ c q)) - bk.ev (δ p q))) =
        ∑ c, P p c * σ (bk.ev (β c q)) - bk.ev (β p q) := by
      rw [hD, hη]; ring
    have h1 : bk.ev bk.E ^ i * bk.ev bk.E ∣ bk.ev bk.E ^ i * ((l : Ainf l) ^ n * η p q +
        (w ^ i * ∑ c, P p c * σ (bk.ev (δ c q)) - bk.ev (δ p q))) := by
      rw [e, ← pow_succ]
      exact (pow_dvd_pow _ him).trans (hent p q)
    exact (mul_dvd_mul_iff_left (pow_ne_zero i (evE_ne_zero bk))).1 h1
  rw [← theta_eq_zero_iff] at hX
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [σ, map_add (f := _), map_sub, map_mul, map_pow, map_natCast, map_sum, GlobalTheory.BKLim.BetaBd.θ_σA_ev, hP,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hX
  refine ⟨-Per.θ l (η p q), ?_⟩
  simp only [Matrix.of_apply]
  linear_combination hX
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaNextCoeffThetaMemStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_beta_next_coeff_theta_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (g : ↥(GK K)) (w : Ainf l), Per.σA (g : GQ l) (bk.ev bk.E) = bk.ev bk.E * w → ∀ (m k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β → ∀ (i n : ℕ), i + 1 ≤ m → ∀ γ : Matrix (Fin d) (Fin d) bk.S, (∀ p q, bk.E ^ i ∣ (β - (l : bk.S) ^ n • γ) p q) → ∃ δ : Matrix (Fin d) (Fin d) bk.S, (∀ p q, bk.E ^ (i + 1) ∣ (β - (l : bk.S) ^ n • γ - bk.E ^ i • δ) p q) ∧ ∀ p q, ∃ y : OC l, Per.θ l (bk.ev (δ p q)) * (Per.θ l w ^ i - 1) = (l : OC l) ^ n * y := by
  first | (exact @GlobalTheory.BKLim.beta_step) | (exact GlobalTheory.BKLim.beta_step) | (intros; apply GlobalTheory.BKLim.beta_step  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowDvdModEisensteinOfTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowDvdModEisensteinOfTheta
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LiftDiv

theorem dvd_mod_E : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (s : bk.S) (n : ℕ) (y : OC l), Per.θ l (bk.ev s) = (l : OC l) ^ n * y → ∃ s' t : bk.S, s = (l : bk.S) ^ n * s' + bk.E * t := by
  intro l _ K bk s n y h
  set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ s) with hr
  have hθ : Per.θ l (bk.ev s) = intToOC K r := bk.θ_ev r s (by rw [hr, RingEquiv.apply_symm_apply])
  have hC : ((((r : ↥K.1) : Om l)) : ℂ_[l]) = (l : ℂ_[l]) ^ n * ((y : OC l) : ℂ_[l]) := by
    rw [← coe_intToOC, ← hθ, h]
    push_cast
    rfl
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hnorm : ‖((r : ↥K.1) : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ n := by
    rw [← PadicComplex.norm_extends, hC, norm_mul, norm_pow, GlobalTheory.UnrWitt.norm_l_C]
    exact mul_le_of_le_one_right (by positivity) (GlobalTheory.UnrWitt.norm_OC_le y)
  set q : ↥K.1 := (r : ↥K.1) / (l : ↥K.1) ^ n with hq
  have hqO : ((q : ↥K.1) : Om l) = ((r : ↥K.1) : Om l) / (l : Om l) ^ n := by
    rw [hq]; push_cast; rfl
  have hq1 : ‖((q : ↥K.1) : Om l)‖ ≤ 1 := by
    rw [hqO, norm_div, norm_pow, GlobalTheory.UnrWitt.norm_l_Om]
    rw [div_le_one (by positivity)]
    exact hnorm
  let r' : ↥(OL K) := ⟨q, GlobalTheory.UnrWitt.mem_OL_of_norm_le K q hq1⟩
  have hrr : r = (l : ↥(OL K)) ^ n * r' := by
    apply Subtype.ext
    apply Subtype.ext
    have : ((((l : ↥(OL K)) ^ n * r' : ↥(OL K)) : ↥K.1) : Om l) = (l : Om l) ^ n * ((q : ↥K.1) : Om l) := by
      push_cast; rfl
    rw [this, hqO, mul_div_cancel₀ _ (pow_ne_zero _ hl0)]
  obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective (bk.str r')
  have hmk : Ideal.Quotient.mk (Ideal.span {bk.E}) (s - (l : bk.S) ^ n * s') = 0 := by
    have e1 : Ideal.Quotient.mk (Ideal.span {bk.E}) s = bk.str r := by
      rw [hr, RingEquiv.apply_symm_apply]
    rw [map_sub, map_mul, map_pow, map_natCast, e1, hs', hrr, map_mul, map_pow, map_natCast, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hmk)
  exact ⟨s', t, by rw [mul_comm bk.E t, ht]; ring⟩

end GlobalTheory.LiftDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowDvdModEisensteinOfThetaStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primePow_dvd_mod_eisenstein_of_theta : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (s : bk.S) (n : ℕ) (y : OC l), Per.θ l (bk.ev s) = (l : OC l) ^ n * y → ∃ s' t : bk.S, s = (l : bk.S) ^ n * s' + bk.E * t := by
  first | exact @GlobalTheory.LiftDiv.dvd_mod_E | exact GlobalTheory.LiftDiv.dvd_mod_E | (intros; apply GlobalTheory.LiftDiv.dvd_mod_E; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaBoundedDenominators
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.BetaBd

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {N d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}

theorem isBeta_scale {bk : BK K} (F : Frame bk N d ρ) {m k : ℕ} {β : Matrix (Fin d) (Fin d) bk.S}
    (hβ : F.IsBeta m k β) (j : ℕ) : F.IsBeta m (k + j) ((l : bk.S) ^ j • β) := by
  refine ⟨fun p q => ?_, fun g p q => ?_⟩
  · have : ((l : bk.S) ^ j • β - (l : bk.S) ^ (k + j) • (1 : Matrix (Fin d) (Fin d) bk.S)) p q =
        (l : bk.S) ^ j * (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) p q := by
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, pow_add]; ring
    rw [this]; exact dvd_mul_of_dvd_right (hβ.1 p q) _
  · have h2 : ((l : bk.S) ^ j • β).map bk.ev = (l : Ainf l) ^ j • β.map bk.ev := by
      ext p q; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    have h1 : (((l : bk.S) ^ j • β).map bk.ev).map (Per.σA (g : GQ l)) =
        (l : Ainf l) ^ j • (β.map bk.ev).map (Per.σA (g : GQ l)) := by
      rw [h2]; ext p q; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    rw [h1, h2, Matrix.mul_smul, ← smul_sub, Matrix.smul_apply, smul_eq_mul]
    exact dvd_mul_of_dvd_right (hβ.2 g p q) _

end GlobalTheory.BKLim.BetaBd


open GlobalTheory.BKLim.BetaBd in
theorem GlobalTheory.BKLim.beta_bdd_denominators : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), ∃ c : ℕ, ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (k : ℕ) (β : Matrix (Fin d) (Fin d) (bk.S)), F.IsBeta m k β → ∃ β', F.IsBeta m c β' := by
  intro l _ K bk m
  obtain ⟨g, z, ⟨w, hw, hzw⟩, hz⟩ := GlobalTheory.T.exists_galois_elem_cyclotomic_period_not_root_of_unity l K bk
  have hu : ∀ i, 1 ≤ i → Per.θ l w ^ i - 1 ≠ 0 := by
    intro i hi h
    apply hz i hi
    have h1 : ((Per.θ l w : OC l) : ℂ_[l]) ^ i = 1 := by
      have := congrArg (fun t : OC l => (t : ℂ_[l])) (sub_eq_zero.1 h)
      simpa using this
    rw [(thetaD_props l).2.2.2.1 w] at hzw
    calc z ^ i = z ^ i * ((Per.θ l w : ℂ_[l]) ^ i) := by rw [h1, mul_one]
      _ = (z * (Per.θ l w : ℂ_[l])) ^ i := (mul_pow _ _ _).symm
      _ = 1 := by rw [hzw, one_pow]
  choose a ha using fun i : {i : ℕ // 1 ≤ i} => exists_dvd_bound _ (hu i.1 i.2)
  let A : ℕ → ℕ := fun i => if h : 1 ≤ i then a ⟨i, h⟩ else 0
  let S : ℕ → ℕ := fun i => ∑ j ∈ Finset.range i, A j
  have hSs : ∀ i, S (i + 1) = S i + A i := fun i => Finset.sum_range_succ _ _
  have hSm : ∀ i j, i ≤ j → S i ≤ S j := fun i j h =>
    Finset.sum_le_sum_of_subset (Finset.range_mono h)
  refine ⟨S m, fun N d ρ F k β hβ => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨(l : bk.S) ^ S 0 • 1, fun p q => by simp, fun g p q => by simp⟩
  by_cases hk : k < S m
  · refine ⟨(l : bk.S) ^ (S m - k) • β, ?_⟩
    have := isBeta_scale F hβ (S m - k)
    rwa [Nat.add_sub_cancel' hk.le] at this
  push_neg at hk
  have key : ∀ i, 1 ≤ i → i ≤ m → ∃ γ : Matrix (Fin d) (Fin d) bk.S,
      ∀ p q, bk.E ^ i ∣ (β - (l : bk.S) ^ (k - S i) • γ) p q := by
    intro i
    induction i with
    | zero => intro h; omega
    | succ i ih =>
      intro _ him
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · refine ⟨(l : bk.S) ^ S 1 • 1, fun p q => ?_⟩
        have hS : S 1 ≤ k := le_trans (hSm 1 m him) hk
        rw [smul_smul, ← pow_add, Nat.sub_add_cancel hS, pow_one]
        exact hβ.1 p q
      · obtain ⟨γ, hγ⟩ := ih hi0 (by omega)
        obtain ⟨δ, hδ1, hδ2⟩ := GlobalTheory.T.breuilKisin_beta_next_coeff_theta_mem l K bk N d ρ F g w hw m k β hβ i (k - S i) him γ hγ
        have hAi : A i = a ⟨i, hi0⟩ := dif_pos hi0
        have hS1 : S (i + 1) ≤ k := le_trans (hSm _ _ him) hk
        have hle : a ⟨i, hi0⟩ ≤ k - S i := by rw [hSs] at hS1; omega
        have hexp : k - S i - a ⟨i, hi0⟩ = k - S (i + 1) := by rw [hSs, hAi]; omega
        have hlift : ∀ p q, ∃ s' t : bk.S, δ p q = (l : bk.S) ^ (k - S (i + 1)) * s' + bk.E * t := by
          intro p q
          obtain ⟨y, hy⟩ := hδ2 p q
          obtain ⟨y', hy'⟩ := ha ⟨i, hi0⟩ _ y _ hy hle
          rw [hexp] at hy'
          exact GlobalTheory.T.exists_primePow_dvd_mod_eisenstein_of_theta l K bk _ _ y' hy'
        choose δ' t ht using hlift
        refine ⟨(l : bk.S) ^ A i • γ + bk.E ^ i • Matrix.of δ', fun p q => ?_⟩
        have hpow : (l : bk.S) ^ (k - S (i + 1)) * (l : bk.S) ^ A i = (l : bk.S) ^ (k - S i) := by
          rw [← pow_add]; congr 1; rw [hSs] at hS1 ⊢; omega
        have e : (β - (l : bk.S) ^ (k - S (i + 1)) • ((l : bk.S) ^ A i • γ + bk.E ^ i • Matrix.of δ')) p q =
            (β - (l : bk.S) ^ (k - S i) • γ - bk.E ^ i • δ) p q + bk.E ^ (i + 1) * t p q := by
          simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
          linear_combination (bk.E ^ i) * ht p q - γ p q * hpow
        rw [e]
        exact dvd_add (hδ1 p q) (dvd_mul_right _ _)
  obtain ⟨γ, hγ⟩ := key m hm le_rfl
  refine ⟨γ, ?_⟩
  have := GlobalTheory.T.breuilKisin_isBeta_sub_of_lpow_smul l K bk N d ρ F m k (k - S m) β γ hβ hm (Nat.sub_le k (S m)) hγ
  rwa [Nat.sub_sub_self hk] at this

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaBoundedDenominatorsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_beta_bounded_denominators : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), ∃ c : ℕ, ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (k : ℕ) (β : Matrix (Fin d) (Fin d) (bk.S)), F.IsBeta m k β → ∃ β', F.IsBeta m c β' := by
  first | (exact @GlobalTheory.BKLim.beta_bdd_denominators) | (exact GlobalTheory.BKLim.beta_bdd_denominators) | (intros; apply GlobalTheory.BKLim.beta_bdd_denominators  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinQuotientEisensteinCompactness
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinQuotientEisensteinCompactness
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.Cpt

theorem of_add {R : Type} (Q : ℕ → R → Prop) (hmono : ∀ n x, Q (n + 1) x → Q n x) :
    ∀ n k x, Q (n + k) x → Q n x := by
  intro n k x
  induction k with
  | zero => exact id
  | succ k ih => exact fun h => ih (hmono _ _ (by rwa [← add_assoc] at h))

def Good {R : Type} [CommRing R] {ι : Type} (I : ℕ → Ideal R) (Q : ℕ → (ι → R) → Prop) (n : ℕ) (y : ι → R) :
    Prop :=
  ∀ k, n ≤ k → ∃ x, Q k x ∧ ∀ i, x i - y i ∈ I n

theorem exists_seq {R : Type} [CommRing R] (I : ℕ → Ideal R) (hI : ∀ n, I (n + 1) ≤ I n) (hI0 : I 0 = ⊤)
    (hfin : ∀ n, Finite (R ⧸ I n)) (ι : Type) [Finite ι] (Q : ℕ → (ι → R) → Prop)
    (hmono : ∀ n x, Q (n + 1) x → Q n x) (hcong : ∀ n x y, Q n x → (∀ i, x i - y i ∈ I n) → Q n y)
    (hex : ∀ n, ∃ x, Q n x) :
    ∃ y : ℕ → ι → R, (∀ n, Q n (y n)) ∧ ∀ n i, y (n + 1) i - y n i ∈ I n := by
  classical
  have step : ∀ n y, Good I Q n y → ∃ y', Good I Q (n + 1) y' ∧ ∀ i, y' i - y i ∈ I n := by
    intro n y hy
    by_contra hne
    haveI : Finite (ι → R ⧸ I (n + 1)) := by haveI := hfin (n + 1); infer_instance
    let rep : (ι → R ⧸ I (n + 1)) → ι → R := fun t i => Classical.choose (Ideal.Quotient.mk_surjective (t i))
    have hrep : ∀ t i, Ideal.Quotient.mk (I (n + 1)) (rep t i) = t i :=
      fun t i => Classical.choose_spec (Ideal.Quotient.mk_surjective (t i))
    let P : (ι → R ⧸ I (n + 1)) → Prop := fun t =>
      ∃ k, n + 1 ≤ k ∧ ¬ ∃ x, Q k x ∧ ∀ i, x i - rep t i ∈ I (n + 1)
    let kf : (ι → R ⧸ I (n + 1)) → ℕ := fun t => if h : P t then h.choose else 0
    have hkf : ∀ t (h : P t), kf t = h.choose := fun t h => dif_pos h
    obtain ⟨t0, ht0⟩ := Finite.exists_max kf
    obtain ⟨x, hx, hxy⟩ := hy (n + kf t0) (Nat.le_add_right _ _)
    let t : ι → R ⧸ I (n + 1) := fun i => Ideal.Quotient.mk _ (x i)
    have hxt : ∀ i, x i - rep t i ∈ I (n + 1) := fun i =>
      Ideal.Quotient.eq.1 (hrep t i).symm
    have hty : ∀ i, rep t i - y i ∈ I n := fun i => by
      have : rep t i - y i = (x i - y i) - (x i - rep t i) := by ring
      rw [this]
      exact sub_mem (hxy i) (hI n (hxt i))
    have hng : ¬ Good I Q (n + 1) (rep t) := fun hg => hne ⟨rep t, hg, hty⟩
    have hP : P t := by
      by_contra hc
      refine hng fun k hk => ?_
      by_contra hk'
      exact hc ⟨k, hk, hk'⟩
    have hs := hP.choose_spec
    rw [← hkf t hP] at hs
    refine hs.2 ⟨x, ?_, hxt⟩
    have hle : kf t ≤ n + kf t0 := (ht0 t).trans (Nat.le_add_left _ _)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    exact of_add Q hmono (kf t) d x (hd ▸ hx)
  choose! f hf1 hf2 using step
  let seq : ℕ → ι → R := fun n => Nat.rec (motive := fun _ => ι → R) 0 (fun n y => f n y) n
  have hgood : ∀ n, Good I Q n (seq n) := by
    intro n
    induction n with
    | zero =>
      intro k _
      obtain ⟨x, hx⟩ := hex k
      exact ⟨x, hx, fun i => by rw [hI0]; exact Submodule.mem_top⟩
    | succ n ih => exact hf1 n (seq n) ih
  refine ⟨seq, fun n => ?_, fun n i => hf2 n (seq n) (hgood n) i⟩
  obtain ⟨x, hx, hxs⟩ := hgood n n le_rfl
  exact hcong n x (seq n) hx hxs

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem X_pow_mem (bk : BK K) (n m : ℕ) :
    (X : bk.S) ^ (bk.Ep.natDegree * (n + m)) ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m} := by
  have h1 : (X : bk.S) ^ (bk.Ep.natDegree * (n + m)) ∈
      (Ideal.span {(l : bk.S)} ⊔ Ideal.span {bk.E}) ^ (n + m) := by
    rw [pow_mul]; exact Ideal.pow_mem_pow (BK.X_pow_natDegree_mem bk) _
  have h2 := Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {(l : bk.S)}) (J := Ideal.span {bk.E})
    (n := n) (m := m)
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h2
  exact h2 h1

theorem finite_quot (bk : BK K) (n m : ℕ) :
    Finite (bk.S ⧸ (Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m})) := by
  haveI := GlobalTheory.T.finite_breuilKisin_quotient_prime_pow_X_pow l K bk n (bk.Ep.natDegree * (n + m))
  have H : Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {(X : bk.S) ^ (bk.Ep.natDegree * (n + m))} ≤
      Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m} :=
    sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 (X_pow_mem bk n m))
  refine Finite.of_surjective (Ideal.Quotient.factor H) fun y => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ x, rfl⟩

theorem exists_lim (bk : BK K) (m : ℕ) (s : ℕ → bk.S)
    (hs : ∀ n, s (n + 1) - s n ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m}) :
    ∃ L : bk.S, ∀ n, s (n + m) - L ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m} := by
  have hd : ∀ n, ∃ a b : bk.S, s (n + 1) - s n = (l : bk.S) ^ n * a + bk.E ^ m * b := by
    intro n
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hs n)
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    exact ⟨a, b, by rw [← hyz]; ring⟩
  choose a b hab using hd
  let z : ℕ → bk.S := fun n => s n - bk.E ^ m * ∑ k ∈ Finset.range n, b k
  have hz1 : ∀ n, z (n + 1) - z n = (l : bk.S) ^ n * a n := by
    intro n
    simp only [z, Finset.sum_range_succ]
    linear_combination hab n
  have hcau : ∀ n N, n ≤ N → z N - z n ∈ Ideal.span {(l : bk.S) ^ n} := by
    intro n N hN
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ N hN ih =>
      have : z (N + 1) - z n = (z (N + 1) - z N) + (z N - z n) := by ring
      rw [this, hz1]
      exact add_mem (Ideal.mem_span_singleton.2 (dvd_mul_of_dvd_left (pow_dvd_pow _ hN) _)) ih
  have hJ : ∀ n, Ideal.span {(l : bk.S) ^ n} ≤ bk.J ^ n := fun n => by
    rw [← Ideal.span_singleton_pow]; exact Ideal.pow_right_mono le_sup_left n
  obtain ⟨L, hL⟩ := bk.complete.toIsPrecomplete.prec (f := z) (fun {p q} hpq => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub]
    exact neg_mem (hJ p (hcau p q hpq)))
  refine ⟨L, fun n => ?_⟩
  have h1 := hL (n + m)
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {(l : bk.S)}) (J := Ideal.span {bk.E})
    (n := n) (m := m)
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h2
  have : s (n + m) - L = (z (n + m) - L) + bk.E ^ m * ∑ k ∈ Finset.range (n + m), b k := by
    simp only [z]; ring
  rw [this]
  exact add_mem (h2 h1) (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

theorem compact : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type) [Finite ι] (m : ℕ)
    (Q : ℕ → (ι → bk.S) → Prop), (∀ n x, Q (n + 1) x → Q n x) →
    (∀ n x y, Q n x → (∀ i, x i - y i ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m}) → Q n y) →
    (∀ n, ∃ x, Q n x) → ∃ x, ∀ n, Q n x := by
  intro l _ K bk ι _ m Q hmono hcong hex
  obtain ⟨y, hQ, hy⟩ := exists_seq (fun n => Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m})
    (fun n => sup_le_sup_right (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ n))) _)
    (by simp) (fun n => finite_quot bk n m) ι Q hmono hcong hex
  choose L hL using fun i => exists_lim bk m (fun n => y n i) (fun n => hy n i)
  exact ⟨L, fun n => hcong n _ _ (of_add Q hmono n m _ (hQ (n + m))) (fun i => hL i n)⟩

end GlobalTheory.BKLim.Cpt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinQuotientEisensteinCompactnessStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_quotient_eisenstein_compactness : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type) [Finite ι] (m : ℕ) (Q : ℕ → (ι → bk.S) → Prop), (∀ n x, Q (n + 1) x → Q n x) → (∀ n x y, Q n x → (∀ i, x i - y i ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m}) → Q n y) → (∀ n, ∃ x, Q n x) → ∃ x, ∀ n, Q n x := by
  first | (exact @GlobalTheory.BKLim.Cpt.compact) | (exact GlobalTheory.BKLim.Cpt.compact) | (intros; apply GlobalTheory.BKLim.Cpt.compact  <;> assumption)
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.DRLim

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

private theorem hom_frobenius_pt {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p]
    (f : WittVector p R →+* WittVector p R) (x : WittVector p R) :
    f (WittVector.frobenius x) = WittVector.frobenius (f x) := by
  have h1 : ∀ z : WittVector p R, (p : WittVector p R) ∣ WittVector.frobenius z - z ^ p := by
    intro z
    rw [← Ideal.mem_span_singleton, WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    have : WittVector.constantCoeff (WittVector.frobenius z - z ^ p) = 0 := by
      rw [map_sub, map_pow, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
        WittVector.coeff_frobenius_charP, sub_self]
    exact this
  have h2 : ∀ y : R, WittVector.frobenius (WittVector.teichmuller p y) = WittVector.teichmuller p y ^ p := by
    intro y
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  have h3 : ∀ n : ℕ, f (WittVector.frobenius x) - WittVector.frobenius (f x) ∈
      Ideal.span {(p : WittVector p R) ^ n} := by
    intro n
    have hnil : IsNilpotent ((p : ℕ) : WittVector p R ⧸ Ideal.span {(p : WittVector p R) ^ n}) := by
      refine ⟨n, ?_⟩
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : WittVector p R) ^ n})), ← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    have := WittVector.eq_of_apply_teichmuller_eq
      ((Ideal.Quotient.mk (Ideal.span {(p : WittVector p R) ^ n})).comp (f.comp WittVector.frobenius))
      ((Ideal.Quotient.mk (Ideal.span {(p : WittVector p R) ^ n})).comp (WittVector.frobenius.comp f)) hnil (by
        intro y
        obtain ⟨w, rfl⟩ := (iterateFrobeniusEquiv R p n).surjective y
        simp only [RingHom.comp_apply]
        rw [eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton, h2, iterateFrobeniusEquiv_def]
        simp only [map_pow]
        rw [pow_right_comm]
        exact (pow_dvd_pow _ (Nat.le_succ n)).trans (dvd_sub_pow_of_dvd_sub (h1 _) n))
    exact Ideal.Quotient.eq.1 (RingHom.congr_fun this x)
  rw [← sub_eq_zero]
  refine WittVector.ext fun n => ?_
  rw [WittVector.zero_coeff]
  exact (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero _ (n + 1)).1 (h3 _) n (Nat.lt_succ_self n)

theorem σA_frob (g : GQ l) (x : Ainf l) :
    Per.σA g (WittVector.frobenius x) = WittVector.frobenius (Per.σA g x) :=
  hom_frobenius_pt (Per.σA g) x

theorem map_mk_eq_zero {R : Type} [CommRing R] {m n : Type} (I : Ideal R) (M : Matrix m n R) :
    M.map (Ideal.Quotient.mk I) = 0 ↔ ∀ i j, M i j ∈ I := by
  rw [← Matrix.ext_iff]
  simp only [Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem]

theorem msub {R B : Type} [CommRing R] [CommRing B] {m n : Type} (f : R →+* B) (M M' : Matrix m n R) :
    (M - M').map f = M.map f - M'.map f := Matrix.map_sub _ (map_sub f) _ _

theorem map_smul_one {R B : Type} [CommRing R] [CommRing B] {n : Type} [DecidableEq n] (f : R →+* B) (a : R) :
    (a • (1 : Matrix n n R)).map f = f a • (1 : Matrix n n B) := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, Matrix.map_apply, Matrix.smul_apply, h]

theorem exists_of_mem_sup {R : Type} [CommRing R] {a b x : R} (h : x ∈ Ideal.span {a} ⊔ Ideal.span {b}) :
    ∃ u v, x = b * u + a * v := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 h
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  exact ⟨z, y, by ring⟩

theorem σA_mem (bk : BK K) (g : GQ l) (n M : ℕ) (a : Ainf l)
    (ha : a ∈ Ideal.span {(l : Ainf l) ^ n} ⊔ Ideal.span {bk.ev bk.E ^ M}) :
    Per.σA g a ∈ Ideal.span {(l : Ainf l) ^ n} ⊔ Ideal.span {bk.ev bk.E ^ M} := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 ha
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  have hE : bk.ev bk.E ∣ Per.σA g (bk.ev bk.E) := by
    rw [← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA]
    have : Per.θ l (bk.ev bk.E) = 0 := by
      rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
    rw [this, map_zero]
  obtain ⟨w, hw⟩ := hE
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, map_natCast, hw, mul_pow]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton'.2 ⟨_, rfl⟩)) (Ideal.mem_sup_right ?_)
  exact Ideal.mem_span_singleton.2 ⟨Per.σA g z * w ^ M, by ring⟩

theorem ev_mem (bk : BK K) (n M : ℕ) (s : bk.S) (hs : s ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ M}) :
    bk.ev s ∈ Ideal.span {(l : Ainf l) ^ n} ⊔ Ideal.span {bk.ev bk.E ^ M} := by
  have := Ideal.mem_map_of_mem bk.ev hs
  rwa [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_pow, map_pow,
    map_natCast] at this

end GlobalTheory.BKLim.DRLim


open GlobalTheory.BKLim.DRLim in
theorem GlobalTheory.BKLim.isDR_of_links : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (F₀ : Frame bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r) → (∀ n, (F n).IsDR) → F₀.IsDR := by
  intro l _ K bk d N ρ tw F F₀ r hlink hDR M
  obtain ⟨c, hc⟩ := GlobalTheory.T.breuilKisin_beta_bounded_denominators l K bk (M + 1)
  obtain ⟨k₀, hk₀⟩ := GlobalTheory.T.exists_invariant_lift_mod_E l K bk (M + 1)
  choose γf hγ1 hγ2 using hk₀
  have htf1 := GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk 1
  have htfM := GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk (M + 1)
  let Xm : (Fin d × Fin d → bk.S) → Matrix (Fin d) (Fin d) bk.S := fun x => Matrix.of fun i j => x (i, j)
  let I₁ : ℕ → Ideal bk.S := fun n => Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ 1}
  let J : ℕ → Ideal (Ainf l) := fun n => Ideal.span {(l : Ainf l) ^ n} ⊔ Ideal.span {bk.ev bk.E ^ (M + 1)}
  let Φ : ↥(GK K) → Matrix (Fin d) (Fin d) bk.S → Matrix (Fin d) (Fin d) (Ainf l) := fun g β =>
    (F₀.ε g).map WittVector.frobenius * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev
  let Q : ℕ → (Fin d × Fin d → bk.S) → Prop := fun n x =>
    (∀ i j, (Xm x - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j ∈ I₁ n) ∧
      ∀ g i j, Φ g (Xm x) i j ∈ J n
  have hmono : ∀ n x, Q (n + 1) x → Q n x := by
    intro n x ⟨h1, h2⟩
    have hl : ∀ {R : Type} [CommRing R] (y : R), Ideal.span {(l : R) ^ (n + 1)} ≤ Ideal.span {(l : R) ^ n} :=
      fun _ => Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ n))
    exact ⟨fun i j => sup_le_sup_right (hl (0 : bk.S)) _ (h1 i j),
      fun g i j => sup_le_sup_right (hl (0 : Ainf l)) _ (h2 g i j)⟩
  have hpert : ∀ n x y, Q n x → (∀ i, x i - y i ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ (M + 1)}) →
      Q n y := by
    intro n x y ⟨h1, h2⟩ hd
    have hle : Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ (M + 1)} ≤ I₁ n :=
      sup_le_sup_left (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (by omega))) _
    have hD : ∀ i j, (Xm x - Xm y) i j ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ (M + 1)} :=
      fun i j => hd (i, j)
    refine ⟨fun i j => ?_, fun g i j => ?_⟩
    · have e : (Xm y - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j =
          (Xm x - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j - (Xm x - Xm y) i j := by
        simp only [Matrix.sub_apply]; ring
      rw [e]
      exact sub_mem (h1 i j) (hle (hD i j))
    · have e : Φ g (Xm y) = Φ g (Xm x) - ((F₀.ε g).map WittVector.frobenius *
          ((Xm x - Xm y).map bk.ev).map (Per.σA (g : GQ l)) - (Xm x - Xm y).map bk.ev) := by
        simp only [Φ, msub, Matrix.mul_sub]; abel
      rw [e, Matrix.sub_apply, Matrix.sub_apply, Matrix.mul_apply]
      refine sub_mem (h2 g i j) (sub_mem (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ ?_) ?_)
      · exact σA_mem bk _ n (M + 1) _ (ev_mem bk n (M + 1) _ (hD k j))
      · exact ev_mem bk n (M + 1) _ (hD i j)
  have hex : ∀ n, ∃ x, Q n x := by
    intro n
    obtain ⟨m, hnm, R, G, hRT, hRG⟩ := hlink n
    obtain ⟨k', β'', hβ''⟩ := hDR m (M + 1)
    obtain ⟨β', hβ'⟩ := hc N (tw.d' m) _ (F m) k' β'' hβ''
    have hrel := GlobalTheory.T.breuilKisinLatticeFrame_cocycles_linked l K bk N N d (tw.d' m) n (fun g => (ρ g).val) (fun g => (tw.ρ' m g).val) F₀ (F m)
      (tw.Pi m) R (fun g i j => (pow_dvd_pow _ hnm).trans ((tw.onto m).equi g i j)) hRT
    let φS := frobS l bk.a
    let γ : Matrix (Fin (tw.d' m)) (Fin d) bk.S := Matrix.of fun i j => γf (φS (G i j))
    let Mx : Matrix (Fin d) (Fin d) bk.S := R.map φS * β' * γ
    refine ⟨fun ij => Mx ij.1 ij.2, ?_, ?_⟩
    ·
      let q := Ideal.Quotient.mk (I₁ n)
      have hE : ∀ s : bk.S, bk.E ∣ s → q s = 0 := fun s hs =>
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton.2 (by simpa using hs)))
      have hL : ∀ s : bk.S, (l : bk.S) ^ n ∣ s → q s = 0 := fun s hs =>
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_span_singleton.2 hs))
      have hq1 : β'.map q = q ((l : bk.S) ^ c) • (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) _) := by
        have : (β' - (l : bk.S) ^ c • (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) bk.S)).map q = 0 := by
          ext i j; exact hE _ (hβ'.1 i j)
        rwa [msub, map_smul_one, sub_eq_zero] at this
      have hq2 : γ.map q = q ((l : bk.S) ^ k₀) • (G.map φS).map q := by
        ext i j
        simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.of_apply, γ, smul_eq_mul, ← map_mul]
        exact (Ideal.Quotient.eq.2 (Ideal.Quotient.eq_zero_iff_mem.1 (hE _ (hγ1 _))))
      have hq3 : (R.map φS).map q * (G.map φS).map q = q ((l : bk.S) ^ r) • (1 : Matrix (Fin d) (Fin d) _) := by
        have : (R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) bk.S)).map (q.comp φS) = 0 := by
          ext i j
          refine hL _ ?_
          have := map_dvd φS (hRG i j)
          simpa [φS, map_pow, map_natCast] using this
        rw [msub, Matrix.map_mul, map_smul_one, sub_eq_zero, RingHom.coe_comp, ← Matrix.map_map, ← Matrix.map_map,
          Function.comp_apply, map_pow, map_natCast] at this
        rw [this, map_pow, map_natCast]
      refine (map_mk_eq_zero (I₁ n) _).1 ?_
      show (Mx - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)).map q = 0
      rw [msub, map_smul_one, Matrix.map_mul, Matrix.map_mul, hq1, hq2]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
      rw [hq3, smul_smul, sub_eq_zero]
      congr 1
      simp only [← map_mul, ← pow_add]
      ring_nf
    · intro g
      refine (map_mk_eq_zero (J n) _).1 ?_
      let p := Ideal.Quotient.mk (J n)
      show (Φ g Mx).map p = 0
      have hp1 : ((F₀.ε g).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p * (((R.map bk.ev).map (Per.σA (g : GQ l))).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p =
          ((R.map bk.ev).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p * (((F m).ε g).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p := by
        have h : (((F₀.ε g * (R.map bk.ev).map (Per.σA (g : GQ l)) - R.map bk.ev * (F m).ε g)).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p = 0 := by
          ext i j
          simp only [Matrix.map_apply, Matrix.zero_apply]
          refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_span_singleton.2 ?_))
          simpa [map_pow, map_natCast] using map_dvd (WittVector.frobenius : Ainf l →+* Ainf l) (hrel g i j)
        simpa only [msub, Matrix.map_mul, sub_eq_zero] using h
      have hp2 : (((F m).ε g).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p * ((β'.map bk.ev).map (Per.σA (g : GQ l))).map p = (β'.map bk.ev).map p := by
        have h : ((((F m).ε g).map (WittVector.frobenius : Ainf l →+* Ainf l) * (β'.map bk.ev).map (Per.σA (g : GQ l)) - β'.map bk.ev)).map p = 0 := by
          ext i j
          simp only [Matrix.map_apply, Matrix.zero_apply]
          exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton.2 (hβ'.2 g i j)))
        simpa only [msub, Matrix.map_mul, sub_eq_zero] using h
      have hp3 : ((γ.map bk.ev).map (Per.σA (g : GQ l))).map p = (γ.map bk.ev).map p := by
        ext i j
        simp only [Matrix.map_apply, Matrix.of_apply, γ]
        exact Ideal.Quotient.eq.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton.2 (hγ2 _ g)))
      have hRev : (R.map φS).map bk.ev = (R.map bk.ev).map (WittVector.frobenius : Ainf l →+* Ainf l) := by
        exact Matrix.ext fun i j => bk.ev_frob _
      have hRσ : ((R.map bk.ev).map (WittVector.frobenius : Ainf l →+* Ainf l)).map (Per.σA (g : GQ l)) = ((R.map bk.ev).map (Per.σA (g : GQ l))).map (WittVector.frobenius : Ainf l →+* Ainf l) := by
        exact Matrix.ext fun i j => σA_frob _ _
      simp only [Φ, Mx, msub, Matrix.map_mul]
      rw [hRev, hRσ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hp1, Matrix.mul_assoc _ ((((F m).ε g).map (WittVector.frobenius : Ainf l →+* Ainf l)).map p), hp2, hp3, sub_self]
  obtain ⟨x, hx⟩ := GlobalTheory.T.breuilKisin_quotient_eisenstein_compactness l K bk (Fin d × Fin d) (M + 1) Q hmono hpert hex
  refine ⟨c + k₀ + r, Xm x, fun i j => ?_, fun g i j => ?_⟩
  · have h4 := htf1.2.2.2 (bk.ev ((Xm x - (l : bk.S) ^ (c + k₀ + r) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j))
      (fun n => exists_of_mem_sup (ev_mem bk n 1 _ ((hx n).1 i j)))
    simpa using htf1.2.1 _ h4
  · have h4 := htfM.2.2.2 (Φ g (Xm x) i j) (fun n => exists_of_mem_sup ((hx n).2 g i j))
    exact (pow_dvd_pow _ (Nat.le_succ M)).trans h4
