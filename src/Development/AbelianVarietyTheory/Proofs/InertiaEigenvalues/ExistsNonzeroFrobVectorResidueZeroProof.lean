module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisPlusSeriesWithThetaResidues
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesLinearIndependentOfFirstTer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPolydiscWindowsSurjectiveBoundsZero
public import GroundTheory.PAdicHodge.TiltField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReductionTeichmullerEmbeddingAtLocalisatio

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroFrobVectorResidueZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOrthogonalFamilyResidueZeros
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltedSeriesRowSubUntiltTruncatedAdditiveRow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUntiltExtensionFinsetSumSubLe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUntiltExtensionFinsetSumSubLe
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem untilt_ext_sum_sub_le : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] (ι : Fl l →+* F)
    (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (α : Type) (s : Finset α) (z : α → F) (R : ℝ), 0 ≤ R → (∀ a ∈ s, ‖z a‖ ≤ R) →
      ‖tsh (∑ a ∈ s, z a) - ∑ a ∈ s, tsh (z a)‖ ≤ ‖(l : ℂ_[l])‖ * R := by
  intro l _ F _ ι tsh hn hι hsurj α s z R hR hz
  classical
  obtain ⟨-, -, -, -, -, hon, -, -⟩ := GlobalTheory.PSer.Laws.sh_laws l
  have hl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := GlobalTheory.PSer.Laws.norm_l
  have hlpos : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := by rw [hl]; exact inv_lt_one_of_one_lt₀ hlpos
  have hl0 : 0 < ‖(l : ℂ_[l])‖ := by rw [hl]; exact inv_pos.2 (by linarith)
  obtain ⟨w, hw⟩ := hon (l : ℂ_[l]) hl1.le
  have hnw : ‖ι w‖ = ‖(l : ℂ_[l])‖ := by rw [← hn, hι, hw]

  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖ι w‖ ^ N * R ≤ 1 := by
    rcases le_or_gt R 1 with h | h
    · exact ⟨0, by simpa using h⟩
    · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (by linarith : (0:ℝ) < R)) (hnw ▸ hl1)
      refine ⟨N, ?_⟩
      have := mul_lt_mul_of_pos_right hN (by linarith : (0:ℝ) < R)
      rw [inv_mul_cancel₀ (by linarith)] at this
      exact this.le
  set c : F := ι w ^ N with hc
  have hcn : ‖c‖ = ‖ι w‖ ^ N := by rw [hc, norm_pow]
  have hcpos : 0 < ‖c‖ := by rw [hcn, hnw]; exact pow_pos hl0 N
  have hx : ∀ a, ∃ x : Fl l, ι x = if a ∈ s then c * z a else 0 := by
    intro a
    split_ifs with ha
    · refine hsurj _ ?_
      rw [norm_mul, hcn]
      calc ‖ι w‖ ^ N * ‖z a‖ ≤ ‖ι w‖ ^ N * R :=
            mul_le_mul_of_nonneg_left (hz a ha) (pow_nonneg (norm_nonneg _) _)
        _ ≤ 1 := hN
    · exact ⟨0, map_zero ι⟩
  choose x hxe using hx
  have hxa : ∀ a ∈ s, ι (x a) = c * z a := fun a ha => by rw [hxe, if_pos ha]
  have hsa : ∀ a ∈ s, sh (x a) = tsh c * tsh (z a) := fun a ha => by
    rw [← hι, hxa a ha, map_mul]
  have hss : sh (∑ a ∈ s, x a) = tsh c * tsh (∑ a ∈ s, z a) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hι, map_sum, Finset.sum_congr rfl hxa, ← Finset.mul_sum, map_mul]
  have hbd : ∀ a ∈ s, ‖sh (x a)‖ ≤ ‖c‖ * R := fun a ha => by
    rw [hsa a ha, norm_mul, hn, hn]
    exact mul_le_mul_of_nonneg_left (hz a ha) (norm_nonneg _)
  have key := (untilt_sum_sub_le l α s (‖c‖ * R) x (mul_nonneg (norm_nonneg _) hR) hbd).1
  rw [hss, Finset.sum_congr rfl hsa, ← Finset.mul_sum, ← mul_sub, norm_mul, hn] at key
  have : ‖c‖ * ‖tsh (∑ a ∈ s, z a) - ∑ a ∈ s, tsh (z a)‖ ≤ ‖c‖ * (‖(l : ℂ_[l])‖ * R) := by
    linarith [key]
  exact le_of_mul_le_mul_left this hcpos

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUntiltExtensionFinsetSumSubLeStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_untilt_extension_finset_sum_sub_le : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (α : Type) (s : Finset α) (z : α → F) (R : ℝ), 0 ≤ R → (∀ a ∈ s, ‖z a‖ ≤ R) →
      ‖tsh (∑ a ∈ s, z a) - ∑ a ∈ s, tsh (z a)‖ ≤ ‖(l : ℂ_[l])‖ * R := by
  first | exact @GlobalTheory.untilt_ext_sum_sub_le | exact GlobalTheory.untilt_ext_sum_sub_le | (intros; apply GlobalTheory.untilt_ext_sum_sub_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomTiltMapTiltFrobeniusIntegerPower
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomTiltMapTiltFrobeniusIntegerPower
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem map_pw_eq_pw (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] [CharP F l] [PerfectRing F l]
    (ι : Fl l →+* F) (k : ℤ) (x : Fl l) : ι (GlobalTheory.PSer.pw k x) = GlobalTheory.PMonE.pw l k (ι x) := by
  have hsymm : ∀ y : Fl l, ι ((frobeniusEquiv (Fl l) l).symm y) = (frobeniusEquiv F l).symm (ι y) :=
    fun y => RingHom.map_frobeniusEquiv_symm l ι y
  have hit : ∀ (n : ℕ) (y : Fl l), ι (((frobeniusEquiv (Fl l) l).symm)^[n] y) = ((frobeniusEquiv F l).symm)^[n] (ι y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih => intro y; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hsymm, ih]
  have hpos : ∀ (n : ℕ) (y : Fl l), ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ n) y = y ^ l ^ n := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ']
      change (frobeniusEquiv (Fl l) l) (((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ n) y) = _
      rw [ih, frobeniusEquiv_apply, frobenius_def, ← pow_mul, pow_succ]
  have hneg : ∀ (n : ℕ) (y : Fl l), ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ (-(n : ℤ))) y
      = ((frobeniusEquiv (Fl l) l).symm)^[n] y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [Nat.cast_succ, neg_add, zpow_add, Function.iterate_succ_apply]
      change ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ (-(n : ℤ)))
        (((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ (-1 : ℤ)) y) = _
      rw [ih, zpow_neg_one]
      rfl
  cases k with
  | ofNat n =>
    simp only [GlobalTheory.PSer.pw, GlobalTheory.PMonE.pw, Int.ofNat_eq_coe, zpow_natCast, hpos, map_pow]
    simp
  | negSucc n =>
    have hk : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := rfl
    simp only [GlobalTheory.PSer.pw, GlobalTheory.PMonE.pw]
    rw [if_neg (by omega), hk, hneg, hit]
    congr

end GlobalTheory.PSer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomTiltMapTiltFrobeniusIntegerPowerStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_tilt_map_tiltFrobeniusIntegerPower : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] [CharP F l] [PerfectRing F l]
    (ι : Fl l →+* F) (k : ℤ) (x : Fl l), ι (GlobalTheory.PSer.pw k x) = GlobalTheory.PMonE.pw l k (ι x) := by
  first | exact @GlobalTheory.PSer.map_pw_eq_pw | exact GlobalTheory.PSer.map_pw_eq_pw | (intros; apply GlobalTheory.PSer.map_pw_eq_pw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltedSeriesRowSubUntiltTruncatedAdditiveRow
noncomputable section

open Formalism.Per GlobalTheory.PSer Finset
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem row_lam_sub_untilt_rowT : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CharP F l]
    [PerfectRing F l] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (h : ℕ) (m x : Fin h → Fl l) (ϖ : F) (K : ℕ) (τ : Fin h → ℝ) (r : Fin h), 1 ≤ h → tsh ϖ = l →
      (∀ j, ‖sh (x j)‖ < 1) →
      (∀ (j : Fin h) (n : ℤ), ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r ∧
        ((K : ℤ) < |n| → ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r / l)) →
      ‖∑ j, sh (m j) * lam h r (x j) - tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r)‖
        ≤ ‖(l : ℂ_[l])‖ * τ r := by
  intro l _ F _ _ _ _ ι tsh hn hs hsurj h m x ϖ K τ r hh hϖ hx hT
  have hid : ∀ j n, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) =
      sh (m j) * ((l : ℂ_[l]) ^ (-n) * sh (pw (n * h + ((r : ℕ) : ℤ)) (x j))) := by
    intro j n
    simp only [GlobalTheory.PMonE.term, map_mul, map_zpow₀, hϖ, hs]
    rw [← GlobalTheory.T.ringHom_tilt_map_tiltFrobeniusIntegerPower l F ι, hs]
    rw [show ((r : ℤ) + n * h) = n * h + ((r : ℕ) : ℤ) by push_cast; ring]
    ring
  have hR : 0 ≤ τ r := (norm_nonneg _).trans (hT r 0).1
  have hR' : 0 ≤ ‖(l : ℂ_[l])‖ * τ r := mul_nonneg (norm_nonneg _) hR
  have hlb : τ r / l = ‖(l : ℂ_[l])‖ * τ r := by rw [Laws.norm_l, div_eq_inv_mul]
  have htail : ∀ j, ‖sh (m j) * lam h r (x j) -
      ∑ n ∈ Icc (-(K : ℤ)) K, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)‖
        ≤ ‖(l : ℂ_[l])‖ * τ r := by
    intro j
    have hsum : Summable (fun n => tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)) := by
      simp only [hid]; exact (Laws.summable_lam hh r (hx j)).mul_left _
    have hlam : sh (m j) * lam h r (x j) =
        ∑' n, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) := by
      simp only [hid, lam]; rw [tsum_mul_left]
    rw [hlam, ← hsum.sum_add_tsum_compl (s := Icc (-(K : ℤ)) K), add_sub_cancel_left]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hR' fun ⟨n, hmem⟩ => ?_
    rw [← hlb]
    show ‖tsh _‖ ≤ _
    rw [hn]
    apply (hT j n).2
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] at hmem
    rw [lt_abs]; omega
  have hfin : ‖∑ j, ∑ n ∈ Icc (-(K : ℤ)) K,
      tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) -
        tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r)‖ ≤ ‖(l : ℂ_[l])‖ * τ r := by
    have := GlobalTheory.T.norm_untilt_extension_finset_sum_sub_le l F ι tsh hn hs hsurj (Fin h × ℤ) (univ ×ˢ Icc (-(K : ℤ)) K)
      (fun a => GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r a.1 a.2) (τ r) hR
      (fun a _ => (hT a.1 a.2).1)
    simp only [Finset.sum_product] at this
    rw [norm_sub_rev]
    simpa [GlobalTheory.PMonE.rowT] using this
  calc _ = ‖∑ j, (sh (m j) * lam h r (x j) -
        ∑ n ∈ Icc (-(K : ℤ)) K, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)) +
      (∑ j, ∑ n ∈ Icc (-(K : ℤ)) K,
        tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) -
        tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r))‖ := by
        rw [Finset.sum_sub_distrib]; congr 1; abel
    _ ≤ max _ _ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ _ := max_le (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR' fun j _ => htail j) hfin

end GlobalTheory.PSer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltedSeriesRowSubUntiltTruncatedAdditiveRowStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tiltedSeriesRow_sub_untilt_truncatedAdditiveRow : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CharP F l]
    [PerfectRing F l] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (h : ℕ) (m x : Fin h → Fl l) (ϖ : F) (K : ℕ) (τ : Fin h → ℝ) (r : Fin h), 1 ≤ h → tsh ϖ = l →
      (∀ j, ‖sh (x j)‖ < 1) →
      (∀ (j : Fin h) (n : ℤ), ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r ∧
        ((K : ℤ) < |n| → ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r / l)) →
      ‖∑ j, sh (m j) * lam h r (x j) - tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r)‖
        ≤ ‖(l : ℂ_[l])‖ * τ r := by
  first | exact @GlobalTheory.PSer.row_lam_sub_untilt_rowT | exact GlobalTheory.PSer.row_lam_sub_untilt_rowT | (intros; apply GlobalTheory.PSer.row_lam_sub_untilt_rowT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltOrthOfUntiltOrth
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltOrthOfUntiltOrth
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem tilt_orth_of_untilt_orth : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (m : Fin h → Fl l), (∀ i j, ‖sh (m i)‖ < l * ‖sh (m j)‖) →
    (∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖sh (m j)‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * sh (m i)‖) →
    ∀ (c : Fin h → ℤ) (j : Fin h), ¬ (l : ℤ) ∣ c j → ‖sh (m j)‖ ≤ ‖sh (∑ i, (c i : Fl l) * m i)‖ := by
  intro l _ h m hrat horth c j hj
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl0 : (0 : ℤ) < l := by exact_mod_cast (Fact.out : l.Prime).pos

  have hne : (Finset.univ : Finset (Fin h)).Nonempty := ⟨j, Finset.mem_univ _⟩
  set M : ℝ := Finset.univ.sup' hne (fun i => ‖sh (m i)‖) with hM
  have hMle : ∀ i, ‖sh (m i)‖ ≤ M := fun i => Finset.le_sup' (fun i => ‖sh (m i)‖) (Finset.mem_univ i)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMle j)
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup' hne (fun i => ‖sh (m i)‖)
  have hsmall : ‖(l : ℂ_[l])‖ * M < ‖sh (m j)‖ := by
    rw [GlobalTheory.PSer.Laws.norm_l, hM, hi0, inv_mul_lt_iff₀ hl]
    exact hrat i0 j

  set n : Fin h → ℕ := fun i => (c i % (l : ℤ)).toNat with hn
  have hnc : ∀ i, ((n i : ℕ) : ℤ) = c i % (l : ℤ) := fun i =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hl0.ne')
  have hcast : ∀ i, (c i : Fl l) = (n i : Fl l) := by
    intro i
    have : ((n i : ℤ) : Fl l) = (n i : Fl l) := Int.cast_natCast _
    rw [← this, CharP.intCast_eq_intCast (Fl l) l, hnc]
    exact (Int.mod_modEq _ _).symm
  have hnj : ‖((n j : ℕ) : ℚ_[l])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff, Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)]
    intro hd
    apply hj
    have h1 : (l : ℤ) ∣ c j % (l : ℤ) := by rw [← hnc]; exact_mod_cast hd
    have h2 := (Int.dvd_iff_emod_eq_zero ..).1 h1
    rw [Int.emod_emod_of_dvd _ (dvd_refl _)] at h2
    exact Int.dvd_of_emod_eq_zero h2

  have hsum : (∑ i, (c i : Fl l) * m i) =
      ∑ p ∈ (Finset.univ : Finset (Fin h)).sigma (fun i => Finset.range (n i)), m p.1 := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hcast]
  have hsum2 : (∑ p ∈ (Finset.univ : Finset (Fin h)).sigma (fun i => Finset.range (n i)), sh (m p.1)) =
      ∑ i, algebraMap ℚ_[l] ℂ_[l] ((n i : ℕ) : ℚ_[l]) * sh (m i) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, map_natCast]
  obtain ⟨hd, -⟩ := GlobalTheory.T.norm_sh_sum_sub_sum_sh_le l ((_ : Fin h) × ℕ) ((Finset.univ : Finset (Fin h)).sigma (fun i => Finset.range (n i)))
    M (fun p => m p.1) hM0 (fun p _ => hMle p.1)
  rw [← hsum, hsum2] at hd
  have ho := horth (fun i => ((n i : ℕ) : ℚ_[l])) j
  simp only [hnj, one_mul] at ho

  by_contra hlt
  push_neg at hlt
  set b := sh (∑ i, (c i : Fl l) * m i)
  set a := ∑ i, algebraMap ℚ_[l] ℂ_[l] ((n i : ℕ) : ℚ_[l]) * sh (m i)
  have : ‖a‖ ≤ max ‖b‖ ‖b - a‖ := by
    have := IsUltrametricDist.norm_add_le_max b (-(b - a))
    rwa [norm_neg, show b + -(b - a) = a by ring] at this
  have hba : ‖b - a‖ < ‖sh (m j)‖ := hd.trans_lt hsmall
  exact absurd (ho.trans this) (not_le.2 (max_lt hlt hba))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltOrthOfUntiltOrthStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sh_le_sh_int_sum_of_orthogonal : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (m : Fin h → Fl l), (∀ i j, ‖sh (m i)‖ < l * ‖sh (m j)‖) →
    (∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖sh (m j)‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * sh (m i)‖) →
    ∀ (c : Fin h → ℤ) (j : Fin h), ¬ (l : ℤ) ∣ c j → ‖sh (m j)‖ ≤ ‖sh (∑ i, (c i : Fl l) * m i)‖ := by
  first | exact @GlobalTheory.tilt_orth_of_untilt_orth | exact GlobalTheory.tilt_orth_of_untilt_orth | (intros; apply GlobalTheory.tilt_orth_of_untilt_orth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltMultiplicativeExtensionSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltMultiplicativeExtensionSurjective
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer.TshOnto

theorem tsh_surjective : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ t : ℂ_[l], ∃ z : F, tsh z = t := by
  intro l _ F _ ι tsh _hn hsh _ t
  obtain ⟨-, -, -, -, -, honto, -, -⟩ := GlobalTheory.PSer.Laws.sh_laws l
  by_cases ht : ‖t‖ ≤ 1
  · obtain ⟨x, hx⟩ := honto t ht
    exact ⟨ι x, by rw [hsh, hx]⟩
  · push_neg at ht
    have hinv : ‖t⁻¹‖ ≤ 1 := by
      rw [norm_inv]; exact inv_le_one_of_one_le₀ ht.le
    obtain ⟨x, hx⟩ := honto t⁻¹ hinv
    refine ⟨(ι x)⁻¹, ?_⟩
    rw [map_inv₀, hsh, hx, inv_inv]

end GlobalTheory.PSer.TshOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltMultiplicativeExtensionSurjectiveStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tiltUntilt_multiplicative_extension_surjective : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ t : ℂ_[l], ∃ z : F, tsh z = t := by
  first | exact @GlobalTheory.PSer.TshOnto.tsh_surjective | exact GlobalTheory.PSer.TshOnto.tsh_surjective | (intros; apply GlobalTheory.PSer.TshOnto.tsh_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltComplexPadicIsAlgClosedUnitBall
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

open GroundTheory.PAdicHodge

theorem tilt_isAlgClosed_and_unitBall : ∀ (l : ℕ) [Fact l.Prime],
    IsAlgClosed (FractionRing (PreTilt (normInteger ℂ_[l]) l)) ∧
      ∃ ι : Fl l →+* FractionRing (PreTilt (normInteger ℂ_[l]) l),
        (∀ x, tiltSharp (K := ℂ_[l]) (p := l) (ι x) = sh x) ∧
        (∀ z : FractionRing (PreTilt (normInteger ℂ_[l]) l), ‖z‖ ≤ 1 → ∃ x, ι x = z) := by
  intro l _
  obtain ⟨e, he⟩ := exists_flEquiv_untilt l
  have hC : IsAlgClosed (Formalism.BasicNotions.Loc.Cb l) := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  refine ⟨?_, (algebraMap (PreTilt (normInteger ℂ_[l]) l) _).comp (e : Fl l →+* _), ?_, ?_⟩
  · let e' : Formalism.BasicNotions.Loc.Cb l ≃+* FractionRing (PreTilt (normInteger ℂ_[l]) l) :=
      IsFractionRing.ringEquivOfRingEquiv (A := Formalism.BasicNotions.Loc.OCb l) (B := PreTilt (normInteger ℂ_[l]) l) e
    exact IsAlgClosed.of_ringEquiv _ _ e'
  · intro x
    rw [RingHom.comp_apply, tiltSharp_algebraMap]
    exact he x
  · intro z hz
    obtain ⟨a, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 hz
    exact ⟨e.symm a, by simp⟩

end GlobalTheory.PSer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumMulUntiltFrobeniusDoubleSeriesEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumMulUntiltFrobeniusDoubleSeriesEqZero
noncomputable section

open Formalism.Per GlobalTheory.PSer Filter Topology
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem summable_Lam_terms (l : ℕ) [Fact l.Prime] (h i : ℕ) (y : ℕ → Fl l) (ρ : ℝ)
    (hh : 1 ≤ h) (hρ : ρ < 1) (hy : ∀ k, ‖sh (y k)‖ ≤ ρ) :
    Summable fun k : ℕ => (l : ℂ_[l]) ^ k * lam h i (y k) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have h2 : Tendsto (fun k : ℕ => ((l : ℝ)⁻¹) ^ k * gam l h i ρ) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 (by linarith))
      (inv_lt_one_of_one_lt₀ hl)).mul_const (gam l h i ρ)
    simpa using this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) h2
  rw [norm_mul, norm_pow, Laws.norm_l]
  exact mul_le_mul_of_nonneg_left (lam_hasSum_norm_le_frob l h i ρ (y k) hh hρ (hy k)).2.1
    (pow_nonneg (inv_nonneg.2 (by linarith)) _)

theorem sum_mul_Lam_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]) (i : ℕ) (y : ℕ → Fin h → Fl l) (ρ : ℝ),
    1 ≤ h → ρ < 1 → (∀ k j, ‖sh (y k j)‖ ≤ ρ) →
    HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * ∑ j, μ j * lam h i (y k j)) 0 →
    ∑ j, μ j * abelian₂ h i (fun k => y k j) = 0 := by
  intro l _ h μ i y ρ hh hρ hy hs
  have hsum : ∀ j, Summable fun k : ℕ => μ j * ((l : ℂ_[l]) ^ k * lam h i (y k j)) := fun j =>
    (summable_Lam_terms l h i (fun k => y k j) ρ hh hρ (fun k => hy k j)).mul_left (μ j)
  calc ∑ j, μ j * abelian₂ h i (fun k => y k j)
      = ∑ j, ∑' k : ℕ, μ j * ((l : ℂ_[l]) ^ k * lam h i (y k j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        unfold abelian₂
        rw [tsum_mul_left]
    _ = ∑' k : ℕ, ∑ j, μ j * ((l : ℂ_[l]) ^ k * lam h i (y k j)) :=
        (Summable.tsum_finsetSum fun j _ => hsum j).symm
    _ = ∑' k : ℕ, (l : ℂ_[l]) ^ k * ∑ j, μ j * lam h i (y k j) := by
        refine tsum_congr fun k => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = 0 := hs.tsum_eq

end GlobalTheory.PSer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumMulUntiltFrobeniusDoubleSeriesEqZeroStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_mul_untiltFrobeniusDoubleSeries_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]) (i : ℕ) (y : ℕ → Fin h → Fl l) (ρ : ℝ),
    1 ≤ h → ρ < 1 → (∀ k j, ‖sh (y k j)‖ ≤ ρ) →
    HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * ∑ j, μ j * lam h i (y k j)) 0 →
    ∑ j, μ j * abelian₂ h i (fun k => y k j) = 0 := by
  first | exact @GlobalTheory.PSer.sum_mul_Lam_eq_zero | exact GlobalTheory.PSer.sum_mul_Lam_eq_zero | (intros; apply GlobalTheory.PSer.sum_mul_Lam_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOrthogonalFamilyResidueZeros
noncomputable section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.CoreOrth

theorem core (l : ℕ) [Fact l.Prime] (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    [IsAlgClosed F] [CharP F l] [PerfectRing F l] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l])
    (hn : ∀ z, ‖tsh z‖ = ‖z‖) (hs : ∀ x, tsh (ι x) = sh x) (hon : ∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z)
    (h : ℕ) (μ : Fin h → ℂ_[l]) (h2 : 2 ≤ h) (hμ : ∀ i, μ i ≠ 0 ∧ ‖μ i‖ ≤ 1)
    (hanti : Antitone (fun i => ‖μ i‖)) (hratio : ∀ i j, ‖μ i‖ < l * ‖μ j‖)
    (horth : ∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖μ j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * μ i‖) :
    ∃ (y : Fin h → ℕ → Formalism.Per.Fl l) (j0 : Fin h) (r R : ℝ), 0 ≤ r ∧ r < 1 ∧ R < 1 ∧
      (∀ a k, ‖sh (y a k)‖ ≤ R) ∧ (∀ k, ‖sh (y j0 k)‖ ≤ r) ∧ r ^ l ^ h < ‖sh (y j0 0)‖ ∧
      ∀ i : Fin h, ∑ j, μ j * abelian₂ h i (y j) = 0 := by
  obtain ⟨-, -, -, -, -, hsurj, -, -⟩ := GlobalTheory.PSer.Laws.sh_laws l
  have hnι : ∀ x, ‖ι x‖ = ‖sh x‖ := fun x => by rw [← hn, hs]
  choose m hm using fun j => hsurj (μ j) (hμ j).2
  obtain ⟨w, hw⟩ := hsurj (l : ℂ_[l]) (by rw [GlobalTheory.PSer.Laws.norm_l]; exact inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le))
  set ϖ : F := ι w with hϖdef
  have hϖ : ‖ϖ‖ = (l : ℝ)⁻¹ := by rw [hnι, hw, GlobalTheory.PSer.Laws.norm_l]
  have hϖs : tsh ϖ = l := by rw [hs, hw]
  set lamF : Fin h → F := fun j => ι (m j) with hlamF
  have hnl : ∀ j, ‖lamF j‖ = ‖μ j‖ := fun j => by simp only [lamF, hnι, hm]
  have hmu : ∀ j, sh (m j) = μ j := hm
  have horthF : GlobalTheory.PMonE.Orth l lamF := by
    intro c j hc
    have := GlobalTheory.T.norm_sh_le_sh_int_sum_of_orthogonal l h m (fun i j => by rw [hmu, hmu]; exact hratio i j) (fun c j => by simp only [hmu]; exact horth c j) c j hc
    have e : (∑ i, (c i : F) * lamF i) = ι (∑ i, (c i : Fl l) * m i) := by simp [lamF, map_sum]
    rw [e, hnι, hnι]; exact this
  have hpos : 0 < h := by omega
  obtain ⟨ρ, τ, K, hρ, hτ, hW1, hW2, hW3⟩ := GlobalTheory.T.frobenius_polydisc_windows_surjective_bounds_zero F l h ϖ hpos hϖ lamF
    (fun j => by rw [← norm_pos_iff, hnl]; exact norm_pos_iff.2 (hμ j).1)
    (fun i j hij => by simp only [hnl]; exact hanti hij) horthF (fun i j => by simp only [hnl]; exact hratio i j)
  set S : Set (Fin h → Fl l) := {x | ∀ j, ‖sh (x j)‖ ≤ ρ j} with hSdef
  let η : (Fin h → Fl l) → Fin h → ℂ_[l] := fun x i => ∑ j, sh (m j) * lam h i (x j)
  have hE : ∀ x ∈ S, ∀ i, ‖η x i - tsh (GlobalTheory.PMonE.rowT l ϖ lamF K (fun j => ι (x j)) i)‖ ≤ ‖(l : ℂ_[l])‖ * τ i := by
    intro x hx i
    exact GlobalTheory.T.tiltedSeriesRow_sub_untilt_truncatedAdditiveRow l F ι tsh hn hs hon h m x ϖ K τ i (by omega) hϖs (fun j => (hx j).trans_lt (hρ j).2)
      (fun j n => hW1 (fun j => ι (x j)) (fun j => by rw [hnι]; exact hx j) i j n)
  have hpre : ∀ z : Fin h → F, (∀ j, ‖z j‖ ≤ ρ j) → ∃ x ∈ S, (fun j => ι (x j)) = z := by
    intro z hz
    choose x hx using fun j => hon (z j) ((hz j).trans (hρ j).2.le)
    refine ⟨x, fun j => ?_, funext hx⟩
    rw [← hnι, hx]; exact hz j
  have hL1 : ∀ t : Fin h → ℂ_[l], (∀ i, ‖t i‖ ≤ τ i) → ∃ y ∈ S, ∀ i, ‖η y i - t i‖ ≤ ‖(l : ℂ_[l])‖ * τ i := by
    intro t ht
    choose b hb using fun i => GlobalTheory.T.tiltUntilt_multiplicative_extension_surjective l F ι tsh hn hs hon (t i)
    obtain ⟨z, hz, hrow⟩ := hW2 b (fun i => by rw [← hn, hb]; exact ht i)
    obtain ⟨x, hxS, hxz⟩ := hpre z hz
    refine ⟨x, hxS, fun i => ?_⟩
    have := hE x hxS i
    rwa [hxz, hrow, hb] at this
  obtain ⟨z0, hz0, ⟨j0, hj0⟩, hrow0⟩ := hW3
  obtain ⟨x0, hx0S, hx0z⟩ := hpre z0 hz0
  have hL2 : ∀ i, ‖η x0 i‖ ≤ ‖(l : ℂ_[l])‖ * τ i := by
    intro i
    have := hE x0 hx0S i
    rwa [hx0z, hrow0, map_zero, sub_zero] at this
  obtain ⟨y, hy0, hyS, hysum⟩ := GlobalTheory.T.lift_hasSum_zero_of_surjective_mod_prime l (Fin h → Fl l) (Fin h) η τ S hL1 x0 hx0S hL2
  haveI : Nonempty (Fin h) := ⟨⟨0, hpos⟩⟩
  set R : ℝ := Finset.univ.sup' Finset.univ_nonempty ρ with hRdef
  have hρR : ∀ j, ρ j ≤ R := fun j => Finset.le_sup' ρ (Finset.mem_univ j)
  have hR1 : R < 1 := (Finset.sup'_lt_iff _).2 fun j _ => (hρ j).2
  refine ⟨fun j k => y k j, j0, ρ j0, R, (hρ j0).1.le, (hρ j0).2, hR1,
    fun a k => (hyS k a).trans (hρR a), fun k => hyS k j0, ?_, ?_⟩
  · show ρ j0 ^ l ^ h < ‖sh (y 0 j0)‖
    rw [hy0, ← hnι]
    have := congrFun hx0z j0
    rw [this]; exact hj0
  · intro i
    refine GlobalTheory.T.sum_mul_untiltFrobeniusDoubleSeries_eq_zero l h μ i y R (by omega) hR1 (fun k j => (hyS k j).trans (hρR j)) ?_
    have := hysum i
    simpa [η, hmu] using this

end GlobalTheory.CoreOrth

namespace GlobalTheory.CoreOrth

theorem residue_zeros : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 2 ≤ h → (∀ i, μ i ≠ 0 ∧ ‖μ i‖ ≤ 1) → Antitone (fun i => ‖μ i‖) → (∀ i j, ‖μ i‖ < l * ‖μ j‖) → (∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖μ j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * μ i‖) → ∃ (y : Fin h → ℕ → Formalism.Per.Fl l) (j0 : Fin h) (r R : ℝ), 0 ≤ r ∧ r < 1 ∧ R < 1 ∧ (∀ a k, ‖sh (y a k)‖ ≤ R) ∧ (∀ k, ‖sh (y j0 k)‖ ≤ r) ∧ r ^ l ^ h < ‖sh (y j0 0)‖ ∧ ∀ i : Fin h, ∑ j, μ j * abelian₂ h i (y j) = 0 := by
  intro l _ h μ h2 hμ hanti hratio horth
  obtain ⟨hac, ι, hs, hon⟩ := GlobalTheory.PSer.tilt_isAlgClosed_and_unitBall l
  haveI := hac
  exact core l _ ι (GroundTheory.PAdicHodge.tiltSharp ℂ_[l] l) (fun z => GroundTheory.PAdicHodge.norm_tiltSharp z) hs hon
    h μ h2 hμ hanti hratio horth
end GlobalTheory.CoreOrth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOrthogonalFamilyResidueZerosStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_family_residue_zeros : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 2 ≤ h → (∀ i, μ i ≠ 0 ∧ ‖μ i‖ ≤ 1) → Antitone (fun i => ‖μ i‖) → (∀ i j, ‖μ i‖ < l * ‖μ j‖) → (∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖μ j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * μ i‖) → ∃ (y : Fin h → ℕ → Formalism.Per.Fl l) (j0 : Fin h) (r R : ℝ), 0 ≤ r ∧ r < 1 ∧ R < 1 ∧ (∀ a k, ‖sh (y a k)‖ ≤ R) ∧ (∀ k, ‖sh (y j0 k)‖ ≤ r) ∧ r ^ l ^ h < ‖sh (y j0 0)‖ ∧ ∀ i : Fin h, ∑ j, μ j * abelian₂ h i (y j) = 0 := by
  first | exact @GlobalTheory.CoreOrth.residue_zeros | exact GlobalTheory.CoreOrth.residue_zeros | (intros; apply GlobalTheory.CoreOrth.residue_zeros <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSortedNormalizedOrthBasisComplexPAdic
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSortedNormalizedOrthBasisComplexPAdic
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PMonE.OrthBasis

private lemma exists_orthogonal_translate (l : ℕ) [Fact l.Prime] (W : Submodule ℚ_[l] ℂ_[l])
    [FiniteDimensional ℚ_[l] W] (x : ℂ_[l]) (hx : x ∉ W) :
    ∃ y : ℂ_[l], y - x ∈ W ∧ y ≠ 0 ∧ ∀ w ∈ W, ‖y‖ ≤ ‖y + w‖ ∧ ‖w‖ ≤ ‖y + w‖ := by
  haveI : ProperSpace W := FiniteDimensional.proper ℚ_[l] W
  obtain ⟨w₀, hw₀K, hmin⟩ := (isCompact_closedBall (0 : W) ‖x‖).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self (norm_nonneg x)⟩
    (Continuous.continuousOn (f := fun w : W => ‖x - (w : ℂ_[l])‖) (by fun_prop))
  have h0 : ‖x - (w₀ : ℂ_[l])‖ ≤ ‖x‖ := by
    simpa using hmin (Metric.mem_closedBall_self (norm_nonneg x) : (0 : W) ∈ _)
  have hglob : ∀ w : W, ‖x - (w₀ : ℂ_[l])‖ ≤ ‖x - (w : ℂ_[l])‖ := by
    intro w
    by_cases hw : w ∈ Metric.closedBall (0 : W) ‖x‖
    · exact hmin hw
    · have hlt : ‖x‖ < ‖(w : ℂ_[l])‖ := by simpa using hw
      have h1 : ‖x - (w : ℂ_[l])‖ = ‖(w : ℂ_[l])‖ := by
        rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact hlt.ne),
          norm_neg, max_eq_right hlt.le]
      rw [h1]; exact h0.trans hlt.le
  refine ⟨x - w₀, by simpa using W.neg_mem w₀.2, ?_, fun w hw => ⟨?_, ?_⟩⟩
  · intro h
    exact hx (by rw [sub_eq_zero.1 h]; exact w₀.2)
  · have := hglob ⟨w₀ - w, W.sub_mem w₀.2 hw⟩
    simpa [sub_sub_eq_add_sub, sub_add_eq_add_sub, add_sub_assoc] using this
  · have h1 := hglob ⟨w₀ - w, W.sub_mem w₀.2 hw⟩
    have h2 : w = (x - w₀ + w) + -(x - w₀) := by abel
    calc ‖w‖ = ‖(x - w₀ + w) + -(x - w₀)‖ := by rw [← h2]
      _ ≤ max ‖x - w₀ + w‖ ‖-(x - w₀)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ ‖x - w₀ + w‖ := by
        rw [norm_neg]
        refine max_le le_rfl ?_
        have : x - (↑(⟨w₀ - w, W.sub_mem w₀.2 hw⟩ : W) : ℂ_[l]) = x - w₀ + w := by simp; abel
        rw [← this]; exact h1

private lemma exists_orthogonal_family_in_span (l : ℕ) [Fact l.Prime] :
    ∀ (n : ℕ) (μ : Fin n → ℂ_[l]), LinearIndependent ℚ_[l] μ →
      ∃ u : Fin n → ℂ_[l], (∀ i, u i ∈ Submodule.span ℚ_[l] (Set.range μ)) ∧ (∀ i, u i ≠ 0) ∧
        ∀ (c : Fin n → ℚ_[l]) (j : Fin n),
          ‖c j‖ * ‖u j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * u i‖ := by
  intro n
  induction n with
  | zero => intro μ _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun _ j => j.elim0⟩
  | succ n ih =>
    intro μ hμ
    rw [← Fin.snoc_init_self μ, linearIndependent_finSnoc] at hμ
    obtain ⟨hμ₀, hx⟩ := hμ
    obtain ⟨u₀, hu₀S, hu₀, horth⟩ := ih _ hμ₀
    set W := Submodule.span ℚ_[l] (Set.range (Fin.init μ))
    haveI : FiniteDimensional ℚ_[l] W :=
      FiniteDimensional.span_of_finite ℚ_[l] (Set.finite_range _)
    obtain ⟨y, hyx, hy0, hy⟩ := exists_orthogonal_translate l W _ hx
    have hWS : W ≤ Submodule.span ℚ_[l] (Set.range μ) := by
      apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨i.castSucc, rfl⟩
    have hxS : μ (Fin.last n) ∈ Submodule.span ℚ_[l] (Set.range μ) :=
      Submodule.subset_span ⟨_, rfl⟩
    refine ⟨Fin.snoc (α := fun _ => ℂ_[l]) u₀ y, fun i => ?_, fun i => ?_, fun c j => ?_⟩
    · refine Fin.lastCases ?_ (fun k => ?_) i
      · simp only [Fin.snoc_last]
        have : y = μ (Fin.last n) + (y - μ (Fin.last n)) := by abel
        rw [this]; exact Submodule.add_mem _ hxS (hWS hyx)
      · simp only [Fin.snoc_castSucc]; exact hWS (hu₀S k)
    · refine Fin.lastCases ?_ (fun k => ?_) i
      · simpa using hy0
      · simpa using hu₀ k
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      set w := ∑ i : Fin n, algebraMap ℚ_[l] ℂ_[l] (c i.castSucc) * u₀ i
      have hw : w ∈ W := Submodule.sum_mem _ fun i _ => by
        rw [← Algebra.smul_def]; exact Submodule.smul_mem _ _ (hu₀S i)
      have key : ‖c (Fin.last n)‖ * ‖y‖ ≤ ‖w + algebraMap ℚ_[l] ℂ_[l] (c (Fin.last n)) * y‖ ∧
          ‖w‖ ≤ ‖w + algebraMap ℚ_[l] ℂ_[l] (c (Fin.last n)) * y‖ := by
        by_cases hc : c (Fin.last n) = 0
        · simp [hc]
        · set a := algebraMap ℚ_[l] ℂ_[l] (c (Fin.last n))
          have hna : ‖a‖ = ‖c (Fin.last n)‖ := norm_algebraMap' ℂ_[l] _
          have ha : a ≠ 0 := by
            intro h; apply hc; rw [← norm_eq_zero, ← hna, h, norm_zero]
          have hw' : a⁻¹ * w ∈ W := by
            rw [show a⁻¹ = algebraMap ℚ_[l] ℂ_[l] (c (Fin.last n))⁻¹ by simp [a],
              ← Algebra.smul_def]
            exact Submodule.smul_mem _ _ hw
          obtain ⟨h1, h2⟩ := hy _ hw'
          have e : w + a * y = a * (y + a⁻¹ * w) := by field_simp; ring
          rw [e, norm_mul, hna]
          refine ⟨mul_le_mul_of_nonneg_left h1 (norm_nonneg _), ?_⟩
          have : ‖w‖ = ‖c (Fin.last n)‖ * ‖a⁻¹ * w‖ := by
            rw [norm_mul, norm_inv, hna, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hc),
              one_mul]
          rw [this]; exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa using key.1
      · simp only [Fin.snoc_castSucc]
        exact (horth (fun i => c i.castSucc) k).trans key.2

private lemma exists_rescale_norm_mem_Ioc (l : ℕ) [Fact l.Prime] (x : ℂ_[l]) (hx : x ≠ 0) :
    ∃ t : ℚ_[l], t ≠ 0 ∧ (l : ℝ)⁻¹ < ‖algebraMap ℚ_[l] ℂ_[l] t * x‖ ∧
      ‖algebraMap ℚ_[l] ℂ_[l] t * x‖ ≤ 1 := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlpos : (0 : ℝ) < l := zero_lt_one.trans hl
  obtain ⟨n, h1, h2⟩ := exists_mem_Ioc_zpow (norm_pos_iff.2 hx) hl
  have hN : ‖algebraMap ℚ_[l] ℂ_[l] ((l : ℚ_[l]) ^ (n + 1)) * x‖ = ‖x‖ / (l : ℝ) ^ (n + 1) := by
    rw [norm_mul, norm_algebraMap', norm_zpow, Padic.norm_p, inv_zpow, div_eq_inv_mul]
  refine ⟨(l : ℚ_[l]) ^ (n + 1), zpow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero),
    ?_, ?_⟩
  · rw [hN, lt_div_iff₀ (zpow_pos hlpos _), zpow_add_one₀ hlpos.ne', mul_comm _ (l : ℝ), ← mul_assoc,
      inv_mul_cancel₀ hlpos.ne', one_mul]
    exact h1
  · rw [hN, div_le_one (zpow_pos hlpos _)]
    exact h2

private lemma exists_sorted_orthogonal_family_in_span (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l])
    (hμ : LinearIndependent ℚ_[l] μ) :
    ∃ v : Fin h → ℂ_[l], (∀ i, v i ∈ Submodule.span ℚ_[l] (Set.range μ)) ∧
      (∀ i, v i ≠ 0 ∧ ‖v i‖ ≤ 1) ∧ (∀ i, (l : ℝ)⁻¹ < ‖v i‖) ∧ Antitone (fun i => ‖v i‖) ∧
      ∀ (c : Fin h → ℚ_[l]) (j : Fin h),
        ‖c j‖ * ‖v j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * v i‖ := by
  obtain ⟨u, huS, hu0, horth⟩ := exists_orthogonal_family_in_span l h μ hμ
  choose t ht0 htlo hthi using fun i => exists_rescale_norm_mem_Ioc l (u i) (hu0 i)
  set w : Fin h → ℂ_[l] := fun i => algebraMap ℚ_[l] ℂ_[l] (t i) * u i with hw_def
  have hworth : ∀ (c : Fin h → ℚ_[l]) (j : Fin h),
      ‖c j‖ * ‖w j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * w i‖ := by
    intro c j
    have := horth (fun i => c i * t i) j
    simp only [hw_def, map_mul, mul_assoc, norm_mul, norm_algebraMap'] at this ⊢
    exact this
  set σ := Tuple.sort (fun i => -‖w i‖)
  refine ⟨fun i => w (σ i), fun i => ?_, fun i => ⟨?_, hthi _⟩, fun i => htlo _, ?_, fun c j => ?_⟩
  · simp only [hw_def]
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (huS _)
  · simp only [hw_def]
    intro h0
    have := congrArg norm h0
    rw [norm_zero] at this
    exact (lt_irrefl (0 : ℝ)) ((inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)).trans
      (this ▸ htlo (σ i)))
  · intro a b hab
    exact neg_le_neg_iff.1 (Tuple.monotone_sort (fun i => -‖w i‖) hab)
  · have := hworth (fun k => c (σ.symm k)) (σ j)
    rw [← Equiv.sum_comp σ] at this
    simpa using this

theorem _root_.GlobalTheory.PMonE.OrthBasis.exists_orthBasis : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), (∀ c : Fin h → ℚ_[l], ∑ j, algebraMap ℚ_[l] ℂ_[l] (c j) * μ j = 0 → c = 0) → ∃ (P : Matrix (Fin h) (Fin h) ℚ_[l]) (μ' : Fin h → ℂ_[l]), P.det ≠ 0 ∧ (∀ i, μ' i = ∑ j, algebraMap ℚ_[l] ℂ_[l] (P i j) * μ j) ∧ (∀ i, μ' i ≠ 0 ∧ ‖μ' i‖ ≤ 1) ∧ Antitone (fun i => ‖μ' i‖) ∧ (∀ i j, ‖μ' i‖ < l * ‖μ' j‖) ∧ ∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖μ' j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * μ' i‖ := by
  intro l _ h μ hind
  classical
  have hμ : LinearIndependent ℚ_[l] μ := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have := hind g (by simpa [Algebra.smul_def] using hg)
    simp [this]
  obtain ⟨v, hvS, hv1, hvlo, hanti, horth⟩ := exists_sorted_orthogonal_family_in_span l h μ hμ
  choose P hP using fun i => (Submodule.mem_span_range_iff_exists_fun ℚ_[l]).1 (hvS i)
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  refine ⟨Matrix.of P, v, ?_, fun i => ?_, hv1, hanti, fun i j => ?_, horth⟩
  · intro hdet
    obtain ⟨w, hw0, hwP⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    have hcol : ∀ j, ∑ i, w i * P i j = 0 := fun j => by
      simpa [Matrix.vecMul, dotProduct] using congrFun hwP j
    have hsum : ∑ i, algebraMap ℚ_[l] ℂ_[l] (w i) * v i = 0 := by
      simp_rw [← Algebra.smul_def, ← hP, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, hcol, zero_smul, Finset.sum_const_zero]
    apply hw0
    funext j
    have h1 := horth w j
    rw [hsum, norm_zero] at h1
    have h2 : 0 < ‖v j‖ := norm_pos_iff.2 (hv1 j).1
    have h3 : ‖w j‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (w j)]) (norm_nonneg _)
    simpa using h3
  · rw [← hP i]
    simp [Algebra.smul_def]
  · calc ‖v i‖ ≤ 1 := (hv1 i).2
      _ = (l : ℝ) * (l : ℝ)⁻¹ := (mul_inv_cancel₀ hlpos.ne').symm
      _ < (l : ℝ) * ‖v j‖ := mul_lt_mul_of_pos_left (hvlo j) hlpos

end GlobalTheory.PMonE.OrthBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSortedNormalizedOrthBasisComplexPAdicStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sorted_normalized_orthBasis_complexPAdic : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), (∀ c : Fin h → ℚ_[l], ∑ j, algebraMap ℚ_[l] ℂ_[l] (c j) * μ j = 0 → c = 0) → ∃ (P : Matrix (Fin h) (Fin h) ℚ_[l]) (μ' : Fin h → ℂ_[l]), P.det ≠ 0 ∧ (∀ i, μ' i = ∑ j, algebraMap ℚ_[l] ℂ_[l] (P i j) * μ j) ∧ (∀ i, μ' i ≠ 0 ∧ ‖μ' i‖ ≤ 1) ∧ Antitone (fun i => ‖μ' i‖) ∧ (∀ i j, ‖μ' i‖ < l * ‖μ' j‖) ∧ ∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖μ' j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * μ' i‖ := by
  first | exact @GlobalTheory.PMonE.OrthBasis.exists_orthBasis | exact GlobalTheory.PMonE.OrthBasis.exists_orthBasis | (intros; apply GlobalTheory.PMonE.OrthBasis.exists_orthBasis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroFrobVectorResidueZero
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMonII

open GlobalTheory.PSer

theorem sh_le_sh_nsmul {l : ℕ} [Fact l.Prime] (y : Formalism.Per.Fl l) (n : ℕ) (hn : ¬ l ∣ n) :
    ‖sh y‖ ≤ ‖sh (n • y)‖ := by
  have hn0 : (n : ZMod l) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  set m := ((n : ZMod l)⁻¹).val with hm
  have hmnZ : ((m * n : ℕ) : ZMod l) = ((1 : ℕ) : ZMod l) := by
    push_cast
    rw [hm, ZMod.natCast_zmod_val, inv_mul_cancel₀ hn0]
  have hmn : ((m * n : ℕ) : Formalism.Per.Fl l) = 1 := by
    rw [← Nat.cast_one, CharP.natCast_eq_natCast (Formalism.Per.Fl l) l]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hmnZ
  have hy : y = (m : Formalism.Per.Fl l) * (n • y) := by
    rw [nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul, hmn, one_mul]
  have hmul : ∀ a b : Formalism.Per.Fl l, sh (a * b) = sh a * sh b := by
    intro a b; simp [sh, map_mul]
  have hle : ∀ x : Formalism.Per.Fl l, ‖sh x‖ ≤ 1 := fun x => (GlobalTheory.RingBasics.mem_OC _).1 (PreTilt.untilt x).2
  calc ‖sh y‖ = ‖sh (m : Formalism.Per.Fl l)‖ * ‖sh (n • y)‖ := by
        conv_lhs => rw [hy]
        rw [hmul, norm_mul]
    _ ≤ 1 * ‖sh (n • y)‖ := mul_le_mul_of_nonneg_right (hle _) (norm_nonneg _)
    _ = ‖sh (n • y)‖ := one_mul _

theorem ev_algebraMap {l : ℕ} [Fact l.Prime] (P : LocPrime l) (m : ℕ) (q : ℚ_[l]) :
    ev P m (algebraMap ℚ_[l] P.R.B q) = algebraMap ℚ_[l] P.R.BdR q := by
  rw [ev, ← AlgHom.coe_pow, AlgHom.commutes, AlgHom.commutes]

end GlobalTheory.PMonII

namespace GlobalTheory.PMonII

open GlobalTheory.PSer

theorem exII : ExII := by
  intro l _ P AI T h hh lam hlam hind
  obtain ⟨S, θ, hS, hker, hQ, hser⟩ := GlobalTheory.T.exists_BcrisPlus_series_with_theta_residues l P AI T
  obtain ⟨-, hPev, hPring, hPq, -, -⟩ := GlobalTheory.PMon.CrisPlus.plus_props l P AI T
  have hθq : ∀ (c : ℚ_[l]) (hm : algebraMap ℚ_[l] P.R.BdR c ∈ S),
      θ ⟨_, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c := by
    intro c hm; obtain ⟨_, h'⟩ := hQ c; exact h'
  have hqS : ∀ c : ℚ_[l], algebraMap ℚ_[l] P.R.BdR c ∈ S := fun c => (hS _).2 (q_mem_Fil P c)
  have hlS : ∀ j, lam j ∈ S := fun j => (hS _).2 (hlam j)
  let μ : Fin h → ℂ_[l] := fun j => θ ⟨lam j, hlS j⟩
  have hμind : ∀ c : Fin h → ℚ_[l], ∑ j, algebraMap ℚ_[l] ℂ_[l] (c j) * μ j = 0 → c = 0 := by
    intro c hc
    apply hind c
    have hm : ∑ j, c j • lam j ∈ S := S.sum_mem fun j _ => by
      rw [Algebra.smul_def]; exact S.mul_mem (hqS _) (hlS j)
    have he : (⟨_, hm⟩ : S) = ∑ j, (⟨_, hqS (c j)⟩ : S) * ⟨lam j, hlS j⟩ := by
      apply Subtype.ext; simp [Algebra.smul_def]
    have h0 : θ ⟨_, hm⟩ = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [he, map_sum, ← hc]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hθq]
    exact (hker ⟨_, hm⟩).1 h0
  obtain ⟨Pm, μ', hdet, hμ', hnorm, hanti, hlt, horth⟩ := GlobalTheory.T.exists_sorted_normalized_orthBasis_complexPAdic l h μ hμind
  obtain ⟨y, j0, r, R, hr0, hr1, hR1, hyR, hyr, hy0, hzero⟩ :=
    GlobalTheory.T.exists_orthogonal_family_residue_zeros l h μ' hh hnorm hanti hlt horth
  have hb : ∀ k : Fin h, ∃ b : P.R.B, Plus T b ∧ P.φB^[h] b = (l : P.R.B) * b ∧
      ∀ j : ℕ, ∃ hm, θ ⟨ev P j b, hm⟩ = abelian₂ h j (y k) :=
    fun k => hser h R (y k) hh hR1 (hyR k)
  choose b hbP hbφ hbθ using hb
  choose hbm hθb using hbθ

  have hbne : b j0 ≠ 0 := by
    intro h0
    have hc := GlobalTheory.T.untiltFrobeniusSeries_linearIndependent_of_firstTerms l h 1 r (fun _ => y j0) hh hr0 hr1 (fun _ k => hyr k) ?_ (fun _ => 1) ?_
    · exact one_ne_zero (congrFun hc 0)
    · intro n hn a
      by_contra hd
      have ha : a = 0 := Subsingleton.elim _ _
      subst ha
      have hle := sh_le_sh_nsmul (y j0 0) (n 0) hd
      simp only [Finset.univ_unique, Finset.sum_singleton] at hn
      have : (default : Fin 1) = 0 := rfl
      rw [this] at hn
      linarith
    · intro j _
      have e : (⟨ev P j (b j0), hbm j0 j⟩ : S) = 0 := Subtype.ext (by
        simp only [h0, ZeroMemClass.coe_zero, ← evHom_apply, map_zero])
      have hL : abelian₂ h j (y j0) = 0 := by rw [← hθb j0 j, e, map_zero]
      simp [hL]
  let a : Fin h → P.R.B := fun j => ∑ k, algebraMap ℚ_[l] P.R.B (Pm k j) * b k
  have hplus0 : Plus T (0 : P.R.B) := by simpa using hPq 0
  have hev : ∀ (i : ℕ) (j : Fin h), ev P i (a j) = ∑ k, algebraMap ℚ_[l] P.R.BdR (Pm k j) * ev P i (b k) := by
    intro i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [a, ← evHom_apply, map_sum, map_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [evHom_apply, evHom_apply, ev_algebraMap]
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  ·
    intro ha
    apply hbne
    have hinv : Pm * Pm⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)
    have key : ∑ j, algebraMap ℚ_[l] P.R.B (Pm⁻¹ j j0) * a j = b j0 := by
      simp only [a, Finset.mul_sum, ← mul_assoc, ← map_mul]
      rw [Finset.sum_comm]
      have : ∀ k, ∑ j, algebraMap ℚ_[l] P.R.B (Pm⁻¹ j j0 * Pm k j) * b k =
          algebraMap ℚ_[l] P.R.B ((Pm * Pm⁻¹) k j0) * b k := by
        intro k
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← Finset.sum_mul, ← map_sum, Matrix.mul_apply]
        simp only [mul_comm]
      simp only [this, hinv, Matrix.one_apply]
      simp
    rw [← key]
    simp [ha]
  · intro j
    refine Finset.sum_induction _ (Plus T) (fun x y hx hy => (hPring x y hx hy).1) hplus0 fun k _ => ?_
    exact (hPring _ _ (hPq _) (hbP k)).2
  · intro j
    simp only [a]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← AlgHom.coe_pow, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, AlgHom.commutes, AlgHom.coe_pow, hbφ k]
    ring
  · intro i
    have hX : ∑ j, lam j * ev P i (a j) ∈ S := S.sum_mem fun j _ => S.mul_mem (hlS j) (by
      rw [hev]; exact S.sum_mem fun k _ => S.mul_mem (hqS _) (hbm k i))
    apply (hker ⟨_, hX⟩).1
    have he : (⟨_, hX⟩ : S) = ∑ j, ∑ k, (⟨lam j, hlS j⟩ : S) * ((⟨_, hqS (Pm k j)⟩ : S) * ⟨_, hbm k i⟩) := by
      apply Subtype.ext
      simp only [hev, Finset.mul_sum]
      simp
    rw [he]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hθq, hθb]
    rw [Finset.sum_comm]
    rw [← hzero i]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hμ' k, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [μ]
    ring

end GlobalTheory.PMonII
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroFrobVectorResidueZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_frobVector_residue_zero : ExII := by
  first | exact @GlobalTheory.PMonII.exII | exact GlobalTheory.PMonII.exII | (intros; apply GlobalTheory.PMonII.exII <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroFrobVectorResidueZeroProof
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exII_holds : ExII := GlobalTheory.T.exists_nonzero_frobVector_residue_zero

end GlobalTheory.PMon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroFrobVectorResidueZeroProofStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsNonzeroFrobVectorResidueZero_proof : ExII := by
  first | exact @GlobalTheory.PMon.exII_holds | exact GlobalTheory.PMon.exII_holds | (intros; apply GlobalTheory.PMon.exII_holds <;> assumption)
end
