module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsJumpMultiset

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLPowIHatToHatSSubDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLPowIHatToHatSSubDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology

section Bounded

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (e : ℕ) [NeZero e]


omit [IsUnitBall O K] in
theorem norm_tail_mul_rad_le {f : K⟦X⟧} {b : ℝ} (hb : 0 ≤ b)
    (hf : ∀ n, ‖coeff n f‖ * rad l (1 / e) ^ n ≤ b) (n : ℕ) :
    ‖tail l e f n‖ * rad l (1 / e) ^ n ≤ b := by
  have hρ := pow_pos (rad_pos l (1 / e)) n
  rw [← le_div_iff₀ hρ]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (div_nonneg hb hρ.le) fun j => ?_
  rw [le_div_iff₀ hρ, norm_term_eq]
  exact hf _

theorem coeff_sub_E_mul_quotE_of_lt [CompleteSpace K] {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) {n : ℕ}
    (hn : n < e) : coeff n (f - E K l e * quotE l e f) = tail l e f n := by
  rw [tail_rec l e hf n, map_sub, E, add_mul, map_add (f := _), coeff_X_pow_mul', if_neg (by omega),
    ← map_natCast (C : K →+* K⟦X⟧) l, coeff_C_mul, quotE, coeff_mk]
  ring

theorem norm_coeff_mul_rad_le_of_mem_S {f : K⟦X⟧} (hf : f ∈ S O K e) (n : ℕ) :
    ‖coeff n f‖ * rad l (1 / e) ^ n ≤ 1 := by
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (hf.1 n)
  refine le_trans ?_ (norm_pow_le_norm_factorial (K := K) l (n / e))
  rw [← rad_pow (K := K) l e, ← pow_mul]
  exact pow_le_pow_of_le_one (rad_nonneg _ _) (rad_le_one l (by positivity)) (Nat.mul_div_le n e)

theorem exists_bdd_div_E_pow [CompleteSpace K] (m : ℕ) {f : K⟦X⟧} (hf : f ∈ Rpi O K l e)
    {b : ℝ} (hb : 0 ≤ b) (hfb : ∀ n, ‖coeff n f‖ * rad l (1 / e) ^ n ≤ b) :
    ∃ g : K⟦X⟧, (∀ n, ‖coeff n g‖ ≤ b * ‖(l : K)‖⁻¹ ^ m) ∧
      ∃ h ∈ Rpi O K l e, f = g + E K l e ^ m * h := by
  induction m generalizing f b with
  | zero => exact ⟨0, fun n => by simpa using hb, f, hf, by simp⟩
  | succ m ih =>
    have hl0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
    have hl1 : ‖(l : K)‖ < 1 := norm_l_lt_one l
    have hρe : rad l (1 / e) ^ e = ‖(l : K)‖ := rad_pow l e
    have hρ0 : 0 < rad l (1 / e) := rad_pos l _
    have hρ1 : rad l (1 / e) ≤ 1 := rad_le_one l (by positivity)
    have htail := norm_tail_mul_rad_le l e hb hfb
    have hq : ∀ n, ‖coeff n (quotE l e f)‖ * rad l (1 / e) ^ n ≤ b * ‖(l : K)‖⁻¹ := fun n => by
      have := htail (n + e)
      rw [pow_add, hρe] at this
      rw [quotE, coeff_mk, le_mul_inv_iff₀ hl0]
      simpa [mul_assoc] using this
    obtain ⟨g1, hg1, h1, hh1, hq1⟩ :=
      ih (quotE_mem_Rpi l e hf) (mul_nonneg hb (inv_nonneg.2 hl0.le)) hq
    have hpow : ‖(l : K)‖⁻¹ ≤ ‖(l : K)‖⁻¹ ^ (m + 1) := by
      simpa using pow_le_pow_right₀ (one_le_inv₀ hl0 |>.2 hl1.le) (Nat.succ_le_succ (Nat.zero_le m))
    refine ⟨(f - E K l e * quotE l e f) + E K l e * g1, fun n => ?_, h1, hh1, ?_⟩
    · rw [map_add (f := _)]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rcases lt_or_ge n e with hn | hn
        · rw [coeff_sub_E_mul_quotE_of_lt l e hf hn]
          have h2 := htail n
          have h3 : ‖(l : K)‖ ≤ rad l (1 / e) ^ n := by
            rw [← hρe]; exact pow_le_pow_of_le_one hρ0.le hρ1 hn.le
          have h4 : ‖tail l e f n‖ ≤ b * ‖(l : K)‖⁻¹ := by
            rw [le_mul_inv_iff₀ hl0]
            exact (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)).trans h2
          exact h4.trans (mul_le_mul_of_nonneg_left hpow hb)
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
          rw [coeff_sub_E_mul_quotE l e hf, norm_zero]
          positivity
      · have hE : ∀ n, ‖coeff n (E K l e)‖ * (1 : ℝ) ≤ 1 := fun n => by
          simpa using (E_mem l e (A O K)) n
        have := norm_coeff_mul_le (w := fun _ => (1 : ℝ)) (fun _ => zero_le_one)
          (fun _ _ => by simp) (a := 1) (b := b * ‖(l : K)‖⁻¹ * ‖(l : K)‖⁻¹ ^ m) zero_le_one
          (by positivity) hE (g := g1) (fun n => by rw [mul_one]; exact hg1 n) n
        have e' : (1 : ℝ) * (b * ‖(l : K)‖⁻¹ * ‖(l : K)‖⁻¹ ^ m) = b * ‖(l : K)‖⁻¹ ^ (m + 1) := by
          ring
        rw [mul_one, e'] at this
        exact this
    · linear_combination E K l e * hq1

end Bounded

end GlobalTheory.BK

namespace GlobalTheory.BKReal

open PowerSeries GlobalTheory.BK

theorem exists_l_pow_iHat_toHatS_sub_dvd (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e)
    [CompleteSpace K] (m : ℕ) (s : S O K e) :
    ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣
      (l : OD l O) ^ m * ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) -
        toOD l O y := by
  obtain ⟨g, hg, h, hh, hs⟩ := exists_bdd_div_E_pow l e m (S_le_R l e s.2) zero_le_one
    (norm_coeff_mul_rad_le_of_mem_S l e s.2)
  have hl0 : ‖(l : K)‖ ≠ 0 := norm_ne_zero_iff.2 (GlobalTheory.BK.l_ne_zero (K := K) l)
  have hG : C ((l : K) ^ m) * g ∈ A O K := fun n => by
    rw [coeff_C_mul, norm_mul, norm_pow]
    calc _ ≤ ‖(l : K)‖ ^ m * (1 * ‖(l : K)‖⁻¹ ^ m) := by gcongr; exact hg n
      _ = 1 := by rw [one_mul, ← mul_pow, mul_inv_cancel₀ hl0, one_pow]
  have hH : C ((l : K) ^ m) * h ∈ Rpi O K l e := mul_mem (HasK.C_mem _) hh
  have key : (l : Rpi O K l e) ^ m * Subalgebra.inclusion (invL_S_le_Rpi l e)
      (algebraMap (S O K e) (invL l (S O K e)) s) =
      ⟨_, A_le_Rpi l e hG⟩ + EIn l e (Rpi O K l e) ^ m * ⟨_, hH⟩ := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_pow, SubringClass.coe_natCast,
      Subalgebra.coe_inclusion, coe_algebraMap_away, coe_EIn, map_pow, map_natCast]
    rw [hs]
    ring
  have e1 : ϖ.iHat O K (toHat O K l e ⟨_, A_le_Rpi l e hG⟩) = toOD l O (ϖ.iA O K ⟨_, hG⟩) :=
    (congrArg (ϖ.iHat O K)
      (toHat_eq_ofAl l e (g := algebraMap (A O K) (invL l (A O K)) ⟨_, hG⟩) rfl)).trans
      (ϖ.iHat_ofA O K _)
  have e2 : ϖ.iHat O K (Ehat O K l e) = ϖ.iAl O K (EIn l e _) := ϖ.iHat_ofAl O K _
  have h1 : (l : OD l O) ^ m *
      ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) =
      ϖ.iHat O K (toHat O K l e ((l : Rpi O K l e) ^ m * Subalgebra.inclusion (invL_S_le_Rpi l e)
        (algebraMap (S O K e) (invL l (S O K e)) s))) := by
    simp only [map_mul, map_pow, map_natCast]
    rfl
  refine ⟨ϖ.iA O K ⟨_, hG⟩, ϖ.iHat O K (toHat O K l e ⟨_, hH⟩), ?_⟩
  rw [h1, key]
  rw [map_add (toHat O K l e), map_add (ϖ.iHat O K), map_mul (toHat O K l e), map_mul (ϖ.iHat O K),
    map_pow (toHat O K l e), map_pow (ϖ.iHat O K), toHat_E, e1, e2]
  ring

end GlobalTheory.BKReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLPowIHatToHatSSubDvdStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_iHat_toHatS_sub_toOD_dvd : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) [CompleteSpace K] (m : ℕ) (s : S O K e), ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣ (l : OD l O) ^ m * ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) - toOD l O y := by
  first | exact @GlobalTheory.BKReal.exists_l_pow_iHat_toHatS_sub_dvd | exact GlobalTheory.BKReal.exists_l_pow_iHat_toHatS_sub_dvd | (intros; apply GlobalTheory.BKReal.exists_l_pow_iHat_toHatS_sub_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoversOfAction
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CoverBridge

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a]

theorem galF_val {k : GQ l} {s : ℕ} (hk : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ s) (z : Fq l a) :
    Per.σF k (Fq.val l a z) = Fq.val l a z ^ l ^ s := by
  obtain ⟨z₀, ω, hω, hz, h⟩ := exists_gen l a
  have h1 := one_lt_pow_l l a
  have hω' : k ω = ω ^ l ^ s := hk ω (by
    rw [← Nat.sub_add_cancel h1.le, pow_succ, hω.pow_eq_one, one_mul])
  have hd : ¬ l ∣ l ^ a - 1 := fun h => hl.out.not_dvd_one
    ((Nat.dvd_sub_iff_right h1.le (dvd_pow_self l (NeZero.ne a))).1 h)
  have h2 : Per.σF k (Fq.val l a z₀) = Fq.val l a z₀ ^ l ^ s := by
    refine GlobalTheory.UnramIdem.tilt_pow (k := l ^ s) hd dvd_rfl hz fun n => ?_
    obtain ⟨y, y1, y2, y3⟩ := hz n
    refine ⟨Per.σO k y, ?_, by rw [← map_pow, y2, map_one], ?_⟩
    · rw [GlobalTheory.RingIface.sigO_coe l, ← map_pow, y1, GlobalTheory.RingBasics.σC_coe, hω']
    · exact GlobalTheory.AdicMaps.coeff_galois l k _ n y y3
  rcases eq_or_ne z 0 with h0 | h0
  · rw [h0, map_zero, map_zero, zero_pow (pow_pos hl.out.pos s).ne']
  · obtain ⟨j, rfl⟩ := h z h0
    rw [map_pow, map_pow, h2, ← pow_mul, ← pow_mul, mul_comm]

theorem galA_wA {k : GQ l} {s : ℕ} (hk : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ s) (w : Wq l a) :
    Per.σA k (wA l a w) = wA l a ((sigma l a ^ s) w) := by
  refine WittVector.ext fun n => ?_
  refine (GlobalTheory.RingIface.sigA_coeff l k _ n).trans ?_
  change Per.σF k (Fq.val l a (w.coeff n)) = Fq.val l a (((sigma l a ^ s) w).coeff n)
  rw [coeff_sigma_pow, map_pow, galF_val hk]

variable {e : ℕ} [NeZero e]

theorem isTiltOf_kummer (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) {ζ : Om l}
    (hζ : k (ϖ.seq 0) = ζ * ϖ.seq 0) : IsTiltOf ζ e (ϖ.kummer k) := by
  have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk
  intro n
  refine ⟨ϖ.ratio k n, ?_, ?_, ϖ.coeff_kummer k n⟩
  · rw [PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow, ϖ.seq_pow, hζ,
      mul_div_cancel_right₀ _ (ϖ.seq_ne_zero 0)]
    rfl
  · refine Subtype.ext ?_
    rw [SubmonoidClass.coe_pow, PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow,
      hfix _ (IntermediateField.subset_adjoin _ _ ⟨n, rfl⟩), div_self (pow_ne_zero _ (ϖ.seq_ne_zero n)),
      map_one]
    rfl

theorem emb_sigma_pow {O : Type} [CommRing O] [Algebra ℤ_[l] O] (t : Wq l a →ₐ[ℤ_[l]] O) (n : ℕ)
    (τ : ZMod a) (w : Wq l a) : emb t τ ((sigma l a ^ n) w) = emb t (τ - n) w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, AlgEquiv.mul_apply, ih, emb_sigma]
    congr 1
    push_cast
    ring

theorem kummer_mem_resSub (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) {ζ : Om l}
    (hζ : k (ϖ.seq 0) = ζ * ϖ.seq 0) (he : e + 1 = l ^ a) : ϖ.kummer k ∈ resSub l a := by
  rw [mem_resSub, ← he, pow_succ, GlobalTheory.MemLoc.IsTiltOf.pow_eq_one (isTiltOf_kummer ϖ hk hζ), one_mul]

theorem galA_ev (ϖ : PiSys l e) {k : GQ l} {s : ℕ} (hk : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ s)
    (z : Fq l a) (hz : Fq.val l a z = ϖ.kummer k) (x : (Wq l a)⟦X⟧) :
    Per.σA k (ϖ.ev a x) = ϖ.ev a (rescale (WittVector.teichmuller l z)
      (PowerSeries.map ((sigma l a ^ s : Wq l a ≃ₐ[ℤ_[l]] Wq l a) : Wq l a →+* Wq l a) x)) := by
  refine RingHom.congr_fun (ringHom_ext_of_sep ((Per.σA k).comp (ϖ.ev a))
    ((ϖ.ev a).comp ((rescale (WittVector.teichmuller l z)).comp
      (PowerSeries.map ((sigma l a ^ s : Wq l a ≃ₐ[ℤ_[l]] Wq l a) : Wq l a →+* Wq l a)))) (fun w => ?_) ?_
    fun y hy => ϖ.sep_teich y fun n => ?_) x
  · simp only [RingHom.comp_apply, PiSys.ev_C, galA_wA hk, map_C]
    have : rescale (WittVector.teichmuller l z) (C ((sigma l a ^ s) w)) = C ((sigma l a ^ s) w) := by
      refine PowerSeries.ext fun m => ?_
      rw [coeff_rescale, coeff_C]
      split_ifs with h
      · rw [h, pow_zero, one_mul]
      · rw [mul_zero]
    rw [RingHom.coe_coe, this, PiSys.ev_C]
  · simp only [RingHom.comp_apply, PiSys.ev_X, map_X, rescale_X, map_mul, PiSys.ev_C, PiSys.gal_teich,
      PiSys.mu, wA_teich, hz, add_sub_cancel]
  · refine Dvd.dvd.trans ?_ (hy n)
    simp only [RingHom.comp_apply, PiSys.ev_X, PiSys.gal_teich, mul_pow]
    exact dvd_mul_left _ _

theorem thetaW_teich (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) (LL : FinExt l) [HasUnr a LL]
    {ζ : ↥LL.1} (hζ : k (ϖ.seq 0) = (ζ : Om l) * ϖ.seq 0) (z : Fq l a) (hz : Fq.val l a z = ϖ.kummer k) :
    ((thetaW a LL (WittVector.teichmuller l z) : ↥(OL LL)) : ↥LL.1) = ζ := by
  refine Subtype.ext ((algebraMap (Om l) ℂ_[l]).injective ?_)
  have h1 := congrArg (fun y : OC l => (y : ℂ_[l])) (intToOC_thetaW a LL (WittVector.teichmuller l z))
  simp only [coe_intToOC, wA_teich, WittVector.fontaineTheta_teichmuller, hz] at h1
  exact h1.trans (GlobalTheory.MemLoc.IsTiltOf.untilt_eq (isTiltOf_kummer ϖ hk hζ))

theorem toAc_rescale {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]
    (t : Wq l a →ₐ[ℤ_[l]] O) (γ : TameGal K l e a) (c : Wq l a)
    (hc : ∀ τ, algebraMap O K (emb t τ c) = γ.root τ) (x : (Wq l a)⟦X⟧) (τ : ZMod a) :
    (toAc t K (rescale c (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) :
      Wq l a →+* Wq l a) x)) τ : K⟦X⟧) = ringAct γ (fun σ => (toAc t K x σ : K⟦X⟧)) τ := by
  refine PowerSeries.ext fun n => ?_
  rw [ringAct_apply, coeff_rescale, coeff_toAc, coeff_toAc, coeff_rescale, coeff_map, map_mul, map_pow,
    map_mul, map_pow, hc]
  congr 2
  rw [RingHom.coe_coe, emb_sigma_pow, ZMod.natCast_zmod_val]

theorem algebraMap_emb_teich (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) (LL : FinExt l) [HasUnr a LL]
    [TameDescentExponentData ↥LL.1 l e a] (γ : TameGal ↥LL.1 l e a)
    (hζ : k (ϖ.seq 0) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0) (z : Fq l a)
    (hz : Fq.val l a z = ϖ.kummer k) (τ : ZMod a) :
    algebraMap ↥(OL LL) ↥LL.1 (emb (thetaW a LL) τ (WittVector.teichmuller l z)) = γ.root τ := by
  change ((thetaW a LL ((sigma l a ^ (-τ).val) (WittVector.teichmuller l z)) : ↥(OL LL)) : ↥LL.1) = _
  rw [sigma_pow_teich, map_pow, SubmonoidClass.coe_pow, thetaW_teich ϖ hk LL hζ z hz, TameGal.root, powL_apply]
  simp

theorem covers_of_root {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (γ : TameGal K l e a) {k : GQ l}
    (hunr : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ γ.shift.val) (z : Fq l a) (hz : Fq.val l a z = ϖ.kummer k)
    (hroot : ∀ τ, algebraMap O K (emb t τ (WittVector.teichmuller l z)) = γ.root τ) : Covers K t ϖ k γ := by
  intro f f' hf'
  obtain ⟨x, rfl⟩ := exists_eq_sum_toAc t K (Module.Free.chooseBasis ℤ_[l] O) f
  set o := Module.Free.chooseBasis ℤ_[l] O
  have hf : f' = ∑ j, o j • toAc t K (rescale (WittVector.teichmuller l z)
      (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) : Wq l a →+* Wq l a) (x j))) := by
    funext τ
    refine Subtype.ext ?_
    rw [hf' τ]
    have h1 : (fun σ => (((∑ j, o j • toAc t K (x j)) σ : A O K) : K⟦X⟧)) =
        ∑ j, algebraMap O K (o j) • (fun σ => (toAc t K (x j) σ : K⟦X⟧)) := by
      funext σ
      simp [Finset.sum_apply, algebraMap_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply]
    simp [algebraMap_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [toAc_rescale t γ _ hroot]
  subst hf
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, PiSys.iTot_toAc, galOA_tmul, galA_ev ϖ hunr z hz]

end GlobalTheory.BKGal.CoverBridge


open GlobalTheory.BKGal.CoverBridge in
theorem GlobalTheory.BKGal.covers_of_action : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e)
    (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (γ : TameGal ↥LL.1 l e a), ∀ k ∈ ϖ.GKinf,
    (∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ γ.shift.val) →
    k (ϖ.seq 0) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 → Covers ↥LL.1 (thetaW a LL) ϖ k γ := by
  intro l _ a e _ _ ϖ LL _ _ γ k hk hunr hζ
  have hmem := kummer_mem_resSub ϖ hk hζ (TameDescentExponentData.succ_eq (K := ↥LL.1) (l := l) (e := e) (a := a))
  exact covers_of_root (thetaW a LL) ϖ γ hunr ⟨ϖ.kummer k, hmem⟩ rfl
    (algebraMap_emb_teich ϖ hk LL γ hζ ⟨ϖ.kummer k, hmem⟩ rfl)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedCharacter
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

noncomputable section
namespace GlobalTheory.UnramZl
open GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws

theorem modEq_of_pow_modEq {l d : ℕ} (hl : 1 < l) (hd : 0 < d) {a b : ℕ}
    (h : l ^ a ≡ l ^ b [MOD l ^ d - 1]) : a ≡ b [MOD d] := by
  wlog hab : a ≤ b generalizing a b
  · exact (this h.symm (le_of_not_ge hab)).symm
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  have h1 : l ^ d - 1 ∣ l ^ (a + c) - l ^ a :=
    (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right hl.le hab)).1 h
  rw [pow_add, ← Nat.mul_sub_one] at h1
  have hcop : (l ^ d - 1).Coprime (l ^ a) := by
    apply Nat.Coprime.pow_right
    have h2 : (l ^ d - 1).Coprime (l ^ d) := by
      have : l ^ d = (l ^ d - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm
      conv_rhs => rw [this]
      simp
    exact h2.coprime_dvd_right (dvd_pow_self l hd.ne')
  have h3 := Nat.gcd_eq_left (hcop.dvd_of_dvd_mul_left h1)
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at h3
  have h4 : l ^ d.gcd c = l ^ d := by
    have := Nat.one_le_pow (d.gcd c) l (by omega)
    have := Nat.one_le_pow d l (by omega)
    omega
  have h5 : d ∣ c := (Nat.pow_right_injective hl h4) ▸ Nat.gcd_dvd_right d c
  exact (Nat.modEq_iff_dvd' hab).2 (by simpa using h5)

variable {l : ℕ} [hl : Fact l.Prime]

theorem lev_pos (n : ℕ) : 0 < l ^ (l ^ n) - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow (pow_pos hl.out.pos n).ne' hl.out.one_lt)

theorem not_dvd_lev (n : ℕ) : ¬ l ∣ l ^ (l ^ n) - 1 := fun h => by
  have h1 : l ∣ l ^ (l ^ n) := dvd_pow_self l (pow_pos hl.out.pos n).ne'
  have h2 := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hl.out.pos)] at h2
  exact hl.out.not_dvd_one h2

def Acts (g : GQ l) (n a : ℕ) : Prop :=
  ∀ ζ : Om l, ζ ^ (l ^ (l ^ n) - 1) = 1 → g ζ = ζ ^ (l ^ a)

theorem exists_prim (n : ℕ) : ∃ ξ : Om l, IsPrimitiveRoot ξ (l ^ (l ^ n) - 1) := by
  haveI : NeZero (l ^ (l ^ n) - 1) := ⟨(lev_pos n).ne'⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) _

theorem Acts.uniq {g : GQ l} {n a b : ℕ} (ha : Acts g n a) (hb : Acts g n b) :
    a ≡ b [MOD l ^ n] := by
  obtain ⟨ξ, hξ⟩ := exists_prim (l := l) n
  have h := (ha ξ hξ.pow_eq_one).symm.trans (hb ξ hξ.pow_eq_one)
  rw [(hξ.isOfFinOrder (lev_pos n).ne').pow_eq_pow_iff_modEq, ← hξ.eq_orderOf] at h
  exact modEq_of_pow_modEq hl.out.one_lt (pow_pos hl.out.pos n) h

theorem Acts.down {g : GQ l} {n a : ℕ} (ha : Acts g (n + 1) a) : Acts g n a := fun ζ hζ => by
  obtain ⟨c, hc⟩ := Nat.pow_sub_one_dvd_pow_sub_one l (pow_dvd_pow l (Nat.le_succ n))
  exact ha ζ (by rw [hc, pow_mul, hζ, one_pow])

theorem Acts.mul {g h : GQ l} {n a b : ℕ} (ha : Acts g n a) (hb : Acts h n b) :
    Acts (g * h) n (a + b) := fun ζ hζ => by
  rw [AlgEquiv.mul_apply, hb ζ hζ, map_pow, ha ζ hζ, ← pow_mul, pow_add]

theorem exists_acts (g : GQ l) (n : ℕ) : ∃ a, Acts g n a :=
  gal_root g (lev_pos n) (not_dvd_lev n)

theorem exists_deg (g : GQ l) :
    ∃ x : ℤ_[l], ∀ n a, Acts g n a → PadicInt.toZModPow n x = (a : ZMod (l ^ n)) := by
  choose a ha using exists_acts g
  have hdv : ∀ i, (l : ℤ) ^ i ∣ (a (i + 1) : ℤ) - a i := fun i => by
    have := ((ha i).uniq (ha (i + 1)).down).dvd
    exact_mod_cast this
  refine ⟨PadicInt.ofIntSeq _
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => (a n : ℤ)) l hdv), fun n b hb => ?_⟩
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => (a n : ℤ)) l hdv n, Int.cast_natCast]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 ((ha n).uniq hb)

def deg (g : GQ l) : ℤ_[l] := (exists_deg g).choose

theorem deg_spec {g : GQ l} {n a : ℕ} (h : Acts g n a) :
    PadicInt.toZModPow n (deg g) = (a : ZMod (l ^ n)) := (exists_deg g).choose_spec n a h

theorem deg_mul (g h : GQ l) : deg (g * h) = deg g + deg h := by
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  obtain ⟨a, ha⟩ := exists_acts g n
  obtain ⟨b, hb⟩ := exists_acts h n
  rw [map_add (f := _), deg_spec ha, deg_spec hb, deg_spec (ha.mul hb), Nat.cast_add]

theorem deg_eq_nat {g : GQ l} {a : ℕ} (h : ∀ n, Acts g n a) : deg g = a := by
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  rw [deg_spec (h n), map_natCast]

theorem deg_one : deg (1 : GQ l) = 0 := by
  simpa using deg_eq_nat (g := (1 : GQ l)) (a := 0) fun n ζ _ => by simp

theorem deg_pow (g : GQ l) (N : ℕ) : deg (g ^ N) = N * deg g := by
  induction N with
  | zero => simp [deg_one]
  | succ N ih => rw [pow_succ, deg_mul, ih]; push_cast; ring

theorem continuous_deg : Continuous (deg : GQ l → ℤ_[l]) := by
  refine continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt l hε
  obtain ⟨ξ, hξ⟩ := exists_prim (l := l) n
  haveI : NeZero (l ^ (l ^ n) - 1) := ⟨(lev_pos n).ne'⟩
  have ho := (stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) ξ).preimage (continuous_const_mul g⁻¹)
  filter_upwards [ho.mem_nhds (show g⁻¹ * g ∈ MulAction.stabilizer (GQ l) ξ by simp)] with h hh
  have h1 : (g⁻¹ * h) ξ = ξ := hh
  have h2 : h ξ = g ξ := by
    conv_rhs => rw [← h1, ← AlgEquiv.mul_apply, mul_inv_cancel_left]
  obtain ⟨a, ha⟩ := exists_acts g n
  have hb : Acts h n a := fun ζ hζ => by
    rw [← ha ζ hζ]
    obtain ⟨i, -, rfl⟩ := hξ.eq_pow_of_pow_eq_one hζ
    rw [map_pow, map_pow, h2]
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ hn
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    deg_spec ha, deg_spec hb, sub_self]

theorem deg_inertia {g : GQ l} (h : ∀ x : Om l, ‖x‖ ≤ 1 → ‖g x - x‖ < 1) : deg g = 0 := by
  simpa using deg_eq_nat (g := g) (a := 0) fun n ζ hζ => by
    let a : OO l := ⟨ζ, (norm_root (lev_pos n) hζ).le⟩
    have ha : a ^ (l ^ (l ^ n) - 1) = 1 := Subtype.ext hζ
    have := res_inj (lev_pos n) (not_dvd_lev n) (a := galO g a) (b := a)
      (by rw [← map_pow, ha, map_one]) ha ((res_eq_iff _ _).2 (h ζ a.2))
    rw [pow_zero, pow_one]
    exact congrArg Subtype.val this

theorem exists_deg_eq_one : ∃ g : GQ l, deg g = 1 := by
  obtain ⟨σ, hσ⟩ := exists_frobenius_Kur l
  obtain ⟨g, hg⟩ := exists_ext σ
  refine ⟨g, ?_⟩
  simpa using deg_eq_nat (g := g) (a := 1) fun n ζ hζ => by
    let c : ↥(MaximalUnramifiedExtension l) :=
      ⟨ζ, IntermediateField.subset_adjoin _ _ ⟨_, lev_pos n, not_dvd_lev n, hζ⟩⟩
    have := hσ c _ (lev_pos n) (not_dvd_lev n) (Subtype.ext hζ)
    rw [show ζ = (c : Om l) from rfl, hg, this, pow_one]; rfl

theorem exists_unramified_character : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l),
    ∃ δ : ↥(GK K) → ℚ_[l], Continuous δ ∧ (∀ g h, δ (g * h) = δ g + δ h) ∧
      (∀ g ∈ IK K, δ g = 0) ∧ ∃ g, δ g ≠ 0 := by
  intro l _ K
  refine ⟨fun g => (deg (g : GQ l) : ℚ_[l]),
    continuous_subtype_val.comp (continuous_deg.comp continuous_subtype_val),
    fun g h => by simp [deg_mul], fun g hg => ?_, ?_⟩
  · have : deg (g : GQ l) = 0 := by
      unfold IK at hg
      induction hg using Subgroup.closure_induction with
      | mem x hx => exact deg_inertia hx
      | one => exact deg_one
      | mul x y _ _ hx hy => rw [Subgroup.coe_mul, deg_mul, hx, hy, add_zero]
      | inv x _ hx =>
        have := deg_mul ((x⁻¹ : ↥(GK K)) : GQ l) x
        rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, deg_one, hx, add_zero] at this
        exact this.symm
    simp [this]
  · obtain ⟨φ, hφ⟩ := exists_deg_eq_one (l := l)
    haveI := K.2
    haveI : Finite (GQ l ⧸ GK K) :=
      Subgroup.quotient_finite_of_isOpen _ (IntermediateField.fixingSubgroup_isOpen K.1)
    obtain ⟨N, hN, -, hm⟩ := (GK K).exists_pow_mem_of_index_ne_zero Subgroup.index_ne_zero_of_finite φ
    refine ⟨⟨φ ^ N, hm⟩, ?_⟩
    simp [deg_pow, hφ, hN.ne']

end GlobalTheory.UnramZl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetGenericSumMemHeckeAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetGenericSumMemHeckeAlgebra
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

theorem charpoly_coeff_mem_of_charPolyIn {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ}
    (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)) (h : CharPolyIn T rep) (g : Γ) (j : ℕ) :
    (fun x => (mat (rep x) g).charpoly.coeff j) ∈ T := by
  unfold CharPolyIn at h
  rcases subsingleton_or_nontrivial O with hO | hO
  · have hz : (fun x => (mat (rep x) g).charpoly.coeff j) = 0 := Subsingleton.elim _ _
    rw [hz]
    exact T.zero_mem
  · by_cases hj : j ≤ n
    · have e : (fun x => (mat (rep x) g).charpoly.coeff j) =
          fun x => (mat (rep x) g).charpolyRev.coeff (n - j) := by
        funext x
        rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
          Fintype.card_fin, Polynomial.revAt_le (Nat.sub_le n j), Nat.sub_sub_self hj]
      rw [e]
      exact h g (n - j)
    · have hz : (fun x => (mat (rep x) g).charpoly.coeff j) = 0 := by
        funext x
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
        omega
      rw [hz]
      exact T.zero_mem

private theorem coeff_det_generic_sum_eval {X O : Type} [CommRing O] {n m : ℕ}
    (a : Fin m → X → Matrix (Fin n) (Fin n) O) (x : X) (d : Fin m →₀ ℕ) :
    AddMonoidAlgebra.coeff (Matrix.det (∑ k,
      (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d =
    (AddMonoidAlgebra.coeff (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
      Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j)))) d : X → O) x := by
  set φ : MvPolynomial (Fin m) (X → O) →+* MvPolynomial (Fin m) O :=
    MvPolynomial.map (Pi.evalRingHom (fun _ => O) x) with hφ
  have h1 : φ.mapMatrix (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
      Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j))) =
      ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Matrix.ext fun i j => ?_
    simp [hφ]
  rw [← h1, ← RingHom.map_det, hφ, MvPolynomial.coeff_map]
  rfl

theorem coeff_det_generic_sum_mem_of_inRing :
    ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O))
      (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep →
      ∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, InRing T rep (a k)) →
      ∀ d : Fin m →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det (∑ k,
        (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d) ∈ T := by
  intro Γ X O _ _ n T rep hT m a ha d
  classical

  let T' : Subring (MvPolynomial (Fin m) (X → O)) := (MvPolynomial.map T.val.toRingHom).range
  have hmemT : ∀ p ∈ T', ∀ e, AddMonoidAlgebra.coeff p e ∈ T := by
    intro p hp e
    obtain ⟨q, rfl⟩ := RingHom.mem_range.1 hp
    rw [MvPolynomial.coeff_map]
    exact (AddMonoidAlgebra.coeff q e).2
  have hC : ∀ f ∈ T, (MvPolynomial.C f : MvPolynomial (Fin m) (X → O)) ∈ T' := fun f hf =>
    RingHom.mem_range.2 ⟨MvPolynomial.C ⟨f, hf⟩, by simp⟩
  have hX : ∀ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) ∈ T' := fun k =>
    RingHom.mem_range.2 ⟨MvPolynomial.X k, by simp⟩

  let M : Γ → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O)) :=
    fun h => Matrix.of fun i j => MvPolynomial.C (fun y => mat (rep y) h i j)
  have hmul : ∀ A ∈ Set.range M, ∀ B ∈ Set.range M, A * B ∈ Set.range M := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
    refine ⟨g * h, ?_⟩
    refine Matrix.ext fun i j => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [M, Matrix.mul_apply, Matrix.of_apply, ← map_mul, ← map_sum]
    congr 1
    funext y
    simp [mat, Matrix.mul_apply, Finset.sum_apply]
  have hchar : ∀ A ∈ Set.range M, ∀ j, A.charpoly.coeff j ∈ T' := by
    rintro _ ⟨h, rfl⟩ j
    have hP : M h = (Matrix.of fun i j => fun y => mat (rep y) h i j).map MvPolynomial.C := by
      refine Matrix.ext fun i j => ?_
      rfl
    rw [hP, Matrix.charpoly_map, Polynomial.coeff_map]
    apply hC
    have e : (Matrix.of fun i j => fun y => mat (rep y) h i j).charpoly.coeff j =
        fun y => (mat (rep y) h).charpoly.coeff j := by
      funext y
      have hm : (Matrix.of fun i j => fun y => mat (rep y) h i j).map (Pi.evalRingHom (fun _ => O) y) =
          mat (rep y) h := by
        refine Matrix.ext fun i j => ?_
        rfl
      have e' := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p j)
        (Matrix.charpoly_map (Matrix.of fun i j => fun y => mat (rep y) h i j) (Pi.evalRingHom (fun _ => O) y))
      rw [hm] at e'
      simp only [Polynomial.coeff_map] at e'
      exact e'.symm
    rw [e]
    exact charpoly_coeff_mem_of_charPolyIn T rep hT h j

  have hlift : ∀ b : X → Matrix (Fin n) (Fin n) O, b ∈ Submodule.span O (gens T rep) →
      (Matrix.of fun i j => MvPolynomial.C (fun y => b y i j) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O)))
        ∈ Submodule.span T' (Set.range M) := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨f, hf, h, rfl⟩ := hb
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (fun x => f x • mat (rep x) h) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) =
          (⟨MvPolynomial.C f, hC f hf⟩ : T') • M h := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Subring.smul_def, Matrix.smul_apply, smul_eq_mul, M, ← map_mul]
        congr 1
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)
    | zero =>
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (0 : X → Matrix (Fin n) (Fin n) O) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) = 0 := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Pi.zero_apply, Matrix.zero_apply]
        exact map_zero _
      rw [e]
      exact Submodule.zero_mem _
    | add b c _ _ hb hc =>
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (b + c) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) =
          Matrix.of (fun i j => MvPolynomial.C (fun y => b y i j)) +
            Matrix.of (fun i j => MvPolynomial.C (fun y => c y i j)) := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Matrix.add_apply, ← map_add (f := _)]
        rfl
      rw [e]
      exact Submodule.add_mem _ hb hc
    | smul r b _ hb =>
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (r • b) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) =
          (⟨MvPolynomial.C (algebraMap O (X → O) r), hC _ (T.algebraMap_mem r)⟩ : T') •
            Matrix.of (fun i j => MvPolynomial.C (fun y => b y i j)) := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Subring.smul_def, Matrix.smul_apply, smul_eq_mul, ← map_mul]
        congr 1
      rw [e]
      exact Submodule.smul_mem _ _ hb
  have hB : (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
      Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j))) ∈ Submodule.span T' (Set.range M) := by
    refine Submodule.sum_mem _ fun k _ => ?_
    have := Submodule.smul_mem (Submodule.span T' (Set.range M)) (⟨MvPolynomial.X k, hX k⟩ : T')
      (hlift (a k) ((inRing_iff_mem_span T rep (a k)).1 (ha k)))
    exact this
  obtain ⟨N, f, g, hfg⟩ := Submodule.mem_span_set'.1 hB
  have hdet := Amitsur.det_sum_smul_mem T' (Set.range M) hmul hchar Finset.univ
    (fun i => (f i : MvPolynomial (Fin m) (X → O))) (fun i => (g i).1)
    (fun i => (f i).2) (fun i => (g i).2)
  have hsum : (∑ i ∈ Finset.univ, (f i : MvPolynomial (Fin m) (X → O)) • (g i).1) =
      ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
        Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j)) := by
    rw [← hfg]
    rfl
  rw [hsum] at hdet
  have key : (fun x => AddMonoidAlgebra.coeff (Matrix.det (∑ k,
      (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d) =
      AddMonoidAlgebra.coeff (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
        Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j)))) d :=
    funext fun x => coeff_det_generic_sum_eval a x d
  rw [key]
  exact hmemT _ hdet d

end GlobalTheory.SpanRing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetGenericSumMemHeckeAlgebraStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_det_generic_sum_mem_heckeAlgebra : ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep → ∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, InRing T rep (a k)) → ∀ d : Fin m →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d) ∈ T := by
  first | exact @GlobalTheory.SpanRing.coeff_det_generic_sum_mem_of_inRing | exact GlobalTheory.SpanRing.coeff_det_generic_sum_mem_of_inRing | (intros; apply GlobalTheory.SpanRing.coeff_det_generic_sum_mem_of_inRing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvTateDual
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvTateDual
noncomputable section

namespace GlobalTheory.TateDualInv

section Bridge

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N
open ReciprocityTheory.Gal (cycZ)

variable {l : ℕ} [Fact l.Prime]

theorem isJumpV_zero_of_invariant (P : LocPrime l) (K LL : FinExt l) {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (x : V) (hx : x ≠ 0)
    (h : ∀ g, ρ g x = x) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) : IsJumpV (P.PD K) ρ τ 0 := by
  have := LL.2
  refine GlobalTheory.HTW.isJumpV_of_injective (P.PD K) (Representation.trivial ↥LL.1 ↥(GK K) ↥LL.1) ρ
    (LinearMap.toSpanSingleton ↥LL.1 V x) (LinearMap.ker_eq_bot.1 (LinearMap.ker_toSpanSingleton _ hx))
    (fun g v => by simp [h]) τ 0 fun h0 => ?_
  have h1 := GlobalTheory.CrysExt.finrank_fildR_trivial (P.PD K) (LL := ↥LL.1) τ 0
  have h2 := GlobalTheory.CrysExt.finrank_fildR_trivial (P.PD K) (LL := ↥LL.1) τ (0 + 1)
  rw [h0, h1] at h2
  simp at h2

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) (P : LocPrime l)

theorem cycLL_eq (g : ↥(GK Bw.Kw)) :
    ((cycLL (P.PD Bw.Kw) ↥Bw.LL.1 g : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) =
      Bw.toLL (algebraMap ℤ_[l] O ((cycZ E Ω l (Bw.e.symm g : ↥Gw) : ℤ_[l]ˣ) : ℤ_[l])) := by
  change algebraMap ℚ_[l] ↥Bw.LL.1 (((P.PD Bw.Kw).χ g : ℚ_[l]ˣ) : ℚ_[l]) = _
  rw [P.PD_χ, ← GlobalTheory.BlockJumps.cycZ_eq_chi Bw P g]
  exact (congrArg Subtype.val (Bw.eO_alg _)).symm

theorem dot_dual {O L : Type} [CommRing O] [CommRing L] (φ : O →+* L) {m : ℕ} (A : GL (Fin m) O) (ε : O)
    (x y : Fin m → L) :
    ((A : Matrix (Fin m) (Fin m) O).map φ).mulVec x ⬝ᵥ
      ((ε • (A : Matrix (Fin m) (Fin m) O)⁻¹.transpose).map φ).mulVec y = φ ε * (x ⬝ᵥ y) := by
  have h1 : (ε • (A : Matrix (Fin m) (Fin m) O)⁻¹.transpose).map φ =
      φ ε • (((A : Matrix (Fin m) (Fin m) O)⁻¹).map φ).transpose := by
    ext a b
    simp
  have h2 : ((A : Matrix (Fin m) (Fin m) O)⁻¹).map φ * (A : Matrix (Fin m) (Fin m) O).map φ = 1 := by
    rw [← Matrix.map_mul, ← Matrix.coe_units_inv, Units.inv_mul, Matrix.map_one _ φ.map_zero φ.map_one]
  rw [h1, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

omit [IsAlgClosed Ω] in
theorem rep_apply {m : ℕ} (r : ↥Gw →* GL (Fin m) O) (g : ↥(GK Bw.Kw)) (x : Fin m → ↥Bw.LL.1) :
    Bw.rep r g x = (((r (Bw.e.symm g) : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map Bw.toLL).mulVec x := rfl

omit [IsAlgClosed Ω] in
theorem card_emb : Nat.card (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1) = Module.finrank ℚ_[l] ↥Bw.Kw.1 := by
  have : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  rw [← AlgHom.card ℚ_[l] ↥Bw.Kw.1 (Loc.Om l), ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun τ => Bw.LL.1.val.comp τ
      invFun := fun τ => τ.codRestrict Bw.LL.1.toSubalgebra (Bw.LL_split τ)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem dot_bijective {L : Type} [Field L] (m : ℕ) :
    Function.Bijective (dotProductBilin L L : (Fin m → L) →ₗ[L] (Fin m → L) →ₗ[L] L) := by
  have hi : Function.Injective (dotProductBilin L L : (Fin m → L) →ₗ[L] (Fin m → L) →ₗ[L] L) := by
    intro x y h
    funext i
    simpa using LinearMap.congr_fun h (Pi.single i 1)
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hi⟩

theorem local_noInv (AI : LocAinf l P) (T : LocTied l P AI) {m : ℕ} (r r' : ↥Gw →* GL (Fin m) O)
    (hd : ∀ g, ((r' g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O) =
      algebraMap ℤ_[l] O ((cycZ E Ω l (g : Ω ≃ₐ[E] Ω) : ℤ_[l]ˣ) : ℤ_[l]) •
        ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O)⁻¹.transpose)
    (hdR : Bw.IsdRW P r) (hj : ∀ τ, ¬ IsJumpV (P.PD Bw.Kw) (Bw.rep r) τ (-1))
    (x : Fin m → ↥Bw.LL.1) (hx : ∀ g, Bw.rep r' g x = x) : x = 0 := by
  by_contra h0
  have : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  have hc := card_emb Bw
  obtain ⟨⟨τ⟩, -⟩ := Nat.card_pos_iff.1 (hc ▸ Module.finrank_pos (R := ℚ_[l]) (M := ↥Bw.Kw.1))
  have hJ := isJumpV_zero_of_invariant P Bw.Kw Bw.LL (Bw.rep r') x h0 hx τ
  have hm := (GlobalTheory.DRDual.twisted_dual_deRham l P AI T Bw.Kw Bw.LL _ (Bw.rep r) _ (Bw.rep r')
    (dotProductBilin _ _) 1 (dot_bijective m) (fun g x y => by
      rw [zpow_one, cycLL_eq, rep_apply, rep_apply, hd]
      exact dot_dual _ _ _ _ _) (by simpa [IsDR, LocBridge.IsdRW] using hdR)).2 τ (-1) hc
  have h1 : multV (P.PD Bw.Kw) (Bw.rep r) τ (-1) = 0 := by
    unfold multV
    rw [not_not.1 (hj τ), sub_self]
  rw [h1, show -(-1 : ℤ) - 1 = 0 by norm_num] at hm
  apply hJ
  have hfin := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T Bw.Kw Bw.LL _ (Bw.rep r')).1
  have hle : FildR (P.PD Bw.Kw) (Bw.rep r') τ 0 ≤ DdR (P.PD Bw.Kw) (Bw.rep r') := le_trans inf_le_left inf_le_left
  have := Submodule.finiteDimensional_of_le hle
  refine Submodule.eq_of_le_of_finrank_eq (inf_le_inf_left _ ?_) ?_
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero =>
      set_option synthInstance.maxHeartbeats 200000 in
        simp
    | tmul v b => exact ⟨v ⊗ₜ[ℚ_[l]] ⟨b.1, (P.PD Bw.Kw).Fil_anti 0 b.2⟩, rfl⟩
    | add x y hx hy => simp only [map_add]; exact Submodule.add_mem _ hx hy
  · unfold multV at hm
    omega

end Bridge

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

section Global

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

def dualHom (i : X.Tw) (s : X.Sig i) : Gen.GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) where
  toFun := Tdual i s
  map_one' := by simp [Tdual, ← Tgl_coe]
  map_mul' g h := by
    simp only [Tdual, ← Tgl_coe, map_mul, Units.val_mul, Matrix.mul_inv_rev, Matrix.transpose_mul, smul_mul_smul_comm]

end Global


open scoped Pointwise in
theorem noInv_tateDual : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), (∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI)) → HodgeL bkP i s → NoJump bkP i s → ∀ v ∈ placesOver D.host.E (D.ntw.l i), NoInv i (Tdual i s) v := by
  rintro D bkP i s ⟨AI, ⟨T⟩⟩ hH hJ v hv A hA x hx
  let φ := algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))
  let M : Gen.GE D.nd → Matrix (Fin D.R.r) (Fin D.R.r) (FractionRing (D.ntw.O0 i)) := fun g => (Tdual i s g).map φ
  have hmul : ∀ g h, M (g * h) = M g * M h := fun g h => by
    simp only [M, ← Matrix.map_mul]
    exact congrArg (fun Y => Matrix.map Y φ) ((dualHom i s).map_mul g h)
  have hone : M 1 = 1 := by
    have : Tdual i s 1 = 1 := (dualHom i s).map_one
    simp only [M, this, Matrix.map_one _ φ.map_zero φ.map_one]
  obtain ⟨k, hk⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) hA (D.nd.plOm.2 v)
  have hy : ∀ g ∈ DecV D.nd v, (M g).mulVec ((M k).mulVec x) = (M k).mulVec x := by
    intro g hg
    have h1 : k⁻¹ * g * k ∈ Dec (F := D.host.E) A := by
      have hg' : g • D.nd.plOm.1 v = D.nd.plOm.1 v := hg
      change (k⁻¹ * g * k) • A = A
      rw [mul_smul, mul_smul, hk, hg', ← hk, inv_smul_smul]
    have h2 : (M (k⁻¹ * g * k)).mulVec x = x := hx _ h1
    conv_rhs => rw [← h2]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hmul, ← hmul]
    congr 2
    group
  have : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  let Bw := bkP.br i v hv
  have hz := local_noInv Bw (D.loc (D.ntw.l i)) AI T ((Tgl i s).comp (DecV D.nd v).subtype)
    ((dualHom i s).toHomUnits.comp (DecV D.nd v).subtype)
    (fun g => by
      change Tdual i s g = _ • (((Tgl i s g : GL (Fin D.R.r) (D.ntw.O0 i)) :
        Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)))⁻¹.transpose
      rw [Tgl_coe]
      rfl)
    (hH v hv _ (Set.mem_insert_of_mem _ rfl)).1
    (fun τ h => by
      have := hJ v hv τ (-1) h
      omega)
    (fun a => Br.toLLK Bw ((M k).mulVec x a)) (fun g => by
      rw [rep_apply]
      funext a
      have h3 := congrArg (Br.toLLK Bw) (congrFun (hy _ (Bw.e.symm g).2) a)
      rw [← h3, RingHom.map_mulVec]
      congr 1
      ext b c
      exact congrArg Subtype.val (Br.toLLK_alg Bw _).symm)
  have h4 : (M k).mulVec x = 0 := funext fun a => (Br.toLLK Bw).injective (by
    rw [Pi.zero_apply, map_zero]; exact congrFun hz a)
  have h5 := congrArg (M k⁻¹).mulVec h4
  rwa [Matrix.mulVec_mulVec, ← hmul, inv_mul_cancel, hone, Matrix.one_mulVec, Matrix.mulVec_zero] at h5

end GlobalTheory.TateDualInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvTateDualStatement
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noInv_tateDual_of_hodge_of_noJump : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), (∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI)) → HodgeL bkP i s → NoJump bkP i s → ∀ v ∈ placesOver D.host.E (D.ntw.l i), NoInv i (Tdual i s) v := by
  first | exact @GlobalTheory.TateDualInv.noInv_tateDual | exact GlobalTheory.TateDualInv.noInv_tateDual | (intros; apply GlobalTheory.TateDualInv.noInv_tateDual <;> assumption)
end
end
