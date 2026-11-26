module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionSubgroupCocompactHaarFundamentalDoma
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntOfHomAt
open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV
open GlobalTheory.GO.ChRoot GlobalTheory.TopStep

namespace GlobalTheory.ColPeriod.EntQ

section Val

variable {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

theorem val_of_pow {a : K} {k : ℕ} (hk : 0 < k) (h : w.valuation K (a ^ k) = 1) : w.valuation K a = 1 := by
  rw [map_pow] at h
  exact (pow_eq_one_iff_of_nonneg zero_le' hk.ne').1 h

theorem val_nat {q : ℕ} (hq : (q : 𝓞 K) ∉ w.asIdeal) : w.valuation K (q : K) = 1 := by
  have := (w.valuation_eq_one_iff_notMem (K := K) (r := (q : 𝓞 K))).2 hq
  simpa using this

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

theorem val_unitV (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) :
    w.valuation K (LocE.unitV χ a) ≤ 1 ∧ w.valuation K (LocE.unitV χ a)⁻¹ ≤ 1 := by
  by_cases h : LocE.unitV χ a = 0
  · simp [h]
  · obtain ⟨k, hk, h1⟩ := unitV_root χ a h
    have := val_of_pow w hk (a := LocE.unitV χ a) (by rw [h1, map_one])
    simp [this]

theorem val_locChar (q : ℕ) {cq : K} (hc : w.valuation K cq = 1) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) :
    w.valuation K (LocE.locChar q cq χ a) ≤ 1 ∧ w.valuation K (LocE.locChar q cq χ a)⁻¹ ≤ 1 := by
  unfold LocE.locChar
  rw [mul_inv, map_mul, map_mul, map_inv₀ _ (cq ^ _), map_zpow₀, hc, one_zpow, inv_one, one_mul, one_mul]
  exact val_unitV w χ _

theorem val_om {a b : ℕ} {mu : E → K} (hmu : ∀ t, w.valuation K (mu t) ≤ 1 ∧ w.valuation K (mu t)⁻¹ ≤ 1) (v : E → ℤ)
    {sq : K} (hsq : w.valuation K sq = 1) (g₀ : (Fin a → E) ≃ₗ[E] (Fin a → E)) (h : (Fin b → E) ≃ₗ[E] (Fin b → E))
    {Φ : Loc.SF E K a b} (hΦ : ∀ x, w.valuation K (Φ x) ≤ 1) (x) : w.valuation K (Loc.om mu v sq g₀ h Φ x) ≤ 1 := by
  unfold Loc.om
  simp only [map_mul, map_zpow₀, hsq, one_zpow, mul_one]
  exact mul_le_one' (mul_le_one' (hmu _).1 (hmu _).2) (hΦ _)

theorem val_PhiQ (q : ℕ) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ) (x) :
    w.valuation K (LocE.PhiQ q χ k₀ r c' n' c n x) ≤ 1 := by
  unfold LocE.PhiQ
  split_ifs
  · exact (val_unitV w χ _).1
  · simp

end Val

section Supp

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem exists_fIdx {k₀ c n l : ℕ} (hk : k₀ ≤ n) (hl : l < n + c) : ∃ s, s < n + c ∧ LocE.fIdx k₀ c n s = l := by
  refine ⟨LocE.fPos k₀ c n l, ?_, ?_⟩
  · unfold LocE.fPos
    split_ifs <;> omega
  · unfold LocE.fIdx LocE.fPos
    split_ifs <;> omega

theorem int_of_PhiQ {q : ℕ} {χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ} {k₀ r c' n' c n : ℕ} (hk' : k₀ ≤ n') (hk : k₀ ≤ n)
    {x : HomE E (n' + c') (n + c)} (hx : LocE.PhiQ q χ k₀ r c' n' c n x ≠ 0) {v : Sp E (n' + c')}
    (hv : v ∈ stdAt E (n' + c') P) : x v ∈ stdAt E (n + c) P := by
  unfold LocE.PhiQ at hx
  split_ifs at hx with h
  · rw [mem_stdAt] at hv ⊢
    intro i
    rw [apply_eq_sum]
    refine intAt_sum _ fun j _ => (hv j).mul ?_
    obtain ⟨p, hp, e⟩ := exists_fIdx hk i.2
    obtain ⟨p', hp', e'⟩ := exists_fIdx hk' j.2
    have h1 := h.1 p p' hp hp'
    have h2 : Loc.eN E (n' + c') j.1 = Pi.single j 1 := by
      funext l
      simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
    simpa [LocE.entB, e, e', LocE.scE, Loc.atN, h2] using h1
  · exact absurd rfl hx

theorem intAt_chArg {n' c' n c : ℕ} (a : E) (x : HomE E (n' + c') (n + c))
    (h : ∀ v ∈ stdAt E (n' + c') P, a • x v ∈ stdAt E (n + c) P) : IntAt P (a * Loc.chArg x) := by
  unfold Loc.chArg
  rw [Finset.mul_sum]
  refine intAt_sum _ fun i _ => ?_
  unfold Loc.atN
  split_ifs with hi
  · exact mem_stdAt.1 (h _ eN_mem) ⟨n + i, hi⟩
  · simpa using intAt_zero

theorem int_of_homAt {a b : ℕ} {z : HomE E a b} (hz : z ∈ homAt {P} (stdLat E a) (stdLat E b)) (B : ℕ) (s : Fin a) (l : Fin b) :
    IntAt P (((qOf P : E) ^ B)⁻¹ * (((qOf P : E) ^ B) • z) (Pi.single s 1) l) := by
  have h := mem_stdAt.1 (hz P (Finset.mem_singleton_self P) _ (single_mem_stdAt s)) l
  have hq := qOf_ne_zero (P := P)
  rwa [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero _ hq)]

end Supp

theorem k_le_N (R : Ranks) (j : ℕ) : R.k ≤ R.N j := by
  unfold Ranks.N
  omega

theorem entryAtQ (hV : VolumeAtQ) : EntryAtQ := by
  intro X Pr R Ch sel S mu cst L G m2 hL P w hP hdeg hq hmu
  have hm := hL.hm
  have hqv := val_nat w hq
  have hsq : w.valuation X.K (cst.sq P) = 1 := val_of_pow w two_pos (by rw [hL.cst_ok.sq_sq, hqv])
  have hom : ∀ i, i < R.m → ∀ hal h x, w.valuation X.K (omPhi Ch sel mu cst i P hal h x) ≤ 1 := by
    intro i hi hal h x
    refine val_om w (fun t => val_locChar w _ (hmu i hi) _ t) _ hsq _ _ (fun y => ?_) x
    rw [PhiAt, if_neg hP]
    exact val_PhiQ w _ _ _ _ _ _ _ _ y
  refine ⟨fun i hi al be => ⟨fun x => ?_, fun x z hz => hL.xiInv i hi al be P x _ (int_of_homAt hz _)⟩,
    fun al y => ⟨fun x => hom m2 (by omega) _ _ _, fun x z hz => hL.psiInvX al P x _ y (int_of_homAt hz _)⟩⟩
  unfold XiAt E1at Loc.E1
  rw [map_mul, map_mul, map_pow, map_inv₀ _ (_ ^ cst.B), map_pow, hqv, one_pow, inv_one, one_pow, one_mul]
  refine mul_le_one' (hV X Pr R _ _ _ _ w hP hdeg hq) (Valuation.map_sum_le _ fun t _ => ?_)
  generalize Loc.xx1 x t = y
  by_cases h0 : omPhi Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) y = 0
  · simp [h0]
  rw [map_mul]
  refine mul_le_one' (hom i (by omega) _ _ _) (le_of_eq ?_)
  have h1 := right_ne_zero_of_mul h0
  rw [PhiAt, if_neg hP] at h1
  have hb := hL.boundQ i al P hP
  have hb' := hL.boundQ (i + 1) be P hP
  have hD := hL.depthQ' P hP
  simp only [lamYat, hP, if_false, mem_lamY_zero] at hb hb'
  have hint : IntAt P.1 ((qOf P.1 : X.E) ^ (i + 1) * Loc.chArg y) := by
    refine intAt_chArg _ y fun v hv => ?_
    have h2 := (hb' _ (int_of_PhiQ (k_le_N R _) (k_le_N R _) h1 (hb v hv).1)).2
    have h3 : (L.h i al P) ((L.h i al P)⁻¹ v) = v := LinearEquiv.apply_symm_apply _ v
    simpa [h3] using h2
  have hint' : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * -Loc.chArg y) := by
    obtain ⟨d, hd⟩ : ∃ d, cst.D P = d + (i + 1) := ⟨cst.D P - (i + 1), by omega⟩
    rw [hd, pow_add, mul_neg, mul_assoc]
    exact intAt_neg ((intAt_pow (intAt_nat _) _).mul hint)
  exact val_of_pow w (pow_pos (qOf_pos _) _) (by rw [psi_root hL.cst_ok P _ hint', map_one])

end GlobalTheory.ColPeriod.EntQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfPow
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.TopStep GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator GlobalTheory.LastSteps

noncomputable section

namespace GlobalTheory.ColPeriod.TopTwist

theorem valuation_le_one_of_pow {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K} {k : ℕ}
    (hk : k ≠ 0) (h : x ^ k = 1) : w.valuation K x ≤ 1 := by
  by_contra hn
  have h1 := one_lt_pow₀ (not_le.1 hn) hk
  rw [← map_pow, h, map_one] at h1
  exact lt_irrefl _ h1

section Phi

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

omit [StarRing E] in
theorem qOf_nat_ne_zero : qOf P ≠ 0 := fun h => (qOf_ne_zero (P := P)) (by rw [h, Nat.cast_zero])

omit [StarRing E] in
theorem qOf_pred_ne_zero : qOf P - 1 ≠ 0 := by
  intro h
  have h0 := qOf_nat_ne_zero (P := P)
  have h1 : qOf P = 1 := by omega
  have h2 := qOf_mem (P := P)
  rw [h1, Nat.cast_one] at h2
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)

omit [StarRing E] in
theorem valuation_PhiQ [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (q k₀ r c' n' c n : ℕ)
    (x : HomE E (n' + c') (n + c)) : w.valuation K (LocE.PhiQ q ξ k₀ r c' n' c n x) ≤ 1 := by
  unfold LocE.PhiQ LocE.unitV
  split_ifs
  · exact valuation_le_one_of_pow w qOf_pred_ne_zero (char_pow ξ _)
  · simp
  · simp

theorem PhiQ_add (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ r c' n' c n : ℕ} (h1 : r ≤ n' + c') (h2 : r ≤ n + c)
    (x z : HomE E (n' + c') (n + c)) (hz : z ∈ homS (LocE.lamY P (qOf P) n' c' 0) (LocE.lamY P (qOf P) n c 0)) :
    LocE.PhiQ (qOf P) ξ k₀ r c' n' c n (x + (qOf P : E) • z) = LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x := by
  have hZ := entB_int k₀ hz
  unfold LocE.PhiQ
  rw [entB_add_smul]
  generalize LocE.entB (qOf P) k₀ c' n' c n 0 0 z = Z at hZ
  generalize LocE.entB (qOf P) k₀ c' n' c n 0 0 x = M
  have e1 := fun a p p' => intAt_add_q (a := a) (hZ p p')
  have e2 := fun a p p' => intAt_add_q_div (a := a) (hZ p p')
  refine ite_eq_ite_zero (by simp only [e1, e2]) fun h => ?_
  exact LastSteps.unitV_congr _ (redP_det_add_q (fun s s' => h.1 _ _ (by have := s.2; omega) (by have := s'.2; omega)) fun _ _ => hZ _ _)

end Phi

section Psi

variable {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {c : LocCst X SB}

theorem psi_add_int' (hc : c.Ok) (P : SB) {a b : X.E} (ha : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * a)) (hb : IntAt P.1 b) :
    c.psi P (a + b) = c.psi P a := by
  rw [hc.psi_add P a b ha ((intAt_pow (intAt_nat _) _).mul hb), hc.psi_int P b hb, mul_one]

theorem psi_pow (hc : c.Ok) (P : SB) {a : X.E} (ha : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * a)) :
    c.psi P a ^ (qOf P.1 ^ c.D P) = 1 := by
  have h : ∀ k : ℕ, c.psi P a ^ k = c.psi P ((k : X.E) * a) := fun k => by
    induction k with
    | zero => rw [pow_zero, Nat.cast_zero, zero_mul, hc.psi_int P 0 intAt_zero]
    | succ k ih =>
      rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, hc.psi_add P _ _ _ ha]
      rw [mul_left_comm]
      exact (intAt_nat _).mul ha
  rw [h, Nat.cast_pow, hc.psi_int P _ ha]

end Psi

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem intAt_arg (P : rowSG Pr sel mu) (hD : 2 * cst.M ≤ cst.D P) {n : ℕ} {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ cst.M) • y ∈ stdAt X.E n P.1) (η : Sp X.E n →ₗ[X.E] X.E)
    (h : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η (Pi.single i 1))) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * η y)) := by
  have he : IntAt P.1 (epsSg : X.E) := by simpa [epsSg] using intAt_neg intAt_one
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hD
  have h1 := (inDual_iff (((qOf P.1 : X.E) ^ cst.M) • η)).2 h _ hy
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
  convert (he.mul (intAt_pow (intAt_nat (qOf P.1)) k)).mul h1 using 1
  rw [hk]
  ring

theorem valuation_ftY (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D P)
    (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((qOf P.1 : ℕ) : 𝓞 X.K) ∉ w.asIdeal) {n : ℕ} {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ cst.M) • y ∈ stdAt X.E n P.1) (η : Sp X.E n →ₗ[X.E] X.E) :
    w.valuation X.K (ftY sel mu cst P η y) ≤ 1 := by
  unfold ftY
  rw [if_neg hP]
  split_ifs with h
  · have h2 : w.valuation X.K (algebraMap (𝓞 X.K) X.K (qOf P.1 : 𝓞 X.K)) = 1 :=
      (w.valuation_eq_one_iff_notMem (K := X.K)).2 hw
    rw [map_natCast] at h2
    rw [map_mul, map_inv₀, map_pow, h2, one_pow, inv_one, one_mul]
    exact valuation_le_one_of_pow w (pow_ne_zero _ qOf_nat_ne_zero) (psi_pow hc P (intAt_arg sel mu cst P hD hy η h))
  · simp

theorem ftY_add (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D P) {n : ℕ} {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ cst.M) • y ∈ stdAt X.E n P.1) (η z : Sp X.E n →ₗ[X.E] X.E) (hz : InDual P.1 z) :
    ftY sel mu cst P (η + ((qOf P.1 : X.E) ^ cst.B) • z) y = ftY sel mu cst P η y := by
  have he : IntAt P.1 (epsSg : X.E) := by simpa [epsSg] using intAt_neg intAt_one
  have hz' := (inDual_iff z).1 hz
  unfold ftY
  simp only [if_neg hP]
  refine ite_eq_ite_zero (forall_congr' fun i => ?_) fun h => ?_
  · rw [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, mul_add]
    exact intAt_add_iff ((intAt_pow (intAt_nat _) _).mul ((intAt_pow (intAt_nat _) _).mul (hz' i)))
  · rw [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, mul_add,
      psi_add_int' hc P (intAt_arg sel mu cst P hD hy η h)]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hc.M_le_B
    have h1 := hz _ hy
    rw [map_smul, smul_eq_mul] at h1
    convert (he.mul (intAt_pow (intAt_nat (qOf P.1)) k)).mul h1 using 1
    rw [hk]
    ring

theorem frsF_mem' {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (x : Sp X.E (R.N j)) : frsF sel mu p P x ∈ localization₂ P.1.asIdeal p.deco.1.N ↔ x ∈ stdAt X.E (R.N j) P.1 := by
  classical
  unfold frsF
  rw [dite_eq_right hP]
  have h : ∀ Q : QE sel (mu : Chr X.F X.E X.K), p.fr Q x ∈ localization₂ Q.1.asIdeal p.deco.1.N ↔ x ∈ stdAt X.E (R.N j) Q.1 :=
    fun Q => p.2 Q x
  exact h ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩

theorem pow_smul_repY {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} {Y : Set (Sp X.E n)} (hY : Y ∈ ybSet sel mu cst N)
    (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) : ((qOf P.1 : X.E) ^ cst.M) • repY Y ∈ localization₂ P.1.asIdeal N := by
  obtain ⟨y, hy, hY⟩ := hY
  have h0 : repY Y ∈ Y := Classical.epsilon_spec (p := fun y => y ∈ Y) ⟨y, by rw [hY]; simp⟩
  generalize repY Y = y' at h0
  rw [hY] at h0
  have h1 := (mem_locLat _ _ _ _).1 hy P
  have h2 := (mem_locLat _ _ _ _).1 h0 P
  rw [if_neg hP] at h1 h2
  simp only [zpow_neg, inv_inv, zpow_natCast] at h1 h2
  have hq : ((qOf P.1 : X.E) ^ cst.M) ≠ 0 := pow_ne_zero _ qOf_ne_zero
  have hi : IntAt P.1 ((qOf P.1 : X.E) ^ cst.M) := intAt_pow (intAt_nat _) _
  have h3 := smul_mem_locP hi (smul_mem_locP hi h2)
  rw [smul_inv_smul₀ hq] at h3
  have h4 := add_mem h3 h1
  rwa [← smul_add, sub_add_cancel] at h4

end Chain

theorem topAtQ : GlobalTheory.ColPeriod.TopAtQ := by
  intro X Pr R Ch sel S mu cst L G m2 u hPr hsel hS hL P w hP _ hw p d Y hY
  have hc := hL.cst_ok
  have hm := hL.hm
  have hD := hL.depthQ P hP
  have hu := piT_notMem_rowSG sel mu hPr hsel u hS
  have hy : ((qOf P.1 : X.E) ^ cst.M) • (frsF sel mu p P).symm (repY Y) ∈ stdAt X.E _ P.1 := by
    rw [← map_smul, ← frsF_mem' sel mu p P hP, LinearEquiv.apply_symm_apply]
    exact pow_smul_repY sel mu cst hY P hP
  refine ⟨fun x => ?_, fun x z hz => ?_⟩
  · unfold facTop PhiTop
    rw [if_neg hP, map_mul]
    exact mul_le_one' (valuation_PhiQ w _ _ _ _ _ _ _ _ _) (valuation_ftY sel mu cst hc P hP hD w hw hy _)
  · have key : ∀ y ∈ stdAt X.E (R.N (m2 + 1)) P.1,
        (d.1.liftFr P).symm (prXp X.E R (z (frsF sel mu p P y))) ∈ stdAt X.E (R.N R.m - 1) P.1 ∧
          IntAt P.1 (((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ * atNL X.E (R.N R.m) (R.N R.m - 1) (z (frsF sel mu p P y))) := fun y hy => by
      have h := (mem_tilH (N_m_succ R) d (conj_piT_notMem hPr u) hu P.1 _).1
        (hz P.1 (Finset.mem_singleton_self _) _ ((frsF_mem' sel mu p P hP y).2 hy))
      rw [LastSteps.atNL_last, ← (liftFr_spec d.2 P).1, LinearEquiv.apply_symm_apply, inv_mul_eq_div]
      exact ⟨h.1, h.2.div_of_notMem (hu P)⟩
    have h1 : R.r ≤ R.N (m2 + 1) + cOf R (m2 + 1) := by
      unfold Ranks.r Ranks.N cOf
      rw [hm, mul_add (m2 + 1)]
      omega
    have h4 : R.N (m2 + 1) + cOf R (m2 + 1) ≤ R.N R.m - 1 + 0 := by
      unfold Ranks.N cOf
      rw [hm, show m2 + 2 = m2 + 1 + 1 from rfl, add_mul (m2 + 1)]
      omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hc.B_pos
    unfold facTop PhiTop
    rw [if_neg hP]
    congr 1
    · have e : (d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ (x + ((qOf P.1 : X.E) ^ cst.B) • z) ∘ₗ
            (frsF sel mu p P).toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) =
          (d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ
            (frsF sel mu p P).toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) +
          (qOf P.1 : X.E) • ((((qOf P.1 : X.E) ^ k) • ((d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ z ∘ₗ
            (frsF sel mu p P).toLinearMap)) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) := by
        rw [hk, pow_succ', mul_smul]
        simp only [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.comp_assoc]
      rw [e]
      refine PhiQ_add _ h1 (h1.trans h4) _ _ ?_
      rw [comp_funLeft_mem (cOf_top hm), lamY_zero]
      exact fun y hy => smul_mem_locP (intAt_pow (intAt_nat _) _) (key y hy).1
    · rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp ((qOf P.1 : X.E) ^ cst.B), LinearMap.comp_smul]
      exact ftY_add sel mu cst hc P hP hD hy _ _ fun y hy => (key y hy).2

end GlobalTheory.ColPeriod.TopTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnfoldingIsGoodCyclotomicInvariantReferenceLatti
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.TopStep GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator GlobalTheory.LastSteps

noncomputable section

namespace GlobalTheory.ColPeriod

section Unfold

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem good_om_two {N' N : ℕ} {e' e : ℕ → ℤ} {Φ : HomE E N' N → K}
    (h : Good P (homS (LocE.sclLat P (qOf P) N' e') (LocE.sclLat P (qOf P) N e)) Φ) (cq sq : K)
    (χ₀ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {g : Sp E N' ≃ₗ[E] Sp E N'} (hg : g ∈ stabL E N' (LocE.sclLat P (qOf P) N' e'))
    {k : Sp E N ≃ₗ[E] Sp E N} (hk : k ∈ stabL E N (LocE.sclLat P (qOf P) N e)) :
    Good P (homS (LocE.sclLat P (qOf P) N' e') (LocE.sclLat P (qOf P) N e))
      (Loc.om (LocE.locChar (qOf P) cq χ₀) (LocE.vP P (qOf P)) sq g k Φ) := by
  have hu := isUnit_det_of_stab hg
  have h1 := isUnit_det_of_stab hk
  unfold Loc.om
  rw [locChar_unit _ _ hu, locChar_unit _ _ h1, vP_unit hu, vP_unit h1]
  refine Good.const_mul (h.comp (H' := homS (LocE.sclLat P (qOf P) N' e') (LocE.sclLat P (qOf P) N e))
    (fun x => k.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap)
    (fun x z => ?_) fun w => ⟨fun hw y hy => (inv_mem hk _).2 (hw _ ((hg y).2 hy)), fun hw y hy => ?_⟩) ?_
  · rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul]
  · have := hw (g.symm y) ((hg _).1 (by simpa using hy))
    rw [← g.apply_symm_apply y]
    exact (inv_mem hk _).1 this
  · simp only [neg_zero, zero_mul, zpow_zero, mul_one]
    exact mul_mem (unitV_mem _ _) (unitV_inv_mem _ _)

omit [NumberField E] [StarRing E] in
theorem freeCoordinateExtension_apply_single {n' c' n c : ℕ} (xj : HomE E n' n) (t : Loc.FC n' c' n c → E) (l : Fin (n + c)) (s : Fin (n' + c')) :
    Loc.xx1 xj t (Pi.single s 1) l =
      if hf : Loc.IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩
      else if hs : s.1 < n' then (if hl : l.1 < n then xj (Pi.single ⟨s.1, hs⟩ 1) ⟨l.1, hl⟩ else 0)
      else if l.1 = n + (s.1 - n') then 1 else 0 := by
  unfold Loc.xx1
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  simp only [Matrix.col_apply, Matrix.of_apply, LinearMap.toMatrix'_apply]

theorem intAt_zpow {z : ℤ} (hz : 0 ≤ z) : IntAt P ((qOf P : E) ^ z) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  rw [zpow_natCast]
  exact intAt_pow (intAt_nat _) _

theorem mem_homS_std {a b : ℕ} {x : HomE E a b} :
    x ∈ homS (stdAt E a P) (stdAt E b P) ↔ ∀ l s, IntAt P (x (Pi.single s 1) l) := by
  refine ⟨fun h l s => mem_stdAt.1 (h _ (single_mem_stdAt s)) l, fun h y hy => mem_stdAt.2 fun l => ?_⟩
  rw [apply_eq_sum]
  exact intAt_sum _ fun j _ => (mem_stdAt.1 hy j).mul (h l j)

theorem standardLattice_restriction_of_freeExtension_mem {n' c' n c : ℕ} {ex' ex : ℕ → ℕ} {xj : HomE E n' n} {t : Loc.FC n' c' n c → E}
    (h : Loc.xx1 xj t ∈ homS (LocE.lamY P (qOf P) n' c' ex') (LocE.lamY P (qOf P) n c ex)) :
    xj ∈ homS (stdAt E n' P) (stdAt E n P) := by
  refine mem_homS_std.2 fun l s => ?_
  have h1 := mem_homS_sclLat.1 h (Fin.castAdd c l) (Fin.castAdd c' s)
  have hs : (Fin.castAdd c' s).1 < n' := s.2
  have hl : (Fin.castAdd c l).1 < n := l.2
  rw [freeCoordinateExtension_apply_single, dite_eq_right (fun hf => absurd hf.1 (by omega)), dite_eq_left hs, dite_eq_left hl] at h1
  simpa [LocE.scE] using h1

theorem chArg_int {n' c' n c : ℕ} {x : HomE E (n' + c') (n + c)}
    (h : x ∈ homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1)) :
    IntAt P ((qOf P : E) * (-Loc.chArg x)) := by
  rw [mul_neg]
  refine intAt_neg ?_
  unfold Loc.chArg
  rw [Finset.mul_sum]
  refine intAt_sum _ fun i _ => ?_
  unfold Loc.atN
  split_ifs with h1
  · by_cases h2 : n' + i + 1 < n' + c'
    · rw [eN_eq h2]
      have h3 := mem_homS_sclLat.1 h ⟨_, h1⟩ ⟨_, h2⟩
      have e : LocE.scE n' (fun i => i + 1) (n' + i + 1) - LocE.scE n (fun i => i + 1) (n + i) = 1 := by
        unfold LocE.scE
        rw [if_neg (by omega), if_neg (by omega)]
        dsimp only
        omega
      rw [e, zpow_one, mul_comm] at h3
      exact h3
    · rw [eN_of_not h2]
      simpa using intAt_zero
  · simpa using intAt_zero

omit [StarRing E] in
theorem chArg_sub_int {n' c' n c : ℕ} {x x' : HomE E (n' + c') (n + c)}
    (h : ∀ l s, IntAt P (x' (Pi.single s 1) l - x (Pi.single s 1) l)) : IntAt P (Loc.chArg x - Loc.chArg x') := by
  rw [← neg_sub]
  refine intAt_neg ?_
  unfold Loc.chArg
  rw [← Finset.sum_sub_distrib]
  refine intAt_sum _ fun i _ => ?_
  unfold Loc.atN
  split_ifs with h1
  · by_cases h2 : n' + i + 1 < n' + c'
    · rw [eN_eq h2]
      exact h _ _
    · rw [eN_of_not h2]
      simpa using intAt_zero
  · simpa using intAt_zero

theorem integrand_congr {n' c' n c : ℕ} {Φ : HomE E (n' + c') (n + c) → K}
    (h : Good P (homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1)) Φ)
    {psi : E → K} (hpsi : ∀ a b, IntAt P ((qOf P : E) * a) → IntAt P b → psi (a + b) = psi a)
    {xj xj' : HomE E n' n} {t t' : Loc.FC n' c' n c → E}
    (hx : ∀ l s, IntAt P ((qOf P : E)⁻¹ * (xj' (Pi.single s 1) l - xj (Pi.single s 1) l))) (ht : ∀ p, IntAt P (t' p - t p)) :
    Φ (Loc.xx1 xj' t') * psi (-Loc.chArg (Loc.xx1 xj' t')) = Φ (Loc.xx1 xj t) * psi (-Loc.chArg (Loc.xx1 xj t)) := by
  have hq : (qOf P : E) ≠ 0 := qOf_ne_zero
  have h1 : (qOf P : E)⁻¹ • (Loc.xx1 xj' t' - Loc.xx1 xj t) ∈
      homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1) := by
    refine mem_homS_sclLat.2 fun l s => ?_
    rw [LinearMap.smul_apply, LinearMap.sub_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, freeCoordinateExtension_apply_single, freeCoordinateExtension_apply_single]
    split_ifs with hf hs hl h4
    · have hl := l.2
      have e : 0 ≤ LocE.scE n' (fun i => i + 1) s.1 - LocE.scE n (fun i => i + 1) l.1 - 1 := by
        unfold LocE.scE
        unfold Loc.IsFree at hf
        dsimp only
        split_ifs <;> omega
      convert (ht ⟨(l, s), hf⟩).mul (intAt_zpow e) using 1
      rw [zpow_sub_one₀ hq]
      ring
    · simpa [LocE.scE, hs, hl] using hx _ _
    all_goals simpa using intAt_zero
  have h2 : ∀ l s, IntAt P (Loc.xx1 xj' t' (Pi.single s 1) l - Loc.xx1 xj t (Pi.single s 1) l) := fun l s => by
    rw [freeCoordinateExtension_apply_single, freeCoordinateExtension_apply_single]
    split_ifs with hf hs hl h4
    · exact ht _
    · have := (intAt_nat (qOf P)).mul (hx ⟨l.1, hl⟩ ⟨s.1, hs⟩)
      rwa [mul_inv_cancel_left₀ hq] at this
    all_goals simpa using intAt_zero
  have h3 := h.2.1 (Loc.xx1 xj t) _ h1
  rw [smul_inv_smul₀ hq, add_sub_cancel] at h3
  rw [h3]
  by_cases h0 : Φ (Loc.xx1 xj t) = 0
  · rw [h0, zero_mul, zero_mul]
  · rw [← hpsi _ _ (chArg_int (h.1 _ h0)) (chArg_sub_int h2)]
    congr 2
    ring

theorem unfolding_isGoodCyclotomicInvariant_referenceLattices [CharZero K] {n' c' n c : ℕ} {Φ : HomE E (n' + c') (n + c) → K}
    (h : Good P (homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1)) Φ)
    {psi : E → K} (hpsi : ∀ a b, IntAt P ((qOf P : E) * a) → IntAt P b → psi (a + b) = psi a)
    (hmem : ∀ a, IntAt P ((qOf P : E) * a) → psi a ∈ Zmu K (qOf P)) (A B : ℕ) :
    Good P (homS (stdAt E n' P) (stdAt E n P)) (Loc.E1 psi (LocE.valsQ E (qOf P) A B) (((qOf P : K) ^ B)⁻¹) Φ) := by
  classical
  have hq : (qOf P : E) ≠ 0 := qOf_ne_zero
  have hqK : (qOf P : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.cast_ne_zero.1 hq)
  refine ⟨fun x hx => ?_, fun x z hz => ?_, fun x => ?_⟩
  · obtain ⟨t, -, h0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hx)
    exact standardLattice_restriction_of_freeExtension_mem (h.1 _ (left_ne_zero_of_mul h0))
  · unfold Loc.E1
    congr 1
    refine Finset.sum_congr rfl fun t _ => integrand_congr h hpsi (fun l s => ?_) fun p => ?_
    · simpa [inv_mul_cancel_left₀ hq] using mem_homS_std.1 hz l s
    · simpa using intAt_zero
  · unfold Loc.E1
    rw [weighted_sum_piFinset (Loc.FC n' c' n c) E K (fun g => ∀ a u, IntAt P u → g (a + (qOf P : E) ^ 0 * u) = g a)
      (LocE.valsQ E (qOf P) A B) (LocE.valsQ E (qOf P) A 0) (((qOf P : K) ^ B)⁻¹) 1 (fun g hg => ?_)
      (fun t => Φ (Loc.xx1 x t) * psi (-Loc.chArg (Loc.xx1 x t))) fun t p a u hu => ?_]
    · rw [one_pow, one_mul]
      refine sum_mem fun t _ => ?_
      by_cases h0 : Φ (Loc.xx1 x t) = 0
      · rw [h0, zero_mul]
        exact zero_mem _
      · exact mul_mem (h.2.2 _) (hmem _ (chArg_int (h.1 _ h0)))
    · rw [sum_valsQ_of_invariant E P K g 0 hg A B (Nat.zero_le B), Nat.sub_zero, inv_mul_cancel_left₀ (pow_ne_zero _ hqK), one_mul]
    · refine integrand_congr h hpsi (fun l s => by simpa using intAt_zero) fun p' => ?_
      by_cases hp : p' = p
      · subst hp
        simpa using hu
      · simpa [hp] using intAt_zero


omit [StarRing E] in
theorem volN_inv_nat {n c : ℕ} {Λ : Submodule (𝓞 E) (Sp E (n + c))} {J : Subgroup (Sp E (n + c) ≃ₗ[E] Sp E (n + c))}
    (hJ : J ≤ stabL E _ Λ) {k : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hk : k ∈ stabL E _ Λ) :
    ∃ m : ℕ, (Loc.volN K (Loc.Cbe J k) (Loc.N1 E n c ⊓ stabL E _ Λ))⁻¹ = m := by
  have h : Loc.Cbe J k ⊓ Loc.N1 E n c ≤ Loc.N1 E n c ⊓ stabL E _ Λ := fun r hr => ⟨hr.2, by
    have h1 : k⁻¹ * r * k⁻¹⁻¹ ∈ stabL E _ Λ := hJ hr.1.2
    have h2 := mul_mem (mul_mem hk h1) (inv_mem hk)
    rwa [show k * (k⁻¹ * r * k⁻¹⁻¹) * k⁻¹ = r by group] at h2⟩
  unfold Loc.volN
  rw [Subgroup.relIndex_eq_one.2 h, Nat.cast_one, one_div, inv_inv]
  exact ⟨_, rfl⟩

end Unfold

theorem entryAtG : EntryAtG := by
  intro X Pr R Ch sel S mu cst L G m2 hL i hi al be P hP _
  have hm := hL.hm
  have hal := hL.stabG i al P hP
  have hbe := hL.stabG (i + 1) be P hP
  have hJ : Jat (Pr := Pr) cst.sharp (i + 1) P.1 ≤ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1) := by
    unfold Jat lamYat
    rw [if_pos hP, if_pos hP]
    split_ifs
    · exact inf_le_left
    · exact inf_le_left
  obtain ⟨v, hv⟩ := volN_inv_nat (K := X.K) hJ hbe
  have h1 : R.k ≤ R.N i := Nat.le_add_right _ _
  have h2 : R.k ≤ R.N (i + 1) := Nat.le_add_right _ _
  have h3 : R.r + (i + 1 - 1) * R.t = R.N i + cOf R i := by
    unfold Ranks.r Ranks.N cOf
    rw [hm, Nat.add_sub_cancel, mul_add i]
    omega
  have h4 : R.N i + cOf R i ≤ R.N (i + 1) + cOf R (i + 1) := by
    unfold Ranks.N cOf
    rw [hm, add_mul i]
    omega
  have hom : Good P.1 (homS (LocE.lamY P.1 (qOf P.1) (R.N i) (cOf R i) fun i => i + 1)
      (LocE.lamY P.1 (qOf P.1) (R.N (i + 1)) (cOf R (i + 1)) fun i => i + 1))
      (omPhi Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P)) := by
    unfold lamYat at hal hbe
    rw [if_pos hP] at hal hbe
    refine good_om_two ?_ _ _ _ hal hbe
    unfold PhiAt
    rw [if_pos hP]
    split_ifs
    · exact good_PhiGS _ _ h1 h2 h3 h4
    · exact good_PhiG _ _ h1 h2 h3 h4
  refine (fnModAt_iff _ _ _).2 (Good.const_mul (unfolding_isGoodCyclotomicInvariant_referenceLattices hom (fun a b => psi_add_int hL.cst_ok P)
    (fun a => psi_mem hL.cst_ok P) cst.A cst.B) ?_)
  rw [hv]
  exact natCast_mem _ v

end GlobalTheory.ColPeriod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodFormsBaseLevelIffGoodProjection
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodFormsBaseLevelIffGoodProjection
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem goodForms_baseLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ i (x : (R.HW i (sg0 D A)).H), (R.HW i _).e x ∈ R.Wat i (sg0 D A) (R.levL F false (sg0 D A)) ↔ eH R i x = x ∧ ∀ p : F.P0, R.gW i (sg0 D A) p x = sg0 D A ((F.ψ0⁻¹ p : D.what₂.LLˣ) : D.what₂.LL) • x := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC _ i x
  have hW := hC.models.HW
  have hg := hC.models.gW
  have hl := GlobalTheory.GalLift.Transl.lifts R i hC.lev
  have hx : (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := (hW i _).2.1.le (LinearMap.mem_range_self _ x)
  have hm := (GlobalTheory.MultMem.mem_mult_iff ..).1 hx
  have hT := GlobalTheory.GalLift.Transl.hasType R i hW (sg0 D A) x
  have hsum : (∑ g, RealDat.eC (A := A) (sg0 D A) g • R.gW i (sg0 D A) g x) = eH R i x := by
    simp [eH, LinearMap.sum_apply]
  have hproj : eH R i x = x ↔ ∀ v, R.eWf i (sg0 D A) ((R.HW i (sg0 D A)).e x v) = (R.HW i (sg0 D A)).e x v := by
    constructor
    · intro h v
      rw [GlobalTheory.GalLift.Transl.proj R i hg, hsum, h]
    · intro h
      apply (hW i _).1
      ext v : 1
      rw [← h v, GlobalTheory.GalLift.Transl.proj R i hg, hsum]
  unfold RealDat.Wat
  rw [mem_goodPart, GlobalTheory.MultMem.mem_mult_iff, hproj]
  have hmem : ∀ p : F.P0, R.eG p ∈ (R.levL F false (sg0 D A)).H := fun p => by
    show R.eG.symm (R.eG p) ∈ F.P0
    rw [MulEquiv.symm_apply_apply]; exact p.2
  have hchi : ∀ p : F.P0, (((R.levL F false (sg0 D A)).chi ⟨R.eG p, hmem p⟩ : ℂˣ) : ℂ) =
      sg0 D A ((F.ψ0⁻¹ p : D.what₂.LLˣ) : D.what₂.LL) := fun p => by
    show sg0 D A ((F.ψ0⁻¹ ⟨R.eG.symm (R.eG p), _⟩ : D.what₂.LLˣ) : D.what₂.LL) = _
    congr 4
    exact R.eG.symm_apply_apply _
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun p => ?_⟩
    apply (hW i _).1
    rw [hg, map_smul]
    ext v h
    have h3 := GlobalTheory.LevelRows.levelType_eigenfunction_of_liftable_element (V := Wc D i) (β := R.βW i) (L := R.datWp i R.triv)
      (P := R.levL F false (sg0 D A)) (F := (R.HW i (sg0 D A)).e x v) (fun κ hκ h => h1.lev v κ hκ h) ⟨R.eG p, hmem p⟩ (hl _)
    exact (congrFun h3 h).trans (congrArg (· * (R.HW i (sg0 D A)).e x v h) (hchi p))
  · rintro ⟨h2, h⟩
    refine ⟨⟨hm.aut, hm.cusp, fun v => ?_, hm.equiv, hm.cont⟩, h2⟩
    have hP : IsPLevel (Wc D i) (R.βW i) (R.datWp i R.triv) (R.levL F false (sg0 D A)) ((R.HW i (sg0 D A)).e x v) := by
      refine ⟨hT v, fun p => ?_⟩
      have hp : R.eG.symm p.1 ∈ F.P0 := p.2
      have h4 := congrArg (fun z => (R.HW i (sg0 D A)).e z v) (h ⟨R.eG.symm p.1, hp⟩)
      simp only [hg _ _ _ x, map_smul] at h4
      have h5 : R.eG (R.eG.symm p.1) = p.1 := R.eG.apply_symm_apply p.1
      rw [h5] at h4
      exact h4
    exact fun κ hκ y => hP.hasType κ hκ y

end GlobalTheory.Hk3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodFormsBaseLevelIffGoodProjectionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodForms_baseLevel_iff_goodProjection : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ i (x : (R.HW i (sg0 D A)).H), (R.HW i _).e x ∈ R.Wat i (sg0 D A) (R.levL F false (sg0 D A)) ↔ eH R i x = x ∧ ∀ p : F.P0, R.gW i (sg0 D A) p x = sg0 D A ((F.ψ0⁻¹ p : D.what₂.LLˣ) : D.what₂.LL) • x := by
  first | exact @GlobalTheory.Hk3.goodForms_baseLevel | exact GlobalTheory.Hk3.goodForms_baseLevel | (intros; apply GlobalTheory.Hk3.goodForms_baseLevel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharPolEqOfDegNeZero
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem trace_eq_of_trace_mul_pow {n m : ℕ} (A S : Matrix (Fin n) (Fin n) ℂ) (B T : Matrix (Fin m) (Fin m) ℂ)
    (hA : IsUnit A.det) (hB : IsUnit B.det)
    (h : ∀ i : ℕ, 1 ≤ i → (S * A ^ i).trace = (T * B ^ i).trace) : S.trace = T.trace := by
  set P := A.charpoly * B.charpoly with hP
  have hPA : Polynomial.aeval A P = 0 := by
    rw [hP, map_mul, Matrix.aeval_self_charpoly, zero_mul]
  have hPB : Polynomial.aeval B P = 0 := by
    rw [hP, map_mul, Matrix.aeval_self_charpoly, mul_zero]
  have eA := congrArg (fun M => (S * M).trace) hPA
  have eB := congrArg (fun M => (T * M).trace) hPB
  simp only [Polynomial.aeval_eq_sum_range, Finset.mul_sum, Matrix.trace_sum, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, mul_zero, Matrix.trace_zero] at eA eB
  rw [Finset.sum_range_succ'] at eA eB
  have hs : ∑ i ∈ Finset.range P.natDegree, P.coeff (i + 1) * (S * A ^ (i + 1)).trace =
      ∑ i ∈ Finset.range P.natDegree, P.coeff (i + 1) * (T * B ^ (i + 1)).trace :=
    Finset.sum_congr rfl fun i _ => by rw [h (i + 1) (by omega)]
  rw [hs] at eA
  have e0 : P.coeff 0 * (S * A ^ 0).trace = P.coeff 0 * (T * B ^ 0).trace := by linear_combination eA - eB
  simp only [pow_zero, Matrix.mul_one] at e0
  have hc : P.coeff 0 ≠ 0 := by
    rw [hP, Polynomial.mul_coeff_zero]
    refine mul_ne_zero (fun h0 => hA.ne_zero ?_) (fun h0 => hB.ne_zero ?_)
    · rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero]
    · rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero]
  exact mul_left_cancel₀ hc e0

end GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem charpoly_eq_toMatrix' {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) :
    f.charpoly = (LinearMap.toMatrix' f).charpoly := by
  rw [← LinearMap.charpoly_toMatrix f (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']

theorem trace_eq_of_charpoly_eq {n : ℕ} {M M' : Matrix (Fin n) (Fin n) ℂ} (e : M.charpoly = M'.charpoly) :
    M.trace = M'.trace := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · simp [Matrix.trace]
  · rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, e]

theorem charPol_eq_of_deg_ne_zero : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (x y : WD h), (∀ σ : Weil h, deg σ ≠ 0 → x.charPol σ = y.charPol σ) → ∀ σ : Weil h, x.charPol σ = y.charPol σ := by
  intro K Ω _ _ _ _ _ A v h x y hxy σ
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  obtain ⟨m, b, rfl⟩ := WD.exists_rep y
  simp only [WD.charPol_mk] at hxy ⊢
  have hnm : n = m := by
    have e := congrArg Polynomial.natDegree (hxy (frob h) (by rw [deg_frob]; exact one_ne_zero))
    rwa [LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree, Module.finrank_fin_fun,
      Module.finrank_fin_fun] at e
  subst hnm
  by_cases hσ : deg σ = 0
  swap
  · exact hxy σ hσ

  have hMA : ∀ τ : Weil h, LinearMap.toMatrix' (a.ρ τ) = (a.toGL τ : Matrix (Fin n) (Fin n) ℂ) :=
    fun τ => (WDRep.coe_toGL a τ).symm
  have hMB : ∀ τ : Weil h, LinearMap.toMatrix' (b.ρ τ) = (b.toGL τ : Matrix (Fin n) (Fin n) ℂ) :=
    fun τ => (WDRep.coe_toGL b τ).symm
  have hne : ∀ τ : Weil h, deg τ ≠ 0 →
      (a.toGL τ : Matrix (Fin n) (Fin n) ℂ).trace = (b.toGL τ : Matrix (Fin n) (Fin n) ℂ).trace := by
    intro τ hτ
    refine trace_eq_of_charpoly_eq ?_
    rw [← hMA, ← hMB, ← charpoly_eq_toMatrix', ← charpoly_eq_toMatrix']
    exact hxy τ hτ
  have hall : ∀ τ : Weil h,
      (a.toGL τ : Matrix (Fin n) (Fin n) ℂ).trace = (b.toGL τ : Matrix (Fin n) (Fin n) ℂ).trace := by
    intro τ
    by_cases hτ : deg τ = 0
    swap
    · exact hne τ hτ
    refine trace_eq_of_trace_mul_pow (a.toGL (frob h) : Matrix (Fin n) (Fin n) ℂ) _
      (b.toGL (frob h) : Matrix (Fin n) (Fin n) ℂ) _
      ((Matrix.isUnit_iff_isUnit_det _).1 (a.toGL (frob h)).isUnit)
      ((Matrix.isUnit_iff_isUnit_det _).1 (b.toGL (frob h)).isUnit) fun i hi => ?_
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← Units.val_mul,
      ← map_pow, ← map_pow, ← map_mul, ← map_mul]
    refine hne _ ?_
    rw [deg_mul, deg_pow, hτ, deg_frob]
    omega
  rw [charpoly_eq_toMatrix', charpoly_eq_toMatrix', hMA, hMB]
  refine GlobalTheory.QuadKernelConj.charpoly_eq_of_trace_pow _ _ fun j => ?_
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
  exact hall _

end GlobalTheory.AboveL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteSkewHermitianValuationMaxQuotSum
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteSkewHermitianValuationMaxQuotSum
open Matrix

namespace GlobalTheory.Hk3.GramSep

theorem gam_quot_finite : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧ ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K) →
  ∀ (r : ℕ) (e : Fin r → ℕ), Finite (↥(GlobalTheory.Hk3.GramSep.gam σ ϖ e) ⧸
    (GlobalTheory.Hk3.GramSep.gam0 σ ϖ e).addSubgroupOf (GlobalTheory.Hk3.GramSep.gam σ ϖ e)) := by
  intro L _ _ ϖ σ hϖ hR r e
  classical
  have hle1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ]
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) ≤ 1)
  set K : ℕ := ∑ k, ∑ j, (e k + e j) with hK
  obtain ⟨R, -, hRc⟩ := hR K
  have hKge : ∀ k j, e k + e j ≤ K := by
    intro k j
    have h1 : e k + e j ≤ ∑ j', (e k + e j') :=
      Finset.single_le_sum (f := fun j' => e k + e j') (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 : ∑ j', (e k + e j') ≤ ∑ k', ∑ j', (e k' + e j') :=
      Finset.single_le_sum (f := fun k' => ∑ j', (e k' + e j')) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    exact h1.trans h2
  have hint : ∀ Γ : ↥(gam σ ϖ e), ∀ k j, (Γ : Matrix (Fin r) (Fin r) L) k j ∈ Formalism.UG.intL L := by
    intro Γ k j
    show Valued.v ((Γ : Matrix (Fin r) (Fin r) L) k j) ≤ 1
    exact (Γ.2.2 k j).trans (pow_le_one' hle1 _)
  have hch : ∀ Γ : ↥(gam σ ϖ e), ∀ k j, ∃ x ∈ R, Valued.v ((Γ : Matrix (Fin r) (Fin r) L) k j - x) ≤ Valued.v ϖ ^ K :=
    fun Γ k j => hRc _ (hint Γ k j)
  let g : ↥(gam σ ϖ e) → (Fin r → Fin r → ↥R) := fun Γ k j => ⟨(hch Γ k j).choose, (hch Γ k j).choose_spec.1⟩
  have hg : ∀ (Γ : ↥(gam σ ϖ e)) k j, Valued.v ((Γ : Matrix (Fin r) (Fin r) L) k j - (g Γ k j : L)) ≤ Valued.v ϖ ^ K :=
    fun Γ k j => (hch Γ k j).choose_spec.2
  let h : (↥(gam σ ϖ e) ⧸ (gam0 σ ϖ e).addSubgroupOf (gam σ ϖ e)) → (Fin r → Fin r → ↥R) :=
    fun q => g (Quotient.out q)
  have hinj : Function.Injective h := by
    intro q1 q2 hq
    rw [← QuotientAddGroup.out_eq' q1, ← QuotientAddGroup.out_eq' q2, QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    set a := Quotient.out q1
    set b := Quotient.out q2
    have hab : g a = g b := hq
    have hmem : ((-a + b : ↥(gam σ ϖ e)) : Matrix (Fin r) (Fin r) L) ∈ gam σ ϖ e := (-a + b).2
    refine ⟨hmem.1, fun k j => ?_⟩
    have e1 : ((-a + b : ↥(gam σ ϖ e)) : Matrix (Fin r) (Fin r) L) k j
        = ((b : Matrix (Fin r) (Fin r) L) k j - (g b k j : L)) - ((a : Matrix (Fin r) (Fin r) L) k j - (g a k j : L)) := by
      rw [hab]; simp; ring
    rw [e1]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    · exact (hg b k j).trans (pow_le_pow_right_of_le_one' hle1 (hKge k j))
    · exact (hg a k j).trans (pow_le_pow_right_of_le_one' hle1 (hKge k j))
  exact Finite.of_injective h hinj

end GlobalTheory.Hk3.GramSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteSkewHermitianValuationMaxQuotSumStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_skewHermitian_valuationMax_quot_sum : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧ ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K) →
  ∀ (r : ℕ) (e : Fin r → ℕ), Finite (↥(GlobalTheory.Hk3.GramSep.gam σ ϖ e) ⧸
    (GlobalTheory.Hk3.GramSep.gam0 σ ϖ e).addSubgroupOf (GlobalTheory.Hk3.GramSep.gam σ ϖ e)) := by
  first | exact @GlobalTheory.Hk3.GramSep.gam_quot_finite | exact GlobalTheory.Hk3.GramSep.gam_quot_finite | (intros; apply GlobalTheory.Hk3.GramSep.gam_quot_finite <;> assumption)
end
end
