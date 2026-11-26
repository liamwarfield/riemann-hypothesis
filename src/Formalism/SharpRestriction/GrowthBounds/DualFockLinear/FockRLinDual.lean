module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneSidedLemma4Realisable
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FormCoreSK
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideEdge
public import Formalism.LocalToGlobal.GroupLattices.FockModels.DualInclusionLattices
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.TestFlat

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FockSumRight
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14
open Formalism.L2.G.Model (kapR kapR_alg)

theorem fock_sum_right {R : Type} [CommRing R] {τ : Type} {ι : Type} (s : Finset ι) (F : MvPolynomial τ R)
    (G : ι → MvPolynomial τ R) : fock F (∑ q ∈ s, G q) = ∑ q ∈ s, fock F (G q) := by
  simp only [fock, MvPolynomial.coeff_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem inWj_map {O : Type} [CommRing O] [IsDomain O] {τ : Type} (w : O) (P : MvPolynomial τ O) :
    InWj w (MvPolynomial.map (algebraMap O (KK O)) P) 0 := by
  intro m
  exact ⟨P.coeff m, by simp [MvPolynomial.coeff_map]⟩

theorem valLe_perturb {O Kf : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [Field Kf] [Algebra O Kf] (p : ℕ) (w : O)
    (hw : ¬ IsUnit w) (hsq : w ^ 2 = (p : O)) (D c : ℕ) (hc : 2 * D < c) (a b z : O) (hab : a * b = (p : O) ^ D) :
    ValLe (Kf := Kf) (p : O) D (algebraMap O Kf (a + w ^ c * z)) := by
  obtain ⟨k, hk⟩ : ∃ k, c = 2 * D + (k + 1) := ⟨c - 2 * D - 1, by omega⟩
  have hwc : w ^ c = (p : O) ^ D * w ^ (k + 1) := by rw [hk, pow_add, pow_mul, hsq]
  have hwk : w ^ (k + 1) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => hw ((isUnit_pow_iff (Nat.succ_ne_zero k)).1 h)
  have hm : b * w ^ (k + 1) * z ∈ IsLocalRing.maximalIdeal O :=
    Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hwk)

  have hu : IsUnit (1 + b * w ^ (k + 1) * z) := by
    by_contra hne
    have h1 : (1 + b * w ^ (k + 1) * z) ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).2 hne
    have h2 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ h1 hm
      simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h2)
  have ha' : a + w ^ c * z = a * (1 + b * w ^ (k + 1) * z) := by rw [hwc, ← hab]; ring
  refine ⟨a + w ^ c * z, b * ↑hu.unit⁻¹, rfl, ?_⟩
  rw [ha', mul_mul_mul_comm, IsUnit.mul_val_inv, mul_one, hab]


set_option maxHeartbeats 1600000 in
theorem restFlat_of (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hXi : RestXi D CLa Ck Crk Cdeg CH CE C6 C18) (hRe : RestReal D CLa Ck Crk Cdeg) :
    RestFlat D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 := by
  intro hA _ h14b
  obtain ⟨Ct0, CDf, C₂, h0, h1, hC2, hX⟩ := hXi hA h14b
  obtain ⟨C₃, hC3, hR⟩ := hRe hA
  obtain ⟨C6U, hC6U, h6⟩ := one_sided_lemma4_of_admitted_theorem_II
  have h6' := h6 D CLa Ck Crk Cdeg hA
  obtain ⟨C₄, hC4, hII⟩ := hypII_at C6U (C6U + 1) C6U
  refine ⟨Ct0, CDf, max (max C₂ C₃) (max C₄ CDf), h0, h1,
    lt_of_lt_of_le hC2 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro C hCC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis
  let _ : Algebra (WF p n') O := algOfIdent j φ
  intro FsB hFsB Θ hΘ
  have c2 : C₂ ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCC
  have c3 : C₃ ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCC
  have c4 : C₄ ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCC
  have c5 : CDf ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCC
  obtain ⟨tF, DX, htF, hDX, hxi⟩ := hX C c2 p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y
    cpp c0 Dp cStar hSet H φ hφ K hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ
  obtain ⟨gv, hgv, hreal⟩ := hR C c3 p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y
    cpp c0 Dp cStar hSet H φ hφ K hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ
  obtain ⟨hII1, hcP⟩ := hII C c4 p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar H F hFr
  have hBas := hyps_basic (C := C) (le_trans hC4 c4) H
  have hGn : goodG' r de h x ≤ n' := by have := H.2.2.1.2.2.2; omega
  have hH : CommonHypotheses p n' r (m + 1) := ⟨H.1, H.2.1, hrk, hSet.1.two_le, hSet.1.even⟩
  have hw0 : algebraMap O Kf w ≠ 0 := Formalism.L2.G.Model.w_ne hSet.1

  have hlog : 0 ≤ (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a := by
    have h2a := hBas.two_le_a
    have hp1 : (1 : ℝ) < (p : ℝ) := by
      have := H.1
      have : 1 < p := by omega
      exact_mod_cast this
    have : 0 ≤ Real.logb p a := Real.logb_nonneg hp1 (by linarith)
    positivity
  have hDp : (DX : ℝ) ≤ Dp := by
    have h10 : C * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a ≤ Dp := H.2.2.2.2.2.2.2.2.2.1
    have : CDf * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a ≤
        C * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a := by
      have e1 : ∀ t : ℝ, t * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a =
          t * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) := fun t => by ring
      rw [e1, e1]
      exact mul_le_mul_of_nonneg_right c5 hlog
    linarith
  have hDp' : DX ≤ Dp := by exact_mod_cast hDp
  have h2D : 2 * DX < cPrime n' r TT.card c0 cpp cStar := by
    have h11 : 8 * (Dp + 1) ≤ cStar := H.2.2.2.2.2.2.2.2.2.2.1
    unfold cPrime
    omega
  refine ⟨tF, DX, htF, hDX, ?_⟩
  intro F1 f1 f2 f3
  obtain ⟨nq, o, sig, hsig, hval⟩ := hxi F1 f1 f2 f3
  have hT : ∀ q, ∃ T : Module.Dual Kf (Vsp Kf (flW (m := m) (dT TT lam0))),
      T ∈ scale (algebraMap O Kf w ^ (-(tF : ℤ))) (dualLat O Kf (HL (O := O) ι σ (flW (dT TT lam0)) e.tgt)) ∧
      T ∈ Re' p ι σ w r (flW (dT TT lam0)) e ∧
      (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
        T ∈ scale (algebraMap O Kf w ^ ((cPrime n' r TT.card c0 cpp cStar : ℕ) : ℤ))
          (Re' p ι σ w r (flW (dT TT lam0)) e')) ∧
      ∃ z : O, be p r (flW (dT TT lam0)) (Θ F1) T =
        kapR hSet.1 ((p : KK O) ^ (kapFl p (m + 1) (dT TT lam0)) *
          fock (subst p n' O w n' r g (F1 : MvPolynomial (TV n' (m + 1)) (KK O))) (sig q) /
            (((∏ s, (dT TT lam0 s).factorial : ℕ) : ℕ) : KK O)) +
          algebraMap O Kf (w ^ (cPrime n' r TT.card c0 cpp cStar) * z) := by
    intro q
    obtain ⟨ho, hmd, hL4⟩ := hsig q
    have hint : InWj w (sig q) 0 := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hs⟩ := hL4
      rw [hs]
      exact inWj_map w _
    have hrl : Realisable p n' w n' r gv (cPrime n' r TT.card c0 cpp cStar) (o q) (sig q) := by
      rw [← hcP] at hL4 ⊢
      exact one_sided_lemma4_realisable D C6U (C6U + 1) C6U h6' O (dvrOfStd hSet) (oHyp_of hSet φ) hk hH F L₁ (orbitWindowCount r de h x)
        (goodG' r de h x) hFr.2.1 (twist_of hFr (by have := H.2.1; omega) hGn p (by have := H.1; omega))
        (flatDeg lam0) ⌈a⌉₊ Y c0 0 (cStar + 2 * r * n' * cpp) (Dp : ℝ) hII1 gv hgv (o q) (sig q) hL4
    obtain ⟨T, t1, t2, t3, t4⟩ := hreal (o q) (sig q) hmd hint hrl
    exact ⟨T, scale_neg_mono w hw0 ho _ t1, t2, t3, t4 F1 f2⟩
  choose T t1 t2 t3 z t4 using hT
  refine ⟨∑ q, T q, Submodule.sum_mem _ fun q _ => t1 q, Submodule.sum_mem _ fun q _ => t2 q,
    fun e' he' htg hne => Submodule.sum_mem _ fun q _ => t3 q e' he' htg hne, ?_⟩
  obtain ⟨aa, bb, hx1, hab⟩ := hval
  have hbe : be p r (flW (dT TT lam0)) (Θ F1) (∑ q, T q) =
      algebraMap O Kf (aa + w ^ (cPrime n' r TT.card c0 cpp cStar) * ∑ q, z q) := by
    have e1 : be p r (flW (dT TT lam0)) (Θ F1) (∑ q, T q) = ∑ q, be p r (flW (dT TT lam0)) (Θ F1) (T q) := by
      unfold be
      rw [LinearMap.sum_apply]
    rw [e1]
    simp only [t4, Finset.sum_add_distrib]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← Finset.sum_div, ← Finset.mul_sum, ← fock_sum_right, hx1, kapR_alg, map_add (f := _), ← map_sum,
      ← Finset.mul_sum]
  rw [hbe]
  exact valLe_perturb p w hSet.2.1.not_isUnit hSet.1.w_sq DX _ h2D aa bb _ hab

end Formalism.MainNotions.TestSideCounting
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.Pf14
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol)
open Formalism.L2.G.Model.TS

section Contra

variable {S : Type} [Fintype S] [DecidableEq S] {R : Type} [CommRing R] {k : ℕ}

theorem fock_eq_fockR {τ : Type} (F G : MvPolynomial τ R) : fock F G = fockR F G := rfl

theorem Lin_X (N : S → Matrix (Fin k) (Fin k) R) (v : S × Fin k) :
    Lin N (X v) = ∑ b : Fin k, C (N v.1 v.2 b) * X (v.1, b) := by
  simp [Lin]

theorem Lin_coeff_zero (N : S → Matrix (Fin k) (Fin k) R) (h : MvPolynomial (S × Fin k) R) :
    AddMonoidAlgebra.coeff (Lin N h) 0 = AddMonoidAlgebra.coeff h 0 := by
  have h1 : (MvPolynomial.constantCoeff : MvPolynomial (S × Fin k) R →+* R).comp (Lin N).toRingHom =
      MvPolynomial.constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro v
      simp [Lin]
  exact congrArg (fun φ : MvPolynomial (S × Fin k) R →+* R => φ h) h1

theorem Lin_chain (N : S → Matrix (Fin k) (Fin k) R) (s : S) (b : Fin k) (h : MvPolynomial (S × Fin k) R) :
    pderiv (s, b) (Lin N h) = ∑ a : Fin k, N s a b • Lin N (pderiv (s, a) h) := by
  have hX : ∀ v : S × Fin k, pderiv (s, b) (Lin N (X v)) = ∑ a : Fin k, N s a b • Lin N (pderiv (s, a) (X v)) := by
    rintro ⟨t, c⟩
    rw [Lin_X]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, MvPolynomial.pderiv_C, smul_zero, add_zero,
      Pi.single_apply, Prod.mk.injEq, smul_eq_mul]
    by_cases ht : t = s
    · subst ht
      simp [Finset.sum_ite_eq', Finset.sum_ite_eq, MvPolynomial.smul_eq_C_mul]
    · simp [ht]
  induction h using MvPolynomial.induction_on with
  | C r =>
    have h1 : Lin N (C r) = C r := (Lin N).commutes r
    simp [h1]
  | add p q hp hq =>
    simp only [map_add (f := _), hp, hq, smul_add, Finset.sum_add_distrib]
  | mul_X p v hp =>
    rw [map_mul, Derivation.leibniz, hp, hX v]
    simp only [Derivation.leibniz, map_add (f := _), map_mul, smul_add, Finset.sum_add_distrib, smul_eq_mul,
      Finset.mul_sum, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp only [MvPolynomial.smul_eq_C_mul]
      ring
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp only [MvPolynomial.smul_eq_C_mul]
      ring

theorem fockR_Lin (N : S → Matrix (Fin k) (Fin k) R) (P : MvPolynomial (S × Fin k) R) :
    ∀ Q : MvPolynomial (S × Fin k) R, fockR (Lin N P) Q = fockR P (Lin (fun s => (N s).transpose) Q) := _root_.Formalism.MainNotions.ColumnSystems.Pf.TF.fockR_Lin N P

theorem fockR_Lin_dual (A B : S → Matrix (Fin k) (Fin k) R) (h : ∀ s, B s * (A s).transpose = 1)
    (P Q : MvPolynomial (S × Fin k) R) : fockR (Lin A P) (Lin B Q) = fockR P Q := by
  rw [fockR_Lin, Lin_comp]
  simp only [h]
  rw [Lin_one]

end Contra

theorem Aa_dual {K : Type} [Field K] {m : ℕ} (vec : Bool) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hM : IsUnit M.det) : Aa vec ((M⁻¹).transpose)⁻¹ * (Aa vec M⁻¹).transpose = 1 := by
  have h1 : IsUnit (M⁻¹).det := Matrix.isUnit_nonsing_inv_det M hM
  have h2 : IsUnit ((M⁻¹).transpose).det := by rwa [Matrix.det_transpose]
  cases vec
  · simp only [Aa, Bool.false_eq_true, if_false]
    rw [Matrix.nonsing_inv_nonsing_inv _ h2, Matrix.transpose_transpose, Matrix.transpose_transpose,
      Matrix.nonsing_inv_nonsing_inv _ hM, Matrix.nonsing_inv_mul _ hM]
  · simp only [Aa, if_true]
    exact Matrix.nonsing_inv_mul _ h2

theorem multDiv_kapFl (O : Type) [CommRing O] [IsLocalRing O] (p : ℕ) [hp : Fact p.Prime]
    (hpO : (p : O) ∈ IsLocalRing.maximalIdeal O) {n' k : ℕ} (d : Fin n' → ℕ) :
    MultDiv O p (kapFl p k d) (k := k) d := by
  intro α hα

  have h1 : ∀ s, (d s).factorial = Nat.multinomial Finset.univ (fun c : Fin k => α (s, c)) *
      ∏ c : Fin k, (α (s, c)).factorial := by
    intro s
    rw [mul_comm, Nat.multinomial_spec, ← hα s]
    rfl
  have h2 : expFact α = ∏ s : Fin n', ∏ c : Fin k, (α (s, c)).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Fintype.prod_prod_type]
  set Mn : ℕ := ∏ s : Fin n', Nat.multinomial Finset.univ (fun c : Fin k => α (s, c)) with hMn
  have h3 : (∏ s, (d s).factorial) = Mn * expFact α := by
    rw [h2, hMn, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => h1 s
  have hMn0 : Mn ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => (Nat.multinomial_pos _ _).ne'
  have h4 : padicValNat p Mn ≤ kapFl p k d := by
    rw [hMn, Formalism.CountingSumsFrames.fock_val_prod p _ _ (fun s _ => (Nat.multinomial_pos _ _).ne')]
    unfold kapFl
    refine Finset.sum_le_sum fun s _ => ?_
    have := Formalism.CountingSumsFrames.fock_mult_val_le p (fun c : Fin k => α (s, c)) Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at this
    have e : ∑ c : Fin k, α (s, c) = d s := hα s
    rw [e] at this
    exact this

  have hdv : p ^ padicValNat p Mn ∣ Mn := (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  have hnd : ¬ p ^ (padicValNat p Mn + 1) ∣ Mn := by
    rw [Nat.padicValNat_def]
    exact pow_succ_multiplicity_not_dvd hMn0
  generalize padicValNat p Mn = v at h4 hdv hnd
  obtain ⟨u, hu⟩ := hdv
  have hpu : ¬ p ∣ u := by
    intro hd
    apply hnd
    rw [hu, pow_succ]
    exact Nat.mul_dvd_mul_left _ hd
  have huO : IsUnit ((u : ℕ) : O) := by
    have hco : Nat.Coprime u p := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpu).symm
    by_contra hnu
    have hm : ((u : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hnu
    have hb := Nat.gcd_eq_gcd_ab u p
    rw [hco] at hb
    have h5 : (1 : O) = (u : O) * ((Nat.gcdA u p : ℤ) : O) + (p : O) * ((Nat.gcdB u p : ℤ) : O) := by
      have := congrArg (fun z : ℤ => (z : O)) hb
      push_cast at this
      exact this
    have h6 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [h5]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hm) (Ideal.mul_mem_right _ _ hpO)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h6)
  obtain ⟨uu, huu⟩ := huO
  refine ⟨(p : O) ^ (kapFl p k d - v) * (↑uu⁻¹ : O), ?_⟩
  rw [h3, hu]
  push_cast
  rw [← huu]
  have e1 : (p : O) ^ kapFl p k d = (p : O) ^ v * (p : O) ^ (kapFl p k d - v) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e1]
  have e2 : (uu : O) * (↑uu⁻¹ : O) = 1 := Units.mul_inv uu
  linear_combination (-(p : O) ^ v * (p : O) ^ (kapFl p k d - v) * (expFact α : O)) * e2

end Formalism.MainNotions.TestSideCounting
