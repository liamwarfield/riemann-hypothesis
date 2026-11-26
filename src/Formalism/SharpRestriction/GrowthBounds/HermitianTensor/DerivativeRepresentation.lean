module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfLoZero
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetFactsPAlt

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DerivativeRepresentation
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def qcOm (n s : ℕ) : Fin n → ℕ := fun t => if t.val < s then 1 else 0

theorem qc_shapeDeg_succ {n K : ℕ} (sz : Fin (K + 1) → ℕ) :
    (shapeDeg sz : Fin n → ℕ) = qcOm n (sz 0) + shapeDeg (fun k : Fin K => sz k.succ) := by
  funext t
  simp only [shapeDeg, qcOm, Pi.add_apply, Finset.card_filter]
  rw [Fin.sum_univ_succ]

theorem qc_shapeDeg_zero {n : ℕ} (sz : Fin 0 → ℕ) : (shapeDeg sz : Fin n → ℕ) = 0 := by
  funext t
  simp [shapeDeg]

theorem qc_initMinor_mem (R : Type) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    initMinor R I hs ∈ dualWeyl R r n (qcOm n s) := by
  have h := bidetMem R r n 1 (fun _ => s) (fun _ => hs) (fun _ => I)
  have h1 : bideterminant R (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) = initMinor R I hs := by
    simp [bideterminant]
  have h2 : (shapeDeg (fun _ : Fin 1 => s) : Fin n → ℕ) = qcOm n s := by
    funext t
    simp only [shapeDeg, qcOm, Finset.card_filter]
    simp
  rw [h1, h2] at h
  exact h

theorem qc_bidet_succ (R : Type) [CommRing R] {r n K : ℕ} (sz : Fin (K + 1) → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    bideterminant R sz hsz I = initMinor R (I 0) (hsz 0) *
      bideterminant R (fun k : Fin K => sz k.succ) (fun k => hsz k.succ) (fun k => I k.succ) := by
  unfold bideterminant
  rw [Fin.prod_univ_succ]

theorem qc_bidet_zero (R : Type) [CommRing R] {r n : ℕ} (sz : Fin 0 → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) : bideterminant R sz hsz I = 1 := by
  simp [bideterminant]

theorem qc_pow_mem (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (y : MvPolynomial (Fin r × Fin n) R)
    (hy : y ∈ dualWeyl R r n ν) (k : ℕ) : y ^ k ∈ dualWeyl R r n (k • ν) := by
  induction k with
  | zero => rw [pow_zero, zero_smul]; exact one_mem_dualWeyl R r n
  | succ k ih => rw [pow_succ, succ_nsmul]; exact dualWeyl_mul R r n _ _ ih hy

theorem qc_full_minor (A : Type) [CommRing A] (r s : ℕ) (hs : s ≤ r) (I : Fin s → Fin r) (hI : StrictMono I)
    (h : s = r) : initMinor A I hs = detY A r := by
  subst h
  have hid : I = id := by
    exact (StrictMono.range_inj_of_wellFoundedLT hI strictMono_id).1
      (by rw [Set.range_id]; exact (Finite.injective_iff_surjective.1 hI.injective).range_eq)
  subst hid
  rfl

theorem qc_empty_minor (A : Type) [CommRing A] {r n : ℕ} (s : ℕ) (hs : s ≤ n) (I : Fin s → Fin r) (h : s = 0) :
    initMinor A I hs = 1 := by
  subst h
  unfold initMinor
  exact Matrix.det_isEmpty

theorem qcOm_zero (n : ℕ) : qcOm n 0 = 0 := by
  funext t
  simp [qcOm]

theorem qc_detDiv_bidet (A : Type) [CommRing A] (r : ℕ) : ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ r)
    (I : ∀ k, Fin (sz k) → Fin r), (∀ k, StrictMono (I k)) →
    ∃ (n : ℕ) (γ : Fin r → ℕ) (u₀ : MvPolynomial (Fin r × Fin r) A), (∀ t, shapeDeg sz t = γ t + n) ∧
      (∀ t : Fin r, t.val + 1 = r → γ t = 0) ∧ u₀ ∈ dualWeyl A r r γ ∧ bideterminant A sz hsz I = detY A r ^ n * u₀ := by
  intro K
  induction K with
  | zero =>
    intro sz hsz I _
    exact ⟨0, 0, 1, by intro t; rw [qc_shapeDeg_zero]; rfl, fun _ _ => rfl, one_mem_dualWeyl A r r,
      by rw [qc_bidet_zero, pow_zero, one_mul]⟩
  | succ K ih =>
    intro sz hsz I hI
    obtain ⟨n, γ, u₀, h1, h2, h3, h4⟩ :=
      ih (fun k => sz k.succ) (fun k => hsz k.succ) (fun k => I k.succ) (fun k => hI k.succ)
    by_cases hr : sz 0 = r
    · refine ⟨n + 1, γ, u₀, ?_, h2, h3, ?_⟩
      · intro t
        rw [qc_shapeDeg_succ, Pi.add_apply, h1 t]
        have : qcOm r (sz 0) t = 1 := by
          unfold qcOm
          rw [ite_eq_left (by rw [hr]; exact t.isLt)]
        omega
      · rw [qc_bidet_succ, h4, qc_full_minor A r _ (hsz 0) (I 0) (hI 0) hr]
        ring
    · refine ⟨n, qcOm r (sz 0) + γ, initMinor A (I 0) (hsz 0) * u₀, ?_, ?_,
        dualWeyl_mul A r r _ _ (qc_initMinor_mem A (I 0) (hsz 0)) h3, ?_⟩
      · intro t
        rw [qc_shapeDeg_succ, Pi.add_apply, Pi.add_apply, h1 t]
        omega
      · intro t ht
        rw [Pi.add_apply, h2 t ht, add_zero]
        unfold qcOm
        rw [ite_eq_right]
        have := hsz 0
        omega
      · rw [qc_bidet_succ, h4]
        ring

theorem detDivP : DetDivP := by
  intro A _ _ r Q β hr hβ u hu
  obtain ⟨b, ⟨-, hspan, -⟩, hb⟩ := sSBasis A r r (fun j => β j + Q)
  rw [← hspan] at hu
  refine Submodule.span_induction (p := fun u _ => ∃ u₀ ∈ dualWeyl A r r β, u = detY A r ^ Q * u₀) ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨m, rfl⟩
    obtain ⟨-, -, K, sz, hsz, I, hsh, hI, hbm⟩ := hb m
    obtain ⟨n, γ, u₀, h1, h2, h3, h4⟩ := qc_detDiv_bidet A r K sz hsz I hI
    have h1' : ∀ t, β t + Q = γ t + n := by
      intro t
      have := h1 t
      rwa [hsh] at this
    have hl : γ ⟨r - 1, by omega⟩ = 0 := h2 _ (by show r - 1 + 1 = r; omega)
    have hn : Q ≤ n := by
      have := h1' ⟨r - 1, by omega⟩
      omega
    refine ⟨detY A r ^ (n - Q) * u₀, ?_, ?_⟩
    · have hd : detY A r ∈ dualWeyl A r r (qcOm r r) := by
        rw [← qc_full_minor A r r le_rfl id strictMono_id rfl]
        exact qc_initMinor_mem A id le_rfl
      have h5 := dualWeyl_mul A r r _ _ (qc_pow_mem A r r _ _ hd (n - Q)) h3
      have e : (n - Q) • qcOm r r + γ = β := by
        funext t
        have := h1' t
        simp only [Pi.add_apply, Pi.smul_apply, qcOm, t.isLt, ite_true, smul_eq_mul, mul_one]
        omega
      rwa [e] at h5
    · rw [hbm, h4, ← mul_assoc, ← pow_add]
      congr 2
      omega
  · exact ⟨0, Submodule.zero_mem _, by rw [mul_zero]⟩
  · rintro x y _ _ ⟨a, ha, rfl⟩ ⟨b', hb', rfl⟩
    exact ⟨a + b', Submodule.add_mem _ ha hb', by rw [mul_add]⟩
  · rintro c x _ ⟨a, ha, rfl⟩
    exact ⟨c • a, Submodule.smul_mem _ _ ha, by rw [mul_smul_comm]⟩

end Formalism.MainNotions.flipOneThree.Pf

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetYNeZero
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem detY_ne_zero (K : Type) [Field K] (r : ℕ) : detY K r ≠ 0 :=
  Matrix.det_mvPolynomialX_ne_zero (Fin r) K

theorem qPh_of (hTau : TauP) (hSm : SmithP) (hBil : BilinP) (hDet : DetFactsP) (hNum : NumP) (hDD : DetDivP) : QPh := by
  intro p n' R r hr a c N α hαA hαN hc hca
  letI := R.charZeroO
  haveI := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  obtain ⟨e, he_def⟩ : ∃ e, α (Fin.last m) = e := ⟨_, rfl⟩
  have he : ∀ i, e ≤ α i := fun i => he_def ▸ hαA (Fin.le_last i)
  have hex : ∃ i, α i = e := ⟨_, he_def⟩
  have heN : e ≤ N := he_def ▸ hαN _
  have hγA : Antitone (fun i => α i - e) := by
    intro i j hij
    have := hαA hij
    show α j - e ≤ α i - e
    omega
  have wtK : ∀ {ν ν' : Fin (m + 1) → ℕ} {f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf},
      ν = ν' → f ∈ dualWeyl R.Kf (m + 1) (m + 1) ν → f ∈ dualWeyl R.Kf (m + 1) (m + 1) ν' := by
    rintro _ _ _ rfl h
    exact h
  have wtO : ∀ {ν ν' : Fin (m + 1) → ℕ} {f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.O},
      ν = ν' → f ∈ dualWeyl R.O (m + 1) (m + 1) ν → f ∈ dualWeyl R.O (m + 1) (m + 1) ν' := by
    rintro _ _ _ rfl h
    exact h
  have hwα : (fun j => (fun i => α i - e) j + e) = α := by
    funext j
    have := he j
    simp only
    omega
  obtain ⟨τ, hτK, hτO, hτsurj, hτeq⟩ := hTau R.O R.Kf hinj (m + 1) N e α (by omega) hαA hαN he hex
  obtain ⟨B, hBeq, hBint, nb, x, x', ka, hnb, hka, hx, hx', hdual⟩ :=
    hSm p n' R m (fun i => α i - e) hγA (by simp [he_def])
  set D : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf := detY R.Kf (m + 1) ^ e with hD_def
  have hD0 : D ≠ 0 := pow_ne_zero _ (detY_ne_zero R.Kf _)
  let μ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf := LinearMap.mulLeft R.Kf D
  have hμ : Function.Injective μ := fun u v h => mul_left_cancel₀ hD0 h
  obtain ⟨Cc, hCc⟩ := Submodule.exists_isCompl (LinearMap.range μ)
  let σ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf :=
    (LinearEquiv.ofInjective μ hμ).symm.toLinearMap ∘ₗ (LinearMap.range μ).projectionOnto Cc hCc
  have hσ : ∀ g, σ (D * g) = g := by
    intro g
    have hmem : D * g ∈ LinearMap.range μ := ⟨g, rfl⟩
    show (LinearEquiv.ofInjective μ hμ).symm ((LinearMap.range μ).projectionOnto Cc hCc (D * g)) = g
    rw [show D * g = ((⟨D * g, hmem⟩ : LinearMap.range μ) : MvPolynomial _ _) from rfl,
      Submodule.linearProjOfIsCompl_apply_left hCc, LinearEquiv.symm_apply_eq]
    ext1
    rw [LinearEquiv.ofInjective_apply]
    rfl
  obtain ⟨L, hL⟩ := hBil R.Kf (m + 1) ((B.compl₂ τ) ∘ₗ σ)
  have hL' : ∀ f f', L ((blockEmb R.Kf true) f * (blockEmb R.Kf false) f') = B (σ f) (τ f') := by
    intro f f'
    rw [hL]
    rfl
  have hmapD : map (algebraMap R.O R.Kf) (detY R.O (m + 1) ^ e) = D := by
    rw [map_pow, detY_map]
  have hdivK : ∀ f ∈ dualWeyl R.Kf (m + 1) (m + 1) α,
      ∃ g ∈ dualWeyl R.Kf (m + 1) (m + 1) (fun i => α i - e), f = D * g := by
    intro f hf
    exact hDD R.Kf (m + 1) e (fun i => α i - e) (by omega) hγA f (wtK hwα.symm hf)
  have hdivO : ∀ f ∈ intO R.O (m + 1) α,
      ∃ g ∈ intO R.O (m + 1) (fun i => α i - e), f = D * g := by
    intro f hf
    obtain ⟨fO, hfO, rfl⟩ := Submodule.mem_map.1 hf
    obtain ⟨gO, hgO, hfg⟩ := hDD R.O (m + 1) e (fun i => α i - e) (by omega) hγA fO (wtO hwα.symm hfO)
    refine ⟨map (algebraMap R.O R.Kf) gO, Submodule.mem_map.2 ⟨gO, hgO, rfl⟩, ?_⟩
    show map (algebraMap R.O R.Kf) fO = _
    rw [hfg, map_mul, hmapD]
  choose U hU hτU using fun a' => hτsurj (x' a') (hx' a')
  refine ⟨L, ?_, ?_, nb, fun b => D * x b, U, ka, ?_, ?_, ?_, hU, ?_⟩
  · intro l hl f hf f' hf'
    obtain ⟨g, hg, rfl⟩ := hdivK f hf
    rw [hL', hL', hσ]
    have hrD : rowAct R.Kf l (D * g) = D * (l.det ^ e • rowAct R.Kf l g) := by
      rw [map_mul, hD_def, map_pow, (hDet R.Kf (m + 1) e).2 l, MvPolynomial.smul_eq_C_mul, map_pow]
      ring
    rw [hrD, hσ, map_smul, LinearMap.smul_apply, hBeq, hτeq l hl f' hf', map_smul, smul_eq_mul,
      smul_eq_mul, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' heN]
  · intro f hf f' hf'
    obtain ⟨g, hg, rfl⟩ := hdivO f hf
    rw [hL', hσ]
    exact hBint g hg (τ f') (hτO f' hf')
  · rw [hnb]
    unfold weylDim
    refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => ?_))
    simp only [Nat.cast_sub (he i), Nat.cast_sub (he j), sub_sub_sub_cancel_right]
  · intro b
    refine (hka b).trans ?_
    have h1 := hc 0 (Fin.last m)
    exact hNum p a c (m + 1) (α 0 - e) R.std.1.prime.two_le (by omega) (by omega) hca
  · intro b
    obtain ⟨xO, hxO, hxe⟩ := Submodule.mem_map.1 (hx b)
    refine Submodule.mem_map.2 ⟨detY R.O (m + 1) ^ e * xO,
      wtO (by funext j; have := he j; simp only [Pi.add_apply]; omega)
        (dualWeyl_mul R.O (m + 1) (m + 1) _ _ (hDet R.O (m + 1) e).1 hxO), ?_⟩
    show map (algebraMap R.O R.Kf) (detY R.O (m + 1) ^ e * xO) = D * x b
    rw [map_mul, hmapD, ← hxe]
    rfl
  · intro a' b
    rw [hL', hσ, hτU]
    exact hdual a' b

end Formalism.MainNotions.flipOneThree.Pf

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.SubYDPsiMonomial
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem midOf_zero (r : ℕ) : midOf (0 : Fin (r + 1 + 1)) = none := by
  unfold midOf
  rw [dite_eq_right]
  simp

theorem subY_X_zero (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) : subY A r (X (a, 0)) = X (a, 0) := by
  simp only [subY, aeval_X, midOf_zero]

theorem subY_X_mid (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) (j : Fin r) :
    subY A r (X (a, midI r j)) = ∑ i : Fin r, C (X (i, j)) * X (a, midI r i) := by
  simp only [subY, aeval_X, midOf_midI]

def dOneY (A : Type) [CommRing A] (r : ℕ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A)) :=
  fun s t => Fin.cases (Fin.cases 1 (fun _ => 0) t) (fun s' => Fin.cases 0 (fun t' => C (X (s', t'))) t) s

theorem det_dOneY (A : Type) [CommRing A] (r : ℕ) : (dOneY A r).det = C (detY A r) := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have h0 : ∀ i : Fin r, dOneY A r i.succ 0 = 0 := fun i => rfl
  have h1 : dOneY A r 0 0 = 1 := rfl
  simp only [h0, h1, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]
  unfold detY
  have h := RingHom.map_det (C : MvPolynomial (Fin r × Fin r) A →+*
    MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A))
    (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A))
  refine Eq.trans ?_ h.symm
  congr 1

theorem subY_covY (K : Type) [Field K] (r : ℕ) (i : Fin (r + 1 + 1)) :
    subY K r (covY K (r + 1) i) = C (detY K r) * map C (covY K (r + 1) i) := by
  unfold covY
  rw [map_mul, map_mul, map_pow, map_pow, map_neg, map_neg, map_one, map_one]
  have hA := AlgHom.map_det (subY K r)
    (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K))
  have hB := RingHom.map_det (map (C : K →+* MvPolynomial (Fin r × Fin r) K))
    (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K))
  have hM : (subY K r).mapMatrix
      (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) =
      (map (C : K →+* MvPolynomial (Fin r × Fin r) K)).mapMatrix
        (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) *
        dOneY K r := by
    apply Matrix.ext
    intro a b
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    induction b using Fin.cases with
    | zero =>
      have h0 : ∀ s : Fin r, dOneY K r s.succ 0 = 0 := fun s => rfl
      have h1 : dOneY K r 0 0 = 1 := rfl
      simp only [h0, h1, mul_zero, Finset.sum_const_zero, add_zero, mul_one]
      show subY K r (X (i.succAbove a, (0 : Fin (r + 1)).castSucc)) = map C (X (i.succAbove a, (0 : Fin (r + 1)).castSucc))
      rw [Fin.castSucc_zero, subY_X_zero, map_X]
    | succ j =>
      have h0 : dOneY K r 0 j.succ = 0 := rfl
      have h1 : ∀ s : Fin r, dOneY K r s.succ j.succ = C (X (s, j)) := fun s => rfl
      simp only [h0, h1, mul_zero, zero_add]
      show subY K r (X (i.succAbove a, j.succ.castSucc)) =
        ∑ s : Fin r, map C (X (i.succAbove a, s.succ.castSucc)) * C (X (s, j))
      have e : ∀ s : Fin r, s.succ.castSucc = midI r s := fun s => (Fin.succ_castSucc s).symm
      simp only [e, map_X]
      rw [subY_X_mid]
      exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  have hdet : subY K r (Matrix.det fun a b : Fin (r + 1) =>
      (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) =
      C (detY K r) * map C (Matrix.det fun a b : Fin (r + 1) =>
      (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) := by
    refine hA.trans ?_
    rw [hM, Matrix.det_mul, det_dOneY, mul_comm]
    congr 1
    exact hB.symm
  rw [hdet]
  ring

theorem subY_dPsi_monomial (K : Type) [Field K] (r : ℕ) (v : XY (r + 1 + 1) →₀ ℕ) (c : K) :
    subY K r (deltaB K (r + 1) (PsiXY K (r + 1) (monomial v c))) =
      C (detY K r ^ yDeg v) * map C (deltaB K (r + 1) (PsiXY K (r + 1) (monomial v c))) := by
  have hx : ∀ i : Fin (r + 1 + 1), deltaB K (r + 1) (PsiXY K (r + 1) (X (Sum.inl i))) = X (i, 0) := by
    intro i
    simp [PsiXY, deltaB]
  have hy : ∀ i : Fin (r + 1 + 1), deltaB K (r + 1) (PsiXY K (r + 1) (X (Sum.inr i))) = covY K (r + 1) i := by
    intro i
    simp only [PsiXY, deltaB, aeval_X, Sum.elim_inr, rename_rename]
    have : (Prod.snd ∘ Prod.mk false : Fin (r + 1 + 1) × Fin (r + 1 + 1) → Fin (r + 1 + 1) × Fin (r + 1 + 1)) = id := rfl
    rw [this, rename_id_apply]
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
  simp only [map_mul, map_prod, map_pow, hx, hy, subY_X_zero, subY_covY, mul_pow, Finset.prod_mul_distrib, map_X]
  have hC : subY K r (deltaB K (r + 1) (PsiXY K (r + 1) (C c))) = map C (deltaB K (r + 1) (PsiXY K (r + 1) (C c))) := by
    simp only [← algebraMap_eq, AlgHom.commutes]
    simp [algebraMap_eq]
  rw [hC]
  have hp : ∏ i : Fin (r + 1 + 1), (C (detY K r) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1))
      (MvPolynomial (Fin r × Fin r) K)) ^ v (Sum.inr i) = C (detY K r) ^ yDeg v := by
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  rw [hp]
  ring

theorem subMuP_of (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) : SubMuP := by
  intro p n' R r hr P Q F hF
  rw [← tie3 h2 h5 hCO R (r + 1) (by omega) P Q] at hF
  obtain ⟨f, hf, rfl⟩ := hF
  rw [dPsi_apply, f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [subY_dPsi_monomial, (hf v hv).2]

end Formalism.MainNotions.flipOneThree.Pf

end
end
