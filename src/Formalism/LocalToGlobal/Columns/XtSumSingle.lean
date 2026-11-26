module

public import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
public import Formalism.LocalToGlobal.Columns.StdBasisFlagSubmoduleOfBlockTriangular

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.XtSumSingle
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Std

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem xt_sum_single {a b : ℕ} (z : HomE E a b) (v : Sp E a) : z v = ∑ j, v j • z (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (Pi.single j (v j) : Sp E a) = v j • Pi.single j 1 := by rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul]

theorem xt_map_std {a b : ℕ} (z : HomE E a b) (hz : ∀ j l, IntAt P (z (Pi.single j 1) l)) {v : Sp E a} (hv : v ∈ stdAt E a P) :
    z v ∈ stdAt E b P := by
  rw [ciMem_stdAt] at hv ⊢
  intro l
  rw [xt_sum_single z v, Finset.sum_apply]
  exact ciIntAt_sum _ _ fun j _ => by
    rw [Pi.smul_apply, smul_eq_mul]
    exact (hv j).mul (hz j l)

end Std

section Law

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def TopLawG (m2 : ℕ) (Λm : LevFam X.E X.K (R.N (m2 + 1 + 1)) Pr.vGs) (b : L.β (m2 + 1)) : Prop :=
  ∀ (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs) (h : ↥(L.levG (m2 + 1) b ⟨w.1, hw⟩).H) (h' : ↥(Λm ⟨w.1, hw⟩).H)
    (κ : ↥(GLint X.E (R.N (m2 + 1)) w.1)) (κ' : ↥(GLint X.E (R.N (m2 + 1 + 1)) w.1)),
    (∀ x ∈ stdAt X.E (R.N (m2 + 1)) w.1, redV w.1 (κ.1 x) = (h.1⁻¹).1.mulVec (redV w.1 x)) →
    (∀ x ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1, redV w.1 (κ'.1 x) = (h'.1⁻¹).1.mulVec (redV w.1 x)) →
    ∀ y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1)), (∀ j l, IntAt w.1 (y (Pi.single j 1) l)) →
      rhoS Ch sel mu (m2 + 1) w (LinearEquiv.det κ.1 : X.Eˣ) * rhoT Ch sel mu (m2 + 1) w (LinearEquiv.det κ'.1 : X.Eˣ) *
          PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1 (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ
            (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) =
        (((Λm ⟨w.1, hw⟩).lam h' : X.Kˣ) : X.K) * ((((L.levG (m2 + 1) b ⟨w.1, hw⟩).lam h)⁻¹ : X.Kˣ) : X.K) *
          PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1 (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ
            LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))))

def LastRow {j : ℕ} (Λm : LevFam X.E X.K (R.N j) Pr.vGs) : Prop :=
  ∀ (w : Pr.vGs), ∀ h' ∈ (Λm w).H, ∀ l : Fin (R.N j),
    (h'.1 : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)) ⟨R.N j - 1, xt_last_lt R j⟩ l = if l.1 = R.N j - 1 then 1 else 0

variable {Ch sel mu cst L}

theorem topDat_law (hc : cst.Ok) {m2 : ℕ} (hn : TopNum R (m2 + 1)) {Λm : LevFam X.E X.K (R.N (m2 + 1 + 1)) Pr.vGs} {b : L.β (m2 + 1)}
    (hLaw : TopLawG Ch sel mu cst L m2 Λm b) (hRow : LastRow Λm)
    (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs) (h : ↥(L.levG (m2 + 1) b ⟨w.1, hw⟩).H) (h' : ↥(Λm ⟨w.1, hw⟩).H)
    (κ : ↥(GLint X.E (R.N (m2 + 1)) w.1)) (κ' : ↥(GLint X.E (R.N (m2 + 1 + 1)) w.1))
    (hκ : ∀ x ∈ stdAt X.E (R.N (m2 + 1)) w.1, redV w.1 (κ.1 x) = (h.1⁻¹).1.mulVec (redV w.1 x))
    (hκ' : ∀ x ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1, redV w.1 (κ'.1 x) = (h'.1⁻¹).1.mulVec (redV w.1 x))
    (hu : ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2)
    (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y₁ y₂ : Sp X.E (R.N (m2 + 1))) (hδ : κ.1 y₁ - y₂ ∈ stdAt X.E (R.N (m2 + 1)) w.1)
    (hq : ((qOf w.1 : ℕ) : X.E) • y₂ ∈ stdAt X.E (R.N (m2 + 1)) w.1) :
    rhoS Ch sel mu (m2 + 1) w (LinearEquiv.det κ.1 : X.Eˣ) * rhoT Ch sel mu (m2 + 1) w (LinearEquiv.det κ'.1 : X.Eˣ) *
        topDat Ch sel mu cst (m2 + 1) w (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) y₁ =
      (((Λm ⟨w.1, hw⟩).lam h' : X.Kˣ) : X.K) * ((((L.levG (m2 + 1) b ⟨w.1, hw⟩).lam h)⁻¹ : X.Kˣ) : X.K) *
        topDat Ch sel mu cst (m2 + 1) w y y₂ := by
  have hk : ∀ v, κ.1 v ∈ stdAt X.E (R.N (m2 + 1)) w.1 ↔ v ∈ stdAt X.E (R.N (m2 + 1)) w.1 := κ.2
  have hk' : ∀ v, κ'.1 v ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1 ↔ v ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1 := κ'.2
  by_cases hint : ∀ j l, IntAt w.1 (y (Pi.single j 1) l)
  ·
    have hF : ftY sel mu cst w (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap)) y₁ =
        ftY sel mu cst w (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y₂ := by
      have e1 : atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) =
          (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.1.symm.toLinearMap ∘ₗ y) ∘ₗ κ.1.toLinearMap := rfl
      rw [e1, ftY_move2 sel mu cst hc w hw κ _ y₂ y₁ hδ hq]
      set ζ : Sp X.E (R.N (m2 + 1)) →ₗ[X.E] X.E :=
        atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.1.symm.toLinearMap ∘ₗ y - atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y with hζdef
      have e2 : atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.1.symm.toLinearMap ∘ₗ y =
          atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y + ζ := by rw [hζdef]; abel

      have hζq : ∀ i, IntAt w.1 (ζ (Pi.single i 1) / (qOf w.1 : X.E)) := by
        intro i
        set v := y (Pi.single i 1) with hv
        have hvs : v ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1 := (ciMem_stdAt _ _).2 (hint i)
        have hvs' : κ'.1.symm v ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1 := (hk' _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hvs)
        have h1 := hκ' _ hvs'
        rw [LinearEquiv.apply_symm_apply] at h1
        have h2 : redV w.1 (κ'.1.symm v) = h'.1.1.mulVec (redV w.1 v) := by
          rw [h1, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
        have h3 : redP w.1 (κ'.1.symm v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩) = redP w.1 (v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩) := by
          have h20 := congrFun h2 ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩
          have e : (h'.1.1.mulVec (redV w.1 v)) ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ = redV w.1 v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ := by
            show ∑ l, h'.1.1 ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ l * redV w.1 v l = _
            rw [Finset.sum_eq_single (⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ : Fin (R.N (m2 + 1 + 1)))]
            · rw [hRow ⟨w.1, hw⟩ h'.1 h'.2 ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩, if_pos rfl, one_mul]
            · intro l _ hl
              rw [hRow ⟨w.1, hw⟩ h'.1 h'.2 l, if_neg (fun hh => hl (Fin.ext hh)), zero_mul]
            · intro hh
              exact absurd (Finset.mem_univ _) hh
          exact h20.trans e
        have ha := (ciMem_stdAt _ _).1 hvs' ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩
        have hb := (ciMem_stdAt _ _).1 hvs ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩
        have e3 : ζ (Pi.single i 1) = κ'.1.symm v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ - v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ := by
          rw [hζdef, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, xt_atNL, xt_atNL]
          rfl
        rw [e3]
        exact ciIntAt_div (ciQ_mem w.1) hu (ciIntAt_sub ha hb) (by rw [redP_sub ha hb, h3, sub_self])
      have hq0 : (qOf w.1 : X.E) ≠ 0 := ciQ_ne_zero hu
      have hζ : ∀ i, IntAt w.1 (ζ (Pi.single i 1)) := fun i => by
        have := (ciIntAt_q (q := qOf w.1)).mul (hζq i)
        rwa [mul_div_cancel₀ _ hq0] at this
      have hζy : IntAt w.1 (ζ y₂) := by
        have e4 : ζ y₂ = ∑ j, y₂ j * ζ (Pi.single j 1) := by
          conv_lhs => rw [← Finset.univ_sum_single y₂]
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          have : (Pi.single j (y₂ j) : Sp X.E (R.N (m2 + 1))) = y₂ j • Pi.single j 1 := by rw [← Pi.single_smul, smul_eq_mul, mul_one]
          rw [this, map_smul, smul_eq_mul]
        rw [e4]
        refine ciIntAt_sum _ _ fun j _ => ?_
        have h1 := (ciMem_stdAt _ _).1 hq j
        rw [Pi.smul_apply, smul_eq_mul] at h1
        have h2 := h1.mul (hζq j)
        have e5 : ((qOf w.1 : ℕ) : X.E) * y₂ j * (ζ (Pi.single j 1) / (qOf w.1 : X.E)) = y₂ j * ζ (Pi.single j 1) := by
          field_simp
        rwa [e5] at h2
      rw [e2]
      exact fourierTwist_add_integral sel mu cst hc w hw _ ζ y₂ hζ hζy hq
    unfold topDat
    rw [hF, ← mul_assoc, hLaw w hw h h' κ κ' hκ hκ' y hint, mul_assoc]
  ·
    have r0 : topDat Ch sel mu cst (m2 + 1) w y y₂ = 0 := by
      by_contra hne
      exact hint fun j l => topDat_int Ch sel mu cst hn w hw y y₂ hne j l
    have l0 : topDat Ch sel mu cst (m2 + 1) w (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) y₁ = 0 := by
      by_contra hne
      have hz := fun j l => topDat_int Ch sel mu cst hn w hw _ y₁ hne j l
      refine hint fun j l => ?_
      have h1 : κ.1.symm (Pi.single j 1) ∈ stdAt X.E (R.N (m2 + 1)) w.1 :=
        (hk _).1 (by rw [LinearEquiv.apply_symm_apply]; exact ciSingle_mem j)
      have h2 := xt_map_std _ hz h1
      have h3 : (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) (κ.1.symm (Pi.single j 1)) = κ'.1.symm (y (Pi.single j 1)) := by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [h3] at h2
      have h4 := (hk' _).2 h2
      rw [LinearEquiv.apply_symm_apply] at h4
      exact (ciMem_stdAt _ _).1 h4 l
    rw [r0, l0, mul_zero, mul_zero]

end Law

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.ReducedMatrixExtensionEntry
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Nat

theorem framePos_of_lt_dim {k₀ c n p : ℕ} (hp : p < n) : LocE.fPos k₀ c n p = if p < k₀ then p else p + c := by
  unfold LocE.fPos
  by_cases h : p < k₀
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_pos hp]

theorem beta_framePos_formula {k₀ rS t j c n p : ℕ} (hcj : c + j = 2 * rS + 1) (hp : p < n) :
    betaExponentOfRanks k₀ rS (k₀ + 2 * rS + 1) t (LocE.fPos k₀ c n p) =
      if p < k₀ then p + rS else if p < k₀ + j then (if p + c < k₀ + rS then p + c - k₀ else p + c)
        else k₀ + 2 * rS + 1 + (p - (k₀ + j)) / t := by
  rw [framePos_of_lt_dim hp]
  unfold betaExponentOfRanks
  by_cases h1 : p < k₀
  · rw [if_pos h1, if_pos h1, if_pos (show p < k₀ + 2 * rS + 1 by omega)]
    unfold symIdx
    rw [if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : p < k₀ + j
    · rw [if_pos h2, if_pos (show p + c < k₀ + 2 * rS + 1 by omega)]
      unfold symIdx
      rw [if_neg (show ¬ p + c < k₀ by omega)]
    · rw [if_neg h2, if_neg (show ¬ p + c < k₀ + 2 * rS + 1 by omega), show p + c - (k₀ + 2 * rS + 1) = p - (k₀ + j) by omega]

theorem not_allowed_of_beta_lt {k₀ rS t j c n p p' : ℕ} (hcj : c + j = 2 * rS + 1) (hp : p < n) (hp' : p' < n)
    (h : betaExponentOfRanks k₀ rS (k₀ + 2 * rS + 1) t (LocE.fPos k₀ c n p') < betaExponentOfRanks k₀ rS (k₀ + 2 * rS + 1) t (LocE.fPos k₀ c n p) ∨
      (LocE.fPos k₀ c n p < k₀ ∧ LocE.fPos k₀ c n p' = k₀ + rS)) : ¬ ocbXAllow k₀ rS j t p p' := by
  have a1 := Nat.zero_le ((p - (k₀ + j)) / t)
  have a2 := Nat.zero_le ((p' - (k₀ + j)) / t)
  rw [beta_framePos_formula hcj hp, beta_framePos_formula hcj hp', framePos_of_lt_dim hp, framePos_of_lt_dim hp'] at h
  unfold ocbXAllow
  split_ifs at h ⊢ <;> omega

theorem beta_lt_of_not_allowed {k₀ rS t j c n p p' : ℕ} (hcj : c + j = 2 * rS + 1) (hp : p < n) (hp' : p' < n) (hne : p ≠ p')
    (h : ¬ ocbXAllow k₀ rS j t p p') :
    betaExponentOfRanks k₀ rS (k₀ + 2 * rS + 1) t (LocE.fPos k₀ c n p') < betaExponentOfRanks k₀ rS (k₀ + 2 * rS + 1) t (LocE.fPos k₀ c n p) ∨
      (LocE.fPos k₀ c n p < k₀ ∧ LocE.fPos k₀ c n p' = k₀ + rS) := by
  have a1 := Nat.zero_le ((p - (k₀ + j)) / t)
  have a2 := Nat.zero_le ((p' - (k₀ + j)) / t)
  rw [beta_framePos_formula hcj hp, beta_framePos_formula hcj hp', framePos_of_lt_dim hp, framePos_of_lt_dim hp']
  unfold ocbXAllow at h
  split_ifs at h ⊢ <;> omega

end Nat

section Ext

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem extendedMatrix_mulVec_single {n c : ℕ} (A : Matrix (Fin n) (Fin n) E) (y : Fin (n + c)) (l : Fin n) :
    (ciExtM c A).mulVec (Pi.single y 1) (Fin.castAdd c l) = if h : y.1 < n then A l ⟨y.1, h⟩ else 0 := by
  rw [ciExtM_castAdd]
  by_cases h : y.1 < n
  · rw [dite_eq_left h, Finset.sum_eq_single (⟨y.1, h⟩ : Fin n)]
    · rw [Pi.single_apply, if_pos (show Fin.castAdd c (⟨y.1, h⟩ : Fin n) = y from Fin.ext rfl), mul_one]
    · intro b _ hb
      rw [Pi.single_apply, if_neg (fun h' => hb (Fin.ext (by have := congrArg Fin.val h'; simpa using this))), mul_zero]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [dite_eq_right h]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Pi.single_apply, if_neg (fun h' => h (by rw [← h']; simp)), mul_zero]

theorem reducedMatrix_blockExtension {n c : ℕ} (G : Matrix (Fin n) (Fin n) E) (ρ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (hap : ∀ v, ρ v = (ciExtM c G).mulVec v)
    (y y' : Fin (n + c)) :
    ob2M P q ρ y y' = if h : y.1 < n ∧ y'.1 < n then redP P (G ⟨y.1, h.1⟩ ⟨y'.1, h.2⟩) else if y = y' then 1 else 0 := by
  unfold ob2M
  rw [hap]
  induction y using Fin.addCases with
  | left l =>
    rw [extendedMatrix_mulVec_single]
    simp only [Fin.val_castAdd]
    by_cases h' : y'.1 < n
    · rw [dite_eq_left h', dite_eq_left ⟨l.2, h'⟩, ciScE_lt _ h', ciScE_lt _ l.2, sub_self, zpow_zero, mul_one]
    · rw [dite_eq_right h', zero_mul, redP_zero, dite_eq_right (fun h => h' h.2), if_neg (fun h => h' (by rw [← h]; simp))]
  | right jj =>
    rw [ciExtM_natAdd, dite_eq_right (fun h => by simp at h), Pi.single_apply]
    by_cases he : Fin.natAdd n jj = y'
    · subst he
      rw [if_pos rfl, if_pos rfl, one_mul, sub_self, zpow_zero, redP_one]
    · rw [if_neg he, if_neg he, zero_mul, redP_zero]

theorem inclusion_single_eq_single {n c : ℕ} (l : Fin n) : Loc.inX E n c (Pi.single l 1) = Pi.single (Fin.castAdd c l) 1 := by
  rw [← ciEN l.2, basisVec_eq_single (show l.1 < n + c by omega)]
  rfl

theorem reducedMatrix_extension_entry {n c : ℕ} {r : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} {g : Sp E n ≃ₗ[E] Sp E n}
    (hrg : ∀ x, r (Loc.inX E n c x) = Loc.inX E n c (g x)) (l l' : Fin n) :
    ob2M P q r (Fin.castAdd c l) (Fin.castAdd c l') = redP P (g (Pi.single l' 1) l) := by
  unfold ob2M
  simp only [Fin.val_castAdd]
  rw [ciScE_lt _ l.2, ciScE_lt _ l'.2, sub_self, zpow_zero, mul_one, ← inclusion_single_eq_single, hrg, ciInX_castAdd]

end Ext

section GrpG

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem ocbGrpGLoc_holds (m2 : ℕ) : OcbGrpGLoc Ch sel mu cst m2 := by
  intro hB j hj w hbar
  obtain ⟨hk, hr, hrN, -⟩ := ranks_frame_inequalities R hB.hm hj
  have hq := ciQ_mem w.1
  have hu := ciQ_notMem_sq hB.hX hB.hPr w.2
  have hq0 := ciQ_ne_zero hu
  have hmS : R.m = 2 * R.rS + 2 := by
    unfold Ranks.rS
    obtain ⟨a, ha⟩ := R.m_even
    have := R.two_le_m
    omega
  have hrr : R.r = R.k + 2 * R.rS + 1 := by
    unfold Ranks.r
    omega
  have hcj : cOf R j + j = 2 * R.rS + 1 := by
    have := hB.hm
    unfold cOf
    omega
  have hnj : R.k + j ≤ R.N j := by
    unfold Ranks.N
    have e : j * (R.t + 1) = j * R.t + j := by ring
    rw [e]
    omega
  have hJat : Jat (Pr := Pr) cst.sharp j w.1 = LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) := by
    unfold Jat
    rw [if_pos w.2, hB.sharp, if_pos rfl]
  constructor
  · rintro ⟨g, ⟨r, hr', hrg⟩, hred⟩
    have hJ : r ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) := by
      rw [← hJat]
      have := hr'.2
      simpa [MulAut.conj_apply] using this
    have hent : ∀ l l' : Fin (R.N j), hbar.1 l l' = ob2M w.1 (qOf w.1) r (Fin.castAdd _ l) (Fin.castAdd _ l') :=
      fun l l' => by rw [ciEntry hred, reducedMatrix_extension_entry hrg]
    refine ⟨fun p hp => ?_, fun p p' hp hp' hne hnz => ?_⟩
    · unfold ocbM
      rw [dite_eq_left ⟨by omega, by omega⟩, hent]
      refine reducedMatrix_parahoric_diag_one hq hu hk hr hJ _ ?_
      show LocE.fPos R.k (cOf R j) (R.N j) p < R.r
      rw [framePos_of_lt_dim (by omega), hrr]
      split_ifs <;> omega
    · by_contra hna
      apply hnz
      unfold ocbM
      rw [dite_eq_left ⟨hp, hp'⟩, hent]
      rcases beta_lt_of_not_allowed (t := R.t) hcj hp hp' hne hna with h | ⟨h1, h2⟩
      · have h' : betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) (Fin.castAdd (cOf R j) (⟨p', hp'⟩ : Fin (R.N j))).1) <
            betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) (Fin.castAdd (cOf R j) (⟨p, hp⟩ : Fin (R.N j))).1) := by
          rw [hrr]
          exact h
        exact reducedMatrix_parahoric_blockTriangular hq hu hk hr hJ h'
      · exact reducedMatrix_parahoric_corner_zero hq hu hk hr hJ _ _ h1 h2
  · intro hpat
    obtain ⟨G, hG⟩ : ∃ G, G = ciLiftM w.1 hbar.1 := ⟨_, rfl⟩
    have hdet : IsUnit G.det := isUnit_iff_ne_zero.2 (by rw [hG]; exact ciLiftM_det_ne hbar)
    have hG1 : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hdet
    have hG2 : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hdet
    have hE1 : ciExtM (cOf R j) G * ciExtM (cOf R j) G⁻¹ = 1 := by rw [← ciExtM_mul, hG1, ciExtM_one]
    have hE2 : ciExtM (cOf R j) G⁻¹ * ciExtM (cOf R j) G = 1 := by rw [← ciExtM_mul, hG2, ciExtM_one]
    have hGi : ∀ i i', IntAt w.1 (G i i') := by rw [hG]; exact ciLiftM_int _
    have hGii : ∀ i i', IntAt w.1 (G⁻¹ i i') := by rw [hG]; exact ciLiftM_inv_int hbar
    have hGred : ∀ i i', redP w.1 (G i i') = hbar.1 i i' := by rw [hG]; exact ciLiftM_red _
    have hap : ∀ v, ciEquiv (ciExtM (cOf R j) G) (ciExtM (cOf R j) G⁻¹) hE1 hE2 v = (ciExtM (cOf R j) G).mulVec v :=
      fun v => ciEquiv_apply _ _ hE1 hE2 v
    have he : ∀ (A : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E), (∀ i i', IntAt w.1 (A i i')) → ∀ l l' : Fin (R.N j),
        IntAt w.1 (A l l' * ((qOf w.1 : ℕ) : X.E) ^ (LocE.scE (R.N j) (fun i => i + 1) l'.1 - LocE.scE (R.N j) (fun i => i + 1) l.1)) := by
      intro A hA l l'
      rw [ciScE_lt _ l.2, ciScE_lt _ l'.2, sub_self, zpow_zero, mul_one]
      exact hA _ _
    have hS : ciEquiv (ciExtM (cOf R j) G) (ciExtM (cOf R j) G⁻¹) hE1 hE2 ∈
        stabL X.E _ (LocE.lamY w.1 (qOf w.1) (R.N j) (cOf R j) fun i => i + 1) :=
      ciEquiv_stab (fun v hv => ciExtM_maps hq0 G _ (he G hGi) v hv) (fun v hv => ciExtM_maps hq0 G⁻¹ _ (he G⁻¹ hGii) v hv)
    have hM := reducedMatrix_blockExtension (P := w.1) (q := qOf w.1) G _ hap
    have hJ : ciEquiv (ciExtM (cOf R j) G) (ciExtM (cOf R j) G⁻¹) hE1 hE2 ∈
        LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) := by
      refine mem_parahoric_of_blockTriangular hq hu hk hr (by omega) hS ?_ ?_ ?_
      · intro y y' hlt
        rw [hM]
        split_ifs with h1 h2
        · rw [hGred]
          by_contra hnz
          have hne : y.1 ≠ y'.1 := fun he' => by
            have hlt' : betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) y'.1) <
                betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) y.1) := hlt
            rw [he'] at hlt'
            exact lt_irrefl _ hlt'
          have hall := hpat.2 y.1 y'.1 h1.1 h1.2 hne (by unfold ocbM; rw [dite_eq_left h1]; exact hnz)
          refine not_allowed_of_beta_lt (t := R.t) hcj h1.1 h1.2 (Or.inl ?_) hall
          rw [← hrr]
          exact hlt
        · subst h2
          exact absurd hlt (lt_irrefl _)
        · rfl
      · intro y hy
        rw [hM]
        split_ifs with h1 h2
        · rw [hGred]
          have hyk : y.1 < R.k + j := by
            rw [framePos_of_lt_dim h1.1, hrr] at hy
            split_ifs at hy <;> omega
          have h3 := hpat.1 y.1 hyk
          unfold ocbM at h3
          rw [dite_eq_left ⟨h1.1, h1.1⟩] at h3
          exact h3
        · rfl
        · exact absurd rfl h2
      · intro y y' hy hy'
        rw [hM]
        split_ifs with h1 h2
        · rw [hGred]
          by_contra hnz
          have hne : y.1 ≠ y'.1 := by
            intro he'
            rw [he'] at hy
            omega
          have hall := hpat.2 y.1 y'.1 h1.1 h1.2 hne (by unfold ocbM; rw [dite_eq_left h1]; exact hnz)
          exact not_allowed_of_beta_lt (t := R.t) hcj h1.1 h1.2 (Or.inr ⟨hy, hy'⟩) hall
        · subst h2
          omega
        · rfl
    refine ⟨ciEquiv G G⁻¹ hG1 hG2, ⟨ciEquiv (ciExtM (cOf R j) G) (ciExtM (cOf R j) G⁻¹) hE1 hE2,
      Subgroup.mem_inf.2 ⟨extended_matrix_in_reduction G G⁻¹ hE1 hE2, Subgroup.mem_comap.2 ?_⟩, fun x => ?_⟩, fun x hx => ?_⟩
    · simpa [MulAut.conj_apply, hJat] using hJ
    · rw [hap, ciEquiv_apply, ciExtM_inX]
    · funext l
      have hx' := (ciMem_stdAt w.1 x).1 hx
      simp only [redV, ciEquiv_apply, Matrix.mulVec, dotProduct]
      rw [redP_sum _ _ (fun l' _ => (hGi _ _).mul (hx' _))]
      refine Finset.sum_congr rfl fun l' _ => ?_
      rw [reduction_mul (hGi _ _) (hx' _), hGred]

end GrpG

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.OcbLevIsSym
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

def OcbLevIsSym : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (m2 : ℕ), R.m = m2 + 2 → OcbLevIs Ch (colLevSym Ch) m2

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.RecPerFF
section -- merged from Formalism.LocalToGlobal.Columns.FirstKernelEqLastComponentKernel
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Defs

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (m2 : ℕ) (al : ∀ j, j ≤ m2 + 1 → L.β j) (Am : Amb X) (u : Pr.Word)


include hQ in
theorem rcol_rowSG_eq : Pr.vGs = rowSG Pr sel mu := by
  classical
  unfold rowSG uSG
  rw [hQ, Finset.union_empty]

end Defs

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {hQ : QE sel (mu : Chr X.F X.E X.K) = ∅} {m2 : ℕ} {al : ∀ j, j ≤ m2 + 1 → L.β j} {Am : Amb X} {u : Pr.Word}
  (hX : X.Ok) {Gc : ChGlob X R.m} (hL : L.Ok Ch sel mu cst Gc m2) (h0 : Λ 0 = colLev Ch 0)
  (hΛ : ∀ j, j ≤ m2 + 1 → ∀ b : L.β j, L.levG j b = Λ j) (h1 : ∀ j, j ≤ m2 + 1 → ∀ b b' : L.β j, b = b')
  (hE : XiEquiv W Λ Ch sel mu cst Am u (refXi1 Ch sel mu cst L hQ m2 al u))
  {b₁ : L.β (m2 + 1)} {hY : YbHyp (R := R) sel mu cst L u m2 b₁} {P : LevFam X.E X.K R.r Pr.vGs}
  (hK : KerEquivC W Ch sel mu cst L Am u m2 b₁ hY P) (hF : ∀ j, (chF W sel mu L u j).Ok)
  (φ : MfV W Ch u)

end Main

end Formalism.L2.Col
end
end

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

def zOfRow0 (σ₀ : X.K →+* ℂ) (hM : (rowGSD W ΛM).Ok) (F : (rowGSD W ΛM).EqFun) : Fin ((rowGSD W ΛM).hDim hM) → ℂ :=
  fun a => σ₀ (((rowGSD W ΛM).hB hM).repr F a)

end Gen

section Cast

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

theorem levFam_eq_cast {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (e : SG = SG')
    (A : LevFam E K n SG) (B : LevFam E K n SG') (h : ∀ (w : SG') (hw : w.1 ∈ SG), B w = A ⟨w.1, hw⟩) : B = e ▸ A := by
  subst e
  funext w
  exact h w w.2

variable {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (e : Pr.vGs = SG') (A : LevFam X.E X.K (R.N R.m - 1) Pr.vGs)
  (Λ' : LevFam X.E X.K (R.N R.m - 1) SG')

def rowCast (hΛ : Λ' = e ▸ A) (F : (formGSD (rowVal W SG') Λ').EqFun) : (rowGSD W A).EqFun := by
  subst hΛ
  subst e
  exact F

end Cast

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (P : LevFam X.E X.K R.r Pr.vGs)

theorem rowTy_inv_cast : (rowTy Ch sel mu P).inv = rcol_rowSG_eq sel mu hQ ▸ (rowTyG Ch P).inv := by
  refine levFam_eq_cast (rcol_rowSG_eq sel mu hQ) _ _ fun w hw => ?_
  first
  | (simp only [LevFam.inv, rowTy, LevFam.glue, dif_pos hw]; done)
  | (unfold LevFam.inv rowTy LevFam.glue; rw [dif_pos hw])
  | (simp [LevFam.inv, rowTy, LevFam.glue, hw])

def zOfRow (σ₀ : X.K →+* ℂ) (hM : (rowGSD W (rowTyG Ch P).inv).Ok) (F : MtildeV W Ch sel mu P) : Fin ((rowGSD W (rowTyG Ch P).inv).hDim hM) → ℂ :=
  zOfRow0 W (rowTyG Ch P).inv σ₀ hM (rowCast W (rcol_rowSG_eq sel mu hQ) (rowTyG Ch P).inv _ (rowTy_inv_cast Ch sel mu hQ P) F)

end Main

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.FrameEntryAuxiliarySuperdiagonal
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

theorem finset_range_sum_split {A : Type} [AddCommMonoid A] (f : ℕ → A) (c j : ℕ) :
    ∑ i ∈ Finset.range (c + j - 1), f i =
      ∑ i ∈ Finset.range (c - 1), f i + (if 1 ≤ c ∧ 1 ≤ j then f (c - 1) else 0) + ∑ i ∈ Finset.range (j - 1), f (c + i) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  rw [if_pos ⟨hc, hj⟩, show c + j - 1 = (c - 1 + 1) + (j - 1) by omega, Finset.sum_range_add, Finset.sum_range_succ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  omega

section ChrLoc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem frameIndex_of_lt {k₀ c n s : ℕ} (hs : s < k₀) : LocE.fIdx k₀ c n s = s := by
  unfold LocE.fIdx
  rw [if_pos hs]

theorem frameIndex_of_ge {k₀ c n s : ℕ} (h : k₀ + c ≤ s) : LocE.fIdx k₀ c n s = s - c := by
  unfold LocE.fIdx
  rw [if_neg (show ¬ s < k₀ by omega), if_neg (show ¬ s < k₀ + c by omega)]

theorem frameEntry_eq_coord_of_extension {k₀ n c : ℕ} {rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} {g : Sp E n ≃ₗ[E] Sp E n}
    (hg : ∀ x, rr (Loc.inX E n c x) = Loc.inX E n c (g x)) {a b : ℕ} (ha : a < n) (hb : b < n) {p p' : ℕ}
    (hpa : LocE.fIdx k₀ c n p = a) (hpb : LocE.fIdx k₀ c n p' = b) :
    LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap p p' = g (Pi.single ⟨b, hb⟩ 1) ⟨a, ha⟩ := by
  unfold LocE.entB
  rw [hpa, hpb, ciScE_lt _ ha, ciScE_lt _ hb, sub_self, zpow_zero, mul_one, ciEN hb]
  show Loc.atN (rr (Loc.inX E n c (Pi.single ⟨b, hb⟩ 1))) a = _
  rw [hg, ciAtN_inX ha]

theorem reduction_frameEntry_of_extension {k₀ n c : ℕ} {rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} {g : Sp E n ≃ₗ[E] Sp E n}
    (hg : ∀ x, rr (Loc.inX E n c x) = Loc.inX E n c (g x)) {hbar : GL (Fin n) (𝓞 E ⧸ P.asIdeal)}
    (hred : ∀ x ∈ stdAt E n P, redV P (g x) = hbar.1.mulVec (redV P x)) {a b : ℕ} (ha : a < n) (hb : b < n) {p p' : ℕ}
    (hpa : LocE.fIdx k₀ c n p = a) (hpb : LocE.fIdx k₀ c n p' = b) :
    redP P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap p p') = ocbM hbar a b := by
  rw [frameEntry_eq_coord_of_extension hg ha hb hpa hpb, ← ciEntry hred]
  unfold ocbM
  rw [dite_eq_left ⟨ha, hb⟩]

theorem frameEntry_auxiliary_superdiagonal {k₀ n c i : ℕ} (hi : i + 1 < c) (rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + i) (k₀ + i + 1) =
      (q : E) * Loc.atN (rr (Loc.eN E (n + c) (n + i + 1))) (n + i) := by
  have h1 : LocE.fIdx k₀ c n (k₀ + i) = n + i := by
    unfold LocE.fIdx
    rw [if_neg (show ¬ k₀ + i < k₀ by omega), if_pos (show k₀ + i < k₀ + c by omega)]
    omega
  have h2 : LocE.fIdx k₀ c n (k₀ + i + 1) = n + i + 1 := by
    unfold LocE.fIdx
    rw [if_neg (show ¬ k₀ + i + 1 < k₀ by omega), if_pos (show k₀ + i + 1 < k₀ + c by omega)]
    omega
  have h3 : LocE.scE n (fun i => i + 1) (n + i + 1) = (i : ℤ) + 2 := by
    simp only [LocE.scE, if_neg (show ¬ n + i + 1 < n by omega), show n + i + 1 - n = i + 1 by omega]
    push_cast
    ring
  have h4 : LocE.scE n (fun i => i + 1) (n + i) = (i : ℤ) + 1 := by
    simp only [LocE.scE, if_neg (show ¬ n + i < n by omega), show n + i - n = i by omega]
    push_cast
    ring
  unfold LocE.entB
  rw [h1, h2, h3, h4, show (i : ℤ) + 2 - (i + 1) = 1 by ring, zpow_one, mul_comm]
  rfl

theorem frameEntry_last_auxiliary_zero {k₀ n c : ℕ} (hc : 1 ≤ c) (hkn : k₀ < n) {rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} {g : Sp E n ≃ₗ[E] Sp E n}
    (hg : ∀ x, rr (Loc.inX E n c x) = Loc.inX E n c (g x)) :
    LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + (c - 1)) (k₀ + (c - 1) + 1) = 0 := by
  have h1 : LocE.fIdx k₀ c n (k₀ + (c - 1)) = n + (c - 1) := by
    unfold LocE.fIdx
    rw [if_neg (show ¬ k₀ + (c - 1) < k₀ by omega), if_pos (show k₀ + (c - 1) < k₀ + c by omega)]
    omega
  have h2 : LocE.fIdx k₀ c n (k₀ + (c - 1) + 1) = k₀ := by
    rw [frameIndex_of_ge (by omega)]
    omega
  unfold LocE.entB
  rw [h1, h2, ciEN hkn]
  show Loc.atN (rr (Loc.inX E n c (Pi.single ⟨k₀, hkn⟩ 1))) (n + (c - 1)) * _ = 0
  rw [hg]
  unfold Loc.atN
  rw [dite_eq_left (show n + (c - 1) < n + c by omega), ciInX_apply]
  split_ifs with h
  · simp only at h
    omega
  · rw [zero_mul]

theorem columns_fact {k₀ n c : ℕ} (rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    (q : E) * Loc.n1Arg rr = ∑ i ∈ Finset.range (c - 1), LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + i) (k₀ + i + 1) := by
  unfold Loc.n1Arg
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [frameEntry_auxiliary_superdiagonal (by have := Finset.mem_range.1 hi; omega)]

theorem addChar_apply_ne_zero' {A : Type} [AddGroup A] (ψ : AddChar A K) (a : A) : ψ a ≠ 0 := fun h => by
  have h1 := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at h1
  exact one_ne_zero h1

theorem lamGBS_eq_addChar_mul_ocbXLam_of_mem_stabL (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ t j n c : ℕ}
    (hk1 : 1 ≤ k₀) (hcj : 1 ≤ c + j) (hn : k₀ + j + j * t ≤ n)
    {rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hrr : rr ∈ stabL E (n + c) (LocE.lamY P q n c fun i => i + 1))
    {g : Sp E n ≃ₗ[E] Sp E n} (hg : ∀ x, rr (Loc.inX E n c x) = Loc.inX E n c (g x))
    {hbar : GL (Fin n) (𝓞 E ⧸ P.asIdeal)} (hred : ∀ x ∈ stdAt E n P, redV P (g x) = hbar.1.mulVec (redV P x)) :
    LocE.lamGBS q ψ₀ χ k₀ (k₀ + c + j) t j n c rr.toLinearMap = ψ₀ (redP P ((q : E) * Loc.n1Arg rr)) * ocbXLam ψ₀ χ k₀ j t hbar := by
  have hq0 := ciQ_ne_zero hu
  have hk : k₀ ≤ n := by omega
  have hint : ∀ p p', p < n + c → p' < n + c →
      IntAt P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap p p') :=
    fun p p' hp hp' => frameEntry_integral_of_stabilizer hq0 hk hp hp' hrr
  have hS : redP P (∑ i ∈ Finset.range (k₀ - 1), LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap i (i + 1) +
      ∑ i ∈ Finset.range (k₀ + c + j - k₀ - 1),
        LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + i) (k₀ + i + 1)) =
      (∑ i ∈ Finset.range (k₀ - 1), ocbM hbar i (i + 1) + ∑ i ∈ Finset.range (j - 1), ocbM hbar (k₀ + i) (k₀ + i + 1)) +
        redP P ((q : E) * Loc.n1Arg rr) := by
    rw [reduction_sum_superdiagonal (show k₀ < k₀ + c + j by omega) _ (fun p hp => hint p (p + 1) (by omega) (by omega)),
      show k₀ + c + j - k₀ - 1 = c + j - 1 by omega, finset_range_sum_split _ c j, columns_fact (k₀ := k₀) rr,
      redP_sum _ _ (fun i hi => hint _ _ (by have := Finset.mem_range.1 hi; omega) (by have := Finset.mem_range.1 hi; omega))]
    have hE : ∀ i ∈ Finset.range (k₀ - 1),
        redP P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap i (i + 1)) = ocbM hbar i (i + 1) := by
      intro i hi
      have := Finset.mem_range.1 hi
      exact reduction_frameEntry_of_extension hg hred (by omega) (by omega) (frameIndex_of_lt (by omega)) (frameIndex_of_lt (by omega))
    have hF : ∀ i ∈ Finset.range (j - 1),
        redP P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + (c + i)) (k₀ + (c + i) + 1)) =
          ocbM hbar (k₀ + i) (k₀ + i + 1) := by
      intro i hi
      have := Finset.mem_range.1 hi
      exact reduction_frameEntry_of_extension hg hred (by omega) (by omega)
        (by rw [frameIndex_of_ge (s := k₀ + (c + i)) (by omega)]; omega)
        (by rw [frameIndex_of_ge (s := k₀ + (c + i) + 1) (by omega)]; omega)
    have hM : (if 1 ≤ c ∧ 1 ≤ j then
        redP P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + (c - 1)) (k₀ + (c - 1) + 1)) else 0) = 0 := by
      split_ifs with h
      · rw [frameEntry_last_auxiliary_zero h.1 (by omega) hg, redP_zero]
      · rfl
    rw [Finset.sum_congr rfl hE, Finset.sum_congr rfl hF, hM]
    abel
  have hBl : ∀ i ∈ Finset.range j, LocE.unitV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t =>
        LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + c + j + i * t + s.1) (k₀ + c + j + i * t + s'.1))) =
      ocbChiK (χ i) (Matrix.det (Matrix.of fun s s' : Fin t => ocbM hbar (k₀ + j + i * t + s.1) (k₀ + j + i * t + s'.1))) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hjt : (i + 1) * t ≤ j * t := Nat.mul_le_mul_right t hi'
    rw [Nat.succ_mul] at hjt
    have hbd : ∀ u : Fin t, k₀ + j + i * t + u.1 < n := fun u => by have := u.2; omega
    show ocbChiK (χ i) (redP P _) = _
    rw [reduction_det_eq_det_reduction _ fun s s' => hint _ _ (by have := hbd s; omega) (by have := hbd s'; omega)]
    congr 1
    congr 1
    ext s s'
    simp only [Matrix.of_apply]
    exact reduction_frameEntry_of_extension hg hred (hbd s) (hbd s')
      (by rw [frameIndex_of_ge (s := k₀ + c + j + i * t + s.1) (by omega)]; omega)
      (by rw [frameIndex_of_ge (s := k₀ + c + j + i * t + s'.1) (by omega)]; omega)
  unfold LocE.lamGBS LocE.lamGvS ocbXLam
  rw [hS, AddChar.map_add_eq_mul, Finset.prod_congr rfl hBl]
  ring

end ChrLoc

section ChrGlob

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem ocbChrGLoc_holds (m2 : ℕ) : OcbChrGLoc Ch sel mu cst m2 := by
  intro hB j hj w hbar g r hr hg hred
  have hw := w.2
  have h2 := R.two_le_m
  have hm := hB.hm
  have hk5 := R.m_add_three_le_k
  have e : j * (R.t + 1) = j * R.t + j := by ring
  have hJ : r ∈ Jat (Pr := Pr) cst.sharp j w.1 := by
    have h := hr.2
    simpa [MulAut.conj_apply] using h
  rw [hB.sharp] at hJ
  have hJ' : r ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) := by
    unfold Jat at hJ
    rwa [if_pos hw, if_pos rfl] at hJ
  have hu := ciQ_notMem_sq hB.hX hB.hPr hw
  have hq0 := ciQ_ne_zero hu
  have hrE : R.r = R.k + cOf R j + j := by
    unfold Ranks.r cOf
    omega
  have hn : R.k + j + j * R.t ≤ R.N j := by
    unfold Ranks.N
    rw [e]
    omega
  have hint : IntAt w.1 ((qOf w.1 : X.E) * Loc.n1Arg r) := by
    rw [columns_fact (k₀ := R.k) r]
    refine ciIntAt_sum _ _ fun i hi => frameEntry_integral_of_stabilizer hq0 (by unfold Ranks.N; omega) ?_ ?_ hJ'.1
    · have := Finset.mem_range.1 hi
      unfold Ranks.N
      omega
    · have := Finset.mem_range.1 hi
      unfold Ranks.N
      omega
  have hpsi := hB.psi0 ⟨w.1, by classical exact Finset.mem_union_left _ w.2⟩ ((qOf w.1 : X.E) * Loc.n1Arg r) hw hint
  rw [mul_div_cancel_left₀ _ hq0] at hpsi
  dsimp only at hpsi
  unfold chiInv lamRow
  dsimp only
  rw [hB.sharp, if_pos hw, if_pos rfl, inv_one, one_mul, mul_one, hpsi, hrE,
    lamGBS_eq_addChar_mul_ocbXLam_of_mem_stabL hu _ _ (by omega) (by unfold cOf; omega) hn hJ'.1 hg hred, ← mul_assoc,
    inv_mul_cancel₀ (addChar_apply_ne_zero' _ _), one_mul]

end ChrGlob

end Formalism.L2.Col
end
end
