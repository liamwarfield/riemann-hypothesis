module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.SemisimpleOfTraceFormNondegenerate
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.TraceNilpotentAscent
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Poisson
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldUnfold
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.TranslationIndependent
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MultiplicityMeasurability.MeasurableMult

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.KeySmall
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.KeySmall
open Module

namespace PI.Tr

private theorem exists_generator_of_finrank_eq_one_zLattice {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (h1 : finrank ℝ E = 1) :
    ∃ a ∈ Λ, a ≠ 0 ∧ ∀ x ∈ Λ, ∃ k : ℤ, x = (k : ℝ) • a := by
  have hrk : finrank ℤ Λ = 1 := (ZLattice.rank ℝ Λ).trans h1
  let b := Module.finBasisOfFinrankEq ℤ Λ hrk
  refine ⟨(b 0 : E), (b 0).2, fun h => b.ne_zero 0 (Subtype.ext h), ?_⟩
  intro x hx
  refine ⟨b.repr ⟨x, hx⟩ 0, ?_⟩
  have h2 : ((b.repr ⟨x, hx⟩ 0 • b 0 : Λ) : E) = x := by
    have hs := b.sum_repr ⟨x, hx⟩
    rw [Fin.sum_univ_one] at hs
    rw [hs]
  rw [Int.cast_smul_eq_zsmul]
  exact h2.symm.trans (Submodule.coe_smul _ _)

theorem keySmall : KeySmall := by
  intro E _ _ _ Λ _ _ lam u hdim hlam hdual
  have hdim' : finrank ℝ E ≤ 1 := hdim
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdim' with h0 | h1
  · have : Subsingleton E := Module.finrank_zero_iff.mp h0
    refine ⟨0, Λ.zero_mem, ?_⟩
    rw [Subsingleton.elim u 0, h0]
    simp
  · obtain ⟨a, haΛ, ha0, hmul⟩ := exists_generator_of_finrank_eq_one_zLattice Λ h1
    obtain ⟨t, rfl⟩ : ∃ t : ℝ, u = t • a := by
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' a ha0).mp h1 u
      exact ⟨c, hc.symm⟩
    have hα : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    rw [h1, Nat.cast_one]
    by_cases hc : lam * ‖a‖ ≤ 1
    · refine ⟨((round t : ℤ) : ℝ) • a, ?_, ?_⟩
      · rw [Int.cast_smul_eq_zsmul]
        exact Λ.smul_mem _ haΛ
      · rw [← sub_smul, norm_smul, Real.norm_eq_abs]
        calc |t - ((round t : ℤ) : ℝ)| * ‖a‖ * lam ≤ (1 / 2) * ‖a‖ * lam :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (abs_sub_round t) (norm_nonneg a)) hlam.le
          _ = (1 / 2) * (lam * ‖a‖) := by ring
          _ ≤ (1 / 2) * 1 := mul_le_mul_of_nonneg_left hc (by norm_num)
          _ = 1 / 2 := by ring
    · push Not at hc
      have hα2 : ‖a‖ ^ 2 ≠ 0 := by positivity
      have key : ∀ s : ℝ, inner ℝ (s • a) ((‖a‖ ^ 2)⁻¹ • a) = s := by
        intro s
        rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
          inv_mul_cancel₀ hα2, mul_one]
      have hnorm : ‖(‖a‖ ^ 2)⁻¹ • a‖ < lam := by
        rw [norm_smul, norm_inv, norm_pow, norm_norm]
        have e : (‖a‖ ^ 2)⁻¹ * ‖a‖ * ‖a‖ = 1 := by
          rw [mul_assoc, ← sq, inv_mul_cancel₀ hα2]
        have hlt : (‖a‖ ^ 2)⁻¹ * ‖a‖ * ‖a‖ < lam * ‖a‖ := by
          rw [e]
          exact hc
        exact lt_of_mul_lt_mul_right hlt hα.le
      obtain ⟨m, hm⟩ := hdual ((‖a‖ ^ 2)⁻¹ • a)
        (by
          intro x hx
          obtain ⟨k, rfl⟩ := hmul x hx
          exact ⟨k, key _⟩) hnorm
      rw [key] at hm
      refine ⟨(m : ℝ) • a, ?_, ?_⟩
      · rw [Int.cast_smul_eq_zsmul]
        exact Λ.smul_mem _ haΛ
      · rw [hm, sub_self, norm_zero, zero_mul]
        norm_num

end PI.Tr
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Skeleton
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Minima
open Module
open scoped InnerProductSpace

namespace PI

variable {N : ℕ}

lemma succMin_nonneg (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) (i : ℕ) : 0 ≤ succMin M i := Real.sInf_nonneg fun _ ht => ht.1

lemma finrank_span_lt_succMin (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) (i : ℕ) (hi : 1 ≤ i) :
    finrank ℝ (Submodule.span ℝ {x : EuclideanSpace ℝ (Fin N) | x ∈ M ∧ ‖x‖ < succMin M i}) < i := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℝ
    {x : EuclideanSpace ℝ (Fin N) | x ∈ M ∧ ‖x‖ < succMin M i}
  have hbfin : b.Finite := hbli.setFinite
  letI := hbfin.fintype
  have hcard := finrank_span_set_eq_card hbli
  rw [hbspan] at hcard
  have hle : i ≤ Fintype.card b := by rw [← Set.toFinset_card]; omega
  let e : Fin i ↪ b := (Fin.castLEEmb hle).trans (Fintype.equivFin b).symm.toEmbedding
  let v : Fin i → EuclideanSpace ℝ (Fin N) := fun j => (e j : EuclideanSpace ℝ (Fin N))
  have hvli : LinearIndependent ℝ v := hbli.comp e e.injective
  have hvS : ∀ j, v j ∈ M ∧ ‖v j‖ < succMin M i := fun j => hbS (e j).2
  have hne : (Finset.univ : Finset (Fin i)).Nonempty := ⟨⟨0, hi⟩, Finset.mem_univ _⟩
  have ht_lt : Finset.univ.sup' hne (fun j => ‖v j‖) < succMin M i :=
    (Finset.sup'_lt_iff hne).2 fun j _ => (hvS j).2
  have ht_mem : Finset.univ.sup' hne (fun j => ‖v j‖) ∈ {t : ℝ | 0 ≤ t ∧
      ∃ v : Fin i → EuclideanSpace ℝ (Fin N), (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t} :=
    ⟨(norm_nonneg _).trans (Finset.le_sup' (fun j => ‖v j‖) (Finset.mem_univ ⟨0, hi⟩)),
      v, fun j => (hvS j).1, hvli, fun j => Finset.le_sup' (fun j => ‖v j‖) (Finset.mem_univ j)⟩
  have hinf : succMin M i ≤ Finset.univ.sup' hne (fun j => ‖v j‖) :=
    csInf_le ⟨0, fun t ht => ht.1⟩ ht_mem
  exact lt_irrefl (succMin M i) (lt_of_le_of_lt hinf ht_lt)

theorem minima_of_key (h : TransferenceKey) : TransferenceMinima := by
  intro N M hdisc hspan i hi hiN
  have hA0 : 0 ≤ succMin M i := succMin_nonneg M i
  have hB0 : 0 ≤ succMin (dualZ M) (N + 1 - i) := succMin_nonneg _ _
  rcases hB0.eq_or_lt with hB | hB
  · rw [← hB, mul_zero]; positivity
  haveI : DiscreteTopology M := hdisc
  haveI : IsZLattice ℝ M := ⟨hspan⟩
  set A := succMin M i with hAdef
  set B := succMin (dualZ M) (N + 1 - i) with hBdef
  set Sd : Submodule ℝ (EuclideanSpace ℝ (Fin N)) :=
    Submodule.span ℝ {y : EuclideanSpace ℝ (Fin N) | y ∈ dualZ M ∧ ‖y‖ < B} with hSddef
  set V' : Submodule ℝ (EuclideanSpace ℝ (Fin N)) :=
    Submodule.span ℝ {x : EuclideanSpace ℝ (Fin N) | x ∈ M ∧ ‖x‖ < A} with hV'def
  have hSd : finrank ℝ Sd < N + 1 - i := finrank_span_lt_succMin (dualZ M) (N + 1 - i) (by omega)
  have hV' : finrank ℝ V' < i := finrank_span_lt_succMin M i hi
  have hE : finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := finrank_euclideanSpace_fin
  have h1 : finrank ℝ Sd + finrank ℝ Sdᗮ = N := (Submodule.finrank_add_finrank_orthogonal Sd).trans hE
  have h2 : finrank ℝ V' + finrank ℝ V'ᗮ = N := (Submodule.finrank_add_finrank_orthogonal V').trans hE
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq Sdᗮ V'ᗮ
  have h4 : finrank ℝ (Sdᗮ ⊔ V'ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin N))) ≤ N := (Submodule.finrank_le _).trans hE.le
  have hne : (Sdᗮ ⊓ V'ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin N))) ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at h3
    omega
  obtain ⟨u0, hu0W, hu0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hu0pos : 0 < ‖u0‖ := norm_pos_iff.2 hu0ne
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  suffices hAB : A ≤ N / B by rwa [le_div_iff₀ hB] at hAB
  apply le_of_forall_pos_le_add
  intro ε hε
  set c : ℝ := N / (2 * B) + ε / 2 with hcdef
  have hc : 0 < c := by positivity
  set u : EuclideanSpace ℝ (Fin N) := (c / ‖u0‖) • u0 with hudef
  have hun : ‖u‖ = c := by
    rw [hudef, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hc hu0pos), div_mul_cancel₀ _ hu0pos.ne']
  have huW : u ∈ (Sdᗮ ⊓ V'ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin N))) :=
    Submodule.smul_mem _ _ hu0W
  have huSd : u ∈ Sdᗮ := (Submodule.mem_inf.1 huW).1
  have huV : u ∈ V'ᗮ := (Submodule.mem_inf.1 huW).2
  obtain ⟨l, hlM, hl⟩ := h (EuclideanSpace ℝ (Fin N)) M B u hB (fun y hy hyB => by
    have hyd : y ∈ dualZ M := fun x hx => by
      obtain ⟨n, hn⟩ := hy x hx
      exact ⟨n, by rw [real_inner_comm]; exact hn⟩
    have hySd : y ∈ Sd := Submodule.subset_span ⟨hyd, hyB⟩
    exact ⟨0, by rw [Submodule.inner_left_of_mem_orthogonal hySd huSd]; simp⟩)
  rw [hE] at hl
  have hul : ‖u - l‖ ≤ N / (2 * B) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hlV : l ∉ V' := by
    intro hlV
    have hin : inner ℝ u l = 0 := Submodule.inner_left_of_mem_orthogonal hlV huV
    have hsq : ‖u - l‖ ^ 2 = ‖u‖ ^ 2 + ‖l‖ ^ 2 := by
      rw [@norm_sub_sq_real, hin]; ring
    have hsq2 : ‖u‖ ^ 2 ≤ ‖u - l‖ ^ 2 := by rw [hsq]; nlinarith [sq_nonneg ‖l‖]
    have hge : ‖u‖ ≤ ‖u - l‖ := by nlinarith [norm_nonneg (u - l), norm_nonneg u]
    linarith
  have hlA : A ≤ ‖l‖ := by
    by_contra hlt
    push_neg at hlt
    exact hlV (Submodule.subset_span ⟨hlM, hlt⟩)
  have htri : ‖l‖ ≤ ‖u‖ + ‖u - l‖ := by
    calc ‖l‖ = ‖u - (u - l)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖u‖ + ‖u - l‖ := norm_sub_le _ _
  have hhalf : (N : ℝ) / (2 * B) + N / (2 * B) = N / B := by field_simp; ring
  linarith

end PI
end

open Module

namespace PI.Tr

theorem key_of (hL : KeyLarge) (hS : KeySmall) : PI.TransferenceKey := by
  intro E _ _ _ Λ _ _ lam u hlam hu
  rcases Nat.lt_or_ge (finrank ℝ E) 2 with h | h
  · exact hS E Λ lam u (by omega) hlam hu
  · exact hL E Λ lam u h hlam hu

theorem transferenceCover_of' (hP : PoissonGauss) (hG : GaussStep) (hS : KeySmall) :
    PI.TransferenceCover := PI.cover_of_key (key_of (hG hP) hS)

theorem transferenceMinima_of' (hP : PoissonGauss) (hG : GaussStep) (hS : KeySmall) :
    PI.TransferenceMinima := PI.minima_of_key (key_of (hG hP) hS)

end PI.Tr
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.NumericMain
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.GaussAbs
open scoped Real

namespace PI.Tr

private theorem summable_mul_of_nonneg_of_abs_le_one {ι : Type} {e θ : ι → ℝ} (he : Summable e)
    (he0 : ∀ i, 0 ≤ e i) (hθ : ∀ i, |θ i| ≤ 1) : Summable fun i => e i * θ i := by
  have h1 : Summable fun i => e i * θ i + e i := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (he.mul_left 2)
    · have := (abs_le.mp (hθ i)).1
      nlinarith [mul_nonneg (he0 i) (by linarith : 0 ≤ θ i + 1)]
    · have := (abs_le.mp (hθ i)).2
      nlinarith [mul_nonneg (he0 i) (by linarith : 0 ≤ 1 - θ i)]
  exact (h1.sub he).congr (fun i => by ring)

private theorem one_le_inv_of_pos_of_le_one {τ : ℝ} (h : 0 < τ) (h' : τ ≤ 1) : 1 ≤ τ⁻¹ := by
  have h1 := mul_inv_cancel₀ h.ne'
  nlinarith [mul_nonneg (inv_pos.mpr h).le (sub_nonneg.mpr h')]

theorem gauss_abstract {X Y : Type} (a a0 : X → ℝ) (q θ : Y → ℝ) (n c : ℝ)
    (hq : ∀ y, 0 ≤ q y) (ha0 : ∀ x, 0 ≤ a0 x) (hθ : ∀ y, |θ y| ≤ 1) (hc : 0 < c) (y0 : Y)
    (sA : ∀ t : ℝ, 0 < t → Summable fun x => Real.exp (-π * t * a x))
    (compactWordAction : ∀ t : ℝ, 0 < t → Summable fun x => Real.exp (-π * t * a0 x))
    (sQ : ∀ t : ℝ, 0 < t → Summable fun y => Real.exp (-π * q y / t))
    (Pu : ∀ t : ℝ, 0 < t → ∑' x, Real.exp (-π * t * a x) =
      c * t ^ (-n / 2) * ∑' y, Real.exp (-π * q y / t) * θ y)
    (P0 : ∀ t : ℝ, 0 < t → ∑' x, Real.exp (-π * t * a0 x) =
      c * t ^ (-n / 2) * ∑' y, Real.exp (-π * q y / t))
    (R2 l2 : ℝ) (hR : ∀ x, R2 ≤ a x) (hl : ∀ y, q y < l2 → θ y = 1)
    (s τ₁ τ₂ : ℝ) (hs : 0 < s) (h1 : 0 < τ₁) (h1' : τ₁ ≤ 1) (h2 : 0 < τ₂) (h2' : τ₂ ≤ 1) :
    1 ≤ Real.exp (-π * s * (1 - τ₁) * R2) * τ₁ ^ (-n / 2) +
      2 * (Real.exp (-π * (1 - τ₂) * l2 / s) * τ₂ ^ (-n / 2)) := by
  have hπ : 0 < π := Real.pi_pos
  have hst1 : 0 < s * τ₁ := mul_pos hs h1
  have hst2 : 0 < s / τ₂ := div_pos hs h2
  have hQs := sQ s hs
  have hQ1 := sQ _ hst1
  have hQ2 := sQ _ hst2
  have hK : 0 < c * s ^ (-n / 2) := mul_pos hc (Real.rpow_pos_of_pos hs _)
  have hA : 0 < τ₁ ^ (-n / 2) := Real.rpow_pos_of_pos h1 _
  have hT : 0 < τ₂ ^ (-n / 2) := Real.rpow_pos_of_pos h2 _
  have hE1 : 0 < Real.exp (-π * s * (1 - τ₁) * R2) := Real.exp_pos _
  have hE2 : 0 < Real.exp (-π * (1 - τ₂) * l2 / s) := Real.exp_pos _
  have hS0pos : 0 < ∑' y, Real.exp (-π * q y / s) :=
    lt_of_lt_of_le (Real.exp_pos _)
      (le_hasSum hQs.hasSum y0 (fun j _ => (Real.exp_pos _).le))
  have up1 : ∑' x, Real.exp (-π * s * a x) ≤
      Real.exp (-π * s * (1 - τ₁) * R2) * ∑' x, Real.exp (-π * (s * τ₁) * a x) := by
    refine hasSum_le (fun x => ?_) (sA s hs).hasSum ((sA _ hst1).hasSum.mul_left _)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h0 : 0 ≤ π * s * (1 - τ₁) := mul_nonneg (mul_nonneg hπ.le hs.le) (sub_nonneg.mpr h1')
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr (hR x))]
  have hle1 : ∑' y, Real.exp (-π * q y / (s * τ₁)) * θ y ≤ ∑' y, Real.exp (-π * q y / s) := by
    refine hasSum_le (fun y => ?_)
      (summable_mul_of_nonneg_of_abs_le_one hQ1 (fun _ => (Real.exp_pos _).le) hθ).hasSum hQs.hasSum
    have hθ1 := (abs_le.mp (hθ y)).2
    have he := Real.exp_pos (-π * q y / (s * τ₁))
    have hmono : Real.exp (-π * q y / (s * τ₁)) ≤ Real.exp (-π * q y / s) := by
      apply Real.exp_le_exp.mpr
      have hw : 0 ≤ π * q y / s := div_nonneg (mul_nonneg hπ.le (hq y)) hs.le
      have e1 : -π * q y / (s * τ₁) = -(π * q y / s) * τ₁⁻¹ := by ring
      have e2 : -π * q y / s = -(π * q y / s) := by ring
      have hinv := one_le_inv_of_pos_of_le_one h1 h1'
      rw [e1, e2]
      nlinarith [mul_nonneg hw (sub_nonneg.mpr hinv)]
    nlinarith [mul_nonneg he.le (sub_nonneg.mpr hθ1)]
  have up2 : ∑' x, Real.exp (-π * (s * τ₁) * a x) ≤
      c * s ^ (-n / 2) * (τ₁ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s)) := by
    rw [Pu _ hst1, Real.mul_rpow hs.le h1.le]
    calc c * (s ^ (-n / 2) * τ₁ ^ (-n / 2)) * ∑' y, Real.exp (-π * q y / (s * τ₁)) * θ y
        ≤ c * (s ^ (-n / 2) * τ₁ ^ (-n / 2)) * ∑' y, Real.exp (-π * q y / s) :=
          mul_le_mul_of_nonneg_left hle1
            (mul_pos hc (mul_pos (Real.rpow_pos_of_pos hs _) hA)).le
      _ = c * s ^ (-n / 2) * (τ₁ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s)) := by ring
  have hup : ∑' y, Real.exp (-π * q y / s) * θ y ≤
      Real.exp (-π * s * (1 - τ₁) * R2) * (τ₁ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s)) := by
    have h := (Pu s hs).symm.le.trans (up1.trans (mul_le_mul_of_nonneg_left up2 hE1.le))
    have h' : c * s ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s) * θ y ≤
        c * s ^ (-n / 2) * (Real.exp (-π * s * (1 - τ₁) * R2) *
          (τ₁ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s))) := by
      calc _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_left h' hK
  have hlow : ∑' y, Real.exp (-π * q y / s) -
      2 * Real.exp (-π * (1 - τ₂) * l2 / s) * ∑' y, Real.exp (-π * q y / (s / τ₂)) ≤
      ∑' y, Real.exp (-π * q y / s) * θ y := by
    refine hasSum_le (fun y => ?_) (hQs.hasSum.sub (hQ2.hasSum.mul_left _))
      (summable_mul_of_nonneg_of_abs_le_one hQs (fun _ => (Real.exp_pos _).le) hθ).hasSum
    have he := Real.exp_pos (-π * q y / s)
    have hf := Real.exp_pos (-π * q y / (s / τ₂))
    have hprod : 0 < 2 * Real.exp (-π * (1 - τ₂) * l2 / s) * Real.exp (-π * q y / (s / τ₂)) :=
      mul_pos (mul_pos two_pos hE2) hf
    by_cases hql : q y < l2
    · rw [hl y hql, mul_one]
      linarith
    · have hql : l2 ≤ q y := not_lt.mp hql
      have hef : Real.exp (-π * q y / s) ≤
          Real.exp (-π * (1 - τ₂) * l2 / s) * Real.exp (-π * q y / (s / τ₂)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have e1 : -π * q y / (s / τ₂) = -π * q y * τ₂ / s := div_div_eq_mul_div _ _ _
        rw [e1]
        have key : -π * q y / s - (-π * (1 - τ₂) * l2 / s + -π * q y * τ₂ / s) =
            -(π * (1 - τ₂) * (q y - l2) / s) := by ring
        have hnn : 0 ≤ π * (1 - τ₂) * (q y - l2) / s :=
          div_nonneg (mul_nonneg (mul_nonneg hπ.le (sub_nonneg.mpr h2')) (sub_nonneg.mpr hql)) hs.le
        linarith
      have hθ0 := (abs_le.mp (hθ y)).1
      nlinarith [mul_nonneg he.le (by linarith : 0 ≤ θ y + 1)]
  have hfB : ∑' y, Real.exp (-π * q y / (s / τ₂)) ≤
      τ₂ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s) := by
    have m : ∑' x, Real.exp (-π * (s / τ₂) * a0 x) ≤ ∑' x, Real.exp (-π * s * a0 x) := by
      refine hasSum_le (fun x => ?_) (compactWordAction _ hst2).hasSum (compactWordAction s hs).hasSum
      apply Real.exp_le_exp.mpr
      have hinv := one_le_inv_of_pos_of_le_one h2 h2'
      have hsle : s ≤ s / τ₂ := by
        rw [div_eq_mul_inv]
        nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hinv)]
      nlinarith [mul_nonneg (mul_nonneg hπ.le (ha0 x)) (sub_nonneg.mpr hsle)]
    rw [P0 _ hst2, P0 s hs, Real.div_rpow hs.le h2.le] at m
    have hPT : s ^ (-n / 2) / τ₂ ^ (-n / 2) * τ₂ ^ (-n / 2) = s ^ (-n / 2) := by
      field_simp [hT.ne']
    have m3 : c * s ^ (-n / 2) * ∑' y, Real.exp (-π * q y / (s / τ₂)) ≤
        c * s ^ (-n / 2) * (τ₂ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s)) := by
      have m2 := mul_le_mul_of_nonneg_right m hT.le
      calc c * s ^ (-n / 2) * ∑' y, Real.exp (-π * q y / (s / τ₂))
          = c * (s ^ (-n / 2) / τ₂ ^ (-n / 2) * τ₂ ^ (-n / 2)) *
              ∑' y, Real.exp (-π * q y / (s / τ₂)) := by rw [hPT]
        _ = (c * (s ^ (-n / 2) / τ₂ ^ (-n / 2)) * ∑' y, Real.exp (-π * q y / (s / τ₂))) *
              τ₂ ^ (-n / 2) := by ring
        _ ≤ (c * s ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s)) * τ₂ ^ (-n / 2) := m2
        _ = c * s ^ (-n / 2) * (τ₂ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s)) := by ring
    exact le_of_mul_le_mul_left m3 hK
  have hfin : (∑' y, Real.exp (-π * q y / s)) * 1 ≤
      (∑' y, Real.exp (-π * q y / s)) * (Real.exp (-π * s * (1 - τ₁) * R2) * τ₁ ^ (-n / 2) +
        2 * (Real.exp (-π * (1 - τ₂) * l2 / s) * τ₂ ^ (-n / 2))) := by
    nlinarith [mul_le_mul_of_nonneg_left hfB (mul_pos two_pos hE2).le]
  exact le_of_mul_le_mul_left hfin hS0pos

end PI.Tr
end

open Module
open scoped Real

namespace PI.Tr

theorem numeric_main : 9 / 4 * Real.exp (-(2 * π / 5)) + 2 * (4 * Real.exp (-(25 * π / 24))) < 1 := by
  have hpi := Real.pi_gt_d2
  have e1 := Real.exp_one_gt_d9
  have q1 := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.256 by norm_num)
  have q2 := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.27 by norm_num)
  have p1 := Real.exp_pos 0.256
  have p2 := Real.exp_pos 0.27
  have hX : 3.5 < Real.exp (2 * π / 5) := by
    have h : Real.exp 1.256 ≤ Real.exp (2 * π / 5) := Real.exp_le_exp.mpr (by linarith)
    have h' : Real.exp 1.256 = Real.exp 1 * Real.exp 0.256 := by
      rw [← Real.exp_add]; norm_num
    nlinarith
  have hY : 26 < Real.exp (25 * π / 24) := by
    have h : Real.exp 3.27 ≤ Real.exp (25 * π / 24) := Real.exp_le_exp.mpr (by linarith)
    have h' : Real.exp 3.27 = Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp 0.27 := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; norm_num
    have e3 : 20 < Real.exp 1 * Real.exp 1 * Real.exp 1 := by nlinarith
    nlinarith
  have hXp : 0 < Real.exp (2 * π / 5) := Real.exp_pos _
  have hYp : 0 < Real.exp (25 * π / 24) := Real.exp_pos _
  rw [Real.exp_neg, Real.exp_neg, inv_eq_one_div, inv_eq_one_div]
  have ha : 1 / Real.exp (2 * π / 5) < 2 / 7 := by
    rw [div_lt_iff₀ hXp]; linarith
  have hb : 1 / Real.exp (25 * π / 24) < 1 / 26 := by
    rw [div_lt_iff₀ hYp]; linarith
  linarith

theorem factor_le (κ τ m : ℝ) (hτ : 0 < τ) (hm : 1 ≤ m) (hh : τ⁻¹ * Real.exp (-κ) ≤ 1) :
    Real.exp (-κ * m) * τ ^ (-m) ≤ τ⁻¹ * Real.exp (-κ) := by
  have hb : 0 < τ⁻¹ * Real.exp (-κ) := by positivity
  have key : Real.exp (-κ * m) * τ ^ (-m) = (τ⁻¹ * Real.exp (-κ)) ^ m := by
    rw [Real.mul_rpow (inv_nonneg.mpr hτ.le) (Real.exp_pos _).le, Real.inv_rpow hτ.le,
      ← Real.rpow_neg hτ.le, ← Real.exp_mul]
    ring
  rw [key]
  calc (τ⁻¹ * Real.exp (-κ)) ^ m ≤ (τ⁻¹ * Real.exp (-κ)) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hb hh hm
    _ = τ⁻¹ * Real.exp (-κ) := Real.rpow_one _

theorem gaussStep : GaussStep := by
  intro hP E _ _ _ Λ _ _ lam u hn hlam hdual
  obtain ⟨sA, sQ, c, hc, PE⟩ := hP E Λ
  by_contra hcon
  push_neg at hcon
  set n : ℝ := (finrank ℝ E : ℝ) with hndef
  have hn2 : (2 : ℝ) ≤ n := by rw [hndef]; exact_mod_cast hn
  set m : ℝ := n / 2 with hmdef
  have hm1 : 1 ≤ m := by rw [hmdef]; linarith
  have hm0 : 0 < m := by linarith
  set R2 : ℝ := (m / lam) ^ 2 with hR2
  set s : ℝ := 18 / 25 * lam ^ 2 / m with hsdef
  have hs : 0 < s := by positivity
  have hR : ∀ x : Λ, R2 ≤ ‖(x : E) + -u‖ ^ 2 := by
    intro x
    have h := hcon x x.2
    have h' : m / lam < ‖(x : E) + -u‖ := by
      rw [div_lt_iff₀ hlam, ← sub_eq_add_neg, norm_sub_rev]
      rw [hmdef]; linarith
    rw [hR2]
    exact pow_le_pow_left₀ (by positivity) h'.le 2
  have hl : ∀ y : dualLat Λ, ‖(y : E)‖ ^ 2 < lam ^ 2 →
      Real.cos (2 * π * inner ℝ (y : E) (-u)) = 1 := by
    intro y hy
    have hy' : ‖(y : E)‖ < lam := by
      nlinarith [norm_nonneg (y : E)]
    obtain ⟨k, hk⟩ := hdual y (fun x hx => y.2 x hx) hy'
    rw [inner_neg_right, real_inner_comm, hk]
    have : 2 * π * -(k : ℝ) = ((-k : ℤ) : ℝ) * (2 * π) := by push_cast; ring
    rw [this, Real.cos_int_mul_two_pi]
  have key := gauss_abstract (X := Λ) (Y := dualLat Λ) (fun x => ‖(x : E) + -u‖ ^ 2)
    (fun x => ‖(x : E) + 0‖ ^ 2) (fun y => ‖(y : E)‖ ^ 2)
    (fun y => Real.cos (2 * π * inner ℝ (y : E) (-u))) n c
    (fun y => sq_nonneg _) (fun x => sq_nonneg _) (fun y => Real.abs_cos_le_one _) hc 0
    (fun t ht => sA t ht (-u)) (fun t ht => sA t ht 0) (fun t ht => sQ t ht)
    (fun t ht => PE t ht (-u))
    (fun t ht => by
      rw [PE t ht 0]
      simp only [inner_zero_right, mul_zero, Real.cos_zero, mul_one])
    R2 (lam ^ 2) hR hl s (4 / 9) (1 / 4) hs (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlam0 : lam ≠ 0 := hlam.ne'
  have hm0' : m ≠ 0 := hm0.ne'
  have e1 : -π * s * (1 - 4 / 9) * R2 = -(2 * π / 5) * m := by
    rw [hsdef, hR2]; field_simp; ring
  have e2 : -π * (1 - 1 / 4) * lam ^ 2 / s = -(25 * π / 24) * m := by
    rw [hsdef]; field_simp; ring
  have e3 : -n / 2 = -m := by rw [hmdef]; ring
  rw [e1, e2, e3] at key
  have hN := numeric_main
  have hA : 0 < Real.exp (-(2 * π / 5)) := Real.exp_pos _
  have hB : 0 < Real.exp (-(25 * π / 24)) := Real.exp_pos _
  have f1 := factor_le (2 * π / 5) (4 / 9) m (by norm_num) hm1 (by
    rw [show ((4 : ℝ) / 9)⁻¹ = 9 / 4 by norm_num]; linarith)
  have f2 := factor_le (25 * π / 24) (1 / 4) m (by norm_num) hm1 (by
    rw [show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num]; linarith)
  rw [show ((4 : ℝ) / 9)⁻¹ = 9 / 4 by norm_num] at f1
  rw [show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num] at f2
  linarith

end PI.Tr
end
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SSAscent
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.TraceFormNondegenerateBaseChange
namespace PI.SSAscent.UnitaryGroupMassFormula

open Matrix

theorem traceFormNondegenerate_baseChange : AscendStep := by
  intro K L _ _ _ a S hK
  classical
  set f : Matrix (Fin a) (Fin a) K →+* Matrix (Fin a) (Fin a) L :=
    (algebraMap K L).mapMatrix with hf
  set P : Submodule K (Matrix (Fin a) (Fin a) K) :=
    Subalgebra.toSubmodule (Algebra.adjoin K S) with hP
  let b := Module.finBasis K P
  set m := Module.finrank K P
  let β : Fin m → Matrix (Fin a) (Fin a) K := fun i => (b i : Matrix (Fin a) (Fin a) K)
  have hβA : ∀ i, β i ∈ Algebra.adjoin K S := fun i => (b i).2
  have hspanA : ∀ x ∈ Algebra.adjoin K S, ∃ d : Fin m → K, ∑ i, d i • β i = x := by
    intro x hx
    refine ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩
    have h1 := congrArg Subtype.val (b.sum_repr (⟨x, hx⟩ : P))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1
  have hli : LinearIndependent K β :=
    b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  let G : Matrix (Fin m) (Fin m) K := Matrix.of fun i j => Matrix.trace (β i * β j)
  have hG : G.det ≠ 0 := by
    intro h0
    obtain ⟨d, hd0, hd⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hd0
    have hz : ∑ i, d i • β i = 0 := by
      apply hK
      · exact Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (hβA i) _
      · intro y hy
        obtain ⟨e, rfl⟩ := hspanA y hy
        rw [Finset.mul_sum, trace_sum]
        apply Finset.sum_eq_zero
        intro j _
        have hj : (d ᵥ* G) j = 0 := by rw [hd]; rfl
        rw [mul_smul_comm, trace_smul, Finset.sum_mul, trace_sum]
        simp only [smul_mul_assoc, trace_smul, smul_eq_mul]
        simp only [vecMul, dotProduct, G, Matrix.of_apply] at hj
        rw [hj, mul_zero]
    funext i
    exact (Fintype.linearIndependent_iff.mp hli) d hz i

  have hfA : ∀ y ∈ Algebra.adjoin K S, f y ∈ Algebra.adjoin L (f '' S) := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap r =>
        have : f (algebraMap K _ r) = algebraMap L (Matrix (Fin a) (Fin a) L) (algebraMap K L r) := by
          ext i j
          rw [hf, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply,
            Matrix.algebraMap_matrix_apply]
          split_ifs <;> simp
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hfsmul : ∀ (c : K) (M : Matrix (Fin a) (Fin a) K), f (c • M) = algebraMap K L c • f M := by
    intro c M
    ext i j
    simp [hf]

  have hBspan : ∀ x ∈ Algebra.adjoin L (f '' S),
      x ∈ Submodule.span L (Set.range fun i => f (β i)) := by
    intro x hx
    have hx' : x ∈ Subalgebra.toSubmodule (Algebra.adjoin L (f '' S)) := hx
    rw [Algebra.adjoin_eq_span] at hx'
    refine (Submodule.span_le.mpr ?_) hx'
    have hcl : (Submonoid.closure (f '' S) : Set (Matrix (Fin a) (Fin a) L)) ⊆
        (Submonoid.map (f : Matrix (Fin a) (Fin a) K →* Matrix (Fin a) (Fin a) L)
          (Algebra.adjoin K S).toSubmonoid : Set _) := by
      have : Submonoid.closure (f '' S) ≤
          Submonoid.map (f : Matrix (Fin a) (Fin a) K →* Matrix (Fin a) (Fin a) L)
            (Algebra.adjoin K S).toSubmonoid := by
        rw [Submonoid.closure_le]
        rintro _ ⟨s, hs, rfl⟩
        exact ⟨s, Algebra.subset_adjoin hs, rfl⟩
      exact this
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hcl hz
    obtain ⟨d, rfl⟩ := hspanA y hy
    show f (∑ i, d i • β i) ∈ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hfsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  intro x hx hxy
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp (hBspan x hx)
  have hG' : (G.map (algebraMap K L)).det ≠ 0 := by
    have := RingHom.map_det (algebraMap K L) G
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (map_ne_zero _).mpr hG
  have hc : c ᵥ* G.map (algebraMap K L) = 0 := by
    funext j
    have h1 := hxy (f (β j)) (hfA _ (hβA j))
    rw [Finset.sum_mul, trace_sum] at h1
    simp only [vecMul, dotProduct, Matrix.map_apply, G, Matrix.of_apply, Pi.zero_apply]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, trace_smul, smul_eq_mul, ← map_mul, AddMonoidHom.map_trace]
    rfl
  by_contra hne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (by simp)
  exact hG' (Matrix.exists_vecMul_eq_zero_iff.mp ⟨c, hc0, hc⟩)

end PI.SSAscent.UnitaryGroupMassFormula
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.RangeMapRep
namespace PI.SSAscent.UnitaryGroupMassFormula

open PI.SSAscent

theorem range_mapRep {Γ : Type} [Group Γ] {K L : Type} [Field K] [Field L] [Algebra K L] {a : ℕ}
    (ρ : Γ →* GL (Fin a) K) :
    (Set.range fun g => ((mapRep (algebraMap K L) ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) =
      (algebraMap K L).mapMatrix '' Set.range fun g => (ρ g : Matrix (Fin a) (Fin a) K) := by
  ext M
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨(ρ g : Matrix (Fin a) (Fin a) K), ⟨g, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩

theorem ssAscent_of (hD : DownStep) (hA : AscendStep) (hU : UpStep) : PI.SSAscent := by
  intro K L _ _ _ _ Γ _ a ρ hρ
  apply hU L Γ a
  have h1 : TrNondeg (imAlg ρ) := hD K Γ a ρ hρ
  have h2 := hA K L a (Set.range fun g => (ρ g : Matrix (Fin a) (Fin a) K)) h1
  have h3 : imAlg (mapRep (algebraMap K L) ρ) =
      Algebra.adjoin L ((algebraMap K L).mapMatrix '' Set.range fun g => (ρ g : Matrix (Fin a) (Fin a) K)) :=
    congrArg (Algebra.adjoin L) (range_mapRep (L := L) ρ)
  rw [h3]
  exact h2

end PI.SSAscent.UnitaryGroupMassFormula
end

theorem ssAscent : PI.SSAscent :=
  PI.SSAscent.UnitaryGroupMassFormula.ssAscent_of
    (PI.SSAscent.UnitaryGroupMassFormula.downStep_of PI.SSAscent.UnitaryGroupMassFormula.trace_nilpotent_ascent)
    PI.SSAscent.UnitaryGroupMassFormula.traceFormNondegenerate_baseChange
    PI.SSAscent.UnitaryGroupMassFormula.semisimpleOfTraceFormNondegenerate
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceMinima
theorem transference_successive_minima : PI.TransferenceMinima :=
  PI.Tr.transferenceMinima_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceCover
theorem transference_covering : PI.TransferenceCover :=
  PI.Tr.transferenceCover_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldDCUnfold
section -- merged from Formalism.PeriodIntegrals.FoldDCUnfold
open MeasureTheory
open scoped ENNReal NNReal

namespace PI.FoldDCUnfold

def FoldDCUnfold : Prop :=
  ∀ (G : Type*) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ S S' : Subgroup G) [Countable Γ], S ≤ Γ → S' ≤ Γ →
  ∀ (D D' : Set G), Formalism.L2.SG.FoldBound.IsRightTransversal Γ S D →
    Formalism.L2.SG.FoldBound.IsRightTransversal Γ S' D' →
  ∀ (R : Set G), Formalism.L2.SG.PoincareSeriesSquareIntegrable.IsDoubleTransversal Γ S S' R →
  ∀ (Fs : G → Set G), (∀ r ∈ R, IsFundamentalDomain (Formalism.L2.SG.PoincareSeriesSquareIntegrable.stab S S' r) (Fs r) μ) →
  ∀ (FΓ : Set G), IsFundamentalDomain Γ FΓ μ →
  ∀ (g h : G → ℝ≥0∞), Measurable g → Measurable h →
    (∀ s ∈ S, ∀ y : G, g (s * y) = g y) → (∀ s ∈ S', ∀ y : G, h (s * y) = h y) →
    (∫⁻ x in FΓ, (∑' δ : D, g ((δ : G) * x)) * (∑' δ' : D', h ((δ' : G) * x)) ∂μ)
      = ∑' r : R, ∫⁻ x in Fs r, g x * h ((r : G)⁻¹ * x) ∂μ

end PI.FoldDCUnfold
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.FoldDCUnfoldOf
open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

namespace PI.FoldDCUnfold.W

universe u

theorem pointwise_of (h1 : TransIndep.{u}) (h3 : DCTrans.{u})
    {G : Type u} [Group G] (Γ S S' : Subgroup G) (hS : S ≤ Γ) (hS' : S' ≤ Γ)
    (D D' : Set G) (hD : IsRightTransversal Γ S D) (hD' : IsRightTransversal Γ S' D')
    (R : Set G) (hR : IsDoubleTransversal Γ S S' R)
    (E : G → Set G) (hE : ∀ r ∈ R, IsRightTransversal S (stab S S' r) (E r))
    (g h : G → ℝ≥0∞) (hg : ∀ s ∈ S, ∀ y : G, g (s * y) = g y)
    (hh : ∀ s ∈ S', ∀ y : G, h (s * y) = h y) (x : G) :
    (∑' δ : D, g ((δ : G) * x)) * (∑' δ' : D', h ((δ' : G) * x)) =
      ∑' r : R, ∑' p : (E (r : G) × D),
        g ((p.1 : G) * (p.2 : G) * x) * h ((r : G)⁻¹ * ((p.1 : G) * (p.2 : G) * x)) := by
  obtain ⟨hinj, hT⟩ := h3 G Γ S S' hS hS' R hR E hE
  have key : ∀ δ : D, ∑' δ' : D', h ((δ' : G) * x) =
      ∑' r : R, ∑' t : E (r : G), h ((r : G)⁻¹ * ((t : G) * (δ : G) * x)) := by
    intro δ
    have hδ : (δ : G) ∈ Γ := hD.1 δ.2
    have h1' : ∑' η : Set.range (fun q : (Σ r : R, E (r : G)) => (q.1 : G)⁻¹ * (q.2 : G)),
        h ((η : G) * (δ : G) * x) = ∑' η : D', h ((η : G) * x) :=
      h1 G Γ S' _ D' hT hD' (δ : G) hδ (fun y => h (y * x))
        (fun s hs y => by rw [mul_assoc]; exact hh s hs (y * x))
    have h2' : ∑' η : Set.range (fun q : (Σ r : R, E (r : G)) => (q.1 : G)⁻¹ * (q.2 : G)),
        h ((η : G) * (δ : G) * x) =
        ∑' q : (Σ r : R, E (r : G)), h ((q.1 : G)⁻¹ * (q.2 : G) * (δ : G) * x) :=
      tsum_range (fun η : G => h (η * (δ : G) * x)) hinj
    rw [← h1', h2', ENNReal.tsum_sigma']
    refine tsum_congr fun r => tsum_congr fun t => ?_
    simp only [mul_assoc]
  have hg' : ∀ r : R, ∀ t : E (r : G), ∀ δ : D,
      g ((t : G) * (δ : G) * x) = g ((δ : G) * x) := by
    intro r t δ
    have ht : (t : G) ∈ S := (hE r r.2).1 t.2
    rw [mul_assoc]
    exact hg _ ht _
  calc (∑' δ : D, g ((δ : G) * x)) * (∑' δ' : D', h ((δ' : G) * x))
      = ∑' δ : D, g ((δ : G) * x) * ∑' δ' : D', h ((δ' : G) * x) := ENNReal.tsum_mul_right.symm
    _ = ∑' δ : D, ∑' r : R, ∑' t : E (r : G),
          g ((t : G) * (δ : G) * x) * h ((r : G)⁻¹ * ((t : G) * (δ : G) * x)) := by
        refine tsum_congr fun δ => ?_
        rw [key δ, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun r => ?_
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun t => ?_
        rw [hg' r t δ]
    _ = ∑' r : R, ∑' t : E (r : G), ∑' δ : D,
          g ((t : G) * (δ : G) * x) * h ((r : G)⁻¹ * ((t : G) * (δ : G) * x)) := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun r => ?_
        rw [ENNReal.tsum_comm]
    _ = _ := by
        refine tsum_congr fun r => ?_
        exact (ENNReal.tsum_prod (f := fun (t : E (r : G)) (δ : D) =>
          g ((t : G) * (δ : G) * x) * h ((r : G)⁻¹ * ((t : G) * (δ : G) * x)))).symm

theorem foldDCUnfold_of (h0 : TransExists.{u}) (h1 : TransIndep.{u}) (h2 : TransProd.{u})
    (h3 : DCTrans.{u}) (hU : PI.FoldUnfold.FoldUnfold.{u}) : PI.FoldDCUnfold.FoldDCUnfold.{u} := by
  intro G _ _ _ μ _ Γ S S' _ hS hS' D D' hD hD' R hR Fs hFs FΓ hFΓ g h hgm hhm hg hh
  have hΓc : (Γ : Set G).Countable := Set.countable_coe_iff.mp (inferInstanceAs (Countable Γ))
  have hstabS : ∀ r : G, stab S S' r ≤ S := fun r => inf_le_left
  choose E hE using fun r : G => h0 G S (stab S S' r) (hstabS r)
  have hTP := fun r : G => h2 G Γ S (stab S S' r) (E r) D (hstabS r) hS (hE r) hD
  have hpt : ∀ x : G, (∑' δ : D, g ((δ : G) * x)) * (∑' δ' : D', h ((δ' : G) * x)) =
      ∑' r : R, ∑' η : Set.range (fun p : E (r : G) × D => (p.1 : G) * (p.2 : G)),
        g ((η : G) * x) * h ((r : G)⁻¹ * ((η : G) * x)) := by
    intro x
    rw [pointwise_of h1 h3 Γ S S' hS hS' D D' hD hD' R hR E (fun r _ => hE r) g h hg hh x]
    refine tsum_congr fun r => ?_
    have h2' : ∑' η : Set.range (fun p : E (r : G) × D => (p.1 : G) * (p.2 : G)),
        g ((η : G) * x) * h ((r : G)⁻¹ * ((η : G) * x)) =
        ∑' p : E (r : G) × D,
          g ((p.1 : G) * (p.2 : G) * x) * h ((r : G)⁻¹ * ((p.1 : G) * (p.2 : G) * x)) :=
      tsum_range (fun η : G => g (η * x) * h ((r : G)⁻¹ * (η * x))) (hTP (r : G)).1
    rw [h2']
  have hFm : ∀ r : G, Measurable (fun y : G => g y * h (r⁻¹ * y)) := fun r =>
    hgm.mul (hhm.comp (measurable_const_mul r⁻¹))
  have hinv : ∀ r : G, ∀ s ∈ stab S S' r, ∀ y : G,
      g (s * y) * h (r⁻¹ * (s * y)) = g y * h (r⁻¹ * y) := by
    intro r s hs y
    have hs2 := Subgroup.mem_inf.mp
      (show s ∈ S ⊓ S'.comap (MulAut.conj r⁻¹).toMonoidHom from hs)
    have hs' : r⁻¹ * s * r ∈ S' := by
      simpa [MulAut.conj_apply] using Subgroup.mem_comap.mp hs2.2
    rw [hg s hs2.1 y]
    congr 1
    calc h (r⁻¹ * (s * y)) = h ((r⁻¹ * s * r) * (r⁻¹ * y)) := by congr 1; group
      _ = h (r⁻¹ * y) := hh _ hs' _
  haveI : Countable R := (hΓc.mono hR.1).to_subtype
  simp_rw [hpt]
  rw [lintegral_tsum (fun r => ?_)]
  · refine tsum_congr fun r => ?_
    exact hU G μ Γ (stab S S' r) ((hstabS r).trans hS) (Fs r) (hFs r r.2) FΓ hFΓ _
      (hTP (r : G)).2 (fun y : G => g y * h ((r : G)⁻¹ * y)) (hFm r) (hinv r)
  · haveI : Countable (Set.range (fun p : E (r : G) × D => (p.1 : G) * (p.2 : G))) :=
      (hΓc.mono (hTP (r : G)).2.1).to_subtype
    exact (Measurable.tsum fun η : Set.range (fun p : E (r : G) × D => (p.1 : G) * (p.2 : G)) =>
      (hFm (r : G)).comp (measurable_const_mul (η : G))).aemeasurable

end PI.FoldDCUnfold.W
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.DoubleCosetTranslation
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

namespace PI.FoldDCUnfold.W

universe u

theorem dc_core {G : Type u} [Group G] (Γ S S' : Subgroup G) (hS : S ≤ Γ) (hS' : S' ≤ Γ)
    (R : Set G) (hR : IsDoubleTransversal Γ S S' R)
    (E : G → Set G) (hE : ∀ r ∈ R, IsRightTransversal S (stab S S' r) (E r))
    (p q : Σ r : R, E (r : G)) (s1 s2 : G) (hs1 : s1 ∈ S') (hs2 : s2 ∈ S')
    (heq : s1 * ((p.1 : G)⁻¹ * (p.2 : G)) = s2 * ((q.1 : G)⁻¹ * (q.2 : G))) :
    p = q ∧ s1 = s2 := by
  obtain ⟨⟨r, hr⟩, e, he⟩ := p
  obtain ⟨⟨r', hr'⟩, e', he'⟩ := q
  change s1 * (r⁻¹ * e) = s2 * (r'⁻¹ * e') at heq
  have heS : e ∈ S := (hE r hr).1 he
  have heS' : e' ∈ S := (hE r' hr').1 he'
  have hrr : (⟨r, hr⟩ : R) = ⟨r', hr'⟩ := by
    refine (hR.2 r (hR.1 hr)).unique ⟨1, S.one_mem, 1, S'.one_mem, by simp⟩
      ⟨e * e'⁻¹, S.mul_mem heS (S.inv_mem heS'), s2⁻¹ * s1, S'.mul_mem (S'.inv_mem hs2) hs1, ?_⟩
    calc e * e'⁻¹ * r' * (s2⁻¹ * s1) = e * (s2 * (r'⁻¹ * e'))⁻¹ * s1 := by group
      _ = e * (s1 * (r⁻¹ * e))⁻¹ * s1 := by rw [heq]
      _ = r := by group
  have hrr' : r = r' := congrArg Subtype.val hrr
  subst hrr'
  have hstab : e * e'⁻¹ ∈ stab S S' r := by
    refine Subgroup.mem_inf.mpr ⟨S.mul_mem heS (S.inv_mem heS'), ?_⟩
    rw [Subgroup.mem_comap]
    have h : r⁻¹ * (e * e'⁻¹) * r = s1⁻¹ * s2 := by
      calc r⁻¹ * (e * e'⁻¹) * r = s1⁻¹ * (s1 * (r⁻¹ * e)) * e'⁻¹ * r := by group
        _ = s1⁻¹ * (s2 * (r⁻¹ * e')) * e'⁻¹ * r := by rw [heq]
        _ = s1⁻¹ * s2 := by group
    show r⁻¹ * (e * e'⁻¹) * r⁻¹⁻¹ ∈ S'
    rw [inv_inv, h]
    exact S'.mul_mem (S'.inv_mem hs1) hs2
  have hee : e = e' := by
    have hu := ((hE r hr).2 e heS).unique (y₁ := (1, ⟨e, he⟩))
      (y₂ := (⟨e * e'⁻¹, hstab⟩, ⟨e', he'⟩)) (by simp) (by simp)
    exact congrArg (fun x => (x.2 : G)) hu
  subst hee
  exact ⟨rfl, mul_right_cancel heq⟩

theorem double_coset_translation : DCTrans.{u} := by
  intro G _ Γ S S' hS hS' R hR E hE
  have hEsub : ∀ r ∈ R, E r ⊆ (S : Set G) := fun r hr => (hE r hr).1
  refine ⟨fun p q hpq => ?_, ?_, fun γ hγ => ?_⟩
  · refine (dc_core Γ S S' hS hS' R hR E hE p q 1 1 S'.one_mem S'.one_mem ?_).1
    rw [one_mul, one_mul]
    exact hpq
  · rintro _ ⟨⟨⟨r, hr⟩, ⟨e, he⟩⟩, rfl⟩
    exact Γ.mul_mem (Γ.inv_mem (hR.1 hr)) (hS (hEsub r hr he))
  · obtain ⟨⟨r, hr⟩, ⟨s, hs, s', hs', hrep⟩, -⟩ := hR.2 γ⁻¹ (Γ.inv_mem hγ)
    change s * r * s' = γ⁻¹ at hrep
    obtain ⟨⟨⟨t, ht⟩, ⟨e, he⟩⟩, hte, -⟩ := (hE r hr).2 s⁻¹ (S.inv_mem hs)
    change t * e = s⁻¹ at hte
    have ht' : r⁻¹ * t * r ∈ S' := by
      have h2 := (Subgroup.mem_inf.mp ht).2
      rw [Subgroup.mem_comap] at h2
      change r⁻¹ * t * r⁻¹⁻¹ ∈ S' at h2
      rwa [inv_inv] at h2
    have hmem : s'⁻¹ * (r⁻¹ * t * r) ∈ S' := S'.mul_mem (S'.inv_mem hs') ht'
    have hγeq : s'⁻¹ * (r⁻¹ * t * r) * (r⁻¹ * e) = γ := by
      calc s'⁻¹ * (r⁻¹ * t * r) * (r⁻¹ * e) = s'⁻¹ * r⁻¹ * (t * e) := by group
        _ = s'⁻¹ * r⁻¹ * s⁻¹ := by rw [hte]
        _ = (s * r * s')⁻¹ := by group
        _ = γ := by rw [hrep, inv_inv]
    refine ⟨(⟨s'⁻¹ * (r⁻¹ * t * r), hmem⟩,
      ⟨r⁻¹ * e, ⟨⟨⟨r, hr⟩, ⟨e, he⟩⟩, rfl⟩⟩), hγeq, ?_⟩
    rintro ⟨⟨a, ha⟩, ⟨d, ⟨p, rfl⟩⟩⟩ hy
    obtain ⟨hp, ha'⟩ := dc_core Γ S S' hS hS' R hR E hE p ⟨⟨r, hr⟩, ⟨e, he⟩⟩ a
      (s'⁻¹ * (r⁻¹ * t * r)) ha hmem (hy.trans hγeq.symm)
    subst hp
    exact Prod.ext (Subtype.ext ha') (Subtype.ext rfl)

end PI.FoldDCUnfold.W
end

theorem fold_dc_unfold : PI.FoldDCUnfold.FoldDCUnfold :=
  PI.FoldDCUnfold.W.foldDCUnfold_of PI.FoldDCUnfold.W.translation_exists
    PI.FoldDCUnfold.W.translation_independent PI.FoldDCUnfold.W.translation_product
    PI.FoldDCUnfold.W.double_coset_translation lintegralTransversalSum
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LowSmooth
theorem low_smooth_of_k_finite : PI.KFinSmooth → PI.LowSmooth := PI.UnitaryGroupMassFormula.LowSmooth.lowSmooth_of_kFinSmooth
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldMult
open PI.FoldMult.UnitaryGroupMassFormula

theorem overlapMultiplicityProperties : PI.FoldMult.FoldMult := by
  intro G _ _ _ _ _ _ _ Γ hΓ Ω hΩ h1
  exact ⟨fun x => one_le_mult Γ Ω h1 x, fun x => mult_lt_top Γ Ω hΩ x,
    fun γ hγ x => mult_mul_left Γ Ω γ hγ x, measurable_mult Γ Ω hΩ⟩
end
