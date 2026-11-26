module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.CapVal
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalPB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ToL2CongrOnUnitaryBis
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ThreeAddLeGapBound
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ToL2EqZeroOfEqZeroOnUJset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.Transport

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.TMapSpec
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.TmETmapSmooth
noncomputable section

open Matrix MeasureTheory
open scoped ContDiff InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

section TMapCalc

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mat k r → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D}

theorem tmE_tensV_apply (f : Fin (2 * r + k + 1) → D) (a b c : Fin (2 * r + k + 1)) :
    LemK.tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  by_cases hc : c = a <;> simp [LemK.tensV, LemK.prj, hc]

theorem tmE_coefX_add (x₀ : Mat k r) (w u v : H) (g : Mat k r) :
    coefX σ x₀ w (u + v) g = coefX σ x₀ w u g + coefX σ x₀ w v g := by
  simp [coefX]

theorem tmE_tmap_smooth (x₁ : Fin (2 * r + k + 1) → ℂ) (x₀ : Mat k r) (w : H) (f : Fin (2 * r + k + 1) → H)
    (hsm : ∀ c, Formalism.REAL.SmoothOnG ε (coefX σ x₀ w (f c))) : Formalism.REAL.SmoothOnG ε (tMap ε σ x₁ x₀ w f) := by
  unfold tMap
  exact tmA_sm_sum _ _ fun c _ => Formalism.REAL.smooth_on_group_mul (tmD_cJ_smooth x₁ _) (hsm c)

theorem tmE_eab_tmap (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {x₀ : Mat k r}
    (hx₀ : x₀ ∈ UJset ε) (x₁ : Fin (2 * r + k + 1) → ℂ) (w : H) (f : Fin (2 * r + k + 1) → D)
    (hsm : ∀ c, Formalism.REAL.SmoothOnG ε (coefX σ x₀ w ((f c : D) : H))) (a b : Fin (2 * r + k + 1))
    {g : Mat k r} (hg : g ∈ UJset ε) :
    Formalism.REAL.Eab ε a b (tMap ε σ x₁ x₀ w (fun c => ((f c : D) : H))) g =
      tMap ε σ x₁ x₀ w (fun c => ((LemK.tensV E a b f c : D) : H)) g := by
  have hy : x₀⁻¹ * g ∈ UJset ε := tmA_inUJ_mul (tmA_inUJ_inv hx₀) hg
  unfold tMap
  rw [tmA_eab_sum _ _ (fun c _ => Formalism.REAL.smooth_on_group_mul (tmD_cJ_smooth x₁ _) (hsm c)) a b hg]
  rw [Finset.sum_congr rfl (fun c _ => Formalism.REAL.lie_derivative_mul a b (tmD_cJ_smooth x₁ _) (hsm c) hg)]
  have hZ : ∀ c, cJ ε x₁ (Matrix.single a b 1 *ᵥ Pi.single c 1) g =
      if c = b then cJ ε x₁ (Pi.single a 1) g else 0 := by
    intro c; rw [tmD_single_mulVec]; split_ifs <;> simp [tmD_cJ_zero]
  have hT : ∀ c, coefX σ x₀ w ((LemK.tensV E a b f c : D) : H) g =
      coefX σ x₀ w ((E a b (f c) : D) : H) g + if c = a then coefX σ x₀ w ((f b : D) : H) g else 0 := by
    intro c; rw [tmE_tensV_apply]; split_ifs <;> simp [tmE_coefX_add]
  simp only [tmD_eab_cJ x₁ _ a b hg, tmB_eab_coef hσ hD hy, hZ, hT, ite_mul, zero_mul, mul_add, mul_ite,
    mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

def tmTw (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D) :
    List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → (Fin (2 * r + k + 1) → D) → (Fin (2 * r + k + 1) → D)
  | [], f => f
  | p :: w, f => LemK.tensV E p.1 p.2 (tmTw E w f)

theorem tmE_genSub_E {V : Submodule ℂ D} (a b : Fin (2 * r + k + 1)) {v : D} (hv : v ∈ genSub E V) :
    E a b v ∈ genSub E V := by
  unfold genSub at *
  rw [Submodule.mem_sInf] at *
  intro T hT
  exact hT.2 a b v (hv T hT)

theorem tmE_tmTw_mem {V : Submodule ℂ D} (f : Fin (2 * r + k + 1) → D) (hf : ∀ c, f c ∈ genSub E V) :
    ∀ (wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (c : Fin (2 * r + k + 1)),
      tmTw E wd f c ∈ genSub E V
  | [], c => hf c
  | p :: wd, c => by
      simp only [tmTw]
      rw [tmE_tensV_apply]
      refine Submodule.add_mem _ (tmE_genSub_E _ _ (tmE_tmTw_mem f hf wd c)) ?_
      split_ifs
      · exact tmE_tmTw_mem f hf wd p.2
      · exact Submodule.zero_mem _

theorem tmE_eword_tmap (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {x₀ : Mat k r}
    (hx₀ : x₀ ∈ UJset ε) (x₁ : Fin (2 * r + k + 1) → ℂ) (w : H) {V : Submodule ℂ D} {a : ℝ}
    (hgood : ∀ m : D, m ∈ genSub E V → TmGood ε σ x₀ w a (m : H))
    (f : Fin (2 * r + k + 1) → D) (hf : ∀ c, f c ∈ genSub E V) :
    ∀ (wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (g : Mat k r), g ∈ UJset ε →
      Formalism.REAL.Eword ε wd (tMap ε σ x₁ x₀ w (fun c => ((f c : D) : H))) g =
        tMap ε σ x₁ x₀ w (fun c => ((tmTw E wd f c : D) : H)) g
  | [], _, _ => rfl
  | p :: wd, g, hg => by
      simp only [Formalism.REAL.Eword, tmTw]
      rw [Formalism.REAL.lie_derivative_congr (h := tMap ε σ x₁ x₀ w (fun c => ((tmTw E wd f c : D) : H))) p.1 p.2
        (fun x hx => tmE_eword_tmap hσ hD hx₀ x₁ w hgood f hf wd x hx) hg]
      exact tmE_eab_tmap hσ hD hx₀ x₁ w (tmTw E wd f)
        (fun c => (hgood _ (tmE_tmTw_mem f hf wd c)).1) p.1 p.2 hg

theorem tmE_tmap_bound {x₀ : Mat k r} (x₁ : Fin (2 * r + k + 1) → ℂ) (w : H) {V : Submodule ℂ D} {a : ℝ}
    (hgood : ∀ m : D, m ∈ genSub E V → TmGood ε σ x₀ w a (m : H))
    (f : Fin (2 * r + k + 1) → D) (hf : ∀ c, f c ∈ genSub E V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ UJset ε, ‖tMap ε σ x₁ x₀ w (fun c => ((f c : D) : H)) g‖ ≤ C * frob g ^ (1 - a) := by
  have hb := fun c => (hgood _ (hf c)).2 []
  choose C hC using hb
  obtain ⟨B, hB0, hBb⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ c g, ‖cJ ε x₁ (Pi.single c 1) g‖ ≤ B * frob g :=
    ⟨_, Finset.sum_nonneg fun i _ => norm_nonneg _, fun c g => tmD_cJ_bound x₁ c g⟩
  refine ⟨B * ∑ c, max (C c) 0, mul_nonneg hB0 (Finset.sum_nonneg fun c _ => le_max_right _ _), fun g hg => ?_⟩
  have hF : 1 ≤ frob g := tmA_one_le_frob hg 0
  have hpow : frob g ^ (1 - a) = frob g * frob g ^ (-a) := by
    rw [sub_eq_add_neg, Real.rpow_add (by linarith), Real.rpow_one]
  have hr : 0 ≤ frob g ^ (-a) := Real.rpow_nonneg (by linarith) _
  unfold tMap
  calc ‖∑ c, cJ ε x₁ (Pi.single c 1) g * coefX σ x₀ w ((f c : D) : H) g‖
      ≤ ∑ c, ‖cJ ε x₁ (Pi.single c 1) g‖ * ‖coefX σ x₀ w ((f c : D) : H) g‖ :=
        (norm_sum_le _ _).trans (le_of_eq (by simp))
    _ ≤ ∑ c, (B * frob g) * (max (C c) 0 * frob g ^ (-a)) := by
        refine Finset.sum_le_sum fun c _ => mul_le_mul (hBb c g) ?_ (norm_nonneg _)
          (by positivity)
        exact (hC c g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr)
    _ = (B * ∑ c, max (C c) 0) * frob g ^ (1 - a) := by
        rw [hpow, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => by ring

end TMapCalc

section L2

variable {n : ℕ} {ε : Fin n → Bool}

theorem tmF_memLp {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : Formalism.REAL.SmoothOnG ε F) {C a : ℝ}
    (s : Bool) (ha : ((2 * (n * Fintype.card (S7.SgIxV ε s)) : ℕ) : ℝ) < 2 * (a - 1)) (a₀ : Fin n)
    (hb : ∀ g, Formalism.REAL.inUJ ε g → ‖F g‖ ≤ C * frob g ^ (1 - a)) :
    MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  apply memLp_muG_of_haar ε F 2
  intro ν hν
  have hae : AEStronglyMeasurable (fun g : S7.UJ ε => F (S7.toM g)) ν :=
    (Formalism.REAL.continuous_smooth_on_group_eval hF).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hae]
  have ha1 : 0 ≤ a - 1 := by
    have : (0 : ℝ) ≤ ((2 * (n * Fintype.card (S7.SgIxV ε s)) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast a₀.pos
  have key : ∀ g : S7.UJ ε, 1 ≤ S7.hs (S7.toM g) ∧
      ‖‖F (S7.toM g)‖ ^ 2‖ ≤ C ^ 2 * S7.hs (S7.toM g) ^ (1 - a) := by
    intro g
    have hg : Formalism.REAL.inUJ ε (S7.toM g) := g.2
    have h1 := hb _ hg
    have hfr : 1 ≤ frob (S7.toM g) := tmA_one_le_frob hg a₀
    have hsq : frob (S7.toM g) ^ 2 = S7.hs (S7.toM g) := by
      unfold frob S7.hs; exact Real.sq_sqrt (by positivity)
    refine ⟨by rw [← hsq]; nlinarith, ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖F (S7.toM g)‖ ^ 2 ≤ (C * frob (S7.toM g) ^ (1 - a)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = C ^ 2 * S7.hs (S7.toM g) ^ (1 - a) := by
          rw [mul_pow, Real.rpow_pow_comm (by linarith), hsq]
  refine S7.integrable_of_decayVG ε s ν _ (hae.norm.pow 2) (C ^ 2) ?_ (2 * (a - 1)) ha ?_
  · intro g _
    obtain ⟨h1, h2⟩ := key g
    refine h2.trans ?_
    have : S7.hs (S7.toM g) ^ (1 - a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    exact mul_le_of_le_one_right (sq_nonneg C) this
  · intro g _
    obtain ⟨h1, h2⟩ := key g
    have hx : 0 < S7.hs (S7.toM g) / n := div_pos (by linarith) (by linarith)
    refine ⟨Real.log (S7.hs (S7.toM g) / n) / 2, ?_, h2.trans ?_⟩
    · rw [show 2 * (Real.log (S7.hs (S7.toM g) / n) / 2) = Real.log (S7.hs (S7.toM g) / n) by ring,
        Real.exp_log hx, mul_div_cancel₀ _ (by linarith)]
    · apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
      rw [show -(2 * (a - 1) * (Real.log (S7.hs (S7.toM g) / n) / 2)) =
          Real.log (S7.hs (S7.toM g) / n) * (1 - a) by ring, ← Real.rpow_def_of_pos hx]
      exact Real.rpow_le_rpow_of_nonpos hx (div_le_self (by linarith) hn) (by linarith)

end L2

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

noncomputable section

open Matrix MeasureTheory
open scoped ContDiff InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

theorem tmG_card (n : ℕ) (ε : Fin n → Bool) : ∃ s : Bool, Fintype.card (S7.SgIxV ε s) = S7.q0 ε := by
  by_cases hpq : pOf ε ≤ qOf ε
  · refine ⟨true, ?_⟩
    rw [Fintype.card_subtype]
    show _ = min (pOf ε) (qOf ε)
    rw [min_eq_left hpq]
    rfl
  · refine ⟨false, ?_⟩
    rw [Fintype.card_subtype]
    show _ = min (pOf ε) (qOf ε)
    rw [min_eq_right (le_of_not_ge hpq)]
    rfl

theorem tMap_spec : TMapStatement := by
  intro k r ε lam h H _ _ _ σ D E V T μ ι hσ hD _ _ _ hμ hcoef hp hq hgap hHC hGap x₁ x₀ w hx₀ f hf
  obtain ⟨hq0, hneed⟩ := gapNeed k r ε h hp hq hgap
  have hdd := ReciprocityTheory.ChartRestriction.DS.Lap.S0.DecDeriv.decDeriv _ ε lam h T μ hHC hGap hneed hq0 hμ
  have hmq : (min (pOf ε : ℝ) (qOf ε : ℝ)) = (S7.q0 ε : ℝ) := by
    rw [S7.q0, Nat.cast_min]
  have hg1 := hgap.1
  have hg2 := hgap.2
  rw [hmq] at hg2
  have hh0 : 0 ≤ h := by
    have : 0 ≤ 3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2 := by positivity
    have := le_max_left (3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2)
      (1 + ((2 * r + k + 1 : ℕ) : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))
    linarith
  have ha0 : 0 ≤ aExp ε h := div_nonneg hh0 (by positivity)
  have hA : aExp ε h = h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ))) := rfl
  have hgood : ∀ m : D, m ∈ genSub E V → TmGood ε σ x₀ ((w : D) : H) (aExp ε h) (m : H) :=
    fun m hm => tmC_good_genSub hσ hD hμ hcoef ha0 (fun wd v₁ v₂ => hdd wd v₁ v₂) hx₀ w hm
  have hword := tmE_eword_tmap hσ hD hx₀ x₁ ((w : D) : H) hgood f hf
  have hbd : ∀ wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)), ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ UJset ε,
      ‖Formalism.REAL.Eword ε wd (tMap ε σ x₁ x₀ ((w : D) : H) (fun c => ((f c : D) : H))) g‖ ≤
        C * frob g ^ (1 - aExp ε h) := by
    intro wd
    obtain ⟨C, hC0, hC⟩ := tmE_tmap_bound x₁ ((w : D) : H) hgood (tmTw E wd f) (tmE_tmTw_mem f hf wd)
    exact ⟨C, hC0, fun g hg => by rw [hword wd g hg]; exact hC g hg⟩
  have hsm : Formalism.REAL.SmoothOnG ε (tMap ε σ x₁ x₀ ((w : D) : H) (fun c => ((f c : D) : H))) :=
    tmE_tmap_smooth x₁ x₀ _ _ fun c => (hgood _ (hf c)).1
  refine ⟨⟨hsm, fun wd => ?_⟩, fun a b g hg => tmE_eab_tmap hσ hD hx₀ x₁ _ f
    (fun c => (hgood _ (hf c)).1) a b hg, fun wd => ?_⟩
  · obtain ⟨s, hs⟩ := tmG_card _ ε
    obtain ⟨C, _, hC⟩ := hbd wd
    refine tmF_memLp (Formalism.REAL.smooth_iterated_lie_derivative hsm wd) s ?_ 0 (fun g hg => hC g hg)
    rw [hs]
    have : 0 ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) := by positivity
    have := le_max_left (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2)
    rw [← hA] at hg2
    push_cast at *
    nlinarith
  · obtain ⟨C, _, hC⟩ := hbd wd
    exact ⟨C, hC⟩

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.QuotP
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.QuotPA
noncomputable section

open Matrix MeasureTheory Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.QuotA

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.LemK

section Map

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

def tL (ε : Fin (2 * r + k + 1) → Bool) (σ : Mat k r → (H →L[ℂ] H)) (x₁ : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) : (Fin (2 * r + k + 1) → D) →ₗ[ℂ] (Mat k r → ℂ) where
  toFun f := tMap ε σ x₁ x₀ w (fun c => ((f c : D) : H))
  map_add' f f' := by
    funext g
    simp only [tMap, coefX, Pi.add_apply, Submodule.coe_add, map_add (f := _), inner_add_right, mul_add,
      Finset.sum_add_distrib]
  map_smul' a f := by
    funext g
    simp only [tMap, coefX, Pi.smul_apply, Submodule.coe_smul, map_smul, inner_smul_right, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring

end Map

section Hull

variable {n : ℕ} {ε : Fin n → Bool} {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem exists_kStable_finiteDimensional_submodule_of_mem_Xs (hE : IsGlRep E) (hVfd : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V) {θ : ℝ}
    {x : Fin n → M} (hx : x ∈ Xs (LemK.eeV E) (genSub E V) θ) :
    ∃ S : Submodule ℂ (Fin n → M), S ≤ Xs (LemK.eeV E) (genSub E V) θ ∧ FiniteDimensional ℂ S ∧
      IsKStableSub ε (LemK.tensV E) S ∧ x ∈ S := by
  classical
  have hxg := (mem_eigenTensorSpace_gen_iff.1 hx).1
  choose m hm using fun c => exists_layer_of_mem_genSub hE hVk (hxg c)
  set K := Finset.univ.sup m
  have hxK : ∀ c, x c ∈ layer ε E V K := fun c => layer_mono (Finset.le_sup (mem_univ c)) (hm c)
  have hfdL : FiniteDimensional ℂ (layer ε E V K) := finiteDimensional_layer hVfd K
  have hLk := layer_kStable hE hVk K
  have := pi_submodule_finiteDimensional (n := n) (layer ε E V K)
  refine ⟨Submodule.pi Set.univ (fun _ => layer ε E V K) ⊓ Xs (LemK.eeV E) (genSub E V) θ, inf_le_right,
    Submodule.finiteDimensional_of_le inf_le_left, ?_, ⟨mem_pi_submodule_iff.2 hxK, hx⟩⟩
  intro a b hab f hf
  refine ⟨mem_pi_submodule_iff.2 fun c => ?_, eigenTensorSpace_stable hE a b hf.2⟩
  rw [entry_bounds_of_partialSum]
  refine add_mem (hLk a b hab _ (mem_pi_submodule_iff.1 hf.1 c)) ?_
  split_ifs
  · exact mem_pi_submodule_iff.1 hf.1 b
  · exact zero_mem _

end Hull

section Line

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
  {V : Submodule ℂ D}

theorem line_V (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hint : ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) (hmono : StrictAnti lam) (hGL : GapLap ε lam h)
    (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) (s : Fin n) {N : Type*} [AddCommGroup N] [Module ℂ N]
    (EN : Fin n → Fin n → Module.End ℂ N) :
    ∃ ys ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), ∀ ψ : (Fin n → D) →ₗ[ℂ] N,
      (∀ a b, ∀ y ∈ Submodule.pi Set.univ (fun _ => genSub E V), ψ (LemK.tensV E a b y) = EN a b (ψ y)) →
      ∀ w' ∈ (Xs (LemK.eeV E) (genSub E V) (thV lam s)).map ψ,
        IsKHWVec ε EN (lowK ε (lam + Pi.single s 1)) w' → ∃ c : ℂ, w' = c • ψ ys := by
  classical
  have hK2 := (k2V n ε lam h H σ D E V s hσ hD hV hc hVK hint hmono hGL hp hq).2
  have hKD : IsKUnitary ε E := isKUnitary_of_isInfUnitary (isInfUnitary_of_isDerivedOn hσ hD)
  have hE : IsGlRep E := hD.glRep
  have hXG : ∀ y ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), y ∈ Submodule.pi Set.univ (fun _ => genSub E V) :=
    fun y hy => by simpa [Submodule.mem_pi] using (mem_eigenTensorSpace_gen_iff.1 hy).1

  have hlift : ∀ ψ : (Fin n → D) →ₗ[ℂ] N,
      (∀ a b, ∀ y ∈ Submodule.pi Set.univ (fun _ => genSub E V), ψ (LemK.tensV E a b y) = EN a b (ψ y)) →
      ∀ w' ∈ (Xs (LemK.eeV E) (genSub E V) (thV lam s)).map ψ,
        IsKHWVec ε EN (lowK ε (lam + Pi.single s 1)) w' →
        ∃ y ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), IsKHWVec ε (LemK.tensV E) (lowK ε (lam + Pi.single s 1)) y ∧
          ψ y = w' := by
    intro ψ hψ w' hw' hw'K
    obtain ⟨y₀, hy₀, rfl⟩ := Submodule.mem_map.1 hw'
    obtain ⟨S, hSX, hfd, hSk, hy₀S⟩ := exists_kStable_finiteDimensional_submodule_of_mem_Xs hE hV.1 hV.2.1 hy₀
    obtain ⟨y, hyS, hyK, hyeq⟩ := partialSum_succ_alt hKD ψ hfd hSk (fun a b _ z hz => hψ a b z (hXG z (hSX hz)))
      hy₀S hw'K
    exact ⟨y, hSX hyS, hyK, hyeq⟩
  by_cases hex : ∃ y ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), y ≠ 0 ∧
      IsKHWVec ε (LemK.tensV E) (lowK ε (lam + Pi.single s 1)) y
  · obtain ⟨ys, hysX, hys0, hysK⟩ := hex
    refine ⟨ys, hysX, fun ψ hψ w' hw' hw'K => ?_⟩
    obtain ⟨y, hyX, hyK, rfl⟩ := hlift ψ hψ w' hw' hw'K
    obtain ⟨c₁, c₂, hne, hrel⟩ := hK2 y ys hyX hysX hyK hysK
    by_cases hc1 : c₁ = 0
    · exfalso
      rw [hc1, zero_smul, zero_add] at hrel
      exact hys0 ((smul_eq_zero.1 hrel).resolve_left (hne.resolve_left (not_not.2 hc1)))
    · refine ⟨-(c₁⁻¹ * c₂), ?_⟩
      have h2 : c₁ • y = -(c₂ • ys) := eq_neg_of_add_eq_zero_left hrel
      have hy : y = -(c₁⁻¹ * c₂) • ys := by
        calc y = c₁⁻¹ • (c₁ • y) := by rw [smul_smul, inv_mul_cancel₀ hc1, one_smul]
          _ = -(c₁⁻¹ * c₂) • ys := by rw [h2, smul_neg, smul_smul, neg_smul]
      rw [hy, map_smul]
  · refine ⟨0, zero_mem _, fun ψ hψ w' hw' hw'K => ⟨0, ?_⟩⟩
    obtain ⟨y, hyX, hyK, rfl⟩ := hlift ψ hψ w' hw' hw'K
    have hy0 : y = 0 := by
      by_contra hy0
      exact hex ⟨y, hyX, hy0, hyK⟩
    rw [hy0, map_zero, zero_smul]

end Line

end ReciprocityTheory.ChartRestriction.DS.Lap.QuotA
end
end

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS TransportMapLinear

theorem quotP : QuotPStatement := by
  intro k r ε u lam h H _ _ _ σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap z c Vp _ _ _ π μW μN
    P hP hB x₀ w ξ s x hx₀ hHC' hGap' hx hper
  classical
  obtain ⟨hq0, hNeed⟩ := gapNeed k r ε h hp hq hsg
  have hmin : 1 ≤ min (pOf ε) (qOf ε) := hq0
  have hp1 : 1 ≤ pOf ε := le_trans hmin (min_le_left _ _)
  have hq1 : 1 ≤ qOf ε := le_trans hmin (min_le_right _ _)
  have hGL : GapLap ε lam h := ⟨hHC.1, hGap, hNeed⟩
  have hstd : StdGap ε (lam + Pi.single s 1) :=
    ⟨hHC'.1, h, hGap', by linarith [LemK.three_add_le_gapBound ε]⟩
  have hE := hD.glRep
  have hR := rreg_isURepOn ε
  have hDR := isDerivedOn_smE hR
  have hUR : IsInfUnitary ε (smE ε (rreg ε)) := Base.smInfUnitary _ ε (L2 ε) (rreg ε) hR
  set G : Submodule ℂ (Fin (2 * r + k + 1) → D) := Submodule.pi Set.univ (fun _ => genSub E V) with hGdef
  set X : Submodule ℂ (Fin (2 * r + k + 1) → D) := LemK.Xs (LemK.eeV E) (genSub E V) (LemK.thV lam s)
    with hXdef
  set L := QuotA.tL (D := D) ε σ (xJ P z) x₀ ((w : D) : H) with hLdef
  have hmemG : ∀ f, f ∈ G ↔ ∀ c, f c ∈ genSub E V := fun f => LemK.mem_pi_submodule_iff
  have hXG : X ≤ G := fun f hf => (hmemG f).2 (LemK.mem_eigenTensorSpace_gen_iff.1 hf).1
  have hGs : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := fun a b v hv => LemK.generated_submodule_stable_under_action V a b hv
  have hGA : ∀ a b, ∀ f ∈ G, LemK.tensV E a b f ∈ G := fun a b f hf => by
    refine (hmemG _).2 fun c' => ?_
    rw [LemK.entry_bounds_of_partialSum]
    refine add_mem (hGs a b _ ((hmemG f).1 hf c')) ?_
    split_ifs
    · exact (hmemG f).1 hf b
    · exact zero_mem _
  have hXA : ∀ a b, ∀ f ∈ X, LemK.tensV E a b f ∈ X := fun a b f hf => LemK.eigenTensorSpace_stable hE a b hf
  have hspec := fun (f : Fin (2 * r + k + 1) → D) (hf : f ∈ G) =>
    tMap_spec k r ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap (xJ P z) x₀ w hx₀ f
      ((hmemG f).1 hf)
  have hsm : ∀ f ∈ G, IsSmoothL2 ε (L f) := fun f hf => (hspec f hf).1
  have hder : ∀ f ∈ G, ∀ a b, ∀ g ∈ UJset ε, Formalism.REAL.Eab ε a b (L f) g = L (LemK.tensV E a b f) g :=
    fun f hf a b g hg => (hspec f hf).2.1 a b g hg
  obtain ⟨Tl, hTl, hTint⟩ := exists_lin ε (LemK.tensV E) G L hsm hGA hder
  have hbd : ∀ f ∈ G, ∃ C : ℝ, ∀ g ∈ UJset ε, ‖L f g‖ ≤ C * frob g ^ (1 - aExp ε h) := fun f hf => by
    obtain ⟨C, hC⟩ := (hspec f hf).2.2 []
    exact ⟨C, hC⟩
  have hcont : ∀ f ∈ G, ContinuousOn (L f) (UJset ε) := fun f hf => QuotA.contOn_of_smooth (hsm f hf).1
  set ψ := Formalism.MainNotions.S.psiGen k r z c with hψdef
  let Z : Submodule ℂ (Fin (2 * r + k + 1) → D) :=
    { carrier := {y | y ∈ X ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN ψ π (L y) ξ g = 0}
      add_mem' := by
        rintro y₁ y₂ ⟨h1X, h1⟩ ⟨h2X, h2⟩
        refine ⟨X.add_mem h1X h2X, fun g hg => ?_⟩
        rw [map_add (f := _), QuotA.per_add hP hB hp hq hsg (hcont _ (hXG h1X)) (hbd _ (hXG h1X)) (hcont _ (hXG h2X))
          (hbd _ (hXG h2X)) ξ hg, h1 g hg, h2 g hg, add_zero]
      zero_mem' := by
        refine ⟨X.zero_mem, fun g hg => ?_⟩
        have := QuotA.per_smul P μW μN ψ π 0 0 ξ g
        rw [zero_smul, zero_smul] at this
        rw [map_zero, this]
      smul_mem' := by
        rintro a y ⟨hyX, hy⟩
        refine ⟨X.smul_mem a hyX, fun g hg => ?_⟩
        rw [map_smul, QuotA.per_smul, hy g hg, smul_zero] }
  have hmemZ : ∀ y, y ∈ Z ↔ y ∈ X ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN ψ π (L y) ξ g = 0 :=
    fun y => Iff.rfl
  have hZX : Z ≤ X := fun y hy => ((hmemZ y).1 hy).1
  have hZA : ∀ a b, ∀ y ∈ Z, LemK.tensV E a b y ∈ Z := by
    intro a b y hy
    obtain ⟨hyX, hy0⟩ := (hmemZ y).1 hy
    refine (hmemZ _).2 ⟨hXA a b y hyX, fun g hg => ?_⟩
    rw [← QuotA.per_congr hP hB ψ (fun g' hg' => hder y (hXG hyX) a b g' hg') ξ hg,
      (per_spec k r ε u h z c Vp π μW μN P hP hB hp hq hsg).2 (L y) (hsm y (hXG hyX)).1
        (fun wd => (hspec y (hXG hyX)).2.2 wd) a b g hg ξ]
    exact QuotA.eabB_zero hP (fun y' hy' => hy0 y' hy') a b hg
  have hZφ : ∀ y ∈ X, ∀ y' ∈ Z, Tl y = Tl y' → y ∈ Z := by
    intro y hy y' hy' he
    have e := congrArg Subtype.val he
    rw [hTl y (hXG hy), hTl y' (hXG (hZX hy'))] at e
    have hEq := QuotA.eqOn_unitary_of_toL2_eq (hsm y (hXG hy)) (hsm y' (hXG (hZX hy'))) e
    refine (hmemZ y).2 ⟨hy, fun g hg => ?_⟩
    rw [QuotA.per_congr hP hB ψ hEq ξ hg]
    exact ((hmemZ y').1 hy').2 g hg
  have hxZ : x ∉ Z := by
    intro hxZ
    obtain ⟨g, hg, hne⟩ := hper
    exact hne (((hmemZ x).1 hxZ).2 g hg)
  have hkfin : ∀ x' ∈ X, ∃ S : Submodule ℂ (Fin (2 * r + k + 1) → D), S ≤ X ∧ FiniteDimensional ℂ S ∧
      IsKStableSub ε (LemK.tensV E) S ∧ x' ∈ S := fun x' hx' => QuotA.exists_kStable_finiteDimensional_submodule_of_mem_Xs hE hV.1 hV.2.1 hx'
  have hK3 : ∀ ψ' : (Fin (2 * r + k + 1) → D) →ₗ[ℂ] smD ε (rreg ε),
      (∀ a b, ∀ y ∈ G, ψ' (LemK.tensV E a b y) = smE ε (rreg ε) a b (ψ' y)) →
      ∀ x' ∈ X, ψ' x' ≠ 0 → ∃ W : Submodule ℂ (smD ε (rreg ε)), W ≤ X.map ψ' ∧
        IsKIrrHW ε (smE ε (rreg ε)) (lowK ε (lam + Pi.single s 1)) W ∧
        ∀ v ∈ W, casimir (smE ε (rreg ε)) v = (casVal (lam + Pi.single s 1) : ℂ) • v := by
    intro ψ' hψ' x' hx' hψx'
    exact LemK.k3V _ ε lam h H σ D E V s (smD ε (rreg ε)) (smE ε (rreg ε)) ψ' x' hσ hD hV hc hVK hHC.2
      hHC.1 hGL hp1 hq1 hHC'.1 hDR.glRep hUR (fun a b f hf => hψ' a b f ((hmemG f).2 hf)) hx' hψx'
  have hline : ∃ ys ∈ X, ∀ ψ' : (Fin (2 * r + k + 1) → D) →ₗ[ℂ] smD ε (rreg ε),
      (∀ a b, ∀ y ∈ G, ψ' (LemK.tensV E a b y) = smE ε (rreg ε) a b (ψ' y)) →
      ∀ w' ∈ X.map ψ', IsKHWVec ε (smE ε (rreg ε)) (lowK ε (lam + Pi.single s 1)) w' →
        ∃ c : ℂ, w' = c • ψ' ys :=
    QuotA.line_V hσ hD hV hc hVK hHC.2 hHC.1 hGL hp1 hq1 s (smE ε (rreg ε))
  obtain ⟨Y', W, hY'X, hW, hY'Z, hirr, hcas, hK⟩ :=
    QuotA.quot_generic (LemK.tensV E) G X Z (lam + Pi.single s 1) hstd Tl hXG hTint hK3 hline hkfin hZX hZA
      hZφ hx hxZ
  refine ⟨Y'.map L, W, ?_, ?_, hirr, hcas, hK, ?_⟩
  · rintro F hF
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hF
    exact ⟨y, hY'X hy, rfl⟩
  · intro v
    rw [hW]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨L y, Submodule.mem_map_of_mem hy, hTl y (hXG (hY'X hy))⟩
    · rintro ⟨F, hF, hv⟩
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hF
      exact ⟨y, hy, Subtype.ext (hv.trans (hTl y (hXG (hY'X hy))).symm)⟩
  · rintro F hF hF0
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hF
    have hyZ : y ∈ Z := (hmemZ y).2 ⟨hY'X hy, hF0⟩
    rw [hY'Z y hy hyZ, map_zero]
    intro g _
    rfl

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.CapIdx
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

open CapelliMinorRestriction in
theorem evalP : EvalPStatement := by
  intro k r ε u lam h H _ _ _ σ D E V T μ ι hσ hD hV hcas hK hμ hψ hp hq hgap hHC hGap z c Vp _ _ _ π μW μN P hP hB x₀ w v ξ s g hx₀ hg hu hne
  have hE : IsGlRep E := hD.1
  have hB2 := hB
  unfold IsBData at hB2
  obtain ⟨-, hTz, -, -, hW, hN⟩ := hB2
  have hP2 := hP
  unfold Formalism.MainNotions.S.IsCayley at hP2
  obtain ⟨hPunit, hPJ⟩ := hP2
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPunit
  have hGN := gapNeed k r ε h hp hq hgap
  have hdec := S0.DecDeriv.decDeriv _ ε lam h T μ hHC hGap hGN.2 hGN.1 hμ
  set a := aExp ε h with ha_def
  have hb : S0.bS k r < a - 1 := CurveContinuity.per_gap hgap
  have hh : 0 ≤ h := by
    have h1 := hgap
    unfold StepGap at h1
    have h2 : (0 : ℝ) < h - 2 := lt_of_le_of_lt (by positivity) (lt_of_le_of_lt (le_max_left _ _) h1.1)
    linarith
  have ha0 : 0 ≤ a := by
    rw [ha_def]; unfold aExp; positivity
  set S := genSub E V with hS
  have hgood : ∀ f : D, f ∈ S → TmGood ε σ x₀ ((w : D) : H) a ((f : D) : H) :=
    fun f hf => tmC_good_genSub hσ hD hμ hψ ha0 hdec hx₀ w hf
  set ψg := Formalism.MainNotions.S.psiGen k r z c with hψg
  obtain ⟨L, hLdef⟩ : ∃ L : H → Vp, L = fun m => per P μW μN ψg π (coefX σ x₀ ((w : D) : H) m) ξ g :=
    ⟨_, rfl⟩
  have hlin : ∀ m m' : D, m ∈ S → m' ∈ S → ∀ t : ℂ,
      L ((m : H) + t • (m' : H)) = L m + t • L m' := by
    intro m m' hm hm' t
    rw [hLdef]
    exact EvaluationEquivalence.per_lin hP hB hg hb ξ (hgood m hm) (hgood m' hm') t
  have hL0 : L 0 = 0 := by
    have h1 := hlin 0 0 S.zero_mem S.zero_mem 1
    simp only [ZeroMemClass.coe_zero, smul_zero, add_zero, one_smul] at h1
    simpa using h1
  let l : S →ₗ[ℂ] Vp :=
    { toFun := fun m => L ((m : D) : H)
      map_add' := fun m m' => by
        have h1 := hlin m m' m.2 m'.2 1
        simpa using h1
      map_smul' := fun t m => by
        have h1 := hlin 0 m S.zero_mem m.2 t
        simpa [hL0] using h1 }
  have hl : ∀ m : S, l m = L ((m : D) : H) := fun m => rfl

  obtain ⟨g₀, Dk, ψ', hfr, hup, hzero, hkap, hWW, hCD⟩ :=
    frameLaw k r ε u lam h H σ D E V T μ ι hσ hD hV hcas hK hμ hψ hp hq hgap hHC hGap z c Vp π μW μN P hP hB
      x₀ w ξ g hx₀ hg
  have hfr2 := hfr
  unfold Formalism.MainNotions.S.IsFrameW at hfr2
  have hg₀u : IsUnit g₀.det := TransportGeo.uh_det hfr2.1
  have hgu : IsUnit g.det := TransportGeo.uh_det hg
  set Q : Mat k r := g₀⁻¹ * g * P⁻¹ with hQdef
  have hQu : IsUnit Q.det := by
    rw [hQdef, Matrix.det_mul, Matrix.det_mul]
    exact ((Matrix.isUnit_nonsing_inv_det _ hg₀u).mul hgu).mul (Matrix.isUnit_nonsing_inv_det _ hPu)
  have hQQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQu
  have hQQ' : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQu
  have hgQ : g * P⁻¹ = g₀ * Q := by
    rw [hQdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv g₀ hg₀u, Matrix.one_mul]
  obtain ⟨c₀, hc₀, hcJ⟩ := CapelliMinorRestriction.beta_formula ε P hPJ z hTz g g₀ Q hfr hgQ
  have hSE : ∀ a' b', ∀ x ∈ S, E a' b' x ∈ S := fun a' b' x hx => CapelliMinorRestriction.gen_stable E V a' b' hx
  have hSF : ∀ a' b', ∀ x ∈ S, frameE Q E a' b' x ∈ S :=
    fun a' b' x hx => CapelliMinorRestriction.gen_stable_frame E V Q a' b' hx
  have hvS : (v : D) ∈ S := CapelliMinorRestriction.le_gen E V v.2
  have hcontT : ∀ (x1 : Fin (2 * r + k + 1) → ℂ) (f : Fin (2 * r + k + 1) → D), (∀ c', f c' ∈ S) →
      ContinuousOn (tMap ε σ x1 x₀ ((w : D) : H) (fun c' => ((f c' : D) : H))) (UJset ε) := by
    intro x1 f hf
    unfold tMap
    apply continuousOn_finsetSum
    intro c' _
    apply ContinuousOn.mul
    · rw [← tmD_cJL_coe]
      exact (tmD_cJL ε x1 (Pi.single c' 1)).continuous.continuousOn
    · exact CapelliMinorRestriction.cont_of_smoothOnG (hgood _ (hf c')).1
  have hintT : ∀ f : Fin (2 * r + k + 1) → D, (∀ c', f c' ∈ S) →
      Integrable (CapelliMinorRestriction.perI P ψg π (tMap ε σ (xJ P z) x₀ ((w : D) : H) (fun c' => ((f c' : D) : H))) ξ g)
        (μW.prod μN) := by
    intro f hf
    obtain ⟨C, hC⟩ := (tMap_spec k r ε lam h H σ D E V T μ ι hσ hD hV hcas hK hμ hψ hp hq hgap hHC hGap
      (xJ P z) x₀ w hx₀ f hf).2.2 []
    exact CurveContinuity.int_of_bound hP hB hg ξ a hb _ (hcontT _ f hf) C hC

  set om : ℂ := ((-(LemK.thV lam s) : ℝ) : ℂ) with hom
  have hcmS : ∀ (p : ℕ) (R C : Fin p → Fin (2 * r + k + 1)) (t : ℂ),
      Capelli.cminor (frameE Q E) R C t (v : D) ∈ S :=
    fun p R C t => CapelliMinorMembership.cminor_mem hSF R C t _ hvS
  have key : ∀ j₀ : Fin (2 * r + k + 1),
      per P μW μN ψg π (tMap ε σ (xJ P z) x₀ ((w : D) : H)
        (fun c' => ((Capelli.nnPlus E (Q⁻¹ *ᵥ Pi.single j₀ 1) om (v : D) c' : D) : H))) ξ g =
      (c₀ * (-1 : ℂ) ^ (2 * r + k + (j₀ : ℕ))) •
        L ((Capelli.cminor (frameE Q E) (Fin.last (2 * r + k)).succAbove j₀.succAbove (om - 1) (v : D) : D) : H) := by
    intro j₀
    set y := Q⁻¹ *ᵥ Pi.single j₀ 1 with hy
    have hnnS : ∀ d, Capelli.nnPlus E y om (v : D) d ∈ S := by
      intro d
      unfold Capelli.nnPlus
      apply Submodule.sum_mem
      intro c' _
      exact S.smul_mem _ (CapelliMinorMembership.cminor_mem hSE _ _ _ _ hvS)
    set F : Fin (2 * r + k + 1) → Mat k r → ℂ := fun d =>
      tMap ε σ (xJ P z) x₀ ((w : D) : H) (Pi.single d ((Capelli.nnPlus E y om (v : D) d : D) : H)) with hF
    have hsing : ∀ d, Pi.single d ((Capelli.nnPlus E y om (v : D) d : D) : H) =
        fun c' => (((Pi.single d (Capelli.nnPlus E y om (v : D) d) : Fin (2 * r + k + 1) → D) c' : D) : H) := by
      intro d
      funext c'
      by_cases hc : c' = d
      · subst hc; simp
      · simp [Pi.single_eq_of_ne hc]
    have hint : ∀ d ∈ (Finset.univ : Finset (Fin (2 * r + k + 1))),
        Integrable (CapelliMinorRestriction.perI P ψg π (F d) ξ g) (μW.prod μN) := by
      intro d _
      simp only [hF]
      rw [hsing d]
      apply hintT
      intro c'
      by_cases hc : c' = d
      · subst hc; simpa using hnnS c'
      · simp [Pi.single_eq_of_ne hc]
    have hfs : tMap ε σ (xJ P z) x₀ ((w : D) : H)
        (fun c' => ((Capelli.nnPlus E y om (v : D) c' : D) : H)) = fun G => ∑ d ∈ Finset.univ, F d G :=
      funext fun G => CapelliMinorRestriction.tMap_sum ε σ (xJ P z) x₀ ((w : D) : H) _ G
    rw [hfs, CapelliMinorRestriction.per_sum P μW μN ψg π Finset.univ F ξ g hint]
    rw [Finset.sum_congr rfl (fun d _ => CapelliMinorRestriction.per_tMap_single ε σ z P hPJ μW μN hW hN ψg π x₀ ((w : D) : H) d
      ((Capelli.nnPlus E y om (v : D) d : D) : H) ξ g)]
    simp only [hcJ]
    have hsumS : (∑ d, (c₀ * Q (Fin.last (2 * r + k)) d) • (⟨Capelli.nnPlus E y om (v : D) d, hnnS d⟩ : S)) =
        (c₀ * (-1 : ℂ) ^ (2 * r + k + (j₀ : ℕ))) •
          (⟨Capelli.cminor (frameE Q E) (Fin.last (2 * r + k)).succAbove j₀.succAbove (om - 1) (v : D),
            hcmS _ _ _ _⟩ : S) := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul]
      exact CapelliMinorRestriction.sum_beta_nnPlus (2 * r + k) E hE Q hQQ c₀ j₀ om (v : D)
    have h1 : ∀ d, per P μW μN ψg π (coefX σ x₀ ((w : D) : H) ((Capelli.nnPlus E y om (v : D) d : D) : H)) ξ g =
        l ⟨Capelli.nnPlus E y om (v : D) d, hnnS d⟩ := by
      intro d; rw [hl, hLdef]
    simp only [h1]
    calc ∑ d, (c₀ * Q (Fin.last (2 * r + k)) d) • l ⟨Capelli.nnPlus E y om (v : D) d, hnnS d⟩
        = l (∑ d, (c₀ * Q (Fin.last (2 * r + k)) d) • (⟨Capelli.nnPlus E y om (v : D) d, hnnS d⟩ : S)) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]; simp only [map_smul]
      _ = _ := by rw [hsumS, map_smul]; rfl

  have hfac : ∀ j, (om - 1 - (r : ℂ) + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2) ≠ 0 := by
    intro j
    have e : om - 1 - (r : ℂ) + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2 = ((u j - (lam s + 1 / 2) : ℝ) : ℂ) := by
      rw [hom]; unfold LemK.thV; push_cast; ring
    rw [e, Complex.ofReal_ne_zero, sub_ne_zero]; exact hu j
  have hprod : (∏ j : Fin k, (om - 1 - (r : ℂ) + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hfac j
  have hlv : l ⟨(v : D), hvS⟩ ≠ 0 := by
    rw [hl, hLdef]; exact hne
  have hFE : IsGlRep (frameE Q E) := CapelliMinorRestriction.frameGl Q E hQQ' hQQ hE
  have hRE : IsGlRep (CapelliMinorRestriction.resE (frameE Q E) S hSF) := CapelliMinorRestriction.isGlRep_resE (frameE Q E) S hSF hFE
  have hres : ∀ (R C : Fin (2 * r + k) → Fin (2 * r + k + 1)) (x : ℂ),
      l (Capelli.cminor (CapelliMinorRestriction.resE (frameE Q E) S hSF) R C x ⟨(v : D), hvS⟩) =
        L ((Capelli.cminor (frameE Q E) R C x (v : D) : D) : H) := by
    intro R C x
    rw [hl, CapelliMinorRestriction.cminor_resE]
  have hnz : ∃ j₀ : Fin (2 * r + k + 1),
      L ((Capelli.cminor (frameE Q E) (Fin.last (2 * r + k)).succAbove j₀.succAbove (om - 1) (v : D) : D) : H) ≠ 0 := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · refine ⟨Fin.last (2 * r + k), ?_⟩
      have hkn : k = 2 * r + k := by omega
      obtain ⟨e, he_def⟩ : ∃ e : Fin (k + 1) → Fin (2 * r + k + 1), e = Fin.cast (by omega) := ⟨_, rfl⟩
      have he : Function.Injective e := fun a' b' hab => by
        rw [he_def] at hab; exact Fin.cast_injective _ hab
      have hidx (i : Fin k) : e (Fin.castSucc i) = capIdx k r (Capelli.wIdx k r i) := by
        rw [he_def]
        apply Fin.ext
        change (i : ℕ) = r + (i : ℕ)
        simp only [hr, zero_add]
      have hWW' : ∀ i j, l ∘ₗ (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (e a') (e b'))
          (Fin.castSucc i) (Fin.castSucc j) = Dk i j ∘ₗ l := by
        intro i j
        apply LinearMap.ext
        intro m
        show L (((CapelliMinorRestriction.resE (frameE Q E) S hSF (e (Fin.castSucc i)) (e (Fin.castSucc j)) m : S) : D) : H) =
          Dk i j (L ((m : D) : H))
        rw [hidx i, hidx j, hLdef]
        exact hWW i j m m.2
      have hB0 := Capelli.whittakerZeroStatement S Vp k (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (e a') (e b')) Dk l
        (om - 1) hWW'
      have hcm : Capelli.cminor (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (e a') (e b'))
          Fin.castSucc Fin.castSucc (om - 1) =
          Capelli.cminor (CapelliMinorRestriction.resE (frameE Q E) S hSF) ((Fin.last (2 * r + k)).succAbove ∘ Fin.cast hkn)
            ((Fin.last (2 * r + k)).succAbove ∘ Fin.cast hkn) (om - 1) := by
        rw [CapelliMinorRestriction.cminor_reindex _ e he]
        congr 1 <;> funext i <;> exact Fin.ext (by simp [he_def, Fin.succAbove_last])
      rw [CapelliMinorRestriction.cminor_cast _ hkn] at hcm
      have h1 := LinearMap.congr_fun hB0 ⟨(v : D), hvS⟩
      simp only [LinearMap.comp_apply] at h1
      rw [hcm, hCD, hres] at h1
      rw [h1]
      have hprod0 : (∏ j : Fin k, (om - 1 + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2)) ≠ 0 := by
        simpa [hr] using hprod
      exact smul_ne_zero hprod0 hlv
    · refine ⟨0, ?_⟩
      have hkn : k + 2 * r = 2 * r + k := by omega
      have hcapinj : Function.Injective (capIdx k r) := by
        delta capIdx
        exact Fin.cast_injective _
      have hup' : ∀ a' b', Capelli.blk k r a' < Capelli.blk k r b' →
          l ∘ₗ (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (capIdx k r a') (capIdx k r b')) a' b' =
            ψ' a' b' • l := by
        intro a' b' hab
        apply LinearMap.ext
        intro m
        show L (((CapelliMinorRestriction.resE (frameE Q E) S hSF (capIdx k r a') (capIdx k r b') m : S) : D) : H) =
          ψ' a' b' • L ((m : D) : H)
        rw [hLdef]
        exact hup a' b' hab m m.2
      have hWW' : ∀ i j, l ∘ₗ (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (capIdx k r a') (capIdx k r b'))
          (Capelli.wIdx k r i) (Capelli.wIdx k r j) = Dk i j ∘ₗ l := by
        intro i j
        apply LinearMap.ext
        intro m
        show L (((CapelliMinorRestriction.resE (frameE Q E) S hSF (capIdx k r (Capelli.wIdx k r i)) (capIdx k r (Capelli.wIdx k r j)) m :
          S) : D) : H) = Dk i j (L ((m : D) : H))
        rw [hLdef]
        exact hWW i j m m.2
      have hB1 := Capelli.capelliB S Vp k r
        (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (capIdx k r a') (capIdx k r b')) Dk ψ' l (om - 1)
        (CapelliMinorRestriction.isGlRep_reindex _ (capIdx k r) hcapinj hRE) hr hup' hzero hWW'
      have hcm : Capelli.cminor (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (capIdx k r a') (capIdx k r b'))
          Fin.castSucc Fin.succ (om - 1) =
          Capelli.cminor (CapelliMinorRestriction.resE (frameE Q E) S hSF) ((Fin.last (2 * r + k)).succAbove ∘ Fin.cast hkn)
            ((0 : Fin (2 * r + k + 1)).succAbove ∘ Fin.cast hkn) (om - 1) := by
        rw [CapelliMinorRestriction.cminor_reindex _ (capIdx k r) hcapinj]
        congr 1 <;> funext i <;> apply Fin.ext <;> delta capIdx <;>
          simp only [Function.comp_apply, Fin.succAbove_last, Fin.succAbove_zero, Fin.val_cast,
            Fin.val_castSucc, Fin.val_succ]
      rw [CapelliMinorRestriction.cminor_cast _ hkn] at hcm
      have h1 := LinearMap.congr_fun hB1 ⟨(v : D), hvS⟩
      simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h1
      rw [hcm, hCD, hres] at h1
      rw [h1]
      exact smul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (hkap hr)) (smul_ne_zero hprod hlv)
  obtain ⟨j₀, hj₀⟩ := hnz
  refine ⟨Q⁻¹ *ᵥ Pi.single j₀ 1, ?_⟩
  rw [key j₀]
  exact smul_ne_zero (mul_ne_zero hc₀ (pow_ne_zero _ (by norm_num))) hj₀

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

theorem stepUp : StepUpStatement := by
  intro hIS k r ε u h hgap hp hq lam s hlam hgl hlam' hgl' hu hB
  classical
  obtain ⟨T, μ, P, z, c, Vp, _, _, _, π, μW, μN, hμ, hP, hBD, v₁, v₂, ξ, x₀, x, hx₀, hx, hne⟩ := hB
  obtain ⟨hq0, hNeed⟩ := gapNeed k r ε h hp hq hgap
  have hdatum := LemK.psiDatum (2 * r + k + 1) ε lam h T μ hlam hgl hNeed hq0 hμ
  obtain ⟨H, _, _, _, σ, D, E, V, ι, hσ, hD, hV, hc, hVK, hcoef⟩ := hdatum
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hX₀ : P * x₀ * P⁻¹ ∈ UJset ε := cayley_conj_mem_unitary_group hP hx₀
  have hper : per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π
      (coefX σ (P * x₀ * P⁻¹) (((ι.symm v₂ : V) : D) : H) (((ι.symm v₁ : V) : D) : H)) ξ x =
      aaFun T μ P μW μN (Formalism.MainNotions.S.psiGen k r z c) π v₁ v₂ ξ x₀ x := by
    have hHW := hBD.2.2.2.2.1
    have hHN := hBD.2.2.2.2.2
    have : SigmaFinite μW := hHW.1
    have : SigmaFinite μN := hHN.1
    unfold per aaFun sInt
    apply integral_congr_ae
    filter_upwards [ae_mem_unitary_nilpotent_product z μW μN hHW hHN] with p hp'
    have hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
      unitary_hermitian_form_mul_mem hp'.1.1 hp'.2.1
    have hg := unitary_hermitian_form_mul_mem hs hx
    have hinv : x₀⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := (Transport.uh_facts hP hx₀).2.1
    have hG : P * (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) * P⁻¹ ∈ UJset ε :=
      cayley_conj_mem_unitary_group hP (unitary_hermitian_form_mul_mem hinv hg)
    have hX : P⁻¹ * (P * x₀ * P⁻¹) * P = x₀ := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.nonsing_inv_mul _ hd,
        Matrix.mul_one]
    have heq : (P * x₀ * P⁻¹)⁻¹ * (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) =
        P * (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) * P⁻¹ := by
      have h1 := conj_inv_mul_conj P (P * x₀ * P⁻¹) (Matrix.of p.1 * Matrix.of p.2 * x) hd
      rw [hX] at h1
      exact h1.symm
    show coefX σ (P * x₀ * P⁻¹) _ _ (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) • _ =
      psiCoef T μ P v₁ v₂ (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) • _
    unfold coefX psiCoef
    rw [heq, hcoef _ hG (ι.symm v₁) (ι.symm v₂)]
    simp only [LinearEquiv.apply_symm_apply]
  have hne' : per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π
      (coefX σ (P * x₀ * P⁻¹) (((ι.symm v₂ : V) : D) : H) (((ι.symm v₁ : V) : D) : H)) ξ x ≠ 0 := by
    rw [hper]; exact hne
  obtain ⟨y, hy⟩ := evalP k r ε u lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hgap hlam hgl z c Vp π
    μW μN P hP hBD (P * x₀ * P⁻¹) (ι.symm v₂) (ι.symm v₁) ξ s x hX₀ hx hu hne'
  have hstab : ∀ a b, ∀ m ∈ genSub E V, E a b m ∈ genSub E V := fun a b _ hm =>
    LemK.generated_submodule_stable_under_action V a b hm
  have hkill : ∀ m ∈ genSub E V, Capelli.capelliC E (((-(LemK.thV lam s)) : ℝ) : ℂ) m = 0 := by
    intro m hm
    rw [capVal (2 * r + k + 1) ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hlam hgl hNeed hq0 _ m hm,
      Finset.prod_eq_zero (Finset.mem_univ s) (by push_cast; ring), zero_smul]
  have hvS : (((ι.symm v₁ : V) : D)) ∈ genSub E V :=
    LemK.le_generatedSubmodule_dual V (ι.symm v₁).2
  have hXs := (eig D (2 * r + k) E (genSub E V) (-(LemK.thV lam s)) y y ((ι.symm v₁ : V) : D)
    hD.glRep hstab hkill hvS).1
  rw [neg_neg] at hXs
  obtain ⟨Wf, W', hWf, hW', hirr, hcas, hK, hinj⟩ := quotP k r ε u lam h H σ D E V T μ ι hσ hD hV hc hVK hμ
    hcoef hp hq hgap hlam hgl z c Vp π μW μN P hP hBD (P * x₀ * P⁻¹) (ι.symm v₂) ξ s
    (Capelli.nnPlus E y (((-(LemK.thV lam s)) : ℝ) : ℂ) ((ι.symm v₁ : V) : D)) hX₀ hlam' hgl' hXs ⟨x, hx, hy⟩
  refine finStep hIS k r ε u (lam + Pi.single s 1) h z c Vp π μW μN P hP hBD hp hq hgap hlam' hgl' ξ Wf W'
    ?_ hW' hirr hcas hK hinj
  intro F hF
  obtain ⟨y', hy', rfl⟩ := hWf F hF
  have hyS : ∀ c', y' c' ∈ genSub E V := (LemK.mem_eigenTensorSpace_gen_iff.1 hy').1
  obtain ⟨hsm, -, hbd⟩ := tMap_spec k r ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hgap hlam hgl
    (xJ P z) (P * x₀ * P⁻¹) (ι.symm v₂) hX₀ y' hyS
  obtain ⟨C, hC⟩ := hbd []
  exact ⟨CapelliMinorRestriction.cont_of_smoothOnG hsm.1, C, hC⟩

end ReciprocityTheory.ChartRestriction.DS.Lap
