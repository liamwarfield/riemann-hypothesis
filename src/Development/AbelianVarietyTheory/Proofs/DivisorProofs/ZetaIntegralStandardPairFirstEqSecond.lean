module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallFStdB
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.StdPairZetaB
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem blk₁_mul_left {m a a' : ℕ} (M : Matrix (Fin m) (Fin m) k) (X : Matrix (Fin m) (Fin (a + a')) k) :
    blk₁ (M * X) = M * blk₁ X := by
  ext i j; simp [blk₁, Matrix.mul_apply]

theorem blk₂_mul_left {m a a' : ℕ} (M : Matrix (Fin m) (Fin m) k) (X : Matrix (Fin m) (Fin (a + a')) k) :
    blk₂ (M * X) = M * blk₂ X := by
  ext i j; simp [blk₂, Matrix.mul_apply]

theorem cball_mul_left {m n : ℕ} {s : kˣ} {M : Matrix (Fin m) (Fin m) k} (hM : ∀ i j, M i j ∈ 𝒪[k])
    {N : Matrix (Fin m) (Fin n) k} (hN : ∀ i j, N i j ∈ cball s) : ∀ i j, (M * N) i j ∈ cball s := fun i j => by
  have hN' : ∀ i j, valuation k (N i j) ≤ valuation k (s : k) := hN
  change valuation k _ ≤ valuation k (s : k)
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact (mul_le_mul' (hM i l) (hN' l j)).trans (by rw [one_mul])

theorem mem_KO_of_isGLO {n : ℕ} (g : GL (Fin n) k) (h : IsGLO g.val) : g ∈ KO k (Fin n) := by
  let A : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨g.val i j, h.1 i j⟩
  have e : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
  have hu : IsUnit A.det := by
    refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
    rw [RingHom.map_det, e]; exact h.2
  obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det A).2 hu
  refine ⟨u, Units.ext ?_⟩
  change (algebraMap 𝒪[k] k).mapMatrix u.val = g.val
  rw [hu', e]

theorem isGLO_of_mem_KO {n : ℕ} {g : GL (Fin n) k} (h : g ∈ KO k (Fin n)) : IsGLO g.val :=
  ⟨((mem_KO_iff g).1 h).1, valuation_gdet_of_mem_KO h⟩

end GlobalTheory.StdPairZetaB


open GlobalTheory.StdPairZetaB in
theorem GlobalTheory.StdPairZetaB.smallF_stdB : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ),
    (∀ Y : Matrix (Fin a') (Fin (a + a')) k, (blk₂ Y).det = 0 →
      smallF (haarVol (KO k (Fin a'))) ν (stdB ν ϖ c a a') Y = 0) ∧
    ∀ (Y : Matrix (Fin a') (Fin (a + a')) k) (g₂ : GL (Fin a') k), g₂.val = blk₂ Y →
      smallF (haarVol (KO k (Fin a'))) ν (stdB ν ϖ c a a') Y =
        (((ν (gdet g₂))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₂) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) *
          Set.indicator {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 ((g₂⁻¹).val * blk₁ Y) := by
  intro k _ _ _ _ _ _ ν ϖ c a a'
  refine ⟨fun Y hY => ?_, fun Y g₂ hg₂ => ?_⟩
  · have h0 : ∀ g : GL (Fin a') k, stdB ν ϖ c a a' (g.val * Y) = 0 := fun g => by
      unfold stdB
      rw [dite_eq_right]
      rintro ⟨h0, -⟩
      apply h0
      rw [blk₂_mul_left, Matrix.det_mul, hY, mul_zero]
    simp [smallF, h0]
  · set d : ℂ := (Fintype.card (Fin (a + a')) : ℂ) / 2 with hd
    set C : ℂ := (((ν (gdet g₂))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₂) (-d) *
      Set.indicator {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 ((g₂⁻¹).val * blk₁ Y) with hC
    set S : Set (GL (Fin a') k) := (fun g => g * g₂) ⁻¹' (KO k (Fin a') : Set (GL (Fin a') k)) with hSdef
    have hSm : @MeasurableSet (GL (Fin a') k) Units.instMeasurableSpace S := by
      letI : MeasurableSpace (GL (Fin a') k) := Units.instMeasurableSpace
      haveI : BorelSpace (GL (Fin a') k) := borel_GL
      exact (isOpen_KO.preimage (continuous_mul_const _)).measurableSet
    have hS1 : (haarVol (KO k (Fin a'))).real S = 1 := by
      simp [hSdef, Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]
    have hint : ∀ g : GL (Fin a') k, stdB ν ϖ c a a' (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) d =
        S.indicator (fun _ => C) g := by
      intro g
      have hb₂ : blk₂ (g.val * Y) = g.val * blk₂ Y := blk₂_mul_left _ _
      have hb₁ : blk₁ (g.val * Y) = g.val * blk₁ Y := blk₁_mul_left _ _
      by_cases hg : g ∈ S
      · rw [Set.indicator_of_mem hg]
        have hκ : g * g₂ ∈ KO k (Fin a') := hg
        have hG := isGLO_of_mem_KO hκ
        have e₂ : blk₂ (g.val * Y) = (g * g₂).val := by rw [hb₂, ← hg₂, Units.val_mul]
        have e₁ : blk₁ (g.val * Y) = (g * g₂).val * ((g₂⁻¹).val * blk₁ Y) := by
          rw [hb₁, ← Matrix.mul_assoc, Units.val_mul, Matrix.mul_assoc g.val, ← Units.val_mul, mul_inv_cancel,
            Units.val_one, Matrix.mul_one]
        have hgd : gdet g = gdet (g * g₂) * (gdet g₂)⁻¹ := by rw [gdet_mul]; group
        have hap : apow (gdet g) d = apow (gdet g₂) (-d) := by
          rw [hgd, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hκ), one_mul, apow_inv]
        unfold stdB
        by_cases hP : ∀ i j, ((g₂⁻¹).val * blk₁ Y) i j ∈ cball (ϖ ^ c)
        · have hcond : (blk₂ (g.val * Y)).det ≠ 0 ∧ IsGLO (blk₂ (g.val * Y)) ∧
              ∀ i j, blk₁ (g.val * Y) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
            rw [e₂, e₁]
            exact ⟨(g * g₂).det_ne_zero, hG, cball_mul_left hG.1 hP⟩
          rw [dite_eq_left hcond, hC, Set.indicator_of_mem (show ((g₂⁻¹).val * blk₁ Y) ∈
            {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} from hP), Pi.one_apply, mul_one, hap]
          have hu : Units.mk0 _ hcond.1 = gdet g * gdet g₂ := Units.ext (by
            rw [Units.val_mk0, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply,
              Matrix.GeneralLinearGroup.val_det_apply, hb₂, ← hg₂, Matrix.det_mul])
          rw [hu, map_mul, mul_inv_rev, Units.val_mul]
          have h1 : ((ν (gdet g))⁻¹ : ℂˣ) * (ν (gdet g) : ℂ) = 1 := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
          linear_combination ((((ν (gdet g₂))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₂) (-d)) * h1
        · have hcond : ¬ ((blk₂ (g.val * Y)).det ≠ 0 ∧ IsGLO (blk₂ (g.val * Y)) ∧
              ∀ i j, blk₁ (g.val * Y) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) := by
            rintro ⟨-, -, h3⟩
            apply hP
            have hinv := (mem_KO_iff (g * g₂)).1 hκ
            have := cball_mul_left hinv.2 h3
            rwa [e₁, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this
          rw [dite_eq_right hcond, hC, Set.indicator_of_notMem (show ((g₂⁻¹).val * blk₁ Y) ∉
            {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} from hP)]
          simp
      · rw [Set.indicator_of_notMem hg]
        unfold stdB
        rw [dite_eq_right, zero_mul, zero_mul]
        rintro ⟨-, h2, -⟩
        apply hg
        show g * g₂ ∈ KO k (Fin a')
        apply mem_KO_of_isGLO
        rwa [Units.val_mul, hg₂, ← hb₂]
    rw [smallF, ← hd]
    simp_rw [hint]
    rw [integral_indicator_const (μ := haarVol (KO k (Fin a'))) C hSm, hS1, one_smul]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKOOfIsGLO
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.StdPairZeta
open GlobalTheory.OneSquareZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem blk₁_mul {m a a' : ℕ} (M : Matrix (Fin m) (Fin a) k) (X : Matrix (Fin a) (Fin (a + a')) k) :
    blk₁ (M * X) = M * blk₁ X := by
  ext i j; simp [blk₁, Matrix.mul_apply]

theorem blk₂_mul {m a a' : ℕ} (M : Matrix (Fin m) (Fin a) k) (X : Matrix (Fin a) (Fin (a + a')) k) :
    blk₂ (M * X) = M * blk₂ X := by
  ext i j; simp [blk₂, Matrix.mul_apply]

theorem val_gdet {a : ℕ} (g : GL (Fin a) k) : ((gdet g : kˣ) : k) = g.val.det := by
  first | rfl | exact Matrix.GeneralLinearGroup.val_det_apply g

theorem isGLO_of_mem_KO {a : ℕ} {g : GL (Fin a) k} (hg : g ∈ KO k (Fin a)) : g.val.det ≠ 0 ∧ IsGLO g.val := by
  have hv : valuation k g.val.det = 1 := by rw [← val_gdet]; exact GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO hg
  exact ⟨fun h => by simp [h] at hv, ((GlobalTheory.SplitFlip.mem_KO_iff g).1 hg).1, hv⟩

theorem mem_KO_of_isGLO {a : ℕ} (g : GL (Fin a) k) (h : IsGLO g.val) : g ∈ KO k (Fin a) := by
  obtain ⟨hM, hd⟩ := h
  let A : Matrix (Fin a) (Fin a) 𝒪[k] := fun i j => ⟨g.val i j, hM i j⟩
  have e : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
  have hu : IsUnit A.det := by
    refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
    rw [RingHom.map_det, e, hd]
  obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det A).2 hu
  refine ⟨u, Units.ext ?_⟩
  change (algebraMap 𝒪[k] k).mapMatrix u.val = g.val
  rw [hu', e]

theorem mul_mem_cball {n m p : ℕ} {s : kˣ} {M : Matrix (Fin n) (Fin m) k} {Y : Matrix (Fin m) (Fin p) k}
    (hM : ∀ i j, M i j ∈ 𝒪[k]) (hY : ∀ i j, Y i j ∈ GlobalTheory.SplitWeil.cball s) :
    ∀ i j, (M * Y) i j ∈ GlobalTheory.SplitWeil.cball s := by
  intro i j
  simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, Matrix.mul_apply] at hY ⊢
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact (mul_le_mul' ((Valuation.mem_integer_iff _ _).1 (hM i l)) (hY l j)).trans_eq (one_mul _)

variable [MeasurableSpace k] [BorelSpace k]

theorem bigF_stdA_zero (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (X : Matrix (Fin a) (Fin (a + a')) k)
    (hX : (blk₁ X).det = 0) : bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X = 0 := by
  have h0 : ∀ g : Matrix (Fin a) (Fin a) k, stdA ν ϖ c a a' (g * X) = 0 := by
    intro g
    unfold stdA
    rw [dite_eq_right]
    rintro ⟨h, -⟩
    exact h (by rw [blk₁_mul, Matrix.det_mul, hX, mul_zero])
  simp [bigF, shellSum, shell, h0]

theorem bigF_stdA_eq (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (hϖ : IsUnif ϖ) (X : Matrix (Fin a) (Fin (a + a')) k)
    (g₁ : GL (Fin a) k) (hg₁ : g₁.val = blk₁ X) :
    bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X =
      (((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₁) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) *
        Set.indicator {M : Matrix (Fin a) (Fin a') k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 ((g₁⁻¹).val * blk₂ X) := by
  set N : ℂ := (Fintype.card (Fin (a + a')) : ℂ) / 2 with hN
  set Y := (g₁⁻¹).val * blk₂ X with hY
  set C : ℂ := (((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₁) (-N) *
      Set.indicator {M : Matrix (Fin a) (Fin a') k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 Y with hC
  set S : Set (GL (Fin a) k) := (fun g => g * g₁) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k)) with hSdef
  have hSm : @MeasurableSet (GL (Fin a) k) Units.instMeasurableSpace S := by
    letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
    haveI : BorelSpace (GL (Fin a) k) := borel_GL
    exact (isOpen_KO.preimage (continuous_mul_const _)).measurableSet
  have hS1 : (haarVol (KO k (Fin a))).real S = 1 := by
    simp [hSdef, Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]
  have hint : ∀ g : GL (Fin a) k, stdA ν ϖ c a a' (g.val * X) * (ν (gdet g) : ℂ) * apow (gdet g) N =
      S.indicator (fun _ => C) g := by
    intro g
    have h1 : blk₁ (g.val * X) = (g * g₁).val := by rw [blk₁_mul, Units.val_mul, hg₁]
    have h2 : blk₂ (g.val * X) = (g * g₁).val * Y := by
      rw [blk₂_mul, hY, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel_right]
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg]
      have hκ : g * g₁ ∈ KO k (Fin a) := hg
      obtain ⟨hdet, hglo⟩ := isGLO_of_mem_KO hκ
      have hv : valuation k ((gdet (g * g₁) : kˣ) : k) = 1 := GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO hκ
      have hinv : (g * g₁)⁻¹ ∈ KO k (Fin a) := inv_mem hκ
      have hYiff : (∀ i j, ((g * g₁).val * Y) i j ∈ cball (ϖ ^ c)) ↔ ∀ i j, Y i j ∈ cball (ϖ ^ c) := by
        constructor
        · intro h
          have e : Y = ((g * g₁)⁻¹).val * ((g * g₁).val * Y) := by
            rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
          rw [e]; exact mul_mem_cball ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hinv).1 h
        · exact mul_mem_cball ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hκ).1
      have hap : apow (gdet g) N = apow (gdet g₁) (-N) := by
        have : gdet g = gdet (g * g₁) * (gdet g₁)⁻¹ := by rw [gdet_mul]; group
        rw [this, apow_mul, apow_of_valuation_eq_one hv, one_mul, apow_inv]
      unfold stdA
      by_cases hc : ∀ i j, Y i j ∈ cball (ϖ ^ c)
      · have hcond : (blk₁ (g.val * X)).det ≠ 0 ∧ IsGLO (blk₁ (g.val * X)) ∧
            ∀ i j, blk₂ (g.val * X) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
          rw [h1, h2]; exact ⟨hdet, hglo, hYiff.2 hc⟩
        have hmk : Units.mk0 _ hcond.1 = gdet g * gdet g₁ := by
          rw [← gdet_mul]; exact Units.ext (by rw [Units.val_mk0, val_gdet, h1])
        rw [dite_eq_left hcond, hC, Set.indicator_of_mem (show Y ∈ {M : Matrix (Fin a) (Fin a') k |
          ∀ i j, M i j ∈ cball (ϖ ^ c)} from hc), Pi.one_apply, mul_one, hmk, hap, map_mul, mul_inv]
        simp only [Units.val_mul, Units.val_inv_eq_inv_val]
        have h3 := (ν (gdet g)).ne_zero
        linear_combination ((ν (gdet g₁) : ℂ))⁻¹ * apow (gdet g₁) (-N) * inv_mul_cancel₀ h3
      · have hneg : ¬ ((blk₁ (g.val * X)).det ≠ 0 ∧ IsGLO (blk₁ (g.val * X)) ∧
            ∀ i j, blk₂ (g.val * X) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) := by
          rintro ⟨-, -, h⟩
          rw [h2] at h
          exact hc (hYiff.1 h)
        rw [dite_eq_right hneg, hC, Set.indicator_of_notMem (show Y ∉ {M : Matrix (Fin a) (Fin a') k |
          ∀ i j, M i j ∈ cball (ϖ ^ c)} from hc)]
        simp
    · rw [Set.indicator_of_notMem hg]
      have hneg : ¬ ((blk₁ (g.val * X)).det ≠ 0 ∧ IsGLO (blk₁ (g.val * X)) ∧
          ∀ i j, blk₂ (g.val * X) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) := by
        rintro ⟨-, hglo, -⟩
        rw [h1] at hglo
        exact hg (mem_KO_of_isGLO _ hglo)
      unfold stdA
      rw [dite_eq_right hneg, zero_mul, zero_mul]
  have hshell : ∀ m : {m : Fin a → ℤ // Antitone m}, shell (haarVol (KO k (Fin a))) ϖ ν N
      (fun M => stdA ν ϖ c a a' (M * X)) m.1 = (haarVol (KO k (Fin a))).real (shellSet ϖ m.1 ∩ S) • C := by
    intro m
    rw [shell]
    simp_rw [hint]
    have e1 := setIntegral_indicator (μ := haarVol (KO k (Fin a))) (s := shellSet ϖ m.1)
      (f := fun _ => C) hSm
    rw [e1, setIntegral_const]
  obtain ⟨⟨m₀, hm₀⟩, hmem, huniq⟩ := exists_unique_shell hϖ g₁⁻¹
  have hsub : S ⊆ shellSet ϖ m₀ := by
    intro g hg
    obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hmem
    refine mem_shellSet.2 ⟨g * g₁ * x, mul_mem hg hx, y, hy, ?_⟩
    calc g = g * g₁ * g₁⁻¹ := by group
      _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
  rw [bigF, shellSum, finsum_eq_single _ ⟨m₀, hm₀⟩]
  · rw [hshell, Set.inter_eq_right.2 hsub, hS1, one_smul]
  · intro m hm
    rw [hshell]
    have : shellSet ϖ m.1 ∩ S = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun g ⟨hg1, hg2⟩ => hm (huniq m ?_)
      obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hg1
      refine mem_shellSet.2 ⟨(g * g₁)⁻¹ * x, mul_mem (inv_mem hg2) hx, y, hy, ?_⟩
      calc g₁⁻¹ = (g * g₁)⁻¹ * g := by group
        _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
    simp [this]

end GlobalTheory.StdPairZeta


open GlobalTheory.StdPairZeta in
theorem GlobalTheory.StdPairZeta.bigF_stdA : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ), IsUnif ϖ →
    (∀ X : Matrix (Fin a) (Fin (a + a')) k, (blk₁ X).det = 0 →
      bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X = 0) ∧
    ∀ (X : Matrix (Fin a) (Fin (a + a')) k) (g₁ : GL (Fin a) k), g₁.val = blk₁ X →
      bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X =
        (((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₁) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) *
          Set.indicator {M : Matrix (Fin a) (Fin a') k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 ((g₁⁻¹).val * blk₂ X) := by
  intro k _ _ _ _ _ _ ν ϖ c a a' hϖ
  exact ⟨fun X hX => bigF_stdA_zero ν ϖ c a a' X hX, fun X g₁ hg₁ => bigF_stdA_eq ν ϖ c a a' hϖ X g₁ hg₁⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralStandardPairFirstEqSecond
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

namespace GlobalTheory.StdZetaAgree
open GlobalTheory.StdPairCone

theorem jacobi_blocks {k m n : Type} [Field k] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (H G : Matrix (m ⊕ n) (m ⊕ n) k) (e : H * G = 1) :
    H.det * G.toBlocks₁₁.det = H.toBlocks₂₂.det ∧
      H.toBlocks₂₁ * G.toBlocks₁₁ + H.toBlocks₂₂ * G.toBlocks₂₁ = 0 := by
  rw [← Matrix.fromBlocks_toBlocks H, ← Matrix.fromBlocks_toBlocks G, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at e
  obtain ⟨e1, -, e3, -⟩ := e
  refine ⟨?_, e3⟩
  have e4 : H * Matrix.fromBlocks G.toBlocks₁₁ 0 G.toBlocks₂₁ 1 =
      Matrix.fromBlocks 1 H.toBlocks₁₂ 0 H.toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks H]
    rw [Matrix.fromBlocks_multiply, e1, e3]
    simp
  have := congrArg Matrix.det e4
  rwa [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    Matrix.det_one, mul_one, one_mul] at this

theorem blocks_rel {k : Type} [Field k] {a a' : ℕ} (h : GL (Fin (a + a')) k) :
    h.val.det * (blk₁ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val)).det = (blk₂ (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val)).det ∧
      blk₁ (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val) * (blk₁ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val))ᵀ +
        blk₂ (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val) * (blk₂ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val))ᵀ = 0 := by
  set H : Matrix (Fin a ⊕ Fin a') (Fin a ⊕ Fin a') k := h.val.submatrix finSumFinEquiv finSumFinEquiv with hH
  set G : Matrix (Fin a ⊕ Fin a') (Fin a ⊕ Fin a') k := (h⁻¹).val.submatrix finSumFinEquiv finSumFinEquiv with hG
  have e : H * G = 1 := by
    rw [hH, hG, Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  obtain ⟨e1, e2⟩ := jacobi_blocks H G e
  have x1 : (blk₁ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val))ᵀ = G.toBlocks₁₁ := by
    ext i j; exact frameMatrixFirstColumnBlock_mul_apply (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) (invT h).val j (Fin.castAdd a' i)
  have x2 : (blk₂ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val))ᵀ = G.toBlocks₂₁ := by
    ext i j; exact frameMatrixFirstColumnBlock_mul_apply (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) (invT h).val j (Fin.natAdd a i)
  have y1 : blk₁ (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val) = H.toBlocks₂₁ := by
    ext i j; exact frameMatrixSecondColumnBlock_mul_apply (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) h.val i (Fin.castAdd a' j)
  have y2 : blk₂ (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val) = H.toBlocks₂₂ := by
    ext i j; exact frameMatrixSecondColumnBlock_mul_apply (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) h.val i (Fin.natAdd a j)
  have hd : H.det = h.val.det := Matrix.det_submatrix_equiv_self _ _
  refine ⟨?_, by rw [x1, x2, y1, y2]; exact e2⟩
  rw [← Matrix.det_transpose (blk₁ _), x1, y2, ← hd]; exact e1

end GlobalTheory.StdZetaAgree


open GlobalTheory.StdPairCone GlobalTheory.StdZetaAgree in
theorem GlobalTheory.StdZetaAgree.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ), IsUnif ϖ →
      bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β (GlobalTheory.StdPairCone.stdA ν ϖ c a a') =
        smallP (haarVol (KO k (Fin a'))) finSumFinEquiv ν (ν * β) (GlobalTheory.StdPairCone.stdB ν ϖ c a a') := by
  intro k _ _ _ _ _ _ ν β ϖ c a a' hϖ
  funext h
  obtain ⟨hA0, hA⟩ := GlobalTheory.StdPairZeta.bigF_stdA ν ϖ c a a' hϖ
  obtain ⟨hB0, hB⟩ := GlobalTheory.StdPairZetaB.smallF_stdB ν ϖ c a a'
  obtain ⟨e1, e2⟩ := blocks_rel h
  rw [bigZetaIntegral_eq, smallP]
  set X : Matrix (Fin a) (Fin (a + a')) k := X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val with hX
  set Y : Matrix (Fin a') (Fin (a + a')) k := Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val with hY
  by_cases h0 : (blk₁ X).det = 0
  · rw [hA0 X h0, hB0 Y (by rw [← e1, h0, mul_zero]), mul_zero, mul_zero]
  have h1 : (blk₂ Y).det ≠ 0 := by rw [← e1]; exact mul_ne_zero h.det_ne_zero h0
  set g₁ : GL (Fin a) k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ h0 with hg₁
  set g₂ : GL (Fin a') k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ h1 with hg₂
  have v₁ : g₁.val = blk₁ X := rfl
  have v₂ : g₂.val = blk₂ Y := rfl
  rw [hA X g₁ v₁, hB Y g₂ v₂]
  have hd : gdet g₂ = gdet h * gdet g₁ := Units.ext (by
    rw [Units.val_mul, GlobalTheory.StdPairZeta.val_gdet, GlobalTheory.StdPairZeta.val_gdet, GlobalTheory.StdPairZeta.val_gdet, v₁, v₂, e1])
  have hm : (g₂⁻¹).val * blk₁ Y = -((g₁⁻¹).val * blk₂ X)ᵀ := by
    rw [← v₁, ← v₂] at e2
    have e3 : blk₁ Y = -(g₂.val * (blk₂ X)ᵀ * (g₁⁻¹).valᵀ) := by
      rw [← Matrix.neg_mul, ← eq_neg_of_add_eq_zero_left e2, Matrix.mul_assoc, ← Matrix.transpose_mul,
        Units.inv_mul, Matrix.transpose_one, Matrix.mul_one]
    rw [e3, Matrix.mul_neg, Matrix.mul_assoc g₂.val, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
      Matrix.transpose_mul]
  have hi : Set.indicator {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} (1 : Matrix (Fin a') (Fin a) k → ℂ)
      ((g₂⁻¹).val * blk₁ Y) = Set.indicator {M : Matrix (Fin a) (Fin a') k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1
        ((g₁⁻¹).val * blk₂ X) := by
    rw [hm]
    generalize (g₁⁻¹).val * blk₂ X = Z
    have hiff : (-Zᵀ) ∈ {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} ↔
        Z ∈ {M : Matrix (Fin a) (Fin a') k | ∀ i j, M i j ∈ cball (ϖ ^ c)} := by
      simp only [Set.mem_setOf_eq, GlobalTheory.SplitWeil.cball, Matrix.neg_apply, Matrix.transpose_apply, Valuation.map_neg]
      exact forall_comm
    by_cases hZ : Z ∈ {M : Matrix (Fin a) (Fin a') k | ∀ i j, M i j ∈ cball (ϖ ^ c)}
    · rw [Set.indicator_of_mem hZ, Set.indicator_of_mem (hiff.2 hZ)]; rfl
    · rw [Set.indicator_of_notMem hZ, Set.indicator_of_notMem (fun h => hZ (hiff.1 h))]
  have hp : apow (gdet h) (-(a : ℂ) / 2) = apow (gdet h) ((Fintype.card (Fin a') : ℂ) / 2) *
      apow (gdet h) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) := by
    rw [← apow_add]; congr 1; simp only [Fintype.card_fin]; push_cast; ring
  rw [hi, hd, apow_mul, hp, map_mul, mul_inv, MonoidHom.mul_apply]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  have h3 := (ν (gdet h)).ne_zero
  field_simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralStandardPairFirstEqSecondStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaIntegral_standardPair_first_eq_second : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ), IsUnif ϖ →
      bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β (GlobalTheory.StdPairCone.stdA ν ϖ c a a') =
        smallP (haarVol (KO k (Fin a'))) finSumFinEquiv ν (ν * β) (GlobalTheory.StdPairCone.stdB ν ϖ c a a') := by
  first | exact @GlobalTheory.StdZetaAgree.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB | exact GlobalTheory.StdZetaAgree.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB | (intros; apply GlobalTheory.StdZetaAgree.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB <;> assumption)
end
