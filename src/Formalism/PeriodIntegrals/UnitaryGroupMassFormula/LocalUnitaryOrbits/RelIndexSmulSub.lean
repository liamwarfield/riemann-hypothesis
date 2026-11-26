module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OmAtComplZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHI
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdDual

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ExistsIntSmulMemAll
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ExistsIntBasis
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SdVolWOfTop
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.PairHermZeroRight
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.VolSqMulIndex
noncomputable section

namespace PI.OmLocU.Sd

open MeasureTheory PI.VolStabSW.SdUniqW Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

section Vol

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]

theorem vol_mul_vol_ann {μ : Measure V} {χ : V → V → ℂ} (hμ : SelfDual μ χ)
    (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (h0 : ∀ y, χ y 0 = 1) (L L' : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V))
    (hL'c : IsCompact (L' : Set V)) (hL'o : IsOpen (L' : Set V)) (hA : ann χ (L : Set V) = L') :
    μ.real (L : Set V) * μ.real (L' : Set V) = 1 := by
  classical
  have := hμ.1
  set c : ℝ := μ.real (L : Set V) with hc
  have hcl : IsClopen (L : Set V) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  set Φ : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hΦ
  have hΦc : Continuous Φ := by
    rw [hΦ, ← Set.piecewise_eq_indicator]
    exact continuous_const.piecewise (by simp [hcl.frontier_eq]) continuous_const
  have hΦs : HasCompactSupport Φ :=
    HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂μ = (L' : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) y := by
    intro y
    rw [hΦ, PI.VolStabSW.SdUniqW.transform_indicator μ χ hχ L hLo y, hA]
  have hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ := by
    have e : (fun y => ∫ x, Φ x * χ x y ∂μ) = (L' : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) :=
      funext hT
    rw [e, integrable_indicator_iff hL'o.measurableSet]
    exact integrableOn_const hL'c.measure_lt_top.ne
  have h1 := hμ.2 Φ hΦc hΦs hI 0
  have e1 : (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y 0) =
      (L' : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) := by
    funext y
    rw [hT y, h0, mul_one]
  rw [e1, integral_indicator_const _ hL'o.measurableSet, neg_zero, hΦ,
    Set.indicator_of_mem (SetLike.mem_coe.2 L.zero_mem)] at h1
  have h2 : μ.real (L' : Set V) * c = 1 := by
    rw [Complex.real_smul] at h1
    exact_mod_cast h1
  rw [mul_comm]
  exact h2

theorem vol_sq_mul_index {μ : Measure V} {χ : V → V → ℂ} (hμ : SelfDual μ χ)
    (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (h0 : ∀ y, χ y 0 = 1) (L L' : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V))
    (hL'c : IsCompact (L' : Set V)) (hL'o : IsOpen (L' : Set V)) (hA : ann χ (L : Set V) = L')
    (hle : L ≤ L') (hN : L.relIndex L' ≠ 0) :
    μ.real (L : Set V) ^ 2 * (L.relIndex L' : ℝ) = 1 := by
  have := hμ.1
  have h1 := vol_mul_vol_ann hμ hχ h0 L L' hLc hLo hL'c hL'o hA
  have h2 := PI.VolStabSW.measure_eq_relIndex_mul μ L L' hle hL'o.measurableSet
    hLo.measurableSet hN
  have h3 : μ.real (L' : Set V) = (L.relIndex L' : ℝ) * μ.real (L : Set V) := by
    rw [measureReal_def, measureReal_def, h2, ENNReal.toReal_mul]
    simp
  rw [h3] at h1
  linarith [h1]

end Vol

section Ann

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem ann_eq_cond {V : Type} (ψ0 : Fv F v → ℂ) (d : Fv F v) (B : V → V → Fv F v) (L : Set V)
    (hC : ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, ψ0 (s * t) = 1) ↔
      d * t ∈ v.adicCompletionIntegers F)
    (hs : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ L, ∃ x' ∈ L, ∀ y, B x' y = s * B x y) :
    ann (fun x y => ψ0 (B x y)) L = {y | ∀ x ∈ L, d * B x y ∈ v.adicCompletionIntegers F} := by
  ext y
  constructor
  · intro hy x hx
    rw [← hC]
    intro s hs'
    obtain ⟨x', hx', h⟩ := hs s hs' x hx
    rw [← h y]
    exact hy x' hx'
  · intro hy x hx
    have ht := (hC _).2 (hy x hx) 1 (one_mem _)
    simpa using ht

end Ann

end PI.OmLocU.Sd
end
end

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.VolStabSW
  PI.VolStabSW.SdUniqW PI.VolStabSW.LatFactsW
open scoped TensorProduct

section Oev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem oev_add {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x + y ∈ OEv (E := E) v := Submodule.add_mem _ hx hy

theorem oev_zero : (0 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := Submodule.zero_mem _

theorem oev_neg {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) : -x ∈ OEv (E := E) v :=
  Submodule.neg_mem _ hx

theorem oev_smul {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E}
    (hx : x ∈ OEv (E := E) v) : s • x ∈ OEv (E := E) v :=
  Submodule.smul_mem _ (⟨s, hs⟩ : v.adicCompletionIntegers F) hx

theorem sdc_sc_mul (x : Fv F v) (c : Fv F v ⊗[F] E) : sc (E := E) v x * c = x • c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul y e => simp [sc, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
  | add p q hp hq => rw [mul_add, hp, hq, smul_add]

theorem dV_int : dV v ∈ v.adicCompletionIntegers F := by
  unfold dV
  split_ifs with h
  · obtain ⟨x, _, he⟩ := h.choose_spec.2.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← he]
    rw [show algebraMap F (Fv F v) ((x : 𝓞 F) : F) = (((x : 𝓞 F) : F) : v.adicCompletion F) from rfl,
      v.valuedAdicCompletion_eq_valuation']
    exact v.valuation_le_one x
  · exact one_mem _

theorem dV_ne_zero : dV v ≠ 0 := by
  unfold dV
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

theorem psiV_zero (ψ : AddChar (AF F) ℂ) : psiV F ψ v 0 = 1 := by
  have hs : singleV F v (0 : Fv F v) = 0 := by
    have h := SdUniqW.singleV_add v (0 : Fv F v) 0
    rw [add_zero] at h
    simpa using h
  rw [psiV, hs]
  convert AddChar.map_zero_eq_one ψ
  rfl

theorem unif_ne_zero {ϖ : Fv F v} (h : IsUnif v ϖ) : ϖ ≠ 0 := by
  intro h0
  rw [IsUnif, h0, map_zero] at h
  exact WithZero.coe_ne_zero h.symm

theorem unif_int {ϖ : Fv F v} (h : IsUnif v ϖ) : ϖ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, h]
  exact le_of_lt (by decide)

end Oev

section HermO

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

def HO (a : ℕ) : AddSubgroup (HermR (Fv F v) σ a) where
  carrier := {S | ∀ i j, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v}
  add_mem' := fun {_ _} hx hy i j => oev_add v (hx i j) (hy i j)
  zero_mem' := fun _ _ => oev_zero v
  neg_mem' := fun {_} hx i j => oev_neg v (hx i j)

theorem mem_HO {a : ℕ} (S : HermR (Fv F v) σ a) :
    S ∈ HO σ v a ↔ ∀ i j, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v :=
  Iff.rfl

theorem smul_mem_HO {a : ℕ} {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F)
    {S : HermR (Fv F v) σ a} (hS : S ∈ HO σ v a) : s • S ∈ HO σ v a := by
  rw [mem_HO] at hS ⊢
  intro i j
  rw [coe_hermSMul, Matrix.smul_apply]
  exact oev_smul v hs (hS i j)

theorem hermitianDivisible_eq_smul {a : ℕ} {ϖ : Fv F v} (hϖ : ϖ ≠ 0) :
    HermP v σ a ϖ = (smulSub ϖ (HO σ v a) : Set (HermR (Fv F v) σ a)) := by
  ext S
  rw [SetLike.mem_coe, mem_smulSub]
  simp only [HermP, PO, Set.mem_ofPred_eq]
  constructor
  · intro hS
    refine ⟨ϖ⁻¹ • S, ?_, ?_⟩
    · rw [mem_HO]
      intro i j
      obtain ⟨c, hc, he⟩ := hS i j
      rw [coe_hermSMul, Matrix.smul_apply, he, sdc_sc_mul, smul_smul, inv_mul_cancel₀ hϖ, one_smul]
      exact hc
    · rw [smul_smul, mul_inv_cancel₀ hϖ, one_smul]
  · rintro ⟨p, hp, rfl⟩ i j
    refine ⟨(p : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j, hp i j, ?_⟩
    rw [coe_hermSMul, Matrix.smul_apply, sdc_sc_mul]

theorem pairHerm_smul_left {a : ℕ} (s : Fv F v) (S T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a (s • S) T = s * pairHerm (Fv F v) σ a S T := by
  simp only [pairHerm, coe_hermSMul, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul,
    smul_eq_mul]
  ring

theorem pairHerm_zero_right {a : ℕ} (S : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a S 0 = 0 := by
  simp [pairHerm]

end HermO

section Steps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def TopH (a : ℕ) : Prop :=
  IsCompact (HO σ v a : Set (HermR (Fv F v) σ a)) ∧ IsOpen (HO σ v a : Set (HermR (Fv F v) σ a))

def DualH (a : ℕ) : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v →
    {T : HermR (Fv F v) σ a | ∀ S ∈ HO σ v a,
      dV v * pairHerm (Fv F v) σ a S T ∈ v.adicCompletionIntegers F} =
      (smulSub (dV v)⁻¹ (HO σ v a) : Set (HermR (Fv F v) σ a))

def IdxHO (a : ℕ) : Prop :=
  UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ((HO σ v a).relIndex (smulSub (dV v)⁻¹ (HO σ v a)) : ℝ) = absV v (dV v) ^ (-((a : ℝ) ^ 2)) ∧
    ((smulSub ϖ (HO σ v a)).relIndex (HO σ v a) : ℝ) = qv v ^ (a ^ 2)

theorem sdVolH_of_top (a : ℕ) (hC : CondV σ J ψ v) (hT : TopH σ v a) (hD : DualH σ J ψ v a)
    (hI : IdxHO σ v a) : SdVolH σ J ψ v a := by
  intro hS hU hν ϖ hϖ
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hϖ0 := unif_ne_zero v hϖ
  have hd0 := dV_ne_zero v
  have hνsd : SdHerm F E σ (Fv F v) (psiV F ψ v) a (dT σ ψ v a) := by
    simp only [dT, dif_pos hν]
    exact hν.choose_spec
  have := hνsd.1
  set ν := dT σ ψ v a with hνdef
  set L := HO σ v a with hLdef
  set L' := smulSub (dV v)⁻¹ L with hL'def
  obtain ⟨hLc, hLo⟩ := hT
  have hL'c : IsCompact (L' : Set (HermR (Fv F v) σ a)) := isCompact_smulSub _ L hLc
  have hL'o : IsOpen (L' : Set (HermR (Fv F v) σ a)) := isOpen_smulSub _ (inv_ne_zero hd0) L hLo
  have hχ : ∀ x t y : HermR (Fv F v) σ a, psiV F ψ v (pairHerm (Fv F v) σ a (t + x) y) =
      psiV F ψ v (pairHerm (Fv F v) σ a t y) * psiV F ψ v (pairHerm (Fv F v) σ a x y) := by
    intro x t y
    rw [pairHerm_add, psiV_add]
  have h0 : ∀ y : HermR (Fv F v) σ a, psiV F ψ v (pairHerm (Fv F v) σ a y 0) = 1 := by
    intro y
    rw [pairHerm_zero_right, psiV_zero]
  have hA : ann (fun S T => psiV F ψ v (pairHerm (Fv F v) σ a S T)) (L : Set (HermR (Fv F v) σ a)) =
      L' := by
    rw [Sd.ann_eq_cond v (psiV F ψ v) (dV v) (pairHerm (Fv F v) σ a) _ (hC hS)]
    · exact hD hS hU
    · intro s hs x hx
      exact ⟨s • x, smul_mem_HO σ v hs hx, fun y => pairHerm_smul_left σ v s x y⟩
  have hle : L ≤ L' := by
    intro S hS'
    rw [hL'def, mem_smulSub]
    refine ⟨dV v • S, smul_mem_HO σ v (dV_int v) hS', ?_⟩
    rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
  obtain ⟨hN1, hN2⟩ := hI hU ϖ hϖ
  have hNz : L.relIndex L' ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hN1
    have := Real.rpow_pos_of_pos (absV_dV_pos v) (-((a : ℝ) ^ 2))
    linarith
  have key := Sd.vol_sq_mul_index hνsd hχ h0 L L' hLc hLo hL'c hL'o hA hle hNz
  rw [hN1] at key
  have hp := absV_dV_pos v
  have hvolL : ν.real (L : Set (HermR (Fv F v) σ a)) = absV v (dV v) ^ ((a : ℝ) ^ 2 / 2) := by
    have e1 : absV v (dV v) ^ (-((a : ℝ) ^ 2)) = (absV v (dV v) ^ ((a : ℝ) ^ 2))⁻¹ :=
      Real.rpow_neg hp.le _
    have e2 : (absV v (dV v) ^ ((a : ℝ) ^ 2 / 2)) ^ 2 = absV v (dV v) ^ ((a : ℝ) ^ 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
      norm_num
    have hA2 : 0 < absV v (dV v) ^ ((a : ℝ) ^ 2) := Real.rpow_pos_of_pos hp _
    rw [e1] at key
    have e3 : ν.real (L : Set (HermR (Fv F v) σ a)) ^ 2 = (absV v (dV v) ^ ((a : ℝ) ^ 2 / 2)) ^ 2 := by
      rw [e2]
      field_simp at key
      linarith
    exact (pow_left_inj₀ measureReal_nonneg (Real.rpow_pos_of_pos hp _).le two_ne_zero).1 e3
  have hle2 : smulSub ϖ L ≤ L := by
    intro S hS'
    rw [mem_smulSub] at hS'
    obtain ⟨p, hp', rfl⟩ := hS'
    exact smul_mem_HO σ v (unif_int v hϖ) hp'
  have hPo : IsOpen (smulSub ϖ L : Set (HermR (Fv F v) σ a)) := isOpen_smulSub _ hϖ0 L hLo
  have hPc : IsCompact (smulSub ϖ L : Set (HermR (Fv F v) σ a)) := isCompact_smulSub _ L hLc
  have hNz2 : (smulSub ϖ L).relIndex L ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hN2
    have := pow_pos (qv_pos v) (a ^ 2)
    linarith
  have h2 := PI.VolStabSW.measure_eq_relIndex_mul ν (smulSub ϖ L) L hle2 hLo.measurableSet
    hPo.measurableSet hNz2
  have h3 : ν.real (L : Set (HermR (Fv F v) σ a)) =
      ((smulSub ϖ L).relIndex L : ℝ) * ν.real (smulSub ϖ L : Set (HermR (Fv F v) σ a)) := by
    rw [measureReal_def, measureReal_def, h2, ENNReal.toReal_mul]
    simp
  rw [hN2, hvolL] at h3
  rw [hermitianDivisible_eq_smul σ v hϖ0, ← ENNReal.ofReal_toReal hPc.measure_lt_top.ne, ← measureReal_def]
  congr 1
  have hq := pow_pos (qv_pos v) (a ^ 2)
  have e4 : qv v ^ (-((a : ℤ) ^ 2)) = (qv v ^ (a ^ 2))⁻¹ := by
    rw [zpow_neg]
    congr 1
  rw [e4, h3]
  field_simp

end Steps

end PI.OmLocU
end
end

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
  PI.VolStabSW PI.VolStabSW.SdUniqW
open scoped TensorProduct

section Steps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def LW (a : ℕ) : AddSubgroup (TupV (E := E) v n a) where
  carrier := LamT v Λ a
  add_mem' := fun {_ _} hx hy i => Submodule.add_mem _ (hx i) (hy i)
  zero_mem' := fun _ => Submodule.zero_mem _
  neg_mem' := fun {_} hx i => Submodule.neg_mem _ (hx i)

theorem coe_LW (a : ℕ) : (LW v Λ a : Set (TupV (E := E) v n a)) = LamT v Λ a := rfl

theorem smul_mem_LW {a : ℕ} {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F)
    {X : TupV (E := E) v n a} (hX : X ∈ LW v Λ a) : s • X ∈ LW v Λ a :=
  fun i => Submodule.smul_mem _ (⟨s, hs⟩ : v.adicCompletionIntegers F) (hX i)

def TopW (a : ℕ) : Prop :=
  (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsCompact (LamT (E := E) v Λ a) ∧ IsOpen (LamT (E := E) v Λ a)

def DualW (a : ℕ) : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v →
    {Y : TupV (E := E) v n a | ∀ X ∈ LamT v Λ a,
      dV v * BR (Fv F v) σ J X Y ∈ v.adicCompletionIntegers F} =
      (smulSub (dV v)⁻¹ (LW v Λ a) : Set (TupV (E := E) v n a))

def IdxW (a : ℕ) : Prop :=
  (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    UnramAt (E := E) v →
    ((LW v Λ a).relIndex (smulSub (dV v)⁻¹ (LW v Λ a)) : ℝ) = absV v (dV v) ^ (-(2 * ((n : ℝ) * a)))

theorem sdVolW_of_top (a : ℕ) (hC : CondV σ J ψ v) (hT : TopW v Λ a) (hD : DualW σ J ψ v Λ a)
    (hI : IdxW v Λ a) : SdVolW σ J ψ v Λ a := by
  intro hS hL hSD hU hμ
  have hd0 := dV_ne_zero v
  have hμsd : SdW F E σ n J (Fv F v) (psiV F ψ v) a (dX σ J ψ v a) := by
    simp only [dX, dif_pos hμ]
    exact hμ.choose_spec
  have := hμsd.1
  set μ := dX σ J ψ v a with hμdef
  set L := LW v Λ a with hLdef
  set L' := smulSub (dV v)⁻¹ L with hL'def
  obtain ⟨hLc, hLo⟩ := hT hL
  rw [← coe_LW] at hLc hLo
  have hL'c : IsCompact (L' : Set (TupV (E := E) v n a)) := isCompact_smulSub _ L hLc
  have hL'o : IsOpen (L' : Set (TupV (E := E) v n a)) := isOpen_smulSub _ (inv_ne_zero hd0) L hLo
  have hχ : ∀ x t y : TupV (E := E) v n a, psiV F ψ v (BR (Fv F v) σ J (t + x) y) =
      psiV F ψ v (BR (Fv F v) σ J t y) * psiV F ψ v (BR (Fv F v) σ J x y) := by
    intro x t y
    rw [BR_add, psiV_add]
  have h0 : ∀ y : TupV (E := E) v n a, psiV F ψ v (BR (Fv F v) σ J y 0) = 1 := by
    intro y
    have e := SdDualW.BR_smul_right v σ J 0 y y
    rw [zero_smul, zero_mul] at e
    rw [e, psiV_zero]
  have hA : ann (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y)) (L : Set (TupV (E := E) v n a)) = L' := by
    rw [Sd.ann_eq_cond v (psiV F ψ v) (dV v) (BR (Fv F v) σ J) _ (hC hS)]
    · exact hD hS hL hSD hU
    · intro s hs x hx
      exact ⟨s • x, smul_mem_LW v Λ hs hx, fun y => SdDualW.BR_smul_left v σ J s x y⟩
  have hle : L ≤ L' := by
    intro X hX
    rw [hL'def, mem_smulSub]
    refine ⟨dV v • X, smul_mem_LW v Λ (dV_int v) hX, ?_⟩
    rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have hN1 := hI hL hU
  have hNz : L.relIndex L' ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hN1
    have := Real.rpow_pos_of_pos (absV_dV_pos v) (-(2 * ((n : ℝ) * a)))
    linarith
  have key := Sd.vol_sq_mul_index hμsd hχ h0 L L' hLc hLo hL'c hL'o hA hle hNz
  rw [hN1] at key
  have hp := absV_dV_pos v
  have e1 : absV v (dV v) ^ (-(2 * ((n : ℝ) * a))) = (absV v (dV v) ^ (2 * ((n : ℝ) * a)))⁻¹ :=
    Real.rpow_neg hp.le _
  have e2 : (absV v (dV v) ^ ((n : ℝ) * a)) ^ 2 = absV v (dV v) ^ (2 * ((n : ℝ) * a)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
    ring_nf
  have hA2 : 0 < absV v (dV v) ^ (2 * ((n : ℝ) * a)) := Real.rpow_pos_of_pos hp _
  rw [e1] at key
  have e3 : μ.real (L : Set (TupV (E := E) v n a)) ^ 2 = (absV v (dV v) ^ ((n : ℝ) * a)) ^ 2 := by
    rw [e2]
    field_simp at key
    rw [key, mul_assoc]
  have hvol := (pow_left_inj₀ measureReal_nonneg (Real.rpow_pos_of_pos hp _).le two_ne_zero).1 e3
  rw [← coe_LW, ← ENNReal.ofReal_toReal hLc.measure_lt_top.ne, ← measureReal_def, hvol]

end Steps

end PI.OmLocU
end
end

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.VolStabSW
  PI.VolStabSW.PositiveNearLattice PI.VolStabSW.SdDualW
open scoped TensorProduct

section Top

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def oevS : AddSubgroup (Fv F v ⊗[F] E) :=
  (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).toAddSubgroup

theorem coe_oevS : (oevS (E := E) v : Set (Fv F v ⊗[F] E)) = OEv (E := E) v := rfl

theorem inclR_mem_oev (x : 𝓞 E) : inclR (F := F) (Fv F v) (x : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨x, Set.mem_univ _, rfl⟩

theorem exists_int_basis : ∃ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ k, IsIntegral ℤ (b k) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  classical
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image (Module.finBasis F E))
  have hyF : IsUnit ((y : F)) := by
    rw [isUnit_iff_ne_zero]
    exact_mod_cast hy
  refine ⟨_, (Module.finBasis F E).isUnitSMul (fun _ => hyF), fun k => ?_⟩
  rw [Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]
  exact hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))

theorem latA_le_oevS [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (hb : ∀ k, IsIntegral ℤ (b k)) : latA v b ≤ oevS (E := E) v := by
  intro z hz
  have hz' : ∀ k, crd b (Fv F v) z k ∈ v.adicCompletionIntegers F := hz
  rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply]
  have hm : inclR (F := F) (Fv F v) (((⟨b k, hb k⟩ : 𝓞 E)) : E) ∈ OEv (E := E) v :=
    inclR_mem_oev v (⟨b k, hb k⟩ : 𝓞 E)
  exact Submodule.smul_mem _ (⟨_, hz' k⟩ : v.adicCompletionIntegers F) hm

theorem isOpen_oev : IsOpen (OEv (E := E) v) := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨d, b, hb⟩ := exists_int_basis (F := F) (E := E)
  rw [← coe_oevS]
  exact AddSubgroup.isOpen_mono (latA_le_oevS v b hb) (isOpen_latA v b)

theorem isCompact_oev : IsCompact (OEv (E := E) v) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  set g : Fin m → Fv F v ⊗[F] E := fun i => inclR (F := F) (Fv F v) ((s i : 𝓞 E) : E) with hg
  have e : OEv (E := E) v = (fun c : Fin m → Fv F v => ∑ i, c i • g i) ''
      Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext z
    constructor
    · intro hz
      have h1 : z ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range g) := by
        refine (Submodule.span_le.2 ?_) hz
        rintro _ ⟨x, _, rfl⟩
        have hx : x ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; exact Submodule.mem_top
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact Submodule.subset_span ⟨i, rfl⟩
        | zero => simpa using Submodule.zero_mem _
        | add p q _ _ hp hq =>
          have e1 : inclR (F := F) (Fv F v) (((p + q : 𝓞 E)) : E) =
              inclR (F := F) (Fv F v) (p : E) + inclR (F := F) (Fv F v) (q : E) := by
            rw [← map_add (f := _)]
            rfl
          show inclR (F := F) (Fv F v) (((p + q : 𝓞 E)) : E) ∈ _
          rw [e1]
          exact Submodule.add_mem _ (hp trivial) (hq trivial)
        | smul r p _ hp =>
          have e1 : inclR (F := F) (Fv F v) (((r • p : 𝓞 E)) : E) =
              r • inclR (F := F) (Fv F v) (p : E) := by
            rw [show ((r • p : 𝓞 E) : E) = r • (p : E) from map_zsmul (algebraMap (𝓞 E) E) r p,
              map_zsmul]
          show inclR (F := F) (Fv F v) (((r • p : 𝓞 E)) : E) ∈ _
          rw [e1]
          exact zsmul_mem (hp trivial) r
      rw [Submodule.mem_span_range_iff_exists_fun] at h1
      obtain ⟨c, rfl⟩ := h1
      exact ⟨fun i => (c i : Fv F v), fun i _ => (c i).2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ (⟨c i, hc i (Set.mem_univ _)⟩ : v.adicCompletionIntegers F)
          (inclR_mem_oev v (s i))
  rw [e]
  exact (isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image
    (continuous_finsetSum _ fun i _ => by fun_prop)

variable (σ : E →ₐ[F] E)

theorem coe_HO (a : ℕ) : (HO σ v a : Set (HermR (Fv F v) σ a)) =
    Subtype.val ⁻¹' (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a => OEv (E := E) v) := by
  ext S
  constructor
  · intro h
    rw [SetLike.mem_coe, mem_HO] at h
    exact fun i _ j _ => h i j
  · intro h
    rw [SetLike.mem_coe, mem_HO]
    exact fun i j => h i (Set.mem_univ _) j (Set.mem_univ _)

theorem topH_holds (a : ℕ) : TopH σ v a := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a => OEv (E := E) v) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_oev v
  have := locallyCompact_Fv F v
  refine ⟨?_, ?_⟩
  · rw [coe_HO]
    exact (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal.isCompact_preimage hK
  · rw [coe_HO]
    exact (isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => isOpen_oev v).preimage continuous_subtype_val

end Top

end PI.OmLocU
end
end

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
  PI.VolStabSW PI.VolStabSW.PositiveNearLattice PI.VolStabSW.SdDualW
open scoped TensorProduct

section TopWs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem sdc_exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ y : ℤ, y ≠ 0 ∧ y • x ∈ L := by
  classical
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  obtain ⟨m, f, g, rfl⟩ := Submodule.mem_span_set'.1 hx
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ (y • f i) := hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  convert L.smul_mem (⟨y • f i, hi⟩ : 𝓞 E) (g i).2 using 1
  rw [← smul_assoc]
  rfl

theorem exists_int_smul_mem_all (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) {ι : Type} [Fintype ι] (w : ι → Fin n → E) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ j, y • w j ∈ L := by
  classical
  choose y hy hw using fun j => sdc_exists_int_smul_mem L hL (w j)
  refine ⟨∏ j, y j, Finset.prod_ne_zero_iff.2 fun j _ => hy j, fun j => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_smul]
  exact zsmul_mem (hw j) _

theorem ratV_single (i : Fin n) (e : E) :
    ratV (F := F) (Fv F v) (Pi.single i e : Fin n → E) =
      (Pi.single i (inclR (F := F) (Fv F v) e) : Fin n → Fv F v ⊗[F] E) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [ratV]
  · simp [ratV, Pi.single_eq_of_ne h]

theorem ratV_mem_latLoc {Λ : Set (Fin n → E)} {x : Fin n → E} (hx : x ∈ Λ) :
    ratV (F := F) (Fv F v) x ∈ latLoc (E := E) v Λ :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem sdc_isOpen_latLoc (Λ : Set (Fin n → E))
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    IsOpen (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨L, hLat, rfl⟩ := hL
  obtain ⟨d, b, hb⟩ := exists_int_basis (F := F) (E := E)
  letI : Submodule.IsFullLattice E L := hLat
  obtain ⟨N, hN, hNw⟩ := exists_int_smul_mem_all L
    (Submodule.IsFullLattice.span_eq_top (A := E) (M := L))
    (fun p : Fin n × Fin d => (Pi.single p.1 (b p.2) : Fin n → E))
  have hNF : IsUnit ((N : F)) := by
    rw [isUnit_iff_ne_zero]
    exact_mod_cast hN
  set b2 := b.isUnitSMul (fun _ => hNF) with hb2
  have hb2L : ∀ i k, (Pi.single i (b2 k) : Fin n → E) ∈ L := by
    intro i k
    have e : (Pi.single i (b2 k) : Fin n → E) = N • (Pi.single i (b k) : Fin n → E) := by
      rw [hb2, Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]
      funext j
      by_cases h : j = i
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]
    rw [e]
    exact hNw (i, k)
  let H : AddSubgroup (Fin n → Fv F v ⊗[F] E) := AddSubgroup.pi Set.univ (fun _ => latA v b2)
  have hHo : IsOpen (H : Set (Fin n → Fv F v ⊗[F] E)) := by
    rw [AddSubgroup.coe_pi]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_latA v b2
  have hle : H ≤ (latLoc (E := E) v (L : Set (Fin n → E))).toAddSubgroup := by
    intro X hX
    rw [AddSubgroup.mem_pi] at hX
    rw [Submodule.mem_toAddSubgroup, ← Finset.univ_sum_single X]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hXi : ∀ k, crd b2 (Fv F v) (X i) k ∈ v.adicCompletionIntegers F := hX i (Set.mem_univ _)
    have e : Pi.single i (X i) = ∑ k, crd b2 (Fv F v) (X i) k •
        ratV (F := F) (Fv F v) (Pi.single i (b2 k) : Fin n → E) := by
      have hr := (Algebra.TensorProduct.basis (Fv F v) b2).sum_repr (X i)
      simp only [Algebra.TensorProduct.basis_apply] at hr
      funext j
      by_cases h : j = i
      · subst h
        simp only [ratV_single, Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same]
        conv_lhs => rw [← hr]
        rfl
      · simp [ratV_single, Finset.sum_apply, Pi.single_eq_of_ne h]
    rw [e]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ (⟨_, hXi k⟩ : v.adicCompletionIntegers F) (ratV_mem_latLoc v (hb2L i k))
  exact AddSubgroup.isOpen_mono hle hHo

theorem sdc_isCompact_latLoc (Λ : Set (Fin n → E))
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    IsCompact (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨L, hLat, rfl⟩ := hL
  have : Module.Finite (𝓞 E) L := Submodule.IsLattice.finite (A := E) L
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := L)
  set g : Fin m → Fin n → Fv F v ⊗[F] E := fun i => ratV (F := F) (Fv F v) ((s i : L) : Fin n → E)
    with hg
  have hadd : ∀ p q : Fin n → E, ratV (F := F) (Fv F v) (p + q) =
      ratV (F := F) (Fv F v) p + ratV (F := F) (Fv F v) q := by
    intro p q
    funext j
    simp [ratV]
  have hzs : ∀ (r : ℤ) (p : Fin n → E), ratV (F := F) (Fv F v) (r • p) = r • ratV (F := F) (Fv F v) p := by
    intro r p
    funext j
    simp [ratV]
  have e : (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) =
      (fun c : Fin m → Fv F v => ∑ i, c i • g i) ''
        Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext z
    constructor
    · intro hz
      have h1 : z ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range g) := by
        refine (Submodule.span_le.2 ?_) hz
        rintro _ ⟨x, hx, rfl⟩
        have hx' : (⟨x, hx⟩ : L) ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; exact Submodule.mem_top
        have key : ∀ y : L, y ∈ Submodule.span ℤ (Set.range s) →
            ratV (F := F) (Fv F v) (y : Fin n → E) ∈
              Submodule.span (v.adicCompletionIntegers F) (Set.range g) := by
          intro y hy
          induction hy using Submodule.span_induction with
          | mem y hy =>
            obtain ⟨i, rfl⟩ := hy
            exact Submodule.subset_span ⟨i, rfl⟩
          | zero =>
            have : ratV (F := F) (Fv F v) (0 : Fin n → E) = 0 := by
              funext j
              simp [ratV]
            simpa [this] using Submodule.zero_mem _
          | add p q _ _ hp hq =>
            rw [Submodule.coe_add, hadd]
            exact Submodule.add_mem _ hp hq
          | smul r p _ hp =>
            rw [show ((r • p : L) : Fin n → E) = r • (p : Fin n → E) from rfl, hzs]
            exact zsmul_mem hp r
        exact key _ hx'
      rw [Submodule.mem_span_range_iff_exists_fun] at h1
      obtain ⟨c, rfl⟩ := h1
      exact ⟨fun i => (c i : Fv F v), fun i _ => (c i).2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ (⟨c i, hc i (Set.mem_univ _)⟩ : v.adicCompletionIntegers F)
          (ratV_mem_latLoc v (s i).2)
  rw [e]
  exact (isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image
    (continuous_finsetSum _ fun i _ => by fun_prop)

theorem topW_holds (Λ : Set (Fin n → E)) (a : ℕ)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) : TopW v Λ a := by
  intro hL
  have e : LamT (E := E) v Λ a =
      Set.pi Set.univ (fun _ : Fin a => (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E))) := by
    ext X
    simp [LamT, Set.mem_pi]
  rw [e]
  exact ⟨isCompact_univ_pi fun _ => sdc_isCompact_latLoc v Λ hL,
    isOpen_set_pi Set.finite_univ fun _ _ => sdc_isOpen_latLoc v Λ hFull⟩

end TopWs

end PI.OmLocU
end
end

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.VolStabSW

section Idx

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  {W : Type} [AddCommGroup W] [Module (Fv F v) W]

theorem sdc_unifEx_holds : UnifEx v := ⟨unifV v, by rw [IsUnif, unifV_val]; rfl⟩

theorem smulSub_smulSub (s t : Fv F v) (P : AddSubgroup W) :
    smulSub s (smulSub t P) = smulSub (s * t) P := by
  ext z
  simp only [mem_smulSub]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, by rw [smul_smul]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨t • p, ⟨p, hp, rfl⟩, by rw [smul_smul]⟩

theorem smulSub_one (P : AddSubgroup W) : smulSub (1 : Fv F v) P = P := by
  ext z
  simp [mem_smulSub]

theorem relIndex_smulSub {t : Fv F v} (ht : t ≠ 0) (H G : AddSubgroup W) :
    (smulSub t H).relIndex (smulSub t G) = H.relIndex G :=
  AddSubgroup.relIndex_map_map_of_injective H G (smul_right_injective W ht)

theorem smulSub_le {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F) (P : AddSubgroup W)
    (hP : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ P, s • x ∈ P) : smulSub s P ≤ P := by
  intro z hz
  rw [mem_smulSub] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  exact hP s hs p hp

theorem smulSub_unit {u : Fv F v} (hu : u ∈ v.adicCompletionIntegers F)
    (hu' : u⁻¹ ∈ v.adicCompletionIntegers F) (hu0 : u ≠ 0) (P : AddSubgroup W)
    (hP : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ P, s • x ∈ P) : smulSub u P = P := by
  apply le_antisymm (smulSub_le v hu P hP)
  intro z hz
  rw [mem_smulSub]
  exact ⟨u⁻¹ • z, hP _ hu' z hz, by rw [smul_smul, mul_inv_cancel₀ hu0, one_smul]⟩

theorem relIndex_pow {ϖ : Fv F v} (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ v.adicCompletionIntegers F)
    (P : AddSubgroup W) (hP : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ P, s • x ∈ P) (k : ℕ) :
    (smulSub (ϖ ^ k) P).relIndex P = ((smulSub ϖ P).relIndex P) ^ k := by
  induction k with
  | zero => simp [smulSub_one]
  | succ k ih =>
    have e : smulSub (ϖ ^ (k + 1)) P = smulSub (ϖ ^ k) (smulSub ϖ P) := by
      rw [smulSub_smulSub, pow_succ]
    have h2 : smulSub (ϖ ^ k) P ≤ P := smulSub_le v (pow_mem hϖ k) P hP
    have h1 : smulSub (ϖ ^ k) (smulSub ϖ P) ≤ smulSub (ϖ ^ k) P := by
      intro z hz
      rw [mem_smulSub] at hz ⊢
      obtain ⟨p, hp, rfl⟩ := hz
      exact ⟨p, smulSub_le v hϖ P hP hp, rfl⟩
    rw [e, ← AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2, relIndex_smulSub v (pow_ne_zero k hϖ0), ih]
    ring

theorem exists_unit_pow {ϖ : Fv F v} (hϖ : IsUnif v ϖ) {d : Fv F v} (hd0 : d ≠ 0)
    (hd : d ∈ v.adicCompletionIntegers F) :
    ∃ k : ℕ, ∃ u : Fv F v, u ∈ v.adicCompletionIntegers F ∧ u⁻¹ ∈ v.adicCompletionIntegers F ∧
      u ≠ 0 ∧ d = ϖ ^ k * u ∧ absV v d = qv v ^ (-(k : ℤ)) := by
  have hϖ0 := unif_ne_zero v hϖ
  have hv : Valued.v d ≠ 0 := (Valuation.ne_zero_iff _).2 hd0
  set m : ℤ := Multiplicative.toAdd (WithZero.unzero hv) with hmdef
  have hvm : Valued.v d = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    simp [m]
  have hm : m ≤ 0 := by
    have h1 : Valued.v d ≤ 1 := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hd
      exact hd
    rw [hvm] at h1
    have h2 : (Multiplicative.ofAdd m : Multiplicative ℤ) ≤ 1 := by exact_mod_cast h1
    rw [← ofAdd_zero] at h2
    exact Multiplicative.ofAdd_le.1 h2
  have hk : ((m.natAbs : ℕ) : ℤ) = -m := Int.ofNat_natAbs_of_nonpos hm
  have hvk : Valued.v (ϖ ^ m.natAbs) = Valued.v d := by
    rw [map_pow, hϖ, hvm, ← WithZero.coe_pow, ← ofAdd_nsmul]
    congr 2
    rw [nsmul_eq_mul, hk]
    ring
  have hϖk : ϖ ^ m.natAbs ≠ 0 := pow_ne_zero _ hϖ0
  have hu1 : Valued.v ((ϖ ^ m.natAbs)⁻¹ * d) = 1 := by
    rw [map_mul, map_inv₀, hvk, inv_mul_cancel₀ hv]
  refine ⟨m.natAbs, (ϖ ^ m.natAbs)⁻¹ * d, ?_, ?_, ?_, ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu1]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu1, inv_one]
  · exact mul_ne_zero (inv_ne_zero hϖk) hd0
  · rw [← mul_assoc, mul_inv_cancel₀ hϖk, one_mul]
  · unfold absV
    rw [dite_eq_right hv]
    unfold qv
    congr 1
    rw [hk]
    simp [m]

end Idx

section Steps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Set (Fin n → E))

def IdxPiW (a : ℕ) : Prop :=
  (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
      ((smulSub ϖ (LW v Λ a)).relIndex (LW v Λ a) : ℝ) = qv v ^ (2 * n * a)

def IdxPiH (a : ℕ) : Prop :=
  UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ((smulSub ϖ (HO σ v a)).relIndex (HO σ v a) : ℝ) = qv v ^ (a ^ 2)

theorem relIndex_dV {W : Type} [AddCommGroup W] [Module (Fv F v) W] (P : AddSubgroup W)
    (hP : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ P, s • x ∈ P) (N : ℕ) (e : ℝ)
    (hN : ∀ ϖ : Fv F v, IsUnif v ϖ → ((smulSub ϖ P).relIndex P : ℝ) = qv v ^ N)
    (he : e = -(N : ℝ)) :
    (P.relIndex (smulSub (dV v)⁻¹ P) : ℝ) = absV v (dV v) ^ e := by
  obtain ⟨ϖ, hϖ⟩ := sdc_unifEx_holds v
  have hd0 := dV_ne_zero v
  obtain ⟨k, u, hu, hu', hu0, hd, habs⟩ := exists_unit_pow v hϖ hd0 (dV_int v)
  have e1 : P.relIndex (smulSub (dV v)⁻¹ P) = (smulSub ϖ P).relIndex P ^ k := by
    rw [← relIndex_smulSub v hd0, smulSub_smulSub, mul_inv_cancel₀ hd0, smulSub_one, hd,
      ← smulSub_smulSub, smulSub_unit v hu hu' hu0 P hP,
      relIndex_pow v (unif_ne_zero v hϖ) (unif_int v hϖ) P hP]
  rw [e1, Nat.cast_pow, hN ϖ hϖ, habs, he]
  have hq := qv_pos v
  rw [← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← pow_mul, ← Real.rpow_natCast]
  congr 1
  push_cast
  ring

theorem idxW_of (a : ℕ) (h : IdxPiW v Λ a) : IdxW v Λ a := by
  intro hL hU
  exact relIndex_dV v (LW v Λ a) (fun s hs x hx => smul_mem_LW v Λ hs hx) (2 * n * a) _
    (fun ϖ hϖ => h hL hU ϖ hϖ) (by push_cast; ring)

theorem idxHO_of (a : ℕ) (h : IdxPiH σ v a) : IdxHO σ v a := by
  intro hU ϖ hϖ
  refine ⟨relIndex_dV v (HO σ v a) (fun s hs x hx => smul_mem_HO σ v hs hx) (a ^ 2) _
    (fun ϖ hϖ => h hU ϖ hϖ) (by push_cast; ring), h hU ϖ hϖ⟩

end Steps

end PI.OmLocU
