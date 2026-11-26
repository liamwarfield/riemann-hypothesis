module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SquareIntegrableInnerProduct
noncomputable section

open Finset Matrix MeasureTheory
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

abbrev L2 (ε : Fin n → Bool) : Type := Lp ℂ 2 (Formalism.REAL.muG ε)

def rregG (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) : L2 ε →L[ℂ] L2 ε :=
  if hm : MeasurePreserving (fun x : Formalism.REAL.UJ ε => x * y) (Formalism.REAL.muG ε) (Formalism.REAL.muG ε) then
    (Lp.compMeasurePreservingₗᵢ ℂ (fun x : Formalism.REAL.UJ ε => x * y) hm).toContinuousLinearMap
  else 1

def rreg (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : L2 ε →L[ℂ] L2 ε :=
  if h : ∃ y : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y = g then rregG ε h.choose else 1

def toL2 (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) : L2 ε :=
  if h : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) then h.toLp _ else 0

theorem signature_matrix_sq (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem exists_unitary_preimage (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ y : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y = g := by
  have hJ := signature_matrix_sq ε
  have h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have hl : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc gᴴ (Formalism.REAL.Jm ε) g, h, hJ]
  have hr : g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1 := by
    first
    | exact mul_eq_one_comm.mp hl
    | (letI := Matrix.invertibleOfLeftInverse g _ hl; exact mul_invOf_self g)
  exact ⟨⟨⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, hr, hl⟩, h⟩, rfl⟩

theorem unitary_matrix_injective (ε : Fin n → Bool) {x y : Formalism.REAL.UJ ε}
    (h : Formalism.MainNotions.S.umat x = Formalism.MainNotions.S.umat y) : x = y := Subtype.ext (Units.ext h)

theorem unitary_matrix_mem_set (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.umat y ∈ UJset ε := y.2

theorem continuous_unitary_matrix (ε : Fin n → Bool) :
    Continuous (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y) := Units.continuous_val.comp continuous_subtype_val

theorem rightRegular_unitary_eq (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) :
    rreg ε (Formalism.MainNotions.S.umat y) = rregG ε y := by
  have h : ∃ y' : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y' = Formalism.MainNotions.S.umat y := ⟨y, rfl⟩
  unfold rreg
  rw [dif_pos h, unitary_matrix_injective ε h.choose_spec]

theorem rightRegularGroup_eq_comp (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) (f : L2 ε) :
    rregG ε y f = Lp.compMeasurePreserving (fun x : Formalism.REAL.UJ ε => x * y) (measurePreserving_mul_right ε y) f := by
  unfold rregG
  rw [dif_pos (measurePreserving_mul_right ε y)]
  rfl

theorem toL2_eq_memLp_toLp (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    toL2 ε F = hF.toLp _ := by
  unfold toL2
  exact dif_pos hF

theorem toL2_eq_zero_of_not_memLp (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : ¬ MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    toL2 ε F = 0 := by
  unfold toL2
  exact dif_neg hF

theorem rreg_umat_ae (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) (f : L2 ε) :
    (rreg ε (Formalism.MainNotions.S.umat y) f : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε] fun x => f (x * y) := by
  rw [rightRegular_unitary_eq, rightRegularGroup_eq_comp]
  exact Lp.coeFn_compMeasurePreserving _ _

theorem rightRegular_toL2 (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : rreg ε g (toL2 ε F) = toL2 ε (fun x => F (x * g)) := by
  obtain ⟨y, rfl⟩ := exists_unitary_preimage ε hg
  by_cases hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)
  · have hFy : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g * Formalism.MainNotions.S.umat y)) 2
        (Formalism.REAL.muG ε) := hF.comp_measurePreserving (measurePreserving_mul_right ε y)
    rw [toL2_eq_memLp_toLp ε hF, toL2_eq_memLp_toLp ε (F := fun x => F (x * Formalism.MainNotions.S.umat y)) hFy,
      rightRegular_unitary_eq, rightRegularGroup_eq_comp]
    refine Lp.ext ?_
    refine (Lp.coeFn_compMeasurePreserving _ _).trans ?_
    refine (hF.coeFn_toLp.comp_tendsto
      (measurePreserving_mul_right ε y).quasiMeasurePreserving.tendsto_ae).trans ?_
    exact hFy.coeFn_toLp.symm
  · have hFy : ¬ MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g * Formalism.MainNotions.S.umat y)) 2
        (Formalism.REAL.muG ε) := by
      intro h
      apply hF
      have h2 := h.comp_measurePreserving (measurePreserving_mul_right ε y⁻¹)
      have e : ((fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g * Formalism.MainNotions.S.umat y)) ∘
          fun x => x * y⁻¹) = fun g => F (Formalism.MainNotions.S.umat g) := by
        funext g
        show F (Formalism.MainNotions.S.umat (g * y⁻¹ * y)) = F (Formalism.MainNotions.S.umat g)
        rw [inv_mul_cancel_right]
      rwa [e] at h2
    rw [toL2_eq_zero_of_not_memLp ε hF, toL2_eq_zero_of_not_memLp ε (F := fun x => F (x * Formalism.MainNotions.S.umat y)) hFy,
      map_zero]

theorem toL2_add_smooth (ε : Fin n → Bool) {F G : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hG : MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    toL2 ε (F + G) = toL2 ε F + toL2 ε G := by
  have hFG : MemLp (fun g : Formalism.REAL.UJ ε => (F + G) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
    hF.add hG
  rw [toL2_eq_memLp_toLp ε hFG, toL2_eq_memLp_toLp ε hF, toL2_eq_memLp_toLp ε hG]
  exact MemLp.toLp_add hF hG

theorem toL2_smul_smooth (ε : Fin n → Bool) (c : ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    toL2 ε (c • F) = c • toL2 ε F := by
  by_cases hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)
  · have hcF : MemLp (fun g : Formalism.REAL.UJ ε => (c • F) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
      hF.const_smul c
    rw [toL2_eq_memLp_toLp ε hcF, toL2_eq_memLp_toLp ε hF]
    exact MemLp.toLp_const_smul c hF
  · by_cases hc : c = 0
    · subst hc
      rw [zero_smul, zero_smul]
      have h0 : MemLp (fun g : Formalism.REAL.UJ ε => (0 : Matrix (Fin n) (Fin n) ℂ → ℂ) (Formalism.MainNotions.S.umat g)) 2
          (Formalism.REAL.muG ε) := MemLp.zero
      rw [toL2_eq_memLp_toLp ε h0]
      exact Lp.ext (h0.coeFn_toLp.trans (Lp.coeFn_zero ..).symm)
    · have hcF : ¬ MemLp (fun g : Formalism.REAL.UJ ε => (c • F) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
        intro h
        apply hF
        have h2 := h.const_smul c⁻¹
        have e : (c⁻¹ • fun g : Formalism.REAL.UJ ε => (c • F) (Formalism.MainNotions.S.umat g)) =
            fun g => F (Formalism.MainNotions.S.umat g) := by
          funext g
          simp only [Pi.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ hc]
        rwa [e] at h2
      rw [toL2_eq_zero_of_not_memLp ε hcF, toL2_eq_zero_of_not_memLp ε hF, smul_zero]

theorem inner_toL2_eq_theta_pairing (ε : Fin n → Bool) {F G : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hG : MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    inner ℂ (toL2 ε F) (toL2 ε G) =
      ∫ g : Formalism.REAL.UJ ε, starRingEnd ℂ (F (Formalism.MainNotions.S.umat g)) * G (Formalism.MainNotions.S.umat g) ∂(Formalism.REAL.muG ε) := by
  rw [toL2_eq_memLp_toLp ε hF, toL2_eq_memLp_toLp ε hG, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with g h1 h2
  simp only [h1, h2, RCLike.inner_apply]
  exact mul_comm _ _

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem rregRep_umat_inj (ε : Fin n → Bool) {x y : Formalism.REAL.UJ ε}
    (h : Formalism.MainNotions.S.umat x = Formalism.MainNotions.S.umat y) : x = y := Subtype.ext (Units.ext h)

theorem rregRep_rreg_umat (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) :
    rreg ε (Formalism.MainNotions.S.umat y) = rregG ε y := by
  have h : ∃ y' : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y' = Formalism.MainNotions.S.umat y := ⟨y, rfl⟩
  rw [rreg, dite_eq_left h]
  exact congrArg (rregG ε) (rregRep_umat_inj ε h.choose_spec)

theorem rregRep_rregG_apply (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) (f : L2 ε) :
    rregG ε y f = Lp.compMeasurePreserving (fun x : Formalism.REAL.UJ ε => x * y)
      (measurePreserving_mul_right ε y) f := by
  rw [rregG, dite_eq_left (measurePreserving_mul_right ε y)]
  rfl

private theorem Jm_mul_selfDiscreteSeriesExistence (ε : Fin n → Bool) :
    Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases h : ε i <;> simp [h]
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

private theorem Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  rw [Matrix.mul_assoc] at hg'
  simp only [Matrix.mul_assoc]
  rw [hg', Jm_mul_selfDiscreteSeriesExistence]

private theorem mul_Jm_conjTranspose_Jm_eq_one_of_mem_UJset (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1 := by
  have hl := Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset ε hg
  first
  | exact mul_eq_one_comm.mp hl
  | (rw [← Matrix.inv_eq_left_inv hl]
     exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse hl))

theorem rregRep_range (ε : Fin n → Bool) :
    Set.range (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) = UJset ε := by
  ext g
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hg
    exact ⟨⟨⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, mul_Jm_conjTranspose_Jm_eq_one_of_mem_UJset ε hg,
      Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset ε hg⟩, hg⟩, rfl⟩

theorem rregRep_mem (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ y : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y = g := by
  have h2 : g ∈ Set.range (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y) := by
    rw [rregRep_range ε]
    exact hg
  obtain ⟨y, hy⟩ := h2
  exact ⟨y, hy⟩

theorem rregRep_one (ε : Fin n → Bool) : rreg ε 1 = 1 := by
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) := rfl
  rw [h1, rregRep_rreg_umat]
  ext1 f
  rw [rregRep_rregG_apply, ContinuousLinearMap.one_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right ε 1)] with x hx
  rw [hx]
  simp

theorem rregRep_mul (ε : Fin n → Bool) (a b : Formalism.REAL.UJ ε) :
    rregG ε (a * b) = (rregG ε a).comp (rregG ε b) := by
  ext1 f
  rw [ContinuousLinearMap.comp_apply, rregRep_rregG_apply, rregRep_rregG_apply,
    rregRep_rregG_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right ε (a * b)),
    Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (fun x : Formalism.REAL.UJ ε => x * b)
        (measurePreserving_mul_right ε b) f) (measurePreserving_mul_right ε a),
    (measurePreserving_mul_right ε a).quasiMeasurePreserving.ae_eq
      (Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right ε b))] with x h1 h2 h3
  simp only [Function.comp_apply] at h1 h2 h3 ⊢
  rw [h1, h2, h3, mul_assoc]

theorem rregRep_cont (ε : Fin n → Bool) (v : L2 ε) :
    Continuous (fun y : Formalism.REAL.UJ ε => rregG ε y v) := by
  haveI : SMulInvariantMeasure (Formalism.REAL.UJ ε)ᵐᵒᵖ (Formalism.REAL.UJ ε) (Formalism.REAL.muG ε) := by
    refine ⟨fun c s hs => ?_⟩
    first
    | exact (measurePreserving_mul_right ε c.unop).measure_preimage hs.nullMeasurableSet
    | exact (measurePreserving_mul_right ε c.unop).measure_preimage hs
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by first | simp | exact ENNReal.ofNat_ne_top⟩
  have he : (fun y : Formalism.REAL.UJ ε => rregG ε y v) =
      fun y => (DomMulAct.mk (MulOpposite.op y)) • v := by
    funext y
    rw [rregRep_rregG_apply]
    rfl
  rw [he]
  have hm : Continuous (fun y : Formalism.REAL.UJ ε => DomMulAct.mk (MulOpposite.op y)) := by
    first
    | exact DomMulAct.continuous_mk.comp MulOpposite.continuous_op
    | exact DomMulAct.mkHomeomorph.continuous.comp MulOpposite.continuous_op
    | fun_prop
  haveI : OpensMeasurableSpace (Formalism.REAL.UJ ε)ᵐᵒᵖ :=
    ⟨MeasurableSpace.generateFrom_le fun s hs =>
      (IsOpen.preimage MulOpposite.continuous_op hs).measurableSet⟩
  exact hm.smul continuous_const

theorem rreg_isURepOn (ε : Fin n → Bool) : IsURepOn (UJset ε) (rreg ε) := by
  unfold IsURepOn
  refine ⟨⟨rregRep_one ε, ?_⟩, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨ya, rfl⟩ := rregRep_mem ε ha
    obtain ⟨yb, rfl⟩ := rregRep_mem ε hb
    have hab : Formalism.MainNotions.S.umat ya * Formalism.MainNotions.S.umat yb = Formalism.MainNotions.S.umat (ya * yb) := rfl
    rw [hab, rregRep_rreg_umat, rregRep_rreg_umat, rregRep_rreg_umat, rregRep_mul]
  · intro g hg v
    obtain ⟨y, rfl⟩ := rregRep_mem ε hg
    rw [rregRep_rreg_umat, rregRep_rregG_apply]
    exact Lp.norm_compMeasurePreserving v _
  · intro v
    obtain ⟨φ, hφc, hφ⟩ : ∃ φ : UJset ε → Formalism.REAL.UJ ε, Continuous φ ∧
        ∀ g : UJset ε, Formalism.MainNotions.S.umat (φ g) = g :=
      ⟨fun g => ⟨⟨(g : Matrix (Fin n) (Fin n) ℂ),
          Formalism.REAL.Jm ε * (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε,
          mul_Jm_conjTranspose_Jm_eq_one_of_mem_UJset ε g.2, Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset ε g.2⟩, g.2⟩,
        by
          apply Continuous.subtype_mk
          rw [Units.continuous_iff]
          constructor
          · exact continuous_subtype_val
          · exact (continuous_const.mul continuous_subtype_val.matrix_conjTranspose).mul
              continuous_const,
        fun g => rfl⟩
    have he : ∀ g : UJset ε, rreg ε (g : Matrix (Fin n) (Fin n) ℂ) v = rregG ε (φ g) v := by
      intro g
      rw [← hφ g, rregRep_rreg_umat]
    rw [continuousOn_iff_continuous_restrict]
    convert (rregRep_cont ε v).comp hφc using 1
    funext g
    exact he g

end ReciprocityTheory.ChartRestriction.DS
