module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ClosureK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiMExpFormula
public import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
public import Formalism.HermitianCurvature.StatementB

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeExpK
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem actM_mem_of_isKStableSub_inK {S : Submodule ℂ D} (hS : IsKStableSub ε E S)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {x : D} (hx : x ∈ S) :
    actM E Z x ∈ S := by
  have hZ0 : ∀ a b, ε a ≠ ε b → Z a b = 0 := by
    intro a b hab
    have h := congrFun (congrFun hZ.2 a) b
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have hne : (if ε b = true then (1 : ℂ) else -1) - (if ε a = true then 1 else -1) ≠ 0 := by
      cases ha : ε a <;> cases hb : ε b <;> simp_all <;> norm_num
    have h2 : Z a b * ((if ε b = true then (1 : ℂ) else -1) - (if ε a = true then 1 else -1)) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp h2).resolve_right hne
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  by_cases hab : ε a = ε b
  · exact S.smul_mem _ (hS a b hab x hx)
  · rw [hZ0 a b hab, zero_smul]
    exact S.zero_mem

theorem actM_pow_mem_of_isKStableSub_inK {S : Submodule ℂ D} (hS : IsKStableSub ε E S)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {x : D} (hx : x ∈ S) (m : ℕ) :
    ((actM E Z) ^ m) x ∈ S := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact actM_mem_of_isKStableSub_inK hS hZ ih

theorem exists_norm_actM_pow_le_of_isKStableSub {S : Submodule ℂ D} (hS : IsKStableSub ε E S)
    (hSf : FiniteDimensional ℂ S) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ m : ℕ, ‖((actM E Z) ^ m) x‖ ≤ C ^ m * ‖x‖ := by
  haveI : FiniteDimensional ℂ S := hSf
  let g : S →ₗ[ℂ] S := (actM E Z).restrict (fun x hx => actM_mem_of_isKStableSub_inK hS hZ hx)
  let gL : S →L[ℂ] S := LinearMap.toContinuousLinearMap g
  refine ⟨‖gL‖, norm_nonneg _, ?_⟩
  have key : ∀ y : S, ‖actM E Z (y : D)‖ ≤ ‖gL‖ * ‖y‖ := fun y => gL.le_opNorm y
  intro x hx m
  induction m with
  | zero => simp
  | succ m ih =>
    have hm := actM_pow_mem_of_isKStableSub_inK hS hZ hx m
    have h1 := key ⟨_, hm⟩
    rw [pow_succ', Module.End.mul_apply]
    calc ‖actM E Z (((actM E Z) ^ m) x)‖ ≤ ‖gL‖ * ‖((actM E Z) ^ m) x‖ := h1
      _ ≤ ‖gL‖ * (‖gL‖ ^ m * ‖x‖) := mul_le_mul_of_nonneg_left ih (norm_nonneg _)
      _ = ‖gL‖ ^ (m + 1) * ‖x‖ := by ring

theorem kStable_of_isKStableSub (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (S : Submodule ℂ D)
    (hS : FiniteDimensional ℂ S) (hk : IsKStableSub ε E S) :
    ∀ k ∈ Kset ε, ∀ v ∈ S, ∃ w ∈ S, (w : H) = σ k v := by
  intro g hg v hv
  obtain ⟨Z, hZ, rfl⟩ := exists_exp_eq_of_mem_Kset hg
  obtain ⟨C, hC0, hC⟩ := exists_norm_actM_pow_le_of_isKStableSub hk hS hZ
  have hs : Summable fun m : ℕ => (C ^ m * ‖v‖) * |(1 : ℝ) - 0| ^ m / (m.factorial : ℝ) := by
    simp only [sub_zero, abs_one, one_pow, mul_one]
    exact ((Real.summable_pow_div_factorial C).mul_right ‖v‖).congr fun m => by ring
  have h := hasSum_orbit_of_bound hσ hD hZ.1 v (fun m => C ^ m * ‖v‖) (fun m => hC v hv m) 0 1 hs
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1,
    ContinuousLinearMap.one_apply, Complex.ofReal_one, one_smul] at h
  haveI : FiniteDimensional ℂ S := hS
  have hT : IsClosed ((S.map D.subtype : Submodule ℂ H) : Set H) :=
    Submodule.closed_of_finiteDimensional _
  have hmem : σ (NormedSpace.exp Z) (v : H) ∈ S.map D.subtype := by
    refine hT.mem_of_tendsto h.tendsto_sum_nat (Filter.Eventually.of_forall fun N => ?_)
    exact Submodule.sum_mem _ fun m _ =>
      Submodule.smul_mem _ _ ⟨_, actM_pow_mem_of_isKStableSub_inK hk hZ hv m, rfl⟩
  obtain ⟨w, hwS, hw⟩ := hmem
  exact ⟨w, hwS, hw⟩

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsSmoothL2OfCasimirEigen
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def IsSmoothL2 (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  Formalism.REAL.SmoothOnG ε F ∧ ∀ w : List (Fin n × Fin n),
    MemLp (fun g : Formalism.REAL.UJ ε => Formalism.REAL.Eword ε w F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)

theorem eword_append_Eab (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (p : Fin n × Fin n) :
    ∀ w : List (Fin n × Fin n),
      Formalism.REAL.Eword ε w (Formalism.REAL.Eab ε p.1 p.2 F) = Formalism.REAL.Eword ε (w ++ [p]) F
  | [] => rfl
  | q :: w => by
      simp only [List.cons_append, Formalism.REAL.Eword]
      rw [eword_append_Eab ε F p w]

theorem IsSmoothL2.Eab {ε : Fin n → Bool} {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F)
    (a b : Fin n) : IsSmoothL2 ε (Formalism.REAL.Eab ε a b F) := by
  refine ⟨Formalism.REAL.smooth_lie_derivative a b hF.1, fun w => ?_⟩
  have h := eword_append_Eab ε F (a, b) w
  simp only at h
  rw [h]
  exact hF.2 _

theorem isSmoothL2_of_casimir_eigen (ε : Fin n → Bool) (W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)) (c : ℂ)
    (hW : FiniteDimensional ℂ W) (hsm : ∀ w ∈ W, Formalism.REAL.SmoothOnG ε w)
    (hK : ∀ w ∈ W, ∀ i j : Fin n, ε i = ε j → ∃ w' ∈ W, ∀ g, Formalism.REAL.inUJ ε g → Formalism.REAL.Eab ε i j w g = w' g)
    (hc : ∀ w ∈ W, ∀ g, Formalism.REAL.inUJ ε g → Formalism.REAL.CasF ε w g = c * w g)
    (hL2 : ∀ w ∈ W, MemLp (fun g : Formalism.REAL.UJ ε => w (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    ∀ w ∈ W, IsSmoothL2 ε w := by
  have hint : ∀ w ∈ W, Integrable (fun g : Formalism.REAL.UJ ε =>
      Real.exp (2 * (0:ℝ) * Formalism.REAL.hh (Formalism.REAL.toM g)) * ‖w (Formalism.REAL.toM g)‖ ^ 2) (Formalism.REAL.muG ε) := by
    intro w hw
    have := (hL2 w hw).integrable_norm_pow (by norm_num)
    simpa using this
  have key := r0bG n ε W c 0 hW le_rfl hsm hK hc hint
  intro f hf
  refine ⟨hsm f hf, fun w => ?_⟩
  obtain ⟨hs, hi, -⟩ := key w [] f f hf hf
  have hae : AEStronglyMeasurable (fun g : Formalism.REAL.UJ ε => Formalism.REAL.Eword ε w f (Formalism.MainNotions.S.umat g))
      (Formalism.REAL.muG ε) := (Formalism.REAL.continuous_smooth_on_group_eval hs).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hae]
  simpa using hi

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeWt
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def bwtDiag (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => (θ a : ℂ) * Complex.I

theorem bwtDiag_inG (ε : Fin n → Bool) (θ : Fin n → ℝ) : inG ε (bwtDiag θ) := by
  show (bwtDiag θ)ᴴ * Jm ε + Jm ε * bwtDiag θ = 0
  rw [bwtDiag, Jm, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, ← Matrix.diagonal_zero]
  congr 1
  funext i
  by_cases hε : ε i = true <;> simp [hε, Complex.conj_I] <;> ring_nf

theorem bwt_exp (θ : Fin n → ℝ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • bwtDiag θ) =
      Matrix.diagonal (fun a => Complex.exp (((t * θ a : ℝ) : ℂ) * Complex.I)) := by
  have h : (t : ℂ) • bwtDiag θ = Matrix.diagonal (fun a => (t : ℂ) * ((θ a : ℂ) * Complex.I)) := by
    rw [bwtDiag]
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
  rw [h, Matrix.exp_diagonal]
  congr 1
  funext a
  rw [Pi.exp_def]
  dsimp only
  rw [← Complex.exp_eq_exp_ℂ]
  congr 1
  push_cast
  ring

theorem bwt_diag_mem_Kset (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply]
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
    simp
  · rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem bwt_actM_diag (E : Fin n → Fin n → Module.End ℂ M) (d : Fin n → ℂ) :
    actM E (Matrix.diagonal d) = ∑ a, d a • E a a := by
  simp [actM, Matrix.diagonal_apply, ite_smul]

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem bwt_actM_apply (θ : Fin n → ℝ) (v : D) :
    ((actM E (bwtDiag θ) v : D) : H) = ∑ a, ((θ a : ℂ) * Complex.I) • ((E a a v : D) : H) := by
  rw [bwtDiag, bwt_actM_diag]
  simp

private theorem exp_smul_bwtDiag_mem_UJset (ε : Fin n → Bool) (θ : Fin n → ℝ) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • bwtDiag θ) ∈ UJset ε := by
  have hK := bwt_diag_mem_Kset ε (fun a => s * θ a)
  obtain ⟨hu, hc⟩ := hK
  rw [bwt_exp]
  have hu' := Matrix.mem_unitaryGroup_iff'.1 hu
  have hJJ : Jm ε = Formalism.REAL.Jm ε := rfl
  show inUJ ε _
  unfold inUJ
  rw [hJJ, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, hu',
    Matrix.one_mul]

private theorem apply_one_eq_exp_smul_of_hasDerivAt_smul {F : ℝ → H} {c : ℂ} (hF : ∀ s, HasDerivAt F (c • F s) s) :
    F 1 = Complex.exp c • F 0 := by
  have hG : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * -c) • F t) 0 s := by
    intro s
    have h1 := (((hasDerivAt_id' s).ofReal_comp).mul_const (-c)).cexp
    refine (h1.smul (hF s)).congr_deriv ?_
    rw [smul_smul, ← add_smul]
    simp
  have hconst := is_const_of_deriv_eq_zero (fun s => (hG s).differentiableAt)
    (fun s => (hG s).deriv) 1 0
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, neg_zero,
    Complex.exp_zero, one_smul] at hconst
  rw [← hconst, smul_smul, ← Complex.exp_add]
  simp

private theorem hasDerivAt_of_shift_of_hasDerivAt_zero {G : ℝ → H} {L : H} (T : ℝ → (H →L[ℂ] H))
    (hG0 : HasDerivAt G L 0) (hshift : ∀ s t, G (s + t) = T s (G t)) (s : ℝ) :
    HasDerivAt G (T s L) s := by
  have h1 := ((T s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hG0
  have h2 : HasDerivAt (fun t => G (s + t)) (T s L) 0 := by
    convert h1 using 1 <;> first | rfl | (funext t; exact hshift s t)
  have h3 : HasDerivAt (fun t => G (s + t)) (T s L) (s - s) := by rwa [sub_self]
  have h4 := HasDerivAt.scomp (h := fun x : ℝ => x - s) s h3 ((hasDerivAt_id' s).sub_const s)
  convert h4 using 1 <;> first | (funext x; simp) | simp

theorem isWtOn_iff (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (v : D) (μ : Fin n → ℝ) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ (v : H) ↔ ∀ a, E a a v = ((μ a : ℝ) : ℂ) • v := by
  constructor
  · intro hw a
    have hder := hD.deriv _ (bwtDiag_inG ε (Pi.single a 1)) v
    have hfun : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • bwtDiag (Pi.single a 1))) (v : H)) =
        fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H) := by
      funext t
      have h := hw (fun b => t * (Pi.single a (1 : ℝ) : Fin n → ℝ) b) (bwt_diag_mem_Kset ε _)
      rw [bwt_exp, h]
      congr 2
      simp [Pi.single_apply] <;> ring
    rw [hfun, bwt_actM_apply] at hder
    have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H))
        (((μ a : ℂ) * Complex.I) • (v : H)) 0 := by
      have := ((((hasDerivAt_id' (0 : ℝ)).ofReal_comp).mul_const
        ((μ a : ℂ) * Complex.I)).cexp).smul_const (v : H)
      convert this using 1
      simp
    have heq := hder.unique hexp
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)] at heq
    simp only [Pi.single_eq_same, Complex.ofReal_one, one_mul] at heq
    apply Subtype.ext
    have h2 : Complex.I • ((E a a v : D) : H) = Complex.I • (((μ a : ℝ) : ℂ) • (v : H)) := by
      rw [heq, smul_smul, mul_comm]
    exact smul_right_injective H Complex.I_ne_zero h2
  · intro hE θ _
    have hlam : ((actM E (bwtDiag θ) v : D) : H) =
        (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • (v : H) := by
      rw [bwt_actM_apply]
      have hterm : ∀ a, ((θ a : ℂ) * Complex.I) • ((E a a v : D) : H) =
          (((θ a : ℂ) * Complex.I) * (μ a : ℂ)) • (v : H) := by
        intro a
        rw [hE a, Submodule.coe_smul, smul_smul]
      rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.sum_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
    have h0 := hD.deriv _ (bwtDiag_inG ε θ) v
    rw [hlam] at h0
    have hshift : ∀ s t : ℝ, σ (NormedSpace.exp (((s + t : ℝ) : ℂ) • bwtDiag θ)) (v : H) =
        σ (NormedSpace.exp ((s : ℂ) • bwtDiag θ)) (σ (NormedSpace.exp ((t : ℂ) • bwtDiag θ)) (v : H)) := by
      intro s t
      have hmul : NormedSpace.exp (((s + t : ℝ) : ℂ) • bwtDiag θ) =
          NormedSpace.exp ((s : ℂ) • bwtDiag θ) * NormedSpace.exp ((t : ℂ) • bwtDiag θ) := by
        rw [Complex.ofReal_add, add_smul]
        exact Matrix.exp_add_of_commute _ _ (((Commute.refl (bwtDiag θ)).smul_left _).smul_right _)
      rw [hmul, hσ.1.2 _ (exp_smul_bwtDiag_mem_UJset ε θ s) _ (exp_smul_bwtDiag_mem_UJset ε θ t)]
      rfl
    have hF : ∀ s : ℝ, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • bwtDiag θ)) (v : H))
        ((((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) •
          σ (NormedSpace.exp ((s : ℂ) • bwtDiag θ)) (v : H)) s := by
      intro s
      have := hasDerivAt_of_shift_of_hasDerivAt_zero (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • bwtDiag θ))) h0 hshift s
      rwa [map_smul] at this
    have hode := apply_one_eq_exp_smul_of_hasDerivAt_smul hF
    have e1 : NormedSpace.exp (((1 : ℝ) : ℂ) • bwtDiag θ) =
        Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) := by
      rw [bwt_exp]
      simp
    have e0 : NormedSpace.exp (((0 : ℝ) : ℂ) • bwtDiag θ) = 1 := by simp
    rw [e1, e0, hσ.1.1] at hode
    simpa using hode

end Rep

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroTopA
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def sztJd (ε : Fin n → Bool) : Fin n → ℂ := fun a => if ε a then 1 else -1

theorem szt_Jm_eq (ε : Fin n → Bool) : Jm ε = Matrix.diagonal (sztJd ε) := rfl

theorem szt_jd_sq (ε : Fin n → Bool) (a : Fin n) : sztJd ε a * sztJd ε a = 1 := by
  unfold sztJd
  split_ifs <;> norm_num

theorem szt_lead_Jconj (ε : Fin n → Bool) (z : Matrix (Fin n) (Fin n) ℂ) (i : ℕ) :
    S7.lead i (Jm ε * z * Jm ε) = S7.lead i z := by
  unfold S7.lead
  split_ifs with h
  · have hsub : (Jm ε * z * Jm ε).submatrix (Fin.castLE h) (Fin.castLE h) =
        Matrix.diagonal (sztJd ε ∘ Fin.castLE h) * z.submatrix (Fin.castLE h) (Fin.castLE h) *
          Matrix.diagonal (sztJd ε ∘ Fin.castLE h) := by
      rw [szt_Jm_eq]
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Function.comp_apply]
    rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hA : (∏ a, (sztJd ε ∘ Fin.castLE h) a) * (∏ a, (sztJd ε ∘ Fin.castLE h) a) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun a _ => szt_jd_sq ε _
    calc (∏ a, (sztJd ε ∘ Fin.castLE h) a) * (z.submatrix (Fin.castLE h) (Fin.castLE h)).det *
          (∏ a, (sztJd ε ∘ Fin.castLE h) a)
        = ((∏ a, (sztJd ε ∘ Fin.castLE h) a) * (∏ a, (sztJd ε ∘ Fin.castLE h) a)) *
            (z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by ring
      _ = (z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by rw [hA, one_mul]
  · rfl

theorem szt_phiM_Jconj (ε : Fin n → Bool) (μ : Fin n → ℤ) (z : Matrix (Fin n) (Fin n) ℂ) :
    S7.PhiM μ (Jm ε * z * Jm ε) = S7.PhiM μ z := by
  unfold S7.PhiM
  simp only [szt_lead_Jconj]

theorem szt_phiM_inv_conj {ε : Fin n → Bool} (μ : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X)
    (k : S7.KG ε) :
    S7.PhiM μ (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k)⁻¹ =
      S7.PhiM μ (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k) := by
  obtain ⟨hY, hE⟩ := S7.inP_conj k⁻¹ hX
  simp only [inv_inv] at hY hE
  rw [← hE, Matrix.inv_eq_left_inv (PolarDecomposition.polar_exp_neg_mul _), ← S7.inP_JXJ hY,
    PolarDecomposition.polar_exp_Jconj, szt_phiM_Jconj]

section Cayley

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem szt_unitary (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) : Pᴴ * P = 1 ∧ P * Pᴴ = 1 := by
  have hPu : P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hP.2
  refine ⟨?_, ?_⟩
  · have := (Matrix.mem_unitaryGroup_iff' (A := P)).mp hPu
    simpa [Matrix.star_eq_conjTranspose] using this
  · have := (Matrix.mem_unitaryGroup_iff (A := P)).mp hPu
    simpa [Matrix.star_eq_conjTranspose] using this

theorem szt_conj_mem (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : P * g * P⁻¹ ∈ UJset ε := by
  rw [← mir_UJset_eq]
  obtain ⟨e1, e2⟩ := szt_unitary hP
  have hinv : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv e1
  have hc : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.1.2
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  rw [hinv]
  calc (P * g * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (P * g * Pᴴ)
      = P * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * Pᴴ := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = P * Pᴴ * Formalism.REAL.Jm ε * (P * Pᴴ) := by
        rw [hc, hg', ← hc]; simp [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [e2]; simp

theorem szt_hs_conj (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    S7.hs (P * g * P⁻¹) = S7.hs g := by
  obtain ⟨e1, -⟩ := szt_unitary hP
  have hinv : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv e1
  have h := S7.decA_hs_conj (K := Pᴴ) (by rw [Matrix.conjTranspose_conjTranspose]; exact e1) g
  rw [Matrix.conjTranspose_conjTranspose] at h
  rw [hinv]
  exact h

end Cayley

theorem szt_gN_eq {k r : ℕ} (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Formalism.FourierDecayAlt.B.gN g = Real.sqrt (S7.hs g) := by
  unfold Formalism.FourierDecayAlt.B.gN S7.hs
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact Complex.normSq_eq_norm_sq _

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroCayleyA
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

section CayleyAux

variable {n : ℕ}

def szcMk (τ : Fin n → Fin n) (d o : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (if j = i then d i else 0) + (if j = τ i then o i else 0)

theorem szcMk_mul_apply (τ : Fin n → Fin n) (d o : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) : (szcMk τ d o * M) i j = d i * M i j + o i * M (τ i) j := by
  rw [Matrix.mul_apply]
  simp only [szcMk, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem szcMk_mul (τ : Fin n → Fin n) (hτ : ∀ i, τ (τ i) = i) (d o d' o' : Fin n → ℂ) :
    szcMk τ d o * szcMk τ d' o' =
      szcMk τ (fun i => d i * d' i + o i * o' (τ i)) (fun i => d i * o' i + o i * d' (τ i)) := by
  ext i j
  rw [szcMk_mul_apply]
  simp only [szcMk, hτ]
  split_ifs <;> ring

theorem szcMk_conjTranspose (τ : Fin n → Fin n) (hτ : ∀ i, τ (τ i) = i) (d o : Fin n → ℂ) :
    (szcMk τ d o)ᴴ = szcMk τ (fun i => star (d i)) (fun i => star (o (τ i))) := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  simp only [szcMk]
  have key : (i = τ j) ↔ (j = τ i) := ⟨fun h => by rw [h, hτ], fun h => by rw [h, hτ]⟩
  by_cases h1 : j = i
  · subst h1
    by_cases h : j = τ j
    · simp [← h]
    · simp [h]
  · by_cases h2 : j = τ i
    · subst h2
      simp [hτ, h1, Ne.symm h1]
    · have h3 : ¬ i = τ j := fun h => h2 (key.mp h)
      simp [h1, Ne.symm h1, h2, h3]

theorem szcMk_zero (τ : Fin n → Fin n) (d : Fin n → ℂ) : szcMk τ d 0 = Matrix.diagonal d := by
  ext i j
  simp only [szcMk, Matrix.diagonal_apply, Pi.zero_apply, ite_self, add_zero]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

end CayleyAux

section Cayley48

def szcTau (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if i.val < r ∨ r + k < i.val then ⟨2 * r + k - i.val, by omega⟩ else i

theorem szcTau_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (szcTau k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := by
  unfold szcTau; split_ifs <;> rfl

theorem szc_tau_pos {k r : ℕ} {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) :
    (szcTau k r i).val = 2 * r + k - i.val := by
  rw [szcTau_val, if_pos h]

theorem szc_tau_neg {k r : ℕ} {i : Fin (2 * r + k + 1)} (h : ¬ (i.val < r ∨ r + k < i.val)) :
    szcTau k r i = i := by
  unfold szcTau; rw [if_neg h]

theorem szcTau_tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : szcTau k r (szcTau k r i) = i := by
  have := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · apply Fin.ext
    have h' : (szcTau k r i).val < r ∨ r + k < (szcTau k r i).val := by rw [szc_tau_pos h]; omega
    rw [szc_tau_pos h', szc_tau_pos h]
    omega
  · rw [szc_tau_neg h, szc_tau_neg h]

def szcS : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)

theorem szcS_sq : szcS * szcS = 1 / 2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2 : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = (1 / 2 : ℝ) := by nlinarith [h]
  unfold szcS
  rw [← Complex.ofReal_mul, h2]
  push_cast
  ring

theorem szcS_star : star szcS = szcS := by
  unfold szcS
  rw [Complex.star_def]
  exact Complex.conj_ofReal _

def szcC (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then szcS else if r + k < i.val then -szcS else 1

def szcO (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r ∨ r + k < i.val then szcS else 0

def szcHD (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r ∨ r + k < i.val then 0 else if i.val = r + k then -1 else 1

def szcHO (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r ∨ r + k < i.val then 1 else 0

def szcD (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r + k then 1 else -1

theorem szcO_tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : szcO k r (szcTau k r i) = szcO k r i := by
  have := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · unfold szcO; rw [szc_tau_pos h]; split_ifs <;> first | rfl | omega
  · rw [szc_tau_neg h]

theorem szcHO_tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : szcHO k r (szcTau k r i) = szcHO k r i := by
  have := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · unfold szcHO; rw [szc_tau_pos h]; split_ifs <;> first | rfl | omega
  · rw [szc_tau_neg h]

theorem szcHD_tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : szcHD k r (szcTau k r i) = szcHD k r i := by
  have := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · unfold szcHD; rw [szc_tau_pos h]; split_ifs <;> first | rfl | omega
  · rw [szc_tau_neg h]

theorem szcC_tau (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    szcC k r (szcTau k r i) = if i.val < r then -szcS else if r + k < i.val then szcS else 1 := by
  have := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · unfold szcC; rw [szc_tau_pos h]; split_ifs <;> first | rfl | omega
  · rw [szc_tau_neg h]; unfold szcC; split_ifs <;> first | rfl | omega

theorem szc_Hpk (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r = szcMk (szcTau k r) (szcHD k r) (szcHO k r) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · have ht := szc_tau_pos h
    simp only [Formalism.QuantumDeterminants.Hpk, szcMk, szcHD, szcHO, Fin.ext_iff, ht]
    split_ifs <;> first | omega | norm_num
  · have ht := szc_tau_neg h
    simp only [Formalism.QuantumDeterminants.Hpk, szcMk, szcHD, szcHO, ht, Fin.ext_iff]
    split_ifs <;> first | omega | norm_num

theorem szc_CC (k r : ℕ) :
    szcMk (szcTau k r) (szcC k r) (szcO k r) * szcMk (szcTau k r) (szcC k r) (szcO k r) = 1 := by
  rw [szcMk_mul _ (szcTau_tau k r), ← Matrix.diagonal_one, ← szcMk_zero (szcTau k r)]
  congr 1
  · funext i
    have := i.isLt
    simp only [szcO_tau]
    unfold szcC szcO
    split_ifs <;> first | omega | ring1 | linear_combination 2 * szcS_sq
  · funext i
    have := i.isLt
    simp only [szcC_tau, Pi.zero_apply]
    unfold szcC szcO
    split_ifs <;> first | omega | ring1

theorem szc_Cstar (k r : ℕ) :
    (szcMk (szcTau k r) (szcC k r) (szcO k r))ᴴ = szcMk (szcTau k r) (szcC k r) (szcO k r) := by
  rw [szcMk_conjTranspose _ (szcTau_tau k r)]
  congr 1
  · funext i; unfold szcC; split_ifs <;> simp [szcS_star]
  · funext i; simp only [szcO_tau]; unfold szcO; split_ifs <;> simp [szcS_star]

theorem szc_CHC (k r : ℕ) :
    szcMk (szcTau k r) (szcC k r) (szcO k r) * Formalism.QuantumDeterminants.Hpk k r *
      szcMk (szcTau k r) (szcC k r) (szcO k r) = Matrix.diagonal (szcD k r) := by
  rw [szc_Hpk, szcMk_mul _ (szcTau_tau k r), szcMk_mul _ (szcTau_tau k r), ← szcMk_zero (szcTau k r)]
  congr 1
  · funext i
    have := i.isLt
    simp only [szcO_tau, szcHO_tau, szcHD_tau]
    unfold szcC szcO szcHD szcHO szcD
    split_ifs <;> first | omega | ring1 | linear_combination 2 * szcS_sq |
      linear_combination (-2) * szcS_sq
  · funext i
    have := i.isLt
    simp only [szcHO_tau, szcHD_tau, szcC_tau, Pi.zero_apply]
    unfold szcC szcO szcHD szcHO
    split_ifs <;> first | omega | ring1

def szcEqvF (k r : ℕ) (hk : 1 ≤ k) :
    {i : Fin (2 * r + k + 1) // Formalism.MainNotions.CayleySignature.eps48 k r i = false} ≃ Fin (r + 1) where
  toFun i := ⟨(i.1.val - k) / 2, by have := i.1.isLt; omega⟩
  invFun b := ⟨⟨k + 2 * b.val, by have := b.isLt; omega⟩, by
    have hb : ¬ (k + 2 * b.val < k - 1) := by omega
    have hb2 : ¬ ((k + 2 * b.val - (k - 1)) % 2 = 0) := by omega
    simp [Formalism.MainNotions.CayleySignature.eps48, hb, hb2]⟩
  left_inv i := by
    obtain ⟨i, hi⟩ := i
    have hlt := i.isLt
    have h1 : ¬ (i.val < k - 1) := by
      intro h1; simp [Formalism.MainNotions.CayleySignature.eps48, h1] at hi
    have h2 : ¬ ((i.val - (k - 1)) % 2 = 0) := by
      intro h2; simp [Formalism.MainNotions.CayleySignature.eps48, h1, h2] at hi
    apply Subtype.ext
    apply Fin.ext
    show k + 2 * ((i.val - k) / 2) = i.val
    omega
  right_inv b := by
    apply Fin.ext
    show (k + 2 * b.val - k) / 2 = b.val
    omega

def szcEqvT (k r : ℕ) : {j : Fin (2 * r + k + 1) // r + k ≤ j.val} ≃ Fin (r + 1) where
  toFun j := ⟨j.1.val - (r + k), by have := j.1.isLt; omega⟩
  invFun b := ⟨⟨r + k + b.val, by have := b.isLt; omega⟩, by show r + k ≤ r + k + b.val; omega⟩
  left_inv j := by
    obtain ⟨j, hj⟩ := j
    apply Subtype.ext
    apply Fin.ext
    show r + k + (j.val - (r + k)) = j.val
    omega
  right_inv b := by
    apply Fin.ext
    show r + k + b.val - (r + k) = b.val
    omega

theorem szc_exists_perm (k r : ℕ) (hk : 1 ≤ k) :
    ∃ π : Fin (2 * r + k + 1) ≃ Fin (2 * r + k + 1),
      ∀ i, (Formalism.MainNotions.CayleySignature.eps48 k r i = false ↔ r + k ≤ (π i).val) := by
  classical
  let e : {i : Fin (2 * r + k + 1) // Formalism.MainNotions.CayleySignature.eps48 k r i = false} ≃
      {j : Fin (2 * r + k + 1) // r + k ≤ j.val} := (szcEqvF k r hk).trans (szcEqvT k r).symm
  have hc : Fintype.card {i : Fin (2 * r + k + 1) // ¬ Formalism.MainNotions.CayleySignature.eps48 k r i = false} =
      Fintype.card {j : Fin (2 * r + k + 1) // ¬ r + k ≤ j.val} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_congr e]
  obtain ⟨f⟩ := Fintype.card_eq.mp hc
  refine ⟨Equiv.subtypeCongr e f, fun i => ?_⟩
  by_cases h : Formalism.MainNotions.CayleySignature.eps48 k r i = false
  · have hx : Equiv.subtypeCongr e f i = (e ⟨i, h⟩ : Fin (2 * r + k + 1)) := by
      simp [Equiv.subtypeCongr, h]
    rw [hx]
    exact ⟨fun _ => (e ⟨i, h⟩).2, fun _ => h⟩
  · have hx : Equiv.subtypeCongr e f i = (f ⟨i, h⟩ : Fin (2 * r + k + 1)) := by
      simp [Equiv.subtypeCongr, h]
    rw [hx]
    exact ⟨fun h' => absurd h' h, fun h' => absurd h' (f ⟨i, h⟩).2⟩

end Cayley48

end ReciprocityTheory.ChartRestriction.DS
end
end
