module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothCore
noncomputable section

open Finset Matrix Filter Topology
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Alg

variable {ε : Fin n → Bool}

theorem smc_inG_add {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) : inG ε (X + Y) :=
  Formalism.REAL.lie_algebra_add_mem_matrix hX hY

theorem smc_inG_rsmul {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (r : ℝ) : inG ε ((r : ℂ) • X) := by
  simpa using smd_inG_add_smul (inG_zero' ε) hX r
where inG_zero' (ε : Fin n → Bool) : inG ε (0 : Matrix (Fin n) (Fin n) ℂ) := by simp [inG]

theorem smc_cpart (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (S7.cpart1 ε Z) ∧ inG ε (S7.cpart2 ε Z) ∧ Z = S7.cpart1 ε Z + Complex.I • S7.cpart2 ε Z ∧
      (inG ε Z → S7.cpart1 ε Z = Z ∧ S7.cpart2 ε Z = 0) :=
  Formalism.REAL.complex_parts_mem_lie_algebra_holds n ε Z

theorem smc_cpart_unique {P Q : Matrix (Fin n) (Fin n) ℂ} (hP : inG ε P) (hQ : inG ε Q) :
    S7.cpart1 ε (P + Complex.I • Q) = P ∧ S7.cpart2 ε (P + Complex.I • Q) = Q :=
  Formalism.REAL.complex_parts_unique hP hQ

theorem smc_cpart1_add (Z W : Matrix (Fin n) (Fin n) ℂ) :
    S7.cpart1 ε (Z + W) = S7.cpart1 ε Z + S7.cpart1 ε W := Formalism.REAL.p0auxiliary_cpart1_add ε Z W

theorem smc_cpart1_real (x : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    S7.cpart1 ε ((x : ℂ) • Z) = (x : ℂ) • S7.cpart1 ε Z := Formalism.REAL.p0auxiliary_cpart1_real ε x Z

theorem smc_cpart1_I (Z : Matrix (Fin n) (Fin n) ℂ) :
    S7.cpart1 ε (Complex.I • Z) = -S7.cpart2 ε Z := Formalism.REAL.p0auxiliary_cpart1_I ε Z

end Alg

section Calc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasDerivAt_rdV_ext {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    {g X : Matrix (Fin n) (Fin n) ℂ} (hU : IsOpen U) (hg : g ∈ U) (hgJ : inUJ ε g) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ h ∈ U, inUJ ε h → f h = F h) (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have hγ := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  refine hcomp.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
  filter_upwards [hmem] with t ht
  exact hfF _ ht (smd_inUJ_mul hgJ (exp_smul_mem_UJset hX t))

theorem rdV_eq_fderiv {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    {g X : Matrix (Fin n) (Fin n) ℂ} (hU : IsOpen U) (hg : g ∈ U) (hgJ : inUJ ε g) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ h ∈ U, inUJ ε h → f h = F h) (hX : inG ε X) :
    S7.RdV X f g = fderiv ℝ F g (g * X) :=
  (hasDerivAt_rdV_ext hU hg hgJ hF hfF hX).deriv

theorem hasDerivAt_rdV {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (S7.RdV X f g) 0 := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  rw [rdV_eq_fderiv hU hgU hg hF hfF hX]
  exact hasDerivAt_rdV_ext hU hgU hg hF hfF hX

theorem rdV_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) : S7.RdV X f g = S7.RdV X f' g := by
  unfold S7.RdV
  congr 1
  funext t
  exact h _ (smd_inUJ_mul hg (exp_smul_mem_UJset hX t))

theorem smoothOnGV_add {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f)
    (hf' : S7.SmoothOnGV ε f') : S7.SmoothOnGV ε (fun g => f g + f' g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, h1, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', h1', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun g => F g + F' g, hU.inter hU', ⟨h1, h1'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), fun g hg hJ => ?_⟩
  show f g + f' g = F g + F' g
  rw [hfF g hg.1 hJ, hfF' g hg.2 hJ]

theorem smoothOnGV_smul (c : ℂ) {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f) :
    S7.SmoothOnGV ε (fun g => c • f g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, h1, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun g => c • F g, hU, h1, hF.const_smul c, fun g hg hJ => ?_⟩
  show c • f g = c • F g
  rw [hfF g hg hJ]

theorem smoothOnGV_rdV {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : S7.SmoothOnGV ε (S7.RdV X f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun k => fderiv ℝ F k (k * X), hU, hg₀U, ?_, ?_⟩
  · have h1 := hF.fderiv_of_isOpen (m := ∞) hU Formalism.REAL.withTop_enat_infty_add_one_le_infty
    have h2 : ContDiffOn ℝ ∞ (fun k : Matrix (Fin n) (Fin n) ℂ => k * X) U :=
      (Formalism.REAL.mulRightRealCLM X).contDiff.contDiffOn
    exact h1.clm_apply h2
  · intro k hk hkJ
    exact rdV_eq_fderiv hU hk hkJ hF hfF hX

theorem rdV_add_smul_fun {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f)
    (hf' : S7.SmoothOnGV ε f') (c : ℂ) {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) :
    S7.RdV X (fun h => f h + c • f' h) g = S7.RdV X f g + c • S7.RdV X f' g :=
  ((hasDerivAt_rdV hf hg hX).add ((hasDerivAt_rdV hf' hg hX).const_smul c)).deriv

theorem rdV_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (φ : E →L[ℂ] E')
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f) {X g : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (hg : inUJ ε g) : S7.RdV X (fun x => φ (f x)) g = φ (S7.RdV X f g) :=
  (((φ.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) (hasDerivAt_rdV hf hg hX)).deriv

theorem smoothOnGV_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (φ : E →L[ℂ] E')
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f) : S7.SmoothOnGV ε (fun x => φ (f x)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun x => φ (F x), hU, hg₀U, (φ.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩
  intro k hk hkJ
  show φ (f k) = φ (F k)
  rw [hfF k hk hkJ]

end Calc

section Orbit

variable {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem isSmoothVecU_iff {v : H} : IsSmoothVecU ε σ v ↔ S7.SmoothOnGV ε (fun g => σ g v) := Iff.rfl

theorem dS_eq_rdV (X : Matrix (Fin n) (Fin n) ℂ) (v : H) : dS σ X v = S7.RdV X (fun g => σ g v) 1 := by
  simp only [dS, S7.RdV, Matrix.one_mul]

theorem orbit_dS (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {v : H}
    (hv : IsSmoothVecU ε σ v) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    σ g (dS σ X v) = S7.RdV X (fun h => σ h v) g := by
  have h := hasDerivAt_dS hσ hX hv
  have h2 : HasDerivAt (fun t : ℝ => σ g (σ (NormedSpace.exp ((t : ℂ) • X)) v)) (σ g (dS σ X v)) 0 :=
    ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have e : (fun t : ℝ => σ (g * NormedSpace.exp ((t : ℂ) • X)) v) =
      fun t : ℝ => σ g (σ (NormedSpace.exp ((t : ℂ) • X)) v) := by
    funext t
    rw [hσ.1.2 g hg _ (exp_smul_mem_UJset hX t)]
    rfl
  show _ = deriv (fun t : ℝ => σ (g * NormedSpace.exp ((t : ℂ) • X)) v) 0
  rw [e]
  exact h2.deriv.symm

theorem orbit_ecV (hσ : IsURepOn (UJset ε) σ) (Z : Matrix (Fin n) (Fin n) ℂ) {v : H}
    (hv : IsSmoothVecU ε σ v) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    σ g (dS σ (S7.cpart1 ε Z) v + Complex.I • dS σ (S7.cpart2 ε Z) v) = S7.EcV ε Z (fun h => σ h v) g := by
  rw [map_add (f := _), map_smul, orbit_dS hσ (smc_cpart Z).1 hv hg, orbit_dS hσ (smc_cpart Z).2.1 hv hg]
  rfl

end Orbit

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothBr
noncomputable section

open Finset Matrix Filter Topology
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Helpers

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ε : Fin n → Bool}

theorem smBr_inUJ_one : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
  unfold inUJ; simp

theorem smBr_hasDerivAt_ext (f F : Matrix (Fin n) (Fin n) ℂ → E) (U : Set (Matrix (Fin n) (Fin n) ℂ))
    (g X : Matrix (Fin n) (Fin n) ℂ) (hU : IsOpen U) (hg : g ∈ U) (hgJ : inUJ ε g)
    (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, inUJ ε h → f h = F h) (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have hγ := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
    filter_upwards [hmem] with t ht
    exact hfF _ ht (Formalism.REAL.indefinite_unitary_mul_mem ε hgJ (Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t))
  exact hcomp.congr_of_eventuallyEq hev

theorem smBr_rdExt (f F : Matrix (Fin n) (Fin n) ℂ → E) (U : Set (Matrix (Fin n) (Fin n) ℂ))
    (g X : Matrix (Fin n) (Fin n) ℂ) (hU : IsOpen U) (hg : g ∈ U) (hgJ : inUJ ε g)
    (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, inUJ ε h → f h = F h) (hX : inG ε X) :
    S7.RdV X f g = fderiv ℝ F g (g * X) :=
  (smBr_hasDerivAt_ext f F U g X hU hg hgJ hF hfF hX).deriv

theorem smBr_rdBracket (f : Matrix (Fin n) (Fin n) ℂ → E) (X Y g : Matrix (Fin n) (Fin n) ℂ)
    (hf : S7.SmoothOnGV ε f) (hX : inG ε X) (hY : inG ε Y) (hg : inUJ ε g) :
    S7.RdV X (S7.RdV Y f) g - S7.RdV Y (S7.RdV X f) g = S7.RdV (X * Y - Y * X) f g := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hFa : ContDiffAt ℝ ∞ F g := hF.contDiffAt (hU.mem_nhds hgU)
  have ext : ∀ Z, inG ε Z → ∀ k ∈ U, inUJ ε k → S7.RdV Z f k = fderiv ℝ F k (k * Z) :=
    fun Z hZ k hk hkJ => smBr_rdExt f F U k Z hU hk hkJ hF hfF hZ
  have hsm : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      ContDiffOn ℝ ∞ (fun k => fderiv ℝ F k (k * Z)) U := fun Z =>
    (hF.fderiv_of_isOpen hU Formalism.REAL.withTop_enat_infty_add_one_le_infty).clm_apply (Formalism.REAL.mulRightRealCLM Z).contDiff.contDiffOn
  have hc : DifferentiableAt ℝ (fderiv ℝ F) g :=
    (hFa.fderiv_right (m := ∞) Formalism.REAL.withTop_enat_infty_add_one_le_infty).differentiableAt (by simp)
  have hd : ∀ Z W : Matrix (Fin n) (Fin n) ℂ, fderiv ℝ (fun k => fderiv ℝ F k (k * Z)) g W
      = fderiv ℝ (fderiv ℝ F) g W (g * Z) + fderiv ℝ F g (W * Z) := by
    intro Z W
    have H := (hc.hasFDerivAt.clm_apply (Formalism.REAL.mulRightRealCLM Z).hasFDerivAt).fderiv
    erw [H]
    exact add_comm _ _
  have e1 : S7.RdV X (S7.RdV Y f) g = fderiv ℝ (fun k => fderiv ℝ F k (k * Y)) g (g * X) :=
    smBr_rdExt (S7.RdV Y f) _ U g X hU hgU hg (hsm Y) (ext Y hY) hX
  have e2 : S7.RdV Y (S7.RdV X f) g = fderiv ℝ (fun k => fderiv ℝ F k (k * X)) g (g * Y) :=
    smBr_rdExt (S7.RdV X f) _ U g Y hU hgU hg (hsm X) (ext X hX) hY
  have e3 := ext _ (Formalism.REAL.lie_algebra_bracket_mem hX hY) g hgU hg
  have hsym : IsSymmSndFDerivAt ℝ F g :=
    hFa.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  have hs2 := hsym (g * X) (g * Y)
  rw [e1, e2, e3, hd, hd]
  simp only [Matrix.mul_sub, Matrix.mul_assoc, map_sub]
  erw [hs2]
  exact add_sub_add_left_eq_sub _ _ _

end Helpers

section Main

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smBr_loc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) :
    S7.RdV X f g = S7.RdV X f' g := by
  unfold S7.RdV
  congr 1
  funext t
  exact h _ (Formalism.REAL.indefinite_unitary_mul_mem ε hg (Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t))

theorem smBr_dS_eq (Z : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    dS σ Z w = S7.RdV Z (fun g => σ g w) 1 := by
  simp only [dS, S7.RdV, one_mul]

theorem smBr_orbit (hσ : IsURepOn (UJset ε) σ) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inG ε Z)
    {v : H} (hv : IsSmoothVecU ε σ v) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    σ g (dS σ Z v) = S7.RdV Z (fun g => σ g v) g := by
  obtain ⟨U, F, hU, h1U, hF, hfF⟩ := hv 1 smBr_inUJ_one
  have hc := smBr_hasDerivAt_ext (fun g => σ g v) F U 1 Z hU h1U smBr_inUJ_one hF hfF hZ
  simp only [one_mul] at hc
  have h2 := ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  have hfun : ((σ g) ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Z)) v) =
      fun t : ℝ => σ (g * NormedSpace.exp ((t : ℂ) • Z)) v := by
    funext t
    rw [hσ.1.2 g hg _ (Formalism.REAL.exp_indefinite_unitary_holds n ε Z hZ t)]
    rfl
  have h3 : HasDerivAt (fun t : ℝ => σ (g * NormedSpace.exp ((t : ℂ) • Z)) v)
      (σ g (fderiv ℝ F 1 Z)) 0 := by
    rw [← hfun]; exact h2
  rw [dS, hc.deriv, S7.RdV, h3.deriv]

end Main

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dS_bracket (hσ : IsURepOn (UJset ε) σ) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y)
    {v : H} (hv : IsSmoothVecU ε σ v) :
    dS σ X (dS σ Y v) - dS σ Y (dS σ X v) = dS σ (X * Y - Y * X) v := by
  have e1 : dS σ X (dS σ Y v) = S7.RdV X (S7.RdV Y (fun g => σ g v)) 1 := by
    rw [smBr_dS_eq]
    exact smBr_loc (fun g hg => smBr_orbit hσ hY hv hg) hX smBr_inUJ_one
  have e2 : dS σ Y (dS σ X v) = S7.RdV Y (S7.RdV X (fun g => σ g v)) 1 := by
    rw [smBr_dS_eq]
    exact smBr_loc (fun g hg => smBr_orbit hσ hX hv hg) hY smBr_inUJ_one
  rw [e1, e2, smBr_dS_eq]
  exact smBr_rdBracket _ X Y 1 hv hX hY smBr_inUJ_one

end ReciprocityTheory.ChartRestriction.DS
end
end
