module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerOfKFiniteVectors
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PeterssonLiftSmulMeasure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatGlueLatIffDual
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links
open Formalism.IndefR.Datum (IsSelfDualC)
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.AdIsom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents
open GlobalTheory.StdFrames hiding OA
open GlobalTheory.IdemSupport (cP cO)
open GlobalTheory.NormSum.AdLattice (lat)

variable {D : D7}

section Flat

variable {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V} {u : D.what₂.Word}

theorem vA_surj (V : HSp D) (x : Fin V.rank → D.host.E) : ∃ y : V.V, vA V y = fun i => inc D (x i) :=
  ⟨(Formalism.L2.Herm.crd V).symm x, funext fun i => by simp [vA]⟩

theorem eq_sum_vA_frame (x : Fin X.rank → EAf D) : x = ∑ i, x i • vA X (X.frame i) := by
  funext k
  have : ∀ i, vA X (X.frame i) k = if i = k then 1 else 0 := fun i => by
    change inc D (X.frame.repr (X.frame i) k) = _
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact map_one _
    · exact map_zero _
  simp [Finset.sum_apply, this]

theorem adelic_induction {p : (Fin X.rank → EAf D) → Prop} (h1 : ∀ x : X.V, p (vA X x)) (h0 : p 0)
    (hadd : ∀ x y, p x → p y → p (x + y)) (hsm : ∀ (a : EAf D) x, p x → p (a • x)) (x : Fin X.rank → EAf D) : p x := by
  rw [eq_sum_vA_frame x]
  exact Finset.sum_induction _ p hadd h0 fun i _ => hsm _ _ (h1 _)

theorem hA_zero_left (V : HSp D) (y : Fin V.rank → EAf D) : hA V 0 y = 0 := by simp [hA, Formalism.UG.hform]

theorem hA_zero_right (V : HSp D) (y : Fin V.rank → EAf D) : hA V y 0 = 0 := by simp [hA, Formalism.UG.hform]

theorem hA_mA_mA (h : HSpace.IsIsomEmb X Y ι) (x x' : Fin X.rank → EAf D) :
    hA Y (mA Y X ι *ᵥ x) (mA Y X ι *ᵥ x') = hA X x x' := by
  induction x using adelic_induction with
  | h1 x =>
    induction x' using adelic_induction with
    | h1 x' => rw [mA_mulVec_vA, mA_mulVec_vA, hA_vA, hA_vA, HSpace.hD, HSpace.hD, h]
    | h0 => rw [mulVec_zero, hA_zero_right, hA_zero_right]
    | hadd a b ha hb => rw [mulVec_add, hA_add_right, hA_add_right, ha, hb]
    | hsm c a ha => rw [mulVec_smul, hA_smul_right, hA_smul_right, ha]
  | h0 => rw [mulVec_zero, hA_zero_left, hA_zero_left]
  | hadd a b ha hb => rw [mulVec_add, hA_add_left, hA_add_left, ha, hb]
  | hsm c a ha => rw [mulVec_smul, hA_smul_left, hA_smul_left, ha]

theorem hA_mA_vA (h : IsLine Y X ι z u) (x : Fin X.rank → EAf D) : hA Y (mA Y X ι *ᵥ x) (vA Y z) = 0 := by
  induction x using adelic_induction with
  | h1 x => rw [mA_mulVec_vA, hA_vA, h.2.1, RingHom.map_zero]
  | h0 => rw [mulVec_zero, hA_zero_left]
  | hadd a b ha hb => rw [mulVec_add, hA_add_left, ha, hb, add_zero]
  | hsm c a ha => rw [mulVec_smul, hA_smul_left, ha, mul_zero]

theorem hA_flat (h : IsLine Y X ι z u) (x x' : Fin X.rank → EAf D) (a a' : EAf D) :
    hA Y (mA Y X ι *ᵥ x + a • vA Y z) (mA Y X ι *ᵥ x' + a' • vA Y z) = hA X x x' - a * cjA D a' * inc D (Tu D u) := by
  have h1 : hA Y (vA Y z) (mA Y X ι *ᵥ x') = 0 := by rw [← cjA_hA, hA_mA_vA h, RingHom.map_zero]
  rw [hA_add_left, hA_add_right, hA_add_right, hA_smul_left, hA_smul_left, hA_smul_right, hA_smul_right,
    hA_mA_mA h.1, hA_mA_vA h, h1, hA_vA, h.2.2, RingHom.map_neg]
  ring

theorem inc_inv_mul (u : D.what₂.Word) : inc D (Tu D u)⁻¹ * inc D (Tu D u) = 1 := by
  rw [← RingHom.map_mul, inv_mul_cancel₀ (Tu_ne_zero u), RingHom.map_one]

theorem cjA_inc_Tu (u : D.what₂.Word) : cjA D (inc D (Tu D u)) = inc D (Tu D u) := by rw [cjA_inc, star_natCast]

theorem cjA_inc_inv (u : D.what₂.Word) : cjA D (inc D (Tu D u)⁻¹) = inc D (Tu D u)⁻¹ := by
  rw [cjA_inc, star_inv₀, star_natCast]

theorem inc_Tu_mem (u : D.what₂.Word) : inc D (Tu D u) ∈ OA D := by
  rw [map_natCast]; exact natCast_mem _ _

theorem eq_zero_of_hA {V : HSp D} {x : Fin V.rank → EAf D} (h : ∀ y, hA V x y = 0) : x = 0 := by
  have h1 : V.gram.map (inc D) *ᵥ x = 0 := funext fun i => by
    rw [← Formalism.UG.P.sf_single (cjA D)]; exact h _
  exact Matrix.mulVec_injective_of_isUnit (isUnit_gram V) (h1.trans (mulVec_zero _).symm)

theorem flat_inj (h : IsLine Y X ι z u) {x x' : Fin X.rank → EAf D} {a a' : EAf D}
    (e : mA Y X ι *ᵥ x + a • vA Y z = mA Y X ι *ᵥ x' + a' • vA Y z) : x = x' ∧ a = a' := by
  constructor
  · rw [← sub_eq_zero]
    refine eq_zero_of_hA fun y => ?_
    have h1 := hA_flat h x y a 0
    rw [e, hA_flat h] at h1
    rw [hA_sub_left]
    simp only [RingHom.map_zero, mul_zero, zero_mul, sub_zero] at h1
    rw [h1, sub_self]
  · have h1 := hA_flat h x 0 a (inc D (Tu D u)⁻¹)
    rw [e, hA_flat h, hA_zero_right, hA_zero_right, cjA_inc_inv, mul_assoc, mul_assoc, inc_inv_mul] at h1
    linear_combination h1

theorem mem_glueLat {L₀ : Lat X} {x₀ : X.V} (y : Y.V) : y ∈ glueLat Y X ι z u L₀ x₀ ↔
    ∃ x : X.V, Formalism.L2.Herm.crd X x ∈ L₀ ∧ ∃ a : 𝓞 D.host.E, y = ι x + (a : D.host.E) • ((Tu D u)⁻¹ • z + ι x₀) := by
  rw [glueLat, Submodule.mem_sup]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, b, hb, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hb
    exact ⟨x, hx, a, by rw [← algebraMap_smul D.host.E a]; rfl⟩
  · rintro ⟨x, hx, a, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, Submodule.mem_span_singleton.2 ⟨a, rfl⟩, by rw [← algebraMap_smul D.host.E a]; rfl⟩


set_option maxHeartbeats 1600000 in
theorem mem_hat_glueLat {L₀ : Lat X} {x₀ : X.V} (y : Fin Y.rank → EAf D) :
    y ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) ↔ ∃ x ∈ hat L₀, ∃ a ∈ OA D,
      y = mA Y X ι *ᵥ (x + a • vA X x₀) + (a * inc D (Tu D u)⁻¹) • vA Y z := by
  constructor
  · intro hy
    refine hat_induction (p := fun y => ∃ x ∈ hat L₀, ∃ a ∈ OA D,
      y = mA Y X ι *ᵥ (x + a • vA X x₀) + (a * inc D (Tu D u)⁻¹) • vA Y z) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, a, rfl⟩ := (mem_glueLat y).1 hy
      refine ⟨vA X x, inc_mem_hat hx, inc D a, (inc_mem_iff _).2 ⟨a, rfl⟩, ?_⟩
      change vA Y _ = _
      rw [vA_add, vA_smul, vA_add, vA_smul, mulVec_add, mulVec_smul, mA_mulVec_vA, mA_mulVec_vA, smul_add, smul_smul]
      abel
    · exact ⟨0, zero_mem_hat, 0, zero_mem _, by rw [zero_smul, add_zero, mulVec_zero, zero_mul, zero_smul, add_zero]⟩
    · rintro _ _ ⟨x, hx, a, ha, rfl⟩ ⟨x', hx', a', ha', rfl⟩
      refine ⟨x + x', add_mem_hat hx hx', a + a', add_mem ha ha', ?_⟩
      rw [add_smul, add_mul, add_smul, add_add_add_comm x, mulVec_add _ (x + _)]
      abel
    · rintro c hc _ ⟨x, hx, a, ha, rfl⟩
      refine ⟨c • x, smul_mem_hat hc hx, c * a, mul_mem hc ha, ?_⟩
      rw [smul_add, ← mulVec_smul, smul_add, smul_smul, smul_smul, mul_assoc]
  · rintro ⟨x, hx, a, ha, rfl⟩
    have h1 : mA Y X ι *ᵥ x ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) := by
      refine hat_induction (p := fun x => mA Y X ι *ᵥ x ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)))
        ?_ ?_ ?_ ?_ hx
      · intro x hx
        obtain ⟨x, rfl⟩ := (Formalism.L2.Herm.crd X).surjective x
        change mA Y X ι *ᵥ vA X x ∈ _
        rw [mA_mulVec_vA]
        exact vA_mem_hat Y ((mem_glueLat _).2 ⟨x, hx, 0, by simp⟩)
      · rw [mulVec_zero]; exact zero_mem_hat
      · intro a b ha hb; rw [mulVec_add]; exact add_mem_hat ha hb
      · intro c hc a ha; rw [mulVec_smul]; exact smul_mem_hat hc ha
    have h2 := smul_mem_hat ha (vA_mem_hat Y ((mem_glueLat (ι := ι) (z := z) (u := u) (L₀ := L₀) (x₀ := x₀)
      ((Tu D u)⁻¹ • z + ι x₀)).2 ⟨0, by simp, 1, by simp⟩))
    convert add_mem_hat h1 h2 using 1
    rw [vA_add, vA_smul, mulVec_add, mulVec_smul, mA_mulVec_vA, smul_add, smul_smul]
    abel

theorem IsGlueVec.congr {L₀ : Lat X} {f f' : Fin X.rank → EAf D} (h : IsGlueVec X u L₀ f) (hf : f - f' ∈ hat L₀) :
    IsGlueVec X u L₀ f' := by
  obtain ⟨d, rfl⟩ : ∃ d, f' = f - d := ⟨f - f', (sub_sub_cancel _ _).symm⟩
  rw [sub_sub_cancel] at hf
  refine ⟨?_, h.int, fun y hy => ?_, ?_, fun y hy => ?_⟩
  · rw [smul_sub]; exact sub_mem_hat h.mul_mem (smul_mem_hat (inc_Tu_mem u) hf)
  · rw [hA_sub_left]; exact sub_mem (h.pair y hy) (h.int d hf y hy)
  · have h1 : hA X d f ∈ OA D := by rw [← cjA_hA]; exact cjA_mem (h.pair d hf)
    have := sub_mem (sub_mem h.norm (h.pair d hf)) (sub_mem h1 (h.int d hf d hf))
    rw [hA_sub_left, hA_sub_right, hA_sub_right]
    convert this using 1
    ring
  · obtain ⟨a, ha, H⟩ := h.dual y hy
    refine ⟨a, ha, ?_⟩
    convert add_mem_hat H (smul_mem_hat ha hf) using 1
    rw [smul_sub]; abel


set_option maxHeartbeats 1600000 in
theorem mem_hat_glueLat_iff_dual (h : IsLine Y X ι z u) {L₀ : Lat X} {x₀ : X.V} (hg : IsGlueVec X u L₀ (vA X x₀))
    (x : Fin X.rank → EAf D) (a : EAf D) :
    mA Y X ι *ᵥ x + a • vA Y z ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) ↔
      ∀ y ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)), hA Y y (mA Y X ι *ᵥ x + a • vA Y z) ∈ OA D := by
  simp only [mem_hat_glueLat]
  generalize vA X x₀ = f at hg
  have t := inc_inv_mul u
  constructor
  · rintro ⟨x₁, hx₁, a₁, ha₁, e⟩ _ ⟨x₂, hx₂, a₂, ha₂, rfl⟩
    have h1 : hA X x₂ f ∈ OA D := by rw [← cjA_hA]; exact cjA_mem (hg.pair _ hx₂)
    have := add_mem (add_mem (hg.int _ hx₂ _ hx₁) (mul_mem (cjA_mem ha₁) h1))
      (add_mem (mul_mem ha₂ (hg.pair _ hx₁)) (mul_mem (mul_mem ha₂ (cjA_mem ha₁)) hg.norm))
    rw [e, hA_flat h, hA_add_left, hA_add_right, hA_add_right, hA_smul_left, hA_smul_left, hA_smul_right, hA_smul_right,
      RingHom.map_mul, cjA_inc_inv]
    convert this using 1
    linear_combination (-(a₂ * cjA D a₁ * inc D (Tu D u)⁻¹)) * t
  · intro H
    obtain ⟨b, hb, hx⟩ := hg.dual x fun x' hx' => by
      have := H _ ⟨x', hx', 0, zero_mem _, rfl⟩
      rwa [hA_flat h, zero_smul, add_zero, zero_mul, zero_mul, zero_mul, sub_zero] at this
    have h1 := H _ ⟨0, zero_mem_hat, 1, one_mem _, rfl⟩
    rw [hA_flat h, zero_add, one_smul, one_mul] at h1
    have h2 := hg.pair _ hx
    rw [hA_sub_right, hA_smul_right] at h2
    have h3 : cjA D (a - b * inc D (Tu D u)⁻¹) ∈ OA D := by
      have := sub_mem (add_mem h2 (mul_mem (cjA_mem hb) hg.norm)) h1
      rw [RingHom.map_sub, RingHom.map_mul, cjA_inc_inv]
      convert this using 1
      linear_combination (-(cjA D a)) * t
    rw [cjA_mem_iff] at h3
    refine ⟨x - b • f - (a - b * inc D (Tu D u)⁻¹) • inc D (Tu D u) • f, sub_mem_hat hx (smul_mem_hat h3 hg.mul_mem),
      a * inc D (Tu D u), ?_, ?_⟩
    · convert add_mem (mul_mem h3 (inc_Tu_mem u)) hb using 1
      linear_combination b * t
    · congr 2
      · rw [smul_smul, sub_mul, mul_assoc b, t, mul_one, sub_smul]
        abel
      · linear_combination (-a) * t

end Flat

end GlobalTheory.AdIsom

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgHasType
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFinCuspAvgType

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined

variable {n : ℕ}

theorem mul_inv_mem_UH {G G₀ A B : Mx n} (hB : IsUnit B) (hA : Aᴴ * G * A = G₀) (hB' : Bᴴ * G * B = G₀) :
    A * B⁻¹ ∈ Formalism.QuantumDeterminants.UH G := by
  have h := Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hB)
  show (A * B⁻¹)ᴴ * G * (A * B⁻¹) = G
  calc (A * B⁻¹)ᴴ * G * (A * B⁻¹) = (B⁻¹)ᴴ * (Aᴴ * G * A) * B⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (B * B⁻¹)ᴴ * G * (B * B⁻¹) := by rw [hA, ← hB']; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [h]; simp

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)}

def uIso (hσ : IsURepOn (UJset ε) σ) {a b : Mx n} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) (hab : a * b = 1)
    (hba : b * a = 1) : H ≃ₗᵢ[ℂ] H :=
  { toFun := σ a
    invFun := σ b
    map_add' := map_add _
    map_smul' := map_smul _
    left_inv := fun w => by
      show σ b (σ a w) = w
      rw [← sigma_mul hσ hb ha, hba, sigma_one hσ]
    right_inv := fun w => by
      show σ a (σ b w) = w
      rw [← sigma_mul hσ ha hb, hab, sigma_one hσ]
    norm_map' := hσ.2.1 a ha }

theorem uIso_apply (hσ : IsURepOn (UJset ε) σ) {a b : Mx n} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) (hab : a * b = 1)
    (hba : b * a = 1) (w : H) : uIso hσ ha hb hab hba w = σ a w := rfl

end GlobalTheory.KFinCuspAvgType

end

namespace GlobalTheory.KFinCuspAvgType

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined

end GlobalTheory.KFinCuspAvgType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AvgOverMaximalCompactWeightedSupNormBound
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AvgOverMaximalCompactWeightedSupNormBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFinCuspApprox

open MeasureTheory Matrix Formalism.REAL GlobalTheory.Grow GlobalTheory.Mem.AutSpace GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate

theorem avgN_weighted_bound : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau)
    (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → ∀ a : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : GA D N.V → ℂ) (B : ℝ), (∀ g, ‖f g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ B) →
        ∀ g, ‖GlobalTheory.KFinCuspApprox.avgN θ N τ e f g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ C * B := by
  intro D θ hθ N τ e he a
  set P := N.M.fr τ with hPdef
  have hU : ∀ k : KG (N.M.ε τ), P⁻¹ * toMK k * P ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) := fun k =>
    GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ) (N.M.fr_gram τ) k
  have hκ : Continuous fun k : KG (N.M.ε τ) => P⁻¹ * toMK k * P :=
    (continuous_const.matrix_mul (GlobalTheory.TypeSum.continuous_toMK _)).matrix_mul continuous_const
  have hA : Continuous fun k : KG (N.M.ε τ) => atTau θ N.V τ (P⁻¹ * toMK k * P) :=
    (continuousOn_atTau hθ N.V τ).comp_continuous hκ hU
  obtain ⟨H, hH⟩ := isCompact_univ.exists_bound_of_continuousOn ((continuous_height N.V).comp hA).continuousOn
  have hHk : ∀ k, height N.V (atTau θ N.V τ (P⁻¹ * toMK k * P)) ≤ |H| := fun k => by
    have h := hH k (Set.mem_univ k)
    simp only [Function.comp_apply, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans (h.trans (le_abs_self _))
  have hne : Continuous fun k => ‖e k‖ := he.norm
  refine ⟨(∫ k, ‖e k‖ ∂(muK (N.M.ε τ))) * |H| ^ a,
    mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (pow_nonneg (abs_nonneg _) _), fun f B hf g => ?_⟩
  have hq := quotHeight_pos N.V g
  have hqa : 0 < quotHeight N.V g ^ a := pow_pos hq a
  have hpt : ∀ k, ‖e k * f (g * atTau θ N.V τ (P⁻¹ * toMK k * P))‖ ≤
      ‖e k‖ * (B * |H| ^ a / quotHeight N.V g ^ a) := by
    intro k
    set A := atTau θ N.V τ (P⁻¹ * toMK k * P)
    have h1 : quotHeight N.V g ≤ quotHeight N.V (g * A) * |H| := by
      have h := quotHeight_mul_le N.V (g * A) A⁻¹
      rw [mul_inv_cancel_right, height_inv] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hHk k) (quotHeight_pos N.V _).le)
    have h2 : quotHeight N.V g ^ a ≤ quotHeight N.V (g * A) ^ a * |H| ^ a := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hq.le h1 a
    have h3 : ‖f (g * A)‖ * quotHeight N.V g ^ a ≤ B * |H| ^ a :=
      calc ‖f (g * A)‖ * quotHeight N.V g ^ a ≤ ‖f (g * A)‖ * (quotHeight N.V (g * A) ^ a * |H| ^ a) :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = (‖f (g * A)‖ * quotHeight N.V (g * A) ^ a) * |H| ^ a := by ring
        _ ≤ B * |H| ^ a := mul_le_mul_of_nonneg_right (hf _) (by positivity)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [le_div_iff₀ hqa]; exact h3
  have hint : ‖GlobalTheory.KFinCuspApprox.avgN θ N τ e f g‖ ≤
      ∫ k, ‖e k‖ * (B * |H| ^ a / quotHeight N.V g ^ a) ∂(muK (N.M.ε τ)) :=
    norm_integral_le_of_norm_le (GlobalTheory.ExpansionAverage.integrable_K (hne.mul continuous_const))
      (Filter.Eventually.of_forall hpt)
  rw [integral_mul_const] at hint
  calc ‖GlobalTheory.KFinCuspApprox.avgN θ N τ e f g‖ * quotHeight N.V g ^ a
      ≤ ((∫ k, ‖e k‖ ∂(muK (N.M.ε τ))) * (B * |H| ^ a / quotHeight N.V g ^ a)) * quotHeight N.V g ^ a :=
        mul_le_mul_of_nonneg_right hint hqa.le
    _ = (∫ k, ‖e k‖ ∂(muK (N.M.ε τ))) * |H| ^ a * B := by field_simp

end GlobalTheory.KFinCuspApprox

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AvgOverMaximalCompactWeightedSupNormBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.avgOverMaximalCompact_weighted_supNorm_bound : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → ∀ a : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : GA D N.V → ℂ) (B : ℝ), (∀ g, ‖f g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ B) → ∀ g, ‖GlobalTheory.KFinCuspApprox.avgN θ N τ e f g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ C * B := by
  first | exact @GlobalTheory.KFinCuspApprox.avgN_weighted_bound | exact GlobalTheory.KFinCuspApprox.avgN_weighted_bound | (intros; apply GlobalTheory.KFinCuspApprox.avgN_weighted_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilThetaLevelPolynomialInHeight
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilThetaLevelPolynomialInHeight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise

noncomputable section

namespace GlobalTheory.LevelGrowth

theorem level_poly : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (Φ : WO M X → ℂ) (hΦ : IsThetaFunO ψ (sgn ε M) X Φ)
    (C₁ : Set (GA D M)) (hC₁ : IsCompact C₁),
    ∃ K₀ : Set (WO M X), K₀ ∈ nhds (0 : WO M X) ∧ IsCompact K₀ ∧ ∃ (m : ℝ) (e : ℕ), ∀ y ∈ C₁, ∀ h : GA D X,
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ m * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ e ∧
        ∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ (sgn ε M) X (n • u) (ω (y, h) Φ) = ω (y, h) Φ := by
  intro D ψ θ hθ ε M X χ χ' ω hω Φ hΦ C₁ hC₁
  obtain ⟨U, hU, hΦU⟩ := GlobalTheory.Size.isTheta_iff_level.1 hΦ
  obtain ⟨K₀, h0, hK₀, m, hlev⟩ := GlobalTheory.KernelSeminorm.exists_level_multiple (S := sgn ε M) (T := X) hU
  obtain ⟨B, hB⟩ := hC₁.bddAbove_image
    ((GlobalTheory.Grow.continuous_height (sgn ε M)).comp (continuous_ofSgn_symm ε M)).continuousOn
  obtain ⟨C, hC, hcmp⟩ := GlobalTheory.Grow.height_comparison X hθ
  refine ⟨K₀, h0, hK₀, m * max B 0 * C, 1, fun y hy h => ?_⟩
  set g := (ofSgn ε M).symm y with hg
  obtain ⟨n, hn, hnle, hmem⟩ := hlev g h
  refine ⟨n, hn, ?_, fun u hu hinf => ?_⟩
  · have hgB : GlobalTheory.Grow.height (sgn ε M) g ≤ max B 0 := (hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)
    have hhC : GlobalTheory.Grow.height X h ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) := (hcmp h).2
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    have hg0 := (GlobalTheory.Grow.height_pos (sgn ε M) g).le
    have hh0 := (GlobalTheory.Grow.height_pos X h).le
    calc (n : ℝ) ≤ m * (GlobalTheory.Grow.height (sgn ε M) g * GlobalTheory.Grow.height X h) := hnle
      _ ≤ m * (max B 0 * (C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hgB hhC hh0 (le_max_right _ _)) hm0
      _ = m * max B 0 * C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ 1 := by ring
  · have hv : (actO (sgn ε M) X g⁻¹ h⁻¹ (n • u)).map (infPart D) = 0 := by
      have : (n • u).map (infPart D) = 0 := by
        ext i j
        have h3 : infPart D (u i j) = 0 := congrFun (congrFun hinf i) j
        exact (map_nsmul (infPart D) n (u i j)).trans ((congrArg (n • ·) h3).trans (nsmul_zero n))
      unfold actO
      rw [Matrix.map_mul, Matrix.map_mul, this, Matrix.mul_zero, Matrix.zero_mul]
    have hfix := hΦU.2 _ (hmem u hu hinf) hv
    have e := hω.om_heis g h (actO (sgn ε M) X g⁻¹ h⁻¹ (n • u)) Φ hΦ
    rw [hfix, GlobalTheory.ThetaGrowth.actO_mul, mul_inv_cancel, mul_inv_cancel, GlobalTheory.ThetaGrowth.actO_one] at e
    have e2 : (WRep.toSgn ε ω) (g, h) = ω (y, h) := by
      simp [WRep.toSgn, hg]
    rw [e2] at e
    exact e.symm

end GlobalTheory.LevelGrowth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilThetaLevelPolynomialInHeightStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilTheta_level_polynomial_in_height : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (Φ : WO M X → ℂ) (hΦ : IsThetaFunO ψ (sgn ε M) X Φ)
    (C₁ : Set (GA D M)) (hC₁ : IsCompact C₁),
    ∃ K₀ : Set (WO M X), K₀ ∈ nhds (0 : WO M X) ∧ IsCompact K₀ ∧ ∃ (m : ℝ) (e : ℕ), ∀ y ∈ C₁, ∀ h : GA D X,
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ m * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ e ∧
        ∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ (sgn ε M) X (n • u) (ω (y, h) Φ) = ω (y, h) Φ := by
  first | exact @GlobalTheory.LevelGrowth.level_poly | exact GlobalTheory.LevelGrowth.level_poly | (intros; apply GlobalTheory.LevelGrowth.level_poly <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyExistsDoubleCosetAntiInvolutionUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyExistsDoubleCosetAntiInvolutionUnitary
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

noncomputable section
namespace GlobalTheory.AntiInvLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eventually_isUnram : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := by
  have hfin := (Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 F) (B := 𝓞 E))).image
    (fun P : HeightOneSpectrum (𝓞 E) => P.under (𝓞 F))
  refine Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)
  simp only [Set.mem_setOf_eq] at hv
  rw [GlobalTheory.LFun.isUnram_iff] at hv
  push_neg at hv
  obtain ⟨P, hP, h1⟩ := hv
  refine ⟨P, ?_, hP⟩
  simp only [Set.mem_setOf_eq]
  by_contra hnd
  haveI := not_dvd_differentIdeal_iff.1 hnd
  exact h1 Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)}

theorem exists_antiInv_split (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : Submodule.IsFullLattice E L)
    (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) (hd : IsSelfDualAt σ J L v) :
    ∃ θ : GLoc σ J v → GLoc σ J v, (∀ x y, θ (x * y) = θ y * θ x) ∧ (∀ x, θ (θ x) = x) ∧
      ∀ g, ∃ a ∈ stabLoc σ J L v, ∃ b ∈ stabLoc σ J L v, θ g = a * g * b := by
  obtain ⟨w, -, -, hw, -⟩ := id hv
  have h : w.under (𝓞 F) = v := HeightOneSpectrum.ext hw
  obtain ⟨e, ⟨-, he⟩, -⟩ := GlobalTheory.LFun.SplitChart.exists_isSplitChart hc hJ hL.fg (Submodule.IsFullLattice.span_eq_top (self := hL)) h hv hd
  refine ⟨fun g => e.symm (Formalism.UG.P.heckecomm_tr (e g)), fun x y => ?_, fun x => ?_, fun g => ?_⟩
  · simp only [map_mul, Formalism.UG.P.heckecomm_tr_mul]
  · simp only [MulEquiv.apply_symm_apply, Formalism.UG.P.heckecomm_tr_tr, MulEquiv.symm_apply_apply]
  · obtain ⟨a, b, hab⟩ := Formalism.UG.P.heckecomm_tr_dc Formalism.UG.P.cartan_decomposition_holds E w n (e g)
    refine ⟨e.symm a, (he _).2 (by simpa using a.2), e.symm b, (he _).2 (by simpa using b.2), ?_⟩
    show e.symm _ = _
    rw [hab]
    apply e.injective
    simp

theorem exists_antiInv_inert (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : Submodule.IsFullLattice E L)
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (hd : IsSelfDualAt σ J L v) :
    ∃ θ : GLoc σ J v → GLoc σ J v, (∀ x y, θ (x * y) = θ y * θ x) ∧ (∀ x, θ (θ x) = x) ∧
      ∀ g, ∃ a ∈ stabLoc σ J L v, ∃ b ∈ stabLoc σ J L v, θ g = a * g * b := by
  have h : w.under (𝓞 F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨-, ⟨c, hc', -⟩, -, -, hrest⟩ := (GlobalTheory.LFun.exists_isInertChart σ hc v).2 w h hw
  obtain ⟨⟨ϖ, hU⟩, hch⟩ := hrest c hc'
  obtain ⟨e, ⟨-, -, he⟩, -⟩ := hch n J L hJ hL.fg (Submodule.IsFullLattice.span_eq_top (self := hL)) hd
  refine ⟨fun g => g⁻¹, mul_inv_rev, inv_inv, fun g => ?_⟩
  obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := GlobalTheory.LFun.ConjParam.inv_mem hU (e g)
  refine ⟨e.symm k₁, (he _).2 (by simpa using hk₁), e.symm k₂, (he _).2 (by simpa using hk₂), ?_⟩
  apply e.injective
  simp [hk]

theorem eventually_exists_antiInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L → ∀ᶠ v in cofinite, ∃ θ : GLoc σ J v → GLoc σ J v, (∀ x y, θ (x * y) = θ y * θ x) ∧ (∀ x, θ (θ x) = x) ∧ ∀ g, ∃ a ∈ stabLoc σ J L v, ∃ b ∈ stabLoc σ J L v, θ g = a * g * b := by
  intro F E _ _ _ _ _ σ hc n J hJ L hL
  filter_upwards [eventually_isUnram (F := F) (E := E),
    GlobalTheory.AdelicU.SelfDual.eventually_isSelfDualAt (σ := σ) hJ.2 hL] with v hu hd
  rcases (GlobalTheory.LFun.exists_isInertChart σ hc v).1 hu with hs | ⟨w, hw⟩
  · exact exists_antiInv_split hc hJ hL hs hd
  · exact exists_antiInv_inert hc hJ hL hw hd

end GlobalTheory.AntiInvLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyExistsDoubleCosetAntiInvolutionUnitaryStatement
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_exists_doubleCoset_antiInvolution_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L → ∀ᶠ v in cofinite, ∃ θ : GLoc σ J v → GLoc σ J v, (∀ x y, θ (x * y) = θ y * θ x) ∧ (∀ x, θ (θ x) = x) ∧ ∀ g, ∃ a ∈ stabLoc σ J L v, ∃ b ∈ stabLoc σ J L v, θ g = a * g * b := by
  first | exact @GlobalTheory.AntiInvLoc.eventually_exists_antiInv | exact GlobalTheory.AntiInvLoc.eventually_exists_antiInv | (intros; apply GlobalTheory.AntiInvLoc.eventually_exists_antiInv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianWittIndexLeNegativeSignature
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianWittIndexLeNegativeSignature
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.WittSig

open Matrix
open scoped ComplexOrder

theorem cT_conj_eq {m k : Type} (M : Matrix m k ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; simp [Formalism.UG.cT, conjTranspose_apply]

theorem Jpq_conjTranspose (q p : ℕ) : (Formalism.UG.Jpq q p)ᴴ = Formalism.UG.Jpq q p := by
  simp [Formalism.UG.Jpq, fromBlocks_conjTranspose]

theorem le_of_isotropic {n : Type} [Fintype n] [DecidableEq n] {q p r : ℕ} (J : Matrix n n ℂ)
    (hS : Formalism.UG.HasSignature J q p) (X Y : Matrix n (Fin r) ℂ) (hxx : Xᴴ * J * X = 0)
    (hxy : Xᴴ * J * Y = 1) : r ≤ p := by
  obtain ⟨e, P, hP⟩ := hS
  rw [cT_conj_eq] at hP
  set Q : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ := (↑(P⁻¹) : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) with hQdef
  have hPQ : (P : Matrix _ _ ℂ) * Q = 1 := by simp [Q]
  have hJ : J.reindex e e = Qᴴ * Formalism.UG.Jpq q p * Q := by
    rw [← hP]
    have h1 : Qᴴ * (P : Matrix _ _ ℂ)ᴴ = 1 := by rw [← conjTranspose_mul, hPQ, conjTranspose_one]
    calc J.reindex e e = (Qᴴ * (P : Matrix _ _ ℂ)ᴴ) * J.reindex e e * ((P : Matrix _ _ ℂ) * Q) := by
          rw [h1, hPQ, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  set Z := Q * X.reindex e (Equiv.refl _) with hZdef
  set W := Q * Y.reindex e (Equiv.refl _) with hWdef
  have key : ∀ A B : Matrix n (Fin r) ℂ,
      (Q * A.reindex e (Equiv.refl _))ᴴ * Formalism.UG.Jpq q p * (Q * B.reindex e (Equiv.refl _)) = Aᴴ * J * B := by
    intro A B
    have : (Q * A.reindex e (Equiv.refl _))ᴴ * Formalism.UG.Jpq q p * (Q * B.reindex e (Equiv.refl _)) =
        (A.reindex e (Equiv.refl _))ᴴ * (Qᴴ * Formalism.UG.Jpq q p * Q) * B.reindex e (Equiv.refl _) := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [this, ← hJ]
    ext i j
    simp [Matrix.mul_apply, Matrix.reindex_apply, conjTranspose_apply]
    rw [← Fintype.sum_sum_type (fun x => (∑ k, (starRingEnd ℂ) (A k i) * J k (e.symm x)) * B (e.symm x) j)]
    exact e.symm.sum_comp (fun x => (∑ k, (starRingEnd ℂ) (A k i) * J k x) * B x j)
  have hZZ : Zᴴ * Formalism.UG.Jpq q p * Z = 0 := by rw [hZdef, key, hxx]
  have hWZ : Wᴴ * Formalism.UG.Jpq q p * Z = 1 := by
    have h := key X Y
    rw [hxy, ← hZdef, ← hWdef] at h
    have h2 := congrArg conjTranspose h
    simpa [conjTranspose_mul, Jpq_conjTranspose, Matrix.mul_assoc] using h2
  let L : (Fin r → ℂ) →ₗ[ℂ] (Fin p → ℂ) := (Z.submatrix Sum.inr id).mulVecLin
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    set u := Z *ᵥ c with hu
    have hlow : ∀ i, u (Sum.inr i) = 0 := fun i => by
      have := congrFun hc i
      simpa [L, u, mulVec, dotProduct, submatrix] using this
    have h0 : star u ⬝ᵥ (Formalism.UG.Jpq q p *ᵥ u) = 0 := by
      have : star c ⬝ᵥ ((Zᴴ * Formalism.UG.Jpq q p * Z) *ᵥ c) = 0 := by rw [hZZ]; simp
      rw [← this, hu, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    have hup : (fun i => u (Sum.inl i)) = 0 := by
      rw [← dotProduct_star_self_eq_zero, ← h0]
      simp [Formalism.UG.Jpq, dotProduct, mulVec, Fintype.sum_sum_type, hlow, Matrix.one_apply]
    have hu0 : u = 0 := by
      funext x
      rcases x with i | i
      · exact congrFun hup i
      · exact hlow i
    calc c = (Wᴴ * Formalism.UG.Jpq q p * Z) *ᵥ c := by rw [hWZ, one_mulVec]
      _ = (Wᴴ * Formalism.UG.Jpq q p) *ᵥ u := by rw [hu, mulVec_mulVec]
      _ = 0 := by rw [hu0, mulVec_zero]
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

theorem wittIndex_le_neg {D : D7} (M : HSp D) {p : ℕ} {τ : D.what₂.Tau}
    (hS : Formalism.UG.HasSignature (gramAt D M τ) (M.rank - p) p) {r : ℕ}
    {Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E}
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf) : r ≤ p := by
  have hc := (GlobalTheory.AdelicU.isCMExt_host D).2.2.2 (tauE D τ)
  have hmap : ∀ {a b : ℕ} (A : Matrix (Fin M.rank) (Fin a) D.host.E)
      (B : Matrix (Fin M.rank) (Fin b) D.host.E),
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * M.gram * B).map (tauE D τ) =
        (A.map (tauE D τ))ᴴ * gramAt D M τ * B.map (tauE D τ) := by
    intro a b A B
    rw [Matrix.map_mul, Matrix.map_mul, gramAt]
    congr 2
    ext i j
    simp [Formalism.UG.cT, conjTranspose_apply, hc]
  apply le_of_isotropic (gramAt D M τ) hS (Xf.map (tauE D τ)) (Yf.map (tauE D τ))
  · rw [← hmap, hW.xx, Matrix.map_zero _ (map_zero _)]
  · rw [← hmap, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.WittSig
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianWittIndexLeNegativeSignatureStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianWittIndex_le_negative_signature : ∀ {D : D7} (M : HSp D) {p : ℕ} {τ : D.what₂.Tau}, Formalism.UG.HasSignature (gramAt D M τ) (M.rank - p) p → ∀ {r : ℕ} {Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E}, GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf → r ≤ p := by
  first | exact @GlobalTheory.WittSig.wittIndex_le_neg | exact GlobalTheory.WittSig.wittIndex_le_neg | (intros; apply GlobalTheory.WittSig.wittIndex_le_neg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryMatchingFramesAtNonconjugatePlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryMatchingFramesAtNonconjugatePlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct Matrix

namespace GlobalTheory.FrameMatch

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem frGL_mul_intGL (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (y z : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    frGL (β * intGL F E n y) z = frGL β (y * z * y⁻¹) := by
  show MulAut.conj (β * intGL F E n y) (intGL F E n z) = MulAut.conj β (intGL F E n (y * z * y⁻¹))
  rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  group

theorem St_mul_intGL (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    St (β * intGL F E n y) = St β := by
  ext x
  show x ∈ (frGL (β * intGL F E n y)).range ↔ x ∈ (frGL β).range
  simp only [MonoidHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨y * z * y⁻¹, (frGL_mul_intGL β y z).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨y⁻¹ * z * y, ?_⟩
    rw [frGL_mul_intGL]
    congr 1
    group

theorem redFn_mul_intGL (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E))
    (PP : Pl E) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    redFn (β * intGL F E n y) PP x =
      (Formalism.UG.bc (resS F PP) y)⁻¹ * redFn β PP x * Formalism.UG.bc (resS F PP) y := by
  by_cases hx : x ∈ St β
  · obtain ⟨z, rfl⟩ := MonoidHom.mem_range.1 hx
    have h1 : frGL β z = frGL (β * intGL F E n y) (y⁻¹ * z * y) := by
      rw [frGL_mul_intGL]
      congr 1
      group
    conv_lhs => rw [h1]
    rw [redFn_frGL, redFn_frGL]
    rw [map_mul, map_mul, map_inv]
  · have hx' : x ∉ St (β * intGL F E n y) := by rwa [St_mul_intGL]
    simp only [redFn, ext1, dif_neg hx, dif_neg hx', mul_one, inv_mul_cancel]

theorem frGL_mul (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    frGL β y * β = β * intGL F E n y := by
  simp only [frGL, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem exists_intGL_of_isFrame {β₁ β₂ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (h₁ : IsFrame β₁ Λ) (h₂ : IsFrame β₂ Λ) : ∃ m : GL (Fin n) (Formalism.L2.Herm.intAf F E), β₂ = β₁ * intGL F E n m := by
  classical

  have key : ∀ {γ δ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}, IsFrame γ Λ → IsFrame δ Λ → ∀ i j,
      ((γ⁻¹ * δ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j ∈
        Formalism.L2.Herm.intAf F E := by
    intro γ δ hγ hδ i j
    set v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F :=
      (δ : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec (Pi.single j 1) with hv
    have hvL : v ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
      rw [hδ v]
      intro k
      rw [hv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rcases eq_or_ne k j with hk | hk
      · subst hk
        simp only [Pi.single_eq_same]
        exact Subring.one_mem _
      · simp only [Pi.single_eq_of_ne hk]
        exact Subring.zero_mem _
    have hi := (hγ v).1 hvL i
    rw [hv, Matrix.mulVec_mulVec, Matrix.mulVec_single_one, ← Units.val_mul] at hi
    simpa [Matrix.transpose_apply] using hi
  let M : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, key h₁ h₂ i j⟩
  let N : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, key h₂ h₁ i j⟩
  have hM : M.map (Formalism.L2.Herm.intAf F E).subtype =
      ((β₁⁻¹ * β₂ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    ext i j
    rfl
  have hN : N.map (Formalism.L2.Herm.intAf F E).subtype =
      ((β₂⁻¹ * β₁ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    ext i j
    rfl
  have hinj : Function.Injective
      (fun A : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) => A.map (Formalism.L2.Herm.intAf F E).subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hone : (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)).map (Formalism.L2.Herm.intAf F E).subtype = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hMN : M * N = 1 := hinj (by
    simp only [Matrix.map_mul, hM, hN, hone, ← Units.val_mul]
    rw [show β₁⁻¹ * β₂ * (β₂⁻¹ * β₁) = 1 by group, Units.val_one])
  have hNM : N * M = 1 := hinj (by
    simp only [Matrix.map_mul, hM, hN, hone, ← Units.val_mul]
    rw [show β₂⁻¹ * β₁ * (β₁⁻¹ * β₂) = 1 by group, Units.val_one])
  refine ⟨⟨M, N, hMN, hNM⟩, ?_⟩
  have hm : intGL F E n ⟨M, N, hMN, hNM⟩ = β₁⁻¹ * β₂ := by
    ext1
    rw [← hM]
    exact Formalism.UG.P.bc_coe _ _
  rw [hm]
  group

end General


set_option maxHeartbeats 1000000 in
theorem frames_match : ∀ {D : D7} (V : HSp D) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP') → ∀ β₁ β₂ : GL (Fin V.rank) (EAf D), IsFrame β₁ (Formalism.L2.Herm.crdLat V V.L0) → IsFrame β₂ (Formalism.L2.Herm.crdLat V V.L0) → ∃ u ∈ GfC V, IsFrame (finE V u * β₁) (Formalism.L2.Herm.crdLat V V.L0) ∧ ∀ PP ∈ Pg, ∀ x, redFn (finE V u * β₁) PP x = redFn β₂ PP x := by
  classical
  intro D V Pg hPg β₁ β₂ h₁ h₂
  obtain ⟨m, hm⟩ := exists_intGL_of_isFrame h₁ h₂

  obtain ⟨β₀, ⟨c, h₀⟩, -⟩ := GlobalTheory.StdFrames.exists_frame_std V
  have hB : IsBaseFrame V β₁ (Formalism.L2.Herm.crdLat V V.L0) (1 ^ c) := ⟨h₁, h₀.2⟩

  have hloc : ∀ PP, ∃ κ : GA D V, κ ∈ GfC V ∧ finE V κ ∈ St β₁ ∧
      (PP ∈ Pg → redFn β₁ PP (finE V κ) = Formalism.UG.bc (resS D.host.F PP) m) ∧
      ∀ P', P' ≠ PP → (PP ∈ Pg → ¬ IsConjPl (D := D) PP P') → redFn β₁ P' (finE V κ) = 1 := by
    intro PP
    by_cases hPP : PP ∈ Pg
    · obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt (hPg PP hPP PP hPP)
      obtain ⟨κ, -, k1, k2, k3, k4⟩ :=
        GlobalTheory.ParahoricLift.exists_local_lift hB he (Formalism.UG.bc (resS D.host.F PP) m)
      exact ⟨κ, k1, k2, fun _ => k3, fun P' hP' hc => k4 P' hP' (hc hPP)⟩
    · refine ⟨1, Subgroup.one_mem _, ?_, fun h => absurd h hPP, fun P' _ _ => ?_⟩
      · rw [map_one]
        exact Subgroup.one_mem _
      · rw [map_one]
        exact blockDiagonalExtendByOnePrimeField_one (St β₁) (redAt β₁ P')
  choose κ hκG hκS hκR hκO using hloc
  have hprod := GlobalTheory.ParahoricLift.redFn_list_prod V β₁ (Pg.toList.map κ) (by
    intro g hg
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hg
    exact hκS b)

  have hred : ∀ PP ∈ Pg, redFn β₁ PP (finE V (Pg.toList.map κ).prod) = Formalism.UG.bc (resS D.host.F PP) m := by
    intro PP hPP
    have hs := GlobalTheory.ParahoricLift.prod_map_single (Finset.nodup_toList Pg) (Finset.mem_toList.2 hPP)
      (fun b => redFn β₁ PP (finE V (κ b)))
      (fun b hb => hκO b PP (Ne.symm hb) (fun hbP => hPg b hbP PP hPP))
    rw [hprod.2 PP, List.map_map]
    exact hs.trans (hκR PP hPP)
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 hprod.1
  refine ⟨(Pg.toList.map κ).prod, (GfC V).list_prod_mem (by
    intro g hg
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hg
    exact hκG b), GlobalTheory.StabLatInv.isFrame_mul_of_mem_St β₁ _ _ h₁ hprod.1, ?_⟩
  intro PP hPP x
  have hz' : Formalism.UG.bc (resS D.host.F PP) z = Formalism.UG.bc (resS D.host.F PP) m := by
    rw [← redFn_frGL β₁ PP z, hz]
    exact hred PP hPP
  rw [← hz, frGL_mul, hm, redFn_mul_intGL, redFn_mul_intGL, hz']

end GlobalTheory.FrameMatch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryMatchingFramesAtNonconjugatePlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_matching_frames_at_nonconjugate_places : ∀ {D : D7} (V : HSp D) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP') → ∀ β₁ β₂ : GL (Fin V.rank) (EAf D), IsFrame β₁ (Formalism.L2.Herm.crdLat V V.L0) → IsFrame β₂ (Formalism.L2.Herm.crdLat V V.L0) → ∃ u ∈ GfC V, IsFrame (finE V u * β₁) (Formalism.L2.Herm.crdLat V V.L0) ∧ ∀ PP ∈ Pg, ∀ x, redFn (finE V u * β₁) PP x = redFn β₂ PP x := by
  first | exact @GlobalTheory.FrameMatch.frames_match | exact GlobalTheory.FrameMatch.frames_match | (intros; apply GlobalTheory.FrameMatch.frames_match <;> assumption)
end
end
