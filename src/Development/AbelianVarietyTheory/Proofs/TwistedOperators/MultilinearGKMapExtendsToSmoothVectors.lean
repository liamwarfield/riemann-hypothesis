module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevFormEqZeroOnSmoothOfKFiniteDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearSlotwiseExtensionOfEquivariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevContinuousModelRepOfSobolevBound
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevContinuousModelRepOfSobolevBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SobFrame

section Conj

variable {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ}

theorem conj_cancel (hP : IsUnit P) (g : Matrix (Fin n) (Fin n) ℂ) : P * (P⁻¹ * g * P) * P⁻¹ = g := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h1]; simp

theorem exp_smul_conj_inv (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P⁻¹ * X * P)) = P⁻¹ * NormedSpace.exp (t • X) * P := by
  rw [← Matrix.exp_conj' _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem prod_conj_inv (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun g => P⁻¹ * g * P).prod = P⁻¹ * l.prod * P := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  induction l with
  | nil => simp [h2]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc P⁻¹ * a * P * (P⁻¹ * l.prod * P) = P⁻¹ * a * (P * P⁻¹) * l.prod * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dRep_conj_inv (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    dRep (fun g => σ (P * g * P⁻¹)) (P⁻¹ * X * P) w = dRep σ X w := by
  unfold dRep
  simp only [exp_smul_conj_inv hP, conj_cancel hP]

theorem foldr_dRep_conj_inv (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) (w : H) :
    (l.map fun X => P⁻¹ * X * P).foldr (dRep fun g => σ (P * g * P⁻¹)) w = l.foldr (dRep σ) w := by
  induction l with
  | nil => rfl
  | cons X l ih => simp only [List.map_cons, List.foldr_cons, ih, dRep_conj_inv hP]

theorem smoothVec_conj_inv (hP : IsUnit P) {A B : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hAB : ∀ X ∈ A, P⁻¹ * X * P ∈ B) {w : H} (hw : SmoothVec B (fun g => σ (P * g * P⁻¹)) w) :
    SmoothVec A σ w := by
  intro k Xs hXs
  have h := hw k (fun i => P⁻¹ * Xs i * P) fun i => hAB _ (hXs i)
  have e : ∀ t : Fin k → ℝ, P * (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))).prod * P⁻¹ =
      (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod := by
    intro t
    have : (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))) =
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P⁻¹ * g * P := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact exp_smul_conj_inv hP _ _
    rw [this, prod_conj_inv hP, conj_cancel hP]
  simpa only [e] using h

end Conj

theorem conj_mem_lieAt {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) :
    (M.fr τ)⁻¹ * X * M.fr τ ∈ lieAt V τ := by
  have hX' : Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X = 0 := hX
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hc : ∀ Y : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one,
      Matrix.one_mul]
  show ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * gramAt D V τ + gramAt D V τ * ((M.fr τ)⁻¹ * X * M.fr τ) = 0
  rw [← M.fr_gram τ]
  have e : ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) +
      (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ * ((M.fr τ)⁻¹ * X * M.fr τ) =
      (M.fr τ)ᴴ * ((Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X) * M.fr τ) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hc, Matrix.mul_nonsing_inv_cancel_left _ _ hd,
      Matrix.add_mul, Matrix.mul_add]
  rw [e, hX', Matrix.zero_mul, Matrix.mul_zero]

theorem sobCont_rep_of_bound : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (ℓ : M.H τ →ₗ[ℂ] ℂ)
    (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) →
    (∀ w, SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w → ‖ℓ w‖ ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w) →
    Sobolev₂ (lieAt V τ) (M.rep τ) ℓ := by
  intro D V S M τ ℓ L C hL hC
  have hP := M.fr_unit τ
  refine ⟨L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ), C, ?_, fun w hw => ?_⟩
  · intro l hl X hX
    obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
    obtain ⟨X₀, hX₀, rfl⟩ := List.mem_map.1 hX
    exact conj_mem_lieAt M τ (hL l₀ hl₀ X₀ hX₀)
  · have hw' : SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w :=
      smoothVec_conj_inv (σ := M.σ τ) hP (fun _ hX => conj_mem_lieAt M τ hX) hw
    have hs : ((L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ)).map
        fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum = GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w := by
      unfold GlobalTheory.SmoothGlob.sobNorm
      rw [List.map_map]
      congr 1
      refine List.map_congr_left fun l _ => ?_
      exact congrArg norm (foldr_dRep_conj_inv (σ := M.σ τ) hP l w)
    rw [hs]
    exact hC w hw'

end GlobalTheory.SobFrame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevContinuousModelRepOfSobolevBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolevContinuous_modelRep_of_sobolevBound : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (ℓ : M.H τ →ₗ[ℂ] ℂ)
    (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) →
    (∀ w, SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w → ‖ℓ w‖ ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w) →
    Sobolev₂ (lieAt V τ) (M.rep τ) ℓ := by
  first | exact @GlobalTheory.SobFrame.sobCont_rep_of_bound | exact GlobalTheory.SobFrame.sobCont_rep_of_bound | (intros; apply GlobalTheory.SobFrame.sobCont_rep_of_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearSlotwiseExtensionOfEquivariantStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multilinear_positionwise_extension_of_equivariant : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type} [∀ τ, AddCommGroup (H τ)] [∀ τ, Module ℂ (H τ)]
    {E : Type} [AddCommGroup E] [Module ℂ E] (A B : ∀ τ, Submodule ℂ (H τ)), (∀ τ, A τ ≤ B τ) →
    ∀ (Rk Rg : ∀ τ, Set ((H τ → H τ) × (E →ₗ[ℂ] E))),
    (∀ τ, ∀ r ∈ Rk τ, ∀ x ∈ A τ, r.1 x ∈ A τ) → (∀ τ, ∀ r ∈ Rg τ, ∀ x ∈ B τ, r.1 x ∈ B τ) →
    ∀ (C : ∀ τ, Submodule ℂ (H τ →ₗ[ℂ] E)),
    (∀ τ, ∀ L ∈ C τ, ∀ L' : H τ →ₗ[ℂ] E, (∀ x ∈ B τ, L' x = L x) → L' ∈ C τ) →
    (∀ τ (L : H τ →ₗ[ℂ] E), (∀ r ∈ Rk τ, ∀ x ∈ A τ, L (r.1 x) = r.2 (L x)) →
      ∃ L' ∈ C τ, (∀ r ∈ Rg τ, ∀ x ∈ B τ, L' (r.1 x) = r.2 (L' x)) ∧ ∀ x ∈ A τ, L' x = L x) →
    (∀ τ, ∀ L ∈ C τ, (∀ x ∈ A τ, L x = 0) → ∀ x ∈ B τ, L x = 0) →
    (∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ L ∈ C τ', r.2 ∘ₗ L ∈ C τ') →
    (∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ r' ∈ Rg τ', r.2 ∘ₗ r'.2 = r'.2 ∘ₗ r.2) →
    (∀ τ τ', τ ≠ τ' → ∀ F : H τ →ₗ[ℂ] H τ' →ₗ[ℂ] E, (∀ w ∈ B τ, F w ∈ C τ') → (∀ a ∈ A τ', F.flip a ∈ C τ) →
      ∀ b ∈ B τ', F.flip b ∈ C τ) →
    ∀ T₀ : MultilinearMap (RingHom.id ℂ) H E,
    (∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ A τ') → ∀ r ∈ Rk τ, ∀ x ∈ A τ,
      T₀ (Function.update u τ (r.1 x)) = r.2 (T₀ (Function.update u τ x))) →
    ∃ T : MultilinearMap (RingHom.id ℂ) H E, (∀ u, (∀ τ, u τ ∈ A τ) → T u = T₀ u) ∧
      ∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ B τ') →
        T.toLinearMap u τ ∈ C τ ∧
          ∀ r ∈ Rg τ, ∀ x ∈ B τ, T (Function.update u τ (r.1 x)) = r.2 (T (Function.update u τ x)) := by
  first | exact @GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension | exact GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension | (intros; apply GlobalTheory.FactorwiseExtension.exists_multilinear_positionwise_extension <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureOfForallDualVanish
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureOfForallDualVanish
namespace GlobalTheory

open Complex

theorem mem_closure_of_forall_dual_vanish :
    ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p → ∀ (Z : Submodule ℂ E) (x : E),
    (∀ f : E →L[ℂ] ℂ, (∀ z ∈ Z, f z = 0) → f x = 0) → x ∈ closure (Z : Set E) := by
  intro E _ _ _ _ p hp Z x h
  haveI := hp.continuousSMul
  haveI : LocallyConvexSpace ℝ E := hp.toLocallyConvexSpace
  by_contra hx
  rw [← Z.topologicalClosure_coe] at hx
  obtain ⟨f, u, hfx, hf⟩ := RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ)
    ((Z.topologicalClosure.restrictScalars ℝ).convex) Z.isClosed_topologicalClosure hx
  simp only [RCLike.re_to_complex] at hfx hf
  have hre : ∀ w ∈ Z, (f w).re = 0 := by
    intro w hw
    by_contra hne
    set t : ℝ := (u - 1) / (f w).re
    have hmem : ((t : ℂ) • w) ∈ Z.topologicalClosure :=
      Z.le_topologicalClosure (Z.smul_mem _ hw)
    have h1 := hf _ hmem
    rw [map_smul, smul_eq_mul, Complex.re_ofReal_mul] at h1
    have : t * (f w).re = u - 1 := by
      simp only [t]; field_simp
    linarith
  have hvan : ∀ z ∈ Z, f z = 0 := by
    intro z hz
    have h1 := hre z hz
    have h2 := hre (Complex.I • z) (Z.smul_mem _ hz)
    rw [map_smul, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im] at h2
    apply Complex.ext
    · simpa using h1
    · simp at h2; simpa using h2
  have h0 := hf 0 (Z.topologicalClosure.zero_mem)
  have hfx0 := h f hvan
  rw [map_zero] at h0
  rw [hfx0] at hfx
  simp at h0 hfx
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureOfForallDualVanishStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_of_forall_clm_vanish : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p → ∀ (Z : Submodule ℂ E) (x : E),
    (∀ f : E →L[ℂ] ℂ, (∀ z ∈ Z, f z = 0) → f x = 0) → x ∈ closure (Z : Set E) := by
  first | exact @GlobalTheory.mem_closure_of_forall_dual_vanish | exact GlobalTheory.mem_closure_of_forall_dual_vanish | (intros; apply GlobalTheory.mem_closure_of_forall_dual_vanish <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BilinearBoundOfDenseSecondSlot
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BilinearBoundOfDenseSecondSlot
open Filter Topology
open scoped Uniformity

namespace GlobalTheory

theorem bilinear_bound_of_dense_right : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p →
    ∀ {X₁ X₂ : Type} [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]
    (j₁ : X₁ →ₗ[ℂ] E) (j₂ : X₂ →ₗ[ℂ] E), Function.Injective j₁ → IsClosed (Set.range j₁) →
    ∀ (D₂ : Submodule ℂ X₂), (∀ x, j₂ x ∈ closure (j₂ '' (D₂ : Set X₂))) →
    ∀ (F : X₁ →ₗ[ℂ] X₂ →ₗ[ℂ] E),
    (∀ w i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ b, p i (F w b) ≤ q (j₂ b)) →
    (∀ a ∈ D₂, ∀ i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w a) ≤ q (j₁ w)) →
    ∀ b i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w b) ≤ q (j₁ w) := by
  intro E _ _ _ _ _ _ p hp X₁ X₂ _ _ _ _ j₁ j₂ hinj hcl D₂ hdense F h₁ h₂ b i
  haveI : ContinuousSMul ℂ E := hp.continuousSMul
  haveI : FirstCountableTopology E := hp.firstCountableTopology
  haveI : PolynormableSpace ℂ E := hp.toPolynormableSpace
  haveI : IsTopologicalAddGroup E := inferInstance
  set Y : Submodule ℂ E := LinearMap.range j₁ with hYdef
  have hYc : IsClosed (Y : Set E) := by simpa [Y, LinearMap.coe_range] using hcl
  haveI : IsUniformAddGroup Y := Y.toAddSubgroup.isUniformAddGroup
  haveI : CompleteSpace Y := hYc.completeSpace_coe
  haveI : FirstCountableTopology Y := Topology.IsInducing.subtypeVal.firstCountableTopology
  haveI : (𝓤 Y).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : BarrelledSpace ℂ Y := inferInstance
  let e : X₁ ≃ₗ[ℂ] Y := LinearEquiv.ofInjective j₁ hinj
  have he : ∀ w, ((e w : Y) : E) = j₁ w := fun w => rfl

  let gl : D₂ → Y →ₗ[ℂ] E := fun a => (F.flip (a : X₂)).comp e.symm.toLinearMap
  have hgl : ∀ a y, gl a y = F (e.symm y) a := fun a y => rfl
  have hgc : ∀ a, Continuous (gl a) := by
    intro a
    refine hp.continuous_of_continuous_comp (gl a) fun k => ?_
    obtain ⟨q, hq, hle⟩ := h₂ a a.2 k
    refine Seminorm.continuous_of_le (q := q.comp Y.subtype) (hq.comp continuous_subtype_val) ?_
    intro y
    have := hle (e.symm y)
    rw [← he, e.apply_symm_apply] at this
    simpa [Seminorm.comp_apply, hgl] using this
  let g : D₂ → Y →L[ℂ] E := fun a => ⟨gl a, hgc a⟩
  let l : Filter D₂ := Filter.comap (fun a : D₂ => j₂ a) (𝓝 (j₂ b))
  haveI : l.NeBot := by
    rw [Filter.comap_neBot_iff]
    intro t ht
    obtain ⟨_, htx, ⟨a, ha, rfl⟩⟩ := mem_closure_iff_nhds.mp (hdense b) t ht
    exact ⟨⟨a, ha⟩, htx⟩
  have hT : Tendsto (fun a y => g a y) l (𝓝 fun y => F (e.symm y) b) := by
    rw [tendsto_pi_nhds]
    intro y
    rw [hp.tendsto_nhds]
    intro k ε hε
    obtain ⟨q, hq, hle⟩ := h₁ (e.symm y) k
    have ht : Tendsto (fun a : D₂ => q (j₂ a - j₂ b)) l (𝓝 0) := by
      have h0 : Tendsto (fun a : D₂ => j₂ a - j₂ b) l (𝓝 (j₂ b - j₂ b)) :=
        tendsto_comap.sub tendsto_const_nhds
      have := (hq.tendsto _).comp h0
      simpa [Function.comp_def] using this
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with a ha
    calc p k (g a y - F (e.symm y) b) = p k (F (e.symm y) ((a : X₂) - b)) := by
          simp [g, hgl, map_sub]
      _ ≤ q (j₂ ((a : X₂) - b)) := hle _
      _ < ε := by simpa [map_sub] using ha
  let G : Y →L[ℂ] E := continuousLinearMapOfTendsto g hT
  have hG : ∀ y, G y = F (e.symm y) b := fun y => rfl
  have hr : Continuous ((p i).comp G.toLinearMap) := (hp.continuous_seminorm i).comp G.continuous
  obtain ⟨q, hq, hle⟩ := Seminorm.exists_le_comp_of_isInducing hr (f := Y.subtype) .subtypeVal
  refine ⟨q, hq, fun w => ?_⟩
  have := hle (e w)
  simpa [Seminorm.comp_apply, hG, he] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BilinearBoundOfDenseSecondSlotStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_seminorm_bound_of_dense_second_slot : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p →
    ∀ {X₁ X₂ : Type} [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]
    (j₁ : X₁ →ₗ[ℂ] E) (j₂ : X₂ →ₗ[ℂ] E), Function.Injective j₁ → IsClosed (Set.range j₁) →
    ∀ (D₂ : Submodule ℂ X₂), (∀ x, j₂ x ∈ closure (j₂ '' (D₂ : Set X₂))) →
    ∀ (F : X₁ →ₗ[ℂ] X₂ →ₗ[ℂ] E),
    (∀ w i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ b, p i (F w b) ≤ q (j₂ b)) →
    (∀ a ∈ D₂, ∀ i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w a) ≤ q (j₁ w)) →
    ∀ b i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w b) ≤ q (j₁ w) := by
  first | exact @GlobalTheory.bilinear_bound_of_dense_right | exact GlobalTheory.bilinear_bound_of_dense_right | (intros; apply GlobalTheory.bilinear_bound_of_dense_right <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearGKMapExtendsToSmoothVectors
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FactorExtension

open GlobalTheory.SmoothGlob

variable {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E]

theorem smul_seminorm_cont {q : Seminorm ℂ E} (hq : Continuous q) (c : NNReal) : Continuous (c • q) := by
  rw [Seminorm.coe_smul]
  exact hq.const_smul c

theorem bound_via {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {p : ℕ → Seminorm ℂ E} {N L : H →ₗ[ℂ] E}
    (hN : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) →
      ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, SmoothVec (lieSet ε) σ w → sobNorm σ S w ≤ q (N w))
    (hL : L ∈ sobBd ε σ p) (i : ℕ) :
    ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, SmoothVec (lieSet ε) σ w → p i (L w) ≤ q (N w) := by
  obtain ⟨S, C, hS, hb⟩ := hL i
  obtain ⟨q, hq, hqb⟩ := hN S hS
  refine ⟨Real.toNNReal |C| • q, smul_seminorm_cont hq _, fun w hw => ?_⟩
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (abs_nonneg C)]
  calc p i (L w) ≤ C * sobNorm σ S w := hb w hw
    _ ≤ |C| * sobNorm σ S w := mul_le_mul_of_nonneg_right (le_abs_self C) (sobNorm_nonneg σ S w)
    _ ≤ |C| * q (N w) := mul_le_mul_of_nonneg_left (hqb w hw) (abs_nonneg C)

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem form_zero (hHC : GlobalTheory.Published.HarishChandraModules) (M : DSModel V S) (τ : D.what₂.Tau) {p : ℕ → Seminorm ℂ E}
    (hp : WithSeminorms p) {L : M.H τ →ₗ[ℂ] E} (hL : L ∈ sobBd (M.ε τ) (M.σ τ) p) (f : E →L[ℂ] ℂ)
    (h0 : ∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, f (L a) = 0) : ∀ w ∈ M.sm τ, f (L w) = 0 := by
  have hq : Continuous ((normSeminorm ℂ ℂ).comp (f : E →ₗ[ℂ] ℂ)) := continuous_norm.comp f.continuous
  obtain ⟨Sl, C, hS, hb⟩ := sobBd_seminorm hp hL _ hq
  have hsc := GlobalTheory.T.sobolevContinuous_modelRep_of_sobolevBound M τ ((f : E →ₗ[ℂ] ℂ) ∘ₗ L) Sl C hS (fun w hw => by simpa using hb w hw)
  exact GlobalTheory.T.sobolevForm_eq_zero_on_smooth_of_kFinite_discreteSeries hHC D V S M τ _ hsc h0

theorem uniq (hHC : GlobalTheory.Published.HarishChandraModules) (M : DSModel V S) (τ : D.what₂.Tau) {p : ℕ → Seminorm ℂ E}
    (hp : WithSeminorms p) {L : M.H τ →ₗ[ℂ] E} (hL : L ∈ sobBd (M.ε τ) (M.σ τ) p)
    (h0 : ∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, L a = 0) : ∀ w ∈ M.sm τ, L w = 0 := by
  intro w hw
  have h := GlobalTheory.T.mem_closure_of_forall_clm_vanish hp ⊥ (L w) fun f _ => form_zero hHC M τ hp hL f (fun a ha => by rw [h0 a ha, map_zero]) w hw
  rw [Submodule.bot_coe, closure_singleton] at h
  exact h

end GlobalTheory.FactorExtension

namespace GlobalTheory.FactorExtension

open GlobalTheory.SmoothGlob

theorem extend_positions : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E] (p : ℕ → Seminorm ℂ E) (π dπ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → (E →L[ℂ] E)), (∀ τ, GlobalTheory.SmoothGlob.IsSmoothModRep (M.ε τ) p (π τ) (dπ τ)) → (∀ τ τ', τ ≠ τ' → ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ g' ∈ Formalism.MainNotions.S.UJset (M.ε τ'), (π τ g).comp (π τ' g') = (π τ' g').comp (π τ g)) → ∀ T₀ : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) E, (∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = M.σ τ k (u τ) → T₀ (Function.update u τ w) = π τ k (T₀ u)) → (∀ τ, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = dRep (M.σ τ) X (u τ) → T₀ (Function.update u τ w) = dπ τ X (T₀ u)) → ∃ T : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => M.sm τ) E, (∀ (v : M.Vec) (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M), (∀ τ, (v τ : M.H τ) = u τ) → T v = T₀ u) ∧ (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.σ τ g (v τ) → T (Function.update v τ w) = π τ g (T v)) ∧ ∀ τ (i : ℕ) (v : M.Vec), ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) ∧ ∀ w : M.sm τ, p i (T (Function.update v τ w)) ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w := by
  intro hHC hCW D V S M E _ _ _ _ _ _ p π dπ hπ hcomm T₀ hK hL
  haveI hc : ∀ τ, CompleteSpace (M.H τ) := fun τ => (M.ds τ).1
  have hsm : ∀ τ w, w ∈ M.sm τ ↔ SmoothVec (lieSet (M.ε τ)) (M.σ τ) w := fun τ w => GlobalTheory.T.mem_smoothVectors_discreteSeriesModel_iff M τ w
  have hstd : ∀ τ, GlobalTheory.TypeSum.Std (M.ε τ) (M.σ τ) := fun τ => GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  have hAB : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ M.sm τ := fun τ v hv => (hsm τ v).2 ((hstd τ).2.2.1 v hv)
  have hPex : ∀ τ, ∃ P : M.H τ →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, P x = x := by
    intro τ
    obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ).subtype
      (Submodule.ker_subtype _)
    exact ⟨P, fun x => LinearMap.congr_fun hP x⟩
  choose P hP using hPex
  have hP' : ∀ τ (x : M.H τ) (hx : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), P τ x = ⟨x, hx⟩ := fun τ x hx => hP τ ⟨x, hx⟩
  let T₀' : MultilinearMap (RingHom.id ℂ) (fun τ => M.H τ) E := T₀.compLinearMap P
  let Rk : ∀ τ, Set ((M.H τ → M.H τ) × (E →ₗ[ℂ] E)) := fun τ =>
    {r | (∃ k ∈ Formalism.REAL.Kset (M.ε τ), r = (⇑(M.σ τ k), (π τ k : E →ₗ[ℂ] E))) ∨
      ∃ X ∈ lieSet (M.ε τ), r = (dRep (M.σ τ) X, (dπ τ X : E →ₗ[ℂ] E))}
  let Rg : ∀ τ, Set ((M.H τ → M.H τ) × (E →ₗ[ℂ] E)) := fun τ =>
    {r | ∃ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), r = (⇑(M.σ τ g), (π τ g : E →ₗ[ℂ] E))}
  have hRk : ∀ τ, ∀ r ∈ Rk τ, ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, r.1 x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := by
    rintro τ r (⟨k, hk, rfl⟩ | ⟨X, hX, rfl⟩) x hx
    · obtain ⟨A, hA, ha, hs⟩ := hx
      exact ⟨A, hA, hs k hk x ha, hs⟩
    · exact GlobalTheory.TypeSum.isKFin_dRep _ _ _ (M.σ τ) (hstd τ) x hx X hX
  have hRg : ∀ τ, ∀ r ∈ Rg τ, ∀ x ∈ M.sm τ, r.1 x ∈ M.sm τ := by
    rintro τ r ⟨g, hg, rfl⟩ x hx
    rw [GlobalTheory.SmVec.sm_eq] at hx ⊢
    exact GlobalTheory.SmVec.sigma_mem (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 hx hg
  let C : ∀ τ, Submodule ℂ (M.H τ →ₗ[ℂ] E) := fun τ => sobBd (M.ε τ) (M.σ τ) p
  have hC : ∀ τ, ∀ L ∈ C τ, ∀ L' : M.H τ →ₗ[ℂ] E, (∀ x ∈ M.sm τ, L' x = L x) → L' ∈ C τ :=
    fun τ L hL L' h => sobBd_congr hL fun w hw => h w ((hsm τ w).2 hw)

  have hcw : ∀ τ (L : M.H τ →ₗ[ℂ] E), (∀ r ∈ Rk τ, ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, L (r.1 x) = r.2 (L x)) →
      ∃ T : M.H τ →ₗ[ℂ] E, (∀ v, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) v → T v = L v) ∧
        IsSmoothGMap (M.ε τ) (M.σ τ) p (π τ) T ∧ IsClosed (T '' {w | SmoothVec (lieSet (M.ε τ)) (M.σ τ) w}) ∧
        ((∃ v, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) v ∧ L v ≠ 0) →
          ∀ Sl : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ)), (∀ l ∈ Sl, ∀ X ∈ l, X ∈ lieSet (M.ε τ)) →
            ∃ q : Seminorm ℂ E, Continuous q ∧
              ∀ w, SmoothVec (lieSet (M.ε τ)) (M.σ τ) w → sobNorm (M.σ τ) Sl w ≤ q (T w)) := by
    intro τ L hLk
    have hGK : IsGKMap (M.ε τ) (M.σ τ) (π τ) (dπ τ) L :=
      ⟨fun k hk v hv => hLk _ (Or.inl ⟨k, hk, rfl⟩) v hv, fun X hX v hv => hLk _ (Or.inr ⟨X, hX, rfl⟩) v hv⟩
    obtain ⟨T, hT1, hT2, -, hT4, hT5⟩ := hCW V.rank (M.ε τ) (M.H τ) (M.σ τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 E p
      (π τ) (dπ τ) (hπ τ) L hGK
    exact ⟨T, hT1, hT2, hT4, hT5⟩
  have hext : ∀ τ (L : M.H τ →ₗ[ℂ] E), (∀ r ∈ Rk τ, ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, L (r.1 x) = r.2 (L x)) →
      ∃ L' ∈ C τ, (∀ r ∈ Rg τ, ∀ x ∈ M.sm τ, L' (r.1 x) = r.2 (L' x)) ∧
        ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, L' x = L x := by
    intro τ L hLk
    obtain ⟨T, hT1, ⟨hT2, hT3⟩, -⟩ := hcw τ L hLk
    refine ⟨T, hT3, ?_, fun x hx => hT1 x hx⟩
    rintro r ⟨g, hg, rfl⟩ x hx
    exact hT2 g hg x ((hsm τ x).1 hx)
  have huniq : ∀ τ, ∀ L ∈ C τ, (∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, L x = 0) → ∀ x ∈ M.sm τ, L x = 0 :=
    fun τ L hL h0 => uniq hHC M τ (hπ τ).withSeminorms hL h0
  have hpostC : ∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ L ∈ C τ', r.2 ∘ₗ L ∈ C τ' := by
    rintro τ τ' - r ((⟨k, -, rfl⟩ | ⟨X, -, rfl⟩) | ⟨g, -, rfl⟩) L hL
    · exact sobBd_comp (hπ τ').withSeminorms hL (π τ k)
    · exact sobBd_comp (hπ τ').withSeminorms hL (dπ τ X)
    · exact sobBd_comp (hπ τ').withSeminorms hL (π τ g)
  have hcomm' : ∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ r' ∈ Rg τ', r.2 ∘ₗ r'.2 = r'.2 ∘ₗ r.2 := by
    rintro τ τ' hne r ((⟨k, hk, rfl⟩ | ⟨X, hX, rfl⟩) | ⟨g, hg, rfl⟩) r' ⟨g', hg', rfl⟩
    · have h := hcomm τ τ' hne k (GlobalTheory.TypeSum.K_le_UJ hk) g' hg'
      ext x
      exact congrArg (fun f : E →L[ℂ] E => f x) h
    · have h := dRep_comm (hπ τ) hX (π τ' g') fun t =>
        hcomm τ' τ hne.symm g' hg' _ (GlobalTheory.TypeSum.exp_mem_UJ hX t)
      ext x
      exact (congrArg (fun f : E →L[ℂ] E => f x) h).symm
    · have h := hcomm τ τ' hne g hg g' hg'
      ext x
      exact congrArg (fun f : E →L[ℂ] E => f x) h
  have h0 : ∀ τ (u : ∀ τ, M.H τ), (∀ τ', τ' ≠ τ → u τ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ') → ∀ r ∈ Rk τ,
      ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ,
      T₀' (Function.update u τ (r.1 x)) = r.2 (T₀' (Function.update u τ x)) := by
    intro τ u _ r hr x hx
    have e : ∀ y : M.H τ, T₀' (Function.update u τ y) = T₀ (Function.update (fun τ' => P τ' (u τ')) τ (P τ y)) :=
      fun y => by
        show T₀ (fun τ' => P τ' (Function.update u τ y τ')) = _
        congr 1
        funext τ'
        exact Function.apply_update (fun τ => P τ) u τ y τ'
    have hr' := hRk τ r hr x hx
    rw [e, e]
    rcases hr with ⟨k, hk, rfl⟩ | ⟨X, hX, rfl⟩
    · have h := hK τ k hk (Function.update (fun τ' => P τ' (u τ')) τ (P τ x)) (P τ (M.σ τ k x))
        (by rw [Function.update_self, hP' τ _ hx, hP' τ _ hr'])
      rw [Function.update_idem] at h
      exact h
    · have h := hL τ X hX (Function.update (fun τ' => P τ' (u τ')) τ (P τ x)) (P τ (dRep (M.σ τ) X x))
        (by rw [Function.update_self, hP' τ _ hx, hP' τ _ hr'])
      rw [Function.update_idem] at h
      exact h
  by_cases hz : ∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, T₀ u = 0
  · refine ⟨0, fun v u _ => (hz u).symm, fun τ g _ v w _ => by simp, fun τ i v => ⟨[], 0, by simp, fun w => by simp⟩⟩
  push_neg at hz
  obtain ⟨u₀, hu₀⟩ := hz

  have hNZ : ∀ τ, ∃ N : M.H τ →ₗ[ℂ] E, N ∈ C τ ∧ IsClosed (N '' {w | SmoothVec (lieSet (M.ε τ)) (M.σ τ) w}) ∧
      ∀ Sl : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ)), (∀ l ∈ Sl, ∀ X ∈ l, X ∈ lieSet (M.ε τ)) →
        ∃ q : Seminorm ℂ E, Continuous q ∧
          ∀ w, SmoothVec (lieSet (M.ε τ)) (M.σ τ) w → sobNorm (M.σ τ) Sl w ≤ q (N w) := by
    intro τ
    let u : ∀ τ, M.H τ := fun τ => (u₀ τ : M.H τ)
    have hLk : ∀ r ∈ Rk τ, ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, T₀'.toLinearMap u τ (r.1 x) = r.2 (T₀'.toLinearMap u τ x) :=
      fun r hr x hx => by
        simp only [MultilinearMap.toLinearMap_apply]
        exact h0 τ u (fun τ' _ => (u₀ τ').2) r hr x hx
    obtain ⟨T, hT1, ⟨-, hT3⟩, hT4, hT5⟩ := hcw τ _ hLk
    refine ⟨T, hT3, hT4, hT5 ⟨u τ, (u₀ τ).2, ?_⟩⟩
    rw [MultilinearMap.toLinearMap_apply, Function.update_eq_self]
    show T₀ (fun τ' => P τ' (u₀ τ' : M.H τ')) ≠ 0
    have : (fun τ' => P τ' (u₀ τ' : M.H τ')) = u₀ := funext fun τ' => hP τ' (u₀ τ')
    rw [this]
    exact hu₀
  have hbs : ∀ τ τ', τ ≠ τ' → ∀ F : M.H τ →ₗ[ℂ] M.H τ' →ₗ[ℂ] E, (∀ w ∈ M.sm τ, F w ∈ C τ') →
      (∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ', F.flip a ∈ C τ) → ∀ b ∈ M.sm τ', F.flip b ∈ C τ := by
    intro τ τ' _ F hF1 hF2 b hb
    obtain ⟨N₁, hN₁C, hN₁cl, hN₁iso⟩ := hNZ τ
    obtain ⟨N₂, hN₂C, -, hN₂iso⟩ := hNZ τ'
    have hp := (hπ τ).withSeminorms
    let j₁ : M.sm τ →ₗ[ℂ] E := N₁ ∘ₗ (M.sm τ).subtype
    let j₂ : M.sm τ' →ₗ[ℂ] E := N₂ ∘ₗ (M.sm τ').subtype
    have hinj : Function.Injective j₁ := by
      refine (injective_iff_map_eq_zero j₁).2 fun x hx => ?_
      obtain ⟨q, -, hq⟩ := hN₁iso [[]] (by simp)
      have h1 := hq x ((hsm τ x).1 x.2)
      have h2 : j₁ x = N₁ x := rfl
      rw [← h2, hx, map_zero] at h1
      have h3 : sobNorm (M.σ τ) [[]] (x : M.H τ) = ‖(x : M.H τ)‖ := by simp [sobNorm]
      rw [h3] at h1
      exact Subtype.ext (norm_le_zero_iff.1 h1)
    have hcl : IsClosed (Set.range j₁) := by
      have e : Set.range j₁ = N₁ '' {w | SmoothVec (lieSet (M.ε τ)) (M.σ τ) w} := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨x, (hsm τ x).1 x.2, rfl⟩
        · rintro ⟨w, hw, rfl⟩
          exact ⟨⟨w, (hsm τ w).2 hw⟩, rfl⟩
      rw [e]
      exact hN₁cl
    let D₂ : Submodule ℂ (M.sm τ') := (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ').comap (M.sm τ').subtype
    have hD : ∀ x, j₂ x ∈ closure (j₂ '' (D₂ : Set (M.sm τ'))) := by
      intro x
      have h := GlobalTheory.T.mem_closure_of_forall_clm_vanish (hπ τ').withSeminorms (D₂.map j₂) (j₂ x) fun f hf =>
        form_zero hHC M τ' (hπ τ').withSeminorms hN₂C f (fun a ha => hf _ ⟨⟨a, hAB τ' ha⟩, ha, rfl⟩) x x.2
      rwa [Submodule.map_coe] at h
    let F' : M.sm τ →ₗ[ℂ] M.sm τ' →ₗ[ℂ] E := F.compl₁₂ (M.sm τ).subtype (M.sm τ').subtype
    have h₂ : ∀ w i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ b, p i (F' w b) ≤ q (j₂ b) := by
      intro w i
      obtain ⟨q, hq, hb⟩ := bound_via hN₂iso (hF1 w w.2) i
      exact ⟨q, hq, fun b => hb b ((hsm τ' b).1 b.2)⟩
    have h₁ : ∀ a ∈ D₂, ∀ i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F' w a) ≤ q (j₁ w) := by
      intro a ha i
      obtain ⟨q, hq, hb⟩ := bound_via hN₁iso (hF2 a ha) i
      exact ⟨q, hq, fun w => hb w ((hsm τ w).1 w.2)⟩
    intro i
    obtain ⟨q, hq, hb'⟩ := GlobalTheory.T.exists_seminorm_bound_of_dense_second_slot hp j₁ j₂ hinj hcl D₂ hD F' h₂ h₁ ⟨b, hb⟩ i
    obtain ⟨Sl, C', hS, hb''⟩ := sobBd_seminorm hp hN₁C q hq
    exact ⟨Sl, C', hS, fun w hw => (hb' ⟨w, (hsm τ w).2 hw⟩).trans (hb'' w hw)⟩
  obtain ⟨Tab, hT1, hT2⟩ := GlobalTheory.T.exists_multilinear_positionwise_extension_of_equivariant (H := fun τ => M.H τ) (fun τ => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ)
    (fun τ => M.sm τ) hAB Rk Rg hRk hRg C hC hext huniq hpostC hcomm' hbs T₀' h0
  have hupd : ∀ (v : M.Vec) τ (w : M.sm τ),
      (fun τ' => ((Function.update v τ w τ' : M.sm τ') : M.H τ')) =
        Function.update (fun τ' => (v τ' : M.H τ')) τ (w : M.H τ) :=
    fun v τ w => funext fun τ' => Function.apply_update (fun τ => ((M.sm τ).subtype : M.sm τ → M.H τ)) v τ w τ'
  refine ⟨Tab.compLinearMap fun τ => (M.sm τ).subtype, ?_, ?_, ?_⟩
  · intro v u hvu
    show Tab (fun τ => (v τ : M.H τ)) = T₀ u
    have e : (fun τ => (v τ : M.H τ)) = fun τ => (u τ : M.H τ) := funext hvu
    rw [e, hT1 _ fun τ => (u τ).2]
    show T₀ (fun τ => P τ (u τ : M.H τ)) = T₀ u
    congr 1
    funext τ
    exact hP τ (u τ)
  · intro τ g hg v w hw
    show Tab (fun τ' => ((Function.update v τ w τ' : M.sm τ') : M.H τ')) = π τ g (Tab fun τ' => (v τ' : M.H τ'))
    rw [hupd, hw]
    have h := (hT2 τ (fun τ' => (v τ' : M.H τ')) fun τ' _ => (v τ').2).2 _ ⟨g, hg, rfl⟩ (v τ) (v τ).2
    rw [Function.update_eq_self] at h
    exact h
  · intro τ i v
    obtain ⟨Sl, C', hS, hb⟩ := (hT2 τ (fun τ' => (v τ' : M.H τ')) fun τ' _ => (v τ').2).1 i
    refine ⟨Sl, C', hS, fun w => ?_⟩
    have h := hb w ((hsm τ w).1 w.2)
    rw [MultilinearMap.toLinearMap_apply] at h
    show p i (Tab (fun τ' => ((Function.update v τ w τ' : M.sm τ') : M.H τ'))) ≤ _
    rw [hupd]
    exact h

end GlobalTheory.FactorExtension
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearGKMapExtendsToSmoothVectorsStatement
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multilinear_gKMap_extends_to_smooth_vectors : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E] (p : ℕ → Seminorm ℂ E) (π dπ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → (E →L[ℂ] E)), (∀ τ, GlobalTheory.SmoothGlob.IsSmoothModRep (M.ε τ) p (π τ) (dπ τ)) → (∀ τ τ', τ ≠ τ' → ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ g' ∈ Formalism.MainNotions.S.UJset (M.ε τ'), (π τ g).comp (π τ' g') = (π τ' g').comp (π τ g)) → ∀ T₀ : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) E, (∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = M.σ τ k (u τ) → T₀ (Function.update u τ w) = π τ k (T₀ u)) → (∀ τ, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = dRep (M.σ τ) X (u τ) → T₀ (Function.update u τ w) = dπ τ X (T₀ u)) → ∃ T : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => M.sm τ) E, (∀ (v : M.Vec) (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M), (∀ τ, (v τ : M.H τ) = u τ) → T v = T₀ u) ∧ (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.σ τ g (v τ) → T (Function.update v τ w) = π τ g (T v)) ∧ ∀ τ (i : ℕ) (v : M.Vec), ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) ∧ ∀ w : M.sm τ, p i (T (Function.update v τ w)) ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w := by
  first | exact @GlobalTheory.FactorExtension.extend_positions | exact GlobalTheory.FactorExtension.extend_positions | (intros; apply GlobalTheory.FactorExtension.extend_positions <;> assumption)
end
