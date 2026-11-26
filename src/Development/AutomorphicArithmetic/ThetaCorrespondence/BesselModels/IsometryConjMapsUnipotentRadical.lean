module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.IsometryConjMapsUnipotentRadical
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.UnipRadConj

theorem conj_mem_unipRad : ∀ {n r : ℕ} {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} {e e' : Matrix (Fin n) (Fin r) ℂ}
    (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = G) (he : Q * e' = e)
    {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ unipRad G e'), Q * u * Qi ∈ unipRad J e := by
  intro n r J G Q Qi e e' h1 h2 hg he u hu
  obtain ⟨hu1, hu2, hu3⟩ := hu
  have hu1' : uᴴ * G * u = G := hu1
  have hw1 : Q * u * Qi - 1 = Q * (u - 1) * Qi := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  have hcol : ∀ i : Fin r, (fun k => e k i) = Q *ᵥ fun k => e' k i := by
    intro i
    rw [← he]
    funext k
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  refine ⟨?_, ?_, ?_⟩
  · show (Q * u * Qi)ᴴ * J * (Q * u * Qi) = J
    calc (Q * u * Qi)ᴴ * J * (Q * u * Qi) = Qiᴴ * (uᴴ * (Qᴴ * J * Q) * u) * Qi := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Qiᴴ * G * Qi := by rw [hg, hu1']
      _ = (Q * Qi)ᴴ * J * (Q * Qi) := by
          rw [← hg, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [h1]; simp
  · intro i
    obtain ⟨a, ha0, ha⟩ := hu2 i
    refine ⟨a, ha0, ?_⟩
    have hq : Q * (u - 1) * Qi * Q = Q * (u - 1) := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]
    rw [hw1, hcol i, Matrix.mulVec_mulVec, hq, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, he]
  · intro x hx
    have hy : (e'ᴴ * G) *ᵥ (Qi *ᵥ x) = 0 := by
      have hm : e'ᴴ * (Qᴴ * J * Q) * Qi = eᴴ * J := by
        rw [← he, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]; rw [h1, Matrix.mul_one]
      rw [Matrix.mulVec_mulVec, ← hg, hm]
      exact hx
    obtain ⟨a, ha⟩ := hu3 _ hy
    refine ⟨a, ?_⟩
    rw [hw1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, he]

end UpperTheory.Lit.Bur.UnipRadConj

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.isometry_conj_maps_unipotentRadical : ∀ {n r : ℕ} {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} {e e' : Matrix (Fin n) (Fin r) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = G) (he : Q * e' = e) {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ unipRad G e'), Q * u * Qi ∈ unipRad J e := by
  first | exact @UpperTheory.Lit.Bur.UnipRadConj.conj_mem_unipRad | exact UpperTheory.Lit.Bur.UnipRadConj.conj_mem_unipRad | (intros; apply UpperTheory.Lit.Bur.UnipRadConj.conj_mem_unipRad <;> assumption)
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.ContragredientConjDefiniteUnitaryIsContIrred
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.BesselContra

theorem isContIrred_contra_conj : ∀ {m : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {J₀ A Ai : Matrix (Fin m) (Fin m) ℂ} (h1 : A * Ai = 1) (h2 : Ai * A = 1) (hA : Aᴴ * J₀ * A = 1) {π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W} (hπ : IsContIrred (Formalism.QuantumDeterminants.UH J₀) π₀), IsContIrred (Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ)) (fun h => ((π₀ (A * hᴴ * Ai)).dualMap : Module.End ℂ (Module.Dual ℂ W))) := by
  intro m W _ _ _ J₀ A Ai h1 h2 hA π₀ hπ
  have hJ : Aiᴴ * Ai = J₀ := by
    calc Aiᴴ * Ai = Aiᴴ * (Aᴴ * J₀ * A) * Ai := by rw [hA, Matrix.mul_one]
      _ = (A * Ai)ᴴ * J₀ * (A * Ai) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = J₀ := by simp [h1]
  have hmem : ∀ h, h ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ) →
      A * hᴴ * Ai ∈ Formalism.QuantumDeterminants.UH J₀ := by
    intro h hh
    have hh' : h * hᴴ = 1 := mul_eq_one_comm.1 (mem_UH_one.1 hh)
    show (A * hᴴ * Ai)ᴴ * J₀ * (A * hᴴ * Ai) = J₀
    calc (A * hᴴ * Ai)ᴴ * J₀ * (A * hᴴ * Ai) = Aiᴴ * h * (Aᴴ * J₀ * A) * hᴴ * Ai := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = Aiᴴ * (h * hᴴ) * Ai := by
          rw [hA]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = J₀ := by rw [hh', Matrix.mul_one, hJ]
  have hadj : ∀ g, g ∈ Formalism.QuantumDeterminants.UH J₀ →
      (Ai * g * A)ᴴ ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ) := by
    intro g hg
    have hg' : gᴴ * J₀ * g = J₀ := hg
    refine mem_UH_one.2 (mul_eq_one_comm.1 ?_)
    rw [conjTranspose_conjTranspose]
    calc (Ai * g * A)ᴴ * (Ai * g * A) = Aᴴ * (gᴴ * (Aiᴴ * Ai) * g) * A := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hJ, hg', hA]
  have hback : ∀ g : Matrix (Fin m) (Fin m) ℂ, A * ((Ai * g * A)ᴴ)ᴴ * Ai = g := by
    intro g
    rw [conjTranspose_conjTranspose]
    calc A * (Ai * g * A) * Ai = (A * Ai) * g * (A * Ai) := by
          simp only [Matrix.mul_assoc]
      _ = g := by simp [h1]
  obtain ⟨⟨hone, hmul⟩, hc, hi⟩ := hπ
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun w l => ?_, fun U hU => ?_⟩
  · have : A * (1 : Matrix (Fin m) (Fin m) ℂ)ᴴ * Ai = 1 := by simp [h1]
    beta_reduce
    rw [this, hone]
    ext l x
    simp
  · have e : A * (a * b)ᴴ * Ai = (A * bᴴ * Ai) * (A * aᴴ * Ai) := by
      calc A * (a * b)ᴴ * Ai = A * bᴴ * (Ai * A) * aᴴ * Ai := by
            rw [h2, conjTranspose_mul]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = (A * bᴴ * Ai) * (A * aᴴ * Ai) := by simp only [Matrix.mul_assoc]
    beta_reduce
    rw [e, hmul _ (hmem b hb) _ (hmem a ha)]
    ext l x
    simp
  · obtain ⟨x, rfl⟩ := (Module.evalEquiv ℂ W).surjective l
    have hφ : Continuous fun h : Matrix (Fin m) (Fin m) ℂ => A * hᴴ * Ai :=
      (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
    exact (hc x w).comp hφ.continuousOn hmem
  · have hs : ∀ g ∈ Formalism.QuantumDeterminants.UH J₀, ∀ v ∈ U.dualCoannihilator,
        π₀ g v ∈ U.dualCoannihilator := fun g hg v hv => by
      rw [Submodule.mem_dualCoannihilator] at hv ⊢
      intro l hl
      have := hv _ (hU _ (hadj g hg) l hl)
      beta_reduce at this
      rw [hback] at this
      simpa using this
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := U)]
    rcases hi _ hs with h | h
    · rw [h]; exact Or.inr Submodule.dualAnnihilator_bot
    · rw [h]; exact Or.inl Submodule.dualAnnihilator_top

end UpperTheory.Lit.Bur.BesselContra

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.contragredient_conj_definiteUnitary_isContIrred : ∀ {m : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {J₀ A Ai : Matrix (Fin m) (Fin m) ℂ} (h1 : A * Ai = 1) (h2 : Ai * A = 1) (hA : Aᴴ * J₀ * A = 1) {π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W} (hπ : IsContIrred (Formalism.QuantumDeterminants.UH J₀) π₀), IsContIrred (Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ)) (fun h => ((π₀ (A * hᴴ * Ai)).dualMap : Module.End ℂ (Module.Dual ℂ W))) := by
  first | exact @UpperTheory.Lit.Bur.BesselContra.isContIrred_contra_conj | exact UpperTheory.Lit.Bur.BesselContra.isContIrred_contra_conj | (intros; apply UpperTheory.Lit.Bur.BesselContra.isContIrred_contra_conj <;> assumption)
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.MemBesselUnipotentRadicalOfMemCoordGroup
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.BesselRadical

theorem mem_unipRad_of_mem_Nset {k r : ℕ} {u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hu : u ∈ Formalism.QuantumDeterminants.Nset k r) : u ∈ unipRad (Formalism.QuantumDeterminants.Hpk k r) (colE k r) := by
  obtain ⟨hU, hcol, hmid⟩ := hu
  have hspan : ∀ y : Fin (2 * r + k + 1) → ℂ, (∀ i : Fin (2 * r + k + 1), r ≤ (i : ℕ) → y i = 0) →
      y = colE k r *ᵥ fun b => y (PI.UpqRep.eI k r b) := by
    intro y hy
    funext i
    simp only [Matrix.mulVec, dotProduct, colE, ite_mul, one_mul, zero_mul]
    by_cases hi : (i : ℕ) < r
    · rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin r)]
      · have h : i = PI.UpqRep.eI k r ⟨i, hi⟩ := Fin.ext rfl
        rw [if_pos h, ← h]
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb (Fin.ext (congrArg Fin.val h).symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [hy i (not_lt.mp hi)]
      symm
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]
      intro h
      apply hi
      rw [h]
      exact b.isLt
  have key : ∀ (x : Fin (2 * r + k + 1) → ℂ) (b : Fin r) (j : Fin (2 * r + k + 1)), (b : ℕ) + j = 2 * r + k →
      (((colE k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r) *ᵥ x) b = x j := by
    intro x b j hbj
    rw [← Matrix.mulVec_mulVec]
    have hc : ∀ w : Fin (2 * r + k + 1) → ℂ, ((colE k r)ᴴ *ᵥ w) b = w (PI.UpqRep.eI k r b) := by
      intro w
      simp [Matrix.mulVec, dotProduct, colE, Matrix.conjTranspose_apply]
    rw [hc]
    simp only [Matrix.mulVec, dotProduct]
    have hb := b.isLt
    rw [Finset.sum_eq_single j]
    · have h1 : Formalism.QuantumDeterminants.Hpk k r (PI.UpqRep.eI k r b) j = 1 := by
        simp [Formalism.QuantumDeterminants.Hpk, PI.UpqRep.eI, hbj, hb]
      rw [h1, one_mul]
    · intro m _ hm
      have hne : (b : ℕ) + m ≠ 2 * r + k := fun h => hm (Fin.ext (by omega))
      have h0 : Formalism.QuantumDeterminants.Hpk k r (PI.UpqRep.eI k r b) m = 0 := by
        simp [Formalism.QuantumDeterminants.Hpk, PI.UpqRep.eI, hne, not_le.mpr hb]
      rw [h0, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine ⟨hU, ?_, ?_⟩
  · intro i
    have hy : ∀ m, ((u - 1) *ᵥ fun m => colE k r m i) m
        = u m (PI.UpqRep.eI k r i) - if m = PI.UpqRep.eI k r i then 1 else 0 := by
      intro m
      simp [Matrix.mulVec, dotProduct, colE, Matrix.sub_apply, Matrix.one_apply, sub_mul]
    refine ⟨fun b => ((u - 1) *ᵥ fun m => colE k r m i) (PI.UpqRep.eI k r b), ?_, hspan _ ?_⟩
    · intro j hij
      show ((u - 1) *ᵥ fun m => colE k r m i) (PI.UpqRep.eI k r j) = 0
      rw [hy]
      exact sub_eq_zero.mpr (hcol i _ hij)
    · intro m hm
      rw [hy]
      exact sub_eq_zero.mpr (hcol i m (le_trans (Nat.le_of_lt i.isLt) hm))
  · intro x hx
    have hxz : ∀ j : Fin (2 * r + k + 1), r + k < (j : ℕ) → x j = 0 := by
      intro j hj
      have hjN := j.isLt
      have hb : 2 * r + k - (j : ℕ) < r := by omega
      have h := key x ⟨2 * r + k - j, hb⟩ j (by show 2 * r + k - (j : ℕ) + j = 2 * r + k; omega)
      rw [← h, hx]
      rfl
    refine ⟨fun b => ((u - 1) *ᵥ x) (PI.UpqRep.eI k r b), hspan _ ?_⟩
    intro i hi
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : (j : ℕ) ≤ r + k
    · have h0 : (u - 1) i j = 0 := by
        rw [Matrix.sub_apply, Matrix.one_apply, sub_eq_zero]
        by_cases hjr : (j : ℕ) < r
        · exact hcol ⟨j, hjr⟩ i (by show (j : ℕ) ≤ i; omega)
        · exact hmid i j (not_lt.mp hjr) hj hi
      rw [h0, zero_mul]
    · rw [hxz j (not_le.mp hj), mul_zero]

end UpperTheory.Lit.Bur.BesselRadical

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.mem_besselUnipotentRadical_of_mem_coordGroup : ∀ {k r : ℕ} {u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hu : u ∈ Formalism.QuantumDeterminants.Nset k r), u ∈ unipRad (Formalism.QuantumDeterminants.Hpk k r) (colE k r) := by
  first | exact @UpperTheory.Lit.Bur.BesselRadical.mem_unipRad_of_mem_Nset | exact UpperTheory.Lit.Bur.BesselRadical.mem_unipRad_of_mem_Nset | (intros; apply UpperTheory.Lit.Bur.BesselRadical.mem_unipRad_of_mem_Nset <;> assumption)
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.ContIrredCompactUnitaryGroupRepIsUnitarizable
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace UpperTheory.Lit.Bur.Unitarize

theorem continuousOn_of_dual {X F : Type} [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] {s : Set X} {f : X → F}
    (h : ∀ l : Module.Dual ℂ F, ContinuousOn (fun x => l (f x)) s) : ContinuousOn f s := by
  let b := Module.finBasis ℂ F
  have e : f = fun x => ∑ i, b.coord i (f x) • b i := by
    funext x
    exact (b.sum_repr (f x)).symm
  rw [e]
  exact continuousOn_finsetSum _ fun i _ => (h (b.coord i)).smul continuousOn_const

theorem exists_invariant_core_of_equiv {G W E : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (e : W ≃ₗ[ℂ] E) (r : G → Module.End ℂ W) (h1 : r 1 = 1) (hm : ∀ a b, r (a * b) = r a * r b)
    (hc : ∀ (w : W) (l : Module.Dual ℂ W), Continuous fun g => l (r g w)) :
    ∃ c : InnerProductSpace.Core ℂ W, ∀ g x y, c.inner (r g x) (r g y) = c.inner x y := by
  let A : G → W → E := fun g x => e (r g⁻¹ x)
  have hA : ∀ x, Continuous fun g => A g x := fun x => by
    rw [← continuousOn_univ]
    refine continuousOn_of_dual fun l => ?_
    have h := hc x (l ∘ₗ (e : W →ₗ[ℂ] E))
    exact (h.comp continuous_inv).continuousOn
  let F : W → W → G → ℂ := fun x y g => ⟪A g x, A g y⟫_ℂ
  have hF : ∀ x y, Continuous (F x y) := fun x y => (hA x).inner (hA y)
  have hI : ∀ x y, Integrable (F x y) μ := fun x y =>
    (hF x y).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hxx : ∀ x, ∫ g, F x x g ∂μ = ((∫ g, ‖A g x‖ ^ 2 ∂μ : ℝ) : ℂ) := fun x => by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [F]
    rw [inner_self_eq_norm_sq_to_K]
    simp
  let core : PreInnerProductSpace.Core ℂ W :=
    { inner := fun x y => ∫ g, F x y g ∂μ
      conj_inner_symm := fun x y => by
        show conj (∫ g, F y x g ∂μ) = ∫ g, F x y g ∂μ
        rw [← integral_conj]
        simp only [F, inner_conj_symm]
      re_inner_nonneg := fun x => by
        show 0 ≤ RCLike.re (∫ g, F x x g ∂μ)
        rw [hxx]
        simpa using integral_nonneg fun g => by positivity
      add_left := fun x y z => by
        show ∫ g, F (x + y) z g ∂μ = ∫ g, F x z g ∂μ + ∫ g, F y z g ∂μ
        rw [← integral_add (hI x z) (hI y z)]
        simp only [F, A, map_add (f := _), inner_add_left]
      smul_left := fun x y a => by
        show ∫ g, F (a • x) y g ∂μ = conj a * ∫ g, F x y g ∂μ
        rw [← integral_const_mul]
        simp only [F, A, map_smul, inner_smul_left] }
  refine ⟨{ core with definite := fun x hx => ?_ }, fun h x y => ?_⟩
  · by_contra hx0
    have hpos := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ)
      (f := fun g => ‖A g x‖ ^ 2) (x := 1) ((hA x).norm.pow 2) (HasCompactSupport.of_compactSpace _)
      (fun g => by positivity) (by simpa [A, h1] using hx0)
    have h0 : ∫ g, F x x g ∂μ = 0 := hx
    rw [hxx] at h0
    exact hpos.ne' (by exact_mod_cast h0)
  · show ∫ g, F (r h x) (r h y) g ∂μ = ∫ g, F x y g ∂μ
    rw [← integral_mul_left_eq_self (F x y) h⁻¹]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp [F, A, _root_.mul_inv_rev, hm]

theorem exists_invariant_core {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (r : G → Module.End ℂ W) (h1 : r 1 = 1) (hm : ∀ a b, r (a * b) = r a * r b)
    (hc : ∀ (w : W) (l : Module.Dual ℂ W), Continuous fun g => l (r g w)) :
    ∃ c : InnerProductSpace.Core ℂ W, ∀ g x y, c.inner (r g x) (r g y) = c.inner x y :=
  exists_invariant_core_of_equiv μ
    (LinearEquiv.ofFinrankEq W (EuclideanSpace ℂ (Fin (Module.finrank ℂ W))) (by simp)) r h1 hm hc

theorem compactSpace_UJ_allPos (k : ℕ) : CompactSpace (PI.UpqRep.UJ (PI.UpqRep.allPos k)) := by
  have hemb := PI.UpqRep.isClosedEmbeddingMatrix k (PI.UpqRep.allPos k)
  rw [← isCompact_univ_iff, hemb.1.isEmbedding.isCompact_iff, Set.image_univ, hemb.2]
  have hc : IsCompact (Set.pi Set.univ fun _ : Fin k => Set.pi Set.univ fun _ : Fin k => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine IsCompact.of_isClosed_subset (X := Matrix (Fin k) (Fin k) ℂ) hc (hemb.2 ▸ hemb.1.isClosed_range) ?_
  intro g hg i _ j _
  have hu : g ∈ Matrix.unitaryGroup (Fin k) ℂ :=
    Matrix.mem_unitaryGroup_iff'.2 (PI.HwUniqW.mem_UJset_allPos.1 hg)
  simpa using entry_norm_bound_of_unitary hu i j

theorem unitarize : ∀ {k : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {π : Matrix (Fin k) (Fin k) ℂ → Module.End ℂ W} (hπ : IsContIrred (Formalism.QuantumDeterminants.UH 1) π), ∃ (Wp : Type) (_ : NormedAddCommGroup Wp) (_ : InnerProductSpace ℂ Wp) (_ : FiniteDimensional ℂ Wp) (ρ : Matrix (Fin k) (Fin k) ℂ → (Wp →L[ℂ] Wp)) (T : W ≃ₗ[ℂ] Wp), PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) ρ ∧ (∀ h ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin k) (Fin k) ℂ), ∀ w, T (π h w) = ρ h (T w)) ∧ ∀ S : Submodule ℂ Wp, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤ := by
  intro k W _ _ _ π hπ
  obtain ⟨⟨h1, hm⟩, hc, hi⟩ := hπ
  have hset : PI.UpqRep.UJset (PI.UpqRep.allPos k) = Formalism.QuantumDeterminants.UH (1 : Matrix (Fin k) (Fin k) ℂ) :=
    Set.ext fun h => PI.HwUniqW.mem_UJset_allPos.trans GlobalTheory.BesselMapOne.mem_UH_one.symm
  rw [hset]
  have hmem : ∀ g : PI.UpqRep.UJ (PI.UpqRep.allPos k), PI.UpqRep.umat g ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin k) (Fin k) ℂ) :=
    fun g => hset ▸ g.2
  have hlift : ∀ g ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin k) (Fin k) ℂ), ∃ u : PI.UpqRep.UJ (PI.UpqRep.allPos k),
      PI.UpqRep.umat u = g := fun g hg => by
    have hg' : g ∈ Set.range (PI.UpqRep.coeMatrixAlt (PI.UpqRep.allPos k)) := by
      rw [PI.UpqRep.range_coeMatrix]
      exact hset.ge hg
    exact hg'
  haveI := compactSpace_UJ_allPos k
  obtain ⟨c, hinv⟩ := exists_invariant_core (PI.UpqRep.muG (PI.UpqRep.allPos k))
    (fun g => π (PI.UpqRep.umat g)) h1 (fun a b => hm _ (hmem a) _ (hmem b))
    (fun w l => (hc w l).comp_continuous (PI.UpqRep.continuous_coeMatrix _) hmem)
  letI : NormedAddCommGroup W := @InnerProductSpace.Core.toNormedAddCommGroup ℂ W _ _ _ c
  letI : InnerProductSpace ℂ W := InnerProductSpace.ofCore c.toCore
  refine ⟨W, inferInstance, inferInstance, ‹_›, fun g => LinearMap.toContinuousLinearMap (π g), LinearEquiv.refl ℂ W, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · ext v
    simp [h1]
  · intro a ha b hb
    ext v
    simp [hm a ha b hb]
  · intro g hg v
    obtain ⟨u, rfl⟩ := hlift g hg
    have := hinv u v v
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) v]
    exact congrArg (fun z : ℂ => Real.sqrt (RCLike.re z)) this
  · intro v
    exact continuousOn_of_dual fun l => hc v l
  · intro h _ w
    rfl
  · intro S hS
    exact hi S hS

end UpperTheory.Lit.Bur.Unitarize

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.contIrred_compactUnitaryGroup_rep_isUnitarizable : ∀ {k : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {π : Matrix (Fin k) (Fin k) ℂ → Module.End ℂ W} (hπ : IsContIrred (Formalism.QuantumDeterminants.UH 1) π), ∃ (Wp : Type) (_ : NormedAddCommGroup Wp) (_ : InnerProductSpace ℂ Wp) (_ : FiniteDimensional ℂ Wp) (ρ : Matrix (Fin k) (Fin k) ℂ → (Wp →L[ℂ] Wp)) (T : W ≃ₗ[ℂ] Wp), PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) ρ ∧ (∀ h ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin k) (Fin k) ℂ), ∀ w, T (π h w) = ρ h (T w)) ∧ ∀ S : Submodule ℂ Wp, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤ := by
  first | exact @UpperTheory.Lit.Bur.Unitarize.unitarize | exact UpperTheory.Lit.Bur.Unitarize.unitarize | (intros; apply UpperTheory.Lit.Bur.Unitarize.unitarize <;> assumption)
end
end
