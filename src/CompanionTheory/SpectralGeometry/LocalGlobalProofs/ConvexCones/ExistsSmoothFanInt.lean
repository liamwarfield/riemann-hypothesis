module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPolyhedralCoverBalancedFormsCMField
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VoronoiFanIsPolyhedral
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSmoothPolyhedralFanRefinement

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsIsPosDefOfBasis
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_isPosDef_of_basis {X : Type} [AddCommGroup X] {n : ℕ} (b : Module.Basis (Fin n) ℤ X) :
    ∃ B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, (∀ y z, B₀ y z = B₀ z y) ∧ IsPosDef B₀ := by
  classical
  let B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ := ∑ k, toReal (GlobalTheory.RedTh.sqForm b (Pi.single k 1))
  have hv : ∀ i j, B₀ (b i) (b j) = if i = j then 1 else 0 := fun i j => by
    simp only [B₀, LinearMap.sum_apply, toReal_apply, GlobalTheory.RedTh.sqForm_basis]
    by_cases h : i = j
    · subst h
      simp [Pi.single_apply]
    · simp [Pi.single_apply, h]
  refine ⟨B₀, fun y z => ?_, (isPosDef_iff_basis b B₀).2 fun c hc => ?_⟩
  · simp only [B₀, LinearMap.sum_apply, toReal_apply, GlobalTheory.RedTh.sqForm_apply, mul_comm]
  · simp only [hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hc
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩

theorem hasRedCover_int : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X], HasRedCover (id : ℤ → ℤ) X := by
  intro X _ _ _
  classical
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℤ X = n := ⟨_, rfl⟩
  let b₀ : Module.Basis (Fin n) ℤ X := Module.finBasisOfFinrankEq ℤ X hn
  obtain ⟨B₀, hs₀, hp₀⟩ := exists_isPosDef_of_basis b₀
  obtain ⟨S, hS⟩ := GlobalTheory.SiegelCone.gram_mem_cone n
  refine GlobalTheory.RedTh.hasRedCover_of_fintype (ι := ↥S) _ (fun l => GlobalTheory.RedTh.sqForm b₀ l.1)
    (fun l y z => by simp only [GlobalTheory.RedTh.sqForm_apply, mul_comm])
    (fun l y => by simp only [GlobalTheory.RedTh.sqForm_apply]; exact mul_self_nonneg _) fun B hB => ?_
  obtain ⟨X₁, _, m₁, hproj, r, B₁, hr, hB₁, hp₁, hBr⟩ := hB
  obtain rfl : m₁ = AddCommGroup.toIntModule X₁ := Subsingleton.elim _ _
  have : Module.Finite ℤ X₁ := Module.Finite.of_surjective r hr
  have : Module.Free ℤ X₁ := inferInstance
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property r LinearMap.id hr
  have hrσ : ∀ y, r (σ y) = y := fun y => LinearMap.congr_fun hσ y
  obtain ⟨b, d, d', u, t, hd, -, -, hg, -⟩ :=
    GlobalTheory.RedTh.exists_siegel_split r σ hrσ B₀ hs₀ hp₀ B₁ hB₁.1 hp₁ n hn
  obtain ⟨c, hc, hG⟩ := hS d u hd
  let e : X ≃ₗ[ℤ] X := b₀.equiv b (Equiv.refl _)
  have he : ∀ i, e (b₀ i) = b i := fun i => by simp [e]
  refine ⟨e, fun l => c l.1, fun l => hc _, ?_⟩
  refine b₀.ext fun i => b₀.ext fun j => ?_
  have hl : B (b i) (b j) = ∑ l ∈ S, c l * ((l i : ℝ) * (l j : ℝ)) := by
    rw [hBr, hg, hG]
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply]
  simp only [pullR_apply, LinearEquiv.coe_coe, he, hl, LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul,
    GlobalTheory.RedTh.sqForm_basis]
  rw [← Finset.sum_coe_sort S]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IntegerLatticeDominates
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IntegerLatticeDominates
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.DomZ

open Matrix

def quadOf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, ∑ j, A i j * x i * x j

theorem quadOf_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadOf A x = star x ⬝ᵥ (A *ᵥ x) := by
  simp only [quadOf, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, star_trivial]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem continuous_quadOf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Continuous (quadOf A) := by
  unfold quadOf
  fun_prop

theorem quadOf_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (x : Fin n → ℝ) :
    quadOf A (t • x) = t ^ 2 * quadOf A x := by
  simp only [quadOf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_nat_quadOf_le {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef)
    (R : Matrix (Fin n) (Fin n) ℝ) : ∃ C : ℕ, ∀ x, quadOf R x ≤ C * quadOf P x := by
  have hpos : ∀ x, x ≠ 0 → 0 < quadOf P x := fun x hx => by
    rw [quadOf_eq]
    exact hP.dotProduct_mulVec_pos hx
  have hS : IsCompact (Metric.sphere (0 : Fin n → ℝ) 1) := isCompact_sphere 0 1
  have hne : ∀ u ∈ Metric.sphere (0 : Fin n → ℝ) 1, u ≠ 0 := fun u hu h => by
    simp [h] at hu
  have hc : ContinuousOn (fun u => quadOf R u / quadOf P u) (Metric.sphere (0 : Fin n → ℝ) 1) :=
    (continuous_quadOf R).continuousOn.div (continuous_quadOf P).continuousOn
      fun u hu => (hpos u (hne u hu)).ne'
  obtain ⟨K, hK⟩ := hS.bddAbove_image hc
  refine ⟨⌈K⌉₊, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx
    simp [quadOf]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  obtain ⟨u, hu⟩ : ∃ u, u = ‖x‖⁻¹ • x := ⟨_, rfl⟩
  have hum : u ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    simp [hu, norm_smul, hn]
  have h1 : quadOf R u / quadOf P u ≤ K := hK ⟨u, hum, rfl⟩
  have hpu := hpos u (hne u hum)
  have h2 : quadOf R u ≤ ⌈K⌉₊ * quadOf P u := by
    rw [div_le_iff₀ hpu] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil K) hpu.le)
  have hxu : x = ‖x‖ • u := by simp [hu, smul_smul, hn]
  have eR : ∀ A : Matrix (Fin n) (Fin n) ℝ, quadOf A x = ‖x‖ ^ 2 * quadOf A u := fun A => by
    rw [← quadOf_smul, ← hxu]
  rw [eR, eR]
  calc ‖x‖ ^ 2 * quadOf R u ≤ ‖x‖ ^ 2 * (⌈K⌉₊ * quadOf P u) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = _ := by ring

theorem sum_mul_nonneg {n : ℕ} {A G : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (hG : G.PosSemidef) :
    0 ≤ ∑ i, ∑ j, A i j * G i j := by
  have h := (hA.hadamard hG).dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
  simpa [dotProduct, mulVec, Matrix.hadamard_apply] using h

theorem posSemidef_of_int_nonneg {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ} (hs : G.IsHermitian)
    (h : ∀ v : Fin n → ℤ, 0 ≤ quadOf G fun i => (v i : ℝ)) : G.PosSemidef := by
  have hrat : ∀ w : Fin n → ℚ, 0 ≤ quadOf G fun i => (w i : ℝ) := fun w => by
    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) w
    choose v hv using hc
    have hc0 : (((c : ℤ) : ℝ)) ≠ 0 := by
      exact_mod_cast nonZeroDivisors.ne_zero c.2
    have hv' : ∀ i, (v i : ℚ) = (c : ℤ) * w i := fun i => by
      simpa [Algebra.smul_def] using hv i
    have e : (fun i => (v i : ℝ)) = ((c : ℤ) : ℝ) • fun i => (w i : ℝ) := by
      funext i
      have := congrArg (Rat.cast : ℚ → ℝ) (hv' i)
      simpa using this
    have h1 := h v
    rw [e, quadOf_smul] at h1
    have h2 : 0 < (((c : ℤ) : ℝ)) ^ 2 := by positivity
    exact nonneg_of_mul_nonneg_right h1 h2
  have hdense : DenseRange (fun (w : Fin n → ℚ) (i : Fin n) => (w i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hcl : IsClosed {x : Fin n → ℝ | 0 ≤ quadOf G x} := isClosed_le continuous_const (continuous_quadOf G)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hs fun x => ?_
  rw [← quadOf_eq]
  exact hdense.induction_on (p := fun x => 0 ≤ quadOf G x) x hcl hrat

section Forms

variable {X : Type} [AddCommGroup X] {n : ℕ} (b : Module.Basis (Fin n) ℤ X)

def elemForm (i j : Fin n) : LinearMap.BilinForm ℤ X :=
  (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j) + (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord j) (b.coord i)

theorem elemForm_comm (i j : Fin n) : elemForm b i j = elemForm b j i := add_comm _ _

theorem two_smul_eq {β : LinearMap.BilinForm ℤ X} (hβ : ∀ y z, β y z = β z y) :
    (2 : ℤ) • β = ∑ i, ∑ j, β (b i) (b j) • elemForm b i j := by
  refine b.ext fun k => b.ext fun l => ?_
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
  simp [elemForm, Finsupp.single_apply, mul_add, Finset.sum_add_distrib]
  rw [hβ (b l) (b k)]
  ring

theorem two_mul_map (L : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {β : LinearMap.BilinForm ℤ X}
    (hβ : ∀ y z, β y z = β z y) : 2 * L β = ∑ i, ∑ j, L (elemForm b i j) * β (b i) (b j) := by
  have h := congrArg L (two_smul_eq b hβ)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_sum, smul_eq_mul] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

end Forms

end GlobalTheory.CompanionTheory.Ar.Fan.DomZ

namespace GlobalTheory.CompanionTheory.Ar.Fan

open Matrix DomZ

theorem dominates_of_basis {X : Type} [AddCommGroup X] {n : ℕ} (b : Module.Basis (Fin n) ℤ X) :
    GlobalTheory.PolFan.Dominates (id : ℤ → ℤ) X := by
  intro ℓ m hℓ
  let Q : Matrix (Fin n) (Fin n) ℚ := fun i j => (ℓ (elemForm b i j) : ℚ)
  let P : Matrix (Fin n) (Fin n) ℝ := Q.map (Rat.cast : ℚ → ℝ)
  let R : Matrix (Fin n) (Fin n) ℝ := fun i j => (m (elemForm b i j) : ℝ)
  have hQs : Q.IsSymm := by
    ext i j
    show (ℓ (elemForm b j i) : ℚ) = (ℓ (elemForm b i j) : ℚ)
    rw [elemForm_comm b j i]
  have hQ : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ i, ∑ j, Q i j * v i * v j := fun v hv => by
    let l : X →ₗ[ℤ] ℤ := ∑ i, v i • b.coord i
    have hl : ∀ i, l (b i) = v i := fun i => by simp [l, Finsupp.single_apply]
    have hsym : ∀ y z, GlobalTheory.PolFan.sqForm l y z = GlobalTheory.PolFan.sqForm l z y := fun y z => by
      simp [mul_comm]
    have hne : GlobalTheory.PolFan.sqForm l ≠ 0 := by
      intro h0
      obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
      have h1 := congrArg (fun β : LinearMap.BilinForm ℤ X => β (b k) (b k)) h0
      simp only [GlobalTheory.PolFan.sqForm_apply, hl, LinearMap.zero_apply, mul_self_eq_zero] at h1
      exact hk h1
    have h1 := hℓ (GlobalTheory.PolFan.sqForm l) (mem_balForms_int.2 hsym)
      (fun y => by simpa using mul_self_nonneg (l y)) hne
    have h2 := two_mul_map b ℓ hsym
    simp only [GlobalTheory.PolFan.sqForm_apply, hl] at h2
    have h3 : (0 : ℤ) < ∑ i, ∑ j, ℓ (elemForm b i j) * (v i * v j) := by
      rw [← h2]
      omega
    have h4 : ((∑ i, ∑ j, ℓ (elemForm b i j) * (v i * v j) : ℤ) : ℚ) = ∑ i, ∑ j, Q i j * v i * v j := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [Q]
      ring
    rw [← h4]
    exact_mod_cast h3
  have hP : P.PosDef := posDef_of_int_pos n Q hQs hQ
  obtain ⟨C, hC⟩ := exists_nat_quadOf_le hP R
  refine ⟨C, fun β hβ hp => ?_⟩
  have hβs := mem_balForms_int.1 hβ
  let G : Matrix (Fin n) (Fin n) ℝ := fun i j => (β (b i) (b j) : ℝ)
  have hG : G.PosSemidef := by
    refine posSemidef_of_int_nonneg ?_ fun v => ?_
    · ext i j
      rw [Matrix.conjTranspose_apply, star_trivial]
      show ((β (b j) (b i) : ℤ) : ℝ) = ((β (b i) (b j) : ℤ) : ℝ)
      rw [hβs]
    · have h1 := hp (∑ i, v i • b i)
      have h2 : ((β (∑ i, v i • b i) (∑ i, v i • b i) : ℤ) : ℝ) = quadOf G fun i => (v i : ℝ) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, quadOf, G]
        push_cast
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [← h2]
      exact_mod_cast h1
  have hRs : R.IsHermitian := by
    ext i j
    rw [Matrix.conjTranspose_apply, star_trivial]
    show (m (elemForm b j i) : ℝ) = (m (elemForm b i j) : ℝ)
    rw [elemForm_comm b j i]
  have hA : ((C : ℝ) • P - R).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · exact (hP.1.smul (by simp)).sub hRs
    · rw [← quadOf_eq]
      have e : quadOf ((C : ℝ) • P - R) x = C * quadOf P x - quadOf R x := by
        simp only [quadOf, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
          ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e]
      linarith [hC x]
  have h1 := sum_mul_nonneg hA hG
  have hPij : ∀ i j, P i j = (ℓ (elemForm b i j) : ℝ) := fun i j => by
    show (((ℓ (elemForm b i j) : ℤ) : ℚ) : ℝ) = _
    simp
  have e1 : ∑ i, ∑ j, P i j * G i j = ((2 * ℓ β : ℤ) : ℝ) := by
    rw [two_mul_map b ℓ hβs]
    push_cast
    simp only [hPij, G]
  have e2 : ∑ i, ∑ j, R i j * G i j = ((2 * m β : ℤ) : ℝ) := by
    rw [two_mul_map b m hβs]
    push_cast
    simp only [R, G]
  have e3 : ∑ i, ∑ j, ((C : ℝ) • P - R) i j * G i j
      = C * ∑ i, ∑ j, P i j * G i j - ∑ i, ∑ j, R i j * G i j := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e3, e1, e2] at h1
  have h2 : (2 * m β : ℝ) ≤ C * (2 * ℓ β) := by
    push_cast at h1
    linarith
  have h3 : (m β : ℝ) ≤ C * ℓ β := by linarith
  exact_mod_cast h3

theorem dominates_int : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X],
    GlobalTheory.PolFan.Dominates (id : ℤ → ℤ) X := fun X _ _ _ => dominates_of_basis (Module.finBasis ℤ X)

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IntegerLatticeDominatesStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integer_lattice_dominates : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X], Dominates (id : ℤ → ℤ) X := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.dominates_int | exact GlobalTheory.CompanionTheory.Ar.Fan.dominates_int | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.dominates_int <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CmOrdIntId
set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem cmOrd_int_id : CMOrd ℤ id := CMOrd.int

end GlobalTheory.CompanionTheory.Ar.Fan
end

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem hasRedCover_int_proj (Y : Type) [AddCommGroup Y] [m : Module ℤ Y] [Module.Finite ℤ Y] [Module.Projective ℤ Y] :
    HasRedCover (id : ℤ → ℤ) Y := by
  obtain rfl : m = AddCommGroup.toIntModule Y := Subsingleton.elim _ _
  have : Module.Free ℤ Y := inferInstance
  exact hasRedCover_int Y

theorem dominates_int_proj (Y : Type) [AddCommGroup Y] [m : Module ℤ Y] [Module.Finite ℤ Y] [Module.Projective ℤ Y] :
    GlobalTheory.PolFan.Dominates (id : ℤ → ℤ) Y := by
  obtain rfl : m = AddCommGroup.toIntModule Y := Subsingleton.elim _ _
  have : Module.Free ℤ Y := inferInstance
  exact GlobalTheory.T.integer_lattice_dominates Y

theorem exists_smooth_fan_int : ∀ g : ℕ, ∃ φ : InvFun ℤ, IsPolFan id g φ ∧ NoSelfInt id g φ := by
  intro g
  have hpoly : IsPolyFan (id : ℤ → ℤ) g (vorFun ℤ g) :=
    GlobalTheory.T.voronoi_fan_is_polyhedral ℤ id g g (fun Y _ _ _ _ => hasRedCover_int_proj Y) (by simp)
  have htw : IsTwG (0 : ℤ) (vorFun ℤ g) := fun σ _ n B => baseFun_twist _ _ _ σ n B
  obtain ⟨φ, h₁, h₂, -, -⟩ := GlobalTheory.T.exists_smooth_polyhedral_fan_refinement ℤ id 0 cmOrd_int_id g (vorFun ℤ g)
    (fun Y _ _ _ _ => dominates_int_proj Y) hpoly htw
  exact ⟨φ, h₁, h₂⟩

end GlobalTheory.CompanionTheory.Ar.Fan
