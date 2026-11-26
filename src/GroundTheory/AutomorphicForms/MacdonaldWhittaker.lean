module

public import GroundTheory.AutomorphicForms.MacdonaldFormula
public import GroundTheory.AutomorphicForms.CuspidalSplittingIsotypic
public import GroundTheory.AutomorphicForms.LeviStagesProduct
public import GroundTheory.AutomorphicForms.LeviStagesExact

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.MacdonaldWhittaker
noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra Finset
open scoped ValuativeRel

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem superdiagSum_mem {M : Matrix (Fin n) (Fin n) F}
    (h : ∀ i j : Fin n, (j : ℕ) = i + 1 → M i j ∈ 𝒪[F]) : Whittaker.superdiagSum M ∈ 𝒪[F] := by
  refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
  split_ifs with hij
  · exact h i j hij
  · exact Subring.zero_mem _

theorem psiN_conj_eq_one {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1) {l : Fin n → ℤ}
    (hl : Antitone l) {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    Whittaker.psiN ψ₀ (torusPow F n l * k * torusPow F n (-l)) = 1 := by
  refine hψ₀ _ (superdiagSum_mem fun i j hij => ?_)
  have heq : ((torusPow F n l * k * torusPow F n (-l) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) i j = (GLnLocal.uniformizer F : F) ^ (l i - l j) * k i j := by
    rw [Units.val_mul, Units.val_mul, coe_torusPow, coe_torusPow, mul_diagonal, diagonal_mul,
      Pi.neg_apply, zpow_sub₀ (uniformizer_ne_zero F), _root_.zpow_neg, div_eq_mul_inv]
    ring
  rw [heq]
  have ht : 0 ≤ l i - l j := by
    have := hl (show i ≤ j from Fin.le_def.2 (by omega))
    linarith
  refine Subring.mul_mem _ ?_ (((mem_integralGL_iff F n).1 hk).1 i j)
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le ht
  rw [hm, zpow_natCast]
  exact Subring.pow_mem _ (GLnLocal.uniformizer F).2 m

theorem exists_iwasawa_decomp (g : GL (Fin n) F) :
    ∃ p : GL (Fin n) F × GL (Fin n) F, p.1 ∈ unipotent F n ∧ p.2 ∈ integralGL F n ∧
      g = p.1 * torusPow F n (iwasawaExponent F n g) * p.2 := by
  obtain ⟨u, hu, k, hk, h⟩ := exists_eq_mul_torusPow_iwasawaExponent F n g
  exact ⟨(u, k), hu, hk, h⟩

def iwasawaUnip (g : GL (Fin n) F) : GL (Fin n) F := (exists_iwasawa_decomp g).choose.1

def iwasawaInt (g : GL (Fin n) F) : GL (Fin n) F := (exists_iwasawa_decomp g).choose.2

theorem iwasawaUnip_mem (g : GL (Fin n) F) : iwasawaUnip g ∈ unipotent F n :=
  (exists_iwasawa_decomp g).choose_spec.1

theorem iwasawaInt_mem (g : GL (Fin n) F) : iwasawaInt g ∈ integralGL F n :=
  (exists_iwasawa_decomp g).choose_spec.2.1

theorem eq_iwasawa (g : GL (Fin n) F) :
    g = iwasawaUnip g * torusPow F n (iwasawaExponent F n g) * iwasawaInt g :=
  (exists_iwasawa_decomp g).choose_spec.2.2


variable (ψ₀ : AddChar F ℂ) (z : Fin n → ℂˣ) in
def sphericalWhittaker (g : GL (Fin n) F) : ℂ :=
  if Antitone (iwasawaExponent F n g) then
    Whittaker.psiN ψ₀ (iwasawaUnip g) * halfModulus F (iwasawaExponent F n g) *
      evalAt z (schur (iwasawaExponent F n g))
  else 0

theorem sphericalWhittaker_apply {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (z : Fin n → ℂˣ) {u k : GL (Fin n) F} (hu : u ∈ unipotent F n) (hk : k ∈ integralGL F n)
    (l : Fin n → ℤ) :
    sphericalWhittaker ψ₀ z (u * torusPow F n l * k) =
      if Antitone l then Whittaker.psiN ψ₀ u * halfModulus F l * evalAt z (schur l) else 0 := by
  have hexp : iwasawaExponent F n (u * torusPow F n l * k) = l := iwasawaExponent_eq F n hu hk
  have hu' := iwasawaUnip_mem (u * torusPow F n l * k)
  have hk' := iwasawaInt_mem (u * torusPow F n l * k)
  have heq := eq_iwasawa (u * torusPow F n l * k)
  set u' := iwasawaUnip (u * torusPow F n l * k)
  set k' := iwasawaInt (u * torusPow F n l * k)
  rw [sphericalWhittaker, hexp]
  split_ifs with hl
  swap
  · rfl
  rw [hexp] at heq

  have hv : u⁻¹ * u' = torusPow F n l * (k * k'⁻¹) * torusPow F n (-l) := by
    rw [torusPow_neg]
    have := congrArg (fun g => u⁻¹ * g * k'⁻¹ * (torusPow F n l)⁻¹) heq
    rw [show u⁻¹ * (u * torusPow F n l * k) * k'⁻¹ * (torusPow F n l)⁻¹ =
      torusPow F n l * (k * k'⁻¹) * (torusPow F n l)⁻¹ by group,
      show u⁻¹ * (u' * torusPow F n l * k') * k'⁻¹ * (torusPow F n l)⁻¹ = u⁻¹ * u' by group] at this
    exact this.symm
  have h1 : Whittaker.psiN ψ₀ (u⁻¹ * u') = 1 := by
    rw [hv]
    exact psiN_conj_eq_one hψ₀ hl (mul_mem hk ((integralGL F n).inv_mem hk'))
  have h2 : u' = u * (u⁻¹ * u') := by group
  change Whittaker.psiN ψ₀ u' * halfModulus F l * evalAt z (schur l) = _
  rw [h2, Whittaker.psiN_mul ψ₀ hu ((unipotent F n).mul_mem ((unipotent F n).inv_mem hu) hu'), h1,
    mul_one]

theorem sphericalWhittaker_mul_left {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (z : Fin n → ℂˣ) {v : GL (Fin n) F} (hv : v ∈ unipotent F n) (g : GL (Fin n) F) :
    sphericalWhittaker ψ₀ z (v * g) = Whittaker.psiN ψ₀ v * sphericalWhittaker ψ₀ z g := by
  have hg := eq_iwasawa g
  have hu := iwasawaUnip_mem g
  have hk := iwasawaInt_mem g
  rw [hg, show v * (iwasawaUnip g * torusPow F n (iwasawaExponent F n g) * iwasawaInt g) =
    (v * iwasawaUnip g) * torusPow F n (iwasawaExponent F n g) * iwasawaInt g by group,
    sphericalWhittaker_apply hψ₀ z ((unipotent F n).mul_mem hv hu) hk,
    sphericalWhittaker_apply hψ₀ z hu hk, Whittaker.psiN_mul ψ₀ hv hu]
  split_ifs <;> ring

theorem sphericalWhittaker_mul_right {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (z : Fin n → ℂˣ) (g : GL (Fin n) F) {k₀ : GL (Fin n) F} (hk₀ : k₀ ∈ integralGL F n) :
    sphericalWhittaker ψ₀ z (g * k₀) = sphericalWhittaker ψ₀ z g := by
  have hg := eq_iwasawa g
  have hu := iwasawaUnip_mem g
  have hk := iwasawaInt_mem g
  rw [hg, mul_assoc, sphericalWhittaker_apply hψ₀ z hu (mul_mem hk hk₀),
    sphericalWhittaker_apply hψ₀ z hu hk]

theorem sphericalWhittaker_torusPow {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (z : Fin n → ℂˣ) (l : Fin n → ℤ) :
    sphericalWhittaker ψ₀ z (torusPow F n l) =
      if Antitone l then halfModulus F l * evalAt z (schur l) else 0 := by
  have := sphericalWhittaker_apply hψ₀ z (unipotent F n).one_mem (integralGL F n).one_mem l
  rw [one_mul, mul_one, Whittaker.psiN_one, one_mul] at this
  exact this

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

end Spherical

end GroundTheory.Automorphic
end
end

section -- merged from GroundTheory.AutomorphicForms.CuspidalSplitting
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function Iwasawa

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem modularCharacter_eq_one_of_mem_center {H : Type*} [TopologicalSpace H] [Group H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] {g : H} (hg : g ∈ Subgroup.center H) :
    MeasureTheory.Measure.modularCharacter g = 1 := by
  change MeasureTheory.Measure.modularCharacterFun g = 1
  borelize H
  rw [MeasureTheory.Measure.modularCharacterFun_eq_haarScalarFactor
    MeasureTheory.Measure.haar g]
  have hcomm : (fun x : H => x * g) = (fun x => g * x) :=
    funext fun x => Subgroup.mem_center_iff.1 hg x
  have key : MeasureTheory.Measure.map (fun x : H => x * g)
      (MeasureTheory.Measure.haar : MeasureTheory.Measure H) = MeasureTheory.Measure.haar := by
    rw [hcomm]
    exact MeasureTheory.map_mul_left_eq_self _ g
  calc MeasureTheory.Measure.haarScalarFactor
        (MeasureTheory.Measure.map (fun x : H => x * g)
          (MeasureTheory.Measure.haar : MeasureTheory.Measure H))
        (MeasureTheory.Measure.haar : MeasureTheory.Measure H)
      = MeasureTheory.Measure.haarScalarFactor
          (MeasureTheory.Measure.haar : MeasureTheory.Measure H)
          (MeasureTheory.Measure.haar : MeasureTheory.Measure H) := by congr 1
    _ = 1 := MeasureTheory.Measure.haarScalarFactor_self _


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem center_le_levi {α : Type*} [LinearOrder α] (β : Fin n → α) :
    Subgroup.center (GL (Fin n) F) ≤ levi F n β := by
  intro z hz
  obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz
  rw [mem_levi]
  intro i j hij
  have hij' : i ≠ j := fun h => hij (h ▸ rfl)
  change (z : Matrix (Fin n) (Fin n) F) i j = 0
  rw [← ha, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij']

theorem sqrtModular_of_mem_center {α : Type*} [LinearOrder α] {β : Fin n → α}
    {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    sqrtModular F n β ⟨z, levi_le_blockUpper (center_le_levi β hz)⟩ = 1 := by
  have hc : (⟨z, levi_le_blockUpper (center_le_levi β hz)⟩ : blockUpper F n β) ∈
      Subgroup.center (blockUpper F n β) :=
    Subgroup.mem_center_iff.2 fun p => Subtype.ext (Subgroup.mem_center_iff.1 hz p)
  change ((NNReal.sqrt (MeasureTheory.Measure.modularCharacter _) : ℝ) : ℂ) = 1
  rw [modularCharacter_eq_one_of_mem_center hc]
  simp

theorem hasCentralChar_parabolicInd {α : Type*} [LinearOrder α] {β : Fin n → α}
    {W : Type*} [AddCommGroup W] [Module ℂ W] {τ : Representation ℂ (levi F n β) W}
    {ω : GL (Fin n) F → ℂ}
    (hτ : ∀ z (hz : z ∈ Subgroup.center (GL (Fin n) F)), ∀ w,
      τ ⟨z, center_le_levi β hz⟩ w = ω z • w) :
    HasCentralChar (parabolicInd F n β τ) ω := by
  intro z hz f
  apply Subtype.ext
  funext x
  have hf := ((mem_parabolicIndSpace τ).1 f.2).1 ⟨z, levi_le_blockUpper (center_le_levi β hz)⟩ x
  change (f : GL (Fin n) F → W) (x * z) = ω z • (f : GL (Fin n) F → W) x
  rw [Subgroup.mem_center_iff.1 hz x]
  change (f : GL (Fin n) F → W) (z * x) = _ at hf
  rw [hf, sqrtModular_of_mem_center hz, one_smul, leviProj_of_mem_levi (center_le_levi β hz),
    hτ z hz]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

theorem not_surjective_of_le_parabolicInd [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) {β : Fin n → ℕ} (hβ : ∃ i j, β i ≠ β j) {W : Type*}
    [AddCommGroup W] [Module ℂ W] {τ : Representation ℂ (levi F n β) W}
    {ω : GL (Fin n) F → ℂ} (hωτ : HasCentralChar (parabolicInd F n β τ) ω)
    (A : Subrepresentation (parabolicInd F n β τ))
    (p : Representation.IntertwiningMap A.toRepresentation π) : ¬ Surjective p := by
  intro hp
  obtain ⟨u₀, hu₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have hωπ : HasCentralChar π ω := by
    intro z hz x
    obtain ⟨a, rfl⟩ := hp x
    rw [← Representation.IntertwiningMap.isIntertwining, (hωτ.toRepresentation A) z hz a,
      map_smul]
  obtain ⟨s, hs⟩ := exists_lift_of_isSupercuspidal hπ hsc hωπ
    (isSmooth_toRepresentation (isSmooth_parabolicInd τ) A) (hωτ.toRepresentation A) p hp
    (Representation.IntertwiningMap.id π)
  let Φ := (subrepIncl A).comp s
  have hJ := hsc β hβ
  have h0 : frobeniusParabolic F n β τ hπ Φ = 0 :=
    Representation.IntertwiningMap.ext (LinearMap.ext fun x => by
      rw [Subsingleton.elim x 0, map_zero]
      rfl)
  have hΦ : Φ = 0 := (frobeniusParabolic F n β τ hπ).injective (h0.trans (map_zero _).symm)
  have h1 : p (s u₀) = u₀ := congrArg (fun φ : Representation.IntertwiningMap π π => φ u₀) hs
  have h2 : s u₀ = 0 := Subtype.ext (congrArg (fun φ : Representation.IntertwiningMap π
    (parabolicInd F n β τ) => φ u₀) hΦ)
  rw [h2, map_zero] at h1
  exact hu₀ h1.symm

theorem not_surjective_of_isIrreducible [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) {β : Fin n → ℕ} (hβ : ∃ i j, β i ≠ β j) {W : Type*}
    [AddCommGroup W] [Module ℂ W] {τ : Representation ℂ (levi F n β) W} [τ.IsIrreducible]
    (hτ : IsSmooth τ) (A : Subrepresentation (parabolicInd F n β τ))
    (p : Representation.IntertwiningMap A.toRepresentation π) : ¬ Surjective p := by
  classical
  have hc : ∀ z (hz : z ∈ Subgroup.center (GL (Fin n) F)), ∃ c : ℂ, ∀ w,
      τ ⟨z, center_le_levi β hz⟩ w = c • w := fun z hz =>
    exists_central_character hτ (Subgroup.mem_center_iff.2 fun m =>
      Subtype.ext (Subgroup.mem_center_iff.1 hz m))
  let ω : GL (Fin n) F → ℂ := fun z =>
    if hz : z ∈ Subgroup.center (GL (Fin n) F) then (hc z hz).choose else 0
  have hωτ : ∀ z (hz : z ∈ Subgroup.center (GL (Fin n) F)), ∀ w,
      τ ⟨z, center_le_levi β hz⟩ w = ω z • w := fun z hz w => by
    simp only [ω, dif_pos hz]
    exact (hc z hz).choose_spec w
  exact not_surjective_of_le_parabolicInd hπ hsc hβ (hasCentralChar_parabolicInd hωτ) A p

end Parabolic

end GroundTheory.Automorphic
end
end
