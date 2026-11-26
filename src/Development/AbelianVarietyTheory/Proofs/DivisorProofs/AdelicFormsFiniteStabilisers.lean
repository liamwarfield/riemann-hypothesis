module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLattice
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HermFormDiagonalEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InnerClassSum


open MeasureTheory IsDedekindDomain NumberField Matrix in
open scoped TensorProduct InnerProductSpace Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.InnerClassSum.finite_stab_of_measure {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ K : Subgroup G) [Countable Γ] {𝓖 : Set G}
    (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (h0 : ν K ≠ 0) (h1 : ν K ≠ ⊤) (a : G) :
    {γ : Γ | a⁻¹ * (γ : G) * a ∈ K}.Finite := by
  set S := {γ : Γ | a⁻¹ * (γ : G) * a ∈ K} with hS_def
  set T : Set G := (fun y => a⁻¹ * y) ⁻¹' (K : Set G) with hT_def
  have hT : ν T = ν K := measure_preimage_mul ν a⁻¹ K
  have hsum := h𝓖.measure_eq_tsum' T
  have hδT : ∀ δ ∈ S, δ • T = T := by
    intro δ hδ
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [hT_def, Set.mem_preimage, SetLike.mem_coe, Subgroup.smul_def, smul_eq_mul,
      Subgroup.coe_inv]
    have hk : a⁻¹ * (δ : G)⁻¹ * a ∈ K := by
      have := K.inv_mem hδ
      simpa [mul_assoc] using this
    constructor
    · intro hx
      have := K.mul_mem (K.inv_mem hk) hx
      simpa [mul_assoc] using this
    · intro hx
      have := K.mul_mem hk hx
      simpa [mul_assoc] using this
  have hinv : ∀ δ ∈ S, ∀ γ : Γ, ν (T ∩ (δ * γ) • 𝓖) = ν (T ∩ γ • 𝓖) := by
    intro δ hδ γ
    rw [← measure_smul ν δ (T ∩ γ • 𝓖), Set.smul_set_inter, hδT δ hδ, mul_smul]
  by_contra hinf
  obtain ⟨γ0, hγ0⟩ : ∃ γ0 : Γ, ν (T ∩ γ0 • 𝓖) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply h0
    rw [← hT, hsum]
    simp [hall]
  have hle := ENNReal.tsum_comp_le_tsum_of_injective (f := fun δ : S => (δ : Γ) * γ0)
    (fun x y hxy => Subtype.ext (mul_right_cancel hxy)) (fun γ : Γ => ν (T ∩ γ • 𝓖))
  have : Infinite S := Set.infinite_coe_iff.2 hinf
  have htop : ∑' δ : S, ν (T ∩ ((δ : Γ) * γ0) • 𝓖) = ⊤ := by
    rw [tsum_congr (fun δ : S => hinv δ δ.2 γ0)]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hγ0
  rw [htop, ← hsum, hT] at hle
  exact h1 (top_le_iff.1 hle)


open MeasureTheory IsDedekindDomain NumberField Matrix in
open scoped TensorProduct InnerProductSpace Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.InnerClassSum.integral_inner_eq_adInner {G H W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ν : Measure G)
    [ν.IsMulLeftInvariant]
    (π : G →* H) (hπ : Function.Surjective π) (Γ : Subgroup G) [Countable Γ] {𝓖 : Set G}
    (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (J : Subgroup H) (ho : IsOpen (J.comap π : Set G))
    (h1 : ν (J.comap π) = 1)
    (ρ : G →* Module.End ℂ W) (hρ : ∀ h x y, inner ℂ (ρ h x) (ρ h y) = inner ℂ x y) (χ : J →* ℂˣ)
    (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1) {I : Type} [Fintype I] (y : I → H)
    (hy : _root_.Formalism.IndefR.Bridge.IsReps (π.comp Γ.subtype) J y) :
    (∀ i, Finite (_root_.Formalism.IndefR.Bridge.stab (π.comp Γ.subtype) J (y i))) ∧
      ∀ f ∈ _root_.Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ,
      ∀ f' ∈ _root_.Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ,
        IntegrableOn (fun h => inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f' (π h)))) 𝓖 ν ∧
        ∫ h in 𝓖, inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f' (π h))) ∂ν =
          _root_.Formalism.IndefR.Bridge.adInner (π.comp Γ.subtype) J y f f' := by
  set K : Subgroup G := J.comap π with hK_def
  choose a ha using fun i => hπ (y i)
  have hmem : ∀ i (γ : Γ), γ ∈ _root_.Formalism.IndefR.Bridge.stab (π.comp Γ.subtype) J (y i) ↔ (a i)⁻¹ * (γ : G) * a i ∈ K := by
    intro i γ
    unfold _root_.Formalism.IndefR.Bridge.stab
    simp [hK_def, Subgroup.mem_comap, MulAut.conj_apply, ← ha i, map_mul, map_inv]
  have hK0 : ν K ≠ 0 := by rw [h1]; exact one_ne_zero
  have hKt : ν K ≠ ⊤ := by rw [h1]; exact ENNReal.one_ne_top
  have hfin : ∀ i, {γ : Γ | (a i)⁻¹ * (γ : G) * a i ∈ K}.Finite := fun i =>
    _root_.GlobalTheory.InnerClassSum.finite_stab_of_measure ν Γ K h𝓖 hK0 hKt (a i)
  refine ⟨fun i => ((hfin i).subset fun γ hγ => (hmem i γ).1 hγ).to_subtype, ?_⟩
  intro f hf f' hf'
  have hf0 : ∀ (γ : Γ) (h : H) (k : J), f (π γ * h * k) = (χ k : ℂ) • ρ γ (f h) := by
    unfold _root_.Formalism.IndefR.Bridge.AdForms at hf
    exact hf
  have hf0' : ∀ (γ : Γ) (h : H) (k : J), f' (π γ * h * k) = (χ k : ℂ) • ρ γ (f' h) := by
    unfold _root_.Formalism.IndefR.Bridge.AdForms at hf'
    exact hf'
  set Fψ : G → ℂ := fun h => inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f' (π h))) with hFψ
  have hFψ' : ∀ h, Fψ h = inner ℂ (f (π h)) (f' (π h)) := fun h => hρ _ _ _
  have hleft : ∀ γ ∈ Γ, ∀ x : G, Fψ (γ * x) = Fψ x := by
    intro γ hγ x
    have e := hf0 ⟨γ, hγ⟩ (π x) 1
    have e' := hf0' ⟨γ, hγ⟩ (π x) 1
    simp only [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at e e'
    rw [hFψ', hFψ', map_mul, e, e', hρ]
  have hright : ∀ k ∈ K, ∀ x : G, Fψ (x * k) = Fψ x := by
    intro k hk x
    have e := hf0 1 (π x) ⟨π k, hk⟩
    have e' := hf0' 1 (π x) ⟨π k, hk⟩
    simp only [OneMemClass.coe_one, map_one, one_mul, Module.End.one_apply] at e e'
    rw [hFψ', hFψ', map_mul, e, e', inner_smul_left, inner_smul_right, ← mul_assoc,
      Complex.conj_mul', hχ, Complex.ofReal_one, one_pow, one_mul]
  have hreps : ∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a i * k := by
    intro x
    obtain ⟨i, ⟨γ, k, hk⟩, huniq⟩ := hy (π x)
    refine ⟨i, ⟨γ, γ.2, (a i)⁻¹ * (γ : G)⁻¹ * x, ?_, by group⟩, ?_⟩
    · change π ((a i)⁻¹ * (γ : G)⁻¹ * x) ∈ J
      have hk' : π x = π γ * y i * k := hk
      rw [map_mul, map_mul, map_inv, map_inv, ha i, hk']
      simpa [mul_assoc] using k.2
    · rintro j ⟨γ', hγ', k', hk', hx⟩
      refine huniq j ⟨⟨γ', hγ'⟩, ⟨π k', hk'⟩, ?_⟩
      change π x = π γ' * y j * π k'
      rw [hx, map_mul, map_mul, ha j]
  have hmain := _root_.GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset G ν Γ K 𝓖 h𝓖 ho hKt I a hreps
    (fun i => by
      have := (hfin i).image (fun γ : Γ => (γ : G))
      refine this.subset ?_
      rintro z ⟨hz, hzK⟩
      exact ⟨⟨z, hz⟩, hzK, rfl⟩) Fψ hleft hright
  obtain ⟨-, hint, heq⟩ := hmain
  refine ⟨hint, ?_⟩
  change ∫ h in 𝓖, Fψ h ∂ν = _
  rw [heq, h1]
  unfold _root_.Formalism.IndefR.Bridge.adInner
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcard : {γ | γ ∈ Γ ∧ (a i)⁻¹ * γ * a i ∈ K}.ncard =
      Nat.card (_root_.Formalism.IndefR.Bridge.stab (π.comp Γ.subtype) J (y i)) := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr
      { toFun := fun z => ⟨⟨z.1, z.2.1⟩, (hmem i _).2 z.2.2⟩
        invFun := fun γ => ⟨γ.1.1, γ.1.2, (hmem i _).1 γ.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hFψ', ha i, hcard]

open MeasureTheory IsDedekindDomain NumberField Matrix in
open scoped TensorProduct InnerProductSpace Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
private lemma norm_character_eq_one_of_finite {A : Type} [Group A] [Finite A] (φ : A →* ℂˣ) (a : A) :
    ‖((φ a : ℂˣ) : ℂ)‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := Nat.card A) _ Nat.card_pos.ne'
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]


open MeasureTheory IsDedekindDomain NumberField Matrix in
open scoped TensorProduct InnerProductSpace Pointwise in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.InnerClassSum.norm_levFn {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] _root_.Formalism.L2.Herm.Af F)) (L : _root_.Formalism.L2.DIV.LevDat E ℂ n) (x : GL (Fin n) (E ⊗[F] _root_.Formalism.L2.Herm.Af F)) :
    ‖(_root_.Formalism.L2.DIV.levFn β L x : ℂ)‖ = 1 := by
  unfold _root_.Formalism.L2.DIV.levFn _root_.Formalism.L2.DIV.ext1
  simp only [Units.val_mul, Units.coe_prod, norm_mul, norm_prod, norm_character_eq_one_of_finite,
    Finset.prod_const_one, mul_one]
  split_ifs
  · exact norm_character_eq_one_of_finite _ _
  · simp

end GlobalTheory.InnerClassSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleDecomposableCompEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleDecomposableCompEquiv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.CuspMult

section
variable {H H' : Type} [Group H] [Group H'] {X : Type} [AddCommGroup X] [Module ℂ X]

def subrepCompIso (ρ : Representation ℂ H' X) (φ : H ≃* H') :
    Subrepresentation (ρ.comp φ.toMonoidHom : Representation ℂ H X) ≃o Subrepresentation ρ where
  toFun U := ⟨U.toSubmodule, fun g v hv => by
    have h := U.apply_mem_toSubmodule (φ.symm g) hv
    simpa using h⟩
  invFun U := ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (φ g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp_mulEquiv (ρ : Representation ℂ H' X) (φ : H ≃* H') (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp φ.toMonoidHom : Representation ℂ H X) := by
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  exact (subrepCompIso ρ φ).isSimpleOrder

theorem isAdmissible_comp_equiv [TopologicalSpace H] [TopologicalSpace H'] (ρ : Representation ℂ H' X) (Φ : H ≃ₜ* H')
    (h : GlobalTheory.PRep.IsAdmissible ρ) :
    GlobalTheory.PRep.IsAdmissible (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X) := by
  refine ⟨fun v => (h.1 v).preimage Φ.continuous, fun K hKo hKc => ?_⟩
  have e : GlobalTheory.PRep.fixed (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X) K =
      GlobalTheory.PRep.fixed ρ (K.map Φ.toMulEquiv.toMonoidHom) := by
    ext v
    constructor
    · rintro hv ⟨_, g, hg, rfl⟩
      exact hv ⟨g, hg⟩
    · intro hv g
      exact hv ⟨_, g.1, g.2, rfl⟩
  rw [e]
  exact h.2 _ (Φ.toHomeomorph.isOpenMap _ hKo) (hKc.image Φ.continuous)

end

theorem isDecomp_comp_equiv : ∀ (H H' : Type) [Group H] [TopologicalSpace H] [Group H'] [TopologicalSpace H'] (X : Type)
    [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H' X) (C : Submodule ℂ X) (Φ : H ≃ₜ* H'),
    IsDecomp ρ C → IsDecomp (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X) C := by
  intro H H' _ _ _ _ X _ _ ρ C Φ h x hx ho
  have ho' : IsOpen {g : H' | ρ g x = x} := by
    have := ho.preimage Φ.symm.continuous
    convert this using 1
    ext g
    show ρ g x = x ↔ ρ (Φ (Φ.symm g)) x = x
    rw [Φ.apply_symm_apply]
  have hm := h x hx ho'
  refine (?_ : irrSum ρ C ≤ irrSum (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X) C) hm
  refine iSup₂_le fun U hU => ?_
  refine le_iSup₂_of_le (f := fun (U : Subrepresentation (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X))
    (_ : U.toSubmodule ≤ C ∧ U.toRepresentation.IsIrreducible ∧ GlobalTheory.PRep.IsAdmissible U.toRepresentation) => U.toSubmodule)
    ((subrepCompIso ρ Φ.toMulEquiv).symm U) ⟨hU.1, ?_, ?_⟩ le_rfl
  · exact isIrreducible_comp_mulEquiv U.toRepresentation Φ.toMulEquiv hU.2.1
  · exact isAdmissible_comp_equiv U.toRepresentation Φ hU.2.2

end GlobalTheory.CuspMult
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleDecomposableCompEquivStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibleAdmissibleDecomposable_comp_equiv : ∀ (H H' : Type) [Group H] [TopologicalSpace H] [Group H'] [TopologicalSpace H'] (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H' X) (C : Submodule ℂ X) (Φ : H ≃ₜ* H'), IsDecomp ρ C → IsDecomp (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X) C := by
  first | exact @GlobalTheory.CuspMult.isDecomp_comp_equiv | exact GlobalTheory.CuspMult.isDecomp_comp_equiv | (intros; apply GlobalTheory.CuspMult.isDecomp_comp_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulConjSelf
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilInner

theorem integral_mul_conj_self {G : Type} [MeasurableSpace G] (ν : Measure G) {f : G → ℂ} (hf : Measurable f) :
    ∫ w, f w * conj (f w) ∂ν = ((∫⁻ w, ‖f w‖ₑ ^ 2 ∂ν).toReal : ℂ) := by
  have e : ∀ w, f w * conj (f w) = ((‖f w‖ ^ 2 : ℝ) : ℂ) := fun w => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [e]
  rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => by positivity)
    (hf.norm.pow_const 2).aestronglyMeasurable]
  congr 2
  refine lintegral_congr fun w => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem integrable_mul_conj {G : Type} [MeasurableSpace G] (ν : Measure G) [IsFiniteMeasure ν] {f g : G → ℂ}
    (hf : Measurable f) (hg : Measurable g) (bf : ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) (bg : ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C) :
    Integrable (fun w => f w * conj (g w)) ν := by
  obtain ⟨C, hC⟩ := bf
  obtain ⟨C', hC'⟩ := bg
  refine Integrable.of_bound (hf.mul (Complex.continuous_conj.measurable.comp hg)).aestronglyMeasurable (C * C')
    (Filter.Eventually.of_forall fun w => ?_)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hC w) (hC' w) (norm_nonneg _) ((norm_nonneg _).trans (hC w))

theorem inner_eq_of_meanSquare {G : Type} [MeasurableSpace G] (ν : Measure G) [IsFiniteMeasure ν]
    (P : (G → ℂ) → Prop) (hadd : ∀ f g, P f → P g → P (f + g)) (hsmul : ∀ (c : ℂ) f, P f → P (c • f))
    (hm : ∀ f, P f → Measurable f) (hb : ∀ f, P f → ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C)
    (A : Module.End ℂ (G → ℂ)) (hA : ∀ f, P f → P (A f))
    (hu : ∀ f, P f → ∫⁻ w, ‖A f w‖ₑ ^ 2 ∂ν = ∫⁻ w, ‖f w‖ₑ ^ 2 ∂ν) {f g : G → ℂ} (hf : P f) (hg : P g) :
    ∫ w, A f w * conj (A g w) ∂ν = ∫ w, f w * conj (g w) ∂ν := by
  have hI : ∀ f g, P f → P g → Integrable (fun w => f w * conj (g w)) ν := fun f g hf hg =>
    integrable_mul_conj ν (hm f hf) (hm g hg) (hb f hf) (hb g hg)
  have hN : ∀ f, P f → ∫ w, A f w * conj (A f w) ∂ν = ∫ w, f w * conj (f w) ∂ν := fun f hf => by
    rw [integral_mul_conj_self ν (hm _ (hA f hf)), integral_mul_conj_self ν (hm f hf), hu f hf]
  have ex : ∀ (c : ℂ) f g, P f → P g → ∫ w, (f + c • g) w * conj ((f + c • g) w) ∂ν =
      ∫ w, f w * conj (f w) ∂ν + conj c * ∫ w, f w * conj (g w) ∂ν + c * ∫ w, g w * conj (f w) ∂ν +
        c * conj c * ∫ w, g w * conj (g w) ∂ν := by
    intro c f g hf hg
    have i1 := hI f f hf hf
    have i2 := (hI f g hf hg).const_mul (conj c)
    have i3 := (hI g f hg hf).const_mul c
    have i4 := (hI g g hg hg).const_mul (c * conj c)
    have i12 : Integrable (fun w => f w * conj (f w) + conj c * (f w * conj (g w))) ν := i1.add i2
    have i13 : Integrable (fun w => f w * conj (f w) + conj c * (f w * conj (g w)) + c * (g w * conj (f w))) ν :=
      i12.add i3
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_add i1 i2,
      ← integral_add i12 i3, ← integral_add i13 i4]
    congr 1
    funext w
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
    ring
  have key : ∀ c : ℂ, conj c * ∫ w, A f w * conj (A g w) ∂ν + c * ∫ w, A g w * conj (A f w) ∂ν =
      conj c * ∫ w, f w * conj (g w) ∂ν + c * ∫ w, g w * conj (f w) ∂ν := by
    intro c
    have h := hN _ (hadd f _ hf (hsmul c g hg))
    rw [map_add (f := _), map_smul, ex c _ _ (hA f hf) (hA g hg), ex c f g hf hg, hN f hf, hN g hg] at h
    linear_combination h
  have h1 := key 1
  have h2 := key I
  rw [map_one] at h1
  rw [Complex.conj_I] at h2
  linear_combination (1 / 2 : ℂ) * h1 + (I / 2) * h2 + (1 / 2 : ℂ) *
    (∫ w, A f w * conj (A g w) ∂ν - ∫ w, A g w * conj (A f w) ∂ν - ∫ w, f w * conj (g w) ∂ν +
      ∫ w, g w * conj (f w) ∂ν) * Complex.I_mul_I

theorem om_inner : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∀ p f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → ∫ w in 𝓕, om p f w * conj (om p f' w) ∂μ = ∫ w in 𝓕, f w * conj (f' w) ∂μ := by
  intro D ψ V W χV χW om hom μ 𝓕 hc p f f' hf hf'
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hc.2.2]; exact ENNReal.one_lt_top⟩
  exact inner_eq_of_meanSquare (μ.restrict 𝓕) (IsThetaFunO ψ V W) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
    (fun c _ => GlobalTheory.OrientedHeis.theta_smul c) (fun _ h => h.cont.measurable)
    (fun _ h => GlobalTheory.OrientedHeis.theta_bounded hom.std h) (om p) (hom.om_pres p)
    (hom.om_unit μ 𝓕 hc.1 hc.2.1 p) hf hf'

end GlobalTheory.WeilInner
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinTensAlgebraMap
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacSign

open GlobalTheory.LatVac

variable {D : D7} {S T : HSp D}

def sgnW (ψ : AddChar (AF D.host.F) ℂ) (w : AE D) (u : WO S T) : ℂ := ψ (symplOH S T u (w • u))

theorem symplOH_self (u : WO S T) : symplOH S T u u = 0 := by
  have h := SplitScalar.symplOH_skew S T u u
  have h2 : symplO S T u u = 0 := by
    rw [← SplitScalar.symplOH_add_self]
    exact add_eq_zero_iff_eq_neg.2 h
  rw [symplOH, h2, mul_zero]

theorem symplOH_smul (a : AE D) (x y : WO S T) : symplOH S T (a • x) y = symplOH S T x (cA D a • y) := by
  rw [symplOH, symplOH, SplitScalar.symplO_smul]

theorem symplOH_quad {w : AE D} (hw : w + cA D w = 1) (u u' : WO S T) :
    symplOH S T u u' + symplOH S T (u + u') (w • (u + u')) =
      symplOH S T u (w • u) + symplOH S T u' (w • u') + symplO S T u (w • u') := by
  have h1 : symplOH S T u u' = symplOH S T u (w • u') + symplOH S T u (cA D w • u') := by
    rw [← SplitScalar.symplOH_add_right, ← add_smul, hw, one_smul]
  have h2 : symplOH S T u' (w • u) = -symplOH S T u (cA D w • u') := by
    rw [SplitScalar.symplOH_skew, symplOH_smul]
  rw [smul_add, SplitScalar.symplOH_add_left, SplitScalar.symplOH_add_right, SplitScalar.symplOH_add_right, h1, h2,
    ← SplitScalar.symplOH_add_self]
  ring

theorem sgnW_add (ψ : AddChar (AF D.host.F) ℂ) {w : AE D} (hw : w + cA D w = 1) {u u' : WO S T}
    (h : ψ (symplO S T u (w • u')) = 1) :
    ψ (symplOH S T u u') * sgnW ψ w (u + u') = sgnW ψ w u * sgnW ψ w u' := by
  rw [sgnW, ← ψ.map_add_eq_mul, symplOH_quad hw, ψ.map_add_eq_mul, ψ.map_add_eq_mul, h, mul_one, sgnW, sgnW]

theorem sgnW_zero (ψ : AddChar (AF D.host.F) ℂ) (w : AE D) : sgnW ψ w (0 : WO S T) = 1 := by
  rw [sgnW, symplOH, SplitScalar.symplO_zero_left, mul_zero, ψ.map_zero_eq_one]

theorem char_ne_zero {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := fun h => by
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem sgnW_half (ψ : AddChar (AF D.host.F) ℂ) (w : AE D) {e : AE D} (he : IsSplitIdem D e) {u : WO S T}
    (hu : IsHalf e u) : sgnW ψ w u = 1 := by
  have h : symplO S T u (w • u) = 0 :=
    SplitScalar.symplO_eq_zero S T (a := e) (b := e) (by rw [mul_comm, he.2.1]) hu fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hu i j]
  rw [sgnW, symplOH, h, mul_zero, ψ.map_zero_eq_one]

theorem sgnW_two (ψ : AddChar (AF D.host.F) ℂ) {w : AE D} (hw : w + cA D w = 1) {u : WO S T}
    (h : ψ (symplO S T u (w • u)) = 1) : sgnW ψ w (2 • u) = 1 := by
  have h1 := sgnW_add ψ hw h
  rw [symplOH_self, ψ.map_zero_eq_one, one_mul] at h1
  rw [two_nsmul, h1]
  exact char_half h

def sgnGroup (ψ : AddChar (AF D.host.F) ℂ) {w : AE D} (hw : w + cA D w = 1) (Λ : AddSubgroup (WO S T))
    (hΛ : ∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u (w • u')) = 1) (f : WO S T → ℂ) : AddSubgroup (WO S T) where
  carrier := {u | u ∈ Λ ∧ heisO ψ S T u f = sgnW ψ w u • f}
  zero_mem' := ⟨zero_mem _, by rw [heisO_zero, sgnW_zero, one_smul]⟩
  add_mem' := by
    rintro u u' ⟨hu, h⟩ ⟨hu', h'⟩
    refine ⟨add_mem hu hu', ?_⟩
    have h1 := heisO_heisO ψ u u' f
    rw [h', heisO_smul, h, smul_smul, mul_comm, ← sgnW_add ψ hw (hΛ u hu u' hu'), mul_smul] at h1
    exact (smul_right_injective _ (char_ne_zero ψ _) h1).symm
  neg_mem' := by
    rintro u ⟨hu, h⟩
    refine ⟨neg_mem hu, ?_⟩
    have h1 := heisO_heisO ψ (-u) u f
    have h2 := sgnW_add ψ hw (hΛ (-u) (neg_mem hu) u hu)
    rw [neg_add_cancel, sgnW_zero, mul_one] at h2
    rw [h, heisO_smul, neg_add_cancel, heisO_zero, h2, mul_comm, mul_smul] at h1
    exact smul_right_injective _ (char_ne_zero ψ _) h1

theorem incA_smul_finTens {m n : ℕ} (x : D.host.E) (α : Af D.host.F) (M : Matrix (Fin m) (Fin n) D.host.E) :
    incA D x • finTens α M = finTens α (x • M) := by
  ext i j
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] x : AE D) * pairA D.host.F 0 α ⊗ₜ[D.host.F] M i j =
    pairA D.host.F 0 α ⊗ₜ[D.host.F] (x * M i j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem smul_mem_latO {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} (c : 𝓞 D.host.E)
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    incA D (c : D.host.E) • u ∈ latO S T LS LT fun _ => True := by
  refine latO_induction (p := fun u => incA D (c : D.host.E) • u ∈ latO S T LS LT fun _ => True) ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    rw [incA_smul_finTens]
    exact finTens_mem_latO hα (smul_mem_latRat c hM)
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

theorem isFinOf_iff (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (u : WO S T) :
    IsFinOf S T γ u ↔ u = finTens 1 γ := by
  constructor
  · rintro ⟨h1, h2⟩
    ext i j
    refine SplitScalar.adele_ext ?_ ?_
    · exact (congrFun (congrFun h1 i) j).trans (infPart_pair _ _).symm
    · exact congrFun (congrFun h2 i) j
  · rintro rfl
    exact ⟨Matrix.ext fun i j => infPart_pair _ _, rfl⟩

theorem continuous_finTens {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    Continuous fun α : Af D.host.F => finTens α M := by
  have hp : Continuous fun α : Af D.host.F => pairA D.host.F 0 α := continuous_const.prodMk continuous_id
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have e : (fun α : Af D.host.F => finTens α M i j) = fun α => pairA D.host.F 0 α • incA D (M i j) := by
    funext α
    change pairA D.host.F 0 α ⊗ₜ[D.host.F] M i j = pairA D.host.F 0 α • ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i j)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e]
  exact Continuous.smul (g := fun _ : Af D.host.F => incA D (M i j)) hp continuous_const

theorem pair_tmul_smul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (a : F) (x : E) :
    pairA F 0 (algebraMap F (Af F) a) ⊗ₜ[F] x = pairA F 0 1 ⊗ₜ[F] (a • x) := by
  rw [← TensorProduct.smul_tmul]
  congr 1
  exact Prod.ext (smul_zero _).symm (Algebra.algebraMap_eq_smul_one a)

theorem finTens_algebraMap {m n : ℕ} (a : D.host.F) (M : Matrix (Fin m) (Fin n) D.host.E) :
    finTens (algebraMap D.host.F (Af D.host.F) a) M = finTens 1 (a • M) := by
  ext i j
  change pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) a) ⊗ₜ[D.host.F] M i j =
    pairA D.host.F 0 1 ⊗ₜ[D.host.F] (a • M i j)
  exact pair_tmul_smul a (M i j)

theorem sgn_of_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) (w : AE D) {f : WO S T → ℂ} (hf : Continuous f)
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    (h : ∀ γ, finTens 1 γ ∈ (latO S T LS LT fun _ => True) →
      heisO ψ S T (finTens 1 γ) f = sgnW ψ w (finTens 1 γ : WO S T) • f)
    {α : Af D.host.F} (hα : α ∈ intAf D.host.F) {M : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (hM : M ∈ latRat S T LS LT) : heisO ψ S T (finTens α M) f = sgnW ψ w (finTens α M : WO S T) • f := by
  have hc := continuous_finTens (D := D) M
  funext x
  refine IntDense.mem_of_isClosed D.host.F
    (C := {α | heisO ψ S T (finTens α M) f x = (sgnW ψ w (finTens α M : WO S T) • f) x})
    (isClosed_eq ?_ ?_) (fun a => ?_) α hα
  · exact (hψ.comp (continuous_const.mul (SplitScalar.continuous_symplO S T continuous_const hc))).mul
      (hf.comp (continuous_const.add hc))
  · have hc' : Continuous fun α : Af D.host.F => w • finTens α M :=
      continuous_pi fun i => continuous_pi fun j =>
        continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp hc))
    exact (hψ.comp (continuous_const.mul (SplitScalar.continuous_symplO S T hc hc'))).mul continuous_const
  · have hm : finTens (algebraMap D.host.F (Af D.host.F) (a : D.host.F)) M ∈ latO S T LS LT fun _ => True :=
      finTens_mem_latO (fun v => by
        rw [AlgHom.commutes]; exact v.coe_algebraMap_mem (𝓞 D.host.F) D.host.F a) hM
    rw [Set.mem_setOf_eq, finTens_algebraMap] at *
    exact congrFun (h _ hm) x

theorem sum_EF {r : ℕ} (hr : T.rank = r) (X : Data D.host.E r) (hS : S.gram = 1) (hX : IsMod T hr X)
    (γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ∑ k, EF X (colsR hr γ k) (colsR hr γ' k) = -Algebra.trace ℚ D.host.E (D.host.xi0 * hRat S T γ γ') := by
  subst hr
  simp only [EF_def]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← map_neg, hX.kap, ← Finset.mul_sum]
  congr 1
  rw [show ∀ x : D.host.E, -(-(2 * x) / 2) = x from fun x => by ring, ← mul_neg]
  congr 1
  rw [hRat, hS, inv_one, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [Matrix.one_apply_ne hb.symm]) (by simp), herm, Finset.sum_comm,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hX.model.1, Matrix.one_apply_eq]
  change γ d a * -(T.gram c d) * star (γ' c a) = _
  ring

theorem sgnW_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {r : ℕ} (hr : T.rank = r)
    (X : Data D.host.E r) (hS : S.gram = 1) (hX : IsMod T hr X) (w : D.host.E)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    sgnW ψ (incA D w) (finTens 1 γ : WO S T) * epsW X w (colsR hr γ) = 1 := by
  have h1 := sum_EF hr X hS hX γ (w • γ)
  have h2 : epsW X w (colsR hr γ) = cexp (Real.pi * I * ((∑ k, EF X (colsR hr γ k) (colsR hr (w • γ) k) : ℚ) : ℂ)) := rfl
  have h3 : symplOH S T (finTens 1 γ) (finTens 1 (w • γ)) = pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F)
      (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * hRat S T γ (w • γ)))) := by
    rw [symplOH, symplO_finTens, one_mul, one_mul, RingHom.map_mul]
    exact Prod.ext (mul_zero _) rfl
  rw [h2, h1, sgnW, incA_smul_finTens, h3, GlobalTheory.T.stdChar_finitePart_rational_eq_exp_trace D ψ hψ, ← Complex.exp_add,
    show (1 / 2 : D.host.F) = algebraMap ℚ D.host.F (1 / 2) by simp, ← Algebra.smul_def, map_smul,
    Algebra.trace_trace, smul_eq_mul]
  refine Eq.trans (congrArg cexp ?_) Complex.exp_zero
  push_cast
  ring

theorem isLatVac_iff_epsW : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSelfDualC V ΛV → IsSelfDualC W ΛW → ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → (IsLatVac (heisO ψ V W) (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) f ↔ ∀ γ u, IsFinOf V W γ u → u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) → heisO ψ V W u f = epsW X (H.w0 : D.host.E) (colsR hr γ) • f) := by
  intro D ψ θ V W r g hr X bas idx hψ _ hV _ hX _ H hH ΛV ΛW hΛV hΛW f hf
  have hw0 : (H.w0 : D.host.E) + star (H.w0 : D.host.E) = 1 := by
    have h1 : 2 * (H.w0 : D.host.E) = 1 + D.host.sqrtMinusD := by
      rw [← hH]; exact congrArg Subtype.val H.two_weight_eq_one_add_root
    have h2 := congrArg star h1
    rw [star_mul', star_add, star_one, star_ofNat, SplitIdem.star_eq_conj D D.host.sqrtMinusD,
      D.host.conj_sqrtMinusD] at h2
    linear_combination (1 / 2 : D.host.E) * h1 + (1 / 2 : D.host.E) * h2
  have hw : incA D (H.w0 : D.host.E) + cA D (incA D (H.w0 : D.host.E)) = 1 := by
    rw [DualPairCheck.cA_incA, ← RingHom.map_add (f := _), hw0, RingHom.map_one]
  have hΛ : ∀ u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
      ∀ u' ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
        ψ (symplO V W u (incA D (H.w0 : D.host.E) • u')) = 1 :=
    fun u hu u' hu' => char_sympl_eq_one hψ hΛV hΛW hu (smul_mem_latO H.w0 hu')
  have he : ∀ γ, (finTens 1 γ : WO V W) ∈
      (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) →
      epsW X (H.w0 : D.host.E) (colsR hr γ) = sgnW ψ (incA D (H.w0 : D.host.E)) (finTens 1 γ : WO V W) := by
    intro γ hγ
    have h1 := sgnW_rat hψ hr X hV hX (H.w0 : D.host.E) γ
    have h2 : sgnW ψ (incA D (H.w0 : D.host.E)) (finTens 1 γ : WO V W) *
        sgnW ψ (incA D (H.w0 : D.host.E)) (finTens 1 γ : WO V W) = 1 := char_half (hΛ _ hγ _ hγ)
    exact mul_left_cancel₀ (char_ne_zero ψ _) (h1.trans h2.symm)
  constructor
  · intro hv γ u hu hm
    rw [isFinOf_iff] at hu
    subst hu
    rw [he γ hm]
    exact (le_of_two_of_half (sgnGroup ψ hw _ hΛ f)
      (fun u hu => ⟨nsmul_mem hu 2, by rw [hv.1 u hu, sgnW_two ψ hw (hΛ u hu u hu), one_smul]⟩)
      (fun e he u hu hh => ⟨hu, by rw [hv.2 e he u hu hh, sgnW_half ψ _ he hh, one_smul]⟩) hm).2
  · intro h
    have hall : ∀ u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
        u ∈ sgnGroup ψ hw _ hΛ f := fun u hu =>
      latO_induction (p := fun u => u ∈ sgnGroup ψ hw _ hΛ f)
        (fun α hα M hM => ⟨finTens_mem_latO hα hM, sgn_of_rat hψ.1.1 _ hf.cont
          (fun γ hγ => by rw [h γ _ ((isFinOf_iff _ _).2 rfl) hγ, he γ hγ]) hα hM⟩)
        (zero_mem _) (fun _ _ => add_mem) (fun _ => neg_mem) hu
    refine ⟨fun u hu => ?_, fun e hs u hu hh => ?_⟩
    · rw [(hall _ (nsmul_mem hu 2)).2, sgnW_two ψ hw (hΛ u hu u hu), one_smul]
    · rw [(hall _ hu).2, sgnW_half ψ _ hs hh, one_smul]

end GlobalTheory.VacSign

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThAHeisEntireLinearInjective
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem thA_heis_entire_linear_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ x ∈ X.dom, ∀ φ : TF n g, GlobalTheory.SW.IsSB φ → (∀ (y : Matrix (Fin n) (Fin r) E) (z : Fin n → Fin g → ℂ), GlobalTheory.SW.IsSB (heisG X bas y φ) ∧ thA X bas idx (heisG X bas y φ) x z = cexp (-(Real.pi * ∑ b, hx X bas idx x (z b + (1 / 2 : ℂ) • pv X idx x (y b)) (pv X idx x (y b)))) * thA X bas idx φ x (fun b => z b + pv X idx x (y b))) ∧ Differentiable ℂ (thA X bas idx φ x) ∧ (∀ φ' : TF n g, GlobalTheory.SW.IsSB φ' → (∀ a b : ℂ, GlobalTheory.SW.IsSB (a • φ + b • φ') ∧ thA X bas idx (a • φ + b • φ') x = a • thA X bas idx φ x + b • thA X bas idx φ' x) ∧ (thA X bas idx φ x = thA X bas idx φ' x → φ = φ')) := by
  intro E _ _ _ r g n X bas idx hs hn x hd φ hφ
  refine ⟨fun y z => ?_, GlobalTheory.SW.ThetaHol.differentiable_thA idx hs hφ hd, fun ψ hψ => ⟨fun a b => ?_, ?_⟩⟩
  · obtain ⟨h1, -, -, -, h2⟩ := (GlobalTheory.SW.heisG_laws E r X g bas idx n hs hn).2.2.2 y φ hφ
    exact ⟨h1, h2 x hd z⟩
  · have h1 : GlobalTheory.SW.IsSB (a • φ) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ hφ hφ).2.1 a
    have h2 : GlobalTheory.SW.IsSB (b • ψ) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ hψ hψ).2.1 b
    refine ⟨(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear _ _ _ _ _ h1 h2).1, ?_⟩
    rw [GlobalTheory.SW.UnAct.thA_add idx hs hd h1 h2, GlobalTheory.SW.UnAct.thA_smul, GlobalTheory.SW.UnAct.thA_smul]
  · exact GlobalTheory.SW.UnAct.eq_of_thA_eq idx hs hd hφ hψ

end GlobalTheory.AdTh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPartMul
noncomputable section

namespace GlobalTheory.OrbDesc

variable {H : Type} [Group H]

theorem locPart_mul {T L : Subgroup H} (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s) {t x l : H} (ht : t ∈ T)
    (hl : l ∈ L) : GlobalTheory.LKLoc.locPart T L (t * x * l) = GlobalTheory.LKLoc.locPart T L x := by
  unfold GlobalTheory.LKLoc.locPart
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hg, k, hk, rfl⟩
    refine ⟨hg, l * k * l⁻¹, L.mul_mem (L.mul_mem hl hk) (L.inv_mem hl), ?_⟩
    calc x * (l * k * l⁻¹) * x⁻¹ = t⁻¹ * ((t * x * l * k * (t * x * l)⁻¹) * t) := by group
      _ = t⁻¹ * (t * (t * x * l * k * (t * x * l)⁻¹)) := by rw [hT _ hg t ht]
      _ = t * x * l * k * (t * x * l)⁻¹ := by group
  · rintro ⟨hg, k, hk, rfl⟩
    refine ⟨hg, l⁻¹ * k * l, L.mul_mem (L.mul_mem (L.inv_mem hl) hk) hl, ?_⟩
    have := hT _ hg t ht
    calc t * x * l * (l⁻¹ * k * l) * (t * x * l)⁻¹ = t * (x * k * x⁻¹) * t⁻¹ := by group
      _ = (x * k * x⁻¹) * t * t⁻¹ := by rw [← this]
      _ = x * k * x⁻¹ := by group

theorem wt_mul {T L : Subgroup H} (U : Subgroup H) {Ψ : H → ℂ} (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    (hΨl : ∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) (hΨr : ∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) {t x l : H} (ht : t ∈ T)
    (hl : l ∈ L) : wt T L U Ψ (t * x * l) = wt T L U Ψ x := by
  unfold wt
  rw [locPart_mul hT ht hl, hΨr l hl, hΨl t ht]

theorem wt_out {T L : Subgroup H} (U : Subgroup H) {Ψ : H → ℂ} (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    (hΨl : ∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) (hΨr : ∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) (x : H) :
    wt T L U Ψ (Quotient.out (DoubleCoset.mk T L x)) = wt T L U Ψ x := by
  obtain ⟨t, ht, l, hl, h⟩ := (@DoubleCoset.eq _ _ T L _ _).1 (DoubleCoset.out_eq' (DoubleCoset.mk T L x))
  exact (wt_mul U hT hΨl hΨr ht hl).symm.trans (congrArg _ h.symm)

end GlobalTheory.OrbDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HxOfIsONFr
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem hx_of_isONFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ x : Frame X.Ψ r, IsONFr X x → x ∈ X.dom ∧ IsUnitFr X x ∧ ∀ z w : Fin g → ℂ, hx X bas idx x z w = ∑ j, (X.c (idx j).1 : ℂ) * z j * conj (w j) := by
  intro E _ _ _ r g n X bas idx hs _ x ho
  have hsg : ∀ a : ℕ, FD.sgn X.p0 a = 1 ∨ FD.sgn X.p0 a = -1 := fun a => by
    unfold FD.sgn; split_ifs <;> simp
  have e (τ : X.Ψ) (i : Fin (r + 1)) : dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [ho τ, sgnM, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((FD.sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  have h0 (i : ℕ) : psgn X.p0 i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => by rcases hsg a with h | h <;> rw [h] <;> norm_num
  have hd : x ∈ X.dom := by
    refine fun τ => ⟨fun h => ?_, fun i => ?_⟩
    · have h1 : FD.gram τ.1 X.Gm (mat x τ) =
          (mat x τ)ᵀ * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ) := by
        ext a b
        simp only [FD.gram, hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
          Matrix.map_apply, Finset.sum_mul]
        exact Finset.sum_comm
      have h2 := congrArg Matrix.det (h1.symm.trans (ho τ))
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, zero_mul, sgnM,
        Matrix.det_diagonal] at h2
      refine Finset.prod_ne_zero_iff.2 (fun a _ => ?_) h2.symm
      rcases hsg a with h | h <;> rw [h] <;> norm_num
    · rw [e, Complex.ofReal_re]
      exact mul_self_pos.2 (h0 _)
  refine ⟨hd, fun τ i => ?_, (GlobalTheory.Dict.hx_ortho E r X g bas idx hs x hd ho).1⟩
  rw [e, psgn]
  push_cast
  rw [norm_prod]
  exact Finset.prod_eq_one fun a _ => by rcases hsg a with h | h <;> rw [h] <;> simp

end GlobalTheory.AdTh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFiniteOfHcFinite
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev
  Formalism.IndefR
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodFiniteDim

variable {D : D7}

theorem isOpen_comap_Kg (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (T : Finset (Pl D.host.E)) :
    IsOpen (((Kg D.sp.cm V.gram β T).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β T] with κ hh
  obtain ⟨h1, h2, h3⟩ := hh
  exact ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩

theorem levFn_eq_one {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {T : Finset (Pl D.host.E)}
    (hg : L.Pg ⊆ T) (hq : L.Q ⊆ T) {x : GL (Fin V.rank) (Lev.EAf D)} (hx : x ∈ Kg D.sp.cm V.gram β T) :
    levFn β L x = 1 := by
  have h3 : ∀ PP ∈ T, redFn β PP x = 1 := by
    have h1 : x ∈ ⨅ PP ∈ T, princAt β PP := hx.2
    exact fun PP hP => (mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h1 PP) hP)).2
  have h4 : rTup β L x = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 x) = 1
    rw [h3 PP.1 (hg PP.2)]; exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levFn
  rw [h4, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hP
    rw [h3 PP (hq hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [h3 PP (hg hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]

theorem exists_open_subgroup (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
      ∀ k ∈ U, k ∈ GfC V → k ∈ (levG V β L : Set (GA D V)) ∧ levChi V β L k = 1 := by
  classical
  refine ⟨_, isOpen_comap_Kg V β (L.Pg ∪ L.Q), fun k hk hf => ⟨⟨hf, ?_⟩, ?_⟩⟩
  · exact Kg_le_lev (D := L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right hk
  · unfold levChi
    rw [levFn_eq_one Finset.subset_union_left Finset.subset_union_right hk, Units.val_one]

end GlobalTheory.GoodFiniteDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorOfAdelicLattice
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.LatBound

variable {E : Type} [Field E] [NumberField E]

theorem coord_mul (z z' : Af E) (w : HeightOneSpectrum (𝓞 E)) : (z * z') w = z w * z' w := rfl

theorem coord_add (z z' : Af E) (w : HeightOneSpectrum (𝓞 E)) : (z + z') w = z w + z' w := rfl

theorem integral_of_int (b : 𝓞 E) (w : HeightOneSpectrum (𝓞 E)) :
    (algebraMap E (Af E) (algebraMap (𝓞 E) E b)) w ∈ w.adicCompletionIntegers E :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
    ((HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_le (w.valuation_le_one b))

theorem integral_natCast (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) :
    ((n : Af E)) w ∈ w.adicCompletionIntegers E := by
  have := integral_of_int (E := E) (n : 𝓞 E) w
  simpa using this

theorem exists_nat_mul_integral (z : Af E) :
    ∃ d : ℕ, 0 < d ∧ ∀ w : HeightOneSpectrum (𝓞 E), ((d : Af E) * z) w ∈ w.adicCompletionIntegers E := by
  obtain ⟨x, a, ha, h⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E 1 one_pos).1 z
  obtain ⟨m, hm0, hm⟩ := IsAlgebraic.exists_integral_multiple
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic x))
  have hint : IsIntegral ℤ ((m.natAbs : E) * x) := by
    rcases Int.natAbs_eq m with h1 | h1
    · have : ((m.natAbs : E) * x) = m • x := by
        rw [zsmul_eq_mul, ← Int.cast_natCast, ← h1]
      rw [this]; exact hm
    · have h1' : (m.natAbs : ℤ) = -m := by omega
      have : ((m.natAbs : E) * x) = -(m • x) := by
        rw [zsmul_eq_mul, ← Int.cast_natCast, h1', Int.cast_neg, neg_mul]
      rw [this]; exact hm.neg
  refine ⟨m.natAbs, Int.natAbs_pos.2 hm0, fun w => ?_⟩
  have e : (m.natAbs : Af E) * z =
      algebraMap E (Af E) (algebraMap (𝓞 E) E ⟨_, hint⟩) + (m.natAbs : Af E) * a := by
    rw [h, one_smul, mul_add]
    congr 1
    show _ = algebraMap E (Af E) ((m.natAbs : E) * x)
    rw [map_mul, map_natCast]
  rw [e, coord_add, coord_mul]
  exact add_mem (integral_of_int _ w) (mul_mem (integral_natCast _ w) (ha w))

theorem integral_of_mem_hatO [IsCMField E] {c : Ideal (OF E)} (hc : c ≠ ⊥) {z : Af E} (hz : z ∈ hatO c)
    (w : HeightOneSpectrum (𝓞 E)) : z w ∈ w.adicCompletionIntegers E := by
  obtain ⟨a, -, ha, hza⟩ := (GlobalTheory.CMVal.HatPlace.mem_hatO_iff E c hc z).1 hz
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : Valued.v (z w - a w) ≤ 1 :=
    (hza w).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have h2 : z w = (z w - a w) + a w := by ring
  rw [h2]
  exact Valuation.map_add_le _ h1 (ha w)

theorem lattice_between : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ y : (Af E)ˣ,
    ∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ lattice c y) ∧
      ∀ x ∈ lattice c y, IsIntegral ℤ ((N : E) * x) := by
  intro E _ _ _ c hc y
  obtain ⟨d₁, hd₁, h₁⟩ := exists_nat_mul_integral (y : Af E)
  obtain ⟨d₂, hd₂, h₂⟩ := exists_nat_mul_integral (↑y⁻¹ : Af E)
  have hN₁ : 0 < Ideal.absNorm c := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  refine ⟨Ideal.absNorm c * d₁ * d₂, by positivity, fun x => ?_, fun x hx => ?_⟩
  · rw [mem_lattice]
    have hY : ∀ w : HeightOneSpectrum (𝓞 E),
        (algebraMap E (Af E) (algebraMap (𝓞 E) E x) * (d₁ : Af E) * ((d₂ : Af E) * (↑y⁻¹ : Af E))) w ∈
          w.adicCompletionIntegers E := fun w => by
      rw [coord_mul, coord_mul]
      exact mul_mem (mul_mem (integral_of_int x w) (integral_natCast d₁ w)) (h₂ w)
    have key := GlobalTheory.CMVal.PicFin.mul_mem_hatO (Ideal.absNorm_mem c) hY
    convert key using 1
    rw [map_natCast, map_natCast, map_mul, map_natCast]
    push_cast
    ring
  · rw [mem_lattice] at hx
    have hz := integral_of_mem_hatO hc hx
    have hint : ∀ w : HeightOneSpectrum (𝓞 E), w.valuation E ((d₁ : E) * x) ≤ 1 := fun w => by
      have e : algebraMap E (Af E) ((d₁ : E) * x) =
          (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) * ((d₁ : Af E) * (y : Af E)) := by
        rw [map_mul, map_natCast]
        have : (↑y⁻¹ : Af E) * (y : Af E) = 1 := Units.inv_mul y
        linear_combination (-(d₁ : Af E) * algebraMap E (Af E) x) * this
      have h3 : (algebraMap E (Af E) ((d₁ : E) * x)) w ∈ w.adicCompletionIntegers E := by
        rw [e, coord_mul]; exact mul_mem (hz w) (h₁ w)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, FiniteAdeleRing.algebraMap_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h3
      exact h3
    obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ hint
    have e2 : ((Ideal.absNorm c * d₁ * d₂ : ℕ) : E) * x =
        algebraMap (𝓞 E) E (((Ideal.absNorm c * d₂ : ℕ) : 𝓞 E) * b) := by
      rw [map_mul, hb, map_natCast]; push_cast; ring
    rw [e2]
    exact RingOfIntegers.isIntegral_coe _

end GlobalTheory.CMVal.LatBound
end
end
