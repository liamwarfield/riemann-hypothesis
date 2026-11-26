module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementForm

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementExtension
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open GroundTheory.Automorphic

noncomputable section

namespace ComplementExtension

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
variable {h : HermitianForm F E W} {v w : W}

theorem toSesq_v_v (hp : IsHyperbolicPair h v w) : h.toSesq v v = 0 := hp.1

theorem toSesq_w_w (hp : IsHyperbolicPair h v w) : h.toSesq w w = 0 := hp.2.1

theorem toSesq_v_w (hp : IsHyperbolicPair h v w) : h.toSesq v w = 1 := hp.2.2

theorem toSesq_w_v (hp : IsHyperbolicPair h v w) : h.toSesq w v = 1 := by
  rw [← h.isSymm.eq v w, hp.2.2, map_one]

theorem toSesq_swap_eq_zero {u z : W} (hz : h.toSesq u z = 0) : h.toSesq z u = 0 := by
  rw [← h.isSymm.eq u z, hz, map_zero]

def proj (hp : IsHyperbolicPair h v w) : W →ₗ[E] hypComplement h v w :=
  LinearMap.codRestrict _
    (LinearMap.id - (h.toSesq w).smulRight v - (h.toSesq v).smulRight w)
    (fun x => by
      rw [mem_hypComplement]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub, map_smul,
        smul_eq_mul, toSesq_v_v hp, toSesq_w_w hp, toSesq_v_w hp, toSesq_w_v hp]
      constructor <;> ring)

theorem proj_apply (hp : IsHyperbolicPair h v w) (x : W) :
    (proj hp x : W) = x - h.toSesq w x • v - h.toSesq v x • w := rfl

theorem split (hp : IsHyperbolicPair h v w) (x : W) :
    h.toSesq w x • v + (proj hp x : W) + h.toSesq v x • w = x := by
  rw [proj_apply]; abel

theorem toSesq_split (hp : IsHyperbolicPair h v w) (a b a' b' : E) (z z' : hypComplement h v w) :
    h.toSesq (a • v + (z : W) + b • w) (a' • v + (z' : W) + b' • w) =
      conjHom F E a * b' + conjHom F E b * a' + h.toSesq z z' := by
  obtain ⟨hvz, hwz⟩ := mem_hypComplement.1 z.2
  obtain ⟨hvz', hwz'⟩ := mem_hypComplement.1 z'.2
  have hzv := toSesq_swap_eq_zero hvz
  have hzw := toSesq_swap_eq_zero hwz
  simp only [map_add (f := _), LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul,
    smul_eq_mul, toSesq_v_v hp, toSesq_w_w hp, toSesq_v_w hp, toSesq_w_v hp, hvz', hwz', hzv, hzw]
  ring

def extMap (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) : W →ₗ[E] W :=
  (h.toSesq w).smulRight v + (hypComplement h v w).subtype ∘ₗ m ∘ₗ proj hp +
    (h.toSesq v).smulRight w

theorem extMap_apply (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    extMap hp m x = h.toSesq w x • v + (m (proj hp x) : W) + h.toSesq v x • w := rfl

theorem toSesq_w_extMap (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    h.toSesq w (extMap hp m x) = h.toSesq w x := by
  have := (mem_hypComplement.1 (m (proj hp x)).2).2
  simp only [extMap_apply, map_add (f := _), map_smul, smul_eq_mul, toSesq_w_w hp, toSesq_w_v hp, this]
  ring

theorem toSesq_v_extMap (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    h.toSesq v (extMap hp m x) = h.toSesq v x := by
  have := (mem_hypComplement.1 (m (proj hp x)).2).1
  simp only [extMap_apply, map_add (f := _), map_smul, smul_eq_mul, toSesq_v_v hp, toSesq_v_w hp, this]
  ring

theorem proj_extMap (hp : IsHyperbolicPair h v w)
    (m : hypComplement h v w →ₗ[E] hypComplement h v w) (x : W) :
    proj hp (extMap hp m x) = m (proj hp x) := by
  apply Subtype.ext
  rw [proj_apply, toSesq_w_extMap, toSesq_v_extMap, extMap_apply]
  abel

theorem extMap_comp (hp : IsHyperbolicPair h v w)
    (m m' : hypComplement h v w →ₗ[E] hypComplement h v w) :
    extMap hp m ∘ₗ extMap hp m' = extMap hp (m ∘ₗ m') := by
  ext x
  rw [LinearMap.comp_apply, extMap_apply hp m, toSesq_w_extMap, toSesq_v_extMap, proj_extMap,
    extMap_apply]
  rfl

theorem extMap_id (hp : IsHyperbolicPair h v w) : extMap hp LinearMap.id = LinearMap.id := by
  ext x
  rw [extMap_apply, LinearMap.id_apply, LinearMap.id_apply]
  exact split hp x

theorem proj_of_mem (hp : IsHyperbolicPair h v w) (x : hypComplement h v w) :
    proj hp (x : W) = x := by
  obtain ⟨hvx, hwx⟩ := mem_hypComplement.1 x.2
  apply Subtype.ext
  rw [proj_apply, hvx, hwx]
  simp

theorem proj_v (hp : IsHyperbolicPair h v w) : proj hp v = 0 := by
  apply Subtype.ext
  rw [proj_apply, toSesq_w_v hp, hp.1]
  simp

theorem proj_w (hp : IsHyperbolicPair h v w) : proj hp w = 0 := by
  apply Subtype.ext
  rw [proj_apply, hp.2.1, hp.2.2]
  simp

theorem proof (h : HermitianForm F E W) : ComplementExtension.Statement h := by
  intro v w hp h' hh' m
  let M : hypComplement h v w ≃ₗ[E] hypComplement h v w := m
  let e : W ≃ₗ[E] W := LinearEquiv.ofLinearMap (extMap hp M.toLinearMap)
    (extMap hp M.symm.toLinearMap)
    (by rw [extMap_comp, LinearEquiv.comp_symm, extMap_id])
    (by rw [extMap_comp, LinearEquiv.symm_comp, extMap_id])
  have he : ∀ x, e x = extMap hp M.toLinearMap x := fun x => rfl
  have hM : ∀ a b, h.toSesq (M a : W) (M b : W) = h.toSesq (a : W) b := by
    intro a b
    rw [← hh', ← hh']
    exact m.2 a b
  have hmem : e ∈ h.unitaryGroup := by
    intro x y
    rw [he, he, extMap_apply, extMap_apply, toSesq_split hp]
    conv_rhs => rw [← split hp x, ← split hp y]
    rw [toSesq_split hp]
    simp only [LinearEquiv.coe_coe, hM]
  refine ⟨⟨e, hmem⟩, ?_, ?_, ?_⟩
  · change e v = v
    rw [he, extMap_apply, proj_v, map_zero, toSesq_w_v hp, hp.1]
    simp
  · change e w = w
    rw [he, extMap_apply, proj_w, map_zero, hp.2.1, hp.2.2]
    simp
  · intro x
    change e x = ((M x : hypComplement h v w) : W)
    obtain ⟨hvx, hwx⟩ := mem_hypComplement.1 x.2
    rw [he, extMap_apply, proj_of_mem, hvx, hwx]
    simp

end ComplementExtension

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipRadicalOfRational
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def UnipRadicalOfRational.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (x₀ : W) (γ : h.unitaryGroup), γ • x₀ = x₀ →
    (∀ z : W, h.toSesq x₀ z = 0 → ∃ a : E, γ • z = z + a • x₀) →
    archEmbed h v γ ∈ unipRadical h v x₀

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StRationalUnipotent
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def RationalUnipotent.Statement (h : HermitianForm F E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ w₀ : W), IsDIntegral h D La → x₀ ∈ La →
    IsHyperbolicPair h x₀ w₀ →
    ∃ m : ℕ, 0 < m ∧ ∀ (y : W) (c : E), y ∈ hypComplement h x₀ w₀ → (∃ z ∈ La, y = m • z) →
      (∃ a : 𝓞 E, c = (m : E) * a) → c + conj F E c = -h.toSesq y y →
      ∃ γ ∈ latticeStab h La, γ • x₀ = x₀ ∧ γ • w₀ = w₀ + y + c • x₀ ∧
        ∀ z ∈ hypComplement h x₀ w₀, γ • z = z - h.toSesq y z • x₀

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsSemidirectHaar
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

def SemidirectHaar.Statement (G T : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] : Prop :=
  ∀ (P H : Subgroup G), IsClosed (P : Set G) → IsClosed (H : Set G) → H ≤ P →
    ∀ (τ : T →* G) (β : P → T) (δ : T → ℝ≥0), Continuous τ → Continuous β → Continuous δ →
    (∀ t, τ t ∈ P) → (∀ t, ∀ x ∈ H, τ t * x * (τ t)⁻¹ ∈ H) → (∀ t, τ t ∈ H → t = 1) →
    (∀ p : P, (p : G) * (τ (β p))⁻¹ ∈ H) →
    ∀ (μ : Measure P) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
      (ρ : Measure T) [ρ.IsHaarMeasure],
    (∀ (t : T) (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ x, f (τ t * x * (τ t)⁻¹) ∂ν = δ t * ∫⁻ x, f x ∂ν) →
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ φ : G → ℝ≥0∞, Measurable φ →
      ∫⁻ p, φ p ∂μ = c * ∫⁻ t, δ t * ∫⁻ x : H, φ (x * τ t) ∂ν ∂ρ

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipotentCoordProper
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

section Coordinate

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def unipCoord (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) (n : unipRadical h v x₀) :
    InfinitePlace E → ι → ℂ :=
  fun w => (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w -
    vecAt v w₀ w

omit [NumberField E] in
theorem unipCoord_apply (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W)
    (n : unipRadical h v x₀) (w : InfinitePlace E) :
    unipCoord h v x₀ w₀ n w =
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w -
        vecAt v w₀ w :=
  rfl


omit [NumberField E] in
theorem continuous_unipCoord (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :
    Continuous (unipCoord h v x₀ w₀) := by
  refine continuous_pi fun w => ?_
  have hc : Continuous fun n : unipRadical h v x₀ =>
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) :=
    Units.continuous_val.comp ((continuous_apply w).comp
      (continuous_subtype_val.comp continuous_subtype_val))
  exact (hc.matrix_mulVec continuous_const).sub continuous_const

def UnipotentCoordProper.Statement [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
    (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ w₀ : W, IsHyperbolicPair h x₀ w₀ → ∀ K : Set (InfinitePlace E → ι → ℂ), IsCompact K →
    IsCompact {n : unipRadical h v x₀ | unipCoord h v x₀ w₀ n ∈ K}

end Coordinate

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLinePairOrbitsFinite
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

universe u

section Sandwich

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem fg_map_of_fg {H : AddSubgroup A} (hH : H.FG) (φ : A →+ B) : (H.map φ).FG := by
  rw [AddSubgroup.fg_iff_exists_fin_addMonoidHom] at hH ⊢
  obtain ⟨k, f, rfl⟩ := hH
  exact ⟨k, φ.comp f, by rw [AddMonoidHom.range_comp]⟩

theorem fg_of_le_fg {H K : AddSubgroup A} (hHK : H ≤ K) (hK : K.FG) : H.FG := by
  have hK' : K.toIntSubmodule.FG := (Submodule.fg_iff_addSubgroup_fg _).2 hK
  have := isNoetherian_of_fg_of_noetherian _ hK'
  exact (Submodule.fg_iff_addSubgroup_fg H.toIntSubmodule).1
    (Submodule.FG.of_le_of_isNoetherian (S := H.toIntSubmodule) (T := K.toIntSubmodule) hHK)

variable [NoZeroSMulDivisors ℕ A]

theorem finite_sandwich (M : AddSubgroup A) {n : ℕ} (hn : 0 < n) :
    {L : AddSubgroup A | M ≤ L ∧ (∀ x ∈ L, n • x ∈ M) ∧ L.FG}.Finite := by
  rcases Set.eq_empty_or_nonempty {L : AddSubgroup A | M ≤ L ∧ (∀ x ∈ L, n • x ∈ M) ∧ L.FG}
    with he | ⟨L₀, hML₀, -, hL₀⟩
  · rw [he]
    exact Set.finite_empty
  have hM : M.FG := fg_of_le_fg hML₀ hL₀
  let f : A →+ A := nsmulAddMonoidHom n
  have hf : Function.Injective f := fun x y hxy => by
    have hxy' : n • x = n • y := hxy
    exact smul_right_injective A hn.ne' hxy'

  let N : AddSubgroup A := M.comap f
  have hNM : (N.map f) ≤ M := AddSubgroup.map_comap_le _ _
  have hN : N.FG := by
    have h1 : (N.map f).FG := fg_of_le_fg hNM hM
    have h2 : N.toIntSubmodule.FG := by
      refine Submodule.fg_of_fg_map_injective f.toIntLinearMap hf ?_
      have : (N.toIntSubmodule.map f.toIntLinearMap) = (N.map f).toIntSubmodule := by
        ext x
        simp
      rw [this]
      exact (Submodule.fg_iff_addSubgroup_fg _).2 h1
    exact (Submodule.fg_iff_addSubgroup_fg _).1 h2
  have hMN : M ≤ N := fun x hx => M.nsmul_mem hx n
  let M' : AddSubgroup N := M.addSubgroupOf N
  have : AddGroup.FG N := (AddGroup.fg_iff_addSubgroup_fg N).2 hN
  have : AddGroup.FG (N ⧸ M') :=
    AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective M')
  have : Finite (N ⧸ M') := by
    refine AddCommGroup.finite_of_fg_isAddTorsion _ fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective M' q
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
    rw [← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    exact x.2

  let q : AddSubgroup A → Set (N ⧸ M') := fun L =>
    QuotientAddGroup.mk' M' '' {y : N | (y : A) ∈ L}
  refine Set.Finite.of_finite_image (f := q) (Set.toFinite _) ?_
  rintro L ⟨hML, hLn, -⟩ L' ⟨hML', hL'n, -⟩ hq
  have key : ∀ L L' : AddSubgroup A, M ≤ L' → (∀ x ∈ L, n • x ∈ M) → q L ⊆ q L' → L ≤ L' := by
    intro L L' hML' hLn hsub x hx
    have hxN : x ∈ N := hLn x hx
    obtain ⟨y, hy, hyx⟩ := hsub ⟨⟨x, hxN⟩, hx, rfl⟩
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq] at hyx
    have hd : -(y : A) + x ∈ M := by
      have := AddSubgroup.mem_addSubgroupOf.1 hyx
      simpa using this
    have : x = y + (-(y : A) + x) := by abel
    rw [this]
    exact L'.add_mem hy (hML' hd)
  exact le_antisymm (key L L' hML' hLn hq.le) (key L' L hML hL'n hq.ge)

end Sandwich

section Pairs

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type u} [AddCommGroup W] [Module E W]

theorem LinePairOrbitsFinite.proof (h : HermitianForm F E W) [FiniteDimensional E W]
    (h₁ : LatticeOrbitsFiniteBelow.{u} F E (finrank E W)) (h₂ : WittPartner.Statement h)
    (h₃ : ComplementForm.Statement h) (h₄ : ComplementExtension.Statement h)
    (h₅ : AdaptedReduction.Statement h) : LinePairOrbitsFinite.Statement h := by
  intro D
  by_cases hex : ∃ v₀ : W, v₀ ≠ 0 ∧ h.toSesq v₀ v₀ = 0
  swap
  · refine ⟨∅, Set.finite_empty, fun La l _ hl => ?_⟩
    exfalso
    have hne : l ≠ ⊥ := fun hb => by
      have := hl.1
      rw [hb, finrank_bot] at this
      exact zero_ne_one this
    obtain ⟨x, hxl, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact hex ⟨x, hx0, hl.2 x hxl x hxl⟩
  obtain ⟨v₀, hv₀, hv₀₀⟩ := hex
  obtain ⟨w₀, hvw, hww⟩ := h₂ v₀ hv₀ hv₀₀
  have hp : IsHyperbolicPair h v₀ w₀ := ⟨hv₀₀, hww, hvw⟩
  obtain ⟨h', hh'⟩ := h₃ v₀ w₀ hp
  obtain ⟨KK, hKK, n, D', hn, hred⟩ := h₅ v₀ w₀ hp h' hh' D
  have hdim : finrank E (hypComplement h v₀ w₀) < finrank E W := by
    refine Submodule.finrank_lt fun htop => ?_
    have hv : v₀ ∈ hypComplement h v₀ w₀ := htop ▸ Submodule.mem_top
    have h1 : h.toSesq w₀ v₀ = 1 := by
      rw [← h.isSymm.eq v₀ w₀, hvw, map_one]
    exact one_ne_zero (h1 ▸ (mem_hypComplement.1 hv).2)
  obtain ⟨S', hS', hS'L⟩ := h₁ (hypComplement h v₀ w₀) h' hdim D'
  have : NoZeroSMulDivisors ℕ W := ⟨fun {c x} hcx => by
    rw [← Nat.cast_smul_eq_nsmul E] at hcx
    rcases smul_eq_zero.1 hcx with h0 | h0
    · exact Or.inl (Nat.cast_eq_zero.1 h0)
    · exact Or.inr h0⟩
  let Mof : AddSubgroup E × AddSubgroup E → AddSubgroup (hypComplement h v₀ w₀) →
      AddSubgroup W := fun p L =>
    p.1.map ((smulAddHom E W).flip v₀) ⊔ L.map (hypComplement h v₀ w₀).subtype.toAddMonoidHom ⊔
      p.2.map ((smulAddHom E W).flip w₀)
  refine ⟨(⋃ p ∈ KK, ⋃ L ∈ S', {La | Mof p L ≤ La ∧ (∀ x ∈ La, n • x ∈ Mof p L) ∧ La.FG}) ×ˢ
    {Submodule.span E {v₀}},
    (hKK.biUnion fun p _ => hS'.biUnion fun L _ => finite_sandwich _ hn).prod
      (Set.finite_singleton _), ?_⟩
  intro La l hLa hl
  obtain ⟨g, La₁, hgLa, hgv, hK, hsplit, hInt⟩ := hred La l hLa hl
  obtain ⟨L, hL, m, hmL⟩ := hS'L _ hInt
  obtain ⟨gm, hgv₀, hgw₀, hgx⟩ := h₄ v₀ w₀ hp h' hh' m

  have hsmul : ∀ (γ : h.unitaryGroup) (c : E) (x : W), γ • (c • x) = c • (γ • x) := fun γ c x =>
    map_smul (γ : W ≃ₗ[E] W) c x
  have hmem : ∀ x : W, x ∈ gm⁻¹ • La₁ ↔ gm • x ∈ La₁ := fun x => by
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists _ _ _).1 hx
      simpa using hy
    · intro hx
      have := AddSubgroup.smul_mem_pointwise_smul _ gm⁻¹ La₁ hx
      rw [inv_smul_smul] at this
      exact this
  refine ⟨(gm⁻¹ • La₁, Submodule.span E {v₀}), ⟨?_, rfl⟩, g * gm, ?_, ?_⟩
  · refine Set.mem_iUnion₂.2 ⟨_, hK, Set.mem_iUnion₂.2 ⟨L, hL, ?_, ?_, ?_⟩⟩
    · refine sup_le (sup_le ?_ ?_) ?_
      · rintro _ ⟨a, ha, rfl⟩
        rw [hmem]
        change gm • (a • v₀) ∈ La₁
        rw [hsmul, hgv₀]
        exact ha
      · rintro _ ⟨y, hy, rfl⟩
        rw [hmem]
        change gm • (y : W) ∈ La₁
        rw [hgx]
        have : m • y ∈ m • L := AddSubgroup.smul_mem_pointwise_smul y m L hy
        rw [hmL] at this
        exact this
      · rintro _ ⟨b, hb, rfl⟩
        rw [hmem]
        change gm • (b • w₀) ∈ La₁
        rw [hsmul, hgw₀]
        exact hb
    · intro x hx
      rw [hmem] at hx
      obtain ⟨a, ha, b, hb, hz⟩ := hsplit _ hx
      set z : W := n • (gm • x) - a • v₀ - b • w₀ with hzdef
      have hzL : z ∈ La₁ :=
        La₁.sub_mem (La₁.sub_mem (La₁.nsmul_mem hx n) ha) hb
      have hz' : (⟨z, hz⟩ : hypComplement h v₀ w₀) ∈ m • L := by
        rw [hmL]
        exact hzL
      obtain ⟨y, hy, hyz⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists _ _ _).1 hz'
      have hnx : n • x = a • v₀ + (y : W) + b • w₀ := by
        apply (MulAction.injective gm)
        show gm • (n • x) = gm • (a • v₀ + (y : W) + b • w₀)
        have e1 : gm • (n • x) = n • (gm • x) := map_nsmul (gm : W ≃ₗ[E] W) n x
        have e2 : gm • (y : W) = z := by
          rw [hgx, hyz]
        rw [e1, smul_add, smul_add, hsmul, hsmul, hgv₀, hgw₀, e2, hzdef]
        abel
      rw [hnx]
      refine AddSubgroup.add_mem _ (AddSubgroup.add_mem _ ?_ ?_) ?_
      · exact AddSubgroup.mem_sup_left (AddSubgroup.mem_sup_left ⟨a, ha, rfl⟩)
      · exact AddSubgroup.mem_sup_left (AddSubgroup.mem_sup_right ⟨y, hy, rfl⟩)
      · exact AddSubgroup.mem_sup_right ⟨b, hb, rfl⟩
    · have hLa₁ : La₁ = g⁻¹ • La := by
        rw [← hgLa, inv_smul_smul]
      have hfg : ∀ (γ : h.unitaryGroup) (S : AddSubgroup W), S.FG → (γ • S).FG := by
        intro γ S hS
        have : γ • S = S.map (((γ : W ≃ₗ[E] W) : W →ₗ[E] W).toAddMonoidHom) := by
          ext x
          constructor
          · intro hx
            obtain ⟨y, hy, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists _ _ _).1 hx
            exact ⟨y, hy, rfl⟩
          · rintro ⟨y, hy, rfl⟩
            exact AddSubgroup.smul_mem_pointwise_smul y γ S hy
        rw [this]
        exact fg_map_of_fg hS _
      exact hfg _ _ (hLa₁ ▸ hfg _ _ hLa.isLattice.fg)
  · rw [mul_smul, smul_inv_smul, hgLa]
  · have hgv0 : (g : W ≃ₗ[E] W) v₀ ≠ 0 := fun h0 =>
      hv₀ ((g : W ≃ₗ[E] W).map_eq_zero_iff.1 h0)
    have hg' : ((g * gm : h.unitaryGroup) : W ≃ₗ[E] W) v₀ = (g : W ≃ₗ[E] W) v₀ := by
      change (g : W ≃ₗ[E] W) ((gm : W ≃ₗ[E] W) v₀) = _
      exact congrArg _ hgv₀
    change (Submodule.span E {v₀}).map _ = l
    rw [Submodule.map_span, Set.image_singleton]
    change Submodule.span E {((g * gm : h.unitaryGroup) : W ≃ₗ[E] W) v₀} = l
    rw [hg']
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem]
      exact hgv
    · rw [finrank_span_singleton hgv0, hl.1]

end Pairs

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StImaginaryLatticeCocompact
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable (F E : Type*) [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

def ImaginaryLatticeCocompact.Statement : Prop :=
  ∀ m : ℕ, 0 < m → ∃ R : ℝ, ∀ s : InfinitePlace E → ℝ, ∃ a : 𝓞 E,
    (m : E) * a + conj F E ((m : E) * a) = 0 ∧ ∀ w, |(w.embedding ((m : E) * a)).im - s w| ≤ R

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineEigenvalue
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]

def LineEigenvalue.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ : W, x₀ ≠ 0 → ∃ β : lineStab h v x₀ → (InfinitePlace E → ℂˣ), Continuous β ∧
    ∀ (p : lineStab h v x₀) (w : InfinitePlace E),
      (((p : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
        (β p w : ℂ) • vecAt v x₀ w

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StComplementArchCocompact
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def ComplementArchCocompact.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (La : AddSubgroup W) (x₀ w₀ : W) (m : ℕ),
    IsLattice (E := E) La → IsHyperbolicPair h x₀ w₀ → 0 < m →
    ∃ K : Set (InfinitePlace E → ι → ℂ), IsCompact K ∧ ∀ Y : InfinitePlace E → ι → ℂ,
      (∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w) = 0 ∧
        star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w) = 0) →
      ∃ y ∈ hypComplement h x₀ w₀, (∃ z ∈ La, y = m • z) ∧ Y - vecAt v y ∈ K

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsTorusEmbedding
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def TorusEmbedding.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ w₀ : W, IsHyperbolicPair h x₀ w₀ →
    ∃ τ : (InfinitePlace E → ℂˣ) →* archUnitary h v, Continuous τ ∧ ∀ a w,
      ((τ a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
          (a w : ℂ) • vecAt v x₀ w ∧
        ((τ a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w =
          (starRingEnd ℂ (a w : ℂ))⁻¹ • vecAt v w₀ w ∧
        ∀ z : ι → ℂ, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
          star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
          ((τ a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsRadicalTorusModulus
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def RadicalTorusModulus.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ w₀ : W, IsHyperbolicPair h x₀ w₀ →
    ∀ (g : archUnitary h v) (a : InfinitePlace E → ℂ),
    (∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = a w • vecAt v x₀ w) →
    (∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w =
      (starRingEnd ℂ (a w))⁻¹ • vecAt v w₀ w) →
    (∀ w (z : ι → ℂ), star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z) →
    ∀ (μ : Measure (unipRadical h v x₀)) [μ.IsHaarMeasure] (f : archUnitary h v → ℝ≥0∞),
      Measurable f →
      ∫⁻ n, f (g * n * g⁻¹) ∂μ = (∏ w, ‖a w‖ₑ⁻¹ ^ (2 * (finrank E W - 1))) * ∫⁻ n, f n ∂μ

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsTorusModulus
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def TorusModulus.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ w₀ : W, IsHyperbolicPair h x₀ w₀ →
    ∀ (g : archUnitary h v) (a : InfinitePlace E → ℂ),
    (∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = a w • vecAt v x₀ w) →
    (∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w =
      (starRingEnd ℂ (a w))⁻¹ • vecAt v w₀ w) →
    (∀ w (z : ι → ℂ), star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z) →
    ∀ (ν : Measure (vecFixGroup h v x₀)) [ν.IsHaarMeasure] (f : archUnitary h v → ℝ≥0∞),
      Measurable f →
      ∫⁻ x, f (g * x * g⁻¹) ∂ν = (∏ w, ‖a w‖ₑ⁻¹ ^ (2 * (finrank E W - 1))) * ∫⁻ x, f x ∂ν

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMajorantStabCompact
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped ComplexOrder

noncomputable section

namespace MajorantStabCompact

theorem form_mulVec {ι : Type*} [Fintype ι] {P A : Matrix ι ι ℂ}
    (hA : (A.map (starRingEnd ℂ))ᵀ * P * A = P) (y : ι → ℂ) :
    star (A *ᵥ y) ⬝ᵥ (P *ᵥ (A *ᵥ y)) = star y ⬝ᵥ (P *ᵥ y) := by
  have hc : (A.map (starRingEnd ℂ))ᵀ = Aᴴ := by
    ext i j
    simp [conjTranspose_apply]
  rw [hc] at hA
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hA]

end MajorantStabCompact

open MajorantStabCompact

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem MajorantStabCompact.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    MajorantStabCompact.Statement h v := by
  intro M
  set e : Fin (Fintype.card ι) → W := v ∘ (Fintype.equivFin ι).symm
  have he : Submodule.span E (Set.range e) = ⊤ := by
    rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ, v.span_eq]
  set C : ℝ := ∑ a, M.len (vecAt v (e a))
  have hcpt := BoundedInverseCompact.proof h v M _ e he C

  have hclosed : IsClosed (M.stab : Set (archUnitary h v)) := by
    have : (M.stab : Set (archUnitary h v)) = ⋂ w, {g : archUnitary h v |
        ((((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)).map (starRingEnd ℂ))ᵀ * M.P w *
          (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)) = M.P w} := by
      ext g
      simp [Majorant.stab, Subgroup.mem_subgroupOf, Subgroup.mem_pi, mem_unitaryGroupMatrix]
    rw [this]
    refine isClosed_iInter fun w => isClosed_eq ?_ continuous_const
    have hg : Continuous fun g : archUnitary h v =>
        (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)) :=
      Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)
    exact ((hg.matrix_map Complex.continuous_conj).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hg
  refine hcpt.of_isClosed_subset hclosed ?_
  intro g hg a

  have hgi : (g⁻¹ : archUnitary h v) ∈ M.stab := inv_mem hg
  have hw : ∀ w, (((((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)).map
      (starRingEnd ℂ))ᵀ * M.P w * ((((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
        Matrix ι ι ℂ)) = M.P w := by
    intro w
    have := (Subgroup.mem_pi _).mp (Subgroup.mem_subgroupOf.mp hgi) w (Set.mem_univ w)
    exact mem_unitaryGroupMatrix.mp this
  have heq : M.len (invApply g (vecAt v (e a))) = M.len (vecAt v (e a)) := by
    simp only [Majorant.len, invApply]
    congr 1
    exact Finset.sum_congr rfl fun w _ => by rw [form_mulVec (hw w)]
  rw [heq]
  exact Finset.single_le_sum (f := fun a => M.len (vecAt v (e a)))
    (fun b _ => Real.sqrt_nonneg _) (Finset.mem_univ a)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
