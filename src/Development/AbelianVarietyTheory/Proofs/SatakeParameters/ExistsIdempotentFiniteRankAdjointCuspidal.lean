module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixNoInvariantSubspaceFiniteField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BarKHomSurjective
noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.IdemAdj

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
def barKHom : Kinf E a →* Kinf E a where
  toFun := barK
  map_one' := Subtype.ext (by ext i j : 1; simp [barK, Matrix.one_apply])
  map_mul' k k' := Subtype.ext (by
    change Matrix.transpose (star (k.1 * k'.1)) = Matrix.transpose (star k.1) * Matrix.transpose (star k'.1)
    ext i j
    simp [Matrix.mul_apply, Matrix.star_apply, mul_comm])



omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem barK_barK (k : Kinf E a) : barK (barK k) = k := Subtype.ext (by
  ext i j
  simp [barK, Matrix.star_apply])


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem barKHom_surjective : Function.Surjective (barKHom E a) := fun k => ⟨barK k, barK_barK k⟩

def cptOn (π : CuspSub E a) : Representation ℂ (Kinf E a) π.V where
  toFun k := π.op (.cpt k)
  map_one' := by
    ext φ
    simp [CuspSub.op, act]
  map_mul' k k' := by
    ext φ
    simp [CuspSub.op, act, map_mul]

@[simp] theorem cptOn_val (π : CuspSub E a) (k : Kinf E a) (φ : π.V) :
    (cptOn π k φ).1 = cptRep E a k φ.1 := rfl

end GlobalTheory.IdemAdj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTypeClosurePreservedByArchCompactIntertw
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTypeClosurePreservedByArchCompactIntertw
open NumberField GlobalTheory.CuspRep GlobalTheory.Published GlobalTheory.IdemAdj

namespace GlobalTheory.IdemAdj

theorem typeClosure_of_intertwine : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ₀ : Representation ℂ (Kinf E a) W) (U : Submodule ℂ π.V), FiniteDimensional ℂ U → (∀ k, ∀ u ∈ U, cptOn π k u ∈ U) → ∀ f : π.V →ₗ[ℂ] π.V, (∀ k, ∀ u ∈ U, f (cptOn π k u) = cptOn π k (f u)) → ∀ u ∈ U, (∀ g, (fun k : Kinf E a => (cptRep E a k u.1).1 g) ∈ AutFin.coeffSpan ρ₀) → ∀ g, (fun k : Kinf E a => (cptRep E a k (f u).1).1 g) ∈ AutFin.coeffSpan ρ₀ := by
  intro E _ _ _ a π W _ _ ρ₀ U hU hst f hf u hu hcoef g
  haveI := hU
  let w : Kinf E a → U := fun k => ⟨cptOn π k u, hst k u hu⟩
  let A : (U →ₗ[ℂ] ℂ) →ₗ[ℂ] (Kinf E a → ℂ) :=
    { toFun := fun ℓ k => ℓ (w k), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let ev : GA E a → (U →ₗ[ℂ] ℂ) := fun h =>
    (LinearMap.proj h).comp ((Sm E a).subtype.comp (π.V.subtype.comp U.subtype))
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    haveI hfr : Module.Free ℂ ((U →ₗ[ℂ] ℂ) ⧸ Submodule.span ℂ (Set.range ev)) :=
      Module.Free.of_divisionRing ℂ _
    haveI : Module.Projective ℂ ((U →ₗ[ℂ] ℂ) ⧸ Submodule.span ℂ (Set.range ev)) :=
      @Module.Projective.of_free _ _ _ _ _ hfr
    refine Submodule.span_eq_top_of_ne_zero fun z hz => ?_
    by_contra hc
    push_neg at hc
    exact hz (Subtype.ext (Subtype.ext (Subtype.ext (funext fun h => hc _ ⟨h, rfl⟩))))
  let L : U →ₗ[ℂ] ℂ :=
    (LinearMap.proj g).comp ((Sm E a).subtype.comp (π.V.subtype.comp (f.comp U.subtype)))
  have hL : L ∈ (AutFin.coeffSpan ρ₀).comap A := by
    have hmem : L ∈ Submodule.span ℂ (Set.range ev) := hspan ▸ Submodule.mem_top
    refine (Submodule.span_le.2 ?_) hmem
    rintro _ ⟨h, rfl⟩
    exact hcoef h
  have key : (fun k : Kinf E a => (cptRep E a k (f u).1).1 g) = A L := by
    funext k
    show _ = (f (cptOn π k u)).1.1 g
    rw [hf k u hu, cptOn_val]
  rw [key]
  exact hL

end GlobalTheory.IdemAdj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTypeClosurePreservedByArchCompactIntertwStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.Published GlobalTheory.IdemAdj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_typeClosure_preserved_by_archCompact_intertwiner : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ₀ : Representation ℂ (Kinf E a) W) (U : Submodule ℂ π.V), FiniteDimensional ℂ U → (∀ k, ∀ u ∈ U, cptOn π k u ∈ U) → ∀ f : π.V →ₗ[ℂ] π.V, (∀ k, ∀ u ∈ U, f (cptOn π k u) = cptOn π k (f u)) → ∀ u ∈ U, (∀ g, (fun k : Kinf E a => (cptRep E a k u.1).1 g) ∈ AutFin.coeffSpan ρ₀) → ∀ g, (fun k : Kinf E a => (cptRep E a k (f u).1).1 g) ∈ AutFin.coeffSpan ρ₀ := by
  first | exact @GlobalTheory.IdemAdj.typeClosure_of_intertwine | exact GlobalTheory.IdemAdj.typeClosure_of_intertwine | (intros; apply GlobalTheory.IdemAdj.typeClosure_of_intertwine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplementWithoutCommonIrreducibleTypes
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplementWithoutCommonIrreducibleTypes
namespace GlobalTheory

namespace TypeComplement

variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}

def supRep (P : Subrepresentation ρ → Prop) : Subrepresentation ρ where
  toSubmodule := ⨆ (S : Subrepresentation ρ) (_ : P S), S.toSubmodule
  apply_mem_toSubmodule k := by
    have h : (⨆ (S : Subrepresentation ρ) (_ : P S), S.toSubmodule) ≤
        (⨆ (S : Subrepresentation ρ) (_ : P S), S.toSubmodule).comap (ρ k) := by
      refine iSup₂_le fun S hS x hx => ?_
      exact (le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : P S) => S.toSubmodule) S hS)
        (S.apply_mem_toSubmodule k hx)
    exact fun v hv => h hv

def imRep (f : V →ₗ[ℂ] V) (hf : ∀ k v, f (ρ k v) = ρ k (f v)) (S : Subrepresentation ρ) :
    Subrepresentation ρ where
  toSubmodule := S.toSubmodule.map f
  apply_mem_toSubmodule k := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨ρ k s, S.apply_mem_toSubmodule k hs, hf k s⟩

def preRep (f : V →ₗ[ℂ] V) (hf : ∀ k v, f (ρ k v) = ρ k (f v)) (S C : Subrepresentation ρ) :
    Subrepresentation ρ where
  toSubmodule := S.toSubmodule ⊓ C.toSubmodule.comap f
  apply_mem_toSubmodule k := by
    rintro v ⟨hv1, hv2⟩
    refine ⟨S.apply_mem_toSubmodule k hv1, ?_⟩
    show f (ρ k v) ∈ C.toSubmodule
    rw [hf k v]
    exact C.apply_mem_toSubmodule k hv2

theorem toSubmodule_bot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl

theorem ne_bot_iff_toSubmodule {S : Subrepresentation ρ} : S ≠ ⊥ ↔ S.toSubmodule ≠ ⊥ := by
  constructor
  · intro h h'
    exact h (Subrepresentation.toSubmodule_injective h')
  · rintro h rfl
    exact h rfl

end TypeComplement

end GlobalTheory

namespace GlobalTheory
namespace TypeComplement
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}

theorem imRep_atom (f : V →ₗ[ℂ] V) (hf : ∀ k v, f (ρ k v) = ρ k (f v)) {S : Subrepresentation ρ}
    (hS : IsAtom S) (hne : ∃ s ∈ S.toSubmodule, f s ≠ 0) :
    IsAtom (imRep f hf S) ∧
      Nonempty (S.toRepresentation.Equiv (imRep f hf S).toRepresentation) := by
  obtain ⟨s₀, hs₀, hfs₀⟩ := hne

  have hinj : Function.Injective (f ∘ₗ S.toSubmodule.subtype) := by
    let Kr : Subrepresentation ρ := preRep f hf S ⊥
    have hK : Kr ≤ S := fun v hv => hv.1
    rcases hS.le_iff.mp hK with h | h
    · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      have hx' : (x : V) ∈ Kr.toSubmodule := by
        refine ⟨x.2, ?_⟩
        show f x ∈ (⊥ : Submodule ℂ V)
        simpa using hx
      rw [h] at hx'
      simp only [toSubmodule_bot, Submodule.mem_bot] at hx'
      simpa using Subtype.ext hx'
    · exfalso
      have : s₀ ∈ Kr.toSubmodule := by rw [h]; exact hs₀
      exact hfs₀ ((Submodule.mem_bot ℂ).mp (show f s₀ ∈ (⊥ : Submodule ℂ V) from this.2))
  refine ⟨⟨?_, fun C hC => ?_⟩, ?_⟩
  · rw [ne_bot_iff_toSubmodule]
    intro h
    have : f s₀ ∈ (imRep f hf S).toSubmodule := ⟨s₀, hs₀, rfl⟩
    rw [h] at this
    exact hfs₀ ((Submodule.mem_bot ℂ).mp this)
  · by_contra hC0
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (ne_bot_iff_toSubmodule.mp hC0)
    obtain ⟨s, hs, rfl⟩ : c ∈ (imRep f hf S).toSubmodule := hC.le hc
    have hB : preRep f hf S C ≤ S := fun v hv => hv.1
    rcases hS.le_iff.mp hB with h | h
    · have : s ∈ (preRep f hf S C).toSubmodule := ⟨hs, hc⟩
      rw [h] at this
      simp only [toSubmodule_bot, Submodule.mem_bot] at this
      exact hc0 (by simp [this])
    · have hle : imRep f hf S ≤ C := by
        rintro _ ⟨t, ht, rfl⟩
        have : t ∈ (preRep f hf S C).toSubmodule := by rw [h]; exact ht
        exact this.2
      exact lt_irrefl _ (lt_of_lt_of_le hC hle)
  · have hr : LinearMap.range (f ∘ₗ S.toSubmodule.subtype) = (imRep f hf S).toSubmodule := by
      rw [LinearMap.range_comp, Submodule.range_subtype]; rfl
    let e : S.toSubmodule ≃ₗ[ℂ] (imRep f hf S).toSubmodule :=
      (LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hr)
    refine ⟨Representation.Equiv.mk e fun k => ?_⟩
    ext x
    simp [e, Subrepresentation.toRepresentation, hf]

end TypeComplement
end GlobalTheory

namespace GlobalTheory
namespace TypeComplement

theorem exists_typeComplement : ∀ (K V : Type) [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V), ρ.IsSemisimpleRepresentation → (∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule) → ∀ X : Subrepresentation ρ, (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → S₂ ≤ X → Nonempty (S₁.toRepresentation.Equiv S₂.toRepresentation) → S₁ ≤ X) → ∃ Y : Subrepresentation ρ, IsCompl X.toSubmodule Y.toSubmodule ∧ (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → IsAtom S₂ → S₁ ≤ Y → S₂ ≤ X → IsEmpty (S₁.toRepresentation.Equiv S₂.toRepresentation)) ∧ ∀ T : V →ₗ[ℂ] V, (∀ k v, T (ρ k v) = ρ k (T v)) → (∀ v ∈ X.toSubmodule, T v ∈ X.toSubmodule) ∧ ∀ v ∈ Y.toSubmodule, T v ∈ Y.toSubmodule := by
  intro K V _ _ _ ρ hss hsum X hcl
  haveI : ComplementedLattice (Subrepresentation ρ) := hss
  let Y : Subrepresentation ρ := supRep (fun S => IsAtom S ∧ ¬ S ≤ X)
  have hYle : ∀ S : Subrepresentation ρ, IsAtom S → ¬ S ≤ X → S.toSubmodule ≤ Y.toSubmodule :=
    fun S hA hn => le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : IsAtom S ∧ ¬ S ≤ X) =>
      S.toSubmodule) S ⟨hA, hn⟩

  obtain ⟨Y₀, hY₀⟩ := exists_isCompl X
  have hXY₀ : IsCompl X.toSubmodule Y₀.toSubmodule := by
    constructor
    · rw [disjoint_iff]
      exact congrArg Subrepresentation.toSubmodule hY₀.inf_eq_bot
    · rw [codisjoint_iff]
      exact congrArg Subrepresentation.toSubmodule hY₀.sup_eq_top
  let p : V →ₗ[ℂ] V := X.toSubmodule.projection Y₀.toSubmodule hXY₀
  have hp : ∀ k v, p (ρ k v) = ρ k (p v) := by
    intro k v
    have hv : v ∈ X.toSubmodule ⊔ Y₀.toSubmodule := by rw [hXY₀.sup_eq_top]; trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    have h1 : ∀ {a b : V}, a ∈ X.toSubmodule → b ∈ Y₀.toSubmodule → p (a + b) = a := by
      intro a b ha hb
      rw [map_add (f := _), Submodule.projection_apply_of_mem_left _ ha]
      have : p b = 0 := (Submodule.projection_apply_eq_zero_iff hXY₀).mpr hb
      rw [this, add_zero]
    rw [map_add (f := _), h1 (X.apply_mem_toSubmodule k hx) (Y₀.apply_mem_toSubmodule k hy), h1 hx hy]

  have hYY₀ : Y.toSubmodule ≤ Y₀.toSubmodule := by
    refine iSup₂_le fun S ⟨hA, hn⟩ => ?_
    by_contra hc
    have hne : ∃ s ∈ S.toSubmodule, p s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hc fun s hs => (Submodule.projection_apply_eq_zero_iff hXY₀).mp (h s hs)
    obtain ⟨_, ⟨e⟩⟩ := imRep_atom p hp hA hne
    have hle : imRep p hp S ≤ X := by
      rintro _ ⟨s, _, rfl⟩
      exact Submodule.projection_apply_mem hXY₀ s
    exact hn (hcl S _ hA hle ⟨e⟩)
  have hdisj : X.toSubmodule ⊓ Y.toSubmodule = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ hYY₀).trans (disjoint_iff.mp hXY₀.disjoint).le)
  refine ⟨Y, ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr ?_⟩, ?_, ?_⟩
  ·
    refine eq_top_iff.mpr ?_
    show (⊤ : Subrepresentation ρ).toSubmodule ≤ _
    refine (hsum ⊤).le.trans (iSup₂_le fun S ⟨hA, _⟩ => ?_)
    by_cases hSX : S ≤ X
    · exact le_sup_of_le_left hSX
    · exact le_sup_of_le_right (hYle S hA hSX)
  ·
    intro S₁ S₂ hS₁ _ hY hX
    refine ⟨fun e => ?_⟩
    have h₁ : S₁ ≤ X := hcl S₁ S₂ hS₁ hX ⟨e⟩
    apply hS₁.1
    apply Subrepresentation.toSubmodule_injective
    rw [toSubmodule_bot, eq_bot_iff, ← hdisj]
    exact le_inf h₁ hY
  · intro T hT
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have hX : X.toSubmodule ≤ X.toSubmodule.comap T := by
        refine (hsum X).le.trans (iSup₂_le fun S ⟨hA, hSX⟩ => ?_)
        by_cases hne : ∃ s ∈ S.toSubmodule, T s ≠ 0
        · obtain ⟨hA', ⟨e⟩⟩ := imRep_atom T hT hA hne
          have hle : imRep T hT S ≤ X := hcl _ S hA' hSX ⟨e.symm⟩
          exact fun s hs => hle ⟨s, hs, rfl⟩
        · push_neg at hne
          intro s hs
          show T s ∈ X.toSubmodule
          rw [hne s hs]
          exact zero_mem _
      exact hX hv
    · have hY : Y.toSubmodule ≤ Y.toSubmodule.comap T := by
        refine iSup₂_le fun S ⟨hA, hn⟩ => ?_
        by_cases hne : ∃ s ∈ S.toSubmodule, T s ≠ 0
        · obtain ⟨hA', ⟨e⟩⟩ := imRep_atom T hT hA hne
          have hnX : ¬ imRep T hT S ≤ X := fun hle => hn (hcl S _ hA hle ⟨e⟩)
          exact fun s hs => hYle _ hA' hnX ⟨s, hs, rfl⟩
        · push_neg at hne
          intro s hs
          show T s ∈ Y.toSubmodule
          rw [hne s hs]
          exact zero_mem _
      exact hY hv

end TypeComplement
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplementWithoutCommonIrreducibleTypesStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complement_without_common_irreducible_types : ∀ (K V : Type) [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V), ρ.IsSemisimpleRepresentation → (∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule) → ∀ X : Subrepresentation ρ, (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → S₂ ≤ X → Nonempty (S₁.toRepresentation.Equiv S₂.toRepresentation) → S₁ ≤ X) → ∃ Y : Subrepresentation ρ, IsCompl X.toSubmodule Y.toSubmodule ∧ (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → IsAtom S₂ → S₁ ≤ Y → S₂ ≤ X → IsEmpty (S₁.toRepresentation.Equiv S₂.toRepresentation)) ∧ ∀ T : V →ₗ[ℂ] V, (∀ k v, T (ρ k v) = ρ k (T v)) → (∀ v ∈ X.toSubmodule, T v ∈ X.toSubmodule) ∧ ∀ v ∈ Y.toSubmodule, T v ∈ Y.toSubmodule := by
  first | exact @GlobalTheory.TypeComplement.exists_typeComplement | exact GlobalTheory.TypeComplement.exists_typeComplement | (intros; apply GlobalTheory.TypeComplement.exists_typeComplement <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsComplOrthogonalOfNoCommonIrreducibleTypes
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsComplOrthogonalOfNoCommonIrreducibleTypes
open Module

namespace GlobalTheory.IsotypicOrth

variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}
  {σ : K →* K}

lemma pair_left (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    (k : K) (x y : V) : B (ρ k x) y = B x (ρ (σ k⁻¹) y) := by
  rw [← hB k x (ρ (σ k⁻¹) y), map_inv, Representation.self_inv_apply]

lemma left_ker_zero (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S : Subrepresentation ρ} (h₁ : IsAtom S₁)
    (hn : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    ∀ x ∈ S₁.toSubmodule, (∀ y ∈ S.toSubmodule, B x y = 0) → x = 0 := by
  let T : Subrepresentation ρ :=
    ⟨S₁.toSubmodule ⊓ ⨅ y ∈ S.toSubmodule, LinearMap.ker (B.flip y), by
      intro k x hx
      simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
        LinearMap.flip_apply] at hx ⊢
      refine ⟨S₁.apply_mem_toSubmodule k hx.1, fun y hy => ?_⟩
      rw [pair_left B hB]
      exact hx.2 _ (S.apply_mem_toSubmodule _ hy)⟩
  have hle : T ≤ S₁ := fun x hx => (Submodule.mem_inf.mp hx).1
  have hmem : ∀ x ∈ S₁.toSubmodule, (∀ y ∈ S.toSubmodule, B x y = 0) → x ∈ T.toSubmodule := by
    intro x hx h0
    simp only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
    exact ⟨hx, h0⟩
  rcases h₁.le_iff.mp hle with h | h
  · intro x hx h0
    have hT : T.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h
    have := hmem x hx h0
    rw [hT] at this
    exact (Submodule.mem_bot ℂ).mp this
  · exfalso
    obtain ⟨x, hx, y, hy, hne⟩ := hn
    have hT : T.toSubmodule = S₁.toSubmodule := congrArg Subrepresentation.toSubmodule h
    rw [← hT] at hx
    simp only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.flip_apply] at hx
    exact hne (hx.2 y hy)

lemma right_ker_zero (hσ : Function.Surjective σ) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S : Subrepresentation ρ} (h : IsAtom S)
    (hn : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    ∀ y ∈ S.toSubmodule, (∀ x ∈ S₁.toSubmodule, B x y = 0) → y = 0 := by
  let T : Subrepresentation ρ :=
    ⟨S.toSubmodule ⊓ ⨅ x ∈ S₁.toSubmodule, LinearMap.ker (B x), by
      intro k' y hy
      obtain ⟨k, rfl⟩ := hσ k'
      simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
      refine ⟨S.apply_mem_toSubmodule _ hy.1, fun x hx => ?_⟩
      have e := hB k (ρ k⁻¹ x) y
      rw [Representation.self_inv_apply] at e
      rw [e]
      exact hy.2 _ (S₁.apply_mem_toSubmodule _ hx)⟩
  have hle : T ≤ S := fun x hx => (Submodule.mem_inf.mp hx).1
  have hmem : ∀ y ∈ S.toSubmodule, (∀ x ∈ S₁.toSubmodule, B x y = 0) → y ∈ T.toSubmodule := by
    intro y hy h0
    simp only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
    exact ⟨hy, h0⟩
  rcases h.le_iff.mp hle with h' | h'
  · intro y hy h0
    have hT : T.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h'
    have := hmem y hy h0
    rw [hT] at this
    exact (Submodule.mem_bot ℂ).mp this
  · exfalso
    obtain ⟨x, hx, y, hy, hne⟩ := hn
    have hT : T.toSubmodule = S.toSubmodule := congrArg Subrepresentation.toSubmodule h'
    rw [← hT] at hy
    simp only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hy
    exact hne (hy.2 x hx)

lemma restr_injective (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S : Subrepresentation ρ} (h₁ : IsAtom S₁)
    (hn : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    Function.Injective (B.domRestrict₁₂ S₁.toSubmodule S.toSubmodule) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  apply Subtype.ext
  refine left_ker_zero B hB h₁ hn a a.2 fun y hy => ?_
  have := LinearMap.congr_fun ha ⟨y, hy⟩
  simpa [LinearMap.domRestrict₁₂_apply] using this

lemma restr_flip_injective (hσ : Function.Surjective σ) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S : Subrepresentation ρ} (h : IsAtom S)
    (hn : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    Function.Injective (B.domRestrict₁₂ S₁.toSubmodule S.toSubmodule).flip := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  apply Subtype.ext
  refine right_ker_zero hσ B hB h hn a a.2 fun x hx => ?_
  have := LinearMap.congr_fun ha ⟨x, hx⟩
  simpa [LinearMap.domRestrict₁₂_apply] using this

theorem nonempty_equiv_of_pair (hσ : Function.Surjective σ)
    (hfin : ∀ S : Subrepresentation ρ, IsAtom S → FiniteDimensional ℂ S.toSubmodule)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S₂ S : Subrepresentation ρ} (h₁ : IsAtom S₁) (h₂ : IsAtom S₂) (h : IsAtom S)
    (hn₁ : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0)
    (hn₂ : ∃ x ∈ S₂.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    Nonempty (S₁.toRepresentation.Equiv S₂.toRepresentation) := by
  haveI := hfin S₁ h₁
  haveI := hfin S₂ h₂
  haveI := hfin S h
  set f₁ := B.domRestrict₁₂ S₁.toSubmodule S.toSubmodule with hf₁def
  set f₂ := B.domRestrict₁₂ S₂.toSubmodule S.toSubmodule with hf₂def
  have i₁ : Function.Injective f₁ := restr_injective B hB h₁ hn₁
  have i₂ : Function.Injective f₂ := restr_injective B hB h₂ hn₂
  have j₁ : Function.Injective f₁.flip := restr_flip_injective hσ B hB h hn₁
  have j₂ : Function.Injective f₂.flip := restr_flip_injective hσ B hB h hn₂
  have d₁ : finrank ℂ S₁.toSubmodule = finrank ℂ (Dual ℂ S.toSubmodule) := by
    rw [Subspace.dual_finrank_eq]
    refine le_antisymm ?_ ?_
    · exact (LinearMap.finrank_le_finrank_of_injective i₁).trans_eq Subspace.dual_finrank_eq
    · exact (LinearMap.finrank_le_finrank_of_injective j₁).trans_eq Subspace.dual_finrank_eq
  have d₂ : finrank ℂ S₂.toSubmodule = finrank ℂ (Dual ℂ S.toSubmodule) := by
    rw [Subspace.dual_finrank_eq]
    refine le_antisymm ?_ ?_
    · exact (LinearMap.finrank_le_finrank_of_injective i₂).trans_eq Subspace.dual_finrank_eq
    · exact (LinearMap.finrank_le_finrank_of_injective j₂).trans_eq Subspace.dual_finrank_eq
  let e₁ := LinearEquiv.ofBijective f₁ ⟨i₁, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank d₁).mp i₁⟩
  let e₂ := LinearEquiv.ofBijective f₂ ⟨i₂, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank d₂).mp i₂⟩
  let e := e₁.trans e₂.symm
  have hfe : ∀ x, f₂ (e x) = f₁ x := by
    intro x
    have h1 : ∀ z, e₁ z = f₁ z := fun z => LinearEquiv.ofBijective_apply _ _
    have h2 : ∀ z, e₂ z = f₂ z := fun z => LinearEquiv.ofBijective_apply _ _
    rw [← h1, ← h2]
    simp [e]
  have hcomm : ∀ (x : S₁.toSubmodule) (y : S.toSubmodule), B (e x : V) y = B x y := by
    intro x y
    have := LinearMap.congr_fun (hfe x) y
    simpa [f₁, f₂, LinearMap.domRestrict₁₂_apply] using this
  refine ⟨Representation.Equiv.mk e fun k => ?_⟩
  apply LinearMap.ext
  intro x
  apply i₂
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hf₂def, LinearMap.domRestrict₁₂_apply]
  rw [hcomm]
  change B (ρ k x) y = B (ρ k (e x)) y
  rw [pair_left B hB, pair_left B hB]
  exact (hcomm x ⟨_, S.apply_mem_toSubmodule _ y.2⟩).symm

lemma exists_atom_pair
    (hsum : ∀ X : Subrepresentation ρ,
      X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (Y : Subrepresentation ρ) (ψ : V)
    (h : ∃ y ∈ Y.toSubmodule, B y ψ ≠ 0) :
    ∃ S₁ : Subrepresentation ρ, IsAtom S₁ ∧ S₁ ≤ Y ∧ ∃ x ∈ S₁.toSubmodule, B x ψ ≠ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨y, hy, hne⟩ := h
  apply hne
  have hle : Y.toSubmodule ≤ LinearMap.ker (B.flip ψ) := by
    rw [hsum Y]
    exact iSup₂_le fun S hS x hx => by simpa using hc S hS.1 hS.2 x hx
  simpa using hle hy

end GlobalTheory.IsotypicOrth

namespace GlobalTheory.IsotypicOrth

theorem orth_isCompl : ∀ (K V : Type) [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V) (σ : K →* K), Function.Surjective σ → (∀ S : Subrepresentation ρ, IsAtom S → FiniteDimensional ℂ S.toSubmodule) → (∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule) → ∀ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ) → ∀ X Y : Subrepresentation ρ, IsCompl X.toSubmodule Y.toSubmodule → (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → IsAtom S₂ → S₁ ≤ Y → S₂ ≤ X → IsEmpty (S₁.toRepresentation.Equiv S₂.toRepresentation)) → IsCompl (⨅ y ∈ Y.toSubmodule, LinearMap.ker (B y)) (⨅ x ∈ X.toSubmodule, LinearMap.ker (B x)) := by
  intro K V _ _ _ ρ σ hσ hfin hsum B _hl hr hB X Y hXY hiso
  constructor
  · rw [Submodule.disjoint_def]
    intro ψ h1 h2
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h1 h2
    apply hr
    intro φ
    have : φ ∈ X.toSubmodule ⊔ Y.toSubmodule := by rw [hXY.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp this
    rw [map_add (f := _), LinearMap.add_apply, h1 b hb, h2 a ha, add_zero]
  · rw [codisjoint_iff, eq_top_iff]
    have htop := hsum ⊤
    change (⊤ : Submodule ℂ V) = _ at htop
    rw [htop]
    refine iSup₂_le fun S hS => ?_
    by_cases hY : S.toSubmodule ≤ ⨅ y ∈ Y.toSubmodule, LinearMap.ker (B y)
    · exact le_sup_of_le_left hY
    by_cases hX : S.toSubmodule ≤ ⨅ x ∈ X.toSubmodule, LinearMap.ker (B x)
    · exact le_sup_of_le_right hX
    exfalso
    obtain ⟨ψ₁, hψ₁, hψ₁'⟩ := SetLike.not_le_iff_exists.mp hY
    obtain ⟨ψ₂, hψ₂, hψ₂'⟩ := SetLike.not_le_iff_exists.mp hX
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, not_forall] at hψ₁' hψ₂'
    obtain ⟨y, hy, hy'⟩ := hψ₁'
    obtain ⟨x, hx, hx'⟩ := hψ₂'
    obtain ⟨S₁, a₁, l₁, x₁, hx₁, n₁⟩ := exists_atom_pair hsum B Y ψ₁ ⟨y, hy, hy'⟩
    obtain ⟨S₂, a₂, l₂, x₂, hx₂, n₂⟩ := exists_atom_pair hsum B X ψ₂ ⟨x, hx, hx'⟩
    have e := nonempty_equiv_of_pair hσ hfin B hB a₁ a₂ hS.1 ⟨x₁, hx₁, ψ₁, hψ₁, n₁⟩
      ⟨x₂, hx₂, ψ₂, hψ₂, n₂⟩
    exact (hiso S₁ S₂ a₁ a₂ l₁ l₂).false e.some

end GlobalTheory.IsotypicOrth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsComplOrthogonalOfNoCommonIrreducibleTypesStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompl_orthogonal_of_no_common_irreducible_types : ∀ (K V : Type) [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V) (σ : K →* K), Function.Surjective σ → (∀ S : Subrepresentation ρ, IsAtom S → FiniteDimensional ℂ S.toSubmodule) → (∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule) → ∀ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ) → ∀ X Y : Subrepresentation ρ, IsCompl X.toSubmodule Y.toSubmodule → (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → IsAtom S₂ → S₁ ≤ Y → S₂ ≤ X → IsEmpty (S₁.toRepresentation.Equiv S₂.toRepresentation)) → IsCompl (⨅ y ∈ Y.toSubmodule, LinearMap.ker (B y)) (⨅ x ∈ X.toSubmodule, LinearMap.ker (B x)) := by
  first | exact @GlobalTheory.IsotypicOrth.orth_isCompl | exact GlobalTheory.IsotypicOrth.orth_isCompl | (intros; apply GlobalTheory.IsotypicOrth.orth_isCompl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdempotentFiniteRankAdjointCuspidal
noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.PRep GlobalTheory.Published

namespace GlobalTheory.IdemAdj

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem coeffSpan_mul_right {W : Type} [AddCommGroup W] [Module ℂ W] (ρ₀ : Representation ℂ (Kinf E a) W)
    (k' : Kinf E a) {f : Kinf E a → ℂ} (hf : f ∈ AutFin.coeffSpan ρ₀) : (fun k => f (k * k')) ∈ AutFin.coeffSpan ρ₀ := by
  let T : (Kinf E a → ℂ) →ₗ[ℂ] (Kinf E a → ℂ) :=
    { toFun := fun f k => f (k * k'), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have : AutFin.coeffSpan ρ₀ ≤ (AutFin.coeffSpan ρ₀).comap T := Submodule.span_le.2 (by
    rintro _ ⟨ℓ, w, rfl⟩
    exact Submodule.subset_span ⟨ℓ, ρ₀ k' w, funext fun k => by simp [T, map_mul]⟩)
  exact this hf

def typeSub (π : CuspSub E a) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ₀ : Representation ℂ (Kinf E a) W) :
    Subrepresentation (cptOn π) where
  toSubmodule :=
    { carrier := {ψ | ∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k ψ.1).1 g) ∈ AutFin.coeffSpan ρ₀}
      add_mem' := fun {x y} hx hy g => by
        have e : (fun k : Kinf E a => (cptRep E a k (x + y).1).1 g) =
            (fun k : Kinf E a => (cptRep E a k x.1).1 g) + (fun k : Kinf E a => (cptRep E a k y.1).1 g) := by
          funext k; simp
        rw [e]; exact add_mem (hx g) (hy g)
      zero_mem' := fun g => by
        have e : (fun k : Kinf E a => (cptRep E a k (0 : π.V).1).1 g) = 0 := by funext k; simp
        rw [e]; exact zero_mem _
      smul_mem' := fun c x hx g => by
        have e : (fun k : Kinf E a => (cptRep E a k (c • x).1).1 g) = c • (fun k : Kinf E a => (cptRep E a k x.1).1 g) := by
          funext k; simp
        rw [e]; exact Submodule.smul_mem _ c (hx g) }
  apply_mem_toSubmodule k' ψ hψ g := by
    have e : (fun k : Kinf E a => (cptRep E a k (cptOn π k' ψ).1).1 g) =
        fun k => (fun k : Kinf E a => (cptRep E a k ψ.1).1 g) (k * k') := by
      funext k; simp [map_mul]
    rw [e]; exact coeffSpan_mul_right ρ₀ k' (hψ g)

theorem adj_of_isCompl {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) {X Y : Submodule ℂ V} {X' Y' : Submodule ℂ V'} (h : IsCompl X Y) (h' : IsCompl X' Y')
    (h1 : ∀ y ∈ Y, ∀ x' ∈ X', B y x' = 0) (h2 : ∀ x ∈ X, ∀ y' ∈ Y', B x y' = 0) (φ : V) (ψ : V') :
    B (X.projection Y h φ) ψ = B φ (X'.projection Y' h' ψ) := by
  have eφ := Submodule.projection_add_projection_eq_self h φ
  have eψ := Submodule.projection_add_projection_eq_self h' ψ
  have m1 := h2 _ (Submodule.projection_apply_mem h φ) _ (Submodule.projection_apply_mem h'.symm ψ)
  have m2 := h1 _ (Submodule.projection_apply_mem h.symm φ) _ (Submodule.projection_apply_mem h' ψ)
  calc B (X.projection Y h φ) ψ = B (X.projection Y h φ) (X'.projection Y' h' ψ + Y'.projection X' h'.symm ψ) := by
        rw [eψ]
    _ = B (X.projection Y h φ + Y.projection X h.symm φ) (X'.projection Y' h' ψ) := by
        rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, m1, m2]
    _ = _ := by rw [eφ]

theorem idem_adj {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (σ : G →* G) {H : Subgroup G} (hH : IsCompact (H : Set G))
    (hH' : IsCompact ((H.map σ : Subgroup G) : Set G)) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ) (φ ψ : V) :
    B (LocGL.idem hρ hH φ) ψ = B φ (LocGL.idem hρ hH' ψ) := by
  refine adj_of_isCompl B (LocGL.isCompl_fixed_twKer hρ hH) (LocGL.isCompl_fixed_twKer hρ hH') ?_ ?_ φ ψ
  · intro y hy x' hx'
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨n, v, rfl⟩ := hz
      have hf : ρ (σ n) x' = x' := GlobalTheory.Parabolic.mem_fixed.1 hx' _ ⟨n, n.2, rfl⟩
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, LinearMap.sub_apply]
      rw [← hB n v x', hf, sub_self]
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  · intro x hx y' hy'
    induction hy' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨m, hm⟩, w, rfl⟩ := hz
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hm
      have hf : ρ n x = x := GlobalTheory.Parabolic.mem_fixed.1 hx _ hn
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
      rw [← hB n x w, hf, sub_self]
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]

theorem finiteDimensional_typeSub_fixed (h : AutomorphicFormsFiniteGL) (π : CuspSub E a) {W : Type} [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] {ρ₀ : Representation ℂ (Kinf E a) W} (hρ₀ : AutFin.IsContRep ρ₀)
    {K' : Subgroup (GL (Fin a) (Af E))} (hK : IsOpen (K' : Set (GL (Fin a) (Af E)))) :
    FiniteDimensional ℂ ↥((typeSub π ρ₀).toSubmodule ⊓ fixed π.finPart K') := by
  have hc : ∀ τ u, ∃ c : ℂ, ∀ φ ∈ π.V, cap τ u φ = c • φ := fun τ u =>
    π.exists_scalar (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) fun o => by
      cases o with
      | fin k => exact commute_cap_finRep τ u k
      | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
      | lie X => exact commute_cap_lie τ u X
  choose c hc using hc
  have := h E a K' hK W ρ₀ hρ₀ c
  refine FiniteDimensional.of_injective ((π.V.subtype ∘ₗ ((typeSub π ρ₀).toSubmodule ⊓ fixed π.finPart K').subtype).codRestrict
    (Submodule.span ℂ (AutFinGL.forms K' ρ₀ c))
    fun v => Submodule.subset_span ⟨(π.cusp _ v.1.2).1, fun k hk => congrArg Subtype.val
      (GlobalTheory.Parabolic.mem_fixed.1 v.2.2 k hk), v.2.1, fun τ u => hc τ u _ v.1.2⟩)
    fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))

theorem exists_idem_adj : AutomorphicFormsFiniteGL → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ)
    (π : CuspSub L a), ∃ P : Module.End ℂ π.V, P ≠ 0 ∧ P ∘ₗ P = P ∧ FiniteDimensional ℂ (LinearMap.range P) ∧
      ∀ s : Op L a → Op L a, (s = invTOp ∨ s = conjOp) → ∀ B : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ,
        (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) →
        (∀ k φ ψ, B (π.op (.fin k) φ) (π.op (s (.fin k)) ψ) = B φ ψ) →
        (∀ k φ ψ, B (π.op (.cpt k) φ) (π.op (s (.cpt k)) ψ) = B φ ψ) →
        (∀ X φ ψ, B (π.op (.lie X) φ) ψ + B φ (π.op (s (.lie X)) ψ) = 0) →
        ∃ P' : Module.End ℂ π.V, ∀ φ ψ, B (P φ) ψ = B φ (P' ψ) := by
  intro h L _ _ _ a π
  haveI := GlobalTheory.T.compactSpace_maximalCompact_unitary_infinite L a

  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  set φ₀ : π.V := ⟨φ, hφ⟩ with hφ₀
  have h0' : φ₀ ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  obtain ⟨U, hUo, hUc⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact L a
  set K' : Subgroup (GL (Fin a) (Af L)) := U ⊓ LocEx.stab π.finPart φ₀ with hK'
  have hKo : IsOpen (K' : Set (GL (Fin a) (Af L))) := hUo.inter (π.isSmooth_finPart φ₀)
  have hKc : IsCompact (K' : Set (GL (Fin a) (Af L))) :=
    hUc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKo) inf_le_left

  set O := LocEx.orbSpan φ with hO
  haveI : FiniteDimensional ℂ O := (π.cusp φ hφ).1.kfin
  set ρ₀ := sub (cptRep L a) O (LocEx.orbSpan_stable φ) with hρ₀
  have hρc : AutFin.IsContRep ρ₀ := LocEx.isContRep_sub _ _

  have hloc : ∀ v : π.V, ∃ U : Submodule ℂ π.V, v ∈ U ∧ FiniteDimensional ℂ U ∧
      (∀ k, ∀ u ∈ U, cptOn π k u ∈ U) ∧ ∀ (ℓ : Module.Dual ℂ π.V), ∀ u ∈ U, Continuous fun k => ℓ (cptOn π k u) := by
    intro v
    have hSV : LocEx.orbSpan v.1 ≤ π.V := Submodule.span_le.2 (by
      rintro _ ⟨k, rfl⟩
      exact (π.op (.cpt k) v).2)
    haveI : FiniteDimensional ℂ (LocEx.orbSpan v.1) := (π.cusp v.1 v.2).1.kfin
    set Uv : Submodule ℂ π.V := (LocEx.orbSpan v.1).comap π.V.subtype
    refine ⟨Uv, Submodule.subset_span ⟨1, by simp⟩, ?_, fun k u hu => ?_, fun ℓ u hu => ?_⟩
    · exact FiniteDimensional.of_injective ((π.V.subtype ∘ₗ Uv.subtype).codRestrict (LocEx.orbSpan v.1)
        fun u => u.2) fun u u' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
    · exact LocEx.orbSpan_stable v.1 k u.1 hu
    · have := LocEx.isContRep_sub (LocEx.orbSpan v.1) (LocEx.orbSpan_stable v.1)
        (ℓ ∘ₗ Submodule.inclusion hSV) ⟨u.1, hu⟩
      convert this using 2 with k
      rfl
  obtain ⟨hss, hfin, hsum⟩ := GlobalTheory.T.isSemisimple_of_locallyFinite_compactGroup (Kinf L a) π.V (cptOn π) hloc

  set X := typeSub π ρ₀ with hX
  have hφX : φ₀ ∈ X.toSubmodule := fun g =>
    AutFinGL.type_of_map ρ₀ O.subtype (fun _ _ => rfl) ⟨φ, Submodule.subset_span ⟨1, by simp⟩⟩ g
  have hclos : ∀ S₁ S₂ : Subrepresentation (cptOn π), IsAtom S₁ → S₂ ≤ X →
      Nonempty (S₁.toRepresentation.Equiv S₂.toRepresentation) → S₁ ≤ X := by
    rintro S₁ S₂ hS₁ hS₂ ⟨e⟩
    haveI := hfin S₁ hS₁
    haveI : FiniteDimensional ℂ S₂.toSubmodule := LinearEquiv.finiteDimensional e.toLinearEquiv
    obtain ⟨F, hF⟩ := LinearMap.exists_extend (S₁.toSubmodule.subtype ∘ₗ e.symm.toLinearEquiv.toLinearMap)
    have hFv : ∀ u (hu : u ∈ S₂.toSubmodule), F u = (e.symm ⟨u, hu⟩ : π.V) := fun u hu =>
      LinearMap.congr_fun hF ⟨u, hu⟩
    intro x hx
    have hx' : x = F (e ⟨x, hx⟩) := by
      rw [hFv _ (e ⟨x, hx⟩).2]
      simp
    rw [hx']
    refine GlobalTheory.T.cuspidal_typeClosure_preserved_by_archCompact_intertwiner L a π O ρ₀ S₂.toSubmodule inferInstance (fun k u hu => S₂.apply_mem_toSubmodule k hu) F
      (fun k u hu => ?_) _ (e ⟨x, hx⟩).2 (hS₂ (e ⟨x, hx⟩).2)
    rw [hFv _ (S₂.apply_mem_toSubmodule k hu), hFv _ hu]
    have := e.symm.toIntertwiningMap.isIntertwining' k
    exact congrArg Subtype.val (LinearMap.congr_fun this ⟨u, hu⟩)
  obtain ⟨Y, hXY, hnoiso, hT⟩ := GlobalTheory.T.exists_complement_without_common_irreducible_types (Kinf L a) π.V (cptOn π) hss hsum X hclos

  set e := LocGL.idem π.isSmooth_finPart hKc with he
  have hcomm : ∀ g k (v : π.V), π.finPart g (cptOn π k v) = cptOn π k (π.finPart g v) := fun g k v => by
    refine Subtype.ext ?_
    change (rt L a (finGL L a g) * rt L a (infGL L a (Unitary.toUnits k))) v.1 =
      (rt L a (infGL L a (Unitary.toUnits k)) * rt L a (finGL L a g)) v.1
    rw [← map_mul, ← map_mul, infGL_comm]
  have hfixS : ∀ k, ∀ v ∈ fixed π.finPart K', cptOn π k v ∈ fixed π.finPart K' := fun k v hv =>
    GlobalTheory.Parabolic.mem_fixed.2 fun u hu => by rw [hcomm, GlobalTheory.Parabolic.mem_fixed.1 hv u hu]
  have hkerS : ∀ k, ∀ v ∈ twKer π.finPart K' 1, cptOn π k v ∈ twKer π.finPart K' 1 := by
    intro k v hv
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨n, w, rfl⟩ := hz
      exact Submodule.subset_span ⟨n, cptOn π k w, by rw [map_sub, map_smul, hcomm]⟩
    | zero => simp
    | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
    | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ c hu
  have hee : ∀ v, e (e v) = e v := fun v => LocGL.idem_of_mem _ _ (LocGL.idem_mem _ _ v)
  have heq : ∀ k v, e (cptOn π k v) = cptOn π k (e v) := by
    intro k v
    have hd : v - e v ∈ twKer π.finPart K' 1 := by
      rw [← LocGL.idem_eq_zero_iff π.isSmooth_finPart hKc, map_sub, hee, sub_self]
    have hv : v = e v + (v - e v) := by abel
    conv_lhs => rw [hv, map_add (f := _), map_add (f := _)]
    rw [LocGL.idem_of_mem _ _ (hfixS k _ (LocGL.idem_mem _ _ v)),
      (LocGL.idem_eq_zero_iff π.isSmooth_finPart hKc).2 (hkerS k _ hd), add_zero]
  obtain ⟨heX, heY⟩ := hT e heq

  set PT := X.toSubmodule.projection Y.toSubmodule hXY with hPT
  have hPTl : ∀ v ∈ X.toSubmodule, PT v = v := fun v hv => by
    rw [hPT]; exact Submodule.projection_apply_of_mem_left hXY hv
  have hPTr : ∀ v ∈ Y.toSubmodule, PT v = 0 := fun v hv => by
    rw [hPT]; exact Submodule.projection_apply_of_mem_right hXY hv
  have hPTm : ∀ v, PT v ∈ X.toSubmodule := fun v => by
    rw [hPT]; exact Submodule.projection_apply_mem hXY v
  have hPTs : ∀ v, PT v + Y.toSubmodule.projection X.toSubmodule hXY.symm v = v := fun v => by
    rw [hPT]; exact Submodule.projection_add_projection_eq_self hXY v
  have hPTe : ∀ v, PT (e v) = e (PT v) := by
    intro v
    have hv := hPTs v
    conv_lhs => rw [← hv, map_add (f := _), map_add (f := _)]
    rw [hPTl _ (heX _ (hPTm v)), hPTr _ (heY _ (Submodule.projection_apply_mem hXY.symm v)), add_zero]
  have hPT2 : ∀ v, PT (PT v) = PT v := fun v => hPTl _ (hPTm v)
  refine ⟨e ∘ₗ PT, ?_, ?_, ?_, ?_⟩
  · intro hP
    have h1 : (e ∘ₗ PT) φ₀ = φ₀ := by
      change e (PT φ₀) = φ₀
      rw [hPTl _ hφX]
      exact LocGL.idem_of_mem _ _ (GlobalTheory.Parabolic.mem_fixed.2 fun u hu => hu.2)
    rw [hP] at h1
    exact h0' h1.symm
  · refine LinearMap.ext fun v => ?_
    change e (PT (e (PT v))) = e (PT v)
    rw [hPTe, hee, hPT2]
  · have hle : LinearMap.range (e ∘ₗ PT) ≤ X.toSubmodule ⊓ fixed π.finPart K' := by
      rintro _ ⟨v, rfl⟩
      exact ⟨heX _ (hPTm v), LocGL.idem_mem π.isSmooth_finPart hKc _⟩
    haveI := finiteDimensional_typeSub_fixed h π hρc hKo (ρ₀ := ρ₀)
    exact Submodule.finiteDimensional_of_le hle
  · intro s hs B hl hr hfinB hcptB _
    obtain ⟨σ, hσc, hσ⟩ : ∃ σ : GL (Fin a) (Af L) →* GL (Fin a) (Af L), Continuous σ ∧
        ∀ k, s (.fin k) = .fin (σ k) := by
      rcases hs with rfl | rfl
      · refine ⟨invT a (Af L), ?_, fun k => rfl⟩
        refine Units.continuous_iff.2 ⟨?_, ?_⟩
        · exact (Units.continuous_val.comp continuous_inv).matrix_transpose
        · exact Units.continuous_val.matrix_transpose
      · exact ⟨Matrix.GeneralLinearGroup.map (conjFin (IsCMField.complexConj L).toRingEquiv),
          Continuous.units_map _ (continuous_id.matrix_map (continuous_conjFin _)), fun k => rfl⟩
    have hsK : ∀ k, s (.cpt k) = .cpt (barKHom L a k) := by
      rcases hs with rfl | rfl <;> exact fun k => rfl
    have hBf : ∀ k φ ψ, B (π.finPart k φ) (π.finPart (σ k) ψ) = B φ ψ := fun k φ ψ => by
      have := hfinB k φ ψ
      rw [hσ] at this
      exact this
    have hBc : ∀ k φ ψ, B (cptOn π k φ) (cptOn π (barKHom L a k) ψ) = B φ ψ := fun k φ ψ => by
      have := hcptB k φ ψ
      rw [hsK] at this
      exact this
    have hKc' : IsCompact ((K'.map σ : Subgroup _) : Set (GL (Fin a) (Af L))) := by
      rw [Subgroup.coe_map]; exact hKc.image hσc
    have hC := GlobalTheory.T.isCompl_orthogonal_of_no_common_irreducible_types (Kinf L a) π.V (cptOn π) (barKHom L a) barKHom_surjective hfin hsum B hl hr hBc X Y hXY hnoiso
    refine ⟨(Submodule.projection _ _ hC) ∘ₗ LocGL.idem π.isSmooth_finPart hKc', fun φ ψ => ?_⟩
    change B (e (PT φ)) ψ = B φ (Submodule.projection _ _ hC (LocGL.idem π.isSmooth_finPart hKc' ψ))
    rw [idem_adj π.isSmooth_finPart σ hKc hKc' B hBf]
    rw [hPT]
    refine adj_of_isCompl B hXY hC (fun y hy x' hx' => ?_) (fun x hx y' hy' => ?_) φ _
    · simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx'
      exact hx' y hy
    · simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hy'
      exact hy' x hx

end GlobalTheory.IdemAdj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdempotentFiniteRankAdjointCuspidalStatement
open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_finiteRank_adjoint_cuspidal : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a), ∃ P : Module.End ℂ π.V, P ≠ 0 ∧ P ∘ₗ P = P ∧ FiniteDimensional ℂ (LinearMap.range P) ∧ ∀ s : Op L a → Op L a, (s = invTOp ∨ s = conjOp) → ∀ B : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B (π.op (.fin k) φ) (π.op (s (.fin k)) ψ) = B φ ψ) → (∀ k φ ψ, B (π.op (.cpt k) φ) (π.op (s (.cpt k)) ψ) = B φ ψ) → (∀ X φ ψ, B (π.op (.lie X) φ) ψ + B φ (π.op (s (.lie X)) ψ) = 0) → ∃ P' : Module.End ℂ π.V, ∀ φ ψ, B (P φ) ψ = B φ (P' ψ) := by
  first | exact @GlobalTheory.IdemAdj.exists_idem_adj | exact GlobalTheory.IdemAdj.exists_idem_adj | (intros; apply GlobalTheory.IdemAdj.exists_idem_adj <;> assumption)
end
