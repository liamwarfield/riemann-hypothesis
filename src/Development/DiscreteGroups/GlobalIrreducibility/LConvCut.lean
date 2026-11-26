module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL

@[expose] public section

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.LConvCut
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.LConv

def IsWhitTest {k : Type} [Field k] [TopologicalSpace k] {m : ℕ} (ψ : AddChar k Circle) (f : GL (Fin m) k → ℂ) :
    Prop :=
  (∀ u ∈ unipB k (Fin m), ∀ g, f (u * g) = (ψ (superDiag u) : ℂ) * f g) ∧ IsLocallyConstant f ∧
    ∃ C : Set (GL (Fin m) k), IsCompact C ∧ ∀ g, f g ≠ 0 → ∃ u ∈ unipB k (Fin m), ∃ c ∈ C, g = u * c

def IsInvForm {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) : Prop :=
  (∀ x y, (starRingEnd ℂ) (B x y) = B y x) ∧ (∀ x, 0 ≤ (B x x).re) ∧ ∀ g x y, B (ρ g x) (ρ g y) = B x y

def IsExtremeForm {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) : Prop :=
  IsInvForm ρ B ∧ ∀ B' : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, IsInvForm ρ B' → IsInvForm ρ (B - B') →
    ∃ c : ℂ, ∀ x y, B' x y = c * B x y

def UnitAdm (G : Type) [Group G] (K : Subgroup G) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : G →* (H →L[ℂ] H)),
    (∀ g x, ‖π g x‖ = ‖x‖) → (∀ T : H →L[ℂ] H, (∀ g, T * π g = π g * T) → ∃ c : ℂ, T = c • (1 : H →L[ℂ] H)) →
    ∃ s : Finset H, ∀ x : H, (∀ κ ∈ K, π κ x = x) → x ∈ Submodule.span ℂ (s : Set H)

def UnifAdm (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (N : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ → ρ.IsIrreducible →
    FiniteDimensional ℂ (fixed ρ K) ∧ Module.finrank ℂ (fixed ρ K) ≤ N

def CuspGen : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), Nontrivial V → IsCuspidal π → IsGeneric ψ π

def KirBump : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin (m + 1)) k) V), IsSmooth ρ → ∀ v₀ : V, ∃ v : V,
      ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l →
        l v = l v₀ ∧ (l v₀ = 0 → ∀ g : GL (Fin m) k, l (ρ (corner g) v) = 0)

def BigCell : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (m : ℕ), 0 < m → ∀ (π₁ π₂ : IrrRep (GL (Fin (m + 1)) k))
    (l₁ : Module.Dual ℂ π₁.V) (l₂ : Module.Dual ℂ π₂.V), IsFunctional ψ π₁.ρ l₁ → IsFunctional ψ π₂.ρ l₂ →
    (∀ (v₁ : π₁.V) (v₂ : π₂.V), (∀ g : GL (Fin m) k, l₁ (π₁.ρ (corner g) v₁) = l₂ (π₂.ρ (corner g) v₂)) →
      l₁ (π₁.ρ (longElt (m + 1) k) v₁) = l₂ (π₂.ρ (longElt (m + 1) k) v₂)) →
    (∃ (v₁ : π₁.V) (v₂ : π₂.V), (∀ g : GL (Fin m) k, l₁ (π₁.ρ (corner g) v₁) = l₂ (π₂.ρ (corner g) v₂)) ∧
      l₁ v₁ ≠ 0) →
    Nonempty (π₁.ρ.Equiv π₂.ρ)

def WhitSep : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (m : ℕ),
    ∃ I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ, IsInvIntegral I ∧
      ∀ ψ : AddChar k Circle, Continuous ψ → ∀ f : GL (Fin m) k → ℂ, IsWhitTest ψ f →
        (∀ (τ : IrrRep (GL (Fin m) k)) (l : Module.Dual ℂ τ.V), IsFunctional ψ⁻¹ τ.ρ l →
          ∀ v : τ.V, I (fun g => f g * l (τ.ρ g v)) = 0) → f = 0

def ExtremeExists : Prop :=
  ∀ (G M : Type) [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M),
    (∃ s : Set M, s.Countable ∧ Submodule.span ℂ s = ⊤) →
    ∀ B₀ : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, IsInvForm ρ B₀ → ∀ f : M, B₀ f f ≠ 0 →
      ∃ B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, IsExtremeForm ρ B ∧ B f f ≠ 0

def ExtremeIrred : Prop :=
  ∀ (G M : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ G M), IsSmooth ρ →
    (∀ x : M, ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ ∀ κ ∈ K, ρ κ x = x) →
    (∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → UnitAdm G K) →
    ∀ B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, IsExtremeForm ρ B →
      ∀ Z : Submodule ℂ M, (∀ g, ∀ z ∈ Z, ρ g z ∈ Z) →
        (∀ z ∈ Z, B z z = 0) ∨ ∀ x : M, ∃ z ∈ Z, B (x - z) (x - z) = 0

def UnitAdmGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ)
    (K : Subgroup (GL (Fin m) k)), IsOpen (K : Set (GL (Fin m) k)) → IsCompact (K : Set (GL (Fin m) k)) →
    UnitAdm (GL (Fin m) k) K

def SepOfExtreme : Prop := ExtremeExists → ExtremeIrred → UnitAdmGL → WhitSep

def CommBound : Prop :=
  ∀ l t : ℕ, ∃ c : ℕ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : Fin l → Module.End ℂ V), (∀ i j, a i * a j = a j * a i) →
    t * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ Module.finrank ℂ V ^ 2 + c * Module.finrank ℂ V

def UnifAdmGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ)
    (K : Subgroup (GL (Fin m) k)), IsOpen (K : Set (GL (Fin m) k)) → ∃ N : ℕ, UnifAdm (GL (Fin m) k) K N

def UnifOfComm : Prop := CommBound → UnifAdmGL

def AltIdentity : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    IsCompact (K : Set G) → Countable (G ⧸ K) → ∀ N : ℕ, UnifAdm G K N →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : G →* (H →L[ℂ] H)),
      (∀ g x, ‖π g x‖ = ‖x‖) → ∀ e : H →L[ℂ] H, IsSelfAdjoint e → (∀ x, ∀ κ ∈ K, π κ (e x) = e x) →
      (∀ x, (∀ κ ∈ K, π κ x = x) → e x = x) → ∀ d : ℕ, N ^ 2 < d → ∀ g : Fin d → G,
        ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun i => e * π (g (σ i)) * e).prod = 0

def FiniteOfAlt : Prop :=
  ∀ (G : Type) [Group G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : G →* (H →L[ℂ] H)), (∀ g x, ‖π g x‖ = ‖x‖) →
    (∀ T : H →L[ℂ] H, (∀ g, T * π g = π g * T) → ∃ c : ℂ, T = c • (1 : H →L[ℂ] H)) →
    ∀ e : H →L[ℂ] H, e * e = e → ∀ d : ℕ, (∀ g : Fin d → G,
      ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun i => e * π (g (σ i)) * e).prod = 0) →
    ∃ s : Finset H, ∀ x : H, e x ∈ Submodule.span ℂ (s : Set H)

def UnitOfUnif : Prop := AltIdentity → FiniteOfAlt → UnifAdmGL → UnitAdmGL

def Glue : Prop := CuspGen → KirBump → BigCell → WhitSep → GlobalTheory.Published.LocalConverseGL

theorem localConverseGL_of_leaves (h1 : CuspGen) (h2 : KirBump) (h3 : BigCell) (h4 : ExtremeExists)
    (h5 : ExtremeIrred) (h6 : SepOfExtreme) (h7 : CommBound) (h8 : UnifOfComm) (h9 : AltIdentity)
    (h10 : FiniteOfAlt) (h11 : UnitOfUnif) (h12 : Glue) : GlobalTheory.Published.LocalConverseGL :=
  h12 h1 h2 h3 (h6 h4 h5 (h11 h9 h10 (h8 h7)))

end DiscreteGroups.sglob.LConv

end
end

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.DzIneEq
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace DiscreteGroups.sglob.DzType

section Fix

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E'] [Algebra E Ω]
  [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω]

theorem natCast_mem_of_normV {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (g n : ℕ)
    (hn : 0 < n) (hN : normV v = g ^ n) : ((g : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have : Finite (𝓞 K ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  let := Fintype.ofFinite (𝓞 K ⧸ v.asIdeal)
  have hc : ((Fintype.card (𝓞 K ⧸ v.asIdeal) : ℕ) : 𝓞 K ⧸ v.asIdeal) = 0 := Nat.cast_card_eq_zero _
  rw [← Nat.card_eq_fintype_card, show Nat.card (𝓞 K ⧸ v.asIdeal) = g ^ n from hN, Nat.cast_pow] at hc
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact (pow_eq_zero_iff hn.ne').1 hc

theorem fix_of_ine (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (he : ∀ [w'.asIdeal.LiesOver w.asIdeal], w'.asIdeal.ramificationIdx (𝓞 E) = 1)
    (σ : G E Ω) (hσ : σ ∈ Ine (F := E) A) (e : E') : σ (algebraMap E' Ω e) = algebraMap E' Ω e := by
  classical
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  let LL := IntermediateField.normalClosure E E' Ω
  have : NumberField (LL) :=
    { to_charZero := charZero_of_injective_algebraMap (algebraMap E (LL)).injective
      to_finiteDimensional := Module.Finite.trans E (LL) }
  have : IsGalois E' (LL) := IsGalois.tower_top_of_isGalois E E' (LL)
  have hmem : ∀ x : 𝓞 (LL), (((x : LL) : Ω)) ∈ A := fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A ((x.2).map (IsScalarTower.toAlgHom ℤ (LL) Ω))
  let ψ : 𝓞 (LL) →+* A :=
    { toFun := fun x => ⟨((x : LL) : Ω), hmem x⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  let P : Ideal (𝓞 (LL)) := (IsLocalRing.maximalIdeal A).comap ψ
  have hP : ∀ x : 𝓞 (LL), x ∈ P ↔ A.valuation (((x : LL) : Ω)) < 1 := fun x => A.valuation_lt_one_iff (ψ x)
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have hcE : ∀ x : 𝓞 E, (((algebraMap (𝓞 E) (𝓞 (LL)) x : 𝓞 (LL)) : LL) : Ω) = algebraMap E Ω (x : E) :=
    fun x => rfl
  have hcE' : ∀ x : 𝓞 E', (((algebraMap (𝓞 E') (𝓞 (LL)) x : 𝓞 (LL)) : LL) : Ω) = algebraMap E' Ω (x : E') :=
    fun x => rfl
  have : P.LiesOver w.asIdeal := ⟨Ideal.ext fun x => by
    rw [Ideal.under, Ideal.mem_comap, hP, hcE]
    exact (h x).symm⟩
  have : P.LiesOver w'.asIdeal := ⟨Ideal.ext fun x => by
    rw [Ideal.under, Ideal.mem_comap, hP, hcE']
    exact (h' x).symm⟩
  have : w'.asIdeal.LiesOver w.asIdeal := ⟨Ideal.ext fun x => by
    rw [Ideal.under, Ideal.mem_comap, ← h' _, ← h x]
    have e1 : algebraMap E' Ω ((algebraMap (𝓞 E) (𝓞 E') x : 𝓞 E') : E') = algebraMap E Ω (x : E) :=
      (IsScalarTower.algebraMap_apply E E' Ω (x : E)).symm
    rw [e1]⟩
  have : IsGaloisGroup (LL ≃ₐ[E] LL) (𝓞 E) (𝓞 (LL)) :=
    IsGaloisGroup.of_isFractionRing (LL ≃ₐ[E] LL) (𝓞 E) (𝓞 (LL)) E (LL)
  have : IsGaloisGroup (LL ≃ₐ[E'] LL) (𝓞 E') (𝓞 (LL)) :=
    IsGaloisGroup.of_isFractionRing (LL ≃ₐ[E'] LL) (𝓞 E') (𝓞 (LL)) E' (LL)
  have c1 := Ideal.card_inertia_eq_ramificationIdxIn (G := LL ≃ₐ[E] LL) w.asIdeal P
  have c2 := Ideal.card_inertia_eq_ramificationIdxIn (G := LL ≃ₐ[E'] LL) w'.asIdeal P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx w.asIdeal P (LL ≃ₐ[E] LL)] at c1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx w'.asIdeal P (LL ≃ₐ[E'] LL)] at c2
  have tower := Ideal.ramificationIdx_tower (R := 𝓞 E) w'.asIdeal P
  have hcard : Nat.card (P.inertia (LL ≃ₐ[E] LL)) ≤ Nat.card (P.inertia (LL ≃ₐ[E'] LL)) := by
    rw [c1, c2, tower, he, one_mul]
  let f : P.inertia (LL ≃ₐ[E'] LL) → P.inertia (LL ≃ₐ[E] LL) := fun τ => ⟨τ.1.restrictScalars E, fun x => τ.2 x⟩
  have hf : Function.Injective f := fun τ τ' hτ =>
    Subtype.ext (AlgEquiv.restrictScalars_injective E (congrArg Subtype.val hτ))
  have hbij := hf.bijective_of_nat_card_le hcard
  let σb : LL ≃ₐ[E] LL := σ.restrictNormal (LL)
  have hcomm : ∀ y : LL, ((σb y : LL) : Ω) = σ ((y : LL) : Ω) := fun y => AlgEquiv.restrictNormal_commutes σ (LL) y
  have hσb : σb ∈ P.inertia (LL ≃ₐ[E] LL) := fun x => by
    show σb • x - x ∈ P
    rw [hP]
    have e2 : (((σb • x - x : 𝓞 (LL)) : LL) : Ω) = ((σb (x : LL) : LL) : Ω) - ((x : LL) : Ω) := rfl
    rw [e2, hcomm]
    exact hσ.2 _ ((A.valuation_le_one_iff _).2 (hmem x))
  obtain ⟨τ, hτ⟩ := hbij.2 ⟨σb, hσb⟩
  have hτ' : τ.1.restrictScalars E = σb := congrArg Subtype.val hτ
  have key : σb (algebraMap E' (LL) e) = algebraMap E' (LL) e := by
    rw [← hτ']
    exact τ.1.commutes e
  have e5 : (((algebraMap E' (LL) e : LL)) : Ω) = algebraMap E' Ω e := rfl
  rw [← e5, ← hcomm, key]

end Fix

theorem ine_lift {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
    [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ)
    [Fact g.Prime] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w') (n : ℕ) (hn : 0 < n)
    (hg : ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2) (hN : normV w' = g ^ n) (σ : G E Ω) (hσ : σ ∈ Ine (F := E) A) :
    ∃ t : G E' Ω, t ∈ Ine (F := E') A ∧ AlgEquiv.restrictScalars E t = σ := by
  have hgw' := natCast_mem_of_normV w' g n hn hN
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    refine (h _).1 ?_
    have e1 : algebraMap E Ω (((g : ℕ) : 𝓞 E) : E) = algebraMap E' Ω (((g : ℕ) : 𝓞 E') : E') := by simp
    rw [e1]
    exact (h' _).2 hgw'
  have he : ∀ [w'.asIdeal.LiesOver w.asIdeal], w'.asIdeal.ramificationIdx (𝓞 E) = 1 := by
    intro _
    have hmap : ¬ Ideal.map (algebraMap (𝓞 E) (𝓞 E')) w.asIdeal ≤ w'.asIdeal ^ 2 := fun hle => hg (by
      have := hle (Ideal.mem_map_of_mem (algebraMap (𝓞 E) (𝓞 E')) hgw)
      rwa [map_natCast] at this)
    have hlt := Ideal.ramificationIdx'_lt hmap
    rw [Ideal.ramificationIdx'_eq_ramificationIdx w.asIdeal w'.asIdeal w.ne_bot] at hlt
    have hpos := Ideal.ramificationIdx_pos (R := 𝓞 E) w'.asIdeal
    omega
  have hfix := fix_of_ine A w h w' h' he σ hσ
  let t : G E' Ω := { σ.toRingEquiv with commutes' := hfix }
  refine ⟨t, ⟨?_, fun x hx => hσ.2 x hx⟩, AlgEquiv.ext fun x => rfl⟩
  show t • A = A
  have hd : σ • A = A := hσ.1
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  conv_rhs => rw [← hd]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact Iff.rfl

end DiscreteGroups.sglob.DzType
end
end

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.DzTame
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

set_option linter.all false

noncomputable section

namespace DiscreteGroups.sglob.DzType

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}

theorem val_lt_iff_of_dec {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) {a b : Ω} (hb : b ≠ 0) :
    A.valuation (σ a) < A.valuation (σ b) ↔ A.valuation a < A.valuation b := by
  have hb' : σ b ≠ 0 := (map_ne_zero σ).mpr hb
  have h1 : 0 < A.valuation b := (Valuation.pos_iff _).mpr hb
  have h2 : 0 < A.valuation (σ b) := (Valuation.pos_iff _).mpr hb'
  rw [← div_lt_one₀ h1, ← div_lt_one₀ h2, ← map_div₀ A.valuation (σ a), ← map_div₀ A.valuation a, ← map_div₀ σ]
  exact valuation_apply_lt_one_iff hσ (a / b)

theorem val_apply_eq {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) (x : Ω) : A.valuation (σ x) = A.valuation x := by
  classical
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have key : ∀ τ ∈ Dec (F := E) A, ∀ y : Ω, y ≠ 0 → A.valuation (τ y) < A.valuation y → False := by
    intro τ hτ y hy hlt
    have hne : ∀ k : ℕ, (τ ^ k) y ≠ 0 := fun k => (map_ne_zero _).mpr hy
    have hdec : ∀ k : ℕ, A.valuation ((τ ^ (k + 1)) y) < A.valuation ((τ ^ k) y) := by
      intro k
      induction k with
      | zero => simpa using hlt
      | succ k ih =>
        have := (val_lt_iff_of_dec hτ (hne k)).mpr ih
        simpa only [← AlgEquiv.mul_apply, ← pow_succ'] using this
    have hanti : StrictAnti fun k : ℕ => A.valuation ((τ ^ k) y) := strictAnti_nat_of_succ_lt hdec
    have hinj : Function.Injective fun k : ℕ => (τ ^ k) y := fun i j hij =>
      hanti.injective (by simp only at hij ⊢; rw [hij])
    have hint : IsIntegral E y := (Algebra.IsAlgebraic.isAlgebraic (R := E) y).isIntegral
    have hfin := (minpoly E y).rootSet_finite Ω
    apply Set.infinite_of_injective_forall_mem hinj (s := (minpoly E y).rootSet Ω) ?_ hfin
    intro k
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [show (τ ^ k) y = ((τ ^ k : G E Ω) : Ω →ₐ[E] Ω) y from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval,
      map_zero]
  rcases lt_trichotomy (A.valuation (σ x)) (A.valuation x) with h | h | h
  · exact (key σ hσ x hx h).elim
  · exact h
  · refine (key σ⁻¹ ((Dec (F := E) A).inv_mem hσ) (σ x) ((map_ne_zero σ).mpr hx) ?_).elim
    rwa [show (σ⁻¹ : G E Ω) (σ x) = x by simp]

theorem val_ratio {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) {x : Ω} (hx : x ≠ 0) : A.valuation (σ x / x) = 1 := by
  rw [map_div₀, val_apply_eq hσ, div_self ((Valuation.ne_zero_iff _).mpr hx)]

theorem ratio_cong {σ ψ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (hψ : ψ ∈ Dec (F := E) A) {x : Ω} (hx : x ≠ 0) :
    A.valuation (σ (ψ x) / ψ x - σ x / x) < 1 := by
  set y := ψ x / x with hy
  have hy1 : A.valuation y = 1 := val_ratio hψ hx
  have hy0 : y ≠ 0 := by intro h; rw [h, map_zero] at hy1; exact zero_ne_one hy1
  have hψx : ψ x = x * y := by rw [hy]; field_simp
  have hσx0 : σ x ≠ 0 := (map_ne_zero σ).mpr hx
  have hσy0 : σ y ≠ 0 := (map_ne_zero σ).mpr hy0
  have e : σ (ψ x) / ψ x - σ x / x = (σ x / x) * ((σ y - y) / y) := by
    rw [hψx, map_mul]; field_simp
  rw [e, map_mul, val_ratio (Ine_le_Dec A hσ) hx, one_mul, map_div₀, hy1, div_one]
  exact hσ.2 y hy1.le

def ratioUnit {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) {x : Ω} (hx : x ≠ 0) : Aˣ where
  val := ⟨σ x / x, (A.valuation_le_one_iff _).mp (val_ratio hσ hx).le⟩
  inv := ⟨x / σ x, (A.valuation_le_one_iff _).mp (by
    rw [map_div₀, val_apply_eq hσ, div_self ((Valuation.ne_zero_iff _).mpr hx)])⟩
  val_inv := by
    have : σ x ≠ 0 := (map_ne_zero σ).mpr hx
    apply Subtype.ext; show σ x / x * (x / σ x) = 1; field_simp
  inv_val := by
    have : σ x ≠ 0 := (map_ne_zero σ).mpr hx
    apply Subtype.ext; show x / σ x * (σ x / x) = 1; field_simp

theorem res_eq_of_cong {a b : A} (h : A.valuation ((a : Ω) - b) < 1) :
    IsLocalRing.residue A a = IsLocalRing.residue A b := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  simpa using h

def tameSym {x : Ω} (hx : x ≠ 0) : Ine (F := E) A →* (IsLocalRing.ResidueField A)ˣ where
  toFun σ := Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A) (ratioUnit (Ine_le_Dec A σ.2) hx)
  map_one' := by
    ext
    show IsLocalRing.residue A ⟨(1 : G E Ω) x / x, _⟩ = 1
    rw [← map_one (IsLocalRing.residue A)]
    congr 1
    apply Subtype.ext
    show (1 : G E Ω) x / x = 1
    simp [hx]
  map_mul' σ τ := by
    ext
    show IsLocalRing.residue A ⟨(σ * τ : G E Ω) x / x, _⟩ =
      IsLocalRing.residue A ⟨(σ : G E Ω) x / x, _⟩ * IsLocalRing.residue A ⟨(τ : G E Ω) x / x, _⟩
    rw [← map_mul]
    apply res_eq_of_cong
    show A.valuation ((σ * τ : G E Ω) x / x - (σ : G E Ω) x / x * ((τ : G E Ω) x / x)) < 1
    have hτx : (τ : G E Ω) x ≠ 0 := (map_ne_zero _).mpr hx
    have e : (σ * τ : G E Ω) x / x - (σ : G E Ω) x / x * ((τ : G E Ω) x / x) =
        ((σ : G E Ω) ((τ : G E Ω) x) / (τ : G E Ω) x - (σ : G E Ω) x / x) * ((τ : G E Ω) x / x) := by
      rw [AlgEquiv.mul_apply]; field_simp
    rw [e, map_mul, val_ratio (Ine_le_Dec A τ.2) hx, mul_one]
    exact ratio_cong σ.2 (Ine_le_Dec A τ.2) hx

theorem isWild_of_tameSym {σ : Ine (F := E) A} (h : ∀ (x : Ω) (hx : x ≠ 0), tameSym hx σ = 1) :
    Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) := by
  refine ⟨σ.2, fun x hx => ?_⟩
  have h1 := congrArg Units.val (h x hx)
  change IsLocalRing.residue A ⟨(σ : G E Ω) x / x, _⟩ = IsLocalRing.residue A 1 at h1
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h1
  have h2 : A.valuation ((σ : G E Ω) x / x - 1) < 1 := by simpa using h1
  have hv : 0 < A.valuation x := (Valuation.pos_iff _).mpr hx
  have e : (σ : G E Ω) x - x = ((σ : G E Ω) x / x - 1) * x := by field_simp
  rw [e, map_mul]
  calc A.valuation ((σ : G E Ω) x / x - 1) * A.valuation x < 1 * A.valuation x :=
        mul_lt_mul_of_pos_right h2 hv
    _ = A.valuation x := one_mul _

theorem isWild_frob {q : ℕ} {φ : G E Ω} (hφ : IsFrob A q φ) (s : Ine (F := E) A) :
    Formalism.MainNotions.BlochKatoReduction.IsWild A (((⟨φ * s * φ⁻¹, conj_mem_Ine hφ.1 s.2⟩ : Ine (F := E) A) * (s ^ q)⁻¹ :
      Ine (F := E) A) : G E Ω) := by
  refine isWild_of_tameSym fun x hx => ?_
  rw [map_mul, map_inv, map_pow, mul_inv_eq_one]
  ext
  show IsLocalRing.residue A ⟨(φ * (s : G E Ω) * φ⁻¹) x / x, _⟩ = (IsLocalRing.residue A ⟨(s : G E Ω) x / x, _⟩) ^ q
  rw [← map_pow]
  apply res_eq_of_cong
  show A.valuation ((φ * (s : G E Ω) * φ⁻¹) x / x - ((s : G E Ω) x / x) ^ q) < 1
  have hφD : φ ∈ Dec (F := E) A := hφ.1
  have hφiD : φ⁻¹ ∈ Dec (F := E) A := (Dec (F := E) A).inv_mem hφD
  set y := (φ⁻¹ : G E Ω) x with hy
  have hy0 : y ≠ 0 := (map_ne_zero _).mpr hx
  have hxy : x = φ y := by rw [hy, mul_inv_apply]
  have e1 : (φ * (s : G E Ω) * φ⁻¹) x / x = φ ((s : G E Ω) y / y) := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← hy, map_div₀]
    conv_lhs => rw [show x = φ y from hxy]
  have hz : A.valuation ((s : G E Ω) y / y) ≤ 1 := (val_ratio (Ine_le_Dec A s.2) hy0).le
  have c1 : A.valuation (φ ((s : G E Ω) y / y) - ((s : G E Ω) y / y) ^ q) < 1 := hφ.2 _ hz
  have c2 : A.valuation ((s : G E Ω) y / y - (s : G E Ω) x / x) < 1 := ratio_cong s.2 hφiD hx
  have c3 := cong_pow hz (val_ratio (Ine_le_Dec A s.2) hx).le c2 q
  rw [e1]
  exact cong_trans c1 c3

end DiscreteGroups.sglob.DzType

end
end
