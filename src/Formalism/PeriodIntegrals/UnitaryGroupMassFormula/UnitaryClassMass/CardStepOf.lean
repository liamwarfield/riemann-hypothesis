module

public import Formalism.ThetaLiftIndependence.ThetaOrbitSums.LatLiftIndep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Development
public import Formalism.PeriodIntegrals.VolFromSW

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UJClassMass
noncomputable section

open Matrix NumberField
open scoped TensorProduct
open PI.UJClassFin

namespace PI.UJClassMass

def gramOf {E V : Type} [Field E] [StarRing E] [AddCommGroup V] [Module E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) {M : ℕ} (b : Module.Basis (Fin M) E V) : Matrix (Fin M) (Fin M) E :=
  fun i j => h (b i) (b j)

def crdOf {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    {M : ℕ} (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) : Set (Fin M → E) :=
  {x | ∑ i, x i • b i ∈ L0}

def stab {G : Type*} [Group G] (Γ K : Subgroup G) (g : G) : Set Γ := {γ | g⁻¹ * ((γ : G) * g) ∈ K}

end PI.UJClassMass
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.EquivFunLinOf
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Development
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Reduce
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Abstract

variable {G : Type*} [Group G] (Γ Kf : Subgroup G)
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) (L0 : Submodule (𝓞 K) V)

structure IsDict (Λ : G → Submodule (𝓞 K) V) (ι : Γ → V ≃ₗ[K] V) : Prop where
  mem : ∀ g, Λ g ∈ genus h L0
  isIsom : ∀ γ, ι γ ∈ isom h
  equiv : ∀ g (γ : Γ) (k : Kf), Λ ((γ : G) * g * k) = gmap (ι γ) (Λ g)
  inj : ∀ g g' (u : V ≃ₗ[K] V), u ∈ isom h → gmap u (Λ g') = Λ g →
    ∃ (γ : Γ) (k : Kf), g = (γ : G) * g' * k
  surj : ∀ N ∈ genus h L0, ∃ g, Λ g = N
  card : ∀ g, Nat.card (PI.UJClassMass.stab Γ Kf g) = Nat.card (autL h (Λ g))

variable {Γ Kf h L0}

private lemma gmap_mul_lemma (a b : V ≃ₗ[K] V) (L : Submodule (𝓞 K) V) :
    gmap (a * b) L = gmap a (gmap b L) := by
  first
  | (simp only [Formalism.HermitianLatticesTheory.gmap]; rw [← Submodule.map_comp]; rfl)
  | (ext x; simp [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map])

private lemma gmap_one_unitary_class_mass (L : Submodule (𝓞 K) V) : gmap (1 : V ≃ₗ[K] V) L = L := by
  first
  | (simp only [Formalism.HermitianLatticesTheory.gmap]; exact Submodule.map_id L)
  | (ext x; simp [Formalism.HermitianLatticesTheory.gmap])

private lemma gmap_inv_gmap_unitary_class_mass (g : V ≃ₗ[K] V) (L : Submodule (𝓞 K) V) : gmap g⁻¹ (gmap g L) = L := by
  rw [← gmap_mul_lemma, inv_mul_cancel, gmap_one_unitary_class_mass]

private lemma mul_mul_inv_mem_autL_gmap {g a : V ≃ₗ[K] V} {N : Submodule (𝓞 K) V} (hg : g ∈ isom h)
    (ha : a ∈ autL h N) : g * a * g⁻¹ ∈ autL h (gmap g N) := by
  have ⟨ha1, ha2⟩ : a ∈ isom h ∧ gmap a N = N := ha
  show g * a * g⁻¹ ∈ isom h ∧ gmap (g * a * g⁻¹) (gmap g N) = gmap g N
  exact ⟨mul_mem (mul_mem hg ha1) (inv_mem hg), by rw [gmap_mul_lemma, gmap_mul_lemma, gmap_inv_gmap_unitary_class_mass, ha2]⟩

private lemma inv_mul_mul_mem_autL {g b : V ≃ₗ[K] V} {N : Submodule (𝓞 K) V} (hg : g ∈ isom h)
    (hb : b ∈ autL h (gmap g N)) : g⁻¹ * b * g ∈ autL h N := by
  have ⟨hb1, hb2⟩ : b ∈ isom h ∧ gmap b (gmap g N) = gmap g N := hb
  show g⁻¹ * b * g ∈ isom h ∧ gmap (g⁻¹ * b * g) N = N
  exact ⟨mul_mem (mul_mem (inv_mem hg) hb1) hg, by rw [gmap_mul_lemma, gmap_mul_lemma, hb2, gmap_inv_gmap_unitary_class_mass]⟩

private lemma natCard_autL_gmap {g : V ≃ₗ[K] V} (hg : g ∈ isom h) (N : Submodule (𝓞 K) V) :
    Nat.card (autL h (gmap g N)) = Nat.card (autL h N) :=
  Nat.card_congr
    { toFun := fun b => ⟨g⁻¹ * b.1 * g, inv_mul_mul_mem_autL hg b.2⟩
      invFun := fun a => ⟨g * a.1 * g⁻¹, mul_mul_inv_mem_autL_gmap hg a.2⟩
      left_inv := fun b => Subtype.ext (by simp [mul_assoc])
      right_inv := fun a => Subtype.ext (by simp [mul_assoc]) }

private lemma sum_inv_card_autL_eq_of_isClassReps {s t : Finset (Submodule (𝓞 K) V)} (hs : IsClassReps h L0 s)
    (ht : IsClassReps h L0 t) :
    ∑ N ∈ s, ((Nat.card (autL h N) : ℕ) : ℝ)⁻¹ = ∑ N ∈ t, ((Nat.card (autL h N) : ℕ) : ℝ)⁻¹ := by
  classical
  have hs' : (∀ M ∈ s, M ∈ genus h L0) ∧
      ∀ M ∈ genus h L0, ∃! N, N ∈ s ∧ ∃ u ∈ isom h, gmap u N = M := hs
  have ht' : (∀ M ∈ t, M ∈ genus h L0) ∧
      ∀ M ∈ genus h L0, ∃! N, N ∈ t ∧ ∃ u ∈ isom h, gmap u N = M := ht
  have hex : ∀ N ∈ s, ∃ P, P ∈ t ∧ ∃ u ∈ isom h, gmap u P = N :=
    fun N hN => (ht'.2 N (hs'.1 N hN)).exists
  refine Finset.sum_bij (fun N hN => (hex N hN).choose) (fun N hN => (hex N hN).choose_spec.1)
    ?_ ?_ ?_
  · intro N₁ h₁ N₂ h₂ heq
    obtain ⟨u₁, hu₁, e₁⟩ := (hex N₁ h₁).choose_spec.2
    obtain ⟨u₂, hu₂, e₂⟩ := (hex N₂ h₂).choose_spec.2
    rw [heq] at e₁
    have key : gmap (u₂ * u₁⁻¹) N₁ = N₂ := by rw [gmap_mul_lemma, ← e₁, gmap_inv_gmap_unitary_class_mass, e₂]
    exact (hs'.2 N₂ (hs'.1 N₂ h₂)).unique ⟨h₁, _, mul_mem hu₂ (inv_mem hu₁), key⟩
      ⟨h₂, 1, one_mem _, gmap_one_unitary_class_mass N₂⟩
  · intro P hP
    obtain ⟨N, ⟨hN, u, hu, e⟩, -⟩ := hs'.2 P (ht'.1 P hP)
    refine ⟨N, hN, ?_⟩
    obtain ⟨v, hv, e'⟩ := (hex N hN).choose_spec.2
    have key : gmap (u * v) (hex N hN).choose = P := by rw [gmap_mul_lemma, e', e]
    exact (ht'.2 P (ht'.1 P hP)).unique ⟨(hex N hN).choose_spec.1, _, mul_mem hu hv, key⟩
      ⟨hP, 1, one_mem _, gmap_one_unitary_class_mass P⟩
  · intro N hN
    obtain ⟨v, hv, e'⟩ := (hex N hN).choose_spec.2
    have hc := natCard_autL_gmap hv (hex N hN).choose
    rw [e'] at hc
    rw [hc]

theorem mass_eq_of_reps {s : Finset (Submodule (𝓞 K) V)} (hs : IsClassReps h L0 s) :
    mass h L0 = ∑ N ∈ s, ((Nat.card (autL h N) : ℕ) : ℝ)⁻¹ := by
  have hex : ∃ t, IsClassReps h L0 t := ⟨s, hs⟩
  rw [Formalism.HermitianLatticesTheory.mass, dite_eq_left hex]
  exact sum_inv_card_autL_eq_of_isClassReps hex.choose_spec hs

theorem sum_eq_mass {Λ : G → Submodule (𝓞 K) V} {ι : Γ → V ≃ₗ[K] V} (D : IsDict Γ Kf h L0 Λ ι)
    (n : ℕ) (g : Fin n → G)
    (hcov : ∀ x, ∃ i, ∃ γ : Γ, ∃ k : Kf, x = (γ : G) * g i * k)
    (hdisj : ∀ i j (γ γ' : Γ) (k k' : Kf), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j) :
    ∑ i, ((Nat.card (PI.UJClassMass.stab Γ Kf (g i)) : ℝ))⁻¹ = mass h L0 := by
  classical
  have hR : ∀ i j (u : V ≃ₗ[K] V), u ∈ isom h → gmap u (Λ (g j)) = Λ (g i) → i = j := by
    intro i j u hu huj
    obtain ⟨γ, k, hk⟩ := D.inj (g i) (g j) u hu huj
    exact hdisj i j 1 γ 1 k (by simpa using hk)
  have hinj : Function.Injective (fun i => Λ (g i)) := fun i j hij =>
    hR i j 1 (one_mem _) (by rw [gmap_one_unitary_class_mass]; exact hij.symm)
  have hs : IsClassReps h L0 (Finset.univ.image (fun i => Λ (g i))) := by
    show (∀ M ∈ Finset.univ.image (fun i => Λ (g i)), M ∈ genus h L0) ∧
      ∀ M ∈ genus h L0, ∃! N, N ∈ Finset.univ.image (fun i => Λ (g i)) ∧ ∃ u ∈ isom h, gmap u N = M
    refine ⟨?_, ?_⟩
    · intro M hM
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hM
      rw [← hi]
      exact D.mem _
    · intro M hM
      obtain ⟨x, rfl⟩ := D.surj M hM
      obtain ⟨i, γ, k, rfl⟩ := hcov x
      refine ⟨Λ (g i), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), ι γ, D.isIsom γ,
        (D.equiv (g i) γ k).symm⟩, ?_⟩
      rintro N ⟨hN, u, hu, huN⟩
      obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hN
      have hj' : Λ (g j) = N := hj
      subst hj'
      rw [D.equiv] at huN
      have key : gmap ((ι γ)⁻¹ * u) (Λ (g j)) = Λ (g i) := by
        rw [gmap_mul_lemma, huN, gmap_inv_gmap_unitary_class_mass]
      obtain rfl := hR i j _ (mul_mem (inv_mem (D.isIsom γ)) hu) key
      rfl
  rw [mass_eq_of_reps hs, Finset.sum_image (by intro i _ j _ hij; exact hinj hij)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [D.card]

end Abstract

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Concrete

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]

def latSet (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin M) E V)
    (L0 : Submodule (𝓞 E) V) (g : HA (AF F) σ J) : Set V :=
  {v | b.equivFun v ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J (crdOf b L0) g}

def ratMat (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (γ : GamG σ J) : GL (Fin M) E :=
  Classical.choose (Subgroup.mem_map.mp
    (Subgroup.mem_subgroupOf.mp (γ.2 : (γ.1 : HR (AF F) σ J) ∈ HFinIn (AF F) σ J)))

def linOf {M : ℕ} (b : Module.Basis (Fin M) E V) (u : GL (Fin M) E) : V ≃ₗ[E] V :=
  LinearEquiv.ofLinear (Matrix.toLin b b (u : Matrix (Fin M) (Fin M) E))
    (Matrix.toLin b b ((u⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E))
    (by rw [← Matrix.toLin_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin_one])

def iotaG (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin M) E V)
    (γ : GamG σ J) : V ≃ₗ[E] V :=
  linOf b (ratMat σ J γ)

end Concrete

theorem coe_gmap {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (u : V ≃ₗ[K] V) (N : Submodule (𝓞 K) V) :
    (gmap u N : Set V) = u '' N := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_coe]
  rfl

def LatStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsFullLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ g : HA (AF F) σ (gramOf h b), ∃ N : Submodule (𝓞 E) V,
      (N : Set V) = latSet σ (gramOf h b) b L0 g ∧ N ∈ genus h L0

def IsomStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsFullLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ γ : GamG σ (gramOf h b), iotaG σ (gramOf h b) b γ ∈ isom h

def EquivStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsFullLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ (g : HA (AF F) σ (gramOf h b)) (γ : GamG σ (gramOf h b)) (k : SFin σ (gramOf h b) (crdOf b L0)),
      latSet σ (gramOf h b) b L0 ((γ : HA (AF F) σ (gramOf h b)) * g * k) = iotaG σ (gramOf h b) b γ '' latSet σ (gramOf h b) b L0 g

def InjStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsFullLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ (g g' : HA (AF F) σ (gramOf h b)) (u : V ≃ₗ[E] V), u ∈ isom h →
      u '' latSet σ (gramOf h b) b L0 g' = latSet σ (gramOf h b) b L0 g →
      ∃ (γ : GamG σ (gramOf h b)) (k : SFin σ (gramOf h b) (crdOf b L0)), g = (γ : HA (AF F) σ (gramOf h b)) * g' * k

def SurjStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsFullLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ N ∈ genus h L0, ∃ g : HA (AF F) σ (gramOf h b), latSet σ (gramOf h b) b L0 g = N

def CardStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsFullLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ g : HA (AF F) σ (gramOf h b),
      Nat.card (stab (GamG σ (gramOf h b)) (SFin σ (gramOf h b) (crdOf b L0)) g) =
        Nat.card {u : V ≃ₗ[E] V // u ∈ isom h ∧ u '' latSet σ (gramOf h b) b L0 g = latSet σ (gramOf h b) b L0 g}

def Dict : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsFullLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∃ (Λ : HA (AF F) σ (gramOf h b) → Submodule (𝓞 E) V) (ι : GamG σ (gramOf h b) → V ≃ₗ[E] V),
      IsDict (GamG σ (gramOf h b)) (SFin σ (gramOf h b) (crdOf b L0)) h L0 Λ ι

theorem uJClassMass_of_dict (hD : Dict) : PI.UJClassMass2.UJClassMass := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig n g hcov hdisj
  obtain ⟨Λ, ι, D⟩ := hD F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig
  exact sum_eq_mass D n g hcov hdisj

theorem dict_of (s1 : LatStep) (si : IsomStep) (s2 : EquivStep) (s3 : InjStep) (s4 : SurjStep)
    (s5 : CardStep) : Dict := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig
  have S1 := s1 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig
  choose Λ hΛ using S1
  refine ⟨Λ, iotaG σ (gramOf h b) b, ⟨fun g => (hΛ g).2, si F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig,
    ?_, ?_, ?_, ?_⟩⟩
  · intro g γ k
    apply SetLike.coe_injective
    rw [coe_gmap, (hΛ g).1, (hΛ _).1]
    exact s2 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig g γ k
  · intro g g' u hu hgm
    apply s3 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig g g' u hu
    have e := congrArg (fun N : Submodule (𝓞 E) V => (N : Set V)) hgm
    simp only [coe_gmap] at e
    rwa [(hΛ g).1, (hΛ g').1] at e
  · intro N hN
    obtain ⟨g, hg⟩ := s4 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig N hN
    exact ⟨g, SetLike.coe_injective ((hΛ g).1.trans hg)⟩
  · intro g
    rw [s5 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig g]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ?_)
    show _ ∧ _ ↔ _ ∧ _
    rw [← (hΛ g).1, ← coe_gmap]
    exact and_congr Iff.rfl ⟨fun e => SetLike.coe_injective e, fun e => by rw [e]⟩

theorem uJClassMass_of (s1 : LatStep) (si : IsomStep) (s2 : EquivStep) (s3 : InjStep)
    (s4 : SurjStep) (s5 : CardStep) : PI.UJClassMass2.UJClassMass := by
  exact uJClassMass_of_dict (dict_of s1 si s2 s3 s4 s5)

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Rat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ratMat_spec (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (γ : GamG σ J) :
    ratMat σ J γ ∈ UJ (σ : E →+* E) J ∧
      bc (inclR (AF F)) (ratMat σ J γ) = (γ.1 : HR (AF F) σ J).1 := by
  unfold ratMat
  first
  | exact Classical.choose_spec (p := fun m => m ∈ UJ (σ : E →+* E) J ∧
      bc (inclR (AF F)) m = (γ.1 : HR (AF F) σ J).1) _
  | (generalize_proofs h1 h2 h3 h4 h5 h6
     first
     | exact Classical.choose_spec h4
     | exact Classical.choose_spec h5
     | exact Classical.choose_spec h6
     | exact Classical.choose_spec h1)

def ratU (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (γ : GamG σ J) :
    UJ (σ : E →+* E) J :=
  ⟨ratMat σ J γ, (ratMat_spec σ J γ).1⟩

theorem emb_ratU (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (γ : GamG σ J) :
    PI.UnitaryGroupMassFormula.UJClassFin.emb σ J (ratU σ J γ) = (γ : HA (AF F) σ J) := by
  exact Subtype.ext (ratMat_spec σ J γ).2

theorem Lam_mul_sfin (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E))
    (g : HA (AF F) σ J) (k : SFin σ J L) :
    PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J L (g * k) = PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J L g := by
  have hk : ∀ y, y ∈ latHat F E L ↔
      (finMat σ J ((k : HA (AF F) σ J)⁻¹)).mulVec y ∈ latHat F E L := (k⁻¹).2
  ext x
  simp only [UJClassFin.abelian₂, Set.mem_setOf_eq, mul_inv_rev]
  unfold finMat at hk ⊢
  unfold HA.mat at hk ⊢
  simp only [Subgroup.coe_mul, Units.val_mul, ← AlgHom.mapMatrix_apply, map_mul] at hk ⊢
  have e : ∀ a c : HA (AF F) σ J, (a * c).1 = a.1 * c.1 := fun a c => rfl
  rw [e, Units.val_mul, map_mul]
  simp only [AlgHom.mapMatrix_apply, ← Matrix.mulVec_mulVec] at hk ⊢
  exact (hk _).symm

end Rat

section Coord

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem equivFun_linOf {M : ℕ} (b : Module.Basis (Fin M) E V) (u : GL (Fin M) E) (v : V) :
    b.equivFun (linOf b u v) = (u : Matrix (Fin M) (Fin M) E).mulVec (b.equivFun v) := by
  unfold linOf
  first
  | simp only [LinearEquiv.ofLinear_apply, Matrix.toLin_apply, Basis.equivFun_apply,
      Basis.repr_sum_self]
  | simp [Matrix.toLin_apply, Basis.repr_sum_self]
  | (simp [Matrix.toLin_apply]
     ext j
     simp [Finset.sum_apply, Finsupp.single_apply])

theorem linOf_basis {M : ℕ} (b : Module.Basis (Fin M) E V) (u : GL (Fin M) E) (i : Fin M) :
    linOf b u (b i) = ∑ k, (u : Matrix (Fin M) (Fin M) E) k i • b k := by
  unfold linOf
  first
  | simp [Matrix.toLin_self]
  | rw [LinearEquiv.ofLinear_apply, Matrix.toLin_self]

end Coord

theorem isomStep : IsomStep := by
  unfold IsomStep
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hsymm hnd hlat hsig γ
  unfold iotaG isom
  set u := ratMat σ (gramOf h b) γ with hu
  have hU : Formalism.UG.cT (σ : E →+* E) (u : Matrix (Fin M) (Fin M) E) * gramOf h b *
      (u : Matrix (Fin M) (Fin M) E) = gramOf h b := (ratMat_spec σ (gramOf h b) γ).1
  have hG : ∀ k l, gramOf h b k l = h (b k) (b l) := fun k l => rfl
  have key : (h.comp (linOf b u : V →ₗ[E] V)).compl₂ (linOf b u : V →ₗ[E] V) = h := by
    refine LinearMap.ext_basis b b fun i j => ?_
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, linOf_basis]
    rw [show h (b i) (b j) = gramOf h b i j from (hG i j).symm, ← hU]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hG,
      AlgHom.coe_toRingHom, RingHom.coe_coe, hσ, Finset.sum_mul, Finset.mul_sum, map_sum,
      map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
      RingHom.id_apply]
    first
    | exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    | (rw [Finset.sum_comm]
       exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring)
  show ∀ x y, h (linOf b u x) (linOf b u y) = h x y
  intro x y
  conv_rhs => rw [← key]
  rfl

theorem equivStep : EquivStep := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 _ _ _ _ _ _ _ g γ k
  ext v
  change b.equivFun v ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0)
      ((γ : HA (AF F) σ (gramOf h b)) * g * (k : HA (AF F) σ (gramOf h b))) ↔
    v ∈ (iotaG σ (gramOf h b) b γ : V → V) '' latSet σ (gramOf h b) b L0 g
  rw [Lam_mul_sfin, ← emb_ratU, PI.UnitaryGroupMassFormula.UJClassFin.Lam_emb_mul]
  constructor
  · rintro ⟨x, hx, hxv⟩
    refine ⟨b.equivFun.symm x, ?_, ?_⟩
    · show b.equivFun (b.equivFun.symm x) ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) g
      rwa [LinearEquiv.apply_symm_apply]
    · apply b.equivFun.injective
      change b.equivFun (linOf b _ _) = _
      rw [equivFun_linOf, LinearEquiv.apply_symm_apply]
      exact hxv
  · rintro ⟨w, hw, rfl⟩
    refine ⟨b.equivFun w, hw, ?_⟩
    change _ = b.equivFun (linOf b _ _)
    rw [equivFun_linOf]
    rfl

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def CrdBounds : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    Submodule.IsFullLattice E L0 →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ crdOf b L0, ∀ i, IsIntegral ℤ ((c : F) • x i)) ∧
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((c : F) • e) ∈ crdOf b L0)

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

instance nontrivialAF : Nontrivial (AF F) := by
  haveI : Nontrivial (Ainf F) := by
    first
    | exact inferInstance
    | (haveI : Nonempty (NumberField.InfinitePlace F) := inferInstance; exact Pi.nontrivial)
  first
  | exact inferInstance
  | exact inferInstanceAs (Nontrivial (Ainf F × Af F))
  | exact (Prod.nontrivial_left : Nontrivial (Ainf F × Af F))

theorem inclR_injective : Function.Injective (inclR (AF F) : E →+* AF F ⊗[F] E) :=
  Algebra.TensorProduct.includeRight_injective (R := F) (A := AF F) (B := E)
    (algebraMap F (AF F)).injective

theorem bc_injective {M : ℕ} :
    Function.Injective (bc (n := Fin M) (inclR (AF F) : E →+* AF F ⊗[F] E)) := by
  intro a a' e
  apply Units.ext
  ext i j
  have := congrArg (fun g : GL (Fin M) (AF F ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j) e
  exact inclR_injective this

theorem ratMat_emb (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (U : UJ (σ : E →+* E) J) :
    ratMat σ J ⟨PI.UnitaryGroupMassFormula.UJClassFin.emb σ J U, PI.UnitaryGroupMassFormula.UJClassFin.emb_mem σ J U⟩ = U :=
  bc_injective (ratMat_spec σ J _).2

end Gen

section Mat

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

def matGL {M : ℕ} (b : Module.Basis (Fin M) E V) (u : V ≃ₗ[E] V) : GL (Fin M) E where
  val := LinearMap.toMatrix b b (u : V →ₗ[E] V)
  inv := LinearMap.toMatrix b b (u.symm : V →ₗ[E] V)
  val_inv := by
    rw [← LinearMap.toMatrix_comp, show (u : V →ₗ[E] V).comp (u.symm : V →ₗ[E] V) = LinearMap.id from
      by ext; simp, LinearMap.toMatrix_id]
  inv_val := by
    rw [← LinearMap.toMatrix_comp, show (u.symm : V →ₗ[E] V).comp (u : V →ₗ[E] V) = LinearMap.id from
      by ext; simp, LinearMap.toMatrix_id]

theorem linOf_matGL {M : ℕ} (b : Module.Basis (Fin M) E V) (u : V ≃ₗ[E] V) : linOf b (matGL b u) = u := by
  apply LinearEquiv.ext
  intro v
  change Matrix.toLin b b (LinearMap.toMatrix b b (u : V →ₗ[E] V)) v = u v
  rw [Matrix.toLin_toMatrix]
  rfl

theorem linOf_inj {M : ℕ} (b : Module.Basis (Fin M) E V) {U U' : GL (Fin M) E}
    (e : linOf b U = linOf b U') : U = U' := by
  apply Units.ext
  have := congrArg (fun w : V ≃ₗ[E] V => LinearMap.toMatrix b b (w : V →ₗ[E] V)) e
  simpa [linOf, LinearMap.toMatrix_toLin] using this

end Mat

section Gram

variable {E V : Type} [Field E] [StarRing E] [AddCommGroup V] [Module E V]

theorem gram_linOf {F : Type} [Field F] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ a = star a)
    (h : V →ₗ⋆[E] V →ₗ[E] E) {M : ℕ} (b : Module.Basis (Fin M) E V) (U : GL (Fin M) E) (i j : Fin M) :
    h (linOf b U (b i)) (linOf b U (b j)) =
      (cT (σ : E →+* E) (U : Matrix (Fin M) (Fin M) E) * gramOf h b * (U : Matrix (Fin M) (Fin M) E)) i j := by
  rw [linOf_basis, linOf_basis]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Matrix.mul_apply, cT, Matrix.map_apply, Matrix.transpose_apply, gramOf, Finset.mul_sum,
    Finset.sum_mul, AlgHom.coe_toRingHom, hσ, starRingEnd_apply]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  simp only [RingHom.id_apply]
  ring

theorem matGL_mem {F : Type} [Field F] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ a = star a)
    (h : V →ₗ⋆[E] V →ₗ[E] E) {M : ℕ} (b : Module.Basis (Fin M) E V) {u : V ≃ₗ[E] V} (hu : u ∈ isom h) :
    matGL b u ∈ UJ (σ : E →+* E) (gramOf h b) := by
  show cT (σ : E →+* E) ((matGL b u : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) * gramOf h b *
    ((matGL b u : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) = gramOf h b
  ext i j
  rw [← gram_linOf σ hσ h b, linOf_matGL]
  exact hu (b i) (b j)

end Gram

section Sets

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]

theorem image_latSet (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin M) E V)
    (L0 : Submodule (𝓞 E) V) (U : GL (Fin M) E) (g : HA (AF F) σ J) :
    (linOf b U : V → V) '' latSet σ J b L0 g =
      {v | b.equivFun v ∈ (fun x => (U : Matrix (Fin M) (Fin M) E).mulVec x) ''
        PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J (crdOf b L0) g} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨b.equivFun w, hw, ?_⟩
    rw [equivFun_linOf]
  · rintro ⟨x, hx, hxv⟩
    refine ⟨b.equivFun.symm x, ?_, ?_⟩
    · show b.equivFun (b.equivFun.symm x) ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J (crdOf b L0) g
      rwa [LinearEquiv.apply_symm_apply]
    · apply b.equivFun.injective
      change b.equivFun (linOf b _ _) = _
      rw [equivFun_linOf, LinearEquiv.apply_symm_apply]
      exact hxv

theorem set_of_coords_inj {M : ℕ} (b : Module.Basis (Fin M) E V) {A A' : Set (Fin M → E)}
    (e : {v : V | b.equivFun v ∈ A} = {v | b.equivFun v ∈ A'}) : A = A' := by
  ext x
  have h1 : b.equivFun.symm x ∈ {v : V | b.equivFun v ∈ A} ↔ b.equivFun.symm x ∈ {v : V | b.equivFun v ∈ A'} := by
    rw [e]
  simpa only [Set.mem_setOf_eq, LinearEquiv.apply_symm_apply] using h1

end Sets

theorem injStep_of (hR : PI.UnitaryGroupMassFormula.UJClassFin.RatDense) (hC : CrdBounds) : InjStep := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ _ _ _ _ hL _ g g' u hu e
  obtain ⟨hb1, hb2⟩ := hC F E V M b L0 hL
  have hR' := hR F E σ M (gramOf h b) (crdOf b L0) hb1 hb2
  set U : UJ (σ : E →+* E) (gramOf h b) := ⟨matGL b u, matGL_mem σ hσ h b hu⟩ with hUdef
  have e1 : (linOf b (matGL b u) : V → V) '' latSet σ (gramOf h b) b L0 g' = latSet σ (gramOf h b) b L0 g := by
    rw [linOf_matGL]; exact e
  rw [image_latSet] at e1
  have e2 := set_of_coords_inj b e1
  have e3 : PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) (PI.UnitaryGroupMassFormula.UJClassFin.emb σ (gramOf h b) U * g') =
      PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) g := by
    rw [PI.UnitaryGroupMassFormula.UJClassFin.Lam_emb_mul]; exact e2
  have hk := PI.UnitaryGroupMassFormula.UJClassFin.sfin_of_Lam_eq σ (gramOf h b) (crdOf b L0) hR' _ _ e3
  refine ⟨⟨_, PI.UnitaryGroupMassFormula.UJClassFin.emb_mem σ (gramOf h b) U⟩, ⟨_, hk⟩, ?_⟩
  simp only [mul_inv_cancel_left]

theorem cardStep_of (hR : PI.UnitaryGroupMassFormula.UJClassFin.RatDense) (hC : CrdBounds) : CardStep := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hn hL hsig g
  obtain ⟨hb1, hb2⟩ := hC F E V M b L0 hL
  have hR' := hR F E σ M (gramOf h b) (crdOf b L0) hb1 hb2

  have wd : ∀ γ : stab (GamG σ (gramOf h b)) (SFin σ (gramOf h b) (crdOf b L0)) g,
      iotaG σ (gramOf h b) b γ.1 ∈ isom h ∧
        (iotaG σ (gramOf h b) b γ.1 : V → V) '' latSet σ (gramOf h b) b L0 g = latSet σ (gramOf h b) b L0 g := by
    intro γ
    refine ⟨isomStep F E σ V h M b L0 hσ hθ hτ hs hn hL hsig γ.1, ?_⟩
    have e1 := equivStep F E σ V h M b L0 hσ hθ hτ hs hn hL hsig g γ.1 1
    rw [← e1]
    have e2 : ((γ.1 : GamG σ (gramOf h b)) : HA (AF F) σ (gramOf h b)) * g *
        ((1 : SFin σ (gramOf h b) (crdOf b L0)) : HA (AF F) σ (gramOf h b)) =
        g * ((⟨_, γ.2⟩ : SFin σ (gramOf h b) (crdOf b L0)) : HA (AF F) σ (gramOf h b)) := by
      simp only [OneMemClass.coe_one, mul_one, mul_inv_cancel_left]
    rw [e2]
    show {v | b.equivFun v ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) (g * _)} =
      {v | b.equivFun v ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) g}
    rw [Lam_mul_sfin]
  let f : stab (GamG σ (gramOf h b)) (SFin σ (gramOf h b) (crdOf b L0)) g →
      {u : V ≃ₗ[E] V // u ∈ isom h ∧ (u : V → V) '' latSet σ (gramOf h b) b L0 g = latSet σ (gramOf h b) b L0 g} :=
    fun γ => ⟨iotaG σ (gramOf h b) b γ.1, wd γ⟩
  apply Nat.card_eq_of_bijective f
  refine ⟨?_, ?_⟩
  · intro γ γ' e
    have e1 : iotaG σ (gramOf h b) b γ.1 = iotaG σ (gramOf h b) b γ'.1 := congrArg Subtype.val e
    have e2 : ratMat σ (gramOf h b) γ.1 = ratMat σ (gramOf h b) γ'.1 := linOf_inj b e1
    have e3 : ratU σ (gramOf h b) γ.1 = ratU σ (gramOf h b) γ'.1 := Subtype.ext e2
    apply Subtype.ext
    apply Subtype.ext
    rw [← emb_ratU σ (gramOf h b) γ.1, ← emb_ratU σ (gramOf h b) γ'.1, e3]
  · rintro ⟨u, hu, hl⟩
    set U : UJ (σ : E →+* E) (gramOf h b) := ⟨matGL b u, matGL_mem σ hσ h b hu⟩ with hUdef
    let γ : GamG σ (gramOf h b) := ⟨PI.UnitaryGroupMassFormula.UJClassFin.emb σ (gramOf h b) U, PI.UnitaryGroupMassFormula.UJClassFin.emb_mem σ (gramOf h b) U⟩
    have hι : iotaG σ (gramOf h b) b γ = u := by
      show linOf b (ratMat σ (gramOf h b) γ) = u
      rw [ratMat_emb]
      exact linOf_matGL b u
    have e1 : (linOf b (matGL b u) : V → V) '' latSet σ (gramOf h b) b L0 g = latSet σ (gramOf h b) b L0 g := by
      rw [linOf_matGL]; exact hl
    rw [image_latSet] at e1
    have e2 := set_of_coords_inj b e1
    have e3 : PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) g =
        PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) ((γ : HA (AF F) σ (gramOf h b)) * g) := by
      rw [PI.UnitaryGroupMassFormula.UJClassFin.Lam_emb_mul]; exact e2.symm
    have hk := PI.UnitaryGroupMassFormula.UJClassFin.sfin_of_Lam_eq σ (gramOf h b) (crdOf b L0) hR' _ _ e3
    refine ⟨⟨γ, hk⟩, ?_⟩
    exact Subtype.ext hι

theorem uJClassMass_of_deep (hR : PI.UnitaryGroupMassFormula.UJClassFin.RatDense) (hC : CrdBounds) (s1 : LatStep) (s4 : SurjStep) :
    PI.UJClassMass2.UJClassMass :=
  uJClassMass_of s1 isomStep equivStep (injStep_of hR hC) s4 (cardStep_of hR hC)

end PI.UnitaryGroupMassFormula.UJClassMass

end
