module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCentreRationalForm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralizedInverseOfLiftLocal

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantFibreRankStalkRank
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantFibreRankStalkRank
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem rankAtStalk_eq_of_finrank_fibres :
    ∀ (R K : Type) [CommRing R] [AddCommGroup K] [Module R K] [Module.Finite R K]
      [Module.Projective R K] (g : ℕ),
      (∀ (k : Type) [Field k] [Algebra R k], Module.finrank k (k ⊗[R] K) = g) →
      ∀ p : PrimeSpectrum R, Module.rankAtStalk K p = g := by
  intro R K _ _ _ _ _ g hg p
  haveI : Module.Free (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] K) :=
    Module.free_of_flat_of_isLocalRing
  rw [Module.rankAtStalk_eq_finrank_tensorProduct,
    ← Module.finrank_baseChange (R := IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)),
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime p.asIdeal)
      (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal))
      (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) K).finrank_eq]
  exact hg _

end GlobalTheory.CompanionTheory.PerfVB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantFibreRankStalkRankStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_fibre_rank_stalk_rank : ∀ (R K : Type) [CommRing R] [AddCommGroup K] [Module R K] [Module.Finite R K] [Module.Projective R K] (g : ℕ), (∀ (k : Type) [Field k] [Algebra R k], Module.finrank k (k ⊗[R] K) = g) → ∀ p : PrimeSpectrum R, Module.rankAtStalk K p = g := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.rankAtStalk_eq_of_finrank_fibres | exact GlobalTheory.CompanionTheory.PerfVB.rankAtStalk_eq_of_finrank_fibres | (intros; apply GlobalTheory.CompanionTheory.PerfVB.rankAtStalk_eq_of_finrank_fibres <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseChangeMapComposition
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseChangeMapComposition
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem exists_bc_comp (R S S' C : Type) [CommRing R] [CommRing S] [CommRing S'] [Algebra R S]
    [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) (F'' : C ⥤ CommAlgCat.{0} S')
    (m : BC F F') (n : BC F' F'') :
    ∃ l : BC F F'', ∀ T b, l.α T b = n.α T (m.α T b) := by
  obtain ⟨α, hα₁, hα₂, hα₃⟩ := m
  obtain ⟨β, hβ₁, hβ₂, hβ₃⟩ := n
  refine ⟨⟨fun T => (β T).comp (α T), ?_, ?_, ?_⟩, fun T b => rfl⟩
  · intro T T' φ b
    simp only [RingHom.comp_apply, hα₁, hβ₁]
  · intro T r b
    simp only [RingHom.comp_apply, hα₂, hβ₂, ← IsScalarTower.algebraMap_apply]
  · intro T
    obtain ⟨e₁, he₁⟩ := hα₃ T
    obtain ⟨e₂, he₂⟩ := hβ₃ T
    refine ⟨(TensorProduct.AlgebraTensorModule.cancelBaseChange R S S' S' (F.obj T)).symm.trans
      ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S' S') e₁).trans e₂), fun b => ?_⟩
    simp only [LinearEquiv.trans_apply, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, he₁, he₂,
      RingHom.comp_apply]

end GlobalTheory.CompanionTheory.PerfVB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseChangeMapCompositionStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_map_composition : ∀ (R S S' C : Type) [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) (F'' : C ⥤ CommAlgCat.{0} S') (m : BC F F') (n : BC F' F''), ∃ l : BC F F'', ∀ T b, l.α T b = n.α T (m.α T b) := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.exists_bc_comp | exact GlobalTheory.CompanionTheory.PerfVB.exists_bc_comp | (intros; apply GlobalTheory.CompanionTheory.PerfVB.exists_bc_comp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitComplexHomotopyData
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitComplexHomotopyData
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.PerfVB

theorem exists_contraction_onto_homology (R P₀ P₁ P₂ : Type) [CommRing R] [AddCommGroup P₀]
    [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂]
    (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (t : P₁ →ₗ[R] P₀) (s : P₂ →ₗ[R] P₁) :
    a₁ ∘ₗ a₀ = 0 → a₀ ∘ₗ t ∘ₗ a₀ = a₀ → a₁ ∘ₗ s ∘ₗ a₁ = a₁ →
    ∃ (j : Hc a₀ a₁ →ₗ[R] P₁) (π : P₁ →ₗ[R] Hc a₀ a₁) (h : P₁ →ₗ[R] P₀) (h' : P₂ →ₗ[R] P₁),
      π ∘ₗ j = LinearMap.id ∧ a₁ ∘ₗ j = 0 ∧ π ∘ₗ a₀ = 0 ∧
        j ∘ₗ π + a₀ ∘ₗ h + h' ∘ₗ a₁ = LinearMap.id := by
  intro h10 ht hs
  have h10' : ∀ y, a₁ (a₀ y) = 0 := fun y => LinearMap.congr_fun h10 y
  have ht' : ∀ y, a₀ (t (a₀ y)) = a₀ y := fun y => LinearMap.congr_fun ht y
  have hs' : ∀ x, a₁ (s (a₁ x)) = a₁ x := fun x => LinearMap.congr_fun hs x
  have hk : ∀ x, x - s (a₁ x) ∈ LinearMap.ker a₁ := fun x => by
    rw [LinearMap.mem_ker, map_sub, hs', sub_self]
  have hp : Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀) ≤
      LinearMap.ker ((LinearMap.id - a₀ ∘ₗ t) ∘ₗ (LinearMap.ker a₁).subtype) := by
    rintro ⟨z, hz⟩ hzN
    obtain ⟨y, rfl⟩ : ∃ y, a₀ y = z := LinearMap.mem_range.1 (Submodule.mem_comap.1 hzN)
    rw [LinearMap.mem_ker]
    change a₀ y - a₀ (t (a₀ y)) = 0
    rw [ht', sub_self]
  refine ⟨Submodule.liftQ _ ((LinearMap.id - a₀ ∘ₗ t) ∘ₗ (LinearMap.ker a₁).subtype) hp,
    (Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀)).mkQ ∘ₗ
      LinearMap.codRestrict (LinearMap.ker a₁) (LinearMap.id - s ∘ₗ a₁) hk,
    t - t ∘ₗ s ∘ₗ a₁, s, ?_, ?_, ?_, ?_⟩
  · refine LinearMap.ext fun q => ?_
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective
      (Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀)) q
    have hz' : a₁ z = 0 := LinearMap.mem_ker.1 hz
    have key : (⟨z - a₀ (t z) - s (a₁ (z - a₀ (t z))), hk _⟩ : LinearMap.ker a₁) - ⟨z, hz⟩ ∈
        Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀) := by
      refine Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨-t z, ?_⟩)
      change a₀ (-t z) = z - a₀ (t z) - s (a₁ (z - a₀ (t z))) - z
      rw [map_sub a₁, hz', h10', sub_self, map_zero, sub_zero, map_neg]
      abel
    exact (Submodule.Quotient.eq _).2 key
  · refine LinearMap.ext fun q => ?_
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective
      (Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀)) q
    have hz' : a₁ z = 0 := LinearMap.mem_ker.1 hz
    change a₁ (z - a₀ (t z)) = 0
    rw [map_sub, hz', h10', sub_zero]
  · refine LinearMap.ext fun y => ?_
    change Submodule.Quotient.mk (p := Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀))
      (⟨a₀ y - s (a₁ (a₀ y)), hk _⟩ : LinearMap.ker a₁) = 0
    refine (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨y, ?_⟩))
    change a₀ y = a₀ y - s (a₁ (a₀ y))
    rw [h10', map_zero, sub_zero]
  · refine LinearMap.ext fun x => ?_
    change x - s (a₁ x) - a₀ (t (x - s (a₁ x))) + a₀ (t x - t (s (a₁ x))) + s (a₁ x) = x
    simp only [map_sub]
    abel

end GlobalTheory.CompanionTheory.PerfVB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitComplexHomotopyDataStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_complex_homotopy_data : ∀ (R P₀ P₁ P₂ : Type) [CommRing R] [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (t : P₁ →ₗ[R] P₀) (s : P₂ →ₗ[R] P₁), a₁ ∘ₗ a₀ = 0 → a₀ ∘ₗ t ∘ₗ a₀ = a₀ → a₁ ∘ₗ s ∘ₗ a₁ = a₁ → ∃ (j : Hc a₀ a₁ →ₗ[R] P₁) (π : P₁ →ₗ[R] Hc a₀ a₁) (h : P₁ →ₗ[R] P₀) (h' : P₂ →ₗ[R] P₁), π ∘ₗ j = LinearMap.id ∧ a₁ ∘ₗ j = 0 ∧ π ∘ₗ a₀ = 0 ∧ j ∘ₗ π + a₀ ∘ₗ h + h' ∘ₗ a₁ = LinearMap.id := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.exists_contraction_onto_homology | exact GlobalTheory.CompanionTheory.PerfVB.exists_contraction_onto_homology | (intros; apply GlobalTheory.CompanionTheory.PerfVB.exists_contraction_onto_homology <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModelComparisonDegreeOneBijective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModelComparisonDegreeOneBijective
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB.Cls

section Abstract

variable {S A₀ A₁ A₂ B₀ B₁ B₂ D₀ D₁ D₂ H : Type} [CommRing S]
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
  [AddCommGroup D₀] [AddCommGroup D₁] [AddCommGroup D₂] [AddCommGroup H]
  [Module S A₀] [Module S A₁] [Module S A₂] [Module S B₀] [Module S B₁] [Module S B₂]
  [Module S D₀] [Module S D₁] [Module S D₂] [Module S H]

theorem homology_equiv (a₀ : A₀ →ₗ[S] A₁) (a₁ : A₁ →ₗ[S] A₂) (b₀ : B₀ →ₗ[S] B₁)
    (b₁ : B₁ →ₗ[S] B₂) (e₀ : D₀ →ₗ[S] D₁) (e₁ : D₁ →ₗ[S] D₂) (f₀ : A₀ →ₗ[S] B₀)
    (f₁ : A₁ →ₗ[S] B₁) (f₂ : A₂ →ₗ[S] B₂) (t₀ : B₀ →ₗ[S] D₀) (t₁ : B₁ →ₗ[S] D₁)
    (t₂ : B₂ →ₗ[S] D₂) (Z : Submodule S D₁) (q : Z →ₗ[S] H)
    (hZ : Z = LinearMap.ker e₁) (hq : Function.Surjective q)
    (hq0 : ∀ z : Z, q z = 0 ↔ ∃ g, e₀ g = z.1)
    (hf₁ : ∀ y, f₁ (a₀ y) = b₀ (f₀ y)) (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x))
    (ht₁ : ∀ y, t₁ (b₀ y) = e₀ (t₀ y)) (ht₂ : ∀ x, t₂ (b₁ x) = e₁ (t₁ x))
    (ht₀s : Function.Surjective t₀) (ht₁b : Function.Bijective t₁)
    (ht₂i : Function.Injective t₂)
    (hinj : ∀ x, a₁ x = 0 → (∃ y, b₀ y = f₁ x) → ∃ y, a₀ y = x)
    (hsurj : ∀ z, b₁ z = 0 → ∃ x y, a₁ x = 0 ∧ f₁ x - z = b₀ y) :
    ∃ e : Hc a₀ a₁ ≃ₗ[S] H, ∀ (x : A₁) (hx : x ∈ LinearMap.ker a₁),
      ∃ hw : t₁ (f₁ x) ∈ Z, e (Submodule.Quotient.mk ⟨x, hx⟩) = q ⟨_, hw⟩ := by
  have hmem : ∀ x : LinearMap.ker a₁, (t₁ ∘ₗ f₁ ∘ₗ (LinearMap.ker a₁).subtype) x ∈ Z := by
    rintro ⟨x, hx⟩
    rw [hZ, LinearMap.mem_ker]
    have hx' : a₁ x = 0 := hx
    change e₁ (t₁ (f₁ x)) = 0
    rw [← ht₂, ← hf₂, hx', map_zero, map_zero]
  let Φ : LinearMap.ker a₁ →ₗ[S] H :=
    q ∘ₗ (t₁ ∘ₗ f₁ ∘ₗ (LinearMap.ker a₁).subtype).codRestrict Z hmem
  have hΦ : ∀ x : LinearMap.ker a₁, Φ x = q ⟨t₁ (f₁ x.1), hmem x⟩ := fun x ↦ rfl
  have hs : Function.Surjective Φ := by
    intro c
    obtain ⟨w, rfl⟩ := hq c
    obtain ⟨w₀, hw₀⟩ := ht₁b.2 w.1
    have hker : ∀ d, d ∈ Z → e₁ d = 0 := fun d hd ↦ by
      rw [hZ] at hd
      exact hd
    have hw : e₁ w.1 = 0 := hker _ w.2
    have hd : b₁ w₀ = 0 := ht₂i (by rw [ht₂, hw₀, hw, map_zero])
    obtain ⟨x, y, hx, hxy⟩ := hsurj w₀ hd
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [hΦ, ← sub_eq_zero, ← map_sub, hq0]
    refine ⟨t₀ y, ?_⟩
    change e₀ (t₀ y) = t₁ (f₁ x) - w.1
    rw [← ht₁, ← hxy, map_sub, hw₀]
  have hk : (LinearMap.range a₀).comap (LinearMap.ker a₁).subtype = LinearMap.ker Φ := by
    ext ⟨x, hx⟩
    have hx' : a₁ x = 0 := hx
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range, LinearMap.mem_ker]
    rw [hΦ, hq0]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨t₀ (f₀ y), by simp only [← ht₁, hf₁]⟩
    · rintro ⟨g, hg⟩
      obtain ⟨g₀, rfl⟩ := ht₀s g
      refine hinj x hx' ⟨g₀, ht₁b.1 ?_⟩
      rw [ht₁]
      exact hg
  refine ⟨(Submodule.quotEquivOfEq _ _ hk).trans (Φ.quotKerEquivOfSurjective hs), fun x hx ↦ ?_⟩
  exact ⟨hmem ⟨x, hx⟩, rfl⟩

end Abstract

variable {R S C : Type} [CommRing R] [CommRing S] [Algebra R S] [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} S}

theorem comparison_degree_one_coboundary (m : BC F F') (x : S ⊗[R] C0 F) :
    th1 m ((d0 F).baseChange S x) = d0 F' (th0 m x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul s g =>
    rw [LinearMap.baseChange_tmul, th1, th0, liftSemi_tmul, liftSemi_tmul, map_smul]
    congr 1
    funext T T' φ
    change m.α T' (g T' - mp F φ (g T)) = m.α T' (g T') - mp F' φ (m.α T (g T))
    rw [map_sub, m.naturality]

theorem comparison_degree_two_coboundary (m : BC F F') (x : S ⊗[R] C1 F) :
    th2 m ((d1 F).baseChange S x) = d1 F' (th1 m x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul s g =>
    rw [LinearMap.baseChange_tmul, th2, th1, liftSemi_tmul, liftSemi_tmul, map_smul]
    congr 1
    funext T T' T'' φ ψ
    change m.α T'' (mp F ψ (g T T' φ) - g T T'' (φ ≫ ψ) + g T' T'' ψ) =
      mp F' ψ (m.α T' (g T T' φ)) - m.α T'' (g T T'' (φ ≫ ψ)) + m.α T'' (g T' T'' ψ)
    rw [map_add (f := _), map_sub, m.naturality]

theorem model_comparison_degree_zero_bijective (R S C P₀ P₁ P₂ : Type) [CommRing R] [CommRing S] [Algebra R S] [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) [AddCommGroup P₀] [AddCommGroup P₁]
    [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁)
    (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F)
    (m : BC F F') : IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → Function.Bijective (th0 m) →
      Function.Bijective (th1 m) → Function.Bijective (th2 m) →
      ∃ e : Hc (a₀.baseChange S) (a₁.baseChange S) ≃ₗ[S] H1 F',
        ∀ (x : S ⊗[R] P₁) (hx : x ∈ LinearMap.ker (a₁.baseChange S)),
          ∃ hw : th1 m (ψ₁.baseChange S x) ∈ Z1 F',
            e (Submodule.Quotient.mk ⟨x, hx⟩) = H1.mk F' ⟨_, hw⟩ := by
  rintro ⟨-, hc0, hc1, hq⟩ b0 b1 b2
  obtain ⟨-, hq2⟩ := hq (ModuleCat.of R S)
  refine homology_equiv (a₀.baseChange S) (a₁.baseChange S) ((d0 F).baseChange S)
    ((d1 F).baseChange S) (d0 F') (d1 F') (ψ₀.baseChange S) (ψ₁.baseChange S) (ψ₂.baseChange S)
    (th0 m) (th1 m) (th2 m) (Z1 F') (H1.mk F') (commAlgFunctorCocyclesOne_eq_ker F') (H1.mk_surjective F')
    (fun z ↦ H1.mk_eq_zero) ?_ ?_ (comparison_degree_one_coboundary m) (comparison_degree_two_coboundary m) b0.2 b1 b2.1 hq2.1 hq2.2
  · intro y
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hc0, LinearMap.baseChange_comp,
      LinearMap.comp_apply]
  · intro y
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hc1, LinearMap.baseChange_comp,
      LinearMap.comp_apply]

end GlobalTheory.CompanionTheory.PerfVB.Cls
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModelComparisonDegreeOneBijectiveStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_comparison_degree_one_bijective : ∀ (R S C P₀ P₁ P₂ : Type) [CommRing R] [CommRing S] [Algebra R S] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F) (m : BC F F'), IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → Function.Bijective (th0 m) → Function.Bijective (th1 m) → Function.Bijective (th2 m) → ∃ e : Hc (a₀.baseChange S) (a₁.baseChange S) ≃ₗ[S] H1 F', ∀ (x : S ⊗[R] P₁) (hx : x ∈ LinearMap.ker (a₁.baseChange S)), ∃ hw : th1 m (ψ₁.baseChange S x) ∈ Z1 F', e (Submodule.Quotient.mk ⟨x, hx⟩) = H1.mk F' ⟨_, hw⟩ := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.Cls.model_comparison_degree_zero_bijective | exact GlobalTheory.CompanionTheory.PerfVB.Cls.model_comparison_degree_zero_bijective | (intros; apply GlobalTheory.CompanionTheory.PerfVB.Cls.model_comparison_degree_zero_bijective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseChangeMapIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseChangeMapIdentity
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfVB

theorem bc_self (R C : Type) [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) :
    ∃ l : BC F F, ∀ T b, l.α T b = b :=
  ⟨⟨fun _ => RingHom.id _, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ => ⟨TensorProduct.lid R _, fun b => by simp [TensorProduct.lid_tmul]⟩⟩, fun _ _ => rfl⟩

end GlobalTheory.CompanionTheory.PerfVB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseChangeMapIdentityStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_map_identity : ∀ (R C : Type) [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∃ l : BC F F, ∀ T b, l.α T b = b := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.bc_self | exact GlobalTheory.CompanionTheory.PerfVB.bc_self | (intros; apply GlobalTheory.CompanionTheory.PerfVB.bc_self <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModelSteinOfComparison
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModelSteinOfComparison
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem comparison_degree_one_tensor_coboundary {R k C : Type} [CommRing R] [CommRing k] [Algebra R k] [Category.{0} C]
    {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} k} (m : BC F F') (y : k ⊗[R] C0 F) :
    th1 m ((d0 F).lTensor k y) = d0 F' (th0 m y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul s f =>
    rw [LinearMap.lTensor_tmul, th1, th0, liftSemi_tmul, liftSemi_tmul, map_smul]
    congr 1
    funext T T' φ
    change m.α T' (d0 F f T T' φ) = d0 F' (c0 m f) T T' φ
    rw [amitsur_d0_apply, amitsur_d0_apply, map_sub, m.naturality]
    rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem const_on_fibre : ∀ (R k C P₀ P₁ P₂ : Type) [CommRing R] [Field k] [Algebra R k] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} k) [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F) (m : BC F F') (e : P₀), IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → Function.Bijective (th0 m) → Stein F' → a₀ e = 0 → ψ₀ e = 1 → ∀ x : k ⊗[R] P₀, a₀.lTensor k x = 0 → ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e) := by
  intro R k C P₀ P₁ P₂ _ _ _ _ F F' _ _ _ _ _ _ a₀ a₁ ψ₀ ψ₁ ψ₂ m e hM hb hS ha he x hx
  obtain ⟨-, h2, -, hQ⟩ := hM
  have hx1 : (d0 F).lTensor k (ψ₀.lTensor k x) = ψ₁.lTensor k (a₀.lTensor k x) := by
    have h := congrArg (LinearMap.lTensor k) h2
    rw [LinearMap.lTensor_comp, LinearMap.lTensor_comp] at h
    exact (LinearMap.congr_fun h x).symm
  have hv : d0 F' (th0 m (ψ₀.lTensor k x)) = 0 := by
    rw [← comparison_degree_one_tensor_coboundary, hx1, hx, map_zero, map_zero]
  obtain ⟨c, hc⟩ := (hS.1 _).1 hv
  have hone : c0 m (1 : C0 F) = 1 := funext fun T ↦ map_one (m.α T)
  have hce : th0 m (ψ₀.lTensor k (c • ((1 : k) ⊗ₜ[R] e))) = th0 m (ψ₀.lTensor k x) := by
    rw [← hc, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one, LinearMap.lTensor_tmul, he, th0,
      liftSemi_tmul, hone, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
  have hψ : ψ₀.lTensor k (x - c • ((1 : k) ⊗ₜ[R] e)) = 0 := by
    rw [map_sub, hb.1 hce, sub_self]
  have ha' : a₀.lTensor k (x - c • ((1 : k) ⊗ₜ[R] e)) = 0 := by
    rw [map_sub, hx, TensorProduct.smul_tmul', LinearMap.lTensor_tmul, ha, TensorProduct.tmul_zero,
      sub_zero]
  obtain ⟨y, hy⟩ := (hQ (ModuleCat.of R k)).1.1 _ ha' ⟨0, by rw [map_zero]; exact hψ.symm⟩
  refine ⟨c, sub_eq_zero.1 ?_⟩
  rw [← hy]
  rfl

end GlobalTheory.CompanionTheory.PerfVB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModelSteinOfComparisonStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_stein_of_comparison : ∀ (R k C P₀ P₁ P₂ : Type) [CommRing R] [Field k] [Algebra R k] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} k) [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F) (m : BC F F') (e : P₀), IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → Function.Bijective (th0 m) → Stein F' → a₀ e = 0 → ψ₀ e = 1 → ∀ x : k ⊗[R] P₀, a₀.lTensor k x = 0 → ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e) := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.const_on_fibre | exact GlobalTheory.CompanionTheory.PerfVB.const_on_fibre | (intros; apply GlobalTheory.CompanionTheory.PerfVB.const_on_fibre <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomotopyDataCohomologyBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomotopyDataCohomologyBaseChange
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.PerfVB.ContrBC

theorem nonempty_Hc_equiv_of_contraction {S A B C H : Type} [CommRing S] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup H] [Module S A] [Module S B] [Module S C]
    [Module S H] (f : A →ₗ[S] B) (g : B →ₗ[S] C) (j : H →ₗ[S] B) (π : B →ₗ[S] H)
    (h : B →ₗ[S] A) (h' : C →ₗ[S] B) (hπj : π ∘ₗ j = LinearMap.id) (hgj : g ∘ₗ j = 0)
    (hπf : π ∘ₗ f = 0) (hc : j ∘ₗ π + f ∘ₗ h + h' ∘ₗ g = LinearMap.id) :
    Nonempty (Hc f g ≃ₗ[S] H) := by
  have hgj' : ∀ y, j y ∈ LinearMap.ker g := fun y => LinearMap.mem_ker.2 (LinearMap.congr_fun hgj y)
  have hπj' : ∀ y, π (j y) = y := fun y => LinearMap.congr_fun hπj y
  have hπf' : ∀ x, π (f x) = 0 := fun x => LinearMap.congr_fun hπf x
  have hc' : ∀ b, j (π b) + f (h b) + h' (g b) = b := fun b => LinearMap.congr_fun hc b
  have hle : Submodule.comap (LinearMap.ker g).subtype (LinearMap.range f) ≤
      LinearMap.ker (π ∘ₗ (LinearMap.ker g).subtype) := by
    rintro ⟨z, hz⟩ hzN
    obtain ⟨x, rfl⟩ : ∃ x, f x = z := LinearMap.mem_range.1 (Submodule.mem_comap.1 hzN)
    rw [LinearMap.mem_ker]
    exact hπf' x
  refine ⟨LinearEquiv.ofLinear (Submodule.liftQ _ (π ∘ₗ (LinearMap.ker g).subtype) hle)
    ((Submodule.comap (LinearMap.ker g).subtype (LinearMap.range f)).mkQ ∘ₗ
      LinearMap.codRestrict (LinearMap.ker g) j hgj') ?_ ?_⟩
  · refine LinearMap.ext fun y => ?_
    exact hπj' y
  · refine LinearMap.ext fun q => ?_
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective
      (Submodule.comap (LinearMap.ker g).subtype (LinearMap.range f)) q
    have hz' : g z = 0 := LinearMap.mem_ker.1 hz
    have e : z = j (π z) + f (h z) := by
      have := hc' z
      rw [hz', map_zero, add_zero] at this
      exact this.symm
    have key : (⟨j (π z), hgj' (π z)⟩ : LinearMap.ker g) - ⟨z, hz⟩ ∈
        Submodule.comap (LinearMap.ker g).subtype (LinearMap.range f) := by
      refine Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨-h z, ?_⟩)
      change f (-h z) = j (π z) - z
      calc f (-h z) = -f (h z) := map_neg _ _
        _ = j (π z) - (j (π z) + f (h z)) := by abel
        _ = j (π z) - z := by rw [← e]
    exact (Submodule.Quotient.eq _).2 key

theorem nonempty_Hc_baseChange_equiv (R A B C H S : Type) [CommRing R] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup H] [Module R A] [Module R B] [Module R C]
    [Module R H] [CommRing S] [Algebra R S] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (j : H →ₗ[R] B)
    (π : B →ₗ[R] H) (h : B →ₗ[R] A) (h' : C →ₗ[R] B) (_hgf : g ∘ₗ f = 0)
    (hπj : π ∘ₗ j = LinearMap.id) (hgj : g ∘ₗ j = 0) (hπf : π ∘ₗ f = 0)
    (hc : j ∘ₗ π + f ∘ₗ h + h' ∘ₗ g = LinearMap.id) :
    Nonempty (Hc (f.baseChange S) (g.baseChange S) ≃ₗ[S] S ⊗[R] H) := by
  refine nonempty_Hc_equiv_of_contraction (f.baseChange S) (g.baseChange S) (j.baseChange S)
    (π.baseChange S) (h.baseChange S) (h'.baseChange S) ?_ ?_ ?_ ?_
  · rw [← LinearMap.baseChange_comp, hπj, LinearMap.baseChange_id]
  · rw [← LinearMap.baseChange_comp, hgj, LinearMap.baseChange_zero]
  · rw [← LinearMap.baseChange_comp, hπf, LinearMap.baseChange_zero]
  · rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_add, ← LinearMap.baseChange_add, hc, LinearMap.baseChange_id]

end GlobalTheory.CompanionTheory.PerfVB.ContrBC
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomotopyDataCohomologyBaseChangeStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homotopy_data_cohomology_base_change : ∀ (R A B C H S : Type) [CommRing R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup H] [Module R A] [Module R B] [Module R C] [Module R H] [CommRing S] [Algebra R S] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (j : H →ₗ[R] B) (π : B →ₗ[R] H) (h : B →ₗ[R] A) (h' : C →ₗ[R] B), g ∘ₗ f = 0 → π ∘ₗ j = LinearMap.id → g ∘ₗ j = 0 → π ∘ₗ f = 0 → j ∘ₗ π + f ∘ₗ h + h' ∘ₗ g = LinearMap.id → Nonempty (Hc (f.baseChange S) (g.baseChange S) ≃ₗ[S] S ⊗[R] H) := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.ContrBC.nonempty_Hc_baseChange_equiv | exact GlobalTheory.CompanionTheory.PerfVB.ContrBC.nonempty_Hc_baseChange_equiv | (intros; apply GlobalTheory.CompanionTheory.PerfVB.ContrBC.nonempty_Hc_baseChange_equiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparisonMapsBijectiveFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparisonMapsBijectiveFinite
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.PerfVB

section Pi

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

def piS {I : Type} {M N : I → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module S (N i)]
    (u : ∀ i, M i →ₛₗ[algebraMap R S] N i) :
    (∀ i, M i) →ₛₗ[algebraMap R S] (∀ i, N i) where
  toFun x i := u i (x i)
  map_add' x y := funext fun i ↦ map_add (u i) _ _
  map_smul' r x := funext fun i ↦ (u i).map_smulₛₗ r (x i)

theorem liftSemi_piS_bijective {I : Type} [Finite I] {M N : I → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] [∀ i, AddCommGroup (N i)] [∀ i, Module S (N i)]
    (u : ∀ i, M i →ₛₗ[algebraMap R S] N i) (hu : ∀ i, Function.Bijective (liftSemi (u i))) :
    Function.Bijective (liftSemi (piS u)) := by
  classical
  haveI := Fintype.ofFinite I
  let e := TensorProduct.piRight R S S M
  have key : (liftSemi (piS u) : S ⊗[R] (∀ i, M i) → ∀ i, N i) =
      (Pi.map fun i ↦ liftSemi (u i)) ∘ e := by
    funext t
    induction t using TensorProduct.induction_on with
    | zero =>
      funext i
      simp
    | add a b ha hb =>
      simp only [map_add (f := _), Function.comp_apply] at ha hb ⊢
      rw [ha, hb]
      funext i
      simp
    | tmul s x =>
      funext i
      simp [e, liftSemi_tmul, piS]
  rw [key]
  exact (Function.Bijective.piMap hu).comp e.bijective

end Pi

section Cochains

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {C : Type} [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} S}

def cT (m : BC F F') (T : C) : F.obj T →ₛₗ[algebraMap R S] F'.obj T where
  toFun := m.α T
  map_add' := map_add (m.α T)
  map_smul' := m.smul T

theorem liftSemi_cT_bijective (m : BC F F') (T : C) : Function.Bijective (liftSemi (cT m T)) := by
  obtain ⟨e, he⟩ := m.bij T
  have key : (liftSemi (cT m T) : S ⊗[R] F.obj T → F'.obj T) = e := by
    funext t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul s b =>
      have h1 : s ⊗ₜ[R] b = s • ((1 : S) ⊗ₜ[R] b) := by simp [TensorProduct.smul_tmul']
      rw [liftSemi_tmul, h1, map_smul, he]
      rfl
  rw [key]
  exact e.bijective

theorem comparison_degree_zero_bijective [Finite C] (m : BC F F') : Function.Bijective (th0 m) :=
  liftSemi_piS_bijective (fun T ↦ cT m T) fun T ↦ liftSemi_cT_bijective m T

theorem comparison_degree_one_bijective [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (m : BC F F') :
    Function.Bijective (th1 m) :=
  liftSemi_piS_bijective (fun T ↦ piS fun T' ↦ piS fun _ : T ⟶ T' ↦ cT m T') fun _ ↦
    liftSemi_piS_bijective _ fun T' ↦ liftSemi_piS_bijective _ fun _ ↦ liftSemi_cT_bijective m T'

theorem comparison_degree_two_bijective [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (m : BC F F') :
    Function.Bijective (th2 m) :=
  liftSemi_piS_bijective
    (fun T ↦ piS fun T' ↦ piS fun T'' ↦ piS fun _ : T ⟶ T' ↦ piS fun _ : T' ⟶ T'' ↦ cT m T'')
    fun _ ↦ liftSemi_piS_bijective _ fun _ ↦ liftSemi_piS_bijective _ fun T'' ↦
      liftSemi_piS_bijective _ fun _ ↦ liftSemi_piS_bijective _ fun _ ↦ liftSemi_cT_bijective m T''

end Cochains

theorem th_bijective (R S P : Type) [CommRing R] [CommRing S] [Algebra R S] [SemilatticeInf P]
    [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (F' : Pᵒᵖ ⥤ CommAlgCat.{0} S) (m : BC F F') :
    Function.Bijective (th0 m) ∧ Function.Bijective (th1 m) ∧ Function.Bijective (th2 m) := by
  haveI : Finite Pᵒᵖ := Finite.of_injective (Opposite.unop : Pᵒᵖ → P) Opposite.unop_injective
  haveI : ∀ T T' : Pᵒᵖ, Finite (T ⟶ T') := fun T T' ↦ inferInstance
  exact ⟨comparison_degree_zero_bijective m, comparison_degree_one_bijective m, comparison_degree_two_bijective m⟩

end GlobalTheory.CompanionTheory.PerfVB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparisonMapsBijectiveFiniteStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_maps_bijective_finite : ∀ (R S P : Type) [CommRing R] [CommRing S] [Algebra R S] [SemilatticeInf P] [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (F' : Pᵒᵖ ⥤ CommAlgCat.{0} S) (m : BC F F'), Function.Bijective (th0 m) ∧ Function.Bijective (th1 m) ∧ Function.Bijective (th2 m) := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.th_bijective | exact GlobalTheory.CompanionTheory.PerfVB.th_bijective | (intros; apply GlobalTheory.CompanionTheory.PerfVB.th_bijective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGeneralizedInverseOfUnitKernel
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGeneralizedInverseOfUnitKernel
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem exists_generalisedInverse_of_fibre_ker_span :
    ∀ (R P₀ P₁ : Type) [CommRing R] [AddCommGroup P₀] [Module R P₀] [Module.Finite R P₀] [Module.Projective R P₀] [AddCommGroup P₁] [Module R P₁] [Module.Finite R P₁] [Module.Projective R P₁] (a₀ : P₀ →ₗ[R] P₁) (e : P₀), a₀ e = 0 → (∀ (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] P₀), a₀.lTensor k x = 0 → ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e)) → ∃ t : P₁ →ₗ[R] P₀, a₀ ∘ₗ t ∘ₗ a₀ = a₀ := by
  intro R P₀ P₁ _ _ _ _ _ _ _ _ _ a₀ e he hker
  have hcomp : a₀ ∘ₗ LinearMap.toSpanSingleton R P₀ e = 0 := by
    ext
    simp [he]
  have hexact : ∀ (m : Ideal R) [m.IsMaximal],
      Function.Exact (LinearMap.lTensor m.ResidueField (LinearMap.toSpanSingleton R P₀ e))
        (LinearMap.lTensor m.ResidueField a₀) := by
    intro m _ y
    constructor
    · intro hy
      obtain ⟨c, rfl⟩ := hker m.ResidueField y hy
      refine ⟨c ⊗ₜ[R] (1 : R), ?_⟩
      rw [LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply, one_smul,
        TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    · rintro ⟨z, rfl⟩
      rw [← LinearMap.lTensor_comp_apply, hcomp, LinearMap.lTensor_zero, LinearMap.zero_apply]
  obtain ⟨s, t, hst⟩ := GlobalTheory.exists_homotopy_of_forall_exact_residueField hcomp hexact
  refine ⟨t, LinearMap.ext fun x => ?_⟩
  have hx : LinearMap.toSpanSingleton R P₀ e (s x) + t (a₀ x) = x := LinearMap.congr_fun hst x
  have htx : t (a₀ x) = x - LinearMap.toSpanSingleton R P₀ e (s x) := eq_sub_of_add_eq' hx
  show a₀ (t (a₀ x)) = a₀ x
  rw [htx, map_sub, LinearMap.toSpanSingleton_apply, map_smul, he, smul_zero, sub_zero]

end GlobalTheory.CompanionTheory.PerfVB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGeneralizedInverseOfUnitKernelStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generalized_inverse_of_unit_kernel : ∀ (R P₀ P₁ : Type) [CommRing R] [AddCommGroup P₀] [Module R P₀] [Module.Finite R P₀] [Module.Projective R P₀] [AddCommGroup P₁] [Module R P₁] [Module.Finite R P₁] [Module.Projective R P₁] (a₀ : P₀ →ₗ[R] P₁) (e : P₀), a₀ e = 0 → (∀ (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] P₀), a₀.lTensor k x = 0 → ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e)) → ∃ t : P₁ →ₗ[R] P₀, a₀ ∘ₗ t ∘ₗ a₀ = a₀ := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.exists_generalisedInverse_of_fibre_ker_span | exact GlobalTheory.CompanionTheory.PerfVB.exists_generalisedInverse_of_fibre_ker_span | (intros; apply GlobalTheory.CompanionTheory.PerfVB.exists_generalisedInverse_of_fibre_ker_span <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModelComplexUnitElement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModelComplexUnitElement
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem lid_lTensor_unit {R A B : Type} [CommRing R] [AddCommGroup A] [AddCommGroup B] [Module R A]
    [Module R B] (f : A →ₗ[R] B) (u : R ⊗[R] A) :
    TensorProduct.lid R B (f.lTensor R u) = f (TensorProduct.lid R A u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul r a => simp

theorem d0_one {R C : Type} [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) :
    d0 F (1 : C0 F) = 0 := by
  funext T T' φ
  simp [d0]

theorem unit_of_model : ∀ (R C P₀ P₁ P₂ : Type) [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂]
    (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F)
    (ψ₂ : P₂ →ₗ[R] C2 F), IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → ∃ e : P₀, a₀ e = 0 ∧ ψ₀ e = 1 := by
  intro R C P₀ P₁ P₂ _ _ F _ _ _ _ _ _ a₀ a₁ ψ₀ ψ₁ ψ₂ h
  obtain ⟨-, -, -, hM⟩ := h
  obtain ⟨x, y, h1, h2⟩ := (hM (ModuleCat.of R R)).1.2 ((1 : R) ⊗ₜ[R] (1 : C0 F))
    (by simp [d0_one F])
  have h1' : a₀.lTensor R x = 0 := h1
  have h2' : ψ₀.lTensor R x - (1 : R) ⊗ₜ[R] (1 : C0 F) = 0 := by simpa using h2
  refine ⟨TensorProduct.lid R P₀ x, ?_, ?_⟩
  · rw [← lid_lTensor_unit, h1', map_zero]
  · rw [← lid_lTensor_unit, sub_eq_zero.mp h2']
    simp

end GlobalTheory.CompanionTheory.PerfVB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModelComplexUnitElementStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_complex_unit_element : ∀ (R C P₀ P₁ P₂ : Type) [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F), IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → ∃ e : P₀, a₀ e = 0 ∧ ψ₀ e = 1 := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.unit_of_model | exact GlobalTheory.CompanionTheory.PerfVB.unit_of_model | (intros; apply GlobalTheory.CompanionTheory.PerfVB.unit_of_model <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparisonDegreeOneTowerFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparisonDegreeOneTowerFormula
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem comparison_degree_one_tower (R S S' C : Type) [CommRing R] [CommRing S] [CommRing S'] [Algebra R S]
    [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) (F'' : C ⥤ CommAlgCat.{0} S')
    (m : BC F F') (n : BC F' F'') (l : BC F F'')
    (h : ∀ T b, l.α T b = n.α T (m.α T b)) (x : S ⊗[R] C1 F) :
    th1 l ((IsScalarTower.toAlgHom R S S').toLinearMap.rTensor (C1 F) x) = c1 n (th1 m x) := by
  have hcomp : ∀ f : GlobalTheory.CatCoh.C1 F,
      GlobalTheory.CompanionTheory.PerfVB.c1 l f =
        GlobalTheory.CompanionTheory.PerfVB.c1 n (GlobalTheory.CompanionTheory.PerfVB.c1 m f) := by
    intro f
    simp only [GlobalTheory.CompanionTheory.PerfVB.c1, LinearMap.coe_mk, AddHom.coe_mk, h]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s f =>
    simp only [GlobalTheory.CompanionTheory.PerfVB.th1, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
      IsScalarTower.coe_toAlgHom', GlobalTheory.CompanionTheory.PerfVB.liftSemi_tmul, LinearMap.map_smulₛₗ, hcomp]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.CompanionTheory.PerfVB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparisonDegreeOneTowerFormulaStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_degree_one_tower_formula : ∀ (R S S' C : Type) [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) (F'' : C ⥤ CommAlgCat.{0} S') (m : BC F F') (n : BC F' F'') (l : BC F F''), (∀ T b, l.α T b = n.α T (m.α T b)) → ∀ x : S ⊗[R] C1 F, th1 l ((IsScalarTower.toAlgHom R S S').toLinearMap.rTensor (C1 F) x) = c1 n (th1 m x) := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.comparison_degree_one_tower | exact GlobalTheory.CompanionTheory.PerfVB.comparison_degree_one_tower | (intros; apply GlobalTheory.CompanionTheory.PerfVB.comparison_degree_one_tower <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.PerfVB

theorem vb_of_equiv {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (E : M ≃ₗ[R] N) {g : ℕ} (h : VB R M g) : VB R N g := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Module.Finite.equiv E, Module.Projective.of_equiv E, fun p => ?_⟩
  rw [← Module.rankAtStalk_eq_of_equiv E]
  exact h3 p

theorem vb_pure {R P₀ P₁ P₂ : Type} [CommRing R] [AddCommGroup P₀] [AddCommGroup P₁]
    [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] [Module.Finite R P₀]
    [Module.Projective R P₀] [Module.Finite R P₁] [Module.Projective R P₁] [Module.Finite R P₂]
    [Module.Projective R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (hc : a₁ ∘ₗ a₀ = 0) (g : ℕ)
    (e : P₀) (he : a₀ e = 0)
    (hE : ∀ (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] P₀), a₀.lTensor k x = 0 →
      ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e))
    (hG : ∀ (k : Type) [Field k] [Algebra R k],
      Module.finrank k (Hc (a₀.baseChange k) (a₁.baseChange k)) = g)
    (hL : SmallLift a₀ a₁) : VB R (Hc (a₀.baseChange R) (a₁.baseChange R)) g := by
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_generalized_inverse_of_unit_kernel R P₀ P₁ a₀ e he hE
  obtain ⟨s, hs⟩ := GlobalTheory.T.local_splitting_global_generalized_inverse R P₁ P₂ a₁ (fun m _ => by
    haveI : Module.Free (Localization.AtPrime m) (TensorProduct R (Localization.AtPrime m) P₁) :=
      Module.free_of_flat_of_isLocalRing
    haveI : Module.Free (Localization.AtPrime m) (TensorProduct R (Localization.AtPrime m) P₂) :=
      Module.free_of_flat_of_isLocalRing
    exact GlobalTheory.T.generalized_inverse_of_lift_local _ _ _ _ (GlobalTheory.T.small_lift_base_change_local R P₀ P₁ P₂ _ a₀ a₁ hc hL))
  obtain ⟨j, π, h, h', hπj, haj, hπa, hsum⟩ := GlobalTheory.T.split_complex_homotopy_data R P₀ P₁ P₂ a₀ a₁ t s hc ht hs
  have hP := Module.Projective.of_split j π hπj
  have hsurj : Function.Surjective π := fun x => ⟨j x, by simpa using LinearMap.congr_fun hπj x⟩
  have hF := Module.Finite.of_surjective π hsurj
  obtain ⟨eR⟩ := GlobalTheory.T.homotopy_data_cohomology_base_change R P₀ P₁ P₂ _ R a₀ a₁ j π h h' hc hπj haj hπa hsum
  refine vb_of_equiv (eR.trans (TensorProduct.lid R _)).symm ⟨hF, hP, GlobalTheory.T.constant_fibre_rank_stalk_rank R _ g ?_⟩
  intro k _ _
  obtain ⟨ek⟩ := GlobalTheory.T.homotopy_data_cohomology_base_change R P₀ P₁ P₂ _ k a₀ a₁ j π h h' hc hπj haj hπa hsum
  rw [← ek.finrank_eq]
  exact hG k

theorem small_lift {R C P₀ P₁ P₂ : Type} [CommRing R] [Category.{0} C]
    (hbij : ∀ (S : Type) [CommRing S] [Algebra R S] (F : C ⥤ CommAlgCat.{0} R)
      (F' : C ⥤ CommAlgCat.{0} S) (m : BC F F'), Function.Bijective (th0 m) ∧
        Function.Bijective (th1 m) ∧ Function.Bijective (th2 m))
    (F : C ⥤ CommAlgCat.{0} R) [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀]
    [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F)
    (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F) (hM : IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂)
    (hs : ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B] (t : B),
      (∀ x, ¬ IsUnit x → x * t = 0) →
      ∃ (F' : C ⥤ CommAlgCat.{0} B) (_ : BC F F') (F'' : C ⥤ CommAlgCat.{0} (B ⧸ Ideal.span {t}))
        (m : BC F' F''), Function.Surjective m.coef.pull1) : SmallLift a₀ a₁ := by
  intro B _ _ _ t ht z hz
  obtain ⟨F', m0, F'', m, hsurj⟩ := hs B t ht
  obtain ⟨l, hl⟩ := GlobalTheory.T.base_change_map_composition R B (B ⧸ Ideal.span {t}) C F F' F'' m0 m
  obtain ⟨b0', b1', b2'⟩ := hbij B F F' m0
  obtain ⟨b0'', b1'', b2''⟩ := hbij (B ⧸ Ideal.span {t}) F F'' l
  obtain ⟨e', he'⟩ := GlobalTheory.T.model_comparison_degree_one_bijective R B C P₀ P₁ P₂ F F' a₀ a₁ ψ₀ ψ₁ ψ₂ m0 hM b0' b1' b2'
  obtain ⟨e'', he''⟩ :=
    GlobalTheory.T.model_comparison_degree_one_bijective R (B ⧸ Ideal.span {t}) C P₀ P₁ P₂ F F'' a₀ a₁ ψ₀ ψ₁ ψ₂ l hM b0'' b1'' b2''
  have hmk : (Ideal.Quotient.mkₐ R (Ideal.span {t})) = IsScalarTower.toAlgHom R B (B ⧸ Ideal.span {t}) := by
    ext b
    rfl
  have hzk : z ∈ (LinearMap.baseChange (B ⧸ Ideal.span {t}) a₁).ker := LinearMap.mem_ker.2 hz
  obtain ⟨w, hw⟩ := hsurj (e'' (Submodule.Quotient.mk ⟨z, hzk⟩))
  obtain ⟨q, rfl⟩ := e'.surjective w
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hxk : LinearMap.lTensor B a₁ x = 0 := LinearMap.mem_ker.1 hx
  have hxbk : LinearMap.rTensor P₁ (IsScalarTower.toAlgHom R B (B ⧸ Ideal.span {t})).toLinearMap x ∈
      (LinearMap.baseChange (B ⧸ Ideal.span {t}) a₁).ker := by
    rw [LinearMap.mem_ker]
    change LinearMap.lTensor (B ⧸ Ideal.span {t}) a₁ _ = 0
    rw [GlobalTheory.CompanionTheory.PerfVB.lTensor_rTensor_apply, hxk, map_zero]
  have key : e'' (Submodule.Quotient.mk ⟨_, hxbk⟩) = e'' (Submodule.Quotient.mk ⟨z, hzk⟩) := by
    rw [← hw]
    obtain ⟨hw1, h1⟩ := he'' _ hxbk
    obtain ⟨hw2, h2⟩ := he' x hx
    rw [h1, h2]
    have hp : ∀ c, m.coef.pull1 (GlobalTheory.CatCoh.H1.mk F' c) = GlobalTheory.CatCoh.H1.mk F'' (m.coef.pullbackOneCocycle c) :=
      fun c => rfl
    rw [hp]
    congr 1
    apply Subtype.ext
    show th1 l _ = c1 m (th1 m0 _)
    rw [← GlobalTheory.T.comparison_degree_one_tower_formula R B (B ⧸ Ideal.span {t}) C F F' F'' m0 m l hl]
    congr 1
    exact GlobalTheory.CompanionTheory.PerfVB.lTensor_rTensor_apply _ _ _
  have hq := (Submodule.Quotient.eq _).1 (e''.injective key)
  rw [Submodule.mem_comap] at hq
  obtain ⟨y, hy⟩ := LinearMap.mem_range.1 hq
  refine ⟨x, y, hxk, ?_⟩
  rw [hmk]
  rw [map_sub, Submodule.subtype_apply, Submodule.subtype_apply] at hy
  exact hy.symm

theorem perfVB : PerfVBSt := by
  unfold MainStatements.Hodge.PerfVBSt MainStatements.Hodge.AllFin
  intro R _ P _ _ F g hPerf hSt hfib hsm
  obtain ⟨P₀, P₁, P₂, P₃, a₀, a₁, a₂, ψ₀, ψ₁, ψ₂, ⟨f0, p0⟩, ⟨f1, p1⟩, ⟨f2, p2⟩, ⟨f3, p3⟩, h10, h21, hψ1, hψ2,
    ⟨ψ₃, hψ3⟩, hQ⟩ := hPerf
  have hMod : IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ := ⟨h10, hψ1, hψ2, fun M => ⟨(hQ M).1, (hQ M).2.1⟩⟩
  obtain ⟨e, he, hψe⟩ := GlobalTheory.T.model_complex_unit_element R Pᵒᵖ P₀ P₁ P₂ F a₀ a₁ ψ₀ ψ₁ ψ₂ hMod
  have hbij : ∀ (S : Type) [CommRing S] [Algebra R S] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R)
      (F' : Pᵒᵖ ⥤ CommAlgCat.{0} S) (m : BC F F'), Function.Bijective (th0 m) ∧
        Function.Bijective (th1 m) ∧ Function.Bijective (th2 m) := by
    intro S _ _ F F' m
    exact GlobalTheory.T.comparison_maps_bijective_finite R S P F F' m
  have hE : ∀ (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] P₀), a₀.lTensor k x = 0 →
      ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e) := by
    intro k _ _ x hx
    obtain ⟨F', m, hS⟩ := hSt k
    exact GlobalTheory.T.model_stein_of_comparison R k Pᵒᵖ P₀ P₁ P₂ F F' a₀ a₁ ψ₀ ψ₁ ψ₂ m e hMod (hbij k F F' m).1 hS he hψe x hx
  have hG : ∀ (k : Type) [Field k] [Algebra R k],
      Module.finrank k (Hc (a₀.baseChange k) (a₁.baseChange k)) = g := by
    intro k _ _
    obtain ⟨F', m, hm⟩ := hfib k
    obtain ⟨b0, b1, b2⟩ := hbij k F F' m
    obtain ⟨ek, -⟩ := GlobalTheory.T.model_comparison_degree_one_bijective R k Pᵒᵖ P₀ P₁ P₂ F F' a₀ a₁ ψ₀ ψ₁ ψ₂ m hMod b0 b1 b2
    rw [ek.finrank_eq]
    exact hm
  have hL : SmallLift a₀ a₁ := small_lift hbij F a₀ a₁ ψ₀ ψ₁ ψ₂ hMod (fun B _ _ _ t ht => hsm B t ht)
  haveI := f0
  haveI := p0
  haveI := f1
  haveI := p1
  haveI := f2
  haveI := p2
  have hv := vb_pure a₀ a₁ h10 g e he hE hG hL
  obtain ⟨l, -⟩ := GlobalTheory.T.base_change_map_identity R Pᵒᵖ F
  obtain ⟨c0, c1, c2⟩ := hbij R F F l
  obtain ⟨eR, -⟩ := GlobalTheory.T.model_comparison_degree_one_bijective R R Pᵒᵖ P₀ P₁ P₂ F F a₀ a₁ ψ₀ ψ₁ ψ₂ l hMod c0 c1 c2
  exact vb_of_equiv eR hv

end GlobalTheory.CompanionTheory.PerfVB
