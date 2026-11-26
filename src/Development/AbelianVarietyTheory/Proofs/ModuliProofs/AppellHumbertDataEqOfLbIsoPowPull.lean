module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsActionOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfLocallyRegular
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDerivationExtendOfFormallySmoothStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppellHumbertDataEqOfLbIsoPowPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

private lemma mul_mul_pow_mul_inv_pow_eq {A B G G' c c' : ℂ} (m n : ℕ) (h : A * G' ^ m = G ^ n * B)
    (hGc : G * c ≠ 0) : A * (G' * c') ^ m * ((G * c) ^ n)⁻¹ = B * c' ^ m * (c ^ n)⁻¹ := by
  have hGn : G ^ n ≠ 0 := pow_ne_zero n (left_ne_zero_of_mul hGc)
  rw [mul_pow, mul_pow, mul_inv,
    show A * (G' ^ m * c' ^ m) * ((G ^ n)⁻¹ * (c ^ n)⁻¹) = A * G' ^ m * (G ^ n)⁻¹ * (c' ^ m * (c ^ n)⁻¹) by ring,
    h, mul_comm (G ^ n) B, mul_inv_cancel_right₀ hGn]
  ring

private lemma mul_pow_mul_inv_pow_eq_of_factor {s a b a' b' x x' E E' : ℂ} (m n : ℕ) (ha : a = x * E * b)
    (ha' : a' = x' * E' * b') (hE : E' ^ m = E ^ n) (hx : x ≠ 0) (hx' : x' ≠ 0) (hEne : E ≠ 0)
    (hb : b ≠ 0) (hb' : b' ≠ 0) :
    s * b' ^ m * (b ^ n)⁻¹ = x ^ n * (x' ^ m)⁻¹ * (s * a' ^ m * (a ^ n)⁻¹) := by
  subst ha ha'
  rw [mul_pow, mul_pow, mul_pow, mul_pow, hE]
  field_simp


open PullHermitian in
theorem semicharacter_pull_eq_of_lbIso_pow :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left), L.IsLB → L'.IsLB →
  ∀ (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g') (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ)
    (Hm' : Matrix (Fin g') (Fin g') ℂ) (χ' : u'.Λ → ℂ), u.IsAH Hm χ → u'.IsAH Hm' χ' →
  ∀ (f : A ⟶ A') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hΛ₀ : ∀ l ∈ u.Λ, F l ∈ u'.Λ), (∀ z, u'.ex (F z) = u.ex z ≫ f) →
  ∀ m n : ℕ, LBIso (lbPow (L'.pull f.left) m) (lbPow L n) →
  ∀ l : u.Λ, χ l ^ n = χ' ⟨F l, hΛ₀ l l.2⟩ ^ m := by
  intro A A' _ _ L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hΛ₀ hex m n hiso

  have hH := hermForm_pull_eq_of_lbIso_pow A A' L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hex m n hiso
  obtain ⟨w, hw⟩ := hiso
  unfold HolUnif.IsAH at hu hu'
  have := u.discrete
  have hxf : ∀ z, (u'.ex (F z)).left = (u.ex z).left ≫ f.left := fun z => by rw [hex z]; rfl

  let φ : L.ι × L'.ι → (Fin g → ℂ) → ℂ := fun p z =>
    valAt' (u.ex z).left _ (w.s (idx f.left m n p.1 p.2)).val * u'.fr p.2 (F z) ^ m * (u.fr p.1 z ^ n)⁻¹
  let V : L.ι × L'.ι → Set (Fin g → ℂ) := fun p =>
    {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U p.1 ∧ ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ L'.U p.2}
  have hFc : Continuous F := LinearMap.continuous_of_finiteDimensional F
  have hV : ∀ p, IsOpen (V p) := fun p =>
    (u.hol (L.U p.1) 0).1.inter ((u'.hol (L'.U p.2) 0).1.preimage hFc)
  have hcov : ∀ z, ∃ p, z ∈ V p := fun z => by
    obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
    obtain ⟨j, hj⟩ := exists_chart (u'.ex (F z)).left hL'
    exact ⟨(i, j), hi, hj⟩
  have hdiv : ∀ i j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ L'.U j →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (lbPow L n) (lbPow (L'.pull f.left) m)).U (idx f.left m n i j) :=
    fun i j z hi hj => idx_chart _ f.left m n i j hi (by rw [← hxf]; exact hj)
  have hφd : ∀ p, DifferentiableOn ℂ (φ p) (V p) := fun p => by
    have h1 := ((u.hol _ (w.s (idx f.left m n p.1 p.2)).val).2).mono
      (fun z (hz : z ∈ V p) => hdiv p.1 p.2 z hz.1 hz.2)
    have h2 : DifferentiableOn ℂ (fun z => u'.fr p.2 (F z)) (V p) :=
      (u'.fr_hol p.2).comp (LinearMap.toContinuousLinearMap F).differentiable.differentiableOn
        (fun z hz => hz.2)
    have h3 : DifferentiableOn ℂ (fun z => u.fr p.1 z) (V p) := (u.fr_hol p.1).mono (fun z hz => hz.1)
    exact (h1.mul (h2.pow m)).mul ((h3.pow n).inv fun z hz => pow_ne_zero _ (u.fr_ne _ z hz.1))
  have hagree : ∀ p q z, z ∈ V p → z ∈ V q → φ p z = φ q z := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ z ⟨hi, hj⟩ ⟨hi', hj'⟩
    have hj₁ : ⊤ ≤ ((u.ex z).left ≫ f.left) ⁻¹ᵁ L'.U j := by rw [← hxf]; exact hj
    have hj₁' : ⊤ ≤ ((u.ex z).left ≫ f.left) ⁻¹ᵁ L'.U j' := by rw [← hxf]; exact hj'
    have hval := val_iso_pow (u.ex z).left f.left m n w hw i i' j j' hi hi' hj₁ hj₁'
    have hc := u.fr_compat i i' z (inf_of _ hi hi')
    have hc' := u'.fr_compat j j' (F z) (inf_of _ hj hj')
    rw [hxf] at hc'
    have hne : u.fr i z ≠ 0 := u.fr_ne i z hi
    simp only [φ]
    rw [hc] at hne ⊢
    rw [hc']
    exact mul_mul_pow_mul_inv_pow_eq m n hval hne
  obtain ⟨r, hr, hrφ⟩ := exists_glue V hV hcov φ hφd hagree
  have hφne : ∀ i j z, z ∈ V (i, j) → φ (i, j) z ≠ 0 := by
    intro i j z hz
    have hd := hdiv i j z hz.1 hz.2
    simp only [φ]
    rw [valAt'_eq_unitVal _ hd]
    exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (u'.fr_ne j _ hz.2)))
      (inv_ne_zero (pow_ne_zero _ (u.fr_ne i z hz.1)))
  have hr_ne : ∀ z, r z ≠ 0 := fun z => by
    obtain ⟨⟨i, j⟩, hp⟩ := hcov z
    rw [hrφ _ z hp]
    exact hφne i j z hp
  have hexl : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => by
    rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
  have hexl' : ∀ (l : u.Λ) z, u'.ex (F (z + l)) = u'.ex (F z) := fun l z => by
    rw [map_add (f := _), u'.ex_add, (u'.ker _).2 (hΛ₀ _ l.2), _root_.mul_one]
  have hχne : ∀ l, χ l ≠ 0 := fun l h0 => by simpa [h0] using hu.2.2.1 l
  have hχne' : ∀ l, χ' l ≠ 0 := fun l h0 => by simpa [h0] using hu'.2.2.1 l
  let c : u.Λ → ℂ := fun l => χ l ^ n * (χ' ⟨F l, hΛ₀ l l.2⟩ ^ m)⁻¹
  have h0 : ∀ a b : Fin g → ℂ, hermForm (0 : Matrix (Fin g) (Fin g) ℂ) a b = 0 := fun a b => by
    simp [hermForm]
  have hper : ∀ (l : u.Λ) z, r (z + l) =
      c l * Complex.exp (Real.pi * hermForm (0 : Matrix (Fin g) (Fin g) ℂ) z (l : Fin g → ℂ) +
        Real.pi / 2 * hermForm (0 : Matrix (Fin g) (Fin g) ℂ) (l : Fin g → ℂ) (l : Fin g → ℂ)) * r z := by
    intro l z
    simp only [h0, mul_zero, add_zero, Complex.exp_zero, _root_.mul_one]
    obtain ⟨⟨i, j⟩, hp⟩ := hcov z
    have hzl : z + l ∈ V (i, j) := ⟨by rw [hexl]; exact hp.1, by rw [hexl']; exact hp.2⟩
    rw [hrφ _ _ hzl, hrφ _ _ hp]
    have ha := hu.2.2.2 l i z hp.1
    have ha' := hu'.2.2.2 ⟨F l, hΛ₀ l l.2⟩ j (F z) hp.2
    dsimp only at ha'
    have hb : u.fr i (z + l) ≠ 0 := u.fr_ne i _ hzl.1
    have hb' : u'.fr j (F z + F l) ≠ 0 := u'.fr_ne j _ (by rw [← map_add (f := _)]; exact hzl.2)
    simp only [φ, c]
    rw [hexl l z, map_add (f := _)]
    refine mul_pow_mul_inv_pow_eq_of_factor m n ha ha' ?_ (hχne l) (hχne' _) (Complex.exp_ne_zero _) hb hb'
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    have e1 := hH z l
    have e2 := hH l l
    simp only [hermForm] at e1 e2
    linear_combination (Real.pi : ℂ) * e1 + ((Real.pi : ℂ) / 2) * e2
  have hcn : ∀ l, ‖c l‖ = 1 := fun l => by
    simp only [c, norm_mul, norm_inv, norm_pow, hu.2.2.1 l, hu'.2.2.1, one_pow, inv_one, _root_.mul_one]
  have key := (appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full 0 c r
    Matrix.isHermitian_zero hcn hr hr_ne hper).2.1
  intro l
  have hl := key l
  simp only [c] at hl
  exact (mul_inv_eq_one₀ (pow_ne_zero _ (hχne' _))).1 hl

theorem appellHumbert_data_eq_of_lbIso_pow_pull :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left) (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g') (Hm : Matrix (Fin g) (Fin g) ℂ) (Hm' : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ) (f : A ⟶ A') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ l ∈ u.Λ, F l ∈ u'.Λ) (n : ℕ), 0 < n → L.IsLB → L'.IsLB → u.IsAH Hm χ → u'.IsAH Hm' χ' → (∀ z, u'.ex (F z) = u.ex z ≫ f) → LBIso (lbPow L n) (lbPow (L'.pull f.left) n) → (∀ z w, hermForm Hm z w = hermForm Hm' (F z) (F w)) ∧ ∀ l : u.Λ, χ l ^ n = χ' ⟨F l, hF l l.2⟩ ^ n := by
  intro A A' _ _ L L' g g' u u' Hm Hm' χ χ' f F hF n hn hL hL' hu hu' hex hiso
  have hiso' := hiso.symm
  refine ⟨fun z w => ?_,
    semicharacter_pull_eq_of_lbIso_pow A A' L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hF hex n n hiso'⟩
  have h := hermForm_pull_eq_of_lbIso_pow A A' L L' hL hL' g g' u u' Hm χ Hm' χ' hu hu' f F hex n n hiso' z w
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  exact (mul_left_cancel₀ hn' h).symm

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientDescendGrpObj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

namespace QuotientDescent

variable {X X' : Scheme.{0}} {π : X ⟶ X'} {G : Over X} {G' : Over X'} {φ : G.left ⟶ G'.left}

noncomputable def up (H : IsPullback φ G.hom G'.hom π) {T : Over X'} (z : T ⟶ G') :
    (Over.pullback π).obj T ⟶ G :=
  Over.homMk (H.lift (pullback.fst T.hom π ≫ z.left) (pullback.snd T.hom π)
    (by rw [Category.assoc, Over.w, pullback.condition])) (H.lift_snd ..)

theorem up_left (H : IsPullback φ G.hom G'.hom π) {T : Over X'} (z : T ⟶ G') :
    (up H z).left ≫ φ = pullback.fst T.hom π ≫ z.left := H.lift_fst ..

theorem hom_ext (H : IsPullback φ G.hom G'.hom π) {T : Over X} {x y : T ⟶ G}
    (h : x.left ≫ φ = y.left ≫ φ) : x = y :=
  Over.OverMorphism.ext (H.hom_ext h ((Over.w x).trans (Over.w y).symm))

theorem up_comp (H : IsPullback φ G.hom G'.hom π) {T T' : Over X'} (u : T' ⟶ T) (z : T ⟶ G') :
    up H (u ≫ z) = (Over.pullback π).map u ≫ up H z := by
  refine hom_ext H ?_
  have A : ((Over.pullback π).map u).left ≫ pullback.fst T.hom π = pullback.fst T'.hom π ≫ u.left :=
    pullback.lift_fst _ _ _
  rw [up_left, Over.comp_left, Over.comp_left, Category.assoc, up_left, ← Category.assoc,
    ← Category.assoc, A]

variable {Γ : Type} [Group Γ] [Finite Γ] {ρ : Γ →* Aut X} {τ : Γ →* Aut G.left}

theorem up_injective (hq : IsAffineQuotient ρ π) (H : IsPullback φ G.hom G'.hom π) {T : Over X'}
    (hT : Flat T.hom) : Function.Injective (up H : (T ⟶ G') → _) := fun x y e ↦ by
  have Hp := (IsPullback.of_hasPullback T.hom π).flip
  obtain ⟨σ, hσ⟩ := exists_action_of_isPullback ρ hq.comp_eq Hp
  have hq' := hq.of_isPullback Hp (fun g ↦ (hσ g).2) (fun g ↦ (hσ g).1)
  refine Over.OverMorphism.ext (hq'.hom_ext ?_)
  rw [← up_left H, ← up_left H, e]

def Equivariant (ρ : Γ →* Aut X) (τ : Γ →* Aut G.left) {T : Over X'}
    (w : (Over.pullback π).obj T ⟶ G) : Prop :=
  ∀ g (s : pullback T.hom π ⟶ pullback T.hom π), s ≫ pullback.fst T.hom π = pullback.fst T.hom π →
    s ≫ pullback.snd T.hom π = pullback.snd T.hom π ≫ (ρ g).asIso.hom →
    s ≫ w.left = w.left ≫ (τ g).asIso.hom

theorem Equivariant.exists_up (hq : IsAffineQuotient ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hτ : ∀ g, (τ g).asIso.hom ≫ φ = φ) {T : Over X'} (hT : Flat T.hom)
    {w : (Over.pullback π).obj T ⟶ G} (hw : Equivariant ρ τ w) : ∃ z : T ⟶ G', up H z = w := by
  have Hp := (IsPullback.of_hasPullback T.hom π).flip
  obtain ⟨σ, hσ⟩ := exists_action_of_isPullback ρ hq.comp_eq Hp
  have hq' := hq.of_isPullback Hp (fun g ↦ (hσ g).2) (fun g ↦ (hσ g).1)
  obtain ⟨z, hz⟩ := hq'.exists_comp_eq (w.left ≫ φ) fun g ↦ by
    rw [← Category.assoc, hw g _ (hσ g).1 (hσ g).2, Category.assoc, hτ]
  refine ⟨Over.homMk z (hq'.hom_ext ?_), hom_ext H ((up_left H _).trans hz)⟩
  rw [reassoc_of% hz, H.w, pullback.condition]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ π) (Over.w w))

omit [Finite Γ] in
theorem equivariant_up (H : IsPullback φ G.hom G'.hom π) (hτ : ∀ g, (τ g).asIso.hom ≫ φ = φ)
    (hτ' : ∀ g, (τ g).asIso.hom ≫ G.hom = G.hom ≫ (ρ g).asIso.hom) {T : Over X'} (z : T ⟶ G') :
    Equivariant ρ τ (up H z) := fun g s h₁ h₂ ↦ by
  have e : (up H z).left ≫ G.hom = pullback.snd T.hom π := Over.w _
  refine H.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, hτ, up_left, reassoc_of% h₁]
  · rw [Category.assoc, Category.assoc, hτ', e, h₂, reassoc_of% e]

noncomputable def equivariantSubgroup [GrpObj G] (hτ : ∀ g, IsGrpPullback G G (ρ g).asIso.hom (τ g).asIso.hom)
    (T : Over X') : Subgroup ((Over.pullback π).obj T ⟶ G) :=
  ⨅ (g : Γ) (s : pullback T.hom π ⟶ pullback T.hom π)
    (_ : s ≫ pullback.fst T.hom π = pullback.fst T.hom π)
    (h : s ≫ pullback.snd T.hom π = pullback.snd T.hom π ≫ (ρ g).asIso.hom),
    (preHom (Over.homMk s h)).eqLocus (pushHom (hτ g) ((Over.pullback π).obj T))

omit [Finite Γ] in
theorem mem_equivariantSubgroup [GrpObj G] (hτ : ∀ g, IsGrpPullback G G (ρ g).asIso.hom (τ g).asIso.hom)
    {T : Over X'} {w : (Over.pullback π).obj T ⟶ G} :
    w ∈ equivariantSubgroup hτ T ↔ Equivariant ρ τ w := by
  simp only [equivariantSubgroup, Subgroup.mem_iInf]
  exact ⟨fun h g s h₁ h₂ ↦ congrArg (fun z ↦ z.left) (h g s h₁ h₂),
    fun h g s h₁ h₂ ↦ Over.OverMorphism.ext (h g s h₁ h₂)⟩

end QuotientDescent

open QuotientDescent

theorem quotient_descend_grpObj :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (O : Type) [CommRing O] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') (φ : G.left ⟶ G'.left) (τ : Γ →* Aut G.left) (a : OAct O G), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsPullback φ G.hom G'.hom π → Flat G'.hom → (∀ g, (τ g).asIso.hom ≫ φ = φ ∧ IsGrpPullback G G (ρ g).asIso.hom (τ g).asIso.hom ∧ ∀ c, (a.act c).left ≫ (τ g).asIso.hom = (τ g).asIso.hom ≫ (a.act c).left) → ∃ (_ : GrpObj G') (_ : IsCommMonObj G') (a' : OAct O G'), IsGrpPullback G G' π φ ∧ ∀ c, (a.act c).left ≫ φ = φ ≫ (a'.act c).left := by
  intro Γ _ _ O _ X X' ρ π G _ _ G' φ τ a ⟨h₁, h₂, h₃⟩ H hG' hτ
  have hq : IsAffineQuotient ρ π :=
    ⟨h₂, h₁, fun V ↦ (h₃ V).1, fun V s hs ↦ (h₃ V).2 s fun g _ ↦ (hs g).2⟩
  have hp (g) := (hτ g).2.1
  have f₀ : Flat (𝟙_ (Over X')).hom := inferInstanceAs (Flat (𝟙 X'))
  have f₂ {A B : Over X'} (hA : Flat A.hom) (hB : Flat B.hom) : Flat (A ⊗ B).hom :=
    inferInstanceAs (Flat (pullback.fst A.hom B.hom ≫ A.hom))
  have inj {T : Over X'} (hT : Flat T.hom) {x y : T ⟶ G'} (e : up H x = up H y) : x = y :=
    up_injective hq H hT e
  have ex {T : Over X'} (hT : Flat T.hom) {w : (Over.pullback π).obj T ⟶ G}
      (hw : w ∈ equivariantSubgroup hp T) : ∃ z : T ⟶ G', up H z = w :=
    ((mem_equivariantSubgroup hp).mp hw).exists_up hq H (fun g ↦ (hτ g).1) hT
  have mem {T : Over X'} (z : T ⟶ G') : up H z ∈ equivariantSubgroup hp T :=
    (mem_equivariantSubgroup hp).mpr (equivariant_up H (fun g ↦ (hτ g).1) (fun g ↦ (hp g).1.w) z)
  obtain ⟨m, hm⟩ := ex (f₂ hG' hG') (mul_mem (mem (fst G' G')) (mem (snd G' G')))
  obtain ⟨e, he⟩ := ex f₀ (one_mem _)
  obtain ⟨i, hi⟩ := ex hG' (inv_mem (mem (𝟙 G')))
  have hb (c : O) : ∃ z : G' ⟶ G', up H z = up H (𝟙 G') ≫ a.act c :=
    ex hG' ((mem_equivariantSubgroup hp).mpr fun g s k₁ k₂ ↦ by
      rw [Over.comp_left, Category.assoc, (hτ g).2.2,
        reassoc_of% ((mem_equivariantSubgroup hp).mp (mem (𝟙 G')) g s k₁ k₂)])
  choose b hb using hb
  have hm' {T : Over X'} (u : T ⟶ G' ⊗ G') :
      up H (u ≫ m) = up H (u ≫ fst _ _) * up H (u ≫ snd _ _) := by
    rw [up_comp, hm, MonObj.comp_mul, ← up_comp, ← up_comp]
  have he' {T : Over X'} (u : T ⟶ 𝟙_ _) : up H (u ≫ e) = 1 := by
    rw [up_comp, he, MonObj.comp_one]
  have hb' {T : Over X'} (u : T ⟶ G') (c : O) : up H (u ≫ b c) = up H u ≫ a.act c := by
    rw [up_comp, hb, ← Category.assoc, ← up_comp, Category.comp_id]
  letI : GrpObj G' :=
    { one := e
      mul := m
      one_mul := inj (f₂ f₀ hG') (by
        rw [hm', whiskerRight_fst, he', _root_.one_mul, whiskerRight_snd, leftUnitor_hom])
      mul_one := inj (f₂ hG' f₀) (by
        rw [hm', whiskerLeft_snd, he', _root_.mul_one, whiskerLeft_fst, rightUnitor_hom])
      mul_assoc := inj (f₂ (f₂ hG' hG') hG') (by
        rw [← Category.assoc, hm' (m ▷ G'), hm' (_ ≫ G' ◁ m), whiskerRight_fst, whiskerRight_snd,
          Category.assoc, Category.assoc, whiskerLeft_fst, whiskerLeft_snd, hm' (fst _ _),
          ← Category.assoc _ _ m, hm', Category.assoc, Category.assoc, associator_hom_fst,
          associator_hom_snd_fst, associator_hom_snd_snd, _root_.mul_assoc])
      inv := i
      left_inv := inj hG' (by rw [hm', he', lift_fst, lift_snd, hi, inv_mul_cancel])
      right_inv := inj hG' (by rw [hm', he', lift_fst, lift_snd, hi, mul_inv_cancel]) }
  have hmul {T : Over X'} (x y : T ⟶ G') : up H (x * y) = up H x * up H y := by
    rw [Hom.mul_def]
    exact (hm' _).trans (by rw [lift_fst, lift_snd])
  have : IsCommMonObj G' := ⟨inj (f₂ hG' hG') (by
    refine (hm' _).trans (Eq.trans ?_ hm.symm)
    rw [braiding_hom_fst, braiding_hom_snd, mul_comm])⟩
  let a' : OAct O G' :=
    { act := b
      hom c := by
        have := a.hom c
        refine ⟨inj f₀ ?_, inj (f₂ hG' hG') ?_⟩
        · rw [hb']
          change up H e ≫ _ = up H e
          rw [he, MonObj.one_comp]
        · rw [hb']
          change up H m ≫ _ = up H (_ ≫ m)
          rw [hm', hm, tensorHom_fst, tensorHom_snd, hb', hb', MonObj.mul_comp]
      one := inj hG' (by rw [hb, a.one, Category.comp_id])
      mul c d := inj hG' (by rw [hb', hb, hb, a.mul, Category.assoc])
      add c d := inj hG' (by rw [hmul, hb, hb, hb, a.add, MonObj.comp_mul]) }
  have sec {T : Over X} : ∃ s : T ⟶ (Over.pullback π).obj (Over.mk (T.hom ≫ π)),
      s.left ≫ pullback.fst _ π = 𝟙 T.left :=
    ⟨Over.homMk (pullback.lift (𝟙 T.left) T.hom (Category.id_comp _)) (pullback.lift_snd ..),
      pullback.lift_fst ..⟩
  refine ⟨inferInstance, this, a', ⟨H, fun T x y x₀ y₀ hx hy ↦ ?_⟩, fun c ↦ ?_⟩
  · obtain ⟨s, hs⟩ := sec (T := T)
    have k (z : Over.mk (T.hom ≫ π) ⟶ G') : (s ≫ up H z).left ≫ φ = z.left := by
      rw [Over.comp_left, Category.assoc, up_left, reassoc_of% hs]
    rw [← k, hmul, MonObj.comp_mul, QuotientDescent.hom_ext H ((k x₀).trans hx),
      QuotientDescent.hom_ext H ((k y₀).trans hy)]
  · obtain ⟨s, hs⟩ := sec (T := G)
    have k (z : Over.mk (G.hom ≫ π) ⟶ G') : (s ≫ up H z).left ≫ φ = z.left := by
      rw [Over.comp_left, Category.assoc, up_left, reassoc_of% hs]
    let u : Over.mk (G.hom ≫ π) ⟶ G' := Over.homMk φ H.w
    have hu : s ≫ up H u = 𝟙 G := QuotientDescent.hom_ext H ((k u).trans (Category.id_comp _).symm)
    have := k (u ≫ b c)
    rwa [hb', reassoc_of% hu] at this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeometricallyConnectedOfIsPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.SemiAbelianDescent

theorem exists_section {Z : Scheme.{0}} {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (f : Z ⟶ Spec (CommRingCat.of Ω)) [IsIntegralHom f] [Surjective f] :
    ∃ s : Spec (CommRingCat.of Ω) ⟶ Z, s ≫ f = 𝟙 _ := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  have : Nonempty Z := ⟨(f.surjective (Nonempty.some inferInstance)).choose⟩
  obtain ⟨z, -, hz⟩ := (isClosed_univ (X := Z)).exists_closed_singleton Set.univ_nonempty
  rw [isClosed_singleton_iff_isClosedImmersion] at hz
  set g : Spec (Z.residueField z) ⟶ Spec (CommRingCat.of Ω) := Z.fromSpecResidueField z ≫ f with hg
  have : IsIntegralHom g := inferInstance
  have : IsIso (Spec.preimage g) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
    rw [← IsIntegralHom.SpecMap_iff, Spec.map_preimage]
    infer_instance
  refine ⟨Spec.map (inv (Spec.preimage g)) ≫ Z.fromSpecResidueField z, ?_⟩
  calc (Spec.map (inv (Spec.preimage g)) ≫ Z.fromSpecResidueField z) ≫ f
      = Spec.map (inv (Spec.preimage g)) ≫ Spec.map (Spec.preimage g) := by
        rw [Category.assoc, Spec.map_preimage]
    _ = 𝟙 _ := by rw [← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]

theorem exists_lift {X X' : Scheme.{0}} (π : X ⟶ X') [IsIntegralHom π] [Surjective π]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (p : Spec (CommRingCat.of Ω) ⟶ X') :
    ∃ q : Spec (CommRingCat.of Ω) ⟶ X, q ≫ π = p := by
  obtain ⟨s, hs⟩ := exists_section (pullback.snd π p)
  refine ⟨s ≫ pullback.fst π p, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]

private theorem isClosed_range_diagonal_of_surjective_universallyClosed {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S) [Surjective j]
    {P : Scheme.{0}} (m : P ⟶ Limits.pullback f f) [UniversallyClosed m] (d : X ⟶ P)
    (hd : IsClosed (Set.range d)) (hc : d ≫ m = j ≫ pullback.diagonal f) :
    IsClosed (Set.range (pullback.diagonal f)) := by
  have key : Set.range (pullback.diagonal f) = m '' Set.range d := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := j.surjective y
      exact ⟨d x, ⟨x, rfl⟩, by rw [← Scheme.Hom.comp_apply, hc, Scheme.Hom.comp_apply]⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨j x, by rw [← Scheme.Hom.comp_apply, ← hc, Scheme.Hom.comp_apply]⟩
  rw [key]
  exact m.isClosedMap _ hd

theorem isSeparated_of_comp {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [UniversallyClosed j] [IsSeparated (j ≫ f)] : IsSeparated f := by
  have hm := MorphismProperty.pullbackMap (P := @UniversallyClosed) (f := j ≫ f) (g := j ≫ f)
    (f' := f) (g' := f) (i₁ := j) (i₂ := j) ‹UniversallyClosed j› ‹UniversallyClosed j› rfl rfl
  have hcl := isClosed_range_diagonal_of_surjective_universallyClosed j f
    (pullback.map (j ≫ f) (j ≫ f) f f j j (𝟙 _) (Category.comp_id _) (Category.comp_id _)) (pullback.diagonal (j ≫ f))
    (pullback.diagonal (j ≫ f)).isClosedEmbedding.isClosed_range (pullback.comp_diagonal j f).symm
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hcl⟩

theorem quasiCompact_of_comp {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [QuasiCompact (j ≫ f)] : QuasiCompact f := by
  refine ⟨fun U hU hU' => ?_⟩
  have h := (QuasiCompact.isCompact_preimage (f := j ≫ f) U hU hU').image j.continuous
  convert h using 1
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := j.surjective x
    exact ⟨y, by simpa using hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem geometricallyConnected_of_isPullback {X X' Y Y' : Scheme.{0}} {π : X ⟶ X'} [IsIntegralHom π]
    [Surjective π] {f : Y ⟶ X} {f' : Y' ⟶ X'} {φ : Y ⟶ Y'} (h : IsPullback φ f f' π)
    [GeometricallyConnected f] : GeometricallyConnected f' := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y => ?_⟩
  let ιK : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  obtain ⟨q, hq⟩ := exists_lift π (ιK ≫ y)
  have hA : ConnectedSpace ↥(pullback f q) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  have hιK : Surjective ιK := ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  let M := (IsPullback.paste_horiz (IsPullback.of_hasPullback f q) h).isoPullback.hom ≫
    (pullback.congrHom rfl hq).hom ≫ (pullbackLeftPullbackSndIso f' y ιK).inv ≫
      pullback.fst (pullback.snd f' y) ιK
  have hM : Surjective M := by dsimp only [M]; infer_instance
  exact M.surjective.connectedSpace M.continuous

theorem isSemiAbelian_descends {X X' : Scheme.{0}} {π : X ⟶ X'} {G : Over X} [GrpObj G] {G' : Over X'}
    [GrpObj G'] [IsCommMonObj G'] {φ : G.left ⟶ G'.left} [IsIntegralHom π] [Surjective π]
    (h : IsGrpPullback G G' π φ) [Smooth G'.hom] (hG : IsSemiAbelian G) : IsSemiAbelian G' := by
  obtain ⟨hc, hsm, hsep, hqc, hgc, hfib⟩ := hG
  have hpb : IsPullback φ G.hom G'.hom π := h.1
  have hφi : IsIntegralHom φ := MorphismProperty.of_isPullback hpb.flip ‹IsIntegralHom π›
  have hφs : Surjective φ := MorphismProperty.of_isPullback hpb.flip ‹Surjective π›
  have hw : φ ≫ G'.hom = G.hom ≫ π := hpb.w
  have hsep' : IsSeparated G'.hom := by
    have : IsSeparated (φ ≫ G'.hom) := by rw [hw]; infer_instance
    exact isSeparated_of_comp φ G'.hom
  have hqc' : QuasiCompact G'.hom := by
    have : QuasiCompact (φ ≫ G'.hom) := by rw [hw]; infer_instance
    exact quasiCompact_of_comp φ G'.hom
  have hgc' : GeometricallyConnected G'.hom := geometricallyConnected_of_isPullback hpb
  refine ⟨‹_›, ‹_›, hsep', hqc', hgc', ?_⟩
  intro Ω _ _ p
  obtain ⟨q, hq⟩ := exists_lift π p
  obtain ⟨T⟩ := hfib Ω q
  have h1 := isGrpPullback_pullback G q
  have h2 := IsGrpPullback.comp h1 h
  have h3 := isGrpPullback_pullback G' p
  obtain ⟨e, he, -⟩ := grpPullback_iso (h2.congr hq rfl) h3
  exact ⟨torusExtOfIso e T⟩

theorem main : ∀ (X X' : Scheme.{0}) (π : X ⟶ X') (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G.left ⟶ G'.left), IsIntegralHom π → Surjective π → IsGrpPullback G G' π φ → Smooth G'.hom → IsSemiAbelian G → IsSemiAbelian G' ∧ ((∃ U : X.Opens, (U : Set X) = abLocus G ∧ IsProper (G.hom ∣_ U)) → (∃ U : X'.Opens, (U : Set X') = abLocus G' ∧ IsProper (G'.hom ∣_ U))) := by
  intro X X' π G _ G' _ _ φ hi hs h hsm hG
  have hG' : IsSemiAbelian G' := isSemiAbelian_descends h hG
  refine ⟨hG', ?_⟩
  rintro ⟨U, hU, hP⟩
  have hloc : ∀ x, π x ∈ abLocus G' ↔ x ∈ abLocus G := abLocus_pullback abLocusOne hG' h.1
  have hV : IsOpen (abLocus G') := by
    have hc : (abLocus G')ᶜ = π '' (U : Set X)ᶜ := by
      ext y
      obtain ⟨x, rfl⟩ := π.surjective y
      constructor
      · intro hy
        refine ⟨x, ?_, rfl⟩
        rw [Set.mem_compl_iff, hU, ← hloc]
        exact hy
      · rintro ⟨x', hx', hxx⟩
        rw [Set.mem_compl_iff, ← hxx, hloc, ← hU]
        exact hx'
    rw [← isClosed_compl_iff, hc]
    exact π.isClosedMap _ U.isOpen.isClosed_compl
  let V' : X'.Opens := ⟨abLocus G', hV⟩
  have hpre : π ⁻¹ᵁ V' = U := by
    ext x
    change π x ∈ abLocus G' ↔ x ∈ (U : Set X)
    rw [hU, hloc]
  rw [← hpre] at hP
  have hpb : IsPullback φ G.hom G'.hom π := h.1
  have hw : φ ≫ G'.hom = G.hom ≫ π := hpb.w
  have hφs : Surjective φ := MorphismProperty.of_isPullback hpb.flip ‹Surjective π›
  have hle : G.hom ⁻¹ᵁ (π ⁻¹ᵁ V') ≤ φ ⁻¹ᵁ (G'.hom ⁻¹ᵁ V') := by
    intro x hx
    change G'.hom (φ x) ∈ V'
    rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
    exact hx
  let a := φ.resLE (G'.hom ⁻¹ᵁ V') (G.hom ⁻¹ᵁ (π ⁻¹ᵁ V')) hle
  have heq : a ≫ (G'.hom ∣_ V') = (G.hom ∣_ (π ⁻¹ᵁ V')) ≫ (π ∣_ V') := by
    rw [← cancel_mono V'.ι]
    simp only [a, Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
      Scheme.Hom.resLE_comp_ι_assoc, hw]
  have ha : Surjective a := by
    constructor
    intro z
    obtain ⟨w, hw'⟩ := φ.surjective ((G'.hom ⁻¹ᵁ V').ι z)
    have hz : (G'.hom ⁻¹ᵁ V').ι z ∈ ((G'.hom ⁻¹ᵁ V' : G'.left.Opens) : Set G'.left) := by
      rw [← Scheme.Opens.range_ι (G'.hom ⁻¹ᵁ V')]
      exact ⟨z, rfl⟩
    have hm : w ∈ Set.range (G.hom ⁻¹ᵁ (π ⁻¹ᵁ V')).ι := by
      rw [Scheme.Opens.range_ι]
      change π (G.hom w) ∈ V'
      rw [← Scheme.Hom.comp_apply, ← hw, Scheme.Hom.comp_apply, hw']
      exact hz
    obtain ⟨w', rfl⟩ := hm
    refine ⟨w', (G'.hom ⁻¹ᵁ V').ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply, hw']
  have hsep : IsSeparated G'.hom := hG'.separated
  have hcomp : UniversallyClosed (a ≫ (G'.hom ∣_ V')) := by
    rw [heq]
    infer_instance
  have huc : UniversallyClosed (G'.hom ∣_ V') := UniversallyClosed.of_comp_surjective a _
  exact ⟨V', rfl, by constructor⟩

end GlobalTheory.SemiAbelianDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ChiEqOneOrOfSym
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ThetaUnifCompare

open GlobalTheory.FrameValue CubeValues SymmetricSemicharacter EigenNorm

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}

theorem chi_neg_of_sym (hL : L.IsLB) (hs : Out.Sym A L) (h : u.IsAH Hm χ) (l : u.Λ) : χ (-l) = χ l := by
  obtain ⟨U, hU, s, hs⟩ := hs (default : PrimeSpectrum ℂ)
  have hr : Set.range (𝟙 A.left : A.left ⟶ A.left) ⊆ Set.range (A.hom ⁻¹ᵁ U).ι := by
    rintro x -
    refine ⟨⟨x, ?_⟩, rfl⟩
    have e : A.hom x = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    show A.hom x ∈ U
    rw [e]; exact hU
  obtain ⟨p, hp⟩ : ∃ p : A.left ⟶ (A.hom ⁻¹ᵁ U).toScheme, p ≫ (A.hom ⁻¹ᵁ U).ι = 𝟙 _ :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have hz : ∀ w, IsLift u (K := Fin 2) ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι]
      ((u.ex w).left ≫ p) ![-w, w] := fun w k => by
    fin_cases k
    · show ((u.ex w).left ≫ p) ≫ (A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left = (u.ex (-w)).left
      rw [Category.assoc, reassoc_of% hp]
      exact ex_neg_left u w
    · show ((u.ex w).left ≫ p) ≫ (A.hom ⁻¹ᵁ U).ι = (u.ex w).left
      rw [Category.assoc, hp, Category.comp_id]
  have hd : Differentiable ℂ fun w => genVal u hL s ((u.ex w).left ≫ p) ![-w, w] :=
    differentiable_genVal hL hs p (q := id) differentiable_id (z := fun w => ![-w, w])
      (fun k => by fin_cases k <;> simp <;> fun_prop) hz
  have hper : ∀ (l : u.Λ) w, genVal u hL s ((u.ex (w + l)).left ≫ p) ![-(w + l), w + l] =
      χ (-l) / χ l * genVal u hL s ((u.ex w).left ≫ p) ![-w, w] := fun l w => by
    have e₂ : ![-(w + l), w + l] = fun k => ![-w, w] k + ((![-l, l] : Fin 2 → u.Λ) k : Fin g → ℂ) := by
      funext k
      fin_cases k <;> simp [add_comm]
    rw [ex_add_period u w l l.2, e₂, genVal_add_period hL h s (hz w)]
    congr 1
    have n := chi_ne_zero h l
    simp [ahFactor, hermForm_neg_left, hermForm_neg_right]
    field_simp
  have hc := const_of_norm_periodic u hd (fun l w => by
    rw [hper, norm_mul, norm_div, h.2.2.1, h.2.2.1, div_one, _root_.one_mul])
  have e := hper l 0
  rw [hc _ 0] at e
  exact (div_eq_one_iff_eq (chi_ne_zero h l)).1
    (mul_right_cancel₀ (genVal_ne_zero hL s (hz 0)) (e.symm.trans (_root_.one_mul _).symm))

theorem chi_eq_one_or_of_sym (hL : L.IsLB) (hs : Out.Sym A L) (h : u.IsAH Hm χ) (l : u.Λ) : χ l = 1 ∨ χ l = -1 := by
  have e := chi_add hL h l (-l)
  have hi : (hermForm Hm l l).im = 0 := Complex.conj_eq_iff_im.1 (hermForm_conj Hm h.1 l l).symm
  rw [add_neg_cancel, chi_zero hL h, chi_neg_of_sym hL hs h, Submodule.coe_neg, hermForm_neg_right, Complex.neg_im,
    hi] at e
  exact mul_self_eq_one_iff.1 (by simpa using e.symm)

end GlobalTheory.ThetaUnifCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationAlongFibreOfSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationAlongFibreOfSmooth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

noncomputable def liftConstHom {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    R →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem liftConstHom_apply {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a : R) :
    liftConstHom p U a = constFn p U a := rfl

theorem liftConstHom_smooth {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens)
    (hp : Smooth p) (hU : IsAffineOpen U) : (liftConstHom p U).Smooth := by
  have h1 : (p.appLE ⊤ U (fun _ _ => trivial)).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth p hp ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (fun _ _ => trivial)
  exact RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)) h1

theorem app_constFn_of_comm {R S : Type} [CommRing R] [CommRing S] (x₀ : R →+* S) {Y X : Scheme.{0}}
    (q : Y ⟶ Sp S) (p : X ⟶ Sp R) (m : Y ⟶ X) (h : m ≫ p = q ≫ spMap x₀) (W : X.Opens) (a : R) :
    (m.app W).hom (constFn p W a) = constFn q (m ⁻¹ᵁ W) (x₀ a) := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ W (fun _ _ => trivial) ≫ m.app W =
      CommRingCat.ofHom x₀ ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ q.appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) := by
    rw [← Category.assoc (CommRingCat.ofHom x₀), Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    congr 1
    have e1 : p.appLE ⊤ W (fun _ _ => trivial) ≫ m.app W = (m ≫ p).appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) := by
      rw [Scheme.Hom.app_eq_appLE]
      exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    have e2 : (q ≫ spMap x₀).appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) =
        (Spec.map (CommRingCat.ofHom x₀)).appTop ≫ q.appLE ⊤ (m ⁻¹ᵁ W) (fun _ _ => trivial) :=
      Scheme.Hom.comp_appLE _ _ _ _ _
    rw [e1, ← e2]
    simp only [h]
  exact congrArg (fun φ => φ.hom a) key

theorem exists_locDer_of_smooth : ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (Y X : Scheme.{0}) (q : Y ⟶ Sp ℂ) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → ℂ) (W₀ : X.Opens), Smooth p → m ≫ p = q ≫ spMap x₀ → IsDer x₀ D → IsAffineOpen W₀ → ∃ d, LocDer q p m D W₀ d := by
  intro R _ x₀ Y X q p m D W₀ hp hm hD hW
  letI : Algebra R Γ(X, W₀) := (liftConstHom p W₀).toAlgebra
  haveI : Algebra.Smooth R Γ(X, W₀) := liftConstHom_smooth p W₀ hp hW
  have hc : ∀ a, (m.app W₀).hom (algebraMap R Γ(X, W₀) a) = liftConstHom q (m ⁻¹ᵁ W₀) (x₀ a) :=
    fun a => app_constFn_of_comm x₀ q p m hm W₀ a
  obtain ⟨d₀, h1, h2, h3⟩ := GlobalTheory.T.exists_derivation_extend' R Γ(X, W₀) Γ(Y, m ⁻¹ᵁ W₀) (m.app W₀).hom
    (fun r => liftConstHom q (m ⁻¹ᵁ W₀) (D r)) (fun a b => by rw [hD.1, map_add (f := _)])
    (fun a b => by rw [hD.2, hc, hc, map_add (f := _), map_mul, map_mul])
  obtain ⟨d, hd, -⟩ := GlobalTheory.T.exists_local_derivation_extension_of_affine R Y X q p m D W₀ hW d₀ h1 h2 h3
  exact ⟨d, hd⟩

end GlobalTheory.KS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationAlongFibreOfSmoothStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localDerivationAlongFibre_of_smooth : ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (Y X : Scheme.{0}) (q : Y ⟶ Sp ℂ) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → ℂ) (W₀ : X.Opens), Smooth p → m ≫ p = q ≫ spMap x₀ → IsDer x₀ D → IsAffineOpen W₀ → ∃ d, LocDer q p m D W₀ d := by
  first | exact @GlobalTheory.KS.exists_locDer_of_smooth | exact GlobalTheory.KS.exists_locDer_of_smooth | (intros; apply GlobalTheory.KS.exists_locDer_of_smooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsDominantGeometricPointOfIsPreimmersion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_isDominant_geometricPoint_of_isPreimmersion {Z W : Scheme.{0}} [IrreducibleSpace W]
    (a : Z ⟶ W) [IsPreimmersion a] [IsDominant a] [QuasiCompact a] :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (t : Sp k ⟶ Z), IsDominant t := by
  have hη : genericPoint W ∈ genericPoints W := by
    rw [genericPoints_eq_singleton]; rfl
  obtain ⟨z, hz⟩ := genericPoints_subset_range_of_isDominant a hη
  let k := AlgebraicClosure (Z.residueField z)
  let t : Sp k ⟶ Z := spMap (algebraMap (Z.residueField z) k) ≫ Z.fromSpecResidueField z
  refine ⟨k, inferInstance, inferInstance, t, ⟨fun z' => ?_⟩⟩
  have h₁ : z ⤳ z' := by
    rw [← a.isEmbedding.isInducing.specializes_iff, hz]
    exact genericPoint_specializes _
  have h₂ : z ∈ Set.range t :=
    ⟨IsLocalRing.closedPoint k, Scheme.fromSpecResidueField_apply z _⟩
  exact closure_mono (Set.singleton_subset_iff.mpr h₂) (specializes_iff_mem_closure.mp h₁)

theorem isOpenImmersion_of_etale_of_mono_pullback_snd {X U W : Scheme.{0}}
    [GlobalTheory.IsNormalScheme X] (j : U ⟶ X) [IsDominant j] (q : W ⟶ X) [Etale q] [IsSeparated q]
    [Mono (pullback.snd q j)] : IsOpenImmersion q := by
  let r : pullback q q ⟶ X := pullback.fst q q ≫ q
  have := isNormalScheme_of_smooth r
  have := isDominant_pullback_fst_of_isOpenMap j r r.isOpenMap
  have h : pullback.lift (f := q) (g := j) (pullback.fst r j ≫ pullback.fst q q) (pullback.snd r j)
        (by rw [Category.assoc]; exact pullback.condition) =
      pullback.lift (pullback.fst r j ≫ pullback.snd q q) (pullback.snd r j)
        (by rw [Category.assoc, ← pullback.condition (f := q) (g := q)]
            exact pullback.condition) := by
    rw [← cancel_mono (pullback.snd q j), pullback.lift_snd, pullback.lift_snd]
  have h' : pullback.fst r j ≫ pullback.fst q q = pullback.fst r j ≫ pullback.snd q q := by
    simpa only [pullback.lift_fst] using congrArg (· ≫ pullback.fst q j) h
  have he : pullback.fst q q = pullback.snd q q :=
    ext_of_isDominant_of_isSeparated q pullback.condition _ h'
  have : Mono q := ⟨fun a b hab => by
    rw [← pullback.lift_fst a b hab, he, pullback.lift_snd]⟩
  exact IsOpenImmersion.of_flat_of_mono q

theorem exists_opens_isOpenImmersion_extending_section : ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (Y : Scheme.{0}) (p : Y ⟶ X) (I : Type) [Finite I] (σ : I → (U ⟶ Y)), Etale p → IsSeparated p → (∀ i, σ i ≫ p = j) → (∀ (k : Type) [Field k] [IsAlgClosed k] (u : Sp k ⟶ U) (y : Sp k ⟶ Y), y ≫ p = u ≫ j → ∃ i, y = u ≫ σ i) → ∀ y : Y, ∃ (i : I) (W : Y.Opens), y ∈ W ∧ IsOpenImmersion (W.ι ≫ p) ∧ pullback.fst (W.ι ≫ p) j ≫ W.ι = pullback.snd (W.ι ≫ p) j ≫ σ i := by
  intro X U _ j hN _ _ _ _ Y p I _ σ _ _ hσ hgeo y
  have := IsNormalScheme.of_pred hN
  have := isNormalScheme_of_smooth p
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  let W : Y.Opens :=
    IsNormalScheme.component ⟨_, irreducibleComponent_mem_irreducibleComponents y⟩
  have hy : y ∈ W := mem_irreducibleComponent
  have : IsIntegral W.toScheme := inferInstance
  let q : W.toScheme ⟶ X := W.ι ≫ p
  have := isDominant_pullback_fst_of_isOpenMap j q q.isOpenMap
  have : ∀ z, IsIso ((pullback.fst q j).stalkMap z) :=
    isIso_stalkMap_of_flat_of_surjectiveOnStalks _
  have := IsNormalScheme.of_isIso_stalkMap (pullback.fst q j)
  obtain ⟨k, _, _, t, _⟩ := exists_isDominant_geometricPoint_of_isPreimmersion (pullback.fst q j)
  obtain ⟨i, hi⟩ := hgeo k (t ≫ pullback.snd q j) (t ≫ pullback.fst q j ≫ W.ι)
    (by simp only [Category.assoc]; rw [← pullback.condition])
  have he : pullback.fst q j ≫ W.ι = pullback.snd q j ≫ σ i :=
    ext_of_isDominant_of_isSeparated p
      (by simp only [Category.assoc]; rw [hσ, ← pullback.condition]) t
      (by rw [hi, Category.assoc])
  have : Mono (pullback.snd q j ≫ σ i) := by rw [← he]; infer_instance
  have : Mono (pullback.snd q j) := mono_of_mono _ (σ i)
  exact ⟨i, W, hy, isOpenImmersion_of_etale_of_mono_pullback_snd j q, he⟩

end GlobalTheory
end
