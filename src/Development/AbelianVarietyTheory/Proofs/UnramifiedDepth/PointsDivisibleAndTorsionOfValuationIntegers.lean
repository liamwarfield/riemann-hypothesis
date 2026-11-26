module

public import ReciprocityTheory.DualLattices.SubMemOfCompat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PointsDivisibleAndTorsionOfValuationIntegers
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem torsVal_valuationRing {O C : Type} [CommRing O] [IsDomain O] [Field C] [Algebra O C]
    {v : Valuation C NNReal} (hv : v.Integers O) : ValuationRing O := by
  refine @ValuationRing.mk _ _ _ ⟨fun a b => ?_⟩
  rcases le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hv h
    exact ⟨c, Or.inr hc.symm⟩
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hv h
    exact ⟨c, Or.inl hc.symm⟩

private theorem torsVal_exists_point {Ω : Type} [Field Ω] [IsAlgClosed Ω] {P A : Scheme.{0}}
    (ψ : P ⟶ A) [LocallyOfFiniteType ψ] [Surjective ψ] (x : Spec (CommRingCat.of Ω) ⟶ A) :
    ∃ p : Spec (CommRingCat.of Ω) ⟶ P, p ≫ ψ = x := by
  have hJ : JacobsonSpace ↥(Limits.pullback ψ x) :=
    LocallyOfFiniteType.jacobsonSpace (Limits.pullback.snd ψ x)
  obtain ⟨w⟩ : Nonempty ↥(Spec (CommRingCat.of Ω)) := inferInstance
  obtain ⟨z₀, -⟩ := (Limits.pullback.snd ψ x).surjective w
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(Limits.pullback ψ x)))
    ⟨z₀, trivial⟩ isClosed_univ.isLocallyClosed
  replace hz : IsClosed {z} := hz
  refine ⟨pointOfClosedPoint (Limits.pullback.snd ψ x) z hz ≫ Limits.pullback.fst _ _, ?_⟩
  rw [Category.assoc, Limits.pullback.condition, pointOfClosedPoint_comp_assoc]

private theorem torsVal_lift {R₀ : Type} [CommRing R₀] {X Y : Over (Spec (CommRingCat.of R₀))}
    (m : X ⟶ Y) [IsFinite m.left] {O C : Type} [CommRing O] [Field C] [Algebra R₀ O] [Algebra O C]
    [Algebra R₀ C] [IsScalarTower R₀ O C] {v : Valuation C NNReal} (hv : v.Integers O)
    (x : sp (R₀ := R₀) O ⟶ Y) (z : sp (R₀ := R₀) C ⟶ X)
    (h : z ≫ m = spMap (IsScalarTower.toAlgHom R₀ O C) ≫ x) :
    ∃! y : sp (R₀ := R₀) O ⟶ X, y ≫ m = x ∧ spMap (IsScalarTower.toAlgHom R₀ O C) ≫ y = z := by
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := torsVal_valuationRing hv
  haveI : IsFractionRing O C := hv.isFractionRing
  have hE : ValuativeCriterion.Existence m.left := by
    have h : UniversallyClosed m.left := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hU : ValuativeCriterion.Uniqueness m.left := IsSeparated.valuativeCriterion m.left
  let S : ValuativeCommSq m.left :=
    { R := O, K := C, i₁ := z.left, i₂ := x.left, commSq := ⟨congrArg Over.Hom.left h⟩ }
  obtain ⟨⟨l, h1, h2⟩⟩ := hE S
  have hw : l ≫ X.hom = (sp (R₀ := R₀) O).hom := by
    rw [← Over.w m, ← Category.assoc, h2]
    exact Over.w x
  refine ⟨Over.homMk l hw, ⟨Over.OverMorphism.ext h2, Over.OverMorphism.ext h1⟩, ?_⟩
  rintro y ⟨hy1, hy2⟩
  have := (hU S).elim ⟨y.left, congrArg Over.Hom.left hy2, congrArg Over.Hom.left hy1⟩ ⟨l, h1, h2⟩
  exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l this)

private theorem torsVal_comp_pow {R₀ : Type} [CommRing R₀] {G T : Over (Spec (CommRingCat.of R₀))}
    [GrpObj G] (y : T ⟶ G) (p : ℕ) : y ≫ ((𝟙 G) ^ p : G ⟶ G) = y ^ p := by
  rw [MonObj.comp_pow, Category.comp_id]

theorem points_divisible_and_torsion_of_valuation_integers :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) [Algebra (O : Type) C] [Algebra R₀ C] [IsScalarTower R₀ (O : Type) C] (p : ℕ), v.Integers (O : Type) → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Surjective ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : sp (R₀ := R₀) (O : Type) ⟶ G, ∃ y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = x) ∧
    ∀ z : sp (R₀ := R₀) C ⟶ G, z ^ p = 1 → ∃! y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = 1 ∧ spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ y = z) := by
  intro R₀ _ G _ _ O C _ _ _ v _ _ _ p hv hfin hsurj
  refine ⟨fun x => ?_, fun z hz => ?_⟩
  · obtain ⟨w, hw⟩ := torsVal_exists_point ((𝟙 G) ^ p : G ⟶ G).left
      (spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ x).left
    have hw' : w ≫ G.hom = (sp (R₀ := R₀) C).hom := by
      rw [← Over.w ((𝟙 G) ^ p : G ⟶ G), ← Category.assoc, hw]
      exact Over.w _
    obtain ⟨y, ⟨hy, -⟩, -⟩ := torsVal_lift ((𝟙 G) ^ p : G ⟶ G) hv x (Over.homMk w hw')
      (Over.OverMorphism.ext hw)
    exact ⟨y, by rw [← torsVal_comp_pow, hy]⟩
  · have := torsVal_lift ((𝟙 G) ^ p : G ⟶ G) hv 1 z
      (by rw [torsVal_comp_pow, hz, MonObj.comp_one])
    simpa only [torsVal_comp_pow] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantGeneratorDescendsMulN
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in
private theorem invGenDescent_gs_appLE {Y Y' : Scheme.{0}} (τ : Y' ⟶ Y) (W : Y.Opens) (W' : Y'.Opens)
    (h : W' ≤ τ ⁻¹ᵁ W) (a : Γ(Y, W)) (x : Y') (hx : x ∈ W') :
    gs (𝟙 Y') x W' ((τ.appLE W W' h).hom a) = gs τ x W a := by
  have e := (gs_res (𝟙 Y') x h hx ((τ.app W).hom a)).trans (gs_pull (𝟙 Y') τ x W (h hx) a)
  rw [Category.id_comp] at e
  exact e


open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in
private theorem invariant_generator_descent {X Y Y' : Scheme.{0}} (m : Y' ⟶ Y) {T : Type} (τ : T → (Y' ⟶ Y'))
    (hτ : ∀ t, τ t ≫ m = m)
    (H : ∀ (V : Y.Opens) (a : Γ(Y', m ⁻¹ᵁ V)),
      (∀ t, ∀ h : m ⁻¹ᵁ V ≤ τ t ⁻¹ᵁ (m ⁻¹ᵁ V), ((τ t).appLE _ _ h).hom a = a) →
      ∃! a' : Γ(Y, V), (m.app V).hom a' = a)
    (M : LB X) (hM : M.IsLB) (ψ : Y ⟶ X)
    (σ : LB.Gen (LB.LinComb M (K := PUnit) (fun _ => m ≫ ψ) (fun _ => 1))) (hσ : σ.IsGen)
    (inv : ∀ t (z : Y') (J : (Y' ⟶ X) → M.1), Good M z J → val σ (𝟙 Y' ≫ τ t) z J = val σ (𝟙 Y') z J) :
    ∃ t : (M.pull ψ).Gen, t.IsGen := by
  have inj : ∀ V : Y.Opens, Function.Injective (m.app V).hom := by
    intro V a b e
    obtain ⟨c, -, hc⟩ := H V ((m.app V).hom a) (fun t h => fn_ext fun x hx => by
      rw [invGenDescent_gs_appLE (τ t) _ _ h _ x hx, gs_pull (τ t) m x V (h hx), gs_pull (𝟙 Y') m x V hx, hτ,
        Category.id_comp])
    exact (hc a rfl).trans (hc b e.symm).symm
  have injU : ∀ V : Y.Opens, Function.Injective (pullU m V) := fun V a b e =>
    Units.ext (inj V (congrArg Units.val e))
  have descU : ∀ (V : Y.Opens) (u : Γ(Y', m ⁻¹ᵁ V)ˣ),
      (∀ t x, x ∈ m ⁻¹ᵁ V → gm (τ t) x _ u = gm (𝟙 Y') x _ u) → ∃ v : Γ(Y, V)ˣ, pullU m V v = u := by
    intro V u hu
    have key : ∀ u : Γ(Y', m ⁻¹ᵁ V)ˣ, (∀ t x, x ∈ m ⁻¹ᵁ V → gm (τ t) x _ u = gm (𝟙 Y') x _ u) →
        ∃ a : Γ(Y, V), (m.app V).hom a = u.val := fun u hu =>
      (H V u.val (fun t h => fn_ext fun x hx => by
        rw [invGenDescent_gs_appLE (τ t) _ _ h _ x hx, gs_unit (τ t) x (m ⁻¹ᵁ V) (h hx),
          gs_unit (𝟙 Y') x (m ⁻¹ᵁ V) hx,
          hu t x hx])).exists
    obtain ⟨a, ha⟩ := key u hu
    obtain ⟨b, hb⟩ := key u⁻¹ (fun t x hx => by rw [map_inv, map_inv, hu t x hx])
    have e : a * b = 1 := inj V (by rw [map_mul, map_one, ha, hb]; exact u.mul_inv)
    exact ⟨⟨a, b, e, (mul_comm _ _).trans e⟩, Units.ext ha⟩
  have le : ∀ j : PUnit → M.ι, m ⁻¹ᵁ LB.wchart M (fun _ : PUnit => ψ) j ≤ LB.wchart M (fun _ : PUnit => m ≫ ψ) j :=
    fun j x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k
  have loc : ∀ j : PUnit → M.ι, ∃ v : Γ(Y, LB.wchart M (fun _ : PUnit => ψ) j)ˣ,
      pullU m _ v = res (le j) (σ.s j) := by
    intro j
    refine descU _ _ fun t x hx => ?_
    have hx' : τ t x ∈ m ⁻¹ᵁ LB.wchart M (fun _ : PUnit => ψ) j :=
      (congrArg (fun q : Y' ⟶ Y => q x ∈ LB.wchart M (fun _ : PUnit => ψ) j) (hτ t)).mpr hx
    obtain ⟨J, hJ, e⟩ := exists_good M hM x (fun _ : PUnit => m ≫ ψ) j (fun a b _ => rfl)
      (fun k => Set.mem_iInter.1 (le j hx) k)
    have := inv t x J hJ
    rw [val_of σ _ x J j (fun k => by rw [Category.id_comp, ← Category.assoc, hτ]; exact e k),
      val_of σ _ x J j (fun k => by rw [Category.id_comp]; exact e k), Category.id_comp] at this
    exact (gm_res (τ t) x (le j) hx' _).trans (this.trans (gm_res (𝟙 Y') x (le j) hx _).symm)
  choose v hv using loc
  refine ⟨⟨v⟩, fun i j => injU _ (unit_ext fun x hx => ?_)⟩
  have hv' : ∀ j : PUnit → M.ι, m x ∈ LB.wchart M (fun _ : PUnit => ψ) j →
      gm (𝟙 Y' ≫ m) x _ (v j) = gm (𝟙 Y') x (LB.wchart M (fun _ : PUnit => m ≫ ψ) j) (σ.s j) := fun j hj =>
    (gm_pull (𝟙 Y') m x _ hj _).symm.trans ((congrArg (gm (𝟙 Y') x _) (hv j)).trans (gm_res (𝟙 Y') x (le j) hj _))
  have hx' : (𝟙 Y' ≫ m) x ∈ LB.wchart M (fun _ : PUnit => ψ) i ⊓ LB.wchart M (fun _ : PUnit => ψ) j := hx
  refine (gm_pull (𝟙 Y') m x _ hx _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m x _ hx _).symm)
  refine (gm_res _ x _ hx' _).trans ((hv' i hx.1).trans ((gen_trans hσ (𝟙 Y') x (le i hx.1) (le j hx.2)).trans
    (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_linComb M (fun _ : PUnit => ψ) (fun _ => 1) (𝟙 Y' ≫ m) x i j hx'.1 hx'.2).trans ?_)
      ((gm_res _ x _ hx' _).trans (hv' j hx.2)))))))
  simp only [trF, Category.assoc]

theorem invariantGenerator_descends_mulN :
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom → IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    ∀ (V : (G ⊗ Over.mk f).left.Opens) (a : Γ((G ⊗ Over.mk f).left, (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V)),
    (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ h : (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V ≤ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left ⁻¹ᵁ ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V), ((lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left.appLE _ _ h).hom a = a) →
    ∃! a' : Γ((G ⊗ Over.mk f).left, V), ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left.app V).hom a' = a) →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom → IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    ∀ (X : Scheme.{0}) (M : ReciprocityTheory.ChartRestriction.G.Semi.LB X), M.IsLB → ∀ (ψ : (G ⊗ Over.mk f).left ⟶ X)
      (σ : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb M (K := PUnit) (fun _ => (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ≫ ψ) (fun _ => 1))), σ.IsGen →
    (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ (Z : Scheme.{0}) (r : Z ⟶ (G ⊗ Over.mk f).left) (z : Z) (J : (Z ⟶ X) → M.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good M z J →
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ (r ≫ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) z J = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ r z J) → ∃ t : (M.pull ψ).Gen, t.IsGen) := by
  intro H S G _ _ K _ _ f N hN h₁ h₂ h₃ h₄ X M hM ψ σ hσ inv
  refine invariant_generator_descent (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left (T := {y : Over.mk f ⟶ G // y ^ N = 1})
    (fun y => (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y.1)) (snd G (Over.mk f))).left) (fun y => ?_)
    (fun V a ha => H S G K f N hN h₁ h₂ h₃ h₄ V a (fun y hy => ha ⟨y, hy⟩)) M hM ψ σ hσ
    (fun y z J hJ => inv y.1 y.2 _ (𝟙 _) z J hJ)
  rw [← Over.comp_left]
  congr 1
  ext1
  · rw [lift_whiskerRight, lift_fst, whiskerRight_fst, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id,
      Category.comp_id, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one, _root_.mul_one]
  · simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionSecondLawProduct
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BiextSym

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_gen_of_iso {X : Scheme.{0}} {L : LB X} {F : X ⟶ X} (h : LBIso L (L.pull F)) :
    ∃ s : LB.Gen (LB.LinComb L (K := Fin 2) ![F, 𝟙 X] ![1, -1]), s.IsGen := by
  obtain ⟨w, hw⟩ := h
  have hp := (isGen_iff w).1 hw
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L (K := Fin 2) ![F, 𝟙 X] j ≤ (L.pull F).U (fun _ => j 0) ⊓ L.U (j 1) :=
    fun j x hx => ⟨mem_pull.2 (Set.mem_iInter.1 hx 0), Set.mem_iInter.1 hx 1⟩
  refine ⟨⟨fun j => res (le j) (w.s (fun _ => j 0, j 1))⟩, fun j j' => unit_ext fun y hy => ?_⟩
  have a := hp _ (𝟙 X) y (j 0) (j' 0) (j 1) (j' 1) (mem_pull.1 (le j hy.1).1) (mem_pull.1 (le j' hy.2).1)
    (le j hy.1).2 (le j' hy.2).2
  refine ((gm_res _ y _ hy _).trans (gm_res (𝟙 X) y (le j) hy.1 _)).trans (a.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L _ _ (𝟙 X) y j j' hy.1 hy.2).trans ?_)
    ((gm_res _ y _ hy _).trans (gm_res (𝟙 X) y (le j') hy.2 _)))
  rw [Fin.prod_univ_two]
  show gm (𝟙 X ≫ F) y _ (L.g (j 0) (j' 0)) ^ (1 : ℤ) * gm (𝟙 X ≫ 𝟙 X) y _ (L.g (j 1) (j' 1)) ^ (-1 : ℤ) = _
  rw [_root_.zpow_neg, _root_.zpow_one, _root_.zpow_one, Category.id_comp (𝟙 X)]

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

omit [GrpObj A] [IsCommMonObj A] in
theorem prod_sym {T : Over S} (x y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ (A ⊗ A).left) → U) :
    ∏ i : Fin 2, h ((lift x y).left ≫ ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] i) ^ (![1, -1] i : ℤ) =
      h (lift y x).left * (h (lift x y).left)⁻¹ := by
  have e : lift x y ≫ lift (snd A A) (fst A A) = lift y x := by rw [comp_lift, lift_fst, lift_snd]
  rw [Fin.prod_univ_two]
  show h (lift x y ≫ lift (snd A A) (fst A A)).left ^ (1 : ℤ) * h ((lift x y).left ≫ 𝟙 _) ^ (-1 : ℤ) = _
  rw [e, Category.comp_id, _root_.zpow_neg, _root_.zpow_one, _root_.zpow_one]

theorem biextension_first_law_product {T : Over S} (x x' y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ (A ⊗ A).left) → U) :
    ∏ i, h ((lift x (lift x' y)).left ≫ law1φ A (x3 A 0) (x3 A 1) (x3 A 2) i) ^ lawε i =
      h (lift (x * x') y).left * (h (lift x y).left)⁻¹ * (h (lift x' y).left)⁻¹ := by
  have a₀ : lift x (lift x' y) ≫ x3 A 0 = x := by simp [x3]
  have a₁ : lift x (lift x' y) ≫ x3 A 1 = x' := by simp [x3]
  have a₂ : lift x (lift x' y) ≫ x3 A 2 = y := by simp [x3]
  have b : lift x (lift x' y) ≫ padd A (x3 A 0) (x3 A 1) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁])
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _
    (fun i => h ((lift x (lift x' y)).left ≫ law1φ A (x3 A 0) (x3 A 1) (x3 A 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift x (lift x' y) ≫ lift (padd A (x3 A 0) (x3 A 1)) (x3 A 2)).left ^ (1 : ℤ) *
    h (lift x (lift x' y) ≫ lift (x3 A 0) (x3 A 2)).left ^ (-1 : ℤ) *
    h (lift x (lift x' y) ≫ lift (x3 A 1) (x3 A 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, b, a₀, a₁, a₂]
  simp only [_root_.zpow_neg, _root_.zpow_one]

theorem biextension_second_law_product {T : Over S} (x y y' : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ (A ⊗ A).left) → U) :
    ∏ i, h ((lift x (lift y y')).left ≫ law2φ A (x3 A 0) (x3 A 1) (x3 A 2) i) ^ lawε i =
      h (lift x (y * y')).left * (h (lift x y).left)⁻¹ * (h (lift x y').left)⁻¹ := by
  have a₀ : lift x (lift y y') ≫ x3 A 0 = x := by simp [x3]
  have a₁ : lift x (lift y y') ≫ x3 A 1 = y := by simp [x3]
  have a₂ : lift x (lift y y') ≫ x3 A 2 = y' := by simp [x3]
  have b : lift x (lift y y') ≫ padd A (x3 A 1) (x3 A 2) = y * y' := (MonObj.comp_mul _ _ _).trans (by rw [a₁, a₂])
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _
    (fun i => h ((lift x (lift y y')).left ≫ law2φ A (x3 A 0) (x3 A 1) (x3 A 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift x (lift y y') ≫ lift (x3 A 0) (padd A (x3 A 1) (x3 A 2))).left ^ (1 : ℤ) *
    h (lift x (lift y y') ≫ lift (x3 A 0) (x3 A 1)).left ^ (-1 : ℤ) *
    h (lift x (lift y y') ≫ lift (x3 A 0) (x3 A 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, b, a₀, a₁, a₂]
  simp only [_root_.zpow_neg, _root_.zpow_one]

theorem exists_norm {P : LB (A ⊗ A).left} (hP : P.IsLB) (h : LBIso P (P.pull (lift (snd A A) (fst A A)).left)) :
    ∃ s : LB.Gen (LB.LinComb P (K := Fin 2) ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] ![1, -1]), s.IsGen ∧
      ∀ (T : Over S) (z : T.left) (J), Good P z J → val s (lift (1 : T ⟶ A) (1 : T ⟶ A)).left z J = 1 := by
  obtain ⟨t, ht⟩ := exists_gen_of_iso h
  obtain ⟨s, hs, hv⟩ := exists_gen hP (K' := Fin 2) (φ' := ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left])
    (ε' := ![1, -1]) (fun V _ k => by
      have p := prod_sym (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A) k
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _
        (c := ∏ i : Fin 2, k (![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] i) ^ (![1, -1] i : ℤ)) rfl
        (DVR.prod_neg _ _ p)) ?_
      rw [mul_inv_cancel, inv_one, _root_.mul_one])
    (LB.mulGen P _ _ _ _ t (LB.invGen P _ _ (LB.pullGen P _ _ t (lift (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨s, hs, fun T z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, ← Over.comp_left, comp_lift, MonObj.comp_one, mul_inv_cancel]

theorem val_pull₂ {X : Scheme.{0}} {P : LB X} {K : Type} [Fintype K] {B C : Over S} {φ : K → ((B ⊗ C).left ⟶ X)}
    {ε : K → ℤ} (u : LB.Gen (LB.LinComb P φ ε)) {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J} (hJ : Good P z J)
    (a : T ⟶ B) (b : T ⟶ C) :
    val (LB.pullGen P φ ε u (lift a b).left) ρ.left z J = val u (lift (ρ ≫ a) (ρ ≫ b)).left z J := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift]

theorem val_pull₃ {X : Scheme.{0}} {P : LB X} {K : Type} [Fintype K] {B C D : Over S}
    {φ : K → ((B ⊗ C ⊗ D).left ⟶ X)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb P φ ε)) {T T' : Over S} (ρ : T' ⟶ T)
    {z : T'.left} {J} (hJ : Good P z J) (a : T ⟶ B) (b : T ⟶ C) (c : T ⟶ D) :
    val (LB.pullGen P φ ε u (lift a (lift b c)).left) ρ.left z J =
      val u (lift (ρ ≫ a) (lift (ρ ≫ b) (ρ ≫ c))).left z J := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift, comp_lift]

theorem law_origin {P : LB (A ⊗ A).left} (β : IsBiext A P) {T : Over S} {z : T.left} {J} (hJ : Good P z J) :
    val β.law1 (lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (1 : T ⟶ A))).left z J =
      val β.law2 (lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (1 : T ⟶ A))).left z J := by
  let ρ := lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (1 : T ⟶ A)))
  have a₀ : ρ ≫ x4 A 0 = 1 := by simp [ρ, x4]
  have a₁ : ρ ≫ x4 A 1 = 1 := by simp [ρ, x4]
  have a₂ : ρ ≫ x4 A 2 = 1 := by simp [ρ, x4]
  have a₃ : ρ ≫ x4 A 3 = 1 := by simp [ρ, x4]
  have b₀ : ρ ≫ padd A (x4 A 0) (x4 A 1) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁, _root_.mul_one])
  have b₁ : ρ ≫ padd A (x4 A 2) (x4 A 3) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [a₂, a₃, _root_.mul_one])
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    (val_pull₃ β.law1 ρ hJ _ _ _) (val_pull₃ β.law2 ρ hJ _ _ _))) (val_pull₃ β.law2 ρ hJ _ _ _))).symm.trans
    ((val_corr hJ β.compat ρ.left).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_pull₃ β.law2 ρ hJ _ _ _) (val_pull₃ β.law1 ρ hJ _ _ _))) (val_pull₃ β.law1 ρ hJ _ _ _))))
  rw [b₀, b₁, a₀, a₁, a₂, a₃, mul_comm (val β.law2 _ z J) (val β.law1 _ z J)] at e
  exact (mul_left_cancel e).symm

theorem main :
  (ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme A →
    ∀ (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (A ⊗ A).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext A P),
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso P (P.pull (lift (snd A A) (fst A A)).left) →
    ∃ s : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb P (K := Fin 2) ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] ![1, -1]), s.IsGen ∧ ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ (A ⊗ A).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J → ∀ x x' y : T ⟶ A,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift y x).left z J = 1 ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift x (lift x' y)).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift (x * x') y).left z J =
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x' y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift y (lift x x')).left z J) := by
  intro hG S A _ _ hA P β hs
  obtain ⟨s, hs, h1⟩ := exists_norm β.isLB hs
  refine ⟨s, hs, fun T z J hJ x x' y => ⟨?_, ?_⟩⟩
  · have ev : ∀ {T' : Over S} (σ : T' ⟶ A ⊗ A) {z : T'.left} {J}, Good P z J →
        val (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ s (lift (fst A A) (snd A A)).left)
          (LB.pullGen P _ _ s (lift (snd A A) (fst A A)).left)) σ.left z J =
          val s (lift (σ ≫ fst A A) (σ ≫ snd A A)).left z J * val s (lift (σ ≫ snd A A) (σ ≫ fst A A)).left z J :=
      fun σ z J hJ => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull₂ s σ hJ _ _) (val_pull₂ s σ hJ _ _))
    let e : 𝟙_ (Over S) ⟶ A ⊗ A := lift 1 1
    have sj : Function.Surjective ((snd A A).left ≫ A.hom).appTop.hom := surj_comp (surj_snd hG hA _) (hG _ _ hA).2
    have he : e.left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by rw [Over.w]; exact Over.w e
    have key := gen_unique' β.isLB (u' := LB.oneGen P (Y := (A ⊗ A).left)) (fun V _ k => by
        refine (Fintype.prod_empty _).trans (Eq.symm ?_)
        refine (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_sym (fst A A) (snd A A) k)
          (prod_sym (snd A A) (fst A A) k)).trans ?_
        rw [_root_.mul_assoc, inv_mul_cancel_left, mul_inv_cancel]) _ e.left he sj
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hs _) (DVR.pullGen_isGen _ _ _ _ hs _))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
      (fun y I hI => by
        refine (ev e hI).trans (Eq.trans ?_ (val_one _).symm)
        rw [lift_fst, lift_snd, h1 _ y I hI, _root_.mul_one]) _ (lift x y).left z J hJ
    have := (ev (lift x y) hJ).symm.trans (key.trans (val_one _))
    rwa [lift_fst, lift_snd] at this
  · let p₀ := x3 A 0
    let p₁ := x3 A 1
    let p₂ := x3 A 2
    have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 A) {z : T'.left} {J}, Good P z J →
        val (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ β.law1 (lift p₀ (lift p₁ p₂)).left)
          (LB.pullGen P _ _ s (lift (p₀ * p₁) p₂).left)) σ.left z J =
          val β.law1 (lift (σ ≫ p₀) (lift (σ ≫ p₁) (σ ≫ p₂))).left z J * val s (lift (σ ≫ (p₀ * p₁)) (σ ≫ p₂)).left z J ∧
        val (LB.mulGen P _ _ _ _ (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ s (lift p₀ p₂).left)
          (LB.pullGen P _ _ s (lift p₁ p₂).left)) (LB.pullGen P _ _ β.law2 (lift p₂ (lift p₀ p₁)).left)) σ.left z J =
          val s (lift (σ ≫ p₀) (σ ≫ p₂)).left z J * val s (lift (σ ≫ p₁) (σ ≫ p₂)).left z J *
            val β.law2 (lift (σ ≫ p₂) (lift (σ ≫ p₀) (σ ≫ p₁))).left z J := fun σ z J hJ =>
      ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull₃ β.law1 σ hJ _ _ _) (val_pull₂ s σ hJ _ _)),
        (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) (val_pull₂ s σ hJ _ _) (val_pull₂ s σ hJ _ _))) (val_pull₃ β.law2 σ hJ _ _ _))⟩
    let e : 𝟙_ (Over S) ⟶ G3 A := lift 1 (lift 1 1)
    have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
    have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
    have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
    have sj : Function.Surjective ((snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom).appTop.hom :=
      surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)
    have he : e.left ≫ (snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by
      rw [Over.w, Over.w]; exact Over.w e
    let ρ : T ⟶ G3 A := lift x (lift x' y)
    have r₀ : ρ ≫ p₀ = x := by simp [ρ, p₀, x3]
    have r₁ : ρ ≫ p₁ = x' := by simp [ρ, p₁, x3]
    have r₂ : ρ ≫ p₂ = y := by simp [ρ, p₂, x3]
    have o₁ : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
    have s₁ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
    have := (ev ρ hJ).1.symm.trans (Eq.trans (gen_unique' β.isLB (fun V _ k => by
        refine (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := ULift.{0} (Fin 3)) (U := V) _
          (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_sym p₀ p₂ k) (prod_sym p₁ p₂ k))
          (biextension_second_law_product p₂ p₀ p₁ k)).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := ULift.{0} (Fin 3)) (K' := Fin 2) (U := V) _
            (biextension_first_law_product p₀ p₁ p₂ k) (prod_sym (p₀ * p₁) p₂ k)).symm)
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel) _ e.left he sj
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ β.isGen1 _) (DVR.pullGen_isGen _ _ _ _ hs _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.pullGen_isGen _ _ _ _ hs _) (DVR.pullGen_isGen _ _ _ _ hs _)) (DVR.pullGen_isGen _ _ _ _ β.isGen2 _))
      (fun y I hI => by
        refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
        rw [o₁, e₀, e₁, e₂, h1 _ y I hI, law_origin β hI, _root_.mul_one, _root_.one_mul, _root_.one_mul])
      _ ρ.left z J hJ) (ev ρ hJ).2)
    rwa [s₁, r₀, r₁, r₂] at this

end GlobalTheory.BiextSym
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PairingNondegenerateIntegralTorsion
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section Transfer
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : LB (G ⊗ G).left} (β : IsBiext G P)

private theorem pfTie_prod1 {T : Over S} (x x' y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ k, h ((CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y)).left ≫ law1φ G (x3 G 0) (x3 G 1) (x3 G 2) k) ^ lawε k =
      h (CartesianMonoidalCategory.lift (x * x') y).left * (h (CartesianMonoidalCategory.lift x y).left)⁻¹ * (h (CartesianMonoidalCategory.lift x' y).left)⁻¹ := by
  have e₀ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (padd G (x3 G 0) (x3 G 1)) (x3 G 2) = CartesianMonoidalCategory.lift (x * x') y := by
    rw [comp_lift]
    congr 1
    · exact (MonObj.comp_mul _ _ _).trans (by simp [x3])
    · simp [x3]
  have e₁ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 2) = CartesianMonoidalCategory.lift x y := by rw [comp_lift]; simp [x3]
  have e₂ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (x3 G 1) (x3 G 2) = CartesianMonoidalCategory.lift x' y := by rw [comp_lift]; simp [x3]
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _
    (fun k => h ((CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y)).left ≫ law1φ G (x3 G 0) (x3 G 1) (x3 G 2) ⟨k⟩) ^ lawε ⟨k⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (padd G (x3 G 0) (x3 G 1)) (x3 G 2)).left ^ (1 : ℤ) *
    h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 2)).left ^ (-1 : ℤ) *
    h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (x3 G 1) (x3 G 2)).left ^ (-1 : ℤ) = _
  rw [e₀, e₁, e₂]
  simp only [_root_.zpow_neg, zpow_one]

private theorem pfTie_prod2 {T : Over S} (x y y' : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ k, h ((CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y')).left ≫ law2φ G (x3 G 0) (x3 G 1) (x3 G 2) k) ^ lawε k =
      h (CartesianMonoidalCategory.lift x (y * y')).left * (h (CartesianMonoidalCategory.lift x y).left)⁻¹ * (h (CartesianMonoidalCategory.lift x y').left)⁻¹ := by
  have e₀ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (padd G (x3 G 1) (x3 G 2)) = CartesianMonoidalCategory.lift x (y * y') := by
    rw [comp_lift]
    congr 1
    · simp [x3]
    · exact (MonObj.comp_mul _ _ _).trans (by simp [x3])
  have e₁ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 1) = CartesianMonoidalCategory.lift x y := by rw [comp_lift]; simp [x3]
  have e₂ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 2) = CartesianMonoidalCategory.lift x y' := by rw [comp_lift]; simp [x3]
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _
    (fun k => h ((CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y')).left ≫ law2φ G (x3 G 0) (x3 G 1) (x3 G 2) ⟨k⟩) ^ lawε ⟨k⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (padd G (x3 G 1) (x3 G 2))).left ^ (1 : ℤ) *
    h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 1)).left ^ (-1 : ℤ) *
    h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 2)).left ^ (-1 : ℤ) = _
  rw [e₀, e₁, e₂]
  simp only [_root_.zpow_neg, zpow_one]

private theorem pfTie_gen {T : Over S} (x y : T ⟶ G) (n : ℕ) :
    ∃ t : LB.Gen (LB.LinComb P (K := Fin 4) ![(CartesianMonoidalCategory.lift (x ^ n) y).left, (CartesianMonoidalCategory.lift (1 : T ⟶ G) y).left, (CartesianMonoidalCategory.lift x (y ^ n)).left,
        (CartesianMonoidalCategory.lift x (1 : T ⟶ G)).left] ![1, -1, -1, 1]), t.IsGen ∧
      ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good P z J →
        val t ρ.left z J = (∏ k ∈ Finset.range n, val β.law1 (CartesianMonoidalCategory.lift ((ρ ≫ x) ^ k) (CartesianMonoidalCategory.lift (ρ ≫ x) (ρ ≫ y))).left z J) *
          (∏ k ∈ Finset.range n, val β.law2 (CartesianMonoidalCategory.lift (ρ ≫ x) (CartesianMonoidalCategory.lift ((ρ ≫ y) ^ k) (ρ ≫ y))).left z J)⁻¹ := by
  induction n with
  | zero =>
    obtain ⟨t, ht, hv⟩ := exists_gen β.isLB (φ' := ![(CartesianMonoidalCategory.lift (x ^ 0) y).left, (CartesianMonoidalCategory.lift (1 : T ⟶ G) y).left, (CartesianMonoidalCategory.lift x (y ^ 0)).left,
        (CartesianMonoidalCategory.lift x (1 : T ⟶ G)).left]) (ε' := ![1, -1, -1, 1])
      (fun U _ h => by simp [Fin.prod_univ_succ]) (LB.oneGen P (Y := T.left))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    exact ⟨t, ht, fun T' ρ z J hJ => ((hv _ _ z J hJ).trans (val_one _)).trans (by simp)⟩
  | succ n ih =>
    obtain ⟨t, ht, hv⟩ := ih
    obtain ⟨t', ht', hv'⟩ := exists_gen β.isLB (φ' := ![(CartesianMonoidalCategory.lift (x ^ (n + 1)) y).left, (CartesianMonoidalCategory.lift (1 : T ⟶ G) y).left,
        (CartesianMonoidalCategory.lift x (y ^ (n + 1))).left, (CartesianMonoidalCategory.lift x (1 : T ⟶ G)).left]) (ε' := ![1, -1, -1, 1]) (fun U _ h => by
        refine (DVR.prod_sum₂ (K := Fin 4) (K' := ULift.{0} (Fin 3) ⊕ ULift.{0} (Fin 3)) (U := U) _
          (c := ∏ i, h ((![(CartesianMonoidalCategory.lift (x ^ n) y).left, (CartesianMonoidalCategory.lift (1 : T ⟶ G) y).left, (CartesianMonoidalCategory.lift x (y ^ n)).left,
            (CartesianMonoidalCategory.lift x (1 : T ⟶ G)).left] : Fin 4 → _) i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i) rfl
          (DVR.prod_sum₂ (K := ULift.{0} (Fin 3)) (K' := ULift.{0} (Fin 3)) (U := U) _ (pfTie_prod1 (x ^ n) x y h)
            (DVR.prod_neg _ _ (pfTie_prod2 x (y ^ n) y h)))).trans ?_
        rw [pow_succ x, pow_succ y]
        apply Additive.ofMul.injective
        simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv]
        abel)
      (LB.mulGen P _ _ _ _ t (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ β.law1 (CartesianMonoidalCategory.lift (x ^ n) (CartesianMonoidalCategory.lift x y)).left)
        (LB.invGen P _ _ (LB.pullGen P _ _ β.law2 (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift (y ^ n) y)).left))))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ β.isGen1 _)
        (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ β.isGen2 _))))
    refine ⟨t', ht', fun T' ρ z J hJ => ?_⟩
    have p₁ : ρ ≫ (x ^ n) = (ρ ≫ x) ^ n := map_pow (preHom ρ) _ _
    have p₂ : ρ ≫ (y ^ n) = (ρ ≫ y) ^ n := map_pow (preHom ρ) _ _
    have q₁ : ρ.left ≫ (CartesianMonoidalCategory.lift (x ^ n) (CartesianMonoidalCategory.lift x y)).left = (CartesianMonoidalCategory.lift ((ρ ≫ x) ^ n) (CartesianMonoidalCategory.lift (ρ ≫ x) (ρ ≫ y))).left := by
      rw [← Over.comp_left, comp_lift, comp_lift, p₁]
    have q₂ : ρ.left ≫ (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift (y ^ n) y)).left = (CartesianMonoidalCategory.lift (ρ ≫ x) (CartesianMonoidalCategory.lift ((ρ ≫ y) ^ n) (ρ ≫ y))).left := by
      rw [← Over.comp_left, comp_lift, comp_lift, p₂]
    refine ((hv' _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv T' ρ z J hJ)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans (congrArg (val β.law1 · z J) q₁))
        ((val_inv _ _).trans (congrArg (·⁻¹) ((val_pull hJ _ _ _).trans (congrArg (val β.law2 · z J) q₂))))))))).trans ?_
    rw [Finset.prod_range_succ, Finset.prod_range_succ, mul_inv, _root_.mul_mul_mul_comm]

private theorem pfTie_unit {T : Over S} (x y : T ⟶ G) (n : ℕ) (hx : x ^ n = 1) (hy : y ^ n = 1) :
    ∃ a : Γ(T.left, ⊤)ˣ, ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good P z J →
        gm ρ.left z ⊤ a = (∏ k ∈ Finset.range n, val β.law1 (CartesianMonoidalCategory.lift ((ρ ≫ x) ^ k) (CartesianMonoidalCategory.lift (ρ ≫ x) (ρ ≫ y))).left z J) *
          (∏ k ∈ Finset.range n, val β.law2 (CartesianMonoidalCategory.lift (ρ ≫ x) (CartesianMonoidalCategory.lift ((ρ ≫ y) ^ k) (ρ ≫ y))).left z J)⁻¹ := by
  obtain ⟨u, hu, hw⟩ := pfTie_gen β x y n
  obtain ⟨t, -, hv⟩ := exists_gen β.isLB (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine Eq.trans ?_ (Fintype.prod_empty _).symm
      rw [hx, hy]
      simp [Fin.prod_univ_succ]) u hu
  have le : (⊤ : T.left.Opens) ≤ LB.wchart P (PEmpty.elim : PEmpty → (T.left ⟶ (G ⊗ G).left)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun T' ρ z J hJ => ?_⟩
  rw [← hw T' ρ z J hJ, ← hv _ _ z J hJ, val_of t ρ.left z J PEmpty.elim (fun k => k.elim)]
  exact gm_res ρ.left z le trivial _

private theorem pfTie_local (R : Type) [CommRing R] [IsLocalRing R] (a : Γ(Spec (CommRingCat.of R), ⊤)ˣ)
    (h : gm (𝟙 (Spec (CommRingCat.of R))) (IsLocalRing.closedPoint R) ⊤ a = 1) : a = 1 := by
  apply Units.ext
  have e := congrArg (fun u => (stalkClosedPointIso (CommRingCat.of R)).hom.hom (Units.val u)) h
  have g := congrArg (fun q => q.hom a.val) (germ_stalkClosedPointIso_hom (CommRingCat.of R))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at g
  have e' : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a.val = 1 :=
    g.symm.trans ((congrArg (stalkClosedPointIso (CommRingCat.of R)).hom.hom (gm_val (𝟙 _) _ ⊤ trivial a)).symm.trans
      (e.trans (map_one _)))
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective (e'.trans (map_one _).symm)

end Transfer


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem pairing_nondegenerate_integral_torsion :
  (∀ {R₀ : Type} [CommRing R₀] (B : BX R₀) (b : ∀ R x y, B.P R x y) (t₁ t₂ : ∀ R : LAlg R₀, B.G R → B.G R → B.G R → (R : Type)ˣ),
    (∀ R x x' y, B.add1 (b R x y) (b R x' y) = B.smul (t₁ R x x' y) (b R (x + x') y)) →
    (∀ R x y y', B.add2 (b R x y) (b R x y') = B.smul (t₂ R x y y') (b R x (y + y'))) →
    (∀ R (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ), B.IsPairing (N + 1) x y z ↔ (N + 1) • x = 0 ∧ (N + 1) • y = 0 ∧
      z = (t₁ R 0 0 y * ∏ k ∈ Finset.range N, t₁ R ((k + 1) • x) x y) / (t₂ R x 0 0 * ∏ k ∈ Finset.range N, t₂ R x ((k + 1) • y) y)) ∧
    ∀ (O : LAlg R₀) (a a' : OEnd B O) (u : ∀ {R : LAlg R₀}, LHom O R → B.G R → B.G R → (R : Type)ˣ),
      (∀ {R : LAlg R₀} (s : LHom O R) x x' y, u s (x + x') y * t₁ R x x' (a'.f s y) = t₁ R (a.f s x) (a.f s x') y * (u s x y * u s x' y)) →
      (∀ {R : LAlg R₀} (s : LHom O R) x y y', u s x (y + y') * t₂ R x (a'.f s y) (a'.f s y') = t₂ R (a.f s x) y y' * (u s x y * u s x y')) →
      ∃ A : OAdj B O, A.a = a ∧ A.ab = a') →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P)
    (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom →
    IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    (∀ x : Over.mk f ⟶ G, (∃ t : (P.pull (lift (snd G (Over.mk f) ≫ x) (fst G (Over.mk f))).left).Gen, t.IsGen) → x = 1) →
    ∀ x : Over.mk f ⟶ G, x ^ N = 1 → (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ (z : (Over.mk f).left) (J : ((Over.mk f).left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
      ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (x ^ k) (lift x y)).left z J = ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift (y ^ k) y)).left z J) → x = 1) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) [Algebra (O : Type) C] [Algebra R₀ C] [IsScalarTower R₀ (O : Type) C] (p : ℕ), v.Integers (O : Type) → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Surjective ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : sp (R₀ := R₀) (O : Type) ⟶ G, ∃ y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = x) ∧
    ∀ z : sp (R₀ := R₀) C ⟶ G, z ^ p = 1 → ∃! y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = 1 ∧ spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ y = z) →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (T : Over S) (z : T.left)
    (J : (T.left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J → ∀ t₁ t₂ : (T ⟶ G) → (T ⟶ G) → (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
    (∀ x x' y, t₁ x x' y = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift x (lift x' y)).left z J) → (∀ x y y', t₂ x y y' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift y y')).left z J) →
    (∀ x x' x'' y, t₁ (x * x') x'' y * t₁ x x' y = t₁ x (x' * x'') y * t₁ x' x'' y) ∧ (∀ x x' y, t₁ x x' y = t₁ x' x y) ∧
    (∀ x y y' y'', t₂ x (y * y') y'' * t₂ x y y' = t₂ x y (y' * y'') * t₂ x y' y'') ∧ (∀ x y y', t₂ x y y' = t₂ x y' y) ∧
    (∀ x x' y y', t₁ x x' (y * y') * t₂ x y y' * t₂ x' y y' = t₂ (x * x') y y' * t₁ x x' y * t₁ x x' y')) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)) (b : ∀ R x y, B.P R x y)
    (J : ∀ R : LAlg R₀, ((sp (R₀ := R₀) (R : Type)).left ⟶ (G ⊗ G).left) → P.1),
    (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    (∀ R : LAlg R₀, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P (Z := (sp (R₀ := R₀) (R : Type)).left) (IsLocalRing.closedPoint (R : Type)) (J R)) →
    (∀ (R : LAlg R₀) x x' y, B.add1 (b R x y) (b R x' y) =
      B.smul (Units.map (stalkClosedPointIso (CommRingCat.of (R : Type))).hom.hom.toMonoidHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (e R x) (lift (e R x') (e R y))).left (IsLocalRing.closedPoint (R : Type)) (J R))) (b R (x + x') y)) →
    (∀ (R : LAlg R₀) x y y', B.add2 (b R x y) (b R x y') =
      B.smul (Units.map (stalkClosedPointIso (CommRingCat.of (R : Type))).hom.hom.toMonoidHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift (e R x) (lift (e R y) (e R y'))).left (IsLocalRing.closedPoint (R : Type)) (J R))) (b R x (y + y'))) →
    ∀ (O : LAlg R₀) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) [Algebra (O : Type) C] [Algebra R₀ C] [IsScalarTower R₀ (O : Type) C] (p : ℕ), p ≠ 0 → v.Integers (O : Type) → Smooth G.hom →
    IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left → Surjective ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : sp (R₀ := R₀) C ⟶ G, (∃ t : (P.pull (lift (snd G (sp (R₀ := R₀) C) ≫ x) (fst G (sp (R₀ := R₀) C))).left).Gen, t.IsGen) → x = 1) →
    ∀ x : B.G O, p • x = 0 → (∀ y : B.G O, p • y = 0 → B.IsPairing p x y 1) → x = 0) := by
  intro FRM PFF TORS BIV R₀ _ G _ _ P β B e b J hb hadd _ hJ h1 h2 O C _ _ _ v _ _ _ p hp hv hsm hfin hfl hsurj hnd x hx H
  obtain ⟨N, rfl⟩ : ∃ N, p = N + 1 := Nat.exists_eq_succ_of_ne_zero hp
  have e0 : e O 0 = 1 := by
    have := hadd O 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have en : ∀ (k : ℕ) (w : B.G O), e O (k • w) = e O w ^ k := fun k w => by
    induction k with
    | zero => rw [zero_nsmul, pow_zero, e0]
    | succ k ih => rw [succ_nsmul, hadd, ih, pow_succ]
  obtain ⟨j, hj⟩ : ∃ j : sp (R₀ := R₀) C ⟶ sp (R₀ := R₀) (O : Type), j = spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) :=
    ⟨_, rfl⟩
  have T := (TORS G O C v (N + 1) hv hfin hsurj).2
  rw [← hj] at T
  have hxp : e O x ^ (N + 1) = 1 := by rw [← en, hx, e0]
  have j1 : j ≫ (1 : sp (R₀ := R₀) (O : Type) ⟶ G) = 1 := map_one (preHom j)
  have key : j ≫ e O x = 1 := by
    refine PFF _ G P β C (Spec.map (CommRingCat.ofHom (algebraMap R₀ C))) (N + 1) (Nat.cast_ne_zero.2 hp) hsm hfin hfl
      hsurj hnd (j ≫ e O x) ((map_pow (preHom j) _ _).symm.trans ((congrArg (j ≫ ·) hxp).trans j1))
      (fun y hy z Jc hJc => ?_)
    obtain ⟨y₀, ⟨hy₀, rfl⟩, -⟩ := T y hy
    obtain ⟨y', rfl⟩ := (hb O).2 y₀
    have hy' : (N + 1) • y' = 0 := (hb O).1 (by rw [en, hy₀, e0])
    have F := (((FRM B b _ _ h1 h2).1 O N x y' 1).1 (H y' hy')).2.2
    obtain ⟨a₁, -, a₂, -, -⟩ := BIV _ G P β (sp (R₀ := R₀) (O : Type)) (IsLocalRing.closedPoint (O : Type)) (J O) (hJ O)
      _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    have b₁ := a₁ 1 1 (e O x) (e O y')
    have b₂ := a₂ (e O x) 1 1 (e O y')
    simp only [_root_.one_mul] at b₁ b₂
    have c₁ := mul_left_cancel b₁
    have c₂ := mul_left_cancel b₂
    obtain ⟨a, ha⟩ := pfTie_unit β (e O x) (e O y') (N + 1) hxp hy₀
    have a1 : a = 1 := by
      apply pfTie_local (O : Type) a
      have g := ha _ (𝟙 _) (IsLocalRing.closedPoint (O : Type)) (J O) (hJ O)
      refine Eq.trans g ?_
      simp only [Category.id_comp]
      rw [Finset.prod_range_succ', Finset.prod_range_succ', pow_zero, pow_zero, ← c₁, ← c₂, mul_inv_eq_one]
      simp only [en, e0] at F
      rw [← map_prod, ← map_prod, ← map_mul, ← map_mul, eq_comm, div_eq_one] at F
      have inj := Units.map_injective (f := (stalkClosedPointIso (CommRingCat.of (O : Type))).hom.hom.toMonoidHom)
        (stalkClosedPointIso (CommRingCat.of (O : Type))).commRingCatIsoToRingEquiv.injective F
      exact (mul_comm _ _).trans (inj.trans (mul_comm _ _))
    have g := ha _ j z Jc hJc
    rw [a1, map_one, eq_comm, mul_inv_eq_one] at g
    exact g
  obtain ⟨w, -, hw⟩ := T 1 (one_pow _)
  exact (hb O).1 (((hw _ ⟨hxp, key⟩).trans (hw 1 ⟨one_pow _, j1⟩).symm).trans e0.symm)

end GlobalTheory
end
