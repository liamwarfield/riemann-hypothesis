module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMatrixBasisAllPlacesTorsionDet
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAbelianFibreIsoOfMatchedTorsionTheta
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTableAlgClosedCompleteSingleValued
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TraitSectionBasisDescendsFiniteDvrExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarizedAbelianValueTableMapsUnderBaseChange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisAtTraitVsGenericBasis
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTableLatticeIntegralFamilies

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteNormalExtContainingAlgebraicElements
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteNormalExtContainingAlgebraicElements
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

namespace GlobalTheory.OneBasis

theorem exists_extend_of_isAlgebraic {A B F : Type} [Field A] [Field B] [Field F] [IsAlgClosed F] [Algebra A B]
    [Algebra.IsAlgebraic A B] (g : A →+* F) : ∃ σ : B →+* F, ∀ x, σ (algebraMap A B x) = g x := by
  letI : Algebra A F := g.toAlgebra
  let σ : B →ₐ[A] F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨(σ : B →+* F), fun x => σ.commutes x⟩

theorem exists_finite_normal_containing : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [CharZero R₁], IsIntegrallyClosed R₁ → ∀ (I : Type) [Finite I] (Φ : I → AlgebraicClosure (FractionRing R₁)), ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R₁ →+* R₂) (h' : FractionRing R₁ →+* FractionRing R₂) (j : FractionRing R₂ →+* AlgebraicClosure (FractionRing R₁)) (Φ₂ : I → FractionRing R₂), Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧ (∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) ∧ (∀ x, j (h' x) = algebraMap (FractionRing R₁) _ x) ∧ (∀ i, j (Φ₂ i) = Φ i) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (ga : FractionRing R₂ →+* F), ∃ σ : AlgebraicClosure (FractionRing R₁) →+* F, ∀ x, σ (j x) = ga x := by
  intro R₁ _ _ _ _ hIC I _ Φ
  let K := FractionRing R₁
  let L := AlgebraicClosure K
  let K₂ : IntermediateField K L := IntermediateField.adjoin K (Set.range Φ)
  haveI : Finite (Set.range Φ) := (Set.finite_range Φ).to_subtype
  haveI : FiniteDimensional K K₂ :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing R₁
  haveI : Algebra.IsSeparable K K₂ := inferInstance
  let R₂ := integralClosure R₁ K₂
  haveI : IsFractionRing R₂ K₂ := IsIntegralClosure.isFractionRing_of_finite_extension R₁ K K₂ R₂
  haveI hfin : Module.Finite R₁ R₂ := IsIntegralClosure.finite R₁ K K₂ R₂
  let e : FractionRing R₂ ≃ₐ[R₂] K₂ := FractionRing.algEquiv R₂ K₂
  have hinj : Function.Injective (algebraMap R₁ K₂) := by
    rw [IsScalarTower.algebraMap_eq R₁ K K₂]
    exact (algebraMap K K₂).injective.comp (IsFractionRing.injective R₁ K)
  refine ⟨R₂, inferInstance, inferInstance, algebraMap R₁ R₂,
    (e.symm : K₂ →+* FractionRing R₂).comp (algebraMap K K₂),
    (algebraMap K₂ L).comp (e : FractionRing R₂ →+* K₂),
    fun i => e.symm ⟨Φ i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    apply hinj
    rw [IsScalarTower.algebraMap_apply R₁ R₂ K₂ a, IsScalarTower.algebraMap_apply R₁ R₂ K₂ b, hab]
  · exact RingHom.finite_algebraMap.mpr hfin
  · exact integralClosure.isIntegrallyClosedOfFiniteExtension K
  · intro r
    change e.symm (algebraMap K K₂ (algebraMap R₁ K r)) = _
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R₁ R₂ K₂, AlgEquiv.commutes]
  · intro x
    change algebraMap K₂ L (e (e.symm (algebraMap K K₂ x))) = _
    rw [e.apply_symm_apply, ← IsScalarTower.algebraMap_apply]
  · intro i
    change algebraMap K₂ L (e (e.symm _)) = _
    rw [e.apply_symm_apply]; rfl
  · intro F _ _ ga
    haveI : Algebra.IsAlgebraic K₂ L := Algebra.IsAlgebraic.tower_top (K := K) K₂
    obtain ⟨σ, hσ⟩ := exists_extend_of_isAlgebraic (A := K₂) (B := L) (ga.comp (e.symm : K₂ →+* FractionRing R₂))
    refine ⟨σ, fun x => (hσ (e x)).trans ?_⟩
    exact congrArg ga (e.symm_apply_apply x)

end GlobalTheory.OneBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteNormalExtContainingAlgebraicElementsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_normal_ext_containing_algebraic_elements : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [CharZero R₁], IsIntegrallyClosed R₁ → ∀ (I : Type) [Finite I] (Φ : I → AlgebraicClosure (FractionRing R₁)), ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R₁ →+* R₂) (h' : FractionRing R₁ →+* FractionRing R₂) (j : FractionRing R₂ →+* AlgebraicClosure (FractionRing R₁)) (Φ₂ : I → FractionRing R₂), Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧ (∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) ∧ (∀ x, j (h' x) = algebraMap (FractionRing R₁) _ x) ∧ (∀ i, j (Φ₂ i) = Φ i) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (ga : FractionRing R₂ →+* F), ∃ σ : AlgebraicClosure (FractionRing R₁) →+* F, ∀ x, σ (j x) = ga x := by
  first | exact @GlobalTheory.OneBasis.exists_finite_normal_containing | exact GlobalTheory.OneBasis.exists_finite_normal_containing | (intros; apply GlobalTheory.OneBasis.exists_finite_normal_containing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ShortestRepresentativesFormSumDependsOnLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ShortestRepresentativesFormSumDependsOnLattice
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

namespace GlobalTheory.OneBasis.ShortSum

variable {X : Type} [AddCommGroup X]

abbrev mulSub (X : Type) [AddCommGroup X] (k : ℕ) : AddSubgroup X := (nsmulAddMonoidHom (α := X) k).range

theorem mk_eq_iff (k : ℕ) (a b : X) :
    (QuotientAddGroup.mk a : X ⧸ mulSub X k) = QuotientAddGroup.mk b ↔ ∃ z, b = a + k • z := by
  rw [QuotientAddGroup.eq]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have : k • z = -a + b := hz
    rw [this]; abel
  · rintro ⟨z, rfl⟩
    exact ⟨z, by simp⟩

theorem surj {k r mu : ℕ} {Q : X → ℤ} {cls : Fin r → X} (h : Adapted k Q cls mu) :
    Function.Surjective (fun i => (QuotientAddGroup.mk (cls i) : X ⧸ mulSub X k)) := by
  intro c
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨i, z, hz⟩ := h.2.2.1 a
  exact ⟨i, (mk_eq_iff k _ _).2 ⟨z, hz⟩⟩

theorem sum_comp {k r mu : ℕ} {Q : X → ℤ} {cls : Fin r → X} (h : Adapted k Q cls mu)
    [Fintype (X ⧸ mulSub X k)] (g : X ⧸ mulSub X k → ℤ) :
    ∑ i, g (QuotientAddGroup.mk (cls i)) = mu * ∑ c, g c := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun i => (QuotientAddGroup.mk (cls i) : X ⧸ mulSub X k)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨i₀, rfl⟩ := surj h c
  rw [Finset.sum_congr rfl (g := fun _ => g (QuotientAddGroup.mk (cls i₀)))
    (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [← h.2.2.2 i₀, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  refine Finset.filter_congr fun i _ => ⟨fun hi => ?_, fun hi => by simp only [hi]⟩
  exact h.2.1 i i₀ ((mk_eq_iff k _ _).1 hi.symm)

theorem val_eq {k r r' mu mu' : ℕ} {Q : X → ℤ} {cls : Fin r → X} {cls' : Fin r' → X} (h : Adapted k Q cls mu)
    (h' : Adapted k Q cls' mu') {i : Fin r} {i' : Fin r'}
    (e : (QuotientAddGroup.mk (cls i) : X ⧸ mulSub X k) = QuotientAddGroup.mk (cls' i')) :
    Q (cls i) = Q (cls' i') := by
  apply le_antisymm
  · obtain ⟨z, hz⟩ := (mk_eq_iff k _ _).1 e
    rw [hz]; exact h.1 i z
  · obtain ⟨z, hz⟩ := (mk_eq_iff k _ _).1 e.symm
    rw [hz]; exact h'.1 i' z

theorem sum_eq {k r mu mu' : ℕ} {Q : X → ℤ} {cls cls' : Fin r → X} (h : Adapted k Q cls mu)
    (h' : Adapted k Q cls' mu') : ∑ i, Q (cls i) = ∑ i, Q (cls' i) := by
  haveI : Finite (X ⧸ mulSub X k) := Finite.of_surjective _ (surj h)
  letI : Fintype (X ⧸ mulSub X k) := Fintype.ofFinite _
  have a := sum_comp h (fun _ => 1)
  have a' := sum_comp h' (fun _ => 1)
  have hm : (mu : ℤ) = mu' := by
    have hp : (∑ _c : X ⧸ mulSub X k, (1 : ℤ)) ≠ 0 := by simp
    exact mul_right_cancel₀ hp (a.symm.trans a')
  have b := sum_comp h (fun c => Q (cls (Function.surjInv (surj h) c)))
  have b' := sum_comp h' (fun c => Q (cls (Function.surjInv (surj h) c)))
  calc ∑ i, Q (cls i) = _ := Finset.sum_congr rfl fun i _ =>
        val_eq h h (Function.surjInv_eq (surj h) _).symm
    _ = _ := b
    _ = _ := by rw [hm]
    _ = _ := b'.symm
    _ = _ := Finset.sum_congr rfl fun i _ => val_eq h h' (Function.surjInv_eq (surj h) _)

theorem transport {X₀ : Type} [AddCommGroup X₀] {q₀ : X₀ → ℤ} {Q : X → ℤ} (e : X₀ ≃+ X) {w : ℕ} (hw : 0 < w)
    (hQ : ∀ y, Q (e y) = w * q₀ y) {k r mu : ℕ} {cls : Fin r → X} (h : Adapted k Q cls mu) :
    Adapted k q₀ (fun i => e.symm (cls i)) mu := by
  refine ⟨fun i z => ?_, fun i i' ⟨z, hz⟩ => ?_, fun α => ?_, fun i₀ => ?_⟩
  · have h1 := h.1 i (e z)
    have h2 := hQ (e.symm (cls i))
    have h3 := hQ (e.symm (cls i) + k • z)
    rw [map_add (f := _), map_nsmul] at h3
    rw [e.apply_symm_apply] at h2 h3
    rw [h2, h3] at h1
    exact le_of_mul_le_mul_left h1 (by exact_mod_cast hw)
  · have h1 := congrArg e hz
    simp only [map_add (f := _), map_nsmul, e.apply_symm_apply] at h1
    simp only [h.2.1 i i' ⟨_, h1⟩]
  · obtain ⟨i, z, hz⟩ := h.2.2.1 (e α)
    refine ⟨i, e.symm z, e.injective ?_⟩
    simp only [map_add (f := _), map_nsmul, e.apply_symm_apply]
    exact hz
  · rw [← h.2.2.2 i₀]
    simp only [e.symm.injective.eq_iff]

end GlobalTheory.OneBasis.ShortSum

namespace GlobalTheory.OneBasis

theorem sum_adapted_eq : ∀ (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (q₀ : X₀ → ℤ) (k r : ℕ), 1 ≤ k → (∀ y, 0 ≤ q₀ y) → ∃ d C : ℕ, 1 ≤ d ∧ ∀ (X : Type) [AddCommGroup X] (Q : X → ℤ) (e : X₀ ≃+ X) (w : ℕ), 0 < w → (∀ y, Q (e y) = w * q₀ y) → ∀ (cls : Fin r → X) (mu : ℕ), Adapted k Q cls mu → (d : ℤ) * ∑ i, Q (cls i) = C * w * k := by
  intro X₀ _ _ _ q₀ k r hk hq
  by_cases hex : ∃ (c₀ : Fin r → X₀) (m₀ : ℕ), Adapted k q₀ c₀ m₀
  · obtain ⟨c₀, m₀, h₀⟩ := hex
    refine ⟨k, (∑ i, q₀ (c₀ i)).toNat, hk, fun X _ Q e w hw hQ cls mu h => ?_⟩
    rw [Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => hq _),
      ShortSum.sum_eq h₀ (ShortSum.transport e hw hQ h)]
    have : ∑ i, Q (cls i) = w * ∑ i, q₀ (e.symm (cls i)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [← hQ, e.apply_symm_apply]
    rw [this]; ring
  · exact ⟨k, 0, hk, fun X _ Q e w hw hQ cls mu h => (hex ⟨_, _, ShortSum.transport e hw hQ h⟩).elim⟩

end GlobalTheory.OneBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ShortestRepresentativesFormSumDependsOnLatticeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortestRepresentatives_form_sum_depends_on_lattice : ∀ (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (q₀ : X₀ → ℤ) (k r : ℕ), 1 ≤ k → (∀ y, 0 ≤ q₀ y) → ∃ d C : ℕ, 1 ≤ d ∧ ∀ (X : Type) [AddCommGroup X] (Q : X → ℤ) (e : X₀ ≃+ X) (w : ℕ), 0 < w → (∀ y, Q (e y) = w * q₀ y) → ∀ (cls : Fin r → X) (mu : ℕ), Adapted k Q cls mu → (d : ℤ) * ∑ i, Q (cls i) = C * w * k := by
  first | exact @GlobalTheory.OneBasis.sum_adapted_eq | exact GlobalTheory.OneBasis.sum_adapted_eq | (intros; apply GlobalTheory.OneBasis.sum_adapted_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RigidifiedBundleTwoPullbacksCompare
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RigidifiedBundleTwoPullbacksCompare
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.Compare

theorem eSec_comm_of_pullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : eSec G' ≫ φ = f ≫ eSec G := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

theorem wVal_tri {X X' X'' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
    {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull (F' ≫ F))}
    (T : Tri w w' w'') (y : Y) {J J' J''} (hJ : Good L y J) (hJ' : Good L' y J') (hJ'' : Good L'' y J'')
    (a : Y ⟶ X'') : GlobalTheory.ConstFam.wVal w'' y J J'' a =
      GlobalTheory.ConstFam.wVal w y J J' (a ≫ F') * GlobalTheory.ConstFam.wVal w' y J' J'' a := by
  have := T Y a y (J (a ≫ F' ≫ F)) (J' (a ≫ F')) (J'' a) (hJ (a ≫ F' ≫ F)) (hJ' (a ≫ F')) (hJ'' a)
  simpa only [GlobalTheory.ConstFam.wVal, Category.assoc] using this

theorem rigPull_compare : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (ρ₀ : LB.Gen (L₀.pull (eSec G₀))), ∀ (S S' : Scheme.{0}) (x : S ⟶ Z) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → ∀ (φ : G.left ⟶ G₀.left) (φ' : G'.left ⟶ G₀.left) (w : LB.Iso L (L₀.pull φ)) (w' : LB.Iso L' (L₀.pull φ')) ρ ρ', RigPull G G₀ x φ w ρ ρ₀ → RigPull G' G₀ (f ≫ x) φ' w' ρ' ρ₀ → ∃ (ψ : G'.left ⟶ G.left) (ω : LB.Iso L' (L.pull ψ)), RigPull G' G f ψ ω ρ' ρ ∧ ∀ (k : ℕ) (T₀ : Over Z) (T : Over S) (T' : Over S') (p : T.left ⟶ T₀.left) (q : T'.left ⟶ T.left), p ≫ T₀.hom = T.hom ≫ x → q ≫ T.hom = T'.hom ≫ f → ∀ s₀ s s', Thru w k (T' := T) (T := T₀) p s₀ s → Thru w' k (T' := T') (T := T₀) (q ≫ p) s₀ s' → Thru ω k (T' := T') (T := T) q s s' := by
  intro Z G₀ _ L₀ hL₀ ρ₀ S S' x f G _ G' _ L L' hL hL' φ φ' w w' ρ ρ' ⟨gp, hw, hρ, hm⟩ ⟨gp', hw', hρ', hm'⟩
  obtain ⟨ψ, e₁, e₂⟩ : ∃ ψ : G'.left ⟶ G.left, ψ ≫ φ = φ' ∧ ψ ≫ G.hom = G'.hom ≫ f :=
    ⟨gp.1.lift φ' (G'.hom ≫ f) (by rw [gp'.1.w, Category.assoc]), gp.1.lift_fst _ _ _, gp.1.lift_snd _ _ _⟩
  subst e₁
  have gψ : IsGrpPullback G' G f ψ := gp.cancel gp' e₂
  have pw := (isGen_iff w).1 hw
  have pw' := (isGen_iff w').1 hw'
  obtain ⟨ω, T⟩ := exists_cancel hL₀ w w' pw pw' hL hL'
  refine ⟨ψ, ω, ⟨gψ, (isGen_iff ω).2 (T.pgen_cancel hL₀ pw pw'), hρ',
    T.pmaps_cancel hL₀ (fun _ => eSec_comm_of_pullback gψ) hm hm'⟩, ?_⟩
  intro k T₀ T₁ T' p q hp hq s₀ s s' H H' Y r' r h₁ h₂ z J J' hJ hJ'
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.ConstFam.exists_good' hL₀ z
  have hw₀ : (r ≫ (fst T₁ G).left ≫ p) ≫ T₀.hom = (r ≫ (snd T₁ G).left ≫ φ) ≫ G₀.hom := by
    simp only [Category.assoc]
    rw [hp, gp.1.w, ← Category.assoc (fst T₁ G).left, ← Category.assoc (snd T₁ G).left, Over.w, Over.w]
  obtain ⟨r₀, a₁, a₂⟩ : ∃ r₀ : Y ⟶ (T₀ ⊗ G₀).left, r₀ ≫ (fst T₀ G₀).left = r ≫ (fst T₁ G).left ≫ p ∧
      r₀ ≫ (snd T₀ G₀).left = r ≫ (snd T₁ G).left ≫ φ :=
    ⟨pullback.lift _ _ hw₀, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have b₁ := H Y r r₀ a₁ a₂ z J₀ J hJ₀ hJ
  have b₂ := H' Y r' r₀ (by rw [a₁, ← Category.assoc, h₁]; simp only [Category.assoc])
    (by rw [a₂, ← Category.assoc, h₂]; simp only [Category.assoc]) z J₀ J' hJ₀ hJ'
  rw [wVal_tri T z hJ₀ hJ hJ', Category.assoc, ← h₂, b₁, Units.val_mul, mul_pow, _root_.mul_assoc,
    ← Units.val_pow_eq_pow_val] at b₂
  exact (Units.mul_right_inj _).1 b₂

end GlobalTheory.OneBasis.Compare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RigidifiedBundleTwoPullbacksCompareStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidified_bundle_two_pullbacks_compare : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (ρ₀ : LB.Gen (L₀.pull (eSec G₀))), ∀ (S S' : Scheme.{0}) (x : S ⟶ Z) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → ∀ (φ : G.left ⟶ G₀.left) (φ' : G'.left ⟶ G₀.left) (w : LB.Iso L (L₀.pull φ)) (w' : LB.Iso L' (L₀.pull φ')) ρ ρ', RigPull G G₀ x φ w ρ ρ₀ → RigPull G' G₀ (f ≫ x) φ' w' ρ' ρ₀ → ∃ (ψ : G'.left ⟶ G.left) (ω : LB.Iso L' (L.pull ψ)), RigPull G' G f ψ ω ρ' ρ ∧ ∀ (k : ℕ) (T₀ : Over Z) (T : Over S) (T' : Over S') (p : T.left ⟶ T₀.left) (q : T'.left ⟶ T.left), p ≫ T₀.hom = T.hom ≫ x → q ≫ T.hom = T'.hom ≫ f → ∀ s₀ s s', Thru w k (T' := T) (T := T₀) p s₀ s → Thru w' k (T' := T') (T := T₀) (q ≫ p) s₀ s' → Thru ω k (T' := T') (T := T) q s s' := by
  first | exact @GlobalTheory.OneBasis.Compare.rigPull_compare | exact GlobalTheory.OneBasis.Compare.rigPull_compare | (intros; apply GlobalTheory.OneBasis.Compare.rigPull_compare <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPlaceCentredClosedPointDetectsUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPlaceCentredClosedPointDetectsUnits
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

namespace GlobalTheory.CentredPlace

theorem exists_extension {F K M : Type} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K] [Field M]
    [IsAlgClosed M] (L : IntermediateField F K) (f : L →+* M) : ∃ σ : K →+* M, ∀ x : L, σ x = f x := by
  letI := f.toAlgebra
  let σ : K →ₐ[L] M := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨σ.toRingHom, fun x => σ.commutes x⟩

theorem exists_mem_of_dvr {R₁ : Type} [CommRing R₁] [IsDomain R₁] [CharZero R₁]
    (P : Set (ValuationSubring (AlgebraicClosure (FractionRing R₁))))
    (hP : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (φ : R₁ →+* V)
      (gam : FractionRing R₁ →+* FractionRing V), (∀ r, gam (algebraMap R₁ _ r) = algebraMap V _ (φ r)) →
      ∀ σ : AlgebraicClosure (FractionRing R₁) →+* AlgebraicClosure (FractionRing V),
      (∀ x, σ (algebraMap (FractionRing R₁) _ x) = algebraMap (FractionRing V) _ (gam x)) →
      ∃ S ∈ P, ∀ x (y : FractionRing V), σ x = algebraMap (FractionRing V) _ y →
        (x ∈ S ↔ y ∈ Set.range (algebraMap V (FractionRing V))))
    (L : IntermediateField (FractionRing R₁) (AlgebraicClosure (FractionRing R₁)))
    (W : ValuationSubring L) [IsDiscreteValuationRing W] (hW : ∀ r : R₁, algebraMap R₁ L r ∈ W) :
    ∃ S ∈ P, ∀ x : L, x ∉ W → (x : AlgebraicClosure (FractionRing R₁)) ∉ S := by
  let V := AdicCompletion (maximalIdeal W) W
  have hj : Function.Injective (algebraMap W V) := algebraMap_adicCompletion_injective_of_dvr W
  let j : W →+* FractionRing V := (algebraMap V (FractionRing V)).comp (algebraMap W V)
  have hj' : Function.Injective j := (IsFractionRing.injective V (FractionRing V)).comp hj
  let f : L →+* FractionRing V := IsFractionRing.lift (K := L) hj'
  have hf : ∀ w : W, f (w : L) = j w := fun w => IsFractionRing.lift_algebraMap hj' w
  let φ : R₁ →+* V := (algebraMap W V).comp ((algebraMap R₁ L).codRestrict W hW)
  have hinj : Function.Injective (algebraMap R₁ L) := by
    rw [IsScalarTower.algebraMap_eq R₁ (FractionRing R₁) L]
    exact (algebraMap (FractionRing R₁) L).injective.comp (IsFractionRing.injective R₁ _)
  have hφ : Function.Injective φ := hj.comp fun a b hab => hinj (congrArg Subtype.val hab)
  have hV : CDvr V := ⟨inferInstance, inferInstance, charZero_of_injective_ringHom hφ⟩
  obtain ⟨σ, hσ⟩ := exists_extension L
    ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp f)
  obtain ⟨S, hS, h⟩ := hP V hV φ (f.comp (algebraMap (FractionRing R₁) L))
    (fun r => by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
      exact hf ⟨_, hW r⟩) σ (fun x => hσ (algebraMap (FractionRing R₁) L x))
  refine ⟨S, hS, fun x hx hxS => ?_⟩
  obtain ⟨v, hv⟩ := (h x (f x) (hσ x)).1 hxS
  have hx0 : x ≠ 0 := fun e => hx (e ▸ W.zero_mem)
  have hi : x⁻¹ ∈ W := (W.mem_or_inv_mem x).resolve_left hx
  have hu : IsUnit (algebraMap W V ⟨x⁻¹, hi⟩) := by
    refine IsUnit.of_mul_eq_one v (IsFractionRing.injective V (FractionRing V) ?_)
    rw [map_mul, hv, map_one]
    change j ⟨x⁻¹, hi⟩ * _ = _
    rw [← hf, ← map_mul, inv_mul_cancel₀ hx0, map_one]
  obtain ⟨u, hu'⟩ := isUnit_iff_exists_inv.1 (IsLocalHom.map_nonunit _ hu)
  have : x⁻¹ * u = 1 := congrArg Subtype.val hu'
  have e : (u : L) = x := by rw [eq_inv_of_mul_eq_one_right this, inv_inv]
  exact hx (e ▸ u.2)

theorem isIntegral_inv {R₀ K : Type} [CommRing R₀] [IsLocalRing R₀] [IsNoetherianRing R₀]
    [IsAdicComplete (maximalIdeal R₀) R₀] [Field K] [Algebra R₀ K] (S : ValuationSubring K)
    (h₁ : ∀ r, algebraMap R₀ K r ∈ S) (h₂ : ∀ r ∈ maximalIdeal R₀, algebraMap R₀ K r ∈ S.nonunits)
    {x : K} (hx : IsIntegral R₀ x) (hxS : x ∈ S) (hv : S.valuation x = 1) : IsIntegral R₀ x⁻¹ := by
  let B := Algebra.adjoin R₀ {x}
  have : Module.Finite R₀ B := Algebra.finite_adjoin_simple_of_isIntegral hx
  have : IsLocalRing B := T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R₀) B
  let S' : Subalgebra R₀ K := { S.toSubring with algebraMap_mem' := h₁ }
  have hB : B ≤ S' := Algebra.adjoin_le (by rintro _ rfl; exact hxS)
  let i : B →+* S := (B.val : B →+* K).codRestrict S fun b => hB b.2
  let p : Ideal B := (maximalIdeal S).comap i
  have hp : (p.comap (algebraMap R₀ B)).IsMaximal := by
    have : maximalIdeal R₀ ≤ p.comap (algebraMap R₀ B) := fun r hr =>
      (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, h₁ r⟩)).mp (h₂ r hr)
    rw [← (maximalIdeal.isMaximal R₀).eq_of_le (Ideal.IsPrime.ne_top inferInstance) this]
    infer_instance
  have hm : p = maximalIdeal B := eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_under p hp)
  have hu : IsUnit (⟨x, Algebra.subset_adjoin rfl⟩ : B) := by
    by_contra hn
    have : (⟨x, Algebra.subset_adjoin rfl⟩ : B) ∈ p := hm ▸ hn
    have h3 : x ∈ S.nonunits := (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, hxS⟩)).mpr this
    exact (S.mem_nonunits_iff.1 h3).ne hv
  obtain ⟨u, hu'⟩ := isUnit_iff_exists_inv.1 hu
  have : x * u = 1 := congrArg Subtype.val hu'
  rw [← eq_inv_of_mul_eq_one_right this]
  exact (Algebra.IsIntegral.isIntegral (R := R₀) u).map B.val

theorem mem_of_isIntegral {R K : Type} [CommRing R] [Field K] [Algebra R K] (S : ValuationSubring K)
    (h : ∀ r, algebraMap R K r ∈ S) {x : K} (hx : IsIntegral R x) : x ∈ S := by
  letI : Algebra R S := ((algebraMap R K).codRestrict S h).toAlgebra
  have : IsScalarTower R S K := .of_algebraMap_eq fun _ => rfl
  obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := S) (K := K)).mp
    (IsIntegral.tower_top (R := R) hx)
  exact y.2

theorem exists_place_detecting_units : ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (ϖ : O'), ArcBase O' ϖ → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁), Function.Injective g → g.Finite → ∀ P : Set (ValuationSubring (AlgebraicClosure (FractionRing R₁))), (∀ S ∈ P, ∀ r : R₁, algebraMap (FractionRing R₁) _ (algebraMap R₁ _ r) ∈ S) → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (φ : R₁ →+* V) (gam : FractionRing R₁ →+* FractionRing V), (∀ r, gam (algebraMap R₁ _ r) = algebraMap V _ (φ r)) → ∀ σ : AlgebraicClosure (FractionRing R₁) →+* AlgebraicClosure (FractionRing V), (∀ x, σ (algebraMap (FractionRing R₁) _ x) = algebraMap (FractionRing V) _ (gam x)) → ∃ S ∈ P, ∀ x (y : FractionRing V), σ x = algebraMap (FractionRing V) _ y → (x ∈ S ↔ y ∈ Set.range (algebraMap V (FractionRing V)))) → ∃ S₀ ∈ P, ∀ x, (∀ S ∈ P, x ∈ S) → S₀.valuation x = 1 → ∀ S ∈ P, S.valuation x = 1 := by
  intro O' _ _ _ ϖ hO R₁ _ _ g hg hfin P hR hP
  obtain ⟨_, _, hc⟩ : ∃ _ : IsLocalRing O', IsPrincipalIdealRing O' ∧ IsAdicComplete (maximalIdeal O') O' := by
    rcases hO with ⟨hF, -⟩ | ⟨hD, hi, hc⟩
    · letI := hF.toField
      refine ⟨inferInstance, inferInstance, ?_⟩
      rw [IsLocalRing.maximalIdeal_eq_bot]
      infer_instance
    · refine ⟨inferInstance, inferInstance, ?_⟩
      rwa [hi.maximalIdeal_eq]
  have hps : IsAdicComplete (maximalIdeal (PowerSeries O')) (PowerSeries O') := ReciprocityTheory.P1.isAdicComplete_ps
  have : CharZero (PowerSeries O') := charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))
  have : CharZero R₁ := charZero_of_injective_ringHom hg
  letI := g.toAlgebra
  have : Module.Finite (PowerSeries O') R₁ := hfin
  have : IsLocalRing R₁ := T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := PowerSeries O') R₁
  have : IsNoetherianRing R₁ := IsNoetherianRing.of_finite (PowerSeries O') R₁
  have : FaithfulSMul (PowerSeries O') R₁ := (faithfulSMul_iff_algebraMap_injective _ _).2 hg
  have hloc : IsLocalHom (algebraMap (PowerSeries O') R₁) := inferInstance
  have hR' : ∀ S ∈ P, ∀ r : R₁, algebraMap R₁ (AlgebraicClosure (FractionRing R₁)) r ∈ S := fun S hS r => by
    rw [IsScalarTower.algebraMap_apply R₁ (FractionRing R₁)]
    exact hR S hS r
  have hinj : Function.Injective (algebraMap R₁ (AlgebraicClosure (FractionRing R₁))) := by
    rw [IsScalarTower.algebraMap_eq R₁ (FractionRing R₁)]
    exact (algebraMap (FractionRing R₁) _).injective.comp (IsFractionRing.injective R₁ _)
  have hnf : ¬ IsField R₁ := fun h => by
    have hX : ¬ IsUnit (PowerSeries.X : PowerSeries O') := PowerSeries.X_prime.not_isUnit
    refine hX (hloc.1 _ ?_)
    obtain ⟨b, hb⟩ := h.mul_inv_cancel ((map_ne_zero_iff g hg).2 PowerSeries.X_ne_zero)
    exact IsUnit.of_mul_eq_one b hb
  have hint : ∀ x, (∀ S ∈ P, x ∈ S) → IsIntegral R₁ x := fun x hx => by
    by_contra hn
    let L := IntermediateField.adjoin (FractionRing R₁) {x}
    have : FiniteDimensional (FractionRing R₁) L :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    have : Algebra.EssFiniteType R₁ (FractionRing R₁) := .of_isLocalization _ (nonZeroDivisors R₁)
    have : Algebra.EssFiniteType R₁ L := .comp R₁ (FractionRing R₁) L
    let x' : L := ⟨x, IntermediateField.subset_adjoin _ _ rfl⟩
    have : IsScalarTower R₁ L (AlgebraicClosure (FractionRing R₁)) := .of_algebraMap_eq fun _ => rfl
    have hn' : ¬ IsIntegral R₁ x' := fun h => hn (h.map (IsScalarTower.toAlgHom R₁ L _))
    obtain ⟨W, _, h2, h3⟩ := exists_discreteValuationSubring_dominating_notMem (R := R₁) hn'
    obtain ⟨S, hS, h⟩ := exists_mem_of_dvr P hP L W
      ((localSubring_range_le_valuationSubring_iff _ _).1 h2).1
    exact h x' h3 (hx S hS)
  let L : IntermediateField (FractionRing R₁) (AlgebraicClosure (FractionRing R₁)) := ⊥
  obtain ⟨W, _, h2⟩ := exists_discreteValuationSubring_dominating R₁ (FractionRing R₁) L hnf
  obtain ⟨h2, h3⟩ := (localSubring_range_le_valuationSubring_iff _ _).1 h2
  obtain ⟨S₀, hS₀, h⟩ := exists_mem_of_dvr P hP L W h2
  refine ⟨S₀, hS₀, fun x hx hv S hS => ?_⟩
  have e : ∀ r, algebraMap (PowerSeries O') (AlgebraicClosure (FractionRing R₁)) r = algebraMap R₁ _ (g r) :=
    fun r => IsScalarTower.algebraMap_apply _ R₁ _ r
  have hi : IsIntegral (PowerSeries O') x⁻¹ := by
    refine isIntegral_inv S₀ (fun r => e r ▸ hR' S₀ hS₀ (g r)) (fun r hr => ?_)
      (isIntegral_trans x (hint x hx)) (hx S₀ hS₀) hv
    have h4 := h3 (g r) (fun hu => hr (hloc.1 r hu))
    rw [e]
    rw [ValuationSubring.mem_nonunits_iff_or] at h4 ⊢
    exact h4.imp (fun e => congrArg Subtype.val e) (fun e => h _ e)
  have h5 : x⁻¹ ∈ S := mem_of_isIntegral S (hR' S hS) hi.tower_top
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hv
  refine le_antisymm ((S.valuation_le_one_iff x).2 (hx S hS)) ?_
  have h6 := (S.valuation_le_one_iff _).2 h5
  rwa [map_inv₀, inv_le_one₀ (by simpa [Valuation.pos_iff] using hx0)] at h6

end GlobalTheory.CentredPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPlaceCentredClosedPointDetectsUnitsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_centred_closed_point_detects_units : ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (ϖ : O'), ArcBase O' ϖ → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁), Function.Injective g → g.Finite → ∀ P : Set (ValuationSubring (AlgebraicClosure (FractionRing R₁))), (∀ S ∈ P, ∀ r : R₁, algebraMap (FractionRing R₁) _ (algebraMap R₁ _ r) ∈ S) → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (φ : R₁ →+* V) (gam : FractionRing R₁ →+* FractionRing V), (∀ r, gam (algebraMap R₁ _ r) = algebraMap V _ (φ r)) → ∀ σ : AlgebraicClosure (FractionRing R₁) →+* AlgebraicClosure (FractionRing V), (∀ x, σ (algebraMap (FractionRing R₁) _ x) = algebraMap (FractionRing V) _ (gam x)) → ∃ S ∈ P, ∀ x (y : FractionRing V), σ x = algebraMap (FractionRing V) _ y → (x ∈ S ↔ y ∈ Set.range (algebraMap V (FractionRing V)))) → ∃ S₀ ∈ P, ∀ x, (∀ S ∈ P, x ∈ S) → S₀.valuation x = 1 → ∀ S ∈ P, S.valuation x = 1 := by
  first | exact @GlobalTheory.CentredPlace.exists_place_detecting_units | exact GlobalTheory.CentredPlace.exists_place_detecting_units | (intros; apply GlobalTheory.CentredPlace.exists_place_detecting_units <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
noncomputable section
namespace GlobalTheory.OneBasis

theorem mem_iff_of_valOver {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
    (y : FractionRing V) : 0 ≤ v (algebraMap _ F y) ↔ y ∈ Set.range (algebraMap V (FractionRing V)) := by
  have key : ∀ x : V, 0 ≤ v (algebraMap _ F (algebraMap V (FractionRing V) x)) := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    rw [hv _ n ⟨u, by simp [mul_comm]⟩]
    exact_mod_cast Nat.zero_le n
  refine ⟨fun h => ?_, fun ⟨x, hx⟩ => hx ▸ key x⟩
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy]⟩
  obtain ⟨n, u, hu⟩ := hasVal_of_ne_zero hϖ hy
  rw [hv _ n ⟨u, hu⟩] at h
  have hn : 0 ≤ n := by exact_mod_cast h
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  exact ⟨ϖ ^ k * u, by simp [hu]⟩

theorem near_of_unif (hV : HV) {Z : Scheme.{0}} {G₀ : Over Z} [GrpObj G₀] {L₀ : LB G₀.left} (hL₀ : L₀.IsLB)
    {ρ₀ : LB.Gen (L₀.pull (eSec G₀))} {R : Type} [CommRing R] [IsDomain R] [CharZero R] {x : Sp (FractionRing R) ⟶ Z}
    {A : PolAV (Sp (FractionRing R))} {φ : A.A.left ⟶ G₀.left} {w : LB.Iso A.L (L₀.pull φ)} {ρ}
    (hA : RigPull A.A G₀ x φ w ρ ρ₀) {K : Type} [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K]
    {m n r d C : ℕ} (hm : Odd m) (h3 : 3 ≤ m) (hn : n.Prime) (hn' : Odd n)
    {θ : LB.Sec (LPow G₀ L₀ ((1 : ℕ) : ℤ) (Over.mk x))} {τ : Fin r → LB.Sec (LPow G₀ L₀ ((m ^ 2 : ℕ) : ℤ) (Over.mk x))}
    (hτ : AllBasis G₀ L₀ (m ^ 2) x τ) {θK : SecA A K 1} {τK : Fin r → SecA A K (m ^ 2)}
    (hθK : Thru w 1 (T' := TFK (R := R) K) (T := Over.mk x) (jFK (R := R) K) θ θK)
    (hτK : ∀ i, Thru w (m ^ 2) (T' := TFK (R := R) K) (T := Over.mk x) (jFK (R := R) K) (τ i) (τK i))
    {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    (hc : IsAdicComplete (maximalIdeal V) V) (hmV : IsUnit (m : V)) (hnV : IsUnit (n : V))
    (gam : FractionRing R →+* FractionRing V) {χ : Sp V ⟶ Z} (h : spMap gam ≫ x = jK V ≫ χ)
    (hθ : FrameAt G₀ L₀ 1 x gam χ h (fun _ : Fin 1 => θ))
    {D : DegData V (maximalIdeal V)} {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (U : Unif (maximalIdeal V) D A' G) {Φ : G.left ⟶ G₀.left} {ω : LB.Iso U.LG.L (L₀.pull Φ)}
    (hω : RigPull G G₀ χ Φ ω U.LG.rig ρ₀) {u₀ : FractionRing R} {u : V} (hu : u ≠ 0) (hu₀ : gam u₀ = algebraMap V _ u)
    (hidx : ∀ (ϖ : V) (Q : D.toPre.X → ℤ) (e : ℕ), Irreducible ϖ → QForm.IsQ D.toPre ϖ Q →
      HasVal ϖ (algebraMap V (FractionRing V) u) e → ∀ (cls : Fin r → D.toPre.X) (mu : ℕ), Adapted (m ^ 2) Q cls mu →
      (d : ℤ) * ∑ i, Q (cls i) = C * e * (m ^ 2 : ℕ)) :
    ∃ (B : Matrix (Fin r) (Fin r) (FractionRing V)) (O : ValuationSubring (AlgebraicClosure (FractionRing V))),
      BasisBy G₀ L₀ (m ^ 2) x gam χ h τ B ∧
      (∀ y, algebraMap (FractionRing V) _ y ∈ O ↔ y ∈ Set.range (algebraMap V (FractionRing V))) ∧
      ∀ σ : K →+* AlgebraicClosure (FractionRing V),
        (∀ y, σ (algebraMap (FractionRing R) K y) = algebraMap (FractionRing V) _ (gam y)) →
        ∃ T', (tab ρ m θK τK).Near (m ^ 2) n d (algebraMap (FractionRing R) K u₀ ^ C) σ O T' (B.map (algebraMap _ _)) := by
  obtain ⟨hL, h₁, h₂, h₃, h₄⟩ := hV
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨v, hv⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 V ϖ hϖ
  choose Q hQ using fun y : D.toPre.X => exists_genHasVal hϖ D.toPre.P.L D.toPre.P.isLB
    (fun _ : PUnit => (D.toPre.c y).left) (fun _ => ptK (D.toPre.c y)) (fun _ => QForm.ptK_eq D.toPre y) (fun _ => -1)
    (D.toPre.psi y) (D.toPre.psi_gen y)
  replace hQ : QForm.IsQ D.toPre ϖ Q := hQ
  obtain ⟨O, hO⟩ := exists_valuationSubring v
  have hm1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨φ', w', ρ', w₀, th, ϑ, cls, mu, b, τF, s, B, p₁, p₂, p₃, p₄, p₅, p₆, p₇, p₈, p₉, q₁, q₂, q₃⟩ :=
    GlobalTheory.T.exists_adaptedBasis_at_trait_vs_generic_basis hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ _ v hv A' G hG U Z G₀ L₀ hL₀ ρ₀ χ Φ ω hω _ x gam h θ hθ (m ^ 2) r τ hm1 hτ
  refine ⟨B, O, q₃, fun y => (hO _).trans (mem_iff_of_valOver hϖ hv y), fun σ hσ => ⟨tab ρ' m th τF, ?_, ?_, ?_⟩⟩
  · rw [← h] at p₁
    obtain ⟨ψ, ω', c₁, c₂⟩ := GlobalTheory.T.rigidified_bundle_two_pullbacks_compare Z G₀ L₀ hL₀ ρ₀ _ _ x (spMap gam) A.A A'.A A.L A'.L A.isLB A'.isLB φ φ' w w' ρ ρ' hA p₁
    have e : spMap σ ≫ jFK (R := R) K = jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ spMap gam := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg (fun q => spMap q) (RingHom.ext hσ)
    rw [← e] at p₅ p₆
    exact GlobalTheory.T.polarizedAbelian_valueTable_maps_under_baseChange hL R V gam A A' ψ ω' ρ ρ' c₁ K _ σ hσ m r θK th τK τF
      (c₂ 1 (Over.mk x) (TFK (R := R) K) (TFK (R := V) _) (jFK (R := R) K) (spMap σ) rfl e _ _ _ hθK p₅)
      fun i => c₂ _ (Over.mk x) (TFK (R := R) K) (TFK (R := V) _) (jFK (R := R) K) (spMap σ) rfl e _ _ _ (hτK i) (p₆ i)
  · exact (GlobalTheory.T.thetaTable_algClosed_complete_singleValued hL V A' _ ρ' p₁.2.2.1 m n r hm hn' th τF q₁).2
  · obtain ⟨e, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hu hϖ
    have he : HasVal ϖ (algebraMap V (FractionRing V) u) e := ⟨u', by simp [hu', mul_comm]⟩
    refine GlobalTheory.T.uniformised_table_lattice_integral_families hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ _ v hv A' G hG U w₀ ρ' p₂ th ϑ p₃ p₄ m n hm hmV h3 hn hn' hnV O hO r cls
      b τF s _ p₈ p₉ q₁ q₂ d _ ?_
    have e₁ : (d : ℚ) * ∑ i, (Q (cls i) : ℚ) = C * e * (m ^ 2 : ℕ) := by exact_mod_cast hidx ϖ Q e hϖ hQ he cls mu p₇
    have e₂ : ((m ^ 2 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ^ 2 ≠ 0)
    rw [e₁, mul_div_cancel_right₀ _ e₂, map_pow, hσ, hu₀, AddValuation.map_pow, hv _ _ he, ← WithTop.coe_nsmul, nsmul_eq_mul]
    norm_cast

theorem exists_odd_prime_unit (O : Type) [CommRing O] [IsLocalRing O] : ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : O) := by
  have h : IsUnit (((3 : ℕ) : O) * 2 + ((5 : ℕ) : O) * (-1)) := by norm_num
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
  · exact ⟨3, by norm_num, by decide, isUnit_of_mul_isUnit_left h⟩
  · exact ⟨5, by norm_num, by decide, isUnit_of_mul_isUnit_left h⟩

theorem exists_fraction_map {W W' : Type} [CommRing W] [IsDomain W] [CommRing W'] [IsDomain W'] {io : W →+* W'}
    (h : Function.Injective io) : ∃ io' : FractionRing W →+* FractionRing W',
      ∀ y, io' (algebraMap W _ y) = algebraMap W' _ (io y) :=
  ⟨IsFractionRing.lift (g := (algebraMap W' (FractionRing W')).comp io) ((IsFractionRing.injective W' _).comp h),
    fun y => IsFractionRing.lift_algebraMap _ y⟩

theorem exists_closure_map {k F : Type} [Field k] [Field F] [IsAlgClosed F] (f : k →+* F) :
    ∃ i : AlgebraicClosure k →+* F, ∀ y, i (algebraMap k _ y) = f y := by
  letI := f.toAlgebra
  let i : AlgebraicClosure k →ₐ[k] F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨i.toRingHom, i.commutes⟩

theorem mem_range_iff_of_finite {W W' : Type} [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CommRing W'] [IsDomain W']
    {io : W →+* W'} (hf : io.Finite) {io' : FractionRing W →+* FractionRing W'}
    (h : ∀ y, io' (algebraMap W _ y) = algebraMap W' _ (io y)) (y : FractionRing W) :
    io' y ∈ Set.range (algebraMap W' (FractionRing W')) ↔ y ∈ Set.range (algebraMap W (FractionRing W)) := by
  refine ⟨fun ⟨z, hz⟩ => ?_, fun ⟨z, hz⟩ => ⟨io z, by rw [← hz, h]⟩⟩
  obtain ⟨p, hp, e⟩ := hf.to_isIntegral z
  refine IsIntegrallyClosed.algebraMap_eq_of_integral ⟨p, hp, io'.injective ?_⟩
  rw [Polynomial.hom_eval₂, map_zero, ← hz, show io'.comp (algebraMap W _) = (algebraMap W' _).comp io from RingHom.ext h,
    ← Polynomial.hom_eval₂, e, map_zero]

theorem exists_unit_matrix {V F : Type} [CommRing V] [IsDomain V] [Field F] [Algebra (FractionRing V) F] {r : ℕ}
    {O : ValuationSubring F} (hO : ∀ y, algebraMap (FractionRing V) F y ∈ O ↔ y ∈ Set.range (algebraMap V (FractionRing V)))
    {Φ B : Matrix (Fin r) (Fin r) (FractionRing V)} (hB : (B.map (algebraMap _ F)).det ≠ 0)
    {U : Matrix (Fin r) (Fin r) O} (hU : IsUnit U.det)
    (e : Φ.map (algebraMap _ F) = U.map O.subtype * B.map (algebraMap _ F)) :
    ∃ U₀ : Matrix (Fin r) (Fin r) V, IsUnit U₀.det ∧ Φ = U₀.map (algebraMap V (FractionRing V)) * B := by
  have hB₀ : IsUnit B.det := by
    refine isUnit_iff_ne_zero.2 fun h => hB ?_
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
  have e₁ : (Φ * B⁻¹).map (algebraMap _ F) = U.map O.subtype := by
    rw [Matrix.map_mul, e, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hB₀,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  choose U₀ hU₀ using fun i j => (hO ((Φ * B⁻¹) i j)).1 (by
    rw [show algebraMap _ F ((Φ * B⁻¹) i j) = (U i j : F) from congrFun (congrFun e₁ i) j]; exact (U i j).2)
  have e₂ : (Matrix.of U₀).map (algebraMap V (FractionRing V)) = Φ * B⁻¹ := Matrix.ext hU₀
  refine ⟨Matrix.of U₀, ?_, by rw [e₂, Matrix.nonsing_inv_mul_cancel_right _ _ hB₀]⟩
  have e₃ : algebraMap _ F (algebraMap V (FractionRing V) (Matrix.of U₀).det) = (U.det : F) := by
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, e₂, e₁]
    exact (RingHom.map_det O.subtype U).symm
  obtain ⟨a, ha⟩ := hU.exists_right_inv
  have ha' : (U.det : F) * a = 1 := congrArg Subtype.val ha
  obtain ⟨z, hz⟩ := (hO (algebraMap V (FractionRing V) (Matrix.of U₀).det)⁻¹).1 (by
    rw [map_inv₀, e₃, ← eq_inv_of_mul_eq_one_right ha']; exact a.2)
  refine IsUnit.of_mul_eq_one z (IsFractionRing.injective V (FractionRing V) ?_)
  rw [map_mul, hz, map_one, mul_inv_cancel₀]
  intro h0
  rw [h0, map_zero] at e₃
  rw [← e₃, zero_mul] at ha'
  exact zero_ne_one ha'

theorem exists_isFrame_pow_sq : GlobalTheory.Ex.HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c), Function.Injective g → g.Finite → IsIntegrallyClosed R₁ → GlobalTheory.LN.TraitData Y a g y₁ → RealAt Y a g y₁ → (∃ θ, GlobalTheory.LN.IsFrame Y.t.G Y.t.PP.L 1 (y₁ ≫ Y.j) (fun _ : Fin 1 => θ)) → ∀ m : ℕ, Odd m → IsUnit (m : O') → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R₁ →+* R₂) (h' : FractionRing R₁ →+* FractionRing R₂), Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧ (∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) ∧ ∃ (n : ℕ) (f : Fin n → _), GlobalTheory.LN.IsFrame Y.t.G Y.t.PP.L (m ^ 2) ((spMap h' ≫ y₁) ≫ Y.j) f := by
  intro hV _ hU _ _ _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ₀ a hB R₁ _ _ g y₁ hg hgf hn hT _ ⟨θ, hθ⟩ m hm hmu
  by_cases hm1 : m = 1
  · subst hm1
    refine ⟨R₁, inferInstance, inferInstance, RingHom.id _, RingHom.id _, Function.injective_id, RingHom.Finite.id _, hn,
      fun _ => rfl, ?_⟩
    have e : spMap (RingHom.id (FractionRing R₁)) ≫ y₁ = y₁ := by
      rw [show spMap (RingHom.id (FractionRing R₁)) = 𝟙 _ from Spec.map_id _, Category.id_comp]
    rw [e]
    exact ⟨1, _, hθ⟩
  have h3 : 3 ≤ m := by obtain ⟨k, rfl⟩ := hm; omega
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hL := hV.1
  have hO' : IsLocalRing O' ∧ IsNoetherianRing O' := by
    rcases hB with ⟨h, -⟩ | ⟨h, -⟩
    · letI := h.toField; exact ⟨inferInstance, inferInstance⟩
    · exact ⟨inferInstance, inferInstance⟩
  obtain ⟨_, _⟩ := hO'
  obtain ⟨n, hnp, hno, hnu⟩ := exists_odd_prime_unit O'
  have : CharZero R₁ := ((g.comp (PowerSeries.C (R := O'))).charZero_iff (hg.comp PowerSeries.C_injective)).1 inferInstance
  have : IsNoetherianRing R₁ := by
    letI := g.toAlgebra
    have : Module.Finite (PowerSeries O') R₁ := hgf
    exact IsNoetherianRing.of_finite (PowerSeries O') R₁
  obtain ⟨x₁, x₂, x₃, x₄⟩ := GlobalTheory.T.model_trait_extension_polarised_flat_bundleIso E H D l Xo c _ _ Y
  have hL₀ := Y.t.PP.isLB
  obtain ⟨A, φA, w, ρ, hA⟩ := GlobalTheory.T.exists_rigidified_polarised_fibre_at_field_point hL.1 hL.2.1 E H _ Y.t _ _ (x₂ _ y₁)
  obtain ⟨r, τ, hτ⟩ := GlobalTheory.T.exists_thetaBasis_after_every_field_extension hL.1 hL.2.1 _ Y.t.G _ hL₀ _ _ A φA w hA.1 hA.2.1 (m ^ 2) hm2
  let K := AlgebraicClosure (FractionRing R₁)
  have cal := GlobalTheory.T.sectionPower_calculus_geometric_fibre _ Y.t.G _ hL₀ R₁ _ A φA w hA.1 hA.2.1 K
  obtain ⟨θK, hθK, -⟩ := (cal 1).1 (Over.mk (y₁ ≫ Y.j)) (jFK (R := R₁) K) rfl θ
  choose τK hτK _ using fun i => (cal (m ^ 2)).1 (Over.mk (y₁ ≫ Y.j)) (jFK (R := R₁) K) rfl (τ i)
  have hfull := (GlobalTheory.T.thetaTable_algClosed_complete_singleValued hL R₁ A K ρ hA.2.2.1 m n r hm hno θK τK
    ((cal (m ^ 2)).2.2 _ _ (algebraMap _ K) rfl r τ τK hτ hτK)).1
  obtain ⟨d, C, hd, hnum⟩ := GlobalTheory.T.shortestRepresentatives_form_sum_depends_on_lattice a.D₀.X (fun y => a.be y y / 2) (m ^ 2) r hm2 fun y => by
    by_cases hy : y = 0
    · simp [hy]
    · exact Int.ediv_nonneg (a.be_pos y hy).le (by norm_num)
  let κ : K := algebraMap (FractionRing R₁) K (algebraMap R₁ _ (g PowerSeries.X)) ^ C
  have key : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (φ : R₁ →+* W)
      (gam : FractionRing R₁ →+* FractionRing W), (∀ r, gam (algebraMap R₁ _ r) = algebraMap W _ (φ r)) →
      ∀ (χ : Sp W ⟶ Y.X), spMap gam ≫ y₁ ≫ Y.j = jK W ≫ χ →
      ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (io : W →+* V)
        (io' : FractionRing W →+* FractionRing V) (h : spMap (io'.comp gam) ≫ y₁ ≫ Y.j = jK V ≫ spMap io ≫ χ)
        (B : Matrix (Fin r) (Fin r) (FractionRing V)) (O : ValuationSubring (AlgebraicClosure (FractionRing V))),
        io.Finite ∧ (∀ y, io' (algebraMap W _ y) = algebraMap V _ (io y)) ∧
        BasisBy Y.t.G Y.t.PP.L (m ^ 2) (y₁ ≫ Y.j) (io'.comp gam) (spMap io ≫ χ) h τ B ∧
        (∀ y, algebraMap (FractionRing V) _ y ∈ O ↔ y ∈ Set.range (algebraMap V (FractionRing V))) ∧
        ∀ σ : K →+* AlgebraicClosure (FractionRing V),
          (∀ y, σ (algebraMap (FractionRing R₁) K y) = algebraMap (FractionRing V) _ (io' (gam y))) →
          ∃ T', (tab ρ m θK τK).Near (m ^ 2) n d κ σ O T' (B.map (algebraMap _ _)) := by
    intro W _ _ _ hW φ gam hgam χ h
    have hφ : Function.Injective φ := fun s t e => IsFractionRing.injective R₁ (FractionRing R₁)
      (gam.injective (by rw [hgam, hgam, e]))
    have step : ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (io : W →+* V)
        (t : SAB H (Sp V)) (_ : SABMap t Y.t (spMap io ≫ χ)) (P : PELUnif (maximalIdeal V) t),
        CDvr V ∧ Function.Injective io ∧ io.Finite ∧
        ∀ (ϖ : V) (Q : P.D.toPre.X → ℤ) (e : ℕ), Irreducible ϖ → QForm.IsQ P.D.toPre ϖ Q →
          HasVal ϖ (algebraMap V (FractionRing V) (io (φ (g PowerSeries.X)))) e →
          ∀ (cls : Fin r → P.D.toPre.X) (mu : ℕ), Adapted (m ^ 2) Q cls mu →
          (d : ℤ) * ∑ i, Q (cls i) = C * e * (m ^ 2 : ℕ) := by
      obtain ⟨g₁, g₂⟩ := hT.2 W hW φ gam hgam χ h
      by_cases hu : IsUnit (φ (g PowerSeries.X))
      · have := hW.1
        have e : spMap (RingHom.id W) ≫ χ = χ := by
          rw [show spMap (RingHom.id W) = 𝟙 _ from Spec.map_id _, Category.id_comp]
        obtain ⟨t, mt, P, hP⟩ := GlobalTheory.T.exists_uniformisation_trivial_torus_abelianLocus hL hU E H D l Xo c _ _ Y W hW χ (spMap gam ≫ y₁)
          ((Category.assoc _ _ _).trans h) (g₁ hu)
        refine ⟨W, inferInstance, inferInstance, inferInstance, RingHom.id W, t, e.symm ▸ mt, P, hW, Function.injective_id,
          RingHom.Finite.id _, fun ϖ Q e hϖ hQ he cls mu _ => ?_⟩
        obtain ⟨u, hu⟩ := hu
        have e₀ : (e : ℤ) = 0 := hasVal_unique hϖ he ⟨u, by simp [hu]⟩
        have : ∀ i, Q (cls i) = 0 := fun i => by rw [Subsingleton.elim (cls i) 0]; exact QForm.Q_zero hϖ P.D hQ
        simp [this, e₀]
      · obtain ⟨V, _, _, _, io, hV', hi, hf, hd⟩ := g₂ hu
        have := hV'.1
        obtain ⟨t, mt, P, ε, hP⟩ := GlobalTheory.T.arcData_psi_valuation_eq_half_form E H D l Xo c _ _ Y O' b a V _ _ _
          (hi.comp (hφ.comp (hg.comp PowerSeries.C_injective))) hd
        refine ⟨V, inferInstance, inferInstance, inferInstance, io, t, mt, P, hV', hi, hf,
          fun ϖ Q e hϖ hQ he cls mu hcls => hnum _ Q ε e (Nat.pos_of_ne_zero ?_) (hP ϖ Q e hϖ hQ he) cls mu hcls⟩
        rintro rfl
        obtain ⟨u, hu'⟩ := he
        have : IsLocalHom io := hf.to_isIntegral.isLocalHom hi
        refine hu (isUnit_of_map_unit io _ ?_)
        rw [IsFractionRing.injective V (FractionRing V) (hu'.trans (by simp) : _ = algebraMap V _ (u : V))]
        exact u.isUnit
    obtain ⟨V, _, _, _, io, t, mt, P, hV', hi, hf, hidx⟩ := step
    obtain ⟨io', hio⟩ := exists_fraction_map hi
    have h' : spMap (io'.comp gam) ≫ y₁ ≫ Y.j = jK V ≫ spMap io ≫ χ := by
      have e₁ : spMap (io'.comp gam) = spMap io' ≫ spMap gam := Spec.map_comp _ _
      have e₂ : spMap io' ≫ jK W = jK V ≫ spMap io := by
        rw [← Spec.map_comp, ← Spec.map_comp]
        exact congrArg (fun q => spMap q) (RingHom.ext hio)
      rw [e₁, Category.assoc, h, ← Category.assoc, e₂, Category.assoc]
    have hc : ∀ s, (io'.comp gam) (algebraMap R₁ _ s) = algebraMap V _ ((io.comp φ) s) := fun s => by
      simp [hgam, hio]
    have := hV'.2.2
    obtain ⟨ω, hω⟩ := x₄ _ t _ mt P.U.LG P.bundle
    have unit : ∀ k : ℕ, IsUnit (k : O') → IsUnit (k : V) := fun k hk => by
      simpa using hk.map (io.comp (φ.comp (g.comp (PowerSeries.C (R := O')))))
    obtain ⟨B, O, b₁, b₂, b₃⟩ := near_of_unif (d := d) (C := C) hV hL₀ hA hm h3 hnp hno hτ hθK hτK hV'.2.1 (unit m hmu)
      (unit n hnu) (io'.comp gam) h' (hθ V hV' (io.comp φ) _ hc _ h') t.semi P.U hω
      (u := io (φ (g PowerSeries.X))) ((map_ne_zero_iff _ hi).2 ((map_ne_zero_iff _ hφ).2
        ((map_ne_zero_iff _ hg).2 PowerSeries.X_ne_zero))) (hc _) hidx
    exact ⟨V, inferInstance, inferInstance, inferInstance, io, io', h', B, O, hf, hio, b₁, b₂, b₃⟩
  let PP : Set (ValuationSubring K) := {S | (∀ s : R₁, algebraMap (FractionRing R₁) K (algebraMap R₁ _ s) ∈ S) ∧
    ∃ (K' : Type) (_ : Field K') (σ : K →+* K') (O : ValuationSubring K') (T' : Tab K' r) (B : Matrix (Fin r) (Fin r) K'),
      O.comap σ = S ∧ (tab ρ m θK τK).Near (m ^ 2) n d κ σ O T' B}
  obtain ⟨S₀, hS₀, hunit⟩ := GlobalTheory.T.exists_place_centred_closed_point_detects_units O' ϖ₀ hB R₁ g hg hgf PP (fun S hS => hS.1) (by
    intro W _ _ _ hW φ gam hgam σ hσ
    have := hW.1
    obtain ⟨χ, hχ⟩ := x₁ W (spMap gam ≫ y₁ ≫ Y.j) (spMap φ ≫ spMap g ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b) (by
      have e₂ : spMap gam ≫ jK R₁ = jK W ≫ spMap φ := by
        rw [← Spec.map_comp, ← Spec.map_comp]
        exact congrArg (fun q => spMap q) (RingHom.ext hgam)
      simp only [Category.assoc]
      rw [hT.1, ← Category.assoc, e₂, Category.assoc])
    obtain ⟨V, _, _, _, io, io', -, B, O, hf, hio, -, b₂, b₃⟩ := key W hW φ gam hgam χ hχ
    obtain ⟨i₀, hi₀⟩ := exists_closure_map ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp io')
    replace hi₀ : ∀ y, i₀ (algebraMap (FractionRing W) _ y) = algebraMap (FractionRing V) _ (io' y) := hi₀
    have mem : ∀ x (y : FractionRing W), σ x = algebraMap (FractionRing W) _ y →
        (x ∈ O.comap (i₀.comp σ) ↔ y ∈ Set.range (algebraMap W (FractionRing W))) := fun x y e => by
      rw [ValuationSubring.mem_comap, RingHom.comp_apply, e, hi₀, b₂, mem_range_iff_of_finite hf hio]
    obtain ⟨T', hT'⟩ := b₃ (i₀.comp σ) fun y => by rw [RingHom.comp_apply, hσ, hi₀]
    exact ⟨_, ⟨fun s => (mem _ _ (hσ _)).2 ⟨φ s, (hgam s).symm⟩, _, _, _, O, T', _, rfl, hT'⟩, mem⟩)
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_global_matrix_eq_unit_det_mul_local K r (tab ρ m θK τK) (m ^ 2) n d κ PP S₀ hm2 hnp.one_le hd hS₀ hfull (fun S hS => hS.2) hunit
  obtain ⟨R₂, _, _, h, h', j, Φ₂, f₁, f₂, f₃, f₄, f₅, f₆, f₇⟩ := GlobalTheory.T.exists_finite_normal_ext_containing_algebraic_elements R₁ hn (Fin r × Fin r) (fun p => Φ p.1 p.2)
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_basis_recombination_invertible_matrix_trait _ Y.t.G _ hL₀ (m ^ 2) _ _ (y₁ ≫ Y.j) h' ((spMap h' ≫ y₁) ≫ Y.j) (Category.assoc _ _ _).symm r τ
    (Matrix.of fun i k => Φ₂ (i, k))
  refine ⟨R₂, inferInstance, inferInstance, h, h', f₁, f₂, f₃, f₄, r, f, fun W _ _ _ hW φ gam hgam χ hχ => ?_⟩
  have := hW.1
  have sp : ∀ {K₁ K₂ K₃ : Type} [Field K₁] [Field K₂] [Field K₃] (p : K₁ →+* K₂) (q : K₂ →+* K₃),
      spMap (q.comp p) = spMap q ≫ spMap p := fun p q => Spec.map_comp _ _
  obtain ⟨V, _, _, _, io, io', hh, B, O, hfin, hio, b₁, b₂, b₃⟩ := key W hW (φ.comp h) (gam.comp h')
    (fun s => by simp [f₄, hgam]) χ (by rw [← hχ, sp]; simp only [Category.assoc])
  obtain ⟨σ, hσ⟩ := f₇ (AlgebraicClosure (FractionRing V)) ((algebraMap (FractionRing V) _).comp (io'.comp gam))
  have hσ' : ∀ y, σ (algebraMap (FractionRing R₁) K y) = algebraMap (FractionRing V) _ (io' ((gam.comp h') y)) := fun y => by
    rw [← f₅, hσ]; rfl
  obtain ⟨T', hT'⟩ := b₃ σ hσ'
  obtain ⟨U, hU₁, hU₂⟩ := hΦ _ σ O T' _ ⟨fun s => by
    rw [ValuationSubring.mem_comap, hσ', b₂]
    exact ⟨io (φ (h s)), by simp [f₄, hgam, hio]⟩, _, _, σ, O, T', _, rfl, hT'⟩ hT'
  obtain ⟨U₀, u₁, u₂⟩ := exists_unit_matrix b₂ (Φ := (Matrix.of fun i k => Φ₂ (i, k)).map (io'.comp gam)) hT'.2.2.1 hU₁
    (Eq.trans (Matrix.ext fun i k => ((congrArg σ (f₆ (i, k))).symm.trans (hσ _)).symm) hU₂)
  have h₂ : spMap (io'.comp gam) ≫ (spMap h' ≫ y₁) ≫ Y.j = jK V ≫ spMap io ≫ χ := by
    rw [← hh, sp, sp, sp]; simp only [Category.assoc]
  exact GlobalTheory.T.trait_sectionBasis_descends_finite_dvr_extension _ Y.t.G _ x₃ hL₀ _ _ _ W V io io' hfin hio gam χ hχ h₂ r f
    (hf V (io'.comp gam) _ hh h₂ B U₀ b₁ u₁ u₂)

end GlobalTheory.OneBasis
end
