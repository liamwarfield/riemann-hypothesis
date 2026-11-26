module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdmissibleBaseOfCompleteDvr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGaugeFiniteExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgClosurePointFactorsThroughFiniteLocalSubalgeb
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgClosurePointFactorsThroughFiniteLocalSubalgeb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem finpt_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (Z : Scheme.{0}) (π : Z ⟶ Sp R) [IsFinite π] (k : Sp (Kb R) ⟶ Z), k ≫ π = (TF (R := R) (Kb R)).hom → ∃ S : Subalgebra R (Kb R), Module.Finite R S ∧ IsLocalRing S ∧ ∃ k₀ : Sp S ⟶ Z, k₀ ≫ π = spMap (algebraMap R S) ∧ spMap (S.val : S →+* Kb R) ≫ k₀ = k := by
  intro R _ _ _ hR Z π _ k hk
  obtain ⟨⟨hN, -, -, hC⟩, -⟩ := hR
  haveI := hN
  haveI := hC
  haveI : IsAffine Z := isAffine_of_isAffineHom π
  let i : Spec Γ(Z, ⊤) ≅ Z := Z.isoSpec.symm
  obtain ⟨θ, hθ⟩ := Spec.map_surjective (i.hom ≫ π)
  have h₁ : θ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hθ]
    infer_instance
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (k ≫ i.inv)
  have hc : θ ≫ ψ = CommRingCat.ofHom (algebraMap R (Kb R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hθ, Category.assoc, i.inv_hom_id_assoc, hk]
    simp only [TF, jFK, jK, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← IsScalarTower.algebraMap_eq]
  let _ : Algebra R Γ(Z, ⊤) := θ.hom.toAlgebra
  have : Module.Finite R Γ(Z, ⊤) := h₁
  let φ : Γ(Z, ⊤) →ₐ[R] Kb R := ⟨ψ.hom, fun r => congr(($hc).hom r)⟩
  let S : Subalgebra R (Kb R) := φ.range
  have hfin : Module.Finite R S :=
    Module.Finite.of_surjective φ.rangeRestrict.toLinearMap φ.rangeRestrict_surjective
  have hloc : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) S
  refine ⟨S, hfin, hloc, spMap (φ.rangeRestrict : Γ(Z, ⊤) →+* S) ≫ i.hom, ?_, ?_⟩
  · rw [Category.assoc, ← hθ, ← Spec.map_comp]
    congr 1
    ext r
    exact congrArg Subtype.val (φ.rangeRestrict.commutes r)
  · rw [← Category.assoc, ← Spec.map_comp]
    have : CommRingCat.ofHom (φ.rangeRestrict : Γ(Z, ⊤) →+* S) ≫ CommRingCat.ofHom (S.val : S →+* Kb R) = ψ := by
      ext b; rfl
    rw [this, hψ, Category.assoc, i.inv_hom_id, Category.comp_id]

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgClosurePointFactorsThroughFiniteLocalSubalgebStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algClosurePoint_factors_through_finite_local_subalgebra : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (Z : Scheme.{0}) (π : Z ⟶ Sp R) [IsFinite π] (k : Sp (Kb R) ⟶ Z), k ≫ π = (TF (R := R) (Kb R)).hom → ∃ S : Subalgebra R (Kb R), Module.Finite R S ∧ IsLocalRing S ∧ ∃ k₀ : Sp S ⟶ Z, k₀ ≫ π = spMap (algebraMap R S) ∧ spMap (S.val : S →+* Kb R) ≫ k₀ = k := by
  first | exact @GlobalTheory.Mum.finpt_factor | exact GlobalTheory.Mum.finpt_factor | (intros; apply GlobalTheory.Mum.finpt_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGaugeFiniteExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.FinGauge
open GlobalTheory.Ex

theorem spMap_val_comp {R : Type} [CommRing R] [IsDomain R] (S : Subalgebra R (Kb R)) :
    spMap (S.val : S →+* Kb R) ≫ spMap (algebraMap R S) = (TF (R := R) (Kb R)).hom := by
  simp only [spMap, TF, Over.mk_hom, jFK, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

theorem vF_sF_mem {F : Type} [Field F] {A : Type} [CommRing A] (f : A →+* F) {X Y : Scheme.{0}} {L : LB X}
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (J : (Sp F ⟶ X) → L.ι) (r₀ : Sp A ⟶ Y)
    (hJ : ∀ k, ⊤ ≤ (r₀ ≫ φ k) ⁻¹ᵁ L.U (J ((spMap f ≫ r₀) ≫ φ k))) :
    (∀ t : LB.Gen (LB.LinComb L φ ε), ∃ u : Aˣ, f u = vF t (spMap f ≫ r₀) J) ∧
      ∀ s : LB.Sec (LB.LinComb L φ ε), ∃ a : A, f a = sF s (spMap f ≫ r₀) J := by
  have key : ∀ (W : Y.Opens) (hr : ⊤ ≤ r₀ ⁻¹ᵁ W) (a : Γ(Y, W)),
      valF (spMap f ≫ r₀) W a = f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((r₀.appLE W ⊤ hr).hom a)) := by
    intro W hr a
    have h' : ⊤ ≤ (spMap f ≫ r₀) ⁻¹ᵁ W := fun q _ => hr (Set.mem_univ (spMap f q))
    rw [valF, dite_eq_left h']
    have e : (spMap f ≫ r₀).appLE W ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom =
        r₀.appLE W ⊤ hr ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom f := by
      rw [← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.appLE_comp_appLE (spMap f) r₀ W ⊤ ⊤ hr le_rfl,
        Category.assoc]
      rfl
    exact congrArg (fun g => g.hom a) e
  let j : K → L.ι := fun k => J ((spMap f ≫ r₀) ≫ φ k)
  have hr : ⊤ ≤ r₀ ⁻¹ᵁ LB.wchart L φ j := fun z _ => Set.mem_iInter.2 fun k => hJ k trivial
  let g : Γ(Y, LB.wchart L φ j) →* A :=
    ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (r₀.appLE _ ⊤ hr).hom).toMonoidHom
  refine ⟨fun t => ⟨Units.map g (t.s j), ?_⟩, fun s => ⟨_, (key _ hr (s.f j)).symm⟩⟩
  exact (key _ hr _).symm

theorem ext_unique {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {F : Type} [Field F] {A : Type} [CommRing A]
    [IsDomain A] (f : A →+* F) (hf : Function.Injective f) (x y : Sp A ⟶ D.P.A.left)
    (h : spMap f ≫ x = spMap f ≫ y) : x = y := by
  haveI := D.P.isAb.proper
  haveI : IsDominant (spMap f) := by
    constructor
    show DenseRange (PrimeSpectrum.comap f)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
    intro a ha
    rw [RingHom.mem_ker, ← map_zero f] at ha
    rw [hf ha]
    exact zero_mem _
  refine ext_of_isDominant_of_isSeparated D.P.A.hom ?_ (spMap f) h
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ D.P.A.hom)
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (y ≫ D.P.A.hom)
  rw [← hφ, ← hφ']
  congr 1
  have e : spMap f ≫ Spec.map φ = spMap f ≫ Spec.map φ' := by
    rw [hφ, hφ', ← Category.assoc, ← Category.assoc, h]
  simp only [spMap, ← Spec.map_comp] at e
  have e' := Spec.map_injective e
  ext r
  exact hf (congrArg (fun g => g.hom r) e')

theorem exists_gauge_local {F : Type} [Field F] {A : Type} [CommRing A] [IsLocalRing A] (f : A →+* F) {X : Scheme.{0}}
    {L : LB X} (hL : L.IsLB) (hu : ∀ x y : Sp A ⟶ X, spMap f ≫ x = spMap f ≫ y → x = y) :
    ∃ J : (Sp F ⟶ X) → L.ι, (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) ∧ ∀ x₀ : Sp A ⟶ X, ⊤ ≤ x₀ ⁻¹ᵁ L.U (J (spMap f ≫ x₀)) := by
  have key : ∀ ψ : Sp F ⟶ X, ∃ j, ⊤ ≤ ψ ⁻¹ᵁ L.U j ∧ ∀ x₀ : Sp A ⟶ X, spMap f ≫ x₀ = ψ → ⊤ ≤ x₀ ⁻¹ᵁ L.U j := by
    intro ψ
    by_cases h : ∃ x₀ : Sp A ⟶ X, spMap f ≫ x₀ = ψ
    · obtain ⟨x₀, rfl⟩ := h
      obtain ⟨j, hj⟩ := GlobalTheory.IntegralGauge.exists_chart_local hL x₀
      exact ⟨j, fun w _ => hj (Set.mem_univ (spMap f w)), fun x₁ e => hu x₀ x₁ e.symm ▸ hj⟩
    · obtain ⟨j, hj⟩ := GlobalTheory.IntegralGauge.exists_chart_local hL ψ
      exact ⟨j, hj, fun x₀ e => (h ⟨x₀, e⟩).elim⟩
  choose J h₁ h₂ using key
  exact ⟨J, h₁, fun x₀ => h₂ _ x₀ rfl⟩

theorem top_of_finite_local {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (S : Subalgebra R (Kb R))
    [Module.Finite R S] [IsLocalRing S] (U : (Sp R).Opens) (h : ⊤ ≤ spMap (algebraMap R S) ⁻¹ᵁ U) : ⊤ ≤ U := by
  haveI : FaithfulSMul R S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b e
    have e' := congrArg (fun s : S => (s : Kb R)) e
    simp only [Subalgebra.coe_algebraMap] at e'
    rw [IsScalarTower.algebraMap_apply R (FractionRing R) (Kb R), IsScalarTower.algebraMap_apply R (FractionRing R) (Kb R) b] at e'
    exact IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) (Kb R)).injective e')
  haveI := Algebra.IsIntegral.isLocalHom R S
  have hc : (spMap (algebraMap R S)).base (IsLocalRing.closedPoint S) = IsLocalRing.closedPoint R := by
    show PrimeSpectrum.comap (algebraMap R S) _ = _
    exact IsLocalRing.comap_closedPoint _
  have hm : IsLocalRing.closedPoint R ∈ U := hc ▸ h (Set.mem_univ (IsLocalRing.closedPoint S))
  exact fun w _ => (IsLocalRing.specializes_closedPoint (R := R) w).mem_open U.isOpen hm

theorem psi_val_mem {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι) (χ : D.X) (I : Ideal R) (hI : D.PsiIn χ I)
    (hc : ⊤ ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (J (jFK (R := R) F ≫ D.xK χ))) :
    ∃ a ∈ I, vF (D.psi χ) (jFK (R := R) F) J = algebraMap (FractionRing R) F (algebraMap R _ a) := by
  have hV : IsAffineOpen (⊤ : (Sp R).Opens) := isAffineOpen_top _
  have h : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U
      (fun _ => J (jFK (R := R) F ≫ D.xK χ)) := fun y _ => Set.mem_iInter.2 fun _ => hc trivial
  obtain ⟨r, hr, er⟩ := hI (fun _ => J (jFK (R := R) F ≫ D.xK χ)) ⊤ hV hc h
  have h4 : ⊤ ≤ jFK (R := R) F ⁻¹ᵁ (jK R ⁻¹ᵁ ⊤) := fun _ _ => trivial
  have a := GlobalTheory.Ex.UnitVal.valF_res' h h4 ((D.psi χ).s _).val
  rw [Scheme.Hom.app_eq_appLE] at er
  have e1 : vF (D.psi χ) (jFK (R := R) F) J = valF (jFK (R := R) F ≫ jK R) ⊤ r :=
    a.symm.trans ((congrArg (valF _ _) er.symm).trans (GlobalTheory.Ex.UnitVal.valF_appLE' (jK R) ⊤ le_rfl h4 r))
  have hsurj : Function.Surjective (DegPre.toOpen (R := R) (⊤ : (Sp R).Opens)) := by
    intro b
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b, ?_⟩
    simp [DegPre.toOpen]
  obtain ⟨a', ha', rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 hr
  refine ⟨a', ha', e1.trans ?_⟩
  have e2 : jFK (R := R) F ≫ jK R = spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _)) := by
    simp only [spMap, jFK, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [DegPre.toOpen, RingHom.comp_apply, GlobalTheory.Ex.UnitVal.valF_res' (le_top : (⊤ : (Sp R).Opens) ≤ ⊤) (fun _ _ => trivial), e2]
  exact GlobalTheory.OriginFrame.valF_spMap_fn _ a'

theorem exists_finite_pt (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (Z : Scheme.{0})
    (π : Z ⟶ Sp R) [IsFinite π] (k : Sp (Kb R) ⟶ Z) (hk : k ≫ π = (TF (R := R) (Kb R)).hom) :
    ∃ S : Subalgebra R (Kb R), Module.Finite R S ∧ IsLocalRing S ∧
      ∃ k₀ : Sp S ⟶ Z, k₀ ≫ π = spMap (algebraMap R S) ∧ spMap (S.val : S →+* Kb R) ≫ k₀ = k :=
  GlobalTheory.T.algClosurePoint_factors_through_finite_local_subalgebra R hR Z π k hk

theorem exists_finite_ext (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (D : DegPre R)
    (x : TF (R := R) (Kb R) ⟶ D.P.A) (m : ℕ) (hm : IsUnit (m : R)) (z : 𝟙_ (Over (Sp R)) ⟶ D.P.A)
    (hx : x ^ m = toUnit _ ≫ z) : ∃ S : Subalgebra R (Kb R), Module.Finite R S ∧ IsLocalRing S ∧
      ∃ x₀ : Sp S ⟶ D.P.A.left, x₀ ≫ D.P.A.hom = spMap (algebraMap R S) ∧ spMap (S.val : S →+* Kb R) ≫ x₀ = x.left := by
  haveI : IsNoetherianRing R := hR.1.1
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp at hm
    · exact h
  haveI : IsFinite (mulA D.P.A m).left := (GlobalTheory.firstFiveLaws.1.mulN (Sp R) D.P m hm1).1
  have hxm : x.left ≫ (mulA D.P.A m).left = (TF (R := R) (Kb R)).hom ≫ z.left := by
    have h1 : (toUnit (TF (R := R) (Kb R))).left = (TF (R := R) (Kb R)).hom := by
      simpa using Over.w (toUnit (TF (R := R) (Kb R)))
    rw [← Over.comp_left, GlobalTheory.IntDiv.comp_mulA, hx, Over.comp_left, h1]
  obtain ⟨S, hSf, hSl, k₀, hk₀, hk⟩ := exists_finite_pt R hR (pullback (mulA D.P.A m).left z.left)
    (pullback.snd _ _) (pullback.lift _ _ hxm) (pullback.lift_snd _ _ _)
  refine ⟨S, hSf, hSl, k₀ ≫ pullback.fst _ _, ?_, ?_⟩
  · have h2 : pullback.fst (mulA D.P.A m).left z.left ≫ D.P.A.hom = pullback.snd _ _ := by
      rw [← Over.w (mulA D.P.A m), ← Category.assoc, pullback.condition, Category.assoc, Over.w z]
      simp
    rw [Category.assoc, h2, hk₀]
  · rw [← Category.assoc, hk, pullback.lift_fst]

theorem gauge : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (N : GlobalTheory.Ex.NumD (Kb R)) (ν : GlobalTheory.Ex.NumOf D.toPre (Kb R) N) (m : ℕ), Odd m → IsUnit (m : R) → ∀ (p : QkPt D.toPre (Kb R) (m ^ 2)), ∃ (N' : GlobalTheory.Ex.NumD (Kb R)) (ν' : GlobalTheory.Ex.NumOf D.toPre (Kb R) N') (q' : N'.QT (m ^ 2)) (S : Subalgebra R (Kb R)), ν'.th = ν.th ∧ ν'.QPt p q' ∧ Module.Finite R S ∧ (∀ x ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), ∀ x' ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), ∀ x'' ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), (N'.θ x x' x'' : Kb R) ∈ S ∧ (((N'.θ x x' x'')⁻¹ : (Kb R)ˣ) : Kb R) ∈ S) ∧ (∀ x ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), (N'.σ x : Kb R) ∈ S ∧ (((N'.σ x)⁻¹ : (Kb R)ˣ) : Kb R) ∈ S) ∧ (∀ χ, N'.th (N'.c χ * (q'.1.2 ^ m).b) ∈ S) ∧ (∀ χ, (N'.ψ χ : Kb R) ∈ S) ∧ ∀ n : ℕ, {χ | ¬ ∃ s ∈ (maximalIdeal R ^ n • ⊤ : Submodule R S), (s : Kb R) = N'.ψ χ}.Finite := by
  intro R _ _ _ hR D N ν m hm hmu p
  obtain ⟨q, hq⟩ := GlobalTheory.SeriesCompare.exists_val D.psi_even D.tau_bimult ν p
  have hxm : (p.g.b ^ m) ^ m = toUnit _ ≫ D.toPre.c (ν.eX q.1.1.toAdd) := by
    rw [← pow_mul, ← sq, ← hq.2.1, ← map_pow, N.QT_pow_b q, ν.c_eq]
  obtain ⟨S, hSf, hSl, x₀, hx₀A, hx₀⟩ := exists_finite_ext R hR D.toPre _ m hmu _ hxm
  let f : S →+* Kb R := S.val
  have hfi : Function.Injective f := Subtype.val_injective
  let TS : Over (Sp R) := Over.mk (spMap (algebraMap R S))
  let ιS : TF (R := R) (Kb R) ⟶ TS := Over.homMk (spMap f) (spMap_val_comp S)
  obtain ⟨J', hJg, hJi⟩ := exists_gauge_local f D.toPre.P.isLB (ext_unique D.toPre f hfi)
  obtain ⟨N', ν', hJ, hth⟩ := GlobalTheory.GaugeValues.exists_numOf GlobalTheory.firstFiveLaws.1 R D.toPre D.psi_even D.tau_bimult
    (Kb R) J' hJg ν.th ν.th_gen
  subst hJ
  obtain ⟨q', hq'⟩ := GlobalTheory.SeriesCompare.exists_val D.psi_even D.tau_bimult ν' p
  set G := Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}) with hG
  have hExt : ∀ a ∈ G, ∃ a₀ : TS ⟶ D.toPre.P.A, ιS ≫ a₀ = ν'.eA a := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a h =>
      rcases h with ⟨χ, rfl⟩ | h
      · exact ⟨toUnit _ ≫ D.toPre.c (ν'.eX χ), by rw [ν'.c_eq, ← Category.assoc]; congr 1; exact toUnit_unique _ _⟩
      · rw [Set.mem_singleton_iff] at h
        subst h
        refine ⟨Over.homMk x₀ hx₀A, Over.OverMorphism.ext ?_⟩
        rw [NumD.Gt.pow_b, map_pow, hq'.2.1]
        exact hx₀
    | one => exact ⟨1, by rw [map_one, comp_one]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨a₀, ha₀⟩ := ha
      obtain ⟨b₀, hb₀⟩ := hb
      exact ⟨a₀ * b₀, by rw [comp_mul, ha₀, hb₀, map_mul]⟩
    | inv a _ ha =>
      obtain ⟨a₀, ha₀⟩ := ha
      exact ⟨a₀⁻¹, by rw [GrpObj.comp_inv, ha₀, map_inv]⟩

  have hval : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ D.toPre.P.A.left)) (ε : K → ℤ) (r₀ : Sp S ⟶ Y),
      (∀ t : LB.Gen (LB.LinComb D.toPre.P.L φ ε), ∃ u : Sˣ, f u = vF t (spMap f ≫ r₀) ν'.J) ∧
        ∀ s : LB.Sec (LB.LinComb D.toPre.P.L φ ε), ∃ a : S, f a = sF s (spMap f ≫ r₀) ν'.J :=
    fun Y K _ φ ε r₀ => vF_sF_mem f ν'.J r₀ fun k => by rw [Category.assoc]; exact hJi _
  have hleft : ∀ (a : N'.A) (a₀ : TS ⟶ D.toPre.P.A), ιS ≫ a₀ = ν'.eA a → (ν'.eA a).left = spMap f ≫ a₀.left := by
    intro a a₀ h
    rw [← h]
    rfl
  have hunit : ∀ (w : (Kb R)ˣ) (u : Sˣ), (w : Kb R) = f u → (w : Kb R) ∈ S ∧ ((w⁻¹ : (Kb R)ˣ) : Kb R) ∈ S := by
    intro w u h
    refine ⟨h ▸ (u : S).2, ?_⟩
    rw [Units.val_inv_eq_inv_val, h, ← map_units_inv]
    exact ((u⁻¹ : Sˣ) : S).2
  have hrig : ∃ u : Sˣ, f u = vF (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A) (ε := fun _ => 1)
      D.toPre.rig (TF (R := R) (Kb R)).hom ν'.J := by
    have := (hval _ PUnit (fun _ => eSec D.toPre.P.A) (fun _ => 1)
      (spMap (algebraMap R S) : Sp S ⟶ (𝟙_ (Over (Sp R))).left)).1 D.toPre.rig
    rwa [spMap_val_comp S] at this
  obtain ⟨u, hu⟩ := hrig
  have hxK : ∀ χ', jFK (R := R) (Kb R) ≫ D.toPre.xK χ' =
      spMap f ≫ (spMap (algebraMap R S) ≫ (D.toPre.c χ').left) := by
    intro χ'
    have h1 : (toUnit (TK R)).left = jK R := by simpa using Over.w (toUnit (TK R))
    simp only [DegPre.xK, ptK, Over.comp_left, h1]
    rw [← Category.assoc, ← Category.assoc, spMap_val_comp S]
    rfl
  have hc : ∀ χ', ⊤ ≤ (D.toPre.c χ').left ⁻¹ᵁ D.toPre.P.L.U (ν'.J (jFK (R := R) (Kb R) ≫ D.toPre.xK χ')) := by
    intro χ'
    have := hJi (spMap (algebraMap R S) ≫ (D.toPre.c χ').left)
    rw [← hxK] at this
    exact top_of_finite_local S _ fun z hz => this hz
  have hψ : ∀ χ (I : Ideal R), D.toPre.PsiIn (ν'.eX χ) I → ∃ a ∈ I, (N'.ψ χ : Kb R) = f (algebraMap R S a * u) := by
    intro χ I hI
    obtain ⟨a, ha, hv⟩ := psi_val_mem D.toPre ν'.J _ I hI (hc _)
    refine ⟨a, ha, ?_⟩
    rw [ν'.ψ_eq, hv, ← hu, map_mul]
    congr 1
  refine ⟨N', ν', q', S, hth, hq', hSf, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx x' hx' x'' hx''
    obtain ⟨a, ha⟩ := hExt x hx
    obtain ⟨b, hb⟩ := hExt x' hx'
    obtain ⟨c, hc⟩ := hExt x'' hx''
    have e : (lift (ν'.eA x) (lift (ν'.eA x') (ν'.eA x''))).left = spMap f ≫ (lift a (lift b c)).left := by
      rw [← ha, ← hb, ← hc, ← comp_lift, ← comp_lift]
      rfl
    obtain ⟨w, hw⟩ := (hval _ _ _ _ (lift a (lift b c)).left).1 D.toPre.cub.t
    refine hunit _ w ?_
    rw [ν'.θ_eq, e]
    exact hw.symm
  · intro x hx
    obtain ⟨a, ha⟩ := hExt x hx
    obtain ⟨w, hw⟩ := (hval _ _ _ _ a.left).1 D.toPre.sym
    refine hunit _ w ?_
    rw [ν'.σ_eq, hleft x a ha, hw]
  · intro χ
    have hm : N'.c χ * (q'.1.2 ^ m).b ∈ G :=
      G.mul_mem (Subgroup.subset_closure (Or.inl ⟨χ, rfl⟩)) (Subgroup.subset_closure (Or.inr rfl))
    obtain ⟨a, ha⟩ := hExt _ hm
    obtain ⟨s, hs⟩ := (hval _ _ _ _ a.left).2 ν'.th
    have e2 := ν'.th_eq (N'.c χ * (q'.1.2 ^ m).b)
    rw [hleft _ a ha, ← hs, ← hu] at e2
    have e3 : N'.th (N'.c χ * (q'.1.2 ^ m).b) = f (s * ((u⁻¹ : Sˣ) : S)) := by
      rw [map_mul, ← e2, map_units_inv, _root_.mul_assoc, mul_inv_cancel₀ ((u.isUnit.map f).ne_zero), _root_.mul_one]
    rw [e3]
    exact (s * ((u⁻¹ : Sˣ) : S)).2
  · intro χ
    by_cases h0 : ν'.eX χ = 0
    · rw [(AddEquiv.map_eq_zero_iff ν'.eX).1 h0, N'.ψ_zero]
      exact S.one_mem
    · obtain ⟨a, -, he⟩ := hψ χ _ (D.psi_pos _ h0)
      rw [he]
      exact (algebraMap R S a * (u : S)).2
  · intro n
    refine ((D.psi_tendsto n).preimage ν'.eX.injective.injOn).subset ?_
    intro χ hχ
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hχ ⊢
    intro hI
    apply hχ
    obtain ⟨a, ha, he⟩ := hψ χ _ hI
    refine ⟨algebraMap R S a * u, ?_, he.symm⟩
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem_smul ha trivial
end GlobalTheory.FinGauge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGaugeFiniteExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_gauge_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (N : GlobalTheory.Ex.NumD (Kb R)) (ν : GlobalTheory.Ex.NumOf D.toPre (Kb R) N) (m : ℕ), Odd m → IsUnit (m : R) → ∀ (p : QkPt D.toPre (Kb R) (m ^ 2)), ∃ (N' : GlobalTheory.Ex.NumD (Kb R)) (ν' : GlobalTheory.Ex.NumOf D.toPre (Kb R) N') (q' : N'.QT (m ^ 2)) (S : Subalgebra R (Kb R)), ν'.th = ν.th ∧ ν'.QPt p q' ∧ Module.Finite R S ∧ (∀ x ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), ∀ x' ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), ∀ x'' ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), (N'.θ x x' x'' : Kb R) ∈ S ∧ (((N'.θ x x' x'')⁻¹ : (Kb R)ˣ) : Kb R) ∈ S) ∧ (∀ x ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), (N'.σ x : Kb R) ∈ S ∧ (((N'.σ x)⁻¹ : (Kb R)ˣ) : Kb R) ∈ S) ∧ (∀ χ, N'.th (N'.c χ * (q'.1.2 ^ m).b) ∈ S) ∧ (∀ χ, (N'.ψ χ : Kb R) ∈ S) ∧ ∀ n : ℕ, {χ | ¬ ∃ s ∈ (maximalIdeal R ^ n • ⊤ : Submodule R S), (s : Kb R) = N'.ψ χ}.Finite := by
  first | exact @GlobalTheory.FinGauge.gauge | exact GlobalTheory.FinGauge.gauge | (intros; apply GlobalTheory.FinGauge.gauge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermSmulAddDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermSmulAddDecomposition
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem theta_term_smul_add (O : Type) [CommRing O] (N : GlobalTheory.Ex.NumD O) (S : Subring O) (m : ℕ) (h : N.Gt)
    (y : N.X) (hy : h ^ m = N.io y)
    (hθ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), ∀ x' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}),
      ∀ x'' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}),
        (N.θ x x' x'' : O) ∈ S ∧ (((N.θ x x' x'')⁻¹ : Oˣ) : O) ∈ S)
    (hσ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), (N.σ x : O) ∈ S ∧ (((N.σ x)⁻¹ : Oˣ) : O) ∈ S)
    (a b : N.X) : ∃ w : Oˣ, (w : O) ∈ S ∧
      N.ψ (m • a + b) * h.s (m • a + b) = w * N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b) := by
  set H := Subgroup.closure (Set.range N.c ∪ {h.b}) with hH
  set T := S.toSubmonoid.units with hT
  set π : Oˣ →* Oˣ ⧸ T := QuotientGroup.mk' T with hπ
  have Hc : ∀ a, N.c a ∈ H := fun a => Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)
  have Hb : h.b ∈ H := Subgroup.subset_closure (Or.inr rfl)
  have θ1 : ∀ x ∈ H, ∀ x' ∈ H, ∀ x'' ∈ H, π (N.θ x x' x'') = 1 := fun x hx x' hx' x'' hx'' =>
    (QuotientGroup.eq_one_iff _).2 ((Submonoid.mem_units_iff _ _).2 (hθ x hx x' hx' x'' hx''))
  have σ1 : ∀ a, π (N.σ (N.c a)) = 1 := fun a =>
    (QuotientGroup.eq_one_iff _).2 ((Submonoid.mem_units_iff _ _).2 (hσ _ (Hc a)))
  have Bl : ∀ a a' b, π (N.τ (a + a') b) = π (N.τ a b) * π (N.τ a' b) := by
    intro a a' b
    have := congrArg π (N.τ_add_left a a' b)
    rwa [map_mul, map_mul, θ1 _ (Hc a) _ (Hc a') _ (Hc b), mul_one] at this
  have Br : ∀ a b b', π (N.τ a (b + b')) = π (N.τ a b) * π (N.τ a b') := by
    intro a b b'
    have := congrArg π (N.τ_add_right a b b')
    rwa [map_mul, map_mul, θ1 _ (Hc b) _ (Hc b') _ (Hc a), mul_one] at this
  have fadd : ∀ a b, π (N.ψ (a + b)) = π (N.τ a b) * π (N.ψ a) * π (N.ψ b) := by
    intro a b
    rw [N.ψ_add, map_mul, map_mul]
  have fneg : ∀ a, π (N.ψ (-a)) = π (N.ψ a) := by
    intro a
    have := congrArg π (N.even a)
    rwa [map_mul, σ1, mul_one] at this
  have Bnegr : ∀ a b, π (N.τ a (-b)) = (π (N.τ a b))⁻¹ := by
    intro a b
    have := Br a b (-b)
    rw [add_neg_cancel, N.τ_zero_right, map_one] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have Bself : ∀ a, π (N.τ a a) = π (N.ψ a) ^ 2 := by
    intro a
    have := fadd a (-a)
    rw [add_neg_cancel, N.ψ_zero, map_one, fneg, Bnegr, mul_assoc, eq_comm, inv_mul_eq_one] at this
    rw [sq]
    exact this
  have Bsmul : ∀ (k : ℕ) a b, π (N.τ (k • a) b) = π (N.τ a b) ^ k := by
    intro k a b
    induction k with
    | zero => simp
    | succ k ih => rw [succ_nsmul, Bl, ih, pow_succ]
  have Bsmulr : ∀ (k : ℕ) a b, π (N.τ a (k • b)) = π (N.τ a b) ^ k := by
    intro k a b
    rw [N.τ_symm, Bsmul, N.τ_symm]
  have fsmul : ∀ (k : ℕ) a, π (N.ψ (k • a)) = π (N.ψ a) ^ (k ^ 2) := by
    intro k a
    induction k with
    | zero => simp
    | succ k ih =>
      rw [succ_nsmul, fadd, ih, Bsmul, Bself, ← pow_mul, ← pow_add, ← pow_succ]
      congr 1
      ring
  have Sadd : ∀ χ χ', π (h.s (χ + χ')) = π (h.s χ) * π (h.s χ') := by
    intro χ χ'
    have := congrArg π (h.mult χ χ')
    rwa [map_mul, map_mul, θ1 _ (Hc χ) _ (Hc χ') _ Hb, mul_one] at this
  have Ssmul : ∀ (k : ℕ) a, π (h.s (k • a)) = π (h.s a) ^ k := by
    intro k a
    induction k with
    | zero => simp
    | succ k ih => rw [succ_nsmul, Sadd, ih, pow_succ]
  have Spow : π (h.s a) ^ m = π (N.τ a y) := by
    have := congrArg π (h.pow_s m a)
    rw [map_mul, map_pow, hy, GlobalTheory.Ex.NumD.io_s, N.τ_symm] at this
    have hc : π (cubN N.θ m 1 h.b (N.c a)) = 1 := by
      unfold cubN
      rw [map_prod]
      exact Finset.prod_eq_one fun i _ => θ1 _ (by rw [one_mul]; exact pow_mem Hb i) _ Hb _ (Hc a)
    rw [hc, mul_one] at this
    exact this.symm
  refine ⟨N.ψ (m • a + b) * h.s (m • a + b) / (N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b)), ?_, ?_⟩
  · have e : π (N.ψ (m • a + b) * h.s (m • a + b) / (N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b))) = 1 := by
      rw [map_div, div_eq_one, map_mul, map_mul, map_mul, map_mul, map_pow, fadd, Sadd, fsmul, Bsmul, Br, Bsmulr,
        Ssmul, Spow]
      ac_rfl
    exact ((Submonoid.mem_units_iff _ _).1 ((QuotientGroup.eq_one_iff _).1 e)).1
  · exact (fun (L X Y Z : Oˣ) => show L = L / (X * Y * Z) * X * Y * Z by
      rw [mul_assoc (L / (X * Y * Z)) X Y, mul_assoc (L / (X * Y * Z)) (X * Y) Z, div_mul_cancel]) _ _ _ _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermSmulAddDecompositionStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeriesTerm_smul_add_decomposition : ∀ (O : Type) [CommRing O] (N : GlobalTheory.Ex.NumD O) (S : Subring O) (m : ℕ) (h : N.Gt) (y : N.X), h ^ m = N.io y → (∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), ∀ x' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), ∀ x'' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), (N.θ x x' x'' : O) ∈ S ∧ (((N.θ x x' x'')⁻¹ : Oˣ) : O) ∈ S) → (∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), (N.σ x : O) ∈ S ∧ (((N.σ x)⁻¹ : Oˣ) : O) ∈ S) → ∀ a b : N.X, ∃ w : Oˣ, (w : O) ∈ S ∧ N.ψ (m • a + b) * h.s (m • a + b) = w * N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b) := by
  first | exact @GlobalTheory.theta_term_smul_add | exact GlobalTheory.theta_term_smul_add | (intros; apply GlobalTheory.theta_term_smul_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCoeffsTendstoZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCoeffsTendstoZero
open IsLocalRing

namespace GlobalTheory

theorem adic_coeffs_tendsto_zero :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) = ⊤ → ∀ (X : Type) (z : X → M), (∀ n : ℕ, {χ | z χ ∉ (maximalIdeal R ^ n • ⊤ : Submodule R M)}.Finite) → ∃ c : X → Fin r → R, (∀ χ, z χ = ∑ j, c χ j • s j) ∧ ∀ n : ℕ, {χ | ¬ ∀ j, c χ j ∈ maximalIdeal R ^ n}.Finite := by
  intro R _ _ _ M _ _ r s hs X z hz
  classical
  set m := maximalIdeal R

  have coef : ∀ (x : M) (k : ℕ), x ∈ (m ^ k • ⊤ : Submodule R M) →
      ∃ a : Fin r → R, x = ∑ j, a j • s j ∧ ∀ j, a j ∈ m ^ k := by
    intro x k hx
    rw [← hs, Submodule.mem_ideal_smul_span_iff_exists_sum] at hx
    obtain ⟨a, ha, hsum⟩ := hx
    refine ⟨a, ?_, ha⟩
    rw [← hsum, Finsupp.sum_fintype]
    intro j; simp
  haveI : Module.Finite R M := ⟨by rw [← hs]; exact Submodule.fg_span (Set.finite_range s)⟩
  have krull : (⨅ i : ℕ, m ^ i • ⊤ : Submodule R M) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top
  have anti : ∀ {a b : ℕ}, a ≤ b → (m ^ b • ⊤ : Submodule R M) ≤ m ^ a • ⊤ :=
    fun h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)
  have choiceχ : ∀ χ, ∃ a : Fin r → R, z χ = ∑ j, a j • s j ∧
      ∀ n, (¬ ∀ j, a j ∈ m ^ n) → z χ ∉ (m ^ n • ⊤ : Submodule R M) := by
    intro χ
    by_cases h : ∃ n, z χ ∉ (m ^ n • ⊤ : Submodule R M)
    · set N := Nat.find h with hN
      have hN0 : N ≠ 0 := by
        intro h0
        have := Nat.find_spec h
        rw [← hN, h0, pow_zero, Ideal.one_eq_top, Submodule.top_smul] at this
        exact this Submodule.mem_top
      have hmem : z χ ∈ (m ^ (N - 1) • ⊤ : Submodule R M) := by
        by_contra hc
        have := Nat.find_min' h hc
        omega
      obtain ⟨a, ha, hm⟩ := coef _ _ hmem
      refine ⟨a, ha, fun n hn hzn => hn fun j => ?_⟩
      have hlt : n < N := by
        by_contra hle
        push_neg at hle
        exact (Nat.find_spec h) (anti hle hzn)
      exact Ideal.pow_le_pow_right (by omega) (hm j)
    · push_neg at h
      have hz0 : z χ = 0 := by
        have : z χ ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule R M) := Submodule.mem_iInf _ |>.mpr h
        rw [krull] at this
        exact (Submodule.mem_bot R).mp this
      refine ⟨0, by simp [hz0], fun n hn _ => hn fun j => ?_⟩
      simp
  choose c hc hbad using choiceχ
  refine ⟨c, hc, fun n => (hz n).subset ?_⟩
  intro χ hχ
  exact hbad χ n hχ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCoeffsTendstoZeroStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeffs_adic_finite_of_span_eq_univ : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) = ⊤ → ∀ (X : Type) (z : X → M), (∀ n : ℕ, {χ | z χ ∉ (maximalIdeal R ^ n • ⊤ : Submodule R M)}.Finite) → ∃ c : X → Fin r → R, (∀ χ, z χ = ∑ j, c χ j • s j) ∧ ∀ n : ℕ, {χ | ¬ ∀ j, c χ j ∈ maximalIdeal R ^ n}.Finite := by
  first | exact @GlobalTheory.adic_coeffs_tendsto_zero | exact GlobalTheory.adic_coeffs_tendsto_zero | (intros; apply GlobalTheory.adic_coeffs_tendsto_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermsTorsionPointFiniteAdicCombinatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

open GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.ThetaTermAdic

theorem decomp (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : ℕ) (hm : 0 < m) :
    ∃ (mu rh : X → X), (Set.range rh).Finite ∧ ∀ χ, χ = m • mu χ + rh χ := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  refine ⟨fun χ => ∑ i, (b.repr χ i / (m : ℤ)) • b i, fun χ => ∑ i, (b.repr χ i % (m : ℤ)) • b i, ?_, fun χ => ?_⟩
  · have hS : (Set.pi Set.univ fun _ : Module.Free.ChooseBasisIndex ℤ X => Set.Ico (0 : ℤ) m).Finite :=
      Set.Finite.pi fun _ => Set.finite_Ico _ _
    refine (hS.image fun f => ∑ i, f i • b i).subset ?_
    rintro _ ⟨χ, rfl⟩
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm
    exact ⟨fun i => b.repr χ i % m, fun i _ => ⟨Int.emod_nonneg _ hm'.ne', Int.emod_lt_of_pos _ hm'⟩, rfl⟩
  · conv_lhs => rw [← b.sum_repr χ]
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ, smul_smul, ← add_smul, Int.mul_ediv_add_emod]

theorem mul_mem_smul_top {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) (a s : S)
    (hs : s ∈ (I • ⊤ : Submodule R S)) : a * s ∈ (I • ⊤ : Submodule R S) := by
  rw [Ideal.smul_top_eq_map] at hs ⊢
  exact Ideal.mul_mem_left _ a hs

theorem core {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (N : GlobalTheory.Ex.NumD (Kb R))
    (S : Subalgebra R (Kb R)) [Module.Finite R S] (m : ℕ) (hm : 0 < m) (q : N.QT (m ^ 2))
    (hθ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {(q.1.2 ^ m).b}), ∀ x' ∈ Subgroup.closure (Set.range N.c ∪ {(q.1.2 ^ m).b}),
      ∀ x'' ∈ Subgroup.closure (Set.range N.c ∪ {(q.1.2 ^ m).b}),
      (N.θ x x' x'' : Kb R) ∈ S ∧ (((N.θ x x' x'')⁻¹ : (Kb R)ˣ) : Kb R) ∈ S)
    (hσ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {(q.1.2 ^ m).b}), (N.σ x : Kb R) ∈ S ∧ (((N.σ x)⁻¹ : (Kb R)ˣ) : Kb R) ∈ S)
    (hthS : ∀ χ, N.th (N.c χ * (q.1.2 ^ m).b) ∈ S) (hψS : ∀ χ, (N.ψ χ : Kb R) ∈ S)
    (hψn : ∀ n : ℕ, {χ | ¬ ∃ s ∈ (maximalIdeal R ^ n • ⊤ : Submodule R S), (s : Kb R) = N.ψ χ}.Finite) :
    ∃ (Jx : Type) (_ : Fintype Jx) (g : Jx → Kb R) (c : N.X → Jx → R),
      (∀ χ, N.txT m q χ = ∑ k, algebraMap (FractionRing R) (Kb R) (algebraMap R _ (c χ k)) * g k) ∧
      ∀ n : ℕ, {χ | ¬ ∀ k, c χ k ∈ maximalIdeal R ^ n}.Finite := by
  classical
  set h := q.1.2 ^ m with hdef
  set y := q.1.1.toAdd with hy
  have hh : h ^ m = N.io y := by rw [hdef, ← pow_mul, ← sq]; exact N.mem_QT.1 q.2
  obtain ⟨mu, rh, hrf, hχ⟩ := decomp N.X m hm
  choose w hwS hw using GlobalTheory.T.thetaSeriesTerm_smul_add_decomposition (Kb R) N S.toSubring m h y hh hθ hσ
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := S)
  obtain ⟨e, he⟩ : ∃ e, m ^ 2 = e + 1 := ⟨m ^ 2 - 1, by have := pow_pos hm 2; omega⟩
  let K : N.X → Kb R := fun b => ((N.wQ q / mulq N.θ N.σ m q.1.2.b : (Kb R)ˣ) : Kb R) *
    ((N.ψ b * h.s b * (N.ψ (m • b + y))⁻¹ : (Kb R)ˣ) : Kb R)
  let z0 : N.X → Kb R := fun χ => (w (mu χ) (rh χ) : Kb R) * (N.ψ (mu χ) : Kb R) ^ e * N.th (N.c χ * h.b) *
    N.ψ (mu χ + (m • rh χ + y))
  have key : ∀ χ, N.txT m q χ = K (rh χ) * z0 χ := fun χ => by
    have a := hw (mu χ) (rh χ)
    rw [← hχ χ, he, NumD.τ] at a
    simp only [NumD.txT, NumD.vt, K, z0]
    rw [← hdef, a]
    push_cast
    field_simp
    ring
  have hz0 : ∀ χ, z0 χ ∈ S := fun χ =>
    S.mul_mem (S.mul_mem (S.mul_mem (Subalgebra.mem_toSubring.1 (hwS _ _)) (S.pow_mem (hψS _) _)) (hthS χ)) (hψS _)
  let zS : N.X → S := fun χ => ⟨z0 χ, hz0 χ⟩
  have hzn : ∀ n : ℕ, {χ | zS χ ∉ (maximalIdeal R ^ n • ⊤ : Submodule R S)}.Finite := fun n => by
    refine (hrf.biUnion fun b _ => (hψn n).image fun χ' => m • (χ' - (m • b + y)) + b).subset ?_
    intro χ hχn
    refine Set.mem_biUnion (Set.mem_range_self χ) ⟨mu χ + (m • rh χ + y), ?_, ?_⟩
    · rintro ⟨s', hs', he'⟩
      refine hχn ?_
      have e1 : zS χ = (⟨(w (mu χ) (rh χ) : Kb R) * (N.ψ (mu χ) : Kb R) ^ e * N.th (N.c χ * h.b),
          S.mul_mem (S.mul_mem (Subalgebra.mem_toSubring.1 (hwS _ _)) (S.pow_mem (hψS _) _)) (hthS χ)⟩ : S) * s' :=
        Subtype.ext (by simp only [zS, z0, Subalgebra.coe_mul, he'])
      rw [e1]
      exact mul_mem_smul_top _ _ _ hs'
    · change m • (mu χ + (m • rh χ + y) - (m • rh χ + y)) + rh χ = χ
      rw [add_sub_cancel_right]; exact (hχ χ).symm
  obtain ⟨c, hc, hcn⟩ := GlobalTheory.T.exists_coeffs_adic_finite_of_span_eq_univ R S r s hs N.X zS hzn
  haveI : Fintype (Set.range rh) := hrf.fintype
  refine ⟨Fin r × Set.range rh, inferInstance, fun k => K k.2 * (s k.1 : Kb R),
    fun χ k => if (⟨rh χ, Set.mem_range_self χ⟩ : Set.range rh) = k.2 then c χ k.1 else 0, fun χ => ?_, fun n => ?_⟩
  · rw [key, Fintype.sum_prod_type]
    have hz : z0 χ = ∑ j, algebraMap R (Kb R) (c χ j) * (s j : Kb R) := by
      have := congrArg Subtype.val (hc χ)
      simpa [zS, Algebra.smul_def] using this
    rw [hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← IsScalarTower.algebraMap_apply]
    ring
  · refine (hcn n).subset fun χ hχ hall => hχ fun k => ?_
    dsimp only
    split_ifs
    · exact hall _
    · exact zero_mem _

theorem terms : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (N : GlobalTheory.Ex.NumD (Kb R)) (ν : GlobalTheory.Ex.NumOf D.toPre (Kb R) N) (m : ℕ), Odd m → IsUnit (m : R) → ∀ (p : QkPt D.toPre (Kb R) (m ^ 2)) (q : N.QT (m ^ 2)), ν.QPt p q → ∃ (Jx : Type) (_ : Fintype Jx) (g : Jx → Kb R) (c : N.X → Jx → R), (∀ χ, N.txT m q χ = ∑ k, algebraMap (FractionRing R) (Kb R) (algebraMap R _ (c χ k)) * g k) ∧ ∀ n : ℕ, {χ | ¬ ∀ k, c χ k ∈ maximalIdeal R ^ n}.Finite := by
  intro R _ _ _ hB D N ν m hm hmu p q hq
  haveI : IsNoetherianRing R := hB.1.1
  obtain ⟨N', ν', q', S, hth, hq', hfin, hθ, hσ, hthS, hψS, hψn⟩ := GlobalTheory.T.exists_integral_gauge_finite_extension R hB D N ν m hm hmu p
  haveI := hfin
  obtain ⟨I, hl, -, hI⟩ := GlobalTheory.GaugeHom.exists_hom R D.toPre (Kb R) (Kb R) (RingHom.id _) (RingHom.id_comp _) N N' ν ν' hth
  obtain ⟨e1, e2⟩ := hI (m ^ 2) p p q q' (GlobalTheory.SeriesCompare.qkExt_id p) hq hq'
  have htx : ∀ χ, N.txT m q χ = N'.txT m q' (I.e χ) := fun χ => by
    rw [I.txT_eq hm q q' e1 e2 χ, hl, Units.val_one, _root_.one_mul, RingHom.id_apply]
  obtain ⟨Jx, fJ, g, c, hc, hcn⟩ := core N' S m hm.pos q' hθ hσ hthS hψS hψn
  exact ⟨Jx, fJ, g, fun χ => c (I.e χ), fun χ => by rw [htx, hc], fun n => (hcn n).preimage I.e.injective.injOn⟩

end GlobalTheory.ThetaTermAdic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermsTorsionPointFiniteAdicCombinatioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeriesTerms_torsionPoint_finite_adic_combination : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (N : GlobalTheory.Ex.NumD (Kb R)) (ν : GlobalTheory.Ex.NumOf D.toPre (Kb R) N) (m : ℕ), Odd m → IsUnit (m : R) → ∀ (p : QkPt D.toPre (Kb R) (m ^ 2)) (q : N.QT (m ^ 2)), ν.QPt p q → ∃ (Jx : Type) (_ : Fintype Jx) (g : Jx → Kb R) (c : N.X → Jx → R), (∀ χ, N.txT m q χ = ∑ k, algebraMap (FractionRing R) (Kb R) (algebraMap R _ (c χ k)) * g k) ∧ ∀ n : ℕ, {χ | ¬ ∀ k, c χ k ∈ maximalIdeal R ^ n}.Finite := by
  first | exact @GlobalTheory.ThetaTermAdic.terms | exact GlobalTheory.ThetaTermAdic.terms | (intros; apply GlobalTheory.ThetaTermAdic.terms <;> assumption)
end
