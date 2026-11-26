module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsogenyOfNcard
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrobeniusOnTorsion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelValuationData
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelValuationData
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.TestValuation

open GlobalTheory.ZH.PsiForm

theorem norm_eq_one_of_isUnit {o F : Type} [CommRing o] [NormedField F] (f : o →+* F) (h : ∀ a, ‖f a‖ ≤ 1)
    {a : o} (ha : IsUnit a) : ‖f a‖ = 1 := by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have h3 : ‖f a‖ * ‖f b‖ = 1 := by rw [← norm_mul, ← map_mul, hb, map_one, norm_one]
  refine le_antisymm (h a) ?_
  calc (1 : ℝ) = _ := h3.symm
    _ ≤ _ * 1 := mul_le_mul_of_nonneg_left (h b) (norm_nonneg _)
    _ = _ := mul_one _

theorem isUnit_of_norm_eq_one {V : Type} [CommRing V] [IsDomain V] {F : Type} [NormedField F]
    [Algebra (FractionRing V) F]
    (hle : ∀ x : FractionRing V, ‖algebraMap _ F x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)))
    {a : V} (ha : ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a)‖ = 1) : IsUnit a := by
  have h0 : algebraMap V (FractionRing V) a ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at ha
    exact zero_ne_one ha
  obtain ⟨w, hw⟩ := (hle (algebraMap V (FractionRing V) a)⁻¹).1 (by rw [map_inv₀, norm_inv, ha, inv_one])
  refine IsUnit.of_mul_eq_one w (IsFractionRing.injective V (FractionRing V) ?_)
  rw [map_mul, hw, mul_inv_cancel₀ h0, map_one]

theorem isPrimitiveRoot_map {o F : Type} [CommRing o] [IsDomain o] [Field F] [CharZero F] (f : o →+* F) {ζ : o}
    {n : ℕ} (hn : 0 < n) (h : IsPrimitiveRoot ζ n) : IsPrimitiveRoot (f ζ) n := by
  have h1 := h.isRoot_cyclotomic hn
  have h2 := h1.map (f := f)
  rw [Polynomial.map_cyclotomic] at h2
  exact (Polynomial.isRoot_cyclotomic_iff_charZero hn).1 h2

theorem main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → CharZero u.V ∧ IsUnit ((ρ.n : ℕ) : u.V) ∧ AdmBase u.V (IsLocalRing.maximalIdeal u.V) ∧ ‖((S.r * S.N : ℕ) : PadicAlgCl p)‖ = 1 ∧ IsPrimitiveRoot (y₀ (algebraMap o S.R S.ζ)) ((S.r * S.N) ^ 2) ∧ ∃ (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ), Irreducible ϖ ∧ ValOver ϖ (PadicAlgCl p) v ∧ NormIs u l ϖ Q v lam := by
  intro o Ω _ _ _ hA S ρ p _ y₀ u l hy
  haveI : IsDomain o := hA.ded.toIsDomain
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  have hN : ‖((S.r * S.N : ℕ) : PadicAlgCl p)‖ = 1 := by
    have := norm_eq_one_of_isUnit (y₀.comp (algebraMap o S.R)) hy S.unit
    rwa [map_natCast] at this
  have hpos : 0 < S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  refine ⟨?_, ?_, ⟨inferInstance, inferInstance, inferInstance, u.complete⟩, hN,
    isPrimitiveRoot_map (y₀.comp (algebraMap o S.R)) (pow_pos hpos 2) S.prim, ?_⟩
  · exact ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  · have h1 : IsUnit ((S.r * S.N : ℕ) : u.V) :=
      isUnit_of_norm_eq_one u.norm_le (by rw [map_natCast, map_natCast, hN])
    refine isUnit_of_dvd_unit (Nat.cast_dvd_cast ?_) h1
    rw [ρ.N_eq, ← pow_mul]
    exact Dvd.dvd.mul_left (dvd_pow_self _ (by have := ρ.two_le; omega)) _
  · choose Q hQ using QForm.exists_QVal hϖ u.D
    have h0 := norm_pos_of_irreducible (F := PadicAlgCl p) hϖ
    have h1 := norm_lt_one_of_irreducible u.norm_le hϖ
    obtain ⟨v, hv1, hv2⟩ := GlobalTheory.PadicVal.exists_addValuation_le_iff_eq_iff p _ h0 h1
    refine ⟨ϖ, Q, v, _, hϖ, ?_, neg_pos.2 (Real.log_neg h0 h1), hQ, fun χ => ?_, hv1, hv2⟩
    · intro c n hc
      rw [hv2, norm_of_hasVal u.norm_le hϖ hc, Rat.cast_intCast]
    · have hc := u.D.toPre.P.isLB.cover
      let x : Sp u.V := IsLocalRing.closedPoint u.V
      have hx : (u.D.toPre.c χ).left x ∈ ⨆ i, u.D.toPre.P.L.U i := by rw [hc]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      have htop : ⊤ ≤ (u.D.toPre.c χ).left ⁻¹ᵁ u.D.toPre.P.L.U i :=
        ((IsLocalRing.closedPoint_mem_iff (R := u.V) _).1 hi).ge
      have e1 := l.q_eq χ (fun _ => i) htop
      have e2 := norm_of_hasVal u.norm_le hϖ
        (hasVal_valF u.D.toPre.P.L _ _ (QForm.ptK_eq u.D.toPre χ) (-1) _ (hQ χ) (fun _ => i) htop)
      exact neg_injective (Real.exp_injective (e1.symm.trans e2))

end GlobalTheory.TestValuation
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelValuationDataStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedModel_valuation_data : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → CharZero u.V ∧ IsUnit ((ρ.n : ℕ) : u.V) ∧ AdmBase u.V (IsLocalRing.maximalIdeal u.V) ∧ ‖((S.r * S.N : ℕ) : PadicAlgCl p)‖ = 1 ∧ IsPrimitiveRoot (y₀ (algebraMap o S.R S.ζ)) ((S.r * S.N) ^ 2) ∧ ∃ (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ), Irreducible ϖ ∧ ValOver ϖ (PadicAlgCl p) v ∧ NormIs u l ϖ Q v lam := by
  first | exact @GlobalTheory.TestValuation.main | exact GlobalTheory.TestValuation.main | (intros; apply GlobalTheory.TestValuation.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreSectionLinearCombExistsUniqueThetaAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreSectionLinearCombExistsUniqueThetaAction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.SecComb

theorem equiv_sum {K M J : Type} [CommRing K] [AddCommGroup M] [Module K M] [Fintype J] (ρ : M ≃ₗ[K] M)
    (c : J → K) (v w : J → M) (h : ∀ i, ρ (v i) = w i) : ρ (∑ i, c i • v i) = ∑ i, c i • w i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, h]

variable {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

omit [IsDomain R] in
theorem ofSec_inj {t t' : SecA A F k}
    (h : (SecM.ofSec A.A t : SecM A.A A.L (k : ℤ) (TFK (R := R) F)) = SecM.ofSec A.A t') : t = t' := by
  have h' : t.f = t'.f := congrArg Subtype.val h
  cases t; cases t'; cases h'; rfl

theorem isComb_iff {J : Type} [Fintype J] (s : J → SecA A F k) (b : J → F) (t : SecA A F k) :
    IsComb A s b t ↔ (SecM.ofSec A.A t : SecM A.A A.L (k : ℤ) (TFK (R := R) F)) =
      ∑ l, cF R (b l) • SecM.ofSec A.A (s l) := by
  have e : ∀ j, ((∑ l, cF R (b l) • SecM.ofSec A.A (s l) : SecM A.A A.L (k : ℤ) (TFK (R := R) F)).1 j) =
      ∑ l, liftFun A.A _ (cF R (b l)) * (s l).f j := fun j => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  exact ⟨fun H => Subtype.ext (funext fun j => (H j).trans (e j).symm),
    fun H j => (congrFun (congrArg Subtype.val H) j).trans (e j)⟩

omit [IsDomain R] in
theorem exists_rho (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) :
    ∃ ρ : SecM A.A A.L (k : ℤ) (TFK (R := R) F) ≃ₗ[Γ((TFK (R := R) F).left, ⊤)]
      SecM A.A A.L (k : ℤ) (TFK (R := R) F), ∀ s s' : SecA A F k,
      IsActOf A.A A.L k θ s s' ↔ ρ (SecM.ofSec A.A s) = SecM.ofSec A.A s' := by
  have hL := A.isLB
  obtain ⟨ρ, hρ⟩ := ThetaAct.exists_equiv hL θ
  refine ⟨ρ, fun s s' => ?_⟩
  rw [ThetaAct.isActOf_iff hL]
  exact ⟨fun H => ThetaAct.sv_ext hL fun y J hJ => (hρ _ _ _ _ _ hJ).trans (H y J hJ).symm,
      fun H y J hJ => H ▸ hρ _ _ _ _ _ hJ⟩

end GlobalTheory.SecComb

namespace GlobalTheory


open SecComb in
theorem secComb_thetaAct : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (J : Type) [Fintype J] (s : J → SecA A F k) (b : J → F), (∃ t, IsComb A s b t) ∧ (∀ t t', IsComb A s b t → IsComb A s b t' → t = t') ∧ (∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (s' : J → SecA A F k) t t', (∀ i, IsActOf A.A A.L k θ (s i) (s' i)) → IsComb A s b t → (IsActOf A.A A.L k θ t t' ↔ IsComb A s' b t')) ∧ (∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (t : SecA A F k), ∃! t', IsActOf A.A A.L k θ t t') ∧ ∀ (I : Type) [Fintype I] (M : I → J → F) (r : I → SecA A F k) (a : I → F) (t : SecA A F k), (∀ i, IsComb A s (M i) (r i)) → IsComb A r a t → IsComb A s (fun j => ∑ i, M i j * a i) t := by
  intro R _ _ A F _ _ k J _ s b
  refine ⟨⟨SecM.toSec A.A (∑ l, cF R (b l) • SecM.ofSec A.A (s l) : SecM A.A A.L (k : ℤ) (TFK (R := R) F)),
    (isComb_iff A _ _ _).2 rfl⟩, fun t t' h h' => ?_, fun θ s' t t' hs h => ?_, fun θ t => ?_,
    fun I _ M r a t hr h => ?_⟩
  · exact ofSec_inj A (((isComb_iff A _ _ _).1 h).trans ((isComb_iff A _ _ _).1 h').symm)
  · obtain ⟨ρ, hρ⟩ := exists_rho A θ
    have e := (congrArg ρ ((isComb_iff A _ _ _).1 h)).trans
      (equiv_sum ρ (fun l => cF R (b l)) _ _ fun i => (hρ _ _).1 (hs i))
    exact ⟨fun H => (isComb_iff A _ _ _).2 (((hρ _ _).1 H).symm.trans e),
      fun H => (hρ _ _).2 (e.trans ((isComb_iff A _ _ _).1 H).symm)⟩
  · obtain ⟨ρ, hρ⟩ := exists_rho A θ
    refine ⟨SecM.toSec A.A (ρ (SecM.ofSec A.A t)), (hρ _ _).2 rfl, fun t' h => ofSec_inj A ?_⟩
    exact ((hρ _ _).1 h).symm
  · rw [isComb_iff] at h ⊢
    rw [h]
    simp only [fun i => (isComb_iff A _ _ _).1 (hr i), Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have e : cF R (∑ i, M i j * a i) = ∑ i, cF R (M i j * a i) := map_sum _ _ _
    rw [e]
    exact Finset.sum_congr rfl fun i _ => (_root_.mul_comm _ _).trans (map_mul _ _ _).symm

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreSectionLinearCombExistsUniqueThetaActionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (J : Type) [Fintype J] (s : J → SecA A F k) (b : J → F), (∃ t, IsComb A s b t) ∧ (∀ t t', IsComb A s b t → IsComb A s b t' → t = t') ∧ (∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (s' : J → SecA A F k) t t', (∀ i, IsActOf A.A A.L k θ (s i) (s' i)) → IsComb A s b t → (IsActOf A.A A.L k θ t t' ↔ IsComb A s' b t')) ∧ (∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (t : SecA A F k), ∃! t', IsActOf A.A A.L k θ t t') ∧ ∀ (I : Type) [Fintype I] (M : I → J → F) (r : I → SecA A F k) (a : I → F) (t : SecA A F k), (∀ i, IsComb A s (M i) (r i)) → IsComb A r a t → IsComb A s (fun j => ∑ i, M i j * a i) t := by
  first | exact @GlobalTheory.secComb_thetaAct | exact GlobalTheory.secComb_thetaAct | (intros; apply GlobalTheory.secComb_thetaAct <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsogenousRetractPolarisedFiniteExt
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteIsAbelianSchemeDescends
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS GlobalTheory.FieldModel

namespace GlobalTheory

theorem exists_finite_isAbelianScheme_range {K : Type} [Field K] (B : Over (Sp K)) [GrpObj B]
    (hB : IsAbelianScheme B) :
    ∃ s : Set K, s.Finite ∧ ∀ (k₁ : Type) [Field k₁] (β : k₁ →+* K), s ⊆ Set.range β →
      ∃ (B₁ : Over (Sp k₁)) (_ : GrpObj B₁) (φ : B.left ⟶ B₁.left),
        IsAbelianScheme B₁ ∧ IsGrpPullback B B₁ (spMap β) φ := by
  have := hB.proper
  obtain ⟨s₀, hs₀⟩ := hasModel B
  let k₀ := Subfield.closure (s₀ : Set K)
  obtain ⟨B₀, φ₀, H₀⟩ := hs₀ k₀ k₀.subtype fun x hx => ⟨⟨x, Subfield.subset_closure hx⟩, rfl⟩
  have lB : LocallyOfFiniteType B.hom := inferInstance
  have pBB : IsProper (B ⊗ B).hom := inferInstanceAs (IsProper (pullback.fst B.hom B.hom ≫ B.hom))
  obtain ⟨sm, hm⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K _ _ _ _ _ _ _ (isPullback_sq H₀) H₀ inferInstance inferInstance lB μ[B]
  obtain ⟨si, hi⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K _ _ _ _ _ _ _ H₀ H₀ inferInstance inferInstance lB ι[B]
  obtain ⟨se, he⟩ := GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt k₀ K _ _ _ _ _ _ _ (isPullback_unit _) H₀
    (inferInstanceAs (QuasiCompact (𝟙 (Sp K)))) (inferInstanceAs (QuasiSeparated (𝟙 (Sp K)))) lB η[B]
  refine ⟨s₀ ∪ (sm ∪ (si ∪ se)), by simp, fun k₁ _ β hs => ?_⟩
  simp only [Set.union_subset_iff] at hs
  obtain ⟨b₀, bm, bi, be⟩ := hs
  obtain ⟨ρ, hρ⟩ := exists_factor β (s₀ : Set K) b₀
  obtain ⟨φ₁, eφ, H₁⟩ := exists_baseChange (spMap_comp hρ) H₀
  have P₁ : IsPullback (pullback.fst B₀.hom (spMap ρ)) ((Over.pullback (spMap ρ)).obj B₀).hom B₀.hom (spMap ρ) :=
    .of_hasPullback _ _
  obtain ⟨m₁, hm₁⟩ := hm k₁ ρ β hρ bm _ _ (sq H₁.w) _ φ₁ _ (isPullback_sq P₁) P₁ (sq_comp eφ _ _ _) eφ
    (isPullback_sq H₁).w H₁.w
  obtain ⟨i₁, hi₁⟩ := hi k₁ ρ β hρ bi _ _ φ₁ _ φ₁ _ P₁ P₁ eφ eφ H₁.w H₁.w
  obtain ⟨e₁, he₁⟩ := he k₁ ρ β hρ be (𝟙_ _) _ (spMap β) _ φ₁ _ (isPullback_unit (spMap ρ)) P₁ (spMap_comp hρ) eφ
    (isPullback_unit (spMap β)).w H₁.w
  obtain ⟨gB, ab, gpB⟩ := GlobalTheory.T.group_structure_descends_along_pullback k₁ K β B _ φ₁ hB H₁ m₁ i₁ e₁ _ (sq_fst _) (sq_snd _) hm₁ hi₁ he₁
  exact ⟨_, gB, φ₁, ab, gpB⟩

theorem exists_finite_isAbelianScheme_descends : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (B : Over (Sp Ω)) [GrpObj B], IsAbelianScheme B → ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (B₁ : Over (Sp L)) (_ : GrpObj B₁) (e : (Over.pullback (spMap (algebraMap L Ω))).obj B₁ ≅ B), IsAbelianScheme B₁ ∧ IsMonHom e.hom := by
  intro K Ω _ _ _ _ B _ hB
  obtain ⟨s, hs, h⟩ := exists_finite_isAbelianScheme_range B hB
  have := hs.to_subtype
  have : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  obtain ⟨B₁, g, φ, ab, gp⟩ := h _ (algebraMap (IntermediateField.adjoin K s) Ω)
    fun x hx => ⟨⟨x, IntermediateField.subset_adjoin K s hx⟩, rfl⟩
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback B₁ _) gp
  exact ⟨IntermediateField.adjoin K s, IntermediateField.finiteDimensional_adjoin
    fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, B₁, g, e, ab, he⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsogenousRetractPolarisedFiniteExt
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.FiniteData

def Pair {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (m : ℕ) : Prop :=
  ∃ (i : A ⟶ B) (r : B ⟶ A), IsMonHom i ∧ IsMonHom r ∧ r ≫ i = 𝟙 B ^ m

theorem Pair.of_iso {S : Scheme.{0}} {A B A' B' : Over S} [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B'] {m : ℕ}
    (a : A' ≅ A) (b : B' ≅ B) [IsMonHom a.hom] [IsMonHom b.hom] (h : Pair A B m) : Pair A' B' m := by
  obtain ⟨i, r, hi, hr, e⟩ := h
  refine ⟨a.hom ≫ i ≫ b.inv, b.hom ≫ r ≫ a.inv, inferInstance, inferInstance, ?_⟩
  have : (b.hom ≫ r ≫ a.inv) ≫ a.hom ≫ i ≫ b.inv = b.hom ≫ (r ≫ i) ≫ b.inv := by simp
  rw [this, e, MonObj.pow_comp, MonObj.comp_pow]
  simp

theorem isMonHom_symm {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (a : A ≅ B) [IsMonHom a.hom] :
    IsMonHom a.symm.hom := inferInstanceAs (IsMonHom a.inv)

theorem isMonHom_refl {S : Scheme.{0}} (A : Over S) [GrpObj A] : IsMonHom (Iso.refl A).hom :=
  inferInstanceAs (IsMonHom (𝟙 A))

attribute [local instance] isMonHom_symm isMonHom_refl

theorem relDim_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Over S) {g : ℕ} (h : SmoothOfRelativeDimension g X.hom) :
    SmoothOfRelativeDimension g ((Over.pullback f).obj X).hom :=
  (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) h

theorem Pair.pullback {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} [GrpObj A] [GrpObj B] {m : ℕ}
    (h : Pair A B m) : Pair ((Over.pullback f).obj A) ((Over.pullback f).obj B) m := by
  obtain ⟨i, r, hi, hr, e⟩ := h
  refine ⟨(Over.pullback f).map i, (Over.pullback f).map r, inferInstance, inferInstance, ?_⟩
  rw [← Functor.map_comp, e, ← CategoryTheory.Functor.map_id]
  exact map_pow ((Over.pullback f).homMonoidHom) _ _

theorem spMap_comp {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂) (g : R₂ →+* R₃)
    (h : R₁ →+* R₃) (e : ∀ x, g (f x) = h x) : spMap g ≫ spMap f = spMap h := by
  obtain rfl : h = g.comp f := RingHom.ext fun x => (e x).symm
  rw [← Spec.map_comp]; rfl

theorem Pair.descend {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    {A B : Over (Sp F)} {A' B' : Over (Sp Ω)} [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {m : ℕ} {φ : A'.left ⟶ A.left} {ψ : B'.left ⟶ B.left}
    (pA : IsGrpPullback A' A (spMap (algebraMap F Ω)) φ) (pB : IsGrpPullback B' B (spMap (algebraMap F Ω)) ψ)
    (h : Pair A' B' m) : ∃ (L : IntermediateField F Ω), FiniteDimensional F L ∧
      ∀ (L' : IntermediateField F Ω), L ≤ L' → ∀ (A'' B'' : Over (Sp L')) [GrpObj A''] [GrpObj B'']
        (φ' : A''.left ⟶ A.left) (ψ' : B''.left ⟶ B.left), IsGrpPullback A'' A (spMap (algebraMap F L')) φ' →
        IsGrpPullback B'' B (spMap (algebraMap F L')) ψ' → Pair A'' B'' m := by
  obtain ⟨a, ha, -⟩ := grpPullback_iso (isGrpPullback_pullback A _) pA
  obtain ⟨b, hb, -⟩ := grpPullback_iso (isGrpPullback_pullback B _) pB
  obtain ⟨i, r, hi, hr, e⟩ := h.of_iso a b
  obtain ⟨L, hL, i', r', hi', hr', e'⟩ := GlobalTheory.homPair_descends_to_finite F Ω A B hA hB i r hi hr
  refine ⟨L, hL, fun L' hle A'' B'' _ _ φ' ψ' qA qB => ?_⟩
  have h₁ : Pair ((Over.pullback (spMap (algebraMap F L))).obj A) ((Over.pullback (spMap (algebraMap F L))).obj B) m :=
    ⟨i', r', hi', hr', (e' m).2 e⟩
  let τ : L →+* L' := (IntermediateField.inclusion hle).toRingHom
  have hτ : spMap τ ≫ spMap (algebraMap F L) = spMap (algebraMap F L') := spMap_comp _ _ _ fun x => rfl
  obtain ⟨a', ha', -⟩ := grpPullback_iso qA
    (((isGrpPullback_pullback _ (spMap τ)).comp (isGrpPullback_pullback A _)).congr hτ rfl)
  obtain ⟨b', hb', -⟩ := grpPullback_iso qB
    (((isGrpPullback_pullback _ (spMap τ)).comp (isGrpPullback_pullback B _)).congr hτ rfl)
  exact (h₁.pullback (spMap τ)).of_iso a' b'

theorem finite_of_fg {o Ω₀ : Type} [Field o] [Field Ω₀] [Algebra o Ω₀] [Algebra.IsAlgebraic o Ω₀] (R₀ : Subalgebra o Ω₀)
    (hfg : R₀.FG) (hfr : ∀ x : Ω₀, ∃ a ∈ R₀, ∃ b ∈ R₀, x = a / b) : FiniteDimensional o Ω₀ := by
  have ht : R₀ = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hfr x
    rw [div_eq_mul_inv]
    exact R₀.mul_mem ha (R₀.inv_mem_of_algebraic (x := ⟨b, hb⟩) (Algebra.IsAlgebraic.isAlgebraic _))
  have : Algebra.FiniteType o Ω₀ := ⟨ht ▸ hfg⟩
  exact Algebra.IsIntegral.finite

theorem exists_pol_baseChange {S S' : Scheme.{0}} (f : S' ⟶ S) (P : Out.PolAV S)
    (h : letI := P.isAb.comm; GlobalTheory.ZH.HypS P.A P.L) :
    ∃ (P' : Out.PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ ∧
      (letI := P'.isAb.comm; GlobalTheory.ZH.HypS P'.A P'.L) := by
  obtain ⟨P', φ, hφ, hg, hm, t, ht⟩ := polBaseChange_holds S S' f P
  have gp : IsGrpPullback P'.A P.A f φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
    rfl⟩
  letI := P.isAb.comm
  letI := P'.isAb.comm
  exact ⟨P', φ, gp, GlobalTheory.SymBaseChange.hypS_baseChange S S' P.A P'.A f φ P.L P'.L P.isLB P'.isLB gp
    (LBIso.symm ⟨t, ht⟩) h⟩

theorem exists_finite_pairs {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    {A B : Over (Sp F)} {A' B' C' : Over (Sp Ω)} [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B'] [GrpObj C']
    (Q : Out.PolAV (Sp F)) (hQ : letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L)
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {m : ℕ} {φ : A'.left ⟶ A.left} {ψ : B'.left ⟶ B.left}
    {χ : C'.left ⟶ Q.A.left}
    (pA : IsGrpPullback A' A (spMap (algebraMap F Ω)) φ) (pB : IsGrpPullback B' B (spMap (algebraMap F Ω)) ψ)
    (pC : IsGrpPullback C' Q.A (spMap (algebraMap F Ω)) χ)
    (h : Pair A' B' m) (h' : Pair C' B' 1) : ∃ (L : IntermediateField F Ω) (Q' : Out.PolAV (Sp L)),
      FiniteDimensional F L ∧ (letI := Q'.isAb.comm; GlobalTheory.ZH.HypS Q'.A Q'.L) ∧
      Pair ((Over.pullback (spMap (algebraMap F L))).obj A) ((Over.pullback (spMap (algebraMap F L))).obj B) m ∧
      Pair Q'.A ((Over.pullback (spMap (algebraMap F L))).obj B) 1 := by
  obtain ⟨L₁, f₁, h₁⟩ := h.descend hA hB pA pB
  obtain ⟨L₂, f₂, h₂⟩ := h'.descend Q.isAb hB pC pB
  obtain ⟨Q', χ', gp, hS⟩ := exists_pol_baseChange (spMap (algebraMap F (L₁ ⊔ L₂ : IntermediateField F Ω))) Q hQ
  exact ⟨L₁ ⊔ L₂, Q', inferInstance, hS,
    h₁ _ le_sup_left _ _ _ _ (isGrpPullback_pullback _ _) (isGrpPullback_pullback _ _),
    h₂ _ le_sup_right _ _ _ _ gp (isGrpPullback_pullback _ _)⟩

theorem exists_finite_data (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (g : ℕ) (hg : SmoothOfRelativeDimension g A.hom) :
    ∃ (L : Type) (_ : Field L) (c : K →+* L) (B : Over (Sp L)) (_ : GrpObj B) (Q : Out.PolAV (Sp L)) (m : ℕ),
      c.Finite ∧ SmoothOfRelativeDimension g B.hom ∧ 1 ≤ m ∧ Pair ((Over.pullback (spMap c)).obj A) B m ∧
      Pair Q.A B 1 ∧ (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) := by
  let Ω := AlgebraicClosure K
  obtain ⟨B, _, M, i, r, m, hB, hgB, hM, hM₁, hM₂, hi, hr, hm, e⟩ :=
    GlobalTheory.SS.PrincIsog.exists_isogeny_kTriv Ω ((Over.pullback (spMap (algebraMap K Ω))).obj A) g (isAbelianScheme_pullback_obj _ A hA) (relDim_pullback _ A hg)
  obtain ⟨Q, i', r', hQ, hi', hr', e'⟩ := GlobalTheory.EighthPowerFactor.exists_polAV_hypS_retract Ω B g hB hgB M hM hM₁ hM₂
  obtain ⟨L₁, f₁, B₁, _, eB, hB₁, heB⟩ := GlobalTheory.exists_finite_isAbelianScheme_descends K Ω B hB
  have lev := GlobalTheory.nonempty_level_of_isAlgClosed Ω Q 1 (Units.map (algebraMap L₁ Ω).toMonoidHom 1) (by simp)
    (by rw [map_one]; exact IsPrimitiveRoot.one)
  obtain ⟨F, _, _, j, R₀, Q₀, χ, hfg, hfr, -, pC, hQ₀, -⟩ := GlobalTheory.SymLevelDescent.descends_to_fg_field L₁ Ω Q 1 1 hQ lev
  letI : Algebra F Ω := j.toRingHom.toAlgebra
  haveI : IsScalarTower L₁ F Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Algebra.IsAlgebraic L₁ Ω := Algebra.IsAlgebraic.tower_top (K := K) L₁
  haveI : Algebra.IsAlgebraic L₁ F := Algebra.IsAlgebraic.of_injective j j.toRingHom.injective
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := L₁) F
  have f₂ : FiniteDimensional L₁ F := finite_of_fg R₀ hfg hfr
  let c₀ : K →+* F := (algebraMap L₁ F).comp (algebraMap K L₁)
  have pB₁ : IsGrpPullback B B₁ (spMap (algebraMap L₁ Ω)) _ :=
    ((isGrpPullback_of_iso eB.symm).comp (isGrpPullback_pullback B₁ _)).congr (Category.id_comp _) rfl
  have hgB₁ : SmoothOfRelativeDimension g B₁.hom :=
    (GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend L₁ Ω _ B₁ B _ pB₁ hB).2 g hgB
  obtain ⟨a, ha, -⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap (algebraMap K Ω)))
    (((isGrpPullback_pullback _ (spMap (algebraMap F Ω))).comp (isGrpPullback_pullback A (spMap c₀))).congr
      (spMap_comp _ _ _ fun x => j.commutes (algebraMap K L₁ x)) rfl)
  obtain ⟨b, hb, -⟩ := grpPullback_iso pB₁
    (((isGrpPullback_pullback _ (spMap (algebraMap F Ω))).comp
      (isGrpPullback_pullback B₁ (spMap (algebraMap L₁ F)))).congr (spMap_comp _ _ _ fun x => j.commutes x) rfl)
  have P₁ : Pair _ B m := ⟨i, r, hi, hr, e⟩
  have P₂ : Pair Q.A B 1 := ⟨r', i', hr', hi', by rw [e', pow_one]⟩
  obtain ⟨L, Q', f₃, hQ', P₃, P₄⟩ := exists_finite_pairs Q₀ hQ₀ (isAbelianScheme_pullback_obj (spMap c₀) A hA)
    (isAbelianScheme_pullback_obj (spMap (algebraMap L₁ F)) B₁ hB₁) (isGrpPullback_pullback _ _)
    (isGrpPullback_pullback _ _) pC (P₁.of_iso a.symm b.symm) (P₂.of_iso (Iso.refl _) b.symm)
  obtain ⟨a', ha', -⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap ((algebraMap F L).comp c₀)))
    (((isGrpPullback_pullback _ (spMap (algebraMap F L))).comp (isGrpPullback_pullback A (spMap c₀))).congr
      (spMap_comp _ _ _ fun x => rfl) rfl)
  exact ⟨L, inferInstance, (algebraMap F L).comp c₀, _, inferInstance, Q', m,
    (RingHom.finite_algebraMap.2 f₃).comp ((RingHom.finite_algebraMap.2 f₂).comp (RingHom.finite_algebraMap.2 f₁)),
    relDim_pullback _ _ (relDim_pullback _ _ hgB₁), hm, P₃.of_iso a' (Iso.refl _), P₄, hQ'⟩

theorem exists_isogenous_retract : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (B : Over (Sp L)) (_ : GrpObj B) (Q : Out.PolAV (Sp L)) (g m : ℕ) (i : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ B) (r : B ⟶ (Over.pullback (spMap (algebraMap K L))).obj A) (i' : B ⟶ Q.A) (r' : Q.A ⟶ B), GlobalTheory.AbLaw.IsProjBy ((Over.pullback (spMap (algebraMap K L))).obj A).hom ∧ SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap K L))).obj A).hom ∧ SmoothOfRelativeDimension g B.hom ∧ IsMonHom i ∧ IsMonHom r ∧ 1 ≤ m ∧ r ≫ i = 𝟙 _ ^ m ∧ IsMonHom i' ∧ IsMonHom r' ∧ i' ≫ r' = 𝟙 B ∧ (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) := by
  intro K _ _ A _ hA
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim K A hA
  obtain ⟨L₀, _, _, f₀, hP⟩ := GlobalTheory.ProjFinite.exists_finite_isProjBy K A hA
  haveI : CharZero L₀ := charZero_of_injective_algebraMap (algebraMap K L₀).injective
  obtain ⟨L, _, c, B, _, Q, m, hc, hgB, hm, P₁, ⟨r', i', hr', hi', e'⟩, hQ⟩ := exists_finite_data L₀ _
    (isAbelianScheme_pullback_obj (spMap (algebraMap K L₀)) A hA) g
    (relDim_pullback _ _ hg)
  letI : Algebra K L := (c.comp (algebraMap K L₀)).toAlgebra
  have f : FiniteDimensional K L := hc.comp (RingHom.finite_algebraMap.2 f₀)
  obtain ⟨a, ha, -⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap (algebraMap K L)))
    (((isGrpPullback_pullback _ (spMap c)).comp (isGrpPullback_pullback A (spMap (algebraMap K L₀)))).congr
      (spMap_comp _ _ _ fun x => rfl) rfl)
  obtain ⟨i, r, hi, hr, e⟩ := P₁.of_iso a (Iso.refl _)
  have gp := ((isGrpPullback_of_iso a).comp (isGrpPullback_pullback _ (spMap c))).congr (Category.id_comp _) rfl
  exact ⟨L, inferInstance, inferInstance, f, B, inferInstance, Q, g, m, i, r, i', r',
    GlobalTheory.AbLaw.isProjBy_baseChange L₀ L c _ _ _ _ _ gp.1 hP,
    relDim_pullback _ _ hg, hgB, hi, hr, hm, e, hi', hr',
    by rw [e', pow_one], hQ⟩

end GlobalTheory.FiniteData
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsogenousRetractPolarisedFiniteExtStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isogenous_retract_polarised_finiteExt : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (B : Over (Sp L)) (_ : GrpObj B) (Q : Out.PolAV (Sp L)) (g m : ℕ) (i : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ B) (r : B ⟶ (Over.pullback (spMap (algebraMap K L))).obj A) (i' : B ⟶ Q.A) (r' : Q.A ⟶ B), GlobalTheory.AbLaw.IsProjBy ((Over.pullback (spMap (algebraMap K L))).obj A).hom ∧ SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap K L))).obj A).hom ∧ SmoothOfRelativeDimension g B.hom ∧ IsMonHom i ∧ IsMonHom r ∧ 1 ≤ m ∧ r ≫ i = 𝟙 _ ^ m ∧ IsMonHom i' ∧ IsMonHom r' ∧ i' ≫ r' = 𝟙 B ∧ (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) := by
  first | exact @GlobalTheory.FiniteData.exists_isogenous_retract | exact GlobalTheory.FiniteData.exists_isogenous_retract | (intros; apply GlobalTheory.FiniteData.exists_isogenous_retract <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisActionTorsionPairingTameFixedPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisActionTorsionPairingTameFixedPoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

section
variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]

noncomputable def galSpecHom (τ : Ω ≃ₐ[K] Ω) :
    Over.mk (spMap (algebraMap K Ω)) ⟶ Over.mk (spMap (algebraMap K Ω)) :=
  Over.homMk (spMap τ.toRingEquiv.toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact τ.commutes c)

theorem galSpecHom_one : galSpecHom (1 : Ω ≃ₐ[K] Ω) = 𝟙 _ := by
  ext1
  exact Spec.map_id _

theorem galSpecHom_mul (τ τ' : Ω ≃ₐ[K] Ω) :
    galSpecHom (τ * τ') = galSpecHom τ ≫ galSpecHom τ' := by
  ext1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

noncomputable def galPointAct (A : Over (Sp K)) [MonObj A] :
    (Ω ≃ₐ[K] Ω) →* MulAut (Over.mk (spMap (algebraMap K Ω)) ⟶ A) where
  toFun τ :=
    { toFun := fun x => galSpecHom τ ≫ x
      invFun := fun x => galSpecHom τ⁻¹ ≫ x
      left_inv := fun x => by
        simp only [← Category.assoc, ← galSpecHom_mul, inv_mul_cancel, galSpecHom_one,
          Category.id_comp]
      right_inv := fun x => by
        simp only [← Category.assoc, ← galSpecHom_mul, mul_inv_cancel, galSpecHom_one,
          Category.id_comp]
      map_mul' := fun x y => MonObj.comp_mul _ _ _ }
  map_one' := by
    ext1 x
    change galSpecHom 1 ≫ x = x
    rw [galSpecHom_one, Category.id_comp]
  map_mul' τ τ' := by
    ext1 x
    change galSpecHom (τ * τ') ≫ x = galSpecHom τ ≫ galSpecHom τ' ≫ x
    rw [galSpecHom_mul, Category.assoc]

theorem galPointAct_left (A : Over (Sp K)) [MonObj A] (τ : Ω ≃ₐ[K] Ω)
    (x : Over.mk (spMap (algebraMap K Ω)) ⟶ A) :
    (galPointAct A τ x).left = spMap τ.toRingEquiv.toRingHom ≫ x.left := rfl

theorem galPointAct_eq_of_agree (A : Over (Sp K)) [MonObj A] (L : IntermediateField K Ω)
    (τ τ' : Ω ≃ₐ[K] Ω) (h : ∀ c ∈ L, τ c = τ' c) (x : Over.mk (spMap (algebraMap K Ω)) ⟶ A)
    (y : Sp L ⟶ A.left) (hy : spMap (algebraMap L Ω) ≫ y = x.left) :
    galPointAct A τ x = galPointAct A τ' x := by
  ext1
  rw [galPointAct_left, galPointAct_left, ← hy, ← Category.assoc, ← Category.assoc]
  congr 1
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext c
  exact h c c.2

theorem algEquiv_mem_of_normal (L : IntermediateField K Ω) [Normal K L] (τ : Ω ≃ₐ[K] Ω)
    {c : Ω} (hc : c ∈ L) : τ c ∈ L := by
  have := AlgEquiv.restrictNormal_commutes τ L ⟨c, hc⟩
  change ((τ.restrictNormal L ⟨c, hc⟩ : L) : Ω) = τ c at this
  rw [← this]
  exact Subtype.prop _

theorem pow_tame_relation (L : IntermediateField K Ω) [Normal K L] (σ φ : Ω ≃ₐ[K] Ω) (q : ℕ)
    (h : ∀ c ∈ L, φ (σ c) = (σ ^ q) (φ c)) (N : ℕ) :
    ∀ c ∈ L, (φ ^ N * σ) c = (σ ^ q ^ N * φ ^ N) c := by
  have h1 : ∀ (a : ℕ), ∀ c ∈ L, φ ((σ ^ a) c) = (σ ^ (q * a)) (φ c) := by
    intro a
    induction a with
    | zero => intro c _; simp
    | succ a ih =>
      intro c hc
      rw [pow_succ', AlgEquiv.mul_apply, h _ (algEquiv_mem_of_normal L _ hc), ih c hc,
        ← AlgEquiv.mul_apply, ← pow_add, Nat.mul_succ, Nat.add_comm]
  induction N with
  | zero => intro c _; simp
  | succ N ih =>
    intro c hc
    have := ih c hc
    simp only [AlgEquiv.mul_apply] at this
    rw [pow_succ' φ, pow_succ' q]
    simp only [AlgEquiv.mul_apply]
    rw [this, h1 _ _ (algEquiv_mem_of_normal L _ hc)]

end

theorem galois_action_torsion_points : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l q : ℕ), l.Prime → (∀ (τ : Ω ≃ₐ[K] Ω) (x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → ∀ (σ φ : Ω ≃ₐ[K] Ω) (K' : Type) [Field K'] (j : K' →+* Ω), (∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → σ ζ = ζ ∧ φ ζ = ζ ^ q) → (∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∀ x ∈ L, φ (σ x) = (σ ^ q) (φ x) ∧ (σ x = x → x ∈ j.fieldRange)) → ∃ (e : ℕ → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → Ωˣ) (act : (Ω ≃ₐ[K] Ω) →* MulAut (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), (∀ τ x, (act τ x).left = spMap τ.toRingEquiv.toRingHom ≫ x.left) ∧ ((∀ n x x' y, x ^ l ^ n = 1 → x' ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (x * x') y = e n x y * e n x' y ∧ e n y x = (e n x y)⁻¹) ∧ (∀ n x y, x ^ l ^ (n + 1) = 1 → y ^ l ^ n = 1 → e (n + 1) x y = e n (x ^ l) y) ∧ (∀ n x, x ^ l ^ n = 1 → (∀ y, y ^ l ^ n = 1 → e n x y = 1) → x = 1)) ∧ (∀ N n x y, x ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (act σ x) (act σ y) = e n x y ∧ e n (act (φ ^ N) x) (act (φ ^ N) y) = e n x y ^ (q ^ N)) ∧ (∀ N n x, x ^ l ^ n = 1 → act (φ ^ N) (act σ x) = (act σ)^[q ^ N] (act (φ ^ N) x)) ∧ ∀ n x, x ^ l ^ n = 1 → act σ x = x → ∃ y : Sp K' ⟶ P.A.left, spMap j ≫ y = x.left := by
  intro K _ _ P Ω _ _ _ l q hl hrat σ φ K' _ j hζ hL
  obtain ⟨-, ⟨e, he, hgal⟩, hfield⟩ := GlobalTheory.T.torsion_points_polarised_abelianVariety_galois K P Ω l hl
  have hφ : ∀ (m N : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → (φ ^ N) ζ = ζ ^ q ^ N := by
    intro m N ζ h
    induction N with
    | zero => simp
    | succ N ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, (hζ m ζ h).2, ← pow_mul, pow_succ']
  refine ⟨e, galPointAct P.A, fun τ x => rfl, he, ?_, ?_, ?_⟩
  · intro N n x y hx hy
    obtain ⟨h1, h2⟩ := hgal σ n x y _ _ hx hy (galPointAct_left _ σ x) (galPointAct_left _ σ y)
    obtain ⟨-, h3⟩ := hgal (φ ^ N) n x y _ _ hx hy (galPointAct_left _ _ x)
      (galPointAct_left _ _ y)
    refine ⟨Units.ext ?_, Units.ext ?_⟩
    · rw [h2, (hζ n _ h1).1]
    · rw [h3, hφ n N _ h1, Units.val_pow_eq_pow_val]
  · intro N n x hx
    obtain ⟨L, hfin, hnorm, hp, hpts⟩ := hfield hrat n
    obtain ⟨y, hy⟩ := hpts x hx
    have := galPointAct_eq_of_agree P.A L _ _
      (pow_tame_relation L σ φ q (fun c hc => (hL L hfin hnorm hp c hc).1) N) x y hy
    rw [map_mul, map_mul, map_pow (galPointAct P.A) σ] at this
    rw [← MulAut.mul_apply, this, MulAut.mul_apply]
    generalize galPointAct P.A (φ ^ N) x = z
    generalize q ^ N = k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, Function.iterate_succ_apply']
  · intro n x hx hfix
    obtain ⟨L, hfin, hnorm, hp, hpts⟩ := hfield hrat n
    obtain ⟨E, hE1, hE2, -⟩ := exists_fieldOfValues P.A.left Ω x.left
    have hEL := (hE2 L (algebraMap L Ω)).2 (hpts x hx)
    have hσ := (hE1 σ.toRingEquiv.toRingHom (RingHom.id Ω)).1 (by
      rw [← galPointAct_left, hfix]
      exact (Category.id_comp _).symm.trans (congrArg (· ≫ x.left) (Spec.map_id _).symm))
    refine (hE2 K' j).1 fun c hc => ?_
    obtain ⟨d, rfl⟩ := hEL hc
    exact (hL L hfin hnorm hp _ d.2).2 (hσ _ hc)

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisActionTorsionPairingTameFixedPointsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_action_torsion_pairing_tame_fixedPoints : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l q : ℕ), l.Prime → (∀ (τ : Ω ≃ₐ[K] Ω) (x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → ∀ (σ φ : Ω ≃ₐ[K] Ω) (K' : Type) [Field K'] (j : K' →+* Ω), (∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → σ ζ = ζ ∧ φ ζ = ζ ^ q) → (∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∀ x ∈ L, φ (σ x) = (σ ^ q) (φ x) ∧ (σ x = x → x ∈ j.fieldRange)) → ∃ (e : ℕ → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → Ωˣ) (act : (Ω ≃ₐ[K] Ω) →* MulAut (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), (∀ τ x, (act τ x).left = spMap τ.toRingEquiv.toRingHom ≫ x.left) ∧ ((∀ n x x' y, x ^ l ^ n = 1 → x' ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (x * x') y = e n x y * e n x' y ∧ e n y x = (e n x y)⁻¹) ∧ (∀ n x y, x ^ l ^ (n + 1) = 1 → y ^ l ^ n = 1 → e (n + 1) x y = e n (x ^ l) y) ∧ (∀ n x, x ^ l ^ n = 1 → (∀ y, y ^ l ^ n = 1 → e n x y = 1) → x = 1)) ∧ (∀ N n x y, x ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (act σ x) (act σ y) = e n x y ∧ e n (act (φ ^ N) x) (act (φ ^ N) y) = e n x y ^ (q ^ N)) ∧ (∀ N n x, x ^ l ^ n = 1 → act (φ ^ N) (act σ x) = (act σ)^[q ^ N] (act (φ ^ N) x)) ∧ ∀ n x, x ^ l ^ n = 1 → act σ x = x → ∃ y : Sp K' ⟶ P.A.left, spMap j ≫ y = x.left := by
  first | exact @GlobalTheory.SS.galois_action_torsion_points | exact GlobalTheory.SS.galois_action_torsion_points | (intros; apply GlobalTheory.SS.galois_action_torsion_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrobeniusCountsIntegralTorsionSpecialFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrobeniusCountsIntegralTorsionSpecialFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.SpecialCount

theorem transfer {M N : Type} [CommGroup M] [Group N] (H : Subgroup M) (r : H →* N) (Φ : MulAut M)
    (φ : ℕ → N → N) (hφ : ∀ (j : ℕ) (x : H), ∃ h : Φ^[j] x ∈ H, r ⟨_, h⟩ = φ j (r x)) (l e : ℕ)
    (hinj : ∀ n (x : H), x ^ l ^ n = 1 → r x = 1 → x = 1) (V : Subgroup N)
    (hV : ∀ x ∈ V, φ 1 x = x ^ e) (hfin : ∀ n, Finite {x : N // x ^ l ^ n = 1}) (Q : Polynomial ℤ)
    (hQ : ∀ (x : N) n, x ^ l ^ n = 1 →
      ((List.range (Q.natDegree + 1)).map fun j => φ j x ^ Q.coeff j).prod ∈ V) :
    ∃ U : Subgroup M,
      (∀ n, Nat.card {x : H // x ^ l ^ n = 1} ≤ Nat.card {x : N // x ^ l ^ n = 1} ∧
        Nat.card {x : U // x ^ l ^ n = 1} ≤ Nat.card {x : V // x ^ l ^ n = 1}) ∧
      (∀ n, ∀ x ∈ U, x ^ l ^ n = 1 → Φ x = x ^ e) ∧
      ∀ n, ∀ x ∈ H, x ^ l ^ n = 1 → ∏ j ∈ Finset.range (Q.natDegree + 1), (Φ^[j] x) ^ Q.coeff j ∈ U := by
  have inj : ∀ n (x y : H), x ^ l ^ n = 1 → y ^ l ^ n = 1 → r x = r y → x = y := by
    intro n x y hx hy h
    have := hinj n (x * y⁻¹) (by rw [mul_pow, inv_pow, hx, hy]; simp) (by rw [map_mul, map_inv, h]; simp)
    exact mul_inv_eq_one.1 this
  have memU : ∀ x : M, x ∈ (V.comap r).map H.subtype ↔ ∃ h : x ∈ H, r ⟨x, h⟩ ∈ V := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨h, hx⟩
      exact ⟨⟨x, h⟩, hx, rfl⟩
  refine ⟨(V.comap r).map H.subtype, fun n => ⟨?_, ?_⟩, fun n x hx hn => ?_, fun n x hx hn => ?_⟩
  · have := hfin n
    refine Nat.card_le_card_of_injective
      (fun x => ⟨r x.1, by rw [← map_pow, x.2, map_one]⟩) fun x y h => ?_
    exact Subtype.ext (inj n _ _ x.2 y.2 (congrArg Subtype.val h))
  · have := hfin n
    have : Finite {x : V // x ^ l ^ n = 1} :=
      Finite.of_injective (β := {x : N // x ^ l ^ n = 1})
        (fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩) fun x y h =>
          Subtype.ext (Subtype.ext (by exact congrArg (fun z : {x : N // x ^ l ^ n = 1} => z.1) h))
    have tor : ∀ x : {x : (V.comap r).map H.subtype // x ^ l ^ n = 1},
        (⟨x.1.1, ((memU _).1 x.1.2).1⟩ : H) ^ l ^ n = 1 := fun x =>
      Subtype.ext (by exact congrArg (fun z : (V.comap r).map H.subtype => z.1) x.2)
    refine Nat.card_le_card_of_injective
      (fun x => ⟨⟨r ⟨x.1.1, ((memU _).1 x.1.2).1⟩, ((memU _).1 x.1.2).2⟩, Subtype.ext (by
        change r _ ^ l ^ n = 1
        rw [← map_pow, tor x, map_one])⟩) fun x y h => ?_
    have := inj n _ _ (tor x) (tor y) (congrArg (fun z => z.1.1) h)
    exact Subtype.ext (Subtype.ext (by exact congrArg (fun z : H => z.1) this))
  · obtain ⟨h, hv⟩ := (memU x).1 hx
    obtain ⟨h', e'⟩ := hφ 1 ⟨x, h⟩
    have := inj n ⟨_, h'⟩ (⟨x, h⟩ ^ e) (Subtype.ext (by
        change Φ x ^ l ^ n = 1
        rw [← map_pow, hn, map_one])) (Subtype.ext (by
        change (x ^ e) ^ l ^ n = 1
        rw [← pow_mul, mul_comm, pow_mul, hn, one_pow])) (by rw [e', hV _ hv, map_pow])
    exact congrArg Subtype.val this
  · choose h e' using fun j => hφ j ⟨x, hx⟩
    have hr := hQ (r ⟨x, hx⟩) n (by
      rw [← map_pow, show (⟨x, hx⟩ : H) ^ l ^ n = 1 from Subtype.ext hn, map_one])
    refine ⟨((List.range (Q.natDegree + 1)).map fun j => (⟨_, h j⟩ : H) ^ Q.coeff j).prod, ?_, ?_⟩
    · change r _ ∈ V
      rw [map_list_prod, List.map_map]
      have : (r ∘ fun j => (⟨_, h j⟩ : H) ^ Q.coeff j) = fun j => φ j (r ⟨x, hx⟩) ^ Q.coeff j := by
        funext j
        simp only [Function.comp, map_zpow, e']
      rw [this]
      exact hr
    · rw [map_list_prod, List.map_map]
      rfl

theorem exists_restrict {R Ω : Type} [CommRing R] [IsLocalRing R] [Field Ω] [Algebra R Ω]
    (hi : Function.Injective (algebraMap R Ω)) (q : ℕ) (ψ : Ω →+* Ω)
    (h : ∀ x : R, ∃ y : R, algebraMap R Ω y = ψ (algebraMap R Ω x) ∧ y - x ^ q ∈ IsLocalRing.maximalIdeal R) :
    ∃ σ : R →+* R, (∀ x, algebraMap R Ω (σ x) = ψ (algebraMap R Ω x)) ∧
      ∀ x, IsLocalRing.residue R (σ x) = IsLocalRing.residue R x ^ q := by
  choose f hf hf' using h
  refine ⟨{ toFun := f
            map_one' := hi (by simp [hf])
            map_mul' := fun x y => hi (by simp [hf])
            map_zero' := hi (by simp [hf])
            map_add' := fun x y => hi (by simp [hf]) }, hf, fun x => ?_⟩
  have := (IsLocalRing.residue_eq_zero_iff _).2 (hf' x)
  rw [map_sub, map_pow, sub_eq_zero] at this
  exact this

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem smConn_pullback {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] (h : SmConn G) :
    SmConn ((Over.pullback f).obj G) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · show Smooth (pullback.snd _ _); infer_instance
  · show IsSeparated (pullback.snd _ _); infer_instance
  · show QuasiCompact (pullback.snd _ _); infer_instance
  · show GeometricallyConnected (pullback.snd _ _); infer_instance

end GlobalTheory.SS.SpecialCount

namespace GlobalTheory.SS
open SpecialCount

theorem frobenius_on_integral_torsion : ∀ (W R Ω : Type) [CommRing W] [CommRing R] [IsDomain R] [IsLocalRing R] [Field Ω] [Algebra W R] [Algebra R Ω] [Algebra W Ω] [IsScalarTower W R Ω], Function.Injective (algebraMap R Ω) → IsAlgClosed (IsLocalRing.ResidueField R) → ∀ (p r l : ℕ), p.Prime → CharP (IsLocalRing.ResidueField R) p → 1 ≤ r → l.Prime → IsUnit (l : R) → (∀ c : IsLocalRing.ResidueField R, ∃ m, 1 ≤ m ∧ c ^ ((p ^ r) ^ m) = c) → ∀ ψ : Ω →+* Ω, (∀ w : W, ψ (algebraMap W Ω w) = algebraMap W Ω w) → (∀ x : R, ∃ y : R, algebraMap R Ω y = ψ (algebraMap R Ω x) ∧ y - x ^ (p ^ r) ∈ IsLocalRing.maximalIdeal R) → ∀ (G : Over (Sp W)) [GrpObj G], SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ L : LB ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G).left, AmpleCub ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G) L → ∀ (M : Type) [CommGroup M] (θ : M ≃* (Over.mk (spMap (algebraMap W Ω)) ⟶ G)) (Ψ : MulAut M), (∀ x, (θ (Ψ x)).left = spMap ψ ≫ (θ x).left) → ∃ (t a m C : ℕ) (Q : Polynomial ℤ) (H U : Subgroup M), 1 ≤ m ∧ (∀ x, x ∈ H ↔ ∃ s : Sp R ⟶ G.left, s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R Ω) ≫ s = (θ x).left) ∧ (∀ n, Nat.card {x : H // x ^ l ^ n = 1} ≤ C * l ^ (n * (t + 2 * a)) ∧ Nat.card {x : U // x ^ l ^ n = 1} ≤ C * l ^ (n * t)) ∧ (∀ β : ℂ, Polynomial.aeval β Q = 0 → ‖β‖ < (((p ^ r) ^ m : ℕ) : ℝ)) ∧ (∀ n, ∀ x ∈ U, x ^ l ^ n = 1 → (Ψ ^ m) x = x ^ ((p ^ r) ^ m)) ∧ (∀ n, ∀ x ∈ H, x ^ l ^ n = 1 → ∏ j ∈ Finset.range (Q.natDegree + 1), ((Ψ ^ m : MulAut M)^[j] x) ^ Q.coeff j ∈ U) ∧ (g ≤ t + a → Nonempty (TorusExtension ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G))) := by
  intro W R Ω _ _ _ _ _ _ _ _ _ hi hac p r l hp hch hr hl hlu hfin ψ hψW hψR G _ hG g hg L hL M _ θ Ψ hΨ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ, hσ, hσ'⟩ := exists_restrict hi (p ^ r) ψ hψR
  have hσW : ∀ w, σ (algebraMap W R w) = algebraMap W R w := fun w => hi (by
    rw [hσ, ← IsScalarTower.algebraMap_apply, hψW])
  obtain ⟨F, hF, hFx⟩ := GlobalTheory.SS.exists_frobG_baseChange W (IsLocalRing.ResidueField R)
    ((IsLocalRing.residue R).comp (algebraMap W R)) p r hr (fun w => by
      rw [RingHom.comp_apply, ← hσ', hσW]) hfin G hG
  have hlp : l ≠ p := by
    rintro rfl
    have := hlu.map (IsLocalRing.residue R)
    rw [map_natCast, CharP.cast_eq_zero] at this
    exact not_isUnit_zero this
  have hq : 2 ≤ p ^ r := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  obtain ⟨t, a, m, C, Q, V, hm, hroot, hV, hcount, hQ, hT⟩ := GlobalTheory.SS.frobenius_on_torsion _ p l hl hlp _
    (smConn_pullback _ G hG) g (by
      show SmoothOfRelativeDimension g (pullback.snd _ _)
      exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback _ _) hg) L hL F (p ^ r) hq hF
  obtain ⟨H₀, red, hH, hred, hinj⟩ := GlobalTheory.RedPts.exists_reduction W R Ω hi G hG
  let H : Subgroup M := H₀.comap θ.toMonoidHom
  let κ : H →* H₀ := (θ.toMonoidHom.subgroupComap H₀)
  have step : ∀ x : H, ∃ h : Ψ x ∈ H, red (κ ⟨_, h⟩) = red (κ x) ≫ F.asHom := by
    intro x
    obtain ⟨s, hs, hs'⟩ := (hH _).1 x.2
    have a1 : (spMap σ ≫ s) ≫ G.hom = spMap (algebraMap W R) := by
      rw [Category.assoc, hs, sp_comp]
      congr 1
      exact RingHom.ext hσW
    have a2 : spMap (algebraMap R Ω) ≫ spMap σ ≫ s = (θ (Ψ x)).left := by
      rw [hΨ, ← Category.assoc, sp_comp, show (algebraMap R Ω).comp σ = ψ.comp (algebraMap R Ω) from
        RingHom.ext hσ, ← sp_comp, Category.assoc, hs']
      rfl
    have hx : Ψ x ∈ H := (hH _).2 ⟨_, a1, a2⟩
    refine ⟨hx, ?_⟩
    have b1 := hred (κ ⟨_, hx⟩) _ a1 a2
    have b2 := hred (κ x) s hs hs'
    have b3 := hFx (red (κ x)) (iterateFrobenius _ p r) (fun c => rfl)
    ext1
    apply pullback.hom_ext
    · refine b1.trans (Eq.trans ?_ b3.symm)
      erw [b2]
      rw [← Category.assoc, ← Category.assoc, sp_comp, sp_comp]
      congr 2
      exact RingHom.ext hσ'
    · exact (Over.w _).trans (Over.w _).symm
  have iter : ∀ (n : ℕ) (x : H), ∃ h : (Ψ ^ n) x ∈ H,
      red (κ ⟨_, h⟩) = red (κ x) ≫ (F ^ n).asHom := by
    intro n
    induction n with
    | zero => exact fun x => ⟨x.2, (Category.comp_id _).symm⟩
    | succ n ih =>
      intro x
      obtain ⟨h, e⟩ := step x
      obtain ⟨h', e'⟩ := ih ⟨_, h⟩
      rw [pow_succ, pow_succ]
      refine ⟨h', e'.trans ?_⟩
      rw [e, Category.assoc]
      rfl
  obtain ⟨U, hU1, hU2, hU3⟩ := transfer H (red.comp κ) (Ψ ^ m)
    (fun j x => x ≫ ((F ^ m) ^ j).asHom) (fun j x => by
      have e : (Ψ ^ m : MulAut M)^[j] x = (Ψ ^ (m * j)) x := by
        rw [pow_mul]
        generalize (x : M) = y
        induction j generalizing y with
        | zero => rfl
        | succ j ih => rw [pow_succ, Function.iterate_succ_apply, ih]; rfl
      rw [e, ← pow_mul]
      exact iter (m * j) x) l ((p ^ r) ^ m) (fun n x hx h => by
      have := hinj (l ^ n) (κ x) (by rw [Nat.cast_pow]; exact hlu.pow n)
        (by rw [← map_pow, hx, map_one]) h
      exact Subtype.ext (θ.injective ((congrArg Subtype.val this).trans (map_one θ).symm))) V
    (fun x hx => by rw [pow_one]; exact hV x hx) (fun n => (hcount n).1) Q hQ
  refine ⟨t, a, m, C, Q, H, U, hm, fun x => hH _, fun n => ⟨(hU1 n).1.trans (hcount n).2.1,
    (hU1 n).2.trans (hcount n).2.2⟩, fun β hβ => ?_, hU2, hU3, hT⟩
  rw [Nat.cast_pow]
  exact hroot β hβ

end GlobalTheory.SS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrobeniusCountsIntegralTorsionSpecialFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_counts_integral_torsion_specialFibre : ∀ (W R Ω : Type) [CommRing W] [CommRing R] [IsDomain R] [IsLocalRing R] [Field Ω] [Algebra W R] [Algebra R Ω] [Algebra W Ω] [IsScalarTower W R Ω], Function.Injective (algebraMap R Ω) → IsAlgClosed (IsLocalRing.ResidueField R) → ∀ (p r l : ℕ), p.Prime → CharP (IsLocalRing.ResidueField R) p → 1 ≤ r → l.Prime → IsUnit (l : R) → (∀ c : IsLocalRing.ResidueField R, ∃ m, 1 ≤ m ∧ c ^ ((p ^ r) ^ m) = c) → ∀ ψ : Ω →+* Ω, (∀ w : W, ψ (algebraMap W Ω w) = algebraMap W Ω w) → (∀ x : R, ∃ y : R, algebraMap R Ω y = ψ (algebraMap R Ω x) ∧ y - x ^ (p ^ r) ∈ IsLocalRing.maximalIdeal R) → ∀ (G : Over (Sp W)) [GrpObj G], SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ L : LB ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G).left, AmpleCub ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G) L → ∀ (M : Type) [CommGroup M] (θ : M ≃* (Over.mk (spMap (algebraMap W Ω)) ⟶ G)) (Ψ : MulAut M), (∀ x, (θ (Ψ x)).left = spMap ψ ≫ (θ x).left) → ∃ (t a m C : ℕ) (Q : Polynomial ℤ) (H U : Subgroup M), 1 ≤ m ∧ (∀ x, x ∈ H ↔ ∃ s : Sp R ⟶ G.left, s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R Ω) ≫ s = (θ x).left) ∧ (∀ n, Nat.card {x : H // x ^ l ^ n = 1} ≤ C * l ^ (n * (t + 2 * a)) ∧ Nat.card {x : U // x ^ l ^ n = 1} ≤ C * l ^ (n * t)) ∧ (∀ β : ℂ, Polynomial.aeval β Q = 0 → ‖β‖ < (((p ^ r) ^ m : ℕ) : ℝ)) ∧ (∀ n, ∀ x ∈ U, x ^ l ^ n = 1 → (Ψ ^ m) x = x ^ ((p ^ r) ^ m)) ∧ (∀ n, ∀ x ∈ H, x ^ l ^ n = 1 → ∏ j ∈ Finset.range (Q.natDegree + 1), ((Ψ ^ m : MulAut M)^[j] x) ^ Q.coeff j ∈ U) ∧ (g ≤ t + a → Nonempty (TorusExtension ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G))) := by
  first | exact @GlobalTheory.SS.frobenius_on_integral_torsion | exact GlobalTheory.SS.frobenius_on_integral_torsion | (intros; apply GlobalTheory.SS.frobenius_on_integral_torsion <;> assumption)
end
end
