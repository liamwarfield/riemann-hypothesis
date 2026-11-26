module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstLeadingOfAgreeDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryEqAdditiveLeadingTerms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryEqAdditiveLeadingTerms
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.CobLead

open CategoryTheory TensorProduct MvPowerSeries in
set_option autoImplicit false in
private lemma subst_constantCoeff_zero_and_linear_coeff_eq {R : Type} [CommRing R] {d : ℕ} {τ : Type}
    (w : Fin d ⊕ Fin d → MvPowerSeries τ R) (hw : ∀ s, constantCoeff (w s) = 0)
    (F G : MvPowerSeries (Fin d ⊕ Fin d) R)
    (hFG : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree ≤ 1 → coeff α F = coeff α G)
    (hG : constantCoeff G = 0) :
    constantCoeff (subst w F) = 0 ∧ constantCoeff (subst w G) = 0 ∧
      ∀ γ : τ →₀ ℕ, γ.degree = 1 → coeff γ (subst w F) = coeff γ (subst w G) := by
  have hlow : ∀ H : MvPowerSeries (Fin d ⊕ Fin d) R, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < 1 → coeff α H = 0) →
      constantCoeff (subst w H) = 0 := by
    intro H hH
    have h := (_root_.GlobalTheory.coeff_subst_leading R _ τ w w 1 H hw hw (fun _ _ _ => rfl) hH 0).1
      (by simp)
    rwa [coeff_zero_eq_constantCoeff_apply] at h
  have hG0 : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < 1 → coeff α G = 0 := by
    intro α hα
    have : α = 0 := (Finsupp.degree_eq_zero_iff α).mp (by omega)
    rw [this, coeff_zero_eq_constantCoeff_apply, hG]
  refine ⟨hlow F (fun α hα => by rw [hFG α hα.le]; exact hG0 α hα), hlow G hG0, ?_⟩
  intro γ hγ
  have hdiff := (_root_.GlobalTheory.coeff_subst_leading R _ τ w w 2 (F - G) hw hw (fun _ _ _ => rfl)
    (fun α hα => by rw [map_sub, hFG α (by omega), sub_self]) γ).1 (by omega)
  rw [subst_sub (hasSubst_of_constantCoeff_zero hw), map_sub, sub_eq_zero] at hdiff
  exact hdiff

open CategoryTheory TensorProduct MvPowerSeries in
set_option autoImplicit false in
theorem _root_.GlobalTheory.CobLead.cob_eq_additive_lead : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (N : ℕ), (∀ i (α : Fin d ⊕ Fin d →₀ ℕ), α.degree ≤ 1 → coeff α (μ i) = coeff α (_root_.GlobalTheory.Katz.addLaw R d i)) → (∀ f : MvPowerSeries (Fin d) R, (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) → ∀ γ : Fin d ⊕ Fin d →₀ ℕ, (γ.degree < N → coeff γ (_root_.GlobalTheory.Katz.cob1 μ f) = 0) ∧ (γ.degree ≤ N → coeff γ (_root_.GlobalTheory.Katz.cob1 μ f) = coeff γ (_root_.GlobalTheory.Katz.cob1 (_root_.GlobalTheory.Katz.addLaw R d) f))) ∧ ∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < N → coeff α c = 0) → ∀ γ : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, γ.degree ≤ N → coeff γ (_root_.GlobalTheory.Katz.cob2 μ c) = coeff γ (_root_.GlobalTheory.Katz.cob2 (_root_.GlobalTheory.Katz.addLaw R d) c) := by
  intro R _ d μ N hμ
  have hadd0 : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.addLaw R d i) = 0 := by
    intro i
    simp [_root_.GlobalTheory.Katz.addLaw]
  have hμ0 : ∀ i, constantCoeff (μ i) = 0 := by
    intro i
    rw [← coeff_zero_eq_constantCoeff_apply, hμ i 0 (by simp), coeff_zero_eq_constantCoeff_apply, hadd0]
  have hX : ∀ {ι κ : Type} (e : ι → κ) (s : ι), constantCoeff (X (e s) : MvPowerSeries κ R) = 0 :=
    fun _ _ => by simp
  refine ⟨fun f hf γ => ⟨fun hγ => ?_, fun hγ => ?_⟩, fun c hc γ hγ => ?_⟩
  · unfold _root_.GlobalTheory.Katz.cob1 _root_.GlobalTheory.Katz.inL _root_.GlobalTheory.Katz.inR
    rw [map_sub, map_sub,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ μ μ N f hμ0 hμ0 (fun _ _ _ => rfl) hf γ).1 hγ,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ _ _ N f (hX Sum.inl) (hX Sum.inl)
        (fun _ _ _ => rfl) hf γ).1 hγ,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ _ _ N f (hX Sum.inr) (hX Sum.inr)
        (fun _ _ _ => rfl) hf γ).1 hγ]
    simp
  · unfold _root_.GlobalTheory.Katz.cob1
    rw [map_sub, map_sub, map_sub, map_sub,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ μ (_root_.GlobalTheory.Katz.addLaw R d) N f hμ0 hadd0
        (fun i γ' hγ' => hμ i γ' hγ'.le) hf γ).2 hγ]
  · have hpts : ∀ {τ : Type} (a b : Fin d → MvPowerSeries τ R), (∀ s, constantCoeff (a s) = 0) →
        (∀ s, constantCoeff (b s) = 0) → ∀ i,
          constantCoeff (_root_.GlobalTheory.Katz.op μ a b i) = 0 ∧
          constantCoeff (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d) a b i) = 0 ∧
          ∀ γ' : τ →₀ ℕ, γ'.degree = 1 → coeff γ' (_root_.GlobalTheory.Katz.op μ a b i) =
            coeff γ' (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d) a b i) := by
      intro τ a b ha hb i
      exact subst_constantCoeff_zero_and_linear_coeff_eq (Sum.elim a b) (fun s => by cases s <;> simp [ha, hb])
        (μ i) (_root_.GlobalTheory.Katz.addLaw R d i) (hμ i) (hadd0 i)
    have hs1 : ∀ s, constantCoeff (_root_.GlobalTheory.Katz.x1 (R := R) (d := d) s) = 0 := fun s => by
      simp [_root_.GlobalTheory.Katz.x1]
    have hs2 : ∀ s, constantCoeff (_root_.GlobalTheory.Katz.x2 (R := R) (d := d) s) = 0 := fun s => by
      simp [_root_.GlobalTheory.Katz.x2]
    have hs3 : ∀ s, constantCoeff (_root_.GlobalTheory.Katz.x3 (R := R) (d := d) s) = 0 := fun s => by
      simp [_root_.GlobalTheory.Katz.x3]
    have h12 := hpts _ _ hs1 hs2
    have h23 := hpts _ _ hs2 hs3
    unfold _root_.GlobalTheory.Katz.cob2 _root_.GlobalTheory.Katz.at2
    rw [map_sub, map_add (f := _), map_sub, map_sub, map_add (f := _), map_sub,
      (_root_.GlobalTheory.coeff_subst_leading R _ _
        (Sum.elim (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1 _root_.GlobalTheory.Katz.x2)
          _root_.GlobalTheory.Katz.x3)
        (Sum.elim (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d) _root_.GlobalTheory.Katz.x1
          _root_.GlobalTheory.Katz.x2) _root_.GlobalTheory.Katz.x3) N c
        (fun s => by rcases s with s | s; exacts [(h12 s).1, hs3 s])
        (fun s => by rcases s with s | s; exacts [(h12 s).2.1, hs3 s])
        (fun s γ' hγ' => by rcases s with s | s; exacts [(h12 s).2.2 γ' hγ', rfl]) hc γ).2 hγ,
      (_root_.GlobalTheory.coeff_subst_leading R _ _
        (Sum.elim _root_.GlobalTheory.Katz.x1
          (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3))
        (Sum.elim _root_.GlobalTheory.Katz.x1 (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d)
          _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3)) N c
        (fun s => by rcases s with s | s; exacts [hs1 s, (h23 s).1])
        (fun s => by rcases s with s | s; exacts [hs1 s, (h23 s).2.1])
        (fun s γ' hγ' => by rcases s with s | s; exacts [rfl, (h23 s).2.2 γ' hγ']) hc γ).2 hγ]

end GlobalTheory.CobLead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryEqAdditiveLeadingTermsStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_eq_additive_leading_terms : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (N : ℕ), (∀ i (α : Fin d ⊕ Fin d →₀ ℕ), α.degree ≤ 1 → coeff α (μ i) = coeff α (addLaw R d i)) → (∀ f : MvPowerSeries (Fin d) R, (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) → ∀ γ : Fin d ⊕ Fin d →₀ ℕ, (γ.degree < N → coeff γ (cob1 μ f) = 0) ∧ (γ.degree ≤ N → coeff γ (cob1 μ f) = coeff γ (cob1 (addLaw R d) f))) ∧ ∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < N → coeff α c = 0) → ∀ γ : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, γ.degree ≤ N → coeff γ (cob2 μ c) = coeff γ (cob2 (addLaw R d) c) := by
  first | exact @GlobalTheory.CobLead.cob_eq_additive_lead | exact GlobalTheory.CobLead.cob_eq_additive_lead | (intros; apply GlobalTheory.CobLead.cob_eq_additive_lead <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeRootOfUnityEqOneOfGeometricPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeRootOfUnityEqOneOfGeometricPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.RootUnitGeom

theorem eq_one_of_pow_eq_one_of_isNilpotent {A : Type*} [CommRing A] {v : A} {k : ℕ}
    (hk : IsUnit (k : A)) (hv : v ^ k = 1) (hn : IsNilpotent (v - 1)) : v = 1 := by
  have hw : IsNilpotent (∑ i ∈ Finset.range k, (v ^ i - 1)) := by
    refine isNilpotent_sum fun i _ => ?_
    have : v ^ i - 1 = (∑ j ∈ Finset.range i, v ^ j) * (v - 1) := (geom_sum_mul v i).symm
    rw [this]
    exact mem_nilradical.1 (Ideal.mul_mem_left _ _ (mem_nilradical.2 hn))
  have hs : ∑ i ∈ Finset.range k, v ^ i = (k : A) + ∑ i ∈ Finset.range k, (v ^ i - 1) := by
    simp [Finset.sum_sub_distrib]
  have hu : IsUnit (∑ i ∈ Finset.range k, v ^ i) := by
    rw [hs]
    exact hw.isUnit_add_left_of_commute hk (Commute.all _ _)
  have h0 : (∑ i ∈ Finset.range k, v ^ i) * (v - 1) = 0 := by
    rw [geom_sum_mul, hv, sub_self]
  have : v - 1 = 0 := (hu.mul_right_eq_zero).1 h0
  exact sub_eq_zero.1 this

end GlobalTheory.RootUnitGeom

namespace GlobalTheory.RootUnitGeom

theorem fromSpecResidueField_appTop_comp (S : Scheme.{0}) (x : S) :
    (S.fromSpecResidueField x).appTop ≫ (Scheme.ΓSpecIso _).hom = S.evaluation ⊤ x trivial := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
  simp only [Category.assoc, Scheme.ΓSpecIso_naturality]
  have e : (homOfLE (le_top : (⊤ : (Spec (S.presheaf.stalk x)).Opens) ≤ ⊤)) = 𝟙 _ := rfl
  rw [e, op_id, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc]
  rfl

theorem evaluation_eq_one (R : Type) [CommRing R] (S : Scheme.{0}) (s : S ⟶ Sp R)
    (u : Γ(S, ⊤)ˣ)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β →
      Units.map x.appTop.hom.toMonoidHom u = 1) (q : S) :
    S.evaluation ⊤ q trivial (u : Γ(S, ⊤)) = 1 := by
  let K := AlgebraicClosure (S.residueField q)
  let f : S.residueField q ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap (S.residueField q) K)
  let x : Sp K ⟶ S := Spec.map f ≫ S.fromSpecResidueField q
  have hx : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := by
    simp [spMap]
  have h1 := h K x _ hx
  have h2 : x.appTop (u : Γ(S, ⊤)) = 1 := by
    have := congrArg Units.val h1
    simpa using this
  have e : x.appTop ≫ (Scheme.ΓSpecIso _).hom = S.evaluation ⊤ q trivial ≫ f := by
    simp only [x, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
    rw [← Category.assoc, fromSpecResidueField_appTop_comp]
  have h3 := congrArg (fun g => g (u : Γ(S, ⊤))) (congrArg (fun g => (CategoryTheory.ConcreteCategory.hom g : _ → _)) e)
  simp only [CategoryTheory.comp_apply, h2, map_one] at h3
  apply (algebraMap (S.residueField q) K).injective
  rw [map_one]
  exact h3.symm

end GlobalTheory.RootUnitGeom

namespace GlobalTheory.RootUnitGeom

theorem germ_isNilpotent (S : Scheme.{0}) (ε : Γ(S, ⊤)) (hε : S.basicOpen ε = ⊥) (q : S) :
    IsNilpotent (S.presheaf.germ ⊤ q trivial ε) := by
  obtain ⟨U, hU, hqU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens)
    (show q ∈ (⊤ : S.Opens) from trivial)
  have hb : S.basicOpen (S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ε) = ⊥ := by
    rw [Scheme.basicOpen_res, hε, inf_bot_eq]
  have hn := (Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact
    (IsAffineOpen.isCompact hU) _).2 hb
  have := hn.map (S.presheaf.germ U q hqU).hom
  rwa [TopCat.Presheaf.germ_res_apply] at this

end GlobalTheory.RootUnitGeom


open GlobalTheory.RootUnitGeom in
theorem GlobalTheory.rootOfUnity_eq_one_of_geom : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (s : S ⟶ Sp R) (k : ℕ)
    (u : Γ(S, ⊤)ˣ), IsUnit (k : R) → u ^ k = 1 →
    (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β →
      Units.map x.appTop.hom.toMonoidHom u = 1) → u = 1 := by
  intro R _ S s k u hk hu h
  have hε : S.basicOpen ((u : Γ(S, ⊤)) - 1) = ⊥ := by
    rw [Scheme.basicOpen_eq_bot_iff_forall_evaluation_eq_zero]
    intro x
    rw [map_sub, map_one, evaluation_eq_one R S s u h x.1, sub_self]
  ext1
  apply TopCat.Presheaf.section_ext S.sheaf ⊤
  intro q hq
  let φ : R →+* S.presheaf.stalk q :=
    (S.presheaf.germ ⊤ q trivial).hom.comp (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  have hk' : IsUnit (k : S.presheaf.stalk q) := by
    simpa [map_natCast] using hk.map φ
  have hv : (S.presheaf.germ ⊤ q trivial (u : Γ(S, ⊤))) ^ k = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, map_one]
  have hn : IsNilpotent (S.presheaf.germ ⊤ q trivial (u : Γ(S, ⊤)) - 1) := by
    have := germ_isNilpotent S _ hε q
    rwa [map_sub, map_one] at this
  have := eq_one_of_pow_eq_one_of_isNilpotent hk' hv hn
  change S.presheaf.germ ⊤ q trivial (u : Γ(S, ⊤)) = S.presheaf.germ ⊤ q trivial ((1 : Γ(S, ⊤)ˣ) : Γ(S, ⊤))
  rw [this, Units.val_one, map_one]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeRootOfUnityEqOneOfGeometricPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scheme_rootOfUnity_eq_one_of_geometric_points : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (s : S ⟶ Sp R) (k : ℕ) (u : Γ(S, ⊤)ˣ), IsUnit (k : R) → u ^ k = 1 → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β → Units.map x.appTop.hom.toMonoidHom u = 1) → u = 1 := by
  first | exact @GlobalTheory.rootOfUnity_eq_one_of_geom | exact GlobalTheory.rootOfUnity_eq_one_of_geom | (intros; apply GlobalTheory.rootOfUnity_eq_one_of_geom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawMapNatMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawMapNatMultiple
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.MapLaw

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem hasSubst_elim {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun i => by cases i with
    | inl i => exact hu i
    | inr i => exact hv i

theorem constantCoeff_powerSeriesEvalTwoGroups_eq_zero {c : MvPowerSeries (Fin d ⊕ Fin d) R} (hc : constantCoeff c = 0)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : constantCoeff (at2 c u v) = 0 := by
  unfold at2
  exact constantCoeff_subst_eq_zero (hasSubst_elim hu hv)
    (fun i => by cases i with
      | inl i => exact hu i
      | inr i => exact hv i) hc

theorem mvPowerSeriesMap_evalTwoGroups (r : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map r (at2 c u v) = at2 (map r c) (fun i => map r (u i)) (fun i => map r (v i)) := by
  unfold at2
  rw [map_subst (hasSubst_elim hu hv)]
  congr 1
  funext i
  cases i <;> rfl

theorem map_op (r : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    map r (op μ u v i) = op (fun j => map r (μ j)) (fun j => map r (u j)) (fun j => map r (v j)) i :=
  mvPowerSeriesMap_evalTwoGroups r (μ i) hu hv

theorem constantCoeff_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) : constantCoeff (op μ u v i) = 0 :=
  constantCoeff_powerSeriesEvalTwoGroups_eq_zero (hμ i) hu hv

end GlobalTheory.MapLaw

open GlobalTheory.MapLaw in
theorem GlobalTheory.isLaw_map_nmul : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ (S : Type) [CommRing S] (r : R →+* S), IsLaw (fun i => map r (μ i)) ∧ ∀ n i, constantCoeff (nmul μ n i) = 0 ∧ map r (nmul μ n i) = nmul (fun i => map r (μ i)) n i := by
  intro R _ d μ hμ S _ r
  have hX : ∀ {σ : Type} (i : σ), constantCoeff (X i : MvPowerSeries σ R) = 0 :=
    fun i => constantCoeff_X i
  have h0 : ∀ i : Fin d, constantCoeff (0 : MvPowerSeries (Fin d) R) = 0 := fun _ => map_zero _
  refine ⟨⟨fun i => ?_, ?_, fun i => ?_, ?_⟩, ?_⟩
  · rw [constantCoeff_map, hμ.const i, map_zero]
  · funext i
    have := congrArg (map r) (congrFun hμ.unit i)
    rw [map_op r μ (fun j => hX j) h0] at this
    simpa [map_X] using this
  · have := congrArg (map r) (hμ.comm i)
    unfold swap at this ⊢
    rw [mvPowerSeriesMap_evalTwoGroups r (μ i) (fun j => hX _) (fun j => hX _)] at this
    simpa [map_X] using this
  · have hx1 : ∀ j, constantCoeff (x1 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 :=
      fun j => hX _
    have hx2 : ∀ j, constantCoeff (x2 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 :=
      fun j => hX _
    have hx3 : ∀ j, constantCoeff (x3 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 :=
      fun j => hX _
    have m1 : (fun j => map r (x1 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) = x1 := by
      funext j; simp [x1, map_X]
    have m2 : (fun j => map r (x2 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) = x2 := by
      funext j; simp [x2, map_X]
    have m3 : (fun j => map r (x3 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) = x3 := by
      funext j; simp [x3, map_X]
    funext i
    have := congrArg (map r) (congrFun hμ.assoc i)
    rw [map_op r μ (constantCoeff_op hμ.const hx1 hx2) hx3,
      map_op r μ hx1 (constantCoeff_op hμ.const hx2 hx3)] at this
    have e12 : (fun j => map r (op μ x1 x2 j)) = op (fun j => map r (μ j)) x1 x2 := by
      funext j; rw [map_op r μ hx1 hx2, m1, m2]
    have e23 : (fun j => map r (op μ x2 x3 j)) = op (fun j => map r (μ j)) x2 x3 := by
      funext j; rw [map_op r μ hx2 hx3, m2, m3]
    rw [e12, e23, m1, m3] at this
    exact this
  · intro n
    induction n with
    | zero => intro i; simp [nmul]
    | succ n ih =>
      intro i
      have hc : ∀ j, constantCoeff (nmul μ n j) = 0 := fun j => (ih j).1
      have e : ∀ (m : ℕ) (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S), nmul ν (m + 1) =
          op ν (nmul ν m) (fun j => X j) := by
        intro m ν
        unfold nmul
        rw [Function.iterate_succ_apply']
      have e' : nmul μ (n + 1) = op μ (nmul μ n) (fun j => X j) := by
        unfold nmul
        rw [Function.iterate_succ_apply']
      rw [e', e]
      refine ⟨constantCoeff_op hμ.const hc (fun j => hX j) i, ?_⟩
      rw [map_op r μ hc (fun j => hX j)]
      have hn : (fun j => map r (nmul μ n j)) = nmul (fun i => map r (μ i)) n := funext fun j => (ih j).2
      rw [hn]
      simp only [map_X]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawMapNatMultipleStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ (S : Type) [CommRing S] (r : R →+* S), IsLaw (fun i => map r (μ i)) ∧ ∀ n i, constantCoeff (nmul μ n i) = 0 ∧ map r (nmul μ n i) = nmul (fun i => map r (μ i)) n i := by
  first | exact @GlobalTheory.isLaw_map_nmul | exact GlobalTheory.isLaw_map_nmul | (intros; apply GlobalTheory.isLaw_map_nmul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCoboundarySwapPullbackCommute
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCoboundarySwapPullbackCommute
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

namespace Katz

namespace CoefChange

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem mvPowerSeriesMap_evalTwoGroups (r : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map r (at2 c u v) = at2 (map r c) (fun i => map r (u i)) (fun i => map r (v i)) := by
  unfold at2
  rw [map_subst (hasSubst_of_constantCoeff_zero (fun j => by
    cases j with
    | inl i => exact hu i
    | inr i => exact hv i))]
  congr 1
  funext j
  cases j <;> rfl

theorem map_subst' (r : R →+* S) {σ : Type} [Finite σ] (a : σ → MvPowerSeries τ R)
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    map r (subst a f) = subst (fun i => map r (a i)) (map r f) := by
  rw [map_subst (hasSubst_of_constantCoeff_zero ha)]

theorem map_inL (r : R →+* S) (f : MvPowerSeries (Fin d) R) : map r (inL f) = inL (map r f) := by
  unfold inL
  rw [map_subst' r _ (fun _ => constantCoeff_X _)]
  congr 1
  funext i
  exact map_X r _

theorem map_inR (r : R →+* S) (f : MvPowerSeries (Fin d) R) : map r (inR f) = inR (map r f) := by
  unfold inR
  rw [map_subst' r _ (fun _ => constantCoeff_X _)]
  congr 1
  funext i
  exact map_X r _

theorem inL_const {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    constantCoeff (inL f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) hf

theorem inR_const {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    constantCoeff (inR f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) hf

end CoefChange


open CoefChange in
theorem map_cob_swap_pull : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (S : Type) [CommRing S] (r : R →+* S), (∀ f, map r (cob1 μ f) = cob1 (fun i => map r (μ i)) (map r f)) ∧ (∀ c, map r (cob2 μ c) = cob2 (fun i => map r (μ i)) (map r c)) ∧ (∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, map r (Katz.swap c) = Katz.swap (map r c)) ∧ (∀ f : MvPowerSeries (Fin d) R, lin (map r f) = fun i => r (lin f i)) ∧ ∀ φ : Fin d → MvPowerSeries (Fin d) R, (∀ i, constantCoeff (φ i) = 0) → (∀ c, map r (pull2 φ c) = pull2 (fun i => map r (φ i)) (map r c)) ∧ ∀ f : MvPowerSeries (Fin d) R, map r (subst φ f) = subst (fun i => map r (φ i)) (map r f) := by
  intro R _ d μ hμ S _ r
  have hX : ∀ {τ : Type} (i : τ), constantCoeff (X i : MvPowerSeries τ R) = 0 :=
    fun i => constantCoeff_X i
  have hop : ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      ∀ i, constantCoeff (op μ u v i) = 0 := by
    intro u v hu hv i
    unfold op at2
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (fun j => by
      cases j with
      | inl i => exact hu i
      | inr i => exact hv i)) (fun j => by
      cases j with
      | inl i => exact hu i
      | inr i => exact hv i) (hμ i)
  have mapop : ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      (fun i => map r (op μ u v i)) =
        op (fun i => map r (μ i)) (fun i => map r (u i)) (fun i => map r (v i)) := by
    intro u v hu hv
    funext i
    exact mvPowerSeriesMap_evalTwoGroups r (μ i) u v hu hv
  have mx1 : (fun i => map r ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = x1 := by
    funext i; exact map_X r _
  have mx2 : (fun i => map r ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = x2 := by
    funext i; exact map_X r _
  have mx3 : (fun i => map r ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = x3 := by
    funext i; exact map_X r _
  have h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => hX _
  have h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => hX _
  have h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => hX _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f
    unfold cob1
    rw [map_sub, map_sub, map_subst' r μ hμ, map_inL, map_inR]
  · intro c
    unfold cob2
    rw [map_sub, map_add (f := _), map_sub, mvPowerSeriesMap_evalTwoGroups r c _ _ h2 h3, mvPowerSeriesMap_evalTwoGroups r c _ _ (hop _ _ h1 h2) h3,
      mvPowerSeriesMap_evalTwoGroups r c _ _ h1 (hop _ _ h2 h3), mvPowerSeriesMap_evalTwoGroups r c _ _ h1 h2, mapop _ _ h1 h2,
      mapop _ _ h2 h3, mx1, mx2, mx3]
  · intro c
    unfold Katz.swap
    rw [mvPowerSeriesMap_evalTwoGroups r c _ _ (fun _ => hX _) (fun _ => hX _)]
    congr 1 <;> funext i <;> exact map_X r _
  · intro f
    funext i
    unfold lin
    rw [coeff_map]
  · intro φ hφ
    refine ⟨?_, fun f => map_subst' r φ hφ f⟩
    intro c
    unfold pull2
    rw [mvPowerSeriesMap_evalTwoGroups r c _ _ (fun i => inL_const (hφ i)) (fun i => inR_const (hφ i))]
    congr 1 <;> funext i
    · exact map_inL r (φ i)
    · exact map_inR r (φ i)

end Katz

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCoboundarySwapPullbackCommuteStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_coboundary_swap_pullback_commute : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (S : Type) [CommRing S] (r : R →+* S), (∀ f, map r (cob1 μ f) = cob1 (fun i => map r (μ i)) (map r f)) ∧ (∀ c, map r (cob2 μ c) = cob2 (fun i => map r (μ i)) (map r c)) ∧ (∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, map r (Katz.swap c) = Katz.swap (map r c)) ∧ (∀ f : MvPowerSeries (Fin d) R, lin (map r f) = fun i => r (lin f i)) ∧ ∀ φ : Fin d → MvPowerSeries (Fin d) R, (∀ i, constantCoeff (φ i) = 0) → (∀ c, map r (pull2 φ c) = pull2 (fun i => map r (φ i)) (map r c)) ∧ ∀ f : MvPowerSeries (Fin d) R, map r (subst φ f) = subst (fun i => map r (φ i)) (map r f) := by
  first | exact @GlobalTheory.Katz.map_cob_swap_pull | exact GlobalTheory.Katz.map_cob_swap_pull | (intros; apply GlobalTheory.Katz.map_cob_swap_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPTorsionIsModularFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPTorsionIsModularFamily
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma mem_tauPair_lattice_iff (τ : ℍ) (z : ℂ) :
    z ∈ (_root_.GlobalTheory.QFam.tauPair τ).lattice ↔ ∃ m n : ℤ, (m : ℂ) * τ + n = z := by
  rw [PeriodPair.mem_lattice]
  simp [_root_.GlobalTheory.QFam.tauPair]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma modularGroup_denom_eq (γ : SL(2, ℤ)) (τ : ℍ) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) ↑τ =
      ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
  simp [UpperHalfPlane.denom]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma modularGroup_denom_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
  rw [← modularGroup_denom_eq]
  exact UpperHalfPlane.denom_ne_zero _ τ

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma coe_modularGroup_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ • τ : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) /
      (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma exists_tors_vact_eq_denom_mul_tors_smul_add (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N)
    (γ : SL(2, ℤ)) (τ : ℍ) :
    ∃ l ∈ (_root_.GlobalTheory.QFam.tauPair τ).lattice,
      _root_.GlobalTheory.WpFam.tors N τ (_root_.GlobalTheory.WpFam.vact N x γ) =
        (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x + l := by
  have hv0 : _root_.GlobalTheory.WpFam.vact N x γ 0 =
      x 0 * ((γ 0 0 : ℤ) : ZMod N) + x 1 * ((γ 1 0 : ℤ) : ZMod N) := by
    simp [_root_.GlobalTheory.WpFam.vact, _root_.GlobalTheory.WpFam.vmul, _root_.GlobalTheory.WpFam.redGL, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two]
  have hv1 : _root_.GlobalTheory.WpFam.vact N x γ 1 =
      x 0 * ((γ 0 1 : ℤ) : ZMod N) + x 1 * ((γ 1 1 : ℤ) : ZMod N) := by
    simp [_root_.GlobalTheory.WpFam.vact, _root_.GlobalTheory.WpFam.vmul, _root_.GlobalTheory.WpFam.redGL, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two]
  set y := _root_.GlobalTheory.WpFam.vact N x γ
  have h0 : (N : ℤ) ∣ ((y 0).val : ℤ) - ((x 0).val * γ 0 0 + (x 1).val * γ 1 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [hv0]
  have h1 : (N : ℤ) ∣ ((y 1).val : ℤ) - ((x 0).val * γ 0 1 + (x 1).val * γ 1 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [hv1]
  obtain ⟨k, hk⟩ := h0
  obtain ⟨k', hk'⟩ := h1
  refine ⟨(k : ℂ) * τ + k', (mem_tauPair_lattice_iff τ _).2 ⟨k, k', rfl⟩, ?_⟩
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hD := modularGroup_denom_ne_zero γ τ
  have e0 := congrArg (fun t : ℤ => (t : ℂ)) hk
  have e1 := congrArg (fun t : ℤ => (t : ℂ)) hk'
  push_cast at e0 e1
  have hw : (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * ((γ • τ : ℍ) : ℂ) =
      ((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ) := by
    rw [coe_modularGroup_smul, mul_div_assoc', mul_div_cancel_left₀ _ hD]
  unfold _root_.GlobalTheory.WpFam.tors
  rw [mul_div_assoc', div_add' _ _ _ hN, div_left_inj' hN]
  linear_combination (τ : ℂ) * e0 + e1 - ((x 0).val : ℂ) * hw

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma isTauOf_tauPair_denom_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    _root_.ReciprocityTheory.ChartRestriction.L1.IsTauOf (_root_.GlobalTheory.QFam.tauPair τ) (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ))
      (γ • τ) := by
  have hD := modularGroup_denom_ne_zero γ τ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  have key : ∀ u v : ℤ, (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) *
      ((u : ℂ) * ((γ • τ : ℍ) : ℂ) + v) =
      ((u * γ 0 0 + v * γ 1 0 : ℤ) : ℂ) * τ + ((u * γ 0 1 + v * γ 1 1 : ℤ) : ℂ) := by
    intro u v
    rw [coe_modularGroup_smul]
    field_simp
    push_cast
    ring
  unfold _root_.ReciprocityTheory.ChartRestriction.L1.IsTauOf
  refine ⟨hD, fun z => ?_⟩
  rw [mem_tauPair_lattice_iff]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨m * γ 1 1 - n * γ 1 0, -(m * γ 0 1) + n * γ 0 0, ?_⟩
    have h1 : (m * γ 1 1 - n * γ 1 0) * γ 0 0 + (-(m * γ 0 1) + n * γ 0 0) * γ 1 0 = m := by
      linear_combination m * hdet
    have h2 : (m * γ 1 1 - n * γ 1 0) * γ 0 1 + (-(m * γ 0 1) + n * γ 0 0) * γ 1 1 = n := by
      linear_combination n * hdet
    rw [key, h1, h2]
  · rintro ⟨u, v, rfl⟩
    exact ⟨_, _, (key u v).symm⟩


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.isFam_wp_wpd : ∀ (N : ℕ) [NeZero N],
    _root_.GlobalTheory.QFam.IsFam (_root_.GlobalTheory.WpFam.vact N) 2
        (_root_.GlobalTheory.WpFam.wp N) ∧
      _root_.GlobalTheory.QFam.IsFam (_root_.GlobalTheory.WpFam.vact N) 3
        (_root_.GlobalTheory.WpFam.wpd N) := by
  intro N _
  constructor
  · intro x γ
    funext τ
    obtain ⟨l, hl, hP⟩ := exists_tors_vact_eq_denom_mul_tors_smul_add N x γ τ
    have hom := _root_.GlobalTheory.WpFam.homogeneity_of_isTauOf _ _ _ (isTauOf_tauPair_denom_smul γ τ)
    have hper : (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP
        ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x + l) =
        (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP
        ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x) :=
      (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP_add_coe _ ⟨l, hl⟩
    rw [ModularForm.SL_slash_apply, modularGroup_denom_eq]
    unfold _root_.GlobalTheory.WpFam.wp
    rw [hP, hper, hom.2.1, zpow_neg, zpow_ofNat]
    ring
  · intro x γ
    funext τ
    obtain ⟨l, hl, hP⟩ := exists_tors_vact_eq_denom_mul_tors_smul_add N x γ τ
    have hom := _root_.GlobalTheory.WpFam.homogeneity_of_isTauOf _ _ _ (isTauOf_tauPair_denom_smul γ τ)
    have hper : (_root_.GlobalTheory.QFam.tauPair τ).derivWeierstrassP
        ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x + l) =
        (_root_.GlobalTheory.QFam.tauPair τ).derivWeierstrassP
        ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x) :=
      (_root_.GlobalTheory.QFam.tauPair τ).derivWeierstrassP_add_coe _ ⟨l, hl⟩
    rw [ModularForm.SL_slash_apply, modularGroup_denom_eq]
    unfold _root_.GlobalTheory.WpFam.wpd
    rw [hP, hper, hom.2.2.1, zpow_neg, zpow_ofNat]
    ring

end GlobalTheory.WpFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPTorsionIsModularFamilyStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_torsion_isModularFamily : ∀ (N : ℕ) [NeZero N], IsFam (vact N) 2 (wp N) ∧ IsFam (vact N) 3 (wpd N) := by
  first | exact @GlobalTheory.WpFam.isFam_wp_wpd | exact GlobalTheory.WpFam.isFam_wp_wpd | (intros; apply GlobalTheory.WpFam.isFam_wp_wpd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsSecondKindFormPreservingGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsSecondKindFormPreservingGroup
noncomputable section

open Filter Topology Matrix

namespace GlobalTheory.ClosedMatGroup

section Banach

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem hasStrictFDerivAt_ofFn_prod {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∀ (d : ℕ) (f : Fin d → E → 𝔸) (f' : Fin d → E →L[ℝ] 𝔸) (x : E), (∀ i, f i x = 1) →
    (∀ i, HasStrictFDerivAt (f i) (f' i) x) →
    HasStrictFDerivAt (fun y => (List.ofFn fun i => f i y).prod) (∑ i, f' i) x := by
  intro d
  induction d with
  | zero =>
    intro f f' x _ _
    simpa using (hasStrictFDerivAt_const (1 : 𝔸) x)
  | succ d ih =>
    intro f f' x h1 hd
    have hr := ih (fun i => f i.succ) (fun i => f' i.succ) x (fun i => h1 _) (fun i => hd _)
    have hm := (hd 0).mul' hr
    simp only [List.ofFn_succ, List.prod_cons]
    refine hm.congr_fderiv ?_
    ext1 v
    simp [Fin.sum_univ_succ, h1, add_comm]

theorem exists_left_inv_ofFn_prod {S : Set 𝔸} (h1 : (1 : 𝔸) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) :
    ∀ (d : ℕ) (Y : Fin d → 𝔸), (∀ i, NormedSpace.exp (-Y i) ∈ S) →
      ∃ Q ∈ S, Q * (List.ofFn fun i => NormedSpace.exp (Y i)).prod = 1 := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  intro d
  induction d with
  | zero => intro Y _; exact ⟨1, h1, by simp⟩
  | succ d ih =>
    intro Y hY
    obtain ⟨Q, hQ, hQe⟩ := ih (fun i => Y i.succ) (fun i => hY _)
    refine ⟨Q * NormedSpace.exp (-Y 0), hm _ hQ _ (hY 0), ?_⟩
    rw [List.ofFn_succ, List.prod_cons]
    have e : NormedSpace.exp (-Y 0) * NormedSpace.exp (Y 0) = 1 := by
      rw [← NormedSpace.exp_add_of_commute (Commute.refl (Y 0)).neg_left, neg_add_cancel,
        NormedSpace.exp_zero]
    calc Q * NormedSpace.exp (-Y 0) * (NormedSpace.exp (Y 0) * (List.ofFn fun i => NormedSpace.exp (Y i.succ)).prod)
        = Q * (NormedSpace.exp (-Y 0) * NormedSpace.exp (Y 0)) * (List.ofFn fun i => NormedSpace.exp (Y i.succ)).prod := by
          simp only [mul_assoc]
      _ = 1 := by rw [e, mul_one, hQe]

end Banach

section Banach2

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem exists_coords_second_kind [FiniteDimensional ℝ 𝔸] {S : Set 𝔸} (hc : IsClosed S)
    (h1 : (1 : 𝔸) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (hi : ∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S) :
    ∃ (d : ℕ) (Z : Fin d → 𝔸) (s : 𝔸 → Fin d → ℝ), (∀ i, Z i ∈ lieSub S hc h1 hm) ∧
      Tendsto s (𝓝 1) (𝓝 0) ∧
      ∀ᶠ X in 𝓝 (1 : 𝔸), X ∈ S → X = (List.ofFn fun i => NormedSpace.exp (s X i • Z i)).prod := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  obtain ⟨W, hW⟩ := (lieSub S hc h1 hm).exists_isCompl
  let L := lieSub S hc h1 hm
  let d := Module.finrank ℝ L
  let bL := Module.finBasis ℝ L
  let Z : Fin d → 𝔸 := fun i => (bL i : 𝔸)
  have hZ : ∀ i, ∀ t : ℝ, NormedSpace.exp (t • Z i) ∈ S := fun i t => (bL i).2 t
  let c : 𝔸 →L[ℝ] (Fin d → ℝ) :=
    LinearMap.toContinuousLinearMap (bL.equivFun.toLinearMap ∘ₗ L.projectionOnto W hW)
  let p : 𝔸 →L[ℝ] 𝔸 := LinearMap.toContinuousLinearMap (L.projection W hW)
  have hpc : ∀ z, ∑ i, c z i • Z i = p z := by
    intro z
    show ∑ i, (bL.equivFun (L.projectionOnto W hW z)) i • (bL i : 𝔸) = ((L.projectionOnto W hW z : L) : 𝔸)
    conv_rhs => rw [← bL.sum_equivFun (L.projectionOnto W hW z)]
    rw [Submodule.coe_sum]
    rfl
  have hqW : ∀ z, z - p z ∈ W := fun z => by
    have h := Submodule.projection_add_projection_eq_self hW z
    have e : z - p z = W.projection _ hW.symm z := by
      rw [sub_eq_iff_eq_add']; exact h.symm
    rw [e]; exact Submodule.projection_apply_mem hW.symm z
  let P : 𝔸 → 𝔸 := fun z => (List.ofFn fun i => NormedSpace.exp (c z i • Z i)).prod
  let Φ : 𝔸 → 𝔸 := fun z => P z * NormedSpace.exp (z - p z)
  have hexp : HasStrictFDerivAt NormedSpace.exp (1 : 𝔸 →L[ℝ] 𝔸) (0 : 𝔸) := hasStrictFDerivAt_exp_zero
  have hf : ∀ i, HasStrictFDerivAt (fun z => NormedSpace.exp (c z i • Z i))
      ((1 : 𝔸 →L[ℝ] 𝔸).comp (((ContinuousLinearMap.proj i).comp c).smulRight (Z i))) 0 := fun i =>
    HasStrictFDerivAt.comp (0 : 𝔸) (g := NormedSpace.exp) (by rw [map_zero, Pi.zero_apply, zero_smul]; exact hexp)
      (((ContinuousLinearMap.proj i).comp c).smulRight (Z i)).hasStrictFDerivAt
  have hP := hasStrictFDerivAt_ofFn_prod d (fun i z => NormedSpace.exp (c z i • Z i)) _ 0
    (fun i => by simp) hf
  have h2 : HasStrictFDerivAt (fun z => NormedSpace.exp (z - p z))
      ((1 : 𝔸 →L[ℝ] 𝔸).comp (ContinuousLinearMap.id ℝ 𝔸 - p)) 0 :=
    HasStrictFDerivAt.comp (0 : 𝔸) (f := fun z => z - p z) (by rw [map_zero, sub_zero]; exact hexp)
      (ContinuousLinearMap.id ℝ 𝔸 - p).hasStrictFDerivAt
  have hP0 : P 0 = 1 := by simp [P]
  have h4 : HasStrictFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 := by
    refine (hP.mul' h2).congr_fderiv ?_
    ext1 z
    have e1 : (List.ofFn fun i => NormedSpace.exp ((0 : Fin d → ℝ) i • Z i)).prod = 1 := by simp
    simp [e1, hpc]
  have hΦ0 : Φ 0 = 1 := by
    show P 0 * NormedSpace.exp (0 - p 0) = 1
    rw [hP0, map_zero, sub_zero, NormedSpace.exp_zero, one_mul]
  let Ψ := h4.localInverse Φ _ 0
  have hΨ : Tendsto Ψ (𝓝 1) (𝓝 0) := by
    have h := h4.localInverse_tendsto
    rw [hΦ0] at h
    exact h
  have hR : ∀ᶠ X in 𝓝 (1 : 𝔸), Φ (Ψ X) = X := by
    have h := h4.eventually_right_inverse
    rw [hΦ0] at h
    exact h
  have hp0 : Tendsto p (𝓝 0) (𝓝 0) := by simpa using p.continuous.tendsto 0
  have hq0 : Tendsto (fun z => z - p z) (𝓝 0) (𝓝 (0 : 𝔸)) := by
    simpa using (tendsto_id (x := 𝓝 (0 : 𝔸))).sub hp0
  refine ⟨d, Z, fun X => c (Ψ X), fun i => (bL i).2, ?_, ?_⟩
  · have hc0 : Tendsto c (𝓝 0) (𝓝 0) := by simpa using c.continuous.tendsto 0
    exact hc0.comp hΨ
  · filter_upwards [hR, hΨ.eventually (hq0.eventually (eventually_eq_zero hc h1 hm hi hW.disjoint))]
      with X hX1 hX2 hXS
    obtain ⟨Q, hQ, hQe⟩ := exists_left_inv_ofFn_prod h1 hm d (fun i => c (Ψ X) i • Z i)
      (fun i => by rw [← neg_smul]; exact hZ i _)
    have hE : NormedSpace.exp (Ψ X - p (Ψ X)) = Q * X := by
      conv_rhs => rw [← hX1]
      show _ = Q * ((List.ofFn fun i => NormedSpace.exp (c (Ψ X) i • Z i)).prod * NormedSpace.exp (Ψ X - p (Ψ X)))
      rw [← mul_assoc, hQe, one_mul]
    have hw := hX2 (hqW _) (by rw [hE]; exact hm _ hQ _ hXS)
    calc X = Φ (Ψ X) := hX1.symm
      _ = _ := by
        show (List.ofFn fun i => NormedSpace.exp (c (Ψ X) i • Z i)).prod * NormedSpace.exp (Ψ X - p (Ψ X)) = _
        rw [hw, NormedSpace.exp_zero, mul_one]

end Banach2

theorem skew_of_exp_smul_mem {m : ℕ} (A Z : Matrix (Fin m) (Fin m) ℂ)
    (hZ : ∀ t : ℝ, NormedSpace.exp (t • Z) ∈ {X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}) :
    Zᴴ * A + A * Z = 0 := by
  let _ := Matrix.linftyOpNormedRing (n := Fin m) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin m) (α := ℂ)
  have _ : CompleteSpace (Matrix (Fin m) (Fin m) ℂ) := FiniteDimensional.complete ℝ _
  have e : ∀ t : ℝ, NormedSpace.exp (t • Zᴴ) * A * NormedSpace.exp (t • Z) = A := fun t => by
    have h := hZ t
    simp only [Set.mem_setOf_eq] at h
    rwa [← Matrix.exp_conjTranspose, conjTranspose_smul, star_trivial] at h
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Zᴴ) * A * NormedSpace.exp (t • Z))
      (Zᴴ * A + A * Z) 0 := by
    have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) Zᴴ (0 : ℝ)).mul_const A
    have h2 := h1.mul (hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ))
    simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at h2
    exact h2
  have hc : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Zᴴ) * A * NormedSpace.exp (t • Z)) 0 0 := by
    have h : (fun t : ℝ => NormedSpace.exp (t • Zᴴ) * A * NormedSpace.exp (t • Z)) = fun _ => A :=
      funext e
    rw [h]; exact hasDerivAt_const 0 A
  exact hd.unique hc

theorem coords_second_kind_unitary : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ), ∃ (d : ℕ)
    (Z : Fin d → Matrix (Fin m) (Fin m) ℂ) (s : Matrix (Fin m) (Fin m) ℂ → Fin d → ℝ),
    (∀ i, (Z i)ᴴ * A + A * Z i = 0) ∧
    Tendsto s (𝓝[{X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}] 1) (𝓝 0) ∧
    ∀ᶠ X in 𝓝[{X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}] 1,
      X = (List.ofFn fun i => NormedSpace.exp (s X i • Z i)).prod := by
  intro m A
  let S := {X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}
  have hc : IsClosed S :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  have h1 : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ S := by simp [S]
  have hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S := by
    intro a ha b hb
    simp only [S, Set.mem_setOf_eq] at ha hb ⊢
    rw [conjTranspose_mul]
    calc bᴴ * aᴴ * A * (a * b) = bᴴ * (aᴴ * A * a) * b := by simp only [Matrix.mul_assoc]
      _ = A := by rw [ha, hb]
  have hi : ∀ Z : Matrix (Fin m) (Fin m) ℂ, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S := by
    intro Z hZ
    simp only [S, Set.mem_setOf_eq] at hZ ⊢
    have hXY : NormedSpace.exp Z * NormedSpace.exp (-Z) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_right, add_neg_cancel,
        NormedSpace.exp_zero]
    calc (NormedSpace.exp (-Z))ᴴ * A * NormedSpace.exp (-Z)
        = (NormedSpace.exp (-Z))ᴴ * ((NormedSpace.exp Z)ᴴ * A * NormedSpace.exp Z) * NormedSpace.exp (-Z) := by
          rw [hZ]
      _ = (NormedSpace.exp Z * NormedSpace.exp (-Z))ᴴ * A * (NormedSpace.exp Z * NormedSpace.exp (-Z)) := by
          rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = A := by rw [hXY]; simp
  let _ := Matrix.linftyOpNormedRing (n := Fin m) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin m) (α := ℂ)
  have _ : CompleteSpace (Matrix (Fin m) (Fin m) ℂ) := FiniteDimensional.complete ℝ _
  obtain ⟨d, Z, s, hZ, hs, hev⟩ := exists_coords_second_kind hc h1 hm hi
  exact ⟨d, Z, s, fun i => skew_of_exp_smul_mem A (Z i) (hZ i), hs.mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_iff.2 hev⟩

end GlobalTheory.ClosedMatGroup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsSecondKindFormPreservingGroupStatement
open Filter Topology Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordsSecondKind_formPreservingGroup : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ), ∃ (d : ℕ) (Z : Fin d → Matrix (Fin m) (Fin m) ℂ) (s : Matrix (Fin m) (Fin m) ℂ → Fin d → ℝ), (∀ i, (Z i)ᴴ * A + A * Z i = 0) ∧ Tendsto s (𝓝[{X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}] 1) (𝓝 0) ∧ ∀ᶠ X in 𝓝[{X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}] 1, X = (List.ofFn fun i => NormedSpace.exp (s X i • Z i)).prod := by
  first | exact @GlobalTheory.ClosedMatGroup.coords_second_kind_unitary | exact GlobalTheory.ClosedMatGroup.coords_second_kind_unitary | (intros; apply GlobalTheory.ClosedMatGroup.coords_second_kind_unitary <;> assumption)
end
end
