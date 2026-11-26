module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfInvariantDerivativesVanishSemiAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkDerivationMemSpanInvariantSemiAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkDerivationMemSpanInvariantSemiAbelian
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.StalkDerSpan

open GlobalTheory.TangentOrigin

theorem stalk_derivation_span : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (p : G.left), G.hom.base p = genericPoint (Sp R) → ∀ (D : Fin n → G.left.presheaf.stalk p → G.left.presheaf.stalk p), (∀ a (W : G.left.Opens) (h : p ∈ W) (g : Γ(G.left, W)), D a (G.left.presheaf.germ W p h g) = G.left.presheaf.germ W p h (dd a W g)) → ∀ (δ : G.left.presheaf.stalk p → ResidueField (G.left.presheaf.stalk p)), (∀ u w, δ (u + w) = δ u + δ w) → (∀ u w, δ (u * w) = residue _ u * δ w + residue _ w * δ u) → (∀ r : R, δ ((G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = 0) → ∃ c : Fin n → G.left.presheaf.stalk p, ∀ y, δ y = residue _ (∑ a, c a * D a y) := by
  intro R _ _ _ _ G _ _ hsa n v dd hinv p _ D hD δ hadd hmul hbase
  haveI : Smooth G.hom := hsa.smooth
  have hv := GlobalTheory.VertCoeffRing.isLieBasis_tvE v
  have hdd := fun (B : Type) [CommRing B] [Algebra R B] e he z O h =>
    GlobalTheory.VertCoeffRing.evalPt_lieExp (fun a => v a) dd hinv B e he z O h

  let ψ : ∀ (V : G.left.Opens), p ∈ V → Γ(G.left, V) →+* ResidueField (G.left.presheaf.stalk p) :=
    fun V hpV => (residue _).comp (G.left.presheaf.germ V p hpV).hom
  have germ_res : ∀ (V V' : G.left.Opens) (e : V' ≤ V) (hpV : p ∈ V) (hpV' : p ∈ V') (f : Γ(G.left, V)),
      G.left.presheaf.germ V' p hpV' (resG G.left e f) = G.left.presheaf.germ V p hpV f := by
    intro V V' e hpV hpV' f
    exact TopCat.Presheaf.germ_res_apply _ (homOfLE e) p hpV' f

  have loc : ∀ (V : G.left.Opens) (hpV : p ∈ V), IsAffineOpen V →
      ∃! c : Fin n → ResidueField (G.left.presheaf.stalk p),
        ∀ f, δ (G.left.presheaf.germ V p hpV f) = ∑ a, c a * ψ V hpV (dd a V f) := by
    intro V hpV hV
    obtain ⟨t, ht, et⟩ := exists_evalPt_eq hV (ψ V hpV)
    letI : Algebra R (ResidueField (G.left.presheaf.stalk p)) := (Spec.preimage (t ≫ G.hom)).hom.toAlgebra
    let y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (ResidueField (G.left.presheaf.stalk p)) ⟶ G :=
      Over.homMk t (Spec.map_preimage (t ≫ G.hom)).symm
    have h : ⊤ ≤ y.left ⁻¹ᵁ V := ht
    have ev : ∀ s, evalPt y.left V h s = ψ V hpV s := fun s => by
      change evalPt t V ht s = _
      rw [et]
    have hconst : ∀ r, G.left.presheaf.germ V p hpV (constFn G.hom V r) =
        (G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
      intro r
      have e1 : constFn G.hom V r = resG G.left (le_top : V ≤ ⊤)
          ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
        unfold constFn
        first
          | rfl
          | (rw [Scheme.Hom.appLE_eq_app_comp_map] ; rfl)
          | (simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]; rfl)
      rw [e1]
      exact germ_res ⊤ V le_top trivial hpV _
    have := GlobalTheory.VertCoeffRing.existsUnique_coeff_alg hv hdd y hV h
      (fun f => δ (G.left.presheaf.germ V p hpV f))
      (fun f f' => by simp only [map_add (f := _), hadd])
      (fun f f' => by simp only [map_mul, hmul, ev]; rfl)
      (fun r => by rw [hconst]; exact hbase r)
    simpa only [ev] using this

  have down : ∀ (V V' : G.left.Opens) (e : V' ≤ V) (hpV : p ∈ V) (hpV' : p ∈ V')
      (c : Fin n → ResidueField (G.left.presheaf.stalk p)),
      (∀ f, δ (G.left.presheaf.germ V' p hpV' f) = ∑ a, c a * ψ V' hpV' (dd a V' f)) →
      ∀ f, δ (G.left.presheaf.germ V p hpV f) = ∑ a, c a * ψ V hpV (dd a V f) := by
    intro V V' e hpV hpV' c hc f
    rw [← germ_res V V' e hpV hpV' f, hc]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    change residue _ (G.left.presheaf.germ V' p hpV' (dd a V' (resG G.left e f))) =
      residue _ (G.left.presheaf.germ V p hpV (dd a V f))
    rw [(hinv a).1.2.2 V V' e le_top f, germ_res]
  obtain ⟨V₀, hV₀, hpV₀, -⟩ := exists_isAffineOpen_mem_and_subset (show p ∈ (⊤ : G.left.Opens) from trivial)
  obtain ⟨c₀, hc₀, hu₀⟩ := loc V₀ hpV₀ hV₀
  choose c hc using fun a => residue_surjective (R := G.left.presheaf.stalk p) (c₀ a)
  refine ⟨c, fun y => ?_⟩
  obtain ⟨W, hpW, g, rfl⟩ := TopCat.Presheaf.germ_exist _ y
  obtain ⟨V', hV', hpV', hle⟩ := exists_isAffineOpen_mem_and_subset (show p ∈ V₀ ⊓ W from ⟨hpV₀, hpW⟩)
  obtain ⟨c', hc', -⟩ := loc V' hpV' hV'
  have hcc : c' = c₀ := hu₀ c' (down V₀ V' (hle.trans inf_le_left) hpV₀ hpV' c' hc')
  subst hcc
  have eW : V' ≤ W := hle.trans inf_le_right
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← germ_res W V' eW hpW hpV' g, hc', map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, hc, hD]
  rfl

end GlobalTheory.StalkDerSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkDerivationMemSpanInvariantSemiAbelianStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalkDerivation_mem_span_invariant_semiAbelian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (p : G.left), G.hom.base p = genericPoint (Sp R) → ∀ (D : Fin n → G.left.presheaf.stalk p → G.left.presheaf.stalk p), (∀ a (W : G.left.Opens) (h : p ∈ W) (g : Γ(G.left, W)), D a (G.left.presheaf.germ W p h g) = G.left.presheaf.germ W p h (dd a W g)) → ∀ (δ : G.left.presheaf.stalk p → ResidueField (G.left.presheaf.stalk p)), (∀ u w, δ (u + w) = δ u + δ w) → (∀ u w, δ (u * w) = residue _ u * δ w + residue _ w * δ u) → (∀ r : R, δ ((G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = 0) → ∃ c : Fin n → G.left.presheaf.stalk p, ∀ y, δ y = residue _ (∑ a, c a * D a y) := by
  first | exact @GlobalTheory.StalkDerSpan.stalk_derivation_span | exact GlobalTheory.StalkDerSpan.stalk_derivation_span | (intros; apply GlobalTheory.StalkDerSpan.stalk_derivation_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendingCotangentForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendingCotangentForm
open IsLocalRing

namespace GlobalTheory.ConormalDer

theorem exists_derivation_cotangent (R B : Type) [CommRing R] [CommRing B] [IsLocalRing B]
    [Algebra R B] [Algebra.FormallySmooth R (ResidueField B)] :
    ∃ D : B →ₗ[R] CotangentSpace B, (∀ a b, D (a * b) = a • D b + b • D a) ∧
      ∀ t : maximalIdeal B, D t = (maximalIdeal B).toCotangent t := by
  set m := maximalIdeal B with hm
  let π : (B ⧸ m ^ 2) →ₐ[R] ResidueField B :=
    Ideal.Quotient.liftₐ (m ^ 2) (IsScalarTower.toAlgHom R B (ResidueField B)) fun a ha =>
      (residue_eq_zero_iff a).2 (Ideal.pow_le_self two_ne_zero ha)
  have hπ : ∀ a, π (Ideal.Quotient.mk _ a) = residue B a := fun _ => rfl
  have hsurj : Function.Surjective π := fun y => by
    obtain ⟨a, rfl⟩ := residue_surjective y
    exact ⟨_, hπ a⟩
  have hker : ∀ z, π z = 0 → z ∈ m.cotangentIdeal := fun z hz => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact Ideal.mk_mem_cotangentIdeal.2 ((residue_eq_zero_iff a).1 hz)
  have hnil : IsNilpotent (RingHom.ker (π : (B ⧸ m ^ 2) →+* ResidueField B)) := by
    refine ⟨2, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← m.cotangentIdeal_square]
    exact Ideal.pow_right_mono (fun z hz => hker z hz) 2
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R (ResidueField B)) π hsurj hnil
  have hs : ∀ y, π (s y) = y := fun y =>
    Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _ y
  have hmem : ∀ a, Ideal.Quotient.mk _ a - s (residue B a) ∈ m.cotangentIdeal := fun a =>
    hker _ (by rw [map_sub, hs, hπ, sub_self])
  let D : B → CotangentSpace B := fun a => m.cotangentEquivIdeal.symm ⟨_, hmem a⟩
  have hD : ∀ a, m.cotangentToQuotientSquare (D a) = Ideal.Quotient.mk _ a - s (residue B a) :=
    fun a => by
      rw [← Ideal.cotangentEquivIdeal_apply]
      simp only [D, LinearEquiv.apply_symm_apply]
  have hinj := m.cotangentToQuotientSquare_injective
  have hsq : ∀ a b, (Ideal.Quotient.mk _ a - s (residue B a)) *
      (Ideal.Quotient.mk _ b - s (residue B b)) = 0 := fun a b => by
    have := Ideal.mul_mem_mul (hmem a) (hmem b)
    rwa [← pow_two, m.cotangentIdeal_square, Ideal.mem_bot] at this
  have hsm : ∀ (a : B) (z : B ⧸ m ^ 2), a • z = Ideal.Quotient.mk _ a * z := fun a z =>
    Algebra.smul_def a z
  have hmul : ∀ a b, D (a * b) = a • D b + b • D a := fun a b => by
    apply hinj
    rw [map_add (f := _), map_smul, map_smul, hD, hD, hD, hsm, hsm, map_mul, map_mul, map_mul]
    linear_combination (-1 : B ⧸ m ^ 2) * hsq a b
  have hR : ∀ c : R, D (algebraMap R B c) = 0 := fun c => by
    apply hinj
    rw [hD, map_zero, sub_eq_zero]
    exact (s.commutes c).symm
  refine ⟨⟨⟨D, fun a b => ?_⟩, fun c a => ?_⟩, hmul, fun t => ?_⟩
  · apply hinj
    rw [map_add (f := _), hD, hD, hD, map_add (f := _), map_add (f := _), map_add (f := _)]
    ring
  · show D (c • a) = c • D a
    rw [Algebra.smul_def, hmul, hR, smul_zero, add_zero, algebraMap_smul]
  · apply hinj
    show m.cotangentToQuotientSquare (D t) = _
    rw [hD, (residue_eq_zero_iff _).2 t.2, map_zero, sub_zero, Ideal.toCotangent_to_quotient_square]
    rfl

theorem formallySmooth_of_charZero (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] :
    Algebra.FormallySmooth F K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  haveI := hs.isAlgebraic_field
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : CharZero (IntermediateField.adjoin F (Set.range ((↑) : s → K))) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : Algebra.IsSeparable (IntermediateField.adjoin F (Set.range ((↑) : s → K))) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

theorem formallySmooth_residueField (R B : Type) [CommRing R] [IsDomain R] [Algebra ℚ R]
    [CommRing B] [IsLocalRing B] [Algebra R B]
    (hu : ∀ r : R, r ≠ 0 → IsUnit (algebraMap R B r)) :
    Algebra.FormallySmooth R (ResidueField B) := by
  let K := FractionRing R
  have hu' : ∀ c : nonZeroDivisors R, IsUnit (algebraMap R B c) := fun c =>
    hu c (nonZeroDivisors.ne_zero c.2)
  letI : Algebra K B := (IsLocalization.lift (M := nonZeroDivisors R) (S := K) hu').toAlgebra
  haveI : IsScalarTower R K B := IsScalarTower.of_algebraMap_eq fun c =>
    (IsLocalization.lift_eq hu' c).symm
  haveI : IsScalarTower R K (ResidueField B) := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K B (ResidueField B), ← IsScalarTower.algebraMap_apply R K B,
      ← IsScalarTower.algebraMap_apply]
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing R
  haveI : Algebra.FormallySmooth K (ResidueField B) := formallySmooth_of_charZero K _
  haveI : Algebra.FormallyEtale R K := .of_isLocalization (nonZeroDivisors R)
  exact .comp R K (ResidueField B)

theorem exists_derivation_extending :
    ∀ (R B : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] [CommRing B] [IsLocalRing B] [Algebra R B], (∀ r : R, r ≠ 0 → IsUnit (algebraMap R B r)) → ∀ (lam : CotangentSpace B →ₗ[ResidueField B] ResidueField B), ∃ δ : Derivation R B (ResidueField B), ∀ y (hy : y ∈ maximalIdeal B), δ y = lam ((maximalIdeal B).toCotangent ⟨y, hy⟩) := by
  intro R B _ _ _ _ _ _ hu lam
  haveI := formallySmooth_residueField R B hu
  obtain ⟨D, hmul, hD⟩ := exists_derivation_cotangent R B
  have hsm : ∀ (a : B) (v : CotangentSpace B), lam (a • v) = a • lam v := fun a v => by
    rw [← algebraMap_smul (ResidueField B) a v, map_smul, algebraMap_smul]
  let L : B →ₗ[R] ResidueField B :=
    { toFun := fun a => lam (D a)
      map_add' := fun a b => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, map_smul, ← algebraMap_smul B c (D a), hsm, algebraMap_smul] }
  refine ⟨Derivation.mk' L fun a b => ?_, fun y hy => ?_⟩
  · change lam (D (a * b)) = a • lam (D b) + b • lam (D a)
    rw [hmul, map_add (f := _), hsm, hsm]
  · show lam (D y) = _
    exact congrArg lam (hD ⟨y, hy⟩)

end GlobalTheory.ConormalDer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendingCotangentFormStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_extending_cotangent_form : ∀ (R B : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] [CommRing B] [IsLocalRing B] [Algebra R B], (∀ r : R, r ≠ 0 → IsUnit (algebraMap R B r)) → ∀ (lam : CotangentSpace B →ₗ[ResidueField B] ResidueField B), ∃ δ : Derivation R B (ResidueField B), ∀ y (hy : y ∈ maximalIdeal B), δ y = lam ((maximalIdeal B).toCotangent ⟨y, hy⟩) := by
  first | exact @GlobalTheory.ConormalDer.exists_derivation_extending | exact GlobalTheory.ConormalDer.exists_derivation_extending | (intros; apply GlobalTheory.ConormalDer.exists_derivation_extending <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfInvariantDerivativesVanishSemiAbelian
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.InvJet

theorem alg_eq_zero (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (hk : ∀ k : ℕ, k ≠ 0 → IsUnit (k : B)) (n : ℕ) (D : Fin n → B → B)
    (hadd : ∀ a u w, D a (u + w) = D a u + D a w) (hmul : ∀ a u w, D a (u * w) = u * D a w + w * D a u)
    (e : Fin n → B) (he : ∀ a, e a ∈ maximalIdeal B)
    (hE : ∀ y ∈ maximalIdeal B, y - ∑ a, e a * D a y ∈ maximalIdeal B ^ 2)
    (f : B) (hf : ∀ l : List (Fin n), l.foldr (fun a g => D a g) f ∈ maximalIdeal B) : f = 0 := by
  set m := maximalIdeal B with hm
  set E : B → B := fun g => ∑ a, e a * D a g with hEdef
  have Eadd : ∀ u w, E (u + w) = E u + E w := by
    intro u w; simp only [hEdef, hadd, mul_add, Finset.sum_add_distrib]
  have Emul : ∀ u w, E (u * w) = u * E w + w * E u := by
    intro u w; simp only [hEdef, hmul, Finset.mul_sum, Finset.sum_add_distrib, mul_add]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring
  have Em : ∀ g, E g ∈ m := fun g => Ideal.sum_mem _ fun a _ => Ideal.mul_mem_right _ _ (he a)
  have step : ∀ k : ℕ, ∀ g ∈ m ^ k, E g - (k : B) * g ∈ m ^ (k + 1) := by
    intro k
    induction k with
    | zero => intro g _; simpa using Em g
    | succ k ih =>
      intro g hg
      rw [pow_succ'] at hg
      refine Submodule.mul_induction_on hg ?_ ?_
      · intro y hy h hh
        have h1 : y * (E h - (k : B) * h) ∈ m ^ (k + 1 + 1) := by
          rw [pow_succ' m (k + 1)]; exact Ideal.mul_mem_mul hy (ih h hh)
        have h2 : h * (E y - y) ∈ m ^ (k + 1 + 1) := by
          have : E y - y ∈ m ^ 2 := by
            have := hE y hy
            rw [← neg_sub]; exact (m ^ 2).neg_mem this
          have := Ideal.mul_mem_mul hh this
          rwa [← pow_add, show k + 2 = k + 1 + 1 by ring] at this
        have : E (y * h) - ((k + 1 : ℕ) : B) * (y * h) = y * (E h - (k : B) * h) + h * (E y - y) := by
          rw [Emul]; push_cast; ring
        rw [this]; exact Ideal.add_mem _ h1 h2
      · intro u w hu hw
        have : E (u + w) - ((k + 1 : ℕ) : B) * (u + w)
            = (E u - ((k + 1 : ℕ) : B) * u) + (E w - ((k + 1 : ℕ) : B) * w) := by
          rw [Eadd]; ring
        rw [this]; exact Ideal.add_mem _ hu hw
  have claim : ∀ k : ℕ, ∀ g : B, (∀ l : List (Fin n), l.foldr (fun a g => D a g) g ∈ m) → g ∈ m ^ (k + 1) := by
    intro k
    induction k with
    | zero => intro g hg; simpa using hg []
    | succ k ih =>
      intro g hg
      have hg1 := ih g hg
      have hDa : ∀ a, D a g ∈ m ^ (k + 1) := by
        intro a; apply ih
        intro l
        have := hg (l ++ [a])
        simpa [List.foldr_append] using this
      have hEg : E g ∈ m ^ (k + 1 + 1) := by
        rw [pow_succ' m (k + 1)]
        exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_mul (he a) (hDa a)
      have hs := step (k + 1) g hg1
      have hkg : ((k + 1 : ℕ) : B) * g ∈ m ^ (k + 1 + 1) := by
        have := Ideal.sub_mem _ hEg hs
        simpa using this
      obtain ⟨u, hu⟩ := hk (k + 1) (by omega)
      have : g = ((u⁻¹ : Bˣ) : B) * (((k + 1 : ℕ) : B) * g) := by
        rw [← hu, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
      rw [this]; exact Ideal.mul_mem_left _ _ hkg
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing m (maximalIdeal.isMaximal B).ne_top
  have : f ∈ ⨅ i, m ^ i := by
    rw [Ideal.mem_iInf]; intro i
    cases i with
    | zero => simp
    | succ k => exact claim k f hf
  rw [hbot] at this; simpa using this

theorem exists_stalkDer (Z : Scheme) (d : Fld Z) (hd : IsField ⊤ d) (z : Z) :
    ∃ D : Z.presheaf.stalk z → Z.presheaf.stalk z,
      (∀ u w, D (u + w) = D u + D w) ∧ (∀ u w, D (u * w) = u * D w + w * D u) ∧
      ∀ (W : Z.Opens) (h : z ∈ W) (g : Γ(Z, W)),
        D (Z.presheaf.germ W z h g) = Z.presheaf.germ W z h (d W g) := by
  obtain ⟨hadd, hmul, hres⟩ := hd
  have hres' : ∀ (W W' : Z.Opens) (i : W' ⟶ W) (g : Γ(Z, W)),
      d W' (Z.presheaf.map i.op g) = Z.presheaf.map i.op (d W g) :=
    fun W W' i g => hres W W' i.le le_top g
  have wd : ∀ (W W' : Z.Opens) (h : z ∈ W) (h' : z ∈ W') (g : Γ(Z, W)) (g' : Γ(Z, W')),
      Z.presheaf.germ W z h g = Z.presheaf.germ W' z h' g' →
      Z.presheaf.germ W z h (d W g) = Z.presheaf.germ W' z h' (d W' g') := by
    intro W W' h h' g g' e
    obtain ⟨V, hV, iU, iV, e'⟩ := TopCat.Presheaf.germ_eq Z.presheaf z h h' g g' e
    rw [← TopCat.Presheaf.germ_res_apply Z.presheaf iU z hV,
      ← TopCat.Presheaf.germ_res_apply Z.presheaf iV z hV, ← hres', ← hres', e']
  choose W hW g hg using fun t : Z.presheaf.stalk z => TopCat.Presheaf.germ_exist Z.presheaf t
  have hD : ∀ (W₀ : Z.Opens) (h : z ∈ W₀) (g₀ : Γ(Z, W₀)),
      Z.presheaf.germ (W (Z.presheaf.germ W₀ z h g₀)) z (hW _) (d _ (g (Z.presheaf.germ W₀ z h g₀)))
        = Z.presheaf.germ W₀ z h (d W₀ g₀) := fun W₀ h g₀ => wd _ _ _ _ _ _ (hg _)
  refine ⟨fun t => Z.presheaf.germ (W t) z (hW t) (d (W t) (g t)), ?_, ?_, hD⟩
  · intro u w
    let V := W u ⊓ W w
    have hV : z ∈ V := ⟨hW u, hW w⟩
    let iu : V ⟶ W u := homOfLE inf_le_left
    let iw : V ⟶ W w := homOfLE inf_le_right
    have eu : u = Z.presheaf.germ V z hV (Z.presheaf.map iu.op (g u)) := by
      rw [TopCat.Presheaf.germ_res_apply]; exact (hg u).symm
    have ew : w = Z.presheaf.germ V z hV (Z.presheaf.map iw.op (g w)) := by
      rw [TopCat.Presheaf.germ_res_apply]; exact (hg w).symm
    have e : u + w = Z.presheaf.germ V z hV
        (Z.presheaf.map iu.op (g u) + Z.presheaf.map iw.op (g w)) := by
      rw [map_add (f := _), ← eu, ← ew]
    show Z.presheaf.germ (W (u + w)) z (hW _) (d _ (g (u + w))) = _
    rw [wd _ _ _ hV _ _ ((hg (u + w)).trans e), hadd V le_top, map_add (f := _), hres', hres',
      TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  · intro u w
    let V := W u ⊓ W w
    have hV : z ∈ V := ⟨hW u, hW w⟩
    let iu : V ⟶ W u := homOfLE inf_le_left
    let iw : V ⟶ W w := homOfLE inf_le_right
    have eu : u = Z.presheaf.germ V z hV (Z.presheaf.map iu.op (g u)) := by
      rw [TopCat.Presheaf.germ_res_apply]; exact (hg u).symm
    have ew : w = Z.presheaf.germ V z hV (Z.presheaf.map iw.op (g w)) := by
      rw [TopCat.Presheaf.germ_res_apply]; exact (hg w).symm
    have e : u * w = Z.presheaf.germ V z hV
        (Z.presheaf.map iu.op (g u) * Z.presheaf.map iw.op (g w)) := by
      rw [map_mul, ← eu, ← ew]
    show Z.presheaf.germ (W (u * w)) z (hW _) (d _ (g (u * w))) = _
    rw [wd _ _ _ hV _ _ ((hg (u * w)).trans e), hmul V le_top, map_add (f := _), map_mul, map_mul, hres', hres']
    simp only [TopCat.Presheaf.germ_res_apply, hg]

theorem germ_mem_of_valR_eq_zero (A : Type) [CommRing A] (Z : Scheme) (x : Sp A ⟶ Z) (W : Z.Opens)
    (hW : ⊤ ≤ x ⁻¹ᵁ W) (q₀ : Sp A) (h : x.base q₀ ∈ W) (g : Γ(Z, W)) (hg : valR x W g = 0) :
    Z.presheaf.germ W _ h g ∈ maximalIdeal (Z.presheaf.stalk (x.base q₀)) := by
  rw [valR, dite_eq_left hW] at hg
  have h0 : Scheme.Hom.appLE x W ⊤ hW g = 0 := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom hg
    rwa [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply, map_zero] at this
  by_contra hn
  have hu : IsUnit (Z.presheaf.germ W _ h g) := by
    by_contra hu'; exact hn ((mem_maximalIdeal _).2 hu')
  have hu2 := hu.map (x.stalkMap q₀).hom
  rw [Scheme.Hom.germ_stalkMap_apply] at hu2
  have e : (Sp A).presheaf.germ (x ⁻¹ᵁ W) q₀ h (x.app W g)
      = (Sp A).presheaf.germ ⊤ q₀ trivial (Scheme.Hom.appLE x W ⊤ hW g) := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
    exact (TopCat.Presheaf.germ_res_apply (Sp A).presheaf (homOfLE hW) q₀ trivial _).symm
  rw [e, h0, map_zero] at hu2
  exact not_isUnit_zero hu2

theorem spMap_genericPoint (R Ω : Type) [CommRing R] [IsDomain R] [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω)
    (hφ : Function.Injective φ) : (spMap φ).base (genericPoint (Sp Ω)) = genericPoint (Sp R) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  change Ideal.comap φ ⊥ = (⊥ : PrimeSpectrum R).asIdeal
  rw [PrimeSpectrum.asIdeal_bot, ← RingHom.ker_eq_comap_bot]; exact (RingHom.injective_iff_ker_eq_bot φ).1 hφ

theorem euler_of_span (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (n : ℕ) (D : Fin n → B → B)
    (hspan : ∀ lam : CotangentSpace B →ₗ[ResidueField B] ResidueField B, ∃ b : Fin n → B,
      ∀ y (hy : y ∈ maximalIdeal B), lam ((maximalIdeal B).toCotangent ⟨y, hy⟩) = residue B (∑ a, b a * D a y)) :
    ∃ e : Fin n → B, (∀ a, e a ∈ maximalIdeal B) ∧
      ∀ y ∈ maximalIdeal B, y - ∑ a, e a * D a y ∈ maximalIdeal B ^ 2 := by
  let β := Module.Free.chooseBasis (ResidueField B) (CotangentSpace B)
  choose y hy using fun i => (maximalIdeal B).toCotangent_surjective (β i)
  choose b hb using fun i => hspan (β.coord i)
  refine ⟨fun a => ∑ i, (y i : B) * b i a, fun a => Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (y i).2, ?_⟩
  intro z hz
  set c : _ → B := fun i => ∑ a, b i a * D a z with hc
  have hre : ∑ a, (∑ i, (y i : B) * b i a) * D a z = ∑ i, c i * (y i : B) := by
    simp only [hc, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro a _; ring
  have hmem : z - ∑ a, (∑ i, (y i : B) * b i a) * D a z ∈ maximalIdeal B :=
    Ideal.sub_mem _ hz (Ideal.sum_mem _ fun a _ =>
          Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (y i).2))
  have hw : (⟨z, hz⟩ : maximalIdeal B) - ∑ i, c i • y i = ⟨_, hmem⟩ := by
    apply Subtype.ext; simp [hre]
  show z - ∑ a, (∑ i, (y i : B) * b i a) * D a z ∈ _
  refine ((maximalIdeal B).toCotangent_eq_zero ⟨_, hmem⟩).1 ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hw, map_sub, map_sum]
  simp only [map_smul, hy]
  have hcoord : ∀ i, c i • β i = β.coord i ((maximalIdeal B).toCotangent ⟨z, hz⟩) • β i := by
    intro i; rw [hb i z hz, ← algebraMap_smul (ResidueField B) (∑ a, b i a * D a z) (β i)]; rfl
  simp only [hcoord]
  rw [sub_eq_zero]
  exact (β.sum_repr _).symm

theorem isUnit_baseGerm (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) (p : G.left)
    (hp : G.hom.base p = genericPoint (Sp R)) (r : R) (hr : r ≠ 0) : IsUnit ((G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) := by
  have e : ((G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = (G.hom.stalkMap p).hom ((Sp R).presheaf.germ ⊤ (G.hom.base p) trivial
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
    erw [Scheme.Hom.germ_stalkMap_apply]; rfl
  rw [e]; apply IsUnit.map
  have hs0 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r ≠ 0 := by
    intro h0
    apply hr
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom h0
    rwa [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero] at this
  generalize (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r = s at hs0
  have key : ∀ (q : Sp R), q = genericPoint (Sp R) → IsUnit ((Sp R).presheaf.germ ⊤ q trivial s) := by
    rintro q rfl
    show IsUnit (((Sp R).presheaf.germ ⊤ (genericPoint (Sp R)) trivial s : (Sp R).functionField))
    exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (germ_injective_of_isIntegral (Sp R) (U := ⊤) (genericPoint (Sp R)) (show genericPoint (Sp R) ∈ (⊤ : (Sp R).Opens) from trivial))).2 hs0)
  exact key _ hp

theorem span_of_parts (h1 : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (p : G.left), G.hom.base p = genericPoint (Sp R) → ∀ (D : Fin n → G.left.presheaf.stalk p → G.left.presheaf.stalk p), (∀ a (W : G.left.Opens) (h : p ∈ W) (g : Γ(G.left, W)), D a (G.left.presheaf.germ W p h g) = G.left.presheaf.germ W p h (dd a W g)) → ∀ (δ : G.left.presheaf.stalk p → ResidueField (G.left.presheaf.stalk p)), (∀ u w, δ (u + w) = δ u + δ w) → (∀ u w, δ (u * w) = residue _ u * δ w + residue _ w * δ u) → (∀ r : R, δ ((G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = 0) → ∃ c : Fin n → G.left.presheaf.stalk p, ∀ y, δ y = residue _ (∑ a, c a * D a y)) (h2 : ∀ (R B : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] [CommRing B] [IsLocalRing B] [Algebra R B], (∀ r : R, r ≠ 0 → IsUnit (algebraMap R B r)) → ∀ (lam : CotangentSpace B →ₗ[ResidueField B] ResidueField B), ∃ δ : Derivation R B (ResidueField B), ∀ y (hy : y ∈ maximalIdeal B), δ y = lam ((maximalIdeal B).toCotangent ⟨y, hy⟩)) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (p : G.left), G.hom.base p = genericPoint (Sp R) → ∀ (D : Fin n → G.left.presheaf.stalk p → G.left.presheaf.stalk p), (∀ a (W : G.left.Opens) (h : p ∈ W) (g : Γ(G.left, W)), D a (G.left.presheaf.germ W p h g) = G.left.presheaf.germ W p h (dd a W g)) → ∀ lam : CotangentSpace (G.left.presheaf.stalk p) →ₗ[ResidueField (G.left.presheaf.stalk p)] ResidueField (G.left.presheaf.stalk p), ∃ b : Fin n → G.left.presheaf.stalk p, ∀ y (hy : y ∈ maximalIdeal (G.left.presheaf.stalk p)), lam ((maximalIdeal _).toCotangent ⟨y, hy⟩) = residue _ (∑ a, b a * D a y) := by
  intro R _ _ _ _ G _ _ hSA n v dd hinv p hp D hD lam
  let ψ : R →+* G.left.presheaf.stalk p :=
    (G.left.presheaf.germ ⊤ p trivial).hom.comp
      ((G.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  letI : Algebra R (G.left.presheaf.stalk p) := ψ.toAlgebra
  obtain ⟨δ, hδ⟩ := h2 R (G.left.presheaf.stalk p) (fun r hr => isUnit_baseGerm R G p hp r hr) lam
  obtain ⟨c, hc⟩ := h1 R G hSA n v dd hinv p hp D hD δ (fun u w => map_add δ u w)
    (fun u w => by simp only [Derivation.leibniz, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq]) (fun r => δ.map_algebraMap r)
  exact ⟨c, fun y hy => by rw [← hδ y hy, hc y]⟩

theorem eq_zero_of_euler (heart : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (p : G.left), G.hom.base p = genericPoint (Sp R) → ∀ (D : Fin n → G.left.presheaf.stalk p → G.left.presheaf.stalk p), (∀ a (W : G.left.Opens) (h : p ∈ W) (g : Γ(G.left, W)), D a (G.left.presheaf.germ W p h g) = G.left.presheaf.germ W p h (dd a W g)) → ∃ e : Fin n → G.left.presheaf.stalk p, (∀ a, e a ∈ maximalIdeal (G.left.presheaf.stalk p)) ∧ ∀ y ∈ maximalIdeal (G.left.presheaf.stalk p), y - ∑ a, e a * D a y ∈ maximalIdeal (G.left.presheaf.stalk p) ^ 2) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω), Function.Injective φ → ∀ (x : Sp Ω ⟶ G.left), x ≫ G.hom = spMap φ → ∀ (O : G.left.Opens) (f : Γ(G.left, O)), ⊤ ≤ x ⁻¹ᵁ O → (∀ l : List (Fin n), valR x O (l.foldr (fun a g => dd a O g) f) = 0) → f = 0 := by
  intro R _ _ _ _ G _ _ hSA n v dd hinv Ω _ _ φ hφ x hx O f hO hf
  haveI : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G := hSA
  haveI : AlgebraicGeometry.IsIntegral G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G
  haveI : Smooth G.hom := hSA.smooth
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  set q₀ := genericPoint (Sp Ω)
  set p := x.base q₀
  have hp : p ∈ O := hO (Set.mem_univ q₀)
  have hpR : G.hom.base p = genericPoint (Sp R) := by
    rw [← spMap_genericPoint R Ω φ hφ, ← hx]; rfl
  choose D hDadd hDmul hDg using fun a => exists_stalkDer G.left (dd a) (hinv a).1 p
  obtain ⟨e, he, hE⟩ := heart R G hSA n v dd hinv p hpR D hDg
  let ψ : R →+* G.left.presheaf.stalk p :=
    (G.left.presheaf.germ ⊤ p trivial).hom.comp
      ((G.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  have hk : ∀ k : ℕ, k ≠ 0 → IsUnit (k : G.left.presheaf.stalk p) := by
    intro k hk0
    have : IsUnit (k : R) := by
      have h1 : IsUnit (k : ℚ) := isUnit_iff_ne_zero.2 (by exact_mod_cast hk0)
      simpa using h1.map (algebraMap ℚ R)
    simpa using this.map ψ
  have hword : ∀ l : List (Fin n), l.foldr (fun a g => D a g) (G.left.presheaf.germ O p hp f)
      = G.left.presheaf.germ O p hp (l.foldr (fun a g => dd a O g) f) := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp only [List.foldr_cons, ih, hDg]
  have h0 := alg_eq_zero _ hk n D hDadd hDmul e he hE (G.left.presheaf.germ O p hp f)
    (fun l => by rw [hword]; exact germ_mem_of_valR_eq_zero Ω G.left x O hO q₀ hp _ (hf l))
  exact germ_injective_of_isIntegral G.left p hp (by rw [h0, map_zero])

theorem eq_zero_of_invDer_vanish : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω), Function.Injective φ → ∀ (x : Sp Ω ⟶ G.left), x ≫ G.hom = spMap φ → ∀ (O : G.left.Opens) (f : Γ(G.left, O)), ⊤ ≤ x ⁻¹ᵁ O → (∀ l : List (Fin n), valR x O (l.foldr (fun a g => dd a O g) f) = 0) → f = 0 := by
  refine eq_zero_of_euler ?_
  intro R _ _ _ _ G _ _ hSA n v dd hinv p hp D hD
  haveI : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G := hSA
  haveI : Smooth G.hom := hSA.smooth
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  exact euler_of_span _ n D (span_of_parts GlobalTheory.T.stalkDerivation_mem_span_invariant_semiAbelian GlobalTheory.T.exists_derivation_extending_cotangent_form R G hSA n v dd hinv p hp D hD)

end GlobalTheory.InvJet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfInvariantDerivativesVanishSemiAbelianStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_invariantDerivatives_vanish_semiAbelian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω), Function.Injective φ → ∀ (x : Sp Ω ⟶ G.left), x ≫ G.hom = spMap φ → ∀ (O : G.left.Opens) (f : Γ(G.left, O)), ⊤ ≤ x ⁻¹ᵁ O → (∀ l : List (Fin n), valR x O (l.foldr (fun a g => dd a O g) f) = 0) → f = 0 := by
  first | exact @GlobalTheory.InvJet.eq_zero_of_invDer_vanish | exact GlobalTheory.InvJet.eq_zero_of_invDer_vanish | (intros; apply GlobalTheory.InvJet.eq_zero_of_invDer_vanish <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointFromFormalRaynaudPointSameDeriva
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointFromFormalRaynaudPointSameDeriva
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.FormalDer

open TrivSqZeroExt (inl inr)
open ReciprocityTheory.ChartRestriction.G.Chart (sp)

theorem isLocalRing_dual (Ω : Type) [CommRing Ω] [IsLocalRing Ω] : IsLocalRing (DualNumber Ω) := by
  have : Nontrivial (DualNumber Ω) := (TrivSqZeroExt.inl_injective (R := Ω) (M := Ω)).nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun y => ?_
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self y.fst

theorem mem_pow_map {Ω : Type} [CommRing Ω] (K : Ideal Ω) (n : ℕ) (y : DualNumber Ω)
    (hy : y ∈ (K.map (algebraMap Ω (DualNumber Ω))) ^ n) : y.fst ∈ K ^ n ∧ y.snd ∈ K ^ n := by
  rw [← Ideal.map_pow] at hy
  let S : Ideal (DualNumber Ω) :=
    { carrier := {y | y.fst ∈ K ^ n ∧ y.snd ∈ K ^ n}
      add_mem' := fun ha hb => ⟨by simpa using add_mem ha.1 hb.1, by simpa using add_mem ha.2 hb.2⟩
      zero_mem' := ⟨by simp, by simp⟩
      smul_mem' := fun c y hy => ⟨by simpa using Ideal.mul_mem_left _ c.fst hy.1, by
        simpa [TrivSqZeroExt.snd_mul, smul_eq_mul, _root_.mul_comm] using
          add_mem (Ideal.mul_mem_left _ c.fst hy.2) (Ideal.mul_mem_left _ c.snd hy.1)⟩ }
  have : (K ^ n).map (algebraMap Ω (DualNumber Ω)) ≤ S :=
    Ideal.map_le_iff_le_comap.2 fun r hr => ⟨by simpa [TrivSqZeroExt.algebraMap_eq_inl] using hr, by
      simp [TrivSqZeroExt.algebraMap_eq_inl]⟩
  exact this hy

theorem isHausdorff_dual {R Ω : Type} [CommRing R] [CommRing Ω] (φ : R →+* Ω) (I : Ideal R)
    [h : IsHausdorff (I.map φ) Ω] :
    IsHausdorff (I.map ((algebraMap Ω (DualNumber Ω)).comp φ)) (DualNumber Ω) := by
  rw [← Ideal.map_map]
  refine ⟨fun y hy => ?_⟩
  have h' : ∀ n, y.fst ∈ (I.map φ) ^ n ∧ y.snd ∈ (I.map φ) ^ n := fun n => mem_pow_map _ n y (by
    have := hy n
    rwa [SModEq.zero, smul_eq_mul, Ideal.mul_top] at this)
  ext
  · exact h.haus y.fst fun n => by rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact (h' n).1
  · exact h.haus y.snd fun n => by rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact (h' n).2

theorem exists_tangent_lift {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (v : TanM (𝟙 (Sp R)) G) : ∃ u : epsR R ⟶ G, u.left = (tv v).left ∧ IsTangent u := by
  have h := CoeffWt.isGrpPullback_self G
  obtain ⟨u, e⟩ := PullbackSections.push_surj h (tv v)
  exact ⟨u, (Category.comp_id _).symm.trans (congrArg (fun q => q.left) e),
    (PullbackSections.isTangent_iff h _).2 (by rw [e]; exact PullbackSections.tv_mem _)⟩

theorem epsHom_comp {R Ω : Type} [CommRing R] [CommRing Ω] (φ : R →+* Ω) (δ : Derivation ℤ Ω Ω)
    (hδφ : ∀ r, δ (φ r) = 0) :
    letI : Algebra R Ω := φ.toAlgebra
    (epsHom δ).comp φ = algebraMap R (DualNumber Ω) := by
  letI : Algebra R Ω := φ.toAlgebra
  refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_
  · show (epsHom δ (φ r)).fst = (algebraMap R (DualNumber Ω) r).fst
    simp [epsHom, TrivSqZeroExt.algebraMap_eq_inl']
    rfl
  · show (epsHom δ (φ r)).snd = (algebraMap R (DualNumber Ω) r).snd
    simp [epsHom, TrivSqZeroExt.algebraMap_eq_inl', hδφ]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → ∀ (x' : Sp Ω ⟶ t.G.left) (hx' : x' ≫ t.G.hom = spMap φ), GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P
  letI := H.starRing
  intro Y n vH dd hdd v' hv' dd' hdd' Ω _ _ _ φ x δ hcomp hx hδφ hδ x' hx' hxx' a O f hO
  letI : Algebra R Ω := φ.toAlgebra
  have hε : (inr 1 : DualNumber Ω) * inr 1 = 0 := TrivSqZeroExt.inr_mul_inr _ _ _
  haveI := isLocalRing_dual Ω
  haveI : IsHausdorff ((maximalIdeal R).map (algebraMap R (DualNumber Ω))) (DualNumber Ω) :=
    isHausdorff_dual φ (maximalIdeal R)
  let jη : epsR R ⟶ overAt (𝟙 (Sp R)) (DualNumber R) := Over.homMk (𝟙 _) (by simp)
  obtain ⟨u₀, hu₀, hut₀⟩ := exists_tangent_lift Y.H (vH a)
  obtain ⟨u₁, hu₁, hut₁⟩ := exists_tangent_lift t.G (v' a)
  have eu₀ : u₀ = jη ≫ tv (vH a) := Over.OverMorphism.ext (hu₀.trans (Category.id_comp _).symm)
  have eu₁ : u₁ = jη ≫ tv (v' a) := Over.OverMorphism.ext (hu₁.trans (Category.id_comp _).symm)
  let T : Over (Sp R) := Over.mk (spMap φ)
  let xt : T ⟶ Y.H := Over.homMk x hx
  let xt' : T ⟶ t.G := Over.homMk x' hx'
  let kz : sp (R₀ := R) (DualNumber Ω) ⟶ T := Over.homMk (spMap (algebraMap Ω (DualNumber Ω))) (by
    show spMap _ ≫ spMap φ = Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber Ω)))
    rw [spMap, spMap, ← Spec.map_comp]
    rfl)
  let kε : sp (R₀ := R) (DualNumber Ω) ⟶ T := Over.homMk (spMap (epsHom (δ a))) (by
    show spMap _ ≫ spMap φ = Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber Ω)))
    rw [spMap, spMap, ← Spec.map_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (epsHom_comp φ (δ a) (hδφ a)))
  let kk := Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ jη
  let z : sp (R₀ := R) (DualNumber Ω) ⟶ Y.H := kz ≫ xt
  let z' : sp (R₀ := R) (DualNumber Ω) ⟶ t.G := kz ≫ xt'
  let yH := (Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ u₀) * z
  let yG := (Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ u₁) * z'

  have e₁ : yH = kε ≫ xt := by
    refine CoeffWt.eq_of_valR Y yH (kε ≫ xt) ⊤ (x (closedPoint Ω)) trivial fun V' _ hp => ?_
    have m : ⊤ ≤ x ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V') := (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of Ω) x hp).ge
    obtain ⟨a₁, a₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (algebraMap Ω (DualNumber Ω)) x _ m
    obtain ⟨b₁, b₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (epsHom (δ a)) x _ m
    obtain ⟨c₁, c₂⟩ := CoeffWt.valR_translate hu₀ hut₀ (hdd a) (inr 1 : DualNumber Ω) hε z _ a₁
    refine ⟨c₁, b₁, fun α g _ => ?_⟩
    refine (c₂ g).trans (Eq.trans ?_ (b₂ g).symm)
    show valR (spMap (algebraMap Ω (DualNumber Ω)) ≫ x) _ g +
      inr 1 * valR (spMap (algebraMap Ω (DualNumber Ω)) ≫ x) _ (dd a _ g) = _
    rw [a₂, a₂, hδ a _ g m]
    ext <;> simp [epsHom, TrivSqZeroExt.algebraMap_eq_inl']
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have pz := hxx'.pull kz (Y.rep.1 _ _ kz xt)
  have pu := (hv' a).pull (Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ jη)
    (Y.rep.1 _ _ (Chart.spMap (GlobalTheory.SqZero.epsTo R (inr 1 : DualNumber Ω) hε) ≫ jη) (tv (vH a)))
  rw [Category.assoc, Category.assoc, ← eu₀, ← eu₁] at pu
  have pm := FormalPoint.IsPointOf.mul hG pu pz (Y.rep.2 _ _ _)
  have pε := hxx'.pull kε (Y.rep.1 _ _ kε xt)
  have e₂ : yG = kε ≫ xt' := by
    have pm' : FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (kε ≫ xt)) yG := by
      rw [← e₁]; exact pm
    exact FormalPoint.IsPointOf.unique pm' pε
  obtain ⟨a₁, a₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (algebraMap Ω (DualNumber Ω)) x' O hO
  obtain ⟨b₁, b₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (epsHom (δ a)) x' O hO
  obtain ⟨c₁, c₂⟩ := CoeffWt.valR_translate hu₁ hut₁ (hdd' a) (inr 1 : DualNumber Ω) hε z' O a₁
  have hz : ∀ g, valR z'.left O g = algebraMap Ω (DualNumber Ω) (valR x' O g) := a₂
  have k : valR yG.left O f = valR (spMap (epsHom (δ a)) ≫ x') O f := by
    rw [e₂]
    rfl
  have k2 : algebraMap Ω (DualNumber Ω) (valR x' O f) +
      inr 1 * algebraMap Ω (DualNumber Ω) (valR x' O (dd' a O f)) = epsHom (δ a) (valR x' O f) := by
    rw [← hz, ← hz, ← c₂, k, b₂]
  have k3 := congrArg TrivSqZeroExt.snd k2
  simpa [epsHom, TrivSqZeroExt.algebraMap_eq_inl'] using k3

end GlobalTheory.Heat.FormalDer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointFromFormalRaynaudPointSameDerivaStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_point_from_formal_raynaud_point_same_derivations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → ∀ (x' : Sp Ω ⟶ t.G.left) (hx' : x' ≫ t.G.hom = spMap φ), GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f) := by
  first | exact @GlobalTheory.Heat.FormalDer.main | exact GlobalTheory.Heat.FormalDer.main | (intros; apply GlobalTheory.Heat.FormalDer.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantVectorFieldSemiAbelianTripleAffin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantVectorFieldSemiAbelianTripleAffin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.InvFieldSemiAb

theorem exists_isInv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (v : TanM (𝟙 (Sp R)) t.G), ∃ dd : Fld t.G.left, IsInv t.G v dd := by
  intro E _ _ _ H R _ t v
  exact GlobalTheory.InvFieldBase.exists_isInv R t.G v

end GlobalTheory.InvFieldSemiAb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantVectorFieldSemiAbelianTripleAffinStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_vectorField_semiAbelian_triple_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (v : TanM (𝟙 (Sp R)) t.G), ∃ dd : Fld t.G.left, IsInv t.G v dd := by
  first | exact @GlobalTheory.InvFieldSemiAb.exists_isInv | exact GlobalTheory.InvFieldSemiAb.exists_isInv | (intros; apply GlobalTheory.InvFieldSemiAb.exists_isInv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedGroupPointSameDerivations
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalPointG

theorem exists_point_sameDerivations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → Function.Injective φ → ∀ (hx : x ≫ Y.H.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → ∃ (x' : Sp Ω ⟶ t.G.left) (hx' : x' ≫ t.G.hom = spMap φ) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) ∧ (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) ∧ (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) ∧ GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ _ _
  letI := H.starRing
  intro Y n vH dd hdd v' hv' Ω _ _ _ φ x δ hΩ hφ hx hδ hxd
  haveI := hΩ
  obtain ⟨x', hx'p, -⟩ :=
    GlobalTheory.FormalPoint.existsUnique_isPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx))
  choose dd' hdd' using fun a => GlobalTheory.T.exists_invariant_vectorField_semiAbelian_triple_affine E H R t (v' a)
  have hpt : GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx))
      (Over.homMk x'.left (Over.w x')) := hx'p
  have hder := GlobalTheory.T.uniformised_point_from_formal_raynaud_point_same_derivations E H R t P Y n (fun a => vH a) dd hdd v' hv' dd' hdd' Ω φ x δ hΩ hx hδ hxd x'.left
    (Over.w x') hpt
  obtain ⟨b, hb⟩ := GlobalTheory.T.uniformisedTangentBasis_of_raynaudBasis E H R t P Y n vH v' hv'
  refine ⟨x'.left, Over.w x', dd', hdd', hder, ?_, hpt⟩
  intro O f hO h0
  refine GlobalTheory.T.eq_zero_of_invariantDerivatives_vanish_semiAbelian R t.G t.semi n b dd' (fun a => (hb a).symm ▸ hdd' a) Ω φ hφ x'.left (Over.w x') O f hO
    fun l => ?_
  have key : ∀ l : List (Fin n), valR x'.left O (l.foldr (fun a g => dd' a O g) f) =
      l.foldr (fun a w => δ a w) (valR x'.left O f) := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.foldr_cons]; rw [hder a O _ hO, ih]
  rw [key, h0]
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons]; rw [ih, map_zero]

end GlobalTheory.FormalPointG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedGroupPointSameDerivationsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisedGroup_point_sameDerivations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → Function.Injective φ → ∀ (hx : x ≫ Y.H.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → ∃ (x' : Sp Ω ⟶ t.G.left) (hx' : x' ≫ t.G.hom = spMap φ) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) ∧ (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) ∧ (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) ∧ GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') := by
  exact @GlobalTheory.FormalPointG.exists_point_sameDerivations
end
