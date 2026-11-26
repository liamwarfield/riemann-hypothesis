module

public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPresCutCocycleLocalCoefficient
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsCocycleTorsionOfHasPres
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsAdmissibleExtensionLatticeTensor
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsCyclicGeneratorLamPowerQuotient
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.IotaCInjectiveAndEquivariant

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ContinuousLocalCoefficientRepTwist
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases UpperTheory.KN

theorem _root_.UpperTheory.KN.continuous_localCoefficientRep_twist :
    ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), GoodR D.nd i r → ∀ x, Continuous fun g => (locOC C (rTwO D.nd i r x) g).map (algebraMap ↥(OL C.LL) ↥C.LL.1) := by
  intro D i r w hw C hr x
  have h1 := GlobalTheory.PotDual.continuous_loc D i w hw _ (GlobalTheory.Pass.FamCont.stepCont D i r hr x).1
  have h2 : Continuous (fun y => C.inc y) :=
    continuous_induced_rng.2 continuous_subtype_val
  refine (h1.matrix_map h2).congr fun g => ?_
  ext a b
  rfl
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPresOfInjectiveEquivariant
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

theorem _root_.UpperTheory.KN.hasPres_of_injective_equivariant :
    ∀ {G O LL : Type} [Group G] [CommRing O] [IsNoetherianRing O] [Field LL] [Algebra O LL] {Xs : Type} {n : ℕ}
      (N : Xs → (G →* Matrix (Fin n) (Fin n) O)) {P Q : Type} [AddCommGroup P] [Module O P] [AddCommGroup Q] [Module O Q]
      (actP : G → P → P) (actQ : G → Q → Q) (ι : P →ₗ[O] Q) (f' : G → P) (f : G → Q),
      Function.Injective ι → (∀ g u, ι (actP g u) = actQ g (ι u)) → (∀ g, ι (f' g) = f g) →
      HasPres LL N actQ f → HasPres LL N actP f' := by
  intro G O LL _ _ _ _ _ Xs n N P Q _ _ _ _ actP actQ ι f' f hinj heq hf h
  obtain ⟨a, x, E, Y, hfg, hst, hE, φ, hφ, hfφ⟩ := h
  let Y' : Submodule O (Fin a → Fin n → LL) := ((LinearMap.range ι).comap φ).map Y.subtype
  have hle : Y' ≤ Y := Submodule.map_subtype_le _ _
  have hmem : ∀ y : Y, (y : Fin a → Fin n → LL) ∈ Y' ↔ φ y ∈ LinearMap.range ι := by
    intro y
    constructor
    · rintro ⟨z, hz, hzy⟩
      have : z = y := Subtype.ext hzy
      subst this
      exact hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hfg' : Y'.FG := by
    haveI : IsNoetherian O Y := isNoetherian_of_fg_of_noetherian Y hfg
    exact Submodule.FG.map _ (IsNoetherian.noetherian _)
  have hst' : ∀ g, ∀ y ∈ Y', actN LL (fun j => N (x j)) g y ∈ Y' := by
    intro g y hy
    have h1 := (hmem ⟨y, hle hy⟩).1 hy
    obtain ⟨u, hu⟩ := h1
    refine (hmem ⟨_, hst g y (hle hy)⟩).2 ⟨actP g u, ?_⟩
    rw [heq, hu]
    exact (hφ g ⟨y, hle hy⟩).symm
  have hE' : ∀ g, actN LL (fun j => N (x j)) g E - E ∈ Y' := by
    intro g
    exact (hmem ⟨_, hE g⟩).2 ⟨f' g, by rw [hf, hfφ]⟩
  let ψ : Y' →ₗ[O] LinearMap.range ι :=
    LinearMap.codRestrict _ (φ ∘ₗ Submodule.inclusion hle)
      (fun y => (hmem ⟨y.1, hle y.2⟩).1 y.2)
  let φ' : Y' →ₗ[O] P := (LinearEquiv.ofInjective ι hinj).symm.toLinearMap ∘ₗ ψ
  have key : ∀ y : Y', ι (φ' y) = φ ⟨y.1, hle y.2⟩ := by
    intro y
    have h2 : ((LinearEquiv.ofInjective ι hinj) (φ' y)) = ψ y :=
      (LinearEquiv.ofInjective ι hinj).apply_symm_apply (ψ y)
    exact congrArg Subtype.val h2
  refine ⟨a, x, E, Y', hfg', hst', hE', φ', ?_, ?_⟩
  · intro g y
    apply hinj
    rw [heq, key, key]
    exact hφ g ⟨y.1, hle y.2⟩
  · intro g
    apply hinj
    rw [key, hf]
    exact hfφ g
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralTensorTorsionCocycleOfTorsionLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralTensorTorsionCocycleOfTorsionLocal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases.LiftW

section Gen

variable {O : Type} (LL : Type) [CommRing O] [Field LL] [Algebra O LL]

def basisVec (k : ℕ) (j : Fin k) : ↥(stdG O LL k) :=
  ⟨Pi.single j 1, ⟨Pi.single j 1, by
    funext j'
    simp [Pi.single_apply]⟩⟩

def coordQ (k : ℕ) (j : Fin k) : ((Fin k → LL) ⧸ stdG O LL k) →ₗ[O] (LL ⧸ intO (O := O) LL) :=
  (stdG O LL k).mapQ (intO LL) (LinearMap.proj j) (by
    rintro _ ⟨u, rfl⟩
    exact ⟨u j, rfl⟩)

theorem coordQ_mk (k : ℕ) (j : Fin k) (v : Fin k → LL) :
    coordQ (O := O) LL k j (Submodule.Quotient.mk v) = Submodule.Quotient.mk (v j) := rfl

theorem iotaW_tmul (lam : O) (a k : ℕ) (t : ↥(stdG O LL k)) (s : LL)
    (hs : (Submodule.Quotient.mk s : LL ⧸ intO (O := O) LL) ∈ Xq LL lam a) :
    iotaW LL lam a k (t ⊗ₜ ⟨Submodule.Quotient.mk s, hs⟩) = Submodule.Quotient.mk (s • (t : Fin k → LL)) := rfl

theorem exists_sum (k : ℕ) {X : Type} [AddCommGroup X] [Module O X] (u : ↥(stdG O LL k) ⊗[O] X) :
    ∃ x : Fin k → X, u = ∑ j, basisVec LL k j ⊗ₜ[O] x j := by
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul t y =>
    obtain ⟨_, c, rfl⟩ := t
    refine ⟨fun j => c j • y, ?_⟩
    simp only [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]
    congr 1
    apply Subtype.ext
    funext j'
    simp [basisVec, Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  | add u v hu hv =>
    obtain ⟨x, rfl⟩ := hu
    obtain ⟨y, rfl⟩ := hv
    exact ⟨x + y, by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

theorem coordQ_iotaW (lam : O) (a k : ℕ) (x : Fin k → ↥(Xq LL lam a)) (j : Fin k) :
    coordQ LL k j (iotaW LL lam a k (∑ j', basisVec LL k j' ⊗ₜ[O] x j')) = x j := by
  have h : ∀ j', coordQ LL k j (iotaW LL lam a k (basisVec LL k j' ⊗ₜ[O] x j')) =
      if j = j' then (x j' : LL ⧸ intO (O := O) LL) else 0 := by
    intro j'
    obtain ⟨y, hy⟩ := x j'
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [iotaW_tmul, coordQ_mk]
    by_cases hj : j = j' <;> simp [basisVec, hj]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, h]

theorem iotaW_injective (lam : O) (a k : ℕ) : Function.Injective (iotaW LL lam a k) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨x, rfl⟩ := exists_sum LL k u
  have : x = 0 := by
    funext j
    apply Subtype.ext
    rw [← coordQ_iotaW, hu]
    simp
  simp [this]

theorem exists_iotaW (lam : O) (a k : ℕ) (q : (Fin k → LL) ⧸ stdG O LL k) (hq : lam ^ a • q = 0) :
    ∃ u, iotaW LL lam a k u = q := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hx : ∀ j, (Submodule.Quotient.mk (v j) : LL ⧸ intO (O := O) LL) ∈ Xq LL lam a := by
    intro j
    have := congrArg (coordQ LL k j) hq
    rw [map_smul, map_zero, coordQ_mk] at this
    exact this
  refine ⟨∑ j, basisVec LL k j ⊗ₜ[O] ⟨_, hx j⟩, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, iotaW_tmul]
  have : v = ∑ j, v j • (basisVec (O := O) LL k j : Fin k → LL) := by
    funext j'
    simp [basisVec, Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [this]
  exact (map_sum (stdG O LL k).mkQ _ _).symm

variable {LL}

theorem iotaW_actTw (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G]
    (lam : O) (a : ℕ) {k : ℕ} (N : G →* Matrix (Fin k) (Fin k) O) (θ : G →* Oˣ) (g : G)
    (u : ↥(stdG O LL k) ⊗[O] ↥(Xq LL lam a)) :
    iotaW LL lam a k (tableLineDegreeTwo.actTw (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) θ g u) =
      actD (stdLatG hinj N) g (iotaW LL lam a k u) := by
  induction u using TensorProduct.induction_on with
  | zero => exact (congrArg _ (map_zero _)).trans ((map_zero _).trans
      ((congrArg _ (map_zero _)).trans (map_zero _)).symm)
  | add u v hu hv =>
    have e1 := map_add (tableLineDegreeTwo.actTw (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) θ g) u v
    have e2 := map_add (actD (stdLatG hinj N) g) (iotaW LL lam a k u) (iotaW LL lam a k v)
    refine (congrArg _ e1).trans ((map_add _ _ _).trans ?_)
    rw [map_add (f := _)]
    exact (congrArg₂ (· + ·) hu hv).trans e2.symm
  | tmul t y =>
    obtain ⟨y, hy⟩ := y
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine (map_smul (iotaW LL lam a k) (((θ g)⁻¹ : Oˣ) : O)
      ((show ↥(stdG O LL k) from actT (stdLatG hinj (twistM N θ)) g t) ⊗ₜ[O] ⟨Submodule.Quotient.mk s, hy⟩)).trans ?_
    rw [iotaW_tmul, iotaW_tmul, ← Submodule.Quotient.mk_smul]
    refine congrArg Submodule.Quotient.mk ?_
    show (((θ g)⁻¹ : Oˣ) : O) • s • (((((θ g : Oˣ) : O) • N g).map (algebraMap O LL)).mulVec (t : Fin k → LL)) =
      ((N g).map (algebraMap O LL)).mulVec (s • (t : Fin k → LL))
    have e : (((θ g : Oˣ) : O) • N g).map (algebraMap O LL) = ((θ g : Oˣ) : O) • (N g).map (algebraMap O LL) := by
      ext p q
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      rw [Algebra.smul_def]
    rw [e, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_comm s, smul_smul, Units.inv_mul, one_smul]

theorem exists_twistedCocycle_lift_torsion (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (lam : O) (a : ℕ) {k : ℕ} (N : G →* Matrix (Fin k) (Fin k) O) (θ : G →* Oˣ)
    (f : G → (Fin k → LL) ⧸ stdG O LL k) (hf : f ∈ divisibleCocycles (stdLatG hinj N)) (hk : ∀ g, lam ^ a • f g = 0) :
    ∃ z' : G → ↥(stdLatG hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a),
      tableLineDegreeTwo.IsCoc (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) θ z' ∧ ∀ g, iotaW LL lam a k (z' g) = f g := by
  choose z hz using fun g => exists_iotaW LL lam a k (f g) (hk g)
  refine ⟨z, ⟨?_, fun g h => ?_⟩, hz⟩
  · refine IsLocallyConstant.desc z (iotaW LL lam a k) ?_ (iotaW_injective LL lam a k)
    have : (iotaW LL lam a k) ∘ z = f := funext hz
    rw [this]
    exact hf.1
  · apply iotaW_injective LL lam a k
    refine (hz _).trans ((hf.2 g h).trans ?_)
    refine Eq.trans ?_ (map_add (iotaW LL lam a k) (z g) _).symm
    rw [hz g, ← hz h]
    exact congrArg _ (iotaW_actTw hinj lam a N θ g (z h)).symm

theorem lift_gen (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (lam : O) (a : ℕ) {k : ℕ} (N : G →* Matrix (Fin k) (Fin k) O) (θ χ : G →* Oˣ) (hχ : χ = θ)
    (f : G → (Fin k → LL) ⧸ stdG O LL k) (hf : f ∈ divisibleCocycles (stdLatG hinj N)) (hk : ∀ g, lam ^ a • f g = 0) :
    ∃ z' : G → ↥(stdLatG hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a),
      tableLineDegreeTwo.IsCoc (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) χ z' ∧ ∀ g, iotaW LL lam a k (z' g) = f g := by
  subst hχ
  exact exists_twistedCocycle_lift_torsion hinj lam a N χ f hf hk

end Gen

theorem chiT_one {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  ext g
  simp [chiT, chiOC]

theorem lift_cocycle : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ)
      (f : Br.G D.nbr i w hw → (Fin k → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 k),
    f ∈ divisibleCocycles (latC C N) → (∀ g, lam ^ a • f g = 0) →
    ∃ z' : Br.G D.nbr i w hw → ↥(latC C (twistM N θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a),
      tableLineDegreeTwo.IsCoc (latC C (twistM N θ)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' ∧ ∀ g, iotaW ↥C.LL.1 lam a k (z' g) = f g := by
  intro D i w hw C lam _ k N θ a f hf hk
  exact lift_gen Subtype.val_injective lam a N θ (chiT C θ 1) (chiT_one C θ) f hf hk

end GlobalTheory.UseLoc.Cases.LiftW

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralTensorTorsionCocycleOfTorsionLocalStatement
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralTensorTorsion_cocycle_of_torsion_localCocycle : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ)
      (f : Br.G D.nbr i w hw → (Fin k → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 k),
    f ∈ divisibleCocycles (latC C N) → (∀ g, lam ^ a • f g = 0) →
    ∃ z' : Br.G D.nbr i w hw → ↥(latC C (twistM N θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a),
      tableLineDegreeTwo.IsCoc (latC C (twistM N θ)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' ∧ ∀ g, iotaW ↥C.LL.1 lam a k (z' g) = f g := by
  first | exact @GlobalTheory.UseLoc.Cases.LiftW.lift_cocycle | exact GlobalTheory.UseLoc.Cases.LiftW.lift_cocycle | (intros; apply GlobalTheory.UseLoc.Cases.LiftW.lift_cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleExtensionConductorTwistedCharacterAdmissi
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
private theorem isAdmCoc_latOne_of_eigenvector_characters {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
      [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
      {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
      [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
      [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
      {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
      {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [IsFractionRing O LL] {nn : ℕ}
      (emb : ZMod nn → (K₀ →ₐ[Qp] LL)) (lam : O) (jT : ZMod nn → ℤ → ℤ) (cT : G → Polynomial LL)
      {Xs : Type} {n : ℕ} (N : Xs → (G →* Matrix (Fin n) (Fin n) O)) (θ χ ψ κ κ₁ : G →* Oˣ) (p : Xs)
      (hinj : Function.Injective (algebraMap O LL)) (M : G →* Matrix (Fin 1) (Fin 1) O) (a : ℕ)
      (z : G → ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a)) (f : G → (Fin 1 → LL) ⧸ stdG O LL 1)
      (hχ : χ = θ) (hψ : ψ = κ * θ) (hκ : κ₁ = 1) (hlam : lam ≠ 0)
      (hM : ∀ g, (((χ g)⁻¹ * ψ g : Oˣ) : O) = M g 0 0)
      (hfull : ∀ x, tableLineDegreeTwo.IsFull PD emb lam jT cT (matRep (mapM (algebraMap O LL) (twistM (N x) θ))))
      (hpres : UpperTheory.KN.HasPres LL N (Q := (Fin 1 → LL) ⧸ stdG O LL 1) (fun g => actD (stdLatG hinj M) g) f)
      (hz : ∀ g, iotaC LL lam a (z g) = f g)
      (hu : ∃ u : Fin n → LL, u ≠ 0 ∧ ∀ g, ((N p g).map (algebraMap O LL)).mulVec u = ((κ g : Oˣ) : O) • u)
      (he : ∃ u : Fin n → LL, u ≠ 0 ∧ ∀ g, ((N p g).map (algebraMap O LL)).mulVec u = ((κ₁ g : Oˣ) : O) • u) :
      tableLineDegreeTwo.IsAdmCoc PD emb lam jT cT (latOne hinj ψ) ↥(Xq LL lam a) χ z := by
  obtain ⟨u, hu0, hu⟩ := hu
  obtain ⟨e, he0, he⟩ := he
  subst hκ
  have hI := UpperTheory.KN.iotaC_injective_and_equivariant hinj M χ ψ lam a hM
  have h3 : UpperTheory.KN.HasPres LL N (fun g => tableLineDegreeTwo.actTw (latOne hinj ψ) ↥(Xq LL lam a) χ g) z :=
    UpperTheory.KN.hasPres_of_injective_equivariant N _ _ (iotaC LL lam a) z f hI.1 hI.2 hz hpres
  obtain ⟨x₀, hx⟩ := UpperTheory.KN.exists_cyclic_generator_lam_power_quotient LL hinj lam a (fun h0 => hlam (hinj (h0.trans (map_zero _).symm)))
  refine ⟨0, fun b _ hb => ?_⟩
  refine UpperTheory.KN.exists_admissible_extension_latticeTensor PD emb lam jT cT N θ χ p (latOne hinj ψ) ↥(Xq LL lam a) z
    (LinearMap.toSpanSingleton LL _ u) e x₀ hχ hlam hfull h3
    (fun s t hst => smul_left_injective LL hu0 hst) (fun g v => ?_) he0 (fun g => ?_) hx b hb
  · rw [LinearMap.toSpanSingleton_apply, LinearMap.toSpanSingleton_apply, Matrix.mulVec_smul, hu g, hψ]
    funext m
    simp [Formalism.WeaklyAdmissibleFiltrations.charRep, tableLineDegreeTwo.charL, Algebra.smul_def]
    ring
  · rw [he g]
    simp

theorem _root_.GlobalTheory.T.cocycleExtension_conductorTwistedCharacter_admissible : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →
    ∀ c ∈ Finset.Icc 1 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c), ∀ (a : ℕ)
      (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsCoc (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (∀ g, iotaC ↥C.LL.1 lam a (z' g) = liftQ C.le 1 (z g)) →
    tableLineDegreeTwo.IsAdmCoc (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (tableLineDegreeTwo.jTil U w' D.R.t)
      (tableLineDegreeTwo.resPoly (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) D.R.t) (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c))
      ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hSet _ _ hDec _ c hc z hz a z' _ hz'
  have hG := GlobalTheory.Pass.goodO_ringOfIntegers (D.nd.l i) C.LL
  have hdom : IsDomain ↥(OL C.LL) := hG.1.1
  have hdvr : @IsDiscreteValuationRing ↥(OL C.LL) _ hdom := hG.1.2.1
  have hfr : IsFractionRing ↥(OL C.LL) ↥C.LL.1 := hG.1.2.2
  have hpid : IsPrincipalIdealRing ↥(OL C.LL) := hdvr.toIsPrincipalIdealRing
  have h2 := UpperTheory.KN.hasPres_cutCocycle_localCoefficient D i r w hw C (chiRatO D.nd i c) z hz
  have hE := UpperTheory.KN.exists_embedding_and_eigenvectors_of_admissible_decomposition D i r ρ π w hw C hDec
  have hκ : chiOC C (chiU D.nd i 1 * (chiU D.nd i 1)⁻¹) = 1 := by simp [chiOC]
  have H := isAdmCoc_latOne_of_eigenvector_characters (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (tableLineDegreeTwo.jTil U w' D.R.t)
    (tableLineDegreeTwo.resPoly (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) D.R.t)
    (fun x => locOC C (rTwO D.nd i r x)) θ (chiT C θ 1) (chiT C θ c)
    (chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹)) (chiOC C (chiU D.nd i 1 * (chiU D.nd i 1)⁻¹)) π
    Subtype.val_injective (locOC C (chiRatO D.nd i c)) a z' (fun g => liftQ C.le 1 (z g))
    (chiT_one_eq_theta C θ) rfl hκ hlam.ne_zero (chiT_ratio C θ c) hSet.2 h2 hz' (hE.2 c hc)
    (hE.2 1 (Finset.mem_Icc.2 ⟨le_rfl, hSet.1.1⟩))
  exact H
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleExtensionTwistedWeilCoefficientsAdmissibl
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

private theorem period_ring_generic_hodge {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL] (hdom : IsDomain O) (hpid : IsPrincipalIdealRing O)
    (hfr : IsFractionRing O LL) {nn : ℕ}
    (emb : ZMod nn → (K₀ →ₐ[Qp] LL)) (lam : O) (jT : ZMod nn → ℤ → ℤ) (cT : G → Polynomial LL)
    {Xs : Type} {n k : ℕ}
    (hinj : Function.Injective (algebraMap O LL))
    (N : Xs → (G →* Matrix (Fin n) (Fin n) O)) (M : G →* Matrix (Fin k) (Fin k) O) (θ χ : G →* Oˣ) (p : Xs) (a : ℕ)
    (z : G → ↥(stdLatG hinj (twistM M θ)).T ⊗[O] ↥(Xq LL lam a)) (f : G → (Fin k → LL) ⧸ stdG O LL k)
    (hχ : χ = θ) (hlam : lam ≠ 0)
    (hfull : ∀ x, tableLineDegreeTwo.IsFull PD emb lam jT cT (matRep (mapM (algebraMap O LL) (twistM (N x) θ))))
    (hz : ∀ g, iotaW LL lam a k (z g) = f g)
    (hpres : UpperTheory.KN.HasPres LL N (Q := (Fin k → LL) ⧸ stdG O LL k) (fun g => actD (stdLatG hinj M) g) f)
    (hW : ∃ iW : (Fin k → LL) →ₗ[LL] (Fin n → LL), Function.Injective iW ∧
      ∀ g v, iW (((M g).map (algebraMap O LL)).mulVec v) = ((N p g).map (algebraMap O LL)).mulVec (iW v))
    (ψ : G →* Oˣ) (hψ : ∀ g, ψ g = 1)
    (he : ∃ e : Fin n → LL, e ≠ 0 ∧ ∀ g, ((N p g).map (algebraMap O LL)).mulVec e = ((ψ g : Oˣ) : O) • e) :
    tableLineDegreeTwo.IsAdmCoc PD emb lam jT cT (stdLatG hinj (twistM M θ)) ↥(Xq LL lam a) χ z := by
  subst hχ
  obtain ⟨iW, hW1, hW2⟩ := hW
  obtain ⟨e, he1, he2⟩ := he
  obtain ⟨x₀, hx⟩ := UpperTheory.KN.exists_cyclic_generator_lam_power_quotient LL hinj lam a (fun h0 => hlam (hinj (h0.trans (map_zero _).symm)))
  have h3 : UpperTheory.KN.HasPres LL N (fun g => tableLineDegreeTwo.actTw (stdLatG hinj (twistM M χ)) ↥(Xq LL lam a) χ g) z :=
    UpperTheory.KN.hasPres_of_injective_equivariant _ _ _ (iotaW LL lam a k) z f (LiftW.iotaW_injective LL lam a k)
      (fun g u => LiftW.iotaW_actTw hinj lam a M χ g u) hz hpres
  refine ⟨0, fun b _ hb => ?_⟩
  refine UpperTheory.KN.exists_admissible_extension_latticeTensor PD emb lam jT cT N χ χ p (stdLatG hinj (twistM M χ)) ↥(Xq LL lam a) z iW e x₀ rfl hlam
    hfull h3 hW1 (fun g v => ?_) he1 (fun g => ?_) hx b hb
  · refine (congrArg _ (matRep_twistM_apply M χ g v)).trans ?_
    rw [LinearMap.map_smul_of_tower]
    exact congrArg _ (hW2 g v)
  · rw [he2 g, hψ g, Units.val_one, one_smul]

private theorem chi_mul_inv_eq_one {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (g : Br.G D.nbr i w hw) :
    chiOC C (chiU D.nd i 1 * (chiU D.nd i 1)⁻¹) g = 1 := by
  simp [chiOC]

attribute [-instance] GlobalTheory.AdmLoc.modFun in
theorem _root_.GlobalTheory.T.cocycleExtension_twistedWeilCoefficients_admissible : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →
    ∀ z ∈ cutCoc i w hw r Set.univ (WpO D.nd i ρ π), ∀ (a : ℕ)
      (z' : Br.G D.nbr i w hw → ↥(latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsCoc (latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (∀ g, iotaW ↥C.LL.1 lam a D.R.r (z' g) = liftQ C.le D.R.r (z g)) →
    tableLineDegreeTwo.IsAdmCoc (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (tableLineDegreeTwo.jTil U w' D.R.t)
      (tableLineDegreeTwo.resPoly (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) D.R.t) (latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hSet _ _ hDec _ z hz a z' _ hz'
  have hG := GlobalTheory.Pass.goodO_ringOfIntegers (D.nd.l i) C.LL
  have hdom : IsDomain ↥(OL C.LL) := hG.1.1
  have hdvr : @IsDiscreteValuationRing ↥(OL C.LL) _ hdom := hG.1.2.1
  have hE := UpperTheory.KN.exists_embedding_and_eigenvectors_of_admissible_decomposition D i r ρ π w hw C hDec
  exact period_ring_generic_hodge (Br.PD D.loc D.nbr i w hw) hdom hdvr.toIsPrincipalIdealRing hG.1.2.2 (embC HW C hA) lam _ _
    Subtype.val_injective (fun x => locOC C (rTwO D.nd i r x)) (locOC C (WpO D.nd i ρ π)) θ (chiT C θ 1) π a z'
    (fun g => liftQ C.le D.R.r (z g)) (LiftW.chiT_one C θ) hlam.ne_zero hSet.2 hz'
    (UpperTheory.KN.hasPres_cutCocycle_localCoefficient D i r w hw C (WpO D.nd i ρ π) z hz) hE.1 _ (chi_mul_inv_eq_one C)
    (hE.2 1 (Finset.mem_Icc.2 ⟨le_rfl, hSet.1.1⟩))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutCocyclesLocallyConstantKilledByUniformiserPow
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
theorem _root_.GlobalTheory.T.cutCocycles_locallyConstant_killed_by_uniformiserPow : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (lam : ↥(OL C.LL)), Irreducible lam → GoodR D.nd i r → TruncatedSeriesCountingIdentities.FamilyContinuous i r →
    ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), ∀ z ∈ cutCoc i w hw r Set.univ M,
    ∃ a : ℕ, (fun g => liftQ C.le k (z g)) ∈ divisibleCocycles (latC C (locOC C M)) ∧ ∀ g, lam ^ a • liftQ C.le k (z g) = 0 := by
  intro D i r w hw C lam hlam hGood _ k M z hz
  have hG := GlobalTheory.Pass.goodO_ringOfIntegers (D.nd.l i) C.LL
  have hdom : IsDomain ↥(OL C.LL) := hG.1.1
  have hdvr : @IsDiscreteValuationRing ↥(OL C.LL) _ hdom := hG.1.2.1
  have hfr : IsFractionRing ↥(OL C.LL) ↥C.LL.1 := hG.1.2.2
  have htop : IsTopologicalRing ↥C.LL.1 := hG.2.2.2.1
  have hopen := hG.2.2.2.2
  have h1 := UpperTheory.KN.continuous_localCoefficientRep_twist D i r w hw C hGood
  have h2 := UpperTheory.KN.hasPres_cutCocycle_localCoefficient D i r w hw C M z hz
  have h3 := @UpperTheory.KN.exists_cocycle_torsion_of_hasPres (Br.G D.nbr i w hw) ↥(OL C.LL) ↥C.LL.1 _ _ _ hdom hdvr _ _ htop _ hfr Subtype.val_injective lam _ _ _
    (fun x => locOC C (rTwO D.nd i r x)) (locOC C M) (fun g => liftQ C.le k (z g)) hlam hopen h1
  exact h3 h2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedReadOfTrivialTwistCoboundaryOnSubgro
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedReadOfTrivialTwistCoboundaryOnSubgro
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases

section Gen

variable {G : Type} [Group G] {O LL : Type} [CommRing O] [Field LL] [Algebra O LL]

theorem actT_latOne (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ) (g : G) :
    actT (latOne (LL := LL) hinj ψ) g = ((ψ g : Oˣ) : O) • LinearMap.id := by
  ext t
  change Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := LL) ψ) g (t : LL) = (((ψ g : Oˣ) : O) • t : LL)
  simp [Formalism.WeaklyAdmissibleFiltrations.charRep, tableLineDegreeTwo.charL, Algebra.smul_def]

theorem actTw_latOne [TopologicalSpace G] (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ) (X : Type)
    [AddCommGroup X] [Module O X] (g : G) :
    tableLineDegreeTwo.actTw (latOne (LL := LL) hinj ψ) X ψ g = LinearMap.id := by
  rw [tableLineDegreeTwo.actTw, actT_latOne, LinearMap.rTensor_smul, LinearMap.rTensor_id, smul_smul]
  simp

theorem eq_zero_of_isUnr_latOne [TopologicalSpace G] (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ)
    (X : Type) [AddCommGroup X] [Module O X] (I : Subgroup G) (z : G → ↥(latOne (LL := LL) hinj ψ).T ⊗[O] X)
    (h : tableLineDegreeTwo.IsUnr (latOne (LL := LL) hinj ψ) X ψ I z) : ∀ g ∈ I, z g = 0 := by
  obtain ⟨m, hm⟩ := h
  intro g hg
  rw [hm g hg, actTw_latOne, LinearMap.id_apply, sub_self]

theorem mem_Z1urD_of_eq_zero {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (I : Subgroup G) (c : G → V ⧸ L.T)
    (h : ∀ g ∈ I, c g = 0) : c ∈ Z1urD L I :=
  ⟨0, fun g hg => by rw [h g hg, map_zero, sub_zero]⟩

end Gen

end GlobalTheory.UseLoc.Cases

theorem GlobalTheory.UseLoc.Cases.readU_unr : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ) (I : Subgroup (Br.G D.nbr i w hw))
    (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsUnr (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) I z' →
    (fun g => iotaC ↥C.LL.1 lam a (z' g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) I := by
  intro D i w hw C lam θ a I z' h
  exact GlobalTheory.UseLoc.Cases.mem_Z1urD_of_eq_zero _ I _ (fun g hg =>
    (congrArg (iotaC ↥C.LL.1 lam a) (GlobalTheory.UseLoc.Cases.eq_zero_of_isUnr_latOne _ _ _ I z' h g hg)).trans (map_zero _))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedReadOfTrivialTwistCoboundaryOnSubgroStatement
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramified_read_of_trivialTwist_coboundary_on_subgroup : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ) (I : Subgroup (Br.G D.nbr i w hw))
    (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsUnr (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) I z' →
    (fun g => iotaC ↥C.LL.1 lam a (z' g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) I := by
  first | exact @GlobalTheory.UseLoc.Cases.readU_unr | exact GlobalTheory.UseLoc.Cases.readU_unr | (intros; apply GlobalTheory.UseLoc.Cases.readU_unr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepresentationOfIntegralMatricesEqInvTwistedChar
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepresentationOfIntegralMatricesEqInvTwistedChar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases

theorem chiOC_one {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) : chiOC C 1 = 1 := by
  ext g; simp [chiOC]

theorem chiT_one {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  rw [chiT, mul_inv_cancel, chiOC_one, one_mul]

theorem repV_eq_inv_smul_twist : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (g : Br.G D.nbr i w hw),
    repV C N g = ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ 1) g)⁻¹ : (↥C.LL.1)ˣ).val • repV C (twistM N θ) g := by
  intro D i w hw C k N θ g
  rw [chiT_one]
  have h : repV C (twistM N θ) g = (algebraMap (↥(OL C.LL)) (↥C.LL.1) (θ g : ↥(OL C.LL))) • repV C N g := by
    simp only [repV, matRep, mapM, twistM]
    simp [RingHom.mapMatrix_apply, Matrix.map_smul', Matrix.toLinAlgEquiv'_apply]
    rw [show ((θ g : ↥(OL C.LL)) • N g).map (algebraMap ↥(OL C.LL) ↥C.LL.1)
        = (algebraMap ↥(OL C.LL) ↥C.LL.1 (θ g : ↥(OL C.LL))) • (N g).map (algebraMap ↥(OL C.LL) ↥C.LL.1) from by
          ext a b; simp [Matrix.map_apply], map_smul]
    rfl
  rw [h, smul_smul]
  simp [tableLineDegreeTwo.charL]

end GlobalTheory.UseLoc.Cases
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepresentationOfIntegralMatricesEqInvTwistedCharStatement
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representationOfIntegralMatrices_eq_inv_twistedChar_smul : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (g : Br.G D.nbr i w hw),
    repV C N g = ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ 1) g)⁻¹ : (↥C.LL.1)ˣ).val • repV C (twistM N θ) g := by
  first | exact @GlobalTheory.UseLoc.Cases.repV_eq_inv_smul_twist | exact GlobalTheory.UseLoc.Cases.repV_eq_inv_smul_twist | (intros; apply GlobalTheory.UseLoc.Cases.repV_eq_inv_smul_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLambdaPowerTorsionFieldModInt
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLambdaPowerTorsionFieldModInt
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases

theorem finite_Xq {l : ℕ} [Fact l.Prime] (LL : FinExt l) (lam : ↥(OL LL)) (hlam : Irreducible lam) (a : ℕ) :
    Finite ↥(Xq ↥LL.1 lam a) := by
  classical
  haveI := GlobalTheory.FullCharpoly.hasFiniteQuotients_OL LL
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hne : lam ^ a ≠ 0 := pow_ne_zero _ hlam.ne_zero
  have hK : algebraMap ↥(OL LL) ↥LL.1 (lam ^ a) ≠ 0 := by
    intro h; exact hne (hinj (by rw [h, map_zero]))
  haveI : Finite (↥(OL LL) ⧸ Ideal.span {lam ^ a}) := Ring.HasFiniteQuotients.finiteQuotient (by
    rwa [Ne, Ideal.span_singleton_eq_bot])
  have hex : ∀ x : ↥(Xq ↥LL.1 lam a), ∃ c : ↥(OL LL), ∃ s : ↥LL.1,
      Submodule.Quotient.mk (p := intO (O := ↥(OL LL)) ↥LL.1) s = x.1 ∧ algebraMap ↥(OL LL) ↥LL.1 c = lam ^ a • s := by
    intro x
    obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ x.1
    have hx := x.2
    simp only [Xq, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hx
    rw [← hs, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨c, hc⟩ := hx
    exact ⟨c, s, hs, hc⟩
  let f : ↥(Xq ↥LL.1 lam a) → ↥(OL LL) ⧸ Ideal.span {lam ^ a} := fun x => Ideal.Quotient.mk _ (hex x).choose
  refine Finite.of_injective f ?_
  intro x y hxy
  obtain ⟨s, hs, hc⟩ := (hex x).choose_spec
  obtain ⟨t, ht, hd⟩ := (hex y).choose_spec
  have h1 := hxy
  simp only [f, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h1
  obtain ⟨d, hd'⟩ := h1
  apply Subtype.ext
  rw [← hs, ← ht, ← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
  refine ⟨d, ?_⟩
  have h2 : algebraMap ↥(OL LL) ↥LL.1 (lam ^ a) * (s - t) = algebraMap ↥(OL LL) ↥LL.1 (lam ^ a) * algebraMap ↥(OL LL) ↥LL.1 d := by
    rw [← map_mul, mul_comm (lam ^ a) d, hd', map_sub, hc, hd, Algebra.smul_def, Algebra.smul_def, mul_sub]
  have := mul_left_cancel₀ hK h2
  simp only [Algebra.linearMap_apply]
  exact this.symm

end GlobalTheory.UseLoc.Cases
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLambdaPowerTorsionFieldModIntStatement
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lambdaPowerTorsionFieldModInt : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l) (lam : ↥(OL LL)), Irreducible lam → ∀ a : ℕ, Finite ↥(Xq ↥LL.1 lam a) := by
  first | exact @GlobalTheory.UseLoc.Cases.finite_Xq | exact GlobalTheory.UseLoc.Cases.finite_Xq | (intros; apply GlobalTheory.UseLoc.Cases.finite_Xq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCoboundaryReadOfTwistedCharacterCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCoboundaryReadOfTwistedCharacterCoboundary
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases.ReadC

section Gen
variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] {G : Type} [Group G]

theorem actT_latOne (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ) (g : G) :
    Formalism.WeaklyAdmissibleFiltrations.actT (latOne hinj ψ) g = ((ψ g : Oˣ) : O) • LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x, hx⟩
  apply Subtype.ext
  simp only [Formalism.WeaklyAdmissibleFiltrations.actT, LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul]
  show ((tableLineDegreeTwo.charL (LL := LL) ψ g : LLˣ) : LL) • x = ((ψ g : Oˣ) : O) • x
  simp [tableLineDegreeTwo.charL, Algebra.smul_def]

theorem actTw_latOne (hinj : Function.Injective (algebraMap O LL)) (lam : O) (a : ℕ) (ψ χ : G →* Oˣ) (g : G) :
    tableLineDegreeTwo.actTw (latOne hinj ψ) (Xq LL lam a) χ g = (((χ g)⁻¹ * ψ g : Oˣ) : O) • LinearMap.id := by
  rw [tableLineDegreeTwo.actTw, actT_latOne, LinearMap.rTensor_smul, LinearMap.rTensor_id, smul_smul, Units.val_mul]

theorem actD_one (hinj : Function.Injective (algebraMap O LL)) (M : G →* Matrix (Fin 1) (Fin 1) O) (g : G) :
    actD (stdLatG hinj M) g = M g 0 0 • LinearMap.id := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.smul_apply, LinearMap.id_apply, actD,
    ← Submodule.Quotient.mk_smul]
  erw [Submodule.mapQ_apply]
  congr 1
  funext j
  fin_cases j
  simp [stdLatG, matRep, mapM, Matrix.mulVec, dotProduct, Algebra.smul_def]

theorem equivG (hinj : Function.Injective (algebraMap O LL)) (lam : O) (a : ℕ) (ψ χ : G →* Oˣ)
    (M : G →* Matrix (Fin 1) (Fin 1) O) (hM : ∀ g, M g 0 0 = (((χ g)⁻¹ * ψ g : Oˣ) : O)) (g : G)
    (u : ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a)) :
    iotaC LL lam a (tableLineDegreeTwo.actTw (latOne hinj ψ) (Xq LL lam a) χ g u) =
      actD (stdLatG hinj M) g (iotaC LL lam a u) := by
  have h1 : tableLineDegreeTwo.actTw (latOne hinj ψ) (Xq LL lam a) χ g u = (((χ g)⁻¹ * ψ g : Oˣ) : O) • u := by
    rw [actTw_latOne]; rfl
  rw [h1, actD_one, hM]
  exact (iotaC LL lam a).map_smul _ u

end Gen
end GlobalTheory.UseLoc.Cases.ReadC

namespace GlobalTheory.UseLoc.Cases.ReadC
section Gen2
variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] {G : Type} [Group G]

theorem readG (hinj : Function.Injective (algebraMap O LL)) (lam : O) (a : ℕ) (ψ χ : G →* Oˣ)
    (M : G →* Matrix (Fin 1) (Fin 1) O) (hM : ∀ g, M g 0 0 = (((χ g)⁻¹ * ψ g : Oˣ) : O))
    (z' : G → ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a))
    (hz : tableLineDegreeTwo.IsCob (latOne hinj ψ) ↥(Xq LL lam a) χ z') :
    (fun g => iotaC LL lam a (z' g)) ∈ BD (stdLatG hinj M) := by
  obtain ⟨m, hm⟩ := hz
  refine ⟨iotaC LL lam a m, ?_⟩
  funext g
  have key := equivG hinj lam a ψ χ M hM g m
  rw [hm g]
  refine Eq.trans ?_ ((iotaC LL lam a).map_sub _ m).symm
  exact (congrArg (fun y => y - iotaC LL lam a m) key).symm

end Gen2
end GlobalTheory.UseLoc.Cases.ReadC

namespace GlobalTheory.UseLoc.Cases.ReadC

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem entry (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (c : ℕ) (g : Br.G D.nbr i w hw) :
    locOC C (chiRatO D.nd i c) g 0 0 = ((chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) := by
  simp [locOC, chiOC, Br.locO, mapM, chiRatO, twistM, Br.iota]

theorem ratio (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ) (g : Br.G D.nbr i w hw) :
    (chiT C θ 1 g)⁻¹ * chiT C θ c g = chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g := by
  have h1 : chiOC C 1 g = 1 := by simp [chiOC]
  simp only [chiT, MonoidHom.mul_apply, mul_inv_cancel, h1, one_mul]
  rw [mul_comm (chiOC C _ g) (θ g)]
  exact inv_mul_cancel_left _ _

theorem entry_ratio (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ) (g : Br.G D.nbr i w hw) :
    locOC C (chiRatO D.nd i c) g 0 0 = (((chiT C θ 1 g)⁻¹ * chiT C θ c g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) := by
  rw [entry, ratio]

end GlobalTheory.UseLoc.Cases.ReadC

theorem GlobalTheory.UseLoc.Cases.readC_cob : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c a : ℕ)
    (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsCob (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (fun g => iotaC ↥C.LL.1 lam a (z' g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c))) :=
  fun D i w hw C lam θ c a z' hz =>
    ReadC.readG (LL := ↥C.LL.1) Subtype.val_injective lam a (chiT C θ c) (chiT C θ 1) (locOC C (chiRatO D.nd i c))
      (ReadC.entry_ratio C θ c) z' hz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCoboundaryReadOfTwistedCharacterCoboundaryStatement
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCoboundary_read_of_twistedCharacter_coboundary : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c a : ℕ)
    (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsCob (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (fun g => iotaC ↥C.LL.1 lam a (z' g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c))) := by
  first | exact @GlobalTheory.UseLoc.Cases.readC_cob | exact GlobalTheory.UseLoc.Cases.readC_cob | (intros; apply GlobalTheory.UseLoc.Cases.readC_cob <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedEnlargementCutCocyclesBlochKato
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass
  GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.UseLoc.Cases

set_option maxHeartbeats 8000000 in
theorem partW : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →

    ∀ z ∈ cutCoc i w hw r Set.univ (WpO D.nd i ρ π),
      (fun g => liftQ C.le D.R.r (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C (WpO D.nd i ρ π))) := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont z hz
  have h5' : 5 ≤ (Br.PD D.loc D.nbr i w hw).p := by rw [Br.PD_p]; exact h5
  have hT := hTop h5' D.R.t h w' η typ U (Fin D.R.r → ↥C.LL.1) (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ))
    (latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) hSet.1
  obtain ⟨a, hZ, hk⟩ := GlobalTheory.T.cutCocycles_locallyConstant_killed_by_uniformiserPow D i r w hw C lam hlam hGood hCont (WpO D.nd i ρ π) z hz
  haveI := GlobalTheory.T.finite_lambdaPowerTorsionFieldModInt C.LL lam hlam a
  obtain ⟨z', hcoc, hz'⟩ := GlobalTheory.T.exists_integralTensorTorsion_cocycle_of_torsion_localCocycle D i w hw C lam hlam (locOC C (WpO D.nd i ρ π)) θ a
    (fun g => liftQ C.le D.R.r (z g)) hZ hk
  have hz'' : ∀ g, iotaW ↥C.LL.1 lam a D.R.r (z' g) = liftQ C.le D.R.r (z g) := hz'
  have hadm := GlobalTheory.T.cocycleExtension_twistedWeilCoefficients_admissible D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hSet hGood hπ hDec hCont z hz a z' hcoc hz''
  have hin := ((hT ↥(Xq ↥C.LL.1 lam a)).1 (repV C (locOC C (WpO D.nd i ρ π)))
    (latC C (locOC C (WpO D.nd i ρ π))) (GlobalTheory.T.representationOfIntegralMatrices_eq_inv_twistedChar_smul D i w hw C (locOC C (WpO D.nd i ρ π)) θ) rfl z' hcoc).1 hadm
  have hr := GlobalTheory.T.isBlochKato_read_of_tensor_selmer_add_coboundary D i w hw C lam (locOC C (WpO D.nd i ρ π)) θ a z' hin
  have e : (fun g => liftQ C.le D.R.r (z g)) = fun g => iotaW ↥C.LL.1 lam a D.R.r (z' g) :=
    funext fun g => (hz'' g).symm
  rw [e]
  exact hr

set_option maxHeartbeats 8000000 in
theorem partC : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →

    ∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c),
      (fun g => liftQ C.le 1 (z g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c))) := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont c hc z hz
  have h5' : 5 ≤ (Br.PD D.loc D.nbr i w hw).p := by rw [Br.PD_p]; exact h5
  have hT := hTop h5' D.R.t h w' η typ U (Fin D.R.r → ↥C.LL.1) (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ))
    (latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) hSet.1
  obtain ⟨a, hZ, hk⟩ := GlobalTheory.T.cutCocycles_locallyConstant_killed_by_uniformiserPow D i r w hw C lam hlam hGood hCont (chiRatO D.nd i c) z hz
  haveI := GlobalTheory.T.finite_lambdaPowerTorsionFieldModInt C.LL lam hlam a
  obtain ⟨z', hcoc, hz'⟩ := GlobalTheory.T.exists_twistedCharacter_cocycle_of_torsion_localCocycle D i w hw C lam hlam θ c a (fun g => liftQ C.le 1 (z g)) hZ hk
  have hz'' : ∀ g, iotaC ↥C.LL.1 lam a (z' g) = liftQ C.le 1 (z g) := hz'
  have hc1 : c ∈ Finset.Icc 1 D.R.t :=
    Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hc).1; omega, (Finset.mem_Icc.1 hc).2⟩
  have hadm := GlobalTheory.T.cocycleExtension_conductorTwistedCharacter_admissible D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hSet hGood hπ hDec hCont c hc1 z hz a z'
    hcoc hz''
  have hin := ((hT ↥(Xq ↥C.LL.1 lam a)).2.1 c hc (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) z'
    hcoc).1 hadm
  have hr := GlobalTheory.T.isCoboundary_read_of_twistedCharacter_coboundary D i w hw C lam θ c a z' hin
  have e : (fun g => liftQ C.le 1 (z g)) = fun g => iotaC ↥C.LL.1 lam a (z' g) :=
    funext fun g => (hz'' g).symm
  rw [e]
  exact hr

set_option maxHeartbeats 8000000 in
theorem partU : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →

    ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1),
      (fun g => liftQ C.le 1 (z g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) (IK (D.nbr i w hw).Kw) := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont z hz
  have h5' : 5 ≤ (Br.PD D.loc D.nbr i w hw).p := by rw [Br.PD_p]; exact h5
  have hT := hTop h5' D.R.t h w' η typ U (Fin D.R.r → ↥C.LL.1) (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ))
    (latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) hSet.1
  obtain ⟨a, hZ, hk⟩ := GlobalTheory.T.cutCocycles_locallyConstant_killed_by_uniformiserPow D i r w hw C lam hlam hGood hCont (chiRatO D.nd i 1) z hz
  haveI := GlobalTheory.T.finite_lambdaPowerTorsionFieldModInt C.LL lam hlam a
  obtain ⟨z', hcoc, hz'⟩ := GlobalTheory.T.exists_twistedCharacter_cocycle_of_torsion_localCocycle D i w hw C lam hlam θ 1 a (fun g => liftQ C.le 1 (z g)) hZ hk
  have hz'' : ∀ g, iotaC ↥C.LL.1 lam a (z' g) = liftQ C.le 1 (z g) := hz'
  have hc1 : 1 ∈ Finset.Icc 1 D.R.t := Finset.mem_Icc.2 ⟨le_rfl, hSet.1.1⟩
  have hadm := GlobalTheory.T.cocycleExtension_conductorTwistedCharacter_admissible D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hSet hGood hπ hDec hCont 1 hc1 z hz a z'
    hcoc hz''
  have hin := ((hT ↥(Xq ↥C.LL.1 lam a)).2.2 (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)) z'
    hcoc).1 hadm
  have hr := GlobalTheory.T.isUnramified_read_of_trivialTwist_coboundary_on_subgroup D i w hw C lam θ a _ z' hin
  have e : (fun g => liftQ C.le 1 (z g)) = fun g => iotaC ↥C.LL.1 lam a (z' g) :=
    funext fun g => (hz'' g).symm
  rw [e]
  exact hr

theorem main : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →
    (∀ z ∈ cutCoc i w hw r Set.univ (WpO D.nd i ρ π),
      (fun g => liftQ C.le D.R.r (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C (WpO D.nd i ρ π)))) ∧
    (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c),
      (fun g => liftQ C.le 1 (z g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c)))) ∧
    (∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1),
      (fun g => liftQ C.le 1 (z g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) (IK (D.nbr i w hw).Kw)) := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont
  exact ⟨partW D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont,
    partC D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont,
    partU D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont⟩

end GlobalTheory.UseLoc.Cases

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedEnlargementCutCocyclesBlochKatoStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedEnlargement_cut_cocycles_blochKato : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →
    (∀ z ∈ cutCoc i w hw r Set.univ (WpO D.nd i ρ π),
      (fun g => liftQ C.le D.R.r (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C (WpO D.nd i ρ π)))) ∧
    (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c),
      (fun g => liftQ C.le 1 (z g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c)))) ∧
    (∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1),
      (fun g => liftQ C.le 1 (z g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) (IK (D.nbr i w hw).Kw)) := by
  first | exact @GlobalTheory.UseLoc.Cases.main | exact GlobalTheory.UseLoc.Cases.main | (intros; apply GlobalTheory.UseLoc.Cases.main <;> assumption)
end
