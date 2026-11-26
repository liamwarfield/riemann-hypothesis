module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalRiemannExtension
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalImageNull
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StImageDimLe
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicJacobianNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

namespace InjectiveHolomorphicJacobianNeZero

theorem det_fin_one (A : (Fin 1 → ℂ) →ₗ[ℂ] Fin 1 → ℂ) : LinearMap.det A = A 1 0 := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin 1)), Matrix.det_unique, LinearMap.toMatrix_apply]
  simp only [Pi.basisFun_apply, Pi.basisFun_repr]
  have h1 : (Pi.single (default : Fin 1) (1 : ℂ) : Fin 1 → ℂ) = 1 := by
    funext i
    fin_cases i
    rfl
  rw [h1]
  rfl

theorem one {U : Set (Fin 1 → ℂ)} {f : (Fin 1 → ℂ) → Fin 1 → ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U) {x : Fin 1 → ℂ} (hx : x ∈ U) :
    LinearMap.det (fderiv ℂ f x : (Fin 1 → ℂ) →ₗ[ℂ] Fin 1 → ℂ) ≠ 0 := by
  set e : (Fin 1 → ℂ) ≃L[ℂ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ with he
  set φ : ℂ → ℂ := fun z => e (f (e.symm z)) with hφ
  have hD : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hφd : DifferentiableOn ℂ φ (e.symm ⁻¹' U) :=
    e.differentiable.comp_differentiableOn (hf.comp e.symm.differentiable.differentiableOn fun _ h => h)
  have hφi : Set.InjOn φ (e.symm ⁻¹' U) := fun s hs t ht h =>
    e.symm.injective (hinj hs ht (e.injective h))
  have hxD : e x ∈ e.symm ⁻¹' U := by simpa using hx
  have hne := InjectiveHolomorphicDerivNeZero.proof _ φ hD hφd hφi (e x) hxD
  have hfx : HasFDerivAt f (fderiv ℂ f x) x := (hf.differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hφx : HasFDerivAt φ ((e : (Fin 1 → ℂ) →L[ℂ] ℂ).comp ((fderiv ℂ f x).comp
      (e.symm : ℂ →L[ℂ] Fin 1 → ℂ))) (e x) := by
    have h1 : HasFDerivAt f (fderiv ℂ f x) (e.symm (e x)) := by simpa using hfx
    exact e.hasFDerivAt.comp (e x) (h1.comp (e x) e.symm.hasFDerivAt)
  rw [hφx.hasDerivAt.deriv] at hne
  rw [det_fin_one]
  simpa [he] using hne

end InjectiveHolomorphicJacobianNeZero

theorem InjectiveHolomorphicJacobianNeZero.proof (hF : HolomorphicKernelFibre.Statement)
    (hC : CriticalFlatNotInjective.Statement) : InjectiveHolomorphicJacobianNeZero.Statement := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro U f hU hf hinj x hx hdet
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · rw [LinearMap.det_eq_one_of_subsingleton] at hdet
      exact one_ne_zero hdet
    · exact InjectiveHolomorphicJacobianNeZero.one hU hf hinj hx hdet
  · by_cases hall : ∀ b ∈ U, LinearMap.det (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) = 0 →
        fderiv ℂ f b = 0
    · exact hC k U f x hk hU hf hx hdet hall hinj
    push Not at hall
    obtain ⟨b, hb, hdb, hne⟩ := hall
    set d := Module.finrank ℂ (LinearMap.ker (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) with hd
    have hd0 : 0 < d := by
      rw [hd, Module.finrank_pos_iff_exists_ne_zero]
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
        (LinearMap.bot_lt_ker_of_det_eq_zero hdb).ne'
      exact ⟨⟨v, hv⟩, by simpa using hv0⟩
    have hdk : d < k := by
      have hker : LinearMap.ker (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) ≠ ⊤ := by
        rw [Ne, LinearMap.ker_eq_top]
        intro h0
        exact hne (ContinuousLinearMap.coe_injective (by simpa using h0))
      simpa [Module.finrank_fin_fun] using Submodule.finrank_lt hker
    obtain ⟨V, y, γ, ℓ, hV, hy, hγ, hmaps, hγinj, hfib, hzero⟩ := hF k U f b hU hf hb d rfl
    have hhd : DifferentiableOn ℂ (fun t => ℓ (f (γ t))) V :=
      ℓ.differentiable.comp_differentiableOn (hf.comp hγ hmaps)
    have hhinj : Set.InjOn (fun t => ℓ (f (γ t))) V := fun s hs t ht h =>
      hγinj hs ht (hinj (hmaps hs) (hmaps ht) (hfib s hs t ht h))
    apply ih d hdk V _ hV hhd hhinj y hy
    rw [hzero, ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero, Module.finrank_fin_fun]
    exact zero_pow hd0.ne'

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericProjectionFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Matrix

noncomputable section

def entries {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : Fin a × Fin b → ℂ := fun ij => A ij.1 ij.2

def rowsPoly {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  bind₁ (fun ij : Fin d × Fin n => ∑ l, C (F (s ij.1) l) * X (l, ij.2)) p

theorem eval_rowsPoly {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) :
    eval (entries U) (rowsPoly F s p) = eval (entries ((F * U).submatrix s id)) p := by
  change eval₂Hom (RingHom.id ℂ) (entries U) (bind₁ _ p) = eval₂Hom (RingHom.id ℂ) _ p
  rw [eval₂Hom_bind₁]
  congr 2
  funext ij
  simp [entries, Matrix.mul_apply]

theorem exists_rows_eq {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) (A : Matrix (Fin d) (Fin n) ℂ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, (F * U).submatrix s id = A := by
  refine ⟨star F * Matrix.of (Function.extend s (fun i => A i) 0), ?_⟩
  rw [← Matrix.mul_assoc, mem_unitaryGroup_iff.mp hF, Matrix.one_mul]
  ext i j
  simp [hs.extend_apply]

theorem rowsPoly_ne_zero {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) {p : MvPolynomial (Fin d × Fin n) ℂ}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : eval (entries A) p ≠ 0) : rowsPoly F s p ≠ 0 := by
  obtain ⟨U, hU⟩ := exists_rows_eq hF hs A
  intro h
  apply hA
  rw [← hU, ← eval_rowsPoly, h, map_zero]

theorem GenericProjectionFinite.proof (hO : FiniteProjectionsContainOpen.Statement)
    (hU : UnitaryZariskiDense.Statement) :
    GenericProjectionFinite.Statement := by
  classical
  intro n d J hJ hd
  obtain ⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hW⟩ := hO n d J hJ hd
  have good : ∀ A : Matrix (Fin d) (Fin n) ℂ, (∃ p ∈ S, eval (entries A) p ≠ 0) →
      IsFiniteProjection J A := fun A hA => hW (by rw [hS]; exact hA)
  have hA₀' := hA₀
  rw [hS] at hA₀'
  obtain ⟨p, hpS, hp⟩ := hA₀'
  have hdn : d ≤ n := by
    have h := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
    exact_mod_cast h
  refine ⟨⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, fun A hA => hW hA⟩, ⟨A₀, hW hA₀⟩, fun D hD hcl => ?_, fun m F => ?_⟩
  · obtain ⟨U, hUu, hUp⟩ := hU n (rowsPoly 1 (Fin.castLE hdn) p)
      (rowsPoly_ne_zero (one_mem _) (Fin.castLE_injective hdn) hp)
    have hUp' : eval (entries (U.submatrix (Fin.castLE hdn) id)) p ≠ 0 := by
      have := eval_rowsPoly 1 (Fin.castLE hdn) p U
      rw [Matrix.one_mul] at this
      exact this ▸ hUp
    have hAo : U.submatrix (Fin.castLE hdn) id ∈ orthoRows d n := by
      show _ * _ = _
      rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
        ← star_eq_conjTranspose, mem_unitaryGroup_iff.mp hUu,
        submatrix_one _ (Fin.castLE_injective hdn)]
    have hopen : IsOpen {B : Matrix (Fin d) (Fin n) ℂ | eval (entries B) p ≠ 0} :=
      isOpen_ne_fun ((MvPolynomial.continuous_eval p).comp
        (continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2)) continuous_const
    obtain ⟨B, hBp, hBD⟩ := mem_closure_iff.mp (hcl hAo) _ hopen hUp'
    exact ⟨B, hBD, good B ⟨p, hpS, hBp⟩⟩
  · have hQ : (∏ ks : Fin m × (Fin d ↪ Fin n), rowsPoly (F ks.1 : Matrix (Fin n) (Fin n) ℂ) ks.2 p) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun ks _ => rowsPoly_ne_zero (F ks.1).2 ks.2.injective hp
    obtain ⟨U, hUu, hUQ⟩ := hU n _ hQ
    refine ⟨U, hUu, fun k s => good _ ⟨p, hpS, ?_⟩⟩
    rw [map_prod] at hUQ
    have := Finset.prod_ne_zero_iff.mp hUQ (k, s) (Finset.mem_univ _)
    change eval (entries U) (rowsPoly _ _ p) ≠ 0 at this
    rwa [eval_rowsPoly] at this

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDominantFibreBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

theorem DominantFibreBound.trdeg_le {n d : ℕ} (P : Ideal (MvPolynomial (Fin n) ℂ)) [P.IsPrime]
    (A : Matrix (Fin d) (Fin n) ℂ) (hA : IsFiniteProjection P A) :
    Algebra.trdeg ℂ (MvPolynomial (Fin n) ℂ ⧸ P) ≤ Cardinal.mk (Fin d) := by
  set a : Fin d → MvPolynomial (Fin n) ℂ ⧸ P := fun i => Ideal.Quotient.mk P (linPoly A i) with ha_def
  have hproj : projHom P A = aeval a := by
    rw [projHom, pullback, comp_aeval]
    rfl
  have hind : AlgebraicIndependent ℂ a := by
    rw [algebraicIndependent_iff_injective_aeval, ← hproj]
    exact hA.injective
  have hint : Algebra.IsIntegral (Algebra.adjoin ℂ (Set.range a)) (MvPolynomial (Fin n) ℂ ⧸ P) := by
    constructor
    intro b
    obtain ⟨f, hfm, hfb⟩ := hA.finite.to_isIntegral b
    refine ⟨f.map (hind.aevalEquiv : MvPolynomial (Fin d) ℂ →+* Algebra.adjoin ℂ (Set.range a)),
      hfm.map _, ?_⟩
    have hcomp : (algebraMap (Algebra.adjoin ℂ (Set.range a)) (MvPolynomial (Fin n) ℂ ⧸ P)).comp
        (hind.aevalEquiv : MvPolynomial (Fin d) ℂ →+* Algebra.adjoin ℂ (Set.range a)) =
        (projHom P A).toRingHom := by
      apply RingHom.ext
      intro y
      rw [RingHom.comp_apply]
      change ((hind.aevalEquiv y : Algebra.adjoin ℂ (Set.range a)) : MvPolynomial (Fin n) ℂ ⧸ P) = projHom P A y
      rw [hproj]
      exact hind.algebraMap_aevalEquiv y
    rw [Polynomial.eval₂_map, hcomp]
    exact hfb
  have : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range a)) (MvPolynomial (Fin n) ℂ ⧸ P) :=
    Algebra.IsIntegral.isAlgebraic
  exact (Algebra.IsAlgebraic.trdeg_le_cardinalMk (R := ℂ) (s := Set.range a)).trans Cardinal.mk_range_le

theorem DominantFibreBound.exists_poly (hG : ComplexSets.GenericProjectionFinite.Statement) {n d : ℕ}
    (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) (hP : P.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = (d : ℕ))
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ ℂ P).comp (aeval p)))
    (b : MvPolynomial (Fin n) ℂ ⧸ P) :
    ∃ g : Polynomial (MvPolynomial (Fin d) ℂ), g ≠ 0 ∧
      (g.map (aeval (fun i => Ideal.Quotient.mk P (p i))).toRingHom).eval b = 0 := by
  obtain ⟨A, hA⟩ := (hG n d P hP hdim).2.1
  set q : Fin d → MvPolynomial (Fin n) ℂ ⧸ P := fun i => Ideal.Quotient.mk P (p i) with hq_def
  have hind : AlgebraicIndependent ℂ q := by
    rw [algebraicIndependent_iff_injective_aeval]
    rw [comp_aeval] at hinj
    exact hinj
  have hbasis : IsTranscendenceBasis ℂ q :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite (DominantFibreBound.trdeg_le P A hA)
  obtain ⟨f, hf0, hfb⟩ := hbasis.isAlgebraic.isAlgebraic b
  refine ⟨f.map (hind.aevalEquiv.symm : Algebra.adjoin ℂ (Set.range q) →+* MvPolynomial (Fin d) ℂ),
    (Polynomial.map_ne_zero_iff hind.aevalEquiv.symm.injective).2 hf0, ?_⟩
  rw [Polynomial.map_map, ← hfb, Polynomial.aeval_def, Polynomial.eval_map]
  congr 1
  ext y
  simp [← hind.algebraMap_aevalEquiv]

theorem DominantFibreBound.proof (hG : ComplexSets.GenericProjectionFinite.Statement) :
    DominantFibreBound.Statement := by
  intro n d P p hP hdim hinj
  choose g hg0 hgb using fun j : Fin n =>
    DominantFibreBound.exists_poly hG P p hP hdim hinj (Ideal.Quotient.mk P (X j))
  refine ⟨∏ j, (g j).natDegree, ∏ j, (g j).leadingCoeff, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun j _ => Polynomial.leadingCoeff_ne_zero.2 (hg0 j)
  intro w hw
  rw [map_prod] at hw
  have hlc : ∀ j, eval w (g j).leadingCoeff ≠ 0 := fun j =>
    (Finset.prod_ne_zero_iff.1 hw) j (Finset.mem_univ j)
  have hne : ∀ j, (g j).map (eval w) ≠ 0 := fun j h => by
    have := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero (eval w) (hlc j)
    rw [h, Polynomial.leadingCoeff_zero] at this
    exact hlc j this.symm
  let R : Fin n → Finset ℂ := fun j => ((g j).map (eval w)).roots.toFinset
  have hsub : {x | x ∈ zeroSet P ∧ ∀ i, eval x (p i) = w i} ⊆
      (Fintype.piFinset R : Set (Fin n → ℂ)) := by
    rintro x ⟨hx, hxw⟩
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro j
    let ψ : MvPolynomial (Fin n) ℂ ⧸ P →+* ℂ := Ideal.Quotient.lift P (eval x) hx
    have hψx : ∀ q, ψ (Ideal.Quotient.mk P q) = eval x q := fun q => Ideal.Quotient.lift_mk P _ _
    have hψ : ψ.comp (aeval (fun i => Ideal.Quotient.mk P (p i))).toRingHom = eval w := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, algHom_C]
        rw [← Ideal.Quotient.mk_algebraMap, hψx, MvPolynomial.algebraMap_eq, eval_C, eval_C]
      · intro i
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
        rw [hψx, hxw i, eval_X]
    have h0 := congrArg ψ (hgb j)
    rw [Polynomial.eval_map, Polynomial.hom_eval₂, hψ, map_zero, ← Polynomial.eval_map] at h0
    have hxj : ψ (Ideal.Quotient.mk P (X j)) = x j := by
      rw [hψx, eval_X]
    rw [hxj] at h0
    exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots (hne j)).2 h0)
  calc _ ≤ (Fintype.piFinset R : Set (Fin n → ℂ)).encard := Set.encard_le_encard hsub
    _ = ((Fintype.piFinset R).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ _ := by
      rw [Fintype.card_piFinset]
      exact_mod_cast Finset.prod_le_prod' fun j _ => (Multiset.toFinset_card_le _).trans
        ((Polynomial.card_roots' _).trans Polynomial.natDegree_map_le)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermsIntegrallyClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def HolGermsIntegrallyClosed.Statement : Prop :=
  ∀ (d : ℕ) (y : Fin d → ℂ), IsDomain (holGerms y) ∧ IsIntegrallyClosed (holGerms y)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermRegularConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IrreducibleGermRegularConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w → GermIrreducibleAt X w →
    ∀ U ∈ 𝓝 w, ∃ B : Set (σ → ℂ), IsOpen B ∧ w ∈ B ∧ B ⊆ U ∧ IsPreconnected (regLocus (X ∩ B))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeAvoidsFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def ConeAvoidsFinite.Statement : Prop :=
  ∀ (n d N : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ),
    ConeAvoids J A N → (projHom J A).toRingHom.Finite

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLeadIdealDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def LeadIdealDim.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ leadIdeal J) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeAvoidsOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def ConeAvoidsOpen.Statement : Prop :=
  ∀ (n d N : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    IsZariskiOpen {A : Matrix (Fin d) (Fin n) ℂ | ConeAvoids J A N}

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeAvoidsExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def ConeAvoidsExists.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
      ∃ (A : Matrix (Fin d) (Fin n) ℂ) (N : ℕ), ConeAvoids J A N

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjHomInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def FiniteProjHomInjective.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → (projHom J A).toRingHom.Finite →
      Function.Injective (projHom J A)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLinearFormCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def LinearFormCut.Statement : Prop :=
  ∀ (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
      ∃ B : Matrix (Fin 1) (Fin n) ℂ,
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (I ⊔ linIdeal B)) ≤ (e : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarSlabMeasure
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

def VarSlabMeasure.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → linForm u ∉ J →
      ∃ C α : ℝ, 0 < α ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ {z | ‖z‖ ≤ R} ∩ {z | ‖∑ j, u j * z j‖ ≤ ε}) ≤
          ENNReal.ofReal (C * ε ^ α)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFrameJacobianSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

noncomputable section

def frameProjLin {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ I :=
  (WithLp.linearEquiv 2 ℂ (I → ℂ)).symm.toLinearMap ∘ₗ LinearMap.pi fun i : I => innerₛₗ ℂ (b i)

theorem frameProjLin_apply {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) :
    WithLp.ofLp (frameProjLin b I z) = frameProj b I z := rfl

def FrameJacobianSum.Statement : Prop :=
  ∀ (d n : ℕ) (T : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))),
    areaJacobian (T.restrictScalars ℝ) =
      ∑ I ∈ Finset.univ.powersetCard d, areaJacobian ((frameProjLin b I ∘ₗ T).restrictScalars ℝ)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaGraphPiece
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal NNReal

noncomputable section

def AreaGraphPiece.Statement : Prop :=
  ∀ (k m : ℕ) (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m))
    (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) (δ : ℝ≥0)
    (t : Set (EuclideanSpace ℝ (Fin k))), δ < 1 → ApproximatesLinearOn F A t δ →
      μH[(k : ℝ)] (realGraphPt F '' t) ≤
          ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ k *
            ENNReal.ofReal (graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
              μH[(k : ℝ)] t ∧
        ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k *
            ENNReal.ofReal (graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
              μH[(k : ℝ)] t ≤
          μH[(k : ℝ)] (realGraphPt F '' t)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaGraphBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal NNReal

noncomputable section

def AreaGraphBound.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (EuclideanSpace ℝ (Fin k)))
    (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)),
    IsOpen U → ContDiffOn ℝ 1 F U → ∀ A ⊆ U, MeasurableSet A →
      ∀ δ : ℝ≥0, 0 < δ → δ < 1 →
        μH[(k : ℝ)] (realGraphPt F '' A) ≤
            ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ (k + 1) *
              ∫⁻ x in A, ENNReal.ofReal (graphJac (fderiv ℝ F x :
                EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)]) ∧
          ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k *
              ∫⁻ x in A, ENNReal.ofReal (graphJac (fderiv ℝ F x :
                EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)]) ≤
            ((1 + δ : ℝ≥0) : ℝ≥0∞) * μH[(k : ℝ)] (realGraphPt F '' A)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietyLelongMono
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory
open scoped ENNReal

noncomputable section

def VarietyLelongMono.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ z ∈ zeroSetEuc J, ∀ r s : ℝ, 0 < r → r ≤ s →
      ENNReal.ofReal (s ^ (2 * d)) * μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z r) ≤
        ENNReal.ofReal (r ^ (2 * d)) * μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z s)

theorem VarietyLelongMono.euclBall_measure (d : ℕ) (z : EuclideanSpace ℂ (Fin d)) {r : ℝ} (hr : 0 < r) :
    μH[((2 * d : ℕ) : ℝ)] (Metric.ball z r) =
      ENNReal.ofReal (r ^ (2 * d)) * μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) := by
  have hf : Module.finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin d)), Complex.finrank_real_complex,
      finrank_euclideanSpace_fin]
  have h : ((2 * d : ℕ) : ℝ) = ((Module.finrank ℝ (EuclideanSpace ℂ (Fin d)) : ℕ) : ℝ) := by rw [hf]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hb : ∀ (x : EuclideanSpace ℂ (Fin 0)) (t : ℝ), 0 < t → Metric.ball x t = Set.univ := fun x t ht =>
      Set.eq_univ_of_forall fun y => Metric.mem_ball.2 (by rw [Subsingleton.elim y x, dist_self]; exact ht)
    rw [hb z r hr, hb 0 1 one_pos]
    simp
  · have : Nontrivial (EuclideanSpace ℂ (Fin d)) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hf]; omega)
    rw [h, Measure.addHaar_ball _ _ hr.le, hf]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscrAdjoin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open Polynomial

theorem DiscrAdjoin.proof : DiscrAdjoin.Statement := by
  intro R K L _ _ _ _ _ _ _ _ _ _ _ _ ℓ hℓ hadj
  have hK : IsIntegral K ℓ := Algebra.IsIntegral.isIntegral ℓ
  have hFK : minpoly K ℓ = (minpoly R ℓ).map (algebraMap R K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hℓ
  have hFm : (minpoly R ℓ).Monic := minpoly.monic hℓ
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hdegK : (minpoly K ℓ).natDegree = (minpoly R ℓ).natDegree := by
    rw [hFK, natDegree_map_eq_of_injective hinj]
  have hdeg : (minpoly R ℓ).natDegree = Module.finrank K L := by
    have h1 := IntermediateField.adjoin.finrank hK
    rw [hadj, IntermediateField.finrank_top', hdegK] at h1
    exact h1.symm
  have hpos : 0 < (minpoly R ℓ).natDegree := minpoly.natDegree_pos hℓ
  have hF'deg : (derivative (minpoly R ℓ)).natDegree ≤ (minpoly R ℓ).natDegree - 1 :=
    natDegree_derivative_le _
  have hres := resultant_deriv (f := minpoly R ℓ) (natDegree_pos_iff_degree_pos.mp hpos)
  rw [hFm.leadingCoeff, mul_one] at hres
  have hdisc : (minpoly R ℓ).discr = (-1) ^ ((minpoly R ℓ).natDegree *
      ((minpoly R ℓ).natDegree - 1) / 2) * resultant (minpoly R ℓ) (derivative (minpoly R ℓ))
        (minpoly R ℓ).natDegree ((minpoly R ℓ).natDegree - 1) := by
    rw [hres, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  refine ⟨hdeg, ?_, ?_⟩
  · intro h0
    have hR : resultant (minpoly R ℓ) (derivative (minpoly R ℓ)) (minpoly R ℓ).natDegree
        ((minpoly R ℓ).natDegree - 1) = 0 := by rw [hres, h0, mul_zero]
    have hRK := congrArg (algebraMap R K) hR
    rw [← resultant_map_map, map_zero, ← derivative_map, ← hFK, ← hdegK] at hRK
    have hsep : (minpoly K ℓ).Separable := Algebra.IsSeparable.isSeparable K ℓ
    have hle : (derivative (minpoly K ℓ)).natDegree ≤ (minpoly K ℓ).natDegree - 1 :=
      natDegree_derivative_le _
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, resultant_add_right_deg _ _ _ _ k le_rfl, coeff_natDegree, (minpoly.monic hK).leadingCoeff,
      one_pow, one_mul] at hRK
    exact resultant_ne_zero _ _ hsep hRK
  · intro z hz
    obtain ⟨p, q, -, -, hpq⟩ := exists_mul_add_mul_eq_C_resultant (minpoly R ℓ)
      (derivative (minpoly R ℓ)) le_rfl hF'deg (Or.inl hpos.ne')
    have hev := congrArg (aeval ℓ) hpq
    simp only [map_add (f := _), map_mul, minpoly.aeval, zero_mul, zero_add, aeval_C] at hev
    have hadjK : Algebra.adjoin K {ℓ} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hK.isAlgebraic, hadj,
        IntermediateField.top_toSubalgebra]
    have hzmem : z ∈ (Algebra.traceForm K L).dualSubmodule
        (Subalgebra.toSubmodule (Algebra.adjoin R {ℓ})) := by
      rw [LinearMap.BilinForm.mem_dualSubmodule]
      intro y hy
      rw [Submodule.mem_one]
      have hyint : IsIntegral R y := adjoin_le_integralClosure hℓ hy
      have htr : IsIntegral R (Algebra.trace K L (z * y)) := Algebra.isIntegral_trace (hz.mul hyint)
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp htr
      exact ⟨r, by simpa [Algebra.traceForm_apply] using hr⟩
    rw [traceForm_dualSubmodule_adjoin R K hadjK hℓ] at hzmem
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hzmem
    have hd : aeval ℓ (derivative (minpoly K ℓ)) = aeval ℓ (derivative (minpoly R ℓ)) := by
      rw [hFK, derivative_map, aeval_map_algebraMap]
    rw [hd]
    have hq : aeval ℓ q ∈ Algebra.adjoin R {ℓ} := aeval_mem_adjoin_singleton R ℓ
    have hw' : w ∈ Algebra.adjoin R {ℓ} := hw
    have key : (minpoly R ℓ).discr • ((aeval ℓ (derivative (minpoly R ℓ)))⁻¹ • w) =
        ((-1 : L) ^ ((minpoly R ℓ).natDegree * ((minpoly R ℓ).natDegree - 1) / 2) * aeval ℓ q * w) *
          (aeval ℓ (derivative (minpoly R ℓ)) * (aeval ℓ (derivative (minpoly R ℓ)))⁻¹) := by
      rw [hdisc, Algebra.smul_def, smul_eq_mul, map_mul, ← hev, map_pow, map_neg, map_one]
      ring
    rw [key]
    by_cases hd0 : aeval ℓ (derivative (minpoly R ℓ)) = 0
    · rw [hd0, zero_mul, mul_zero]
      exact zero_mem _
    · rw [mul_inv_cancel₀ hd0, mul_one]
      exact mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) hq) hw'

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermFiniteProjection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem eventually_eq_zero_of_lines {d : ℕ} {h : (Fin d → ℂ) → ℂ} {a : Fin d → ℂ}
    (ha : AnalyticAt ℂ h a) (hl : ∀ v : Fin d → ℂ, ∀ᶠ t in 𝓝 (0 : ℂ), h (a + t • v) = 0) :
    ∀ᶠ y in 𝓝 a, h y = 0 := by
  obtain ⟨r, hr, han⟩ := ha.exists_ball_analyticOnNhd
  filter_upwards [Metric.ball_mem_nhds a hr] with y hy
  by_cases hv : y - a = 0
  · have hya : y = a := sub_eq_zero.1 hv
    have h0 := (hl 0).self_of_nhds
    simpa [hya] using h0
  have hvpos : 0 < ‖y - a‖ := norm_pos_iff.2 hv
  have hmaps : ∀ t ∈ Metric.ball (0 : ℂ) (r / ‖y - a‖), a + t • (y - a) ∈ Metric.ball a r := by
    intro t ht
    rw [Metric.mem_ball, dist_zero_right, lt_div_iff₀ hvpos] at ht
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact ht
  have hg : AnalyticOnNhd ℂ (fun t : ℂ => h (a + t • (y - a))) (Metric.ball (0 : ℂ) (r / ‖y - a‖)) := by
    intro t ht
    have h1 : AnalyticAt ℂ (fun t : ℂ => a + t • (y - a)) t := by fun_prop
    exact AnalyticAt.comp (g := h) (f := fun s : ℂ => a + s • (y - a)) (han _ (hmaps t ht)) h1
  have h1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) (r / ‖y - a‖) := by
    rw [Metric.mem_ball, dist_zero_right, norm_one, one_lt_div hvpos, ← dist_eq_norm]
    exact hy
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (r / ‖y - a‖) := Metric.mem_ball_self (div_pos hr hvpos)
  have hz := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (0 : ℂ) _).isPreconnected h0
    (by filter_upwards [hl (y - a)] with t ht using ht) h1
  simpa using hz

theorem exists_line_eventually_ne_zero {d : ℕ} {h : (Fin d → ℂ) → ℂ} {a : Fin d → ℂ}
    (ha : AnalyticAt ℂ h a) (hne : ¬ ∀ᶠ y in 𝓝 a, h y = 0) :
    ∃ v : Fin d → ℂ, ∀ᶠ t in 𝓝[≠] (0 : ℂ), h (a + t • v) ≠ 0 := by
  by_contra hcon
  refine hne (eventually_eq_zero_of_lines ha fun v => ?_)
  have h1 : AnalyticAt ℂ (fun t : ℂ => a + t • v) 0 := by fun_prop
  have ha' : AnalyticAt ℂ h (a + (0 : ℂ) • v) := by simpa using ha
  rcases (AnalyticAt.comp (g := h) (f := fun s : ℂ => a + s • v) ha' h1).eventually_eq_zero_or_eventually_ne_zero with h0 | h0
  · exact h0
  · exact absurd ⟨v, h0⟩ hcon

theorem exists_proj_fibres_line {d : ℕ} (v : Fin d → ℂ) (hv : v ≠ 0) :
    ∃ π : (Fin d → ℂ) →L[ℂ] (Fin (d - 1) → ℂ), ∀ y y', π y = π y' → ∃ t : ℂ, y = y' + t • v := by
  have hrank : Module.finrank ℂ ((Fin d → ℂ) ⧸ (ℂ ∙ v)) = Module.finrank ℂ (Fin (d - 1) → ℂ) := by
    have h1 := Submodule.finrank_quotient_add_finrank (ℂ ∙ v)
    rw [finrank_span_singleton hv, Module.finrank_fin_fun] at h1
    rw [Module.finrank_fin_fun]
    omega
  let e := LinearEquiv.ofFinrankEq _ _ hrank
  refine ⟨LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ (ℂ ∙ v).mkQ), fun y y' hyy => ?_⟩
  have hq : (ℂ ∙ v).mkQ y = (ℂ ∙ v).mkQ y' := e.injective hyy
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_span_singleton] at hq
  obtain ⟨t, ht⟩ := hq
  exact ⟨t, by rw [ht]; abel⟩

theorem GermFiniteProjection.proof : GermFiniteProjection.Statement := by
  intro σ _ X w _ hirr
  classical
  have hw : w ∈ X := hirr.1
  have hP : ∃ d : ℕ, ∃ A : (σ → ℂ) →L[ℂ] (Fin d → ℂ), ∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w := by
    let e : (σ → ℂ) ≃ₗ[ℂ] (Fin (Fintype.card σ) → ℂ) :=
      LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ).symm
    exact ⟨Fintype.card σ, LinearMap.toContinuousLinearMap e.toLinearMap, Set.univ, univ_mem,
      fun x _ hx => e.injective hx⟩
  obtain ⟨A, W, hW, hAW⟩ := Nat.find_spec hP
  refine ⟨Nat.find hP, A, ⟨W, hW, hAW⟩, fun h hh hXh => ?_⟩
  by_contra hne
  have hAw : h (A w) = 0 := hXh.self_of_nhds hw
  obtain ⟨v, hv⟩ := exists_line_eventually_ne_zero hh hne
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hv.exists
    simp [hAw] at ht
  have hd : Nat.find hP - 1 < Nat.find hP := by
    have : 0 < Nat.find hP := Nat.pos_of_ne_zero fun h0 => hv0 (funext fun i => (Fin.cast h0 i).elim0)
    omega
  obtain ⟨π, hπ⟩ := exists_proj_fibres_line v hv0
  obtain ⟨ε, hε, hεv⟩ := Metric.mem_nhdsWithin_iff.1 hv
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have hcont : ∀ᶠ x in 𝓝 w, A x ∈ Metric.ball (A w) (ε * ‖v‖) :=
    A.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (mul_pos hε hvpos))
  refine Nat.find_min hP hd ⟨π.comp A, W ∩ {x | (x ∈ X → h (A x) = 0) ∧ A x ∈ Metric.ball (A w) (ε * ‖v‖)},
    inter_mem hW (hXh.and hcont), ?_⟩
  rintro x ⟨hxX, hxW, hxh, hxb⟩ hπx
  apply hAW x ⟨hxX, hxW⟩
  obtain ⟨t, ht⟩ := hπ (A x) (A w) hπx
  by_cases ht0 : t = 0
  · simpa [ht0] using ht
  exfalso
  have htε : t ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    have hb : ‖t • v‖ < ε * ‖v‖ := by
      rw [Metric.mem_ball, dist_eq_norm, ht, add_sub_cancel_left] at hxb
      exact hxb
    rw [norm_smul] at hb
    exact lt_of_mul_lt_mul_right hb hvpos.le
  exact hεv ⟨htε, ht0⟩ (by rw [← ht]; exact hxh hxX)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreCriterion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def SerreCriterion.Statement : Prop :=
  ∀ (A : Type) [CommRing A], IsNoetherianRing A → (NormalRing A ↔ SerreR A 1 ∧ SerreS A 2)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Imports
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def SerreNormalOfRegularDepth.Statement : Prop :=
  ∀ (A : Type) [CommRing A], IsNoetherianRing A → SerreR A 1 → SerreS A 2 → NormalRing A

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAdicCompletionRegular
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def AdicCompletionRegular.Statement : Prop :=
  ∀ (R : Type) [CommRing R], IsNoetherianRing R → ∀ (M : Ideal R) [M.IsMaximal],
    IsRegularLocalRing (Localization.AtPrime M) → IsRegularLocalRing (AdicCompletion M R)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalLocalDepthTwo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def NormalLocalDepthTwo.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B],
    SerreSAt B 2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDerivationAdicCompletion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def DerivationAdicCompletion.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (D : Derivation ℤ R R),
    ∃ D' : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R),
      ∀ r : R, D' (algebraMap R (AdicCompletion I R) r) = algebraMap R (AdicCompletion I R) (D r)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibresRegularPolynomial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def FormalFibresRegularPolynomial.Statement : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (M : Ideal (MvPolynomial (Fin n) k)), M.IsMaximal →
    ∀ (P : Ideal (AdicCompletion M (MvPolynomial (Fin n) k))) [P.IsPrime],
      IsRegularLocalRing (primeFibreLocalRing (MvPolynomial (Fin n) k) P)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
