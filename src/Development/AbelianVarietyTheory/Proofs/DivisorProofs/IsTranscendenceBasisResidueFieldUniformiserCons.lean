module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSectionOfSmoothClosedFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFromBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionPullbackNaturality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeCrystalReducesToDeRhamSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtalePolynomialPlaceToPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffPow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisResidueFieldUniformiserCons
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisResidueFieldUniformiserCons
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.ResidueTrBasis

open IsLocalRing

theorem trdeg_le_of_residue {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K)
    (S : Place cL) (ψ : S.ring →+* K) (hψ : Function.Surjective ψ)
    (hc : ∀ a, ψ (S.const a) = cK a) (m : ℕ) (x : Fin (m + 2) → L) (hx : TrBasis cL x) :
    letI := cK.toAlgebra
    Algebra.trdeg ℂ K ≤ (m + 1 : ℕ) := by
  letI : Algebra ℂ S.ring := S.const.toAlgebra
  letI : Algebra ℂ L := cL.toAlgebra
  letI : Algebra ℂ K := cK.toAlgebra
  haveI : IsScalarTower ℂ S.ring L := IsScalarTower.of_algebraMap_eq' rfl
  have hcomp : ψ.comp (algebraMap ℂ S.ring) = algebraMap ℂ K := RingHom.ext hc
  haveI : Algebra.EssFiniteType ℂ S.ring := S.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ S.ring
  have hker : RingHom.ker ψ = maximalIdeal S.ring := by
    haveI := RingHom.ker_isMaximal_of_surjective ψ hψ
    exact IsLocalRing.eq_maximalIdeal this
  have hL : Algebra.trdeg ℂ L = (m + 2 : ℕ) := by
    have := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
    rw [Cardinal.mk_fin] at this
    exact this.symm
  have hR : Algebra.trdeg ℂ (ResidueField S.ring) = (m + 1 : ℕ) :=
    trdeg_residueField_of_trdeg ℂ S.ring L hL
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℂ K
  let res := IsLocalRing.residue S.ring
  let lift : s → S.ring := fun i => Function.surjInv hψ (i : K)
  have hlift : ψ ∘ lift = Subtype.val := funext fun i => Function.surjInv_eq hψ _
  have hg : AlgebraicIndependent ℂ (fun i => res (lift i)) := by
    refine algebraicIndependent_iff.2 fun P hP => ?_
    have h0 : res (MvPolynomial.eval₂ (algebraMap ℂ S.ring) lift P) = 0 := by
      rw [MvPolynomial.eval₂_comp_left]
      exact hP
    rw [IsLocalRing.residue_eq_zero_iff, ← hker, RingHom.mem_ker, MvPolynomial.hom_eval₂,
      hcomp, show (fun i => ψ (lift i)) = Subtype.val from hlift] at h0
    exact algebraicIndependent_iff.1 hs.1 P h0
  have h1 := hg.cardinalMk_le_trdeg
  rw [hs.cardinalMk_eq_trdeg, hR] at h1
  exact h1

theorem trBasis_cons : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (S : Place cL) (ψ : S.ring →+* K),
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) →
  ∀ (F : Place cK) (m : ℕ) (π : K) (y : Fin m → K), (∃ x : Fin (m + 2) → L, TrBasis cL x) →
  F.ord π = 1 → (∀ i, y i ∈ F.ring) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK y P ≠ 0 ∧ (MvPolynomial.eval₂ cK y P)⁻¹ ∈ F.ring) →
  TrBasis cK (Fin.cons π y : Fin (m + 1) → K) := by
  intro L K _ _ cL cK S ψ hψ hc F m π y ⟨x, hx⟩ hπ hy hP
  have htr := trdeg_le_of_residue cL cK S ψ hψ hc m x hx
  letI : Algebra ℂ F.ring := F.const.toAlgebra
  letI : Algebra ℂ K := cK.toAlgebra
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp [Place.ord] at hπ
  have hπm : π ∈ F.ring := (F.ord_nonneg_iff hπ0).1 (by omega)
  let f : F.ring := ⟨π, hπm⟩
  have hf0 : f ≠ 0 := fun h => hπ0 (congrArg Subtype.val h)
  have hfm : f ∈ maximalIdeal F.ring := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := F.ord_eq_zero hu
    change F.ord π = 0 at this
    omega
  let w : Fin m → F.ring := fun i => ⟨y i, hy i⟩
  have hev : ∀ P : MvPolynomial (Fin m) ℂ,
      ((MvPolynomial.eval₂ (algebraMap ℂ F.ring) w P : F.ring) : K) = MvPolynomial.eval₂ cK y P := by
    intro P
    have h := MvPolynomial.hom_eval₂ P (algebraMap ℂ F.ring) F.ring.subtype w
    rw [ValuationSubring.subtype_apply] at h
    rw [h]
    rfl
  have hwu : ∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 →
      IsUnit (MvPolynomial.eval₂ (algebraMap ℂ F.ring) w P) := by
    intro P hP0
    obtain ⟨h1, h2⟩ := hP P hP0
    refine IsUnit.of_mul_eq_one (⟨_, h2⟩ : F.ring) (Subtype.ext ?_)
    change ((MvPolynomial.eval₂ (algebraMap ℂ F.ring) w P : F.ring) : K) * _ = 1
    rw [hev]
    exact mul_inv_cancel₀ h1
  have hsplit : ∀ P : MvPolynomial (Fin (m + 1)) ℂ,
      MvPolynomial.eval₂ (algebraMap ℂ F.ring) (Fin.cons f w : Fin (m + 1) → F.ring) P =
        Polynomial.eval f (Polynomial.map (MvPolynomial.eval₂Hom (algebraMap ℂ F.ring) w)
          (MvPolynomial.finSuccEquiv ℂ m P)) := by
    intro P
    have hrh : MvPolynomial.eval₂Hom (algebraMap ℂ F.ring) (Fin.cons f w : Fin (m + 1) → F.ring) =
        (Polynomial.evalRingHom f).comp
          ((Polynomial.mapRingHom (MvPolynomial.eval₂Hom (algebraMap ℂ F.ring) w)).comp
            (MvPolynomial.finSuccEquiv ℂ m : MvPolynomial (Fin (m + 1)) ℂ →+* _)) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [MvPolynomial.finSuccEquiv_apply]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i <;>
          simp [MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
    exact RingHom.congr_fun hrh P
  have hcoe : ∀ P : MvPolynomial (Fin (m + 1)) ℂ,
      MvPolynomial.aeval (Fin.cons π y : Fin (m + 1) → K) P =
        ((MvPolynomial.eval₂ (algebraMap ℂ F.ring) (Fin.cons f w : Fin (m + 1) → F.ring) P :
          F.ring) : K) := by
    intro P
    have h := MvPolynomial.hom_eval₂ P (algebraMap ℂ F.ring) F.ring.subtype
      (Fin.cons f w : Fin (m + 1) → F.ring)
    rw [ValuationSubring.subtype_apply] at h
    rw [h, MvPolynomial.aeval_def]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have hind : AlgebraicIndependent ℂ (Fin.cons π y : Fin (m + 1) → K) := by
    refine algebraicIndependent_iff.2 fun P hP => ?_
    rw [hcoe, ZeroMemClass.coe_eq_zero, hsplit] at hP
    set Q := MvPolynomial.finSuccEquiv ℂ m P with hQ
    have hq := eq_zero_of_eval_mem_maximalIdeal hf0 hfm _ (fun i hi => by
      rw [Polynomial.coeff_map] at hi ⊢
      refine hwu _ fun h0 => hi ?_
      rw [h0, map_zero]) hP
    have hQ0 : Q = 0 := by
      apply Polynomial.ext
      intro i
      rw [Polynomial.coeff_zero]
      by_contra h0
      apply (hwu _ h0).ne_zero
      have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) hq
      simpa [Polynomial.coeff_map] using this
    exact (MvPolynomial.finSuccEquiv ℂ m).injective (by rw [← hQ, hQ0, map_zero])
  unfold TrBasis
  refine hind.isTranscendenceBasis_of_trdeg_le_of_finite ?_
  rw [Cardinal.mk_fin]
  exact htr

end GlobalTheory.FieldPair.ResidueTrBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisResidueFieldUniformiserConsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTranscendenceBasis_residueField_uniformiser_cons : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (S : Place cL) (ψ : S.ring →+* K),
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) →
  ∀ (F : Place cK) (m : ℕ) (π : K) (y : Fin m → K), (∃ x : Fin (m + 2) → L, TrBasis cL x) →
  F.ord π = 1 → (∀ i, y i ∈ F.ring) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK y P ≠ 0 ∧ (MvPolynomial.eval₂ cK y P)⁻¹ ∈ F.ring) →
  TrBasis cK (Fin.cons π y : Fin (m + 1) → K) := by
  first | exact @GlobalTheory.FieldPair.ResidueTrBasis.trBasis_cons | exact GlobalTheory.FieldPair.ResidueTrBasis.trBasis_cons | (intros; apply GlobalTheory.FieldPair.ResidueTrBasis.trBasis_cons <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseCocycleLocalSectionsGlueBasicOpenCover
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtExt.GlueSec

variable {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} {W : K → X.left.Opens} {u : Fn1 X}
  {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) {n : ℕ}
  (τ : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E)

def locVal (u : Fn1 X) (a : Fin n) {E : Type} [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E)
    (F : Type) [CommRing F] [Algebra R F] (ρ : E →ₐ[R] F) : F :=
  τ a F (ρ.comp ψ) - u E F ρ (spOver ψ ≫ x)

theorem pt_comp {E F : Type} [CommRing E] [Algebra R E] [CommRing F] [Algebra R F]
    (ψ : D →ₐ[R] E) (ρ : E →ₐ[R] F) : spOver (ρ.comp ψ) ≫ x = spOver ρ ≫ (spOver ψ ≫ x) := by
  rw [← spOver_comp, Category.assoc]

theorem sm_comp {E F : Type} [CommRing E] [Algebra R E] [CommRing F] [Algebra R F]
    (ψ : D →ₐ[R] E) (ρ : E →ₐ[R] F) (h : Sm W (D := E) (spOver ψ ≫ x)) :
    Sm W (D := F) (spOver (ρ.comp ψ) ≫ x) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, fun p _ ↦ ?_⟩
  rw [pt_comp]
  exact hi trivial

variable {x τ} {s : Fin n → D}

theorem locVal_map (hu : IsCoc W u)
    (hsec : ∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) →
      τ a E' (θ.comp ψ) - θ (τ a E ψ) = u E E' θ (spOver ψ ≫ x))
    (a : Fin n) {E : Type} [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E) (hsm : Sm W (D := E) (spOver ψ ≫ x))
    {F G : Type} [CommRing F] [Algebra R F] [CommRing G] [Algebra R G] (ρ : E →ₐ[R] F) (θ : F →ₐ[R] G)
    (hunit : IsUnit (ρ (ψ (s a)))) :
    θ (locVal x τ u a ψ F ρ) = locVal x τ u a ψ G (θ.comp ρ) := by
  have h1 := hsec a F G (ρ.comp ψ) θ hunit
  have h2 := hu E F G ρ θ (spOver ψ ≫ x) hsm
  rw [pt_comp] at h1
  unfold locVal
  rw [map_sub, AlgHom.comp_assoc]
  linear_combination h2 - h1

theorem locVal_agree
    (hagree : ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → τ a E ψ = τ b E ψ)
    (a b : Fin n) {E : Type} [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E)
    {F : Type} [CommRing F] [Algebra R F] (ρ : E →ₐ[R] F)
    (ha : IsUnit (ρ (ψ (s a)))) (hb : IsUnit (ρ (ψ (s b)))) :
    locVal x τ u a ψ F ρ = locVal x τ u b ψ F ρ := by
  unfold locVal
  rw [hagree a b F (ρ.comp ψ) ha hb]

theorem span_range (hs : Ideal.span (Set.range s) = ⊤) {E : Type} [CommRing E] [Algebra R E]
    (ψ : D →ₐ[R] E) : Ideal.span (Set.range fun a ↦ ψ (s a)) = ⊤ := by
  change Ideal.span (Set.range ((ψ : D →+* E) ∘ s)) = ⊤
  rw [Set.range_comp ((ψ : D →+* E) : D → E) s, ← Ideal.map_span, hs, Ideal.map_top]

end GlobalTheory.PtExt.GlueSec

namespace GlobalTheory.PtExt.GlueSec

variable {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} {W : K → X.left.Opens} {u : Fn1 X}
  {D : Type} [CommRing D] [Algebra R D] {x : Pt X D} {n : ℕ}
  {τ : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E} {s : Fin n → D}

theorem isUnit_locAlg {E : Type} [CommRing E] [Algebra R E] (t : E) : IsUnit (locAlg R t t) := by
  change IsUnit (algebraMap E (Localization.Away t) t)
  exact IsLocalization.Away.algebraMap_isUnit t

theorem glue_exists (hs : Ideal.span (Set.range s) = ⊤) (hu : IsCoc W u)
    (hsec : ∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) →
      τ a E' (θ.comp ψ) - θ (τ a E ψ) = u E E' θ (spOver ψ ≫ x))
    (hagree : ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → τ a E ψ = τ b E ψ)
    {E : Type} [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E) (hsm : Sm W (D := E) (spOver ψ ≫ x)) :
    ∃ e : E, ∀ (F : Type) [CommRing F] [Algebra R F] (ρ : E →ₐ[R] F) (a : Fin n),
      IsUnit (ρ (ψ (s a))) → ρ e = locVal x τ u a ψ F ρ := by
  let T : Set E := Set.range fun a ↦ ψ (s a)
  have hT : Ideal.span T = ⊤ := span_range hs ψ
  have hc : ∀ t : T, ∃ a, ψ (s a) = t.1 := fun t ↦ t.2
  choose c hc using hc
  have hcu : ∀ t : T, IsUnit (locAlg R t.1 (ψ (s (c t)))) := fun t ↦ by
    rw [hc t]; exact isUnit_locAlg _
  let v : ∀ t : T, Localization.Away t.1 := fun t ↦ locVal x τ u (c t) ψ _ (locAlg R t.1)
  obtain ⟨e, he, -⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top T hT v (fun t₁ t₂ ↦ by
    change awR R t₁.1 t₂.1 (v t₁) = awL R t₁.1 t₂.1 (v t₂)
    have hm : IsUnit (locAlg R (t₁.1 * t₂.1) (t₁.1 * t₂.1)) := isUnit_locAlg _
    rw [map_mul] at hm
    simp only [v]
    rw [locVal_map hu hsec _ ψ hsm _ _ (hcu t₁), locVal_map hu hsec _ ψ hsm _ _ (hcu t₂), awR_comp, awL_comp]
    apply locVal_agree hagree
    · rw [hc t₁]; exact isUnit_of_mul_isUnit_left hm
    · rw [hc t₂]; exact isUnit_of_mul_isUnit_right hm)
  refine ⟨e, fun F _ _ ρ a ha ↦ ?_⟩
  apply Localization.algebraMap_injective_of_span_eq_top _ (span_range hs (ρ.comp ψ))
  funext ⟨_, b, rfl⟩
  let t : T := ⟨ψ (s b), b, rfl⟩
  let lam : F →ₐ[R] Localization.Away (ρ (ψ (s b))) := locAlg R (ρ (ψ (s b)))
  let mu : Localization.Away t.1 →ₐ[R] Localization.Away (ρ (ψ (s b))) := Localization.awayMapₐ ρ t.1
  have hmu : mu.comp (locAlg R t.1) = lam.comp ρ := AlgHom.ext fun z ↦ by
    simp [mu, lam, t, IsLocalization.Away.map, IsLocalization.map_eq]
  change lam (ρ e) = lam (locVal x τ u a ψ F ρ)
  have het : locAlg R t.1 e = v t := he t
  rw [locVal_map hu hsec a ψ hsm ρ lam ha]
  rw [show lam (ρ e) = mu (locAlg R t.1 e) from (DFunLike.congr_fun hmu e).symm, het]
  simp only [v]
  rw [locVal_map hu hsec _ ψ hsm _ _ (hcu t), hmu]
  apply locVal_agree hagree
  · rw [AlgHom.comp_apply, hc t]; exact isUnit_locAlg _
  · exact ha.map lam

end GlobalTheory.PtExt.GlueSec

namespace GlobalTheory.PtExt

open GlueSec in
theorem glue_sections :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens) (u : Fn1 X),
    IsCoc W u → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D) (n : ℕ) (s : Fin n → D),
    Ideal.span (Set.range s) = ⊤ → ∀ τ : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E,
    (∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) →
      τ a E' (θ.comp ψ) - θ (τ a E ψ) = u E E' θ (spOver ψ ≫ x)) →
    (∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → τ a E ψ = τ b E ψ) →
    ∃ σ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E,
    ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), Sm W (D := E) (spOver ψ ≫ x) →
      σ E' (θ.comp ψ) - θ (σ E ψ) = u E E' θ (spOver ψ ≫ x) := by
  intro R _ X K W u hu D _ _ x n s hs τ hsec hagree
  classical
  let σ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E := fun E _ _ ψ ↦
    if h : Sm W (D := E) (spOver ψ ≫ x) then Classical.choose (glue_exists hs hu hsec hagree ψ h) else 0
  refine ⟨σ, fun E _ _ E' _ _ ψ θ hsm ↦ ?_⟩
  have hsm' : Sm W (D := E') (spOver (θ.comp ψ) ≫ x) := sm_comp x ψ θ hsm
  have P := Classical.choose_spec (glue_exists hs hu hsec hagree ψ hsm)
  have P' := Classical.choose_spec (glue_exists hs hu hsec hagree (θ.comp ψ) hsm')
  have e1 : σ E ψ = Classical.choose (glue_exists hs hu hsec hagree ψ hsm) := dite_eq_left hsm
  have e2 : σ E' (θ.comp ψ) = Classical.choose (glue_exists hs hu hsec hagree (θ.comp ψ) hsm') :=
    dite_eq_left hsm'
  rw [e1, e2]
  apply Localization.algebraMap_injective_of_span_eq_top _ (span_range hs (θ.comp ψ))
  funext ⟨_, a, rfl⟩
  let lam : E' →ₐ[R] Localization.Away ((θ.comp ψ) (s a)) := locAlg R ((θ.comp ψ) (s a))
  let lt : E →ₐ[R] Localization.Away ((θ.comp ψ) (s a)) := lam.comp θ
  change lam (Classical.choose (glue_exists hs hu hsec hagree (θ.comp ψ) hsm') - θ (Classical.choose (glue_exists hs hu hsec hagree ψ hsm))) = lam (u E E' θ (spOver ψ ≫ x))
  rw [map_sub, P' (Localization.Away ((θ.comp ψ) (s a))) lam a (isUnit_locAlg ((θ.comp ψ) (s a))),
    show lam (θ (Classical.choose (glue_exists hs hu hsec hagree ψ hsm))) =
      lt (Classical.choose (glue_exists hs hu hsec hagree ψ hsm)) from rfl,
    P (Localization.Away ((θ.comp ψ) (s a))) lt a (isUnit_locAlg (R := R) ((θ.comp ψ) (s a)))]
  have h2 := hu E E' (Localization.Away ((θ.comp ψ) (s a))) θ lam (spOver ψ ≫ x) hsm
  unfold locVal
  simp only [lt]
  rw [pt_comp x ψ θ, AlgHom.comp_assoc]
  linear_combination h2

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupSubsingletonOfBoundedRamification
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupSubsingletonOfBoundedRamification
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TorsRam

theorem classes_fixed {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.LN.CDvr W)
    {D : DegData W (maximalIdeal W)} {Q : PolAV (Sp (FractionRing W))} {H : Over (Sp W)} [GrpObj H] [IsCommMonObj H]
    (hH : IsSemiAbelian H) (U : Unif (maximalIdeal W) D Q H) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing W) F] {k : ℕ} (hk : 1 ≤ k) (σ : F ≃+* F)
    (hσ : σ.toRingHom.comp (algebraMap (FractionRing W) F) = algebraMap (FractionRing W) F)
    (hfixH : ∀ x : TF (R := W) F ⟶ H, x ^ k = 1 → spMap σ.toRingHom ≫ x.left = x.left)
    (p q : QkPt D.toPre F k) (hpq : QkExt σ.toRingHom p q) : QkPt.Equiv D.toPre F p q := by
  haveI : CharZero W := hW.2.2
  have hA := GlobalTheory.ArcPointDescent.admissibleBase_maximalIdeal_completeDVR hW
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  obtain ⟨f, hf, hiff⟩ := GlobalTheory.Mum.Recog.exists_goodLab hA hH U F
  have hx₀ : f k p ^ k = 1 := hf.pow k hk p
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have gp : IsGrpPullback Q.A H (jK W) (U.gen.inv.left ≫ pullback.fst H.hom (jK W)) :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback H (jK W))).congr (Category.id_comp _) rfl
  have w₁ : ((f k p).left ≫ U.gen.inv.left ≫ pullback.fst H.hom (jK W)) ≫ H.hom = jFK (R := W) F ≫ jK W := by
    rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w (f k p)]; rfl
  let xG : TF (R := W) F ⟶ H := Over.homMk ((f k p).left ≫ U.gen.inv.left ≫ pullback.fst H.hom (jK W)) w₁
  have hxG : xG ^ k = 1 := (GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull rfl gp (x := xG) (x' := f k p) rfl).1 hx₀
  have fixG := hfixH xG hxG
  let σ' : F →ₐ[FractionRing W] F := ⟨σ.toRingHom, RingHom.congr_fun hσ⟩
  have s₂ : spMap σ.toRingHom ≫ jFK (R := W) F = jFK (R := W) F := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ]
  have fix₀ : spMap σ.toRingHom ≫ (f k p).left = (f k p).left := by
    refine gp.1.hom_ext ?_ ?_
    · rw [Category.assoc]; exact fixG
    · rw [Category.assoc, Over.w (f k p)]; exact s₂
  let x' : TFK (R := W) F ⟶ Q.A := Over.homMk (spMap σ.toRingHom ≫ (f k p).left) (by
    rw [Category.assoc, Over.w (f k p)]; exact s₂)
  have hq : QkToAkU U.toUnifPre F k q x' :=
    (GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt hL W (maximalIdeal W) hA D Q H hH U F F σ' k hk p q (f k p) x' hpq rfl).1
      ((hiff k hk p (f k p)).2 rfl)
  have e : x' = f k p := Over.OverMorphism.ext fix₀
  exact (hf.eqv k hk p q).1 (e.symm.trans ((hiff k hk q x').1 hq))

end GlobalTheory.TorsRam

namespace GlobalTheory.TorsRam

open GlobalTheory.BXOf in
theorem psiLoc_not_unit {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (D : DegData W (maximalIdeal W))
    (J₀ : D.toPre.P.A.left → D.toPre.P.L.ι) (h₀ : ∀ x, x ∈ D.toPre.P.L.U (J₀ x)) (χ : D.toPre.X) (hχ : χ ≠ 0) (u : Wˣ)
    (hu : (GlobalTheory.UnramTorsion.psiLoc D.toPre χ (J₀ ((D.toPre.c χ).left (closedPoint W))) : FractionRing W) =
      algebraMap W _ u) : False := by
  obtain ⟨e, -, a, ha, hψ⟩ := GlobalTheory.LevelOneIdeal.exists_psi_val D.toPre χ (D.psi_pos χ hχ)
  have := D.toPre.P.isAb.proper
  have : D.toPre.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.toPre.P.A.hom]; infer_instance⟩
  obtain ⟨J, hJ, eJ⟩ := GlobalTheory.UnramTorsion.exists_good_ext D.toPre.P.isLB (algebraMap W (FractionRing W))
    (IsFractionRing.injective W (FractionRing W)) J₀ h₀
  have h1 := hψ (TK W).left (𝟙 _) (closedPoint (FractionRing W)) J hJ
  have hj : J (𝟙 _ ≫ D.toPre.xK χ) = J₀ ((D.toPre.c χ).left (closedPoint W)) := by
    rw [Category.id_comp]
    exact eJ (D.toPre.c χ).left
  have e0 := val_of (D.toPre.psi χ) (𝟙 _) (closedPoint (FractionRing W)) J _ (fun _ => hj)
  have e1 : (stalkClosedPointIso (CommRingCat.of (FractionRing W))).hom.hom
      (val (D.toPre.psi χ) (𝟙 _) (closedPoint (FractionRing W)) J).val = algebraMap W _ u := by
    rw [e0]; exact hu
  obtain ⟨u', hu'⟩ := GlobalTheory.UnramTorsion.val_integral (algebraMap W (FractionRing W)) h₀ eJ e (𝟙 _)
  have e2 : (stalkClosedPointIso (CommRingCat.of (FractionRing W))).hom.hom
      (cst (𝟙 (TK W).left ≫ jK W) (closedPoint (FractionRing W)) a) = algebraMap W _ a := by
    rw [Category.id_comp]; exact GlobalTheory.UnramTorsion.stalk_gs_top _ a
  have e3 : (stalkClosedPointIso (CommRingCat.of (FractionRing W))).hom.hom
      (val e (𝟙 (TK W).left ≫ jK W) (closedPoint (FractionRing W)) J).val = algebraMap W _ u' := by
    rw [Category.id_comp]; exact hu'
  have e4 := congrArg (stalkClosedPointIso (CommRingCat.of (FractionRing W))).hom.hom h1
  rw [map_mul, e1, e2, e3, ← map_mul] at e4
  have e5 := IsFractionRing.injective W (FractionRing W) e4
  exact (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_mul_isUnit_left (e5 ▸ u.isUnit))

end GlobalTheory.TorsRam

namespace GlobalTheory.TorsRam

theorem zpow_of_mul_eq {F : Type} [Field F] {a b c : F} {e : ℕ} (hb : b ≠ 0) (h : a * b = c ^ e) (m : ℤ) :
    a ^ m = c ^ ((e : ℤ) * m) * b ^ (-m) := by
  rw [show a = c ^ e * b⁻¹ by rw [← h, mul_inv_cancel_right₀ hb], mul_zpow, zpow_mul, zpow_natCast, inv_zpow']

theorem coe_units_zpow {F : Type} [Field F] (T : Subring F) (w : Tˣ) (z : ℤ) :
    (((w ^ z : Tˣ) : T) : F) = ((w : T) : F) ^ z :=
  (congrArg Units.val (map_zpow (Units.map T.subtype.toMonoidHom) w z)).trans (Units.val_zpow_eq_zpow_val _ _)

theorem subsingleton_of_bounded_ramification : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (D : DegData W (maximalIdeal W)) (Q : PolAV (Sp (FractionRing W))) (H : Over (Sp W)) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ U : Unif (maximalIdeal W) D Q H, GlobalTheory.LN.ToATotal U.toUnifPre → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W) F] (n N : ℕ), 2 ≤ n → (∀ j : ℕ, ∃ (T : Subring F) (_ : IsDiscreteValuationRing T) (g : W →+* T) (e : ℕ), (∀ w, (g w : F) = algebraMap (FractionRing W) F (algebraMap W _ w)) ∧ 1 ≤ e ∧ e ≤ N ∧ (∀ π, Irreducible π → ∃ ϖ : T, Irreducible ϖ ∧ Associated (g π) (ϖ ^ e)) ∧ ∀ σ : F ≃+* F, (∀ z ∈ T, σ z = z) → ∀ x : TF (R := W) F ⟶ H, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left) → Subsingleton D.toPre.X := by
  intro W _ _ _ hW D Q H _ _ hH U _ F _ _ _ n N hn Hj
  haveI : IsDiscreteValuationRing W := hW.1
  haveI : CharZero W := hW.2.2
  haveI : CharZero (FractionRing W) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective W (FractionRing W))
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing W) F).injective
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  choose J₀ h₀ using fun x : D.toPre.P.A.left => exists_chart D.toPre.P.isLB x
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  choose m u hu using fun χ => IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := FractionRing W) hπ
    (GlobalTheory.UnramTorsion.psiLoc D.toPre χ (J₀ ((D.toPre.c χ).left (closedPoint W)))).ne_zero
  have key : ∀ j : ℕ, ∃ e : ℕ, 1 ≤ e ∧ e ≤ N ∧ (∀ y χ, ((n ^ j : ℕ) : ℤ) ∣ (e : ℤ) * m (y + χ) - (e : ℤ) * m y - (e : ℤ) * m χ) ∧
      ∀ χ, (e : ℤ) * m (-χ) = (e : ℤ) * m χ := fun j => by
    obtain ⟨T, hT, g, e, hg, he1, heN, hram, hfix⟩ := Hj j
    obtain ⟨ϖ, hϖ, v, hv⟩ := hram π hπ
    have hP : ∀ r, r ∈ (closedPoint W).asIdeal ↔ ¬ IsUnit (g r) := fun r => by
      show r ∈ maximalIdeal W ↔ _
      refine ⟨fun hr hgr => ?_, fun h => (mem_maximalIdeal r).2 fun hr => h (hr.map g)⟩
      · rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hr
        obtain ⟨s, rfl⟩ := hr
        rw [map_mul] at hgr
        have h1 : IsUnit (ϖ ^ e) := hv ▸ (isUnit_of_mul_isUnit_left hgr).mul v.isUnit
        exact hϖ.not_isUnit (isUnit_pow_iff (by omega) |>.1 h1)
    have hv' : (g π : F) * ((v : T) : F) = (ϖ : F) ^ e := by
      have := congrArg (fun t : T => (t : F)) hv
      simpa only [Subring.coe_mul, Subring.coe_pow] using this
    have hvne : ((v : T) : F) ≠ 0 := fun h => v.ne_zero (Subtype.ext h)
    have hm : ∀ χ, ∃ u' : Tˣ, algebraMap (FractionRing W) F
        (GlobalTheory.UnramTorsion.psiLoc D.toPre χ (J₀ ((D.toPre.c χ).left (closedPoint W))) : FractionRing W) =
        ((u' : T) : F) * (ϖ : F) ^ ((fun χ => (e : ℤ) * m χ) χ) := fun χ =>
      ⟨Units.map g.toMonoidHom (u χ) * v ^ (-(m χ)), by
        rw [hu χ, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, ← hg, ← hg, Units.val_mul, Subring.coe_mul,
          coe_units_zpow, zpow_of_mul_eq hvne hv' (m χ)]
        rw [show (((Units.map g.toMonoidHom (u χ) : Tˣ) : T) : F) = (g (u χ) : F) from rfl]
        ring⟩
    have hσ : ∀ σ : F ≃+* F, (∀ z ∈ T, σ z = z) →
        σ.toRingHom.comp (algebraMap (FractionRing W) F) = algebraMap (FractionRing W) F := fun σ hσ =>
      IsLocalization.ringHom_ext (nonZeroDivisors W) (RingHom.ext fun r => by
        show σ (algebraMap (FractionRing W) F (algebraMap W _ r)) = algebraMap (FractionRing W) F (algebraMap W _ r)
        rw [← hg]; exact hσ _ (g r).2)
    obtain ⟨h1, h2⟩ := GlobalTheory.UnramTorsion.level_step hL.1.mulN D.tau_bimult D.psi_even (closedPoint W) J₀ h₀ (n ^ j)
      (pow_ne_zero _ (by omega)) T g hg hP ϖ hϖ (fun χ => (e : ℤ) * m χ) hm
      (fun σ hσ' p q hpq => classes_fixed hW hH U F (Nat.one_le_pow _ _ (by omega)) σ (hσ σ hσ')
        (fun x hx => hfix σ hσ' x hx) p q hpq)
    exact ⟨e, he1, heN, h1, h2⟩
  have add : ∀ y χ, m (y + χ) = m y + m χ := fun y χ => by
    obtain ⟨e, he1, heN, hdiv, -⟩ := key (N * (m (y + χ) - m y - m χ).natAbs)
    have h1 := hdiv y χ
    rw [show (e : ℤ) * m (y + χ) - (e : ℤ) * m y - (e : ℤ) * m χ = (e : ℤ) * (m (y + χ) - m y - m χ) by ring] at h1
    by_contra hne
    have hd : m (y + χ) - m y - m χ ≠ 0 := fun h => hne (by omega)
    have h2 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h1 (by
      rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
      exact lt_of_le_of_lt (Nat.mul_le_mul_right _ heN) (Nat.lt_pow_self (by omega)))
    exact (mul_ne_zero (by exact_mod_cast (show e ≠ 0 by omega)) hd) h2
  have even : ∀ χ, m (-χ) = m χ := fun χ => by
    obtain ⟨e, he1, -, -, h⟩ := key 0
    exact Int.eq_of_mul_eq_mul_left (by exact_mod_cast (show e ≠ 0 by omega)) (h χ)
  have m0 : ∀ y, m y = 0 := fun y => by
    have a := add 0 0
    have b := add y (-y)
    rw [add_zero] at a
    rw [add_neg_cancel, even] at b
    omega
  have z : ∀ y : D.toPre.X, y = 0 := fun y => by
    by_contra hy
    refine psiLoc_not_unit D J₀ h₀ y hy (u y) ?_
    rw [hu y, m0, zpow_zero, Units.smul_def, Algebra.smul_def, _root_.mul_one]
  exact ⟨fun a b => (z a).trans (z b).symm⟩

end GlobalTheory.TorsRam

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupSubsingletonOfBoundedRamificationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterGroup_subsingleton_of_bounded_ramification : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (D : DegData W (maximalIdeal W)) (Q : PolAV (Sp (FractionRing W))) (H : Over (Sp W)) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ U : Unif (maximalIdeal W) D Q H, GlobalTheory.LN.ToATotal U.toUnifPre → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W) F] (n N : ℕ), 2 ≤ n → (∀ j : ℕ, ∃ (T : Subring F) (_ : IsDiscreteValuationRing T) (g : W →+* T) (e : ℕ), (∀ w, (g w : F) = algebraMap (FractionRing W) F (algebraMap W _ w)) ∧ 1 ≤ e ∧ e ≤ N ∧ (∀ π, Irreducible π → ∃ ϖ : T, Irreducible ϖ ∧ Associated (g π) (ϖ ^ e)) ∧ ∀ σ : F ≃+* F, (∀ z ∈ T, σ z = z) → ∀ x : TF (R := W) F ⟶ H, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left) → Subsingleton D.toPre.X := by
  first | exact @GlobalTheory.TorsRam.subsingleton_of_bounded_ramification | exact GlobalTheory.TorsRam.subsingleton_of_bounded_ramification | (intros; apply GlobalTheory.TorsRam.subsingleton_of_bounded_ramification <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrderWedgeEqOfEtaleTowerHeightOnePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtalePolynomialPlaceToPlaceStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formallyEtale_polynomialPlace_to_place : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K)
    (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (P : Place cL) (P0 : Place cK)
    (j : K →+* L), IsEtTower cK R cL T ι ψ τ → P.IsPrimeOf T → P0.IsPrimeOf R →
    (∀ g : R, j (g : K) = (ι g : L)) → ∀ (hA : ∀ f ∈ P0.ring, j f ∈ P.ring)
    (hτ : ∀ i, (τ i : L) ∈ P.ring),
    (MvPolynomial.eval₂Hom (j.restrict P0.ring P.ring hA) (fun i => (⟨τ i, hτ i⟩ : P.ring))).FormallyEtale := by
  first | exact @GlobalTheory.FieldPair.formallyEtale_polyPlace | exact GlobalTheory.FieldPair.formallyEtale_polyPlace | (intros; apply GlobalTheory.FieldPair.formallyEtale_polyPlace <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerWedgeFormMapEqSmulOfBasisStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerWedgeFormMapEqSmulOfBasis
open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.TopFormAppend

theorem dForm_append_eq_smul : ∀ {k K L : Type} [CommRing k] [CommRing K] [CommRing L] (cK : k →+* K) (cL : k →+* L)
    (j : K →+* L), j.comp cK = cL → ∀ {n r : ℕ} (x w : Fin n → K) (bK : Module.Basis (Fin n) K (Omega cK)),
    (∀ i, bK i = dFun cK (w i)) → ∀ f : K, dForm cK x = f • dForm cK w → ∀ t : Fin r → L,
    dForm cL (Fin.append t (fun i => j (x i))) = j f • dForm cL (Fin.append t (fun i => j (w i))) := by
  intro k K L _ _ _ cK cL j hc n r x w bK hbK f hf t
  let a : Matrix (Fin n) (Fin n) K := Matrix.of fun i l => bK.repr (dFun cK (x i)) l
  have ha : ∀ i, dFun cK (x i) = ∑ l, a i l • dFun cK (w l) := fun i => by
    conv_lhs => rw [← bK.sum_repr (dFun cK (x i))]
    exact Finset.sum_congr rfl fun l _ => by rw [hbK]; rfl
  have hdet : a.det = f :=
    (isFreeGen_dForm w bK hbK).1 ((dForm_eq_det_smul x w a ha).symm.trans hf)
  have hL : ∀ i, dFun cL (j (x i)) = ∑ l, j (a i l) • dFun cL (j (w l)) := fun i => by
    letI := cK.toAlgebra
    letI := cL.toAlgebra
    letI := j.toAlgebra
    haveI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' hc.symm
    have := congrArg (KaehlerDifferential.map k k K L) (ha i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simp only [map_smul, KaehlerDifferential.map_D] at this
    refine this.trans (Finset.sum_congr rfl fun l _ => ?_)
    rw [← algebraMap_smul L]
    rfl
  let M : Matrix (Fin (r + n)) (Fin (r + n)) L :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 (j.mapMatrix a))
  have hM : M.det = j f := by
    rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul,
      ← RingHom.map_det, hdet]
  rw [← hM]
  refine dForm_eq_det_smul _ _ M fun i => ?_
  rw [Fin.sum_univ_add]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [M, Matrix.one_apply, Fin.append_left]
  · simp [M, Fin.append_right, hL]

end GlobalTheory.TopFormAppend
end

open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehlerWedgeForm_map_eq_smul_of_basis : ∀ {k K L : Type} [CommRing k] [CommRing K] [CommRing L] (cK : k →+* K) (cL : k →+* L)
    (j : K →+* L), j.comp cK = cL → ∀ {n r : ℕ} (x w : Fin n → K) (bK : Module.Basis (Fin n) K (Omega cK)),
    (∀ i, bK i = dFun cK (w i)) → ∀ f : K, dForm cK x = f • dForm cK w → ∀ t : Fin r → L,
    dForm cL (Fin.append t (fun i => j (x i))) = j f • dForm cL (Fin.append t (fun i => j (w i))) := by
  first | exact @GlobalTheory.TopFormAppend.dForm_append_eq_smul | exact GlobalTheory.TopFormAppend.dForm_append_eq_smul | (intros; apply GlobalTheory.TopFormAppend.dForm_append_eq_smul <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrderWedgeEqOfEtaleTowerHeightOnePrime
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FieldPair

theorem formOrd_append_of_ord_eq : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) (P : Place cL) (P0 : Place cK),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) → P.IsPrimeOf T → P0.IsPrimeOf R →
  (∀ g : R, g ≠ 0 → P.ord (ι g : L) = P0.ord (g : K)) →
  (fun ω => @dite ℤ (∃ a, P.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) = (fun ω => @dite ℤ (∃ a, P0.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cK (fun i => (x i : K))) := by
  intro K L _ _ cK cL n r R T ι ψ τ x P P0 hE hx hP hP0 hord
  have hιinj : Function.Injective ι := fun a b h => by
    have := congrArg ψ h
    rwa [hE.retr, hE.retr] at this
  haveI : IsFractionRing R K := IsFractionRing.of_field R K fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hE.base.frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, eq_div_of_mul_eq hb0 e⟩
  have hginj : Function.Injective (T.subtype.comp ι) := Subtype.val_injective.comp hιinj
  let j : K →+* L := IsFractionRing.lift hginj
  have hj : ∀ g : R, j (g : K) = (ι g : L) := fun g => IsFractionRing.lift_algebraMap hginj g
  have hordK : ∀ f : K, f ≠ 0 → P.ord (j f) = P0.ord f := by
    intro f hf
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hE.base.frac f
    have ha0 : a ≠ 0 := by rw [← e]; exact mul_ne_zero hf hb0
    have ef : f = a * b⁻¹ := by rw [← e, mul_inv_cancel_right₀ hb0]
    have hjb : j b ≠ 0 := (map_ne_zero j).2 hb0
    have hja : j a ≠ 0 := (map_ne_zero j).2 ha0
    have hga : (⟨a, ha⟩ : R) ≠ 0 := fun h => ha0 (congrArg Subtype.val h)
    have hgb : (⟨b, hb⟩ : R) ≠ 0 := fun h => hb0 (congrArg Subtype.val h)
    have h1 := hord _ hga
    have h2 := hord _ hgb
    rw [← hj] at h1 h2
    rw [ef, map_mul, map_inv₀, P.ord_mul hja (inv_ne_zero hjb), P.ord_inv,
      P0.ord_mul ha0 (inv_ne_zero hb0), P0.ord_inv]
    simp only at h1 h2
    rw [h1, h2]
  have hA : ∀ f ∈ P0.ring, j f ∈ P.ring := by
    intro f hf
    by_cases h0 : f = 0
    · rw [h0, map_zero]; exact P.ring.zero_mem
    · have hj0 : j f ≠ 0 := (map_ne_zero j).2 h0
      rw [← P.ord_nonneg_iff hj0, hordK f h0, P0.ord_nonneg_iff h0]
      exact hf
  have hτ : ∀ i, (τ i : L) ∈ P.ring := fun i => hP.1 _ (τ i).2
  let ρ : P0.ring →+* P.ring := j.restrict P0.ring P.ring hA
  let τ' : Fin r → P.ring := fun i => ⟨τ i, hτ i⟩
  have hc : ρ.comp P0.const = P.const := by
    ext a
    change j (cK a) = cL a
    have := hj ⟨cK a, hE.base.const_mem a⟩
    rw [hE.const a] at this
    exact this
  have hFE := GlobalTheory.T.formallyEtale_polynomialPlace_to_place cK cL r R T ι ψ τ P P0 j hE hP hP0 hj hA hτ

  letI := P0.const.toAlgebra
  letI := cK.toAlgebra
  haveI : IsScalarTower ℂ P0.ring K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType ℂ P0.ring := P0.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ P0.ring
  obtain ⟨t0, ht0⟩ := IsDiscreteValuationRing.exists_irreducible P0.ring
  obtain ⟨m, z, b, -, hb⟩ := exists_basis_kaehler_uniformiser ℂ ht0
  have h1 := trdeg_eq_of_basis_kaehler ℂ K b
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
  rw [h1, Cardinal.mk_fin] at h2
  obtain rfl : n = m + 1 := by exact_mod_cast h2
  have hω0 : IsFreeGen P0.ring (dForm P0.const z) := isFreeGen_dForm z b hb
  have hF : IsFreeGen P.ring (dForm P.const (Fin.append τ' (fun i => ρ (z i)))) :=
    GlobalTheory.T.isFreeGen_wedgeForm_of_formallyEtale_mvPolynomial P0.const P.const ρ hc z b hb τ' hFE
  haveI : Algebra.FormallyEtale P0.ring K := .of_isLocalization (nonZeroDivisors P0.ring)
  let bK : Module.Basis (Fin (m + 1)) K (Omega cK) :=
    (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ P0.ring K).basis b
  have hbK : ∀ i, bK i = dFun cK (z i : K) := by
    intro i
    simp only [bK, IsBaseChange.basis_apply, hb]
    exact KaehlerDifferential.map_D ℂ ℂ P0.ring K (z i)
  have hrat0 : P0.toRat (m + 1) (dForm P0.const z) = dForm cK (fun i => (z i : K)) :=
    formMap_dForm _ rfl z
  have hratP : P.toRat (r + (m + 1)) (dForm P.const (Fin.append τ' (fun i => ρ (z i)))) =
      dForm cL (Fin.append (fun i => (τ i : L)) (fun i => j (z i : K))) := by
    refine (formMap_dForm _ rfl _).trans (congrArg _ (funext fun k => ?_))
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp only [Fin.append_left]; rfl
    · simp only [Fin.append_right]; rfl
  obtain ⟨f, hf⟩ := (P0.isFreeGen_toRat hω0).2 (dForm cK (fun i => (x i : K)))
  simp only at hf
  have hxK := isFreeGen_dForm_of_trBasis cK hx
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hf
    exact one_ne_zero (hxK.1 (a₁ := 1) (a₂ := 0) (by simp [← hf]))
  have hK : P0.formOrd (dForm cK (fun i => (x i : K))) = P0.ord f := by
    rw [← hf]; exact P0.formOrd_smul_toRat hω0 hf0
  have key := GlobalTheory.T.kaehlerWedgeForm_map_eq_smul_of_basis cK cL j (RingHom.ext fun a => by
      change j (cK a) = cL a
      have := hj ⟨cK a, hE.base.const_mem a⟩
      rw [hE.const a] at this
      exact this) (fun i => (x i : K)) (fun i => (z i : K)) bK hbK f
    (by rw [← hf, hrat0]) (fun i => (τ i : L))
  have e1 : (fun i => j (x i : K)) = fun i => (ι (x i) : L) := funext fun i => hj (x i)
  rw [e1, ← hratP] at key
  change P.formOrd (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) =
    P0.formOrd (dForm cK (fun i => (x i : K)))
  rw [key, P.formOrd_smul_toRat hF ((map_ne_zero j).2 hf0), hordK f hf0, hK]

end GlobalTheory.FieldPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrderWedgeEqOfEtaleTowerHeightOnePrimeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formOrder_wedge_eq_of_etaleTower_heightOnePrime : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) (P : Place cL) (P0 : Place cK),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) → P.IsPrimeOf T → P0.IsPrimeOf R →
  (∀ g : R, g ≠ 0 → P.ord (ι g : L) = P0.ord (g : K)) →
  (fun ω => @dite ℤ (∃ a, P.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) = (fun ω => @dite ℤ (∃ a, P0.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cK (fun i => (x i : K))) := by
  first | exact @GlobalTheory.FieldPair.formOrd_append_of_ord_eq | exact GlobalTheory.FieldPair.formOrd_append_of_ord_eq | (intros; apply GlobalTheory.FieldPair.formOrd_append_of_ord_eq <;> assumption)
end
end
