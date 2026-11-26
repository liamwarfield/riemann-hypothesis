module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointOverGeometricBasePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointOverGeometricBasePoint
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCptBase

theorem exists_geomPt (S : Scheme.{0}) (s : S) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (q : Sp K ⟶ S), s ∈ Set.range q := by
  let K := AlgebraicClosure (S.residueField s)
  obtain ⟨t⟩ : Nonempty (Sp K) := inferInstance
  refine ⟨K, inferInstance, inferInstance, spMap (algebraMap (S.residueField s) K) ≫ S.fromSpecResidueField s, t, ?_⟩
  have h : S.fromSpecResidueField s (spMap (algebraMap (S.residueField s) K) t) ∈
      Set.range (S.fromSpecResidueField s) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecResidueField] at h
  rw [Scheme.Hom.comp_apply]
  exact h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

theorem isClosed_range_π (C : FlagCpt Z e) : IsClosed (Set.range C.π) := by
  have hZ : IsProper Z.s := projProper O Z.X Z.s Z.proj
  have : IsProper (genStr Z) := inferInstance
  have : IsSeparated (genStr Z ≫ spMap e.toRingHom) := inferInstance
  have : IsProper (C.π ≫ genStr Z ≫ spMap e.toRingHom) := by rw [C.π_str]; infer_instance
  have : IsProper C.π := IsProper.of_comp C.π (genStr Z ≫ spMap e.toRingHom)
  exact C.π.isClosedMap.isClosed_range

end GlobalTheory.FlagCptBase

namespace GlobalTheory.FlagCptBase

open CategoryTheory.Limits

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}

theorem exists_mem_range (Φ : FlagTor Z e U) (w : gen Z) : ∃ i, w ∈ Set.range (Φ.C i).π := by
  obtain ⟨K, _, _, q, t, hq⟩ := exists_geomPt _ w
  let χ : c.F →+* K := (Spec.preimage (q ≫ genStr Z)).hom
  have hχ : q ≫ genStr Z = spMap χ := (Spec.map_preimage _).symm
  obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z K χ q hχ
  obtain ⟨⟨i, p⟩, ⟨hp, -⟩, -⟩ := Φ.lifts K χ q hχ g
  refine ⟨i, p t, ?_⟩
  rw [← hq, ← Scheme.Hom.comp_apply]
  exact congrArg (fun m : Sp K ⟶ gen Z => m t) hp

theorem eq_of_apply_eq (Φ : FlagTor Z e U)
    (hA : ∀ (i : U.Comp) (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z),
      x ≫ genStr Z = spMap χ → ∀ (g g' : EigFrame Z χ (x ≫ genι Z)) (p : Sp K ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π = x →
      (Φ.C i).Carries p g → ∃ p' : Sp K ⟶ (Φ.C i).Y.X, p' ≫ (Φ.C i).π = x ∧ (Φ.C i).Carries p' g')
    (hB : ∀ (i : U.Comp) (K : Type) [Field K] (χ : c.F →+* K) (p : Sp K ⟶ (Φ.C i).Y.X),
      p ≫ (Φ.C i).π ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (p ≫ (Φ.C i).π ≫ genι Z), (Φ.C i).Carries p g)
    {i i' : U.Comp} (y : (Φ.C i).Y.X) (y' : (Φ.C i').Y.X) (h : (Φ.C i).π y = (Φ.C i').π y') : i = i' := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (Φ.C i).π) (g := (Φ.C i').π) y y' h
  obtain ⟨K, _, _, q, -⟩ := exists_geomPt _ z
  let p := q ≫ pullback.fst (Φ.C i).π (Φ.C i').π
  let p' := q ≫ pullback.snd (Φ.C i).π (Φ.C i').π
  let w := p ≫ (Φ.C i).π
  have hw' : p' ≫ (Φ.C i').π = w := by
    simp only [p, p', w, Category.assoc, pullback.condition]
  let χ : c.F →+* K := (Spec.preimage (w ≫ genStr Z)).hom
  have hχ : w ≫ genStr Z = spMap χ := (Spec.map_preimage _).symm
  have hB' : ∀ (i : U.Comp) (p : Sp K ⟶ (Φ.C i).Y.X) (x : Sp K ⟶ gen Z), p ≫ (Φ.C i).π = x →
      x ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (x ≫ genι Z), (Φ.C i).Carries p g := by
    intro i p x hx hxχ
    subst hx
    rw [Category.assoc] at hxχ ⊢
    exact hB i K χ p hxχ
  obtain ⟨g, hg⟩ := hB' i p w rfl hχ
  obtain ⟨g', hg'⟩ := hB' i' p' w hw' hχ
  obtain ⟨p'', hp'', hc''⟩ := hA i K χ w hχ g g' p rfl hg
  obtain ⟨_, -, huniq⟩ := Φ.lifts K χ w hχ g'
  have h1 := huniq ⟨i, p''⟩ ⟨hp'', hc''⟩
  have h2 := huniq ⟨i', p'⟩ ⟨hw', hg'⟩
  exact congrArg Sigma.fst (h1.trans h2.symm)

end GlobalTheory.FlagCptBase

theorem GlobalTheory.FlagCptBase.exists_pt_over_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U) (k : U.Comp) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : (Φ.C k).Y.X ⟶ X.X), f ≫ j = (Φ.C k).π → (∀ (i : U.Comp) (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z), x ≫ genStr Z = spMap χ → ∀ (g g' : EigFrame Z χ (x ≫ genι Z)) (p : Sp K ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π = x → (Φ.C i).Carries p g → ∃ p' : Sp K ⟶ (Φ.C i).Y.X, p' ≫ (Φ.C i).π = x ∧ (Φ.C i).Carries p' g') → (∀ (i : U.Comp) (K : Type) [Field K] (χ : c.F →+* K) (p : Sp K ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (p ≫ (Φ.C i).π ≫ genι Z), (Φ.C i).Carries p g) → ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∃ p : Sp K ⟶ (Φ.C k).Y.X, p ≫ f = x := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ k X j hj _ f hf hA hB K _ _ χ x hx
  let W : U.Comp → Set X.X := fun i => j ⁻¹' Set.range (Φ.C i).π
  have hcl : ∀ i, IsClosed (W i) := fun i => (GlobalTheory.FlagCptBase.isClosed_range_π (Φ.C i)).preimage j.continuous
  have hdis : ∀ i i' z, z ∈ W i → z ∈ W i' → i = i' := by
    rintro i i' z ⟨y, hy⟩ ⟨y', hy'⟩
    exact GlobalTheory.FlagCptBase.eq_of_apply_eq Φ hA hB y y' (hy.trans hy'.symm)
  have hcov : ∀ z, ∃ i, z ∈ W i := fun z => GlobalTheory.FlagCptBase.exists_mem_range Φ (j z)
  have hWk : W k = Set.univ := by
    have hc : (W k)ᶜ = ⋃ i ∈ ({k}ᶜ : Set U.Comp), W i := by
      ext z
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
      constructor
      · intro hz
        obtain ⟨i, hi⟩ := hcov z
        exact ⟨i, fun h => hz (h ▸ hi), hi⟩
      · rintro ⟨i, hik, hi⟩ hz
        exact hik (hdis i k z hi hz)
    have hopen : IsOpen (W k) := by
      rw [← isClosed_compl_iff, hc]
      exact Set.Finite.isClosed_biUnion (Set.toFinite _) (fun i _ => hcl i)
    obtain ⟨y⟩ : Nonempty (Φ.C k).Y.X := inferInstance
    have hne : (W k).Nonempty := ⟨f y, y, by rw [← hf, Scheme.Hom.comp_apply]⟩
    exact IsClopen.eq_univ ⟨hcl k, hopen⟩ hne
  have hx' : (x ≫ j) ≫ genStr Z = spMap χ := by rw [Category.assoc]; exact hx
  obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z K χ (x ≫ j) hx'
  obtain ⟨⟨i, p⟩, ⟨hp, -⟩, -⟩ := Φ.lifts K χ (x ≫ j) hx' g
  obtain ⟨t⟩ : Nonempty (Sp K) := inferInstance
  have hi : i = k := by
    have h1 : x t ∈ W i := ⟨p t, by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun m : Sp K ⟶ gen Z => m t) hp⟩
    have h2 : x t ∈ W k := hWk ▸ Set.mem_univ _
    exact hdis _ _ _ h1 h2
  subst hi
  refine ⟨p, ?_⟩
  rw [← cancel_mono j, Category.assoc, hf]
  exact hp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointOverGeometricBasePointStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagComponent_point_over_geometricBasePoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U) (k : U.Comp) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : (Φ.C k).Y.X ⟶ X.X), f ≫ j = (Φ.C k).π → (∀ (i : U.Comp) (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z), x ≫ genStr Z = spMap χ → ∀ (g g' : EigFrame Z χ (x ≫ genι Z)) (p : Sp K ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π = x → (Φ.C i).Carries p g → ∃ p' : Sp K ⟶ (Φ.C i).Y.X, p' ≫ (Φ.C i).π = x ∧ (Φ.C i).Carries p' g') → (∀ (i : U.Comp) (K : Type) [Field K] (χ : c.F →+* K) (p : Sp K ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (p ≫ (Φ.C i).π ≫ genι Z), (Φ.C i).Carries p g) → ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∃ p : Sp K ⟶ (Φ.C k).Y.X, p ≫ f = x := by
  first | exact @GlobalTheory.FlagCptBase.exists_pt_over_base | exact GlobalTheory.FlagCptBase.exists_pt_over_base | (intros; apply GlobalTheory.FlagCptBase.exists_pt_over_base <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointLiftValuationRing
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointLiftValuationRing
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCptLift

theorem exists_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (L : Type) [Field L] [Algebra V L] [IsFractionRing V L] (yV : Sp V ⟶ gen Z) (pL : Sp L ⟶ C.Y.X), pL ≫ C.π = spMap (algebraMap V L) ≫ yV → ∃ q : Sp V ⟶ C.Y.X, q ≫ C.π = yV ∧ spMap (algebraMap V L) ≫ q = pL := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C V _ _ _ L _ _ _ yV pL h
  have : IsProper Z.s := projProper O Z.X Z.s Z.proj
  have : IsProper (genStr Z) := inferInstance
  have : IsIso (spMap e.toRingHom) := by
    have : IsIso (CommRingCat.ofHom e.toRingHom) := e.toCommRingCatIso.isIso_hom
    infer_instance
  have : IsSeparated (genStr Z ≫ spMap e.toRingHom) := inferInstance
  have : IsProper (C.π ≫ genStr Z ≫ spMap e.toRingHom) := by rw [C.π_str]; infer_instance
  have : IsProper C.π := IsProper.of_comp C.π (genStr Z ≫ spMap e.toRingHom)
  have hv : ValuativeCriterion.Existence C.π := by
    have h' : UniversallyClosed C.π := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h'
    exact h'.1
  obtain ⟨⟨q, q1, q2⟩⟩ := (hv ⟨V, L, pL, yV, ⟨h⟩⟩).exists_lift
  exact ⟨q, q2, q1⟩

end GlobalTheory.FlagCptLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointLiftValuationRingStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagComponent_point_lift_valuationRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (L : Type) [Field L] [Algebra V L] [IsFractionRing V L] (yV : Sp V ⟶ gen Z) (pL : Sp L ⟶ C.Y.X), pL ≫ C.π = spMap (algebraMap V L) ≫ yV → ∃ q : Sp V ⟶ C.Y.X, q ≫ C.π = yV ∧ spMap (algebraMap V L) ≫ q = pL := by
  first | exact @GlobalTheory.FlagCptLift.exists_lift | exact GlobalTheory.FlagCptLift.exists_lift | (intros; apply GlobalTheory.FlagCptLift.exists_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferBaseChange
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
open scoped CategoryTheory.Obj

namespace GlobalTheory.PolExt

section Det

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.PolFin
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l' : Level H}
  {Xo : Moduli D l} {Xo' : Moduli D l'} {c : Coeff l} {c' : Coeff l'} {O O' : Type} [CommRing O] [CommRing O']
  {β : O →+* c.F} {β' : O' →+* c'.F} {Z : Model Xo c β} {Z' : Model Xo' c' β'} {N : Scheme.{0}} {p' : N ⟶ Z'.X}
  {p : N ⟶ Z.X} {G : Over N} [GrpObj G] [IsCommMonObj G] {ψ' : G.left ⟶ Z'.t.G.left} {ψ : G.left ⟶ Z.t.G.left}
  (h' : IsGrpPullback G Z'.t.G p' ψ') (h : IsGrpPullback G Z.t.G p ψ) {S S' : Type} [CommRing S] [CommRing S']

def pullBasis (M : MChart Z) (x : Sp S ⟶ N) (hx : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M.U) : Module.Basis (Fin M.n) S (TanM x G) :=
  (lieBasis M (x ≫ p) hx).map (tanEquiv h x).symm

theorem tanPull_pullBasis (M : MChart Z) (φ : S →+* S') {x : Sp S ⟶ N} {x' : Sp S' ⟶ N} (e : spMap φ ≫ x = x')
    (hx : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M.U) (hx' : ⊤ ≤ (x' ≫ p) ⁻¹ᵁ M.U) (j : Fin M.n) :
    tanPull φ e (pullBasis h M x hx j) = pullBasis h M x' hx' j := by
  have e' : spMap φ ≫ x ≫ p = x' ≫ p := by rw [← Category.assoc, e]
  apply (tanEquiv h x').injective
  rw [← tanPull_tanEquiv h φ e e']
  simp only [pullBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
  exact tanPull_lieBasis M φ e' hx hx' j

theorem pullBasis_toMatrix (M M₁ : MChart Z) (x : Sp S ⟶ N) (hx : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M.U)
    (hx₁ : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M₁.U) : (pullBasis h M x hx).toMatrix (pullBasis h M₁ x hx₁) =
      (lieBasis M (x ≫ p) hx).toMatrix (lieBasis M₁ (x ≫ p) hx₁) := by
  ext i j
  simp [pullBasis, Module.Basis.toMatrix_apply]

def twoDet (M : MChart Z) (M' : MChart Z') (ha : IsAffineOpen (p ⁻¹ᵁ M.U ⊓ p' ⁻¹ᵁ M'.U)) :
    Γ(N, p ⁻¹ᵁ M.U ⊓ p' ⁻¹ᵁ M'.U)ˣ :=
  (isUnit_rdet_toMatrix (pullBasis h M (tau ha) (le_preimage_map p inf_le_left (tau_le _ le_rfl)))
    (pullBasis h' M' (tau ha) (le_preimage_map p' inf_le_right (tau_le _ le_rfl)))).unit

theorem ev_twoDet (M : MChart Z) (M' : MChart Z') (ha : IsAffineOpen (p ⁻¹ᵁ M.U ⊓ p' ⁻¹ᵁ M'.U)) (x : Sp S ⟶ N)
    (h₀ : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M.U) (h₁ : ⊤ ≤ (x ≫ p') ⁻¹ᵁ M'.U) (hh : ⊤ ≤ x ⁻¹ᵁ (p ⁻¹ᵁ M.U ⊓ p' ⁻¹ᵁ M'.U)) :
    ev x _ hh (twoDet h' h M M' ha).val = rdet ((pullBasis h M x h₀).toMatrix (pullBasis h' M' x h₁)) := by
  have e : spMap (ev x _ hh) ≫ tau ha = x := spMap_ev x _ hh
  refine (map_rdet _ _).trans (congrArg rdet ?_)
  ext i j
  have h1 := (pullBasis h M (tau ha) (le_preimage_map p inf_le_left (tau_le _ le_rfl))).sum_toMatrix_smul_self
    (pullBasis h' M' (tau ha) (le_preimage_map p' inf_le_right (tau_le _ le_rfl))) j
  have h2 := congrArg (tanPull (G := G) _ e) h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, tanPull_pullBasis h' M' _ e _ h₁] at h2
  simp only [map_smulₛₗ, tanPull_pullBasis h M _ e _ h₀] at h2
  rw [Module.Basis.toMatrix_apply, ← h2, Module.Basis.repr_sum_self]
  rfl


include h' h in
theorem lbIso_detLie_pull (ha : ∀ (U : Z.X.Opens) (U' : Z'.X.Opens), IsAffineOpen U → IsAffineOpen U' →
    IsAffineOpen (p ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ U')) : LBIso ((detLie Z').pull p') ((detLie Z).pull p) := by
  have le : ∀ J : ((detLie Z).pull p).ι, ((detLie Z).pull p).U J ≤ p ⁻¹ᵁ (J PUnit.unit).U := fun J =>
    LB.wchart_le (detLie Z) (fun _ : PUnit => p) J PUnit.unit
  have le' : ∀ J : ((detLie Z').pull p').ι, ((detLie Z').pull p').U J ≤ p' ⁻¹ᵁ (J PUnit.unit).U := fun J =>
    LB.wchart_le (detLie Z') (fun _ : PUnit => p') J PUnit.unit
  refine ⟨⟨fun a => res (inf_le_inf (le a.1) (le' a.2))
    (twoDet h' h (a.1 PUnit.unit) (a.2 PUnit.unit) (ha _ _ (MChart.hU _) (MChart.hU _)))⟩, fun a b => ?_⟩
  refine Eq.trans ?_ (mul_right_comm _ _ _)
  refine eq_mul_inv_of_mul_eq (Units.ext (ext_ev fun S _ z hz => ?_))
  have hp := le_preimage_mono inf_le_left hz
  have hq := le_preimage_mono inf_le_right hz
  have hp1 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z).pull p).U a.1 := le_preimage_mono inf_le_left hp
  have hq1 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z).pull p).U b.1 := le_preimage_mono inf_le_left hq
  have hp2 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z').pull p').U a.2 := le_preimage_mono inf_le_right hp
  have hq2 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z').pull p').U b.2 := le_preimage_mono inf_le_right hq
  have hp0 := le_preimage_map p (le a.1) hp1
  have hq0 := le_preimage_map p (le b.1) hq1
  have hp3 := le_preimage_map p' (le' a.2) hp2
  have hq3 := le_preimage_map p' (le' b.2) hq2
  have hp4 := le_preimage_mono (inf_le_inf (le a.1) (le' a.2)) hp
  have hq4 := le_preimage_mono (inf_le_inf (le b.1) (le' b.2)) hq
  have g := GlobalTheory.PolFin.ev_pull_g (detLie Z) p z a.1 b.1 (LocM.le_preimage_inf hp1 hq1) (LocM.le_preimage_inf hp0 hq0)
  have g' := GlobalTheory.PolFin.ev_pull_g (detLie Z') p' z a.2 b.2 (LocM.le_preimage_inf hp2 hq2) (LocM.le_preimage_inf hp3 hq3)
  refine (map_mul (ev z _ hz) _ _).trans (Eq.trans ?_ (map_mul (ev z _ hz) _ _).symm)
  refine (congrArg₂ (· * ·) ((ev_res z _ hz hp _).trans ((ev_res z _ hp hp4 _).trans
    (ev_twoDet h' h _ _ _ z hp0 hp3 hp4)))
    ((ev_res z _ hz _ _).trans (g'.trans (ev_detChg _ _ _ hp3 hq3 _)))).trans (Eq.trans ?_
    (congrArg₂ (· * ·) ((ev_res z _ hz _ _).trans (g.trans (ev_detChg _ _ _ hp0 hq0 _)))
      ((ev_res z _ hz hq _).trans ((ev_res z _ hq hq4 _).trans (ev_twoDet h' h _ _ _ z hq0 hq3 hq4)))).symm)
  exact (congrArg (_ * rdet ·) (pullBasis_toMatrix h' _ _ z hp3 hq3).symm).trans ((rdet_toMatrix_mul _ _ _).trans
    ((congrArg (rdet · * _) (pullBasis_toMatrix h _ _ z hp0 hq0).symm).trans (rdet_toMatrix_mul _ _ _)).symm)

end Det

theorem isAffineOpen_snd_inf_fst {X Y T : Scheme.{0}} [IsAffine T] (f : X ⟶ T) (g : Y ⟶ T) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (pullback.snd f g ⁻¹ᵁ V ⊓ pullback.fst f g ⁻¹ᵁ U) := by
  let m : pullback (hU.fromSpec ≫ f) (hV.fromSpec ≫ g) ⟶ pullback f g :=
    pullback.map _ _ _ _ hU.fromSpec hV.fromSpec (𝟙 _) (by simp) (by simp)
  have e : m.opensRange = pullback.snd f g ⁻¹ᵁ V ⊓ pullback.fst f g ⁻¹ᵁ U := by
    apply Opens.ext
    rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_map, hU.range_fromSpec, hV.range_fromSpec, Set.inter_comm]
    rfl
  exact e ▸ isAffineOpen_opensRange m

end GlobalTheory.PolExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpecOfAnypoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperTriangularMul
namespace GlobalTheory.UpperTriangularMul

theorem upperTriangular_mul :
    ∀ {n : ℕ} {R : Type} [inst : CommRing R] {M N : Matrix (Fin n) (Fin n) R},
      (∀ (a i : Fin n), i < a → M a i = (0 : R)) →
      (∀ (a i : Fin n), i < a → N a i = (0 : R)) →
      (∀ (a i : Fin n), i < a → (M * N) a i = (0 : R)) ∧
        ∀ (i : Fin n), (M * N) i i = M i i * N i i := by
  intro n R _ M N hM hN
  refine ⟨fun a i hia => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases lt_or_ge j a with h | h
    · rw [hM a j h, zero_mul]
    · rw [hN j i (lt_of_lt_of_le hia h), mul_zero]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hM i j h, zero_mul]
    · rw [hN j i h, mul_zero]

end GlobalTheory.UpperTriangularMul
end

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.CarrySpec

theorem upper_mul {n : ℕ} {R : Type} [CommRing R] {M N : Matrix (Fin n) (Fin n) R}
    (hM : ∀ a i, i < a → M a i = 0) (hN : ∀ a i, i < a → N a i = 0) :
    (∀ a i, i < a → (M * N) a i = 0) ∧ ∀ i, (M * N) i i = M i i * N i i := by
  first
  | exact @_root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul
  | exact _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul
  | (apply _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul ..)

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (ρ : R →+* R') (ψ : R' →+* R'') :
    spMap (ψ.comp ρ) = spMap ψ ≫ spMap ρ := by
  simp [spMap, Spec.map_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem isMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} {f : EigFrame Z φ x}
    {f' : EigFrame Z φ' x'} {f'' : EigFrame Z φ'' x''} {ρ : R →+* R'} {ψ : R' →+* R''}
    (h1 : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) ρ f') (h2 : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f' embτ basisIdx) ψ f'') : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) (ψ.comp ρ) f'' := fun τ i => by
  rw [h2 τ i, h1 τ i, GlobalTheory.ShFam.CarriesAt.spMap_dualMap_comp, Category.assoc]

theorem tri_of_co {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'} {x : Sp R ⟶ Z.X}
    {x' : Sp R' ⟶ Z.X} {f : EigFrame Z φ x} {ψ : R →+* R'} {f' g : EigFrame Z φ' x'} (hf : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) ψ f')
    (hx : x' = spMap ψ ≫ x) (hφ : φ' = ψ.comp φ) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ)
    (hu : ∀ τ a i, i < a → f'.co g τ a i = 0) (hd : ∀ τ i, f'.co g τ i i = t τ i) : f.Tri ψ g t :=
  ⟨hx, hφ, fun τ i => ⟨fun a => f'.co g τ a i, hd τ i, fun k hk => hu τ k i hk, by
    have := f'.co_spec g τ i
    rwa [funext (hf τ)] at this⟩⟩

theorem tri_spec {R V L k : Type} [CommRing R] [CommRing V] [CommRing L] [CommRing k]
    {φ₁ : c.F →+* R} {x₁ : Sp R ⟶ Z.X} (f : EigFrame Z φ₁ x₁) (ρ : R →+* V) (ν : V →+* L)
    (hν : Function.Injective ν) (r : V →+* k) {φV : c.F →+* V} {xV : Sp V ⟶ Z.X} (hxV : xV = spMap ρ ≫ x₁)
    (gV : EigFrame Z φV xV) {φL : c.F →+* L} {xL : Sp L ⟶ Z.X} (gL : EigFrame Z φL xL)
    (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (hL : gV.Tri ν gL tL)
    (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (hfL : f.Tri (ν.comp ρ) gL t')
    {φk : c.F →+* k} {xk : Sp k ⟶ Z.X} (gk : EigFrame Z φk xk) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ)
    (hk : gV.Tri r gk tk) : ∃ t'' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ, f.Tri (r.comp ρ) gk t'' := by
  have hφV : φV = ρ.comp φ₁ := RingHom.ext fun a => hν (by
    have := RingHom.congr_fun (hL.2.1.symm.trans hfL.2.1) a
    simpa using this)
  obtain ⟨h, hh⟩ := EigFrame.exists_isMap f ρ hφV hxV
  obtain ⟨gVL, hgVL⟩ := EigFrame.exists_isMap gV ν hL.2.1 hL.1
  obtain ⟨hLf, hhL⟩ := EigFrame.exists_isMap h ν hL.2.1 hL.1
  have hfhL : (_root_.GlobalTheory.ShFam.EigFrame.IsMap f) (ν.comp ρ) hLf := isMap_comp hh hhL

  have hA : ∀ τ, (∀ a i, i < a → h.co gV τ a i = 0) := fun τ a i hia => by
    obtain ⟨hU, -⟩ := EigFrame.Tri.co τ hfL hfhL
    obtain ⟨hW, -⟩ := EigFrame.Tri.co τ hL hgVL
    have hmap := EigFrame.IsMap.co τ hhL hgVL hL.1
    have hmul := EigFrame.co_mul hLf gVL gL τ
    have hWu := EigFrame.isUnit_det_co gVL gL τ
    set W := gVL.co gL τ
    have hWt : W.BlockTriangular id := fun a b h => hW a b h
    letI := Matrix.invertibleOfIsUnitDet W hWu
    have hWi : W⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hWt
    have hM : hLf.co gVL τ = hLf.co gL τ * W⁻¹ := by
      rw [← hmul, Matrix.mul_nonsing_inv_cancel_right _ _ hWu]
    have hP : (hLf.co gL τ * W⁻¹).BlockTriangular id :=
      Matrix.BlockTriangular.mul (fun a b h => hU a b h) hWi
    apply hν
    have := hP hia
    rw [← hM, hmap, Matrix.map_apply] at this
    rw [this, map_zero]
  have hAd : ∀ τ i, IsUnit (h.co gV τ i i) := fun τ i => by
    have hdet := EigFrame.isUnit_det_co h gV τ
    rw [Matrix.det_of_upperTriangular (fun a b hab => hA τ a b hab)] at hdet
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => h.co gV τ j j) (Finset.mem_univ i)) hdet

  obtain ⟨hkf, hhk⟩ := EigFrame.exists_isMap h r hk.2.1 hk.1
  obtain ⟨gVk, hgVk⟩ := EigFrame.exists_isMap gV r hk.2.1 hk.1
  have hfhk : (_root_.GlobalTheory.ShFam.EigFrame.IsMap f) (r.comp ρ) hkf := isMap_comp hh hhk
  have hco : ∀ τ, hkf.co gk τ = (h.co gV τ).map r * gVk.co gk τ := fun τ => by
    rw [← EigFrame.IsMap.co τ hhk hgVk hk.1, EigFrame.co_mul]
  have key : ∀ τ, (∀ a i, i < a → hkf.co gk τ a i = 0) ∧ ∀ i, hkf.co gk τ i i = r (h.co gV τ i i) * tk τ i := by
    intro τ
    obtain ⟨hN, hNd⟩ := EigFrame.Tri.co τ hk hgVk
    have hm := upper_mul (M := (h.co gV τ).map r) (fun a i hia => by rw [Matrix.map_apply, hA τ a i hia, map_zero]) hN
    rw [hco]
    exact ⟨hm.1, fun i => by rw [hm.2, Matrix.map_apply, hNd]⟩
  refine ⟨fun τ i => ((hAd τ i).map r).unit * tk τ i, tri_of_co hfhk ?_ ?_ _ (fun τ => (key τ).1) fun τ i => ?_⟩
  · rw [hk.1, hxV, spMap_comp, Category.assoc]
  · rw [hk.2.1, hφV, RingHom.comp_assoc]
  · rw [(key τ).2, Units.val_mul, IsUnit.unit_spec]

end GlobalTheory.CarrySpec

namespace GlobalTheory.CarrySpec

open MvPolynomial GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem spec_of_anypoint (hany : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (k : Type) [Field k] (φ : c.F →+* k) (x : Sp k ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp k ⟶ C.Y.X), C.Carries p g → ∀ (y : C.Y.X) (ψ : C.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* C.Y.X.presheaf.stalk y) (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), p = spMap ψ ≫ stalkPt C.Y y → f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t → ∃ t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ, f.Tri ψ g t') : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (V : Type) [CommRing V] [IsLocalRing V] (L : Type) [Field L] (ν : V →+* L), Function.Injective ν → ∀ (k : Type) [Field k] (r : V →+* k), RingHom.ker r = IsLocalRing.maximalIdeal V → ∀ (q : Sp V ⟶ C.Y.X) (φV : c.F →+* V) (xV : Sp V ⟶ Z.X), xV = q ≫ C.π ≫ genι Z → ∀ (gV : EigFrame Z φV xV) (φL : c.F →+* L) (xL : Sp L ⟶ Z.X) (gL : EigFrame Z φL xL) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ), gV.Tri ν gL tL → C.Carries (spMap ν ≫ q) gL → ∀ (φk : c.F →+* k) (xk : Sp k ⟶ Z.X) (gk : EigFrame Z φk xk) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ), gV.Tri r gk tk → C.Carries (spMap r ≫ q) gk := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C V _ _ L _ ν hν k _ r _ q φV xV hxV gV φL xL gL tL hL hcar φk xk gk tk hk
  set y₀ := q (IsLocalRing.closedPoint V)
  set ρ := (Scheme.stalkClosedPointTo (R := CommRingCat.of V) q).hom
  have hq : spMap ρ ≫ stalkPt C.Y y₀ = q := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of V) q
  obtain ⟨φ₁, f, t, hf, -⟩ := C.gr_spec y₀
  have hpL : spMap ν ≫ q = spMap (ν.comp ρ) ≫ stalkPt C.Y y₀ :=
    (congrArg (spMap ν ≫ ·) hq).symm.trans (by rw [spMap_comp, Category.assoc])
  obtain ⟨t', hfL⟩ := hany E H Dw l Xo c O β Z F e C L φL xL gL (spMap ν ≫ q) hcar y₀ (ν.comp ρ) φ₁ f t hpL hf
  have hxV' : xV = spMap ρ ≫ (stalkPt C.Y y₀ ≫ C.π ≫ genι Z) :=
    hxV.trans ((congrArg (· ≫ C.π ≫ genι Z) hq).symm.trans (Category.assoc _ _ _))
  obtain ⟨t'', htri⟩ := tri_spec f ρ ν hν r hxV' gV gL tL hL t' hfL gk tk hk
  exact ⟨y₀, r.comp ρ, φ₁, f, t, t'',
    (congrArg (spMap r ≫ ·) hq).symm.trans (by rw [spMap_comp, Category.assoc]), hf, htri⟩

end GlobalTheory.CarrySpec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFrameTriangularThroughStalkFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFrameTriangularThroughStalkFrames
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions
  Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.GoodMetric GlobalTheory.LieBase

namespace GlobalTheory.ShFam.CarriesAt

theorem diag_mul_of_blockTriangular {R : Type} [CommRing R] {n : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hA h, zero_mul]
  · rw [hB h, mul_zero]

theorem isUnit_diag_of_blockTriangular {R : Type} [CommRing R] {n : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : A.BlockTriangular id) (hd : IsUnit A.det) (i : Fin n) : IsUnit (A i i) := by
  rw [Matrix.det_of_upperTriangular hA] at hd
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => A j j) (Finset.mem_univ i)) hd

theorem tri_of_carries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (k : Type) [Field k] (φ : c.F →+* k) (x : Sp k ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp k ⟶ C.Y.X), C.Carries p g → ∀ (y : C.Y.X) (ψ : C.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* C.Y.X.presheaf.stalk y) (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), p = spMap ψ ≫ stalkPt C.Y y → f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t → ∃ t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ, f.Tri ψ g t' := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C k _ φ x g p hC y ψ φ₁ f t hp hf
  obtain ⟨y₁, ψ₁, φ₂, f₁, t₁, t₁', hp₁, hf₁, hg₁⟩ := hC

  have hsp : p (IsLocalRing.closedPoint k) ⤳ y := by
    have : p (IsLocalRing.closedPoint k) ∈ Set.range (C.Y.X.fromSpecStalk y) := by
      rw [hp]
      exact ⟨spMap ψ (IsLocalRing.closedPoint k), rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hsp₁ : p (IsLocalRing.closedPoint k) ⤳ y₁ := by
    have : p (IsLocalRing.closedPoint k) ∈ Set.range (C.Y.X.fromSpecStalk y₁) := by
      rw [hp₁]
      exact ⟨spMap ψ₁ (IsLocalRing.closedPoint k), rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hψ : ψ = (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
    refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y)).1 ?_)
    have e1 := spMap_stalkClosedPointTo p
    have e2 : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ C.Y.X.fromSpecStalk y = C.Y.X.fromSpecStalk _ :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
    have e3 : spMap ((Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom) =
        spMap (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom ≫ spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
      simp [spMap, Spec.map_comp]
    rw [e3, Category.assoc, e2, e1]
    exact hp.symm
  have hψ₁ : ψ₁ = (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp₁).hom := by
    refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y₁)).1 ?_)
    have e1 := spMap_stalkClosedPointTo p
    have e2 : spMap (C.Y.X.presheaf.stalkSpecializes hsp₁).hom ≫ C.Y.X.fromSpecStalk y₁ = C.Y.X.fromSpecStalk _ :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp₁
    have e3 : spMap ((Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp₁).hom) =
        spMap (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom ≫ spMap (C.Y.X.presheaf.stalkSpecializes hsp₁).hom := by
      simp [spMap, Spec.map_comp]
    rw [e3, Category.assoc, e2, e1]
    exact hp₁.symm
  set ψp := (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom with hψpdef
  set ρ := (C.Y.X.presheaf.stalkSpecializes hsp).hom with hρdef
  set ρ₁ := (C.Y.X.presheaf.stalkSpecializes hsp₁).hom with hρ₁def
  set alg := algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint k))) C.Y.X.functionField with halgdef
  have hinj : Function.Injective alg := IsFractionRing.injective _ _
  have halg : algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField = alg.comp ρ := algebraMap_eq_comp_specializes hsp
  have halg₁ : algebraMap (C.Y.X.presheaf.stalk y₁) C.Y.X.functionField = alg.comp ρ₁ :=
    algebraMap_eq_comp_specializes hsp₁
  have hxp : spMap ρ ≫ stalkPt C.Y y = stalkPt C.Y (p (IsLocalRing.closedPoint k)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hxp₁ : spMap ρ₁ ≫ stalkPt C.Y y₁ = stalkPt C.Y (p (IsLocalRing.closedPoint k)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp₁
  have hpp : spMap ψp ≫ stalkPt C.Y (p (IsLocalRing.closedPoint k)) = p := spMap_stalkClosedPointTo p

  have c1 : alg.comp (ρ.comp φ₁) = constF e C.Y := by rw [← RingHom.comp_assoc, ← halg, hf.2.1]
  have c2 : alg.comp (ρ₁.comp φ₂) = constF e C.Y := by rw [← RingHom.comp_assoc, ← halg₁, hf₁.2.1]
  have hρφ : ρ₁.comp φ₂ = ρ.comp φ₁ := RingHom.ext fun a => hinj
    ((RingHom.congr_fun c2 a).trans (RingHom.congr_fun c1 a).symm)
  have hgen : genericPt C.Y ≫ C.π ≫ genι Z = spMap alg ≫ stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z := by
    rw [hf.1, halg, ← hxp]
    simp [spMap, Spec.map_comp]
  have hx0 : x = p ≫ C.π ≫ genι Z := by rw [hg₁.1, hp₁, Category.assoc]
  have hxk : x = spMap ψp ≫ stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z := by
    rw [hx0, ← Category.assoc (spMap ψp), hpp]
  have hxψ : x = spMap ψ ≫ stalkPt C.Y y ≫ C.π ≫ genι Z := by
    rw [hx0, hp, Category.assoc]
  have hφk : φ = ψ.comp φ₁ := by
    rw [hg₁.2.1, hψ₁, hψ, RingHom.comp_assoc, RingHom.comp_assoc, hρφ]

  obtain ⟨f', hf'⟩ := f.exists_isMap ρ (x' := stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z) rfl
    (by rw [← hxp, Category.assoc])
  obtain ⟨f₁', hf₁'⟩ := f₁.exists_isMap ρ₁ (x' := stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z) hρφ.symm
    (by rw [← hxp₁, Category.assoc])
  obtain ⟨fF, hfF⟩ := f'.exists_isMap alg c1.symm hgen
  obtain ⟨f₁F, hf₁F⟩ := f₁'.exists_isMap alg c1.symm hgen
  obtain ⟨fk, hfk⟩ := f.exists_isMap ψ hφk hxψ
  obtain ⟨f₁k, hf₁k⟩ := f₁.exists_isMap ψ₁ hg₁.2.1 hg₁.1
  have iF : (_root_.GlobalTheory.ShFam.EigFrame.IsMap f) (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) fF := fun τ i => by
    rw [hfF τ i, hf' τ i, ← Category.assoc (spMap (Formalism.L2.Pj.dualMap alg)), ← spMap_dualMap_comp, ← halg]
  have i₁F : f₁.IsMap (algebraMap (C.Y.X.presheaf.stalk y₁) C.Y.X.functionField) f₁F := fun τ i => by
    rw [hf₁F τ i, hf₁' τ i, ← Category.assoc (spMap (Formalism.L2.Pj.dualMap alg)), ← spMap_dualMap_comp, ← halg₁]
  have ik : f'.IsMap ψp fk := fun τ i => by
    rw [hfk τ i, hf' τ i, ← Category.assoc (spMap (Formalism.L2.Pj.dualMap ψp)), ← spMap_dualMap_comp, ← hψ]
  have i₁k : f₁'.IsMap ψp f₁k := fun τ i => by
    rw [hf₁k τ i, hf₁' τ i, ← Category.assoc (spMap (Formalism.L2.Pj.dualMap ψp)), ← spMap_dualMap_comp, ← hψ₁]

  have key : ∀ τ, (fk.co g τ).BlockTriangular id ∧ ∀ i, IsUnit (fk.co g τ i i) := by
    intro τ
    have hU := EigFrame.Tri.co (τ := τ) hf iF
    have hU₁ := EigFrame.Tri.co (τ := τ) hf₁ i₁F
    have hU₁t : (f₁F.co C.f0 τ).BlockTriangular id := fun a i h => hU₁.1 a i h
    have hU₁d : IsUnit (f₁F.co C.f0 τ).det := f₁F.isUnit_det_co C.f0 τ
    have hW : fF.co f₁F τ = fF.co C.f0 τ * (f₁F.co C.f0 τ)⁻¹ := by
      rw [← fF.co_mul f₁F C.f0 τ, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU₁d, Matrix.mul_one]
    have hWt : (fF.co f₁F τ).BlockTriangular id := by
      haveI := Matrix.invertibleOfIsUnitDet _ hU₁d
      rw [hW]
      exact Matrix.BlockTriangular.mul (fun a i h => hU.1 a i h) (Matrix.blockTriangular_inv_of_blockTriangular hU₁t)
    have hM : fF.co f₁F τ = (f'.co f₁' τ).map alg := EigFrame.IsMap.co τ hfF hf₁F hgen
    have hMt : (f'.co f₁' τ).BlockTriangular id := fun a i h => hinj (by
      have := hWt h
      rw [hM, Matrix.map_apply] at this
      rw [this, map_zero])
    have hMu : ∀ i, IsUnit (f'.co f₁' τ i i) := isUnit_diag_of_blockTriangular hMt (f'.isUnit_det_co f₁' τ)
    have hN := EigFrame.Tri.co (τ := τ) hg₁ hf₁k
    have hNt : (f₁k.co g τ).BlockTriangular id := fun a i h => hN.1 a i h
    have hMk : fk.co f₁k τ = (f'.co f₁' τ).map ψp := EigFrame.IsMap.co τ ik i₁k hxk
    have hMkt : (fk.co f₁k τ).BlockTriangular id := fun a i h => by
      rw [hMk, Matrix.map_apply, hMt h, map_zero]
    have hQ : fk.co g τ = fk.co f₁k τ * f₁k.co g τ := (fk.co_mul f₁k g τ).symm
    refine ⟨hQ ▸ hMkt.mul hNt, fun i => ?_⟩
    rw [hQ, diag_mul_of_blockTriangular hMkt hNt, hMk, Matrix.map_apply, hN.2 i]
    exact ((hMu i).map ψp).mul (Units.isUnit _)
  refine ⟨fun τ i => ((key τ).2 i).unit, hxψ, hφk, fun τ i => ⟨fun a => fk.co g τ a i, ((key τ).2 i).unit_spec.symm,
    fun a ha => (key τ).1 ha, ?_⟩⟩
  rw [← funext (hfk τ)]
  exact fk.co_spec g τ i

end GlobalTheory.ShFam.CarriesAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFrameTriangularThroughStalkFramesStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carried_frame_triangular_through_stalkFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (k : Type) [Field k] (φ : c.F →+* k) (x : Sp k ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp k ⟶ C.Y.X), C.Carries p g → ∀ (y : C.Y.X) (ψ : C.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* C.Y.X.presheaf.stalk y) (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), p = spMap ψ ≫ stalkPt C.Y y → f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t → ∃ t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ, f.Tri ψ g t' := by
  first | exact @GlobalTheory.ShFam.CarriesAt.tri_of_carries | exact GlobalTheory.ShFam.CarriesAt.tri_of_carries | (intros; apply GlobalTheory.ShFam.CarriesAt.tri_of_carries <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyConnectedComponentGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicConstantsDescendToNormalIntegralScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicConstantsDescendToNormalIntegralScheme
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConstDescent

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.Cartier

theorem exists_fnOf_eq_of_algebraic {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp F) (U : X.Opens) (hU : genericPoint X ∈ U)
    {a : X.functionField} (ha : ∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (Cartier.constFn p) a = 0) :
    ∃ s : Γ(X, U), fnOf U hU s = a := by
  haveI : Nonempty U := ⟨⟨_, hU⟩⟩
  letI := (algX p U).toAlgebra
  letI : Algebra F X.functionField := (Cartier.constFn p).toAlgebra
  haveI : IsScalarTower F Γ(X, U) X.functionField :=
    IsScalarTower.of_algebraMap_eq' (fnOf_comp_algX p U hU).symm
  obtain ⟨P, hP, hPa⟩ := ha
  have hint : IsIntegral F a := (show IsAlgebraic F a from
    ⟨P, hP, by rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra]; exact hPa⟩).isIntegral
  obtain ⟨s, hs⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := Γ(X, U))
    (A := X.functionField)).1 hint.tower_top
  exact ⟨s, hs⟩

theorem appLE_comp_algX {F : Type} [CommRing F] {W V : Scheme.{0}} (pW : W ⟶ Sp F) (π : V ⟶ W) :
    (π.appLE ⊤ ⊤ le_top).hom.comp (algX pW ⊤) = algX (π ≫ pW) ⊤ := by
  have e := Scheme.Hom.appLE_comp_appLE π pW ⊤ ⊤ ⊤ le_top le_top
  exact congrArg (fun f => (CommRingCat.Hom.hom f).comp
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom) e

theorem descent : ∀ (F : Type) [Field F] (W V : Scheme.{0}) [IsIntegral W] [IsIntegral V]
    [GlobalTheory.IsNormalScheme W] (pW : W ⟶ Sp F) (pV : V ⟶ Sp F) (π : V ⟶ W), π ≫ pW = pV →
    (∀ b : V.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn pV) b = 0) →
      b ∈ (GlobalTheory.Cartier.constFn pV).range) →
    ∀ a : W.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn pW) a = 0) →
      a ∈ (GlobalTheory.Cartier.constFn pW).range := by
  intro F _ W V _ _ _ pW pV π hπ hV a ha
  subst hπ
  have hW : genericPoint W ∈ (⊤ : W.Opens) := trivial
  have hV' : genericPoint V ∈ (⊤ : V.Opens) := trivial

  let φ : Γ(W, ⊤) →+* V.functionField := (fnOf ⊤ hV').comp (π.appLE ⊤ ⊤ le_top).hom
  have hφ : φ.comp (algX pW ⊤) = Cartier.constFn (π ≫ pW) := by
    simp only [φ, RingHom.comp_assoc, appLE_comp_algX]
    rfl
  obtain ⟨s, hs⟩ := exists_fnOf_eq_of_algebraic pW ⊤ hW ha
  obtain ⟨P, hP, hPa⟩ := ha
  have h0 : P.eval₂ (algX pW ⊤) s = 0 := fnOf_injective ⊤ trivial (by
    rw [Polynomial.hom_eval₂, fnOf_comp_algX pW ⊤ hW, hs, hPa, map_zero])
  have hb : P.eval₂ (Cartier.constFn (π ≫ pW)) (φ s) = 0 := by
    rw [← hφ, ← Polynomial.hom_eval₂, h0, map_zero]
  obtain ⟨c, hc⟩ := hV _ ⟨P, hP, hb⟩
  refine ⟨c, ?_⟩
  by_contra hne
  have hne' : a - Cartier.constFn pW c ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have ht : fnOf ⊤ hW (s - algX pW ⊤ c) = a - Cartier.constFn pW c := by
    rw [map_sub, hs, ← fnOf_comp_algX pW ⊤ hW, RingHom.comp_apply]
  have hφt : φ (s - algX pW ⊤ c) = 0 := by
    rw [map_sub, ← RingHom.comp_apply φ, hφ, hc, sub_self]
  have hinv : ∃ Q : Polynomial F, Q ≠ 0 ∧ Q.eval₂ (Cartier.constFn pW) (a - Cartier.constFn pW c)⁻¹ = 0 := by
    letI : Algebra F W.functionField := (Cartier.constFn pW).toAlgebra
    have h1 : IsAlgebraic F a :=
      ⟨P, hP, by rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra]; exact hPa⟩
    have h2 : IsAlgebraic F (a - Cartier.constFn pW c) :=
      h1.sub (isAlgebraic_algebraMap (A := W.functionField) c)
    obtain ⟨Q, hQ, hQx⟩ := h2.inv
    exact ⟨Q, hQ, by rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] at hQx; exact hQx⟩
  obtain ⟨u, hu⟩ := exists_fnOf_eq_of_algebraic pW ⊤ hW hinv
  have htu : (s - algX pW ⊤ c) * u = 1 := fnOf_injective ⊤ trivial (by
    rw [map_mul, ht, hu, map_one, mul_inv_cancel₀ hne'])
  have h3 := congrArg φ htu
  rw [map_mul, hφt, zero_mul, map_one] at h3
  exact zero_ne_one h3

end GlobalTheory.ConstDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicConstantsDescendToNormalIntegralSchemeStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicConstants_descend_to_normalIntegralScheme : ∀ (F : Type) [Field F] (W V : Scheme.{0}) [IsIntegral W] [IsIntegral V] [GlobalTheory.IsNormalScheme W] (pW : W ⟶ Sp F) (pV : V ⟶ Sp F) (π : V ⟶ W), π ≫ pW = pV → (∀ b : V.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn pV) b = 0) → b ∈ (GlobalTheory.Cartier.constFn pV).range) → ∀ a : W.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn pW) a = 0) → a ∈ (GlobalTheory.Cartier.constFn pW).range := by
  first | exact @GlobalTheory.ConstDescent.descent | exact GlobalTheory.ConstDescent.descent | (intros; apply GlobalTheory.ConstDescent.descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyConnectedComponentGenericFibre
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.CompOfVar

theorem exists_var_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F), SmoothOfRelativeDimension Dw.dim (genStr Z) → ∀ (Y : Var F) (π : Y.X ⟶ gen Z), π ≫ genStr Z ≫ spMap e.toRingHom = Y.str → ∃ (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j ∧ j ≫ genStr Z ≫ spMap e.toRingHom = X.str ∧ Set.range π ⊆ Set.range j := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e hsm Y π hπ
  have hS : Smooth (genStr Z) := SmoothOfRelativeDimension.smooth Dw.dim _
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  have : CompactSpace (gen Z) := QuasiCompact.compactSpace_of_compactSpace (genStr Z)
  have : IsNoetherian (gen Z) := {}
  have hcc := fun z : gen Z => PtComp.connectedComponent_mem
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (fun W hW W' hW' => PtComp.disjoint_of_smooth (genStr Z) hS W W' hW hW') z
  let z : gen Z := π (genericPoint Y.X)
  let V : (gen Z).Opens := ⟨connectedComponent z, (hcc z).2⟩
  have hred : IsReduced (gen Z) := by
    have := GlobalTheory.isNormalScheme_of_smooth (genStr Z)
    exact GlobalTheory.IsNormalScheme.isReduced
  have : CharZero F := e.toRingHom.charZero
  have : IsIso (spMap e.toRingHom) :=
    inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  have hproj : IsProjOver (genStr Z ≫ spMap e.toRingHom) := GlobalTheory.GenFibreComp.isProjOver_comp_equiv e _
    ((GlobalTheory.ProjSpace.points_and_stability O 0).2.2.1 c.F β Z.X Z.s Z.proj)
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace (hcc z).1.1
  have : IsIntegral V.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hcl : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact isClosed_connectedComponent)
  have hp : IsProjOver (V.ι ≫ genStr Z ≫ spMap e.toRingHom) :=
    (GlobalTheory.ProjSpace.points_and_stability F 0).2.2.2.1 _ _ _ _ hcl hproj
  have hsd : SmoothOfRelativeDimension Dw.dim (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := by
    have h : SmoothOfRelativeDimension (0 + (Dw.dim + 0)) (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := inferInstance
    simpa using h
  have hr : Set.range π ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact (isPreconnected_range π.continuous).subset_connectedComponent ⟨_, rfl⟩
  let g : Y.X ⟶ V.toScheme := IsOpenImmersion.lift V.ι π hr
  have hg : g ≫ V.ι = π := IsOpenImmersion.lift_fac _ _ _
  have : Smooth (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := SmoothOfRelativeDimension.smooth Dw.dim _
  have : GlobalTheory.IsNormalScheme V.toScheme := GlobalTheory.ModifSections.isNormalScheme_of_smooth (V.ι ≫ genStr Z ≫ spMap e.toRingHom)
  have : GeometricallyConnected (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := by
    refine GlobalTheory.GeomConnFn.geometricallyConnected_of_locallyOfFiniteType _ ?_
    exact GlobalTheory.T.algebraicConstants_descend_to_normalIntegralScheme F V.toScheme Y.X _ Y.str g (by rw [reassoc_of% hg, hπ])
      (GlobalTheory.T.geometricallyIntegral_algebraicConstants_mem_range F Y.X Y.str)
  obtain ⟨X, ε, -, hs⟩ := GlobalTheory.ProjVar.Var.exists_iso _ Dw.dim hp
  refine ⟨X, ε.inv ≫ V.ι, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, ← hs, Iso.inv_hom_id_assoc]
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ε.inv.surjective.range_eq, Set.image_univ]
    exact hr

end GlobalTheory.CompOfVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyConnectedComponentGenericFibreStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_variety_connectedComponent_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F), SmoothOfRelativeDimension Dw.dim (genStr Z) → ∀ (Y : Var F) (π : Y.X ⟶ gen Z), π ≫ genStr Z ≫ spMap e.toRingHom = Y.str → ∃ (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j ∧ j ≫ genStr Z ≫ spMap e.toRingHom = X.str ∧ Set.range π ⊆ Set.range j := by
  first | exact @GlobalTheory.CompOfVar.exists_var_comp | exact GlobalTheory.CompOfVar.exists_var_comp | (intros; apply GlobalTheory.CompOfVar.exists_var_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieGramEqGramOf
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.FlagBundle GlobalTheory.ShFam GlobalTheory.CxPts GlobalTheory.ProjVar

namespace GlobalTheory.LieBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {σ : c.F →+* ℂ}


open Classical in
def gramOf (e : F ≃+* c.F) (G : EigMet Z σ) {X : Var F} {j : X.X ⟶ gen Z}
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z))
    (A₀ A : Mat Dw.mult X.Fn) (y : CxPts X.str (σ.comp e.toRingHom)) : Mat Dw.mult ℂ :=
  if h : ∃ g : EigFrame Z σ ((cxOf e σ hj y).1 ≫ genι Z), FrameAt e f₀ A₀ A y g then
    fun τ => (G.gram (cxOf e σ hj y) h.choose τ)ᵀ
  else 0

theorem lieGram_eq_gramOf (e : F ≃+* c.F) {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) {X : Var F} {j : X.X ⟶ gen Z}
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z))
    (A₀ : Mat Dw.mult X.Fn) : lieGram e U hj f₀ A₀ = gramOf e (hodgeMet Z U) hj f₀ A₀ := rfl

end GlobalTheory.LieBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanCarrierDimensionBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanCarrierDimensionBounded
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem genRank_le_sq (E : Type) [Field E] [NumberField E] (q : ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (hX : Module.finrank (𝓞 E) X ≤ q) {m : ℕ}
    (γ : Fin m → LinearMap.BilinForm ℤ X) : genRank γ ≤ (q * Module.finrank ℚ E) ^ 2 := by
  have : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have : Module.Free ℤ X := free_int_of_projective E
  have h1 : genRank γ ≤ Module.finrank ℤ (LinearMap.BilinForm ℤ X) :=
    Submodule.finrank_le _
  have h2 : Module.finrank ℤ (LinearMap.BilinForm ℤ X) = Module.finrank ℤ X * Module.finrank ℤ X := by
    unfold LinearMap.BilinForm
    rw [Module.finrank_linearMap, Module.finrank_linearMap_self]
  have h3 : Module.finrank ℤ X ≤ q * Module.finrank ℚ E := by
    rw [finrank_int_eq_finrank_mul E X, mul_comm]
    exact Nat.mul_le_mul_right _ hX
  calc genRank γ ≤ Module.finrank ℤ X * Module.finrank ℤ X := h2 ▸ h1
    _ ≤ (q * Module.finrank ℚ E) * (q * Module.finrank ℚ E) := Nat.mul_le_mul h3 h3
    _ = (q * Module.finrank ℚ E) ^ 2 := (sq _).symm

theorem carrierDim_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ lab : InvFun (𝓞 E)), IsCarrierDim H.bar q ψ lab → ∃ N : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → lab.evalZ β ≤ N := by
  intro E _ _ _ H q ψ lab hlab
  refine ⟨(q * Module.finrank ℚ E) ^ 2, fun X _ _ _ _ hX β hβ hpos => ?_⟩
  rw [hlab X hX β hβ hpos]
  exact_mod_cast (by
    rcases Set.eq_empty_or_nonempty {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧
        InRCone γ β ∧ genRank γ = k} with he | hne
    · rw [he, Nat.sInf_empty]; exact Nat.zero_le _
    · obtain ⟨m, γ, -, -, hk⟩ := Nat.sInf_mem hne
      rw [← hk]; exact genRank_le_sq E q X hX γ :
    sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ β ∧ genRank γ = k} ≤
      (q * Module.finrank ℚ E) ^ 2)

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanCarrierDimensionBoundedStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polFanCarrierDimension_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)), IsCarrierDim H.bar q ψ lab → ∃ N : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → lab.evalZ β ≤ N := by
  first | exact @GlobalTheory.PolFan.carrierDim_bounded | exact GlobalTheory.PolFan.carrierDim_bounded | (intros; apply GlobalTheory.PolFan.carrierDim_bounded <;> assumption)
end
end
