module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFlatProjectiveThroughPointsGoodFibres
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectPullbackExistsAndFull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwaySurjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ActCommOfClosure
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyMorphismFromVeryDenseGraphs
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyMorphismFromVeryDenseGraphs
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ZM.GraphMor

theorem spMap_comp_hom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_chart_two {Y X₁ X₂ : Scheme.{0}} {σ₁ σ₂ : Type} {M₁ : LB X₁} {M₂ : LB X₂} (h₁ : M₁.IsLB) (h₂ : M₂.IsLB)
    (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (a₁ : Y ⟶ X₁) (a₂ : Y ⟶ X₂) (t : Y) :
    ∃ (A : Type) (_ : CommRing A) (y : Sp A ⟶ Y) (_ : IsOpenImmersion y) (v₁ : σ₁ → A) (v₂ : σ₂ → A),
      t ∈ Set.range y ∧ SecCoord M₁ th₁ (y ≫ a₁) v₁ ∧ SecCoord M₂ th₂ (y ≫ a₂) v₂ := by
  obtain ⟨W, hW, j, hj, ht, hc⟩ := RepUniq.exists_affine_secCoord h₁ th₁ a₁ t
  obtain ⟨t', rfl⟩ : t ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact ht
  obtain ⟨W', hW', j', hj', ht', hc'⟩ := RepUniq.exists_affine_secCoord h₂ th₂ (hW.fromSpec ≫ a₂) t'
  obtain ⟨t'', rfl⟩ : t' ∈ Set.range hW'.fromSpec := by rw [hW'.range_fromSpec]; exact ht'
  obtain ⟨β, hβ⟩ := RepUniq.exists_spMap (R := Γ(Y, W)) (A := Γ(Spec Γ(Y, W), W')) hW'.fromSpec
  have hb := Coord.baseChange hc β
  rw [← hβ] at hb
  exact ⟨Γ(Spec Γ(Y, W), W'), inferInstance, hW'.fromSpec ≫ hW.fromSpec,
    (inferInstance : IsOpenImmersion (hW'.fromSpec ≫ hW.fromSpec)), _, _, ⟨t'', rfl⟩, hb, hc'⟩

theorem exists_coord_field {X : Scheme.{0}} {σ : Type} {M : LB X} (h : M.IsLB) (th : σ → M.Sec) {K : Type} [Field K]
    (y : Sp K ⟶ X) : ∃ v, SecCoord M th y v := by
  let t : Sp K := (default : PrimeSpectrum K)
  obtain ⟨j, hj⟩ := LB.mem_of_cover h (y t)
  have hle : (⊤ : (Sp K).Opens) ≤ y ⁻¹ᵁ M.U j := fun t' _ => by
    obtain rfl : t' = t := Subsingleton.elim (α := PrimeSpectrum K) _ _
    exact hj
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom ((y.appLE _ ⊤ hle).hom ((th i).f j)),
    RepUniq.secCoord_of_frame h ⟨j, hle, 1, isUnit_one, fun i => ?_⟩⟩
  simp [RepUniq.fn]

theorem hom_ext_chart {Y X : Scheme.{0}} (a b : Y ⟶ X)
    (h : ∀ t : Y, ∃ (T : Scheme.{0}) (y : T ⟶ Y) (_ : IsOpenImmersion y), t ∈ Set.range y ∧ y ≫ a = y ≫ b) : a = b := by
  refine Scheme.hom_ext_of_forall _ _ fun t => ?_
  obtain ⟨T, y, _, ht, e⟩ := h t
  refine ⟨y.opensRange, ht, ?_⟩
  rw [← y.isoOpensRange_inv_comp, Category.assoc, Category.assoc, e]

theorem exists_common_field {R K K' : Type} [CommRing R] [Field K] [Field K'] (x : R →+* K) (β : R →+* K')
    (h : RingHom.ker x = RingHom.ker β) :
    ∃ (L : Type) (_ : Field L) (a : K' →+* L) (b : K →+* L), spMap a ≫ spMap β = spMap b ≫ spMap x := by
  let t : Sp K := (default : PrimeSpectrum K)
  let t' : Sp K' := (default : PrimeSpectrum K')
  have e : spMap β t' = spMap x t := PrimeSpectrum.ext (by
    rw [VeryDenseFibres.spMap_apply_asIdeal, VeryDenseFibres.spMap_apply_asIdeal, h])
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := spMap β) (g := spMap x) t' t e
  let L : Type := (pullback (spMap β) (spMap x)).residueField z
  obtain ⟨a, ha⟩ := RepUniq.exists_spMap (R := K') (A := L)
    ((pullback (spMap β) (spMap x)).fromSpecResidueField z ≫ pullback.fst _ _)
  obtain ⟨b, hb⟩ := RepUniq.exists_spMap (R := K) (A := L)
    ((pullback (spMap β) (spMap x)).fromSpecResidueField z ≫ pullback.snd _ _)
  refine ⟨L, inferInstance, a, b, ?_⟩
  rw [← ha, ← hb, Category.assoc, Category.assoc, pullback.condition]

theorem smooth_of_veryDense {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) [IsProper s] [Flat s]
    [LocallyOfFinitePresentation s] {P : Set (Ideal R)} (hP : VeryDense P)
    (h : ∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K), RingHom.ker x = q ∧ Smooth (pullback.snd s (spMap x))) :
    Smooth s := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  refine VeryDenseFibres.eq_top_of_forall_mem s P (fun q hq => ?_) _ fun z hz => ?_
  · obtain ⟨p, h1, h2, h3, -⟩ := hP q 1 hq ((Ideal.ne_top_iff_one _).1 hq.ne_top)
    exact ⟨p, h1, h2, h3⟩
  · obtain ⟨K, _, x, hx, hs⟩ := h _ hz
    let w : Sp K := (default : PrimeSpectrum K)
    have hw : s z = spMap x w := PrimeSpectrum.ext (by rw [VeryDenseFibres.spMap_apply_asIdeal, hx])
    refine VeryDenseFibres.mem_smoothLocus_of_smooth_fiber s z ?_
    rw [hw]
    exact VeryDenseFibres.smooth_fiber_of_smooth_fiber s (spMap x) w
      (inferInstanceAs (Smooth (pullback.snd (pullback.snd s (spMap x)) ((Sp K).fromSpecResidueField w))))

theorem dense_of_veryDense {R : Type} [CommRing R] {P : Set (Ideal R)} (hP : VeryDense P) :
    Dense {q : Sp R | q.asIdeal ∈ P} := by
  refine (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).dense_iff.2 ?_
  rintro _ ⟨f, rfl⟩ ⟨q, hq⟩
  obtain ⟨p, h1, h2, -, h4⟩ := hP q.asIdeal f q.isPrime hq
  exact ⟨⟨p, h2⟩, h4, h1⟩

theorem exists_pair {S Y : Scheme.{0}} (Z₁ Z₂ : Over S) (a₁ : Y ⟶ Z₁.left) (a₂ : Y ⟶ Z₂.left)
    (h : a₁ ≫ Z₁.hom = a₂ ≫ Z₂.hom) :
    ∃ c : Y ⟶ (Z₁ ⊗ Z₂).left, c ≫ (fst Z₁ Z₂).left = a₁ ∧ c ≫ (snd Z₁ Z₂).left = a₂ :=
  ⟨pullback.lift a₁ a₂ h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem mem_of_components {R σ : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {F : MvPolynomial σ R}
    (h : ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) : F ∈ I := by
  rw [← MvPolynomial.sum_homogeneousComponent F]
  exact Ideal.sum_mem _ fun e _ => h e

theorem eval_eq_zero_of_mem_idealOf {R σ : Type} [CommRing R] {Y : Scheme.{0}} {s : Y ⟶ Sp R} {M : LB Y}
    {th : σ → M.Sec} {F : MvPolynomial σ R} (hF : F ∈ idealOf s M th (𝟙 Y)) {T : Type} [CommRing T] {β : R →+* T}
    {y : Sp T ⟶ Y} {v : σ → T} (hy : y ≫ s = spMap β) (hv : SecCoord M th y v) : MvPolynomial.eval₂ β v F = 0 := by
  simp only [idealOf, Ideal.mem_iInf] at hF
  exact hF T inferInstance β y v ⟨hy, by rwa [Category.comp_id]⟩

theorem exists_hom_of_graphs : ∀ (R σ₁ σ₂ Hh : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] [Finite σ₁] [Finite σ₂] [Finite Hh] (Z₁ Z₂ : Over (Sp R)) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (p₁ : Hh → σ₁ → R) (p₂ : Hh → σ₂ → R) (Q : Polynomial ℚ) (d : ℕ) (G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback Z₁.hom (spMap x) ⟶ Z₂.left) → Prop), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsProper Z₁.hom → IsProper Z₂.hom → Smooth Z₁.hom → (∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → f ≫ Z₂.hom = pullback.snd _ _ ≫ spMap x ∧ CutBy (graphIdeal (pullback.snd Z₁.hom (spMap x)) M₁ th₁ (pullback.fst _ _) M₂ th₂ f) Q d (fun h i => x (p₁ h i.1 * p₂ h i.2))) → VeryDense {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (f : _), RingHom.ker x = q ∧ G K x f} → ∃ F : Z₁ ⟶ Z₂, ∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → f = pullback.fst _ _ ≫ F.left := by
  intro R σ₁ σ₂ Hh _ _ _ _ _ _ Z₁ Z₂ I₁ I₂ M₁ M₂ th₁ th₂ p₁ p₂ Q d G h₁ h₂ hp₁ hp₂ hsm hG hP
  obtain ⟨Γ', M, th, hΓ, -, hflat, hlfp, hfib⟩ := GlobalTheory.T.exists_flat_projective_through_points_goodFibres R (σ₁ × σ₂) Hh
    (fun h i => p₁ h i.1 * p₂ h i.2) Q d
    (fun K _ x I => ∃ f, G K x f ∧
      I = graphIdeal (pullback.snd Z₁.hom (spMap x)) M₁ th₁ (pullback.fst _ _) M₂ th₂ f)
    (by
      rintro K _ x _ ⟨f, hf, rfl⟩
      exact ⟨ideals_homogeneous.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.1 h₂.1, (hG K x f hf).2⟩)
    (fun q r hq hr => by
      obtain ⟨p, ⟨K, _, x, f, hx, hf⟩, hp⟩ := hP q r hq hr
      exact ⟨p, ⟨K, _, x, _, hx, f, hf, rfl⟩, hp⟩)
  have hpr : IsProper Γ'.hom := (projRep_projective_ample R _ _ Γ' M th hΓ).2.1

  have good : ∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → ∃ φ : pullback Z₁.hom (spMap x) ⟶ Γ'.left,
      IsPullback φ (pullback.snd _ _) Γ'.hom (spMap x) ∧
      ∀ (T : Type) [CommRing T] (y : Sp T ⟶ pullback Z₁.hom (spMap x)) (v₁ : σ₁ → T) (v₂ : σ₂ → T),
        SecCoord M₁ th₁ (y ≫ pullback.fst _ _) v₁ → SecCoord M₂ th₂ (y ≫ f) v₂ →
        SecCoord M th (y ≫ φ) (fun i => v₁ i.1 * v₂ i.2) := by
    intro K _ x f hf
    obtain ⟨N, ty, hN, hc⟩ := GlobalTheory.T.projRep_graph_segre_coordinates_fibre R K σ₁ σ₂ x I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ _ (pullback.snd _ _)
      (pullback.fst _ _) f h₁ h₂ (IsPullback.of_hasPullback _ _) (hG K x f hf).1
    obtain ⟨φ, hφ, -, hφc⟩ := hfib K x _ _ _ N ty ⟨f, hf, rfl⟩ hN
    exact ⟨φ, hφ, fun T _ y v₁ v₂ e₁ e₂ => (hφc T y _).1 (hc T y v₁ v₂ e₁ e₂)⟩
  have hsmΓ : Smooth Γ'.hom := smooth_of_veryDense Γ'.hom hP (by
    rintro _ ⟨K, _, x, f, rfl, hf⟩
    obtain ⟨φ, hφ, -⟩ := good K x f hf
    refine ⟨K, _, x, rfl, ?_⟩
    rw [← hφ.isoPullback_inv_snd]
    infer_instance)
  have hred : IsReduced Γ'.left := GlobalTheory.isReduced_of_smooth_of_isReduced Γ'.hom
  obtain ⟨I₃, M₃, th₃, h₃', hseg⟩ := SegreCoord.segre_coordinates R σ₁ σ₂ I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ h₁ h₂
  have h₃ := ideals_homogeneous.2.2 R _ _ _ _ _ _ h₃'
  have w₁ : (fst Z₁ Z₂).left ≫ Z₁.hom = (Z₁ ⊗ Z₂).hom := Over.w _
  have w₂ : (snd Z₁ Z₂).left ≫ Z₂.hom = (Z₁ ⊗ Z₂).hom := Over.w _

  have hle : idealOf (Z₁ ⊗ Z₂).hom M₃ th₃ (𝟙 _) ≤ idealOf Γ'.hom M th (𝟙 _) := fun F hF => by
    refine mem_of_components fun e => ?_
    refine DenseFib.mem_idealOf_of_dense R _ _ _ M th _ _ e hred hflat hlfp hΓ.1 (dense_of_veryDense hP)
      (MvPolynomial.homogeneousComponent_isHomogeneous e F) ?_
    intro K' _ _ β y v hy hβ hv
    have hF' := ideals_homogeneous.1 R _ _ _ _ _ _ _ h₃.1 F hF e
    obtain ⟨K, _, x, f, hx, hf⟩ := hβ ⟨(default : PrimeSpectrum K'), rfl⟩
    rw [VeryDenseFibres.spMap_apply_asIdeal] at hx
    obtain ⟨L, _, a, b, hab⟩ := exists_common_field x β hx
    obtain ⟨φ, hφ, hc⟩ := good K x f hf
    have hw : (spMap a ≫ y) ≫ Γ'.hom = spMap b ≫ spMap x := by rw [Category.assoc, hy, hab]
    let z := hφ.lift _ _ hw
    obtain ⟨v₁, hv₁⟩ := exists_coord_field h₁.1 th₁ (z ≫ pullback.fst _ _)
    obtain ⟨v₂, hv₂⟩ := exists_coord_field h₂.1 th₂ (z ≫ f)
    have hz := hc L z v₁ v₂ hv₁ hv₂
    rw [hφ.lift_fst] at hz
    obtain ⟨u, hu⟩ := Coord.unique hΓ.1 hz (Coord.baseChange hv a)
    obtain ⟨c, g₁, g₂⟩ := exists_pair Z₁ Z₂ (pullback.fst _ _) f (pullback.condition.trans (hG K x f hf).1.symm)
    have hs := Coord.scale (hseg L (z ≫ c) v₁ v₂ (by rwa [Category.assoc, g₁]) (by rwa [Category.assoc, g₂])) u
    have hb : (z ≫ c) ≫ (Z₁ ⊗ Z₂).hom = spMap (a.comp β) := by
      rw [spMap_comp_hom, hab, ← w₁, Category.assoc, reassoc_of% g₁, pullback.condition, hφ.lift_snd_assoc]
    have h0 := eval_eq_zero_of_mem_idealOf hF' hb hs
    apply a.injective
    rw [map_zero, MvPolynomial.eval₂_comp_left, ← h0]
    congr 1
    exact funext hu
  obtain ⟨g, hg, -, hgc, -⟩ := RepMap.exists_map_of_coord R _ _ _ _ _ Γ'.hom M₃ M th₃ th h₃ hΓ.1
    (fun T _ β y v hy hv => ⟨(hΓ.2.1 T β y v hy hv).1, fun F hF => eval_eq_zero_of_mem_idealOf (hle hF) hy hv⟩)
  have fib : ∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → ∃ φ : pullback Z₁.hom (spMap x) ⟶ Γ'.left,
      IsPullback φ (pullback.snd _ _) Γ'.hom (spMap x) ∧ φ ≫ g ≫ (fst Z₁ Z₂).left = pullback.fst _ _ ∧
      φ ≫ g ≫ (snd Z₁ Z₂).left = f := by
    intro K _ x f hf
    obtain ⟨φ, hφ, hc⟩ := good K x f hf
    obtain ⟨c, g₁, g₂⟩ := exists_pair Z₁ Z₂ (pullback.fst _ _) f (pullback.condition.trans (hG K x f hf).1.symm)
    have e : φ ≫ g = c := hom_ext_chart _ _ fun t => by
      obtain ⟨A, _, y, hy, v₁, v₂, ht, hv₁, hv₂⟩ := exists_chart_two h₁.1 h₂.1 th₁ th₂ (pullback.fst _ _) f t
      refine ⟨_, y, hy, ht, ?_⟩
      have c₁ := (hgc A _ _).1 (hc A y v₁ v₂ hv₁ hv₂)
      have c₂ := hseg A (y ≫ c) v₁ v₂ (by rwa [Category.assoc, g₁]) (by rwa [Category.assoc, g₂])
      obtain ⟨β, hβ⟩ := RepUniq.exists_spMap ((y ≫ c) ≫ (Z₁ ⊗ Z₂).hom)
      obtain ⟨k₁, k₂⟩ := h₃.2.1 A β _ _ hβ c₂
      rw [← Category.assoc]
      refine (h₃.2.2 A β _ k₁ k₂).unique ⟨?_, c₁⟩ ⟨hβ, c₂⟩
      rw [← hβ, Category.assoc, hg, Category.assoc, hφ.w, Category.assoc, ← w₁, reassoc_of% g₁, pullback.condition]
    exact ⟨φ, hφ, by rw [reassoc_of% e, g₁], by rw [reassoc_of% e, g₂]⟩
  have hπ : (g ≫ (fst Z₁ Z₂).left) ≫ Z₁.hom = Γ'.hom := by rw [Category.assoc, w₁, hg]
  have hππ : IsProper ((g ≫ (fst Z₁ Z₂).left) ≫ Z₁.hom) := hπ ▸ hpr
  have hiso : IsIso (g ≫ (fst Z₁ Z₂).left) := DenseFibreIso.main R _ _ Z₁.hom _ _ hP hp₁ inferInstance
    (IsProper.of_comp _ Z₁.hom) (hπ ▸ hflat) (by
      rintro _ ⟨K, _, x, f, rfl, hf⟩
      obtain ⟨φ, hφ, e₁, -⟩ := fib K x f hf
      refine ⟨K, _, x, rfl, ?_⟩
      have hq : IsPullback φ (𝟙 _) (g ≫ (fst Z₁ Z₂).left) (pullback.fst Z₁.hom (spMap x)) :=
        IsPullback.of_bot (by rwa [Category.id_comp, hπ]) (by rw [e₁, Category.id_comp])
          (IsPullback.of_hasPullback Z₁.hom (spMap x))
      rw [← hq.isoPullback_inv_snd]
      infer_instance)
  refine ⟨Over.homMk (inv (g ≫ (fst Z₁ Z₂).left) ≫ g ≫ (snd Z₁ Z₂).left) ?_, fun K _ x f hf => ?_⟩
  · rw [Category.assoc, Category.assoc, w₂, hg, ← hπ, IsIso.inv_hom_id_assoc]
  · obtain ⟨φ, -, e₁, e₂⟩ := fib K x f hf
    change f = pullback.fst _ _ ≫ inv (g ≫ (fst Z₁ Z₂).left) ≫ g ≫ (snd Z₁ Z₂).left
    rw [← e₁, Category.assoc, IsIso.hom_inv_id_assoc, e₂]

end GlobalTheory.ZM.GraphMor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyMorphismFromVeryDenseGraphsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_family_morphism_from_veryDense_graphs : ∀ (R σ₁ σ₂ Hh : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] [Finite σ₁] [Finite σ₂] [Finite Hh] (Z₁ Z₂ : Over (Sp R)) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (p₁ : Hh → σ₁ → R) (p₂ : Hh → σ₂ → R) (Q : Polynomial ℚ) (d : ℕ) (G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback Z₁.hom (spMap x) ⟶ Z₂.left) → Prop), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsProper Z₁.hom → IsProper Z₂.hom → Smooth Z₁.hom → (∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → f ≫ Z₂.hom = pullback.snd _ _ ≫ spMap x ∧ CutBy (graphIdeal (pullback.snd Z₁.hom (spMap x)) M₁ th₁ (pullback.fst _ _) M₂ th₂ f) Q d (fun h i => x (p₁ h i.1 * p₂ h i.2))) → VeryDense {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (f : _), RingHom.ker x = q ∧ G K x f} → ∃ F : Z₁ ⟶ Z₂, ∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → f = pullback.fst _ _ ≫ F.left := by
  first | exact @GlobalTheory.ZM.GraphMor.exists_hom_of_graphs | exact GlobalTheory.ZM.GraphMor.exists_hom_of_graphs | (intros; apply GlobalTheory.ZM.GraphMor.exists_hom_of_graphs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TransitionFramesPushOpenImmersionImage
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TransitionFramesPushOpenImmersionImage
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ModelSum

theorem appIso_inv_topIso_inv {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (W' : Z'.Opens) (W : Z.Opens)
    (hle : W ≤ f ''ᵁ W') (v : W'.toScheme ⟶ W.toScheme) (hv : v ≫ W.ι = W'.ι ≫ f) :
    (f.appIso W').inv ≫ Z.presheaf.map (homOfLE hle).op ≫ W.topIso.inv ≫ v.appTop = W'.topIso.inv := by
  have e : W.topIso.inv = W.ι.appLE W ⊤ (by simp) := (Scheme.Opens.ι_appLE W W ⊤ _).symm
  have e' : W'.topIso.inv = W'.ι.appLE W' ⊤ (by simp) := (Scheme.Opens.ι_appLE W' W' ⊤ _).symm
  have e₂ : v.appTop = v.appLE ⊤ ⊤ (le_top (a := ⊤) |>.trans (Scheme.Hom.preimage_top v).ge) := (Scheme.Hom.appLE_eq_app v).symm
  rw [Iso.inv_comp_eq, Scheme.Hom.appIso_hom', e, e', e₂, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.map_appLE]
  simp only [hv]

theorem exists_iso_image {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (W' : Z'.Opens) (W : Z.Opens)
    (h : W = f ''ᵁ W') : ∃ v : W'.toScheme ≅ W.toScheme, v.hom ≫ W.ι = W'.ι ≫ f := by
  subst h
  exact ⟨f.isoImage W', Scheme.Hom.isoImage_hom_ι f W'⟩

theorem appTop_hom_inv {X Y : Scheme.{0}} (v : X ≅ Y) (a : Γ(X, ⊤)) :
    v.hom.appTop.hom (v.inv.appTop.hom a) = a := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, v.hom_inv_id, Scheme.Hom.id_appTop]; rfl

theorem appTop_inv_hom {X Y : Scheme.{0}} (v : X ≅ Y) (a : Γ(Y, ⊤)) :
    v.inv.appTop.hom (v.hom.appTop.hom a) = a := appTop_hom_inv v.symm a

theorem exists_transport {Z Z' : Scheme.{0}} {G : Over Z} {G' : Over Z'} {f : Z' ⟶ Z} {φ : G'.left ⟶ G.left}
    {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) (hφ : IsPullback φ G'.hom G.hom f)
    (hw : LBIso L' (L.pull φ)) (N : ℕ) :
    ∃ e : ∀ {X' X : Scheme.{0}} (a' : X' ⟶ Z') (a : X ⟶ Z) (u : X' ≅ X), u.hom ≫ a = a' ≫ f →
      LB.Sec (Out.LPow G' L' (N : ℤ) (Over.mk a')) → LB.Sec (Out.LPow G L (N : ℤ) (Over.mk a)),
    (∀ {X₁' X₂' X₁ X₂ : Scheme.{0}} {a₁' : X₁' ⟶ Z'} {a₂' : X₂' ⟶ Z'} {a₁ : X₁ ⟶ Z} {a₂ : X₂ ⟶ Z}
      (u₁ : X₁' ≅ X₁) (u₂ : X₂' ≅ X₂) (h₁ : u₁.hom ≫ a₁ = a₁' ≫ f) (h₂ : u₂.hom ≫ a₂ = a₂' ≫ f)
      (k' : X₂' ⟶ X₁') (k : X₂ ⟶ X₁) (hk' : k' ≫ a₁' = a₂') (hk : k ≫ a₁ = a₂), k' ≫ u₁.hom = u₂.hom ≫ k →
      ∀ (n : ℕ) (b : Fin n → LB.Sec (Out.LPow G' L' (N : ℤ) (Over.mk a₁'))) (c' : Fin n → Γ(X₂', ⊤))
        (c : Fin n → Γ(X₂, ⊤)), (∀ i, u₂.hom.appTop.hom (c i) = c' i) →
        ∀ s : LB.Sec (Out.LPow G' L' (N : ℤ) (Over.mk a₂')),
        Lin G' L' N (Over.homMk k' hk' : Over.mk a₂' ⟶ Over.mk a₁') b c' s →
          Lin G L N (Over.homMk k hk : Over.mk a₂ ⟶ Over.mk a₁) (fun i => e a₁' a₁ u₁ h₁ (b i)) c (e a₂' a₂ u₂ h₂ s)) ∧
    ∀ {X₁' X₁ Y : Scheme.{0}} {a₁' : X₁' ⟶ Z'} {a₁ : X₁ ⟶ Z} (u₁ : X₁' ≅ X₁) (h₁ : u₁.hom ≫ a₁ = a₁' ≫ f)
      (χ : Y ⟶ X₁) (n : ℕ) (b : Fin n → LB.Sec (Out.LPow G' L' (N : ℤ) (Over.mk a₁'))),
      BasisAlong G' L' N (Over.homMk (χ ≫ u₁.inv) rfl : Over.mk ((χ ≫ u₁.inv) ≫ a₁') ⟶ Over.mk a₁') b →
        BasisAlong G L N (Over.homMk χ rfl : Over.mk (χ ≫ a₁) ⟶ Over.mk a₁) (fun i => e a₁' a₁ u₁ h₁ (b i)) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_sectionPower_transport_cartesian_square Z Z' G G' f φ L L' hL hL' hφ hw N
  refine ⟨fun a' a u h => e (Over.mk a') (Over.mk a) u h, ?_, ?_⟩
  · intro X₁' X₂' X₁ X₂ a₁' a₂' a₁ a₂ u₁ u₂ h₁ h₂ k' k hk' hk hc n b c' c hcc s H
    obtain rfl : c' = fun i => u₂.hom.appTop.hom (c i) := funext fun i => (hcc i).symm
    exact (he (Over.mk a₁') (Over.mk a₂') (Over.mk a₁) (Over.mk a₂) u₁ u₂ h₁ h₂ (Over.homMk k' hk') (Over.homMk k hk)
      hc n b c s).1 H
  · intro X₁' X₁ Y a₁' a₁ u₁ h₁ χ n b B σ
    have hc' : (Iso.refl Y).hom ≫ χ ≫ a₁ = ((χ ≫ u₁.inv) ≫ a₁') ≫ f := by
      simp [← h₁]
    have hk : (χ ≫ u₁.inv) ≫ u₁.hom = (Iso.refl Y).hom ≫ χ := by simp
    have hid : ∀ a : Γ(Y, ⊤), (Iso.refl Y).hom.appTop.hom a = a := fun a => by simp
    obtain ⟨σ', rfl⟩ := (e (Over.mk ((χ ≫ u₁.inv) ≫ a₁')) (Over.mk (χ ≫ a₁)) (Iso.refl Y) hc').surjective σ
    refine (existsUnique_congr fun c => ?_).1 (B σ')
    refine Iff.trans ?_ (he (Over.mk a₁') (Over.mk ((χ ≫ u₁.inv) ≫ a₁')) (Over.mk a₁)
      (Over.mk (χ ≫ a₁)) u₁ (Iso.refl Y) h₁ hc' (Over.homMk (χ ≫ u₁.inv) rfl) (Over.homMk χ rfl) hk n b c σ')
    exact iff_of_eq (congrArg (fun c => Lin G' L' N _ b c σ') (funext fun k => (hid (c k)).symm))

theorem unit_rel_push {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (W' : Z'.Opens) (W : Z.Opens)
    (hle : W ≤ f ''ᵁ W') (v : W'.toScheme ≅ W.toScheme) (hv : v.hom ≫ W.ι = W'.ι ≫ f) {n : ℕ} (r s : ℤ)
    (g : Γ(Z', W')) (c : Γ(W'.toScheme, ⊤)ˣ) (M : GL (Fin n) Γ(W'.toScheme, ⊤))
    (hg : W'.topIso.inv.hom g = (c ^ r * Matrix.GeneralLinearGroup.det M ^ s).val) :
    W.topIso.inv.hom ((Z.presheaf.map (homOfLE hle).op).hom ((f.appIso W').inv.hom g)) =
      (Units.map v.inv.appTop.hom.toMonoidHom c ^ r *
        Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map v.inv.appTop.hom M) ^ s).val := by
  have E : v.hom.appTop.hom (W.topIso.inv.hom ((Z.presheaf.map (homOfLE hle).op).hom ((f.appIso W').inv.hom g))) =
      W'.topIso.inv.hom g := congrArg (fun k => k.hom g) (appIso_inv_topIso_inv f W' W hle v.hom hv)
  have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map v.inv.appTop.hom M) =
      Units.map v.inv.appTop.hom.toMonoidHom (Matrix.GeneralLinearGroup.det M) :=
    Units.ext (RingHom.map_det v.inv.appTop.hom M.val).symm
  rw [hd, ← map_zpow, ← map_zpow, ← map_mul]
  exact (appTop_inv_hom v _).symm.trans (congrArg v.inv.appTop.hom (E.trans hg))

theorem hasFrames_pushLB : ∀ (Z Z' : Scheme.{0}) (G : Over Z) (G' : Over Z') (f : Z' ⟶ Z) [IsOpenImmersion f] (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsPullback φ G'.hom G.hom f → LBIso L' (L.pull φ) → f ⁻¹' abLocus G ⊆ abLocus G' → ∀ (N : ℕ) (A : LB Z') (n : ℕ) (r s : ℤ), HasFrames G' L' N A n r s → HasFrames G L N (pushLB f A) n r s := by
  intro Z Z' G G' f _ φ L L' hL hL' hφ hw hab N A n r s ⟨th, b, h₁, h₂⟩
  obtain ⟨e₁, he₁, hb₁⟩ := exists_transport hL hL' hφ hw 1
  obtain ⟨eN, heN, hbN⟩ := exists_transport hL hL' hφ hw N
  choose u hu using fun i : A.ι => exists_iso_image f (A.U i) (f ''ᵁ A.U i) rfl
  refine ⟨fun i => e₁ (A.U i).ι (f ''ᵁ A.U i).ι (u i) (hu i) (th i),
    fun i k => eN (A.U i).ι (f ''ᵁ A.U i).ι (u i) (hu i) (b i k), fun (i j : A.ι) => ?_,
    fun (i : A.ι) W _ _ _ hW (χ : Sp W ⟶ (f ''ᵁ A.U i).toScheme) hχ => ?_⟩
  · obtain ⟨c, M, ⟨t, ht, ht'⟩, hb, hg⟩ := h₁ i j
    obtain ⟨v, hv⟩ := exists_iso_image f (A.U i ⊓ A.U j) (f ''ᵁ A.U i ⊓ f ''ᵁ A.U j)
      (le_antisymm (image_inf_le f _ _) (le_inf (f.image_mono inf_le_left) (f.image_mono inf_le_right)))
    have ki : Z'.homOfLE (inf_le_left : A.U i ⊓ A.U j ≤ A.U i) ≫ (u i).hom =
        v.hom ≫ Z.homOfLE (inf_le_left : f ''ᵁ A.U i ⊓ f ''ᵁ A.U j ≤ _) := by
      rw [← cancel_mono (f ''ᵁ A.U i).ι, Category.assoc, Category.assoc, hu, Scheme.homOfLE_ι, hv, Scheme.homOfLE_ι_assoc]
    have kj : Z'.homOfLE (inf_le_right : A.U i ⊓ A.U j ≤ A.U j) ≫ (u j).hom =
        v.hom ≫ Z.homOfLE (inf_le_right : f ''ᵁ A.U i ⊓ f ''ᵁ A.U j ≤ _) := by
      rw [← cancel_mono (f ''ᵁ A.U j).ι, Category.assoc, Category.assoc, hu, Scheme.homOfLE_ι, hv, Scheme.homOfLE_ι_assoc]
    refine ⟨Units.map v.inv.appTop.hom.toMonoidHom c, Matrix.GeneralLinearGroup.map v.inv.appTop.hom M,
      ⟨e₁ (A.U i ⊓ A.U j).ι (f ''ᵁ A.U i ⊓ f ''ᵁ A.U j).ι v hv t, ?_, ?_⟩, fun k => ?_, ?_⟩
    · exact he₁ (u i) v (hu i) hv _ _ _ (Scheme.homOfLE_ι _ _) ki 1 (fun _ => th i) (fun _ => 1) (fun _ => 1)
        (fun _ => map_one _) t ht
    · exact he₁ (u j) v (hu j) hv _ _ _ (Scheme.homOfLE_ι _ _) kj 1 (fun _ => th j) (fun _ => c.val)
        (fun _ => v.inv.appTop.hom c.val) (fun _ => appTop_hom_inv v _) t ht'
    · obtain ⟨t, ht, ht'⟩ := hb k
      refine ⟨eN (A.U i ⊓ A.U j).ι (f ''ᵁ A.U i ⊓ f ''ᵁ A.U j).ι v hv t, ?_, ?_⟩
      · exact heN (u i) v (hu i) hv _ _ _ (Scheme.homOfLE_ι _ _) ki 1 (fun _ => b i k) (fun _ => 1) (fun _ => 1)
          (fun _ => map_one _) t ht
      · exact heN (u j) v (hu j) hv _ _ _ (Scheme.homOfLE_ι _ _) kj n (b j) (fun k' => M.val k k')
          (fun k' => v.inv.appTop.hom (M.val k k')) (fun _ => appTop_hom_inv v _) t ht'
    · exact unit_rel_push f (A.U i ⊓ A.U j) _ (image_inf_le f _ _) v hv r s _ c M hg
  · have hc : ((Out.jK W ≫ (χ ≫ (u i).inv) ≫ (A.U i).ι) ≫ f) = Out.jK W ≫ χ ≫ (f ''ᵁ A.U i).ι := by
      simp only [Category.assoc]; rw [← hu i, Iso.inv_hom_id_assoc]
    obtain ⟨B₁, BN⟩ := h₂ i W hW (χ ≫ (u i).inv) (by
      rintro _ ⟨x, rfl⟩
      refine hab (hχ ⟨x, ?_⟩)
      exact (congrArg (fun k => k x) hc).symm.trans (Scheme.Hom.comp_apply _ _ _))
    exact ⟨hb₁ (u i) (hu i) χ 1 (fun _ => th i) B₁, hbN (u i) (hu i) χ n (b i) BN⟩

end GlobalTheory.ModelSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TransitionFramesPushOpenImmersionImageStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transitionFrames_push_openImmersion_image : ∀ (Z Z' : Scheme.{0}) (G : Over Z) (G' : Over Z') (f : Z' ⟶ Z) [IsOpenImmersion f] (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsPullback φ G'.hom G.hom f → LBIso L' (L.pull φ) → f ⁻¹' abLocus G ⊆ abLocus G' → ∀ (N : ℕ) (A : LB Z') (n : ℕ) (r s : ℤ), HasFrames G' L' N A n r s → HasFrames G L N (pushLB f A) n r s := by
  first | exact @GlobalTheory.ModelSum.hasFrames_pushLB | exact GlobalTheory.ModelSum.hasFrames_pushLB | (intros; apply GlobalTheory.ModelSum.hasFrames_pushLB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAdjointPrimitiveOfDenseEighthPowers
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAdjointPrimitiveOfDenseEighthPowers
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SharpAdjoint

section Bundles

variable {X X' Y Y' : Scheme.{0}}

theorem iso_linComb_pull {L : LB X} {L' : LB X'} {F : X' ⟶ X} (H : LBIso L' (L.pull F)) {K : Type} [Fintype K]
    (ψ' : K → (Y' ⟶ X')) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (e : ∀ k, ψ' k ≫ F = h ≫ ψ k) :
    LBIso (LB.LinComb L' ψ' ε) ((LB.LinComb L ψ ε).pull h) := by
  obtain ⟨w, hw⟩ := H
  exact LBIso.chartPull (chartPullId _) (chartPullOut L ψ ε h _ e) (iso_linComb ((isGen_iff w).1 hw) ψ' ε)

theorem iso_up {M N : LB Y} {M' N' : LB Y'} {h : Y' ⟶ Y} (hM : M.IsLB) (hN : N.IsLB) (hM' : M'.IsLB) (hN' : N'.IsLB)
    (a : LBIso M' (M.pull h)) (b : LBIso N' (N.pull h)) (H : LBIso M N) : LBIso M' N' :=
  LBIso.trans hM' (pull_isLB hM h) hN' a (LBIso.trans (pull_isLB hM h) (pull_isLB hN h) hN'
    (H.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M h h rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull N h h rfl)) b.symm)

end Bundles

section Field

variable {K : Type} [Field K] {S' : Scheme.{0}} (f : S' ⟶ Sp K)

theorem exists_point [Nonempty S'] :
    ∃ (K' : Type) (_ : Field K') (i : K →+* K') (x : Sp K' ⟶ S'), x ≫ f = spMap i := by
  obtain ⟨y⟩ := ‹Nonempty S'›
  obtain ⟨i, hi⟩ := Spec.map_surjective (S'.fromSpecResidueField y ≫ f)
  exact ⟨S'.residueField y, inferInstance, i.hom, S'.fromSpecResidueField y, hi.symm⟩

variable {f}

theorem iso_down [Nonempty S'] {X₀ X : Scheme.{0}} {p₀ : X₀ ⟶ Sp K} {p : X ⟶ S'} {h : X ⟶ X₀}
    (H : IsPullback h p p₀ f) (h₁ : Smooth p₀) (h₂ : IsProper p₀) (h₃ : GeometricallyConnected p₀)
    {M N : LB X₀} {M' N' : LB X} (hM : M.IsLB) (hN : N.IsLB) (hM' : M'.IsLB) (hN' : N'.IsLB)
    (a : LBIso M' (M.pull h)) (b : LBIso N' (N.pull h)) (c : LBIso M' N') : LBIso M N := by
  obtain ⟨K', _, i, x, hx⟩ := exists_point f
  have P : IsPullback (pullback.fst p x ≫ h) (pullback.snd p x) p₀ (spMap i) :=
    hx ▸ (IsPullback.of_hasPullback p x).paste_horiz H
  have d : LBIso (M.pull h) (N.pull h) := LBIso.trans (pull_isLB hM h) hM' (pull_isLB hN h) a.symm
    (LBIso.trans hM' hN' (pull_isLB hN h) c b)
  exact (GlobalTheory.lb_gen_iso_descend_field K K' i X₀ _ p₀ _ _ h₁ h₂ h₃ P).2 M N hM hN (d.chartPull
    (chartPullSame M _ _ _ (pullback.fst p x) fun _ => rfl) (chartPullSame N _ _ _ (pullback.fst p x) fun _ => rfl))

end Field

section Group

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
  (h : IsGrpPullback G' G f φ)

section Points

variable {T : Over S} {T' : Over S'} (U : Over.mk (T'.hom ≫ f) ⟶ T)

theorem push_comp {x' : T' ⟶ G'} {x : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x) {a' : G' ⟶ G'} {a : G ⟶ G}
    (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w (x' ≫ a') = U ≫ x ≫ a := by
  rw [← Category.assoc, ← hx]
  refine Over.OverMorphism.ext ?_
  show (x'.left ≫ _) ≫ _ = (x'.left ≫ _) ≫ _
  rw [Category.assoc, ha, Category.assoc]

theorem iso_cubeLB_pull [IsCommMonObj G] [IsCommMonObj G'] {L : LB G.left} {L' : LB G'.left}
    (H : LBIso L' (L.pull φ)) {a' b' : T' ⟶ G'} {a b : T ⟶ G} (ha : pushPt h.1.w a' = U ≫ a)
    (hb : pushPt h.1.w b' = U ≫ b) : LBIso (cubeLB G' ![a', b'] L') ((cubeLB G ![a, b] L).pull U.left) :=
  iso_linComb_pull H _ _ _ U.left fun I => psum_push h _ _ U (fun i => by
    fin_cases i
    exacts [ha, hb]) I.down

end Points

def sqMap : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G ⊗ G := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))

theorem push_fst : pushPt h.1.w (fst G' G') = sqMap h ≫ fst G G := (lift_fst _ _).symm

theorem push_snd : pushPt h.1.w (snd G' G') = sqMap h ≫ snd G G := (lift_snd _ _).symm

theorem isPullback_sqMap : IsPullback (sqMap h).left (G' ⊗ G').hom (G ⊗ G).hom f := by
  have e₁ : (sqMap h).left ≫ (fst G G).left = (fst G' G').left ≫ φ := congrArg (fun q => q.left) (push_fst h).symm
  have e₂ : (sqMap h).left ≫ (snd G G).left = (snd G' G').left ≫ φ := congrArg (fun q => q.left) (push_snd h).symm
  have A : IsPullback (snd G G).left (fst G G).left G.hom G.hom := (IsPullback.of_hasPullback G.hom G.hom).flip
  have A' : IsPullback (snd G' G').left (fst G' G').left G'.hom G'.hom := (IsPullback.of_hasPullback G'.hom G'.hom).flip
  have B := A'.paste_horiz h.1
  rw [← e₂, ← h.1.w] at B
  have C := (IsPullback.of_right B e₁ A).paste_vert h.1
  rwa [Over.w, Over.w] at C

def selfMap : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w

theorem push_id : pushPt h.1.w (𝟙 G') = selfMap h ≫ 𝟙 G :=
  Over.OverMorphism.ext ((Category.id_comp _).trans (Category.comp_id _).symm)

theorem push_end {a' : G' ⟶ G'} {a : G ⟶ G} (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w a' = selfMap h ≫ a :=
  Over.OverMorphism.ext ha

end Group

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}

theorem isLB_linComb {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X))
    (ε : K → ℤ) : (LB.LinComb L ψ ε).IsLB := DVR.linComb_isLB _ hL _ _

theorem transfer {K : Type} [Field K] {S₁ S₂ : Scheme.{0}} [Nonempty S₁] {s₀ : Sp K ⟶ Sp o} {s₁ : S₁ ⟶ Sp o}
    {s₂ : S₂ ⟶ Sp o} {f₁ : S₁ ⟶ Sp K} {f₂ : S₂ ⟶ Sp K} {t₀ : TObj g k J b s₀} {t₁ : TObj g k J b s₁}
    {t₂ : TObj g k J b s₂} (H₁ : TMap t₁ t₀ f₁) (H₂ : TMap t₂ t₀ f₂) (w w' : J) :
    (LBIso (cubeLB t₁.A ![fst t₁.A t₁.A ≫ t₁.act w, snd t₁.A t₁.A] t₁.L)
        (cubeLB t₁.A ![fst t₁.A t₁.A, snd t₁.A t₁.A ≫ t₁.act w'] t₁.L) →
      LBIso (cubeLB t₂.A ![fst t₂.A t₂.A ≫ t₂.act w, snd t₂.A t₂.A] t₂.L)
        (cubeLB t₂.A ![fst t₂.A t₂.A, snd t₂.A t₂.A ≫ t₂.act w'] t₂.L)) ∧
    (LBIso t₁.L (cubeLB t₁.A ![𝟙 t₁.A, t₁.act w] t₁.L) → LBIso t₂.L (cubeLB t₂.A ![𝟙 t₂.A, t₂.act w] t₂.L)) := by
  obtain ⟨φ, h, hL, -, hact⟩ := H₁
  obtain ⟨φ', h', hL', -, hact'⟩ := H₂
  let _ := t₀.ab.comm
  let _ := t₁.ab.comm
  let _ := t₂.ab.comm
  have := t₀.ab.smooth
  have := t₀.ab.proper
  have := t₀.ab.geomConnected
  have pr : IsProper (t₀.A ⊗ t₀.A).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  have i₂ := iso_cubeLB_pull h _ hL (push_comp h _ (push_fst h) (hact w)) (push_snd h)
  have i₃ := iso_cubeLB_pull h _ hL (push_fst h) (push_comp h _ (push_snd h) (hact w'))
  have i₄ := iso_cubeLB_pull h _ hL (push_id h) (push_end h (hact w))
  have j₂ := iso_cubeLB_pull h' _ hL' (push_comp h' _ (push_fst h') (hact' w)) (push_snd h')
  have j₃ := iso_cubeLB_pull h' _ hL' (push_fst h') (push_comp h' _ (push_snd h') (hact' w'))
  have j₄ := iso_cubeLB_pull h' _ hL' (push_id h') (push_end h' (hact' w))
  refine ⟨fun H => ?_, fun H => ?_⟩
  · have d := iso_down (isPullback_sqMap h) (smooth_tensorObj_hom _ _) pr (geometricallyConnected_tensorObj_hom _ _)
      (isLB_linComb t₀.isLB _ _) (isLB_linComb t₀.isLB _ _) (isLB_linComb t₁.isLB _ _) (isLB_linComb t₁.isLB _ _)
      i₂ i₃ H
    exact iso_up (isLB_linComb t₀.isLB _ _) (isLB_linComb t₀.isLB _ _) (isLB_linComb t₂.isLB _ _)
      (isLB_linComb t₂.isLB _ _) j₂ j₃ d
  · have d := iso_down h.1 ‹_› ‹_› ‹_› t₀.isLB (isLB_linComb t₀.isLB _ _) t₁.isLB (isLB_linComb t₁.isLB _ _) hL i₄ H
    exact iso_up t₀.isLB (isLB_linComb t₀.isLB _ _) t₂.isLB (isLB_linComb t₂.isLB _ _) hL' j₄ d

theorem adjoint_primitive_of_dense : Out.GlobalFnsSt → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Dense (fromSet em (SharpClass (b := b) W a bas em) t) → (∀ j j', (a j).transpose * (W + W.transpose) = (W + W.transpose) * a j' → LBIso (cubeLB t.A ![fst t.A t.A ≫ t.act j, snd t.A t.A] t.L) (cubeLB t.A ![fst t.A t.A, snd t.A t.A ≫ t.act j'] t.L)) ∧ ∀ j, (W + W.transpose) * a j = W → LBIso t.L (cubeLB t.A ![𝟙 t.A, t.act j] t.L) := by
  intro hG cube h g W J a bas k o _ b em S _ s t hd
  let _ := t.ab.comm
  have : Nonempty (Sp ℂ) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
  refine ⟨fun j j' hj => GlobalTheory.T.adjoint_endomorphisms_cubeLB_of_dense_fibres hG S t.A t.L _ _ t.ab t.isLB t.ample (t.hom j) (t.hom j') (hd.mono ?_),
    fun j hj => GlobalTheory.T.lbIso_cube_graph_of_dense_fibres hG S t.A t.L _ t.ab t.isLB t.ample t.rigid (t.hom j) (hd.mono ?_)⟩
  · rintro p ⟨K, _, x, hp, K₀, _, β, i, i', t₀, tx, tc, -, -, ⟨φ, hφ, hL, -, hact⟩, m₂, m₁, c, -, pr, hm, hu, hl,
      hmat, -⟩
    exact ⟨K, inferInstance, x, tx.A, inferInstance, tx.ab.comm, φ, tx.L, tx.act j, tx.act j', hp, hφ, tx.isLB, hL,
      hact j, hact j', (transfer m₁ m₂ j j').1 ((PowerAdjoint.matrix_primitive_adjoint cube W ℂ o _ h k _ c tc.pol pr
        hm hu hl (a j) (tc.act j) (hmat j)).2 (a j') (tc.act j') (hmat j') hj)⟩
  · rintro p ⟨K, _, x, hp, K₀, _, β, i, i', t₀, tx, tc, -, -, ⟨φ, hφ, hL, -, hact⟩, m₂, m₁, c, -, pr, hm, hu, hl,
      hmat, -⟩
    exact ⟨K, inferInstance, x, tx.A, inferInstance, tx.ab.comm, φ, tx.L, tx.act j, hp, hφ, tx.isLB, hL,
      hact j, (transfer m₁ m₂ j j).2 ((PowerAdjoint.matrix_primitive_adjoint cube W ℂ o _ h k _ c tc.pol pr
        hm hu hl (a j) (tc.act j) (hmat j)).1 hj)⟩

end GlobalTheory.SharpAdjoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAdjointPrimitiveOfDenseEighthPowersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLevel_adjoint_primitive_of_dense_eighth_powers : Out.GlobalFnsSt → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Dense (fromSet em (SharpClass (b := b) W a bas em) t) → (∀ j j', (a j).transpose * (W + W.transpose) = (W + W.transpose) * a j' → LBIso (cubeLB t.A ![fst t.A t.A ≫ t.act j, snd t.A t.A] t.L) (cubeLB t.A ![fst t.A t.A, snd t.A t.A ≫ t.act j'] t.L)) ∧ ∀ j, (W + W.transpose) * a j = W → LBIso t.L (cubeLB t.A ![𝟙 t.A, t.act j] t.L) := by
  first | exact @GlobalTheory.SharpAdjoint.adjoint_primitive_of_dense | exact GlobalTheory.SharpAdjoint.adjoint_primitive_of_dense | (intros; apply GlobalTheory.SharpAdjoint.adjoint_primitive_of_dense <;> assumption)
end
end
