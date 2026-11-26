module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueRealLinearOfEventuallyAddModDiscrete
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
open Filter Topology Set Metric

namespace GlobalTheory

section Analytic

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W] {A : Type*} [AddCommGroup A]
  {ι : Type*} {Y : Type*} [TopologicalSpace Y] [T2Space Y]

theorem tendsto_map_nhds_of_separating [CompleteSpace V] [ProperSpace W] {ex : W →+ A}
    (hex : Function.Surjective ex) {G : V →+ A} {S : Set A} (h0 : (0 : A) ∈ S) {f : ι → A → Y}
    (hsep : ∀ a ∈ S, ∀ b ∈ S, (∀ i, f i a = f i b) → a = b)
    (hSe : IsOpen (ex ⁻¹' S)) (hSG : IsOpen (G ⁻¹' S))
    (hfe : ∀ i, ContinuousOn (fun w ↦ f i (ex w)) (ex ⁻¹' S))
    (hfG : ∀ i, ContinuousOn (fun z ↦ f i (G z)) (G ⁻¹' S)) :
    ∀ N ∈ 𝓝 (0 : W), ∀ᶠ z in 𝓝 (0 : V), G z ∈ ex '' N := by
  intro N hN
  have hN' : N ∩ ex ⁻¹' S ∈ 𝓝 (0 : W) := inter_mem hN (hSe.mem_nhds (by simpa using h0))
  obtain ⟨R, hR, hRN⟩ := nhds_basis_closedBall.mem_iff.1 hN'
  set r := R / 4 with hr
  have hr0 : 0 < r := by positivity
  let T : Set V := {z | ∃ w ∈ closedBall (0 : W) (2 * r), ex w = G z}
  have hKS : closedBall (0 : W) (2 * r) ⊆ ex ⁻¹' S := fun w hw ↦
    (hRN (closedBall_subset_closedBall (by linarith) hw)).2
  have hTS : T ⊆ G ⁻¹' S := by
    rintro z ⟨w, hw, h⟩
    rw [mem_preimage, ← h]
    exact hKS hw
  have hcl : closure T ∩ G ⁻¹' S ⊆ T := by
    rintro z ⟨hz, hzS⟩
    obtain ⟨x, hx, hxz⟩ := mem_closure_iff_seq_limit.1 hz
    choose w hw hwx using hx
    obtain ⟨w₀, hw₀, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : W) (2 * r)).tendsto_subseq hw
    refine ⟨w₀, hw₀, hsep _ (hKS hw₀) _ hzS fun i ↦ ?_⟩
    have h1 := (((hfe i).continuousAt (hSe.mem_nhds (hKS hw₀))).tendsto).comp hlim
    have h2 := (((hfG i).continuousAt (hSG.mem_nhds hzS)).tendsto).comp
      (hxz.comp hφ.tendsto_atTop)
    refine tendsto_nhds_unique h1 (h2.congr fun n ↦ ?_)
    simp [hwx]
  obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq W
  let B : ℕ → Set V := fun j ↦ {z | ∃ w ∈ ball (c j) r, ex w = G z}
  have hB : ⋃ j, closure (B j) = univ := by
    refine eq_univ_of_forall fun z ↦ ?_
    obtain ⟨w, hw⟩ := hex (G z)
    obtain ⟨j, hj⟩ := hc.exists_dist_lt w hr0
    exact mem_iUnion.2 ⟨j, subset_closure ⟨w, hj, hw⟩⟩
  obtain ⟨j, y, hy⟩ := nonempty_interior_of_iUnion_of_closed (fun _ ↦ isClosed_closure) hB
  obtain ⟨z₀, hz₀i, w₀, hw₀, hz₀⟩ :=
    mem_closure_iff.1 (interior_subset hy) _ isOpen_interior hy
  have hBT : ∀ z ∈ B j, z - z₀ ∈ T := by
    rintro z ⟨w, hw, h⟩
    refine ⟨w - w₀, ?_, by simp [h, hz₀]⟩
    rw [mem_closedBall, dist_zero_right, ← dist_eq_norm]
    have := dist_triangle_right w w₀ (c j)
    rw [mem_ball] at hw hw₀
    linarith
  have h1 : ∀ᶠ z in 𝓝 (0 : V), z + z₀ ∈ closure (B j) := by
    have : Tendsto (fun z : V ↦ z + z₀) (𝓝 0) (𝓝 z₀) := by
      simpa using (continuous_add_const z₀).tendsto 0
    exact this (mem_interior_iff_mem_nhds.1 hz₀i)
  filter_upwards [h1, hSG.mem_nhds (show (0 : V) ∈ G ⁻¹' S by simpa using h0)] with z hz hzS
  have hzT : z ∈ closure T := by
    simpa using map_mem_closure (continuous_sub_right z₀) hz hBT
  obtain ⟨w, hw, h⟩ := hcl ⟨hzT, hzS⟩
  exact ⟨w, (hRN (closedBall_subset_closedBall (by linarith) hw)).1, h⟩

theorem existsUnique_linear_lift_of_separating [NormedSpace ℂ V] [NormedSpace ℂ W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {ex : W →+ A}
    (hex : Function.Surjective ex) (hker : IsDiscrete (ex.ker : Set W))
    {G : V →+ A} {S : Set A} (h0 : (0 : A) ∈ S) {f : ι → A → ℂ}
    (hsep : ∀ a ∈ S, ∀ b ∈ S, (∀ i, f i a = f i b) → a = b)
    (hSe : IsOpen (ex ⁻¹' S)) (hSG : IsOpen (G ⁻¹' S))
    (hfe : ∀ i, DifferentiableOn ℂ (fun w ↦ f i (ex w)) (ex ⁻¹' S))
    (hfG : ∀ i, DifferentiableOn ℂ (fun z ↦ f i (G z)) (G ⁻¹' S))
    (hD : ∀ w, (∀ i, fderiv ℂ (fun w ↦ f i (ex w)) 0 w = 0) → w = 0) :
    ∃! F : V →ₗ[ℂ] W, ∀ z, ex (F z) = G z := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  have : ProperSpace W := FiniteDimensional.proper ℂ W
  have ht := tendsto_map_nhds_of_separating hex h0 hsep hSe hSG
    (fun i ↦ (hfe i).continuousOn) (fun i ↦ (hfG i).continuousOn)
  have ht' : Tendsto G (𝓝 0) (map ex (𝓝 0)) := fun s hs ↦
    (ht _ hs).mono fun z hz ↦ image_preimage_subset _ _ hz
  obtain ⟨U, hU, hU0⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1 hker 0 ex.ker.zero_mem
  obtain ⟨N, hN, hNU⟩ := exists_nhds_half_neg (hU.mem_nhds (hU0.ge rfl).1)
  have hinj : InjOn ex N := fun x hx y hy hxy ↦
    sub_eq_zero.1 (hU0.le ⟨hNU x hx y hy, by simp [AddMonoidHom.mem_ker, hxy]⟩)
  have hs : ∀ᶠ z in 𝓝 0, Function.invFunOn ex N (ex z) = z := by
    filter_upwards [hN] with z hz using hinj.leftInvOn_invFunOn hz
  have hs0 : Function.invFunOn ex N 0 = 0 := by simpa using hs.self_of_nhds
  have hc : ContinuousAt (fun z ↦ Function.invFunOn ex N (G z)) 0 := by
    rw [ContinuousAt, map_zero, hs0]
    have h1 : Tendsto (Function.invFunOn ex N) (map ex (𝓝 0)) (𝓝 0) :=
      tendsto_map'_iff.2 (tendsto_id.congr' (hs.mono fun z hz ↦ hz.symm))
    exact h1.comp ht'
  obtain ⟨L, hL, hu⟩ := existsUnique_realLinear_lift_of_germ (ex := G) hker hc
    ((ht N hN).mono fun z hz ↦ Function.invFunOn_eq hz)
  have hI : ∀ (c : ℂ) z, L (c • z) = c • L z := by
    intro c z
    refine sub_eq_zero.1 (hD _ fun i ↦ ?_)
    have h1 : DifferentiableAt ℂ (fun w ↦ f i (ex w)) 0 :=
      (hfe i).differentiableAt (hSe.mem_nhds (by simpa using h0))
    have h2 : DifferentiableAt ℂ (fun z ↦ f i (G z)) 0 :=
      (hfG i).differentiableAt (hSG.mem_nhds (by simpa using h0))
    have h3 := (h1.hasFDerivAt.restrictScalars ℝ)
    rw [← map_zero L] at h3
    have h4 := h3.comp 0 L.hasFDerivAt
    have h5 : ((fun w ↦ f i (ex w)) ∘ L) = fun z ↦ f i (G z) := by
      funext z
      simp [hL]
    rw [h5, map_zero] at h4
    have h6 := h4.unique (h2.hasFDerivAt.restrictScalars ℝ)
    have h7 : ∀ z, fderiv ℂ (fun w ↦ f i (ex w)) 0 (L z) = fderiv ℂ (fun z ↦ f i (G z)) 0 z :=
      fun z ↦ DFunLike.congr_fun h6 z
    rw [map_sub, h7, map_smul, map_smul, h7, sub_self]
  refine ⟨⟨⟨L, L.map_add⟩, hI⟩, hL, fun F hF ↦ ?_⟩
  have := realLinear_eq_of_sub_mem_discrete hker (L := F.restrictScalars ℝ) (L' := L.toLinearMap)
    fun x ↦ by simp [AddMonoidHom.mem_ker, hF, hL]
  ext z
  exact DFunLike.congr_fun this z

end Analytic

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor


open TangentOrigin in
theorem existsUnique_linear_lift_of_isHolTo :
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g m : ℕ)
      (u : HolUnif A L g), (∀ v, IsTangent v → ∃! w, u.IsDiff w v) →
      (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) →
      ∀ G : (Fin m → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A), (∀ z w, G (z + w) = G z * G w) →
      IsHolTo (Set.univ : Set (Fin m → ℂ)) (fun z => (G z).left) →
      ∃! F : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = G z := by
  intro A _ _ L g m u h₁ h₂ G hG hhol
  letI : CommGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    { (inferInstance : Group (𝟙_ (Over (Sp ℂ)) ⟶ A)) with
      mul_comm := fun a b ↦ by
        obtain ⟨z, rfl⟩ := u.ex_onto a
        obtain ⟨w, rfl⟩ := u.ex_onto b
        exact (u.ex_add z w).symm.trans ((congrArg u.ex (add_comm z w)).trans (u.ex_add w z)) }
  let ex : (Fin g → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (u.ex z)) u.ex_add
  let G' : (Fin m → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (G z)) hG
  let pt : (𝟙_ (Over (Sp ℂ))).left := (default : PrimeSpectrum ℂ)
  have hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt := fun q ↦
    Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := (u.ex 0).left pt) (U := ⊤)
    (Set.mem_univ _)
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
    intro q _
    rw [hsub q]
    exact hpU
  have hker : (ex.ker : Set (Fin g → ℂ)) = u.Λ := Set.ext fun z ↦ u.ker z
  refine existsUnique_linear_lift_of_separating (ex := ex) (G := G') u.ex_onto
    (hker ▸ isDiscrete_iff_discreteTopology.2 u.discrete)
    (S := {a | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U})
    (f := fun (s : Γ(A.left, U)) a ↦ valAt' (Additive.toMul a).left U s)
    ?_ ?_ (u.hol U 0).1 ?_ (fun s ↦ (u.hol U s).2) ?_ ?_
  · rw [← map_zero ex]
    exact h0
  · intro a ha b hb h
    refine Over.OverMorphism.ext (f := Additive.toMul a) (g := Additive.toMul b)
      (ext_evalPt (R := ℂ) hU ha hb (RingHom.ext fun s ↦ ?_))
    exact (valAt'_eq_evalPt _ U ha s).symm.trans ((h s).trans (valAt'_eq_evalPt _ U hb s))
  · have := (hhol U 0).1
    simp only [Set.mem_univ, true_and] at this
    exact this
  · intro s
    have := (hhol U s).2
    simp only [Set.mem_univ, true_and] at this
    exact this
  · intro w hw
    obtain ⟨v, ⟨hv, hd⟩, -⟩ := h₂ w
    have hvU := (tangent_mem_iff (u := u) hv U).2 h0
    refine (h₁ v hv).unique hd ((isDiff_iff hv hU hvU h0 0).2 ?_)
    rw [(isDiff_iff hv hU hvU h0 w).1 hd]
    refine RingHom.ext fun s ↦ TrivSqZeroExt.ext rfl ?_
    rw [jet_snd, jet_snd, map_zero]
    exact hw s

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVarietStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.existsUnique_linearLift_of_holomorphic_abelianVariety : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g m : ℕ) (u : HolUnif A L g),
  (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) →
  ∀ G : (Fin m → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A), (∀ z w, G (z + w) = G z * G w) →
  IsHolTo (Set.univ : Set (Fin m → ℂ)) (fun z => (G z).left) →
  ∃! F : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = G z := by
  first | exact @GlobalTheory.existsUnique_linear_lift_of_isHolTo | exact GlobalTheory.existsUnique_linear_lift_of_isHolTo | (intros; apply GlobalTheory.existsUnique_linear_lift_of_isHolTo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory
namespace SymmetricSemicharacter
open CubeValues

lemma valueRules : ValueRules := by
  intro X x
  have h1 : ∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U := fun U =>
    ⟨fun h => h (x := (default : PrimeSpectrum ℂ)) trivial, fun h p _ => by
      have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      subst this
      exact h⟩
  refine ⟨h1, fun U h => ?_, fun U V h f hV => ?_, fun Y φ U f => ?_, fun U f => ?_,
    fun p hp U a h => ?_⟩
  · exact ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.appLE U ⊤ h).hom,
      fun f => by simp only [valAt', dif_pos h, valAt]; rfl⟩
  · have hU : ⊤ ≤ x ⁻¹ᵁ U := fun p hp => h (hV hp)
    simp only [valAt', dif_pos hV, dif_pos hU, valAt]
    congr 1
    exact congr($(Scheme.Hom.map_appLE x hV (homOfLE h).op).hom f)
  · by_cases h : ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U
    · have h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := h
      simp only [valAt', dif_pos h, dif_pos h', valAt]
      congr 1
    · have h' : ¬ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := h
      simp only [valAt', dif_neg h, dif_neg h']
  · by_cases h : ⊤ ≤ x ⁻¹ᵁ U
    · have e : (Sp ℂ).basicOpen ((x.appLE U ⊤ h).hom f) = x ⁻¹ᵁ X.basicOpen f := by
        rw [Scheme.basicOpen_appLE, top_inf_eq]
      simp only [valAt', dif_pos h, valAt]
      rw [← e]
      generalize (x.appLE U ⊤ h).hom f = s
      obtain ⟨a, rfl⟩ : ∃ a : ℂ, (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a = s :=
        ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom s, by simp⟩
      have ea : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) = a := by simp
      rw [ea]
      constructor
      · rintro k rfl
        rw [map_zero, Scheme.basicOpen_zero] at k
        exact k (x := (default : PrimeSpectrum ℂ)) trivial
      · intro k
        exact (Scheme.basicOpen_of_isUnit _ ((isUnit_iff_ne_zero.2 k).map _)).ge
    · simp only [valAt', dif_neg h, ne_eq, not_true, iff_false]
      exact fun k => h fun p hp => X.basicOpen_le f (k hp)
  · simp only [valAt', dif_pos h, valAt, constFn]
    have := congr($(Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ (fun _ _ => trivial) h).hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
    simp only [hp, CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    have e : ∀ k, Scheme.Hom.appLE (𝟙 (Sp ℂ)) ⊤ ⊤ k = 𝟙 _ := fun k => by
      rw [← Scheme.Hom.id_app]
      exact (Scheme.Hom.app_eq_appLE (𝟙 (Sp ℂ)) (U := ⊤)).symm
    rw [e]
    simp

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

lemma ex_neg_left (z : Fin g → ℂ) :
    (u.ex z).left ≫ (GrpObj.inv : A ⟶ A).left = (u.ex (-z)).left := by
  have h : u.ex (-z) = (u.ex z)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← u.ex_add, neg_add_cancel, ex_zero]
  rw [h, Hom.inv_def, Over.comp_left]

lemma exists_chart (hv : ValueRules) (hL : L.IsLB) (z : Fin g → ℂ) :
    ∃ i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i := by
  have h : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i := by
    rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨i, ((hv _ (u.ex z).left).1 _).2 hi⟩

lemma mul_neg_eq_one (hv : ValueRules) (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) (l : u.Λ) : χ l * χ (-l) = 1 := by
  obtain ⟨i, hi⟩ := exists_chart u hv hL 0
  have hi' : ⊤ ≤ (u.ex (0 + l)).left ⁻¹ᵁ L.U i := by rwa [ex_add_period u 0 l l.2]
  have h1 := h.2.2.2 l i 0 hi
  have h2 := h.2.2.2 (-l) i _ hi'
  rw [h2] at h1
  simp only [zero_add, Submodule.coe_neg, add_neg_cancel, star_neg, Matrix.mulVec_neg,
    dotProduct_neg, neg_dotProduct, neg_neg, zero_dotProduct, mul_zero] at h1
  set b := (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))
  have he : Complex.exp (Real.pi / 2 * b) * Complex.exp (Real.pi * -b + Real.pi / 2 * b) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  refine mul_right_cancel₀ (u.fr_ne i 0 hi) ?_
  linear_combination -h1 - χ l * χ (-l) * u.fr i 0 * he

lemma exists_symmetry_values (hv : ValueRules) (hs : Out.Sym A L) :
    ∃ T : L.ι → L.ι → (Fin g → ℂ) → ℂ,
      (∀ i j, DifferentiableOn ℂ (T i j)
        {z | ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U i ∧ ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j}) ∧
      (∀ i j z, ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j → T i j z ≠ 0) ∧
      (∀ i j i' j' z, ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j →
        ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U i' → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j' →
        T i j z = valAt' (u.ex (-z)).left (L.U i ⊓ L.U i') (L.g i i').val *
          (valAt' (u.ex z).left (L.U j ⊓ L.U j') (L.g j j').val)⁻¹ * T i' j' z) ∧
      ∀ i j z (l : u.Λ), T i j (z + l) = T i j z := by
  obtain ⟨U, hU, t, ht⟩ := hs (default : PrimeSpectrum ℂ)
  have hr : Set.range (𝟙 A.left : A.left ⟶ A.left) ⊆ Set.range (A.hom ⁻¹ᵁ U).ι := by
    intro x _
    rw [Scheme.Opens.range_ι]
    have : A.hom x = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    change A.hom x ∈ U
    rw [this]
    exact hU
  obtain ⟨σ, hσ⟩ : ∃ σ : A.left ⟶ (A.hom ⁻¹ᵁ U).toScheme, σ ≫ (A.hom ⁻¹ᵁ U).ι = 𝟙 _ :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  revert t
  set φ : Fin 2 → ((A.hom ⁻¹ᵁ U).toScheme ⟶ A.left) :=
    ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] with hφ
  intro t ht
  have h0 : ∀ z, ((u.ex z).left ≫ σ) ≫ φ 0 = (u.ex (-z)).left := fun z => by
    simp only [hφ, Matrix.cons_val_zero, Category.assoc, reassoc_of% hσ, ex_neg_left]
  have h1 : ∀ z, ((u.ex z).left ≫ σ) ≫ φ 1 = (u.ex z).left := fun z => by
    simp only [hφ, Matrix.cons_val_one, Matrix.cons_val_zero, Category.assoc, hσ, Category.comp_id]
  have hch : ∀ i j z, ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j →
      ⊤ ≤ ((u.ex z).left ≫ σ) ⁻¹ᵁ L.wchart φ ![i, j] := fun i j z hi hj => by
    refine (le_preimage_wchart ((u.ex z).left ≫ σ) L φ _).2 ?_
    rw [Fin.forall_fin_two]
    exact ⟨(h0 z).symm ▸ hi, (h1 z).symm ▸ hj⟩
  refine ⟨fun i j z => valAt' ((u.ex z).left ≫ σ) (L.wchart φ ![i, j]) (t.s ![i, j]).val,
    fun i j => ?_, fun i j z hi hj => ?_, fun i j i' j' z hi hj hi' hj' => ?_, fun i j z l => ?_⟩
  · have h := (u.hol (σ ⁻¹ᵁ L.wchart φ ![i, j]) ((σ.app _).hom (t.s ![i, j]).val)).2
    refine (h.mono (by exact fun z hz => hch i j z hz.1 hz.2)).congr fun z _ => ?_
    exact ((hv _ (u.ex z).left).2.2.2.1 _ σ _ _).symm
  · exact val_unit_ne_zero _ hv (hch i j z hi hj) _
  · have k1 := hch i j z hi hj
    have k2 := hch i' j' z hi' hj'
    refine (val_gen _ hv t ht _ _ k1 k2).trans ?_
    congr 1
    refine (val_linComb ((u.ex z).left ≫ σ) hv L φ _ _ _ k1 k2).trans ?_
    rw [Fin.prod_univ_two, h0, h1]
    simp
  · simp only [ex_add_period u z l l.2]

lemma neg_eq (hv : ValueRules) (hL : L.IsLB) (hs : Out.Sym A L)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) (l : u.Λ) : χ (-l) = χ l := by
  obtain ⟨T, hTd, hT0, hTc, hTp⟩ := exists_symmetry_values u hv hs
  choose ch hch using exists_chart u hv hL
  let R : L.ι → L.ι → (Fin g → ℂ) → ℂ := fun i j z => T i j z * u.fr j z / u.fr i (-z)
  let r : (Fin g → ℂ) → ℂ := fun z => R (ch (-z)) (ch z) z
  have hrR : ∀ i j z, ⊤ ≤ (u.ex (-z)).left ⁻¹ᵁ L.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j →
      r z = R i j z := fun i j z hi hj => by
    have k1 := (le_preimage_inf _ _ _).2 ⟨hch (-z), hi⟩
    have k2 := (le_preimage_inf _ _ _).2 ⟨hch z, hj⟩
    have n1 := val_unit_ne_zero _ hv k1 (L.g _ _)
    have n2 := val_unit_ne_zero _ hv k2 (L.g _ _)
    have n3 := u.fr_ne i _ hi
    simp only [r, R]
    rw [hTc _ _ i j z (hch _) (hch _) hi hj, u.fr_compat _ _ _ k1, u.fr_compat _ _ _ k2]
    field_simp
  have hopen : ∀ i, IsOpen {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i} := fun i => (u.hol _ 0).1
  have hd : Differentiable ℂ r := fun z => by
    set i := ch (-z)
    set j := ch z
    have ho : IsOpen {w | ⊤ ≤ (u.ex (-w)).left ⁻¹ᵁ L.U i ∧ ⊤ ≤ (u.ex w).left ⁻¹ᵁ L.U j} :=
      ((hopen i).preimage continuous_neg).inter (hopen j)
    have hR : DifferentiableOn ℂ (R i j)
        {w | ⊤ ≤ (u.ex (-w)).left ⁻¹ᵁ L.U i ∧ ⊤ ≤ (u.ex w).left ⁻¹ᵁ L.U j} := by
      simp only [R, div_eq_mul_inv]
      refine ((hTd i j).fun_mul ((u.fr_hol j).mono fun w hw => hw.2)).fun_mul
        (DifferentiableOn.fun_inv ?_ fun w hw => u.fr_ne i _ hw.1)
      exact (u.fr_hol i).comp (f := fun w => -w) (by fun_prop) fun w hw => hw.1
    exact (hR.congr fun w hw => hrR i j w hw.1 hw.2).differentiableAt
      (ho.mem_nhds ⟨hch _, hch _⟩)
  have hne : ∀ z, r z ≠ 0 := fun z =>
    div_ne_zero (mul_ne_zero (hT0 _ _ _ (hch _) (hch _)) (u.fr_ne _ _ (hch _))) (u.fr_ne _ _ (hch _))
  have hχ : ∀ l, χ l ≠ 0 := fun l h0 => by simpa [h0] using h.2.2.1 l
  haveI := u.discrete
  have key := (appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full 0
    (fun l => χ (-l) / χ l) r Matrix.isHermitian_zero
    (fun l => by rw [norm_div, h.2.2.1, h.2.2.1, div_one]) hd hne (fun l z => ?_)).2.1 l
  · exact (div_eq_one_iff_eq (hχ l)).1 key
  have e : -(z + (l : Fin g → ℂ)) = -z + ((-l : u.Λ) : Fin g → ℂ) := by
    rw [Submodule.coe_neg, neg_add]
  have hi : ⊤ ≤ (u.ex (-(z + l))).left ⁻¹ᵁ L.U (ch (-z)) := by
    rw [e, ex_add_period u _ _ (-l).2]; exact hch _
  have hj : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U (ch z) := by
    rw [ex_add_period u _ _ l.2]; exact hch _
  rw [hrR _ _ _ hi hj]
  have n1 := u.fr_ne _ _ hi
  have n2 := hχ l
  have n3 := hχ (-l)
  simp only [r, R]
  rw [hTp, h.2.2.2 l _ z (hch _), h.2.2.2 (-l) _ (-z) (hch _), ← e]
  simp only [hermForm, Matrix.zero_mulVec, dotProduct_zero, mul_zero, add_zero, Complex.exp_zero,
    Submodule.coe_neg, star_neg, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
  have n4 := Complex.exp_ne_zero (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))
  field_simp

end SymmetricSemicharacter


open SymmetricSemicharacter in
theorem semicharacter_sq_eq_one_of_symmetric :
    ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ)
      (χ : u.Λ → ℂ), u.IsAH Hm χ → ∀ l, χ l ^ 2 = 1 := by
  intro P u Hm χ h l
  have h1 := mul_neg_eq_one u valueRules P.isLB h l
  rwa [neg_eq u valueRules P.isLB P.sym h l, ← sq] at h1

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeSurjectiveOfOntoComplexPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.OntoSurj

theorem surjective_of_points {R K : Type} [CommRing R] [Field K] [IsAlgClosed K] (σ : R →+* K)
    (hσ : Function.Injective σ) {P A : Scheme.{0}} (a : A ⟶ Sp R) [LocallyOfFiniteType a]
    (ha : IsOpenMap a) (ψ : P ⟶ A) (hψ : IsClosed (Set.range ψ))
    (h : ∀ x : Sp K ⟶ A, x ≫ a = spMap σ → ∃ p : Sp K ⟶ P, x = p ≫ ψ) : Surjective ψ := by
  have hd : Dense (Set.range (spMap σ)) := by
    have : DenseRange (PrimeSpectrum.comap σ) := by
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
        (RingHom.injective_iff_ker_eq_bot σ).mp hσ]
      exact bot_le
    exact this
  have hJ : JacobsonSpace ↥(pullback a (spMap σ)) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd a (spMap σ))
  have hZ : IsClosed ((pullback.fst a (spMap σ)) ⁻¹' Set.range ψ) :=
    hψ.preimage (pullback.fst a (spMap σ)).continuous
  have hsub : closedPoints ↥(pullback a (spMap σ)) ⊆
      (pullback.fst a (spMap σ)) ⁻¹' Set.range ψ := by
    intro z hz
    replace hz : IsClosed {z} := hz
    obtain ⟨p, hp⟩ := h (pointOfClosedPoint (pullback.snd a (spMap σ)) z hz ≫ pullback.fst _ _)
      (by rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc])
    obtain ⟨w⟩ : Nonempty ↥(Sp K) := inferInstance
    refine ⟨p w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hp, Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
  have hall := closure_minimal hsub hZ
  rw [closure_closedPoints] at hall
  have hsub' : a ⁻¹' Set.range (spMap σ) ⊆ Set.range ψ := by
    rw [← Scheme.Pullback.range_fst]
    rintro _ ⟨z, rfl⟩
    exact hall (Set.mem_univ z)
  have hall' := closure_minimal hsub' hψ
  rw [(hd.preimage ha).closure_eq] at hall'
  exact ⟨fun y ↦ hall' (Set.mem_univ y)⟩

theorem surjective_of_onto_complex_points :
    ∀ (R : Type) [CommRing R] [IsDomain R] (σ : R →+* ℂ), Function.Injective σ → ∀ (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (Φ : B ⟶ A), IsAbelianScheme A → IsAbelianScheme B → (∀ y : Over.mk (spMap σ) ⟶ A, ∃ x : Over.mk (spMap σ) ⟶ B, y = x ≫ Φ) → Surjective Φ.left ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (y : Over.mk t ⟶ A), ∃ x : Over.mk t ⟶ B, y = x ≫ Φ := by
  intro R _ _ σ hσ A B _ _ Φ hA hB h
  have := hB.proper
  have := hA.proper
  have := hA.smooth
  have hpr : IsProper Φ.left := by
    have : IsProper (Φ.left ≫ A.hom) := by rwa [Over.w]
    exact IsProper.of_comp Φ.left A.hom
  have hs : Surjective Φ.left := by
    refine surjective_of_points σ hσ A.hom A.hom.isOpenMap Φ.left
      Φ.left.isClosedMap.isClosed_range fun y hy ↦ ?_
    obtain ⟨p, hp⟩ := h (Over.homMk y hy)
    exact ⟨p.left, congrArg (·.left) hp⟩
  refine ⟨hs, fun k _ _ t y ↦ ?_⟩
  obtain ⟨p, hp⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective Φ.left y.left
  refine ⟨Over.homMk p ?_, Over.OverMorphism.ext hp⟩
  rw [← Over.w Φ, ← Category.assoc, ← hp]
  exact Over.w y

end GlobalTheory.OntoSurj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPrincipalDimOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory


open PureTypeVector in
theorem hermForm_principal_dim_one :
  ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (w : Fin g → ℂ) (L : PeriodPair) (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ), g = 1 → w ≠ 0 → (∀ z : ℂ, z ∈ L.lattice ↔ z • w ∈ Λ) → Hm.IsHermitian → 0 < (hermForm Hm w w).re → (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) → Function.Bijective Ef → ∀ z z' : ℂ, hermForm Hm (z • w) (z' • w) = z * starRingEnd ℂ z' / (|(L.ω₁ * starRingEnd ℂ L.ω₂).im| : ℝ) := by
  intro g Λ w L Hm Ef hg hw hΛ hH hpos hEf hbij z z'
  subst hg
  set H := hermForm Hm w w with hHdef
  have hHim : H.im = 0 := hermForm_self_im hH w
  have hHreal : H = (H.re : ℂ) := Complex.ext (by simp) (by simp [hHim])
  have hsm : ∀ u v : ℂ, hermForm Hm (u • w) (v • w) = u * starRingEnd ℂ v * H :=
    fun u v => hermForm_smul_smul Hm u v w w
  set D := (L.ω₁ * starRingEnd ℂ L.ω₂).im with hD
  have hw0 : w 0 ≠ 0 := by
    intro h
    apply hw
    funext i
    rw [Subsingleton.elim i 0]
    simpa using h
  have hcoord : ∀ x : Λ, ∃ m n : ℤ, (x : Fin 1 → ℂ) = ((m : ℂ) * L.ω₁ + n * L.ω₂) • w := by
    intro x
    have hx : (x : Fin 1 → ℂ) = (x.1 0 / w 0) • w := by
      funext i
      rw [Subsingleton.elim i 0]
      simp [div_mul_cancel₀ _ hw0]
    have hmem : (x.1 0 / w 0) ∈ L.lattice := (hΛ _).2 (by rw [← hx]; exact x.2)
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.1 hmem
    exact ⟨m, n, by rw [hmn]; exact hx⟩
  have him : ∀ m n m' n' : ℤ,
      (((m : ℂ) * L.ω₁ + n * L.ω₂) * starRingEnd ℂ ((m' : ℂ) * L.ω₁ + n' * L.ω₂)).im
        = ((m * n' - n * m' : ℤ) : ℝ) * D := by
    intro m n m' n'
    simp only [hD, map_add (f := _), map_mul, map_intCast, Complex.mul_im, Complex.add_im, Complex.add_re,
      Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.intCast_re, Complex.intCast_im]
    push_cast
    ring
  have hEfc : ∀ (x y : Λ) (m n m' n' : ℤ),
      (x : Fin 1 → ℂ) = ((m : ℂ) * L.ω₁ + n * L.ω₂) • w →
      (y : Fin 1 → ℂ) = ((m' : ℂ) * L.ω₁ + n' * L.ω₂) • w →
      (Ef x y : ℝ) = ((m * n' - n * m' : ℤ) : ℝ) * (H.re * D) := by
    intro x y m n m' n' hx hy
    rw [hEf, hx, hy, hsm, Complex.mul_im, hHim, him]
    ring
  have ha : L.ω₁ • w ∈ Λ := (hΛ _).1 L.ω₁_mem_lattice
  have hb : L.ω₂ • w ∈ Λ := (hΛ _).1 L.ω₂_mem_lattice
  let a : Λ := ⟨L.ω₁ • w, ha⟩
  let b : Λ := ⟨L.ω₂ • w, hb⟩
  have ea : (a : Fin 1 → ℂ) = (((1 : ℤ) : ℂ) * L.ω₁ + ((0 : ℤ) : ℂ) * L.ω₂) • w := by
    show L.ω₁ • w = _
    simp
  have eb : (b : Fin 1 → ℂ) = (((0 : ℤ) : ℂ) * L.ω₁ + ((1 : ℤ) : ℂ) * L.ω₂) • w := by
    show L.ω₂ • w = _
    simp
  set k := Ef a b with hkdef
  have hk : (k : ℝ) = H.re * D := by
    rw [hEfc a b 1 0 0 1 ea eb]
    norm_num
  have hdvd : ∀ x y : Λ, k ∣ Ef x y := by
    intro x y
    obtain ⟨m, n, hx⟩ := hcoord x
    obtain ⟨m', n', hy⟩ := hcoord y
    refine ⟨m * n' - n * m', ?_⟩
    have h := hEfc x y m n m' n' hx hy
    rw [← hk, mul_comm] at h
    exact_mod_cast h
  have hba : Ef b a = -k := by
    have h := hEfc b a 0 1 1 0 eb ea
    rw [← hk] at h
    have h' : ((Ef b a : ℤ) : ℝ) = ((-k : ℤ) : ℝ) := by
      rw [h]
      push_cast
      ring
    exact_mod_cast h'
  have hk0 : k ≠ 0 := by
    intro hk0
    have hEa : Ef a = Ef 0 := by
      apply LinearMap.ext
      intro y
      rw [map_zero, LinearMap.zero_apply]
      obtain ⟨c, hc⟩ := hdvd a y
      rw [hc, hk0, zero_mul]
    have ha0 : a = 0 := hbij.1 hEa
    have h0 : L.ω₁ • w = 0 := congrArg Subtype.val ha0
    rcases smul_eq_zero.1 h0 with h | h
    · exact L.indep.ne_zero 0 (by simpa using h)
    · exact hw h
  let f : Λ →ₗ[ℤ] ℤ :=
    { toFun := fun y => Ef y a / k
      map_add' := fun y y' => by
        simp only [map_add (f := _), LinearMap.add_apply]
        exact Int.add_ediv_of_dvd_left (hdvd y a)
      map_smul' := fun c y => by
        simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (hdvd y a) }
  obtain ⟨x, hx⟩ := hbij.2 f
  have hxb : Ef x b = -1 := by
    rw [hx]
    show Ef b a / k = -1
    rw [hba, Int.neg_ediv_of_dvd (dvd_refl k), Int.ediv_self hk0]
  have hunit : k = 1 ∨ k = -1 := by
    have h := hdvd x b
    rw [hxb] at h
    exact Int.isUnit_iff.1 (isUnit_of_dvd_one (dvd_neg.1 h))
  have hHre : H.re * |D| = 1 := by
    have hpos' : 0 < H.re := hpos
    rcases hunit with h | h
    · have h1 : H.re * D = 1 := by rw [← hk, h]; norm_num
      have hD0 : 0 < D := by nlinarith
      rw [abs_of_pos hD0]
      exact h1
    · have h1 : H.re * D = -1 := by rw [← hk, h]; norm_num
      have hD0 : D < 0 := by nlinarith
      rw [abs_of_neg hD0]
      linarith
  have hDabs : |D| ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hHre
    exact zero_ne_one hHre
  have hr : H.re = 1 / |D| := by
    rw [eq_div_iff hDabs]
    exact hHre
  rw [hsm, hHreal, hr, Complex.ofReal_div, Complex.ofReal_one]
  ring

end GlobalTheory
end
