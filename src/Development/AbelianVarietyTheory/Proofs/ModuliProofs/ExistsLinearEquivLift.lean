module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueRealLinearOfEventuallyAddModDiscrete
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology

namespace GlobalTheory.LocLift

noncomputable section

section Hol

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {X Y : Scheme.{0}}

theorem isHolTo_comp_hom {B : Set V} {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (φ : X ⟶ Y) :
    IsHolTo B (fun b => y b ≫ φ) := by
  intro U f
  have := h (φ ⁻¹ᵁ U) ((φ.app U).hom f)
  simpa only [valAt'_comp, ← top_le_preimage_comp] using this

theorem isHolTo_comp {B : Set V} {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) {C : Set W} (hC : IsOpen C) {β : W → V}
    (hβ : DifferentiableOn ℂ β C) (hm : Set.MapsTo β C B) : IsHolTo C (fun w => y (β w)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  refine ⟨?_, h2.comp (hβ.mono fun w hw => hw.1) fun w hw => ⟨hm hw.1, hw.2⟩⟩
  have := hβ.continuousOn.isOpen_inter_preimage hC h1
  convert this using 1
  ext w
  exact ⟨fun hw => ⟨hw.1, hm hw.1, hw.2⟩, fun hw => ⟨hw.1, hw.2.2⟩⟩

theorem isHolTo_congr {B : Set V} {y y' : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (e : ∀ b ∈ B, y' b = y b) :
    IsHolTo B y' := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have : {b ∈ B | ⊤ ≤ y' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext b
    exact and_congr_right fun hb => by rw [e b hb]
  rw [this]
  exact ⟨h1, h2.congr fun b hb => by rw [e b hb.1]⟩

theorem isHolTo_mono {B C : Set V} {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (hC : IsOpen C) (hCB : C ⊆ B) :
    IsHolTo C y :=
  isHolTo_comp (β := id) h hC differentiableOn_id hCB

end Hol

section Grp

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Q : Type} [Group Q]

theorem hom_zero {A : Type} [AddGroup A] {e : A → Q} (h : ∀ z w, e (z + w) = e z * e w) : e 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem hom_sub_eq_one {A : Type} [AddGroup A] {e : A → Q} (h : ∀ z w, e (z + w) = e z * e w) {z w : A} :
    e (z - w) = 1 ↔ e z = e w := by
  have := h (z - w) w
  rw [sub_add_cancel] at this
  rw [this, mul_eq_right]

theorem hom_nsmul {A : Type} [AddGroup A] {e : A → Q} (h : ∀ z w, e (z + w) = e z * e w) (z : A) (n : ℕ) :
    e (n • z) = e z ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, hom_zero h]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

def homKer {A : Type} [AddGroup A] {e : A → Q} (h : ∀ z w, e (z + w) = e z * e w) : AddSubgroup A :=
  (AddMonoidHom.mk' (G := Additive Q) (fun z => Additive.ofMul (e z)) fun z w => congrArg _ (h z w)).ker

theorem mem_homKer {A : Type} [AddGroup A] {e : A → Q} (h : ∀ z w, e (z + w) = e z * e w) {z : A} :
    z ∈ homKer h ↔ e z = 1 := Iff.rfl

theorem isDiscrete_of_norm {K : AddSubgroup W} {r : ℝ} (hr : 0 < r) (h : ∀ z ∈ K, ‖z‖ < r → z = 0) :
    IsDiscrete (K : Set W) := by
  have : DiscreteTopology K := DiscreteTopology.of_forall_le_norm (E := K) hr fun x hx =>
    not_lt.1 fun h' => hx (Subtype.ext (h x x.2 h'))
  exact DiscreteTopology.isDiscrete

theorem linear_lift_unique {e : W → Q} (h : ∀ z w, e (z + w) = e z * e w) {r : ℝ} (hr : 0 < r)
    (hk : ∀ z, ‖z‖ < r → e z = 1 → z = 0) {L L' : V →ₗ[ℂ] W} (hL : ∀ z, e (L z) = e (L' z)) : L = L' := by
  have := realLinear_eq_of_sub_mem_discrete (Γ := homKer h) (isDiscrete_of_norm hr fun z hz hn => hk z hn hz)
    (L := L.restrictScalars ℝ) (L' := L'.restrictScalars ℝ) fun x => (hom_sub_eq_one h).2 (hL x)
  ext z
  exact DFunLike.congr_fun this z

theorem fderiv_lift {x : V → Q} {e : W → Q} (hx : ∀ z w, x (z + w) = x z * x w) (h : ∀ z w, e (z + w) = e z * e w)
    (hs : Function.Surjective e) {r : ℝ} (hr : 0 < r) (hk : ∀ z, ‖z‖ < r → e z = 1 → z = 0) {ζ : V → W}
    (hd : DifferentiableAt ℂ ζ 0) (hζ : ∀ᶠ z in 𝓝 0, e (ζ z) = x z) (z : V) : e (fderiv ℂ ζ 0 z) = x z := by
  letI : CommGroup Q := { (inferInstance : Group Q) with
    mul_comm := fun a b => by
      obtain ⟨a, rfl⟩ := hs a
      obtain ⟨b, rfl⟩ := hs b
      rw [← h, ← h, add_comm] }
  exact apply_fderiv_eq_of_germ (𝕜 := ℂ) (A := Additive Q)
    (ex := AddMonoidHom.mk' (fun z => Additive.ofMul (x z)) fun z w => congrArg _ (hx z w))
    (ex' := AddMonoidHom.mk' (fun z => Additive.ofMul (e z)) fun z w => congrArg _ (h z w))
    (isDiscrete_of_norm hr fun z hz hn => hk z hn hz) hd hζ z

theorem exists_linearEquiv_lift [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {x : V → Q} {e : W → Q}
    (hx : ∀ z w, x (z + w) = x z * x w) (h : ∀ z w, e (z + w) = e z * e w) (hsx : Function.Surjective x)
    (hs : Function.Surjective e) (hkx : IsDiscrete {z | x z = 1})
    {r : ℝ} (hr : 0 < r) (hk : ∀ z, ‖z‖ < r → e z = 1 → z = 0) {ζ : V → W}
    (hd : DifferentiableAt ℂ ζ 0) (hζ : ∀ᶠ z in 𝓝 0, e (ζ z) = x z) : ∃ L : V ≃L[ℂ] W, ∀ z, e (L z) = x z := by
  letI : CommGroup Q := { (inferInstance : Group Q) with
    mul_comm := fun a b => by
      obtain ⟨a, rfl⟩ := hs a
      obtain ⟨b, rfl⟩ := hs b
      rw [← h, ← h, add_comm] }
  obtain ⟨L, hL, -⟩ := existsUnique_linearEquiv_of_uniformisations (𝕜 := ℂ) (A := Additive Q)
    (ex := AddMonoidHom.mk' (fun z => Additive.ofMul (x z)) fun z w => congrArg _ (hx z w))
    (ex' := AddMonoidHom.mk' (fun z => Additive.ofMul (e z)) fun z w => congrArg _ (h z w))
    hkx (isDiscrete_of_norm hr fun z hz hn => hk z hn hz) (fun q _ => hsx q) hd hζ
  exact ⟨L, hL.1⟩

theorem eq_zero_of_small {T : Type} [TopologicalSpace T] {B : Set T} (hB : IsPreconnected B) {d : T → W}
    (hd : ContinuousOn d B) {r : ℝ} (hr : 0 < r) (h : ∀ b ∈ B, ‖d b‖ < r → d b = 0) {b₀ : T} (hb₀ : b₀ ∈ B)
    (h0 : d b₀ = 0) : ∀ b ∈ B, d b = 0 := by
  intro b hb
  refine h b hb (not_le.1 fun hle => ?_)
  obtain ⟨c, hc, hc'⟩ := hB.intermediate_value hb₀ hb hd.norm
    (show r / 2 ∈ Set.Icc ‖d b₀‖ ‖d b‖ from ⟨by rw [h0, norm_zero]; positivity, by linarith⟩)
  have hc'' : ‖d c‖ = r / 2 := hc'
  have := h c hc (by linarith)
  rw [this, norm_zero] at hc''
  linarith

end Grp

section Exp

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}

def IsExp (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) : Prop :=
  (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)

def HasLifts (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X))
    (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) : Prop :=
  ∀ (n : ℕ) (W : Set (Fin n → ℂ)) (β : (Fin n → ℂ) → (Fin m → ℂ)) (x : ∀ w, Over.mk (y (β w)) ⟶ G)
    (w₀ : Fin n → ℂ) (z₀ : Fin g → ℂ), IsOpen W → w₀ ∈ W → DifferentiableOn ℂ β W → Set.MapsTo β W B →
    IsHolTo W (fun w => (x w).left) → e (β w₀) z₀ = x w₀ →
    ∃ ζ : (Fin n → ℂ) → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w

omit [GrpObj G] in
theorem HasLifts.lift {B : Set (Fin m → ℂ)} {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)}
    {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} (h : HasLifts B y e) {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] {W : Set V} {β : V → (Fin m → ℂ)} (x : ∀ w, Over.mk (y (β w)) ⟶ G)
    {w₀ : V} {z₀ : Fin g → ℂ} (hW : IsOpen W) (hw₀ : w₀ ∈ W) (hβ : DifferentiableOn ℂ β W)
    (hm : Set.MapsTo β W B) (hx : IsHolTo W (fun w => (x w).left)) (h0 : e (β w₀) z₀ = x w₀) :
    ∃ ζ : V → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w := by
  let φ : V ≃L[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨u₀, rfl⟩ := φ.symm.surjective w₀
  have hW' : IsOpen (φ.symm ⁻¹' W) := hW.preimage φ.symm.continuous
  obtain ⟨ζ, h1, h2, h3⟩ := h _ (φ.symm ⁻¹' W) (fun u => β (φ.symm u)) (fun u => x (φ.symm u)) u₀ z₀ hW' hw₀
    (hβ.comp φ.symm.differentiableOn fun _ hu => hu) (fun _ hu => hm hu)
    (isHolTo_comp hx hW' φ.symm.differentiableOn fun _ hu => hu) h0
  refine ⟨fun w => ζ (φ w), by simpa using h1, ?_, ?_⟩
  · exact AnalyticAt.comp_of_eq h2 (φ.toContinuousLinearMap.analyticAt (φ.symm u₀)) (by simp)
  · have ht : map φ.symm (𝓝 u₀) = 𝓝 (φ.symm u₀) := φ.symm.toHomeomorph.map_nhds_eq u₀
    rw [← ht, eventually_map]
    simpa only [φ.apply_symm_apply] using h3

theorem isDerivAt0_comp {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (h : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) (w : Fin g → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 (fun z => e (h z)) w v ↔ IsDerivAt0 e (h w) v := by
  have key : ∀ (U : X.Opens) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (h z)) U f) 0 w =
      fderiv ℂ (fun z => valAt' (e z) U f) 0 (h w) := fun U f => by
    have := h.comp_right_fderiv (f := fun z => valAt' (e z) U f) (x := 0)
    rw [map_zero] at this
    exact DFunLike.congr_fun this w
  simp only [IsDerivAt0, key, map_zero]

theorem IsExp.comp {y : Sp ℂ ⟶ X} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : IsExp y e)
    (h : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) : IsExp y (fun z => e (h z)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := he
  refine ⟨fun z w => by simp only [map_add (f := _), h1], h2.comp h.surjective,
    isHolTo_comp h3 isOpen_univ h.differentiableOn (Set.mapsTo_univ _ _), fun w => ?_, fun v hv => ?_⟩
  · simpa only [isDerivAt0_comp (e := fun z => (e z).left)] using h4 (h w)
  · simp only [isDerivAt0_comp (e := fun z => (e z).left)]
    obtain ⟨w, hw, hu⟩ := h5 v (by simpa only [map_zero] using hv)
    exact ⟨h.symm w, by simpa using hw, fun w' hw' => by rw [← hu _ hw', h.symm_apply_apply]⟩

theorem one_left (y : Sp ℂ ⟶ X) : (1 : Over.mk y ⟶ G).left = y ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl

theorem eq_one_of_mem_range [IsSeparated G.hom] {y : Sp ℂ ⟶ X} (x : Over.mk y ⟶ G)
    (hx : x.left (default : PrimeSpectrum ℂ) ∈ Set.range η[G].left) : x = 1 := by
  have hw : η[G].left ≫ G.hom = 𝟙 _ := Over.w η[G]
  haveI : IsClosedImmersion (η[G].left ≫ G.hom) := hw ▸ inferInstance
  haveI : IsClosedImmersion η[G].left := IsClosedImmersion.of_comp _ G.hom
  haveI : IsReduced (Over.mk y).left := inferInstanceAs (IsReduced (Sp ℂ))
  haveI : Surjective (pullback.fst x.left η[G].left) := ⟨fun p => by
    have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    subst this
    change _ ∈ Set.range _
    rw [Scheme.Pullback.range_fst]
    exact hx⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.fst x.left η[G].left)
  have e : x.left = (inv (pullback.fst x.left η[G].left) ≫ pullback.snd _ _) ≫ η[G].left := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  have e' : inv (pullback.fst x.left η[G].left) ≫ pullback.snd _ _ = y := by
    have := Over.w x
    rw [e, Category.assoc, hw] at this
    exact (Category.comp_id _).symm.trans this
  rw [e'] at e
  exact Over.OverMorphism.ext (e.trans (one_left y).symm)

theorem isOpen_ne_one [IsSeparated G.hom] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V}
    {y : V → (Sp ℂ ⟶ X)} {x : ∀ b, Over.mk (y b) ⟶ G} (hx : IsHolTo B (fun b => (x b).left)) :
    IsOpen {b ∈ B | x b ≠ 1} := by
  have hw : η[G].left ≫ G.hom = 𝟙 _ := Over.w η[G]
  haveI : IsClosedImmersion (η[G].left ≫ G.hom) := hw ▸ inferInstance
  haveI : IsClosedImmersion η[G].left := IsClosedImmersion.of_comp _ G.hom
  let U : G.left.Opens := ⟨(Set.range η[G].left)ᶜ, η[G].left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  convert (hx U 0).1 using 3 with b
  refine and_congr_right fun _ => ?_
  rw [top_le_preimage_iff_mem]
  refine not_congr ⟨fun h => ?_, eq_one_of_mem_range _⟩
  beta_reduce
  rw [h, one_left]
  exact ⟨y b (default : PrimeSpectrum ℂ), rfl⟩

end Exp

end

end GlobalTheory.LocLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.SimLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

theorem ext_form {x y : D.La} (h : ∀ b, D.EF x b = D.EF y b) : x = y :=
  D.unimod.1 (LinearMap.ext h)

theorem form_skew (x y : D.La) : D.EF x y = -D.EF y x := by
  have h := D.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, D.alt] at h
  linarith

theorem exists_vec (φ : D.La → ℤ) (hφ : ∀ a b, φ (a + b) = φ a + φ b) : ∃ x, ∀ b, D.EF x b = φ b := by
  obtain ⟨x, hx⟩ := D.unimod.2 (AddMonoidHom.mk' φ hφ).toIntLinearMap
  exact ⟨x, fun b => by rw [hx]; rfl⟩

theorem exists_rep (B : D.La → D.La → ℤ) (h1 : ∀ a a' b, B (a + a') b = B a b + B a' b)
    (h2 : ∀ a b b', B a (b + b') = B a b + B a b')
    (h3 : ∀ (c : 𝓞 E) a b, B (c • a) b = B a (H.bar c • b)) :
    ∃ u : D.La →ₗ[𝓞 E] D.La, ∀ a b, D.EF (u a) b = B a b := by
  choose u hu using fun a => exists_vec D (B a) (h2 a)
  refine ⟨⟨⟨u, fun a a' => ext_form D fun b => ?_⟩, fun c a => ext_form D fun b => ?_⟩, hu⟩
  · rw [map_add (f := _), LinearMap.add_apply, hu, hu, hu, h1]
  · simp only [RingHom.id_apply]
    rw [D.adj, hu, hu, h3]

theorem modN_of_dvd {n : ℕ} (hn : 0 < n) {x : D.La} (h : ∀ b, (n : ℤ) ∣ D.EF x b) : D.ModN n x := by
  choose φ hφ using h
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨y, hy⟩ := exists_vec D φ fun a b => by
    apply mul_left_cancel₀ hn'
    rw [← hφ, map_add (f := _), hφ, hφ, mul_add]
  refine ⟨y, ext_form D fun b => ?_⟩
  rw [map_nsmul, LinearMap.smul_apply, hy, hφ, nsmul_eq_mul]

theorem modN_of_dvd_modulus {n m : ℕ} (h : n ∣ m) {x : D.La} (hx : D.ModN m x) : D.ModN n x := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨b, rfl⟩ := hx
  exact ⟨k • b, mul_smul _ _ _⟩

theorem modN_trans {n : ℕ} {x y z : D.La} (h1 : D.ModN n (x - y)) (h2 : D.ModN n (y - z)) :
    D.ModN n (x - z) := by
  obtain ⟨b, hb⟩ := h1
  obtain ⟨c, hc⟩ := h2
  exact ⟨b + c, by rw [smul_add, ← hb, ← hc]; abel⟩

def IsSimMod (n : ℕ) (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ) : Prop :=
  IsCoprime ν (n : ℤ) ∧ ∀ a b, (n : ℤ) ∣ D.EF (f a) (f b) - ν * D.EF a b

theorem IsSimMod.of_dvd {n m : ℕ} (h : n ∣ m) {f : D.La →ₗ[𝓞 E] D.La} {ν : ℤ} (hf : IsSimMod D m f ν) :
    IsSimMod D n f ν :=
  have h' : (n : ℤ) ∣ m := Int.natCast_dvd_natCast.mpr h
  ⟨hf.1.of_isCoprime_of_dvd_right h', fun a b => h'.trans (hf.2 a b)⟩

theorem step_sq {n : ℕ} (hn : 0 < n) {f : D.La →ₗ[𝓞 E] D.La} {ν : ℤ} (hf : IsSimMod D n f ν) :
    ∃ f', IsSimMod D (n * n) f' ν ∧ ∀ a, D.ModN n (f' a - f a) := by
  obtain ⟨hc, hB⟩ := hf
  have hc2 : IsCoprime ν ((n * n : ℕ) : ℤ) := by
    push_cast; exact hc.mul_right hc
  obtain ⟨κ, t, hκ⟩ := hc
  choose B hB using hB
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨u, hu⟩ := exists_rep D B
    (fun a a' b => by
      apply mul_left_cancel₀ hn'
      rw [mul_add, ← hB, ← hB, ← hB]
      simp only [map_add (f := _), LinearMap.add_apply]; ring)
    (fun a b b' => by
      apply mul_left_cancel₀ hn'
      rw [mul_add, ← hB, ← hB, ← hB]
      simp only [map_add (f := _)]; ring)
    (fun c a b => by
      apply mul_left_cancel₀ hn'
      rw [← hB, ← hB, f.map_smul, f.map_smul, D.adj, D.adj])
  have hskew : ∀ a b, B a b = -B b a := fun a b => by
    apply mul_left_cancel₀ hn'
    rw [mul_neg, ← hB, ← hB, form_skew D (f a), form_skew D a]; ring
  have hsa : ∀ a b, D.EF a (u b) = D.EF (u a) b := fun a b => by
    rw [form_skew D a, hu, hu, hskew a b]
  set v : D.La →ₗ[𝓞 E] D.La := H.w0 • u with hv
  have hkey : ∀ a b, D.EF (v a) b + D.EF a (v b) = B a b := fun a b => by
    have h1 : D.EF a (v b) = D.EF ((1 - H.w0) • u a) b := by
      have hb : H.bar (1 - H.w0) = H.w0 := by
        rw [map_sub, map_one, HostModel.cmHost_bar_halfIntegerGenerator]; ring
      rw [← u.map_smul, ← hsa, D.adj, hb, hv, LinearMap.smul_apply]
    rw [h1, ← LinearMap.add_apply, ← map_add (f := _), hv, LinearMap.smul_apply, ← add_smul, ← hu]
    simp
  have hff : ∀ a b, D.EF (f a) (f b) = ν * D.EF a b + n * B a b := fun a b => by
    rw [← hB]; ring
  refine ⟨f - ((n : ℤ) * κ) • (f ∘ₗ v), ⟨hc2, fun a b => ?_⟩, fun a => ⟨-(κ • f (v a)), ?_⟩⟩
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sub, map_zsmul,
      smul_eq_mul, hff]
    refine ⟨t * B a b - κ * (B (v a) b + B a (v b)) +
      κ * κ * (ν * D.EF (v a) (v b) + n * B (v a) (v b)), ?_⟩
    push_cast
    linear_combination (-(n : ℤ) * κ * ν) * hkey a b - (n : ℤ) * B a b * hκ
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [mul_smul, natCast_zsmul, smul_neg]; abel

theorem step_coprime {n r : ℕ} (hnr : IsCoprime (n : ℤ) (r : ℤ)) {f : D.La →ₗ[𝓞 E] D.La} {ν : ℤ}
    (hf : IsSimMod D n f ν) :
    ∃ f' ν', IsSimMod D (n * r) f' ν' ∧ (∀ a, D.ModN n (f' a - f a)) ∧ (n : ℤ) ∣ ν' - ν := by
  obtain ⟨x, y, hxy⟩ := hnr
  obtain ⟨hc, hB⟩ := hf
  refine ⟨(y * r) • f + (x * n) • LinearMap.id, y * r * ν + x * n, ⟨?_, fun a b => ?_⟩,
    fun a => ⟨x • (a - f a), ?_⟩, ⟨x * (1 - ν), by linear_combination ν * hxy⟩⟩
  · push_cast
    refine IsCoprime.mul_right ?_ ?_
    · obtain ⟨κ, t, hκ⟩ := hc
      exact ⟨κ, t - κ * x * (1 - ν), by linear_combination hκ + κ * ν * hxy⟩
    · exact ⟨1, y * (1 - ν), by linear_combination hxy⟩
  · obtain ⟨B, hB⟩ := hB a b
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, map_add (f := _), map_zsmul,
      smul_eq_mul]
    refine ⟨y * B + x * y * (D.EF (f a) b + D.EF a (f b) - D.EF (f a) (f b) - D.EF a b), ?_⟩
    push_cast
    linear_combination (y * r) * hB + (y * r * D.EF (f a) (f b) + x * n * D.EF a b) * hxy
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have h : y * (r : ℤ) = 1 - n * x := by linear_combination hxy
    rw [h, ← natCast_zsmul, ← mul_smul, _root_.mul_comm x, sub_smul, smul_sub, one_smul]; abel

theorem step (m : ℕ) : 0 < m → ∀ (n : ℕ), 0 < n → ∀ (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ), IsSimMod D n f ν →
    ∃ f' ν', IsSimMod D (n * m) f' ν' ∧ (∀ a, D.ModN n (f' a - f a)) ∧ (n : ℤ) ∣ ν' - ν := by
  induction m using induction_on_primes with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ n _ f ν hf
    exact ⟨f, ν, by simpa using hf, fun a => ⟨0, by simp⟩, by simp⟩
  | prime_mul p a hp ih =>
    intro hpa n hn f ν hf
    have ha : 0 < a := Nat.pos_of_mul_pos_left hpa
    have h1 : ∃ f' ν', IsSimMod D (n * p) f' ν' ∧ (∀ a, D.ModN n (f' a - f a)) ∧ (n : ℤ) ∣ ν' - ν := by
      by_cases hpn : p ∣ n
      · obtain ⟨f', h1, h2⟩ := step_sq D hn hf
        exact ⟨f', ν, h1.of_dvd D (Nat.mul_dvd_mul_left n hpn), h2, by simp⟩
      · exact step_coprime D
          (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm) hf
    obtain ⟨f₁, ν₁, h1, h2, h3⟩ := h1
    obtain ⟨f₂, ν₂, h4, h5, h6⟩ := ih ha (n * p) (Nat.mul_pos hn hp.pos) f₁ ν₁ h1
    refine ⟨f₂, ν₂, by rwa [← Nat.mul_assoc], fun x =>
      modN_trans D (modN_of_dvd_modulus D (dvd_mul_right n p) (h5 x)) (h2 x), ?_⟩
    have h7 : (n : ℤ) ∣ ν₂ - ν₁ := (Int.natCast_dvd_natCast.mpr (dvd_mul_right n p)).trans h6
    simpa using dvd_add h7 h3

theorem exists_inv {n : ℕ} (hn : 0 < n) {f : D.La →ₗ[𝓞 E] D.La} {ν : ℤ} (hf : IsSimMod D n f ν) :
    ∃ g : D.La →ₗ[𝓞 E] D.La, ∀ a, D.ModN n (g (f a) - a) ∧ D.ModN n (f (g a) - a) := by
  obtain ⟨⟨κ, t, hκ⟩, hB⟩ := hf
  obtain ⟨u, hu⟩ := exists_rep D (fun a b => D.EF a (f b)) (fun a a' b => by simp)
    (fun a b b' => by simp) (fun c a b => by rw [f.map_smul, D.adj])
  set g : D.La →ₗ[𝓞 E] D.La := κ • u with hg
  have h1 : ∀ a, D.ModN n (g (f a) - a) := fun a => modN_of_dvd D hn fun b => by
    obtain ⟨B, hB⟩ := hB a b
    simp only [hg, LinearMap.smul_apply, map_sub, map_zsmul, LinearMap.sub_apply, smul_eq_mul, hu]
    exact ⟨κ * B - t * D.EF a b, by linear_combination κ * hB + D.EF a b * hκ⟩
  let S : Submodule (𝓞 E) D.La := LinearMap.range (n • (LinearMap.id : D.La →ₗ[𝓞 E] D.La))
  have hS : ∀ x, x ∈ S ↔ D.ModN n x := fun x =>
    ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  have hgS : S ≤ S.comap g := by
    rintro x hx
    obtain ⟨b, rfl⟩ := (hS x).mp hx
    exact (hS _).mpr ⟨g b, map_nsmul g n b⟩
  have := D.fin
  have hsurj : Function.Surjective (S.mapQ S g hgS) := by
    intro q
    obtain ⟨a, rfl⟩ := S.mkQ_surjective q
    exact ⟨S.mkQ (f a), (Submodule.Quotient.eq S).mpr ((hS _).mpr (h1 a))⟩
  have hinj := OrzechProperty.injective_of_surjective_endomorphism _ hsurj
  refine ⟨g, fun a => ⟨h1 a, (hS _).mp ((Submodule.Quotient.eq S).mp (hinj ?_))⟩⟩
  exact (Submodule.Quotient.eq S).mpr ((hS _).mpr (h1 (g a)))

end GlobalTheory.SimLift

namespace GlobalTheory

open SimLift

theorem exists_sim_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (N : ℕ)
    (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) →
    (∀ a b, (N : ℤ) ∣ D.EF (f a) (f b) - ν * D.EF a b) →
    ∃ g : Sim D, (∀ a, D.ModN N (g.f N a - f a)) ∧ (N : ℤ) ∣ g.ν N - ν := by
  intro E _ _ _ H D N f ν hN hc hf
  let T : ℕ → Type := fun k =>
    {x : (D.La →ₗ[𝓞 E] D.La) × ℤ // IsSimMod D (N * k.factorial) x.1 x.2}
  have hstep : ∀ k (x : T k), ∃ y : T (k + 1),
      (∀ a, D.ModN (N * k.factorial) (y.1.1 a - x.1.1 a)) ∧ ((N * k.factorial : ℕ) : ℤ) ∣ y.1.2 - x.1.2 := by
    intro k x
    obtain ⟨f', ν', h1, h2⟩ := step D (k + 1) k.succ_pos _ (Nat.mul_pos hN k.factorial_pos) _ _ x.2
    refine ⟨⟨(f', ν'), ?_⟩, h2⟩
    rwa [Nat.factorial_succ, Nat.mul_comm (k + 1), ← Nat.mul_assoc]
  choose nx hnx using hstep
  let s : ∀ k, T k := fun k => Nat.rec (⟨(f, ν), by
    rw [Nat.factorial_zero, Nat.mul_one]; exact ⟨hc, hf⟩⟩ : T 0) nx k
  have hs : ∀ k j, k ≤ j → (∀ a, D.ModN (N * k.factorial) ((s j).1.1 a - (s k).1.1 a)) ∧
      ((N * k.factorial : ℕ) : ℤ) ∣ (s j).1.2 - (s k).1.2 := by
    intro k j hkj
    induction j, hkj using Nat.le_induction with
    | base => exact ⟨fun a => ⟨0, by simp⟩, by simp⟩
    | succ j hkj ih =>
      have hd : N * k.factorial ∣ N * j.factorial :=
        Nat.mul_dvd_mul_left N (Nat.factorial_dvd_factorial hkj)
      obtain ⟨h1, h2⟩ := hnx j (s j)
      refine ⟨fun a => modN_trans D (modN_of_dvd_modulus D hd (h1 a)) (ih.1 a), ?_⟩
      have h3 := dvd_add ((Int.natCast_dvd_natCast.mpr hd).trans h2) ih.2
      rwa [sub_add_sub_cancel] at h3
  have hd : ∀ n, 0 < n → n ∣ N * n.factorial := fun n hn =>
    (Nat.dvd_factorial hn le_rfl).mul_left N
  refine ⟨⟨fun n => (s n).1.1, fun n => (s n).1.2, fun n m hn hm a => ?_, fun n hn => ?_,
    fun n hn => ?_⟩, fun a => ?_, ?_⟩
  · exact modN_of_dvd_modulus D (hd n hn) ((hs n _ (Nat.le_mul_of_pos_right n hm)).1 a)
  · exact exists_inv D hn ((s n).2.of_dvd D (hd n hn))
  · exact ((s n).2.of_dvd D (hd n hn)).2
  · exact modN_of_dvd_modulus D (dvd_mul_right N _) ((hs 0 N N.zero_le).1 a)
  · exact (Int.natCast_dvd_natCast.mpr (dvd_mul_right N _)).trans (hs 0 N N.zero_le).2

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NsmulMemSmulTop
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.ObjLower

section Identity

variable {X : Scheme.{0}}

def idIso (L : LB X) : LB.Iso L (L.pull (𝟙 X)) where
  s := fun p => res (fun _ hx => ⟨mem_pull.1 hx.1, hx.2⟩ :
    (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2) (L.g (p.1 PUnit.unit) p.2)

theorem gw_idIso (L : LB X) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j k : L.ι) (hj : f y ∈ L.U j) (hk : f y ∈ L.U k) :
    gw (idIso L) f y j k = gm f y _ (L.g j k) :=
  gm_res f y _ (show f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k from ⟨mem_pull.2 hj, hk⟩) _

theorem pgen_idIso {L : LB X} (hL : L.IsLB) : PGen (idIso L) := by
  intro Y f y j j' k k' hj hj' hk hk'
  rw [gw_idIso L f y j k hj hk, gw_idIso L f y j' k' hj' hk', Category.comp_id,
    ← gm_cocycle hL f y hj' hk hk', ← gm_cocycle hL f y hj hj' hk]
  generalize gm f y _ (L.g j j') = A
  generalize gm f y _ (L.g j' k) = B
  generalize gm f y _ (L.g k k') = C
  rw [_root_.mul_assoc, mul_comm B C, inv_mul_cancel_left]

theorem pmaps_idIso (L : LB X) {K : Type} [Fintype K] {Y : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : PMaps (idIso L) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  have hm : r z ∈ LB.wchart L φ p ⊓ LB.wchart L φ q := ⟨Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩
  have e := congrArg (gm r z (LB.wchart L φ p ⊓ LB.wchart L φ q)) (ht p q)
  rw [Category.comp_id]
  refine (gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans ?_))
  refine congrArg₂ (· * ·) ?_ (gm_res r z _ hm _)
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  rw [gw_idIso L (r ≫ φ k) z (p k) (q k) (hp k) (hq k)]
  exact (gm_res r z _ hm _).trans (gm_pull r (φ k) z (L.U (p k) ⊓ L.U (q k)) ⟨hp k, hq k⟩ _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

def cubeId (G : Over S) [GrpObj G] [IsCommMonObj G] : CubeMap G G where
  F := 𝟙 _
  F3 := 𝟙 _
  e := 𝟙 _
  e_comm := by rw [Category.comp_id, Category.id_comp]
  psum_comm := fun _ => by rw [Category.comp_id, Category.id_comp]

def sabId (t : SAB H S) : SABMap t t (𝟙 S) where
  cm := cubeId t.G
  cart := by
    refine ⟨(IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (𝟙 t.G.left) t.G.hom t.G.hom (𝟙 S)),
      fun T x y x₀ y₀ hx hy => ?_⟩
    refine Eq.trans ?_ (Category.comp_id _).symm
    exact mul_left_congr (b := T.hom) (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _))
      (hy.trans (Category.comp_id _))
  base := rfl
  act := fun a => by
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    rw [Category.comp_id, Category.id_comp]
  lin := (isPullCubical_iff _ _ _).2 ⟨idIso t.PP.L, pgen_idIso t.PP.isLB,
    pmaps_idIso _ _ _ _ t.PP.rigGen, pmaps_idIso _ _ _ _ t.cub.isGen⟩

end Identity

section Ideals

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem quot_mul_mem {l l₂ : Level H} (h : l.Dvd l₂) {x : 𝓞 E} (hx : x ∈ l.Mb) :
    ((l₂.M / l.M : ℕ) : 𝓞 E) * x ∈ l₂.Mb := by
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 h.2.1
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have h0 : Ideal.span {(l.M : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast hM
  have e : Ideal.span {(l.M : 𝓞 E)} * (J * J.map (H.bar : 𝓞 E →+* 𝓞 E)) =
      Ideal.span {(l.M : 𝓞 E)} * Ideal.span {((l₂.M / l.M : ℕ) : 𝓞 E)} := by
    rw [Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul, Nat.mul_div_cancel' h.1, ← l₂.prod, ← l.prod, hJ,
      Ideal.map_mul]
    ring
  have hk : ((l₂.M / l.M : ℕ) : 𝓞 E) ∈ J := by
    apply (Ideal.mul_le_left : J * J.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ J)
    rw [mul_left_cancel₀ h0 e]
    exact Ideal.mem_span_singleton_self _
  rw [hJ, mul_comm _ x]
  exact Ideal.mul_mem_mul hx hk

theorem quot_mul_mem_map {l l₂ : Level H} (h : l.Dvd l₂) {x : 𝓞 E}
    (hx : x ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) :
    ((l₂.M / l.M : ℕ) : 𝓞 E) * x ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 hx
  have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) (quot_mul_mem h hy)
  rwa [map_mul, map_natCast] at this

theorem nsmul_mem_smul_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {I J : Ideal R} {n : ℕ}
    (h : ∀ x ∈ I, (n : R) * x ∈ J) {a : M} (ha : a ∈ I • (⊤ : Submodule R M)) :
    n • a ∈ J • (⊤ : Submodule R M) := by
  refine Submodule.smul_induction_on ha (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · rw [← Nat.cast_smul_eq_nsmul R, smul_smul]
    exact Submodule.smul_mem_smul (h r hr) trivial
  · rw [smul_add]; exact add_mem hx hy

end Ideals

theorem map_nsmul_of_add {A Q : Type*} [AddCommGroup A] [Group Q] (f : A → Q) (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : A) : f (n • a) = f a ^ n := by
  induction n with
  | zero =>
    have := hf 0 0
    rw [add_zero] at this
    rw [zero_nsmul, pow_zero]
    exact left_eq_mul.1 this
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}
  {B : Type} [CommRing B] {b : Base l B} {b₂ : Base l₂ B} {S : Scheme.{0}} {s : S ⟶ Sp B}

def lower (o₂ : Obj D l₂ b₂ s) (h : l.Dvd l₂) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) : Obj D l b s where
  t := o₂.t
  proper := o₂.proper
  ample := o₂.ample
  ktriv := o₂.ktriv
  eta a := o₂.eta a ^ (l₂.M / l.M)
  eta_add a c := by rw [o₂.eta_add, mul_pow]
  eta_ker a ha := by
    rw [← map_nsmul_of_add _ o₂.eta_add]
    exact o₂.eta_ker _ (nsmul_mem_smul_top (fun _ hx => quot_mul_mem h hx) ha)
  etaA a := o₂.etaA a ^ (l₂.A / l.A)
  etaA_add a c := by rw [o₂.etaA_add, mul_pow]
  etaA_ker a := by
    rw [← map_nsmul_of_add _ o₂.etaA_add, smul_smul, Nat.div_mul_cancel h.2.2, o₂.etaA_ker]
  geom k _ _ x β hx := by
    obtain ⟨hd, I, h₁, h₂, h₃⟩ := o₂.geom k x β hx
    have hA : 0 < l₂.A / l.A := Nat.div_pos (Nat.le_of_dvd l₂.A_pos h.2.2) l.A_pos
    have hM₁ : 0 < l.M := by have := l.three_le; omega
    have hM₂ : 0 < l₂.M := by have := l₂.three_le; omega
    have hM : 0 < l₂.M / l.M := Nat.div_pos (Nat.le_of_dvd hM₂ h.1) hM₁
    refine ⟨hρ ▸ hd, I, ?_, fun a => ?_, fun a ha => ?_⟩
    · rw [hζ, map_pow, ← h₁, ← I.ζ_pow l.A _ l.A_pos hA, Nat.mul_div_cancel' h.2.2, Units.val_pow_eq_pow_val]
    · rw [MonObj.comp_pow, h₂, ← I.tower l.A _ l.A_pos hA, Nat.mul_div_cancel' h.2.2]
    · rw [← map_nsmul_of_add _ o₂.eta_add,
        h₃ _ (nsmul_mem_smul_top (fun _ hx => quot_mul_mem_map h hx) ha),
        map_nsmul_of_add _ (I.add _), ← I.tower l.M _ hM₁ hM, Nat.mul_div_cancel' h.1]

end GlobalTheory.ObjLower

namespace GlobalTheory

theorem obj_lower_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l l₂ : Level H) (B : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B)
    (o₂ : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) →
    ∃ (o : Obj D l b s) (m : SABMap o₂.t o.t (𝟙 S)),
      (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta a).left) ∧
      (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left) := by
  intro E _ _ _ H D l l₂ B _ b b₂ S s o₂ h hρ hζ
  exact ⟨ObjLower.lower o₂ h hρ hζ, ObjLower.sabId o₂.t,
    fun _ => (Category.comp_id _).trans (Category.id_comp _).symm,
    fun _ => (Category.comp_id _).trans (Category.id_comp _).symm⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliRepOfBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

def objRestrictBase {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {B : Type} [CommRing B] {b : Base l B} (j : KA l →+* B) {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)
    (hρ : j (baseKA l).ρ = b.ρ) (hζ : j (baseKA l).ζ = b.ζ) : Obj D l (baseKA l) (s ≫ spMap j) where
  t := o.t
  proper := o.proper
  ample := o.ample
  ktriv := o.ktriv
  eta := o.eta
  eta_add := o.eta_add
  eta_ker := o.eta_ker
  etaA := o.etaA
  etaA_add := o.etaA_add
  etaA_ker := o.etaA_ker
  geom := by
    intro k _ _ x β hx
    have h1 : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := by
      simp [spMap]
    have h2 : β = (Spec.preimage (x ≫ s)).hom.comp j := by
      have h3 : spMap β = spMap ((Spec.preimage (x ≫ s)).hom.comp j) := by
        rw [← hx, ← Category.assoc]
        conv_lhs => rw [h1]
        simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h3)
    have h := o.geom k x _ h1
    rw [← hρ, ← hζ] at h
    subst h2
    exact h

theorem moduli_rep_of_base :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o'' : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫ f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f) := by
  intro _ E _ _ _ H D l Xo B _ b j S s o hS hρ hζ
  obtain ⟨f, ⟨hf, ⟨m⟩⟩, hu⟩ := Xo.rep S (s ≫ spMap j) hS (objRestrictBase j o hρ hζ)
  refine ⟨f, ⟨hf, ⟨⟨m.toSABMap, m.eta, m.etaA⟩⟩⟩, ?_⟩
  rintro g ⟨hg, ⟨m'⟩⟩
  exact hu g ⟨hg, ⟨⟨m'.toSABMap, m'.eta, m'.etaA⟩⟩⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfBaseEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

theorem zeta_eq_pow_div_of_dvd {a b : ℕ} (hb : 0 < b) (h : a ∣ b) : zeta a = zeta b ^ (b / a) := by
  obtain ⟨c, rfl⟩ := h
  have ha : 0 < a := Nat.pos_of_mul_pos_right hb
  have hc : 0 < c := Nat.pos_of_mul_pos_left hb
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  rw [Nat.mul_div_cancel_left c ha, zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem levelField_le_of_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : KA l ≤ KA l₂ := by
  unfold KA
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  rcases hx with rfl | hx
  · exact IntermediateField.subset_adjoin _ _ (by simp)
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [zeta_eq_pow_div_of_dvd l₂.A_pos h]
    exact pow_mem (IntermediateField.subset_adjoin ℚ ({H.rt0, zeta l₂.A} : Set ℂ) (by simp)) _

def baseOfFinerLevel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : Base l (KA l₂) where
  unit := (baseKA l₂).unit
  ρ := (baseKA l₂).ρ
  ρ_sq := (baseKA l₂).ρ_sq
  ζ := IntermediateField.inclusion (levelField_le_of_dvd h) (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective (IntermediateField.inclusion_injective (levelField_le_of_dvd h))

def levelFieldIncl {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : KA l →+* KA l₂ :=
  (IntermediateField.inclusion (levelField_le_of_dvd h)).toRingHom

theorem coe_levelFieldIncl {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) (x : KA l) : ((levelFieldIncl h x : KA l₂) : ℂ) = (x : ℂ) :=
  IntermediateField.coe_inclusion (levelField_le_of_dvd h) x

theorem coe_baseKA_rho {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    (((baseKA l).ρ : KA l) : ℂ) = H.rt0 := rfl

theorem levelFieldIncl_rho {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : levelFieldIncl h (baseKA l).ρ = (baseOfFinerLevel h).ρ :=
  Subtype.ext ((coe_levelFieldIncl h _).trans ((coe_baseKA_rho l).trans (coe_baseKA_rho l₂).symm))

theorem levelFieldIncl_zeta {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : levelFieldIncl h (baseKA l).ζ = (baseOfFinerLevel h).ζ := rfl

theorem baseOfFinerLevel_rho {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : (baseOfFinerLevel h).ρ = (baseKA l₂).ρ := rfl

theorem baseOfFinerLevel_zeta {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : (baseOfFinerLevel h).ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, ← levelFieldIncl_zeta, coe_levelFieldIncl]
  exact zeta_eq_pow_div_of_dvd l₂.A_pos h

theorem exists_sabMap_of_base_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f g : S' ⟶ S} (n : SABMap t' t f) (h : f = g) :
    ∃ n' : SABMap t' t g, n'.φ = n.φ := by
  subst h
  exact ⟨n, rfl⟩

theorem exists_levelMap : (∀ (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k), Smooth s → IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o'' : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫ f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o₂ : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (o : Obj D l b s) (m : SABMap o₂.t o.t (𝟙 S)), (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∃ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) := by
  intro hsm _ hlow hrep E _ _ _ H D l l₂ Xo Xo₂ _ hd
  have hA : l.A ∣ l₂.A := hd.2.2
  obtain ⟨o, m₁, h₁, h₁A⟩ := hlow E H D l l₂ (KA l₂) (baseOfFinerLevel hA) (baseKA l₂) Xo₂.X Xo₂.s Xo₂.univ hd
    (baseOfFinerLevel_rho hA) (baseOfFinerLevel_zeta hA)
  have hred : IsReduced Xo₂.X := by
    have := Xo₂.smooth
    exact (hsm _ _ Xo₂.s (SmoothOfRelativeDimension.smooth D.dim Xo₂.s)).1
  obtain ⟨r, ⟨hr, ⟨m₂⟩⟩, -⟩ := hrep E H D l Xo (KA l₂) (baseOfFinerLevel hA) (levelFieldIncl hA) Xo₂.X Xo₂.s o hred
    (levelFieldIncl_rho hA) (levelFieldIncl_zeta hA)
  obtain ⟨m, hm⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₂.toSABMap m₁
  obtain ⟨n, hn⟩ := exists_sabMap_of_base_eq m (Category.id_comp r)
  have hφ : n.φ = m₁.φ ≫ m₂.toSABMap.φ := hn.trans hm
  refine ⟨r, levelFieldIncl hA, n, coe_levelFieldIncl hA, hr, fun a => ?_, fun a => ?_⟩
  · exact (congrArg (_ ≫ ·) hφ).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ m₂.toSABMap.φ) ((h₁ a).trans (Category.id_comp _))).trans (m₂.eta a)))
  · exact (congrArg (_ ≫ ·) hφ).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ m₂.toSABMap.φ) ((h₁A a).trans (Category.id_comp _))).trans (m₂.etaA a)))

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DifferentiableOnProdOfForall
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

private theorem differentiableOn_prod_of_forall {E κ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E}
    (s : Finset κ) (φ : κ → E → ℂ) (h : ∀ k, DifferentiableOn ℂ (φ k) S) :
    DifferentiableOn ℂ (fun z => ∏ k ∈ s, φ k z) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using differentiableOn_const (c := (1 : ℂ))
  | insert a t ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

section

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
  (u : HolUnif A L g) (u' : HolUnif A' L' g') {K : Type} [Fintype K] (f : K → (A ⟶ A'))
  (F : K → ((Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))) (ε : K → ℤ)

def linCombUnif (h : ∀ k z, u'.ex (F k z) = u.ex z ≫ f k) :
    HolUnif A (LB.LinComb L' (fun k => (f k).left) ε) g :=
  have hl : ∀ k z, (u'.ex (F k z)).left = (u.ex z).left ≫ (f k).left := fun k z => by
    rw [h k z]; rfl
  have hc : ∀ (j : K → L'.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ LB.wchart L' (fun k => (f k).left) j →
      ∀ k, ⊤ ≤ (u'.ex (F k z)).left ⁻¹ᵁ L'.U (j k) := fun j z hz k => by
    rw [hl k z]
    exact (CubeValues.le_preimage_wchart (u.ex z).left L' (fun k => (f k).left) j).1 hz k
  { ex := u.ex
    ex_add := u.ex_add
    ex_onto := u.ex_onto
    Λ := u.Λ
    ker := u.ker
    discrete := u.discrete
    full := u.full
    hol := u.hol
    fr := fun (j : K → L'.ι) z => ∏ k, u'.fr (j k) (F k z) ^ ε k
    fr_hol := fun j => by
      refine differentiableOn_prod_of_forall Finset.univ
        (fun k (z : Fin g → ℂ) => u'.fr (j k) (F k z) ^ ε k) fun k => ?_
      refine DifferentiableOn.zpow ?_ (Or.inl fun z hz => u'.fr_ne _ _ (hc j z hz k))
      exact (u'.fr_hol (j k)).comp (LinearMap.toContinuousLinearMap (F k)).differentiable.differentiableOn
        fun z hz => hc j z hz k
    fr_ne := fun j z hz => Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (u'.fr_ne _ _ (hc j z hz k))
    fr_compat := fun j j' z hz => by
      obtain ⟨h1, h2⟩ := (top_le_preimage_inf (u.ex z).left _ _).1 hz
      have e := CubeValues.val_linComb (u.ex z).left valAt'_rules L' (fun k => (f k).left) ε j j' h1 h2
      refine Eq.trans ?_ (congrArg (· * ∏ k, u'.fr (j' k) (F k z) ^ ε k) e.symm)
      show _ = (∏ k, _) * _
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← mul_zpow, ← hl k z]
      exact congrArg (· ^ ε k) (u'.fr_compat (j k) (j' k) (F k z)
        ((top_le_preimage_inf _ _ _).2 ⟨hc j z h1 k, hc j' z h2 k⟩)) }

end

theorem exists_holUnif_linComb : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left) (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g') (K : Type) [Fintype K] (f : K → (A ⟶ A')) (F : K → ((Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))) (ε : K → ℤ), (∀ k z, u'.ex (F k z) = u.ex z ≫ f k) → ∃ u₁ : HolUnif A (LB.LinComb L' (fun k => (f k).left) ε) g, u₁.ex = u.ex ∧ u₁.Λ = u.Λ ∧ ∀ (j : K → L'.ι) z, u₁.fr j z = ∏ k, u'.fr (j k) (F k z) ^ ε k := by
  intro A A' _ _ L L' g g' u u' K _ f F ε hF
  refine ⟨linCombUnif u u' f F ε hF, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro j z
    rfl

end GlobalTheory
end
end
