module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DerivativeAlongTangentCombinationModuli
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianFormsSameSignatureSameSpace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

section

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem exists_mulEquiv_of_isGrpPullback (h : IsGrpPullback G' G f φ) {X : Scheme.{0}} (a : X ⟶ S') (b : X ⟶ S)
    (hb : b = a ≫ f) :
    ∃ e : (Over.mk a ⟶ G') ≃* (Over.mk b ⟶ G), ∀ x, (e x).left = x.left ≫ φ := by
  subst hb
  let ρ : (Over.mk a ⟶ G') →* (Over.mk (a ≫ f) ⟶ G) :=
    MonoidHom.mk' (pushPt h.1.w) fun x y => Over.OverMorphism.ext (h.2 (Over.mk a) x y _ _ rfl rfl).symm
  have hρ : ∀ x, (ρ x).left = x.left ≫ φ := fun _ => rfl
  refine ⟨MulEquiv.ofBijective ρ ⟨fun x y hxy => ?_, fun y => ?_⟩, hρ⟩
  · refine Over.OverMorphism.ext (h.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm))
    exact (hρ x).symm.trans ((congrArg (fun z => z.left) hxy).trans (hρ y))
  · exact ⟨Over.homMk (h.1.lift y.left a (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext ((hρ _).trans (h.1.lift_fst _ _ _))⟩

variable {k : Type} [Field k]

theorem spMap_epsScale_comp_algebraMap (c : k) :
    spMap (epsScale c) ≫ spMap (algebraMap k (DualNumber k)) = spMap (algebraMap k (DualNumber k)) := by
  rw [← Spec.map_comp]
  congr 1
  ext a <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]

theorem spMap_fstHom_comp_algebraMap :
    spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 (Sp k) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem lieMult_iff_of_isGrpPullback (h : IsGrpPullback G' G f φ) {O : Type} [CommRing O] (act' : OAct O G')
    (act : OAct O G) (hact : ∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left) (x : Sp k ⟶ S') (τ : O →+* k)
    (n : ℕ) : LieMult act' x τ n ↔ LieMult act (x ≫ f) τ n := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback h (spMap (algebraMap k (DualNumber k)) ≫ x)
    (spMap (algebraMap k (DualNumber k)) ≫ x ≫ f) (Category.assoc _ _ _).symm
  obtain ⟨e₀, he₀⟩ := exists_mulEquiv_of_isGrpPullback h x (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ G').left ≫ φ := by
    rw [← he₀, map_one]
  have scale : ∀ (c : k) (u v : epsPt x ⟶ G'),
      u.left = spMap (epsScale c) ≫ v.left ↔ (e u).left = spMap (epsScale c) ≫ (e v).left := by
    intro c u v
    rw [he, he, ← Category.assoc]
    refine ⟨fun huv => congrArg (· ≫ φ) huv, fun huv => h.1.hom_ext huv ?_⟩
    refine (Over.w u).trans (Eq.symm ?_)
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w v)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (spMap_epsScale_comp_algebraMap c))
  have eact : ∀ (a : O) (v : epsPt x ⟶ G'), e (v ≫ act'.act a) = e v ≫ act.act a := by
    intro a v
    refine Over.OverMorphism.ext ?_
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc]
  have eig : ∀ v : epsPt x ⟶ G', IsLieEigen act' x τ v ↔ IsLieEigen act (x ≫ f) τ (e v) := by
    intro v
    refine and_congr ?_ (forall_congr' fun a => by rw [scale, eact])
    rw [he, one, ← Category.assoc]
    refine ⟨fun hv => by rw [hv], fun hv => h.1.hom_ext hv ?_⟩
    refine Eq.trans ?_ (Over.w (1 : Over.mk x ⟶ G')).symm
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w v)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ x) spMap_fstHom_comp_algebraMap).trans (Category.id_comp _))
  have prod : ∀ u : Fin n → (epsPt x ⟶ G'), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := by
    intro u
    rw [map_list_prod, List.map_ofFn]
    rfl
  have key : ∀ (v : Fin n → (epsPt x ⟶ G')) (w : epsPt x ⟶ G') (c : Fin n → k),
      (∃ u : Fin n → (epsPt x ⟶ G'),
        (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod) ↔
      ∃ u : Fin n → (epsPt (x ≫ f) ⟶ G),
        (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (e (v i)).left) ∧ e w = (List.ofFn u).prod := by
    intro v w c
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => e (u i), fun i => (scale _ _ _).1 (hu i), prod u⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => e.symm (u i), fun i => (scale _ _ _).2 ?_, e.injective ?_⟩
      · rw [e.apply_symm_apply]; exact hu i
      · rw [prod, hw]
        simp only [e.apply_symm_apply]
  constructor
  · rintro ⟨v, hv, hw⟩
    refine ⟨fun i => e (v i), fun i => (eig _).1 (hv i), fun w hw' => ?_⟩
    obtain ⟨w, rfl⟩ := e.surjective w
    exact (existsUnique_congr (key v w)).1 (hw w ((eig w).2 hw'))
  · rintro ⟨v, hv, hw⟩
    obtain ⟨v, rfl⟩ : ∃ v' : Fin n → (epsPt x ⟶ G'), v = fun i => e (v' i) :=
      ⟨fun i => e.symm (v i), funext fun i => (e.apply_symm_apply _).symm⟩
    exact ⟨v, fun i => (eig _).2 (hv i), fun w hw' => (existsUnique_congr (key v w)).2 (hw _ ((eig w).1 hw'))⟩

end

theorem detCond_iff_of_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S), Nonempty (SABMap t' t f) →
    ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (ρ : k), DetCond D t'.act x ρ ↔ DetCond D t.act (x ≫ f) ρ := by
  rintro E _ _ _ H D S S' t t' f ⟨m⟩ k _ x ρ
  refine forall_congr' fun τ => ?_
  rw [lieMult_iff_of_isGrpPullback m.cart t'.act t.act m.act x τ D.p,
    lieMult_iff_of_isGrpPullback m.cart t'.act t.act m.act x τ D.q]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.DerLin

theorem surj_fst (S : Type) [CommRing S] :
    Function.Surjective (spMap (TrivSqZeroExt.fstHom S S S).toRingHom : Sp S ⟶ Sp (DualNumber S)) := by
  intro p
  have hs : Function.Surjective (TrivSqZeroExt.fstHom S S S).toRingHom := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hr := range_comap_of_surjective _ _ hs
  have hp : (show PrimeSpectrum (DualNumber S) from p) ∈
      PrimeSpectrum.zeroLocus (RingHom.ker (TrivSqZeroExt.fstHom S S S).toRingHom : Set (DualNumber S)) := by
    intro x hx
    have hx0 : x.fst = 0 := hx
    have : x * x = 0 := by
      ext <;> simp [hx0]
    have hP := (show PrimeSpectrum (DualNumber S) from p).isPrime
    have h0 : x * x ∈ (show PrimeSpectrum (DualNumber S) from p).asIdeal := by
      rw [this]; exact Ideal.zero_mem _
    exact (hP.mem_or_mem h0).elim id id
  rw [← hr] at hp
  obtain ⟨q, hq⟩ := hp
  exact ⟨q, hq⟩

theorem le_of_fst_eq {S : Type} [CommRing S] {X : Scheme.{0}} {v v' : Sp (DualNumber S) ⟶ X}
    (hh : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v')
    {U : X.Opens} (h : ⊤ ≤ v' ⁻¹ᵁ U) : ⊤ ≤ v ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := surj_fst S p
  have h1 := h (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom S S S).toRingHom : Sp S ⟶ Sp (DualNumber S)) q))
  change v' _ ∈ U at h1
  change v _ ∈ U
  rw [← Scheme.Hom.comp_apply] at h1 ⊢
  rw [hh]; exact h1

theorem isCombAt_iff_isDerivAt0 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) ty P → ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (w : Fin m → (Fin g → ℂ)), (∀ i, IsDerivAt0 (fun z => (F.ex k P z).left) (w i) (v i)) → ∀ (a : Fin m → ℂ) (v' : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)), IsCombAt (F.u k P) v a v' ↔ IsDerivAt0 (fun z => (F.ex k P z).left) (∑ i, a i • w i) v' := by
  intro E _ _ _ H Dw l Xo σ' g ty F k P hP m v w hvw a
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.exponential_derivative_at_zero_isTangent E H Dw l Xo σ' g ty F k P hP
  obtain ⟨N, _, _, ν, ρ, -, hr, hc, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo ℂ (F.u k P)
  have htan : ∀ i, IsTanAt (F.u k P) (v i) := fun i => h1 _ _ (hvw i)
  choose b hb using fun i => (hr (v i)).1 (htan i)
  have hv : v = fun i => ν (b i) := funext fun i => (hb i).symm
  have fwd : ∀ v', IsCombAt (F.u k P) v a v' →
      IsDerivAt0 (fun z => (F.ex k P z).left) (∑ i, a i • w i) v' := by
    intro v' hv'
    have ht' : IsTanAt (F.u k P) v' := by
      rw [hv, hc] at hv'
      exact (hr v').2 ⟨_, hv'.symm⟩
    obtain ⟨v0, hv0, -⟩ := h2 0
    refine ⟨ht'.2.trans ((h1 _ _ hv0).2.symm.trans hv0.1), fun U h f => ?_⟩
    have hU : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U := fun i => le_of_fst_eq ((htan i).2.trans ht'.2.symm) h
    refine (GlobalTheory.T.derivative_along_tangent_combination_moduli E H Dw l Xo ℂ (F.u k P) m v a v' htan hv' U h hU f).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    exact congrArg (a i * ·) ((hvw i).2 U (hU i) f)
  intro v'
  refine ⟨fwd v', fun hd => ?_⟩
  have hex : IsCombAt (F.u k P) v a (ν (∑ i, a i • b i)) := by
    rw [hv, hc]
  rw [(h2 _).unique hd (fwd _ hex)]
  exact hex

end GlobalTheory.DerLin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HolFibre

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem isHolTo_comp {W : Set E} {X Y : Scheme.{0}} {c : E → (Sp ℂ ⟶ X)} (hc : IsHolTo W c) (ψ : X ⟶ Y) :
    IsHolTo W (fun w => c w ≫ ψ) := by
  intro U f
  have := hc (ψ ⁻¹ᵁ U) ((ψ.app U).hom f)
  simp only [valAt'_comp, ← top_le_preimage_comp] at this
  exact this

theorem isHolTo_const {W : Set E} (hW : IsOpen W) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) :
    IsHolTo W (fun _ => x) := by
  intro U f
  refine ⟨?_, differentiableOn_const _⟩
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp only [h, and_true]
    exact hW
  · simp only [h, and_false, Set.setOf_false, isOpen_empty]

theorem isHolTo_of_isPullback {W : Set E} {S X Y Z : Scheme.{0}}
    {p : Z ⟶ X} {q : Z ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S} (H : IsPullback p q s t) {c : E → (Sp ℂ ⟶ Z)}
    (ha : IsHolTo W (fun w => c w ≫ p)) (hb : IsHolTo W (fun w => c w ≫ q)) : IsHolTo W c := by
  intro U f
  refine holFamily_of_affine valAt'_rules W Z c (fun w₀ hw₀ => ?_) U f
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hx₀, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((c w₀ ≫ p ≫ s) (default : PrimeSpectrum ℂ))) isOpen_univ
  have hm₁ : (c w₀ ≫ p) (default : PrimeSpectrum ℂ) ∈ s ⁻¹ᵁ U₀ := by
    rw [← top_le_preimage_iff_mem, ← top_le_preimage_comp, Category.assoc, top_le_preimage_iff_mem]
    exact hx₀
  have hm₂ : (c w₀ ≫ q) (default : PrimeSpectrum ℂ) ∈ t ⁻¹ᵁ U₀ := by
    rw [← top_le_preimage_iff_mem, ← top_le_preimage_comp, Category.assoc, ← H.w, top_le_preimage_iff_mem]
    exact hx₀
  obtain ⟨_, ⟨U₁, hU₁, rfl⟩, hx₁, hl₁⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hm₁ (s ⁻¹ᵁ U₀).isOpen
  obtain ⟨_, ⟨U₂, hU₂, rfl⟩, hx₂, hl₂⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    hm₂ (t ⁻¹ᵁ U₀).isOpen
  have hU₀ : IsAffineOpen U₀ := hU₀
  have hU₁ : IsAffineOpen U₁ := hU₁
  have hU₂ : IsAffineOpen U₂ := hU₂
  have hl₁ : U₁ ≤ s ⁻¹ᵁ U₀ := hl₁
  have hl₂ : U₂ ≤ t ⁻¹ᵁ U₀ := hl₂
  set V : Z.Opens := p ⁻¹ᵁ U₁ ⊓ q ⁻¹ᵁ U₂ with hVdef
  have hiff : ∀ w, ⊤ ≤ c w ⁻¹ᵁ V ↔ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ U₁ ∧ ⊤ ≤ (c w ≫ q) ⁻¹ᵁ U₂ := fun w => by
    rw [hVdef, Scheme.Hom.preimage_inf, le_inf_iff, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  have hV : IsAffineOpen V := by
    have : IsAffine _ := hU₀
    have : IsAffine _ := hU₁
    have : IsAffine _ := hU₂
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := U₀) (UT := U₂) (UX := U₁) hl₂ hl₁
      hVdef).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := U₀) (UT := U₂) (UX := U₁) hl₂ hl₁ hVdef).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ hU₀ hU₂ hU₁)
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  refine ⟨V, hV, (hiff w₀).2 ⟨(top_le_preimage_iff_mem _ _).2 hx₁, (top_le_preimage_iff_mem _ _).2 hx₂⟩, ?_,
    fun g => ?_⟩
  · convert (ha U₁ 0).1.inter (hb U₂ 0).1 using 1
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hiff]
    tauto
  · have hg : g ∈ Subring.closure _ := hgen.ge (Subring.mem_top g)
    induction hg using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · exact ((ha U₁ y).2.mono fun w (hw : w ∈ {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V}) =>
          ⟨hw.1, ((hiff w).1 hw.2).1⟩).congr fun w hw =>
          valAt'_appLE (c w) p U₁ V _ y hw.2
      · exact ((hb U₂ y).2.mono fun w (hw : w ∈ {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V}) =>
          ⟨hw.1, ((hiff w).1 hw.2).2⟩).congr fun w hw =>
          valAt'_appLE (c w) q U₂ V _ y hw.2
    | zero => exact (differentiableOn_const (0 : ℂ)).congr fun w _ => valAt'_zero _ _
    | one => exact (differentiableOn_const (1 : ℂ)).congr fun w hw => valAt'_one _ hw.2
    | add x y _ _ hx hy => exact (hx.add hy).congr fun w _ => valAt'_add _ _ _ _
    | neg x _ hx => exact hx.neg.congr fun w _ => valAt'_neg _ _ _
    | mul x y _ _ hx hy => exact (hx.mul hy).congr fun w _ => valAt'_mul _ _ _ _

theorem isHolTo_fibPt {W : Set E} (hW : IsOpen W) {X : Scheme.{0}} (G : Over X) (y : Sp ℂ ⟶ X)
    (e : E → (Over.mk y ⟶ G)) (he : IsHolTo W (fun z => (e z).left)) :
    IsHolTo W (fun z => fibPt G (e z)) := by
  refine isHolTo_of_isPullback (IsPullback.of_hasPullback G.hom y) ?_ ?_
  · simp only [fibPt, pullback.lift_fst]
    exact he
  · simp only [fibPt, pullback.lift_snd]
    exact isHolTo_const hW _

theorem isHolTo_fibPt_and_comp :
    ∀ (X : Scheme.{0}) (G : Over X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => fibPt G (e z)) ∧ ∀ (Y : Scheme.{0}) (ψ : pullback G.hom y ⟶ Y), IsHolTo Set.univ (fun z => fibPt G (e z) ≫ ψ) :=
  fun _ G y _ e he =>
    ⟨isHolTo_fibPt isOpen_univ G y e he, fun _ ψ => isHolTo_comp (isHolTo_fibPt isOpen_univ G y e he) ψ⟩

end GlobalTheory.HolFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.isHolTo_fibPt_and_comp_fibre : ∀ (X : Scheme.{0}) (G : Over X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => fibPt G (e z)) ∧ ∀ (Y : Scheme.{0}) (ψ : pullback G.hom y ⟶ Y), IsHolTo Set.univ (fun z => fibPt G (e z) ≫ ψ) := by
  first | exact @GlobalTheory.HolFibre.isHolTo_fibPt_and_comp | exact GlobalTheory.HolFibre.isHolTo_fibPt_and_comp | (intros; apply GlobalTheory.HolFibre.isHolTo_fibPt_and_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionary
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionary
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem exists_letter_equiv {E : Type} [Field E] (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (p q r : ℕ) (hr : r = p + q)
    (ρ : (E →+* ℂ) → (E →+* ℂ)) (hρ : Function.Bijective ρ) (m : (E →+* ℂ) → ℕ)
    (hp : ∀ τ, ρ τ ∈ Ψ → m τ = p) (hq : ∀ τ, ρ τ ∉ Ψ → m τ = q) :
    ∃ f : (Σ τ, Fin (m τ)) ≃ Ψ × Fin r, ∀ s,
      (ρ s.1 ∈ Ψ ∧ (f s).1.1 = ρ s.1 ∧ ((f s).2 : ℕ) = q + s.2) ∨
      (ρ s.1 ∉ Ψ ∧ (f s).1.1 = ComplexEmbedding.conjugate (ρ s.1) ∧ ((f s).2 : ℕ) = q - 1 - s.2 ∧ (s.2 : ℕ) < q) := by
  classical
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  have hf : ∀ s : Σ τ, Fin (m τ), ∃ t : Ψ × Fin r,
      (ρ s.1 ∈ Ψ ∧ t.1.1 = ρ s.1 ∧ (t.2 : ℕ) = q + s.2) ∨
      (ρ s.1 ∉ Ψ ∧ t.1.1 = ComplexEmbedding.conjugate (ρ s.1) ∧ (t.2 : ℕ) = q - 1 - s.2 ∧ (s.2 : ℕ) < q) := by
    rintro ⟨τ, i⟩
    have hi := i.2
    by_cases h : ρ τ ∈ Ψ
    · have := hp τ h
      exact ⟨(⟨ρ τ, h⟩, ⟨q + i, by omega⟩), Or.inl ⟨h, rfl, rfl⟩⟩
    · have := hq τ h
      have h' : ComplexEmbedding.conjugate (ρ τ) ∈ Ψ := by
        by_contra h'
        exact h ((hΨ _).2 h')
      exact ⟨(⟨_, h'⟩, ⟨q - 1 - i, by omega⟩), Or.inr ⟨h, rfl, rfl, by show (i : ℕ) < q; omega⟩⟩
  choose f hf using hf
  have hext : ∀ s s' : Σ τ, Fin (m τ), ρ s.1 = ρ s'.1 → (s.2 : ℕ) = s'.2 → s = s' := by
    rintro ⟨τ, i⟩ ⟨τ', i'⟩ h1 h2
    obtain rfl : τ = τ' := hρ.1 h1
    obtain rfl : i = i' := Fin.ext h2
    rfl
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩, hf⟩
  · intro s s' hss
    have h1 := hf s
    have h2 := hf s'
    rw [← hss] at h2
    rcases h1 with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩ <;> rcases h2 with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
    · exact hext _ _ (b1.symm.trans b2) (by omega)
    · omega
    · omega
    · refine hext _ _ ?_ (by omega)
      rw [← hcc (ρ s.1), ← b1, b2, hcc]
  · rintro ⟨⟨τ, hτ⟩, j⟩
    have hj := j.2
    by_cases h : (j : ℕ) < q
    · obtain ⟨τ0, h0⟩ := hρ.2 (ComplexEmbedding.conjugate τ)
      have hn : ρ τ0 ∉ Ψ := h0 ▸ (hΨ τ).1 hτ
      have := hq τ0 hn
      refine ⟨⟨τ0, ⟨q - 1 - j, by omega⟩⟩, ?_⟩
      rcases hf ⟨τ0, ⟨q - 1 - j, by omega⟩⟩ with ⟨a, -⟩ | ⟨-, b, c, -⟩
      · exact absurd a hn
      · refine Prod.ext (Subtype.ext ?_) (Fin.ext ?_)
        · rw [b]; show ComplexEmbedding.conjugate (ρ τ0) = τ; rw [h0, hcc]
        · rw [c]; show q - 1 - (q - 1 - j) = j; omega
    · obtain ⟨τ0, h0⟩ := hρ.2 τ
      have hn : ρ τ0 ∈ Ψ := h0 ▸ hτ
      have := hp τ0 hn
      refine ⟨⟨τ0, ⟨j - q, by omega⟩⟩, ?_⟩
      rcases hf ⟨τ0, ⟨j - q, by omega⟩⟩ with ⟨-, b, c⟩ | ⟨a, -⟩
      · refine Prod.ext (Subtype.ext ?_) (Fin.ext ?_)
        · rw [b]; exact h0
        · rw [c]; show q + (j - q) = j; omega
      · exact absurd hn a

theorem letter_column_dictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, (∃ idx : Fin g ≃ (M.X k).Ψ × Fin r, (∀ j, relab c σ (e j).1 = if ((idx j).2 : ℕ) < (F.Di k).q then ComplexEmbedding.conjugate (idx j).1.1 else (idx j).1.1) ∧ (∀ j, ((idx j).2 : ℕ) = if ((idx j).2 : ℕ) < (F.Di k).q then (F.Di k).q - 1 - (e j).2 else (F.Di k).q + (e j).2) ∧ ∀ (x : Frame (M.X k).Ψ r) (v : Fin r → E) j, perFr (M.X k) x v (relab c σ (e j).1) (e j).2 = if ((idx j).2 : ℕ) < (F.Di k).q then hermC (idx j).1.1 (M.X k).Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v) else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2) ∧ (M.X k).p0 = (F.Di k).q ∧ r = (F.Di k).p + (F.Di k).q ∧ cc (-(M.X k).ξ0) = -(-(M.X k).ξ0) ∧ (∀ τ ∈ (M.X k).Ψ, 0 < (τ (-(M.X k).ξ0)).im) ∧ ∀ φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E), (∀ a, φ a = (M.φ k a : Fin r → E)) → LinearMap.range φ = (M.X k).Λ ∧ (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc ((M.X k).Gm a b) = (M.X k).Gm b a) ∧ (M.X k).Gm.det ≠ 0 ∧ ∀ x y, (((F.Di k).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-(M.X k).ξ0 * herm (M.X k).Gm (φ x) (φ y))) := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hσ hB hN k
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp, hq⟩ := F.sig k
  obtain ⟨hp0, hty⟩ := hB.type k
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  refine ⟨?_, hp0.trans hq.symm, by rw [hp, hq]; exact hB.rank, ?_, ?_, ?_⟩
  · obtain ⟨f, hf⟩ := exists_letter_equiv (M.X k).Ψ (M.X k).cmType Dw.p Dw.q r hB.rank (relab c σ) hbij Dw.mult
      (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
      (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
    obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ (M.X k).Ψ × Fin r, ∀ j,
        (relab c σ (e j).1 ∈ (M.X k).Ψ ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
        (relab c σ (e j).1 ∉ (M.X k).Ψ ∧ (idx j).1.1 = ComplexEmbedding.conjugate (relab c σ (e j).1) ∧
          ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
    rw [hq]
    refine ⟨idx, fun j => ?_, fun j => ?_, fun x v j => ?_⟩
    · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
      · rw [if_neg (by omega), b]
      · rw [if_pos (by omega), b, hcc]
    · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
      · rw [if_neg (by omega), c']
      · rw [if_pos (by omega), c']
    · have h := hi j
      generalize idx j = t at h ⊢
      obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
      dsimp only at h ⊢
      rw [← hp0] at h ⊢
      rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
      · rw [if_neg (by omega)]
        unfold perFr
        rw [dite_eq_left a, dite_eq_left hn]
      · rw [if_pos (by omega)]
        unfold perFr
        rw [dite_eq_right a, dite_eq_left (show conjEmb (relab c σ (e j).1) ∈ (M.X k).Ψ from hτ), dite_eq_left hn]
        rfl
  · have h := (M.X k).ξ0_im
    unfold cc at h ⊢
    rw [map_neg, h]
  · intro τ hτ
    have := hN k τ hτ
    rw [map_neg, Complex.neg_im]
    linarith
  · intro φ hφ
    have hrange : LinearMap.range φ = (M.X k).Λ := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        rw [hφ]
        exact (M.φ k a).2
      · intro hy
        exact ⟨(M.φ k).symm ⟨y, hy⟩, by rw [hφ, LinearEquiv.apply_symm_apply]⟩
    refine ⟨hrange, ?_, ?_, (M.X k).Gm_herm, (M.X k).Gm_det, fun x y => ?_⟩
    · intro a b hab
      rw [hφ, hφ] at hab
      exact (M.φ k).injective (Subtype.ext hab)
    · rw [← LinearMap.coe_range, hrange]
      exact (M.X k).Λ_span
    · rw [hφ, hφ]
      exact hB.ef k x y

end GlobalTheory.FrameUnif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionaryStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmType_letter_frame_column_dictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, (∃ idx : Fin g ≃ (M.X k).Ψ × Fin r, (∀ j, relab c σ (e j).1 = if ((idx j).2 : ℕ) < (F.Di k).q then ComplexEmbedding.conjugate (idx j).1.1 else (idx j).1.1) ∧ (∀ j, ((idx j).2 : ℕ) = if ((idx j).2 : ℕ) < (F.Di k).q then (F.Di k).q - 1 - (e j).2 else (F.Di k).q + (e j).2) ∧ ∀ (x : Frame (M.X k).Ψ r) (v : Fin r → E) j, perFr (M.X k) x v (relab c σ (e j).1) (e j).2 = if ((idx j).2 : ℕ) < (F.Di k).q then hermC (idx j).1.1 (M.X k).Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v) else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2) ∧ (M.X k).p0 = (F.Di k).q ∧ r = (F.Di k).p + (F.Di k).q ∧ cc (-(M.X k).ξ0) = -(-(M.X k).ξ0) ∧ (∀ τ ∈ (M.X k).Ψ, 0 < (τ (-(M.X k).ξ0)).im) ∧ ∀ φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E), (∀ a, φ a = (M.φ k a : Fin r → E)) → LinearMap.range φ = (M.X k).Λ ∧ (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc ((M.X k).Gm a b) = (M.X k).Gm b a) ∧ (M.X k).Gm.det ≠ 0 ∧ ∀ x y, (((F.Di k).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-(M.X k).ξ0 * herm (M.X k).Gm (φ x) (φ y))) := by
  first | exact @GlobalTheory.FrameUnif.letter_column_dictionary | exact GlobalTheory.FrameUnif.letter_column_dictionary | (intros; apply GlobalTheory.FrameUnif.letter_column_dictionary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.UnitFrames

open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

theorem uMat_conj_eq_diagonal {n : ℕ} (p0 : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hs : ∀ i : Fin (n + 1), 0 < psgn p0 i * (lminor A i).re) :
    ∃ d : Fin n → ℝ, (∀ k : Fin n, 0 < sgn p0 k * d k) ∧
      (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ) = Matrix.diagonal fun a => ((d a : ℝ) : ℂ) := by
  have hdet : ∀ c : Fin n, (blk A c).det ≠ 0 := by
    intro c h0
    have h := hs ⟨c, Nat.lt_succ_of_lt c.isLt⟩
    have : lminor A ⟨c, Nat.lt_succ_of_lt c.isLt⟩ = 0 := h0
    rw [this] at h
    simp at h
  set B := (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ) with hB
  have hH : B.IsHermitian := by
    have e : (uMat A).map (starRingEnd ℂ) = ((uMat A)ᵀ)ᴴ := by
      ext a c; simp [Matrix.conjTranspose_apply]
    rw [hB, e]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hA
  have hdiag : B = Matrix.diagonal fun k => B k k := by
    ext a c
    rcases lt_trichotomy a c with hac | hac | hac
    · rw [Matrix.diagonal_apply_ne _ (ne_of_lt hac), ← hH.apply a c, hB,
        uGu_lower _ hdet hac, star_zero]
    · subst hac
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ (ne_of_gt hac), hB, uGu_lower _ hdet hac]
  have hprod : ∀ i : Fin (n + 1), lminor A i
      = ∏ j : Fin i, (fun k => B k k) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
    intro i
    have e : lminor B i = lminor A i := by
      rw [hB, lminor_conj (uMat_upper _) i]
      simp only [uMat_diag, Finset.prod_const_one, one_mul, map_one, mul_one]
    rw [← e]
    exact (congrArg (fun M => lminor M i) hdiag).trans (lminor_diagonal _ i)
  have hre : ∀ k, (B k k).im = 0 := fun k => Complex.conj_eq_iff_im.1 (hH.apply k k)
  refine ⟨fun k => (B k k).re, fun k => ?_, ?_⟩
  · have hsucc : lminor A k.succ = lminor A k.castSucc * B k k := by
      rw [hprod k.succ, hprod k.castSucc]
      exact prod_castLE_succ (f := fun k => B k k) k.isLt
    have h1 := hs k.succ
    have h0 := hs k.castSucc
    rw [hsucc, Complex.mul_re, hre, mul_zero, sub_zero, Fin.val_succ, psgn_succ] at h1
    rw [Fin.val_castSucc] at h0
    refine (pos_iff_pos_of_mul_pos (a := psgn p0 k * (lminor A k.castSucc).re) ?_).1 h0
    exact h1.trans_eq (by ring)
  · rw [hdiag]
    congr 1
    funext k
    apply Complex.ext <;> simp [hre]

theorem exists_upper_conj_eq_signature {n : ℕ} (p0 : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hs : ∀ i : Fin (n + 1), 0 < psgn p0 i * (lminor A i).re) :
    ∃ b : Matrix (Fin n) (Fin n) ℂ, b.det ≠ 0 ∧ b.BlockTriangular id ∧
      bᵀ * A * b.map (starRingEnd ℂ)
        = Matrix.diagonal fun a : Fin n => ((sgn p0 (a : ℕ) : ℝ) : ℂ) := by
  obtain ⟨d, hd, hA'⟩ := uMat_conj_eq_diagonal p0 A hA hs
  refine ⟨uMat A * Matrix.diagonal fun k : Fin n => (((√(sgn p0 k * d k))⁻¹ : ℝ) : ℂ), ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, det_uMat, one_mul, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    exact Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 (hd k)).ne')
  · exact (uMat_upper A).mul (Matrix.blockTriangular_diagonal _)
  · rw [Matrix.transpose_mul, Matrix.map_mul, Matrix.diagonal_transpose,
      Matrix.diagonal_map (map_zero _), ← Matrix.mul_assoc, Matrix.mul_assoc _ (uMat A)ᵀ,
      Matrix.mul_assoc _ ((uMat A)ᵀ * A), hA',
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj]
    have h1 := Real.mul_self_sqrt (hd k).le
    have h2 := (Real.sqrt_pos.2 (hd k)).ne'
    set s := √(sgn p0 k * d k)
    have h3 : d k = sgn p0 k * (s * s) := by
      rw [h1]
      rcases sgn_sq p0 k with h | h <;> simp [h]
    rw [h3]
    field_simp

theorem frame_mul_triangular_orthonormal :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E), (∀ a b, cc (Gm a b) = Gm b a) → (∀ x ∈ GG Ψ Gm p0, ∃ x₀ : Frame Ψ r, ∃ b ∈ Bor Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ x₀ = rmul x b) ∧ ∀ (τ : E →+* ℂ) (x₀ x₁ : Matrix (Fin r) (Fin r) ℂ), gram τ Gm x₀ = (Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → gram τ Gm x₁ = gram τ Gm x₀ → ∃ u : Matrix (Fin r) (Fin r) ℂ, uᵀ * Gm.map τ * u.map (starRingEnd ℂ) = Gm.map τ ∧ x₁ = u * x₀ := by
  intro E _ _ _ r p0 Ψ Gm hG
  refine ⟨fun x hx => ?_, fun τ x₀ x₁ h0 h1 => ?_⟩
  · choose b hb using fun τ : Ψ => exists_upper_conj_eq_signature p0 (gram τ.1 Gm (mat x τ))
      (gram_isHermitian τ.1 hG _) (hx τ).2
    refine ⟨rmul x fun τ => b τ, fun τ => b τ,
      fun τ => ⟨(hb τ).1, fun a c hca => (hb τ).2.1 hca⟩, fun τ => ?_, rfl⟩
    show gram τ.1 Gm (mat x τ * b τ) = _
    rw [FrameDegreeData.gram_mul]
    exact (hb τ).2.2
  · have hdet : IsUnit x₀.det := by
      refine isUnit_iff_ne_zero.2 fun h => ?_
      have h2 := congrArg Matrix.det h0
      rw [FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul,
        zero_mul, Matrix.det_diagonal] at h2
      refine Finset.prod_ne_zero_iff.2 (fun k _ => ?_) h2.symm
      rcases sgn_sq p0 k with h' | h' <;> simp [h']
    refine ⟨x₁ * x₀⁻¹, ?_, (Matrix.nonsing_inv_mul_cancel_right _ _ hdet).symm⟩
    rw [← FrameDegreeData.gram_eq, FrameDegreeData.gram_mul, h1, ← FrameDegreeData.gram_mul, Matrix.mul_nonsing_inv _ hdet,
      FrameDegreeData.gram_eq]
    simp

end GlobalTheory.UnitFrames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ObjComp

section Bundle

variable {X : Scheme.{0}}

def idPullIso (L : LB X) : LB.Iso L (L.pull (𝟙 X)) :=
  ⟨fun p => res (fun _ hy => ⟨mem_pull.1 hy.1, hy.2⟩ :
    (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2) (L.g (p.1 PUnit.unit) p.2)⟩

theorem gw_idPullIso (L : LB X) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j k : L.ι) (hj : f y ∈ L.U j)
    (hk : f y ∈ L.U k) : gw (idPullIso L) f y j k = gm f y _ (L.g j k) := by
  have hm : f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k := ⟨mem_pull.2 hj, hk⟩
  show gm f y _ (res _ (L.g j k)) = _
  exact gm_res f y _ hm _

theorem pgen_idPullIso {L : LB X} (hL : L.IsLB) : PGen (idPullIso L) := by
  intro Y f y j j' k k' hj hj' hk hk'
  have hj₀ : f y ∈ L.U j := hj
  have hj₀' : f y ∈ L.U j' := hj'
  rw [gw_idPullIso L f y j k hj₀ hk, gw_idPullIso L f y j' k' hj₀' hk', Category.comp_id]
  have a := gm_cocycle hL f y hj₀ hk hk'
  have b := gm_cocycle hL f y hj₀ hj₀' hk'
  rw [mul_right_comm, b, ← a, mul_inv_cancel_right]

theorem pmaps_idPullIso (L : LB X) {K : Type} [Fintype K] {Y : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : PMaps (idPullIso L) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  have hp₀ : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  have hm : r z ∈ LB.wchart L φ p ⊓ LB.wchart L φ q := ⟨Set.mem_iInter.2 hp₀, Set.mem_iInter.2 hq⟩
  have e := congrArg (gm r z (LB.wchart L φ p ⊓ LB.wchart L φ q)) (ht p q)
  rw [Category.comp_id]
  refine (gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  rw [gw_idPullIso L (r ≫ φ k) z (p k) (q k) (hp₀ k) (hq k)]
  exact (gm_res r z _ hm _).trans (gm_pull r (φ k) z (L.U (p k) ⊓ L.U (q k)) ⟨hp₀ k, hq k⟩ _)

end Bundle

section Group

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

theorem isGrpPullback_id : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (mul_left_congr (b := T.hom) (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _))
    (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm

variable [IsCommMonObj G]

def cubeMapId : CubeMap G G where
  F := 𝟙 _
  F3 := 𝟙 _
  e := 𝟙 _
  e_comm := by rw [Category.comp_id, Category.id_comp]
  psum_comm := fun _ => by rw [Category.comp_id, Category.id_comp]

theorem isPullCubical_id {L : RigLB G} (c : CubicalStr G L) : (cubeMapId G).IsPullCubical c c :=
  (isPullCubical_iff _ c c).2 ⟨idPullIso L.L, pgen_idPullIso L.isLB,
    pmaps_idPullIso L.L _ _ L.rig L.rigGen, pmaps_idPullIso L.L _ _ c.t c.isGen⟩

end Group

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def sabMapId {S : Scheme.{0}} (t : SAB H S) : SABMap t t (𝟙 S) where
  cm := cubeMapId t.G
  cart := isGrpPullback_id t.G
  base := rfl
  act := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm
  lin := isPullCubical_id t.G t.cub

variable {D : Datum H} {l : Level H}

def objMapId {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s) :
    ObjMap o o (𝟙 S) where
  toSABMap := sabMapId o.t
  eta := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm
  etaA := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm

section

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {b : Base l B} {b' : Base l B'} {b'' : Base l B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {o : Obj D l b s} {o' : Obj D l b' s'} {o'' : Obj D l b'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}

theorem sec_comp {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    {x : S ⟶ G.left} {x' : S' ⟶ G'.left} {x'' : S'' ⟶ G''.left} (h : x' ≫ φ = f ≫ x) (h' : x'' ≫ φ' = f' ≫ x') :
    x'' ≫ φ' ≫ φ = (f' ≫ f) ≫ x := by
  rw [← Category.assoc, h', Category.assoc, h, Category.assoc]

theorem sec_cancel {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    (hp : IsPullback φ G'.hom G.hom f) (w : φ' ≫ G'.hom = G''.hom ≫ f')
    {x : S ⟶ G.left} {x' : S' ⟶ G'.left} {x'' : S'' ⟶ G''.left} (hx' : x' ≫ G'.hom = 𝟙 _) (hx'' : x'' ≫ G''.hom = 𝟙 _)
    (h : x' ≫ φ = f ≫ x) (h'' : x'' ≫ φ' ≫ φ = (f' ≫ f) ≫ x) : x'' ≫ φ' = f' ≫ x' := by
  apply hp.hom_ext
  · rw [Category.assoc, h'', Category.assoc, Category.assoc, h]
  · rw [Category.assoc, w, ← Category.assoc, hx'', Category.assoc, hx']; simp

theorem objMap_comp (m : ObjMap o' o f) (m' : ObjMap o'' o' f') :
    ∃ n : ObjMap o'' o (f' ≫ f), n.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ := by
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H S S' S'' o.t o'.t o''.t f f' m.toSABMap m'.toSABMap
  have hn' : n.cm.F = m'.cm.F ≫ m.cm.F := hn
  exact ⟨⟨n, fun a => by rw [hn']; exact sec_comp (m.eta a) (m'.eta a),
    fun a => by rw [hn']; exact sec_comp (m.etaA a) (m'.etaA a)⟩, hn⟩

theorem objMap_cancel (m : ObjMap o' o f) (n : ObjMap o'' o (f' ≫ f)) :
    ∃ m' : ObjMap o'' o' f', n.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ := by
  obtain ⟨m', hn⟩ := sabCancel pullCubCancel E H S S' S'' o.t o'.t o''.t f f' m.toSABMap n.toSABMap
  have hn' : n.cm.F = m'.cm.F ≫ m.cm.F := hn
  exact ⟨⟨m', fun a => sec_cancel m.cart.1 m'.cart.1.w (Over.w (o'.eta a)) (Over.w (o''.eta a)) (m.eta a)
      (by rw [← hn']; exact n.eta a),
    fun a => sec_cancel m.cart.1 m'.cart.1.w (Over.w (o'.etaA a)) (Over.w (o''.etaA a)) (m.etaA a)
      (by rw [← hn']; exact n.etaA a)⟩, hn⟩

end

end GlobalTheory.ObjComp

namespace GlobalTheory

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EigenBasisIffTangentBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EigenBasisIffTangentBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem basis_iff_of_split {S N J : Type} [CommRing S] [AddCommGroup N] [Module S N] [Fintype J]
    (m : J → ℕ) (M : J → Submodule S N)
    (hs : ∀ n : N, ∃! f : J → N, (∀ τ, f τ ∈ M τ) ∧ ∑ τ, f τ = n)
    (b : ∀ τ, Fin (m τ) → N) (hb : ∀ τ i, b τ i ∈ M τ) (g : ℕ) (e : Fin g ≃ Σ τ : J, Fin (m τ)) :
    (∀ τ n, n ∈ M τ → ∃! a : Fin (m τ) → S, n = ∑ i, a i • b τ i) ↔
      ∀ n : N, ∃! a : Fin g → S, n = ∑ j, a j • b (e j).1 (e j).2 := by
  classical
  have key : ∀ a : ∀ τ, Fin (m τ) → S,
      ∑ j, a (e j).1 (e j).2 • b (e j).1 (e j).2 = ∑ τ, ∑ i, a τ i • b τ i := by
    intro a
    rw [e.sum_comp (fun p : Σ τ : J, Fin (m τ) => a p.1 p.2 • b p.1 p.2), Fintype.sum_sigma]
  have key' : ∀ a : Fin g → S,
      ∑ j, a j • b (e j).1 (e j).2 = ∑ τ, ∑ i, a (e.symm ⟨τ, i⟩) • b τ i := by
    intro a
    rw [← key (fun τ i => a (e.symm ⟨τ, i⟩))]
    simp
  have hmem : ∀ τ (a : Fin (m τ) → S), ∑ i, a i • b τ i ∈ M τ := fun τ a =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb τ i)
  constructor
  · intro h n
    obtain ⟨f, ⟨hf, hfn⟩, hu⟩ := hs n
    choose a ha hau using fun τ => h τ (f τ) (hf τ)
    refine ⟨fun j => a (e j).1 (e j).2, ?_, ?_⟩
    · change n = ∑ j, a (e j).1 (e j).2 • b (e j).1 (e j).2
      rw [key, ← hfn]
      exact Finset.sum_congr rfl fun τ _ => ha τ
    · intro a' ha'
      rw [key'] at ha'
      have h1 := hu (fun τ => ∑ i, a' (e.symm ⟨τ, i⟩) • b τ i) ⟨fun τ => hmem τ _, ha'.symm⟩
      funext j
      have h2 := hau (e j).1 (fun i => a' (e.symm ⟨(e j).1, i⟩)) (congrFun h1 (e j).1).symm
      have h3 := congrFun h2 (e j).2
      simpa using h3
  · intro h τ n hn
    obtain ⟨a', ha', hu'⟩ := h n
    have hA : ∀ a : Fin (m τ) → S, n = ∑ i, a i • b τ i →
        (fun j => (Pi.single τ a : ∀ σ, Fin (m σ) → S) (e j).1 (e j).2) = a' := by
      intro a ha
      apply hu'
      change n = ∑ j, (Pi.single τ a : ∀ σ, Fin (m σ) → S) (e j).1 (e j).2 • b (e j).1 (e j).2
      rw [key, Finset.sum_eq_single τ]
      · simpa using ha
      · intro σ _ hσ
        simp [Pi.single_eq_of_ne hσ]
      · simp
    refine ⟨fun i => a' (e.symm ⟨τ, i⟩), ?_, ?_⟩
    · have ha2 : n = ∑ j, a' j • b (e j).1 (e j).2 := ha'
      rw [key'] at ha2
      have h1 := (hs n).unique (y₁ := fun τ => ∑ i, a' (e.symm ⟨τ, i⟩) • b τ i)
        (y₂ := Pi.single τ n) ⟨fun τ => hmem τ _, ha2.symm⟩ ⟨fun σ => by
          by_cases hσ : σ = τ
          · subst hσ; simpa using hn
          · simp [Pi.single_eq_of_ne hσ], by simp⟩
      have h2 := congrFun h1 τ
      simpa using h2.symm
    · intro a ha
      funext i
      have h1 := congrFun (hA a ha) (e.symm ⟨τ, i⟩)
      rw [← h1, Equiv.apply_symm_apply]
      simp

theorem eigBasis_iff_tanBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), (∀ τ i, IsTanAt x (u τ i)) → (∀ τ i, IsEigAt c τ (u τ i)) → ((∀ τ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → S, IsCombAt x (u τ) a w) ↔ TanBasis x (fun j => u (e j).1 (e j).2)) := by
  intro E _ _ _ H Dw l Xo c S _ _ x u g e ht he
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, hρ, hsm⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo S x
  choose b hb using fun τ i => (htan (u τ i)).1 (ht τ i)
  obtain rfl : u = fun τ i => v (b τ i) := by funext τ i; exact (hb τ i).symm
  let M : (E →+* ℂ) → Submodule S N := fun τ =>
    ⨅ a : 𝓞 E, Module.End.eigenspace (ρ a) (algebraMap c.F S (embK c τ a))
  have hM : ∀ τ n, n ∈ M τ ↔ ∀ a, ρ a n = algebraMap c.F S (embK c τ a) • n := by
    intro τ n
    simp only [M, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hE : ∀ τ n, IsEigAt c τ (v n) ↔ n ∈ M τ := by
    intro τ n
    rw [hM]
    refine forall_congr' fun a => ?_
    rw [← hρ, ← hsm, hinj.eq_iff]
  have hs : ∀ n : N, ∃! f : (E →+* ℂ) → N, (∀ τ, f τ ∈ M τ) ∧ ∑ τ, f τ = n := by
    intro n
    simp only [hM]
    exact GlobalTheory.T.existsUnique_cmEmbedding_eigenvector_sum E H l c S N ρ n
  have hmain := basis_iff_of_split (fun τ => Dw.mult τ) M hs b (fun τ i => (hE τ _).1 (he τ i)) g e
  have hT : ∀ n, IsTanAt x (v n) := fun n => (htan _).2 ⟨n, rfl⟩
  have hC : ∀ (k : ℕ) (b : Fin k → N) (a : Fin k → S) (n : N),
      IsCombAt x (fun i => v (b i)) a (v n) ↔ n = ∑ i, a i • b i := by
    intro k b a n
    rw [hcomb, hinj.eq_iff]
  constructor
  · intro h
    refine ⟨fun j => hT _, fun w hw => ?_⟩
    obtain ⟨n, rfl⟩ := (htan w).1 hw
    have h1 := hmain.1 (fun τ n hn => by
      have h2 := h τ (v n) (hT n) ((hE τ n).2 hn)
      simpa only [hC] using h2) n
    simpa only [hC] using h1
  · rintro ⟨-, h⟩ τ w hw hew
    obtain ⟨n, rfl⟩ := (htan w).1 hw
    have h1 := hmain.2 (fun n => by
      have h2 := h (v n) (hT n)
      simpa only [hC] using h2) τ n ((hE τ n).1 hew)
    simpa only [hC] using h1

end GlobalTheory.Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EigenBasisIffTangentBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenBasis_iff_tangentBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), (∀ τ i, IsTanAt x (u τ i)) → (∀ τ i, IsEigAt c τ (u τ i)) → ((∀ τ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → S, IsCombAt x (u τ) a w) ↔ TanBasis x (fun j => u (e j).1 (e j).2)) := by
  first | exact @GlobalTheory.Frames.eigBasis_iff_tanBasis | exact GlobalTheory.Frames.eigBasis_iff_tanBasis | (intros; apply GlobalTheory.Frames.eigBasis_iff_tanBasis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsScaledIsometry
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.SelfDualIsom

theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {M₁ M₂ V : Type}
    [AddCommGroup M₁] [Module (𝓞 E) M₁] [Module.Finite (𝓞 E) M₁]
    [AddCommGroup M₂] [Module (𝓞 E) M₂] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (φ₁ : M₁ →ₗ[𝓞 E] V) (φ₂ : M₂ →ₗ[𝓞 E] V)
    (hspan : Submodule.span E (Set.range φ₂) = ⊤) :
    ∃ N : ℕ, 0 < N ∧ ∀ x, (N : 𝓞 E) • φ₁ x ∈ LinearMap.range φ₂ := by
  classical
  have h1 : ∀ v : V, ∃ n : ℕ, 0 < n ∧ (n : 𝓞 E) • v ∈ LinearMap.range φ₂ := by
    intro v
    have hv : v ∈ Submodule.span E (Set.range φ₂) := by rw [hspan]; trivial
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E _ v hv
    rw [← LinearMap.coe_range, Submodule.span_eq] at ht
    have ht0 : (t : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero t.2
    have hm := Ideal.absNorm_mem (Ideal.span {(t : 𝓞 E)})
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hm
    refine ⟨Ideal.absNorm (Ideal.span {(t : 𝓞 E)}), Nat.pos_of_ne_zero ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact ht0
    · rw [← hc, mul_smul]
      exact Submodule.smul_mem _ _ ht
  choose n hn hmem using h1
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := 𝓞 E) (M := M₁)
  refine ⟨∏ x ∈ s, n (φ₁ x), Finset.prod_pos fun x _ => hn _, fun x => ?_⟩
  have hx : x ∈ Submodule.span (𝓞 E) (s : Set M₁) := by rw [hs]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => n (φ₁ x)) (Finset.mem_coe.1 hy)
    rw [hk, Nat.cast_mul, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (hmem _)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _), smul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul, smul_comm]; exact Submodule.smul_mem _ _ ha

end GlobalTheory.SelfDualIsom
end
