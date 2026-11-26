module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLogPeriodFamily
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PpicDvr
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixMiddle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixRight

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolarizedAbelianPartPrincipal
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolarizedAbelianPartPrincipal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.polarized_abelian_part_principal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (r : V →+* ℂ) (tV : SAB H (Sp V)), GlobalTheory.LN.CDvr V → Function.Surjective r → RingHom.ker r = IsLocalRing.maximalIdeal V → GlobalTheory.LN.PolAt tV (Out.jK V) → ∀ P : AbPart tV (spMap r), IsPrincipal P.tB := by
  first | exact @PositivityTheory.HtPt.Ppic.dvr | exact PositivityTheory.HtPt.Ppic.dvr
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolarizedAbelianPartPrincipalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarized_abelian_part_principal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (r : V →+* ℂ) (tV : SAB H (Sp V)), GlobalTheory.LN.CDvr V → Function.Surjective r → RingHom.ker r = IsLocalRing.maximalIdeal V → GlobalTheory.LN.PolAt tV (Out.jK V) → ∀ P : AbPart tV (spMap r), IsPrincipal P.tB := by
  first | exact @GlobalTheory.CompanionTheory.Relay.polarized_abelian_part_principal | exact GlobalTheory.CompanionTheory.Relay.polarized_abelian_part_principal | (intros; apply GlobalTheory.CompanionTheory.Relay.polarized_abelian_part_principal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0ZeroOfFixed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL.Pol
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {X : Scheme.{0}}

noncomputable def pullPolL (P : Out.PolAV X) {z : Sp ℂ ⟶ X} {A : Over (Sp ℂ)} [GrpObj A]
    {φ : A.left ⟶ P.A.left} (h : IsGrpPullback A P.A z φ) : Out.PolAV (Sp ℂ) :=
  have hL := pull_isLB P.isLB φ
  have H := pol_pull _ _ P.A A _ φ P.L _ P.isLB hL P.isAb h (PolBaseChange.lbIso_refl hL)
  { A := A, isAb := H.1, g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
    L := P.L.pull φ, isLB := hL, rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym, ample := H.2.1 P.ample, ktriv := H.2.2 P.ktriv }

end GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL.Pol

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL

open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows ReciprocityTheory.ChartRestriction.G.TB.ValAt _root_.Formalism.L2.Pj

theorem isDerivAt0_zero_of_fixed {g : ℕ} {Y : Scheme.{0}} {F : (Fin g → ℂ) → (Sp ℂ ⟶ Y)}
    {v : Sp (DualNumber ℂ) ⟶ Y} (h0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = F 0)
    (hv : spMap (epsMul (0 : ℂ)) ≫ v = v) : IsDerivAt0 F 0 v := by
  refine ⟨h0, fun U h f => ?_⟩
  rw [map_zero]
  have key : ∀ (v' : Sp (DualNumber ℂ) ⟶ Y) (_ : v' = spMap (epsMul (0 : ℂ)) ≫ v) (h' : ⊤ ≤ v' ⁻¹ᵁ U),
      TrivSqZeroExt.snd (show DualNumber ℂ from
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v'.appLE U ⊤ h').hom f)) = 0 := by
    rintro _ rfl h'
    have hs := ReciprocityTheory.ChartRestriction.G.PullbackSections.specMap_comp_appLE (CommRingCat.ofHom (epsMul (0 : ℂ))) v U h' h
    have := ConcreteCategory.congr_hom hs f
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    erw [this]
    simp [epsMul]
  exact key v hv.symm h

theorem isHolTo_slice {n g : ℕ} {B : Set (Fin n → ℂ)} {Y : Scheme.{0}}
    {F : (Fin n → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ Y)} (h : IsHolTo (B ×ˢ Set.univ) F) {b : Fin n → ℂ} (hb : b ∈ B) :
    IsHolTo Set.univ (fun z : Fin g → ℂ => F (b, z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hc : Continuous (fun z : Fin g → ℂ => (b, z)) := by fun_prop
  have hmem : ∀ z, z ∈ {z ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ F (b, z) ⁻¹ᵁ U} →
      (b, z) ∈ {bz ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ F bz ⁻¹ᵁ U} :=
    fun z hz => ⟨⟨hb, trivial⟩, hz.2⟩
  have hset : {z ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ F (b, z) ⁻¹ᵁ U} =
      (fun z => (b, z)) ⁻¹' {bz ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ F bz ⁻¹ᵁ U} :=
    Set.ext fun z => ⟨hmem z, fun hz => ⟨trivial, hz.2⟩⟩
  refine ⟨hset ▸ h1.preimage hc, fun z hz => ?_⟩
  have hd := (h2 _ (hmem z hz)).differentiableAt (h1.mem_nhds (hmem z hz))
  have hi : DifferentiableAt ℂ (fun z : Fin g → ℂ => (b, z)) z := by fun_prop
  exact (DifferentiableAt.comp z hd hi).differentiableWithinAt

theorem isDerivAt0_pt {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ}
    {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}
    (e : Flat.FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (Mz : LieModel G (spMap (ψ b)) (Fin g → ℂ))
    (hL : ∀ i, ((Mz.pt (Pi.single i 1)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt (Pi.single i 1)).left)) (x : Fin g → ℂ) :
    IsDerivAt0 (fun z => (e.ex b z).left) x (Mz.pt x).left := by
  have h1 : e.ex b 0 = 1 := by
    have := e.add b hb 0 0
    rw [add_zero] at this
    exact mul_eq_left.mp this.symm
  have h0 : (fun z => (e.ex b z).left) 0 = (1 : Over.mk (spMap (ψ b)) ⟶ G).left := congrArg (·.left) h1
  have hbas : ∀ i, IsDerivAt0 (fun z => (e.ex b z).left) (Pi.single i 1) (Mz.pt (Pi.single i 1)).left := fun i => by
    have h := e.diff b hb i
    have h' := hL i
    change _ ≫ _ = _ ≫ _ at h'
    rw [Category.comp_id] at h'
    rwa [← h'] at h
  have hsc : ∀ (c : ℂ) i, IsDerivAt0 (fun z => (e.ex b z).left) (c • Pi.single i 1)
      (Mz.pt (c • Pi.single i 1)).left := fun c i => by
    rw [Mz.smul]
    exact isDerivAt0_smul (hbas i) c
  have hzero : IsDerivAt0 (fun z => (e.ex b z).left) 0 (Mz.pt 0).left := by
    refine isDerivAt0_zero_of_fixed ((Mz.tan 0).trans h0.symm) ?_
    have := Mz.smul 0 0
    rw [zero_smul] at this
    exact this.symm
  have hsum : ∀ s : Finset (Fin g), IsDerivAt0 (fun z => (e.ex b z).left) (∑ i ∈ s, x i • Pi.single i 1)
      (Mz.pt (∑ i ∈ s, x i • Pi.single i 1)).left := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Mz.add]
      exact UnifCompare.isDerivAt0_mul h0 (hsc _ _) ih
  have hx : ∑ i, x i • (Pi.single i 1 : Fin g → ℂ) = x := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := hsum Finset.univ
  rwa [hx] at this

theorem isDiff_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (t : SAB H (Sp ℂ))
    (hP : IsPrincipal t) {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ t.G.left} (hφ : IsGrpPullback A t.G (𝟙 _) φ)
    {g' : ℕ} (u : HolUnif A (t.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (hA : u.IsAH Hm χ)
    {v : epsR ℂ ⟶ A} (hv : IsTangent v) {w w' : Fin g' → ℂ} (h : u.IsDiff w v) (h' : u.IsDiff w' v) : w = w' := by
  obtain ⟨hpr, ham, hk⟩ := hP
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t.G.hom) (𝟙 _) (𝟙 _) t.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (eSec t.G (default : PrimeSpectrum ℂ))
  let Q : Out.PolAV (Sp ℂ) :=
    { A := t.G, g := d, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB, ample := ham, ktriv := hk
      isAb := ⟨inferInstance, inferInstance, hpr, ‹_›⟩
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩
      sym := GlobalTheory.CechPic.sym_of_isSymmetric t.PP t.sym }
  have hφ' : IsGrpPullback A Q.A (𝟙 _) φ := hφ
  obtain ⟨-, -, -, -, t1, -, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all
    (GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL.Pol.pullPolL Q hφ') g' u Hm χ hA
  exact (t1 v hv).unique h h'

theorem isDiff_eq_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ → ∀ (Mz : LieModel t.G (spMap (ψ b)) (Fin g → ℂ)), (∀ i, ((Mz.pt (Pi.single i 1)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt (Pi.single i 1)).left)) → ∀ (x : Fin g → ℂ) (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v' : epsR ℂ ⟶ A) (w : Fin g' → ℂ), v.left ≫ P.m.φ = (Mz.pt x).left → v'.left ≫ φ = (v ≫ P.τ.q ≫ P.e.hom).left → u.IsDiff w v' → w = ℓ x := by
  intro E _ _ _ H R _ t g n M B ψ e b P A _ φ g' u Hm χ ℓ hb hφ hA hP hl Mz hL x v v' w hv hv' hw
  have Hc := P.m.cart.1
  have hex : ∀ y, ∃ s : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G, s.left ≫ P.m.φ = (e.ex b y).left := fun y =>
    ⟨Over.homMk (Hc.lift (e.ex b y).left (𝟙 _) (by simpa using Over.w (e.ex b y))) (Hc.lift_snd _ _ _),
      Hc.lift_fst _ _ _⟩
  choose s hs using hex
  have hd1 := isDerivAt0_pt e hb Mz hL x
  have hFeq : (fun z => (s z).left ≫ P.m.φ) = fun z => (e.ex b z).left := funext hs
  have hd2 : IsDerivAt0 (fun z => (s z).left) x v.left :=
    GlobalTheory.FibreDeriv.isDerivAt0_of_isPullback Hc (fun z => Over.w (s z))
      (by rw [hFeq]; exact isHolTo_slice e.hol hb) (by simpa using Over.w v) (by rw [hFeq, hv]; exact hd1)
  have : IsIso φ := hφ.1.isIso_fst_of_isIso
  have hd3 := isDerivAt0_comp_hom hd2 ((P.τ.q ≫ P.e.hom).left ≫ inv φ)
  have e1 : v.left ≫ (P.τ.q ≫ P.e.hom).left ≫ inv φ = v'.left := by
    rw [← Category.assoc, ← Over.comp_left, ← hv', Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have e2 : (fun z => (s z).left ≫ (P.τ.q ≫ P.e.hom).left ≫ inv φ) = fun z => (u.ex (ℓ z)).left :=
    funext fun z => by
      rw [← Category.assoc, ← Over.comp_left, ← hl z (s z) (hs z), Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
  rw [e1, e2] at hd3
  have hz : (u.ex (ℓ 0)).left = η[A].left := by
    rw [map_zero]
    exact GlobalTheory.CompanionTheory.Ar.Flat.PerGram.ex_zero_left u
  have htan : IsTangent v' := hd3.1.trans hz
  have hdiff : u.IsDiff (ℓ x) v' := fun U h f => by
    refine (hd3.2 U h f).trans ?_
    have hU : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
      have := tangent_open_preimage_zero hd3 U h
      simpa using this
    have hd : DifferentiableAt ℂ (fun z => valAt' (u.ex z).left U f) (ℓ.toContinuousLinearMap 0) := by
      rw [map_zero]
      exact ((u.hol U f).2 0 hU).differentiableAt ((u.hol U f).1.mem_nhds hU)
    have := fderiv_comp (𝕜 := ℂ) (0 : Fin g → ℂ) hd ℓ.toContinuousLinearMap.differentiableAt
    show fderiv ℂ ((fun z => valAt' (u.ex z).left U f) ∘ ℓ.toContinuousLinearMap) 0 x = _
    rw [this, ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv, map_zero]
    rfl
  exact isDiff_unique P.tB hP hφ u Hm χ hA htan hw hdiff

end GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixLeft
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixLeft
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isHolTo_fibreSlice {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {X : Scheme.{0}} {B : Set V} {y : V × W → (Sp ℂ ⟶ X)} (h : IsHolTo (B ×ˢ Set.univ) y)
    {b : V} (hb : b ∈ B) : IsHolTo Set.univ (fun z => y (b, z)) := by
  intro U f
  have hc : Differentiable ℂ (fun z : W => (b, z)) := by fun_prop
  refine ⟨?_, (h U f).2.comp hc.differentiableOn fun z hz => ⟨⟨hb, trivial⟩, hz.2⟩⟩
  convert (h U f).1.preimage hc.continuous using 1
  ext z
  exact ⟨fun hz => ⟨⟨hb, trivial⟩, hz.2⟩, fun hz => ⟨trivial, hz.2⟩⟩

theorem tangent_of_isGrpPullback {tB : SAB H (Sp ℂ)} (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ tB.G.left)
    (hφ : IsGrpPullback A tB.G (𝟙 _) φ) (hP : IsPrincipal tB) {g : ℕ} (u : HolUnif A (tB.PP.L.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (hu : u.IsAH Hm χ) :
    IsAbelianScheme A ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) := by
  have := tB.semi.smooth
  have := tB.semi.geomConnected
  have hAb : IsAbelianScheme tB.G := ⟨tB.semi.comm, tB.semi.smooth, hP.1, tB.semi.geomConnected⟩
  have hA : IsAbelianScheme A := by
    have := hAb.comm
    have hc : IsCommMonObj A := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hφ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hφ.2 T x y (pushPt hφ.1.w x) (pushPt hφ.1.w y) rfl rfl,
        ← hφ.2 T y x (pushPt hφ.1.w y) (pushPt hφ.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) hφ.1 hAb.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hφ.1 hAb.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hφ.1 hAb.geomConnected⟩
  have : ConnectedSpace tB.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := tB.G.hom) (𝟙 _) (𝟙 _) tB.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected tB.G.hom (eSec tB.G (default : PrimeSpectrum ℂ))
  obtain ⟨-, ws, gs', -⟩ := tB.sym
  have hL' := pull_isLB tB.PP.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let Q : Out.PolAV (Sp ℂ) :=
    { A := A, isAb := hA, g := d
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hφ.1 hd
      L := tB.PP.L.pull φ, isLB := hL'
      rigid := GlobalTheory.PolBaseChange.rigidified_pull hφ ⟨tB.PP.rig, tB.PP.rigGen⟩
      sym := GlobalTheory.PolBaseChange.sym_pull hφ fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩
      ample := relAmple_pull hφ.1 tB.PP.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) hP.2.1
      ktriv := kTriv_pull hφ tB.PP.isLB hL' hw hP.2.2 }
  obtain ⟨-, -, -, -, h₁, h₂, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all Q g u Hm χ hu
  exact ⟨hA, h₁, h₂⟩

theorem exists_isAbLift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → ∃ ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ := by
  intro E _ _ _ H R _ t g n M B ψ e b P A _ φ g' u Hm χ hb hφ hu hP
  obtain ⟨hA, h₁, h₂⟩ := tangent_of_isGrpPullback A φ hφ hP u Hm χ hu
  obtain ⟨p, hp⟩ := GlobalTheory.CMSpreadCompare.exists_pointEquiv P.m.cart (𝟙_ _) (s := spMap (ψ b)) (Category.id_comp _).symm
  obtain ⟨c, hc⟩ := GlobalTheory.CMSpreadCompare.exists_pointEquiv hφ (𝟙_ _) (s := 𝟙 _) (Category.comp_id _).symm
  letI := P.τ.grpB
  haveI : IsMonHom P.τ.q := P.τ.q_hom
  haveI : IsMonHom P.e.hom := P.e_hom
  let r : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.tB.G) := fun y => p.symm (e.ex b y) ≫ P.τ.q ≫ P.e.hom
  let G : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A) := fun y => c.symm (r y)
  have hr : ∀ z w, r (z + w) = r z * r w := fun z w => by
    simp only [r, e.add b hb, map_mul, MonObj.mul_comp]
  have hG : ∀ z w, G (z + w) = G z * G w := fun z w => by
    simp only [G, hr, map_mul]
  have hGr : ∀ y, (G y).left ≫ φ = (r y).left := fun y => by
    rw [← hc, c.apply_symm_apply]
  have hs : IsHolTo Set.univ (fun y => (p.symm (e.ex b y)).left) := by
    refine GlobalTheory.HolFibre.isHolTo_of_isPullback P.m.cart.1 ?_ ?_
    · have h := isHolTo_fibreSlice e.hol hb
      have e₁ : (fun y => (p.symm (e.ex b y)).left ≫ P.m.cm.F) = fun y => (e.ex b y).left :=
        funext fun y => by rw [← hp, p.apply_symm_apply]
      rw [e₁]
      exact h
    · have e₁ : (fun y => (p.symm (e.ex b y)).left ≫ P.tK.G.hom) = fun _ => 𝟙 (Sp ℂ) :=
        funext fun y => Over.w (p.symm (e.ex b y))
      rw [e₁]
      exact GlobalTheory.HolFibre.isHolTo_const isOpen_univ _
  have hol : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z => (G z).left) := by
    refine GlobalTheory.HolFibre.isHolTo_of_isPullback hφ.1 ?_ ?_
    · have h := GlobalTheory.CMSpreadCompare.isHolTo_postcomp hs (P.τ.q ≫ P.e.hom).left
      have e₁ : (fun y => (G y).left ≫ φ) = fun y => (p.symm (e.ex b y)).left ≫ (P.τ.q ≫ P.e.hom).left :=
        funext fun y => by rw [hGr]; rfl
      rw [e₁]
      exact h
    · have e₁ : (fun y => (G y).left ≫ A.hom) = fun _ => 𝟙 (Sp ℂ) := funext fun y => Over.w (G y)
      rw [e₁]
      exact GlobalTheory.HolFibre.isHolTo_const isOpen_univ _
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hA _ g' g u h₁ h₂ G hG hol
  refine ⟨F, fun y s hs' => ?_⟩
  have es : s = p.symm (e.ex b y) := by
    rw [eq_comm, MulEquiv.symm_apply_eq]
    exact Over.OverMorphism.ext ((hp s).trans hs').symm
  rw [hF, hGr, es]

end GlobalTheory.CompanionTheory.Ar.QuotLoc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixLeftStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hol_unif_period_matrix_left : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → ∃ ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_isAbLift | exact GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_isAbLift | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_isAbLift <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartFactorsThrough
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartFactorsThrough
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.AbPartPull

theorem exists_sabMap_tK : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (m : SABMap t' t f) (K : Type) [Field K] (z : Sp K ⟶ S') (P : AbPart t (z ≫ f)), ∃ m' : SABMap P.tK t' z, m'.φ ≫ m.φ = P.m.φ := by
  intro E _ _ _ H S S' t' t f m K _ z P
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ t t' P.tK f z m P.m
  exact ⟨n, hn.symm⟩

end GlobalTheory.CompanionTheory.Ar.AbPartPull
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartFactorsThroughStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_part_factors_through : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (m : SABMap t' t f) (K : Type) [Field K] (z : Sp K ⟶ S') (P : AbPart t (z ≫ f)), ∃ m' : SABMap P.tK t' z, m'.φ ≫ m.φ = P.m.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AbPartPull.exists_sabMap_tK | exact GlobalTheory.CompanionTheory.Ar.AbPartPull.exists_sabMap_tK | (intros; apply GlobalTheory.CompanionTheory.Ar.AbPartPull.exists_sabMap_tK <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDvrThroughDiscPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDvrThroughDiscPoint
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.Flat

section Curve

variable {R : Type} [CommRing R] {n : ℕ} {ψ : (Fin n → ℂ) → (R →+* ℂ)} {z : Fin n → ℂ}

def diagLine (z : Fin n → ℂ) (T : ℂ) : Fin n → ℂ := fun i => z i + T

theorem diagLine_zero (z : Fin n → ℂ) : diagLine z 0 = z := by
  funext i; simp [diagLine]

theorem diagLine_mem_ball (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) {T : ℂ}
    (hT : T ∈ Metric.ball (0 : ℂ) (1 - ‖z‖)) : diagLine z T ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff] at hT ⊢
  rw [pi_norm_lt_iff one_pos]
  intro i
  have h₁ := norm_le_pi_norm z i
  calc ‖z i + T‖ ≤ ‖z i‖ + ‖T‖ := norm_add_le _ _
    _ < 1 := by linarith

theorem analyticOnNhd_diagLine (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) (x : R) :
    AnalyticOnNhd ℂ (fun T => ψ (diagLine z T) x) (Metric.ball (0 : ℂ) (1 - ‖z‖)) := by
  have hl : DifferentiableOn ℂ (diagLine z) (Metric.ball (0 : ℂ) (1 - ‖z‖)) :=
    (differentiable_pi.2 fun i => (differentiable_const (z i)).add differentiable_id).differentiableOn
  exact ((h.2 x).comp hl fun T hT => diagLine_mem_ball hz hT).analyticOnNhd Metric.isOpen_ball

theorem zero_mem_ball_norm (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (1 - ‖z‖) := by
  have := mem_ball_zero_iff.1 hz
  simpa using this

theorem analyticAt_diagLine (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) (x : R) :
    AnalyticAt ℂ (fun T => ψ (diagLine z T) x) 0 :=
  analyticOnNhd_diagLine h hz x 0 (zero_mem_ball_norm hz)

def taylorHom (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) : R →+* PowerSeries ℂ where
  toFun x := Formalism.L2.Th1.F.taylor0 (fun T => ψ (diagLine z T) x)
  map_one' := by
    simp only [map_one]
    rw [Formalism.L2.Th1.F.Taylor.taylor0_const, map_one]
  map_zero' := by
    simp only [map_zero]
    rw [Formalism.L2.Th1.F.Taylor.taylor0_const, map_zero]
  map_mul' x y := by
    simp only [map_mul]
    exact Formalism.L2.Th1.F.Taylor.taylor0_mul (analyticAt_diagLine h hz x) (analyticAt_diagLine h hz y)
  map_add' x y := by
    simp only [map_add (f := _)]
    exact Formalism.L2.Th1.F.Taylor.taylor0_add (analyticAt_diagLine h hz x) (analyticAt_diagLine h hz y)

theorem constantCoeff_comp_taylorHom (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    (PowerSeries.constantCoeff (R := ℂ)).comp (taylorHom h hz) = ψ z := by
  ext x
  have e := Formalism.L2.Th1.F.Taylor.coeff_taylor0 (fun T => ψ (diagLine z T) x) 0
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, diagLine_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] at e
  exact e

theorem eq_zero_of_taylorHom (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) {x : R}
    (hx : taylorHom h hz x = 0) {T : ℂ} (hT : T ∈ Metric.ball (0 : ℂ) (1 - ‖z‖)) : ψ (diagLine z T) x = 0 := by
  have h₀ : Formalism.L2.Th1.F.taylor0 (fun T => ψ (diagLine z T) x) = Formalism.L2.Th1.F.taylor0 (fun _ => (0 : ℂ)) := by
    rw [Formalism.L2.Th1.F.Taylor.taylor0_const, map_zero]
    exact hx
  have he := Formalism.L2.Th1.F.Taylor.taylor0_inj (analyticAt_diagLine h hz x) analyticAt_const h₀
  exact (analyticOnNhd_diagLine h hz x).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected (zero_mem_ball_norm hz) he hT

theorem exists_diagLine_mem_punct (a : ℕ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    ∃ T ∈ Metric.ball (0 : ℂ) (1 - ‖z‖), diagLine z T ∈ punct n a 1 := by
  have hinf : (Metric.ball (0 : ℂ) (1 - ‖z‖)).Infinite :=
    infinite_of_mem_nhds 0 (Metric.isOpen_ball.mem_nhds (zero_mem_ball_norm hz))
  obtain ⟨T, hT, hn⟩ := hinf.exists_notMem_finset (Finset.univ.image fun i : Fin n => -z i)
  refine ⟨T, hT, diagLine_mem_ball hz hT, fun i _ he => hn ?_⟩
  refine Finset.mem_image.2 ⟨i, Finset.mem_univ _, ?_⟩
  have : z i + T = 0 := he
  linear_combination -this

end Curve

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem range_jK_taylorHom_subset {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : Flat.BdryChart Xo σ n a)
    {z : Fin n → ℂ} (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    Set.range (Out.jK (PowerSeries ℂ) ≫ spMap (taylorHom C.hol hz)) ⊆ Set.range C.j := by
  have := C.j_open
  rintro _ ⟨q, rfl⟩
  obtain ⟨T, hT, hp⟩ := exists_diagLine_mem_punct a hz
  obtain ⟨s⟩ : Nonempty (Sp ℂ) := inferInstance
  have hw : spMap (C.ψ (diagLine z T)) s ∈ Set.range C.j :=
    ⟨C.pt (diagLine z T) s, by rw [← (C.pt_eq _ hp).1, Scheme.Hom.comp_apply]⟩
  refine Specializes.mem_open ?_ C.j.isOpenEmbedding.isOpen_range hw
  refine (PrimeSpectrum.le_iff_specializes _ _).1 fun x hx => ?_
  have hq : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top
  rw [Scheme.Hom.comp_apply] at hx
  have h₁ : algebraMap (PowerSeries ℂ) (FractionRing (PowerSeries ℂ)) (taylorHom C.hol hz x) ∈ q.asIdeal := hx
  rw [hq, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h₁
  have h₂ : C.ψ (diagLine z T) x = 0 := eq_zero_of_taylorHom C.hol hz h₁ hT
  show C.ψ (diagLine z T) x ∈ s.asIdeal
  rw [h₂]
  exact Ideal.zero_mem _

section Pulled

open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem polAt_of_pulled {S S' X : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {K : Type} [Field K] {tK : SAB H (Sp K)} {j : Sp K ⟶ S} (mK : SABMap tK t j)
    {u : SAB H X} {x : Sp K ⟶ X} (mx : SABMap tK u x) (hp : IsProper u.G.hom) (ha : Out.RelAmple u.G u.PP.L)
    (hk : Out.KTriv u.G u.PP.L) (j' : Sp K ⟶ S') (h : j' ≫ f = j) : GlobalTheory.LN.PolAt t' j' := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull j' t'
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₂
  have cancel : ∀ (t₂ : SAB H (Sp K)) (p : Sp K ⟶ S) (_ : p = 𝟙 _ ≫ j) (_ : SABMap t₂ t p),
      Nonempty (SABMap t₂ u (𝟙 _ ≫ x)) := by
    intro t₂ p hp n
    subst hp
    exact ⟨(sabComp pullCubComp E H _ _ _ _ _ _ _ _ mx
      (sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mK n).choose).choose⟩
  obtain ⟨m₃⟩ := cancel _ _ (h.trans (Category.id_comp _).symm) n
  have h₂ : LBIso PP'.L (t'.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (u.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull t'.PP.isLB (pullback.fst t'.G.hom j')
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 hp,
    amplePt _ _ (𝟙 _ ≫ x) _ _ m₃.φ m₃.cart _ _ u.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull u.PP.isLB _) h₂.symm h₃) ha hk⟩

end Pulled

theorem exists_curve_through_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (z : Fin n → ℂ), z ∈ Metric.ball (0 : Fin n → ℂ) 1 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : C.R →+* V) (r : V →+* ℂ) (tV : SAB H (Sp V)) (_ : SABMap tV C.t (spMap f)), GlobalTheory.LN.CDvr V ∧ Function.Surjective r ∧ RingHom.ker r = IsLocalRing.maximalIdeal V ∧ r.comp f = C.ψ z ∧ GlobalTheory.LN.PolAt tV (Out.jK V) := by
  intro E _ _ _ H D l Xo σ n a C z hz
  have := C.j_open
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (taylorHom C.hol hz)) C.t
  have hc : GlobalTheory.LN.CDvr (PowerSeries ℂ) :=
    ⟨inferInstance, by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance, algebraRat.charZero _⟩
  have hsurj : Function.Surjective (PowerSeries.constantCoeff (R := ℂ)) := fun c =>
    ⟨PowerSeries.C c, by simp⟩
  refine ⟨PowerSeries ℂ, inferInstance, inferInstance, inferInstance, taylorHom C.hol hz,
    PowerSeries.constantCoeff (R := ℂ), _, m, hc, hsurj, ?_, constantCoeff_comp_taylorHom C.hol hz, ?_⟩
  · have := RingHom.ker_isMaximal_of_surjective _ hsurj
    exact IsLocalRing.eq_maximalIdeal this
  · have hr := range_jK_taylorHom_subset C hz
    let y := IsOpenImmersion.lift C.j _ hr
    have hy : y ≫ C.j = Out.jK (PowerSeries ℂ) ≫ spMap (taylorHom C.hol hz) := IsOpenImmersion.lift_fac _ _ _
    obtain ⟨_, _, _, _, _, m₀, -⟩ := sabPull Out.CubePf.cubePull y C.tV
    obtain ⟨mK, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m₁ m₀
    obtain ⟨mx, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m₂ m₀
    exact polAt_of_pulled m mK mx Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (Out.jK (PowerSeries ℂ)) hy.symm

end GlobalTheory.CompanionTheory.Ar.QuotLoc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDvrThroughDiscPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_through_disc_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (z : Fin n → ℂ), z ∈ Metric.ball (0 : Fin n → ℂ) 1 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : C.R →+* V) (r : V →+* ℂ) (tV : SAB H (Sp V)) (_ : SABMap tV C.t (spMap f)), GlobalTheory.LN.CDvr V ∧ Function.Surjective r ∧ RingHom.ker r = IsLocalRing.maximalIdeal V ∧ r.comp f = C.ψ z ∧ GlobalTheory.LN.PolAt tV (Out.jK V) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_curve_through_point | exact GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_curve_through_point | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_curve_through_point <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExpLogCoverBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExpLogCoverBound
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.Flat _root_.Metric

theorem isHolTo_comp {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']
    {X : Scheme.{0}} {A : Set V'} {y : V' → (Sp ℂ ⟶ X)} (hy : IsHolTo A y) {B' : Set V} (hB' : IsOpen B')
    {φ : V → V'} (hφ : DifferentiableOn ℂ φ B') (hmap : Set.MapsTo φ B' A) : IsHolTo B' (fun b => y (φ b)) := by
  intro U f
  obtain ⟨h₁, h₂⟩ := hy U f
  have hset : {b ∈ B' | ⊤ ≤ y (φ b) ⁻¹ᵁ U} = B' ∩ φ ⁻¹' {v ∈ A | ⊤ ≤ y v ⁻¹ᵁ U} := by
    ext b
    constructor
    · rintro ⟨hb, hU⟩
      exact ⟨hb, hmap hb, hU⟩
    · rintro ⟨hb, _, hU⟩
      exact ⟨hb, hU⟩
  rw [hset]
  refine ⟨hφ.continuousOn.isOpen_inter_preimage hB' h₁, ?_⟩
  exact h₂.comp (hφ.mono Set.inter_subset_left) (fun b hb => hb.2)

section Exp

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {g n : ℕ}
  {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}

theorem ex_zero_eq_one (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) : e.ex b 0 = 1 := by
  have h := e.add b hb 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem ex_pow_eq (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (z : Fin g → ℂ) (N : ℕ) :
    e.ex b z ^ N = e.ex b ((N : ℂ) • z) := by
  induction N with
  | zero => simp [ex_zero_eq_one e hb]
  | succ k ih =>
    rw [pow_succ, ih, ← e.add b hb]
    congr 1
    push_cast
    rw [add_smul, one_smul]

theorem ex_inv_smul_pow (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) {s : Fin g → ℂ} (hs : s ∈ e.per b)
    {N : ℕ} (hN : 0 < N) : e.ex b ((N : ℂ)⁻¹ • s) ^ N = 1 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [ex_pow_eq e hb, smul_smul, mul_inv_cancel₀ hN', one_smul]
  exact hs

theorem hol_ex_comp (e : FamExp G M B ψ) {B' : Set (Fin n → ℂ)} (hB' : IsOpen B') (hsub : B' ⊆ B)
    {s : (Fin n → ℂ) → (Fin g → ℂ)} (hs : DifferentiableOn ℂ s B') :
    IsHolTo B' (fun b => (e.ex b (s b)).left) :=
  isHolTo_comp e.hol hB' (φ := fun b => (b, s b)) (differentiableOn_id.prodMk hs) (fun _ hb => ⟨hsub hb, trivial⟩)

theorem period_of_tendsto (e : FamExp G M B ψ) (hsep : IsSeparated G.hom) (hhol : IsHolPts B ψ)
    {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ B) {bs : ℕ → Fin n → ℂ} {q : ℕ → Fin g → ℂ} {p : Fin g → ℂ}
    (hb : Tendsto bs atTop (𝓝 b₀)) (hq : Tendsto q atTop (𝓝 p))
    (hper : ∀ m, q m ∈ e.per (bs m)) : p ∈ e.per b₀ := by
  by_cases hfreq : ∃ᶠ m in atTop, bs m = b₀
  · obtain ⟨Γ₀, hΓ, hdisc, -, -⟩ := GlobalTheory.T.period_lattice_discrete_free R G g n M B ψ e b₀ hb₀
    have hcl : IsClosed (Γ₀ : Set (Fin g → ℂ)) := by
      haveI := hdisc
      exact (Γ₀.toAddSubgroup).isClosed_of_discreteTopology
    rw [hΓ] at hcl
    refine hcl.mem_of_frequently_of_tendsto (hfreq.mono fun m hm => ?_) hq
    rw [← hm]
    exact hper m
  · have hne : ∀ᶠ m in atTop, bs m ≠ b₀ := not_frequently.mp hfreq
    classical
    let s : (Fin n → ℂ) → (Fin g → ℂ) := fun b =>
      if h : b ≠ b₀ ∧ ∃ m, bs m = b then q (Nat.find h.2) else p
    have hs₀ : s b₀ = p := dif_neg (fun h => h.1 rfl)
    have hcont : ContinuousAt s b₀ := by
      rw [ContinuousAt, hs₀]
      intro U hU
      obtain ⟨K, hK⟩ := eventually_atTop.mp (hq hU)
      have hV : ∀ᶠ b in 𝓝 b₀, ∀ k ∈ Finset.range K, bs k ≠ b₀ → b ≠ bs k := by
        rw [Filter.eventually_all_finset]
        intro k _
        by_cases hk : bs k = b₀
        · exact Eventually.of_forall fun _ h => absurd hk h
        · filter_upwards [eventually_ne_nhds (Ne.symm hk)] with b hb' _ using hb'
      refine Filter.mem_map.mpr ?_
      filter_upwards [hV] with b hbV
      show s b ∈ U
      by_cases h : b ≠ b₀ ∧ ∃ m, bs m = b
      · have hsb : s b = q (Nat.find h.2) := dif_pos h
        rw [hsb]
        have hspec : bs (Nat.find h.2) = b := Nat.find_spec h.2
        refine hK _ ?_
        by_contra hlt
        refine hbV _ (Finset.mem_range.mpr (not_le.mp hlt)) ?_ hspec.symm
        rw [hspec]
        exact h.1
      · have hsb : s b = p := dif_neg h
        rw [hsb]
        exact mem_of_mem_nhds hU
    have hfr : ∃ᶠ b in 𝓝 b₀, b ∈ B ∧ s b ∈ e.per b := by
      refine hb.frequently (Eventually.frequently ?_)
      filter_upwards [hne, hb (hhol.1.mem_nhds hb₀)] with m hm hmB
      refine ⟨hmB, ?_⟩
      have h : bs m ≠ b₀ ∧ ∃ k, bs k = bs m := ⟨hm, m, rfl⟩
      obtain ⟨k, hk, hsk⟩ : ∃ k, bs k = bs m ∧ s (bs m) = q k := ⟨Nat.find h.2, Nat.find_spec h.2, dif_pos h⟩
      rw [hsk, ← hk]
      exact hper k
    have := GlobalTheory.T.period_set_closed R G g n M B ψ e hsep hhol b₀ hb₀ s hcont hfr
    rwa [hs₀] at this

end Exp

section Core

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem limit_core {R : Type} [CommRing R] (t : SAB H (Sp R)) {g n : ℕ} {M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)}
    {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)} (e : FamExp t.G M B ψ) (hhol : IsHolPts B ψ)
    {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ B) {bs : ℕ → Fin n → ℂ} (hbs : Tendsto bs atTop (𝓝 b₀))
    {Λ : Type} [AddCommGroup Λ] (Ef : Λ → Λ → ℤ) (P : ℕ → Λ →+ (Fin g → ℂ))
    (hlink : ∀ m, (∀ p, p ∈ e.per (bs m) ↔ ∃ x, P m x = p) ∧ ∀ (N : ℕ) (ζ : ℂˣ) (x x' : Λ), 0 < N →
      GlobalTheory.UU.CubWeil t.cub N (e.ex (bs m) ((N : ℂ)⁻¹ • P m x)) (e.ex (bs m) ((N : ℂ)⁻¹ • P m x')) (unitOn ζ) →
      (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Ef x x' : ℤ) : ℂ) / N))
    (W : Submodule ℤ Λ) (per : W →+ (Fin g → ℂ))
    (hper : ∀ x : W, Tendsto (fun m => P m x) atTop (𝓝 (per x)))
    (h4 : ∀ (x : ℕ → Λ) (p : Fin g → ℂ), Tendsto (fun m => P m (x m)) atTop (𝓝 p) →
      ∃ x₀ : W, p = per x₀ ∧ ∀ᶠ m in atTop, x m = x₀) :
    (∀ x : W, per x ∈ e.per b₀) ∧ (∀ p ∈ e.per b₀, ∃ x : W, per x = p) ∧
      ∀ (N : ℕ) (ζ : ℂˣ) (x x' : W), 0 < N →
        (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Ef x x' : ℤ) : ℂ) / N) →
        GlobalTheory.UU.CubWeil t.cub N (e.ex b₀ ((N : ℂ)⁻¹ • per x)) (e.ex b₀ ((N : ℂ)⁻¹ • per x')) (unitOn ζ) := by
  have hsep : IsSeparated t.G.hom := t.semi.separated
  have hP : ∀ m x, P m x ∈ e.per (bs m) := fun m x => ((hlink m).1 _).2 ⟨x, rfl⟩
  have spread : ∀ p ∈ e.per b₀, ∃ (ε : ℝ) (s : (Fin n → ℂ) → (Fin g → ℂ)) (y : ℕ → Λ), 0 < ε ∧ ball b₀ ε ⊆ B ∧
      DifferentiableOn ℂ s (ball b₀ ε) ∧ s b₀ = p ∧ (∀ b ∈ ball b₀ ε, s b ∈ e.per b) ∧
      (∀ m, bs m ∈ ball b₀ ε → P m (y m) = s (bs m)) ∧ Tendsto (fun m => P m (y m)) atTop (𝓝 p) := by
    intro p hp
    obtain ⟨ε, s, hε, hsub, hsd, hs₀, hsper⟩ := GlobalTheory.T.period_holomorphic_continuation R t.G g n M B ψ e hhol.1 b₀ hb₀ p hp
    have hy : ∀ m, ∃ y : Λ, bs m ∈ ball b₀ ε → P m y = s (bs m) := by
      intro m
      by_cases hm : bs m ∈ ball b₀ ε
      · obtain ⟨y, hy⟩ := ((hlink m).1 _).1 (hsper _ hm)
        exact ⟨y, fun _ => hy⟩
      · exact ⟨0, fun h => absurd h hm⟩
    choose y hy using hy
    refine ⟨ε, s, y, hε, hsub, hsd, hs₀, hsper, hy, ?_⟩
    have hc : ContinuousAt s b₀ := hsd.continuousOn.continuousAt (ball_mem_nhds b₀ hε)
    have ht : Tendsto (fun m => s (bs m)) atTop (𝓝 p) := by
      have := hc.tendsto.comp hbs
      rwa [hs₀] at this
    refine ht.congr' ?_
    filter_upwards [hbs (ball_mem_nhds b₀ hε)] with m hm
    exact (hy m hm).symm
  have hinj : ∀ x : W, per x = 0 → x = 0 := by
    intro x hx
    classical
    let y : ℕ → Λ := fun m => if Even m then (x : Λ) else 0
    have hy : Tendsto (fun m => P m (y m)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun m => P m x) atTop (𝓝 0) := by
        have := hper x
        rwa [hx] at this
      refine squeeze_zero_norm (fun m => ?_) (tendsto_zero_iff_norm_tendsto_zero.mp h0)
      by_cases hm : Even m
      · simp [y, hm]
      · simp [y, hm]
    obtain ⟨x₀, -, hev⟩ := h4 y 0 hy
    obtain ⟨K, hK⟩ := eventually_atTop.mp hev
    have h1 : (x : Λ) = x₀ := by
      have := hK (2 * K) (by omega)
      simpa [y] using this
    have h2 : (0 : Λ) = x₀ := by
      have := hK (2 * K + 1) (by omega)
      have hodd : ¬ Even (2 * K + 1) := by
        rw [Nat.not_even_iff_odd]
        exact ⟨K, rfl⟩
      simpa [y, hodd] using this
    exact Subtype.ext (h1.trans h2.symm)
  have hval : ∀ (x : W) (y : ℕ → Λ), Tendsto (fun m => P m (y m)) atTop (𝓝 (per x)) →
      ∀ᶠ m in atTop, y m = x := by
    intro x y hy
    obtain ⟨x₀, hp, hev⟩ := h4 y (per x) hy
    have h0 : x - x₀ = 0 := hinj _ (by rw [map_sub, hp, sub_self])
    have hxx : x = x₀ := sub_eq_zero.mp h0
    filter_upwards [hev] with m hm
    rw [hm, hxx]
  refine ⟨fun x => period_of_tendsto e hsep hhol hb₀ hbs (hper x) (fun m => hP m x), ?_, ?_⟩
  · intro p hp
    obtain ⟨ε, s, y, -, -, -, -, -, -, ht⟩ := spread p hp
    obtain ⟨x₀, h, -⟩ := h4 y p ht
    exact ⟨x₀, h.symm⟩
  · intro N ζ x x' hN hζ
    have hpx := period_of_tendsto e hsep hhol hb₀ hbs (hper x) (fun m => hP m x)
    have hpx' := period_of_tendsto e hsep hhol hb₀ hbs (hper x') (fun m => hP m x')
    obtain ⟨ε, s, y, hε, hsub, hsd, hs₀, hsper, hy, ht⟩ := spread _ hpx
    obtain ⟨ε', s', y', hε', hsub', hsd', hs₀', hsper', hy', ht'⟩ := spread _ hpx'
    have hδ : 0 < min ε ε' := lt_min hε hε'
    have hl : ball b₀ (min ε ε') ⊆ ball b₀ ε := ball_subset_ball (min_le_left _ _)
    have hr : ball b₀ (min ε ε') ⊆ ball b₀ ε' := ball_subset_ball (min_le_right _ _)
    let X : ∀ b, Over.mk (spMap (ψ b)) ⟶ t.G := fun b => e.ex b ((N : ℂ)⁻¹ • s b)
    let X' : ∀ b, Over.mk (spMap (ψ b)) ⟶ t.G := fun b => e.ex b ((N : ℂ)⁻¹ • s' b)
    have hX : IsHolTo (ball b₀ (min ε ε')) (fun b => (X b).left) :=
      hol_ex_comp e isOpen_ball (hl.trans hsub) (s := fun b => (N : ℂ)⁻¹ • s b) ((hsd.mono hl).const_smul ((N : ℂ)⁻¹))
    have hX' : IsHolTo (ball b₀ (min ε ε')) (fun b => (X' b).left) :=
      hol_ex_comp e isOpen_ball (hl.trans hsub) (s := fun b => (N : ℂ)⁻¹ • s' b) ((hsd'.mono hr).const_smul ((N : ℂ)⁻¹))
    have htors : ∀ b ∈ ball b₀ (min ε ε'), X b ^ N = 1 ∧ X' b ^ N = 1 ∧
        (X b).left ≫ t.G.hom = (X' b).left ≫ t.G.hom := fun b hb =>
      ⟨ex_inv_smul_pow e (hsub (hl hb)) (hsper b (hl hb)) hN,
        ex_inv_smul_pow e (hsub (hl hb)) (hsper' b (hr hb)) hN, (Over.w (X b)).trans (Over.w (X' b)).symm⟩
    have hb₀' : b₀ ∈ ball b₀ (min ε ε') := mem_ball_self hδ
    obtain ⟨u, hu, -⟩ := GlobalTheory.UU.existsUnique_cubWeil t.cub (htors b₀ hb₀').1 (htors b₀ hb₀').2.1
    obtain ⟨ζ₁, rfl⟩ : ∃ z : ℂˣ, unitOn z = u :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.toMonoidHom u, Units.ext (by simp [unitOn])⟩
    have hconst := GlobalTheory.T.torsion_section_eq_of_connected (Sp R) t.G t.PP t.cub n N (ball b₀ (min ε ε')) (fun b => spMap (ψ b)) X X' ζ₁ b₀ hN
      isOpen_ball (convex_ball _ _).isPreconnected hb₀' hX hX' htors hu
    have hbm : ∀ᶠ m in atTop, bs m ∈ ball b₀ (min ε ε') := hbs (ball_mem_nhds b₀ hδ)
    obtain ⟨m, hm, hym, hym'⟩ := (hbm.and ((hval x y ht).and (hval x' y' ht'))).exists
    have hm1 := hconst (bs m) hm
    have e1 : s (bs m) = P m x := by rw [← hy m (hl hm), hym]
    have e2 : s' (bs m) = P m x' := by rw [← hy' m (hr hm), hym']
    have hc : GlobalTheory.UU.CubWeil t.cub N (e.ex (bs m) ((N : ℂ)⁻¹ • P m x)) (e.ex (bs m) ((N : ℂ)⁻¹ • P m x'))
        (unitOn ζ₁) := by
      rw [← e1, ← e2]
      exact hm1
    have hζ₁ : ζ₁ = ζ := Units.ext (((hlink m).2 N ζ₁ x x' hN hc).trans hζ.symm)
    rw [← hζ₁, ← hs₀, ← hs₀']
    exact hu

end Core

theorem limit_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n a : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (ρ : ℝ) (e : Flat.FamExp t.G M (Metric.ball 0 ρ) ψ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ), 0 < ρ → ρ ≤ 1 → Flat.IsHolPts (Metric.ball 0 ρ) ψ → (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, (∀ p, p ∈ e.per ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ↔ ∃ x, L.P w x = p) ∧ ∀ (N : ℕ) (ζ : ℂˣ) (x x' : Λ), 0 < N → GlobalTheory.UU.CubWeil t.cub N (e.ex ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ((N : ℂ)⁻¹ • L.P w x)) (e.ex ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ((N : ℂ)⁻¹ • L.P w x')) (unitOn ζ) → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ (ws : ℕ → Fin n → ℂ) (W : Submodule ℤ Λ) (per : W →+ (Fin g → ℂ)), (∀ m, ws m ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le) → Tendsto (fun m => GroundTheory.Heights₂.Heights.Regular.expCover a (ws m)) atTop (𝓝 z) → (∀ x : W, Tendsto (fun m => L.P (ws m) x) atTop (𝓝 (per x))) → (∀ (x : ℕ → Λ) (p : Fin g → ℂ), Tendsto (fun m => L.P (ws m) (x m)) atTop (𝓝 p) → ∃ x₀ : W, p = per x₀ ∧ ∀ᶠ m in atTop, x m = x₀) → (∀ x : W, per x ∈ e.per ((ρ : ℂ) • z)) ∧ (∀ p ∈ e.per ((ρ : ℂ) • z), ∃ x : W, per x = p) ∧ ∀ (N : ℕ) (ζ : ℂˣ) (x x' : W), 0 < N → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N) → GlobalTheory.UU.CubWeil t.cub N (e.ex ((ρ : ℂ) • z) ((N : ℂ)⁻¹ • per x)) (e.ex ((ρ : ℂ) • z) ((N : ℂ)⁻¹ • per x')) (unitOn ζ) := by
  intro E _ _ _ H R _ t g n a M ψ ρ e Λ _ L hρ _ hhol hlink z hz ws W per hws hlim hper h4
  have hb₀ : (ρ : ℂ) • z ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
    rw [mem_ball_zero_iff, norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    have : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    nlinarith
  exact limit_core t e hhol hb₀ (hlim.const_smul (ρ : ℂ)) (fun x y => L.E x y) (fun m => L.P (ws m))
    (fun m => hlink _ (hws m)) W per hper h4

end GlobalTheory.CompanionTheory.Ar.QuotLoc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExpLogCoverBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_exp_log_cover_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n a : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (ρ : ℝ) (e : Flat.FamExp t.G M (Metric.ball 0 ρ) ψ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ), 0 < ρ → ρ ≤ 1 → Flat.IsHolPts (Metric.ball 0 ρ) ψ → (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, (∀ p, p ∈ e.per ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ↔ ∃ x, L.P w x = p) ∧ ∀ (N : ℕ) (ζ : ℂˣ) (x x' : Λ), 0 < N → GlobalTheory.UU.CubWeil t.cub N (e.ex ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ((N : ℂ)⁻¹ • L.P w x)) (e.ex ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ((N : ℂ)⁻¹ • L.P w x')) (unitOn ζ) → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ (ws : ℕ → Fin n → ℂ) (W : Submodule ℤ Λ) (per : W →+ (Fin g → ℂ)), (∀ m, ws m ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le) → Tendsto (fun m => GroundTheory.Heights₂.Heights.Regular.expCover a (ws m)) atTop (𝓝 z) → (∀ x : W, Tendsto (fun m => L.P (ws m) x) atTop (𝓝 (per x))) → (∀ (x : ℕ → Λ) (p : Fin g → ℂ), Tendsto (fun m => L.P (ws m) (x m)) atTop (𝓝 p) → ∃ x₀ : W, p = per x₀ ∧ ∀ᶠ m in atTop, x m = x₀) → (∀ x : W, per x ∈ e.per ((ρ : ℂ) • z)) ∧ (∀ p ∈ e.per ((ρ : ℂ) • z), ∃ x : W, per x = p) ∧ ∀ (N : ℕ) (ζ : ℂˣ) (x x' : W), 0 < N → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N) → GlobalTheory.UU.CubWeil t.cub N (e.ex ((ρ : ℂ) • z) ((N : ℂ)⁻¹ • per x)) (e.ex ((ρ : ℂ) • z) ((N : ℂ)⁻¹ • per x')) (unitOn ζ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotLoc.limit_lattice | exact GlobalTheory.CompanionTheory.Ar.QuotLoc.limit_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotLoc.limit_lattice <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalNearBoundary
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc

theorem exists_pull_form {g g' : ℕ} (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (Hm : Matrix (Fin g') (Fin g') ℂ) (hH : Hm.IsHermitian) :
    ∃ Hb : Matrix (Fin g) (Fin g) ℂ, Hb.IsHermitian ∧ (∀ x y, x ⬝ᵥ Hb *ᵥ star y = ℓ x ⬝ᵥ Hm *ᵥ star (ℓ y)) ∧
      ∀ y, ℓ y = 0 → Hb *ᵥ star y = 0 := by
  set Lm := LinearMap.toMatrix' ℓ with hLm
  have h1 : ∀ x, Lm *ᵥ x = ℓ x := fun x => LinearMap.toMatrix'_mulVec ℓ x
  have h2 : ∀ y, (Lm.map star) *ᵥ star y = star (ℓ y) := fun y => by
    rw [← h1]
    ext i
    simp [Matrix.mulVec, dotProduct]
  have h3 : ∀ y, (Lmᵀ * Hm * Lm.map star) *ᵥ star y = Lmᵀ *ᵥ (Hm *ᵥ star (ℓ y)) := fun y => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2]
  refine ⟨Lmᵀ * Hm * Lm.map star, ?_, fun x y => ?_, fun y hy => ?_⟩
  · have e1 : (Lm.map star)ᴴ = Lmᵀ := by ext i j; simp [Matrix.conjTranspose_apply]
    have e2 : (Lmᵀ)ᴴ = Lm.map star := by ext i j; simp [Matrix.conjTranspose_apply]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, e1, e2, hH.eq, Matrix.mul_assoc]
  · rw [h3, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h1]
  · rw [h3, hy]
    simp

theorem eq_of_forall_exp {d e : ℝ} (h : ∀ N : ℕ, 0 < N →
    Complex.exp (-(2 * Real.pi * Complex.I) * (d : ℂ) / N) = Complex.exp (-(2 * Real.pi * Complex.I) * (e : ℂ) / N)) :
    d = e := by
  obtain ⟨N, hN⟩ := exists_nat_gt |d - e|
  have hN0 : 0 < N + 1 := Nat.succ_pos N
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h (N + 1) hN0)
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hNc : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have h1 : ((d - e : ℝ) : ℂ) = (((-k * (N + 1 : ℕ) : ℤ) : ℝ) : ℂ) := by
    push_cast
    field_simp at hk
    push_cast at hk
    linear_combination -hk
  have h2 : d - e = ((-k * (N + 1 : ℕ) : ℤ) : ℝ) := by exact_mod_cast h1
  by_contra hne
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hne
    simpa [sub_eq_zero] using h2
  have h3 : (N + 1 : ℝ) ≤ |d - e| := by
    rw [h2]
    have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
    have h4 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast this
    push_cast
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)]
    nlinarith [abs_nonneg (k : ℝ), (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  linarith

theorem eq_zero_of_im_lattice {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (Λ : Submodule ℤ (Fin g → ℂ))
    (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) (p : Fin g → ℂ)
    (h : ∀ q ∈ Λ, (p ⬝ᵥ Hm *ᵥ star q).im = 0) : p = 0 := by
  have key : ∀ w : Fin g → ℂ, (p ⬝ᵥ Hm *ᵥ star w).im = 0 := by
    intro w
    have hw : w ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := by rw [hfull]; trivial
    induction hw using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => simp
    | add x y _ _ hx hy => simp [star_add, Matrix.mulVec_add, dotProduct_add, hx, hy]
    | smul c x _ hx =>
      have e : star (c • x) = (c : ℂ) • star x := by
        ext i; simp
      rw [e, Matrix.mulVec_smul, dotProduct_smul]
      simp [hx]
  by_contra hp
  have h1 := hpos p hp
  have h2 := key (Complex.I • p)
  have e : star (Complex.I • p) = (-Complex.I) • star p := by
    ext i; simp
  rw [e, Matrix.mulVec_smul, dotProduct_smul] at h2
  simp at h2
  linarith

theorem abPart_principal_and_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → ∃ ρ K : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ P : AbPart C.t (spMap (C.ψ z)), IsPrincipal P.tB ∧ ∀ (Mz : LieModel C.t.G (spMap (C.ψ z)) (Fin C.g → ℂ)), (∀ i, ((Mz.pt (Pi.single i 1)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ z)) ≫ (C.M.pt (Pi.single i 1)).left)) → ∀ (x : Fin C.g → ℂ) (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (c : ℂ), v.left ≫ P.m.φ = (Mz.pt x).left → HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ K * ∑ i, ‖x i‖ ^ 2 := by
  intro E _ _ _ H D l Xo σ n a C hpq hσ
  obtain ⟨ρ₀, Λ, _, L, e, hρ0, hρ1, hlink⟩ := GlobalTheory.T.exists_log_period_family E H D l Xo σ n a C hpq hσ
  obtain ⟨ρ₁, Cb, h1, h2, hL⟩ := GlobalTheory.T.log_period_limit n a C.g Λ L
  have hol : Flat.IsHolPts (Metric.ball 0 ρ₀) C.ψ :=
    ⟨Metric.isOpen_ball, fun r => (C.hol.2 r).mono (Metric.ball_subset_ball hρ1)⟩
  have hprin : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ P : AbPart C.t (spMap (C.ψ z)), IsPrincipal P.tB := by
    intro z hz P
    obtain ⟨V, _, _, _, f, r, tV, mV, hV, hr, hker, hrf, hpol⟩ := GlobalTheory.T.exists_dvr_through_disc_point E H D l Xo σ n a C z hz
    have key : ∀ (z₀ : Sp ℂ ⟶ Sp C.R), z₀ = spMap r ≫ spMap f → ∀ P : AbPart C.t z₀, IsPrincipal P.tB := by
      rintro _ rfl P
      obtain ⟨m', -⟩ := GlobalTheory.T.abelian_part_factors_through E H _ _ tV C.t _ mV ℂ (spMap r) P
      exact GlobalTheory.T.polarized_abelian_part_principal E H V r tV hV hr hker hpol ⟨P.tK, m', P.τ, P.tB, P.e, P.e_hom, P.act, P.pp⟩
    refine key _ ?_ P
    rw [← hrf]
    show Spec.map (CommRingCat.ofHom (r.comp f)) = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  refine ⟨ρ₀ * ρ₁, Real.pi * Cb, mul_pos hρ0 h1, by nlinarith, ?_⟩
  intro z hz
  obtain ⟨z', hz', rfl⟩ : ∃ z' ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, z = (ρ₀ : ℂ) • z' := by
    refine ⟨(ρ₀⁻¹ : ℂ) • z, ?_, ?_⟩
    · rw [mem_ball_zero_iff] at hz ⊢
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
      rw [inv_mul_lt_iff₀ hρ0]
      exact hz
    · rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hρ0.ne'), one_smul]
  have hz1 : z' ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.ball_subset_ball h2 hz'
  have hb : (ρ₀ : ℂ) • z' ∈ Metric.ball (0 : Fin n → ℂ) ρ₀ := by
    rw [mem_ball_zero_iff] at hz1 ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
    nlinarith
  have hb1 : (ρ₀ : ℂ) • z' ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.ball_subset_ball hρ1 hb
  obtain ⟨ws, W, per, hws, hlim, hper, hfour, -, hsix⟩ := hL z' hz'
  obtain ⟨hA, hB, hC⟩ := GlobalTheory.T.family_exp_log_cover_bound E H C.R C.t C.g n a C.M C.ψ ρ₀ e Λ L hρ0 hρ1 hol hlink z' hz1 ws W per hws hlim hper hfour
  intro P
  have hP := hprin _ hb1 P
  refine ⟨hP, ?_⟩
  intro Mz hMz x v c hv hc
  obtain ⟨-, -, -, A, iA, φ, g', u, Hm, χ, v', w', a', b', hφ, hAH, hv', hw', ha', hb', rfl⟩ := hc
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.hol_unif_period_matrix_left E H C.R C.t C.g n C.M _ C.ψ e _ P A iA φ g' u Hm χ hb hφ hAH hP
  have e1 : a' = ℓ x := GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL.isDiff_eq_lift E H C.R C.t C.g n C.M _ C.ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ Mz hMz x v v' a' hv hv' ha'
  have e2 : b' = ℓ x := GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL.isDiff_eq_lift E H C.R C.t C.g n C.M _ C.ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ Mz hMz x v w' b' hv hw' hb'
  obtain ⟨hin, honto⟩ := GlobalTheory.T.hol_unif_period_matrix_right E H C.R C.t C.g n C.M _ C.ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ
  obtain ⟨Hb, hH1, hH2, hH3⟩ := exists_pull_form ℓ Hm hAH.1
  have hE : ∀ x x' : W, (per x ⬝ᵥ Hb *ᵥ star (per x')).im = ((L.E x x' : ℤ) : ℝ) := by
    intro x x'
    rw [hH2]
    refine eq_of_forall_exp fun N hN => ?_
    have hw := hC N (Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N))) x x' hN rfl
    have := GlobalTheory.T.hol_unif_period_matrix_middle E H C.R C.t C.g n C.M _ C.ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ N _ (per x) (per x') hN
      (hA x) (hA x') hw
    rw [Units.val_mk0] at this
    have c : (((L.E x x' : ℤ) : ℝ) : ℂ) = ((L.E x x' : ℤ) : ℂ) := by push_cast; rfl
    rw [c]
    exact this.symm
  have hrad : ∀ x : W, (∀ x' : W, L.E x x' = 0) → Hb *ᵥ star (per x) = 0 := by
    intro x hx
    refine hH3 _ (eq_zero_of_im_lattice Hm u.Λ u.full hAH.2.1 _ fun q hq => ?_)
    obtain ⟨y, hy, rfl⟩ := honto q hq
    obtain ⟨x', rfl⟩ := hB y hy
    rw [← hH2, hE, hx]
    simp
  subst e1 e2
  have hbd := (hsix Hb hH1 hE hrad x).2.1
  rw [hH2] at hbd
  have e3 : ((Real.pi : ℂ) * (ℓ x ⬝ᵥ Hm.mulVec (star (ℓ x)))).re = Real.pi * (ℓ x ⬝ᵥ Hm *ᵥ star (ℓ x)).re := by simp
  rw [e3, _root_.mul_assoc]
  exact mul_le_mul_of_nonneg_left hbd Real.pi_pos.le

end GlobalTheory.CompanionTheory.Ar.QuotLoc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalNearBoundaryStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_near_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → ∃ ρ K : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ P : AbPart C.t (spMap (C.ψ z)), IsPrincipal P.tB ∧ ∀ (Mz : LieModel C.t.G (spMap (C.ψ z)) (Fin C.g → ℂ)), (∀ i, ((Mz.pt (Pi.single i 1)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ z)) ≫ (C.M.pt (Pi.single i 1)).left)) → ∀ (x : Fin C.g → ℂ) (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (c : ℂ), v.left ≫ P.m.φ = (Mz.pt x).left → HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ K * ∑ i, ‖x i‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotLoc.abPart_principal_and_bound | exact GlobalTheory.CompanionTheory.Ar.QuotLoc.abPart_principal_and_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotLoc.abPart_principal_and_bound <;> assumption)
end
