module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceMoveRationalFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocallyHolomorphicPeriodsFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocallyHolomorphicPeriodsFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
open Filter GlobalTheory.HolHom

namespace GlobalTheory.ShFam.HorLift

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isHolTo_of_comp_open {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] {B : Set V} {y : V → (Sp ℂ ⟶ X)}
    (h : IsHolTo B fun b => y b ≫ i) : IsHolTo B y := by
  intro U f
  have key : ∀ (U' : X.Opens) (_ : i ⁻¹ᵁ (i ''ᵁ U) = U') (f : Γ(X, U')), IsOpen {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} ∧
      DifferentiableOn ℂ (fun b => valAt' (y b) U' f) {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} := by
    rintro _ rfl f
    have : IsIso (i.app (i ''ᵁ U)) := i.isIso_app _ (i.image_le_opensRange U)
    obtain ⟨g, rfl⟩ := (ConcreteCategory.bijective_of_isIso (i.app (i ''ᵁ U))).2 f
    have := h (i ''ᵁ U) g
    simp only [valAt'_eq_valR, valR_comp] at this
    exact this
  exact key U (i.preimage_image_eq U) f

theorem differentiableAt_dir [FiniteDimensional ℂ V] {G' G₀ G₁ S' S₀ S₁ : Scheme.{0}} {φ₀ : G' ⟶ G₀} {φ₁ : G' ⟶ G₁}
    {p : G' ⟶ S'} {p₀ : G₀ ⟶ S₀} {p₁ : G₁ ⟶ S₁} {f₀ : S' ⟶ S₀} {f₁ : S' ⟶ S₁} (H₀ : IsPullback φ₀ p p₀ f₀)
    (H₁ : IsPullback φ₁ p p₁ f₁) {g : ℕ} {B : Set V} {y : V → (Sp ℂ ⟶ S')} (hy : IsHolTo B y)
    {ex : V → (Fin g → ℂ) → (Sp ℂ ⟶ G₀)}
    (hex : IsHolTo (B ×ˢ Set.univ) fun bz : V × (Fin g → ℂ) => ex bz.1 bz.2)
    (hover : ∀ b ∈ B, ∀ w, ex b w ≫ p₀ = y b ≫ f₀) {b₀ : V} (hb₀ : b₀ ∈ B)
    (hinj : ∀ w, IsDerivAt (ex b₀) 0 w (constVec (ex b₀ 0)) → w = 0) {v : V → (Sp (DualNumber ℂ) ⟶ G₁)}
    (hv : HolTan B v) {W : V → Fin g → ℂ}
    (hW : ∀ b ∈ B, ∃ v₀ : Sp (DualNumber ℂ) ⟶ G', v₀ ≫ p = constVec (y b) ∧ v₀ ≫ φ₁ = v b ∧
      IsDerivAt0 (ex b) (W b) (v₀ ≫ φ₀)) : DifferentiableAt ℂ W b₀ := by
  haveI : Nonempty (Sp ℂ ⟶ G') := ⟨H₀.lift _ _ (hover b₀ hb₀ 0)⟩
  choose! e h₀ hp using fun b (hb : b ∈ B) w =>
    (⟨H₀.lift _ _ (hover b hb w), H₀.lift_fst _ _ _, H₀.lift_snd _ _ _⟩ :
      ∃ x : Sp ℂ ⟶ G', x ≫ φ₀ = ex b w ∧ x ≫ p = y b)
  have hO := isOpen_of_isHolTo hex
  have he : IsHolTo (B ×ˢ Set.univ) fun bz : V × (Fin g → ℂ) => e bz.1 bz.2 := by
    have h1 := LocLift.isHolTo_congr (y' := fun bz : V × (Fin g → ℂ) => e bz.1 bz.2 ≫ φ₀) hex
      fun bz hb => h₀ _ hb.1 _
    have h2 := LocLift.isHolTo_congr (y' := fun bz : V × (Fin g → ℂ) => e bz.1 bz.2 ≫ p)
      (LocLift.isHolTo_comp hy hO differentiableOn_fst fun _ hb => hb.1) fun bz hb => hp _ hb.1 _
    exact isHolTo_of_holAt hO fun z hz =>
      holAt_of_isPullback H₀ (holAt_of_isHolTo h1 hz) (holAt_of_isHolTo h2 hz)
  have hsl : ∀ b ∈ B, HolAt (e b) 0 := fun b hb =>
    (holAt_of_isHolTo he (z := (b, 0)) ⟨hb, trivial⟩).precomp (k := fun z => (b, z)) (by fun_prop)
  have hder : ∀ b ∈ B, ∀ w, ∃ u, IsDerivAt (e b) 0 w u ∧ IsDerivAt (ex b) 0 w (u ≫ φ₀) ∧
      u ≫ p = constVec (y b) := fun b hb w => by
    obtain ⟨u, hu⟩ := (hsl b hb).exists_isDerivAt w
    have h1 := hu.comp φ₀
    have h2 := hu.comp p
    simp only [h₀ b hb, hp b hb] at h1 h2
    exact ⟨u, hu, h1, h2.unique (isDerivAt_const _ _ _)⟩
  have hv' : ∀ b ∈ B, IsDerivAt (fun w => e b w ≫ φ₁) 0 (W b) (v b) := fun b hb => by
    obtain ⟨v₀, a1, a2, a3⟩ := hW b hb
    obtain ⟨u, hu, h1, h2⟩ := hder b hb (W b)
    obtain rfl : u = v₀ := H₀.hom_ext (h1.unique ((isDerivAt0_iff _ _ _).1 a3)) (h2.trans a1.symm)
    exact a2 ▸ hu.comp φ₁
  have he₁ := LocLift.isHolTo_comp_hom he φ₁
  refine HolLieFrame.differentiableAt_of_forms _ b₀ fun w hw => hinj w ?_
  obtain ⟨u, hu, h1, h2⟩ := hder b₀ hb₀ w
  have h3 : IsDerivAt (fun w => e b₀ w ≫ φ₁) 0 w (constVec (e b₀ 0 ≫ φ₁)) := by
    refine (isDerivAt_constVec_iff (c := fun w => e b₀ w ≫ φ₁)).2 fun U hU f => ?_
    refine hw (fun b => fderiv ℂ (fun z => valAt' (e b z ≫ φ₁) U f) 0)
      (differentiableAt_partial (he₁ U f).1 (he₁ U f).2 ⟨⟨hb₀, trivial⟩, hU⟩) ?_
    have hc : ContinuousAt (fun b : V => (b, (0 : Fin g → ℂ))) b₀ := by fun_prop
    have hn := hc.eventually ((he₁ U f).1.mem_nhds ⟨⟨hb₀, trivial⟩, hU⟩)
    refine ((hv U f).differentiableAt (hn.mono fun b hb =>
      ⟨hb.1.1, (le_preimage_dual_iff (hv' b hb.1.1).1 U).2 hb.2⟩)).congr_of_eventuallyEq ?_
    exact hn.mono fun b hb => ((hv' b hb.1.1).2 U hb.2 f).symm
  obtain rfl : u = constVec (e b₀ 0) := H₁.hom_ext ((hu.comp φ₁).unique h3)
    (by rw [h2, Category.assoc, hp b₀ hb₀])
  rwa [Category.assoc, h₀ b₀ hb₀] at h1

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw}

theorem exists_inner_lift (x : CxPts (genStr Z) σ) (hx : Inner x) : ∃ y : Sp ℂ ⟶ Xo.XF c, y ≫ Z.jQ = x.1 := by
  haveI := Z.jQ_open
  refine ⟨IsOpenImmersion.lift Z.jQ x.1 ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨p, rfl⟩
  obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact not_not.1 hx

theorem exists_dirs (Fu : Fam Xo c σ e) (a : CxFr Z σ) (y : Sp ℂ ⟶ Xo.XF c) (hy : y ≫ Z.jQ = a.1.1) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    (hu : Fu.u i P = y ≫ pullback.fst _ _) :
    ∃ (w : Fin g → Fin g → ℂ) (M : Matrix (Fin g) (Fin g) ℂ), (∀ j, M *ᵥ w j = Pi.single j 1) ∧
      ∀ z : Letter Dw, ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
        v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = a.2.v z.1 z.2 ∧
        IsDerivAt0 (fun w => (Fu.ex i P w).left) (w (e.symm z)) (v₀ ≫ Z.m0.toSABMap.φ) := by
  have hs : y ≫ pullback.snd _ _ = spMap σ := by
    rw [← Z.jQ_over, ← Category.assoc, hy]; exact a.1.2
  obtain ⟨y', v, hx, hv⟩ := @OpenReg.exists_frPt_of_eigFrame E _ _ _ H Dw l Xo c O _ β Z (CAt σ) inferInstance
    (inferInstanceAs (IsLocalRing ℂ)) inferInstance y hs (a.1.1 ≫ genι Z)
    (by rw [← hy]; exact (Category.assoc _ _ _).symm) a.2
  obtain ⟨w, M, -, hw, hM, -⟩ := AdaptedPeriods.exists_adapted E H Dw l Xo c σ g e Fu y' i P hP (hu.trans hx.symm)
  refine ⟨w, M, hM, fun z => ⟨v z.1 z.2, (hv _ _).1, (hv _ _).2.2, ?_⟩⟩
  have := hw (e.symm z)
  rw [Equiv.apply_symm_apply, ← (hv _ _).2.1] at this
  exact this

theorem exists_hol_per : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, Inner (a b).1) → ∀ b₀ ∈ B, ∃ (B' : Set V) (i : Fin Fu.n) (Q : V → ((Fu.Di i).La →+ (Letter Dw → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ (∀ b ∈ B', Per Fu (a b) i (Q b)) ∧ ∀ v z, DifferentiableOn ℂ (fun b => Q b v z) B' := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu V _ _ _ B a hB ha hI b₀ hb₀
  haveI := Z.jQ_open
  haveI : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨(exists_inner_lift _ (hI b₀ hb₀)).choose⟩
  choose! y hy using fun b (hb : b ∈ B) => exists_inner_lift _ (hI b hb)
  have hyh : IsHolTo B y := isHolTo_of_comp_open Z.jQ (LocLift.isHolTo_congr ha.1 hy)
  let φ : V ≃L[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hBφ : IsOpen (φ.symm ⁻¹' B) := hB.preimage φ.symm.continuous
  obtain ⟨B₁, i, P₁, hB₁, hb₁, hsub, hP₁, hu₁⟩ := Fu.lift _ (φ.symm ⁻¹' B) (fun t => y (φ.symm t) ≫ pullback.fst _ _) hBφ
    (fun t ht => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, ← Z.jQ_over, ← Category.assoc, hy _ ht,
        ← OpenReg.spMap_comp]
      exact congrArg (· ≫ _) (a _).1.2)
    (LocLift.isHolTo_comp (LocLift.isHolTo_comp_hom hyh _) hBφ φ.symm.differentiableOn fun _ h => h) (φ b₀)
    (by simpa using hb₀)
  have hB' : IsOpen (φ ⁻¹' B₁) := hB₁.preimage φ.continuous
  have hsub' : φ ⁻¹' B₁ ⊆ B := fun b hb => by simpa using hsub hb
  have hu : ∀ b ∈ φ ⁻¹' B₁, Fu.u i (P₁ (φ b)) = y b ≫ pullback.fst _ _ := fun b hb => by simpa using hu₁ _ hb
  have hex : IsHolTo ((φ ⁻¹' B₁) ×ˢ Set.univ) fun bz : V × (Fin g → ℂ) => (Fu.ex i (P₁ (φ bz.1)) bz.2).left :=
    LocLift.isHolTo_comp (β := fun bz : V × (Fin g → ℂ) => (φ bz.1, bz.2)) (Fu.hol i _ B₁ P₁ hB₁ hP₁).2
      (hB'.prod isOpen_univ) (by fun_prop) fun _ h => ⟨h.1, trivial⟩
  choose! w M hM hw using fun b (hb : b ∈ φ ⁻¹' B₁) =>
    exists_dirs Fu (a b) (y b) (hy b (hsub' hb)) i (P₁ (φ b)) (hP₁.1 _ hb) (hu b hb)
  have hM' : ∀ b ∈ φ ⁻¹' B₁, M b * (Matrix.of fun i j => w b j i) = 1 := fun b hb => by
    ext i j
    have := congrFun (hM b hb j) i
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  let Q : V → ((Fu.Di i).La →+ (Letter Dw → ℂ)) := fun b =>
    AddMonoidHom.mk' (fun v z => (M b *ᵥ P₁ (φ b) v) (e.symm z)) fun v v' => by
      funext z
      simp [Matrix.mulVec_add]
  refine ⟨φ ⁻¹' B₁, i, Q, hB', hb₁, hsub', fun b hb => ⟨P₁ (φ b), fun z => w b (e.symm z), y b, hP₁.1 _ hb,
    (hu b hb).symm, hy b (hsub' hb), hw b hb, fun v => ?_⟩, fun v z b hb => ?_⟩
  · have h1 := congrArg (· *ᵥ P₁ (φ b) v) (mul_eq_one_comm.1 (hM' b hb))
    simp only [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at h1
    rw [← h1]
    refine Eq.trans ?_ (Equiv.sum_comp e.symm fun j => (M b *ᵥ P₁ (φ b) v) j • w b j).symm
    funext k
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  · have hwd : ∀ j, DifferentiableAt ℂ (fun b => w b j) b := fun j => by
      obtain ⟨z, rfl⟩ := e.symm.surjective j
      refine differentiableAt_dir Z.m0.toSABMap.cart.1 Z.m.cart.1 (LocLift.isHolTo_mono hyh hB' hsub')
        (ex := fun b u => (Fu.ex i (P₁ (φ b)) u).left) hex
        (fun b hb u => (Over.w (Fu.ex i (P₁ (φ b)) u)).trans (hu b hb)) hb (fun u h => ?_)
        (v := fun b => (a b).2.v z.1 z.2) (fun U f => (ha.2 z.1 z.2 U f).mono fun _ h => ⟨hsub' h.1, h.2⟩)
        fun b hb => hw b hb z
      have h0 : IsDerivAt (fun u => (Fu.ex i (P₁ (φ b)) u).left) 0 0 (constVec (Fu.ex i (P₁ (φ b)) 0).left) :=
        (isDerivAt_constVec_iff (c := fun u => (Fu.ex i (P₁ (φ b)) u).left)).2 fun _ _ _ => map_zero _
      exact ((Fu.ex_diff i _ (hP₁.1 _ hb)).2 (Over.homMk _ h.over) h.1).unique ((isDerivAt0_iff _ _ _).2 h)
        ((isDerivAt0_iff _ _ _).2 h0)
    have hMd : ∀ i j, DifferentiableAt ℂ (fun b => M b i j) b :=
      HolFrameMatrix.differentiableAt_of_mul_eq_one M (fun b => Matrix.of fun i j => w b j i) b
        (fun i j => differentiableAt_pi.1 (hwd j) i) (eventually_of_mem (hB'.mem_nhds hb) hM')
    have hPd : DifferentiableAt ℂ (fun b => P₁ (φ b) v) b :=
      ((hP₁.2 v).differentiableAt (hB₁.mem_nhds hb)).comp b φ.differentiableAt
    refine DifferentiableAt.differentiableWithinAt ?_
    show DifferentiableAt ℂ (fun b => ∑ j, M b (e.symm z) j * P₁ (φ b) v j) b
    exact DifferentiableAt.fun_sum fun j _ => (hMd _ j).mul (differentiableAt_pi.1 hPd j)

end GlobalTheory.ShFam.HorLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocallyHolomorphicPeriodsFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_locally_holomorphic_periods_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, Inner (a b).1) → ∀ b₀ ∈ B, ∃ (B' : Set V) (i : Fin Fu.n) (Q : V → ((Fu.Di i).La →+ (Letter Dw → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ (∀ b ∈ B', Per Fu (a b) i (Q b)) ∧ ∀ v z, DifferentiableOn ℂ (fun b => Q b v z) B' := by
  first | exact @GlobalTheory.ShFam.HorLift.exists_hol_per | exact GlobalTheory.ShFam.HorLift.exists_hol_per | (intros; apply GlobalTheory.ShFam.HorLift.exists_hol_per <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisOfIntFrame
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet GlobalTheory.LocM
open GlobalTheory.GradedPieces GlobalTheory.Points

namespace GlobalTheory.TotalFrame

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_basis_sigma {O S M J : Type} [CommRing O] [CommRing S] [AddCommGroup M] [Module S M] [Fintype J]
    {χ : J → O →+* S} (h : EigenSplit.IsSplitting χ) (ρ : O →+* Module.End S M) {m : J → ℕ}
    (u : ∀ σ, Fin (m σ) → M) (li : ∀ σ, LinearIndependent S (u σ))
    (hs : ∀ σ, Submodule.span S (Set.range (u σ)) = EigenSplit.eigenSub ρ (χ σ)) :
    ∃ b : Module.Basis (Σ σ, Fin (m σ)) S M, ∀ σ a, b ⟨σ, a⟩ = u σ a := by
  classical
  have hi := EigenSplit.isInternal_eigenSub h ρ
  simp only [← hs] at hi
  exact ⟨hi.collectedBasis fun σ => Module.Basis.span (li σ), fun σ a => by
    rw [DirectSum.IsInternal.collectedBasis_coe]
    exact congrArg Subtype.val (Module.Basis.span_apply (li σ) a)⟩

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X} {m : ℕ}

theorem exists_basis {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ i, IsTanAtG t x (v i))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x v cf w) :
    ∃ b : Module.Basis (Fin m) S (TanM x t.G), ∀ i, b i = tanOf (hv i) := by
  refine ⟨Module.Basis.mk (v := fun i => tanOf (hv i)) (Fintype.linearIndependent_iffₛ.2 fun c c' h => congrFun
    ((hb _ (isTan_tv (∑ i, c i • tanOf (hv i)))).unique ((isComb_iff (fun i => tanOf (hv i)) c _).2 rfl)
      ((isComb_iff (fun i => tanOf (hv i)) c' _).2 h))) fun w _ => ?_, fun i => Module.Basis.mk_apply _ _ i⟩
  obtain ⟨a, ha, -⟩ := hb _ (isTan_tv w)
  rw [(isComb_iff (fun i => tanOf (hv i)) a w).1 ha]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_basis_map {J : Type} [Fintype J] (b : Module.Basis J S (TanM x t.G)) (φ : S →+* T) {x' : Sp T ⟶ X}
    (hx : spMap φ ≫ x = x') :
    ∃ b' : Module.Basis J T (TanM x' t.G), ∀ i, (tv (b' i)).left = spMap (dualMap φ) ≫ (tv (b i)).left := by
  let e := Fintype.equivFin J
  have hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x (fun i => (tv (b.reindex e i)).left) cf w := fun w hw =>
    ⟨(b.reindex e).repr (tanOf hw), (isComb_iff _ _ (tanOf hw)).2 ((b.reindex e).sum_repr _).symm, fun a ha => by
      rw [(isComb_iff _ _ (tanOf hw)).1 ha, Module.Basis.repr_sum_self]⟩
  obtain ⟨b', hb'⟩ := exists_basis (fun i => isTan_map φ hx (isTan_tv (b.reindex e i)))
    (basis_map φ hx (fun i => isTan_tv _) hb)
  refine ⟨b'.reindex e.symm, fun i => ?_⟩
  rw [Module.Basis.reindex_apply, hb', left_tanOf, Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

theorem dualMap_epsMul (φ : S →+* T) (a : S) {Y : Scheme.{0}} (v : Sp (DualNumber S) ⟶ Y) :
    spMap (dualMap φ) ≫ spMap (epsMul a) ≫ v = spMap (epsMul (φ a)) ≫ spMap (dualMap φ) ≫ v := by
  rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap]
  congr 2
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

variable {Dw : Datum H} {l : Level H} {c : Coeff l} {w : Vecs Dw t S} {χ : (E →+* ℂ) → 𝓞 E →+* S}


variable (c x w χ) in
def FramesSeparate : Prop :=
  ∀ r s : S, (∀ (k : Type) [Field k] (φ : S →+* k) (f : c.F →+* k), IsFrame t f (spMap φ ≫ x) (w.bc φ) →
    (∀ σ a, f (embK c σ a) = φ (χ σ a)) → φ r = φ s) → r = s

theorem span_eq_eigenSub (hw : FramesSeparate x c w χ) (σ : E →+* ℂ) (ht : ∀ i, IsTanAtG t x (w σ i))
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (e : Fin (Dw.mult σ) ↪ Fin m) (he : ∀ i, v (e i) = w σ i)
    (hv : ∀ i, IsTanAtG t x (v i)) (hb : ∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x v cf u) :
    Submodule.span S (Set.range fun i => tanOf (ht i)) = EigenSplit.eigenSub (actR t.act) (χ σ) := by
  classical
  refine le_antisymm (Submodule.span_le.2 ?_) fun u hu => ?_
  · rintro _ ⟨i, rfl⟩
    refine EigenSplit.mem_eigenSub.2 fun a => ?_
    obtain ⟨g, hc, -⟩ := hb _ (isTan_tv (actR t.act a (tanOf (ht i))))
    obtain ⟨g', hc', -⟩ := hb _ (isTan_tv (χ σ a • tanOf (ht i)))
    have hcc : g = g' := funext fun l => hw _ _ fun k _ φ f hf hfj => by
      have h1 := comb_map φ rfl hc
      have h2 := comb_map φ rfl hc'
      have h3 : spMap (dualMap φ) ≫ (tv (actR t.act a (tanOf (ht i)))).left =
          spMap (dualMap φ) ≫ (tv (χ σ a • tanOf (ht i))).left := by
        refine (Category.assoc _ _ _).symm.trans (((hf.1 σ i).2 a).trans ?_)
        rw [hfj]
        exact (dualMap_epsMul φ _ _).symm
      rw [h3] at h1
      exact congrFun ((basis_map φ rfl hv hb _ (isTan_map φ rfl (isTan_tv _))).unique h1 h2) l
    subst hcc
    exact ((isComb_iff (fun i => tanOf (hv i)) g _).1 hc).trans ((isComb_iff (fun i => tanOf (hv i)) g _).1 hc').symm
  · obtain ⟨g, hc, -⟩ := hb _ (isTan_tv u)
    rw [(isComb_iff (fun i => tanOf (hv i)) g _).1 hc]
    refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : ∃ i, e i = l
    · obtain ⟨i, rfl⟩ := hl
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, tan_ext (he i).symm⟩)
    have h0 : g l = 0 := hw _ _ fun k _ φ f hf hfj => by
      have hvk := fun i => isTan_map φ rfl (hv i)
      have huk := isTan_map φ rfl (isTan_tv u)
      obtain ⟨d, hd, -⟩ := hf.2 σ _ huk fun a => by
        rw [hfj, ← dualMap_epsMul, Category.assoc]
        exact congrArg (fun q => spMap (dualMap φ) ≫ (tv q).left) (EigenSplit.mem_eigenSub.1 hu a)
      have h1 := (comb_iff hvk _ huk).1 (comb_map φ rfl hc)
      have h2 := (comb_iff (fun i => (hf.1 σ i).1) _ huk).1 hd
      have h3 : ∑ i, d i • tanOf (hf.1 σ i).1 = ∑ l, Function.extend e d 0 l • tanOf (hvk l) :=
        Fintype.sum_of_injective e e.injective _ _
          (fun l hl => by rw [Function.extend_apply' _ _ _ hl, Pi.zero_apply, zero_smul])
          (fun i => by
            rw [e.injective.extend_apply]
            exact congrArg (d i • ·) (tan_ext (congrArg (spMap (dualMap φ) ≫ ·) (he i).symm)))
      rw [map_zero, Fintype.linearIndependent_iffₛ.1 (linInd_of_basis hvk (basis_map φ rfl hv hb)) _ _
        (h1.symm.trans (h2.trans h3)) l, Function.extend_apply' _ _ _ hl, Pi.zero_apply]
    rw [h0, zero_smul]
    exact Submodule.zero_mem _

theorem exists_basis_total (hw : FramesSeparate x c w χ) (hχ : EigenSplit.IsSplitting χ)
    (h : ∀ σ, ∃ (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)) (e : Fin (Dw.mult σ) ↪ Fin n),
      (∀ i, v (e i) = w σ i) ∧ (∀ i, IsTanAtG t x (v i)) ∧ ∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x v cf u)
    (φ : S →+* T) {x' : Sp T ⟶ X} (hx : spMap φ ≫ x = x') :
    ∃ b : Module.Basis (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) T (TanM x' t.G), ∀ σ a, (tv (b ⟨σ, a⟩)).left = w.bc φ σ a := by
  choose n v e he hv hb using h
  have ht : ∀ σ i, IsTanAtG t x (w σ i) := fun σ i => he σ i ▸ hv σ (e σ i)
  have li : ∀ σ, LinearIndependent S fun i => tanOf (ht σ i) := fun σ => by
    obtain ⟨b, hb'⟩ := exists_basis (hv σ) (hb σ)
    convert b.linearIndependent.comp (e σ) (e σ).injective using 1
    exact funext fun i => Eq.trans (tan_ext (w := tanOf (hv σ (e σ i))) (he σ i).symm) (hb' (e σ i)).symm
  obtain ⟨b, hb'⟩ := exists_basis_sigma hχ _ (fun σ i => tanOf (ht σ i)) li
    fun σ => span_eq_eigenSub hw σ (ht σ) (e σ) (he σ) (hv σ) (hb σ)
  obtain ⟨b', hb''⟩ := exists_basis_map b φ hx
  exact ⟨b', fun σ a => by rw [hb'', hb']; rfl⟩

end Tangent

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def embV {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (σ : E →+* ℂ) : 𝓞 E →+* c.V W :=
  (embK c σ).codRestrict (c.V W) fun a =>
    GlobalTheory.CoeffRings.mem_of_isIntegral _ (map_isIntegral_int (embK c σ) (RingOfIntegers.isIntegral a))

theorem isSplitting_embV {l : Level H} (c : Coeff l) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)
    (hd : ¬ p ∣ (discr E).natAbs) {S : Type} [CommRing S] (j : c.V W →+* S) :
    EigenSplit.IsSplitting fun σ : E →+* ℂ => j.comp (embV c W σ) := by
  refine EigenSplit.isSplitting_of_isDomain (fun σ τ h => ?_) (NumberField.Embeddings.card E ℂ) j ?_
  · exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
      (RingHom.ext fun a => congrArg (fun f : 𝓞 E →+* c.V W => (((f a : c.V W) : c.F) : ℂ)) h)
  · have hu := (((GlobalTheory.CoeffRings.coeff_isDedFrac E H l c).2.2.2 p W hp hW).2.1 _
      (hp.coprime_iff_not_dvd.2 hd).symm).map j
    rw [map_natCast] at hu
    rcases Int.natAbs_eq (discr E) with h | h <;> rw [h]
    · rwa [Int.cast_natCast]
    · rw [Int.cast_neg, Int.cast_natCast]
      exact hu.neg

variable {Z : Mdl Y i₀} {U : Z.X.Opens} {hU : IsAffineOpen U} {w : Vecs Dw (Y Z.i).t Γ(Z.X, U)}


variable (hU) in
theorem fn_ext_affine {f g : Γ(Z.X, U)} (h : ∀ (k : Type) [Field k] (φ : Γ(Z.X, U) →+* k),
    Set.range (spMap φ ≫ hU.fromSpec) ⊆ Z.opn → φ f = φ g) : f = g :=
  fn_ext Z fun k _ x hx ho => by
    rw [valR_eq x U hx, valR_eq x U hx]
    exact h k (valMap x U hx).hom (by
      rw [show spMap (valMap x U hx).hom ≫ hU.fromSpec = x from specMap_valMap_fromSpec hU x hx]
      exact ho)

theorem frame_at (hw : IntFrame Z hU w) {j : Z.i.c.V W →+* Γ(Z.X, U)} (hj : spMap j = hU.fromSpec ≫ Z.s)
    {k : Type} [Field k] (φ : Γ(Z.X, U) →+* k) (ho : Set.range (spMap φ ≫ hU.fromSpec) ⊆ Z.opn) :
    ∃ f : Z.i.c.F →+* k, IsFrame (Y Z.i).t f (spMap φ ≫ hU.fromSpec ≫ Z.π) (w.bc φ) ∧
      ∀ σ a, f (embK Z.i.c σ a) = φ (j (embV Z.i.c W σ a)) := by
  obtain ⟨a, ψ, hx, hf, -⟩ := hw.2 k φ ho
  rw [Category.assoc] at hf
  refine ⟨_, hf, fun σ r => ?_⟩
  have e : spMap (ψ.comp ((Z.alg a).comp (Z.i.c.V W).subtype)) = spMap (φ.comp j) := by
    rw [← spMap_comp_spMap _ ψ, ← spMap_comp_spMap _ φ, hj, ← Z.alg_s a, ← Category.assoc, hx, Category.assoc]
  exact congrArg (fun q => q.hom (embV Z.i.c W σ r)) (Spec.map_injective e)

end Model

theorem exists_basis_of_intFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ)
    (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ¬ p ∣ (discr E).natAbs →
    ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Mdl Y i₀) (U : Z.X.Opens) (hU : IsAffineOpen U)
      (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)), IntFrame Z hU w → ∀ (R : Type) [CommRing R] (φ : Γ(Z.X, U) →+* R)
      (x : Sp R ⟶ Z.X), spMap φ ≫ hU.fromSpec = x →
      ∃ b : Module.Basis (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) R (TanM (x ≫ Z.π) (Y Z.i).t.G),
        ∀ σ a, (tv (b ⟨σ, a⟩)).left = w.bc φ σ a := by
  intro E _ _ _ H Dw Xo p W hp hW hd Y i₀ Z U hU w hw R _ φ x hx
  let j : Z.i.c.V W →+* Γ(Z.X, U) := (Spec.preimage (hU.fromSpec ≫ Z.s)).hom
  have hj : spMap j = hU.fromSpec ≫ Z.s := Spec.map_preimage _
  refine exists_basis_total (c := Z.i.c) (fun r s h => fn_ext_affine hU fun k _ ψ ho => ?_)
    (isSplitting_embV Z.i.c hp hW hd j) hw.1 φ (hx ▸ (Category.assoc _ _ _).symm)
  obtain ⟨f, hf, hfj⟩ := frame_at hw hj ψ ho
  exact h k ψ f hf hfj

end GlobalTheory.TotalFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralComparisonTransportedDivisionLatticeChan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReOfDiv
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SIsoReD
noncomputable section

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe.IsoRe

variable {D : D7} (Z : New D) {X : HidaSetting D} {Y : Full X} (h : FinX Y) (h' : FinX (reY Z Y))

def eP (u u' : D.what₂.Word) : RP Y u u' ≃ RP (reY Z Y) (wd Z u) (wd Z u') :=
  (rp_iso_pair D Z X Y h h' u u').choose


set_option maxHeartbeats 4000000 in
def sIsoRe : SIso (sOf h) ((@sOf (reD D Z) (@reX D Z X) (@reY D Z X Y) h')) where
  cd := (by with_unfolding_all exact ((Eq.refl (Formalism.L2.SG.PairVal.cdScaleOf D)) :))
  del := (by with_unfolding_all exact ((Eq.refl D.s.Del) :))
  letter := (by with_unfolding_all exact ((Eq.refl D.s.letter) :))
  eHH := (by with_unfolding_all exact ((eHHre Z X) :))
  eCu := (by with_unfolding_all exact ((eCure Z h h') :))
  Pu_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D Z X Y h h').1 :))
  volN := (by with_unfolding_all exact ((Eq.refl Y.volN) :))
  volH := (by with_unfolding_all exact ((Eq.refl Y.volH) :))
  eT := (by with_unfolding_all exact ((eRT Z Y) :))
  aTerm_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D Z X Y h h').2.2 :))
  isId := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).1 :))
  inS := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.1 :))
  relevant := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.1 :))
  FeqF := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.1 :))
  Gterm := fun {u u'} t => Subtype.ext (a1 := (sOf h).Gterm t) (a2 := (by with_unfolding_all exact (((sOf h').Gterm (eRT Z Y u u' t)) :))) ((by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.1 :)))
  atP := fun p => (by with_unfolding_all exact ((Formalism.L2.S.LocIso.refl (Formalism.L2.S.locC D p)) :))
  ePl := (by with_unfolding_all exact ((Equiv.refl (Formalism.MainNotions.S.LocalSplitGroups.PlF D)) :))
  BBne := fun {u u'} t q => (by with_unfolding_all exact ((((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.2.1 q) :))
  generic := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.1 :))
  eP := (by with_unfolding_all exact ((eP Z h h') :))
  pfst := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).1) :))
  psnd := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.1) :))
  s0 := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.2.1) :))
  scalarPair := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.2.2.1) :))
  pval := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.2.2.2) :))
  ptOf := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.2.2.1 :))
  cTerm := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.2.2.2.2 :))
  massPair := fun {u u'} p => (by with_unfolding_all exact (((((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 ((p.1.1) : RT Y u u')).2.2.2.2.2.2.2.2.1).trans
      (congrArg Formalism.L2.SG.PairVal.massTerm ((rp_iso_pair D Z X Y h h' u u').choose_spec ((p) : RP Y u u')).1)) : _))
  meanCount := (by with_unfolding_all exact ((funext fun u => funext fun u' => funext fun w => (GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').2 w :
      (fun (u u' : D.what₂.Word) w => Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w) =
        fun (u u' : D.what₂.Word) w => Formalism.L2.SG.PairVal.meanCount (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) w) :))

end GlobalTheory.Mem.SRe.IsoRe

namespace GlobalTheory.Mem.SRe


set_option maxHeartbeats 4000000 in
theorem sIso_reD : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (h : FinX Y) (h' : FinX (reY Z Y)),
    ∃ e : SIso (sOf h) ((@sOf (reD D Z) (@reX D Z X) (@reY D Z X Y) h')), HEq e.eHH (eHHre Z X) ∧ ∀ u, HEq (e.eCu u) (eCure Z h h' u) :=
  fun _ Z X _ h h' => ⟨IsoRe.sIsoRe Z h h', (by with_unfolding_all exact ((HEq.refl (eHHre Z X)) :)),
    fun u => (by with_unfolding_all exact ((HEq.refl (eCure Z h h' u)) :))⟩

end GlobalTheory.Mem.SRe
end
end

noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000

section Trans

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

def LocIso.trans {A B C : Formalism.MainNotions.S.Loc.LocAt F E sig p} (a : Formalism.L2.S.LocIso A B) (b : Formalism.L2.S.LocIso B C) :
    Formalism.L2.S.LocIso A C where
  eF := a.eF.trans b.eF
  eF_ι x := (congrArg b.eF (a.eF_ι x)).trans (b.eF_ι x)
  eF_val x y := (a.eF_val x y).trans (b.eF_val _ _)
  eF_cont := b.eF_cont.comp a.eF_cont
  eF_symm_cont := a.eF_symm_cont.comp b.eF_symm_cont
  eF_ql x := (congrArg b.eF (a.eF_ql x)).trans (b.eF_ql x)
  eE := a.eE.trans b.eE
  eE_alg x := (congrArg b.eE (a.eE_alg x)).trans (b.eE_alg _)
  eE_ι x := (congrArg b.eE (a.eE_ι x)).trans (b.eE_ι x)
  eE_cont := b.eE_cont.comp a.eE_cont
  eE_symm_cont := a.eE_symm_cont.comp b.eE_symm_cont
  eE_cj y := (congrArg b.eE (a.eE_cj y)).trans (b.eE_cj _)
  eE_O y := (a.eE_O y).trans (b.eE_O _)
  eE_psi y := (a.eE_psi y).trans (b.eE_psi _)

variable {R : Ranks} {Word Tau : Type} {hc : Word → Tau → HCParam R}

def SIso.trans {s s' s'' : Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc} (a : SIso s s') (b : SIso s' s'') : SIso s s'' where
  cd := a.cd.trans b.cd
  del := a.del.trans b.del
  letter := a.letter.trans b.letter
  eHH := a.eHH.trans b.eHH
  eCu u := (a.eCu u).trans (b.eCu u)
  Pu_eq u x := (congrArg b.eHH (a.Pu_eq u x)).trans (b.Pu_eq u _)
  volN := a.volN.trans b.volN
  volH := a.volH.trans b.volH
  eT u u' := (a.eT u u').trans (b.eT u u')
  aTerm_eq u u' t x := (congrArg (b.eCu u) (a.aTerm_eq u u' t x)).trans (b.aTerm_eq u u' _ _)
  isId t := (a.isId t).trans (b.isId _)
  inS t := (a.inS t).trans (b.inS _)
  relevant t := (a.relevant t).trans (b.relevant _)
  FeqF t := (a.FeqF t).trans (b.FeqF _)
  Gterm t := (a.Gterm t).trans (b.Gterm _)
  atP p := LocIso.trans (a.atP p) (b.atP p)
  ePl := a.ePl.trans b.ePl
  BBne t q := (a.BBne t q).trans (b.BBne _ _)
  generic t := (a.generic t).trans (b.generic _)
  eP u u' := (a.eP u u').trans (b.eP u u')
  pfst p := (congrArg (b.eT _ _) (a.pfst p)).trans (b.pfst _)
  psnd p := (congrArg (b.eT _ _) (a.psnd p)).trans (b.psnd _)
  s0 p := (a.s0 p).trans (b.s0 _)
  scalarPair p := (a.scalarPair p).trans (b.scalarPair _)
  pval p := (a.pval p).trans (b.pval _)
  ptOf t := (a.ptOf t).trans (b.ptOf _)
  cTerm t := (a.cTerm t).trans (b.cTerm _)
  massPair p := (a.massPair p).trans (b.massPair _)
  meanCount := a.meanCount.trans b.meanCount

end Trans

section Move

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ)

theorem SRest.exists_re_ofDiv {F : ∀ u, Forms0 D u} {P : SPack D F} (S : SRest P)
    {F' : ∀ u, Forms0 (reD D (New.ofDiv D N hh)) u} (h : SameForms0LevelsAndValues (New.ofDiv D N hh) F F')
    (hF : FinX (reY (New.ofDiv D N hh) P.Y)) :
    ∃ S' : SRest (P.re (New.ofDiv D N hh) h hF), HEq S'.j S.j := by
  obtain ⟨e, heH, heC⟩ := sIso_reD D (New.ofDiv D N hh) P.X P.Y P.fin hF
  let hI' : SIso (reD D (New.ofDiv D N hh)).s (sOf (P.re (New.ofDiv D N hh) h hF).fin) := (by with_unfolding_all exact (SIso.trans S.hI e :))
  let aT : Formalism.MainNotions.S.AutTie (reD D (New.ofDiv D N hh)) (P.re (New.ofDiv D N hh) h hF).X.B
      (P.re (New.ofDiv D N hh) h hF).X.pl :=
    ⟨(by with_unfolding_all exact (S.autTie.n_eq :)), (by with_unfolding_all exact (S.autTie.f_eq :)), (by with_unfolding_all exact (S.autTie.rd_eq :)), (by with_unfolding_all exact (S.autTie.eps_eq :)),
      (by with_unfolding_all exact (S.autTie.lam_eq :)), (by with_unfolding_all exact (S.autTie.ds :)), (by with_unfolding_all exact (S.autTie.low :)), (by with_unfolding_all exact (S.autTie.g_eq :)),
      (by with_unfolding_all exact (S.autTie.g0_eq :)), (by with_unfolding_all exact (S.autTie.D_eq :)), (by with_unfolding_all exact (S.autTie.Dstar_eq :))⟩
  let jj : (reD D (New.ofDiv D N hh)).what₂.EE ≃ₗᵢ[ℂ] EEC (P.re (New.ofDiv D N hh) h hF).X
      (P.re (New.ofDiv D N hh) h hF).G := (by with_unfolding_all exact (S.j :))
  have lT : Formalism.L2.SG.Pf.LocCP.LocTied (reD D (New.ofDiv D N hh)) := (by with_unfolding_all exact (S.locTied :))
  have cP : ∀ (u : (reD D (New.ofDiv D N hh)).what₂.Word) (x : (reD D (New.ofDiv D N hh)).s.Cu u),
      colDict (P.re (New.ofDiv D N hh) h hF).X ((P.re (New.ofDiv D N hh) h hF).tr u)
        (P.re (New.ofDiv D N hh) h hF).Y.hK ((P.re (New.ofDiv D N hh) h hF).into u)
        ((P.re (New.ofDiv D N hh) h hF).bij u) (hI'.eCu u x) = (reD D (New.ofDiv D N hh)).s_Cu u x := by
    intro u x
    have hx : hI'.eCu u x = ((by with_unfolding_all exact (S.hI.eCu u x :))) := (by with_unfolding_all exact (congrArg (fun f => f (S.hI.eCu u x)) (eq_of_heq (heC u)) :))
    rw [hx]
    apply Subtype.ext
    exact (by with_unfolding_all exact ((colDictL_reTr (New.ofDiv D N hh) (P.tr u) (h u).2.1 (h u).2.2 P.Y.hK
      (toCu (cs := P.Y.cs u) (hinj := P.fin.shInj u) P.X P.Y.hK (S.hI.eCu u x))).trans (congrArg Subtype.val (S.colPin u x)) :))
  have rP : ∀ x : (reD D (New.ofDiv D N hh)).what₂.EE,
      hI'.eHH ((reD D (New.ofDiv D N hh)).sEE x) =
        conjHH (P.re (New.ofDiv D N hh) h hF).X (P.re (New.ofDiv D N hh) h hF).G (jj x) := by
    intro x
    exact (by with_unfolding_all exact ((congrArg (fun f => f (S.hI.eHH (D.sEE x))) (eq_of_heq heH)).trans (S.rowPin x) :))
  exact ⟨⟨hI', aT, cP, jj, rP, lT⟩, (by with_unfolding_all exact (HEq.refl S.j :))⟩

end Move

end GlobalTheory.Mem.SRe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralComparisonTransportedDivisionLatticeChan
noncomputable section

open GlobalTheory.Mem.R3.Tr Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe

theorem of_heq_cast {α β : Sort _} {y : β} {x : α} (P : α → Prop) (h : HEq y x) (hx : P x) :
    P (cast (type_eq_of_heq h) y) := by
  cases h
  exact hx


set_option maxHeartbeats 4000000 in
theorem sAtL_exists_ofDiv : ∀ (B : Base) (C : Cols B) (a : Late B C) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] (R : RealDat a.D A Ks) (F : Face a.D A) (F0 : ∀ u, Forms0 a.D u) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (s : SAt R F eE F0) (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ) (F₁ : ∀ u, Forms0 (reL a (New.ofDiv a.D N hh)).D u), SameL a (New.ofDiv a.D N hh) F0 F₁ → ∃ s' : SAtL a (New.ofDiv a.D N hh) R F eE F₁, SAtL.pt a (New.ofDiv a.D N hh) s' = tL a (New.ofDiv a.D N hh) s.t := by
  intro B C a G' _ _ Pl0 T A Ks _ _ iK R F F0 eE s N hh F₁ hS
  have hF : FinX (reY (New.ofDiv a.D N hh) s.P.Y) := finX_reY a.D (New.ofDiv a.D N hh) s.P.X s.P.Y s.P.fin
  have h : SameForms0LevelsAndValues (New.ofDiv a.D N hh) F0 ((by with_unfolding_all exact (F₁ :))) := hS
  obtain ⟨S', hj⟩ := SRest.exists_re_ofDiv N hh s.S h hF
  have hsee := mvSee a (New.ofDiv a.D N hh) R F s.P.X s.P.inst s.t s.see
  have hev := mvEv_holds a (New.ofDiv a.D N hh) R F s.P.X s.P.inst s.P.G s.t s.c s.ev
  have hrow := mvRowJ a (New.ofDiv a.D N hh) R s.P.X s.P.inst s.P.G s.t eE s.S.j s.rowJ
  letI := alg (reL a (New.ofDiv a.D N hh)) iK
  have hrow' := of_heq_cast (fun j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC s.P.X s.P.G =>
      RowJ (real (reL a (New.ofDiv a.D N hh)) R) (eL a (New.ofDiv a.D N hh) R eE) (XL a (New.ofDiv a.D N hh) s.P.X)
        (hL a (New.ofDiv a.D N hh) s.P.inst) (gdL a (New.ofDiv a.D N hh) s.P.G) (tL a (New.ofDiv a.D N hh) s.t)
        (jL a (New.ofDiv a.D N hh) j)) hj hrow
  let s' : SAt (real (reL a (New.ofDiv a.D N hh)) R) (face (reL a (New.ofDiv a.D N hh)) F) (eL a (New.ofDiv a.D N hh) R eE) F₁ :=
    { P := (by with_unfolding_all exact (s.P.re (New.ofDiv a.D N hh) h hF :))
      S := (by with_unfolding_all exact (S' :))
      t := tL a (New.ofDiv a.D N hh) s.t
      c := s.c
      c_pos := s.c_pos
      see := (by with_unfolding_all exact (hsee :))
      ev := (by with_unfolding_all exact (hev :))
      rowJ := (by with_unfolding_all exact (hrow' :)) }
  exact ⟨s', (by with_unfolding_all exact (Eq.refl (tL a (New.ofDiv a.D N hh) s.t) :))⟩

end GlobalTheory.Mem.SRe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralComparisonTransportedDivisionLatticeChanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spectralComparison_transported_divisionLatticeChange : ∀ (B : Base) (C : Cols B) (a : Late B C) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] (R : RealDat a.D A Ks) (F : Face a.D A) (F0 : ∀ u, Forms0 a.D u) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (s : SAt R F eE F0) (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ) (F₁ : ∀ u, Forms0 (reL a (New.ofDiv a.D N hh)).D u), SameL a (New.ofDiv a.D N hh) F0 F₁ → ∃ s' : SAtL a (New.ofDiv a.D N hh) R F eE F₁, SAtL.pt a (New.ofDiv a.D N hh) s' = tL a (New.ofDiv a.D N hh) s.t := by
  first | exact @GlobalTheory.Mem.SRe.sAtL_exists_ofDiv | exact GlobalTheory.Mem.SRe.sAtL_exists_ofDiv | (intros; apply GlobalTheory.Mem.SRe.sAtL_exists_ofDiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TautologicalFamilyRefinementCompatibleLieAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TautologicalFamilyRefinementCompatibleLieAlgebra
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam.TieUp

theorem exists_lift {ι : Type} {m k : ι → ℕ} {R K : Type} [CommRing R] [Field K] (a : R →+* K)
    (ha : Function.Injective a) {O : Subring K} (hO : ∀ x ∈ O, ∃ r, a r = x) {G : Mat m K} (hG : Par k O G) :
    ∃ G' : Mat m R, G'.map a = G ∧ ∀ τ, IsUnit (G' τ).det := by
  have h1 : ∀ τ i j, ∃ r, a r = G τ i j := fun τ i j => hO _ ((hG τ).1 i j)
  choose G' hG' using h1
  let G'' : Mat m R := fun τ => Matrix.of (G' τ)
  have e : G''.map a = G := by
    funext τ; ext i j; exact hG' τ i j
  refine ⟨G'', e, fun τ => ?_⟩
  obtain ⟨r, hr⟩ := hO _ (hG τ).2.2.1
  have hd : a (G'' τ).det = (G τ).det := by
    rw [← e]; exact a.map_det (G'' τ)
  refine IsUnit.of_mul_eq_one r (ha ?_)
  rw [map_mul, hd, hr, map_one, mul_inv_cancel₀ (hG.det_ne τ)]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (B Y : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn) (k : (E →+* ℂ) → ℕ) (S' : Fr (ratOf Y) Dw.mult k) (φ : B.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ B.X), Tied e B j f₀ S A₀ → Refines S S' φ f → ∃ (g₀ : EigFrame Z (constF e Y) (genericPt Y ≫ (f ≫ j) ≫ genι Z)) (A₁ : Mat Dw.mult Y.Fn), Tied e Y (f ≫ j) g₀ S' A₁ ∧ f₀.Coord (φ : B.Fn →+* Y.Fn) g₀ (A₁ * (A₀.map φ)⁻¹) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e B Y j f₀ S A₀ k S' φ f hT hR
  obtain ⟨A₁, hA₁⟩ := S'.nonempty (genericPoint Y.X)
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hT.1
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := Fr.det_ne hA₁
  have hmapd : ∀ {A : Mat Dw.mult B.Fn}, (∀ τ, (A τ).det ≠ 0) →
      ∀ τ, (A.map (φ : B.Fn →+* Y.Fn) τ).det ≠ 0 := fun {A} hA τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hA τ)
  have hgen : genericPt Y ≫ f = spMap (φ : B.Fn →+* Y.Fn) ≫ genericPt B := hR.hom
  have hx : genericPt Y ≫ (f ≫ j) ≫ genι Z = spMap (φ : B.Fn →+* Y.Fn) ≫ genericPt B ≫ j ≫ genι Z := by
    rw [Category.assoc, ← Category.assoc, hgen, Category.assoc]
  have hc : constF e Y = (φ : B.Fn →+* Y.Fn).comp (constF e B) :=
    RingHom.ext fun a => (φ.commutes _).symm
  have hst₀ : f₀.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f₀ inferInstance
  obtain ⟨g₀, hg₀⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ f₀ Y.Fn (constF e Y)
    (genericPt Y ≫ (f ≫ j) ≫ genι Z) (φ : B.Fn →+* Y.Fn) inferInstance hst₀ hx hc).2
    (A₁ * (A₀.map (φ : B.Fn →+* Y.Fn))⁻¹) fun τ => by
      rw [Pi.mul_apply, Matrix.det_mul, Pi.inv_apply, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      exact Ne.isUnit (mul_ne_zero (hA₁d τ) (inv_ne_zero (hmapd hA₀d τ)))
  refine ⟨g₀, A₁, ⟨hA₁, fun y A' hA' => ?_⟩, hg₀⟩
  obtain ⟨A, hA⟩ := S.nonempty (f y)
  obtain ⟨φ₁, fA, hfA⟩ := hT.2 (f y) A hA
  have hAd : ∀ τ, (A τ).det ≠ 0 := Fr.det_ne hA
  have hA'd : ∀ τ, (A' τ).det ≠ 0 := Fr.det_ne hA'
  let aY : Y.X.presheaf.stalk y →+* Y.Fn := algebraMap (Y.X.presheaf.stalk y) Y.X.functionField
  let aB : B.X.presheaf.stalk (f y) →+* B.Fn := algebraMap (B.X.presheaf.stalk (f y)) B.X.functionField
  let σ : B.X.presheaf.stalk (f y) →+* Y.X.presheaf.stalk y := (f.stalkMap y).hom
  have hcomp : (φ : B.Fn →+* Y.Fn).comp aB = aY.comp σ :=
    RingHom.ext fun a => map_algebraMap_stalk hR.hom y a
  obtain ⟨G, hG, hGd⟩ := exists_lift aY (IsFractionRing.injective (Y.X.presheaf.stalk y) Y.X.functionField)
    (fun x hx => mem_O_ratOf.1 hx) (hR.sub y A' hA' A hA)
  have hstA : fA.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ fA inferInstance
  have hσ : spMap σ ≫ stalkPt B (f y) = stalkPt Y y ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hx' : stalkPt Y y ≫ (f ≫ j) ≫ genι Z = spMap σ ≫ stalkPt B (f y) ≫ j ≫ genι Z := by
    rw [Category.assoc, ← Category.assoc, ← hσ, Category.assoc]
  obtain ⟨f', hf'⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ fA (Y.X.presheaf.stalk y) (σ.comp φ₁)
    (stalkPt Y y ≫ (f ≫ j) ≫ genι Z) σ inferInstance hstA hx' rfl).2 G hGd
  have hst' : f'.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f' inferInstance
  have haY : spMap aY ≫ stalkPt Y y = genericPt Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)
  have hx'' : genericPt Y ≫ (f ≫ j) ≫ genι Z = spMap aY ≫ stalkPt Y y ≫ (f ≫ j) ≫ genι Z := by
    rw [← haY, Category.assoc]
  have hc' : constF e Y = aY.comp (σ.comp φ₁) := by
    rw [← RingHom.comp_assoc, ← hcomp, RingHom.comp_assoc, hc, hfA.2.1]
  obtain ⟨T, hTc, -⟩ := ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ f' Y.Fn (constF e Y)
    (genericPt Y ≫ (f ≫ j) ≫ genι Z) aY inferInstance hst' hx'' hc').1 g₀).1
  have h1 := GlobalTheory.ShFam.CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f' _ _ _ g₀ σ aY G T inferInstance hf' hTc
  have h2 := GlobalTheory.ShFam.CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f₀ _ _ _ g₀ aB (φ : B.Fn →+* Y.Fn) _ _
    inferInstance hfA hg₀
  rw [hcomp] at h2
  have hu := ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ fA Y.Fn (constF e Y)
    (genericPt Y ≫ (f ≫ j) ≫ genι Z) (aY.comp σ) inferInstance hstA h1.1 h1.2.1).1 g₀).1.unique h1 h2
  have hG' : G.map aY = A' * (A.map (φ : B.Fn →+* Y.Fn))⁻¹ := hG
  rw [hG', Mat.map_mul, Mat.map_inv, ← mul_assoc, ← mul_assoc, mul_assoc A₁, Mat.inv_mul (hmapd hA₀d), mul_one] at hu
  have hT' : T = A₁ * A'⁻¹ := by
    have h3 := congrArg (fun M => M * A.map (φ : B.Fn →+* Y.Fn) * A'⁻¹) hu
    rwa [mul_assoc (T * A'), mul_assoc A₁, Mat.inv_mul (hmapd hAd), mul_one, mul_one, mul_assoc,
      Mat.mul_inv hA'd, mul_one] at h3
  exact ⟨σ.comp φ₁, f', hT' ▸ hTc⟩

end GlobalTheory.ShFam.TieUp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TautologicalFamilyRefinementCompatibleLieAlgebraStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautologicalFamily_refinement_compatible_lieAlgebraFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (B Y : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn) (k : (E →+* ℂ) → ℕ) (S' : Fr (ratOf Y) Dw.mult k) (φ : B.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ B.X), Tied e B j f₀ S A₀ → Refines S S' φ f → ∃ (g₀ : EigFrame Z (constF e Y) (genericPt Y ≫ (f ≫ j) ≫ genι Z)) (A₁ : Mat Dw.mult Y.Fn), Tied e Y (f ≫ j) g₀ S' A₁ ∧ f₀.Coord (φ : B.Fn →+* Y.Fn) g₀ (A₁ * (A₀.map φ)⁻¹) := by
  first | exact @GlobalTheory.ShFam.TieUp.main | exact GlobalTheory.ShFam.TieUp.main | (intros; apply GlobalTheory.ShFam.TieUp.main <;> assumption)
end
end
