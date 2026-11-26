module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSurjectiveOfOmegaMapSurjectiveConnected
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceStandardChartFubiniStudy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassBilinear

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.GCTrait

theorem spMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem map_cycAway_mem {n : ℕ} {L : Type} [Field L] (φ : cycAway n →+* L) (K : Subring L)
    (hz : φ (zetaAway n) ∈ K) (hi : φ ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ ∈ K) (c : cycAway n) : φ c ∈ K := by
  obtain ⟨c, hc⟩ := c
  induction hc using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hz
    · exact hi
  | zero => rw [show (⟨0, _⟩ : cycAway n) = 0 from rfl, map_zero]; exact K.zero_mem
  | one => rw [show (⟨1, _⟩ : cycAway n) = 1 from rfl, map_one]; exact K.one_mem
  | add x y hx hy ihx ihy =>
    rw [show (⟨x + y, _⟩ : cycAway n) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add (f := _)]; exact K.add_mem ihx ihy
  | neg x hx ih =>
    rw [show (⟨-x, _⟩ : cycAway n) = -⟨x, hx⟩ from rfl, map_neg]; exact K.neg_mem ih
  | mul x y hx hy ihx ihy =>
    rw [show (⟨x * y, _⟩ : cycAway n) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]; exact K.mul_mem ihx ihy

theorem exists_finite_point (n : ℕ) {X : Scheme.{0}} (s : X ⟶ Sp (cycAway n)) [LocallyOfFiniteType s]
    (p : ℕ) [Fact p.Prime] (y : Sp (PadicAlgCl p) ⟶ X) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K) (x : Sp K ⟶ X),
      spMap (algebraMap K (PadicAlgCl p)) ≫ x = y := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := y (default : PrimeSpectrum (PadicAlgCl p))) trivial
  have hr : Set.range y ⊆ Set.range hU.fromSpec := by
    rintro _ ⟨q, rfl⟩
    rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) q default]
    exact hy
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hU.fromSpec y hr)
  obtain ⟨a, ha⟩ := Spec.map_surjective (hU.fromSpec ≫ s)
  have hft : a.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), ha]
    infer_instance
  letI := a.hom.toAlgebra
  obtain ⟨T, hT⟩ := Algebra.FiniteType.out (R := cycAway n) (A := Γ(X, U)) (self := hft)
  let S : Set (PadicAlgCl p) := φ.hom '' (T : Set Γ(X, U)) ∪
    {φ.hom (a.hom (zetaAway n)), φ.hom (a.hom ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩)}
  have hSfin : S.Finite := (T.finite_toSet.image _).union (Set.toFinite _)
  haveI : Finite S := hSfin.to_subtype
  let K := IntermediateField.adjoin ℚ_[p] S
  have hK : FiniteDimensional ℚ_[p] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hS : S ⊆ K := IntermediateField.subset_adjoin ℚ_[p] S
  have hc : ∀ c : cycAway n, φ.hom (a.hom c) ∈ K.toSubfield.toSubring :=
    map_cycAway_mem (φ.hom.comp a.hom) K.toSubfield.toSubring
      (hS (Or.inr (Or.inl rfl))) (hS (Or.inr (Or.inr rfl)))
  have hmem : ∀ b, φ.hom b ∈ K := fun b => by
    have hb : b ∈ Algebra.adjoin (cycAway n) (T : Set Γ(X, U)) := hT ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact hS (Or.inl ⟨x, hx, rfl⟩)
    | algebraMap c => exact hc c
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact K.add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact K.mul_mem ha hb
  let φK : Γ(X, U) →+* K := φ.hom.codRestrict K hmem
  refine ⟨K, hK, spMap φK ≫ hU.fromSpec, ?_⟩
  rw [← Category.assoc, spMap_comp'', ← IsOpenImmersion.lift_fac hU.fromSpec y hr, ← hφ]
  rfl

theorem exists_ext_emb (p : ℕ) [Fact p.Prime] (V W : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : V →+* W) (fK : FractionRing V →+* FractionRing W)
    (hinj : Function.Injective f) (hloc : IsLocalHom f) (hfin : f.Finite)
    (hc : ∀ a, fK (algebraMap V _ a) = algebraMap W _ (f a)) (κ : FractionRing V →+* PadicAlgCl p)
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ∃ ι : FractionRing W →+* PadicAlgCl p, ι.comp fK = κ ∧
      ∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W)) := by
  letI : Algebra V W := f.toAlgebra
  letI : Algebra (FractionRing V) (FractionRing W) := fK.toAlgebra
  letI : Algebra (FractionRing V) (PadicAlgCl p) := κ.toAlgebra
  haveI : Algebra.IsIntegral V W := ⟨fun w => hfin.to_isIntegral w⟩
  haveI : IsLocalHom (algebraMap V W) := hloc
  have hint : ∀ w : W, IsIntegral (FractionRing V) (algebraMap W (FractionRing W) w) := fun w =>
    IsIntegral.map_of_comp_eq (algebraMap V (FractionRing V)) (algebraMap W (FractionRing W))
      (RingHom.ext fun v => hc v) (Algebra.IsIntegral.isIntegral w)
  haveI : Algebra.IsAlgebraic (FractionRing V) (FractionRing W) := by
    constructor
    intro z
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W) z
    rw [div_eq_mul_inv]
    exact ((hint a).mul (hint b).inv).isAlgebraic
  let ι : FractionRing W →ₐ[FractionRing V] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hι : ι.toRingHom.comp fK = κ := RingHom.ext fun x => ι.commutes x
  refine ⟨ι.toRingHom, hι, GlobalTheory.unitBall_eq_of_integral_dvr p V W hinj κ ι.toRingHom (fun v => ?_) hV⟩
  show ι (algebraMap W (FractionRing W) (f v)) = _
  rw [← hc]
  exact ι.commutes _

theorem exists_cTrait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X₁.M.Z), Set.range (gPt p ≫ y ≫ X₁.π) ⊆ Set.range i → ∃ c : CTrait X₁ p (y (cPt p)), c.y = y := by
  intro g n F W Z i X₁ hg hn hodd hi p _ y hr
  let y₁ : Sp (PadicAlgCl p) ⟶ F.X := IsOpenImmersion.lift i (gPt p ≫ y ≫ X₁.π) hr
  have hy₁ : y₁ ≫ i = gPt p ≫ y ≫ X₁.π := IsOpenImmersion.lift_fac _ _ _
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  obtain ⟨K, hK, x, hx⟩ := exists_finite_point n F.s p y₁
  obtain ⟨hdvr, hcomp, hunit⟩ := GlobalTheory.intRing_complete_dvr p K hK
  haveI := hdvr
  haveI : CharZero (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := inferInstance
  let e : FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ≃ₐ[GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K] K := FractionRing.algEquiv _ K
  let es : K →+* FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := e.symm.toRingEquiv.toRingHom
  have hbase : GlobalTheory.Mum.Base (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
  obtain ⟨T, f, fK, hinj, hloc, hfin, hc, hTy⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n (cycAway n) (zetaAway n) F _ hbase hdvr (spMap es ≫ x)
  obtain ⟨ι, hι, hint⟩ := exists_ext_emb p _ T.V f fK hinj hloc hfin hc _ hunit
  have h2 : algebraMap (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (PadicAlgCl p) =
      (algebraMap K (PadicAlgCl p)).comp e.toRingEquiv.toRingHom := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (RingHom.ext fun v => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
    refine (IsFractionRing.lift_algebraMap (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing_injective K) v).trans ?_
    show _ = algebraMap K (PadicAlgCl p) (e (algebraMap _ _ v))
    rw [AlgEquiv.commutes]
    rfl
  have hκ : (algebraMap (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (PadicAlgCl p)).comp es = algebraMap K (PadicAlgCl p) := by
    ext k
    rw [h2]
    show algebraMap K (PadicAlgCl p) (e (e.symm k)) = _
    rw [AlgEquiv.apply_symm_apply]
  have key : spMap ι ≫ spMap fK ≫ spMap es = spMap (algebraMap K (PadicAlgCl p)) := by
    rw [spMap_comp'', spMap_comp'', ← RingHom.comp_assoc, hι, hκ]
  refine ⟨⟨y, rfl, T, ι, hint, ?_⟩, rfl⟩
  calc gPt p ≫ y ≫ X₁.π = y₁ ≫ i := hy₁.symm
    _ = (spMap (algebraMap K (PadicAlgCl p)) ≫ x) ≫ i := by rw [hx]
    _ = ((spMap ι ≫ spMap fK ≫ spMap es) ≫ x) ≫ i := by rw [key]
    _ = spMap ι ≫ T.y ≫ i := by rw [hTy]; simp only [Category.assoc]

end GlobalTheory.Poinc.GCTrait
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDifferentialsConnectedPDivGroupCoordina
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDifferentialsConnectedPDivGroupCoordina
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.OmegaCoord

variable {k : Type} [CommRing k] {d : ℕ}

theorem coeff_eq_zero_of_mem_sq {g : MvPowerSeries (Fin d) k}
    (hg : g ∈ RingHom.ker (constantCoeff (R := k) (σ := Fin d)) ^ 2) (α : Fin d →₀ ℕ)
    (hα : α.degree < 2) : coeff α g = 0 := by
  rw [pow_two] at hg
  refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [coeff_mul]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hdeg : q.1.degree + q.2.degree < 2 := by rw [← map_add (f := _), hq]; exact hα
    rw [RingHom.mem_ker] at ha hb
    rcases Nat.lt_or_ge q.1.degree 1 with h | h
    · have : q.1 = 0 := (Finsupp.degree_eq_zero_iff _).1 (by omega)
      rw [this, coeff_zero_eq_constantCoeff_apply, ha, zero_mul]
    · have : q.2 = 0 := (Finsupp.degree_eq_zero_iff _).1 (by omega)
      rw [this, coeff_zero_eq_constantCoeff_apply, hb, mul_zero]
  · rw [map_add (f := _), ha, hb, add_zero]

variable {A : Type} [CommRing A] [Bialgebra k A] (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i))
  (haug : ∀ i, Coalgebra.counit (R := k) (x i) = 0)


include haug in
theorem exists_eq_sum (hsurj : Function.Surjective (evA k x hx)) (u : Cot k A) :
    ∃ w : Fin d → k, u = ∑ i, w i • dUnit (R := k) (x i) := by
  obtain ⟨a, rfl⟩ := AugCot.d_surjective _ u
  obtain ⟨f, rfl⟩ := hsurj a
  exact ⟨lin f, (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d A x hx haug f).2⟩


include haug in
theorem eq_zero_of_sum (hsurj : Function.Surjective (evA k x hx))
    (hker : ∀ f, evA k x hx f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < 2 → coeff α f = 0)
    (w : Fin d → k) (hw : ∑ i, w i • dUnit (R := k) (x i) = 0) : w = 0 := by
  set f : MvPowerSeries (Fin d) k := ∑ i, w i • X i with hf
  have hlin : lin f = w := by
    funext i
    simp [f, lin, coeff_X, Finsupp.single_eq_single_iff]
  have hcc : constantCoeff f = 0 := by simp [f]
  obtain ⟨h1, h2⟩ := GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d A x hx haug f
  have hd : dUnit (R := k) (evA k x hx f) = 0 := by rw [h2, hlin, hw]
  have hε : ∀ g, Bialgebra.counitAlgHom k A (evA k x hx g) = constantCoeff g := fun g =>
    (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d A x hx haug g).1
  rw [dUnit, AugCot.d_eq_zero_iff, hε, hcc, map_zero, sub_zero] at hd
  have hK : RingHom.ker (Bialgebra.counitAlgHom k A) =
      Ideal.map (evA k x hx) (RingHom.ker (constantCoeff (R := k) (σ := Fin d))) := by
    ext a
    rw [Ideal.mem_map_iff_of_surjective _ hsurj]
    constructor
    · intro ha
      obtain ⟨g, rfl⟩ := hsurj a
      refine ⟨g, ?_, rfl⟩
      rw [RingHom.mem_ker] at ha ⊢
      rw [← hε]; exact ha
    · rintro ⟨g, hg, rfl⟩
      rw [RingHom.mem_ker] at hg ⊢
      rw [hε]; exact hg
  rw [hK, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ hsurj] at hd
  obtain ⟨g, hg, hgf⟩ := hd
  have hfg : evA k x hx (f - g) = 0 := by rw [map_sub, hgf, sub_self]
  funext i
  have hdeg : (Finsupp.single i 1 : Fin d →₀ ℕ).degree < 2 := by simp
  have e1 := hker _ hfg (Finsupp.single i 1) hdeg
  rw [map_sub, coeff_eq_zero_of_mem_sq hg _ hdeg, sub_zero] at e1
  rw [← hlin]; exact e1

end GlobalTheory.OmegaCoord

namespace GlobalTheory.OmegaCoord

theorem omega_coord : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), (∀ w : Fin d → k, (fun n => ∑ i, w i • dUnit (R := k) (c.x n i)) ∈ G.omegaSub) ∧
      ∀ u : G.omega, ∃! w : Fin d → k, ∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i) := by
  intro p k _ d G c
  have hres : ∀ n (w : Fin d → k), cotMap (G.res n) (∑ i, w i • dUnit (R := k) (c.x (n + 1) i)) =
      ∑ i, w i • dUnit (R := k) (c.x n i) := by
    intro n w
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, cotMap_d, c.res]
  refine ⟨fun w n => hres n w, fun u => ?_⟩
  have hu : ∀ n, cotMap (G.res n) (u.1 (n + 1)) = u.1 n := u.2
  obtain ⟨n0, hn0⟩ := c.presents.2 2
  have hone := (GlobalTheory.T.functions_eq_series_in_chart p k d G c).1
  have hker : ∀ j f, c.ev (n0 + j) f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < 2 → coeff α f = 0 := by
    intro j
    induction j with
    | zero => exact hn0
    | succ j ih =>
      intro f hf
      refine ih f ?_
      rw [← hone (n0 + j) f]
      exact (congrArg (G.res (n0 + j)) hf).trans (map_zero _)
  have hind : ∀ j (v w : Fin d → k), ∑ i, v i • dUnit (R := k) (c.x (n0 + j) i) =
      ∑ i, w i • dUnit (R := k) (c.x (n0 + j) i) → v = w := by
    intro j v w h
    have := eq_zero_of_sum (c.x (n0 + j)) (c.nil _) (c.aug _) (c.presents.1 _) (hker j) (v - w)
      (by simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self])
    exact sub_eq_zero.1 this
  have hspan : ∀ n, ∃ w : Fin d → k, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i) := fun n =>
    exists_eq_sum (c.x n) (c.nil n) (c.aug n) (c.presents.1 n) (u.1 n)
  obtain ⟨w, hw⟩ := hspan n0
  have hup : ∀ j, u.1 (n0 + j) = ∑ i, w i • dUnit (R := k) (c.x (n0 + j) i) := by
    intro j
    induction j with
    | zero => exact hw
    | succ j ih =>
      obtain ⟨v, hv⟩ := hspan (n0 + j + 1)
      have h1 : ∑ i, v i • dUnit (R := k) (c.x (n0 + j) i) = ∑ i, w i • dUnit (R := k) (c.x (n0 + j) i) := by
        rw [← hres, ← hv, hu, ih]
      rw [← hind j v w h1]
      exact hv
  have hdown : ∀ n j, u.1 (n + j) = ∑ i, w i • dUnit (R := k) (c.x (n + j) i) →
      u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i) := by
    intro n j
    induction j with
    | zero => exact id
    | succ j ih =>
      intro h
      refine ih ?_
      rw [← hu, ← hres]
      exact congrArg (cotMap (G.res (n + j))) h
  refine ⟨w, fun n => hdown n n0 (by rw [Nat.add_comm]; exact hup n), fun w' hw' => ?_⟩
  exact hind 0 w' w ((hw' n0).symm.trans (hup 0))

end GlobalTheory.OmegaCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDifferentialsConnectedPDivGroupCoordinaStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), (∀ w : Fin d → k, (fun n => ∑ i, w i • dUnit (R := k) (c.x n i)) ∈ G.omegaSub) ∧ ∀ u : G.omega, ∃! w : Fin d → k, ∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i) := by
  first | exact @GlobalTheory.OmegaCoord.omega_coord | exact GlobalTheory.OmegaCoord.omega_coord | (intros; apply GlobalTheory.OmegaCoord.omega_coord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridMovedTensorBoundedSupportLocallyConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridMovedTensorBoundedSupportLocallyConstant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

namespace GlobalTheory.MovedBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_le_inv_pow {ϖ : kˣ} (hϖ : IsUnif ϖ) (x : k) :
    ∃ n : ℕ, valuation k x ≤ (valuation k (ϖ : k) ^ n)⁻¹ := by
  have h1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hv : (valuation k x)⁻¹ ≠ 0 := by simp [hx]
  obtain ⟨m, hm⟩ := exists_pow_lt₀ h1 (Units.mk0 _ hv)
  have hu : 0 < valuation k (ϖ : k) ^ m := by
    rw [pos_iff_ne_zero]; simp
  refine ⟨m, ?_⟩
  have hx0 : 0 < valuation k x := by rw [pos_iff_ne_zero]; simp [hx]
  exact (le_inv_comm₀ hu hx0).1 (by simpa using hm.le)

theorem inv_pow_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) {n N : ℕ} (h : n ≤ N) :
    (valuation k (ϖ : k) ^ n)⁻¹ ≤ (valuation k (ϖ : k) ^ N)⁻¹ := by
  have h1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hu : 0 < valuation k (ϖ : k) ^ N := by rw [pos_iff_ne_zero]; simp
  exact inv_anti₀ hu (pow_le_pow_right_of_le_one' h1.le h)

theorem exists_uniform {α : Type*} (s : Finset α) (P : α → ℕ → Prop)
    (hP : ∀ a n N, n ≤ N → P a n → P a N) (h : ∀ a ∈ s, ∃ n, P a n) : ∃ n, ∀ a ∈ s, P a n := by
  classical
  choose f hf using h
  exact ⟨s.attach.sup fun a => f a.1 a.2, fun a ha =>
    hP _ _ _ (Finset.le_sup (f := fun a : s => f a.1 a.2) (Finset.mem_attach s ⟨a, ha⟩)) (hf a ha)⟩

theorem exists_matrix_bound {ϖ : kˣ} (hϖ : IsUnif ϖ) {m n : Type*} [Fintype m] [Fintype n] (P : Matrix m n k) :
    ∃ N : ℕ, ∀ r s, valuation k (P r s) ≤ (valuation k (ϖ : k) ^ N)⁻¹ := by
  obtain ⟨N, hN⟩ := exists_uniform (Finset.univ : Finset (m × n))
    (fun rs N => valuation k (P rs.1 rs.2) ≤ (valuation k (ϖ : k) ^ N)⁻¹)
    (fun _ _ _ h h' => h'.trans (inv_pow_mono hϖ h)) (fun rs _ => exists_le_inv_pow hϖ _)
  exact ⟨N, fun r s => hN (r, s) (Finset.mem_univ _)⟩

theorem val_mul_mul_le {a b c d : Type*} [Fintype b] [Fintype c] (P : Matrix a b k) (X : Matrix b c k)
    (Q : Matrix c d k) (p x q : ValueGroupWithZero k) (hP : ∀ r s, valuation k (P r s) ≤ p)
    (hX : ∀ r s, valuation k (X r s) ≤ x) (hQ : ∀ r s, valuation k (Q r s) ≤ q) (r : a) (s : d) :
    valuation k ((P * X * Q) r s) ≤ p * x * q := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul, Matrix.mul_apply]
  refine mul_le_mul' (Valuation.map_sum_le _ fun i _ => ?_) (hQ _ _)
  rw [map_mul]
  exact mul_le_mul' (hP _ _) (hX _ _)

end GlobalTheory.MovedBound

namespace GlobalTheory.MovedBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_unitsPow_inv (ϖ : kˣ) (n : ℕ) :
    valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) = (valuation k (ϖ : k) ^ n)⁻¹ := by
  simp [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow]

theorem val_unitsPow (ϖ : kˣ) (n : ℕ) :
    valuation k ((ϖ ^ n : kˣ) : k) = valuation k (ϖ : k) ^ n := by
  simp [Units.val_pow_eq_pow_val, map_pow]

end GlobalTheory.MovedBound


open GlobalTheory.MovedBound in
theorem GlobalTheory.MovedBound.moved_bounded_locConst : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, (∀ z : G.Args, moved G keep g T z ≠ 0 → ∀ b ∈ oppositePath G.m, ∀ r s, valuation k (z b r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)) ∧ ∀ z δ : G.Args, (∀ b ∈ oppositePath G.m, ∀ r s, valuation k (δ b r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → moved G keep g T (z + δ) = moved G keep g T z := by
  intro k _ _ _ _ G ϖ e T keep g hϖ hT
  classical
  set u := valuation k (ϖ : k) with hu_def
  have hu0 : u ≠ 0 := by simp [u]
  have hu1 : u ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  let A : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.tgt)) k := fun b => ((Assignment.one.read (g b.tgt))⁻¹).val
  let Ai : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.tgt)) k := fun b => (Assignment.one.read (g b.tgt)).val
  let B : ∀ b : Edge, Matrix (Fin (G.rank b.src)) (Fin (G.rank b.src)) k := fun b => (Assignment.one.read (g b.src)).val
  let Bi : ∀ b : Edge, Matrix (Fin (G.rank b.src)) (Fin (G.rank b.src)) k := fun b => ((Assignment.one.read (g b.src))⁻¹).val
  obtain ⟨n0, hn0⟩ := exists_uniform (oppositePath G.m).toFinset
    (fun b N => (∀ r s, valuation k (A b r s) ≤ (u ^ N)⁻¹) ∧ (∀ r s, valuation k (Ai b r s) ≤ (u ^ N)⁻¹) ∧
      (∀ r s, valuation k (B b r s) ≤ (u ^ N)⁻¹) ∧ (∀ r s, valuation k (Bi b r s) ≤ (u ^ N)⁻¹))
    (fun _ _ _ h ⟨h1, h2, h3, h4⟩ => ⟨fun r s => (h1 r s).trans (inv_pow_mono hϖ h),
      fun r s => (h2 r s).trans (inv_pow_mono hϖ h), fun r s => (h3 r s).trans (inv_pow_mono hϖ h),
      fun r s => (h4 r s).trans (inv_pow_mono hϖ h)⟩)
    (fun b _ => by
      obtain ⟨n1, h1⟩ := exists_matrix_bound hϖ (A b)
      obtain ⟨n2, h2⟩ := exists_matrix_bound hϖ (Ai b)
      obtain ⟨n3, h3⟩ := exists_matrix_bound hϖ (B b)
      obtain ⟨n4, h4⟩ := exists_matrix_bound hϖ (Bi b)
      refine ⟨n1 + n2 + n3 + n4, fun r s => (h1 r s).trans (inv_pow_mono hϖ (by omega)),
        fun r s => (h2 r s).trans (inv_pow_mono hϖ (by omega)), fun r s => (h3 r s).trans (inv_pow_mono hϖ (by omega)),
        fun r s => (h4 r s).trans (inv_pow_mono hϖ (by omega))⟩)
  have hmv : ∀ x : G.Args, ∀ b, G.moveArgs .one g x b = A b * x b * B b := fun _ _ => rfl
  refine ⟨2 * n0 + e, ?_, ?_⟩
  · intro z hz b hb r s
    have hT0 : T (G.moveArgs .one g z) ≠ 0 := by
      intro h0; apply hz; simp [moved, Grid.pathAct, h0]
    have hint : G.moveArgs .one g z b ∈ matLat _ (stdLat k _) := by
      by_contra hc; exact hT0 (hT.2.1 _ b hb hc)
    have hint' := mem_matLat_stdLat.1 hint
    have hz' : z b = Ai b * G.moveArgs .one g z b * Bi b := by
      simp [hmv, A, Ai, B, Bi, ← Matrix.mul_assoc]
    obtain ⟨-, h2, -, h4⟩ := hn0 b (List.mem_toFinset.2 hb)
    rw [hz', val_unitsPow_inv]
    refine (val_mul_mul_le _ _ _ _ 1 _ h2 (fun r s => (hint' r s)) h4 r s).trans ?_
    rw [mul_one, ← mul_inv, ← pow_add]
    exact inv_pow_mono hϖ (by omega)
  · intro z δ hδ
    let δ' : G.Args := fun b => if b ∈ oppositePath G.m then G.moveArgs .one g δ b else 0
    have h1 : T (G.moveArgs .one g (z + δ)) = T (G.moveArgs .one g z + δ') := by
      refine hT.1 fun b hb => ?_
      simp only [Set.mem_setOf_eq] at hb
      simp [δ', hb, hmv, Matrix.mul_add, Matrix.add_mul]
    have h2 : T (G.moveArgs .one g z + δ') = T (G.moveArgs .one g z) := by
      refine hT.2.2 _ _ fun b => ?_
      by_cases hb : b ∈ oppositePath G.m
      · simp only [δ', hb, if_true]
        obtain ⟨h1, -, h3, -⟩ := hn0 b (List.mem_toFinset.2 hb)
        have hd : ∀ r s, valuation k (δ b r s) ≤ u ^ (2 * n0 + e) := fun r s => by
          rw [← val_unitsPow]; exact hδ b hb r s
        have hbd : ∀ r s, valuation k (G.moveArgs .one g δ b r s) ≤ u ^ e := fun r s => by
          rw [hmv]
          refine (val_mul_mul_le _ _ _ _ _ _ h1 hd h3 r s).trans (le_of_eq ?_)
          rw [show 2 * n0 + e = n0 + (n0 + e) by ring, pow_add, pow_add]
          field_simp
        rw [mem_matLat]
        intro i
        rw [mem_smul_lat, mem_stdLat]
        intro j
        rw [Valuation.mem_integer_iff]
        simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul, Matrix.row_apply]
        rw [map_mul, val_unitsPow_inv]
        calc (u ^ e)⁻¹ * valuation k (G.moveArgs .one g δ b i j) ≤ (u ^ e)⁻¹ * u ^ e := mul_le_mul' le_rfl (hbd i j)
          _ = 1 := inv_mul_cancel₀ (pow_ne_zero _ hu0)
      · simp only [δ', hb, if_false]
        exact zero_mem _
    simp only [moved, Grid.pathAct, h1, h2]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridMovedTensorBoundedSupportLocallyConstantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridMovedTensor_bounded_support_locallyConstant : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, (∀ z : G.Args, moved G keep g T z ≠ 0 → ∀ b ∈ oppositePath G.m, ∀ r s, valuation k (z b r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)) ∧ ∀ z δ : G.Args, (∀ b ∈ oppositePath G.m, ∀ r s, valuation k (δ b r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → moved G keep g T (z + δ) = moved G keep g T z := by
  first | exact @GlobalTheory.MovedBound.moved_bounded_locConst | exact GlobalTheory.MovedBound.moved_bounded_locConst | (intros; apply GlobalTheory.MovedBound.moved_bounded_locConst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralAdditiveInFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralAddOfDensityAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralAddOfDensityAdd
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem GlobalTheory.Mix.part_le_add_of_dens_add {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L₁ L₂ L₃ : Fin D → MLine p σ)
    (h : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, dens L₁ c y = dens L₂ c y + dens L₃ c y) (ε : ℤˣ) :
    part L₁ ε ≤ part L₂ ε + part L₃ ε := by
  unfold part glueMeas
  refine iSup_le fun c => ?_
  refine le_trans ?_ (add_le_add
    (le_iSup (fun c : AlgChart p σ D => chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * dens L₂ c y)) c)
    (le_iSup (fun c : AlgChart p σ D => chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * dens L₃ c y)) c))
  refine Measure.le_iff.2 fun A hA => ?_
  have hB : MeasurableSet (c.e.source ∩ A) := c.e.open_source.measurableSet.inter hA
  have hI := GlobalTheory.ChartGlue.measurableSet_image c.e hB inter_subset_left
  have hsub : c.e '' (c.e.source ∩ A) ⊆ c.e.target := fun _ ⟨y, hy, e⟩ => e ▸ c.e.map_source hy.1
  have hcont : ContinuousOn (fun v => dens L₂ c (c.e.symm v)) c.e.target :=
    (GlobalTheory.T.continuousOn_mixedChernFormDensityInChart k X p σ D L₂ c).comp c.e.continuousOn_symm c.e.mapsTo_symm
  have hm : AEMeasurable (fun v => ENNReal.ofReal (((ε : ℤ) : ℝ) * dens L₂ c (c.e.symm v)))
      (volume.restrict (c.e '' (c.e.source ∩ A))) :=
    (((hcont.aemeasurable c.e.open_target.measurableSet).const_mul _).ennreal_ofReal).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  rw [Measure.add_apply, chartMeas_apply _ _ hA, chartMeas_apply _ _ hA, chartMeas_apply _ _ hA,
    ← lintegral_add_left' hm]
  refine setLIntegral_mono' hI fun v hv => ?_
  beta_reduce
  rw [h c _ (c.e.map_target (hsub hv)), mul_add]
  exact ENNReal.ofReal_add_le

theorem GlobalTheory.Mix.int_add_of_dens_add : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L₁ L₂ L₃ : Fin D → MLine p σ), (∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, dens L₁ c y = dens L₂ c y + dens L₃ c y) → ∀ f : CxPts p σ → ℝ, (Intg L₂ f → Intg L₃ f → Intg L₁ f) ∧ (Intg L₁ f → Intg L₂ f → Intg L₃ f → Mix.int L₁ f = Mix.int L₂ f + Mix.int L₃ f) := by
  intro k _ X p σ _ D L₁ L₂ L₃ h f
  refine ⟨fun h₂ h₃ => ⟨(h₂.1.add_measure h₃.1).mono_measure (GlobalTheory.Mix.part_le_add_of_dens_add L₁ L₂ L₃ h 1),
    (h₂.2.add_measure h₃.2).mono_measure (GlobalTheory.Mix.part_le_add_of_dens_add L₁ L₂ L₃ h (-1))⟩, fun h₁ h₂ h₃ => ?_⟩
  have := GlobalTheory.T.linear_relation_mixed_densities_integrals k X p σ D (Fin 3) ![1, -1, -1] ![L₁, L₂, L₃]
    (fun c y hy => by
      rw [Fin.sum_univ_three]
      show 1 * dens L₁ c y + -1 * dens L₂ c y + -1 * dens L₃ c y = 0
      rw [h c y hy]; ring) f
    (fun i => by
      fin_cases i
      · exact h₁
      · exact h₂
      · exact h₃)
  rw [Fin.sum_univ_three] at this
  change 1 * Mix.int L₁ f + -1 * Mix.int L₂ f + -1 * Mix.int L₃ f = 0 at this
  linarith
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralAddOfDensityAddStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChern_integral_add_of_density_add : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L₁ L₂ L₃ : Fin D → MLine p σ), (∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, dens L₁ c y = dens L₂ c y + dens L₃ c y) → ∀ f : CxPts p σ → ℝ, (Intg L₂ f → Intg L₃ f → Intg L₁ f) ∧ (Intg L₁ f → Intg L₂ f → Intg L₃ f → Mix.int L₁ f = Mix.int L₂ f + Mix.int L₃ f) := by
  first | exact @GlobalTheory.Mix.int_add_of_dens_add | exact GlobalTheory.Mix.int_add_of_dens_add | (intros; apply GlobalTheory.Mix.int_add_of_dens_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormDensityUpdateTensorAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormDensityUpdateTensorAdd
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem det_perm_update_add {D : ℕ} (F : Fin D → Matrix (Fin D) (Fin D) ℂ) (i : Fin D)
    (P Q : Matrix (Fin D) (Fin D) ℂ) (τ : Equiv.Perm (Fin D)) :
    (Matrix.of fun j l => Function.update F i (P + Q) (τ l) j l).det =
      (Matrix.of fun j l => Function.update F i P (τ l) j l).det +
      (Matrix.of fun j l => Function.update F i Q (τ l) j l).det := by
  have key : ∀ R : Matrix (Fin D) (Fin D) ℂ, (Matrix.of fun j l => Function.update F i R (τ l) j l) =
      (Matrix.of fun j l => Function.update F i 0 (τ l) j l).updateCol (τ.symm i)
        (fun j => R j (τ.symm i)) := by
    intro R
    ext j l
    by_cases h : l = τ.symm i
    · subst h
      simp
    · have hl : τ l ≠ i := fun e => h (by rw [← e, Equiv.symm_apply_apply])
      simp [Matrix.updateCol_ne h, Function.update_of_ne hl]
  rw [key (P + Q), key P, key Q, ← Matrix.det_updateCol_add]
  rfl

theorem dens_update_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → MLine p σ) (i : Fin D) (A B : MLine p σ) (c : AlgChart p σ D), ∀ y ∈ c.e.source, dens (Function.update L i (A.tens B)) c y = dens (Function.update L i A) c y + dens (Function.update L i B) c y := by
  intro k _ X p σ D L i A B c y hy
  let G : MLine p σ → Matrix (Fin D) (Fin D) ℂ := fun M => c.hess M.φ (pick M.φ.isLB y) y
  have hd : ∀ L' : Fin D → MLine p σ, dens L' c y = (Real.pi ^ D)⁻¹ *
      (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => (G ∘ L') (τ l) j l).det).re := fun _ => rfl
  have hT : G (A.tens B) = G A + G B := by
    have ha := mem_pick A.φ.isLB y
    have hb := mem_pick B.φ.isLB y
    have hab : y ∈ ptsIn p σ ((A.tens B).B.U (pick A.φ.isLB y, pick B.φ.isLB y)) :=
      mem_ptsIn_inf.2 ⟨ha, hb⟩
    show c.hess (A.tens B).φ _ y = _
    rw [c.hess_eq (A.tens B).cInf hy hab (mem_pick _ y)]
    have ho := isOpen_over c.e
      (isOpen_ptsIn (p := p) (σ := σ) (A.B.U (pick A.φ.isLB y) ⊓ B.B.U (pick B.φ.isLB y)))
    have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
    have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
      ((contDiffOn_chart (A.cInf _) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩)
      ((contDiffOn_chart (B.cInf _) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩) 1 hm
    simp only [one_mul, Complex.ofReal_one, one_smul, Function.comp_apply] at e
    exact e
  rw [hd, hd, hd, Function.comp_update, Function.comp_update, Function.comp_update, hT]
  simp only [det_perm_update_add, Finset.sum_add_distrib, Complex.add_re]
  ring

end GlobalTheory.Mix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormDensityUpdateTensorAddStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernFormDensity_update_tensor_add : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → MLine p σ) (i : Fin D) (A B : MLine p σ) (c : AlgChart p σ D), ∀ y ∈ c.e.source, dens (Function.update L i (A.tens B)) c y = dens (Function.update L i A) c y + dens (Function.update L i B) c y := by
  first | exact @GlobalTheory.Mix.dens_update_tens | exact GlobalTheory.Mix.dens_update_tens | (intros; apply GlobalTheory.Mix.dens_update_tens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralAdditiveInFactor
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem int_update_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ) (i : Fin D) (A B : MLine p σ) (f : CxPts p σ → ℝ), Intg (Function.update L i A) f → Intg (Function.update L i B) f → Intg (Function.update L i (A.tens B)) f ∧ Mix.int (Function.update L i (A.tens B)) f = Mix.int (Function.update L i A) f + Mix.int (Function.update L i B) f := by
  intro k _ X p σ hp D L i A B f hA hB
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hp
  have h := GlobalTheory.T.mixedChern_integral_add_of_density_add k X p σ D _ _ _ (fun c => GlobalTheory.T.mixedChernFormDensity_update_tensor_add k X p σ D L i A B c) f
  exact ⟨h.1 hA hB, h.2 (h.1 hA hB) hA hB⟩

end GlobalTheory.Mix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralAdditiveInFactorStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernIntegral_additive_in_factor : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ) (i : Fin D) (A B : MLine p σ) (f : CxPts p σ → ℝ), Intg (Function.update L i A) f → Intg (Function.update L i B) f → Intg (Function.update L i (A.tens B)) f ∧ Mix.int (Function.update L i (A.tens B)) f = Mix.int (Function.update L i A) f + Mix.int (Function.update L i B) f := by
  first | exact @GlobalTheory.Mix.int_update_tens | exact GlobalTheory.Mix.int_update_tens | (intros; apply GlobalTheory.Mix.int_update_tens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSpaceOrderArithVarietyFubiniStudyDegre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSpaceOrderArithVarietyFubiniStudyDegre
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open ReciprocityTheory.AnForm.M
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PSpaceDeg

theorem ringKrullDim_eq_one (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] :
    ringKrullDim k = 1 := by
  rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (A := ℤ) (B := k)
    (algebraMap ℤ k).injective_int]
  exact IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

theorem isArithVar (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ) :
    IsArithVar (PSpace.str k D) D :=
  ProjModel.isArithVar_pspace k (ringKrullDim_eq_one k) D

theorem injective_ringHom {k : Type} [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    (ψ : k →+* ℂ) : Function.Injective ψ := by
  refine (RingHom.injective_iff_ker_eq_bot ψ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
  change Ideal.comap (algebraMap ℤ k) (RingHom.ker ψ) = ⊥
  rw [RingHom.comap_ker]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)

def ringHomEquiv (k K : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] [Field K]
    [Algebra k K] [IsFractionRing k K] : (k →+* ℂ) ≃ (K →+* ℂ) where
  toFun ψ := IsFractionRing.lift (injective_ringHom ψ)
  invFun φ := φ.comp (algebraMap k K)
  left_inv ψ := by
    ext x
    rw [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (injective_ringHom ψ) x
  right_inv φ := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors k) (RingHom.ext fun x => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (injective_ringHom (φ.comp (algebraMap k K))) x

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

theorem finrank_fractionRing (k K : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    [Field K] [Algebra k K] [IsFractionRing k K] [CharZero K] :
    Module.finrank ℚ K = Module.finrank ℤ k ∧ FiniteDimensional ℚ K := by
  haveI : Module.Free ℤ k := Module.free_of_finite_type_torsion_free'
  haveI : @IsScalarTower ℤ ℚ K Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid k (nonZeroDivisors ℤ)) K := inferInstance
  let b := Module.Free.chooseBasis ℤ k
  let b' := b.localizationLocalization ℚ (nonZeroDivisors ℤ) K
  exact ⟨(Module.finrank_eq_card_basis b').trans (Module.finrank_eq_card_basis b).symm,
    Module.Finite.of_basis b'⟩

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

theorem card_ringHom (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] :
    Nat.card (k →+* ℂ) = Module.finrank ℤ k := by
  haveI : CharZero (FractionRing k) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective k (FractionRing k))
  obtain ⟨h1, h2⟩ := finrank_fractionRing k (FractionRing k)
  haveI : NumberField (FractionRing k) := ⟨⟩
  rw [Nat.card_congr (ringHomEquiv k (FractionRing k)), Nat.card_eq_fintype_card,
    NumberField.Embeddings.card, h1]

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

open Set
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V)

theorem exists_stdChart (k : Type) [CommRing k] (σ : k →+* ℂ) (N : ℕ) :
    ∃ (c : AlgChart (PSpace.str k N) σ N) (i : (ProjSpace.hermitianTwistingSheaf k N).B.ι),
      c.e.source = ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0) ∧ c.e.target = Set.univ ∧
      c.e.source ⊆ ptsIn (PSpace.str k N) σ ((ProjSpace.hermitianTwistingSheaf k N).B.U i) ∧
      ∀ v, ((ProjSpace.hermitianTwistingSheaf k N).φ σ).φ i (c.e.symm v) = Real.log (1 + ‖v‖ ^ 2) := by
  obtain ⟨c, h₁, h₂, h₃⟩ := StdProjChart.exists_of_bijective (p := PSpace.str k N) σ
    (ProjSpace.isAffineOpen_chart k N 0) _ (StdProjChart.bijective_ratio k N 0)
  refine ⟨c, (0 : Fin (N + 1)), h₁, h₂, h₁.le, fun v => ?_⟩
  have hv : c.e.symm v ∈ ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0) :=
    h₁ ▸ c.e.map_target (h₂ ▸ trivial)
  have h := Weight.fsBasis_φ (p := PSpace.str k N) (σ := σ) (ProjSpace.O1_isLB k N)
    (ProjSpace.coord k N) (ProjSpace.iSup_nonzeroLocus_coord k N) 1 (by simp) (0 : Fin (N + 1))
    (c.e.symm v)
  refine h.trans ?_
  have h0 : ev (PSpace.str k N) σ (ProjSpace.chart k N 0) (ProjSpace.ratio k N 0 0)
      (c.e.symm v) = 1 := by
    simp only [ProjSpace.ratio, ProjSpace.ratioOn_self]
    rw [ev_eq hv, map_one]
  have key : ∑ a : Fin (N + 1), ‖ev (PSpace.str k N) σ (ProjSpace.chart k N 0)
      (ProjSpace.ratio k N 0 a) (c.e.symm v)‖ ^ 2 = 1 + ‖v‖ ^ 2 := by
    rw [Fin.sum_univ_succ, h0, EuclideanSpace.norm_sq_eq]
    simp only [Fin.succAbove_zero] at h₃
    simp only [h₃, norm_one, one_pow]
  rw [← key]
  simp [Matrix.one_apply, ev, ProjSpace.O1]

theorem chern_mass_hermitian_O_one_projective (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    (N : ℕ) (σ : k →+* ℂ) :
    ((ProjSpace.hermitianTwistingSheaf k N).φ σ).chernPart N 1 Set.univ = 1 ∧
      ((ProjSpace.hermitianTwistingSheaf k N).φ σ).chernPart N (-1) Set.univ = 0 := by
  have hA := isArithVar k N
  have hproj : IsProjOver (PSpace.str k N) := hA.isProjOver
  haveI : IsIntegral (PSpace k N) := ProjSpace.isIntegral_of_isDomain k N
  haveI := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hproj
  have hC : ((ProjSpace.hermitianTwistingSheaf k N).φ σ).IsCInf := (ProjSpace.hermitianTwistingSheaf k N).cInf _
  have hSP : ((ProjSpace.hermitianTwistingSheaf k N).φ σ).SemiPosReg N :=
    (HermLB.semiPos_fs _ _ _ _ _ _ : (ProjSpace.hermitianTwistingSheaf k N).SemiPos N) _
  refine ⟨?_, by rw [Weight.chernPart_neg_eq_zero hC hSP]; rfl⟩
  obtain ⟨c, i, hsrc, htgt, hsub, hφv⟩ := exists_stdChart k σ N
  have hmem : c.e.symm 0 ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  have hgen : genericPoint (PSpace k N) ∈ ProjSpace.chart k N 0 := by
    have h0 : c.e.symm 0 ∈ ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0) := hsrc ▸ hmem
    exact ((genericPoint_spec (PSpace k N)).mem_open_set_iff (ProjSpace.chart k N 0).isOpen).2
      ⟨_, by simp, mem_ptsIn.1 h0⟩
  have hnull := ChernNull.chernPart_over_closed hA ((ProjSpace.chart k N 0 : (PSpace k N).Opens) : Set (PSpace k N))ᶜ
    (ProjSpace.chart k N 0).isOpen.isClosed_compl (by simpa using hgen) σ ((ProjSpace.hermitianTwistingSheaf k N).φ σ) 1
  have hcX : (ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0))ᶜ =
      {y : CxPts (PSpace.str k N) σ | y.1 (IsLocalRing.closedPoint ℂ) ∈
        ((ProjSpace.chart k N 0 : (PSpace k N).Opens) : Set (PSpace k N))ᶜ} := by
    ext y
    simp [mem_ptsIn]
  rw [← hcX, ← hsrc] at hnull
  have hmeas : MeasurableSet c.e.source := c.e.open_source.measurableSet
  rw [← union_compl_self c.e.source, measure_union disjoint_compl_right hmeas.compl, hnull, add_zero,
    Weight.chernPart_apply hC 1 c hmeas subset_rfl, c.e.image_source_eq_target, htgt,
    Measure.restrict_univ]
  refine Eq.trans (lintegral_congr fun v => ?_) (lintegral_fubiniStudy_density_eq_one N)
  have hv : c.e.symm v ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  rw [AlgChart.chernDens_eq c hC hv (hsub hv), AlgChart.hess, c.e.right_inv (htgt ▸ mem_univ _)]
  have hf : (fun w => ((((ProjSpace.hermitianTwistingSheaf k N).φ σ).φ i (c.e.symm w) : ℝ) : ℂ)) =
      fun w => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ) := funext fun w => by rw [hφv w]
  rw [hf, FSDet.det_fubiniStudy_hess N v]
  simp

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

theorem degree_hermitian_O_one_projective (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ) :
    gdeg (ProjSpace.hermitianTwistingSheaf k D) D = Nat.card (k →+* ℂ) := by
  have hσ : ∀ σ : k →+* ℂ, ((ProjSpace.hermitianTwistingSheaf k D).φ σ).chernInt D Set.univ (fun _ => 1) = 1 := by
    intro σ
    obtain ⟨h1, h0⟩ := chern_mass_hermitian_O_one_projective k D σ
    rw [GdegPullProof.chernInt_one, h1, h0]
    simp
  haveI : Finite (k →+* ℂ) := by
    haveI : CharZero (FractionRing k) :=
      charZero_of_injective_algebraMap (IsFractionRing.injective k (FractionRing k))
    haveI : FiniteDimensional ℚ (FractionRing k) := (finrank_fractionRing k (FractionRing k)).2
    haveI : NumberField (FractionRing k) := ⟨⟩
    exact Finite.of_equiv _ (ringHomEquiv k (FractionRing k)).symm
  haveI := Fintype.ofFinite (k →+* ℂ)
  simp only [gdeg, chInt, hσ]
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
    nsmul_eq_mul, mul_one]

theorem main : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ),
    IsArithVar (PSpace.str k D) D ∧ gdeg (ProjSpace.hermitianTwistingSheaf k D) D = Nat.card (k →+* ℂ) ∧
      Nat.card (k →+* ℂ) = Module.finrank ℤ k :=
  fun k _ _ _ _ D => ⟨isArithVar k D, degree_hermitian_O_one_projective k D, card_ringHom k⟩

end GlobalTheory.PSpaceDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSpaceOrderArithVarietyFubiniStudyDegreStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveSpace_order_arithVariety_fubiniStudyDegree : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ), IsArithVar (PSpace.str k D) D ∧ gdeg (ProjSpace.hermitianTwistingSheaf k D) D = Nat.card (k →+* ℂ) ∧ Nat.card (k →+* ℂ) = Module.finrank ℤ k := by
  first | exact @GlobalTheory.PSpaceDeg.main | exact GlobalTheory.PSpaceDeg.main | (intros; apply GlobalTheory.PSpaceDeg.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomSurjectiveIffFinrankKernelQuotientEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomSurjectiveIffFinrankKernelQuotientEqOne
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem surjective_iff_finrank_quot_kerIdeal_eq_one :
    ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A] [IsCocomm k A]
      [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C]
      [Module.Finite k C] (f : C →ₐc[k] A),
      Function.Surjective f ↔ Module.finrank k (A ⧸ kerIdeal f) = 1 := by
  intro k _ A _ _ _ _ C _ _ _ _ f
  constructor
  · intro hf
    rw [kerIdeal_of_surjective hf]
    have hs : Function.Surjective (counitAlgHom k A) := fun c =>
      ⟨algebraMap k A c, by simp⟩
    let e : (A ⧸ augIdeal (R := k) (A := A)) ≃ₐ[k] k := Ideal.quotientKerAlgEquivOfSurjective hs
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_self]
  · intro h
    have hL := GlobalTheory.T.finrank_hopfAlgebra_eq_range_mul_kernel k A C f
    rw [h, mul_one] at hL
    have htop : LinearMap.range (f : C →ₐ[k] A).toLinearMap = ⊤ :=
      Submodule.eq_top_of_finrank_eq hL.symm
    intro a
    have ha : a ∈ LinearMap.range (f : C →ₐ[k] A).toLinearMap := htop ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := ha
    exact ⟨c, hc⟩

end GlobalTheory.Dieu
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomSurjectiveIffFinrankKernelQuotientEqOneStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bialgHom_surjective_iff_finrank_kernelQuotient_eq_one : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A] [IsCocomm k A] [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (f : C →ₐc[k] A), Function.Surjective f ↔ Module.finrank k (A ⧸ kerIdeal f) = 1 := by
  first | exact @GlobalTheory.Dieu.surjective_iff_finrank_quot_kerIdeal_eq_one | exact GlobalTheory.Dieu.surjective_iff_finrank_quot_kerIdeal_eq_one | (intros; apply GlobalTheory.Dieu.surjective_iff_finrank_quot_kerIdeal_eq_one <;> assumption)
end
end
