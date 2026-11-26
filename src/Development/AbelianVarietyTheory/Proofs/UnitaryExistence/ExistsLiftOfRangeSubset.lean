module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaAtClosedPoint
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHolomorphicLieFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AbelianSubgroupFinite

theorem exists_lift_of_range_subset {T N B : Scheme.{0}} [IsReduced T] (x : T ⟶ B) (ν : N ⟶ B)
    [IsClosedImmersion ν] (h : Set.range x ⊆ Set.range ν) : ∃ l : T ⟶ N, l ≫ ν = x := by
  have hs : Surjective (pullback.snd ν x) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
    exact Set.eq_univ_of_forall fun t => h ⟨t, rfl⟩⟩
  have : IsIso (pullback.snd ν x) := isIso_of_isClosedImmersion_of_surjective _
  exact ⟨inv (pullback.snd ν x) ≫ pullback.fst ν x, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem isCommMonObj_of_mono {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞]
    [BraidedCategory 𝒞] {N B : 𝒞} [MonObj N] [MonObj B] [IsCommMonObj B] (ν : N ⟶ B) [Mono ν]
    [IsMonHom ν] : IsCommMonObj N where
  mul_comm := by
    rw [← cancel_mono ν, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]

theorem finite_of_no_torsion : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C) := by
  intro hcount k _ _ B _ n hB hn hnk C Z hZ hC htor
  have := hB.smooth
  have := hB.proper
  have := hB.comm
  obtain ⟨N, _, ν, hν, hνc, hNs, hr⟩ :=
    GlobalTheory.ReducedSubgroup.exists_smooth_closed_subgroup k B inferInstance C Z hZ hC
  have hNp : IsProper N.hom := by rw [← ν.w]; infer_instance
  obtain ⟨N₀, _, ν₀, g, hν₀, -, hν₀c, hgc, hg, hfin⟩ :=
    GlobalTheory.exists_neutralComponent k N hNs inferInstance
  have : IsClosedImmersion (ν₀ ≫ ν).left := by rw [Over.comp_left]; infer_instance
  have : Mono (ν₀ ≫ ν) := Over.mono_of_mono_left _
  have hA : IsAbelianScheme N₀ :=
    { comm := isCommMonObj_of_mono (ν₀ ≫ ν)
      smooth := SmoothOfRelativeDimension.smooth g N₀.hom
      proper := by rw [← ν₀.w]; infer_instance
      geomConnected := hgc }
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C := fun x => by
    rw [hC, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  have h1 : Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ N₀) // x ^ n = 1} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, one_pow n⟩, fun x => Subtype.ext ?_⟩
    have h2 : x.1 ≫ ν₀ ≫ ν = 1 := by
      refine htor _ (by rw [← Category.assoc]; exact hmem _) ?_
      rw [← MonObj.pow_comp, x.2, MonObj.one_comp]
    rw [← cancel_mono (ν₀ ≫ ν), h2, MonObj.one_comp]
  rw [hcount k N₀ g n hA hg hnk] at h1
  have hg0 : g = 0 := by
    rcases (Nat.pow_eq_one.1 h1) with h | h
    · exact absurd h hn.one_lt.ne'
    · omega
  have := hfin hg0
  refine Finite.of_surjective (fun x : 𝟙_ (Over (Sp k)) ⟶ N => (⟨x ≫ ν, hmem x⟩ : C)) ?_
  rintro ⟨x, hx⟩
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  obtain ⟨l, hl⟩ := exists_lift_of_range_subset x.left ν.left (hr ▸ (hC x).1 hx)
  refine ⟨Over.homMk l ?_, Subtype.ext (Over.OverMorphism.ext hl)⟩
  rw [← ν.w, ← Category.assoc, hl, x.w]

end GlobalTheory.AbelianSubgroupFinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

namespace GlobalTheory.PeriodFormCompare

variable {R : Type} [CommRing R] [IsDomain R]

theorem generic_val (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
      (((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r)) = algebraMap R (FractionRing R) r := by
  have e : DegPre.toOpen (R := R) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    simp [DegPre.toOpen]
  rw [e]
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (jK R).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom).hom r = _
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rfl

theorem psiCoord_iff (D : DegPre R) (χ : D.X) (r : R) :
    PsiCoord D χ r ↔ ∃ x, IsPsiCoord D χ x ∧ x.val = algebraMap R (FractionRing R) r := by
  constructor
  · rintro ⟨j, hj, h, e⟩
    exact ⟨_, ⟨j, h, hj, rfl⟩, (congrArg _ e.symm).trans (generic_val r)⟩
  · rintro ⟨_, ⟨j, h, hj, rfl⟩, e⟩
    refine ⟨j, hj, h, ?_⟩
    exact (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.injective
      ((generic_val r).trans e.symm)

theorem isPsiCoord_toUnitK {D : DegPre R} {χ : D.X} {r : R} (h : PsiCoord D χ r) (h0 : r ≠ 0) :
    IsPsiCoord D χ (toUnitK r h0) := by
  obtain ⟨x, hx, e⟩ := (psiCoord_iff D χ r).1 h
  have : x = toUnitK r h0 := Units.ext e
  exact this ▸ hx

theorem exists_psiCoord_iff [IsLocalRing R] (D : DegPre R) (χ : D.X) :
    (∃ r, PsiCoord D χ r) ↔ D.PsiIn χ ⊤ := by
  constructor
  · rintro ⟨r, hr⟩
    exact (PeriodFormEdge.psiIn_iff hr ⊤).2 trivial
  · intro hI
    obtain ⟨j, hj⟩ := PsiCoordLocal.exists_chart_top D χ
    have h := PsiCoordLocal.generic_le D χ j hj
    obtain ⟨s, -, e⟩ := hI j ⊤ (isAffineOpen_top _) hj h
    obtain ⟨r, rfl⟩ := PsiCoordLocal.toOpen_top_bijective.2 s
    exact ⟨r, j, hj, h, e⟩

theorem exists_psiCoord_of_isPsiCoord [IsLocalRing R] {D : DegPre R} {χ : D.X} (hI : D.PsiIn χ ⊤)
    {x : (FractionRing R)ˣ} (hx : IsPsiCoord D χ x) :
    ∃ r, PsiCoord D χ r ∧ x.val = algebraMap R (FractionRing R) r := by
  obtain ⟨r, hr⟩ := (exists_psiCoord_iff D χ).2 hI
  obtain ⟨y, hy, e⟩ := (psiCoord_iff D χ r).1 hr
  obtain ⟨u, hu⟩ := hx.unique hy
  have : x.val = algebraMap R (FractionRing R) (u * r) := by
    rw [hu, map_mul, ← e]; rfl
  exact ⟨u * r, (psiCoord_iff D χ _).2 ⟨x, hx, this⟩, this⟩

theorem psiIn_top {I : Ideal R} (D : DegData R I) (χ : D.toPre.X) : D.toPre.PsiIn χ ⊤ := by
  by_cases h : χ = 0
  · subst h; exact (PsiZero.main R D.toPre).1 D.tau_bimult
  · exact (PsiZero.main R D.toPre).2 χ I ⊤ le_top (D.psi_pos χ h)

section DVR

variable [IsDiscreteValuationRing R]

end DVR

section At

variable [IsLocalRing R] {C : Type} [NormedField C]


variable {φ : FractionRing R →+* C}

end At

end GlobalTheory.PeriodFormCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnExponentialFrameMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnExponentialFrameMatrix
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

open Filter Topology GlobalTheory.TangentOrigin GlobalTheory.HolLieFrame

namespace GlobalTheory.HolFrameMatrix

theorem differentiableAt_of_mul_eq_one {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ}
    (G A : V → Matrix (Fin n) (Fin n) ℂ) (b₀ : V) (hA : ∀ i j, DifferentiableAt ℂ (fun b => A b i j) b₀)
    (h : ∀ᶠ b in 𝓝 b₀, G b * A b = 1) (i j : Fin n) : DifferentiableAt ℂ (fun b => G b i j) b₀ := by
  refine differentiableAt_pi.1 (differentiableAt_of_forms (fun b => G b i) b₀ fun w hw => ?_) j
  have h0 : w ᵥ* A b₀ = 0 := by
    funext i'
    have := hw (fun b => ∑ j, A b j i' • ContinuousLinearMap.proj j)
      (DifferentiableAt.fun_sum fun j _ => (hA j i').smul_const _) ?_
    · simpa [Matrix.vecMul, dotProduct, mul_comm] using this
    · refine (differentiableAt_const ((1 : Matrix (Fin n) (Fin n) ℂ) i i')).congr_of_eventuallyEq ?_
      filter_upwards [h] with b hb
      rw [← hb]
      simp [Matrix.mul_apply, mul_comm]
  have h1 : A b₀ * G b₀ = 1 := mul_eq_one_comm.1 h.self_of_nhds
  have := congrArg (· ᵥ* G b₀) h0
  simpa [Matrix.vecMul_vecMul, h1] using this

theorem differentiableAt_coord {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) (i : Fin U.n) {m : ℕ} {B : Set (Fin m → ℂ)}
    {P : (Fin m → ℂ) → ((U.Di i).La →+ (Fin g → ℂ))} {R : Type} [CommRing R]
    (v : Sp (DualNumber R) ⟶ Xo.univ.t.G.left) (ev : (Fin m → ℂ) → (R →+* ℂ)) (hB : IsOpen B)
    (hP : IsHolPeriods (U.Di i) ty B P) (W : (Fin m → ℂ) → Fin g → ℂ)
    (hW : ∀ b ∈ B, IsDerivAt0 (fun z => (U.ex i (P b) z).left) (W b) (spMap (Chart.dualMapR (ev b)) ≫ v))
    {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) (hev : ∀ t, DifferentiableAt ℂ (fun b => ev b t) b₀) :
    DifferentiableAt ℂ W b₀ := by
  obtain ⟨hol₁, hol₂⟩ := U.hol i m B P hB hP
  refine differentiableAt_of_forms _ b₀ fun w hw => ?_
  have hw' : ∀ (O : Xo.univ.t.G.left.Opens) (f : Γ(Xo.univ.t.G.left, O)), ⊤ ≤ (U.ex i (P b₀) 0).left ⁻¹ᵁ O →
      fderiv ℂ (fun z => valAt' (U.ex i (P b₀) z).left O f) 0 w = 0 := by
    intro O f hO
    refine hw (fun b => fderiv ℂ (fun z => valAt' (U.ex i (P b) z).left O f) 0)
      (differentiableAt_fderiv (e := fun b z => (U.ex i (P b) z).left) hol₂ hb₀ O f hO) ?_
    obtain ⟨F, hF, hF'⟩ := exists_hol_snd v ev b₀ hev O f
      ((top_le_preimage_iff _ O).2 (by rw [(hW b₀ hb₀).1]; exact hO))
    refine hF.congr_of_eventuallyEq ?_
    filter_upwards [hF', hB.mem_nhds hb₀] with b ⟨h, e⟩ hb
    exact ((hW b hb).2 O h f).symm.trans e
  have d₁ := LocalLift.isDerivAt0_const (fun z => (U.ex i (P b₀) z).left) w hw'
  have d₀ := LocalLift.isDerivAt0_const (fun z => (U.ex i (P b₀) z).left) 0 fun _ _ _ => map_zero _
  let v₀ : epsPt (U.u i (P b₀)) ⟶ Xo.univ.t.G :=
    Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (U.ex i (P b₀) 0).left)
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w (U.ex i (P b₀) 0))))
  exact ((U.ex_diff i _ (hP.1 b₀ hb₀)).2 v₀ d₁.1).unique d₁ d₀

theorem dualMap_eq {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) : dualMap φ = Chart.dualMapR φ := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap, Chart.dualMapR]

theorem differentiableOn_frameMatrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k) (R : Type) [CommRing R] [Algebra c.F R] (y₀ : FrPt Xo c R) (B : Set (Fin T.m → ℂ)) (ψ : (Fin T.m → ℂ) → (R →ₐ[c.F] CAt σ)) (κ : (Fin T.m → ℂ) → ℂ) (z y : (Fin T.m → ℂ) → FrPt Xo c (CAt σ)) (G : (Fin T.m → ℂ) → (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))) (a : (Fin T.m → ℂ) → CAt σ), IsOpen B → B ⊆ T.co ⁻¹' (M.X k).dom → (∀ t : R, DifferentiableOn ℂ (fun b => toC (ψ b t)) B) → (∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (G b) (a b) (z b) (y b) ∧ IsThetaPt T b (κ b) (y b)) → ∀ τ i j, DifferentiableOn ℂ (fun b => toC (G b τ i j)) B := by
  intro E _ _ _ H Dw l Xo c σ g e F r M k T R _ _ y₀ B ψ κ z y G a hB hsub hψ h τ i j
  have hP : IsHolPeriods (F.Di k) (fun j => relab c σ (e j).1) B (fun b => T.Pf (T.co b)) :=
    ⟨fun b hb => T.holPer.1 b (hsub hb), fun x => (T.holPer.2 x).mono hsub⟩
  have hx : ∀ b ∈ B, (z b).x = F.u k (T.Pf (T.co b)) := fun b hb => (h b hb).2.1.1.symm.trans (h b hb).2.2.1
  have hI := fun b hb => GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k _ (hP.1 b hb)
  have htan : ∀ b ∈ B, ∀ j, IsTanAt (S := ℂ) (F.u k (T.Pf (T.co b))) ((z b).u τ j) := fun b hb j => by
    rw [← hx b hb]; exact (z b).tan τ j
  choose! W hW using fun b hb j => ((hI b hb).2.2 _ (htan b hb j)).exists
  let ev : (Fin T.m → ℂ) → (R →+* ℂ) := fun b => (ψ b).toRingHom
  intro b₀ hb₀
  refine DifferentiableAt.differentiableWithinAt ?_
  refine differentiableAt_of_mul_eq_one (fun b => Matrix.of fun i j => toC (G b τ i j))
    (fun b => Matrix.of fun j i' => W b j (e.symm ⟨τ, i'⟩)) b₀ (fun j i' => ?_) ?_ i j
  · refine differentiableAt_pi.1 (differentiableAt_coord F k (y₀.u τ j) ev hB hP (fun b => W b j) (fun b hb => ?_) hb₀
      fun t => (hψ t).differentiableAt (hB.mem_nhds hb₀)) _
    have := hW b hb j
    rw [(h b hb).1.2.1 τ j] at this
    rw [← dualMap_eq]
    exact this
  · filter_upwards [hB.mem_nhds hb₀] with b hb
    ext i i'
    have hc : IsCombAt (S := ℂ) (F.u k (T.Pf (T.co b))) ((z b).u τ) (fun j => toC (G b τ i j)) ((y b).u τ i) := by
      rw [← hx b hb]; exact (h b hb).2.1.2.1 τ i
    have hd := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k _ (hP.1 b hb) _ _ _ (hW b hb) _ _).1 hc
    have hd' := (h b hb).2.2.2.1 τ i
    have := congrFun (((hI b hb).2.2 _ ((hI b hb).1 _ _ hd)).unique hd hd') (e.symm ⟨τ, i'⟩)
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Pi.single_apply, eq_comm] using this

end GlobalTheory.HolFrameMatrix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnExponentialFrameMatrixStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_exponential_frame_matrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k) (R : Type) [CommRing R] [Algebra c.F R] (y₀ : FrPt Xo c R) (B : Set (Fin T.m → ℂ)) (ψ : (Fin T.m → ℂ) → (R →ₐ[c.F] CAt σ)) (κ : (Fin T.m → ℂ) → ℂ) (z y : (Fin T.m → ℂ) → FrPt Xo c (CAt σ)) (G : (Fin T.m → ℂ) → (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))) (a : (Fin T.m → ℂ) → CAt σ), IsOpen B → B ⊆ T.co ⁻¹' (M.X k).dom → (∀ t : R, DifferentiableOn ℂ (fun b => toC (ψ b t)) B) → (∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (G b) (a b) (z b) (y b) ∧ IsThetaPt T b (κ b) (y b)) → ∀ τ i j, DifferentiableOn ℂ (fun b => toC (G b τ i j)) B := by
  first | exact @GlobalTheory.HolFrameMatrix.differentiableOn_frameMatrix | exact GlobalTheory.HolFrameMatrix.differentiableOn_frameMatrix | (intros; apply GlobalTheory.HolFrameMatrix.differentiableOn_frameMatrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsInverseBlock
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CoverFrame

theorem exists_inverse_block {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (w : Fin g → Fin g → ℂ)
    (h : ∀ j, ∃ a : Fin (m (e j).1) → ℂ, ∑ i, a i • w (e.symm ⟨(e j).1, i⟩) = Pi.single j 1) :
    ∃ V : Matrix (Fin g) (Fin g) ℂ, IsUnit V.det ∧ (∀ j j', V j j' ≠ 0 → (e j).1 = (e j').1) ∧
      ∀ j, V *ᵥ w j = Pi.single j 1 := by
  classical
  choose a ha using h
  let cv : Fin g → Fin g → ℂ := fun j => ∑ i, a j i • Pi.single (e.symm ⟨(e j).1, i⟩) 1
  let Wm : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => w j i
  let V : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => cv j i
  have hW : ∀ j, Wm *ᵥ Pi.single j 1 = w j := fun j => by
    ext i; simp [Wm]
  have hV : ∀ j, V *ᵥ Pi.single j 1 = cv j := fun j => by
    ext i; simp [V]
  have hWV : Wm * V = 1 := by
    have : ∀ j, (Wm * V) *ᵥ Pi.single j 1 = Pi.single j 1 := fun j => by
      rw [← Matrix.mulVec_mulVec, hV, ← ha j]
      simp only [cv, Matrix.mulVec_sum, Matrix.mulVec_smul, hW]
    ext i j
    have h1 := congrFun (this j) i
    simpa [Matrix.one_apply, Pi.single_apply] using h1
  have hVW : V * Wm = 1 := mul_eq_one_comm.mp hWV
  refine ⟨V, Matrix.isUnit_det_of_left_inverse hWV, fun j j' hj => ?_, fun j => ?_⟩
  · by_contra hne
    apply hj
    simp only [V, cv, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Pi.single_eq_of_ne, smul_zero]
    intro hh
    apply hne
    rw [hh, Equiv.apply_symm_apply]
  · rw [← hW, Matrix.mulVec_mulVec, hVW, Matrix.one_mulVec]


set_option maxHeartbeats 1000000 in
theorem coverTri : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → CoverTri e F M := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hG hB hN y
  classical
  obtain ⟨k, P, hP, hy⟩ := F.onto y.x y.x_over
  obtain ⟨ht1, ht2, ht3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k P hP
  have hw : ∀ j : Fin g, ∃ w, IsDerivAt0 (fun z => (F.ex k P z).left) w (y.u (e j).1 (e j).2) := fun j =>
    (ht3 (y.u (e j).1 (e j).2) (by rw [hy]; exact y.tan _ _)).exists
  choose w hw using hw
  have hw' : ∀ τ (i : Fin (Dw.mult τ)),
      IsDerivAt0 (fun z => (F.ex k P z).left) (w (e.symm ⟨τ, i⟩)) (y.u τ i) := fun τ i => by
    have := hw (e.symm ⟨τ, i⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this
  have hsp : ∀ j, ∃ a : Fin (Dw.mult (e j).1) → ℂ, ∑ i, a i • w (e.symm ⟨(e j).1, i⟩) = Pi.single j 1 := by
    intro j
    obtain ⟨v, hv⟩ := (ht2 (Pi.single j 1)).exists
    have htan := ht1 _ _ hv
    have heig :=
      (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F k P hP (Pi.single j 1) v (e j).1 hv).2
        (fun j' hj' => by
          by_contra hne
          exact hj' (Pi.single_eq_of_ne (fun hh => hne (by rw [hh])) _))
    have htan' : IsTanAt y.x v := by rw [← hy]; exact htan
    obtain ⟨a, ha⟩ := (y.basis (e j).1 v htan' heig).exists
    have ha' : IsCombAt (F.u k P) (y.u (e j).1) (show Fin (Dw.mult (e j).1) → ℂ from a) v := by
      rw [hy]; exact ha
    have hd := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k P hP _ (y.u (e j).1)
      (fun i => w (e.symm ⟨(e j).1, i⟩)) (hw' (e j).1) a v).1 ha'
    exact ⟨a, (ht3 v htan).unique hd hv⟩
  obtain ⟨V, hVu, hVt, hVw⟩ := exists_inverse_block e w hsp
  obtain ⟨P', hP', hP'e⟩ := GlobalTheory.PeriodLin.exists_period_mulVec E H (F.Di k) g _ P V hP hVu
    (fun j j' h => by rw [hVt j j' h])
  obtain ⟨-, hu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F k P P'
    (LinearEquiv.refl _ _) V hP hP' (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩) (fun a => ⟨0, by simp⟩) hP'e
  obtain ⟨Pf, hPf, -, -, -, hon⟩ := GlobalTheory.T.exists_framePeriods_alt E H Dw l Xo c σ g e F r M hG hB hN k
  obtain ⟨x, hx, hxP⟩ := hon P' hP'
  have hy' : F.u k P' = y.x := hu.symm.trans hy
  refine ⟨k, ⟨x, hx⟩, P', fun a j => by rw [← hxP]; exact hPf x a j, hy', fun v hv τ i => ?_⟩
  have hyu : IsDerivAt0 (fun z => (F.ex k P' z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i) := by
    have := (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F k P hP k P' (Matrix.mulVecLin V) hP' hex
      _ _).1 (hw' τ i)
    rw [Matrix.mulVecLin_apply, hVw] at this
    exact this
  have hc := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k P' hP' _ (v τ)
    (fun i => Pi.single (e.symm ⟨τ, i⟩) 1) (hv τ) (Pi.single i 1) (y.u τ i)).2 (by
      rw [Finset.sum_eq_single i (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp),
        Pi.single_eq_same, one_smul]
      exact hyu)
  refine ⟨(Pi.single i 1 : Fin (Dw.mult τ) → ℂ), ?_, fun j hj => Pi.single_eq_of_ne (M := fun _ => ℂ) hj.ne' _, ?_⟩
  · show IsUnit ((Pi.single i 1 : Fin (Dw.mult τ) → ℂ) i)
    rw [Pi.single_eq_same]; exact isUnit_one
  · rw [← hy']; exact hc

end GlobalTheory.CoverFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionNowhereZeroOfPullbackTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionNowhereZeroOfPullbackTriple
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SecTransport

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

section Calc

variable {X X' Y : Scheme.{0}}

theorem chart_le_preimage (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (h : Y ⟶ X') (e : h ≫ F = φ) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => φ) j ≤ h ⁻¹ᵁ (L.pull F).U (fun _ => j 0) := fun y hy =>
  mem_pull.2 ((congrArg (fun q => q y ∈ L.U (j 0)) e).mpr (LB.wchart_le L _ j 0 hy))

def secPullOne (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (h : Y ⟶ X') (e : h ≫ F = φ) (s : LB.Sec (L.pull F)) :
    LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)) where
  f := fun (j : Fin 1 → L.ι) => (h.appLE _ _ (chart_le_preimage L h e j)).hom (s.f (fun _ => j 0))
  compat := fun (j j' : Fin 1 → L.ι) => fn_ext fun y hy => by
    have h₁ : h y ∈ (L.pull F).U (fun _ => j 0) := chart_le_preimage L h e j hy.1
    have h₂ : h y ∈ (L.pull F).U (fun _ => j' 0) := chart_le_preimage L h e j' hy.2
    have g : gm (𝟙 Y) y _ ((LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)).g j j') =
        gm (𝟙 Y ≫ φ) y (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) :=
      (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2).trans (by rw [Fin.prod_univ_one, zpow_one])
    have eφ : (𝟙 Y ≫ h) ≫ F = 𝟙 Y ≫ φ := by rw [Category.assoc, e]
    exact (gs_res _ y _ hy _).trans ((gs_appLE h _ _ _ (𝟙 _) y hy.1 _).trans ((gs_compat s (𝟙 Y ≫ h) y h₁ h₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
        ((gs_unit _ y _ hy _).trans (congrArg Units.val (g.trans ((congrArg (fun q => gm q y (L.U (j 0) ⊓ L.U (j' 0))
          (L.g (j 0) (j' 0))) eφ).symm.trans (gm_pull_g L F (𝟙 Y ≫ h) y _ _ h₁ h₂).symm))))
        ((gs_res _ y _ hy _).trans (gs_appLE h _ _ _ (𝟙 _) y hy.2 _)))))))

theorem exists_sec_along_iso {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB)
    (hL' : L'.IsLB) (σ : LB.Sec L') : ∃ s : LB.Sec (L.pull F), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z)
      (J : PUnit → L.ι) (k : L'.ι), r z ∈ (L.pull F).U J → r z ∈ L'.U k →
      gs r z _ (s.f J) = (gw w r z (J PUnit.unit) k).val * gs r z _ (σ.f k) := by
  have glue : ∀ J : PUnit → L.ι, ∃ a : Γ(X', (L.pull F).U J), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (k : L'.ι),
      r z ∈ (L.pull F).U J → r z ∈ L'.U k → gs r z _ a = (gw w r z (J PUnit.unit) k).val * gs r z _ (σ.f k) := by
    intro J
    obtain ⟨u, hu⟩ : ∃ u : ∀ k, Γ(X', (L.pull F).U J ⊓ L'.U k), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) k,
        r z ∈ (L.pull F).U J ⊓ L'.U k → gs r z _ (u k) = (gw w r z (J PUnit.unit) k).val * gs r z _ (σ.f k) :=
      ⟨fun k => (show Γ(X', (L.pull F).U J ⊓ L'.U k) from (w.s (J, k)).val) * resG X' inf_le_right (σ.f k), fun Z r z k hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hz _) (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := X'.sheaf.existsUnique_gluing' (fun k => (L.pull F).U J ⊓ L'.U k) ((L.pull F).U J)
      (fun k => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hL' y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩) u
      (fun k k' => fn_ext (V := ((L.pull F).U J ⊓ L'.U k) ⊓ ((L.pull F).U J ⊓ L'.U k')) fun y hy => by
        refine (gs_res (𝟙 X') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X') y inf_le_right hy _).symm)
        have hj : F y ∈ L.U (J PUnit.unit) := mem_pull.1 hy.1.1
        rw [hu _ _ y k hy.1, hu _ _ y k' hy.2, gs_compat σ (𝟙 X') y hy.1.2 hy.2.2,
          hw _ (𝟙 X') y (J PUnit.unit) (J PUnit.unit) k k' hj hj hy.1.2 hy.2.2, gm_self hL (𝟙 X' ≫ F) y hj,
          _root_.one_mul, Units.val_mul, _root_.mul_assoc, mul_left_comm (gw w (𝟙 X') y (J PUnit.unit) k').val,
          Units.inv_mul_cancel_left])
    refine ⟨a, fun Z r z k h₁ h₂ => ?_⟩
    have hz : r z ∈ (L.pull F).U J ⊓ L'.U k := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z _) (ha k)).trans (hu Z r z k hz))
  choose a ha using glue
  refine ⟨⟨a, fun (J J' : PUnit → L.ι) => fn_ext fun y hy => ?_⟩, fun Z r z J k => ha J Z r z k⟩
  obtain ⟨k, hk⟩ := exists_chart hL' y
  have hj : F y ∈ L.U (J PUnit.unit) := mem_pull.1 hy.1
  have hj' : F y ∈ L.U (J' PUnit.unit) := mem_pull.1 hy.2
  rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy, gm_pull_g L F (𝟙 X') y J J' hy.1 hy.2,
    ha J _ (𝟙 X') y k hy.1 hk, ha J' _ (𝟙 X') y k hy.2 hk,
    hw _ (𝟙 X') y (J PUnit.unit) (J' PUnit.unit) k k hj hj' hk hk, gm_self hL' (𝟙 X') y hk, inv_one, _root_.mul_one,
    Units.val_mul, _root_.mul_assoc]

theorem isUnit_gs_iff (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    IsUnit (gs f y U a) ↔ f y ∈ X.basicOpen a := by
  unfold gs
  rw [dite_eq_left h]
  have e : y ∈ f ⁻¹ᵁ X.basicOpen a ↔ y ∈ Y.basicOpen (f.app U a) := by
    rw [Scheme.preimage_basicOpen]
  exact (Y.mem_basicOpen (f.app U a) y h).symm.trans e.symm

end Calc


set_option maxHeartbeats 400000 in
theorem exists_sec_nonzero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (t' : SAB H (Sp S)) (m : SABMap t' Xo.univ.t x) (th : t'.PP.L.Sec), (∀ y : Sp S, ∃ q : t'.G.left, t'.G.hom q = y ∧ q ∈ Out.nonzeroLocus th) → ∃ s : LB.Sec (PPx x), SecNZ x s := by
  intro E _ _ _ H Dw l Xo S _ x t' m1 σ' hnz
  obtain ⟨w1, g1, r1, -⟩ := m1.lin
  have hw1 := (isGen_iff w1).1 g1
  have hL := Xo.univ.t.PP.isLB
  have hL' := t'.PP.isLB
  obtain ⟨s1, hs1⟩ := exists_sec_along_iso hw1 hL hL' σ'
  let A := Xo.univ.t.G
  have cond : (snd (Over.mk x) A).left ≫ A.hom = (fst (Over.mk x) A).left ≫ x :=
    (Over.w (snd (Over.mk x) A)).trans (Over.w (fst (Over.mk x) A)).symm
  let h : Gx x ⟶ t'.G.left := m1.cart.1.lift _ _ cond
  have hφ : h ≫ m1.φ = (snd (Over.mk x) A).left := m1.cart.1.lift_fst _ _ cond
  have hh : h ≫ t'.G.hom = (fst (Over.mk x) A).left := m1.cart.1.lift_snd _ _ cond
  let a0 : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x := Over.homMk t'.G.hom rfl
  let b0 : Over.mk (t'.G.hom ≫ x) ⟶ A := Over.homMk m1.φ m1.cart.1.w
  let g0 : t'.G.left ⟶ Gx x := (lift a0 b0).left
  have g0f : g0 ≫ (fst (Over.mk x) A).left = t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
  have g0s : g0 ≫ (snd (Over.mk x) A).left = m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
  have hg0 : g0 ≫ h = 𝟙 _ := m1.cart.1.hom_ext (by rw [Category.assoc, hφ, g0s, Category.id_comp])
        (by rw [Category.assoc, hh, g0f, Category.id_comp])
  let s : LB.Sec (PPx x) := secPullOne Xo.univ.t.PP.L h hφ s1
  refine ⟨s, fun p => ?_⟩
  obtain ⟨q, hq, hqn⟩ := hnz p
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hqn
  have hkU : q ∈ t'.PP.L.U k := t'.G.left.basicOpen_le _ hk
  obtain ⟨j, hj⟩ := exists_chart hL (m1.φ q)
  have mg : g0 q ∈ (PPx x).U (fun _ => j) :=
    Set.mem_iInter.2 fun _ => (congrArg (fun r => r q ∈ Xo.univ.t.PP.L.U j) g0s).mpr hj
  refine ⟨g0 q, fun _ => j, (congrArg (fun r => r q) g0f).trans hq, ?_⟩
  refine (isUnit_gs_iff g0 q _ mg _).1 ?_
  have e : gs g0 q _ (s.f (fun _ => j)) = (gw w1 (𝟙 _) q j k).val * gs (𝟙 _) q _ (σ'.f k) := by
    refine (gs_appLE h _ _ (chart_le_preimage _ h hφ _) g0 q mg _).trans ?_
    rw [hg0]
    exact hs1 _ (𝟙 _) q (fun _ => j) k (mem_pull.2 hj) hkU
  rw [e]
  exact (Units.isUnit _).mul ((isUnit_gs_iff (𝟙 _) q _ hkU _).2 hk)

end GlobalTheory.SecTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionNowhereZeroOfPullbackTripleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibreSection_nowhereZero_of_pullbackTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (t' : SAB H (Sp S)) (m : SABMap t' Xo.univ.t x) (th : t'.PP.L.Sec), (∀ y : Sp S, ∃ q : t'.G.left, t'.G.hom q = y ∧ q ∈ Out.nonzeroLocus th) → ∃ s : LB.Sec (PPx x), SecNZ x s := by
  first | exact @GlobalTheory.SecTransport.exists_sec_nonzero | exact GlobalTheory.SecTransport.exists_sec_nonzero | (intros; apply GlobalTheory.SecTransport.exists_sec_nonzero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BlockTriangularOfMulEqOne
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FibreFlag

theorem blockTriangular_of_mul_eq_one {n : Type} [Fintype n] [DecidableEq n] (f : n → ℕ) (A C : Matrix n n ℂ)
    (h : A * C = 1) (hC : C.BlockTriangular f) : A.BlockTriangular f := by
  haveI : Invertible C := C.invertibleOfIsUnitDet (Matrix.isUnit_det_of_left_inverse h)
  rw [← Matrix.inv_eq_left_inv h]
  exact Matrix.blockTriangular_inv_of_blockTriangular hC

theorem upper_of_blocks {r : ℕ} (q : ℕ) (B : Matrix (Fin r) (Fin r) ℂ) (hB : B.det ≠ 0)
    (h1 : ∀ a c : Fin r, (c : ℕ) < q → c < a → B a c = 0)
    (h2 : ∀ a c : Fin r, q ≤ (c : ℕ) → c < a → B⁻¹ a c = 0) (a c : Fin r) (hca : c < a) : B a c = 0 := by
  have hu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  have t1 : B.BlockTriangular (fun a => min (a : ℕ) q) := fun a c h =>
    h1 a c (by simp only at h; omega) (by simp only at h; rw [Fin.lt_def]; omega)
  have t2 := blockTriangular_of_mul_eq_one _ _ _ (Matrix.nonsing_inv_mul B hu) t1
  have t3 : B⁻¹.BlockTriangular (fun a => (a : ℕ)) := fun a c h => by
    by_cases hc : (c : ℕ) < q
    · exact t2 (by simp only at h ⊢; omega)
    · exact h2 a c (not_lt.1 hc) h
  exact blockTriangular_of_mul_eq_one _ _ _ (Matrix.mul_nonsing_inv B hu) t3 hca


set_option maxHeartbeats 1000000 in
theorem fibTri : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → FibTri e F M := by
  classical
  intro E _ _ _ H Dw l Xo c σ g e F r M hσ hM hneg k k' x x' Pm Pm' v v' hP hP' hu hv hv' hcf
  have hper : ∀ (k) (x : (M.X k).dom) (Pm : (F.Di k).La →+ (Fin g → ℂ)),
      (∀ a j, Pm a j = perFr (M.X k) x.1 (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) →
      IsPeriod (F.Di k) (fun j => relab c σ (e j).1) Pm := by
    intro k x Pm hP
    obtain ⟨⟨idx, hty, -, hfr⟩, hp0, hr, hξ, hpos, hφ⟩ := GlobalTheory.FrameUnif.letter_column_dictionary E H Dw l Xo c σ g e F r M hσ hM hneg k
    have hlat := (hφ ((M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap) (fun _ => rfl)).2
    exact ((FramePeriod.isPeriod_frame E H (F.Di k) r _ _ _ _ (hM.type k).2 g idx _ hty hξ hpos hlat hr).2 x.1
      (hp0 ▸ x.2)).2 Pm fun a j => (hP a j).trans (hfr _ _ _)
  have p := hper k x Pm hP
  have p' := hper k' x' Pm' hP'
  obtain rfl := F.disj k k' _ _ p p' hu
  obtain ⟨⟨idx, hty, hix, hfr⟩, hp0, hr, hξ, hpos, hφ⟩ := GlobalTheory.FrameUnif.letter_column_dictionary E H Dw l Xo c σ g e F r M hσ hM hneg k
  obtain ⟨φ, hφe⟩ : ∃ φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E), ∀ a, φ a = (M.φ k a : Fin r → E) :=
    ⟨(M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap, fun _ => rfl⟩
  obtain ⟨hΛ, hlat⟩ := hφ φ hφe
  have hΨ := (hM.type k).2
  have hx : x.1 ∈ GG (M.X k).Ψ (M.X k).Gm (F.Di k).q := hp0 ▸ x.2
  have hx' : x'.1 ∈ GG (M.X k).Ψ (M.X k).Gm (F.Di k).q := hp0 ▸ x'.2
  obtain ⟨gam, h, hiso, hhalf, hA, hh⟩ := (F.fibre k _ _ p p').1 hu
  obtain ⟨γ, hγ⟩ := FrameFibre.exists_gl φ hlat.1 hlat.2.1 gam
  have hun := FrameFibre.herm_of_trace φ hlat.2.1 (M.X k).Gm γ _ (neg_ne_zero.2 (M.X k).ξ0_ne) fun v w => by
    rw [hγ, hγ, ← hlat.2.2.2.2, ← hlat.2.2.2.2, hiso]
  have hγΓ : γ ∈ (M.X k).Γ := by
    rw [hM.gam]
    refine ⟨⟨hun, fun y => hΛ ▸ (?_ : y ∈ LinearMap.range φ ↔ _ ∈ LinearMap.range φ)⟩, fun a ha => ?_, fun a => ?_⟩
    · constructor
      · rintro ⟨v, rfl⟩
        exact ⟨gam v, (hγ v).symm⟩
      · rintro ⟨v, hv⟩
        refine ⟨gam.symm v, ?_⟩
        apply (Matrix.mulVec_injective_of_isUnit γ.isUnit)
        rw [hγ, LinearEquiv.apply_symm_apply, hv]
    · obtain ⟨b, hb⟩ := hhalf a ha
      exact ⟨b, by rw [← hφe, ← hφe, hγ, hb, map_add (f := _), map_nsmul]⟩
    · obtain ⟨b, hb⟩ := hA a
      exact ⟨b, by rw [← hφe, ← hφe, hγ, hb, map_add (f := _), map_nsmul]⟩
  have hγx := FrameFibre.lact_mem_GG hun hx
  obtain ⟨Pg, hPg⟩ := ((FramePeriod.isPeriod_frame E H (F.Di k) r _ _ _ _ hΨ g idx _ hty hξ hpos hlat hr).2 _ hγx).1
  have hP1 := fun a j => (hP a j).trans (hfr x.1 _ j)
  have hP2 := fun a j => (hP' a j).trans (hfr x'.1 _ j)
  simp only [← hφe] at hP1 hP2
  have hmove := (per_move E H (F.Di k) r _ _ φ _ hΨ g idx _ hty hξ hpos hlat).2.1 x.1 γ Pm Pg hun hP1 hPg
  set A := LinearMap.toMatrix' h.toLinearMap with hAdef
  have hAv : ∀ z, A *ᵥ z = h z := fun z => by rw [hAdef, LinearMap.toMatrix'_mulVec]; rfl
  obtain ⟨b, hb, hb0, hb1, hb2, -⟩ := FramePeriod.frame_of_period_linear E H (F.Di k) r _ _ φ _ hΨ g idx _ hty
    hξ hpos hlat Pg _ hγx x'.1 hx' hPg Pm' hP2 A fun v => by
      obtain ⟨a, rfl⟩ := gam.surjective v
      rw [hAv, hh, hmove a (gam a) (hγ a).symm]
  have hrig := (FamRigid.ex_eq_of_level_group latMinkowski E H Dw l Xo _ g _ F k Pm Pm' gam A p p' hiso hhalf hA
    fun a => by rw [hAv, hh]).2.2
  choose cf hcf1 hcf2 hcf3 using hcf
  have hcol : ∀ τ i, A *ᵥ (∑ j, (show ℂ from cf τ i j) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) =
      Pi.single (e.symm ⟨τ, i⟩) 1 := by
    intro τ i
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k Pm p _ (v τ) _ (hv τ) (cf τ i) (v' τ i)).1
      (hcf3 τ i)
    have d2 := (ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F k Pm p k Pm' h.toLinearMap p'
      (fun z => by rw [← hrig z, hAv]; rfl) _ _).1 d1
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k Pm' p'
    rw [hAv]
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 (hv' τ i)
  let C : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun j j' =>
    (∑ i, (show ℂ from cf (e j').1 (e j').2 i) • (Pi.single (e.symm ⟨(e j').1, i⟩) 1 : Fin g → ℂ)) j
  have hAC : A * C = 1 := by
    ext j j'
    have := congrFun (hcol (e j').1 (e j').2) j
    rw [Sigma.eta, Equiv.symm_apply_apply, Pi.single_apply] at this
    rw [Matrix.one_apply, ← this]
    rfl
  have hC : C.BlockTriangular (fun j => ((e j).2 : ℕ)) := by
    intro j j' hj
    simp only [C, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : j = e.symm ⟨(e j').1, i⟩
    · have h3 : (((e j).2 : ℕ)) = i := by rw [hi, Equiv.apply_symm_apply]
      have h4 : cf (e j').1 (e j').2 i = 0 := hcf2 _ _ i (by rw [Fin.lt_def, ← h3]; exact hj)
      rw [h4]
      exact zero_mul _
    · have h5 : (Pi.single (e.symm ⟨(e j').1, i⟩) 1 : Fin g → ℂ) j = 0 := Pi.single_eq_of_ne hi _
      exact mul_eq_zero_of_right (M₀ := ℂ) _ h5
  have hT := blockTriangular_of_mul_eq_one _ _ _ hAC hC
  have hdet : ∀ τ, (mat b τ).det ≠ 0 := fun τ h0 => (hx' τ).1 (by
    have e1 : mat x'.1 τ = mat (lact γ x.1) τ * mat b τ := by rw [hb]; rfl
    rw [e1, Matrix.det_mul, h0, mul_zero])
  refine ⟨γ, hγΓ, b, fun τ => ⟨hdet τ, upper_of_blocks (F.Di k).q (mat b τ) (hdet τ) ?_ ?_⟩, by rw [← hb]⟩
  · intro a c' hc hca
    by_cases ha : (a : ℕ) < (F.Di k).q
    · have h1 := hb1 (idx.symm (τ, c')) (idx.symm (τ, a))
      have i1 := hix (idx.symm (τ, c'))
      have i2 := hix (idx.symm (τ, a))
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
      rw [Equiv.apply_symm_apply] at i1 i2
      simp only [hc, ha, if_true] at i1 i2
      rw [Fin.lt_def] at hca
      exact (h1 rfl hc ha).symm.trans (hT (by simp only; omega))
    · exact hb0 τ a c' hc (not_lt.1 ha)
  · intro a c' hc hca
    rw [Fin.lt_def] at hca
    have ha : (F.Di k).q ≤ (a : ℕ) := by omega
    have h1 := hb2 (idx.symm (τ, a)) (idx.symm (τ, c'))
    have i1 := hix (idx.symm (τ, c'))
    have i2 := hix (idx.symm (τ, a))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
    rw [Equiv.apply_symm_apply] at i1 i2
    simp only [not_lt.2 hc, not_lt.2 ha, if_false] at i1 i2
    exact (h1 rfl ha hc).symm.trans (hT (by simp only; omega))

end GlobalTheory.FibreFlag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSecGeneratorFibre
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory

theorem exists_sec_generator_fibre (hT : Out.SecTwistSt) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)
    {K : Type} [Field K] (y : Sp K ⟶ S) :
    ∃ β : (o.t.PP.L.pull (pullback.fst o.t.G.hom y)).Sec, ∀ s : (o.t.PP.L.pull (pullback.fst o.t.G.hom y)).Sec,
      ∃ a : K, ∀ i, s.f i = constFn (pullback.snd o.t.G.hom y) _ a * β.f i := by
  have h := isGrpPullback_pullback o.t.G y
  obtain ⟨hL, hr, -, hs⟩ := Out.CubePf.cubePull _ _ o.t.G _ (cubeMapOf h) o.t.PP o.t.cub
  have := o.t.semi.smooth
  have : Smooth ((Over.pullback y).obj o.t.G).hom := by
    change Smooth (pullback.snd o.t.G.hom y)
    infer_instance
  obtain ⟨am, kt⟩ := amplePt _ _ y _ _ _ h _ _ o.t.PP.isLB hL ⟨_, Out.CubePf.idIsoL_isGen hL⟩ o.ample o.ktriv
  have := o.t.semi.geomConnected
  have : GeometricallyConnected ((Over.pullback y).obj o.t.G).hom := by
    change GeometricallyConnected (pullback.snd o.t.G.hom y)
    infer_instance
  have : ConnectedSpace ((Over.pullback y).obj o.t.G).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := ((Over.pullback y).obj o.t.G).hom) (𝟙 _) (𝟙 _)
      ((Over.pullback y).obj o.t.G).hom (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected ((Over.pullback y).obj o.t.G).hom
    (eSec ((Over.pullback y).obj o.t.G) (default : PrimeSpectrum K))
  obtain ⟨-, ws, gs', -⟩ := hs o.t.sym
  obtain ⟨β, hβ⟩ := principalPolarisation_exists_unique_section hT
    { A := (Over.pullback y).obj o.t.G, g := d, smoothDim := hd, L := ((cubeMapOf h).rigLB o.t.PP hL hr).L
      isLB := hL, ample := am, ktriv := kt
      isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) h.1 o.proper, ‹_›⟩
      rigid := ⟨((cubeMapOf h).rigLB o.t.PP hL hr).rig, ((cubeMapOf h).rigLB o.t.PP hL hr).rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  exact ⟨β, fun s => (hβ s).exists⟩

theorem FamilyUnif_isOpen_ex {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) (i : Fin U.n)
    (P : (U.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ty P) (V : Xo.univ.t.G.left.Opens) :
    IsOpen {z | ⊤ ≤ (U.ex i P z).left ⁻¹ᵁ V} := by
  have h := ((U.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun x => differentiableOn_const _⟩).2 V 0).1
  have c : Continuous (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) := by fun_prop
  convert h.preimage c using 1
  ext z
  simp

theorem thetaFrame_ratio : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((U.Di i).La →+ (Fin g → ℂ))) (θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ), (∀ b ∈ B, IsPeriod (U.Di i) ty (P b)) → (∀ j, DifferentiableOn ℂ (fr j) {bz | bz.1 ∈ B ∧ ⊤ ≤ (U.ex i (P bz.1) bz.2).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) → (∀ j b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, z) ≠ 0) → (∀ j j' b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') → fr j (b, z) = valAt' (U.ex i (P b) z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' (b, z)) → (∀ j b, b ∈ B → ⊤ ≤ (U.ex i (P b) 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, 0) = valAt' (U.u i (P b)) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) → (∀ b ∈ B, ∃ s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).Sec, ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b))), x ≫ pullback.fst _ _ = (U.ex i (P b) z).left → x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => j)) (s.f (fun _ => j)) = θ b z * fr j (b, z)) → ∀ b ∈ B, ∀ b' ∈ B, ∀ h₀ : Matrix (Fin g) (Fin g) ℂ, θ b ≠ 0 → θ b' ≠ 0 → IsUnit h₀.det → (U.u i (P b)) = (U.u i (P b')) → (∀ z, (U.ex i (P b') (h₀ *ᵥ z)).left = (U.ex i (P b) z).left) → ∃ (ρ : (Fin g → ℂ) → ℂ) (κ : ℂ), Differentiable ℂ ρ ∧ (∀ z, ρ z ≠ 0) ∧ ρ 0 = 1 ∧ κ ≠ 0 ∧ (∀ z, θ b' (h₀ *ᵥ z) * ρ z = κ * θ b z) ∧ ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b', h₀ *ᵥ z) = ρ z * fr j (b, z) := by
  intro hT E _ _ _ H D l Xo σ g ty U i m B P θ fr hP hd hn hc h0 hs b hb b' hb' h₀ hθ hθ' hdet hu hex
  have cover : ∀ z, ∃ j, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z => by
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB ((U.ex i (P b) z).left (default : PrimeSpectrum ℂ))
    exact ⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩
  choose J hJ using cover
  have tr : ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      ⊤ ≤ (U.ex i (P b') (h₀ *ᵥ z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j z h => by rw [hex]; exact h
  have key : ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j (b', h₀ *ᵥ z) = fr (J z) (b', h₀ *ᵥ z) / fr (J z) (b, z) * fr j (b, z) := fun j z h => by
    have h1 : ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U (J z)) :=
      (top_le_preimage_inf _ _ _).2 ⟨h, hJ z⟩
    have e1 := hc j (J z) b z hb h1
    have e2 := hc j (J z) b' (h₀ *ᵥ z) hb' (by rw [hex]; exact h1)
    rw [hex] at e2
    have := hn _ _ _ hb (hJ z)
    rw [e1, e2]
    field_simp
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (Fin g → ℂ) → ℂ, ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j (b', h₀ *ᵥ z) = ρ z * fr j (b, z) := ⟨_, key⟩
  clear key
  have hρ0 : ∀ z, ρ z ≠ 0 := fun z h => hn _ _ _ hb' (tr _ _ (hJ z)) (by rw [hρ _ _ (hJ z), h, zero_mul])

  obtain ⟨s, hs1⟩ := hs b hb
  obtain ⟨s', hs2⟩ := hs b' hb'
  have hs3 : ∃ s' : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).Sec,
      ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b))), x ≫ pullback.fst _ _ = (U.ex i (P b') z).left →
      x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (U.ex i (P b') z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => j))
        (s'.f (fun _ => j)) = θ b' z * fr j (b', z) := by
    rw [hu]; exact ⟨s', hs2⟩
  clear s' hs2
  obtain ⟨s', hs2⟩ := hs3
  obtain ⟨β, hβ⟩ := exists_sec_generator_fibre hT Xo.univ (U.u i (P b))
  obtain ⟨a, ha⟩ := hβ s
  obtain ⟨a', ha'⟩ := hβ s'
  have val : ∀ z, ∃ v : ℂ, a * v = θ b z * fr (J z) (b, z) ∧
      a' * v = θ b' (h₀ *ᵥ z) * (ρ z * fr (J z) (b, z)) := fun z => by
    have w : (U.ex i (P b) z).left ≫ Xo.univ.t.G.hom = 𝟙 _ ≫ U.u i (P b) :=
      (Over.w (U.ex i (P b) z)).trans (Category.id_comp _).symm
    let x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b)) := pullback.lift _ _ w
    have x1 : x ≫ pullback.fst _ _ = (U.ex i (P b) z).left := pullback.lift_fst _ _ _
    have x2 : x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hx : ⊤ ≤ x ⁻¹ᵁ (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => J z) := by
      rw [top_le_preimage_iff_mem, mem_pull]
      have := hJ z
      rw [← x1, top_le_preimage_iff_mem] at this
      exact this
    have e1 := hs1 (J z) z x x1 x2 (hJ z)
    have e2 := hs2 (J z) (h₀ *ᵥ z) x (x1.trans (hex z).symm) x2 (tr _ _ (hJ z))
    rw [hρ _ _ (hJ z)] at e2
    have f1 := (congrArg (valAt' x _) (ha (fun _ => J z))).trans ((valAt'_mul _ _ _ _).trans
      (congrArg (· * _) (valAt'_constFn x _ x2 _ _ hx)))
    have f2 := (congrArg (valAt' x _) (ha' (fun _ => J z))).trans ((valAt'_mul _ _ _ _).trans
      (congrArg (· * _) (valAt'_constFn x _ x2 _ _ hx)))
    exact ⟨_, f1.symm.trans e1, f2.symm.trans e2⟩
  have ha0 : a ≠ 0 := fun h => hθ (funext fun z => by
    obtain ⟨v, e, -⟩ := val z
    rw [h, zero_mul] at e
    exact (mul_eq_zero.1 e.symm).resolve_right (hn _ _ _ hb (hJ z)))
  have ha0' : a' ≠ 0 := fun h => hθ' (funext fun w => by
    obtain ⟨v, -, e⟩ := val (h₀⁻¹ *ᵥ w)
    rw [h, zero_mul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at e
    exact (mul_eq_zero.1 e.symm).resolve_right (mul_ne_zero (hρ0 _) (hn _ _ _ hb (hJ _))))
  refine ⟨ρ, a' / a, fun z => ?_, hρ0, ?_, div_ne_zero ha0' ha0, fun z => ?_, hρ⟩
  · have ho := FamilyUnif_isOpen_ex U i (P b) (hP b hb) (Xo.univ.t.PP.L.U (J z))
    have hz := ho.mem_nhds (hJ z)
    have d1 : DifferentiableOn ℂ (fun z' => fr (J z) (b, z'))
        {z' | ⊤ ≤ (U.ex i (P b) z').left ⁻¹ᵁ Xo.univ.t.PP.L.U (J z)} :=
      (hd (J z)).comp (f := fun z' => (b, z')) (by fun_prop) (fun z' h => ⟨hb, h⟩)
    have dl : Differentiable ℂ (fun z' : Fin g → ℂ => h₀ *ᵥ z') :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h₀)).differentiable
    have d2 : DifferentiableOn ℂ (fun z' => fr (J z) (b', h₀ *ᵥ z'))
        {z' | ⊤ ≤ (U.ex i (P b) z').left ⁻¹ᵁ Xo.univ.t.PP.L.U (J z)} :=
      (hd (J z)).comp (f := fun z' => (b', h₀ *ᵥ z'))
        ((differentiable_const _).prodMk dl).differentiableOn (fun z' h => ⟨hb', tr _ _ h⟩)
    have d3 := (d2.mul (d1.inv (fun z' h => hn _ _ _ hb h))).congr (f₁ := ρ) (fun z' h => by
      have := hn _ _ _ hb h
      show ρ z' = fr (J z) (b', h₀ *ᵥ z') * (fr (J z) (b, z'))⁻¹
      rw [hρ _ _ h]; field_simp)
    exact d3.differentiableAt hz
  · have e := hρ _ _ (hJ 0)
    have t := tr _ _ (hJ 0)
    rw [Matrix.mulVec_zero] at e t
    have e' : fr (J 0) (b', 0) = fr (J 0) (b, 0) := by rw [h0 _ _ hb (hJ 0), h0 _ _ hb' t, hu]
    rw [e'] at e
    exact ((mul_eq_right₀ (hn _ _ _ hb (hJ 0))).1 e.symm)
  · obtain ⟨v, e1, e2⟩ := val z
    have := hn _ _ _ hb (hJ z)
    apply mul_right_cancel₀ this
    rw [_root_.mul_assoc, ← e2, _root_.mul_assoc, ← e1]
    field_simp

end GlobalTheory
end
end
