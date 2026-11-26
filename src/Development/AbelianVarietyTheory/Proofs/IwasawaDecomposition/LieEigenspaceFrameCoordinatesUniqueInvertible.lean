module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RelabelledWeight
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsBasicOpenCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertible
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertible
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.EigCoord

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc GlobalTheory.FlagBundle
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (IsUnivChart sp)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {n : ℕ}
  {xc : ∀ m : ℕ, sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) m) ⟶ (Over.pullback x).obj Z.t.G}

theorem exists_basis (hx : IsUnivChart _ n xc) (g : EigFrame Z φ x) (τ : E →+* ℂ) :
    ∃ B : Module.Basis (Fin (Dw.mult τ)) R (eig c φ hx τ), ∀ i, g.v τ i = vec Z.t x xc (B i) := by
  choose e he using fun i => vec_exists hx (g.v τ i) (g.tan τ i)
  have hm : ∀ i, e i ∈ eig c φ hx τ := fun i => (vec_eig_iff hx _ _).1 (by rw [← he i]; exact g.eig τ i)
  let b : Fin (Dw.mult τ) → eig c φ hx τ := fun i => ⟨e i, hm i⟩
  have key : ∀ w : eig c φ hx τ, ∃! a : Fin (Dw.mult τ) → R, ∑ j, a j • b j = w := fun w => by
    have h := g.basis τ (vec Z.t x xc w) (vec_tan hx _) ((vec_eig_iff hx _ _).2 w.2)
    rw [show g.v τ = fun j => vec Z.t x xc (e j) from funext he] at h
    simp only [comb_iff hx] at h
    refine (existsUnique_congr fun a => ?_).1 h
    rw [Subtype.ext_iff, eq_comm]
    simp [b]
  have li : LinearIndependent R b := Fintype.linearIndependent_iff.2 fun a ha i =>
    congrFun ((key 0).unique ha (show ∑ j, (0 : Fin (Dw.mult τ) → R) j • b j = 0 by simp)) i
  have sp' : ⊤ ≤ Submodule.span R (Set.range b) := fun w _ =>
    (Submodule.mem_span_range_iff_exists_fun R).2 (key w).exists
  exact ⟨Module.Basis.mk li sp', fun i => by rw [Module.Basis.mk_apply]; exact he i⟩

theorem exists_frame (hx : IsUnivChart _ n xc) (B : ∀ τ, Module.Basis (Fin (Dw.mult τ)) R (eig c φ hx τ)) :
    ∃ g : EigFrame Z φ x, ∀ τ i, g.v τ i = vec Z.t x xc (B τ i) := by
  refine ⟨⟨fun τ i => vec Z.t x xc (B τ i), fun τ i => vec_tan hx _, fun τ i => (vec_eig_iff hx _ _).2 (B τ i).2,
    fun τ w hw he => ?_⟩, fun _ _ => rfl⟩
  obtain ⟨cc, rfl⟩ := vec_exists hx w hw
  let v : eig c φ hx τ := ⟨cc, (vec_eig_iff hx _ _).1 he⟩
  have k : ∀ a, IsCombAtG Z.t x (fun i => vec Z.t x xc (B τ i)) a (vec Z.t x xc cc) ↔ (B τ).equivFun v = a := fun a => by
    rw [comb_iff hx, ← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp [v]
  simp only [k]
  exact existsUnique_eq'

theorem exists_basis_of_isUnit {M ι : Type} [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
    (B : Module.Basis ι R M) (A : Matrix ι ι R) (h : IsUnit A.det) :
    ∃ B' : Module.Basis ι R M, ∀ i, B' i = ∑ j, A i j • B j := by
  refine ⟨B.map (Matrix.toLinearEquiv B A.transpose (by rwa [Matrix.det_transpose])), fun i => ?_⟩
  simp [Matrix.toLin_self]

theorem isUnit_det_of_basis {M ι : Type} [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
    (B B' : Module.Basis ι R M) (A : Matrix ι ι R) (h : ∀ i, B' i = ∑ j, A i j • B j) : IsUnit A.det := by
  have e : A = (B.toMatrix B').transpose := by
    ext i j
    rw [Matrix.transpose_apply, Module.Basis.toMatrix_apply, h i, Module.Basis.repr_sum_self]
  rw [e, Matrix.det_transpose]
  exact B.isUnit_det B'

end GlobalTheory.ShFam.EigCoord


open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.EigCoord GlobalTheory.LieLocBasis in
theorem GlobalTheory.ShFam.EigCoord.coord_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (R' : Type) [CommRing R'] (φ' : c.F →+* R') (x' : Sp R' ⟶ Z.X) (ψ : R →+* R'), IsLocalRing R' → f.Stable → x' = spMap ψ ≫ x → φ' = ψ.comp φ → (∀ g : EigFrame Z φ' x', (∃! A : Mat Dw.mult R', f.Coord ψ g A) ∧ ∀ A, f.Coord ψ g A → ∀ τ, IsUnit (A τ).det) ∧ ∀ A : Mat Dw.mult R', (∀ τ, IsUnit (A τ).det) → ∃ g : EigFrame Z φ' x', f.Coord ψ g A := by
  intro E _ _ _ H Dw l Xo c O _ β Z R _ φ x f R' _ φ' x' ψ _ hf hx' hφ'
  subst hx' hφ'
  obtain ⟨g₀, hg₀⟩ := hf R' ψ
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t (spMap ψ ≫ x)
  choose B₀ hB₀ using exists_basis hx g₀
  have hv : ∀ τ, (fun k => spMap (dualMap ψ) ≫ f.v τ k) = g₀.v τ := fun τ => funext fun k => (hg₀ τ k).symm
  have key : ∀ (g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x))
      (B : ∀ τ, Module.Basis (Fin (Dw.mult τ)) R' (eig c (ψ.comp φ) hx τ)),
      (∀ τ i, g.v τ i = vec Z.t _ xc (B τ i)) → ∀ A : Mat Dw.mult R',
        f.Coord ψ g A ↔ ∀ τ i, B τ i = ∑ j, A τ i j • B₀ τ j := fun g B hB A => by
    simp only [EigFrame.Coord, true_and]
    refine forall_congr' fun τ => forall_congr' fun i => ?_
    rw [hv, hB, show g₀.v τ = fun j => vec Z.t _ xc (B₀ τ j) from funext (hB₀ τ), comb_iff hx, Subtype.ext_iff]
    simp
  refine ⟨fun g => ⟨?_, fun A hA τ => ?_⟩, fun A hA => ?_⟩
  · choose A hA hu using fun τ i => g₀.basis τ (g.v τ i) (g.tan τ i) (g.eig τ i)
    refine ⟨A, ⟨rfl, rfl, fun τ i => by rw [hv]; exact hA τ i⟩, fun A' hA' => ?_⟩
    funext τ i
    exact hu τ i _ (by have := hA'.2.2 τ i; rwa [hv] at this)
  · choose B hB using exists_basis hx g
    exact isUnit_det_of_basis (B₀ τ) (B τ) (A τ) ((key g B hB A).1 hA τ)
  · choose B hB using fun τ => exists_basis_of_isUnit (B₀ τ) (A τ) (hA τ)
    obtain ⟨g, hg⟩ := exists_frame hx B
    exact ⟨g, (key g B hg A).2 hB⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertibleStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.EigCoord GlobalTheory.LieLocBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (R' : Type) [CommRing R'] (φ' : c.F →+* R') (x' : Sp R' ⟶ Z.X) (ψ : R →+* R'), IsLocalRing R' → f.Stable → x' = spMap ψ ≫ x → φ' = ψ.comp φ → (∀ g : EigFrame Z φ' x', (∃! A : Mat Dw.mult R', f.Coord ψ g A) ∧ ∀ A, f.Coord ψ g A → ∀ τ, IsUnit (A τ).det) ∧ ∀ A : Mat Dw.mult R', (∀ τ, IsUnit (A τ).det) → ∃ g : EigFrame Z φ' x', f.Coord ψ g A := by
  exact @_root_.GlobalTheory.ShFam.EigCoord.coord_spec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartDirectionalDerivativeRegularCoordinate
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CxPts GlobalTheory.ProjSpace
open scoped Matrix

namespace GlobalTheory.ProjPos

theorem leviV_log_pos {n N : ℕ} {w : Fin N → V n → ℂ} {x : V n} (hC : ∀ a, ContDiffAt ℂ 2 (w a) x) {j : Fin N}
    (hj : w j =ᶠ[𝓝 x] fun _ => 1) (ξ : V n) (h : ¬ ∀ a, fderiv ℂ (w a) x ξ = 0) :
    0 < (leviV n (fun z => ((Real.log (∑ a, ‖w a z‖ ^ 2) : ℝ) : ℂ)) x ξ.ofLp).re := by
  have hD : ∀ a, DifferentiableAt ℂ (w a) x := fun a => (hC a).differentiableAt (by simp)
  have h1 : w j x = 1 := hj.eq_of_nhds
  have hne : (fun i => w i x) ≠ 0 := fun e => one_ne_zero (h1.symm.trans (congrFun e j))
  have e1 : (fun z => ((Real.log (∑ a, ‖w a z‖ ^ 2) : ℝ) : ℂ)) =
      fun y => ((Real.log (sqNorm (fun i => w i y)) : ℝ) : ℂ) := by
    funext y; simp [sqNorm, Complex.normSq_eq_norm_sq]
  have hJ (a) : (wJac n N w x *ᵥ ξ.ofLp) a = fderiv ℂ (w a) x ξ := by
    have hξ : ξ = ∑ j, ξ.ofLp j • bas n j := by
      ext i
      simp [bas, Pi.single_apply]
    conv_rhs => rw [hξ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [wJac, Matrix.mulVec, dotProduct, wd_of_differentiableAt (hD a), map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e1, leviLogNormSq n N w x ξ.ofLp hC hne, Complex.ofReal_re]
  refine div_pos (sqNorm_pos fun hz => h fun a => ?_) (sqNorm_pos hne)
  rw [projPerp_mulVec, sub_eq_zero] at hz
  have h2 := congrFun hz j
  rw [hJ, hj.fderiv_eq, Pi.smul_apply, h1, smul_eq_mul, mul_one] at h2
  have h3 := congrFun hz a
  rw [hJ, ← h2] at h3
  simpa using h3

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
  {c : AlgChart p σ D} {y : CxPts p σ} {W : Y.Opens} {ξ : V D}


variable (c y ξ) in
def dirDer (f : Γ(Y, W)) : ℂ := fderiv ℂ (ev p σ W f ∘ c.e.symm) (c.e y) ξ

theorem dirDer_add (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W) (f g : Γ(Y, W)) :
    dirDer c y ξ (f + g) = dirDer c y ξ f + dirDer c y ξ g := by
  have e : ev p σ W (f + g) ∘ c.e.symm = (ev p σ W f ∘ c.e.symm) + (ev p σ W g ∘ c.e.symm) :=
    funext fun v => ev_add _ _ _
  simp only [dirDer, e, fderiv_add (c.differentiableAt_ev f hy hW) (c.differentiableAt_ev g hy hW)]
  rfl

theorem dirDer_mul (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W) (f g : Γ(Y, W)) :
    dirDer c y ξ (f * g) = ev p σ W f y * dirDer c y ξ g + ev p σ W g y * dirDer c y ξ f := by
  have e : ev p σ W (f * g) ∘ c.e.symm = (ev p σ W f ∘ c.e.symm) * (ev p σ W g ∘ c.e.symm) :=
    funext fun v => ev_mul _ _ _
  simp only [dirDer, e, fderiv_mul (c.differentiableAt_ev f hy hW) (c.differentiableAt_ev g hy hW),
    Function.comp_apply, c.e.left_inv hy]
  rfl

theorem dirDer_const (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W) {f : Γ(Y, W)} {a : ℂ}
    (h : ∀ z ∈ ptsIn p σ W, ev p σ W f z = a) : dirDer c y ξ f = 0 := by
  have e : ev p σ W f ∘ c.e.symm =ᶠ[𝓝 (c.e y)] fun _ => a :=
    eventually_of_mem ((isOpen_over c.e (isOpen_ptsIn W)).mem_nhds (mem_over c.e hy hW)) fun v hv => h _ hv.2
  rw [dirDer, e.fderiv_eq]
  simp

theorem dirDer_res {W' : Y.Opens} (h : W' ≤ W) (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W') (f : Γ(Y, W)) :
    dirDer c y ξ (resG Y h f) = dirDer c y ξ f := by
  have e : ev p σ W' (resG Y h f) ∘ c.e.symm =ᶠ[𝓝 (c.e y)] ev p σ W f ∘ c.e.symm :=
    eventually_of_mem ((isOpen_over c.e (isOpen_ptsIn W')).mem_nhds (mem_over c.e hy hW))
      fun v hv => ev_res h hv.2 _
  simp only [dirDer, e.fderiv_eq]

theorem chartDirectionalDerivativeRegular_coordinate (hy : y ∈ c.e.source) (a : Fin D) : dirDer c y ξ (c.x a) = ξ a := by
  have e : ev p σ _ (c.x a) ∘ c.e.symm =ᶠ[𝓝 (c.e y)] (EuclideanSpace.proj (𝕜 := ℂ) a : V D →L[ℂ] ℂ) :=
    eventually_of_mem (c.e.open_target.mem_nhds (c.e.map_source hy)) fun v hv =>
      (c.apply_eq _ (c.e.map_target hv) a).symm.trans (by rw [c.e.right_inv hv]; rfl)
  rw [dirDer, e.fderiv_eq, ContinuousLinearMap.fderiv]
  rfl

theorem eq_zero_of_dirDer (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W) (hU : IsAffineOpen W)
    (h0 : ∀ f : Γ(Y, W), dirDer c y ξ f = 0) : ξ = 0 := by
  ext b
  obtain ⟨h, hhW, hh⟩ := hU.exists_basicOpen_le (V := c.U) ⟨_, mem_ptsIn.1 (c.source_subset hy)⟩ (mem_ptsIn.1 hW)
  have hB : y ∈ ptsIn p σ (Y.basicOpen h) := mem_ptsIn.2 hh
  have := hU.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h (resG Y hhW (c.x b))
  have ha' : resG Y hhW (c.x b) * resG Y (Y.basicOpen_le h) (h ^ n) = resG Y (Y.basicOpen_le h) a := by
    rw [map_pow]; exact ha
  have e := congrArg (dirDer c y ξ) ha'
  rw [dirDer_mul hy hB, dirDer_res _ hy hB, dirDer_res _ hy hB, dirDer_res _ hy hB, h0, h0, chartDirectionalDerivativeRegular_coordinate hy, mul_zero,
    zero_add, ev_res _ hB, ev_eq hW, map_pow, ← ev_eq] at e
  exact (mul_eq_zero.1 e).resolve_left (pow_ne_zero n ((mem_ptsIn_basicOpen hW h).1 hB))

variable {N : ℕ} (i : Y ⟶ PSpace k N) (hi : i ≫ PSpace.str k N = p)


include hi in
theorem eq_zero_of_dirDer_ratio [IsClosedImmersion i] (hy : y ∈ c.e.source) {j : Fin (N + 1)}
    (hW : y ∈ ptsIn p σ (i ⁻¹ᵁ chart k N j)) (h0 : ∀ a, dirDer c y ξ (i.app _ (ratio k N j a)) = 0) : ξ = 0 := by
  refine eq_zero_of_dirDer hy hW ((isAffineOpen_chart k N j).preimage i) fun f => ?_
  obtain ⟨g, rfl⟩ := i.app_surjective _ (isAffineOpen_chart k N j) f
  obtain ⟨P, rfl⟩ := aeval_ratio_surjective k N j g
  have hm : ∀ z : CxPts p σ, (PtsOver.map i hi _ z).1 = z.1 ≫ i := fun _ => rfl
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine dirDer_const hy hW (a := σ a) fun z hz => ?_
    rw [← ev_of_comp hm, MvPolynomial.aeval_C]
    exact ev_algX ((mem_ptsIn_preimage hm).1 hz) a
  | add P Q hP hQ => rw [map_add (f := _), map_add (f := _), dirDer_add hy hW, hP, hQ, add_zero]
  | mul_X P a hP => rw [map_mul, map_mul, dirDer_mul hy hW, hP, MvPolynomial.aeval_X, h0, mul_zero, mul_zero, add_zero]

theorem fubiniStudy_weight_pullback_chart_formula (j : Fin (N + 1)) (z : CxPts p σ) :
    ((ProjAn.fsO1 k σ N).pull i hi).φ (fun _ => j) z =
      Real.log (∑ a, ‖ev p σ (i ⁻¹ᵁ chart k N j) (i.app _ (ratio k N j a)) z‖ ^ 2) := by
  have hm : ∀ z : CxPts p σ, (PtsOver.map i hi _ z).1 = z.1 ≫ i := fun _ => rfl
  refine (Weight.pull_φ _ _ _ _ _).trans ((Weight.fsBasis_φ _ _ _ _ _ _ _).trans
    (congrArg _ (Finset.sum_congr rfl fun a _ => ?_)))
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← ev_of_comp hm]
  rfl

theorem fubiniStudy_weight_pullback_isSmooth (R : AnRead p σ D) : ((ProjAn.fsO1 k σ N).pull i hi).IsSmooth R :=
  Weight.IsSmooth.pull (R := .all _ σ N) (Weight.isSmooth_fsBasis _ _ _ _ _) i hi R

theorem fubiniStudy_weight_pullback_closed_immersion_strictPos [IsClosedImmersion i] (R : AnRead p σ D) :
    ((ProjAn.fsO1 k σ N).pull i hi).StrictPos R := by
  refine (fubiniStudy_weight_pullback_isSmooth i hi R).strictPos_of_exists fun y => ?_
  obtain ⟨l, hy⟩ := R.cover y
  obtain ⟨j, hj⟩ := GlobalTheory.ProjSpace.exists_mem_chart k N (i (y.1 (IsLocalRing.closedPoint ℂ)))
  have hW : y ∈ ptsIn p σ (i ⁻¹ᵁ chart k N j) := mem_ptsIn.2 hj
  set c := R.chart l
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (i ⁻¹ᵁ chart k N j))
  have hn := ho.mem_nhds (mem_over c.e hy hW)
  refine ⟨c, fun _ => j, hy, mem_ptsIn.2 (Set.mem_iInter.2 fun _ => hj), fun ξ hξ => ?_⟩
  simp only [AlgChart.levi, fubiniStudy_weight_pullback_chart_formula]
  refine leviV_log_pos (w := fun a => ev p σ (i ⁻¹ᵁ chart k N j) (i.app _ (ratio k N j a)) ∘ c.e.symm)
    (fun a => ((contDiffOn_of_differentiableOn D _ _ ho (c.holo _ _)).contDiffAt hn).of_le
      (WithTop.coe_le_coe.2 le_top)) (j := j) (eventually_of_mem hn fun v hv => ?_) (WithLp.toLp 2 ξ) fun h => ?_
  · rw [Function.comp_apply, ratio, ratioOn_self, map_one, ev_eq hv.2, map_one]
  · exact hξ (congrArg WithLp.ofLp (eq_zero_of_dirDer_ratio i hi hy hW h))

end GlobalTheory.ProjPos
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerExponentSectionOfChartRegular
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerExponentSectionOfChartRegular
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.SecGlueInt

open GlobalTheory.Reg.ChartCompat (comp_eq away_lift away_inj)
open GlobalTheory.Reg.SecGlue (chart_comp eq_of_fields)

def zchar {J S : Type} [Fintype J] [CommRing S] (e : J → ℤ) (t : J → Sˣ) : S := ((∏ i, t i ^ e i : Sˣ) : S)

theorem zchar_mul {J S : Type} [Fintype J] [CommRing S] (e : J → ℤ) (t t' : J → Sˣ) :
    zchar e (t * t') = zchar e t * zchar e t' := by
  simp only [zchar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul]

theorem zchar_one {J S : Type} [Fintype J] [CommRing S] (e : J → ℤ) : zchar e (1 : J → Sˣ) = 1 := by
  simp [zchar]

theorem zchar_map {J K S T : Type} [Fintype J] [Field K] [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]
    (φ : S →ₐ[K] T) (e : J → ℤ) (t : J → Sˣ) :
    zchar e (fun i => Units.map (φ : S →* T) (t i)) = φ (zchar e t) := by
  have : (∏ i, Units.map (φ : S →* T) (t i) ^ e i) = Units.map (φ : S →* T) (∏ i, t i ^ e i) := by
    simp only [map_prod, map_zpow]
  unfold zchar
  rw [this]
  rfl


set_option maxHeartbeats 1000000 in
attribute [local instance 1100] Subalgebra.algebra OreLocalization.instAlgebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem chart_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, ∀ (C C' : FChart h) (L : Type) [Field L] [Algebra c.F L] (ψ : C.R →ₐ[c.F] L) (ψ' : C'.R →ₐ[c.F] L) (z z' : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ C.y z → FrMap ψ' C'.y z' → FrBor t z z' → C.Z = C'.Z ∧ ∀ (e : Ix Dw → ℤ) (b : ∀ Z : Comp Xo c, Om Z) (hb : zchar e C.t * b C.Z ∈ C.R) (hb' : zchar e C'.t * b C'.Z ∈ C'.R), ψ' ⟨_, hb'⟩ = zchar e t * ψ ⟨_, hb⟩ := by
  intro E _ _ _ H Dw l Xo c hev h C C' L _ _ ψ ψ' z z' t hz hz' hbor
  have G := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c
  have U := GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c
  obtain ⟨g, hg, hopn⟩ := C'.opn C.R L ψ C.y z hz ⟨ψ', z', t⁻¹, hz', (G L).2.2.1 t z z' hbor⟩
  have hg0 : g ≠ 0 := fun e => hg (by rw [e, map_zero])
  have hg1 : C.R.val g ≠ 0 := fun e => hg0 (Subtype.ext e)
  have hZ : C.Z = C'.Z := by
    obtain ⟨ψ0, z0, t0, h1, h2⟩ := hopn (Om C.Z) C.R.val (Ne.isUnit hg1) C.yg C.gen
    exact comp_eq C C' ψ0 z0 t0 h1 h2
  refine ⟨hZ, ?_⟩
  obtain ⟨Z, R, sm, frac, y, yg, tC, gen, bor, mono, opn⟩ := C
  obtain ⟨Z', R', sm', frac', y', yg', tC', gen', bor', mono', opn'⟩ := C'
  dsimp only at *
  subst hZ
  intro e b hb hb'
  let S := Localization.Away g
  let lam : R →ₐ[c.F] S := IsScalarTower.toAlgHom c.F R S
  have hlam : IsUnit (lam g) := IsLocalization.Away.algebraMap_isUnit g
  obtain ⟨mu, hmu⟩ : ∃ m : S →ₐ[c.F] Om Z, m.comp lam = R.val := away_lift g R.val hg1
  obtain ⟨nu, hnu⟩ : ∃ m : S →ₐ[c.F] L, m.comp lam = ψ := away_lift g ψ hg
  have hinj : Function.Injective mu := away_inj g mu (by rw [hmu]; exact Subtype.val_injective)
  obtain ⟨w, hw⟩ := hev.bc R S lam y
  obtain ⟨φ, v, s, hv, hs⟩ := hopn S lam hlam w hw

  obtain ⟨vmu, hvmu⟩ := hev.bc S (Om Z) mu v
  have m1 : FrMap mu w yg := frMap_cancel _ _ _ lam mu y w yg hw (by rw [hmu]; exact gen)
  have b1 := frBorBC _ _ mu s v w vmu yg hs hvmu m1
  have m2 : FrMap (mu.comp φ) y' vmu := frMap_trans _ _ _ φ mu y' v vmu hv hvmu
  have b2 := (G _).2.1 _ _ _ _ _ b1 ((G _).2.1 _ _ _ _ _ ((G _).2.2.1 _ _ _ bor) bor')
  have e1 : mu.comp φ = R'.val := mono' _ _ _ _ _ _ m2 gen' b2
  have e2 : vmu = yg' := (U _ _ R'.val y').1 _ _ (e1 ▸ m2) gen'
  subst e2
  have e3 : tC = tC' * fun i => Units.map (mu : S →* Om Z) (s i) :=
    (G _).2.2.2 _ _ _ _ bor ((G _).2.1 _ _ _ _ _ bor' b1)

  obtain ⟨vnu, hvnu⟩ := hev.bc S L nu v
  have m3 : FrMap nu w z := frMap_cancel _ _ _ lam nu y w z hw (by rw [hnu]; exact hz)
  have b3 := frBorBC _ _ nu s v w vnu z hs hvnu m3
  have m4 : FrMap (nu.comp φ) y' vnu := frMap_trans _ _ _ φ nu y' v vnu hv hvnu
  have b4 := (G _).2.1 _ _ _ _ _ b3 hbor
  have e4 : nu.comp φ = ψ' := mono' _ _ _ _ _ _ m4 hz' b4
  have e5 : vnu = z' := (U _ _ ψ' y').1 _ _ (e4 ▸ m4) hz'
  subst e5
  have e6 : (fun i => Units.map (nu : S →* L) (s i)) * t = 1 :=
    (G _).2.2.2 _ _ _ _ b4 ((G _).1 _)
  have e7 : lam ⟨_, hb⟩ = zchar e s * φ ⟨_, hb'⟩ := by
    apply hinj
    have a1 : mu (lam ⟨_, hb⟩) = zchar e tC * b Z := DFunLike.congr_fun hmu ⟨_, hb⟩
    have a2 : mu (φ ⟨_, hb'⟩) = zchar e tC' * b Z := DFunLike.congr_fun e1 ⟨_, hb'⟩
    have a0 : zchar e tC = zchar e tC' * mu (zchar e s) :=
      (congrArg (zchar e) e3).trans ((zchar_mul _ _ _).trans (congrArg _ (zchar_map mu e s)))
    rw [map_mul, a1, a2]
    linear_combination (b Z) * a0
  have a3 : ψ ⟨_, hb⟩ = nu (zchar e s) * ψ' ⟨_, hb'⟩ := by
    rw [← hnu, ← e4, AlgHom.comp_apply, AlgHom.comp_apply, e7, map_mul]
  have a4 : nu (zchar e s) * zchar e t = 1 := by
    rw [← zchar_map, ← zchar_mul, e6, zchar_one]
  linear_combination (-(zchar e t)) * a3 - (ψ' ⟨_, hb'⟩) * a4

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Val

variable {h : GenFrEx Xo c} {e : Ix Dw → ℤ} {b : ∀ Z : Comp Xo c, Om Z}
  (hb : ∀ C : FChart h, zchar e C.t * b C.Z ∈ C.R)

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
def Val {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ∃ (C : FChart h) (ψ : C.R →ₐ[c.F] S) (z : FrPt Xo c S) (t : Ix Dw → Sˣ),
    FrMap ψ C.y z ∧ FrBor t z y ∧ v = zchar e t * ψ ⟨_, hb C⟩

theorem val_unique (hl : EvLaws Xo c) {L : Type} [Field L] [Algebra c.F L] {y : FrPt Xo c L} {v v' : L}
    (h1 : Val hb y v) (h2 : Val hb y v') : v = v' := by
  obtain ⟨C, ψ, z, t, hz, ht, rfl⟩ := h1
  obtain ⟨C', ψ', z', t', hz', ht', rfl⟩ := h2
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L
  have := (chart_compat E H Dw l Xo c hl h C C' L ψ ψ' z z' _ hz hz'
    (hmul _ _ _ _ _ ht (hinv _ _ _ ht'))).2 e b (hb C) (hb C')
  rw [this, ← mul_assoc, ← zchar_mul, mul_comm t, mul_inv_cancel_left]

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem val_map (hl : EvLaws Xo c) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y : FrPt Xo c S} {y' : FrPt Xo c T} (hy : FrMap φ y y') {v : S} (h1 : Val hb y v) :
    Val hb y' (φ v) := by
  obtain ⟨C, ψ, z, t, hz, ht, rfl⟩ := h1
  obtain ⟨z', hz'⟩ := hl.bc S T φ z
  refine ⟨C, φ.comp ψ, z', _, frMap_trans _ _ _ ψ φ _ _ _ hz hz', frBorBC _ _ φ t z y z' y' ht hz' hy, ?_⟩
  rw [zchar_map, map_mul]; rfl

theorem val_bor {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S}
    (hy : FrBor t y y') {v : S} (h1 : Val hb y v) : Val hb y' (zchar e t * v) := by
  obtain ⟨C, ψ, z, t₀, hz, ht, rfl⟩ := h1
  refine ⟨C, ψ, z, t₀ * t, hz, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c S).2.1 _ _ _ _ _ ht hy, ?_⟩
  rw [zchar_mul]; ring

theorem val_ex (hA : Atlas h) {L : Type} [Field L] [Algebra c.F L] (y : FrPt Xo c L) : ∃ v, Val hb y v := by
  obtain ⟨C, ψ, z, t, h1, h2⟩ := hA L y
  exact ⟨_, C, ψ, z, t, h1, h2, rfl⟩

theorem val_gen (hA : Atlas h) (Z : Comp Xo c) : Val hb (genFr h Z) (b Z) := by
  obtain ⟨C, ψ, z, t, h1, h2⟩ := hA _ (genFr h Z)
  obtain rfl := chart_comp Z C ψ z t h1 h2
  refine ⟨C, C.R.val, C.yg, C.t⁻¹, C.gen, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c _).2.2.1 _ _ _ C.bor, ?_⟩
  show b C.Z = zchar e C.t⁻¹ * (zchar e C.t * b C.Z)
  rw [← mul_assoc, ← zchar_mul, inv_mul_cancel, zchar_one, one_mul]

def Rep {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (g s : S) : Prop :=
  ∀ (L : Type) [Field L] [Algebra c.F L] (χ : S →ₐ[c.F] L) (w : FrPt Xo c L) (v : L),
    FrMap χ y w → Val hb w v → χ g * v = χ s

theorem exists_rep (hl : EvLaws Xo c) (hA : Atlas h) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ∃ s, Rep hb y 1 s := by
  let I : Ideal S :=
    { carrier := {g | ∃ s, Rep hb y g s}
      zero_mem' := ⟨0, fun L _ _ χ w v _ _ => by simp⟩
      add_mem' := by
        rintro g g' ⟨s, hs⟩ ⟨s', hs'⟩
        exact ⟨s + s', fun L _ _ χ w v h1 h2 => by
          rw [map_add (f := _), map_add (f := _), add_mul, hs L χ w v h1 h2, hs' L χ w v h1 h2]⟩
      smul_mem' := by
        rintro r g ⟨s, hs⟩
        exact ⟨r * s, fun L _ _ χ w v h1 h2 => by
          rw [smul_eq_mul, map_mul, map_mul, mul_assoc, hs L χ w v h1 h2]⟩ }
  by_contra hne
  have hI : I ≠ ⊤ := fun hI => hne ((Ideal.eq_top_iff_one I).1 hI)
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
  have := hP.isPrime
  let χ₀ : S →ₐ[c.F] FractionRing (S ⧸ P) :=
    (IsScalarTower.toAlgHom c.F (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mkₐ c.F P)
  obtain ⟨w₀, hw₀⟩ := hl.bc _ _ χ₀ y
  obtain ⟨C, ψ₀, z₀, t₀, h1, h2⟩ := hA _ w₀
  obtain ⟨g, hg, hloc⟩ := C.opn S _ χ₀ y w₀ hw₀ ⟨ψ₀, z₀, t₀, h1, h2⟩
  let lam : S →ₐ[c.F] Localization.Away g := IsScalarTower.toAlgHom c.F S _
  have hu : IsUnit (lam g) := IsLocalization.Away.algebraMap_isUnit g
  obtain ⟨w', hw'⟩ := hl.bc _ _ lam y
  obtain ⟨ψ, z, t, h3, h4⟩ := hloc _ lam hu w' hw'
  have hv : Val hb w' (zchar e t * ψ ⟨_, hb C⟩) := ⟨C, ψ, z, t, h3, h4, rfl⟩
  generalize zchar e t * ψ ⟨_, hb C⟩ = u at hv
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g u
  have hmem : g ^ (n + 1) ∈ I := by
    refine ⟨g * a, fun L _ _ χ w v h5 h6 => ?_⟩
    by_cases hχ : χ g = 0
    · simp [hχ]
    · let mu : Localization.Away g →ₐ[c.F] L :=
        IsLocalization.liftAlgHom (M := Submonoid.powers g) (f := χ) (by
          rintro ⟨_, k, rfl⟩
          simpa using (IsUnit.mk0 _ hχ).pow k)
      have hmu' : ∀ x, mu (algebraMap S _ x) = χ x := fun x => by
        simp [mu]
      have hmu : mu.comp lam = χ := AlgHom.ext hmu'
      have h7 : FrMap mu w' w := frMap_cancel _ _ _ lam mu y w' w hw' (by rw [hmu]; exact h5)
      have h8 := val_unique hb hl h6 (val_map hb hl mu h7 hv)
      have h9 := congrArg mu ha
      rw [map_mul, map_pow, hmu', hmu'] at h9
      rw [h8, map_mul, map_pow, ← h9]
      ring
  have hgP : g ∈ P := this.mem_of_pow_mem _ (hIP hmem)
  apply hg
  show algebraMap (S ⧸ P) (FractionRing (S ⧸ P)) (Ideal.Quotient.mk P g) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hgP, map_zero]

end Val

theorem exists_sec_of_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, Atlas h → ∀ (a : Ix Dw → ℤ) (b : ∀ Z : Comp Xo c, Om Z), (∀ C : FChart h, zchar a C.t * b C.Z ∈ C.R) → ∃ g ∈ GlobalTheory.AllWt.secZ Xo c a, ∀ Z, evC h Z g = b Z := by
  intro E _ _ _ H Dw l Xo c hl h hA a b hb
  have hred : ∀ p : TRing c.F, IsReduced p.R := fun p => (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  choose g hg using fun (p : TRing c.F) (y : FrPt Xo c p.R) => exists_rep hb hl hA y
  have hg' : ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (L : Type) [Field L] [Algebra c.F L] (χ : p.R →ₐ[c.F] L)
      (w : FrPt Xo c L) (v : L), FrMap χ y w → Val hb w v → χ (g p y) = v := by
    intro p y L _ _ χ w v h1 h2
    rw [← hg p y L χ w v h1 h2, map_one, one_mul]
  refine ⟨g, GlobalTheory.AllWt.mem_secZ.2 ⟨fun p q φ y z hz => ?_, fun p t y y' hy => ?_⟩, fun Z => ?_⟩
  · have := hred q
    refine eq_of_fields (K := c.F) _ _ fun L _ _ χ => ?_
    obtain ⟨w, hw⟩ := hl.bc _ _ χ z
    obtain ⟨v, hv⟩ := val_ex hb hA w
    rw [hg' q z L χ w v hw hv]
    exact (hg' p y L (χ.comp φ) w v (frMap_trans _ _ _ φ χ y z w hz hw) hv).symm
  · have := hred p
    show g p y' = zchar a t * g p y
    refine eq_of_fields (K := c.F) _ _ fun L _ _ χ => ?_
    obtain ⟨w, hw⟩ := hl.bc _ _ χ y
    obtain ⟨w', hw'⟩ := hl.bc _ _ χ y'
    obtain ⟨v, hv⟩ := val_ex hb hA w
    have hv' := val_bor hb (frBorBC _ _ χ t y y' w w' hy hw hw') hv
    rw [hg' p y' L χ w' _ hw' hv', map_mul, hg' p y L χ w v hw hv, zchar_map]
  · have hh := hl.test _ (genFr h Z)
    unfold evC evR evalAt
    rw [dite_eq_left hh]
    exact hg' _ _ _ _ _ _ hh.choose_spec.choose_spec.choose_spec (val_gen hb hA Z)

theorem exists_secZ_of_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (h : GenFrEx Xo c) (w : Ix Dw → ℤ) (b : ∀ Z : Comp Xo c, Om Z), (∀ C : FChart h, ((∏ i, C.t i ^ w i : (Om C.Z)ˣ) : Om C.Z) * b C.Z ∈ C.R) → ∃ f ∈ GlobalTheory.AllWt.secZ Xo c w, ∀ Z, evC h Z f = b Z := by
  intro E _ _ _ H Dw l Xo c h w b hb
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  exact exists_sec_of_regular E H Dw l Xo c hL h (hA h) w b hb

end GlobalTheory.SecGlueInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerExponentSectionOfChartRegularStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_exponent_section_of_chart_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (h : GenFrEx Xo c) (w : Ix Dw → ℤ) (b : ∀ Z : Comp Xo c, Om Z), (∀ C : FChart h, ((∏ i, C.t i ^ w i : (Om C.Z)ˣ) : Om C.Z) * b C.Z ∈ C.R) → ∃ f ∈ GlobalTheory.AllWt.secZ Xo c w, ∀ Z, evC h Z f = b Z := by
  first | exact @GlobalTheory.SecGlueInt.exists_secZ_of_regular | exact GlobalTheory.SecGlueInt.exists_secZ_of_regular | (intros; apply GlobalTheory.SecGlueInt.exists_secZ_of_regular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernRenameBlockPerm
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernRenameBlockPerm
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric.RootDiscrPerm

theorem prod_Iio_eq_det {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) :
    (∏ j : Fin N, ∏ i ∈ Finset.Iio j, (v j - v i)) = (Matrix.vandermonde v).det := by
  rw [Matrix.det_vandermonde]
  exact Finset.prod_comm' (fun j i => by simp [and_comm])

theorem det_vandermonde_comp_perm {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) (σ : Equiv.Perm (Fin N)) :
    (Matrix.vandermonde (fun i => v (σ i))).det = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) * (Matrix.vandermonde v).det := by
  have h : Matrix.vandermonde (fun i => v (σ i)) = (Matrix.vandermonde v).submatrix σ id := by
    ext i k; simp [Matrix.vandermonde_apply]
  rw [h, Matrix.det_permute]

theorem rootDiscr_eq_prod_det (ι : Type) [Fintype ι] (m : ι → ℕ) :
    rootDiscr m = ∏ τ, (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))).det := by
  unfold rootDiscr
  exact Finset.prod_congr rfl fun τ _ => prod_Iio_eq_det _

end GlobalTheory.GoodMetric.RootDiscrPerm

open GlobalTheory.GoodMetric.RootDiscrPerm in
theorem GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ))), rename (Equiv.sigmaCongrRight w) (rootDiscr m) = ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rootDiscr m := by
  intro ι _ m w
  rw [rootDiscr_eq_prod_det, map_prod]
  have h : ∀ τ, rename (Equiv.sigmaCongrRight w)
      (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))).det =
      ((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) * (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))).det := by
    intro τ
    rw [AlgHom.map_det]
    have e : (rename (Equiv.sigmaCongrRight w) : MvPolynomial (Root m) ℝ →ₐ[ℝ] MvPolynomial (Root m) ℝ).mapMatrix
        (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))) =
        Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, w τ i⟩ : MvPolynomial (Root m) ℝ)) := by
      ext i k; simp [Matrix.vandermonde_apply]
    rw [e]
    exact det_vandermonde_comp_perm (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ)) (w τ)
  rw [Finset.prod_congr rfl fun τ _ => h τ, Finset.prod_mul_distrib, zsmul_eq_mul]
  push_cast
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernRenameBlockPermStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagRelativeTangentTopChern_rename_block_perm : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ))), rename (Equiv.sigmaCongrRight w) (rootDiscr m) = ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rootDiscr m := by
  first | exact @GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr | exact GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr | (intros; apply GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromSpecStalkMemZeroLocusIff
open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.SncComponents

theorem fromSpecStalk_mem_zeroLocus_iff {Y : Scheme.{0}} (U : Y.affineOpens) (x : Y) (hx : x ∈ U.1)
    (f : Γ(Y, U.1)) (q : PrimeSpectrum (Y.presheaf.stalk x)) :
    Y.fromSpecStalk x q ∈ Y.zeroLocus {f} ↔ Y.presheaf.germ U.1 x hx f ∈ q.asIdeal := by
  have hU : IsAffineOpen U.1 := U.2
  have e : Y.fromSpecStalk x q =
      hU.fromSpec (PrimeSpectrum.comap (Y.presheaf.germ U.1 x hx).hom q) := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hx]
    rfl
  rw [Scheme.mem_zeroLocus_iff, e]
  simp only [Set.mem_singleton_iff, forall_eq]
  have h := hU.fromSpec_preimage_basicOpen f
  have h2 : hU.fromSpec (PrimeSpectrum.comap (Y.presheaf.germ U.1 x hx).hom q) ∈ Y.basicOpen f ↔
      PrimeSpectrum.comap (Y.presheaf.germ U.1 x hx).hom q ∈ PrimeSpectrum.basicOpen f :=
    iff_of_eq (congrArg (fun V => PrimeSpectrum.comap (Y.presheaf.germ U.1 x hx).hom q ∈ V) h)
  exact (not_congr h2).trans not_not

theorem effCartier_of_mem_comps {Y : Scheme.{0}} [IsNoetherian Y] {Z : Y.IdealSheafData}
    (hZ : FinalTheorems.Snc Z) (C : Closeds Y) (hC : (C : Set Y) ∈ comps (Z.support : Set Y)) :
    FinalTheorems.EffCartier (Scheme.IdealSheafData.vanishingIdeal C) := by
  refine effCartier_of_stalkId _ fun x => ?_
  obtain ⟨hreg, U, hx, n, f, J, hrsp, hZU⟩ := hZ x
  obtain ⟨O, hxO, -, hO⟩ := exists_open_comps x U hx f J hrsp hZU
  have hO' := hO _ hC
  have hq : ∀ q : PrimeSpectrum (Y.presheaf.stalk x), Y.fromSpecStalk x q ∈ (C : Set Y) ↔
      ∃ i ∈ J, IsBranch (Z.support : Set Y) (f i) x C ∧
        Y.presheaf.germ U.1 x hx (f i) ∈ q.asIdeal := by
    intro q
    have hqO : Y.fromSpecStalk x q ∈ (O : Set Y) := by
      have h : Y.fromSpecStalk x q ∈ Set.range (Y.fromSpecStalk x) := ⟨q, rfl⟩
      rw [Scheme.range_fromSpecStalk] at h
      exact Specializes.mem_open h O.isOpen hxO
    have h := Set.ext_iff.1 hO' (Y.fromSpecStalk x q)
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hqO, and_true, true_and,
      fromSpecStalk_mem_zeroLocus_iff U x hx] at h
    exact h
  have hCC : C.compl.compl = C := SetLike.coe_injective (compl_compl _)
  by_cases hb : ∃ i ∈ J, IsBranch (Z.support : Set Y) (f i) x C
  · obtain ⟨i, hi, hbi⟩ := hb
    have hp : Prime (Y.presheaf.germ U.1 x hx (f i)) :=
      prime_of_regular_params (fun i => Y.presheaf.germ U.1 x hx (f i)) hrsp.1 hrsp.2 i
    haveI : IsDomain (Y.presheaf.stalk x) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
    refine ⟨_, mem_nonZeroDivisors_of_ne_zero hp.ne_zero, ?_⟩
    have h := AffineComplement.stalkId_vanishingIdeal_compl C.compl x
      (Y.presheaf.germ U.1 x hx (f i)) fun q => by
        refine not_congr ((hq q).trans ⟨?_, fun h => ⟨i, hi, hbi, h⟩⟩)
        rintro ⟨j, hj, hbj, h⟩
        by_cases hij : i = j
        · exact hij ▸ h
        · exact absurd rfl (branch_ne x U hx f J hrsp hZU hi hj hij hbi hbj)
    rw [hCC] at h
    rw [h]
    exact ((Ideal.span_singleton_prime hp.ne_zero).2 hp).radical
  · refine ⟨1, one_mem _, ?_⟩
    have h := AffineComplement.stalkId_vanishingIdeal_compl C.compl x 1 fun q => by
      refine not_congr ((hq q).trans ⟨?_, fun h => ?_⟩)
      · rintro ⟨j, hj, hbj, -⟩
        exact absurd ⟨j, hj, hbj⟩ hb
      · exact absurd ((Ideal.eq_top_iff_one _).2 h) q.isPrime.ne_top
    rw [hCC] at h
    rw [h, Ideal.span_singleton_one, Ideal.radical_top]

theorem exists_compList_effCartier (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ)
    [SmoothOfRelativeDimension d p] [QuasiCompact p] (B : Closeds Y)
    (hB : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)) :
    ∃ (m : ℕ) (C : Fin m → Closeds Y), FinalTheorems.CompList (B : Set Y) C ∧
      ∀ i, FinalTheorems.EffCartier (Scheme.IdealSheafData.vanishingIdeal (C i)) := by
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  haveI : IsNoetherian Y := {}
  haveI : Finite (comps (B : Set Y)) := (comps_finite _).to_subtype
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin (comps (B : Set Y))
  refine ⟨m, fun i => ⟨(e.symm i).1, isClosed_of_mem_comps B.isClosed (e.symm i).2⟩,
    ⟨fun i => (e.symm i).2.1.1, ?_, fun i j hij => ?_⟩, fun i => ?_⟩
  · conv_rhs => rw [← sUnion_comps (B : Set Y), Set.sUnion_eq_iUnion]
    exact e.symm.surjective.iUnion_comp (fun c => (c.1 : Set Y))
  · have hi : Maximal (fun C => IsIrreducible C ∧ C ⊆ (B : Set Y)) (e.symm i).1 := (e.symm i).2
    exact e.symm.injective (Subtype.ext (Set.Subset.antisymm hij (hi.2 (e.symm j).2.1 hij)))
  · refine effCartier_of_mem_comps hB _ ?_
    have hs : ((Scheme.IdealSheafData.vanishingIdeal B).support : Set Y) = B := by simp
    rw [hs]
    exact (e.symm i).2

end GlobalTheory.SncComponents
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalTripleFibresBaseChangeKeyData
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalTripleFibresBaseChangeKeyData
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem tied_keyPB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (S S' : Type) [CommRing S] [Algebra c.F S] [CommRing S'] [Nontrivial S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (y : FrPt Xo c S) (z : FrPt Xo c S') (Φ : FibKey Xo S y.x) (Φ' : FibKey Xo S' z.x), FrMap φ y z → Tied e y.s y.u Φ → Tied e z.s z.u Φ' → KeyPB Φ'.key Φ.key φ.toRingHom := by
  open GlobalTheory GlobalTheory.CM GlobalTheory.Frames MonoidalCategory CartesianMonoidalCategory MonObj IsDedekindDomain MeasureTheory in
  intro E _ _ _ H Dw l Xo c g e S S' _ _ _ _ _ φ y z Φ Φ' hm ⟨ht, hg1, hv1⟩ ⟨ht', hg2, hv2⟩
  obtain ⟨hx, hu, hs⟩ := ((GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S S' φ y).2.2 z).1 hm
  obtain ⟨hg, v', hv', hk, hv⟩ := GlobalTheory.LamT.fibKey_keyPB E H Dw l Xo S S' φ.toRingHom y.x z.x Φ Φ' y.s z.s hx ht ht' hs
  have hvv : v' = Φ'.v := by
    funext i
    apply Over.OverMorphism.ext
    apply Φ'.m.cart.1.hom_ext
    · rw [hv i, hv1, hv2, hu]
      rfl
    · rw [Over.w, Over.w]
  subst hvv
  exact hk

end GlobalTheory.KeyFourth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalTripleFibresBaseChangeKeyDataStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_triple_fibres_base_change_key_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (S S' : Type) [CommRing S] [Algebra c.F S] [CommRing S'] [Nontrivial S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (y : FrPt Xo c S) (z : FrPt Xo c S') (Φ : FibKey Xo S y.x) (Φ' : FibKey Xo S' z.x), FrMap φ y z → Tied e y.s y.u Φ → Tied e z.s z.u Φ' → KeyPB Φ'.key Φ.key φ.toRingHom := by
  first | exact @GlobalTheory.KeyFourth.tied_keyPB | exact GlobalTheory.KeyFourth.tied_keyPB | (intros; apply GlobalTheory.KeyFourth.tied_keyPB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldedIsSecZeroKeySection
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

namespace GlobalTheory.CuspFrom.KeyHol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem exists_sec_rdU_ne_zero (U : Formalism.L2.PjFree.Unf Xo c σ r) (k : U.Comp) (x₀ : Frame (U.X k).Ψ r)
    (hx₀ : x₀ ∈ (U.X k).dom) :
    ∃ (m : ℕ) (f : Rul Xo c), f ∈ sec Xo c 0 (2 * (m + 1)) ∧ Formalism.L2.PjFree.rdU U f k x₀ ≠ 0 := by
  have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
  have hR : Odd 3 := by decide
  have h1 : 1 < 3 := by norm_num
  obtain ⟨hfG, hfL, -⟩ := GlobalTheory.EtaCard.card_levGrp_and_span E H Dw 3 h1
  letI hFin : Fintype (GlobalTheory.EtaForm.LatMod Dw 3) := Fintype.ofFinite _
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  obtain ⟨cf, -, hne⟩ := GlobalTheory.EtaForm.exists_small_coeff_etaValAt_ne_zero GlobalTheory.firstFiveLaws.1 E H Dw l Xo c 3 hR h1
    2 0 (CAt σ) 1 (fun _ => U.un k ⟨x₀, hx₀⟩)
  obtain ⟨⟨f, hrule, -⟩, hsec⟩ := GlobalTheory.EtaForm.isEtaRule_existsUnique_mem_sec GlobalTheory.firstFiveLaws.1 E H Dw l Xo c 3 hR
    (Fin 2 → GlobalTheory.EtaForm.LatMod Dw 3) 2 (fun j => (cf j : ℤ)) (GlobalTheory.EtaForm.shiftFam 3 0)
  have hpos : 0 < Nat.card (GlobalTheory.EtaForm.LevGrp Dw (3 ^ 4)) := Nat.card_pos
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  refine ⟨m, f, by have := hsec f hrule; rwa [hm] at this, ?_⟩
  have hv := (GlobalTheory.EtaForm.etaValAt_evR_of_fromTest E H Dw l Xo c 3 hR _ _ _ _ f hrule (CAt σ) (U.un k ⟨x₀, hx₀⟩)
    (hT _ _)).1
  have h0 := hne 0 _ hv
  have e1 : Formalism.L2.PjFree.rdU U f k x₀ = Formalism.L2.PjFree.toC (evR Xo c f (U.un k ⟨x₀, hx₀⟩)) := dif_pos hx₀
  rw [e1]
  exact h0

end GlobalTheory.CuspFrom.KeyHol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBadPrimeOverBadPlaceOfChain
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBadPrimeOverBadPlaceOfChain
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT

theorem exists_SBof_over : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v → ∃ P ∈ SBof I a, Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P) := by
  classical
  intro B X I hOk l Z a v hv
  obtain ⟨-, hPr, -⟩ := base_fields_primes_ok B X
  rcases hv with hv | ⟨P, hP, rfl⟩
  · have key : ∀ (i : Fin 2), v ∈ plUnder (I.rec7 l Z).host.F (E := (I.rec7 l Z).host.E) ((B.primes X).vG i) ↔ ((B.primes X).g i : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal := by
      intro i
      have h0 : B.fields.conjO ((B.primes X).piG i) ≠ 0 := by
        intro h
        have h1 := hPr.piG_norm i
        rw [h, mul_zero] at h1
        exact (Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero) h1.symm
      refine mem_plUnder_iff_norm (I.rec7 l Z).sp.cm (fun P => mem_divs h0 P) ((B.primes X).g i) ?_ v
      have h2 : cO (I.rec7 l Z).host.E (B.fields.conjO ((B.primes X).piG i)) = (B.primes X).piG i := cO_cO ((B.primes X).piG i)
      rw [h2]
      have h3 : B.fields.conjO ((B.primes X).piG i) * (B.primes X).piG i = ((B.primes X).g i : 𝓞 B.fields.E) := by
        rw [mul_comm]
        exact hPr.piG_norm i
      exact h3
    have hv' : v ∈ plUnder (I.rec7 l Z).host.F (E := (I.rec7 l Z).host.E) (B.primes X).vGs := by
      rcases hv with h | h
      · obtain ⟨P, hP, hPv⟩ := (key 0).2 h
        exact ⟨P, Finset.mem_union_left _ hP, hPv⟩
      · obtain ⟨P, hP, hPv⟩ := (key 1).2 h
        exact ⟨P, Finset.mem_union_right _ hP, hPv⟩
    obtain ⟨P, hP, hPv⟩ := hv'
    refine ⟨P, Finset.mem_union_left _ hP, ?_⟩
    exact hPv
  · refine ⟨P, Finset.mem_union_right _ hP, ?_⟩
    exact rfl

end GlobalTheory.Mem.Col2.AdT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBadPrimeOverBadPlaceOfChainStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_badPrime_over_bad_place_of_chain : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v → ∃ P ∈ SBof I a, Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.exists_SBof_over | exact GlobalTheory.Mem.Col2.AdT.exists_SBof_over | (intros; apply GlobalTheory.Mem.Col2.AdT.exists_SBof_over <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceDimensionEqSumChoose
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceDimensionEqSumChoose
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.FlagDimSum

theorem mul_add_choose_two (p q : ℕ) :
    p * q + p.choose 2 + q.choose 2 = (p + q).choose 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 : (q + 1).choose 2 = q + q.choose 2 := by
      rw [Nat.choose_succ_succ' q 1, Nat.choose_one_right]
    have h2 : (p + q + 1).choose 2 = (p + q) + (p + q).choose 2 := by
      rw [Nat.choose_succ_succ' (p + q) 1, Nat.choose_one_right]
    rw [← add_assoc, h1, h2, ← ih]
    ring

theorem dim_add_sum_choose : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H), Dw.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 =
      Module.finrank ℚ E / 2 * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) := by
  intro E _ _ _ H Dw
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ => τ (H.rt : E) = H.rt0)
  rw [Finset.card_univ, Embeddings.card] at h1
  have h2 := GlobalTheory.PeriodCoord.card_cmType H
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h2
  have h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E) := by
    rw [← (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E),
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  have h4 : (Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (H.rt : E) = H.rt0)).card =
      Module.finrank ℚ E / 2 := by
    omega
  have hs : ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 =
      Module.finrank ℚ E / 2 * (Dw.p.choose 2 + Dw.q.choose 2) := by
    simp_rw [Datum.mult, apply_ite (fun n : ℕ => n.choose 2)]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, h4, h2, smul_eq_mul, smul_eq_mul, mul_add]
  rw [hs, Datum.dim, ← Nat.choose_two_right, ← mul_add_choose_two, mul_assoc, ← mul_add, ← add_assoc]

end GlobalTheory.FlagDimSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceDimensionEqSumChooseStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_space_dimension_eq_sum_choose : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H), Dw.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 = Module.finrank ℚ E / 2 * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) := by
  first | exact @GlobalTheory.FlagDimSum.dim_add_sum_choose | exact GlobalTheory.FlagDimSum.dim_add_sum_choose | (intros; apply GlobalTheory.FlagDimSum.dim_add_sum_choose <;> assumption)
end
end
