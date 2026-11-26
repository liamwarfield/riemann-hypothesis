module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TorusGraphMaps
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermFormConjDiag
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameOfIsPeriod
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsDerivAt0NotIsDerivAlong
noncomputable section

namespace GlobalTheory.PeriodCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open scoped TensorProduct Topology

section Period

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isTypeFn_iff (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) :
    Tor.IsTypeFn H D.p D.q ty ↔ IndefiniteRowSideFullHecke.PeriodMapPresentation.IsTypeFn D ty := by
  refine forall_congr' fun τ => ?_
  unfold sigMult
  by_cases h : τ (H.rt : E) = H.rt0 <;> simp [h]

theorem isTypeFn_of_sum (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (h : ∀ a : 𝓞 E, ∑ i, ty i (a : E) = sigTrace D a) : IndefiniteRowSideFullHecke.PeriodMapPresentation.IsTypeFn D ty := by
  classical
  let κ := Σ τ : E →+* ℂ, Fin (sigMult D τ)
  let ε := Fintype.equivFin κ
  have h0 : IndefiniteRowSideFullHecke.PeriodMapPresentation.IsTypeFn D (fun k => (ε.symm k).1) := fun τ => by
    rw [Nat.card_congr (ε.symm.subtypeEquiv (q := fun x : κ => x.1 = τ) fun _ => Iff.rfl),
      Nat.card_congr (Equiv.sigmaSubtype τ)]
    simp
  obtain ⟨e, he⟩ := PeriodNonempty.exists_equiv_of_sum_eq ty (fun k => (ε.symm k).1) fun a => by
    rw [h, PeriodNonempty.sum_type H ((isTypeFn_iff D _).2 h0)]
    rfl
  intro τ
  rw [← h0 τ]
  exact Nat.card_congr (e.subtypeEquiv fun i => by rw [← he i])

theorem finiteDimensional (D : Datum H) : Module.Finite ℤ D.La ∧ Module.Free ℤ D.La := by
  haveI := D.fin
  haveI := D.proj
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  exact ⟨inferInstance, inferInstance⟩

theorem trace_eq_of_pos {W : Type} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (B : LinearMap.BilinForm ℝ W) (J J' A : W →ₗ[ℝ] W) (hJ : ∀ x, J (J x) = -x) (hJ' : ∀ x, J' (J' x) = -x)
    (hp : ∀ x, x ≠ 0 → 0 < B (J x) x) (hp' : ∀ x, x ≠ 0 → 0 < B (J' x) x)
    (hA : J ∘ₗ A = A ∘ₗ J) (hA' : J' ∘ₗ A = A ∘ₗ J') :
    LinearMap.trace ℝ W (J ∘ₗ A) = LinearMap.trace ℝ W (J' ∘ₗ A) := by
  have hinj : Function.Injective (J + J') := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have h1 := hp x h0
    have h2 := hp' x h0
    have h3 : B ((J + J') x) x = 0 := by rw [hx]; simp
    simp only [LinearMap.add_apply, map_add (f := _)] at h3
    linarith
  let T := LinearEquiv.ofInjectiveEndo _ hinj
  have hT : ∀ x, T x = J x + J' x := fun _ => rfl
  have hA1 : ∀ x, J (A x) = A (J x) := fun x => LinearMap.congr_fun hA x
  have hA2 : ∀ x, J' (A x) = A (J' x) := fun x => LinearMap.congr_fun hA' x
  rw [← LinearMap.trace_conj' (J ∘ₗ A) T]
  congr 1
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := T.surjective y
  rw [LinearEquiv.conj_apply_apply, T.symm_apply_apply, hT, hT]
  simp only [LinearMap.comp_apply, map_add (f := _), ← hA1, ← hA2, hJ, hJ']
  abel

theorem mem_domain (D : Datum H) {J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La} (h1 : ∀ x, J (J x) = -x)
    (h2 : ∀ a : 𝓞 E, J ∘ₗ actR D a = actR D a ∘ₗ J)
    (h3 : ∀ x y, D.EF.baseChange ℝ (J x) (J y) = D.EF.baseChange ℝ x y)
    (h4 : ∀ x, x ≠ 0 → 0 < D.EF.baseChange ℝ (J x) x) : J ∈ domain D := by
  obtain ⟨_, _⟩ := finiteDimensional D
  obtain ⟨J', k1, k2, -, k4, k5⟩ := domain_nonempty D
  refine ⟨h1, h2, h3, h4, fun a => ?_⟩
  rw [trace_eq_of_pos _ J J' _ h1 k1 h4 k4 (h2 a) (k2 a), k5]

theorem trace_of_presents {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    {J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La} (h : Presents D ty P J) (a : 𝓞 E) :
    ((LinearMap.trace ℝ _ (actR D a) : ℝ) : ℂ) / 2 -
      Complex.I * ((LinearMap.trace ℝ _ (J ∘ₗ actR D a) : ℝ) : ℂ) / 2 = ∑ i, ty i (a : E) := by
  obtain ⟨_, _⟩ := finiteDimensional D
  obtain ⟨φ, -, h2, h3⟩ := h
  let f : Module.End ℂ (Fin g → ℂ) := Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E))
  have hf : ∀ z, f z = tyAct ty a z := fun z => by
    funext i; simp [f, tyAct, Matrix.mulVec_diagonal]
  have ht : LinearMap.trace ℂ _ f = ∑ i, ty i (a : E) := by simp [f]
  have e1 : φ.conj (actR D a) = f.restrictScalars ℝ := by
    refine LinearMap.ext fun y => ?_
    rw [LinearEquiv.conj_apply_apply, h3, φ.apply_symm_apply]
    exact (hf y).symm
  have e2 : φ.conj (J ∘ₗ actR D a) = (Complex.I • f).restrictScalars ℝ := by
    refine LinearMap.ext fun y => ?_
    rw [LinearEquiv.conj_apply_apply, LinearMap.comp_apply, h2, h3, φ.apply_symm_apply, ← hf]
    rfl
  rw [← LinearMap.trace_conj' _ φ, ← LinearMap.trace_conj' (J ∘ₗ actR D a) φ, e1, e2, PeriodNonempty.trace_real,
    PeriodNonempty.trace_real, map_smul, ht]
  generalize ∑ i, ty i (a : E) = t
  apply Complex.ext
  · simp
  · simp; ring

def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm z w).im)
    (fun a b c => by simp [hermForm, add_dotProduct])
    (fun r a b => by simp [hermForm, smul_dotProduct])
    (fun a b c => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun r a b => by
      simp only [hermForm, star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul]
      simp)

theorem exists_presents {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (h : IsPeriod D ty P) : ∃ J ∈ domain D, Presents D ty P J := by
  obtain ⟨_, _⟩ := finiteDimensional D
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, -, hpos, hE⟩ := h
  let ψ : ℝ ⊗[ℤ] D.La →ₗ[ℝ] (Fin g → ℂ) := P.toIntLinearMap.liftBaseChange ℝ
  have hψ : ∀ (r : ℝ) x, ψ (r ⊗ₜ x) = r • P x := fun r x => by simp [ψ]
  have hsurj : Function.Surjective ψ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by simp [hψ]⟩
  have hrk : Module.finrank ℝ (ℝ ⊗[ℤ] D.La) = Module.finrank ℝ (Fin g → ℂ) := by
    haveI : DiscreteTopology (LinearMap.range P.toIntLinearMap) := hdisc
    haveI : IsZLattice ℝ (LinearMap.range P.toIntLinearMap) := ⟨hspan⟩
    rw [Module.finrank_baseChange, (LinearEquiv.ofInjective P.toIntLinearMap hinj).finrank_eq, ZLattice.rank ℝ]
  let φ := LinearEquiv.ofBijective ψ ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).2 hsurj, hsurj⟩
  have hφ : ∀ (r : ℝ) x, φ (r ⊗ₜ x) = r • P x := hψ
  let J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
    φ.symm.conj ((Complex.I • (LinearMap.id : Module.End ℂ (Fin g → ℂ))).restrictScalars ℝ)
  have hJ : ∀ v, φ (J v) = Complex.I • φ v := fun v => by simp [J, LinearEquiv.conj_apply_apply]
  have hact : ∀ (a : 𝓞 E) v, φ (actR D a v) = tyAct ty a (φ v) := fun a v => by
    induction v using TensorProduct.induction_on with
    | zero => funext i; simp [tyAct]
    | add u v hu hv => funext i; simp [tyAct, hu, hv, mul_add]
    | tmul r x =>
      funext i
      have : actR D a (r ⊗ₜ x) = r ⊗ₜ (a • x) := rfl
      simp [this, hφ, tyAct, hlin, mul_left_comm]
  have hB : ∀ x y, D.EF.baseChange ℝ x y = imForm Hm (φ x) (φ y) := fun x y => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']
    | tmul r x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' h h' => simp only [map_add (f := _), h, h']
      | tmul r' y =>
        have : imForm Hm (P x) (P y) = D.EF x y := hE x y
        simp only [hφ, map_smul, LinearMap.smul_apply, this, LinearMap.BilinForm.baseChange_tmul, smul_eq_mul,
          zsmul_eq_mul]
        ring
  refine ⟨J, mem_domain D (fun x => φ.injective ?_) (fun a => LinearMap.ext fun v => φ.injective ?_)
    (fun x y => ?_) (fun x hx => ?_), φ, fun x => by simp [hφ], hJ, hact⟩
  · rw [hJ, hJ, smul_smul, Complex.I_mul_I, map_neg, neg_smul, one_smul]
  · simp only [LinearMap.comp_apply, hJ, hact]
    funext i; simp [tyAct, mul_left_comm]
  · rw [hB, hB, hJ, hJ]
    change (hermForm _ _ _).im = (hermForm _ _ _).im
    simp [hermForm, star_smul, Matrix.mulVec_smul, Matrix.mulVec_neg, ← mul_assoc]
  · rw [hB, hJ]
    have := hpos (φ x) (by simpa using hx)
    change 0 < (hermForm _ _ _).im
    simpa [hermForm, smul_dotProduct] using this

theorem isPeriod_of_presents {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    {J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La} (hJ : J ∈ domain D) (h : Presents D ty P J) : IsPeriod D ty P := by
  classical
  obtain ⟨_, _⟩ := finiteDimensional D
  obtain ⟨-, -, hinv, hpos, -⟩ := hJ
  obtain ⟨e, hP, heJ, heρ⟩ := h
  let b := Module.Free.chooseBasis ℤ D.La
  let c := (b.baseChange ℝ).map e
  have hc : ∀ i, c i = P (b i) := fun i => by simp [c, hP]
  have hrange : P.range = (Submodule.span ℤ (Set.range c)).toAddSubgroup := by
    have h1 : Set.range c = P.toIntLinearMap '' Set.range b := by
      rw [← Set.range_comp]; congr 1; funext i; exact hc i
    rw [h1, ← Submodule.map_span, b.span_eq]
    ext z; simp
  refine ⟨fun a x i => ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hP, ← hP]
    exact congrFun (heρ a (1 ⊗ₜ x)) i
  · set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    rw [← hP, e.map_eq_zero_iff] at hx
    apply b.ext_elem
    intro i
    have := congrArg (fun v => (b.baseChange ℝ).repr v i) hx
    simpa using this
  · rw [hrange]; infer_instance
  · rw [eq_top_iff, ← c.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, (hc i).symm⟩
  · have halt0 : ∀ x y, D.EF x y = -D.EF y x := fun x y => by
      have := D.alt (x + y)
      simp only [map_add (f := _), LinearMap.add_apply, D.alt] at this
      linarith
    have halt : ∀ x y, D.EF.baseChange ℝ x y = -D.EF.baseChange ℝ y x := fun x y => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']; ring
      | tmul r x =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add y y' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']; ring
        | tmul r' y => simp [halt0 x y, mul_comm]
    have hs : ∀ z, e.symm (Complex.I • z) = J (e.symm z) := fun z => by
      rw [e.symm_apply_eq, heJ, e.apply_symm_apply]
    obtain ⟨Hm, h1, h2, h3⟩ := PeriodNonempty.exists_herm
      ((D.EF.baseChange ℝ).comp e.symm.toLinearMap e.symm.toLinearMap)
      (fun x y => halt _ _) (fun x y => by simp [hs, hinv])
      (fun x hx => by simpa [hs] using hpos (e.symm x) (by simpa using hx))
    refine ⟨Hm, h1, h2, fun x y => ?_⟩
    rw [h3]
    simp [← hP]

theorem isTypeFn_of_isPeriod {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (h : IsPeriod D ty P) : Tor.IsTypeFn H D.p D.q ty := by
  obtain ⟨J, hJ, hP⟩ := exists_presents h
  exact (isTypeFn_iff D ty).2 (isTypeFn_of_sum D ty fun a => (trace_of_presents hP a).symm.trans (hJ.2.2.2.2 a))

end Period

section Hol

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}


end Hol

section Theta

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {g m : ℕ}

end Theta

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n)

end Family

end GlobalTheory.PeriodCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PeriodsEqFramePeriods
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem periods_eq_frame_periods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : (U.Di i).La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (idx : Fin g ≃ Ψ × Fin r) (Pf : FD.Frame Ψ r → ((U.Di i).La →+ (Fin g → ℂ))), (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → (∀ k, ty k = if ((idx k).2 : ℕ) < (U.Di i).q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1) → FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, (((U.Di i).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → r = (U.Di i).p + (U.Di i).q → (∀ x v k, Pf x v k = if ((idx k).2 : ℕ) < (U.Di i).q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → (∀ x ∈ FD.GG Ψ Gm (U.Di i).q, IsPeriod (U.Di i) ty (Pf x) ∧ U.u i (Pf x) ≫ Xo.s = spMap σ) ∧ ∀ P, IsPeriod (U.Di i) ty P → ∃ x ∈ FD.GG Ψ Gm (U.Di i).q, Pf x = P := by
  intro E _ _ _ H D l Xo σ g ty U i r ξ Gm φ Ψ idx Pf hΨ hty hξ hpos hφ hr hPf
  refine ⟨fun x hx => ?_, fun P hP => ?_⟩
  · have h := ((FramePeriod.isPeriod_frame E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hφ
      hr).2 x hx).2 (Pf x) (hPf x)
    exact ⟨h, U.over_σ i _ h⟩
  · obtain ⟨x, hx, h⟩ := exists_frame_of_isPeriod E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos
      hφ hr P hP
    exact ⟨x, hx, AddMonoidHom.ext fun v => funext fun k => (hPf x v k).trans (h v k).symm⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFrameFrames
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FrameTheta

theorem isOpen_frames {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (p : ℕ) : IsOpen (FD.GG Ψ G p) := by
  have hmat : ∀ τ : Ψ, Continuous fun x : FD.Frame Ψ r => FD.mat x τ := fun τ =>
    show Continuous fun x : FD.Frame Ψ r => (x τ : Matrix (Fin r) (Fin r) ℂ) from continuous_apply τ
  have hgram : ∀ τ : Ψ, Continuous fun x : FD.Frame Ψ r => FD.gram τ.1 G (FD.mat x τ) := by
    intro τ
    refine continuous_matrix fun a b => ?_
    simp only [FD.gram, FD.hermC, FD.col, FD.mat, Matrix.of_apply]
    fun_prop
  have hdmin : ∀ (τ : Ψ) (i : Fin (r + 1)), Continuous fun x : FD.Frame Ψ r => FD.dmin G x τ i := by
    intro τ i
    unfold FD.dmin FD.lminor
    exact ((hgram τ).matrix_submatrix _ _).matrix_det
  unfold FD.GG
  simp only [Set.setOf_forall, Set.setOf_and]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun (hmat τ).matrix_det continuous_const
  · exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (hdmin τ i)))

theorem exists_thetaFrame_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : (U.Di i).La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (idx : Fin g ≃ Ψ × Fin r) (Pf : FD.Frame Ψ r → ((U.Di i).La →+ (Fin g → ℂ))), (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → (∀ k, ty k = if ((idx k).2 : ℕ) < (U.Di i).q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1) → FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, (((U.Di i).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → r = (U.Di i).p + (U.Di i).q → (∀ x v k, Pf x v k = if ((idx k).2 : ℕ) < (U.Di i).q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → IsPreconnected (FD.GG Ψ Gm (U.Di i).q) → ∀ (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.Di i).La), (∀ a b, (U.Di i).EF (bas a) (bas b) = -omegaStd a b) → ∀ (m : ℕ) (ι : (Fin m → ℂ) ≃L[ℂ] FD.Frame Ψ r), ∃ (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ), (∀ b ∈ ι ⁻¹' FD.GG Ψ Gm (U.Di i).q, IsUnit (h b).det ∧ (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef ∧ ∀ k, h b *ᵥ Pf (ι b) (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h b *ᵥ Pf (ι b) (bas (Pi.single (Sum.inr k) 1)) = τ b *ᵥ Pi.single k 1) ∧ (∀ j k, DifferentiableOn ℂ (fun b => h b j k) (ι ⁻¹' FD.GG Ψ Gm (U.Di i).q) ∧ DifferentiableOn ℂ (fun b => τ b j k) (ι ⁻¹' FD.GG Ψ Gm (U.Di i).q)) ∧ (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ IsThetaFrame Xo.univ.t.PP (ι ⁻¹' FD.GG Ψ Gm (U.Di i).q) (fun b => U.u i (Pf (ι b))) (fun b z => (U.ex i (Pf (ι b)) z).left) (fun b z => thetaChar (τ b) c₁ c₂ (h b *ᵥ z)) := by
  classical
  intro E _ _ _ H D l Xo σ g ty U i r ξ Gm φ Ψ idx Pf hΨ hty hξ hpos hφ hr hPf hconn bas hbas m ι
  have hper := (GlobalTheory.FramePeriod.isPeriod_frame E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hφ hr).2
  have hdiff := (GlobalTheory.per_move E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hφ).1 Pf hPf
  obtain ⟨hR1, hR2⟩ := GlobalTheory.RiemannRel.riemann_relations E H (U.Di i) g ty bas hbas
  have hhol : IsHolPeriods (U.Di i) ty (ι ⁻¹' FD.GG Ψ Gm (U.Di i).q) (fun b => Pf (ι b)) :=
    ⟨fun b hb => (hper _ hb).2 _ (hPf _), fun v =>
      (hdiff v).comp ι.differentiable.differentiableOn fun _ hb => hb⟩
  have hopen : IsOpen (ι ⁻¹' FD.GG Ψ Gm (U.Di i).q) := (isOpen_frames Ψ Gm _).preimage ι.continuous
  have hpre : IsPreconnected (ι ⁻¹' FD.GG Ψ Gm (U.Di i).q) :=
    ι.toHomeomorph.isPreconnected_preimage.2 hconn
  have hex : ∀ b : Fin m → ℂ, ∃ h τ : Matrix (Fin g) (Fin g) ℂ, b ∈ ι ⁻¹' FD.GG Ψ Gm (U.Di i).q →
      IsUnit h.det ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ ∀ k,
        h *ᵥ Pf (ι b) (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧
        h *ᵥ Pf (ι b) (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1 := by
    intro b
    by_cases hb : b ∈ ι ⁻¹' FD.GG Ψ Gm (U.Di i).q
    · obtain ⟨h, τ, h1, h2, h3, h4, -⟩ := hR1 _ (hhol.1 b hb)
      exact ⟨h, τ, fun _ => ⟨h2, h3, h4, h1⟩⟩
    · exact ⟨0, 0, fun h => absurd h hb⟩
  choose h τ hhτ using hex
  obtain ⟨c₁, c₂, hc₁, hc₂, hθ⟩ := U.theta i m _ (fun b => Pf (ι b)) bas (-1) h τ hopen hpre hhol
    (fun a b => by rw [hbas]; simp) (fun b hb => ⟨(hhτ b hb).2.2.1, (hhτ b hb).2.2.2⟩)
  exact ⟨h, τ, c₁, c₂, hhτ, hR2 m _ _ h τ hhol fun b hb => (hhτ b hb).2.2.2, hc₁, hc₂, hθ⟩

end GlobalTheory.FrameTheta
end
