module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolyDivDet
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLamObjGoodOfCmObj

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsMetricConjugateFramedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsMetricConjugateFramedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem isLieComb_of_two_pullbacks {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {X : Scheme.{0}}
    {x : Sp R ⟶ X} {x' : Sp S ⟶ X} (hx : x' = spMap f ≫ x) {G : Over X} [GrpObj G] {G₀ : Over (Sp R)} [GrpObj G₀]
    {G' : Over (Sp S)} [GrpObj G'] {φ : G₀.left ⟶ G.left} {φ' : G'.left ⟶ G.left}
    (h : IsGrpPullback G₀ G x φ) (h' : IsGrpPullback G' G x' φ') {n n' : ℕ} (hn : n' = n)
    {c : Fin n → R} {v : Fin n → (epsR R ⟶ G₀)} {w : epsR R ⟶ G₀} (hc : IsLieComb c v w)
    {v' : Fin n' → (epsR S ⟶ G')} {w' : epsR S ⟶ G'}
    (hv : ∀ i, (v' i).left ≫ φ' = spMap (Formalism.L2.Pj.dualMap f) ≫ (v (i.cast hn)).left ≫ φ)
    (hw : w'.left ≫ φ' = spMap (Formalism.L2.Pj.dualMap f) ≫ w.left ≫ φ) :
    IsLieComb (fun i => f (c (i.cast hn))) v' w' := by
  subst hn
  subst hx
  have hw0 : φ' ≫ G.hom = (G'.hom ≫ spMap f) ≫ x := by rw [Category.assoc]; exact h'.1.w
  have hψ1 : h.1.lift φ' (G'.hom ≫ spMap f) hw0 ≫ φ = φ' := h.1.lift_fst _ _ _
  have hψ2 : h.1.lift φ' (G'.hom ≫ spMap f) hw0 ≫ G₀.hom = G'.hom ≫ spMap f := h.1.lift_snd _ _ _
  have hG : IsGrpPullback G' G₀ (spMap f) (h.1.lift φ' (G'.hom ≫ spMap f) hw0) :=
    IsGrpPullback.cancel h (IsGrpPullback.congr h' rfl hψ1.symm) hψ2
  have he : (algebraMap S (DualNumber S)).comp f = (Chart.dualMapR f).comp (algebraMap R (DualNumber R)) := by
    clear h h' hv hw hc hG hψ1 hψ2 hw0
    first
    | exact RingHom.ext fun r => rfl
    | (ext r <;> simp [Chart.dualMapR] <;> rfl)
    | (ext r <;> simp [Chart.dualMapR] <;> erw [TrivSqZeroExt.algebraMap_eq_inl] <;> simp <;> done)
    | (ext r <;> simp [Chart.dualMapR] <;> simp [Algebra.algebraMap_eq_smul_one] <;> done)
    | (ext r
       · simp [Chart.dualMapR]
         show f r = f r
         rfl
       · simp [Chart.dualMapR]
         show (0 : S) = f 0
         simp)
  refine ReciprocityTheory.ChartRestriction.G.Chart.comb_baseChange f hG hc (fun i => ?_) ?_
  · apply h.1.hom_ext
    · rw [Category.assoc, hψ1, hv i, Category.assoc]
      rfl
    · rw [Category.assoc, hψ2, ← Category.assoc, Over.w (v' i), Category.assoc, Over.w (v i)]
      first
      | (show spMap _ ≫ spMap f = spMap _ ≫ spMap _
         rw [← spMap_comp, ← spMap_comp, he])
      | (show spMap _ ≫ spMap f = spMap _ ≫ spMap _
         rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, he])
      | (unfold epsR; simp only [Over.mk_hom, ← spMap_comp, he])
      | (show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
         rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, he])
  · apply h.1.hom_ext
    · rw [Category.assoc, hψ1, hw, Category.assoc]
      rfl
    · rw [Category.assoc, hψ2, ← Category.assoc, Over.w w', Category.assoc, Over.w w]
      first
      | (show spMap _ ≫ spMap f = spMap _ ≫ spMap _
         rw [← spMap_comp, ← spMap_comp, he])
      | (show spMap _ ≫ spMap f = spMap _ ≫ spMap _
         rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, he])
      | (unfold epsR; simp only [Over.mk_hom, ← spMap_comp, he])
      | (show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
         rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, he])

theorem hermForm_map_conj {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm (Hm.map (starRingEnd ℂ)) (fun i => starRingEnd ℂ (z i)) (fun i => starRingEnd ℂ (w i)) =
      starRingEnd ℂ (hermForm Hm z w) := by
  unfold hermForm
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]

theorem isMetricAt_of_dim {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} (x : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x))
    (uu : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (N : ℝ)
    (Gr : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)
    (Φ : FibKey Xo ℂ x) (g : ℕ) (hg : Φ.key.P.g = g) (u : HolUnif Φ.key.P.A Φ.key.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ))
    (w : ∀ b : E →+* ℂ, Fin (Dw.mult b) → (epsR ℂ ⟶ Φ.key.P.A))
    (W : ∀ b : E →+* ℂ, Fin (Dw.mult b) → Fin g → ℂ)
    (h : SecTie Φ.m Φ.th s ∧ u.IsAH Hm χ ∧ u.IsRig Φ.key.rig ∧ u.IsFn Φ.key.th θ ∧
      IsAddFundamentalDomain u.Λ Fd volume ∧
      N = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal ∧
      (∀ b i, (w b i).left ≫ Φ.m.φ = uu b i ∧ u.IsDiff (W b i) (w b i)) ∧
      ∀ b i k, Gr b i k = Real.pi * hermForm Hm (W b k) (W b i)) : IsMetricAt x s uu N Gr := by
  subst hg
  exact ⟨Φ, u, Hm, χ, θ, Fd, w, W, h⟩

theorem isMetricAt_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} (hpq : 1 ≤ Dw.p + Dw.q) (x x' : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x'))
    (uu uu' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (N : ℝ)
    (Gr : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)
    (hx : x' = spMap (starRingEnd ℂ) ≫ x) (hs : SecBC (starRingEnd ℂ) 1 x x' s s') (hgen : SecGen x' s')
    (ht : ∀ τ i, IsTanAt x (uu τ i)) (ht' : ∀ τ i, IsTanAt x' (uu' τ i))
    (hu : ∀ τ i, uu' τ i = spMap (Formalism.L2.Pj.dualMap (starRingEnd ℂ)) ≫ uu τ i)
    (h : IsMetricAt x s uu N Gr) : IsMetricAt x' s' uu' N (fun b => (Gr b).map (starRingEnd ℂ)) := by
  obtain ⟨Φ, u, Hm, χ, θ, Fd, w, W, hT, hAH, hRig, hFn, hFd, hN, hw, hGr⟩ := h
  obtain ⟨Φ0⟩ := GlobalTheory.T.universalTripleFibreKeyData_nonempty_field E H Dw l Xo ℂ x' hpq
  have hNZ : SecNZ x' s' := GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo ℂ x' s' hgen
  obtain ⟨-, hex, huniq⟩ := GlobalTheory.T.rigidifiedSectionCorrespondence_existsUnique_nonvanishing E H Dw l Xo ℂ x' Φ0.T.t Φ0.m
  obtain ⟨th, hth⟩ := hex s'
  have hne := ((huniq th s' hth).2).1 hNZ
  obtain ⟨hg, v', hv', hKey, hvrel⟩ := GlobalTheory.T.universalTripleFibreKeyData_baseChange_keyPullback E H Dw l Xo ℂ ℂ (starRingEnd ℂ) x x' Φ
    { Φ0 with th := th, th_ne := hne } s s' hx hT hth hs
  obtain ⟨u', χ', θ', Fd', hAH', hRig', hFn', hFd', hNeq, hdiff⟩ :=
    GlobalTheory.T.exists_uniformisation_of_complexConjugate_keyDatum Φ.key _ hKey hg _ u Hm χ θ Fd ⟨hAH, hRig, hFn, hFd⟩
  have hpb : ∀ (Ψ : FibKey Xo ℂ x'), IsGrpPullback Ψ.T.t.G Xo.univ.t.G x' Ψ.m.φ := by
    intro Ψ
    exact Ψ.m.cart
  have hpb0 : IsGrpPullback Φ.T.t.G Xo.univ.t.G x Φ.m.φ := Φ.m.cart
  have hcomb : ∀ b i, ∃ cf : Fin Φ.T.g → ℂ, IsLieComb cf Φ.v (w b i) := by
    intro b i
    have hTB := ((GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo ℂ x _ Φ.m.φ hpb0).2 _ Φ.v).1 Φ.basis
    obtain ⟨a, ha, -⟩ := hTB.2 _ (ht b i)
    refine ⟨a, (ReciprocityTheory.ChartRestriction.G.Chart.comb_push hpb0 a Φ.v (w b i)).2 ?_⟩
    rw [← (hw b i).1] at ha
    exact ha
  choose cf hcf using hcomb
  have hw' : ∀ b i, ∃ w' : epsR ℂ ⟶ Φ0.T.t.G, w'.left ≫ Φ0.m.φ = uu' b i :=
    fun b i => (GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo ℂ x' Φ0.T.t.G Φ0.m.φ (hpb Φ0)).1 _ (ht' b i)
  choose w' hw'e using hw'
  refine isMetricAt_of_dim x' s' uu' N _ _ _ hg u' (Hm.map (starRingEnd ℂ)) χ' θ' Fd' w'
    (fun b i k => starRingEnd ℂ (W b i k)) ⟨hth, hAH', hRig', hFn', hFd', ?_, fun b i => ⟨hw'e b i, ?_⟩, fun b i k => ?_⟩
  · rw [hN, hNeq]
  · exact hdiff (cf b i) (w b i) (w' b i) (W b i) (hcf b i)
      (isLieComb_of_two_pullbacks (starRingEnd ℂ) hx hpb0 (hpb _) hg (hcf b i) hvrel
        (by rw [hw'e, hu, (hw b i).1])) (hw b i).2
  · rw [Matrix.map_apply, hGr, map_mul, hermForm_map_conj]
    simp

theorem scal_one_mul_sec {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)) (i : (PPx x).ι) :
    scal x 1 i * s.f i = s.f i := by
  simp only [scal]
  first
  | rw [map_one, one_mul]
  | simp [Out.liftFun]

theorem isMetric_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((starRingEnd ℂ).comp σ))) (N : ℝ) (Gr : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)), 1 ≤ Dw.p + Dw.q → FrMap (FrameNorm.conjAlg σ) y y' → IsMetric y N Gr → IsMetric y' N (fun b => (Gr b).map (starRingEnd ℂ)) := by
  intro E _ _ _ H Dw l Xo c σ y y' N Gr hpq hF hM
  obtain ⟨hx, hu, pm, h1, h2, h3⟩ := hF
  unfold IsMetric at hM ⊢
  refine isMetricAt_conj hpq y.x y'.x y.s y'.s y.u y'.u N Gr hx ?_ y'.gen y.tan y'.tan hu hM
  refine ⟨pm, h1, h2, fun i h => ?_⟩
  have h4 := h3 i h
  first
  | exact (congrArg _ (scal_one_mul_sec (S := ℂ) y.x y.s i)).trans h4
  | exact (congrArg _ (scal_one_mul_sec y.x y.s i)).trans h4
  | (convert h4 using 2; exact scal_one_mul_sec (S := ℂ) y.x y.s i)
  | (convert h4 using 2; simp only [scal]; first | rw [map_one, one_mul] | simp [Out.liftFun])
  | (erw [scal_one_mul_sec]; exact h4)

end GlobalTheory.LamT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsMetricConjugateFramedPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMetric_conjugate_framedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((starRingEnd ℂ).comp σ))) (N : ℝ) (Gr : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)), 1 ≤ Dw.p + Dw.q → FrMap (FrameNorm.conjAlg σ) y y' → IsMetric y N Gr → IsMetric y' N (fun b => (Gr b).map (starRingEnd ℂ)) := by
  first | exact @GlobalTheory.LamT.isMetric_conj | exact GlobalTheory.LamT.isMetric_conj | (intros; apply GlobalTheory.LamT.isMetric_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ClausesIffExistsUnique
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.abelian₂ Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.FD (Data DataX Frame LamBasis fdeg)
open GlobalTheory.SecTransport GlobalTheory.SecTieEx

namespace GlobalTheory.FramedCMPointCompare

section Bundles

variable {X X' Y : Scheme.{0}}

end Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} {c : Coeff l}

section Letters

variable [StarRing (𝓞 E)] {nΨ n' : ℕ}

variable {o : LamObj c nΨ n'}

end Letters

section Data

variable {Dw : Datum H} {Xo : Moduli Dw l}

end Data

variable {D : D7}

theorem fdeg_host (D : D7) : fdeg D.host.E = D.R.f := by
  unfold fdeg
  rw [hostSize_finrank]
  omega

end GlobalTheory.FramedCMPointCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ThetaSectionNormAndHermitianFormIndepUniformisat
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ThetaSectionNormAndHermitianFormIndepUniformisat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.KeyUniq

theorem volume_image {g : ℕ} (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (s : Set (Fin g → ℂ)) :
    (volume (F '' s)).toReal = ‖LinearMap.det F‖ ^ 2 * (volume s).toReal := by
  have h := Measure.addHaar_image_linearMap volume (F.restrictScalars ℝ) s
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, abs_of_nonneg (Complex.normSq_nonneg _),
    Complex.normSq_eq_norm_sq] at h
  rw [show (F '' s) = (F.restrictScalars ℝ) '' s from rfl, h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

theorem volume_fund {g : ℕ} (Λ Λ' : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ']
    (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, F z ∈ Λ' ↔ z ∈ Λ) {s s' : Set (Fin g → ℂ)}
    (hs : IsAddFundamentalDomain Λ s volume) (hs' : IsAddFundamentalDomain Λ' s' volume) :
    (volume s').toReal = ‖LinearMap.det F.toLinearMap‖ ^ 2 * (volume s).toReal := by
  let φ : Λ' ≃ Λ :=
    { toFun := fun b => ⟨F.symm b, (hF _).1 (by rw [F.apply_symm_apply]; exact b.2)⟩
      invFun := fun a => ⟨F a, (hF a).2 a.2⟩
      left_inv := fun b => Subtype.ext (F.apply_symm_apply b.1)
      right_inv := fun a => Subtype.ext (F.symm_apply_apply a.1) }
  have hq : Measure.QuasiMeasurePreserving F.toEquiv.symm volume volume :=
    Measure.LinearMap.quasiMeasurePreserving volume (F.symm.restrictScalars ℝ).toLinearMap
      (F.symm.restrictScalars ℝ).isUnit_det'.ne_zero
  have h1 : IsAddFundamentalDomain Λ' (F.toEquiv '' s) volume :=
    hs.image_of_equiv F.toEquiv hq φ fun b z => by
      change F (F.symm b + z) = b + F z
      rw [map_add (f := _), F.apply_symm_apply]
  have : Countable Λ' := countable_of_Lindelof_of_discrete
  have : MeasurableConstVAdd Λ' (Fin g → ℂ) := ⟨fun c => measurable_const_add (c : Fin g → ℂ)⟩
  have : VAddInvariantMeasure Λ' (Fin g → ℂ) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : Fin g → ℂ) s⟩
  rw [hs'.measure_eq h1]
  exact volume_image F.toLinearMap s

theorem norm_eq_and_hermForm_eq : ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)) (u' : HolUnif x.P.A x.P.L x.P.g) (Hm' : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ' : u'.Λ → ℂ) (θ' : (Fin x.P.g → ℂ) → ℂ) (Fd' : Set (Fin x.P.g → ℂ)), u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume → u'.IsAH Hm' χ' ∧ u'.IsRig x.rig ∧ u'.IsFn x.th θ' ∧ IsAddFundamentalDomain u'.Λ Fd' volume → (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal = (∫ z in Fd', ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re)) / (volume Fd').toReal ∧ ∀ (v w : epsR ℂ ⟶ x.P.A) (V W V' W' : Fin x.P.g → ℂ), IsTangent v → IsTangent w → u.IsDiff V v → u.IsDiff W w → u'.IsDiff V' v → u'.IsDiff W' w → hermForm Hm V W = hermForm Hm' V' W' := by
  rintro x u Hm χ θ Fd u' Hm' χ' θ' Fd' ⟨hA, hR, hθ, hD⟩ ⟨hA', hR', hθ', hD'⟩
  obtain ⟨-, t1, -⟩ := unimodular_and_tangent_of_isAH thetaUnifAV_all x.P x.rig x.rig_gen u Hm χ hA
  obtain ⟨-, t1', t2'⟩ := unimodular_and_tangent_of_isAH thetaUnifAV_all x.P x.rig x.rig_gen u' Hm' χ' hA'
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo x.P.A x.P.isAb x.P.L x.P.g x.P.g u' t1' t2' u.ex u.ex_add
    (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  let e : (Fin x.P.g → ℂ) ≃ₗ[ℂ] (Fin x.P.g → ℂ) := LinearEquiv.ofInjectiveEndo F (UnifCompare.injective u u' F hF)
  have hd : ∀ w v, u.IsDiff w v ↔ u'.IsDiff (F w) v :=
    UnifCompare.isDiff_iff u u' e.toContinuousLinearEquiv hF
  refine ⟨?_, fun v w V W V' W' hv hw h1 h2 h3 h4 => ?_⟩
  · obtain ⟨N, hN, κ, -, -, -, -, hK⟩ := keyFormulaPow_and_keyDegree.1
    choose W hW using fun i => (t1 _ (x.basis.1 i)).exists
    have k := hK x u Hm (Matrix.of W) χ θ Fd _ _ hA hR hθ hW hD rfl rfl
    have k' := hK x u' Hm' (Matrix.of fun i => F (W i)) χ' θ' Fd' _ _ hA' hR' hθ' (fun i => (hd _ _).1 (hW i)) hD' rfl rfl
    have := u'.discrete
    have hvol : (volume Fd').toReal = ‖LinearMap.det F‖ ^ 2 * (volume Fd).toReal :=
      volume_fund u.Λ u'.Λ e (UnifCompare.mem_iff u u' F hF) hD hD'
    have hdet : (Matrix.of fun i => F (W i)).det = LinearMap.det F * (Matrix.of W).det := by
      have : (Matrix.of fun i => F (W i)) = Matrix.of W * (LinearMap.toMatrix' F).transpose := by
        ext i j
        rw [Matrix.of_apply, ← LinearMap.toMatrix'_mulVec, Matrix.mul_apply, Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _
      rw [this, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix', _root_.mul_comm]
    have h0 : ‖LinearMap.det F‖ ≠ 0 := norm_ne_zero_iff.2 e.isUnit_det'.ne_zero
    have hη : (volume Fd').toReal / (Real.pi ^ x.P.g * ‖(Matrix.of fun i => F (W i)).det‖ ^ 2) =
        (volume Fd).toReal / (Real.pi ^ x.P.g * ‖(Matrix.of W).det‖ ^ 2) := by
      rw [hvol, hdet, norm_mul, mul_pow, mul_left_comm, mul_div_mul_left _ _ (pow_ne_zero 2 h0)]
    rw [hη] at k'
    have hne := k.trans_ne (pow_ne_zero _ Real.two_pi_pos.ne')
    have h1 := mul_left_cancel₀ (left_ne_zero_of_mul (left_ne_zero_of_mul hne))
      (mul_right_cancel₀ (right_ne_zero_of_mul hne) (k.trans k'.symm))
    exact (pow_left_inj₀ (div_nonneg (integral_nonneg fun z => by positivity) ENNReal.toReal_nonneg)
      (div_nonneg (integral_nonneg fun z => by positivity) ENNReal.toReal_nonneg)
      (by have := hN x.P.g; omega)).1 h1
  · rw [(t1' v hv).unique h3 ((hd _ _).1 h1), (t1' w hw).unique h4 ((hd _ _).1 h2)]
    exact (UnifCompare.hermForm_eq x.P.isLB u u' hA hA' F hF V W).symm

end GlobalTheory.KeyUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ThetaSectionNormAndHermitianFormIndepUniformisatStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSection_norm_and_hermitianForm_indep_uniformisation : ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)) (u' : HolUnif x.P.A x.P.L x.P.g) (Hm' : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ' : u'.Λ → ℂ) (θ' : (Fin x.P.g → ℂ) → ℂ) (Fd' : Set (Fin x.P.g → ℂ)), u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume → u'.IsAH Hm' χ' ∧ u'.IsRig x.rig ∧ u'.IsFn x.th θ' ∧ IsAddFundamentalDomain u'.Λ Fd' volume → (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal = (∫ z in Fd', ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re)) / (volume Fd').toReal ∧ ∀ (v w : epsR ℂ ⟶ x.P.A) (V W V' W' : Fin x.P.g → ℂ), IsTangent v → IsTangent w → u.IsDiff V v → u.IsDiff W w → u'.IsDiff V' v → u'.IsDiff W' w → hermForm Hm V W = hermForm Hm' V' W' := by
  first | exact @GlobalTheory.KeyUniq.norm_eq_and_hermForm_eq | exact GlobalTheory.KeyUniq.norm_eq_and_hermForm_eq | (intros; apply GlobalTheory.KeyUniq.norm_eq_and_hermForm_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationEqOfIsLocGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.KeyVal

theorem exists_unit_of_pow {R K' : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K'] [Algebra R K']
    [IsFractionRing R K'] {z : K'} {m : ℕ} (hm : 0 < m) (w : Rˣ) (h : z ^ m = algebraMap R K' w) :
    ∃ u : Rˣ, z = algebraMap R K' u := by
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) (K := K') (x := z) hm
    (by rw [h]; exact isIntegral_algebraMap)
  have h1 : r ^ m = w := IsFractionRing.injective R K' (by rw [map_pow, hr, h])
  have h2 : IsUnit r := (isUnit_pow_iff hm.ne').1 (h1 ▸ w.isUnit)
  exact ⟨h2.unit, by simp [hr]⟩

theorem unit_iff {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) {R K' : Type} [CommRing R]
    [Field K'] [Algebra R K'] (hi : Function.Injective (algebraMap R K')) (f : K →+* K')
    (hv : ∀ y : K, f y ∈ Set.range (algebraMap R K') ↔ p.valuation K y ≤ 1) (y : K) :
    (∃ u : Rˣ, f y = algebraMap R K' u) ↔ p.valuation K y = 1 := by
  constructor
  · rintro ⟨u, hu⟩
    have hy : y ≠ 0 := by
      rintro rfl
      exact (u.isUnit.map (algebraMap R K')).ne_zero (by rw [← hu, map_zero])
    refine eq_one_of_one_le_mul_left ((hv y).1 ⟨_, hu.symm⟩)
      ((hv y⁻¹).1 ⟨(u⁻¹ : Rˣ), by rw [map_units_inv, map_inv₀, hu]⟩) ?_
    rw [← map_mul, mul_inv_cancel₀ hy, map_one]
  · intro h
    have hy : y ≠ 0 := by
      rintro rfl
      simp at h
    obtain ⟨r, hr⟩ := (hv y).2 h.le
    obtain ⟨s, hs⟩ := (hv y⁻¹).2 (by rw [map_inv₀, h, inv_one])
    have e : r * s = 1 := hi (by rw [map_mul, hr, hs, ← map_mul, mul_inv_cancel₀ hy, map_one, map_one])
    exact ⟨Units.mkOfMulEqOne r s e, by simp [hr]⟩

theorem valuation_eq_of_isLocGen {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)} {c c' : K}
    {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (h : IsLocGen p c I) (h' : IsLocGen p c' I) :
    p.valuation K c = p.valuation K c' := by
  rw [valuation_eq_exp_count p h.1, valuation_eq_exp_count p h'.1, h.2, h'.2]

theorem exists_pow_rel (K : Type) [Field K] [NumberField K] (x : KeyIn K) :
    ∃ (n : ℕ) (k : K), 1 ≤ n ∧ k ≠ 0 ∧ ∀ (R K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K']
      [Algebra R K'] [IsFractionRing R K'] (f : K →+* K') (x' : KeyIn K') (a d : K'), KeyPB x' x f →
      KeyIntegral R x' a d → ∃ u : Rˣ, a ^ (8 * n) * algebraMap R K' u = d ^ (4 * n) * f k := by
  obtain ⟨N, hN, κ, hH, hF, hU, -⟩ := GlobalTheory.keyFormulaPow_and_keyDegree.1
  refine ⟨N x.P.g, κ K x, hN _, (κ K x).ne_zero, ?_⟩
  intro R K' _ _ _ _ _ _ f x' a d hPB hInt
  haveI : CharZero K' := (RingHom.charZero_iff f.injective).1 inferInstance
  obtain ⟨th', hth', v', hv', M, xR, hth'eq, hv'eq, hMdet, hPBR⟩ := hInt
  have hFx := hF K K' f x x' hPB
  have hHx := hH K' x'.P x'.g_pos x'.rig x'.rig_gen x'.th x'.th_ne x'.v x'.basis th' hth' v' hv' a M hth'eq hv'eq
  obtain ⟨u, hu, -⟩ := hU R K' xR _ hPBR
  have hg : x'.P.g = x.P.g := by obtain ⟨-, -, -, hg, -⟩ := hPB; exact hg
  refine ⟨u, ?_⟩
  rw [← hu, ← hFx, ← hMdet, ← hg]
  exact hHx

theorem integral_section_unit : ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (Tl abelian₂ : MLine K) (p : HeightOneSpectrum (𝓞 K)), KeyLocAt x Tl abelian₂ p → ∀ (R K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K'] [Algebra R K'] [IsFractionRing R K'] (f : K →+* K') (x' : KeyIn K') (a d : K') (ca cd : K) (ud : Rˣ), (∀ y : K, f y ∈ Set.range (algebraMap R K') ↔ p.valuation K y ≤ 1) → KeyPB x' x f → KeyIntegral R x' a d → IsLocGen p cd abelian₂.I → d = f cd * algebraMap R K' ud → IsLocGen p ca Tl.I → ∃ u : Rˣ, a = f ca * algebraMap R K' u := by
  intro K _ _ x Tl abelian₂ p hloc R K' _ _ _ _ _ _ f x' a d ca cd ud hval hPB hInt hcd hd hca
  obtain ⟨n, k, hn, hk, H⟩ := exists_pow_rel K x
  obtain ⟨K₁, _, _, R₁, _, _, _, _, _, f₁, x₁, a₁, d₁, ca₁, cd₁, ua₁, ud₁, hPB₁, hInt₁, hval₁, ha₁, hd₁, hca₁, hcd₁⟩ := hloc
  obtain ⟨u₁, hu₁⟩ := H R₁ K₁ f₁ x₁ a₁ d₁ hPB₁ hInt₁
  obtain ⟨u, hu⟩ := H R K' f x' a d hPB hInt
  have h1 : p.valuation K (cd₁ ^ (4 * n) * k / ca₁ ^ (8 * n)) = 1 := by
    refine (unit_iff p (IsFractionRing.injective R₁ K₁) f₁ hval₁ _).1 ⟨ua₁ ^ (8 * n) * u₁ * ud₁⁻¹ ^ (4 * n), ?_⟩
    have hfa : f₁ ca₁ ≠ 0 := (map_ne_zero f₁).2 hca₁.1
    have hD : algebraMap R₁ K₁ (ud₁ : R₁) ≠ 0 := (ud₁.isUnit.map (algebraMap R₁ K₁)).ne_zero
    rw [ha₁, hd₁, mul_pow, mul_pow] at hu₁
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_mul, map_mul,
      map_pow, map_pow, map_units_inv, map_div₀, map_mul, map_pow, map_pow, inv_pow, ← div_eq_mul_inv,
      div_eq_div_iff (pow_ne_zero _ hfa) (pow_ne_zero _ hD)]
    linear_combination -hu₁
  have h2 : p.valuation K (cd ^ (4 * n) * k / ca ^ (8 * n)) = 1 := by
    rw [map_div₀, map_mul, map_pow, map_pow] at h1 ⊢
    rw [valuation_eq_of_isLocGen hca hca₁, valuation_eq_of_isLocGen hcd hcd₁, h1]
  obtain ⟨w, hw⟩ := (unit_iff p (IsFractionRing.injective R K') f hval _).2 h2
  have hfa : f ca ≠ 0 := (map_ne_zero f).2 hca.1
  have hU : algebraMap R K' (u : R) ≠ 0 := (u.isUnit.map (algebraMap R K')).ne_zero
  obtain ⟨t, ht⟩ := exists_unit_of_pow (R := R) (z := a / f ca) (m := 8 * n) (by omega) (w * ud ^ (4 * n) * u⁻¹) (by
    rw [hd, mul_pow] at hu
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_mul,
      map_pow, map_units_inv, ← hw, map_div₀, map_mul, map_pow, map_pow, div_pow, ← div_eq_mul_inv,
      eq_div_iff hU, div_mul_eq_mul_div, div_mul_eq_mul_div, hu]
    ring)
  exact ⟨t, by rw [← ht, mul_div_cancel₀ _ hfa]⟩

end GlobalTheory.KeyVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodCmPointOfIntegralCmObject
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFramedPointOfLieEigenbasis
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFramedPointOfLieEigenbasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem exists_frPt_of_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (x : Sp K ⟶ Xo.X) (Φ : FibKey Xo K x) (e : (Σ b : E →+* ℂ, Fin (Dw.mult b)) ≃ Fin Φ.T.g) (U : Matrix (Fin Φ.T.g) (Fin Φ.T.g) K) (w : Fin Φ.T.g → (epsR K ⟶ Φ.T.t.G)), x ≫ Xo.s = sOf c K → U.det ≠ 0 → (∀ k, IsLieComb (U k) Φ.v (w k)) → (∀ τ i, IsEigAt c τ ((w (e ⟨τ, i⟩)).left ≫ Φ.m.φ)) → ∃ y : FrPt Xo c K, y.x = x ∧ SecTie Φ.m Φ.th y.s ∧ ∀ τ i, y.u τ i = (w (e ⟨τ, i⟩)).left ≫ Φ.m.φ := by
  intro E _ _ _ H Dw l Xo c K _ _ x Φ e U w hx hU hw heig
  have hb : IsLieBasis w :=
    ((GlobalTheory.LieComb.lieComb_algebra K Φ.T.t.G Φ.T.g Φ.v Φ.basis.1).2.2.2.2 U w Φ.basis hw).2 hU.isUnit
  have ht : TanBasis x (fun i => (w i).left ≫ Φ.m.φ) :=
    ((GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo K x Φ.T.t.G Φ.m.φ Φ.m.cart).2 _ w).1 hb
  have htan : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), IsTanAt x ((w (e ⟨τ, i⟩)).left ≫ Φ.m.φ) :=
    fun τ i => ht.1 (e ⟨τ, i⟩)
  have hbas := (GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c K x
    (fun τ i => (w (e ⟨τ, i⟩)).left ≫ Φ.m.φ) Φ.T.g e.symm htan heig).2 (by
      have : (fun j => (w (e ⟨(e.symm j).1, (e.symm j).2⟩)).left ≫ Φ.m.φ) = fun i => (w i).left ≫ Φ.m.φ :=
        funext fun j => congrArg (fun k => (w k).left ≫ Φ.m.φ) (e.apply_symm_apply j)
      exact this ▸ ht)
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.rigidifiedSectionCorrespondence_existsUnique_nonvanishing E H Dw l Xo K x Φ.T.t Φ.m
  obtain ⟨s, hs⟩ := h1 Φ.th
  have hgen : SecGen x s := GlobalTheory.Frames.secGen_of_secNZ GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo K x s
    ((h3 Φ.th s hs).2.2 Φ.th_ne)
  exact ⟨⟨x, hx, fun τ i => (w (e ⟨τ, i⟩)).left ≫ Φ.m.φ, htan, heig, hbas, s, hgen⟩, rfl, hs, fun _ _ => rfl⟩

end GlobalTheory.LamT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFramedPointOfLieEigenbasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framedPoint_of_lie_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (x : Sp K ⟶ Xo.X) (Φ : FibKey Xo K x) (e : (Σ b : E →+* ℂ, Fin (Dw.mult b)) ≃ Fin Φ.T.g) (U : Matrix (Fin Φ.T.g) (Fin Φ.T.g) K) (w : Fin Φ.T.g → (epsR K ⟶ Φ.T.t.G)), x ≫ Xo.s = sOf c K → U.det ≠ 0 → (∀ k, IsLieComb (U k) Φ.v (w k)) → (∀ τ i, IsEigAt c τ ((w (e ⟨τ, i⟩)).left ≫ Φ.m.φ)) → ∃ y : FrPt Xo c K, y.x = x ∧ SecTie Φ.m Φ.th y.s ∧ ∀ τ i, y.u τ i = (w (e ⟨τ, i⟩)).left ≫ Φ.m.φ := by
  first | exact @GlobalTheory.LamT.exists_frPt_of_eigenbasis | exact GlobalTheory.LamT.exists_frPt_of_eigenbasis | (intros; apply GlobalTheory.LamT.exists_frPt_of_eigenbasis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsEigenvectorAtOfModel
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsEigenvectorAtOfModel
set_option autoImplicit false

namespace GlobalTheory.LamT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

theorem isEigAt_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (x : Sp K ⟶ Xo.X) (t₀ : SAB H (Sp K)) (B : SAB H (Sp (𝓞 K))) (m : SABMap t₀ Xo.univ.t x) (m' : SABMap t₀ B (spMap (algebraMap (𝓞 K) K))) (τ : E →+* ℂ) (w : epsR K ⟶ t₀.G), (∀ a : 𝓞 E, ∃ w' : epsR K ⟶ t₀.G, IsLieComb ![LamF.labK c K τ (a : E)] ![w] w' ∧ w.left ≫ m'.φ ≫ (B.act.act a).left = w'.left ≫ m'.φ) → IsEigAt c τ (w.left ≫ m.φ) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ x t₀ B m m' τ w h a
  obtain ⟨w', ⟨u, hu, hw'⟩, e⟩ := h a
  have h1 : w'.left = spMap (epsScaleR (LamF.labK c K τ (a : E))) ≫ w.left := by
    rw [hw']
    simpa using hu 0
  have h2 : w.left ≫ (t₀.act.act a).left = w'.left := by
    apply m'.cart.1.hom_ext
    · rw [Category.assoc, m'.act a]
      exact e
    · rw [Category.assoc, Over.w (t₀.act.act a), Over.w w, Over.w w']
  rw [Category.assoc, ← m.act a, ← Category.assoc, h2, h1, Category.assoc]
  rfl

end GlobalTheory.LamT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsEigenvectorAtOfModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEigenvectorAt_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (x : Sp K ⟶ Xo.X) (t₀ : SAB H (Sp K)) (B : SAB H (Sp (𝓞 K))) (m : SABMap t₀ Xo.univ.t x) (m' : SABMap t₀ B (spMap (algebraMap (𝓞 K) K))) (τ : E →+* ℂ) (w : epsR K ⟶ t₀.G), (∀ a : 𝓞 E, ∃ w' : epsR K ⟶ t₀.G, IsLieComb ![LamF.labK c K τ (a : E)] ![w] w' ∧ w.left ≫ m'.φ ≫ (B.act.act a).left = w'.left ≫ m'.φ) → IsEigAt c τ (w.left ≫ m.φ) := by
  first | exact @GlobalTheory.LamT.isEigAt_of_model | exact GlobalTheory.LamT.isEigAt_of_model | (intros; apply GlobalTheory.LamT.isEigAt_of_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodCmPointOfIntegralCmObject
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT


set_option maxHeartbeats 1000000 in
theorem exists_cmPt_good_of_cmObj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (ρ : 𝓞 K) (σ : K →+* ℂ) (X : CMObj H K ρ σ Dw.p Dw.q) (La : ℝ) (x : Sp K ⟶ Xo.X) (Φ : FibKey Xo K x) (_ : SABMap Φ.T.t X.B.t (spMap (algebraMap (𝓞 K) K))), (∀ τ, τ ∈ LamF.psiSet H ↔ LamF.labK c K τ (H.rt : E) = (ρ : K)) → (∀ j (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ La ^ 2) → x ≫ Xo.s = sOf c K → ∀ (S : Type) [CommRing S] [Algebra c.F S] (σ₁ : K →ₐ[c.F] S), ∃ (z : CMPt Xo c) (σ' : z.K →ₐ[c.F] S), z.Good (Module.finrank ℚ E / 2) La ∧ spMap σ'.toRingHom ≫ z.y.x = spMap σ₁.toRingHom ≫ x := by
  intro E _ _ _ H Dw l Xo c _ hstar K _ _ _ ρ σ X La x Φ m' hρ hLa hx S _ _ σ₁
  have hfib : LamF.IsFibreOf X.B.pol Φ.key (LamF.gmap K) m'.φ :=
    (LamF.isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) X.B.pol Φ.key m'.φ).2
      ((GlobalTheory.T.principalTriple_pullback E H (𝓞 K) K (algebraMap (𝓞 K) K) X.B).2 Φ.T m' inferInstance).2.1
  obtain ⟨oa, oaΨ, oa', xΨ, x', φΨ, φ', τΨ, τ', ℓΨ, ℓ', Tl, LamL, hoa, -, -, hgood⟩ :=
    LamF.exists_lamObjGood_of_cmObj GlobalTheory.firstFiveLaws.2.1.secTwist GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1
      GlobalTheory.homExtension_semiAbelian_dvr_unconditional E H l c hstar K ρ σ Dw.p Dw.q X La hρ hLa Φ.key m'.φ hfib
  obtain ⟨L, hL, hm⟩ := LamF.exists_lamLetters_isGood E H l c _ _ _ _ La hgood
  have hdet := LamF.Ind.lamInd E H l c hstar _ _ _ _ La hgood L hL
  have heig := LamF.LetterEigen.letter_eigen E H l c _ _ _ _ La hgood L hL
  obtain ⟨mm, e, src, U, ℓ⟩ := L
  have hmm : mm = Dw.mult := by
    funext b
    unfold Datum.mult
    split_ifs with h
    · exact (hm b).1 h
    · exact (hm b).2 h
  subst hmm
  choose w hw hU using hL.2.2.1
  obtain ⟨y, hy, htie, hu⟩ := GlobalTheory.T.exists_framedPoint_of_lie_eigenbasis E H Dw l Xo c K x Φ e U w hx hdet hU (fun τ i =>
    GlobalTheory.T.isEigenvectorAt_of_model E H Dw l Xo c K x Φ.T.t X.B.t Φ.m m' τ (w (e ⟨τ, i⟩)) (fun a => by
      have h := heig τ i (w (e ⟨τ, i⟩)) (hw _) a
      rw [← hoa]
      exact h))
  refine ⟨CMPt.mk K x Φ X.B m' oa (X.A true).pol oaΨ (X.A false).pol oa' (fun i => X.φ (Sum.inl i))
    (fun i => X.φ (Sum.inr i)) (fun i => X.hh (Sum.inl i)) (fun i => X.hh (Sum.inr i)) xΨ x' φΨ φ' τΨ τ' ℓΨ ℓ' Tl LamL
    e src U ℓ y, σ₁, ⟨hgood, hL, hoa, hy, htie, fun τ i => ⟨w (e ⟨τ, i⟩), hw _, hu τ i⟩⟩, ?_⟩
  exact congrArg (fun t => spMap σ₁.toRingHom ≫ t) hy

end GlobalTheory.LamT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodCmPointOfIntegralCmObjectStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_cm_point_of_integral_cm_object : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (ρ : 𝓞 K) (σ : K →+* ℂ) (X : CMObj H K ρ σ Dw.p Dw.q) (La : ℝ) (x : Sp K ⟶ Xo.X) (Φ : FibKey Xo K x) (_ : SABMap Φ.T.t X.B.t (spMap (algebraMap (𝓞 K) K))), (∀ τ, τ ∈ LamF.psiSet H ↔ LamF.labK c K τ (H.rt : E) = (ρ : K)) → (∀ j (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ La ^ 2) → x ≫ Xo.s = sOf c K → ∀ (S : Type) [CommRing S] [Algebra c.F S] (σ₁ : K →ₐ[c.F] S), ∃ (z : CMPt Xo c) (σ' : z.K →ₐ[c.F] S), z.Good (Module.finrank ℚ E / 2) La ∧ spMap σ'.toRingHom ≫ z.y.x = spMap σ₁.toRingHom ≫ x := by
  first | exact @GlobalTheory.LamT.exists_cmPt_good_of_cmObj | exact GlobalTheory.LamT.exists_cmPt_good_of_cmObj | (intros; apply GlobalTheory.LamT.exists_cmPt_good_of_cmObj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsFramePolynomialOfRuleNumberField
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EvalFrEqProdDetPowMul
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DetDvdEquivariantFramePolynomialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_dvd_equivariant_framePolynomial : ∀ (K : Type) [Field K] [Infinite K] (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ), (∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) K), (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id → evalFr P (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i)) * evalFr P X) → ∀ b : B, (∀ i, 1 ≤ a b i) → ∃ Q : MvPolynomial (FrVar m) K, P = (Matrix.of fun i k : Fin (m b) => (MvPolynomial.X ⟨b, (k, i)⟩ : MvPolynomial (FrVar m) K)).det * Q := by
  first | exact @GlobalTheory.FrameDet.det_dvd_of_equivariant | exact GlobalTheory.FrameDet.det_dvd_of_equivariant | (intros; apply GlobalTheory.FrameDet.det_dvd_of_equivariant <;> assumption)
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

noncomputable def blockDetPoly (K : Type) [CommRing K] {B : Type} (m : B → ℕ) (b : B) :
    MvPolynomial (FrVar m) K :=
  (Matrix.of fun i k : Fin (m b) => (MvPolynomial.X ⟨b, (k, i)⟩ : MvPolynomial (FrVar m) K)).det

theorem evalFr_map_blockDetPoly {K S : Type} [CommRing K] [CommRing S] (φ : K →+* S) {B : Type}
    [Fintype B] (m : B → ℕ) (b : B) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) S) :
    evalFr (MvPolynomial.map φ (blockDetPoly K m b)) X = (X b).det := by
  unfold evalFr blockDetPoly
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i k
  simp

theorem evalFr_blockDetPoly {K : Type} [CommRing K] {B : Type}
    [Fintype B] (m : B → ℕ) (b : B) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) :
    evalFr (blockDetPoly K m b) X = (X b).det := by
  have := evalFr_map_blockDetPoly (RingHom.id K) m b X
  rwa [MvPolynomial.map_id] at this

theorem exists_eq_prod_blockDetPoly_pow_mul (K : Type) [Field K] [Infinite K] (B : Type) [Fintype B]
    [DecidableEq B] (m : B → ℕ) (a : ∀ b, Fin (m b) → ℕ) (s : ℕ) :
    ∀ (n : B → ℕ), ∑ b, n b = s → ∀ (P : MvPolynomial (FrVar m) K),
      (∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) K),
        (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id →
        evalFr P (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i + n b)) * evalFr P X) →
      ∃ G : MvPolynomial (FrVar m) K, P = (∏ b, blockDetPoly K m b ^ n b) * G := by
  induction s with
  | zero =>
    intro n hn P _
    have h0 : ∀ b, n b = 0 := fun b =>
      (Finset.sum_eq_zero_iff.1 hn) b (Finset.mem_univ b)
    exact ⟨P, by simp [h0]⟩
  | succ s ih =>
    intro n hn P hP
    obtain ⟨b₀, -, hb₀⟩ : ∃ b ∈ (Finset.univ : Finset B), n b ≠ 0 :=
      Finset.exists_ne_zero_of_sum_ne_zero (by omega)
    obtain ⟨Q, hQ⟩ := GlobalTheory.T.det_dvd_equivariant_framePolynomial K B m P (fun b i => a b i + n b) hP b₀ (fun i => by omega)
    change P = blockDetPoly K m b₀ * Q at hQ
    set n' : B → ℕ := Function.update n b₀ (n b₀ - 1) with hn'
    have hn'0 : n' b₀ + 1 = n b₀ := by simp only [hn', Function.update_self]; omega
    have hn'1 : ∀ b, b ≠ b₀ → n' b = n b := fun b hb => by
      simp only [hn', Function.update_of_ne hb]
    have hsum : ∑ b, n' b = s := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b₀)] at hn ⊢
      have : ∑ b ∈ Finset.univ.erase b₀, n' b = ∑ b ∈ Finset.univ.erase b₀, n b :=
        Finset.sum_congr rfl fun b hb => hn'1 b (Finset.ne_of_mem_erase hb)
      omega
    have hev : ∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K,
        evalFr P X = (X b₀).det * evalFr Q X := fun X => by
      rw [← evalFr_blockDetPoly m b₀ X, hQ]
      simp only [evalFr, map_mul]
    obtain ⟨G, hG⟩ := ih n' hsum Q (by
      intro X b t hX ht htri
      have h := hP X b t hX ht htri
      rw [hev, hev] at h
      by_cases hb : b = b₀
      · subst hb
        rw [Function.update_self, Matrix.det_mul] at h
        have hd : t.det = ∏ i, t i i := Matrix.det_of_upperTriangular htri
        have hp : (∏ i, t i i ^ (a b i + n b)) = t.det * ∏ i, t i i ^ (a b i + n' b) := by
          rw [hd, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [← hn'0]; ring
        rw [hp] at h
        apply mul_left_cancel₀ (mul_ne_zero (hX b) ht)
        rw [h]; ring
      · rw [Function.update_of_ne (Ne.symm hb)] at h
        rw [hn'1 b hb]
        apply mul_left_cancel₀ (hX b₀)
        rw [h]; ring)
    refine ⟨G, ?_⟩
    rw [hQ, hG, ← Finset.mul_prod_erase _ _ (Finset.mem_univ b₀),
      ← Finset.mul_prod_erase _ (fun b => blockDetPoly K m b ^ n b) (Finset.mem_univ b₀)]
    have : ∏ b ∈ Finset.univ.erase b₀, blockDetPoly K m b ^ n' b
        = ∏ b ∈ Finset.univ.erase b₀, blockDetPoly K m b ^ n b :=
      Finset.prod_congr rfl fun b hb => by rw [hn'1 b (Finset.ne_of_mem_erase hb)]
    rw [this, ← hn'0]; ring

theorem evalFr_eq_prod_det_pow_mul : ∀ (K : Type) [Field K] [Infinite K] (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ) (N : ℕ), (∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) K), (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id → evalFr P (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i + N)) * evalFr P X) → ∃ G : MvPolynomial (FrVar m) K, ∀ (S : Type) [CommRing S] (φ : K →+* S) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) S), evalFr (MvPolynomial.map φ P) X = (∏ b, (X b).det) ^ N * evalFr (MvPolynomial.map φ G) X := by
  intro K _ _ B _ _ m P a N hP
  obtain ⟨G, hG⟩ := exists_eq_prod_blockDetPoly_pow_mul K B m a _ (fun _ => N) rfl P hP
  refine ⟨G, fun S _ φ X => ?_⟩
  rw [hG, ← Finset.prod_pow]
  simp only [← evalFr_map_blockDetPoly φ m _ X]
  simp only [evalFr, map_mul, map_prod, map_pow]

end GlobalTheory.LamT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsFramePolynomialOfRuleNumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem evR_frChg_mul_triangular (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (F : Rul Xo c) (hF : F ∈ sec Xo c a n) (z z' : FrPt Xo c K)
    (T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K) (hT : ∀ b, (T b).BlockTriangular id)
    (hd : ∀ b, (T b).det ≠ 0) (h : FrChg (fun b => (T b).transpose) 1 z z') :
    evR Xo c F z' = (∏ b, ∏ i, T b i i ^ a (b, i)) * evR Xo c F z := by
  have hne : ∀ b i, T b i i ≠ 0 := by
    intro b i
    have h1 := hd b
    rw [Matrix.det_of_isUpperTriangular (hT b)] at h1
    exact (Finset.prod_ne_zero_iff.1 h1) i (Finset.mem_univ i)
  let t : Formalism.L2.Pj.Ix Dw → Kˣ := fun o => match o with
    | none => 1
    | some x => Units.mk0 (T x.1 x.2 x.2) (hne x.1 x.2)
  have hb : FrBor t z z' := by
    refine ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K z z' z').1 t).2
      ⟨fun b => (T b).transpose, fun τ i j hij => ?_, fun τ i => rfl, h⟩
    exact hT τ hij
  have hw := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 K inferInstance a n F hF
    t z z' hb
  rw [hw]
  congr 1
  simp only [wchar, Fintype.prod_option, Fintype.prod_sigma, t, Formalism.L2.Pj.ex, Units.val_one, one_pow, _root_.one_mul,
    Units.val_mk0]

theorem exists_isFrPoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, ∃ G : MvPolynomial (FrVar Dw.mult) K, IsFrPoly F y G := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ _ y a n F hF
  obtain ⟨P, N, hP⟩ := GlobalTheory.LamT.RatFn.exists_poly_div_det E H Dw l Xo c K y a n F hF
  have hrefl : FrMap (AlgHom.id c.F K) y y := GlobalTheory.Frames.frMapUniq_refl y
  have hPK : ∀ (z' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y z' →
      (∏ b, (Y b).det) ^ N * evR Xo c F z' = evalFr P Y := by
    intro z' Y hY h
    have h1 := hP K (AlgHom.id c.F K) y z' Y (fun b => (hY b).isUnit) hrefl h
    have h2 : MvPolynomial.map (AlgHom.id c.F K).toRingHom P = P := MvPolynomial.map_id P
    rwa [h2] at h1
  obtain ⟨G, hG⟩ := GlobalTheory.LamT.evalFr_eq_prod_det_pow_mul K (E →+* ℂ) Dw.mult P (fun b i => a (b, i)) N (by
    intro X b t hX ht htri
    let T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := Function.update (fun _ => 1) b t
    have hTb : T b = t := Function.update_self ..
    have hTo : ∀ b', b' ≠ b → T b' = 1 := fun b' h => Function.update_of_ne h ..
    have hTtri : ∀ b', (T b').BlockTriangular id := by
      intro b'
      by_cases h : b' = b
      · subst h; rw [hTb]; exact htri
      · rw [hTo b' h]; exact Matrix.blockTriangular_one
    have hTd : ∀ b', (T b').det ≠ 0 := by
      intro b'
      by_cases h : b' = b
      · subst h; rw [hTb]; exact ht
      · rw [hTo b' h]; simp
    have hup : Function.update X b (X b * t) = fun b' => X b' * T b' := by
      funext b'
      by_cases h : b' = b
      · subst h; rw [hTb, Function.update_self]
      · rw [hTo b' h, Function.update_of_ne h, _root_.mul_one]
    obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y (fun b => (X b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
    obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
    rw [Units.val_one] at h₁ h₂
    have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y z₁ z₂).2 _ _ _ _ h₁ h₂
    simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
    have e₁ := hPK z₁ X hX h₁
    have e₂ := hPK z₂ (fun b' => X b' * T b')
      (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃
    have e₃ := evR_frChg_mul_triangular E H Dw l Xo c K a n F hF z₁ z₂ T hTtri hTd h₂
    have p₁ : (∏ b', ∏ i, T b' i i ^ a (b', i)) = ∏ i, t i i ^ a (b, i) := by
      rw [Finset.prod_eq_single b, hTb]
      · intro b' _ h
        rw [hTo b' h]; simp
      · intro h; exact absurd (Finset.mem_univ b) h
    have p₂ : (∏ b', (X b' * T b').det) = (∏ b', (X b').det) * ∏ i, t i i := by
      simp only [Matrix.det_mul, Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_eq_single b, hTb, Matrix.det_of_isUpperTriangular htri]
      · intro b' _ h
        rw [hTo b' h]; simp
      · intro h; exact absurd (Finset.mem_univ b) h
    rw [hup, ← e₂, ← e₁, e₃, p₁, p₂]
    simp only [pow_add, Finset.prod_mul_distrib, mul_pow, Finset.prod_pow]
    ring)
  refine ⟨G, fun S _ _ φ z z' Y hY hz hz' => ?_⟩
  have h1 := hP S φ z z' Y hY hz hz'
  rw [hG S φ.toRingHom Y] at h1
  have hu : IsUnit ((∏ b, (Y b).det) ^ N) := (IsUnit.prod_univ_iff.2 hY).pow N
  exact hu.mul_left_cancel h1

end GlobalTheory.LamT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsFramePolynomialOfRuleNumberFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isFramePolynomialOfRule_numberField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, ∃ G : MvPolynomial (FrVar Dw.mult) K, IsFrPoly F y G := by
  first | exact @GlobalTheory.LamT.exists_isFrPoly | exact GlobalTheory.LamT.exists_isFrPoly | (intros; apply GlobalTheory.LamT.exists_isFrPoly <;> assumption)
end
end
