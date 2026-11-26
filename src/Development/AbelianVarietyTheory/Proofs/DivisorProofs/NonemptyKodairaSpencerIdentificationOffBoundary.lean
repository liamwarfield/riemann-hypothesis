module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeDeRhamOnModificationOfFlagCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDerivativesBorelFrameChangeCanonicalWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerCoordinateUniqueNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularKodairaSpencerCoordinateAffineOffBo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDerivativesTangentLiftNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberDeformationLiftModification
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberDeformationLiftModification
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

theorem exists_isDef_lift_dualNumber : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {Q : FrPt Xo c K} (hz : z ≫ toFlag M = X.ptY Q) (zw : Sp (DualNumber K) ⟶ M.X) (hw : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ zw = z), ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧ zw ≫ toFlag M = X.ptY w := by
  intro E _ _ _ H Dw l Xo c Y X Z M K _ _ z ho Q hz zw hw
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hwU : ⊤ ≤ (zw ≫ M.σ) ⁻¹ᵁ U₀ X Z :=
    le_preimage_of_dualNumber (TrivSqZeroExt.fstHom K K K).toRingHom _ _ (by rw [← Category.assoc, hw]; exact hU)
  have hF : ⊤ ≤ (zw ≫ toFlag M) ⁻¹ᵁ flagOpen X := hwU
  have hr : Set.range (zw ≫ toFlag M) ⊆ Set.range X.inc := by
    rintro _ ⟨s, rfl⟩
    exact (opensRange_inc X).ge (hF (Set.mem_univ s))
  obtain ⟨w, hwi⟩ : ∃ w, w ≫ X.inc = zw ≫ toFlag M := ⟨_, IsOpenImmersion.lift_fac X.inc _ hr⟩
  have hred : spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ w = X.pt Q := by
    rw [← cancel_mono X.inc, Category.assoc, hwi, X.pt_inc, ← hz, ← Category.assoc]
    exact congrArg (· ≫ toFlag M) hw

  have hnil : IsNilpotent (RingHom.ker (GlobalTheory.FlagTan.red c K).toRingHom) := ⟨2, by
    rw [Ideal.zero_eq_bot, eq_bot_iff, pow_two]
    refine Ideal.mul_le.2 fun a ha b hb => ?_
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hb']⟩
  have hs : w ≫ pullback.snd _ _ ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) := by
    obtain ⟨φ, hφ⟩ : ∃ φ : c.F →+* DualNumber K, spMap φ = w ≫ pullback.snd _ _ ≫ pullback.snd _ _ :=
      ⟨(Spec.preimage (w ≫ pullback.snd _ _ ≫ pullback.snd _ _)).hom, by
        rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]⟩
    have h1 : spMap ((GlobalTheory.FlagTan.red c K).toRingHom.comp φ) = spMap (algebraMap c.F K) := by
      show Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom (GlobalTheory.FlagTan.red c K).toRingHom) = _
      rw [Spec.map_comp]
      change spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ spMap φ = _
      rw [hφ, ← Category.assoc, hred, ← Category.assoc, X.pt_snd, frX_snd]
    have h2 : (GlobalTheory.FlagTan.red c K).toRingHom.comp φ = algebraMap c.F K :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    haveI : FiniteDimensional ℚ c.F := c.fin
    haveI : Algebra.IsSeparable ℚ c.F := inferInstance
    haveI : Algebra.FormallyUnramified ℚ c.F := Algebra.FormallyUnramified.of_isSeparable ℚ c.F
    haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
    haveI : Algebra.FormallyUnramified ℤ c.F := Algebra.FormallyUnramified.comp ℤ ℚ c.F
    have h3 := Algebra.FormallyUnramified.ext' (R := ℤ) (A := c.F) (B := DualNumber K)
      (GlobalTheory.FlagTan.red c K).toRingHom hnil φ.toIntAlgHom (algebraMap c.F (DualNumber K)).toIntAlgHom
      (fun x => by
        show (GlobalTheory.FlagTan.red c K).toRingHom (φ x) =
          (GlobalTheory.FlagTan.red c K).toRingHom (algebraMap c.F (DualNumber K) x)
        exact (RingHom.congr_fun h2 x).trans ((GlobalTheory.FlagTan.red c K).commutes x).symm)
    rw [← hφ]
    exact congrArg spMap (congrArg AlgHom.toRingHom h3)
  obtain ⟨P', hP'⟩ := ((X.points (S := DualNumber K)).1 w).1 hs
  obtain ⟨P'', hP''⟩ := GlobalTheory.FlagMod.exists_frMap (GlobalTheory.FlagTan.red c K) P'
  have e1 : X.pt P'' = X.pt Q := by rw [← X.pt_frMap hP'', hP', hred]
  obtain ⟨t, ht⟩ := ((X.points (S := K)).2 P'' Q).1 e1
  obtain ⟨g, hgl, hgd, hc⟩ := (GlobalTheory.Frames.frBor_iff_frChg P'' Q t).1 ht
  have hdet : ∀ τ, IsUnit ((g τ).map (GlobalTheory.FlagTan.cst c K)).det := fun τ => by
    have h0 : IsUnit (g τ).det := by
      rw [Matrix.det_of_lowerTriangular (g τ) fun i j hij => hgl τ i j hij]
      exact IsUnit.prod_univ_iff.2 fun i => by rw [hgd]; exact Units.isUnit _
    have := h0.map (GlobalTheory.FlagTan.cst c K).toRingHom
    rwa [RingHom.map_det] at this
  obtain ⟨w', hW, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ P' (fun τ => (g τ).map (GlobalTheory.FlagTan.cst c K))
    (Units.map (GlobalTheory.FlagTan.cst c K).toRingHom.toMonoidHom (t none)) hdet
  have hdefQ : IsDef Q w' := by
    refine (GlobalTheory.FlagTan.frMap_iff_frChg hW hP'').2 ?_
    convert hc using 2 with τ
    · ext i j; simp
    · rfl
  have hB : FrBor (fun i => Units.map (GlobalTheory.FlagTan.cst c K).toRingHom.toMonoidHom (t i)) P' w' :=
    (GlobalTheory.Frames.frBor_iff_frChg P' w' _).2 ⟨fun τ => (g τ).map (GlobalTheory.FlagTan.cst c K),
      fun τ i j hij => by simp [hgl τ i j hij], fun τ i => by simp [hgd], hW⟩
  refine ⟨w', hdefQ, ?_⟩
  rw [← X.ptY_frBor hB, ← X.pt_inc, hP', hwi]

end GlobalTheory.CompHS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberDeformationLiftModificationStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualNumber_deformation_lift_modification : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {Q : FrPt Xo c K} (hz : z ≫ toFlag M = X.ptY Q) (zw : Sp (DualNumber K) ⟶ M.X) (hw : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ zw = z), ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧ zw ≫ toFlag M = X.ptY w := by
  first | exact @GlobalTheory.CompHS.exists_isDef_lift_dualNumber | exact GlobalTheory.CompHS.exists_isDef_lift_dualNumber | (intros; apply GlobalTheory.CompHS.exists_isDef_lift_dualNumber <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDerivativesTangentLiftNeZero
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

noncomputable section

theorem _root_.GlobalTheory.CompHS.det_tanLift_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {Q : FrPt Xo c K}
    (hz : z ≫ toFlag M = X.ptY Q) {v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)}
    (hv : IsTanFrame (psiSet H) Q v) {zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)}
    (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b)) (i : M.K.bundle.ι) (O : M.X.Opens) (hO : O ≤ M.K.bundle.U i)
    (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hzO : ⊤ ≤ z ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hJ : evalPt z O hzO (M.K.jacobian i hO g) ≠ 0), (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det ≠ 0 := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS K _ _ z ho Q hz v hv zv hl i O hO g hzO hzv hJ
  obtain ⟨O₁, hzO₁, x, w, hw, hdx⟩ := GlobalTheory.T.exists_tangentVectors_functions_invertible_derivs M.str (dimFlag Dw) z
  have hzi : ⊤ ≤ z ⁻¹ᵁ M.K.bundle.U i := fun s hs => hO (hzO hs)
  have hzO' : ⊤ ≤ z ⁻¹ᵁ (O₁ ⊓ M.K.bundle.U i) := fun s hs => ⟨hzO₁ hs, hzi hs⟩
  let x' : Fin (dimFlag Dw) → Γ(M.X, O₁ ⊓ M.K.bundle.U i) := fun a => resG M.X inf_le_left (x a)
  have hwO : ∀ b, ⊤ ≤ w b ⁻¹ᵁ O := fun b => le_preimage_of_dualNumber _ _ _ (by rw [hw b]; exact hzO)
  have hwO' : ∀ b, ⊤ ≤ w b ⁻¹ᵁ (O₁ ⊓ M.K.bundle.U i) := fun b => le_preimage_of_dualNumber _ _ _ (by rw [hw b]; exact hzO')
  have hwO₁ : ∀ b, ⊤ ≤ w b ⁻¹ᵁ O₁ := fun b => le_preimage_of_dualNumber _ _ _ (by rw [hw b]; exact hzO₁)
  have e1 : (Matrix.of fun a b => (evalPt (w b) (O₁ ⊓ M.K.bundle.U i) (hwO' b) (x' a)).snd) =
      Matrix.of fun a b => (evalPt (w b) O₁ (hwO₁ b) (x a)).snd := by
    ext a b
    simp only [Matrix.of_apply, x']
    rw [evalPt_res (w b) inf_le_left (hwO₁ b) (hwO' b)]
  have hjc := GlobalTheory.T.det_derivatives_div_jacobian_independent M z i w hw O (O₁ ⊓ M.K.bundle.U i) hO inf_le_right g x' hzO hzO' hwO hwO'
  rw [e1] at hjc
  have hdg : (Matrix.of fun a b => (evalPt (w b) O (hwO b) (g a)).snd).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hjc
    exact mul_ne_zero (hdx hwO₁) hJ hjc.symm
  have hQ := hKS K Q
  have hspan : ∀ c0 : Fin (dimFlag Dw), ∃ C : TIx Dw (psiSet H) → K, ∀ a,
      (evalPt (w c0) O (hwO c0) (g a)).snd = ∑ t, C t * (evalPt (zv t) O (hzv t) (g a)).snd := by
    intro c0
    obtain ⟨wf, hdef, hlw⟩ := GlobalTheory.T.exists_dualNumber_deformation_lift_modification M z ho hz (w c0) (hw c0)
    obtain ⟨Mx, hMx, -⟩ := hQ.existsUnique hdef.isTanX
    obtain ⟨C, hC⟩ := GlobalTheory.T.derivative_along_kodairaSpencer_deformation_lift M z ho hQ hz hv hl hdef hMx hlw
    refine ⟨Sum.elim Mx C, fun a => ?_⟩
    rw [hC O (g a) (hwO c0) hzv, Fintype.sum_sum_type]
    rfl
  choose C hC using hspan
  have hmat : (Matrix.of fun a b => (evalPt (w b) O (hwO b) (g a)).snd) =
      (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd) *
        Matrix.of (fun b c0 => C c0 (tanOrd Dw b)) := by
    ext a c0
    rw [Matrix.mul_apply, Matrix.of_apply, hC c0 a, ← Equiv.sum_comp (tanOrd Dw)]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Matrix.of_apply]
    ring
  intro h0
  apply hdg
  rw [hmat, Matrix.det_mul, h0, zero_mul]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDerivativesTangentLiftNeZeroStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_derivatives_tangentLift_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {Q : FrPt Xo c K}
    (hz : z ≫ toFlag M = X.ptY Q) {v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)}
    (hv : IsTanFrame (psiSet H) Q v) {zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)}
    (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b)) (i : M.K.bundle.ι) (O : M.X.Opens) (hO : O ≤ M.K.bundle.U i)
    (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hzO : ⊤ ≤ z ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hJ : evalPt z O hzO (M.K.jacobian i hO g) ≠ 0), (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det ≠ 0 := by
  first | exact @GlobalTheory.CompHS.det_tanLift_ne_zero | exact GlobalTheory.CompHS.det_tanLift_ne_zero | (intros; apply GlobalTheory.CompHS.det_tanLift_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingMapsLiftVerticalDeformationsAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingMapsLiftVerticalDeformationsAffine
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS


open TrivSqZeroExt in
theorem exists_spMap_fst_eq {S : Type} [CommRing S] (s : Sp (DualNumber S)) :
    ∃ t : Sp S, spMap (fstHom S S S).toRingHom t = s := by
  refine ⟨PrimeSpectrum.comap (inlHom S S) s, ?_⟩
  show PrimeSpectrum.comap _ (PrimeSpectrum.comap _ s) = s
  ext x
  have hr : inr x.snd ∈ s.asIdeal := s.2.mem_of_pow_mem 2 (by
    rw [show (inr x.snd : DualNumber S) ^ 2 = 0 by ext <;> simp [pow_two]]
    exact s.asIdeal.zero_mem)
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  change inl x.fst ∈ s.asIdeal ↔ x ∈ s.asIdeal
  have e1 : inl x.fst + inr x.snd = x := inl_fst_add_inr_snd_eq x
  have e2 : inl x.fst = x - inr x.snd := eq_sub_of_add_eq e1
  constructor
  · intro h
    rw [← e1]
    exact s.asIdeal.add_mem h hr
  · intro h
    rw [e2]
    exact s.asIdeal.sub_mem h hr

theorem le_preimage_of_fst {S : Type} [CommRing S] {T : Scheme.{0}} (x : Sp (DualNumber S) ⟶ T) (V : T.Opens)
    (h : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  obtain ⟨t, rfl⟩ := exists_spMap_fst_eq s
  exact h (Set.mem_univ t)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw))

theorem exists_dualLift {S : Type} [CommRing S] [Algebra c.F S] {Q : FrPt Xo c S} {v : FrPt Xo c (DualNumber S)}
    (hv : FrMap (TrivSqZeroExt.fstHom c.F S S) v Q) {z : Sp S ⟶ M.X} (hz : z ≫ toFlag M = X.ptY Q)
    (ho : ⊤ ≤ z ⁻¹ᵁ M.off) :
    ∃ zv : Sp (DualNumber S) ⟶ M.X, zv ≫ toFlag M = X.ptY v ∧
      spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ zv = z := by
  have e : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ X.ptY v = z ≫ toFlag M :=
    (X.ptY_frMap hv).trans hz.symm
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hb : ⊤ ≤ X.ptY v ⁻¹ᵁ (inc₀ X Z).opensRange := le_preimage_of_fst _ _ (by
    rw [e]
    rintro s -
    exact ⟨(z ≫ M.σ) s, rfl⟩)
  have hr : Set.range (X.ptY v) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    exact hb (Set.mem_univ s)
  obtain ⟨w, hw⟩ : ∃ w, w ≫ inc₀ X Z = X.ptY v := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have ered : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw, e, Category.assoc]
  have hwU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z := le_preimage_of_fst _ _ (by rw [ered]; exact hU)
  obtain ⟨zv, hzv, -⟩ := M.existsUnique_lift w hwU
  have hred : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ zv = z :=
    (M.existsUnique_lift (z ≫ M.σ) hU).unique (by rw [Category.assoc, hzv, ered]) rfl
  refine ⟨zv, ?_, hred⟩
  rw [toFlag, ← Category.assoc, hzv, hw]

def vertMat {S : Type} [CommRing S] (b : VIx Dw) (σ : E →+* ℂ) :
    Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) (DualNumber S) :=
  Matrix.of fun i j => TrivSqZeroExt.inl ((1 : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S) i j) +
    TrivSqZeroExt.inr ((Pi.single b.toF (1 : S) : GlobalTheory.FlagTan.FIx Dw → S) (some ⟨σ, i, j⟩))

theorem isUnit_det_vertMat {S : Type} [CommRing S] (b : VIx Dw) (σ : E →+* ℂ) :
    IsUnit (vertMat (S := S) b σ).det := by
  have e : (TrivSqZeroExt.fstHom S S S).toRingHom.mapMatrix (vertMat (S := S) b σ) = 1 := by
    ext i j; simp [vertMat]
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  show IsUnit ((TrivSqZeroExt.fstHom S S S).toRingHom _)
  rw [RingHom.map_det, e, Matrix.det_one]
  exact isUnit_one

theorem exists_vertLift (k : X.F.J) (W : M.X.Opens) (hW : IsAffineOpen W)
    (hle : W ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k) :
    ∃ e : VIx Dw → (Γ(M.X, W) →+* DualNumber Γ(M.X, W)), (∀ b s, (e b s).fst = s) ∧
      ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W) →+* K)
        (hk : ⊤ ≤ ((spMap ψ ≫ tau hW) ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
        X.F.ChartFr k _ hk Q → ∀ b : VIx Dw, ∃ w : FrPt Xo c (DualNumber K),
          IsVert Q (Pi.single b.toF (1 : K)) w ∧
          spMap ((dualMap ψ).comp (e b)) ≫ tau hW ≫ toFlag M = X.ptY w := by
  have hτo : ⊤ ≤ tau hW ⁻¹ᵁ M.off := tau_le hW (hle.trans inf_le_left)
  have hτk : ⊤ ≤ (tau hW ≫ toFlag M) ⁻¹ᵁ X.F.U k := fun x hx => tau_le hW (hle.trans inf_le_right) hx
  have hF : ⊤ ≤ (tau hW ≫ toFlag M) ⁻¹ᵁ flagOpen X := fun x hx => by
    have := hτo hx
    rw [M.off_eq] at this
    exact this
  obtain ⟨_, hch⟩ := exists_chartFr _ hF
  obtain ⟨Q₀, hQ₀⟩ := hch k hτk
  have e₀ : tau hW ≫ toFlag M = X.ptY Q₀ := GlobalTheory.FlagMod.FlagCover.eq_ptY hQ₀.lies
  obtain ⟨Q₁, hQ₁⟩ := GlobalTheory.FlagTan.exists_frMap (TrivSqZeroExt.inlAlgHom c.F Γ(M.X, W) Γ(M.X, W)) Q₀
  have hred : FrMap (TrivSqZeroExt.fstHom c.F Γ(M.X, W) Γ(M.X, W)) Q₁ Q₀ :=
    GlobalTheory.FlagTan.frMap_of_comp hQ₁ (GlobalTheory.FlagTan.frMap_id Q₀) fun _ => rfl
  have hV : ∀ b : VIx Dw, ∃ V : FrPt Xo c (DualNumber Γ(M.X, W)),
      GlobalTheory.Frames.FrChg (vertMat b) ((1 : (DualNumber Γ(M.X, W))ˣ) : DualNumber Γ(M.X, W)) Q₁ V := fun b =>
    (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ Q₁ (vertMat b) 1 (isUnit_det_vertMat b)).exists
  choose V hV using hV
  have hVr : ∀ b, FrMap (TrivSqZeroExt.fstHom c.F Γ(M.X, W) Γ(M.X, W)) (V b) Q₀ := fun b => by
    refine (GlobalTheory.FlagTan.frMap_iff_frChg (hV b) hred).2 ?_
    convert (GlobalTheory.Frames.frChg_calculus E H Dw l Xo c Γ(M.X, W)).2.1 Q₀ using 2 with σ
    · ext i j; simp [vertMat]
    · simp
  choose zv hzv hzr using fun b => exists_dualLift M (hVr b) e₀ hτo
  have hzW : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ W := fun b => le_preimage_of_fst _ _ (by rw [hzr b]; exact tau_le hW le_rfl)
  refine ⟨fun b => GlobalTheory.FlagMod.ev (zv b) W (hzW b), fun b s => ?_, ?_⟩
  · have h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom Γ(M.X, W) Γ(M.X, W) Γ(M.X, W)).toRingHom ≫ zv b) ⁻¹ᵁ W := by
      rw [hzr b]; exact tau_le hW le_rfl
    have h1 := GlobalTheory.FlagMod.ev_spMap _ (zv b) W (hzW b) h'
    rw [GlobalTheory.FlagMod.ev_congr (hzr b) W h' (tau_le hW le_rfl), GlobalTheory.FlagMod.ev_tau_self] at h1
    exact (DFunLike.congr_fun h1 s).symm
  intro K _ _ ψ hk Q hQ b

  have hx : frX Q = spMap ψ ≫ frX Q₀ := by
    let w₀ : Sp Γ(M.X, W) ⟶ X.Yo := pullback.lift (tau hW ≫ toFlag M) (frX Q₀) hQ₀.over.symm
    let w₁ : Sp K ⟶ X.Yo := pullback.lift ((spMap ψ ≫ tau hW) ≫ toFlag M) (frX Q) hQ.over.symm
    have e : w₁ = spMap ψ ≫ w₀ := by
      rw [← cancel_mono X.inc]
      simp only [w₀, w₁, Category.assoc, pullback.lift_fst]
    have := congrArg (· ≫ pullback.snd X.π Y.j) e
    simpa only [w₀, w₁, Category.assoc, pullback.lift_snd] using this
  have hs : spMap (algebraMap c.F K) = spMap (ψ.comp (algebraMap c.F Γ(M.X, W))) := by
    rw [← frX_snd Q, hx, Category.assoc, frX_snd Q₀, spMap_comp']
  have hψ : ψ.comp (algebraMap c.F Γ(M.X, W)) = algebraMap c.F K :=
    (congrArg CommRingCat.Hom.hom (Spec.map_injective hs)).symm
  let φ : Γ(M.X, W) →ₐ[c.F] K := { ψ with commutes' := fun r => DFunLike.congr_fun hψ r }
  let φε : DualNumber Γ(M.X, W) →ₐ[c.F] DualNumber K :=
    { dualMap ψ with
      commutes' := fun r => by
        ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl', ← DFunLike.congr_fun hψ r] }
  obtain ⟨Q', hQ'⟩ := GlobalTheory.FlagTan.exists_frMap φ Q₀
  have eQ : Q = Q' := hQ.unique (hQ₀.frMap hQ' (by rw [Category.assoc]) hk)
  subst eQ
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.FlagTan.exists_frMap φε Q₁
  obtain ⟨w, hw⟩ := GlobalTheory.FlagTan.exists_frMap φε (V b)
  refine ⟨w, ⟨y₀, GlobalTheory.FlagTan.frMap_of_comp hQ' (GlobalTheory.FlagTan.frMap_comp (χ := φε.comp (TrivSqZeroExt.inlAlgHom c.F Γ(M.X, W) Γ(M.X, W))) hQ₁ hy₀ fun _ => rfl) fun a => ?_, ?_⟩, ?_⟩
  · ext <;> simp [φ, φε, dualMap]
  · have h2 := (GlobalTheory.FlagTan.frMap_iff_frChg (hV b) hy₀).1 hw
    unfold GlobalTheory.FlagTan.IsShift
    convert h2 using 2 with σ
    · ext i j <;> simp [GlobalTheory.FlagTan.unip, vertMat, φε, dualMap, Matrix.one_apply, Pi.single_apply] <;> split_ifs <;> simp
    · ext <;> simp [GlobalTheory.FlagTan.unip₀, φε, dualMap, GlobalTheory.FlagTan.VIx.toF]
  · have h3 : spMap (GlobalTheory.FlagMod.ev (zv b) W (hzW b)) ≫ tau hW = zv b := GlobalTheory.FlagMod.spMap_ev (zv b) hW (hzW b)
    rw [← spMap_comp', Category.assoc, ← Category.assoc (spMap _) (tau hW), h3, hzv b]
    have e4 : dualMap ψ = φε.toRingHom := RingHom.ext fun _ => rfl
    rw [e4]
    exact X.ptY_frMap hw

end GlobalTheory.CompHS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingMapsLiftVerticalDeformationsAffineStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringMaps_lift_vertical_deformations_affine : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (k : X.F.J) (W : M.X.Opens) (hW : IsAffineOpen W)
    (hle : W ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k), ∃ e : VIx Dw → (Γ(M.X, W) →+* DualNumber Γ(M.X, W)), (∀ b s, (e b s).fst = s) ∧
      ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W) →+* K)
        (hk : ⊤ ≤ ((spMap ψ ≫ tau hW) ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
        X.F.ChartFr k _ hk Q → ∀ b : VIx Dw, ∃ w : FrPt Xo c (DualNumber K),
          IsVert Q (Pi.single b.toF (1 : K)) w ∧
          spMap ((dualMap ψ).comp (e b)) ≫ tau hW ≫ toFlag M = X.ptY w := by
  first | exact @GlobalTheory.CompHS.exists_vertLift | exact GlobalTheory.CompHS.exists_vertLift | (intros; apply GlobalTheory.CompHS.exists_vertLift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularKodairaSpencerCoordinateAffineOffBo
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CompHS
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open scoped Classical
open GlobalTheory.AllWt (exOf)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw))

theorem glue_field_cover {Z : Scheme.{0}} [IsReduced Z] (V : Z.Opens)
    (R : ∀ (L : Type) [Field L], (Sp L ⟶ Z) → L → Prop)
    (loc : ∀ p ∈ V, ∃ (W : Z.Opens) (a : Γ(Z, W)), p ∈ W ∧ W ≤ V ∧
      (∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ W), R L z (ev z W hz a)) ∧
      ∀ (L : Type) [Field L] (z : Sp L ⟶ Z), ⊤ ≤ z ⁻¹ᵁ W → ∀ x y, R L z x → R L z y → x = y) :
    ∃ a : Γ(Z, V), ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), R L z (ev z V hz a) := by
  choose! W a hp hWV ha hu using loc
  let I := {p // p ∈ V}
  have hc : ∀ p ∈ V, ∃ i : I, p ∈ W i.1 := fun p h => ⟨⟨p, h⟩, hp p h⟩
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => W i.1) V (fun i => homOfLE (hWV i.1 i.2))
    (fun p h => TopologicalSpace.Opens.mem_iSup.2 (hc p h)) (fun i => a i.1) (fun i j => by
      refine GlobalTheory.FlagMod.ext_ev_field (a := resG Z inf_le_left (a i.1)) (b := resG Z inf_le_right (a j.1)) fun L _ z hz => ?_
      have hi := le_preimage_mono inf_le_left hz
      have hj := le_preimage_mono inf_le_right hz
      rw [GlobalTheory.FlagMod.ev_res z _ hz hi, GlobalTheory.FlagMod.ev_res z _ hz hj]
      exact hu i.1 i.2 L z hi _ _ (ha i.1 i.2 L z hi) (ha j.1 j.2 L z hj))
  refine ⟨s, fun L _ z hz => ?_⟩
  obtain ⟨i, hi⟩ := hc (z (IsLocalRing.closedPoint L)) (hz (Set.mem_univ _))
  have hi' : ⊤ ≤ z ⁻¹ᵁ W i.1 := ((IsLocalRing.closed_point_mem_iff (U := z ⁻¹ᵁ W i.1)).1 hi).ge
  have e : ev z V hz s = ev z (W i.1) hi' (a i.1) :=
    (GlobalTheory.FlagMod.ev_res z (hWV i.1 i.2) hi' hz s).symm.trans (congrArg _ (hs i))
  exact e ▸ ha i.1 i.2 L z hi'

theorem exists_local (hP : GlobalTheory.Published.AbelianDeRham)
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    (i : M.K.bundle.ι) (k : X.F.J) (W : M.X.Opens) (hW : W ≤ ksOpen M i k) (p : M.X) (hp : p ∈ W) :
    ∃ (W' : M.X.Opens) (a : Γ(M.X, W')), p ∈ W' ∧ W' ≤ W ∧
      (∀ (L : Type) [Field L] (z : Sp L ⟶ M.X) (hz : ⊤ ≤ z ⁻¹ᵁ W'), KSRel M i k z (ev z W' hz a)) ∧
      ∀ (L : Type) [Field L] (z : Sp L ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ W' → ∀ x y, KSRel M i k z x → KSRel M i k z y → x = y := by
  have hWk : ksOpen M i k ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k := fun s hs =>
    ⟨hs.1, (((common₀ X Z).pull M.σ).mem _ _ _).1 hs.2.2⟩
  have hWi : ksOpen M i k ≤ M.K.bundle.U i := fun s hs => hs.2.1
  obtain ⟨V, f, hpV, hf⟩ := exists_isFrame_dOn M.str (dimFlag Dw) p
  obtain ⟨W₁, hW₁, hpW₁, hW₁V⟩ := Opens.isBasis_iff_nbhd.1 M.X.isBasis_affineOpens (show p ∈ W ⊓ V from ⟨hp, hpV⟩)
  obtain ⟨W', hW', eH, hpW', hWW', eH1, eH2⟩ := GlobalTheory.T.hodge_de_rham_on_modification_of_flag_cover M hP hKS k W₁
    ((hW₁V.trans inf_le_left).trans (hW.trans hWk)) p hpW₁
  have hWV : W' ≤ W := hWW'.trans (hW₁V.trans inf_le_left)
  have hW'k : W' ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k := hWV.trans (hW.trans hWk)
  have hW'i : W' ≤ M.K.bundle.U i := hWV.trans (hW.trans hWi)
  obtain ⟨eV, eV1, eV2⟩ := GlobalTheory.T.exists_ringMaps_lift_vertical_deformations_affine M k W' hW' hW'k
  let e : TIx Dw (psiSet H) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W')) := Sum.elim eH eV
  have e1 : ∀ b s, (e b s).fst = s := by
    rintro (b | b) s
    · exact eH1 b s
    · exact eV1 b s

  have e2 : ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W') →+* K)
      (hk : ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
      X.F.ChartFr k _ hk Q → ∃ v, IsTanFrame (psiSet H) Q v ∧
        ∀ b, spMap ((dualMap ψ).comp (e b)) ≫ tau hW' ≫ toFlag M = X.ptY (v b) := by
    intro K _ _ ψ hk Q hQ
    choose w₁ hw₁ hw₁' hw₁'' using eH2 K ψ hk Q hQ
    choose w₂ hw₂ hw₂' using eV2 K ψ hk Q hQ
    refine ⟨Sum.elim w₁ w₂, ⟨fun b => ⟨hw₁ b, hw₁' b⟩, fun b => hw₂ b⟩, ?_⟩
    rintro (b | b)
    · exact hw₁'' b
    · exact hw₂' b
  let g : Fin (dimFlag Dw) → Γ(M.X, W') := fun a => resG M.X (hWW'.trans (hW₁V.trans inf_le_right)) (f a)
  have hu : IsUnit (M.K.jacobian i hW'i g) := (M.K.isUnit_jacobian_iff i hW' hW'i g).2 (by
    have := hf.res hW' (hWW'.trans (hW₁V.trans inf_le_right))
    rwa [resForm_dOn] at this)
  let A : Matrix (Fin (dimFlag Dw)) (Fin (dimFlag Dw)) Γ(M.X, W') :=
    Matrix.of fun a b => (e (tanOrd Dw b) (g a)).snd

  let zv : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X) :=
    fun ψ b => spMap ((dualMap ψ).comp (e b)) ≫ tau hW'
  have hzvW : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K) b, ⊤ ≤ zv ψ b ⁻¹ᵁ W' := fun ψ b =>
    le_preimage_comp _ (tau_le hW' le_rfl)
  have hred : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K) b,
      spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ zv ψ b = spMap ψ ≫ tau hW' := fun {K} _ ψ b => by
    simp only [zv]
    rw [← Category.assoc, ← spMap_comp]
    congr 2
    ext s
    simp [dualMap, e1]
  have hev : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K) a b,
      (evalPt (zv ψ b) W' (hzvW ψ b) (g a)).snd = ψ (e b (g a)).snd := fun ψ a b => by
    have := ev_spMap_tau hW' ((dualMap ψ).comp (e b)) (hzvW ψ b)
    have h2 : evalPt (zv ψ b) W' (hzvW ψ b) (g a) = ((dualMap ψ).comp (e b)) (g a) := congrFun (congrArg DFunLike.coe this) _
    rw [h2]
    simp [dualMap]
  have hdet : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K),
      (Matrix.of fun a b => (evalPt (zv ψ (tanOrd Dw b)) W' (hzvW ψ _) (g a)).snd).det = ψ A.det := fun ψ => by
    rw [RingHom.map_det]
    congr 1
    ext a b
    exact hev ψ a _
  have hzW : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ⊤ ≤ (spMap ψ ≫ tau hW') ⁻¹ᵁ W' := fun ψ =>
    le_preimage_comp _ (tau_le hW' le_rfl)
  have ho : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ⊤ ≤ (spMap ψ ≫ tau hW') ⁻¹ᵁ M.off := fun ψ =>
    le_preimage_comp _ (tau_le hW' (hW'k.trans inf_le_left))
  have hkk : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ X.F.U k :=
    fun ψ => by
      show ⊤ ≤ (spMap ψ ≫ tau hW') ⁻¹ᵁ (toFlag M ⁻¹ᵁ X.F.U k)
      exact le_preimage_comp _ (tau_le hW' (hW'k.trans inf_le_right))
  have chart : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ∃ (_ : Algebra c.F K) (Q : FrPt Xo c K),
      X.F.ChartFr k _ (hkk ψ) Q := fun ψ => by
    have hF : ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ flagOpen X := fun s _ => by
      have := ho ψ (Set.mem_univ s)
      rw [M.off_eq] at this
      exact this
    obtain ⟨a, h⟩ := exists_chartFr _ hF
    exact ⟨a, h k (hkk ψ)⟩
  have hJ : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), evalPt (spMap ψ ≫ tau hW') W' (hzW ψ) (M.K.jacobian i hW'i g) = ψ (M.K.jacobian i hW'i g) :=
    fun ψ => congrFun (congrArg DFunLike.coe (ev_spMap_tau hW' ψ (hzW ψ))) _
  have hl' : ∀ {K : Type} [Field K] [Algebra c.F K] (ψ : Γ(M.X, W') →+* K) {v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)},
      (∀ b, spMap ((dualMap ψ).comp (e b)) ≫ tau hW' ≫ toFlag M = X.ptY (v b)) → ∀ b, zv ψ b ≫ toFlag M = X.ptY (v b) :=
    fun ψ _ h b => (Category.assoc _ _ _).trans (h b)
  have hne : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ψ A.det ≠ 0 := fun {K} _ ψ => by
    obtain ⟨_, Q, hQ⟩ := chart ψ
    obtain ⟨v, hv, hl⟩ := e2 K ψ _ Q hQ
    have := GlobalTheory.T.det_derivatives_tangentLift_ne_zero M hKS (spMap ψ ≫ tau hW') (ho ψ) (FlagCover.eq_ptY hQ.lies) hv (hl' ψ hl) i W' hW'i g (hzW ψ)
      (hzvW ψ) (by rw [hJ]; exact (hu.map ψ).ne_zero)
    rwa [hdet] at this
  have hAu : IsUnit A.det := by
    by_contra h
    obtain ⟨m, hm, hdm⟩ := exists_max_ideal_of_mem_nonunits h
    letI := Ideal.Quotient.field m
    exact hne (Ideal.Quotient.mk m) (Ideal.Quotient.eq_zero_iff_mem.2 hdm)
  let a : Γ(M.X, W') := M.K.jacobian i hW'i g * ↑(hAu.unit⁻¹)
  have hinv : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), ψ A.det * ψ ↑(hAu.unit⁻¹) = 1 := fun ψ => by
    rw [← map_mul]
    have : A.det * ↑(hAu.unit⁻¹) = 1 := hAu.mul_val_inv
    rw [this, map_one]
  have rel : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K), KSRel M i k (spMap ψ ≫ tau hW') (ψ a) := by
    intro K _ ψ _ P Q t v zv' O hO g' hz hzv hk hQ ht hv hl
    obtain ⟨v0, hv0, hl0⟩ := e2 K ψ hk Q hQ
    have hzO : ∀ b, ⊤ ≤ zv ψ b ⁻¹ᵁ O := fun b => le_preimage_of_dualNumber (TrivSqZeroExt.fstHom K K K).toRingHom _ O
      (by rw [hred]; exact hz)
    have tc := GlobalTheory.T.det_derivatives_borelFrameChange_canonicalWeight M hKS (spMap ψ ≫ tau hW') (ho ψ) t (FlagCover.eq_ptY hQ.lies) ht hv hv0 hl (hl' ψ hl0) O g' hzv hzO
    have jc := GlobalTheory.T.det_derivatives_div_jacobian_independent M (spMap ψ ≫ tau hW') i (fun b => zv ψ (tanOrd Dw b)) (fun b => hred ψ _) O W' hO hW'i g' g hz
      (hzW ψ) (fun b => hzO _) (fun b => hzvW ψ _)
    rw [hJ, hdet] at jc
    rw [tc]
    generalize (Matrix.of fun a b => (evalPt (zv ψ (tanOrd Dw b)) O (hzO _) (g' a)).snd).det = D0 at jc ⊢
    generalize evalPt (spMap ψ ≫ tau hW') O hz (M.K.jacobian i hO g') = J1 at jc ⊢
    generalize ((∏ ix, t ix ^ exOf Dw (kap Dw) 0 ix : Kˣ) : K) = T
    have h1 := hinv ψ
    simp only [a, map_mul]
    generalize ψ ↑(hAu.unit⁻¹) = u at h1 ⊢
    generalize ψ A.det = d at jc h1
    generalize ψ (M.K.jacobian i hW'i g) = J0 at jc ⊢
    calc J0 * u * (T * D0) = T * u * (D0 * J0) := by ring
      _ = T * u * (d * J1) := by rw [jc]
      _ = (d * u) * (T * J1) := by ring
      _ = T * J1 := by rw [h1, one_mul]
  have uniq : ∀ {K : Type} [Field K] (ψ : Γ(M.X, W') →+* K) (x y : K), KSRel M i k (spMap ψ ≫ tau hW') x →
      KSRel M i k (spMap ψ ≫ tau hW') y → x = y := by
    intro K _ ψ x y hx hy
    obtain ⟨alg, Q, hQ⟩ := chart ψ
    obtain ⟨v0, hv0, hl0⟩ := e2 K ψ _ Q hQ
    have hb := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K).1 Q
    have a1 := @hx alg Q Q 1 v0 (zv ψ) W' hW'i g (hzW ψ) (hzvW ψ) _ hQ hb hv0 (hl' ψ hl0)
    have a2 := @hy alg Q Q 1 v0 (zv ψ) W' hW'i g (hzW ψ) (hzvW ψ) _ hQ hb hv0 (hl' ψ hl0)
    rw [hdet] at a1 a2
    exact mul_right_cancel₀ (hne ψ) (a1.trans a2.symm)
  refine ⟨W', a, hpW', hWV, fun L _ z hz => ?_, fun L _ z hz x y hx hy => ?_⟩
  · have e0 : spMap (ev z W' hz) ≫ tau hW' = z := spMap_ev z hW' hz
    have h : KSRel M i k (spMap (ev z W' hz) ≫ tau hW') (ev z W' hz a) := @rel L _ (ev z W' hz)
    rwa [e0] at h
  · have e0 : spMap (ev z W' hz) ≫ tau hW' = z := spMap_ev z hW' hz
    rw [← e0] at hx hy
    exact uniq _ x y hx hy

theorem exists_regular_ksRel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), GlobalTheory.Published.AbelianDeRham → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (i : M.K.bundle.ι) (k : X.F.J) (W : M.X.Opens), IsAffineOpen W → W ≤ ksOpen M i k → ∃ a : Γ(M.X, W), ∀ (K : Type) [Field K] (z : Sp K ⟶ M.X) (hz : ⊤ ≤ z ⁻¹ᵁ W), KSRel M i k z (GlobalTheory.FlagMod.ev z W hz a) := by
  intro E _ _ _ H Dw l Xo c Y X Z M hP hKS i k W _ hW
  haveI : Smooth M.str := SmoothOfRelativeDimension.smooth (dimFlag Dw) M.str
  haveI : IsReduced M.X := isReduced_of_smooth M.str
  exact glue_field_cover W (fun L _ z x => KSRel M i k z x) (exists_local M hP hKS i k W hW)

end GlobalTheory.CompHS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularKodairaSpencerCoordinateAffineOffBoStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_kodairaSpencerCoordinate_affine_off_boundary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), GlobalTheory.Published.AbelianDeRham → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (i : M.K.bundle.ι) (k : X.F.J) (W : M.X.Opens), IsAffineOpen W → W ≤ ksOpen M i k → ∃ a : Γ(M.X, W), ∀ (K : Type) [Field K] (z : Sp K ⟶ M.X) (hz : ⊤ ≤ z ⁻¹ᵁ W), KSRel M i k z (GlobalTheory.FlagMod.ev z W hz a) := by
  first | exact @GlobalTheory.CompHS.exists_regular_ksRel | exact GlobalTheory.CompHS.exists_regular_ksRel | (intros; apply GlobalTheory.CompHS.exists_regular_ksRel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerCoordsTwoChartsTransition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerCoordsTwoChartsTransition
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.AllWt (exOf)

theorem mem_prime_dual_iff {K : Type} [Field K] (p : Ideal (DualNumber K)) [hp : p.IsPrime] (x : DualNumber K) :
    x ∈ p ↔ x.fst = 0 := by
  constructor
  · intro hx
    by_contra h
    have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 h)
    exact hp.ne_top (Ideal.eq_top_of_isUnit_mem p hx hu)
  · intro h
    have hx : x = TrivSqZeroExt.inr x.snd := TrivSqZeroExt.ext h rfl
    have h2 : x * x = 0 := by rw [hx, TrivSqZeroExt.inr_mul_inr]
    exact (hp.mem_or_mem (h2 ▸ p.zero_mem)).elim id id

theorem dual_pt_eq {K : Type} [Field K] (p q : Sp (DualNumber K)) : p = q := by
  apply PrimeSpectrum.ext
  ext x
  have hp : p.asIdeal.IsPrime := p.isPrime
  have hq : q.asIdeal.IsPrime := q.isPrime
  exact (mem_prime_dual_iff (K := K) p.asIdeal x).trans (mem_prime_dual_iff (K := K) q.asIdeal x).symm

theorem top_le_of_red {K : Type} [Field K] {T : Scheme.{0}} (φ : DualNumber K →+* K) (w : Sp (DualNumber K) ⟶ T)
    {V : T.Opens} (h : ⊤ ≤ (spMap φ ≫ w) ⁻¹ᵁ V) : ⊤ ≤ w ⁻¹ᵁ V := by
  intro p _
  obtain ⟨q⟩ : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have e : p = spMap φ q := dual_pt_eq _ _
  have hq := h (Set.mem_univ q)
  rw [e]
  exact hq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))

theorem ev_resU {T : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ T) {U V : T.Opens} (e : V ≤ U)
    (hV : ⊤ ≤ z ⁻¹ᵁ V) (hU : ⊤ ≤ z ⁻¹ᵁ U) (u : Γ(T, U)ˣ) :
    GlobalTheory.FlagMod.ev z V hV (res e u).val = GlobalTheory.FlagMod.ev z U hU u.val :=
  GlobalTheory.FlagMod.ev_res z e hV hU u.val

theorem tAt_congr {K : Type} [CommRing K] (k k' : X.F.J) {w w' : Sp K ⟶ X.YY} (e : w = w')
    (h : ⊤ ≤ w ⁻¹ᵁ (X.F.U k ⊓ X.F.U k')) (h' : ⊤ ≤ w' ⁻¹ᵁ (X.F.U k ⊓ X.F.U k')) :
    X.F.TAt k k' w h = X.F.TAt k k' w' h' := by
  subst e; rfl


open Classical in
theorem ev_div_g (i i' : M.K.bundle.ι) (k k' : X.F.J) {K : Type} [Field K] (z : Sp K ⟶ M.X)
    (hg : ⊤ ≤ z ⁻¹ᵁ ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k) ⊓
      (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i', flagIdx M _ k')))
    (hK : ⊤ ≤ z ⁻¹ᵁ (M.K.bundle.U i ⊓ M.K.bundle.U i')) (hh : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k')) :
    GlobalTheory.FlagMod.ev z _ hg ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).g (i, flagIdx M _ k)
                 (i', flagIdx M _ k')).val =
      GlobalTheory.FlagMod.ev z _ hK (M.K.bundle.g i i').val *
        (∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ exOf Dw (FlagTan.kap Dw) 0 ix).val := by
  set e := exOf Dw (FlagTan.kap Dw) 0
  have hL : ⊤ ≤ z ⁻¹ᵁ (((L₀ X Z (FlagTan.kap Dw)).pull M.σ).U (flagIdx M _ k) ⊓
      ((L₀ X Z (FlagTan.kap Dw)).pull M.σ).U (flagIdx M _ k')) := fun p hp => ⟨(hg hp).1.2, (hg hp).2.2⟩
  have hh1 : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ ((L₀ X Z (FlagTan.kap Dw)).U (flagIdx M _ k PUnit.unit) ⊓
      (L₀ X Z (FlagTan.kap Dw)).U (flagIdx M _ k' PUnit.unit)) := fun p hp => ⟨mem_pIdx.2 (hh hp).1, mem_pIdx.2 (hh hp).2⟩
  have hh2 : ⊤ ≤ ((z ≫ M.σ) ≫ inc₀ X Z) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k') := fun p hp => hh hp
  have eL : GlobalTheory.FlagMod.ev z _ hL (((L₀ X Z (FlagTan.kap Dw)).pull M.σ).g (flagIdx M _ k) (flagIdx M _ k')).val =
      (∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ (-e ix)).val := by
    rw [GlobalTheory.FlagMod.ev_pull_g _ _ _ _ z hL hh1]
    rw [GlobalTheory.FlagMod.ev_pull_g _ _ _ _ (z ≫ M.σ) hh1 hh2]
    refine (X.F.ev_LL_g e k k' _ hh2).trans ?_
    rw [tAt_congr k k' (Category.assoc _ _ _) hh2 hh]
  have ei : ((∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ (-e ix) : Kˣ) : K)⁻¹ =
      ((∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ e ix : Kˣ) : K) := by
    rw [← Units.val_inv_eq_inv_val, ← Finset.prod_inv_distrib]
    simp only [zpow_neg, inv_inv]
  dsimp only [LB.div]
  refine ((GlobalTheory.FlagMod.ev z _ hg).map_mul _ _).trans (congrArg₂ (· * ·) (ev_resU z _ hg hK _)
    ((map_units_inv (GlobalTheory.FlagMod.ev z _ hg) _).trans ?_))
  refine (congrArg Inv.inv (ev_resU z _ hg hL _)).trans ?_
  rw [eL, ei]

theorem red_comp_eq {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {P : FrPt Xo c K}
    (hP : z ≫ toFlag M = X.ptY P) {w : FrPt Xo c (DualNumber K)} (hw : FlagTan.IsDef P w)
    (zw : Sp (DualNumber K) ⟶ M.X) (hl : zw ≫ toFlag M = X.ptY w) :
    spMap (FlagTan.red c K).toRingHom ≫ zw = z := by
  have hx : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun p hp => by
    have := ho hp
    rw [M.off_eq] at this
    exact this
  have h1 : (spMap (FlagTan.red c K).toRingHom ≫ zw) ≫ M.σ = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z)]
    simp only [Category.assoc]
    have e1 : zw ≫ M.σ ≫ inc₀ X Z = X.ptY w := hl
    have e2 : z ≫ M.σ ≫ inc₀ X Z = X.ptY P := hP
    rw [e1, e2]
    exact X.ptY_frMap hw
  exact (M.existsUnique_lift (z ≫ M.σ) hx).unique h1 rfl

theorem top_le_of_isDef {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {P : FrPt Xo c K} (hP : z ≫ toFlag M = X.ptY P) {w : FrPt Xo c (DualNumber K)} (hw : FlagTan.IsDef P w)
    (zw : Sp (DualNumber K) ⟶ M.X) (hl : zw ≫ toFlag M = X.ptY w) {V : M.X.Opens} (hV : ⊤ ≤ z ⁻¹ᵁ V) :
    ⊤ ≤ zw ⁻¹ᵁ V :=
  top_le_of_red _ zw (by rw [red_comp_eq M z ho hP hw zw hl]; exact hV)


open Classical in
theorem ksRel_of_ksRel {i i' : M.K.bundle.ι} {k k' : X.F.J} {K : Type} [Field K] {z : Sp K ⟶ M.X}
    (hs : ⊤ ≤ z ⁻¹ᵁ ksOpen M i k) (hs' : ⊤ ≤ z ⁻¹ᵁ ksOpen M i' k')
    (hg : ⊤ ≤ z ⁻¹ᵁ ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k) ⊓
      (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i', flagIdx M _ k'))) {x' : K}
    (hx' : KSRel M i' k' z x') :
    KSRel M i k z (GlobalTheory.FlagMod.ev z _ hg ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).g
      (i, flagIdx M _ k) (i', flagIdx M _ k')).val * x') := by
  intro _ P Q t v zv O hO g hz hzv hk hQ ht hv hl
  have ho : ⊤ ≤ z ⁻¹ᵁ M.off := fun p hp => (hs hp).1
  have hi' : ⊤ ≤ z ⁻¹ᵁ M.K.bundle.U i' := fun p hp => (hs' hp).2.1
  have hK : ⊤ ≤ z ⁻¹ᵁ (M.K.bundle.U i ⊓ M.K.bundle.U i') := fun p hp => ⟨(hs hp).2.1, (hs' hp).2.1⟩
  have hk' : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k' := fun p hp => mem_pIdx.1 (mem_pIdx.1 (hs' hp).2.2)
  have hh : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k') := GlobalTheory.FlagMod.le_preimage_inf hk hk'
  have hlies := hQ.lies
  obtain ⟨Q', hQ'⟩ := X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd Q) hlies.1 k' hk'
  obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K
  have hB := hQ.frBor hQ' hh
  have ht' := g1 _ _ _ _ _ (g2 _ _ _ hB) ht
  have hP : z ≫ toFlag M = X.ptY P := FlagCover.eq_ptY (hlies.frBor ht)
  have hzv' : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ (O ⊓ M.K.bundle.U i') := fun b =>
    GlobalTheory.FlagMod.le_preimage_inf (hzv b) (top_le_of_isDef M z ho hP (hv.isDef b) (zv b) (hl b) hi')
  have hz' : ⊤ ≤ z ⁻¹ᵁ (O ⊓ M.K.bundle.U i') := GlobalTheory.FlagMod.le_preimage_inf hz hi'
  have key := hx' P Q' _ v zv (O ⊓ M.K.bundle.U i') inf_le_right (fun a => resG M.X inf_le_left (g a)) hz' hzv' hk'
    hQ' ht' hv hl
  have hdet : (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) (O ⊓ M.K.bundle.U i') (hzv' _)
      (resG M.X inf_le_left (g a))).snd) = Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd := by
    ext a b
    simp only [Matrix.of_apply]
    rw [evalPt_res]
  rw [hdet] at key
  have hJ : evalPt z O hz (M.K.jacobian i hO g) = GlobalTheory.FlagMod.ev z _ hK (M.K.bundle.g i i').val *
      evalPt z (O ⊓ M.K.bundle.U i') hz' (M.K.jacobian i' inf_le_right fun a => resG M.X inf_le_left (g a)) := by
    rw [← evalPt_res z inf_le_left hz hz', CanonLB.resG_jacobian,
      CanonLB.jacobian_change _ i i' (inf_le_left.trans hO) inf_le_right, map_mul]
    congr 1
    exact evalPt_res z _ hK hz' _
  rw [ev_div_g M i i' k k' z hg hK hh, hJ]
  have hu : (∏ ix, ((X.F.TAt k k' (z ≫ toFlag M) hh)⁻¹ * t) ix ^ exOf Dw (FlagTan.kap Dw) 0 ix) =
      (∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ exOf Dw (FlagTan.kap Dw) 0 ix)⁻¹ *
        ∏ ix, t ix ^ exOf Dw (FlagTan.kap Dw) 0 ix := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ix _ => ?_
    rw [Pi.mul_apply, Pi.inv_apply, mul_zpow, inv_zpow]
  rw [hu, Units.val_mul] at key
  have hTT := Units.mul_inv (∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ exOf Dw (FlagTan.kap Dw) 0 ix)
  linear_combination (GlobalTheory.FlagMod.ev z _ hK (M.K.bundle.g i i').val *
      ((∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ exOf Dw (FlagTan.kap Dw) 0 ix : Kˣ) : K)) * key +
    ((∏ ix, t ix ^ exOf Dw (FlagTan.kap Dw) 0 ix : Kˣ) : K) * GlobalTheory.FlagMod.ev z _ hK (M.K.bundle.g i i').val *
      evalPt z (O ⊓ M.K.bundle.U i') hz' (M.K.jacobian i' inf_le_right fun a => resG M.X inf_le_left (g a)) * hTT

end GlobalTheory.CompHS


open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS in
theorem GlobalTheory.CompHS.ksRel_change : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (i i' : M.K.bundle.ι) (k k' : X.F.J) (K : Type) [Field K] (z : Sp K ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ ksOpen M i k → ⊤ ≤ z ⁻¹ᵁ ksOpen M i' k' → ∀ (hg : ⊤ ≤ z ⁻¹ᵁ ((LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k) ⊓ (LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).U (i', flagIdx M _ k'))) (x x' : K), KSRel M i k z x → KSRel M i' k' z x' → x = GlobalTheory.FlagMod.ev z _ hg ((LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).g (i, flagIdx M _ k) (i', flagIdx M _ k')).val * x' := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS i i' k k' K _ z hs hs' hg x x' hx hx'
  exact (GlobalTheory.T.kodairaSpencer_coordinate_unique_ne_zero M hKS i k K z hs).1 x _ hx (ksRel_of_ksRel M hs hs' hg hx')
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerCoordsTwoChartsTransitionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencerCoords_two_charts_transition : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (i i' : M.K.bundle.ι) (k k' : X.F.J) (K : Type) [Field K] (z : Sp K ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ ksOpen M i k → ⊤ ≤ z ⁻¹ᵁ ksOpen M i' k' → ∀ (hg : ⊤ ≤ z ⁻¹ᵁ ((LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k) ⊓ (LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).U (i', flagIdx M _ k'))) (x x' : K), KSRel M i k z x → KSRel M i' k' z x' → x = GlobalTheory.FlagMod.ev z _ hg ((LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).g (i, flagIdx M _ k) (i', flagIdx M _ k')).val * x' := by
  first | exact @GlobalTheory.CompHS.ksRel_change | exact GlobalTheory.CompHS.ksRel_change | (intros; apply GlobalTheory.CompHS.ksRel_change <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKodairaSpencerIdentificationOffBoundary
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame KSIso)

theorem isUnit_ger_of_ev {Z : Scheme.{0}} {V : Z.Opens} (a : Γ(Z, V)) (y : Z) (hy : y ∈ V)
    (h : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), GlobalTheory.FlagMod.ev z V hz a ≠ 0) :
    IsUnit (ger y hy a) := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open hy V.isOpen
  have hWV : W ≤ V := hWV
  replace hW : IsAffineOpen W := hW
  let p := hW.primeIdealOf ⟨y, hyW⟩
  have hne := h p.asIdeal.ResidueField (spMap (algebraMap Γ(Z, W) p.asIdeal.ResidueField) ≫ GlobalTheory.FlagMod.tau hW)
    (GlobalTheory.FlagMod.le_preimage_comp _ (GlobalTheory.FlagMod.tau_le hW hWV))
  rw [← GlobalTheory.FlagMod.ev_res _ hWV (GlobalTheory.FlagMod.le_preimage_comp _ (GlobalTheory.FlagMod.tau_le hW le_rfl)),
    GlobalTheory.FlagMod.ev_spMap_tau] at hne
  have hnm : resG Z hWV a ∈ p.asIdeal.primeCompl := fun hm => hne (Ideal.algebraMap_residueField_eq_zero.2 hm)
  letI := Z.presheaf.algebra_section_stalk (⟨y, hyW⟩ : W)
  have := hW.isLocalization_stalk ⟨y, hyW⟩
  have hu := (IsLocalization.AtPrime.isUnit_to_map_iff (Z.presheaf.stalk y) p.asIdeal (resG Z hWV a)).2 hnm
  rw [← ger_resG hWV y hyW]
  exact hu

theorem canId_nonempty : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F))
    (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)),
    (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) →
    Nonempty (CanId M) := by
  intro hdR E _ _ _ H Dw l Xo c Y X Z M hKS
  haveI : Smooth M.str := SmoothOfRelativeDimension.smooth (dimFlag Dw) M.str
  haveI : IsReduced M.X := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isReduced_of_smooth M.str
  have hBLB : (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).IsLB :=
    LB.isLB_div M.K.isLB (LB.isLB_pull ((common₀ X Z).isLB _) M.σ)
  have hloc : ∀ t : M.K.bundle.ι × X.F.J, ∃ a : Γ(M.X, ksOpen M t.1 t.2), ∀ (K : Type) [Field K]
      (z : Sp K ⟶ M.X) (hz : ⊤ ≤ z ⁻¹ᵁ ksOpen M t.1 t.2), KSRel M t.1 t.2 z (GlobalTheory.FlagMod.ev z _ hz a) := fun t =>
    GlobalTheory.FlagMod.glue_field (ksOpen M t.1 t.2) (fun L _ z x => KSRel M t.1 t.2 z x)
      (fun L _ z hz x y hx hy => (GlobalTheory.T.kodairaSpencer_coordinate_unique_ne_zero M hKS t.1 t.2 L z hz).1 x y hx hy)
      (fun W hW hle => GlobalTheory.T.exists_regular_kodairaSpencerCoordinate_affine_off_boundary M hdR hKS t.1 t.2 W hW hle)
  choose a ha using hloc
  have cover : ∀ y ∈ M.off, ∃ t : M.K.bundle.ι × X.F.J, y ∈ ksOpen M t.1 t.2 := by
    intro y hy
    obtain ⟨i, hi⟩ := exists_chart M.K.isLB y
    obtain ⟨k, hk⟩ := ((common₀ X Z).pull M.σ).cover y
    exact ⟨(i, k), hy, hi, (((common₀ X Z).pull M.σ).mem _ k y).2 hk⟩
  have rule : ∀ (y : M.X) (t t' : M.K.bundle.ι × X.F.J) (h : y ∈ ksOpen M t.1 t.2) (h' : y ∈ ksOpen M t'.1 t'.2),
      ger y h (a t) = (tr (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) y (t.1, flagIdx M _ t.2)
        (t'.1, flagIdx M _ t'.2) : _) * ger y h' (a t') := by
    intro y t t' h h'
    have hle : ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2 ≤
        (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (t.1, flagIdx M _ t.2) ⊓
          (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (t'.1, flagIdx M _ t'.2) :=
      fun q hq => ⟨hq.1.2, hq.2.2⟩
    rw [val_tr _ y (hle ⟨h, h'⟩)]
    have e : resG M.X (inf_le_left : ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2 ≤ _) (a t) =
        resG M.X hle ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).g (t.1, flagIdx M _ t.2)
          (t'.1, flagIdx M _ t'.2)).val * resG M.X inf_le_right (a t') := by
      refine GlobalTheory.FlagMod.ext_ev_field fun L _ z hz => ?_
      have h1 := GlobalTheory.FlagMod.le_preimage_mono inf_le_left hz
      have h2 := GlobalTheory.FlagMod.le_preimage_mono inf_le_right hz
      have hg := GlobalTheory.FlagMod.le_preimage_mono hle hz
      rw [map_mul, GlobalTheory.FlagMod.ev_res z _ hz h1, GlobalTheory.FlagMod.ev_res z _ hz h2, GlobalTheory.FlagMod.ev_res z _ hz hg]
      exact GlobalTheory.T.kodairaSpencerCoords_two_charts_transition M hKS t.1 t'.1 t.2 t'.2 L z h1 h2 hg _ _ (ha t L z h1) (ha t' L z h2)
    have := congrArg (ger y (⟨h, h'⟩ : y ∈ ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2)) e
    have e1 := ger_resG (inf_le_left : ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2 ≤ _) y ⟨h, h'⟩ (a t)
    have e2 := ger_resG (inf_le_right : ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2 ≤ _) y ⟨h, h'⟩ (a t')
    have e3 := ger_resG hle y ⟨h, h'⟩ ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).g (t.1, flagIdx M _ t.2)
          (t'.1, flagIdx M _ t'.2)).val
    rw [map_mul, e1, e2, e3] at this
    exact this
  obtain ⟨f, hf⟩ := H0.exists_of_germs (p := M.str) (O := M.off) hBLB
    (fun t : M.K.bundle.ι × X.F.J => ksOpen M t.1 t.2) (fun t => (t.1, flagIdx M _ t.2))
    (fun t => inf_le_left) (fun t => inf_le_right) cover a rule
  have hloc' : ∀ i k, f.loc (i, flagIdx M _ k) = a (i, k) := fun i k =>
    fun_ext_ger fun y hy => (H0.germ_apply _ y hy.1 hy.2 f).symm.trans (hf (i, k) y hy)
  refine ⟨⟨f, nowhereZero_of_exists fun y hy => ?_, (isKS_iff_ksRel M f).2 @fun K _ z i k ho hi => ?_⟩⟩
  · obtain ⟨t, ht⟩ := cover y hy
    refine ⟨(t.1, flagIdx M _ t.2), ht.2, ?_⟩
    rw [hf t y ht]
    exact isUnit_ger_of_ev (a t) y ht fun L _ z hz => (GlobalTheory.T.kodairaSpencer_coordinate_unique_ne_zero M hKS t.1 t.2 L z hz).2 _ (ha t L z hz)
  · have hk : KSRel M i k z (GlobalTheory.FlagMod.ev z (ksOpen M i k) (GlobalTheory.FlagMod.le_preimage_inf ho hi) (a (i, k))) :=
      ha (i, k) K z (GlobalTheory.FlagMod.le_preimage_inf ho hi)
    have e : H0.val (B := LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi f =
        GlobalTheory.FlagMod.ev z (ksOpen M i k) (GlobalTheory.FlagMod.le_preimage_inf ho hi) (a (i, k)) := by
      rw [← hloc' i k]
      rfl
    rw [e]
    exact @hk

end GlobalTheory.CompHS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKodairaSpencerIdentificationOffBoundaryStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_kodairaSpencer_identification_offBoundary : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → Nonempty (CanId M) := by
  first | exact @GlobalTheory.CompHS.canId_nonempty | exact GlobalTheory.CompHS.canId_nonempty | (intros; apply GlobalTheory.CompHS.canId_nonempty <;> assumption)
end
