module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeAlongKodairaSpencerDeformationLift

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeAlongVerticalDeformationLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SndEvalPtDir
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod
open GlobalTheory.FlagTan (dimFlag)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

theorem primeSpectrum_trivSqZeroExt_eq {L M : Type} [Field L] [AddCommGroup M] [Module L M] [Module Lᵐᵒᵖ M]
    [IsCentralScalar L M] (x y : PrimeSpectrum (TrivSqZeroExt L M)) : x = y := by
  have h : ∀ z : PrimeSpectrum (TrivSqZeroExt L M), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  ext a
  rw [h, h]

theorem le_preimage_of_reduction {R L : Type} [CommRing R] [Field L] (hR : ∀ a b : PrimeSpectrum R, a = b)
    (φ : R →+* L) {T : Scheme.{0}} (x : Sp R ⟶ T) (V : T.Opens) (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  have hp : (spMap φ) (IsLocalRing.closedPoint L) = s := hR _ _
  have h₁ : (spMap φ ≫ x) (IsLocalRing.closedPoint L) ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

theorem le_preimage_of_comp {R S : Type} [CommRing R] [CommRing S] (hR : ∀ a b : PrimeSpectrum R, a = b)
    (φ : R →+* S) (s₀ : Sp S) {T : Scheme.{0}} (x : Sp R ⟶ T) (V : T.Opens) (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) :
    ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  have hp : (spMap φ) s₀ = s := hR _ _
  have h₁ : (spMap φ ≫ x) s₀ ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}

theorem exists_thickLift (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K]
    {ι : Type} [Fintype ι] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {Q : FrPt Xo c K} (hz : z ≫ toFlag M = X.ptY Q)
    {W : FrPt Xo c (TrivSqZeroExt K (ι → K))} (hW : FrMap (TrivSqZeroExt.fstHom c.F K (ι → K)) W Q) :
    ∃ ZW : Sp (TrivSqZeroExt K (ι → K)) ⟶ M.X, ZW ≫ toFlag M = X.ptY W ∧
      ∀ (m : ι → K) (x : Sp (DualNumber K) ⟶ M.X),
        x ≫ toFlag M = spMap (GlobalTheory.FlagTan.dir c m).toRingHom ≫ X.ptY W →
          x = spMap (GlobalTheory.FlagTan.dir c m).toRingHom ≫ ZW := by
  have hred : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X.ptY W = X.ptY Q := X.ptY_frMap hW
  have hpt : ∀ a b : PrimeSpectrum (TrivSqZeroExt K (ι → K)), a = b := primeSpectrum_trivSqZeroExt_eq
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hb : ⊤ ≤ X.ptY W ⁻¹ᵁ (inc₀ X Z).opensRange :=
    le_preimage_of_reduction hpt (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom _ _ (by
      rw [hred, ← hz]
      rintro s -
      exact ⟨(z ≫ M.σ) s, rfl⟩)
  have hr : Set.range (X.ptY W) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    exact hb (Set.mem_univ s)
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, w₁ ≫ inc₀ X Z = X.ptY W := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have ered : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ w₁ = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw₁, hred, ← hz, Category.assoc]
  have hwU : ⊤ ≤ w₁ ⁻¹ᵁ U₀ X Z := le_preimage_of_reduction hpt _ _ _ (by rw [ered]; exact hU)
  obtain ⟨ZW, hZW, -⟩ := M.existsUnique_lift w₁ hwU
  refine ⟨ZW, by rw [toFlag, ← Category.assoc, hZW, hw₁], fun m x hx => ?_⟩
  have hxU : ⊤ ≤ (spMap (GlobalTheory.FlagTan.dir c m).toRingHom ≫ w₁) ⁻¹ᵁ U₀ X Z := fun s _ => hwU (Set.mem_univ _)
  refine (M.existsUnique_lift _ hxU).unique ?_ (by rw [Category.assoc, hZW])
  rw [← cancel_mono (inc₀ X Z), Category.assoc, Category.assoc, hw₁, ← hx]

theorem snd_evalPt_dir {K : Type} [Field K] [Algebra c.F K] {ι : Type} [Fintype ι] {T : Scheme.{0}}
    (ZW : Sp (TrivSqZeroExt K (ι → K)) ⟶ T) (O : T.Opens) (hO : ⊤ ≤ ZW ⁻¹ᵁ O) (m : ι → K)
    (x : Sp (DualNumber K) ⟶ T) (hx : ⊤ ≤ x ⁻¹ᵁ O) (e : x = spMap (GlobalTheory.FlagTan.dir c m).toRingHom ≫ ZW) (g : Γ(T, O)) :
    (evalPt x O hx g).snd = ∑ k, (evalPt ZW O hO g).snd k * m k := by
  subst e
  rw [evalPt_spMap_comp (GlobalTheory.FlagTan.dir c m).toRingHom ZW O hO hx g]
  exact GlobalTheory.FlagTan.snd_dir m _

end GlobalTheory.CompHS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeAlongVerticalDeformationLift
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}


open GlobalTheory.FlagTan in
theorem der_fun_ver (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K]
    (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {Q : FrPt Xo c K} (hz : z ≫ toFlag M = X.ptY Q)
    {v : VIx Dw → FrPt Xo c (DualNumber K)} (hv : ∀ k : VIx Dw, IsVert Q (Pi.single k.toF (1 : K)) (v k))
    {zv : VIx Dw → (Sp (DualNumber K) ⟶ M.X)} (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b))
    {w : FrPt Xo c (DualNumber K)} {N : FIx Dw → K} (hw : IsVert Q N w)
    {zw : Sp (DualNumber K) ⟶ M.X} (hlw : zw ≫ toFlag M = X.ptY w)
    (O : M.X.Opens) (g : Γ(M.X, O)) (hzw : ⊤ ≤ zw ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O) :
    (evalPt zw O hzw g).snd = ∑ k : VIx Dw, N k.toF * (evalPt (zv k) O (hzv _) g).snd := by
  choose vp hvp using fun m : FIx Dw → K => (existsUnique_isVert Q m).exists
  obtain ⟨y₀, h₀⟩ := GlobalTheory.FlagTan.exists_frMap (cst c K) Q
  obtain ⟨W₀, hW₀⟩ := GlobalTheory.FlagTan.exists_frMap (TrivSqZeroExt.inlAlgHom c.F K (FIx Dw → K)) Q
  let n : FIx Dw → FIx Dw → K := fun k => Pi.single k 1
  obtain ⟨W, hW, -⟩ :=
    GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ W₀ _ (isUnit_unip₀ (K := K) n).unit (isUnit_det_unip n)

  have hWm : ∀ m, FrMap (dir c m) W (vp m) := fun m => by
    obtain ⟨y₁, h₁, hs⟩ := hvp m
    obtain rfl := GlobalTheory.FlagTan.frMap_unique h₁ h₀
    refine (GlobalTheory.FlagTan.frMap_iff_frChg hW (GlobalTheory.FlagTan.frMap_of_comp hW₀ h₀ fun a => by ext <;> simp)).2 ?_
    unfold IsShift at hs
    convert hs using 2 with τ
    · ext i j <;> simp [unip, n, Pi.single_apply]
    · ext <;> simp [unip₀, n, Pi.single_apply]
  have hP : ∀ m, spMap (dir c m).toRingHom ≫ X.ptY W = X.ptY (vp m) := fun m => X.ptY_frMap (hWm m)
  obtain ⟨ZW, hZf, huniq⟩ := exists_thickLift M z ho hz
    (GlobalTheory.FlagTan.frMap_comp (hWm 0) (hvp 0).isDef fun a => by simp)
  have huniq' : ∀ m (x : Sp (DualNumber K) ⟶ M.X), x ≫ toFlag M = X.ptY (vp m) →
      x = spMap (dir c m).toRingHom ≫ ZW := fun m x hx => huniq m x (hx.trans (hP m).symm)
  have ew : zw = spMap (dir c N).toRingHom ≫ ZW :=
    huniq' N zw (by rw [hlw, (existsUnique_isVert Q N).unique hw (hvp N)])
  have hZO : ⊤ ≤ ZW ⁻¹ᵁ O :=
    le_preimage_of_comp primeSpectrum_trivSqZeroExt_eq (dir c N).toRingHom
      ((spMap (red c K).toRingHom) (IsLocalRing.closedPoint K)) ZW O (ew ▸ hzw)

  have hflag : ∀ N' : FIx Dw → K, (∀ σ i j, i < j → N' (some ⟨σ, i, j⟩) = 0) → X.ptY (vp N') = X.ptY y₀ :=
    fun N' hN' => by
      obtain ⟨y₁, h₁, hs⟩ := hvp N'
      obtain rfl := GlobalTheory.FlagTan.frMap_unique h₁ h₀
      exact (X.ptY_frBor (t := fun k => oneAddEps (Multiplicative.ofAdd (diagOf N' k)))
        ((GlobalTheory.Frames.frBor_iff_frChg _ _ _).2 ⟨unip K N', fun σ i j hij => by
          simp [unip, hN' σ i j hij, hij.ne], fun _ _ => by simp [unip, oneAddEps, diagOf], hs⟩)).symm
  have h0 : ∀ j : FIx Dw, j ∉ Set.range VIx.toF → (evalPt ZW O hZO g).snd j = 0 := fun j hj => by
    have hx : ⊤ ≤ (spMap (dir c (Pi.single j 1)).toRingHom ≫ ZW) ⁻¹ᵁ O := fun s _ => hZO (Set.mem_univ _)
    have e1 := huniq 0 (spMap (dir c (Pi.single j 1)).toRingHom ≫ ZW) (by
      rw [Category.assoc, hZf, hP, hP, hflag _ (fun σ i j' hij => Pi.single_eq_of_ne (by
        rintro rfl
        exact hj ⟨⟨σ, (i, j'), hij⟩, rfl⟩) _), hflag 0 fun _ _ _ _ => rfl])
    have a1 := snd_evalPt_dir ZW O hZO (Pi.single j 1) _ hx rfl g
    have a2 := snd_evalPt_dir ZW O hZO 0 _ hx e1 g
    simpa [Pi.single_apply] using a1.symm.trans a2
  have hk : ∀ k : VIx Dw, (evalPt (zv k) O (hzv k) g).snd = (evalPt ZW O hZO g).snd k.toF := fun k => by
    rw [snd_evalPt_dir ZW O hZO _ _ _
      (huniq' _ _ ((hl k).trans (congrArg X.ptY ((existsUnique_isVert Q _).unique (hv k) (hvp _))))) g]
    simp [Pi.single_apply]
  rw [snd_evalPt_dir ZW O hZO N zw hzw ew g]
  simp only [hk]
  have hz0 : ∑ k ∈ Finset.univ.filter (fun k => k ∉ Set.range VIx.toF), (evalPt ZW O hZO g).snd k * N k = 0 :=
    Finset.sum_eq_zero fun k hk => by rw [h0 k (Finset.mem_filter.1 hk).2, zero_mul]
  rw [sum_FIx, hz0, add_zero]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end GlobalTheory.CompHS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeAlongVerticalDeformationLiftStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_along_vertical_deformation_lift : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {Q : FrPt Xo c K} (hz : z ≫ toFlag M = X.ptY Q)
    {v : VIx Dw → FrPt Xo c (DualNumber K)} (hv : ∀ k : VIx Dw, IsVert Q (Pi.single k.toF (1 : K)) (v k))
    {zv : VIx Dw → (Sp (DualNumber K) ⟶ M.X)} (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b))
    {w : FrPt Xo c (DualNumber K)} {N : GlobalTheory.FlagTan.FIx Dw → K} (hw : IsVert Q N w)
    {zw : Sp (DualNumber K) ⟶ M.X} (hlw : zw ≫ toFlag M = X.ptY w)
    (O : M.X.Opens) (g : Γ(M.X, O)) (hzw : ⊤ ≤ zw ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O), (evalPt zw O hzw g).snd = ∑ k : VIx Dw, N k.toF * (evalPt (zv k) O (hzv _) g).snd := by
  first | exact @GlobalTheory.CompHS.der_fun_ver | exact GlobalTheory.CompHS.der_fun_ver | (intros; apply GlobalTheory.CompHS.der_fun_ver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqProdDiagOfHeight
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Frames GlobalTheory.AllWt
open Formalism.L2.Pj hiding conjEmb_conjEmb
open TrivSqZeroExt hiding map lift
open scoped Classical

namespace GlobalTheory.FlagTan

theorem det_eq_prod_diag_of_height {m R : Type} [Fintype m] [DecidableEq m] [CommRing R] (P : Matrix m m R)
    (b : m → ℤ) (h : ∀ k j, P k j ≠ 0 → k = j ∨ b j < b k) : P.det = ∏ k, P k k := by
  rw [Matrix.det_apply, Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    suffices ∏ i, P (σ i) i = 0 by rw [this, smul_zero]
    by_contra hne
    have h1 : ∀ i, P (σ i) i ≠ 0 := fun i hi => hne (Finset.prod_eq_zero (Finset.mem_univ i) hi)
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
      by_contra hc
      exact hσ (Equiv.ext fun i => by_contra fun k => hc ⟨i, k⟩)
    have := Finset.sum_lt_sum (s := Finset.univ) (f := b) (g := fun i => b (σ i))
      (fun j _ => (h _ _ (h1 j)).elim (fun e => by rw [e]) le_of_lt)
      ⟨i, Finset.mem_univ _, (h _ _ (h1 i)).resolve_left hi⟩
    rw [Equiv.sum_comp σ b] at this
    exact lt_irrefl _ this
  · simp

theorem prod_pairs_lt {G : Type} [CommGroup G] {n : ℕ} (x : Fin n → G) :
    ∏ q : {q : Fin n × Fin n // q.1 < q.2}, ((x q.1.1)⁻¹ * x q.1.2) =
      ∏ i, x i ^ (((Finset.Iio i).card : ℤ) - (Finset.Ioi i).card) := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun q : Fin n × Fin n => q.1 < q.2) (by simp)
    (fun q => (x q.1)⁻¹ * x q.2), Finset.prod_mul_distrib, Finset.prod_filter, Finset.prod_filter,
    Fintype.prod_prod_type, Fintype.prod_prod_type_right, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  dsimp only
  rw [← Finset.prod_filter, ← Finset.prod_filter, Finset.prod_const, Finset.prod_const, zpow_sub, mul_comm]
  simp only [zpow_natCast, inv_pow, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem IsHalf.prod_univ {Φ : Finset (E →+* ℂ)} (h : IsHalf Φ) {G : Type} [CommMonoid G] (g : (E →+* ℂ) → G) :
    ∏ σ, g σ = ∏ τ ∈ Φ, (g τ * g (conjEmb τ)) := by
  rw [Finset.prod_mul_distrib, ← Finset.prod_mul_prod_compl Φ]
  congr 1
  refine Finset.prod_bij' (fun σ _ => conjEmb σ) (fun σ _ => conjEmb σ) (fun σ hσ => ?_) (fun σ hσ => ?_)
    (fun σ _ => conjEmb_conjEmb σ) (fun σ _ => conjEmb_conjEmb σ) fun σ _ => by rw [conjEmb_conjEmb]
  · rw [h, conjEmb_conjEmb]; exact Finset.mem_compl.1 hσ
  · exact Finset.mem_compl.2 ((h σ).1 hσ)

theorem prod_char_eq {Φ : Finset (E →+* ℂ)} (h : IsHalf Φ) {G : Type} [CommGroup G] (t : Ix Dw → G) :
    (∏ k : HIx Dw Φ, (t (some ⟨conjEmb k.1.1, k.2.1⟩) * t (some ⟨k.1.1, k.2.2⟩))) *
      ∏ k : VIx Dw, ((t (some ⟨k.1, k.2.1.1⟩))⁻¹ * t (some ⟨k.1, k.2.1.2⟩)) = ∏ k, t k ^ detTanEx Dw k := by
  have e1 : ∏ k : HIx Dw Φ, (t (some ⟨conjEmb k.1.1, k.2.1⟩) * t (some ⟨k.1.1, k.2.2⟩)) =
      ∏ σ, ∏ i, t (some ⟨σ, i⟩) ^ Dw.mult (conjEmb σ) := by
    rw [h.prod_univ, Fintype.prod_sigma, ← Finset.prod_coe_sort Φ]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Fintype.prod_prod_type, conjEmb_conjEmb]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_pow]
    exact mul_comm _ _
  rw [e1, Fintype.prod_sigma, Fintype.prod_option, Fintype.prod_sigma, ← Finset.prod_mul_distrib]
  simp only [detTanEx, zpow_zero, one_mul]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [prod_pairs_lt fun i => t (some ⟨σ, i⟩), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [zpow_add, zpow_natCast, mul_comm]

variable {K : Type} [Field K] [Algebra c.F K] {K₀ : Type} [CommRing K₀] [Algebra c.F K₀] {ι : Type} [Fintype ι]

theorem exists_move {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K} {a : K}
    {y y' : FrPt Xo c K} (h : FrChg g a y y') {v' : FrPt Xo c (DualNumber K)} (hv : IsDef y' v') :
    ∃ w, IsDef y w ∧ FrChg (fun τ => (g τ).map (cst c K)) (cst c K a) w v' := by
  obtain ⟨g', a', hg', h'⟩ := (frChg_exists_unique E H Dw l Xo c K y' y).1 h.1.symm
  have C := frChg_calculus E H Dw l Xo c K
  have D := frChg_calculus E H Dw l Xo c (DualNumber K)
  obtain ⟨e, e'⟩ := (frChg_exists_unique E H Dw l Xo c K y' y').2 _ _ _ _ ((C.1 _ _ _ _ _ _ _ h').1 h) (C.2.1 y')
  obtain ⟨w, hw, -⟩ := existsUnique_frChg E H Dw l Xo c _ v' (fun τ => (g' τ).map (cst c K))
    (Units.map (cst c K).toRingHom.toMonoidHom a') fun τ => by
      have := (hg' τ).map (cst c K).toRingHom
      rwa [RingHom.map_det] at this
  refine ⟨w, (frMap_iff_frChg hw hv).2 ?_, (D.1 _ _ _ _ _ _ _ hw).2 ?_⟩
  · convert h' using 2 with τ
    · ext i j; simp
    · rfl
  · convert D.2.1 v' using 2 with τ
    · rw [← Matrix.map_mul, congrFun e τ, Matrix.map_one _ (map_zero _) (map_one _)]
    · exact (map_mul (cst c K) a a').symm.trans (by rw [e', map_one])

theorem isVert_move {g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K} {a : Kˣ}
    {y y' : FrPt Xo c K} (h : FrChg g a y y') (hg : ∀ τ, g τ * g' τ = 1) {N : FIx Dw → K}
    {w v' : FrPt Xo c (DualNumber K)} (hv : IsVert y' N v')
    (hw : FrChg (fun τ => (g τ).map (cst c K)) (cst c K a) w v') :
    IsVert y (fun k => k.elim (N none) fun q =>
      (g' q.1 * (Matrix.of fun i j => N (some ⟨q.1, i, j⟩)) * g q.1) q.2.1 q.2.2) w := by
  have D := frChg_calculus E H Dw l Xo c (DualNumber K)
  obtain ⟨y₀', h₀', hs⟩ := hv
  obtain ⟨y₀, h₀⟩ := exists_frMap (cst c K) y
  have k1 := (D.1 _ _ _ _ _ _ _ ((frMap_iff_frChg h h₀).1 h₀')).1 hs
  obtain ⟨w', hw', -⟩ := existsUnique_isShift (fun k : FIx Dw => k.elim (N none) fun q =>
      (g' q.1 * (Matrix.of fun i j => N (some ⟨q.1, i, j⟩)) * g q.1) q.2.1 q.2.2) y₀
  have k2 : FrChg (fun τ => (g τ).map (cst c K)) (cst c K a) w' v' := by
    refine (D.1 _ _ _ _ _ _ _ hw').2 ?_
    convert (preTransparency := .reducible) k1 using 1
    · funext τ
      have : g τ * (g' τ * (Matrix.of fun i j => N (some ⟨τ, i, j⟩)) * g τ) =
          (Matrix.of fun i j => N (some ⟨τ, i, j⟩)) * g τ := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg, Matrix.one_mul]
      ext i j
      · simp [unip, Matrix.mul_apply, fst_sum, Matrix.one_apply]
      · have := congrFun (congrFun this i) j
        rw [Matrix.mul_apply, Matrix.mul_apply] at this
        simpa [unip, Matrix.mul_apply (M := Matrix.map _ _), Matrix.mul_apply (N := Matrix.map _ _), snd_sum] using this
    · ext <;> simp [unip₀, mul_comm]
  obtain ⟨G, A, -, k3⟩ := (frChg_exists_unique E H Dw l Xo c _ v' w).1 hw.1.symm
  obtain ⟨e, e'⟩ := (frChg_exists_unique E H Dw l Xo c _ w w).2 _ _ _ _ ((D.1 _ _ _ _ _ _ _ hw).1 k3) (D.2.1 w)
  have k4 := (D.1 _ _ _ _ _ _ _ k2).1 k3
  rw [e, e'] at k4
  obtain rfl : w = w' :=
    (existsUnique_frChg E H Dw l Xo c _ w' (fun _ => 1) 1 fun _ => by simp).unique k4 (D.2.1 w')
  exact ⟨y₀, h₀, hw'⟩

end GlobalTheory.FlagTan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDerivativesBorelFrameChangeCanonicalWeight
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlagTan

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Frames GlobalTheory.AllWt
open Formalism.L2.Pj hiding conjEmb_conjEmb
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {K : Type} [Field K]

def movedVert (g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) (k : VIx Dw) : FIx Dw → K :=
  fun x => x.elim ((Pi.single k.toF (1 : K) : FIx Dw → K) none) fun q =>
    (g' q.1 * (Matrix.of fun i j => (Pi.single k.toF (1 : K) : FIx Dw → K) (some ⟨q.1, i, j⟩)) * g q.1) q.2.1 q.2.2

theorem det_moved {Φ : Finset (E →+* ℂ)} (hΦ : IsHalf Φ) {t : Ix Dw → Kˣ}
    {g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K}
    (hg : ∀ τ i j, i < j → g τ i j = 0) (hd : ∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : K))
    (hg' : ∀ τ i j, i < j → g' τ i j = 0) (hd' : ∀ τ i, g' τ i i = ((t (some ⟨τ, i⟩))⁻¹ : Kˣ)) :
    (Matrix.of fun k => ksChg Φ g (Pi.single k 1)).det *
      (Matrix.of fun k j : VIx Dw => movedVert g g' k j.toF).det =
      ((∏ k, t k ^ exOf Dw (kap Dw) 0 k : Kˣ) : K) := by
  have eM : ∀ k j : HIx Dw Φ, ksChg Φ g (Pi.single k 1) j ≠ 0 →
      k = j ∨ ((j.2.1 : ℤ) + j.2.2 < (k.2.1 : ℤ) + k.2.2) := by
    rintro k ⟨τ, a, b⟩ hne
    rw [ksChg_apply] at hne
    obtain ⟨a', -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨b', -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain rfl : ⟨τ, a', b'⟩ = k := by
      by_contra hk
      simp [Pi.single_eq_of_ne hk] at hne
    have h1 : ¬ a' < a := fun k => by simp [hg _ _ _ k] at hne
    have h2 : ¬ b' < b := fun k => by simp [hg _ _ _ k] at hne
    by_cases h3 : a' = a ∧ b' = b
    · left; rw [h3.1, h3.2]
    · right
      simp only [Fin.ext_iff, Fin.lt_def] at h1 h2 h3 ⊢
      omega
  have dM : ∀ k : HIx Dw Φ, ksChg Φ g (Pi.single k 1) k =
      ((t (some ⟨conjEmb k.1.1, k.2.1⟩) * t (some ⟨k.1.1, k.2.2⟩) : Kˣ) : K) := by
    rintro ⟨τ, a, b⟩
    simp [ksChg_apply, Pi.single_apply, hd, ite_and]
  have fN : ∀ (k : VIx Dw) (σ : E →+* ℂ) (i j : Fin (Dw.mult σ)),
      (g' σ * (Matrix.of fun i j => (Pi.single k.toF (1 : K) : FIx Dw → K) (some ⟨σ, i, j⟩)) * g σ) i j =
      ∑ a, ∑ b, g' σ i a * (Pi.single k.toF (1 : K) : FIx Dw → K) (some ⟨σ, a, b⟩) * g σ b j := fun k σ i j => by
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [det_eq_prod_diag_of_height _ (fun k => (k.2.1 : ℤ) + k.2.2) eM,
    det_eq_prod_diag_of_height (m := VIx Dw) _ (fun k => (k.2.1.2 : ℤ) - k.2.1.1)]
  · rw [exOf_kap, ← prod_char_eq hΦ, Units.val_mul, Units.coe_prod, Units.coe_prod]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => dM k)
      (Finset.prod_congr rfl fun ⟨σ, ⟨i, j⟩, hij⟩ _ => (fN _ σ i j).trans ?_)
    simp [VIx.toF, Pi.single_apply, hd, hd', ite_and]
  · rintro ⟨σ', ⟨i', j'⟩, hij'⟩ ⟨σ, ⟨i, j⟩, hij⟩ hne
    have hne := fun e => hne ((fN _ σ i j).trans e)
    obtain ⟨a, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨b, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have e : (some ⟨σ, a, b⟩ : FIx Dw) = some ⟨σ', i', j'⟩ := by
      by_contra hk
      exact hne (by rw [VIx.toF, Pi.single_eq_of_ne hk, mul_zero, zero_mul])
    obtain ⟨rfl, e⟩ := Sigma.mk.inj_iff.1 (Option.some.inj e)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq e)
    have h1 : ¬ i < a := fun k => by simp [hg' _ _ _ k] at hne
    have h2 : ¬ b < j := fun k => by simp [hg _ _ _ k] at hne
    by_cases h3 : a = i ∧ b = j
    · left; obtain ⟨rfl, rfl⟩ := h3; rfl
    · right
      simp only [Fin.ext_iff, Fin.lt_def] at h1 h2 h3 ⊢
      omega

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F K]

theorem exists_moved_defs {Φ : Finset (E →+* ℂ)} (hΦ : IsHalf Φ) {t : Ix Dw → Kˣ} {y y' : FrPt Xo c K}
    (h : FrBor t y y') {v' : TIx Dw Φ → FrPt Xo c (DualNumber K)} (hv' : IsTanFrame Φ y' v') :
    ∃ (w : TIx Dw Φ → FrPt Xo c (DualNumber K)) (M : HIx Dw Φ → HIx Dw Φ → K) (N : VIx Dw → FIx Dw → K),
      (∀ k, ∃ t' : Ix Dw → (DualNumber K)ˣ, FrBor t' (w k) (v' k)) ∧
      (∀ k, IsDef y (w (.inl k)) ∧ IsKS Φ y (w (.inl k)).x (M k)) ∧ (∀ k, IsVert y (N k) (w (.inr k))) ∧
      (Matrix.of M).det * (Matrix.of fun k j : VIx Dw => N k j.toF).det =
        ((∏ k, t k ^ exOf Dw (kap Dw) 0 k : Kˣ) : K) := by
  obtain ⟨g, hg, hd, hc⟩ := (frBor_iff_frChg _ _ _).1 h
  obtain ⟨g', a', -, e1, e2⟩ := exists_frChg_inv hc
  have hg' : ∀ τ i j, i < j → g' τ i j = 0 := fun τ i j hij => by
    let _ : Invertible (g τ) := ⟨g' τ, e1 τ, e2 τ⟩
    have := Matrix.blockTriangular_inv_of_blockTriangular (M := g τ) (b := OrderDual.toDual)
      (fun i j hij => hg τ i j hij)
    rw [Matrix.inv_eq_left_inv (e1 τ)] at this
    exact this hij
  have hd' : ∀ τ i, g' τ i i = ((t (some ⟨τ, i⟩))⁻¹ : Kˣ) := fun τ i => by
    have := congrFun (congrFun (e1 τ) i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hd, Matrix.one_apply_eq] at this
    · exact (Units.mul_eq_one_iff_eq_inv).1 this
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with k | k
      · rw [hg τ j i k, mul_zero]
      · rw [hg' τ i j k, zero_mul]
    · simp
  choose w hw hw' using fun k => exists_move hc (hv'.isDef k)
  refine ⟨w, fun k => ksChg Φ g (Pi.single k 1), movedVert g g', fun k =>
    ⟨fun i => Units.map (cst c K).toRingHom.toMonoidHom (t i),
      (frBor_iff_frChg _ _ _).2 ⟨_, fun τ i j hij => by simp [hg τ i j hij], fun τ i => by simp [hd], hw' k⟩⟩,
    fun k => ⟨hw _, by rw [← (hw' _).1]; exact (hv'.1 k).2.of_frChg hc⟩,
    fun k => isVert_move hc e2 (hv'.2 k) (hw' (.inr k)), det_moved hΦ hg hd hg' hd'⟩

end GlobalTheory.FlagTan

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem det_der_frBor : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {P Q : FrPt Xo c K}
    (t : Ix Dw → Kˣ) (hz : z ≫ toFlag M = X.ptY Q) (ht : FrBor t Q P)
    {v v' : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)}
    (hv : IsTanFrame (psiSet H) P v) (hv' : IsTanFrame (psiSet H) Q v')
    {zv zv' : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)}
    (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b)) (hl' : ∀ b, zv' b ≫ toFlag M = X.ptY (v' b))
    (O : M.X.Opens) (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hzv' : ∀ b, ⊤ ≤ zv' b ⁻¹ᵁ O), (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det =
      (∏ ix, t ix ^ exOf Dw (kap Dw) 0 ix).val *
        (Matrix.of fun a b => (evalPt (zv' (tanOrd Dw b)) O (hzv' _) (g a)).snd).det := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS K _ _ z ho P Q t hz ht v v' hv hv' zv zv' hl hl' O g hzv hzv'
  obtain ⟨w, Mx, N, hb, hM, hN, hdet⟩ := GlobalTheory.FlagTan.exists_moved_defs (GlobalTheory.FlagTan.isHalf_psiSet H) ht hv
  have hlw : ∀ k, zv k ≫ toFlag M = X.ptY (w k) := fun k => by
    obtain ⟨_, h⟩ := hb k
    rw [hl, X.ptY_frBor h]
  choose C hC using fun k => GlobalTheory.T.derivative_along_kodairaSpencer_deformation_lift M z ho (hKS K Q) hz hv' hl' (hM k).1 (hM k).2 (hlw (.inl k))
  have hV := fun k => GlobalTheory.T.derivative_along_vertical_deformation_lift M z ho hz (v := fun j => v' (.inr j)) (fun j => hv'.2 j)
    (zv := fun j => zv' (.inr j)) (fun j => hl' _) (hN k) (hlw (.inr k))
  let T : Matrix (TIx Dw (psiSet H)) (TIx Dw (psiSet H)) K :=
    Matrix.fromBlocks (Matrix.of Mx) (Matrix.of C) 0 (Matrix.of fun k j : VIx Dw => N k j.toF)
  have hT : ∀ a b, (evalPt (zv b) O (hzv b) (g a)).snd =
      ∑ c', T b c' * (evalPt (zv' c') O (hzv' c') (g a)).snd := by
    intro a b
    rcases b with k | k
    · rw [hC k O (g a) (hzv _) hzv', Fintype.sum_sum_type]
      simp [T]
    · rw [hV k O (g a) (hzv _) (fun j => hzv' _), Fintype.sum_sum_type]
      simp [T]
  have hA : (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd) =
      (Matrix.of fun a b => (evalPt (zv' (tanOrd Dw b)) O (hzv' _) (g a)).snd) *
        (T.submatrix (tanOrd Dw) (tanOrd Dw)).transpose := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, hT]
    rw [← (tanOrd Dw).sum_comp]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hA, Matrix.det_mul, Matrix.det_transpose, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, hdet,
    mul_comm]

end GlobalTheory.CompHS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDerivativesBorelFrameChangeCanonicalWeightStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_derivatives_borelFrameChange_canonicalWeight : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {P Q : FrPt Xo c K}
    (t : Ix Dw → Kˣ) (hz : z ≫ toFlag M = X.ptY Q) (ht : FrBor t Q P)
    {v v' : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)}
    (hv : IsTanFrame (psiSet H) P v) (hv' : IsTanFrame (psiSet H) Q v')
    {zv zv' : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)}
    (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b)) (hl' : ∀ b, zv' b ≫ toFlag M = X.ptY (v' b))
    (O : M.X.Opens) (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hzv' : ∀ b, ⊤ ≤ zv' b ⁻¹ᵁ O), (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det =
      (∏ ix, t ix ^ exOf Dw (kap Dw) 0 ix).val *
        (Matrix.of fun a b => (evalPt (zv' (tanOrd Dw b)) O (hzv' _) (g a)).snd).det := by
  first | exact @GlobalTheory.CompHS.det_der_frBor | exact GlobalTheory.CompHS.det_der_frBor | (intros; apply GlobalTheory.CompHS.det_der_frBor <;> assumption)
end
