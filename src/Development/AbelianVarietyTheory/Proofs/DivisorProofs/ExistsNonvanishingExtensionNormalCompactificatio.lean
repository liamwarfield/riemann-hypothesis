module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPtCompClosedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingHeckeTranslateEqZeta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalGenericFibreAffineFrameCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliSchemeAffineFrameCoverTwoEigenParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFramesLastStepEigenmodules
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingFrameUnitChangeToChart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantSectionUnitIntegralFramesDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantSectionUnitIntegralFramesDvr
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.DvrUnit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {O' : Type} [CommRing O'] {β' : O' →+* c.F}
  {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_ext (Z : Model Xo c β) (U : Set (Xo.XF c)) (j : c.F →+* R) (x : Sp K ⟶ Xo.XF c)
    (h1 : x ≫ toF Xo c = spMap ((algebraMap R K).comp j)) (hU : Set.range x ⊆ U) :
    ∃ χ : Sp R ⟶ gen Z, χ ≫ genStr Z = spMap j ∧ x ≫ Z.jQ = spMap (algebraMap R K) ≫ χ ∧
      Set.range χ ⊆ compactOf Z U := by
  haveI := isProper_genStr Z
  obtain ⟨χ, h2, h3⟩ := GlobalTheory.exists_valuativeExtension (genStr Z) (spMap j) (x ≫ Z.jQ) (by
    rw [Category.assoc, Z.jQ_over, ← Geo.Tor.spMap_comp]
    exact h1)
  refine ⟨χ, h3, h2.symm, ?_⟩
  rintro _ ⟨p, rfl⟩
  let g0 : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hg : χ (spMap (algebraMap R K) g0) ∈ Z.jQ '' U := by
    rw [← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply]
    exact ⟨_, hU ⟨g0, rfl⟩, rfl⟩
  have hp : p ∈ closure {spMap (algebraMap R K) g0} := by
    apply (PrimeSpectrum.le_iff_mem_closure _ _).1
    show Ideal.comap (algebraMap R K) (⊥ : Ideal K) ≤ (p : PrimeSpectrum R).asIdeal
    rw [Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]
    exact bot_le
  exact map_mem_closure χ.continuous hp (fun z hz => by rw [Set.mem_singleton_iff.1 hz]; exact hg)


omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem exists_ident (Z : Model Xo c β) {χ : Sp R ⟶ gen Z} {x : Sp K ⟶ Xo.XF c}
    (hχ : x ≫ Z.jQ = spMap (algebraMap R K) ≫ χ) {tK : SAB H (Sp K)}
    (mK : SABMap tK Xo.univ.t (x ≫ toX Xo c)) {t : SAB H (Sp R)} (m : SABMap t Z.t (χ ≫ genι Z)) :
    ∃ (a : SABMap tK t (spMap (algebraMap R K))) (mF : SABMap tK Z.oF.t x),
      mF.φ ≫ Z.m0.toSABMap.φ = mK.φ ∧ mF.φ ≫ Z.m.φ = a.φ ≫ m.φ := by
  obtain ⟨mF, h1⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Z.oF.t tK (pullback.fst _ _) x
    Z.m0.toSABMap mK
  obtain ⟨mJ, h2⟩ := sabComp pullCubComp E H _ _ _ Z.t Z.oF.t tK (Z.jQ ≫ pullback.fst _ _) x Z.m mF
  have hj : x ≫ Z.jQ ≫ pullback.fst _ _ = spMap (algebraMap R K) ≫ χ ≫ genι Z := by
    rw [← Category.assoc, hχ, Category.assoc]
  obtain ⟨a, h3⟩ := sabCancel pullCubCancel E H _ _ _ Z.t t tK (χ ≫ genι Z) (spMap (algebraMap R K)) m
    (PullbackSections.sabMapCast mJ hj)
  exact ⟨a, mF, h1.symm, by rw [← h2, ← PullbackSections.sabMapCast_φ mJ hj, h3]⟩


omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem exists_lift_vec {Z : Model Xo c β} {Y : Model Xo c β'} {χ : Sp R ⟶ gen Z} {χ' : Sp R ⟶ gen Y}
    {x : Sp K ⟶ Xo.XF c} {tK : SAB H (Sp K)} {mK : SABMap tK Xo.univ.t (x ≫ toX Xo c)} {t t' : SAB H (Sp R)}
    {m : SABMap t Z.t (χ ≫ genι Z)} {m' : SABMap t' Y.t (χ' ≫ genι Y)} {ψ : SABMap t t' (𝟙 (Sp R))}
    {a : SABMap tK t (spMap (algebraMap R K))} {a' : SABMap tK t' (spMap (algebraMap R K))}
    {mF : SABMap tK Z.oF.t x} {mF' : SABMap tK Y.oF.t x}
    (hψ : a.φ ≫ ψ.φ = a'.φ) (hF0 : mF.φ ≫ Z.m0.toSABMap.φ = mK.φ)
    (hFm : mF.φ ≫ Z.m.φ = a.φ ≫ m.φ) (hF0' : mF'.φ ≫ Y.m0.toSABMap.φ = mK.φ) (hFm' : mF'.φ ≫ Y.m.φ = a'.φ ≫ m'.φ)
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ 𝟙 _)
    (w' : epsAt x ⟶ Y.oF.t.G)
    (hw3 : w'.left ≫ Y.m.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ (v ≫ ψ.φ) ≫ m'.φ) :
    ∃ w : epsAt x ⟶ Z.oF.t.G, w.left ≫ Z.m0.toSABMap.φ = w'.left ≫ Y.m0.toSABMap.φ ∧
      w.left ≫ Z.m.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ v ≫ m.φ := by
  rw [Category.comp_id] at hv
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : Sp (DualNumber K) ⟶ Y.oF.t.G.left, w₀ = w'.left := ⟨_, rfl⟩
  have hw1 : w₀ ≫ Y.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ x := hw₀ ▸ Over.w w'
  have hw3' : w₀ ≫ Y.m.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ (v ≫ ψ.φ) ≫ m'.φ := hw₀ ▸ hw3
  obtain ⟨u, e1, hu1⟩ : ∃ u : Sp (DualNumber K) ⟶ tK.G.left, u ≫ mF'.φ = w₀ ∧
      u ≫ tK.G.hom = spMap (algebraMap K (DualNumber K)) :=
    ⟨mF'.cart.1.lift _ _ hw1, mF'.cart.1.lift_fst _ _ _, mF'.cart.1.lift_snd _ _ _⟩
  have hbase : spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap R K) =
      spMap (Chart.dualMapR (algebraMap R K)) ≫ spMap (algebraMap R (DualNumber R)) := by
    rw [OpenReg.spMap_comp, OpenReg.spMap_comp]
    congr 1
    ext z <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have e2 : u ≫ a.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ v := by
    apply ψ.cart.1.hom_ext
    · rw [Category.assoc, hψ]
      apply m'.cart.1.hom_ext
      · rw [Category.assoc, ← hFm', ← Category.assoc, e1, hw3']
        simp only [Category.assoc]
      · rw [Category.assoc, a'.cart.1.w, ← Category.assoc, hu1, hbase]
        simp only [Category.assoc, ψ.cart.1.w, Category.comp_id, hv]
    · rw [Category.assoc, a.cart.1.w, ← Category.assoc, hu1, Category.assoc, hv, hbase]
  have k1 : (u ≫ mF.φ) ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ x := by
    rw [Category.assoc, mF.cart.1.w, ← Category.assoc, hu1]
  have k2 : (u ≫ mF.φ) ≫ Z.m0.toSABMap.φ = w₀ ≫ Y.m0.toSABMap.φ := by
    rw [Category.assoc, hF0, ← e1, Category.assoc, hF0']
  have k3 : (u ≫ mF.φ) ≫ Z.m.φ = spMap (Chart.dualMapR (algebraMap R K)) ≫ v ≫ m.φ := by
    rw [Category.assoc, hFm, ← Category.assoc, e2, Category.assoc]
  subst hw₀
  exact ⟨Over.homMk (u ≫ mF.φ) k1, k2, k3⟩

theorem exists_move (Y : Model Xo c β') (Z : Model Xo c β) {xR : Sp R ⟶ gen Y} {xZ : Sp R ⟶ gen Z}
    {x : Sp K ⟶ Xo.XF c} (hY : x ≫ Y.jQ = spMap (algebraMap R K) ≫ xR) (hZ : x ≫ Z.jQ = spMap (algebraMap R K) ≫ xZ)
    (χ : 𝓞 E →+* R) {n : ℕ} (vR : Fin n → (epsAt (xR ≫ genι Y) ⟶ Y.t.G))
    (hvR : IsEigBasisAt Y.t.act (xR ≫ genι Y) χ vR) {v : Fin n → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)}
    {vb : Fin n → (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)} (hs : SameVecs Y x v vb)
    (hb : ∀ i, (vb i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (vR i).left) :
    ∃ vZ : Fin n → (epsAt (xZ ≫ genι Z) ⟶ Z.t.G), IsEigBasisAt Z.t.act (xZ ≫ genι Z) χ vZ ∧
      ∀ vK : Fin n → (epsAt ((x ≫ Z.jQ) ≫ genι Z) ⟶ Z.t.G),
        (∀ i, (vK i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (vZ i).left) → SameVecs Z x v vK := by
  obtain ⟨tK, ⟨mK⟩⟩ := GlobalTheory.ModFam.exists_sabPull (x ≫ toX Xo c) Xo.univ.t
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull (xZ ≫ genι Z) Z.t
  obtain ⟨t', ⟨m'⟩⟩ := GlobalTheory.ModFam.exists_sabPull (xR ≫ genι Y) Y.t
  obtain ⟨a, mF, hF0, hFm⟩ := exists_ident Z hZ mK m
  obtain ⟨a', mF', hF0', hFm'⟩ := exists_ident Y hY mK m'
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.ModelUniqueChecks.existsUnique_map R K t t' tK a a'
  obtain ⟨e, he, hbe⟩ := BdryUnit.exists_eigEquiv m.cart m.act (𝟙 _) (xZ ≫ genι Z) (Category.id_comp _).symm
  obtain ⟨e', he', hbe'⟩ := BdryUnit.exists_eigEquiv m'.cart m'.act (𝟙 _) (xR ≫ genι Y) (Category.id_comp _).symm
  obtain ⟨f, hf, hbf⟩ := BdryUnit.exists_eigEquiv ψ.cart ψ.act (𝟙 _) (𝟙 _) (Category.id_comp _).symm
  obtain ⟨v₀, rfl⟩ : ∃ v₀ : Fin n → _, vR = fun i => e' (f (v₀ i)) :=
    ⟨fun i => f.symm (e'.symm (vR i)), funext fun i => by simp⟩
  refine ⟨fun i => e (v₀ i), (hbe χ n v₀).1 ((hbf χ n v₀).2 ((hbe' χ n fun i => f (v₀ i)).2 hvR)), fun vK hK i => ?_⟩
  obtain ⟨w', h1, h2⟩ := hs i
  have h3 := h2.trans (hb i)
  rw [he', hf] at h3
  obtain ⟨w, h4, h5⟩ := exists_lift_vec hψ hF0 hFm hF0' hFm' (Over.w (v₀ i)) w' h3
  refine ⟨w, h4.trans h1, h5.trans ?_⟩
  rw [hK i, he]

theorem unit_in_integral_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z : Model Xo c β') (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σZ : RuleY Z) (σ : RuleU Xo c), SecY Z (compactOf Z U) τ σZ → NzY Z (compactOf Z U) τ σZ → Restricts Z U τ σZ σ → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (j : c.F →+* R) (xR : Sp R ⟶ gen Y) (x : Sp K ⟶ Xo.XF c) (V : Set (gen Y)) vR wR v w vb wb, FrY Y V τ j xR vR wR → FrU Xo c U τ ((algebraMap R K).comp j) x v w → x ≫ Y.jQ = spMap (algebraMap R K) ≫ xR → SameVecs Y x v vb → SameVecs Y x w wb → (∀ i, (vb i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (vR i).left) → (∀ i, (wb i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (wR i).left) → ∃ u : Rˣ, σ K x v w = algebraMap R K u := by
  intro E _ _ _ H D l Xo c O _ β Y O' _ β' Z U τ σZ σ hsec hnz hres R K _ _ _ _ _ _ j xR x V vR wR v w vb wb
    hR hU hx hv hw ev ew
  obtain ⟨xZ, h1, h2, h3⟩ := exists_ext Z U j x hU.1 hU.2.1
  obtain ⟨vZ, hvZ, sv⟩ := exists_move Y Z hx h2 _ vR hR.2.2.1 hv ev
  obtain ⟨wZ, hwZ, sw⟩ := exists_move Y Z hx h2 _ wR hR.2.2.2 hw ew
  have hZ : FrY Z (compactOf Z U) τ j xZ vZ wZ := ⟨h1, h3, hvZ, hwZ⟩
  obtain ⟨vK, wK, hK, a, b⟩ := exists_pull (algebraMap R K) hZ h2
  obtain ⟨u, hu⟩ := hnz R j xZ vZ wZ hZ
  refine ⟨u, ?_⟩
  rw [← hres K _ x v w vK wK hU hK (sv vK a) (sw wK b), hu]
  exact hsec.1 R K (algebraMap R K) (Chart.dualMapR (algebraMap R K)) j _ xZ _ vZ wZ vK wK
    (fun a => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by ext <;> simp [Chart.dualMapR]) hZ hK h2 a b

end GlobalTheory.DetLine.DvrUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantSectionUnitIntegralFramesDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinantSection_unit_integral_frames_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z : Model Xo c β') (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σZ : RuleY Z) (σ : RuleU Xo c), SecY Z (compactOf Z U) τ σZ → NzY Z (compactOf Z U) τ σZ → Restricts Z U τ σZ σ → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (j : c.F →+* R) (xR : Sp R ⟶ gen Y) (x : Sp K ⟶ Xo.XF c) (V : Set (gen Y)) vR wR v w vb wb, FrY Y V τ j xR vR wR → FrU Xo c U τ ((algebraMap R K).comp j) x v w → x ≫ Y.jQ = spMap (algebraMap R K) ≫ xR → SameVecs Y x v vb → SameVecs Y x w wb → (∀ i, (vb i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (vR i).left) → (∀ i, (wb i).left = spMap (Chart.dualMapR (algebraMap R K)) ≫ (wR i).left) → ∃ u : Rˣ, σ K x v w = algebraMap R K u := by
  first | exact @GlobalTheory.DetLine.DvrUnit.unit_in_integral_frame | exact GlobalTheory.DetLine.DvrUnit.unit_in_integral_frame | (intros; apply GlobalTheory.DetLine.DvrUnit.unit_in_integral_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonvanishingExtensionNormalCompactificatio
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.ExtendNormal

open FromGeneric

theorem valR_eq_one {X : Scheme.{0}} [IsReduced X] {U : X.Opens} {K : Type} [Field K] (x : Sp K ⟶ X)
    (hx : Set.range x ⊆ U) (hd : ∀ z ∈ U, x (IsLocalRing.closedPoint K) ⤳ z) {f : Γ(X, U)} (hf : valR x U f = 1)
    {R : Type} [CommRing R] (x' : Sp R ⟶ X) (hx' : Set.range x' ⊆ U) : valR x' U f = 1 := by
  have h : ⊤ ≤ x ⁻¹ᵁ U := fun z _ => hx ⟨z, rfl⟩
  have h' : ⊤ ≤ x' ⁻¹ᵁ U := fun z _ => hx' ⟨z, rfl⟩
  have h0 : (x.appLE U ⊤ h).hom (f - 1) = 0 := by
    rw [valR, dite_eq_left h] at hf
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1
    rw [map_sub, map_sub, map_one, map_one, map_zero]
    exact sub_eq_zero.2 hf
  have h1 : f - 1 = 0 := by
    refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun z hz => ?_)
    have h2 : x (IsLocalRing.closedPoint K) ∈ X.basicOpen (f - 1) :=
      (hd z (X.basicOpen_le _ hz)).mem_open (X.basicOpen _).isOpen hz
    have h3 := Scheme.basicOpen_appLE x ⊤ U h (f - 1)
    rw [show (x.appLE U ⊤ h) (f - 1) = 0 from h0, Scheme.basicOpen_zero] at h3
    have h4 : IsLocalRing.closedPoint K ∈ (⊤ ⊓ x ⁻¹ᵁ X.basicOpen (f - 1) : (Sp K).Opens) := ⟨trivial, h2⟩
    rw [← h3] at h4
    exact h4.elim
  rw [sub_eq_zero.1 h1, valR, dite_eq_left h', map_one, map_one]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

theorem exists_frame_local {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {V : Set X}
    {τ : E →+* ℂ} {p q : ℕ} (hcov : FrameCover t π s V (HermitianCompactForm.chi c τ) p q) {R : Type} [CommRing R] [IsLocalRing R]
    (x : Sp R ⟶ X) (hx : x (IsLocalRing.closedPoint R) ∈ V) :
    ∃ (j : c.F →+* R) (v : Fin p → (epsAt (x ≫ π) ⟶ t.G)) (w : Fin q → (epsAt (x ≫ π) ⟶ t.G)),
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w := by
  obtain ⟨W, hW, j, v, w, hz, h⟩ := hcov _ hx
  have : IsOpenImmersion (show Sp Γ(X, W) ⟶ X from hW.fromSpec) := inferInstanceAs (IsOpenImmersion hW.fromSpec)
  obtain ⟨m, hm⟩ := exists_lift (show Sp Γ(X, W) ⟶ X from hW.fromSpec) x (range_subset _
    (show Sp Γ(X, W) ⟶ X from hW.fromSpec).isOpenEmbedding.isOpen_range (by
      rw [show Set.range _ = _ from hW.range_fromSpec]; exact hz))
  obtain ⟨v', w', h', -⟩ := exists_pull m h hm
  exact ⟨_, v', w', h'⟩

theorem unitAtPt_of_dvr {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {V : Set X}
    {τ : E →+* ℂ} {p q : ℕ} (hcov : FrameCover t π s V (HermitianCompactForm.chi c τ) p q) {B : Scheme.{0}} [IsIntegral B]
    [IsLocallyNoetherian B] (hB : ∀ y : B, IsIntegrallyClosed (B.presheaf.stalk y)) (io : B ⟶ X)
    (hio : ∀ y, io y ∈ V) {j₀ : c.F →+* B.functionField} {v₀ w₀}
    (h₀ : IsFrame t π s V (HermitianCompactForm.chi c τ) (p := p) (q := q) j₀ (genPt B ≫ io) v₀ w₀) {δ : B.functionField} (hδ : δ ≠ 0)
    (hdvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R B.functionField]
      [IsFractionRing R B.functionField] (j : c.F →+* R) (x : Sp R ⟶ X) v w M N,
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w →
      IsChg t π (algebraMap R B.functionField) x v w (genPt B ≫ io) v₀ w₀ M N →
      ∃ u : Rˣ, N.det * algebraMap R B.functionField u = M.det * δ) (y : B) :
    UnitAtPt t π s V (HermitianCompactForm.chi c τ) io v₀ w₀ δ y := by
  obtain ⟨j, v, w, h⟩ := exists_frame_local hcov (locPt B y ≫ io) (by rw [locPt_comp_closedPoint]; exact hio y)
  obtain ⟨-, M, N, hc⟩ := exists_chg (algebraMap (B.presheaf.stalk y) B.functionField) h h₀
    (by rw [genPt_eq y, Category.assoc])
  obtain ⟨hM, hN⟩ := chg_isUnit h h₀ hc
  have hφ : M.det * δ / N.det ≠ 0 := div_ne_zero (mul_ne_zero hM.ne_zero hδ) hN.ne_zero
  have key : ∀ z : B, z ⤳ y → IsDiscreteValuationRing (B.presheaf.stalk z) →
      ∃ u : (B.presheaf.stalk z)ˣ, algebraMap _ B.functionField (u : B.presheaf.stalk z) = M.det * δ / N.det := by
    intro z hz _
    let g : B.presheaf.stalk y →+* B.presheaf.stalk z := (B.presheaf.stalkSpecializes hz).hom
    have hg : (algebraMap (B.presheaf.stalk z) B.functionField).comp g =
        algebraMap (B.presheaf.stalk y) B.functionField :=
      congrArg CommRingCat.Hom.hom (B.presheaf.stalkSpecializes_comp ((genericPoint_spec B).specializes trivial) hz)
    obtain ⟨v', w', h', a, b⟩ := exists_pull g h rfl
    obtain ⟨u, hu⟩ := hdvr _ _ _ v' w' M N h' ⟨by
      rw [← Category.assoc, ← DetExtendZero.spMap_comp, hg]; exact hc.1, fun i => by
      simp only [a, ← Category.assoc, ← DetExtendZero.dual_comp, hg]; exact hc.2.1 i, fun i => by
      simp only [b, ← Category.assoc, ← DetExtendZero.dual_comp, hg]; exact hc.2.2 i⟩
    exact ⟨u, by rw [← hu, mul_div_cancel_left₀ _ hN.ne_zero]⟩
  obtain ⟨a, ha⟩ := GlobalTheory.Hartogs.regAt_of_forall_dvr B hB (M.det * δ / N.det) y fun z hz hz' => by
    obtain ⟨u, hu⟩ := key z hz hz'
    exact ⟨u, hu⟩
  obtain ⟨b, hb⟩ := GlobalTheory.Hartogs.regAt_of_forall_dvr B hB (M.det * δ / N.det)⁻¹ y fun z hz hz' => by
    obtain ⟨u, hu⟩ := key z hz hz'
    exact ⟨(u⁻¹ : (B.presheaf.stalk z)ˣ), by rw [← hu, map_units_inv]⟩
  have hab : a * b = 1 := IsFractionRing.injective (B.presheaf.stalk y) B.functionField (by
    rw [map_mul, map_one, ha, hb, mul_inv_cancel₀ hφ])
  refine ⟨j, v, w, M, N, Units.mkOfMulEqOne a b hab, h, hc, ?_⟩
  rw [Units.val_mkOfMulEqOne, ha, mul_div_cancel₀ _ hN.ne_zero]

theorem exists_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z : Model Xo c β') (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (σZ : RuleY Z) (σ : RuleU Xo c), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → τ (H.rt : E) = H.rt0 → SecY Z (compactOf Z U) τ σZ → NzY Z (compactOf Z U) τ σZ → SecU Xo c U τ σ → Restricts Z U τ σZ σ → ∃ σb : RuleY Y, SecY Y (compactOf Y U) τ σb ∧ NzY Y (compactOf Y U) τ σb ∧ Restricts Y U τ σb σ := by
  intro E _ _ _ H D l Xo c O _ β Y O' _ β' Z U τ σZ σ hn hcl hU hτ hσZ hZ hσ hres
  obtain ⟨V, hV, hint⟩ := GlobalTheory.T.genericFibre_componentClosure_open_isIntegral E H D l Xo c O β Y U hn hcl hU
  have := Y.jQ_open
  have : IsProper (genStr Y) := isProper_genStr Y
  have : IsLocallyNoetherian (gen Y) := LocallyOfFiniteType.isLocallyNoetherian (genStr Y)
  have : IsReduced (gen Y) := by
    have := fun y => (hn y).1
    exact isReduced_of_isReduced_stalk _
  have : IsReduced (Xo.XF c) := isReduced_of_isOpenImmersion Y.jQ
  have hB : ∀ y : V.toScheme, IsIntegrallyClosed (V.toScheme.presheaf.stalk y) := fun y =>
    haveI := (hn (V.ι y)).2
    IsIntegrallyClosed.of_equiv (asIso (V.ι.stalkMap y)).commRingCatIsoToRingEquiv
  have hcov := frameCover_gen E H D l Xo c O β Y V τ hτ
  rw [hV] at hcov
  have hio : ∀ y, V.ι y ∈ compactOf Y U := fun y => hV ▸ y.2
  have hpt : (genPt V.toScheme ≫ V.ι) (IsLocalRing.closedPoint _) = V.ι (genericPoint V.toScheme) :=
    locPt_comp_closedPoint V.ι _
  have hsp : ∀ z ∈ compactOf Y U, V.ι (genericPoint V.toScheme) ⤳ z := fun z hz =>
    (genericPoint_specializes (α := V.toScheme) (⟨z, (hV ▸ hz : z ∈ (V : Set (gen Y)))⟩ : V.toScheme)).map V.ι.continuous
  have hgen : V.ι (genericPoint V.toScheme) ∈ Y.jQ '' (U : Set (Xo.XF c)) := by
    obtain ⟨z, hz⟩ := closure_nonempty_iff.1 ⟨_, hio (genericPoint V.toScheme)⟩
    exact (hsp z (subset_closure hz)).mem_open (Y.jQ.isOpenEmbedding.isOpenMap _ U.isOpen) hz
  obtain ⟨j₀, v₀, w₀, h₀⟩ := exists_frame_local hcov (genPt V.toScheme ≫ V.ι) (by rw [hpt]; exact hio _)
  have main : ∀ (K : Type) [Field K] (xb : Sp K ⟶ gen Y) (j₀ : c.F →+* K) v₀ w₀,
      xb (IsLocalRing.closedPoint K) = V.ι (genericPoint V.toScheme) → FrY Y (compactOf Y U) τ j₀ xb v₀ w₀ →
      ∃ δ : K, δ ≠ 0 ∧ (∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R K]
        [IsFractionRing R K] (j : c.F →+* R) (x : Sp R ⟶ gen Y) v w M N, FrY Y (compactOf Y U) τ j x v w →
        IsChg Y.t (genι Y) (algebraMap R K) x v w xb v₀ w₀ M N → ∃ u : Rˣ, N.det * algebraMap R K u = M.det * δ) ∧
        ∀ σb : RuleY Y, SecY Y (compactOf Y U) τ σb → NzY Y (compactOf Y U) τ σb → σb K xb v₀ w₀ = δ →
          Restricts Y U τ σb σ := by
    intro K _ xb j₀ v₀ w₀ hxb h₀
    obtain ⟨x, rfl⟩ : ∃ x : Sp K ⟶ Xo.XF c, x ≫ Y.jQ = xb :=
      ⟨IsOpenImmersion.lift Y.jQ xb (range_subset _ Y.jQ.isOpenEmbedding.isOpen_range
        (hxb ▸ Set.image_subset_range _ _ hgen)), IsOpenImmersion.lift_fac _ _ _⟩
    have hxb' : Y.jQ (x (IsLocalRing.closedPoint K)) = V.ι (genericPoint V.toScheme) :=
      (Scheme.Hom.comp_apply _ _ _).symm.trans hxb
    have hxU : Set.range x ⊆ U := range_subset _ U.isOpen (by
      obtain ⟨z, hz, e⟩ := hgen
      rwa [Y.jQ.isOpenEmbedding.injective (hxb'.trans e.symm)])
    obtain ⟨v, w, h, sv, sw⟩ := (frame_transfer E H D l Xo c O β Y U τ K j₀ x).2 _ v₀ w₀ hxU h₀
    refine ⟨σ K x v w, ?_, fun R _ _ _ _ _ j xR vR wR M N hR hc => ?_, fun σb hb hnz e => ?_⟩
    · obtain ⟨vz, wz, hz, a, b⟩ := (frame_transfer E H D l Xo c O' β' Z U τ K j₀ x).1 v w h
      rw [← hres K j₀ x v w vz wz h hz a b]
      exact (hZ K j₀ _ vz wz hz).ne_zero
    · obtain ⟨vb, wb, hb, a, b⟩ := exists_pull (algebraMap R K) hR hc.1
      obtain ⟨v', w', h', sv', sw'⟩ := (frame_transfer E H D l Xo c O β Y U τ K _ x).2 _ vb wb hxU hb
      obtain ⟨u, hu⟩ := GlobalTheory.T.determinantSection_unit_integral_frames_dvr E H D l Xo c O β Y O' β' Z U τ σZ σ hσZ hZ hres R K j xR x _ vR wR v' w' vb wb
        hR h' hc.1 sv' sw' a b
      have hid : x = spMap (RingHom.id K) ≫ x := by rw [DetExtendZero.spMap_id, Category.id_comp]
      refine ⟨u, ?_⟩
      rw [← hu]
      refine sec_chg (g := RingHom.id K) hσ h' h ⟨hid, fun i => ?_, fun i => ?_⟩
      · refine (isCombination_iff_of_sameVecs E H D l Xo c O β Y K K _ x x _ v' vb v v₀ hid sv' sv _ i).2 ?_
        simp only [DetExtendZero.dual_id, Category.id_comp, a]
        exact hc.2.1 i
      · refine (isCombination_iff_of_sameVecs E H D l Xo c O β Y K K _ x x _ w' wb w w₀ hid sw' sw _ i).2 ?_
        simp only [DetExtendZero.dual_id, Category.id_comp, b]
        exact hc.2.2 i
    · obtain ⟨σ₁, h1, h2, h3⟩ := GlobalTheory.T.exists_determinantLine_section_restriction E H D l Xo c O β Y U τ σb hb
      obtain ⟨f, hf⟩ := GlobalTheory.detLine_exists_ratio E H l c _ _ _ _ _ τ _ _ U σ₁ σ
        (frameCover_univ E H D l Xo c U τ hτ) h1 (h3 hnz) hσ
      have e1 : valR x U f = 1 := by
        have e2 := hf K j₀ x v w h
        rw [← e, h2 K j₀ x v w v₀ w₀ h h₀ sv sw] at e2
        exact ((h3 hnz K j₀ x v w h).mul_right_cancel ((_root_.one_mul _).trans e2)).symm
      intro R _ j x' v' w' vb wb h' hb' a b
      rw [h2 R j x' v' w' vb wb h' hb' a b, hf R j x' v' w' h',
        valR_eq_one x hxU (fun z hz => ?_) e1 x' h'.2.1, _root_.one_mul]
      rw [← Y.jQ.isOpenEmbedding.isInducing.specializes_iff, hxb']
      exact hsp _ (subset_closure ⟨z, hz, rfl⟩)
  obtain ⟨δ, hδ, hdvr, hfin⟩ := main _ _ j₀ v₀ w₀ hpt h₀
  obtain ⟨σb, h1, h2, h3⟩ := exists_section E H l c _ _ _ _ _ τ _ _ V.toScheme V.ι _ inferInstance
    (V.range_ι.trans hV) hcov j₀ v₀ w₀ δ h₀ (unitAtPt_of_dvr hcov hB V.ι hio h₀ hδ hdvr)
  exact ⟨σb, h1, h2, hfin σb h1 h2 h3⟩

end GlobalTheory.DetLine.ExtendNormal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonvanishingExtensionNormalCompactificatioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonvanishing_extension_normal_compactification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z : Model Xo c β') (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (σZ : RuleY Z) (σ : RuleU Xo c), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → τ (H.rt : E) = H.rt0 → SecY Z (compactOf Z U) τ σZ → NzY Z (compactOf Z U) τ σZ → SecU Xo c U τ σ → Restricts Z U τ σZ σ → ∃ σb : RuleY Y, SecY Y (compactOf Y U) τ σb ∧ NzY Y (compactOf Y U) τ σb ∧ Restricts Y U τ σb σ := by
  first | exact @GlobalTheory.DetLine.ExtendNormal.exists_extension | exact GlobalTheory.DetLine.ExtendNormal.exists_extension | (intros; apply GlobalTheory.DetLine.ExtendNormal.exists_extension <;> assumption)
end
