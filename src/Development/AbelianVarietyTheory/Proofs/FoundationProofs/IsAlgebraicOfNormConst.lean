module

public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsBijectiveKappa
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsNonzeroOfGenerator

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst
noncomputable section

namespace GlobalTheory.FlatLine

theorem isAlgebraic_of_norm_const {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [Algebra K ℂ]
    (P₀ : Ω →ₐ[K] ℂ) {b : Ω} (h : ∀ P : Ω →ₐ[K] ℂ, ‖P b‖ = ‖P₀ b‖) : IsAlgebraic K b := by
  by_contra hb
  have hi : AlgebraicIndepOn K id ({b} : Set Ω) := algebraicIndependent_unique_type_iff.2 hb
  obtain ⟨T, hT, hbas⟩ := exists_isTranscendenceBasis_superset hi
  have hw : AlgebraicIndependent K fun i : T => P₀ i := hbas.1.map' P₀.injective
  have hw2 : AlgebraicIndependent K fun i : T => Polynomial.aeval (P₀ i) (Polynomial.C (2 : K) * Polynomial.X) :=
    hw.polynomial_aeval_of_transcendental fun _ => Polynomial.transcendental _
      (by rw [Polynomial.natDegree_C_mul_X _ two_ne_zero]; exact one_ne_zero)
      (by rw [Polynomial.leadingCoeff_C_mul_X]; exact mem_nonZeroDivisors_of_ne_zero two_ne_zero)
  letI : Algebra (MvPolynomial T K) Ω := (MvPolynomial.aeval fun i : T => (i : Ω)).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial T K) ℂ := (MvPolynomial.aeval fun i : T =>
    Polynomial.aeval (P₀ i) (Polynomial.C (2 : K) * Polynomial.X)).toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial T K) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hbas.1
  haveI : FaithfulSMul (MvPolynomial T K) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hw2
  haveI : Algebra.IsAlgebraic (MvPolynomial T K) Ω :=
    haveI := hbas.isAlgebraic
    ⟨fun y => (IsAlgebraic.ringHom_of_comp_eq (f := hbas.1.aevalEquiv.symm.toRingHom) (g := RingHom.id Ω)
      (Algebra.IsAlgebraic.isAlgebraic y) hbas.1.aevalEquiv.symm.injective (RingHom.ext fun z => by
        obtain ⟨p, rfl⟩ := hbas.1.aevalEquiv.surjective z
        simp [RingHom.algebraMap_toAlgebra]))⟩
  let Q : Ω →ₐ[MvPolynomial T K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let P : Ω →ₐ[K] ℂ := { Q.toRingHom with
    commutes' := fun a => by
      have := Q.commutes (MvPolynomial.C a)
      simpa [RingHom.algebraMap_toAlgebra] using this }
  have h1 : P b = 2 * P₀ b := by
    show Q b = _
    have := Q.commutes (MvPolynomial.X ⟨b, hT rfl⟩)
    simpa [RingHom.algebraMap_toAlgebra, map_ofNat] using this
  have h2 := h P
  rw [h1, norm_mul, Complex.norm_two] at h2
  have h3 : P₀ b = 0 := norm_eq_zero.1 (by linarith)
  exact hb ((map_eq_zero P₀).1 h3 ▸ isAlgebraic_zero)

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  Formalism.L2.Pj GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem liesOn_frMap {Z : Comp Xo c} {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) (hy : LiesOn Z y) : LiesOn Z z := by
  have e : ptF z = spMap φ.toRingHom ≫ ptF y := by
    apply pullback.hom_ext
    · rw [ptF, pullback.lift_fst, Category.assoc, ptF, pullback.lift_fst, h.1]
    · rw [ptF, pullback.lift_snd, Category.assoc, ptF, pullback.lift_snd, ← Spec.map_comp]
      congr 1
      ext a
      exact (φ.commutes a).symm
  intro s
  rw [e, Scheme.Hom.comp_apply]
  exact hy _

theorem liesOn_frBor {Z : Comp Xo c} {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ} {y z : FrPt Xo c S}
    (h : FrBor t y z) (hz : LiesOn Z z) : LiesOn Z y := by
  have e : ptF y = ptF z := by
    apply pullback.hom_ext
    · rw [ptF, pullback.lift_fst, ptF, pullback.lift_fst, h.1]
    · rw [ptF, pullback.lift_snd, ptF, pullback.lift_snd]
  intro s
  rw [e]
  exact hz s

theorem secZ_zero_eq : secZ Xo c 0 = sec Xo c 0 0 := by
  rw [← secZ_nat]
  congr 1
  funext i
  cases i <;> rfl

theorem exists_eq_smul_idem {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hF : FnAlgClosed (Xo := Xo) (c := c)) {Z : Comp Xo c} {g : Rul Xo c} (hg : g ∈ secZ Xo c 0) (hs : g ∈ suppOn Z) {b : ℝ}
    (hb : ∀ z ∈ framesOn U Z, ‖rdU U g z.1 z.2‖ = b) : ∃ a : c.F, g = a • idem Z := by
  obtain ⟨hL, -, h, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨⟨P₀⟩, hP⟩ := GlobalTheory.GenericReading.embedding_read_at_frame E H Dw l Xo c σ r U hσ hU h Z
  have hi := idem_mem_secZ Z
  rw [secZ_zero_eq] at hg hi
  have key : ∀ P : Om Z →ₐ[c.F] CAt σ, ‖toC (P (evC h Z g))‖ = b := fun P => by
    obtain ⟨k, x, y', t, hm, ht⟩ := hP P
    obtain ⟨w, -, hw⟩ := GlobalTheory.CompBij.rdU_eq_of_reads U h k Z x P y' t hm ht 0 0
    have hz : (⟨k, x.1⟩ : Σ k, Frame (U.X k).Ψ r) ∈ framesOn U Z :=
      ⟨x.2, liesOn_frBor ht (liesOn_frMap hm (liesOn_genFr h Z))⟩
    have h1 := hw _ hi
    have h2 : rdU U (idem Z) k x = 1 := by
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, x.2, dif_pos]
      exact evR_idem (S := CAt σ) hz.2 (haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ); hL.test _ _)
    have h3 : evC h Z (idem Z) = 1 := evR_idem (liesOn_genFr h Z) (hL.test _ _)
    rw [h2, h3, map_one, mul_one] at h1
    rw [← hw g hg, h1]
    exact (congrArg norm (one_mul _)).trans (hb _ hz)
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨a, ha⟩ := hF Z _ (isAlgebraic_of_norm_const (K := c.F) (b := evC h Z g) P₀
    fun P => (key P).trans (key P₀).symm)
  refine ⟨a, sub_eq_zero.1 (GlobalTheory.Reg.sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _
    (sub_mem hg (Submodule.smul_mem _ _ hi)) fun Z' => ?_)⟩
  by_cases hZ : Z' = Z
  · subst hZ
    have h3 : evC h Z' (idem Z') = 1 := evR_idem (liesOn_genFr h Z') (hL.test _ _)
    have h4 := evalAt_add (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) g ((-a) • idem Z')
      (genFr h Z')
    have h5 := evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (-a) (idem Z')
      (genFr h Z')
    rw [sub_eq_add_neg, ← neg_smul]
    refine h4.trans ?_
    rw [h5]
    show evC h Z' g + algebraMap _ _ (-a) * evC h Z' (idem Z') = 0
    rw [h3, ← ha, map_neg, mul_one, add_neg_cancel]
  · exact evC_eq_zero h hZ (sub_mem hs (Submodule.smul_mem _ _ (idem_mem_suppOn Z)))

variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem ConstSec.exists_eq_smul (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hF : FnAlgClosed (Xo := Xo) (c := c)) {Z : Comp Xo c}
    {la : GlobalTheory.AllWt.Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s t : ConstSec U x Z la δ) :
    ∃ (a : c.F) (ha : a ≠ 0), t = s.smul a ha := by
  have hσ := goodEmb_goodOf c c.F.val.toRingHom
  let u : ConstSec U x Z 0 0 := (t.mul s.symm).copy (add_neg_cancel la) (add_neg_cancel δ)
  obtain ⟨a, ha⟩ := exists_eq_smul_idem (U _) hσ (hU _ hσ) hF (g := u.sig) (exOf_zero (Dw := Dw) ▸ u.sig_mem)
    u.sig_mem_suppOn (b := u.cInf c.F.val.toRingHom) fun z hz => by
      rw [← homN_zero _ x, ← wtOf_zero (Dw := Dw)]; exact u.homN_eq hz
  have ha' : t.sig * s.inv = a • idem Z := ha
  have h : t.sig = a • s.sig :=
    calc t.sig = t.sig * s.inv * s.sig := by
          rw [mul_assoc, mul_comm s.inv, s.mul_inv, mul_comm, t.idem_sig]
      _ = a • s.sig := by rw [ha', smul_mul_assoc, s.idem_sig]
  have h0 : a ≠ 0 := by
    intro h0
    apply t.sig_ne_zero
    rw [h, h0]
    set_option synthInstance.maxHeartbeats 200000 in
      exact zero_smul c.F s.sig
  exact ⟨a, h0, ConstSec.ext h⟩

theorem ConstSec.deg_eq (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hF : FnAlgClosed (Xo := Xo) (c := c)) {Z : Comp Xo c}
    {la : GlobalTheory.AllWt.Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s t : ConstSec U x Z la δ) : t.deg = s.deg := by
  obtain ⟨a, ha, rfl⟩ := ConstSec.exists_eq_smul hU hF s t
  exact ConstSec.deg_smul a ha s

end GlobalTheory.FlatLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasPhiExistsExtAndUnique
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem hasVal_of_irreducible {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ ϖ' : V}
    (h : Irreducible ϖ) (h' : Irreducible ϖ') {x : FractionRing V} {n : ℤ} (hx : HasVal ϖ' x n) : HasVal ϖ x n := by
  obtain ⟨v, rfl⟩ := IsDiscreteValuationRing.associated_of_irreducible V h h'
  obtain ⟨u, rfl⟩ := hx
  refine ⟨v ^ n * u, ?_⟩
  have e : algebraMap V (FractionRing V) ((v ^ n : Vˣ) : V) = algebraMap V (FractionRing V) v ^ n := by
    have := congrArg Units.val (map_zpow (Units.map (algebraMap V (FractionRing V)).toMonoidHom) v n)
    rwa [Units.val_zpow_eq_zpow_val] at this
  rw [Units.val_mul, map_mul, map_mul, mul_zpow, e, _root_.mul_assoc]

theorem nonempty_sabMap_of_models {T : CDVR} {x : Sp T.Fr ⟶ Xo.X} {G G' : SAB H (Sp T.V)} {t t' : SAB H (Sp T.Fr)}
    (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G (spMap (algebraMap T.V T.Fr)))
    (m1' : SABMap t' Xo.univ.t x) (m2' : SABMap t' G' (spMap (algebraMap T.V T.Fr))) :
    Nonempty (SABMap G' G (𝟙 _)) := by
  obtain ⟨k, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ (𝟙 _) m1 ((Category.id_comp x).symm ▸ m1')
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m2 k
  have hp : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m1'.cart.1 Xo.univ.proper
  obtain ⟨ψ, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H T.V inferInstance G' G t' hp m2'
    (Category.id_comp (spMap (algebraMap T.V T.Fr)) ▸ n)
  exact ⟨ψ⟩

theorem HasPhi.unique {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {φ φ' : ℝ} (h : HasPhi y φ)
    (h' : HasPhi y φ') : φ = φ' := by
  obtain ⟨G, t, m1, m2, P, ϖ, Q, β, hϖ, hQ, -, hβ, rfl⟩ := h
  obtain ⟨G', t', m1', m2', P', ϖ', Q', β', hϖ', hQ', -, hβ', rfl⟩ := h'
  obtain ⟨ψ⟩ := nonempty_sabMap_of_models m1 m2 m1' m2'
  obtain ⟨d, hd⟩ := GlobalTheory.SameCoord.exists_equiv_psiCoord E H T.V G G' ψ P P' inferInstance inferInstance inferInstance
  have hQQ : ∀ χ, Q' (d χ) = Q χ := fun χ => by
    obtain ⟨r, hr, -⟩ := (GlobalTheory.PsiCoordLocal.main T.V P.D inferInstance χ).1
    obtain ⟨u, hu⟩ := hd χ r hr
    have h1 := hasVal_mul_unit (GlobalTheory.ValForm.hasVal_coord (hQ χ) hr) u
    have h2 := hasVal_of_irreducible hϖ hϖ' (GlobalTheory.ValForm.hasVal_coord (hQ' (d χ)) hu)
    rw [← map_mul, _root_.mul_comm] at h1
    exact hasVal_unique hϖ h2 h1
  obtain ⟨β₁, hβ₁, hφ⟩ := GlobalTheory.EtaVal.phiC_smul_pull E _ _ _ d β' 1 zero_le_one
  have hdiag : ∀ a, β₁.1 a a = β.1 a a := fun a => by
    rw [hβ₁, hβ', hβ, hQQ, _root_.one_mul]
  have e : β₁ = β := by
    refine Subtype.ext (LinearMap.ext fun a => LinearMap.ext fun b => ?_)
    have h1 := hdiag (a + b)
    have s1 := β₁.2.1 a b
    have s2 := β.2.1 a b
    simp only [map_add (f := _), LinearMap.add_apply] at h1
    linarith [hdiag a, hdiag b]
  rw [← e, hφ, _root_.one_mul]

theorem exists_ext_hasPhi {la : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ}
    (ho : OverLa la T.V io e) (y : IntFr Xo c T io) (hy : y.IsAlg) :
    ∃ (T' : CDVR) (i : T.Fr →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' (i.comp io)) (φ : ℝ),
      i.Finite ∧ OverLa la T'.V (i.comp io) e' ∧ y'.IsAlg ∧ HasPhi y' φ ∧
      (letI := io.toAlgebra; letI := (i.comp io).toAlgebra;
        FrMap ({ i with commutes' := fun _ => rfl } : T.Fr →ₐ[c.F] T'.Fr) y.1 y'.1) ∧
      ∀ f : Rul Xo c, IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f →
        evI y' f = i (evI y f) ∧ nval T'.V e' (evI y' f) = nval T.V e (evI y f) := by
  let _ := H.starRing
  obtain ⟨T', i, y', e', hi, ho', hy', -, hm, hv, C, -, P, -⟩ :=
    GlobalTheory.IntegralExt.exists_ext_chart_unif E H Dw l Xo c T io y la e ho hy
  obtain ⟨φ, hφ⟩ := exists_hasPhi y' C.I.G C.I.t' C.I.m1 C.I.m2 P
  exact ⟨T', i, e', y', φ, hi, ho', hy', hφ, hm, hv⟩

theorem hasPhi_exists_ext_and_unique :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
      (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
      (∀ (p : ℕ) (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e →
        ∀ y : IntFr Xo c T io, y.IsAlg →
          ∃ (T' : CDVR) (i : T.Fr →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' (i.comp io)) (φ : ℝ),
            i.Finite ∧ OverLa la.1 T'.V (i.comp io) e' ∧ y'.IsAlg ∧ HasPhi y' φ ∧
            ∀ (w : Ix Dw → ℤ) (f : Rul Xo c), f ∈ secZ Xo c w →
              evI y' f = i (evI y f) ∧ nval T'.V e' (evI y' f) = nval T.V e (evI y f)) ∧
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ φ' : ℝ), HasPhi y φ → HasPhi y φ' → φ = φ' := by
  intro E _ _ _ H Dw l Xo c
  refine ⟨fun p la T io e ho y hy => ?_, fun _ _ _ _ _ => HasPhi.unique⟩
  obtain ⟨T', i, e', y', φ, hi, ho', hy', hφ, -, hv⟩ := exists_ext_hasPhi ho y hy
  exact ⟨T', i, e', y', φ, hi, ho', hy', hφ, fun w f hf => hv f hf.1⟩

end GlobalTheory.SlopeRec
end
end
