module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.TorusFrame
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UnitaryDatumNumbersForSupBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UnitaryDatumNumbersForSupBounds
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.SupDict

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E]
  simp only [Ranks.f, Ranks.n]
  ring

theorem xiR_pos (D : D7) : 0 < xiR D := by
  unfold xiR
  refine norm_pos_iff.mpr ((map_ne_zero _).mpr ?_)
  have hd : (D.host.d : D.host.E) ≠ 0 := by
    have hlt := D.host.qd_big.2
    exact_mod_cast (Nat.zero_lt_of_lt hlt).ne'
  have hs : D.host.sqd ≠ 0 := by
    intro h0
    have h2 := D.host.sqd_sq
    rw [h0] at h2
    apply hd
    have h3 : -(D.host.d : D.host.E) = 0 := by rw [← h2]; ring
    exact neg_eq_zero.mp h3
  have hn : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.mpr (fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
  simp only [Host.xi0, Host.sqrtMinusD]
  exact div_ne_zero (neg_ne_zero.mpr one_ne_zero) (mul_ne_zero hn hs)

theorem one_le_dE (E : Type) [Field E] [NumberField E] : 1 ≤ dE E := by
  unfold dE
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero E)

private lemma sum_ext0_le_sum {l : ℕ} (a : Fin l → ℕ) (M : ℕ) : ∑ i : Fin M, ext0 a (i : ℕ) ≤ ∑ i, a i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ext0 a i) M]
  have h1 : ∑ i ∈ Finset.range M, ext0 a i = ∑ i ∈ (Finset.range M).filter (· < l), ext0 a i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs with hi
    · rfl
    · simp [ext0, hi]
  have h2 : ∑ i ∈ (Finset.range M).filter (· < l), ext0 a i ≤ ∑ i ∈ Finset.range l, ext0 a i :=
    Finset.sum_le_sum_of_subset (fun i hi => by simp at hi ⊢; omega)
  have h3 : ∑ i ∈ Finset.range l, ext0 a i = ∑ i, a i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => ext0 a i) l]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [ext0, i.isLt]
  omega

theorem record_dictionary : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), fdeg D.host.E = D.R.f ∧ Real.log (rdE D.host.E) = lrd D ∧ 1 ≤ rdE D.host.E ∧ 1 ≤ D.R.f ∧ 1 ≤ D.R.r ∧ 0 < xiR D ∧ Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) ≤ WeightAlgebra.DF w ∧ absA w = (WeightAlgebra.DF w : ℝ) ∧ (∀ σ, GoodEmb T.Q.c σ → ∀ k τ, ((T.U j σ).X k).c τ = 2 * xiR D) ∧ lieFac (T.Q.Dw j) (xiR D) (wtA w) = Real.exp (-(((Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℕ) : ℝ) / 2) * Real.log (Real.pi * (2 * xiR D))) ∧ T.Q.l.A = 1 ∧ 0 < D.host.pde ∧ 0 < D.host.pde' ∧ ∀ (ι : Type) (σ : T.Q.c.F →+* ℂ) (P : MvPolynomial ι T.Q.c.F), l1At (goodOf T.Q.c σ) P = l1At σ P := by
  intro D T h j hj w
  have hfin := finrank_host D
  have hdpos : 0 < dE D.host.E := lt_of_lt_of_le one_pos (one_le_dE _)
  refine ⟨?_, ?_, ?_, ?_, ?_, xiR_pos D, ?_, ?_, ?_, ?_, ?_, D.host.pde_prime.pos, D.host.pde'_prime.pos, ?_⟩
  · unfold fdeg
    rw [hfin]
    omega
  · rw [rdE, Real.log_rpow hdpos, hfin, lrd, dE]
    push_cast
    ring
  · unfold rdE
    exact Real.one_le_rpow (one_le_dE _) (by positivity)
  · have h1 := D.R.two_le_m
    have h2 := D.R.m_le_f
    simp only [Ranks.f, Ranks.n]
    omega
  · have h1 := D.R.two_le_m
    simp only [Ranks.r]
    omega
  · unfold wtA Formalism.L2.Pj.DF WeightAlgebra.DF WeightAlgebra.degP
    simp only [Finset.sum_add_distrib]
    apply add_le_add
    · rw [Finset.sum_congr rfl (fun τ _ => Finset.sum_comm), Finset.sum_comm]
      refine Finset.sum_le_sum (fun t _ => ?_)
      rw [Finset.sum_eq_single (DV.tauEmb D t)]
      · simp only [↓reduceIte]
        exact sum_ext0_le_sum _ _
      · intro τ _ hτ
        simp [hτ]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    · rw [Finset.sum_congr rfl (fun τ _ => Finset.sum_comm), Finset.sum_comm]
      refine Finset.sum_le_sum (fun t _ => ?_)
      rw [Finset.sum_eq_single (conjEmb (DV.tauEmb D t))]
      · simp only [↓reduceIte]
        exact sum_ext0_le_sum _ _
      · intro τ _ hτ
        simp [hτ]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
  · unfold absA WeightAlgebra.DF WeightAlgebra.degP
    push_cast
    rfl
  · intro σ hσ k τ
    unfold Data.c
    rw [h.xiAbs j hj σ hσ k τ.1]
  · unfold lieFac Formalism.L2.Pj.DF
    rw [show (2 : ℝ) * Real.pi * xiR D = Real.pi * (2 * xiR D) by ring]
    push_cast
    rfl
  · obtain ⟨-, hl, -, -⟩ := h.pins
    unfold Par.PinLevel at hl
    exact hl.2
  · intro ι σ P
    unfold l1At goodOf
    split_ifs with hg
    · rfl
    · simp only [RingHom.comp_apply, Complex.norm_conj]

end GlobalTheory.SupDict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UnitaryDatumNumbersForSupBoundsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryDatumNumbers_for_supBounds : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), fdeg D.host.E = D.R.f ∧ Real.log (rdE D.host.E) = lrd D ∧ 1 ≤ rdE D.host.E ∧ 1 ≤ D.R.f ∧ 1 ≤ D.R.r ∧ 0 < xiR D ∧ Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) ≤ WeightAlgebra.DF w ∧ absA w = (WeightAlgebra.DF w : ℝ) ∧ (∀ σ, GoodEmb T.Q.c σ → ∀ k τ, ((T.U j σ).X k).c τ = 2 * xiR D) ∧ lieFac (T.Q.Dw j) (xiR D) (wtA w) = Real.exp (-(((Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℕ) : ℝ) / 2) * Real.log (Real.pi * (2 * xiR D))) ∧ T.Q.l.A = 1 ∧ 0 < D.host.pde ∧ 0 < D.host.pde' ∧ ∀ (ι : Type) (σ : T.Q.c.F →+* ℂ) (P : MvPolynomial ι T.Q.c.F), l1At (goodOf T.Q.c σ) P = l1At σ P := by
  first | exact @GlobalTheory.SupDict.record_dictionary | exact GlobalTheory.SupDict.record_dictionary | (intros; apply GlobalTheory.SupDict.record_dictionary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EtaValAtExistsUniqueNatural
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaForm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem finite_latMod (Dw : Datum H) {k : ℕ} (hk : 0 < k) : Finite (LatMod Dw k) := by
  haveI := Dw.fin
  haveI : Module.Finite ℤ (LatMod Dw k) := Module.Finite.trans (𝓞 E) _
  refine Module.finite_of_fg_torsion (M := LatMod Dw k) fun x => ?_
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  refine ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩
  change (k : ℤ) • Submodule.mkQ (Ideal.span {(k : 𝓞 E)} • ⊤ : Submodule (𝓞 E) Dw.La) x = 0
  rw [natCast_zsmul, ← map_nsmul]
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

theorem finite_levGrp (Dw : Datum H) {k : ℕ} (hk : 0 < k) : Finite (LevGrp Dw k) := by
  haveI := finite_latMod Dw hk
  exact Finite.of_injective (fun g : LevGrp Dw k => (g : LatMod Dw k → LatMod Dw k)) DFunLike.coe_injective

theorem map_etaExpr {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {k : ℕ} (hk : 0 < k) {J : Type} [Fintype J]
    {n : ℕ} (cf : J → ℤ) (x : J → Fin n → LatMod Dw k) (w : LatMod Dw k → S) :
    φ (etaExpr k cf x w) = etaExpr k cf x (fun q => φ (w q)) := by
  haveI := finite_levGrp Dw hk
  haveI := Fintype.ofFinite (LevGrp Dw k)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [etaExpr, finprod_eq_prod_of_fintype, map_prod, map_sum, map_mul, map_intCast]

theorem etaExpr_comp {S : Type} [CommRing S] {k : ℕ} {J : Type} [Fintype J]
    {n : ℕ} (cf : J → ℤ) (x : J → Fin n → LatMod Dw k) (w : LatMod Dw k → S) (g₀ : LevGrp Dw k) :
    etaExpr k cf x (fun q => w (g₀ q)) = etaExpr k cf x w := by
  unfold etaExpr
  exact finprod_eq_of_bijective (fun g : LevGrp Dw k => g₀ * g) (Group.mulLeft_bijective g₀) fun g => rfl

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_level_baseChange (hL : Laws) {R : ℕ} (hR : Odd R) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T]
    [Algebra c.F T] (ψ : S →ₐ[c.F] T) {y : FrPt Xo c S} {z : FrPt Xo c T} (hm : FrMap ψ y z)
    {ev : LatMod Dw (R ^ 4) → (ptO Xo y.x ⟶ Xo.univ.t.G)} {w : LatMod Dw (R ^ 4) → S}
    (hev : IsFullLev Xo (R ^ 4) y.x ev) (hw : ∀ q, IsNullVal Xo c (R ^ 2) y (ev q) (w q)) :
    ∃ ev' : LatMod Dw (R ^ 4) → (ptO Xo z.x ⟶ Xo.univ.t.G), IsFullLev Xo (R ^ 4) z.x ev' ∧
      ∀ q, IsNullVal Xo c (R ^ 2) z (ev' q) (ψ (w q)) := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  let h : ptO Xo z.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hm.1.symm
  refine ⟨fun q => h ≫ ev q,
    ((GlobalTheory.T.fullLinearLevel_cover_baseChange_torsor hL E H Dw l Xo _ hk).2.1 S T ψ.toRingHom y.x z.x h rfl ev hev).1, fun q => ?_⟩
  exact (GlobalTheory.T.thetaNullValue_existsUnique_natural_linear hL E H Dw l Xo c (R ^ 2) hR.pow).2.1 S T ψ y z hm (ev q) (h ≫ ev q) rfl _ (hw q)

theorem existsUnique_nullVal (hL : Laws) {R : ℕ} (hR : Odd R) {S : Type} [CommRing S] [Algebra c.F S]
    {y : FrPt Xo c S} {ev : LatMod Dw (R ^ 4) → (ptO Xo y.x ⟶ Xo.univ.t.G)}
    (hev : IsFullLev Xo (R ^ 4) y.x ev) (q : LatMod Dw (R ^ 4)) : ∃! w, IsNullVal Xo c (R ^ 2) y (ev q) w := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  refine (GlobalTheory.T.thetaNullValue_existsUnique_natural_linear hL E H Dw l Xo c (R ^ 2) hR.pow).1 S y (ev q) ?_
  have h1 := ((GlobalTheory.T.fullLinearLevel_cover_baseChange_torsor hL E H Dw l Xo _ hk).2.1 S S (RingHom.id S) y.x y.x (𝟙 _)
    (by simp [spMap]) ev hev).2 q
  rw [← pow_mul]
  exact h1

theorem etaExpr_eq_of_levels (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw (R ^ 4)) {T : Type} [CommRing T] [Algebra c.F T] {z : FrPt Xo c T}
    {ev ev' : LatMod Dw (R ^ 4) → (ptO Xo z.x ⟶ Xo.univ.t.G)} {w w' : LatMod Dw (R ^ 4) → T}
    (hev : IsFullLev Xo (R ^ 4) z.x ev) (hw : ∀ q, IsNullVal Xo c (R ^ 2) z (ev q) (w q))
    (hev' : IsFullLev Xo (R ^ 4) z.x ev') (hw' : ∀ q, IsNullVal Xo c (R ^ 2) z (ev' q) (w' q)) :
    etaExpr (R ^ 4) cf x w = etaExpr (R ^ 4) cf x w' := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  refine Module.eq_of_localization_maximal (R := T) (fun P _ => Localization.AtPrime P)
    (fun P _ => Algebra.linearMap T (Localization.AtPrime P)) _ _ fun P _ => ?_
  let ψ : T →ₐ[c.F] Localization.AtPrime P := IsScalarTower.toAlgHom c.F T _
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c T _ ψ z
  obtain ⟨e, he, hv⟩ := exists_level_baseChange hL hR ψ hu hev hw
  obtain ⟨e', he', hv'⟩ := exists_level_baseChange hL hR ψ hu hev' hw'
  obtain ⟨g, hg⟩ := ((GlobalTheory.T.fullLinearLevel_cover_baseChange_torsor hL E H Dw l Xo _ hk).2.2.1 _ u.x e he).2 e' he'
  have hww : (fun q => ψ (w' q)) = fun q => ψ (w (g q)) := funext fun q =>
    (existsUnique_nullVal hL hR he (g q)).unique (hg q ▸ hv' q) (hv (g q))
  change algebraMap T (Localization.AtPrime P) (etaExpr (R ^ 4) cf x w) =
    algebraMap T (Localization.AtPrime P) (etaExpr (R ^ 4) cf x w')
  rw [map_etaExpr _ hk, map_etaExpr _ hk]
  exact (etaExpr_comp cf x (fun q => ψ (w q)) g).symm.trans (congrArg _ hww.symm)

theorem map_etaExpr_eq_of_levels (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw (R ^ 4)) {S₁ S₂ T : Type} [CommRing S₁] [Algebra c.F S₁] [CommRing S₂] [Algebra c.F S₂]
    [CommRing T] [Algebra c.F T] (ψ₁ : S₁ →ₐ[c.F] T) (ψ₂ : S₂ →ₐ[c.F] T) {y₁ : FrPt Xo c S₁} {y₂ : FrPt Xo c S₂}
    {z : FrPt Xo c T} (h₁ : FrMap ψ₁ y₁ z) (h₂ : FrMap ψ₂ y₂ z)
    {ev₁ : LatMod Dw (R ^ 4) → (ptO Xo y₁.x ⟶ Xo.univ.t.G)} {w₁ : LatMod Dw (R ^ 4) → S₁}
    {ev₂ : LatMod Dw (R ^ 4) → (ptO Xo y₂.x ⟶ Xo.univ.t.G)} {w₂ : LatMod Dw (R ^ 4) → S₂}
    (hev₁ : IsFullLev Xo (R ^ 4) y₁.x ev₁) (hw₁ : ∀ q, IsNullVal Xo c (R ^ 2) y₁ (ev₁ q) (w₁ q))
    (hev₂ : IsFullLev Xo (R ^ 4) y₂.x ev₂) (hw₂ : ∀ q, IsNullVal Xo c (R ^ 2) y₂ (ev₂ q) (w₂ q)) :
    ψ₁ (etaExpr (R ^ 4) cf x w₁) = ψ₂ (etaExpr (R ^ 4) cf x w₂) := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  obtain ⟨e₁, he₁, hv₁⟩ := exists_level_baseChange hL hR ψ₁ h₁ hev₁ hw₁
  obtain ⟨e₂, he₂, hv₂⟩ := exists_level_baseChange hL hR ψ₂ h₂ hev₂ hw₂
  exact (map_etaExpr ψ₁.toRingHom hk cf x w₁).trans
    ((etaExpr_eq_of_levels hL hR cf x he₁ hv₁ he₂ hv₂).trans (map_etaExpr ψ₂.toRingHom hk cf x w₂).symm)

theorem map_eq_of_etaValAt (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} {cf : J → ℤ}
    {x : J → Fin n → LatMod Dw (R ^ 4)} {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y₀ : FrPt Xo c S} {y : FrPt Xo c T} (hm : FrMap φ y₀ y) {v₀ : S} {v : T}
    (h₀ : EtaValAt Xo c R cf x y₀ v₀) (h : EtaValAt Xo c R cf x y v) : φ v₀ = v := by
  obtain ⟨S', _, _, α, y₀', ev₀, w₀, hα, hmα, hev₀, hw₀, e₀⟩ := h₀
  obtain ⟨T', _, _, β, y', ev, w, hβ, hmβ, hev, hw, e⟩ := h
  obtain ⟨U, _, _, ψ₁, ψ₂, hc, -, hinj⟩ := GlobalTheory.exists_faithfullyFlat_pushout c.F S T' S' (β.comp φ) α hα
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c T' U ψ₁ y'
  have hz₀ : FrMap (ψ₂.comp α) y₀ z :=
    hc ▸ FramedBaseChange.trans _ ψ₁ (FramedBaseChange.trans φ β hm hmβ) hz
  have key := map_etaExpr_eq_of_levels hL hR cf x ψ₁ ψ₂ hz (FramedBaseChange.cancel α ψ₂ hmα hz₀) hev hw hev₀ hw₀
  have hβi : Function.Injective β := hβ.injective
  refine hβi (hinj ?_)
  rw [e, key, ← e₀]
  exact DFunLike.congr_fun hc v₀

theorem exists_etaValAt (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw (R ^ 4)) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ∃ v, EtaValAt Xo c R cf x y v := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  obtain ⟨B, _, φ₀, ev₀, hφ, hev₀⟩ := (GlobalTheory.T.fullLinearLevel_cover_baseChange_torsor hL E H Dw l Xo _ hk).1 S y.x
  letI : Algebra c.F B := (φ₀.comp (algebraMap c.F S)).toAlgebra
  let φ : S →ₐ[c.F] B := { φ₀ with commutes' := fun _ => rfl }
  obtain ⟨y', hm⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c S B φ y
  obtain ⟨ev, hev⟩ : ∃ ev, IsFullLev Xo (R ^ 4) y'.x ev := by
    rw [hm.1]
    exact ⟨ev₀, hev₀⟩
  choose w hw using fun q => (existsUnique_nullVal hL hR hev q).exists
  obtain ⟨v, hv, -⟩ := GlobalTheory.existsUnique_preimage_of_faithfullyFlat c.F S B φ hφ (etaExpr (R ^ 4) cf x w)
    fun T _ _ ψ₁ ψ₂ hc => by
      obtain ⟨z, hz⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c B T ψ₁ y'
      have hz₀ : FrMap (ψ₂.comp φ) y z := hc ▸ FramedBaseChange.trans φ ψ₁ hm hz
      exact map_etaExpr_eq_of_levels hL hR cf x ψ₁ ψ₂ hz (FramedBaseChange.cancel φ ψ₂ hm hz₀) hev hw hev hw
  exact ⟨v, B, inferInstance, inferInstance, φ, y', ev, w, hφ, hm, hev, hw, hv⟩

theorem etaValAt_existsUnique_natural : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : ℕ), Odd R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (x : J → Fin n → LatMod Dw (R ^ 4)), (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃! v, EtaValAt Xo c R cf x y v) ∧ ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ v0 v, EtaValAt Xo c R cf x y0 v0 → EtaValAt Xo c R cf x y v → φ v0 = v := by
  intro hL E _ _ _ H Dw l Xo c R hR J _ n cf x
  refine ⟨fun S _ _ y => ?_, fun S T _ _ _ _ φ y₀ y hm v₀ v h₀ h => map_eq_of_etaValAt hL hR φ hm h₀ h⟩
  obtain ⟨v, hv⟩ := exists_etaValAt hL hR cf x y
  exact ⟨v, hv, fun v' hv' => map_eq_of_etaValAt hL hR (AlgHom.id c.F S) (FramedBaseChange.refl y) hv' hv⟩

end GlobalTheory.EtaForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShiftNullValNeZero
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaBase

open GlobalTheory.ThetaCoord GlobalTheory.VVRank

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem mk_eq_zero_iff (k : ℕ) (m : Dw.La) :
    (Submodule.Quotient.mk m : LatMod Dw k) = 0 ↔ ∃ m' : Dw.La, k • m' = m := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and, Nat.cast_smul_eq_nsmul]

theorem exists_shift {R : ℕ} (hR : R ≠ 0) (q : LatMod Dw (R ^ 4)) (hq : R • q = 0) :
    ∃ u : LatMod Dw R, (Submodule.Quotient.mk (R ^ 3 • qRep u) : LatMod Dw (R ^ 4)) = q := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨m', hm⟩ := (mk_eq_zero_iff (R ^ 4) (R • m)).1 hq
  have e : R ^ 3 • m' = m := by
    have h : R • R ^ 3 • m' = R • m := by rw [← hm, ← mul_nsmul', ← pow_succ']
    refine Dw.unimod.1 (LinearMap.ext fun v => nsmul_right_injective hR ?_)
    have := congrArg (fun t => Dw.EF t v) h
    simpa only [map_nsmul, LinearMap.smul_apply] using this
  refine ⟨Submodule.Quotient.mk m', ?_⟩
  have h : (Submodule.Quotient.mk (qRep (Submodule.Quotient.mk m' : LatMod Dw R)) : LatMod Dw R) =
      Submodule.Quotient.mk m' := Classical.choose_spec (Submodule.Quotient.mk_surjective _ _)
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub] at h ⊢
  obtain ⟨d, hd⟩ := (mk_eq_zero_iff R _).1 h
  refine (mk_eq_zero_iff _ _).2 ⟨d, ?_⟩
  rw [← e, ← smul_sub, ← hd, ← mul_nsmul', ← pow_succ]

variable (Xo : Moduli Dw l) (c : Coeff l)

theorem gen_ne_zero {K : Type} [CommRing K] [Nontrivial K] [Algebra c.F K] (y : FrPt Xo c K) :
    (SecM.ofSec Xo.univ.t.G y.s : SecM Xo.univ.t.G Xo.univ.t.PP.L 1 (Over.mk y.x)) ≠ 0 := fun h => by
  have h₀ : ∀ i, y.s.f i = 0 := fun i => congrFun (congrArg Subtype.val h) i
  exact zero_ne_one ((y.gen y.s).unique (y₁ := 0) (y₂ := 1) (fun i => by rw [h₀, MulZeroClass.mul_zero])
    (fun i => by rw [h₀, MulZeroClass.mul_zero]))

theorem exists_nullVal_ne_zero (hL : Laws) {K : Type} [Field K] [IsAlgClosed K] [Algebra c.F K] (y : FrPt Xo c K)
    (N : ℕ) {n : ℕ} (hn : 2 ≤ n) (a : ptO Xo y.x ⟶ Xo.univ.t.G) :
    ∃ z : ptO Xo y.x ⟶ Xo.univ.t.G, z ^ n = 1 ∧
      ∀ p w, IsNullVal Xo c N y p w → p ^ N = a * z → w ≠ 0 := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  have hK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨z, hz, hu⟩ := UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange (UnivPol.pol Xo) y.x hn hK y.s
    (gen_ne_zero Xo c y) a
  refine ⟨z, hz, ?_⟩
  rintro p w ⟨F, ⟨t', α₀, α, s₁, U, -, rfl, -, -, -, hs₁, hU, hF⟩, hw⟩ hp h₀
  let o : (Over.mk y.x).left := IsLocalRing.closedPoint K
  choose J hJ using fun χ : (Over.mk y.x).left ⟶ Xo.univ.t.G.left => exists_chart Xo.univ.t.PP.isLB (χ o)
  replace hJ : Good Xo.univ.t.PP.L o J := hJ
  have b₁ := sv_act hU.pt_eq hF (𝟙 _) hJ 1
  have b₂ := sv_mulPull hs₁ (𝟙 _) hJ t'
  have b₃ := sv_of_isValueAt hw (𝟙 _) hJ
  rw [Category.id_comp, _root_.mul_one] at b₁
  rw [Category.id_comp] at b₃
  rw [b₃, b₂, hp, h₀, map_zero, UT.ExactTerm.gs_zero' _ _ ⊤ trivial, MulZeroClass.zero_mul] at b₁
  exact ((Units.isUnit _).mul ((Units.isUnit _).mul (hu o J hJ))).ne_zero b₁.symm

end GlobalTheory.EtaBase

namespace GlobalTheory

open GlobalTheory.EtaBase

theorem exists_shift_nullVal_ne_zero : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : ℕ), Odd R → 1 < R → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y : FrPt Xo c K) (ev : LatMod Dw (R ^ 4) → (ptO Xo y.x ⟶ Xo.univ.t.G)) (w : LatMod Dw (R ^ 4) → K), IsFullLev Xo (R ^ 4) y.x ev → (∀ q, IsNullVal Xo c (R ^ 2) y (ev q) (w q)) → ∀ (n : ℕ) (x₀ : Fin n → Dw.La) (g : LevGrp Dw (R ^ 4)), ∃ u : Fin n → LatMod Dw R, ∀ b, w (g (shiftFam R x₀ u b)) ≠ 0 := by
  intro hL E _ _ _ H Dw l Xo c R _ hR K _ _ _ y ev w hev hw n x₀ g
  have hR₀ : R ≠ 0 := by omega
  have e₀ : ev 0 = 1 := by
    have := hev.1 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have es : ∀ (m : ℕ) q, ev (m • q) = ev q ^ m := fun m q => by
    induction m with
    | zero => rw [zero_smul, e₀, pow_zero]
    | succ m ih => rw [succ_nsmul, hev.1, ih, pow_succ]
  have sur := ((T.fullLinearLevel_cover_baseChange_torsor hL E H Dw l Xo (R ^ 4) (by positivity)).2.2.1 K y.x ev hev).1
  have key : ∀ x : Dw.La, ∃ u : LatMod Dw R,
      w (g (Submodule.Quotient.mk (x + R • qRep u))) ≠ 0 := fun x => by
    obtain ⟨z, hz, h⟩ := exists_nullVal_ne_zero Xo c hL y (R ^ 2) hR (ev (g (Submodule.Quotient.mk x)) ^ R ^ 2)
    obtain ⟨q, rfl⟩ := sur z (by rw [pow_succ', pow_mul, hz, one_pow])
    have hq : R • q = 0 := hev.2.2 K (RingHom.id K) _ _ (by rw [es, hz, e₀])
    obtain ⟨u, hu⟩ := exists_shift hR₀ (g.symm q) (by rw [← map_nsmul, hq, map_zero])
    refine ⟨u, h _ _ (hw _) ?_⟩
    rw [← es, ← es, ← hev.1, ← g.apply_symm_apply q, ← hu, ← map_nsmul, ← map_nsmul, ← map_add (f := _)]
    congr 2
    show (Submodule.Quotient.mk (R ^ 2 • (x + R • qRep u)) : LatMod Dw (R ^ 4)) =
      Submodule.Quotient.mk (R ^ 2 • x + R ^ 3 • qRep u)
    rw [smul_add, ← mul_nsmul', ← pow_succ]
  choose u hu using key
  exact ⟨fun b => u (x₀ b), fun b => hu (x₀ b)⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaSumEqOfWitnessesCommonAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaSumEqOfWitnessesCommonAlgebra
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_pull (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {n : ℕ} (Λ : GenLat E n) (N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (w : FrPt Xo c T) (hm : FrMap ψ y w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo y.x z)
    (ht : ∀ q b, tp q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b))
    (hF : ∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (tp q b) (F q i b)) :
    ∃ (z' : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo w.x ⟶ Xo.univ.t.G))
      (tp' : (Fin n → LevQ Dw l) → Fin n → (ptO Xo w.x ⟶ Xo.univ.t.G))
      (F' : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
        LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo w.x))),
      (∀ i, InZh Xo Λ N (z' i)) ∧ GeoInj Xo w.x z' ∧
      (∀ q b, tp' q b ^ N = levPt Xo w.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp' q b)) ∧
      (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N w.s (z' i b) (tp' q b) (F' q i b)) ∧
      ∀ q, ψ (∑ i, ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          ∏ b, nab y ((N : ℤ) ^ 2) (F q i b) (colOf m b)) =
        ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
          ∏ b, nab w ((N : ℤ) ^ 2) (F' q i b) (colOf m b) := by
  have hx : w.x = spMap ψ.toRingHom ≫ y.x := by
    unfold FrMap at hm
    exact hm.1
  let h : ptO Xo w.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hx.symm
  have hh : h.left = spMap ψ.toRingHom := rfl
  have hs := GlobalTheory.FramedBaseChange.isPullSec ψ hm h hh
  have hpull : ∀ q i b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G)
      (whiskerRight_snd _ _) (F q i b) (GlobalTheory.VVRank.pullS Xo.univ.t.G ((N : ℤ) ^ 2) h (F q i b)) :=
    fun q i b => GlobalTheory.VVRank.isPullSec_pullS _ _ h _
  obtain ⟨hZ, -, hG, -⟩ := GlobalTheory.T.inZh_geoInj_stable_alt E H Dw l Xo n Λ N
  refine ⟨fun i b => h ≫ z i b, fun q b => h ≫ tp q b,
    fun q i b => GlobalTheory.VVRank.pullS Xo.univ.t.G ((N : ℤ) ^ 2) h (F q i b),
    fun i => hZ _ _ h _ (hz i), hG S T y.x w.x ψ.toRingHom h hh _ z hg, fun q b => ⟨?_, ?_⟩,
    fun q i b => (GlobalTheory.VtBaseChange.isVtOver_isUUOver_baseChange E H Dw l Xo N ⊥ _ _ h y.s w.s hs
      (F q i b) _ (hpull q i b)).2 (z i b) (tp q b) (hF q i b), fun q => ?_⟩
  · dsimp only
    rw [← MonObj.comp_pow, (ht q b).1]
    unfold levPt
    rw [← Category.assoc, toUnit_unique (h ≫ toUnit _) (toUnit _)]
  · obtain ⟨j, hj⟩ := (ht q b).2
    refine ⟨j, ?_⟩
    unfold KilledBy at hj ⊢
    intro x hx
    rw [Category.assoc, hj x hx, MonObj.comp_one]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact GlobalTheory.T.harmonicValue_baseChange_alt hC E H Dw l Xo c nab hnab S T ψ y w hm h hh a n P hP N (F q i)
        (fun b => GlobalTheory.VVRank.pullS Xo.univ.t.G ((N : ℤ) ^ 2) h (F q i b)) (hpull q i)

theorem eq_of_local {K T : Type} [Field K] [CommRing T] [Algebra K T] (u v : T)
    (h : ∀ (U : Type) [CommRing U] [IsLocalRing U] [Algebra K U] (κ : T →ₐ[K] U), κ u = κ v) : u = v := by
  rw [← sub_eq_zero]
  refine eq_zero_of_localization (u - v) fun J hJ => ?_
  have := hJ.isPrime
  have e := h (Localization.AtPrime J) (IsScalarTower.toAlgHom K T (Localization.AtPrime J))
  simpa [map_sub, sub_eq_zero] using e

theorem shortSum_eq_of_witnesses : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (S1 : Type) [CommRing S1] [Algebra c.F S1] (φ1 : S →ₐ[c.F] S1) (y1 : FrPt Xo c S1) (z1 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y1.x ⟶ Xo.univ.t.G)) (tp1 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y1.x ⟶ Xo.univ.t.G)) (F1 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y1.x))) (S2 : Type) [CommRing S2] [Algebra c.F S2] (φ2 : S →ₐ[c.F] S2) (y2 : FrPt Xo c S2) (z2 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y2.x ⟶ Xo.univ.t.G)) (tp2 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y2.x ⟶ Xo.univ.t.G)) (F2 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y2.x))), FrMap φ1 y y1 → FrMap φ2 y y2 → (∀ i, InZh Xo Λ N (z1 i)) → GeoInj Xo y1.x z1 → (∀ q b, tp1 q b ^ N = levPt Xo y1.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp1 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y1.s (z1 i b) (tp1 q b) (F1 q i b)) → (∀ i, InZh Xo Λ N (z2 i)) → GeoInj Xo y2.x z2 → (∀ q b, tp2 q b ^ N = levPt Xo y2.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp2 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y2.s (z2 i b) (tp2 q b) (F2 q i b)) → ∀ (T : Type) [CommRing T] [Algebra c.F T] (ψ1 : S1 →ₐ[c.F] T) (ψ2 : S2 →ₐ[c.F] T), ψ1.comp φ1 = ψ2.comp φ2 → ∀ q, ψ1 (∑ i, ∑ m ∈ P.support, algebraMap c.F S1 (P.coeff m) * ∏ b, nab y1 ((N : ℤ) ^ 2) (F1 q i b) (colOf m b)) = ψ2 (∑ i, ∑ m ∈ P.support, algebraMap c.F S2 (P.coeff m) * ∏ b, nab y2 ((N : ℤ) ^ 2) (F2 q i b) (colOf m b)) := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab n Λ N hUn hTr hLev a P hP S _ _ y S1 _ _ φ1 y1 z1 tp1 F1
    S2 _ _ φ2 y2 z2 tp2 F2 hm1 hm2 hz1 hg1 ht1 hF1 hz2 hg2 ht2 hF2 T _ _ ψ1 ψ2 hψ q
  refine eq_of_local (K := c.F) _ _ fun U _ _ _ κ => ?_
  obtain ⟨yU, hyU⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c S U ((κ.comp ψ1).comp φ1) y
  have e : (κ.comp ψ1).comp φ1 = (κ.comp ψ2).comp φ2 := by
    rw [AlgHom.comp_assoc, AlgHom.comp_assoc, hψ]
  have hU1 : FrMap (κ.comp ψ1) y1 yU := GlobalTheory.FramedBaseChange.cancel φ1 (κ.comp ψ1) hm1 hyU
  have hU2 : FrMap (κ.comp ψ2) y2 yU := GlobalTheory.FramedBaseChange.cancel φ2 (κ.comp ψ2) hm2 (e ▸ hyU)
  obtain ⟨z1', tp1', F1', hz1', hg1', ht1', hF1', hs1⟩ :=
    exists_pull hC nab hnab Λ N a P hP (κ.comp ψ1) y1 yU hU1 z1 tp1 F1 hz1 hg1 ht1 hF1
  obtain ⟨z2', tp2', F2', hz2', hg2', ht2', hF2', hs2⟩ :=
    exists_pull hC nab hnab Λ N a P hP (κ.comp ψ2) y2 yU hU2 z2 tp2 F2 hz2 hg2 ht2 hF2
  have key := GlobalTheory.T.isotropicSum_independent_of_choices_local hL E H Dw l Xo c nab hnab n Λ N hUn hTr hLev P U yU z1' tp1' F1' z2' tp2' F2'
    hz1' hg1' ht1' hF1' hz2' hg2' ht2' hF2' q
  have h1 := hs1 q
  have h2 := hs2 q
  simp only [AlgHom.comp_apply] at h1 h2
  rw [h1, h2]
  exact key

end GlobalTheory.ShortCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaSumEqOfWitnessesCommonAlgebraStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortThetaSum_eq_of_witnesses_common_algebra : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (S1 : Type) [CommRing S1] [Algebra c.F S1] (φ1 : S →ₐ[c.F] S1) (y1 : FrPt Xo c S1) (z1 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y1.x ⟶ Xo.univ.t.G)) (tp1 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y1.x ⟶ Xo.univ.t.G)) (F1 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y1.x))) (S2 : Type) [CommRing S2] [Algebra c.F S2] (φ2 : S →ₐ[c.F] S2) (y2 : FrPt Xo c S2) (z2 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y2.x ⟶ Xo.univ.t.G)) (tp2 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y2.x ⟶ Xo.univ.t.G)) (F2 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y2.x))), FrMap φ1 y y1 → FrMap φ2 y y2 → (∀ i, InZh Xo Λ N (z1 i)) → GeoInj Xo y1.x z1 → (∀ q b, tp1 q b ^ N = levPt Xo y1.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp1 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y1.s (z1 i b) (tp1 q b) (F1 q i b)) → (∀ i, InZh Xo Λ N (z2 i)) → GeoInj Xo y2.x z2 → (∀ q b, tp2 q b ^ N = levPt Xo y2.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp2 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y2.s (z2 i b) (tp2 q b) (F2 q i b)) → ∀ (T : Type) [CommRing T] [Algebra c.F T] (ψ1 : S1 →ₐ[c.F] T) (ψ2 : S2 →ₐ[c.F] T), ψ1.comp φ1 = ψ2.comp φ2 → ∀ q, ψ1 (∑ i, ∑ m ∈ P.support, algebraMap c.F S1 (P.coeff m) * ∏ b, nab y1 ((N : ℤ) ^ 2) (F1 q i b) (colOf m b)) = ψ2 (∑ i, ∑ m ∈ P.support, algebraMap c.F S2 (P.coeff m) * ∏ b, nab y2 ((N : ℤ) ^ 2) (F2 q i b) (colOf m b)) := by
  first | exact @GlobalTheory.ShortCompare.shortSum_eq_of_witnesses | exact GlobalTheory.ShortCompare.shortSum_eq_of_witnesses | (intros; apply GlobalTheory.ShortCompare.shortSum_eq_of_witnesses <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModelWeightSizeSpreadBound
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModelWeightSizeSpreadBound
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

noncomputable section

namespace GlobalTheory.RunIn.WtSize

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sum_cm {M : Type} [AddCommMonoid M] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (g : (E →+* ℂ) → M) :
    ∑ τ : X.Ψ, (g τ.1 + g (ComplexEmbedding.conjugate τ.1)) = ∑ τ, g τ := by
  classical
  have hs : ∑ τ : X.Ψ, (g τ.1 + g (ComplexEmbedding.conjugate τ.1)) =
      ∑ τ ∈ X.Ψ, (g τ + g (ComplexEmbedding.conjugate τ)) :=
    Finset.sum_coe_sort X.Ψ (fun τ => g τ + g (ComplexEmbedding.conjugate τ))
  rw [hs, Finset.sum_add_distrib, ← Finset.sum_add_sum_compl X.Ψ g]
  congr 1
  refine Finset.sum_nbij' (fun τ => ComplexEmbedding.conjugate τ) (fun τ => ComplexEmbedding.conjugate τ)
    ?_ ?_ ?_ ?_ ?_
  · intro τ hτ
    simpa [Finset.mem_compl] using (X.cmType τ).1 hτ
  · intro τ hτ
    have h1 : τ ∉ X.Ψ := by simpa [Finset.mem_compl] using hτ
    by_contra h2
    exact h1 ((X.cmType τ).2 (by simpa using h2))
  · intro τ _
    simp
  · intro τ _
    simp
  · intro τ _
    rfl

theorem two_mul_card_cm {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) :
    2 * Fintype.card X.Ψ = Module.finrank ℚ E := by
  have h := sum_cm X (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  rw [← NumberField.Embeddings.card E ℂ, ← h]
  ring

theorem sum_row_le (r p0 : ℕ) (hp : p0 ≤ r) (u v : ℕ → ℕ) :
    ∑ j : Fin r, (if p0 ≤ (j : ℕ) then u ((j : ℕ) - p0) else v (p0 - 1 - (j : ℕ))) ≤
      ∑ i ∈ Finset.range r, u i + ∑ i ∈ Finset.range r, v i := by
  classical
  rw [Finset.sum_ite]
  gcongr
  · calc ∑ j ∈ Finset.univ.filter (fun j : Fin r => p0 ≤ (j : ℕ)), u ((j : ℕ) - p0)
          = ∑ i ∈ Finset.image (fun j : Fin r => (j : ℕ) - p0) (Finset.univ.filter (fun j : Fin r => p0 ≤ (j : ℕ))), u i := by
            refine (Finset.sum_image ?_).symm
            intro a ha b hb hab
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
            dsimp only at hab
            exact Fin.ext (by omega)
      _ ≤ ∑ i ∈ Finset.range r, u i := by
            apply Finset.sum_le_sum_of_subset
            intro i hi
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            obtain ⟨j, _, rfl⟩ := hi
            simp only [Finset.mem_range]
            have := j.isLt
            omega
  · calc ∑ j ∈ Finset.univ.filter (fun j : Fin r => ¬ p0 ≤ (j : ℕ)), v (p0 - 1 - (j : ℕ))
          = ∑ i ∈ Finset.image (fun j : Fin r => p0 - 1 - (j : ℕ)) (Finset.univ.filter (fun j : Fin r => ¬ p0 ≤ (j : ℕ))), v i := by
            refine (Finset.sum_image ?_).symm
            intro a ha b hb hab
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
            dsimp only at hab
            exact Fin.ext (by omega)
      _ ≤ ∑ i ∈ Finset.range r, v i := by
            apply Finset.sum_le_sum_of_subset
            intro i hi
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            obtain ⟨j, hj, rfl⟩ := hi
            simp only [Finset.mem_range]
            have := j.isLt
            omega

theorem spread_le {r : ℕ} (x b : Fin r → ℝ) (m : ℝ) (hm : 0 ≤ m) (hb : ∀ i, 0 ≤ b i)
    (hx : ∀ i, |x i| = b i + m) : (⨆ i, x i) - ⨅ i, x i ≤ ∑ i, b i + 2 * m := by
  classical
  rcases isEmpty_or_nonempty (Fin r) with hr | hr
  · rw [Real.iSup_of_isEmpty, Real.iInf_of_isEmpty]
    have : 0 ≤ ∑ i, b i := Finset.sum_nonneg (fun i _ => hb i)
    linarith
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := x)
    obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := x)
    rw [← hi, ← hj]
    have hxi : x i ≤ b i + m := (le_abs_self _).trans (hx i).le
    have hxj : -(b j + m) ≤ x j := by
      have := neg_abs_le (x j)
      rw [hx j] at this
      exact this
    by_cases hij : i = j
    · subst hij
      have : 0 ≤ ∑ k, b k := Finset.sum_nonneg (fun k _ => hb k)
      linarith
    · have hpair : b i + b j ≤ ∑ k, b k := by
        rw [← Finset.sum_pair hij]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => hb k)
      linarith

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ}

theorem relab_bijective (c : Coeff l) (σ : c.F →+* ℂ) : Function.Bijective (relab (E := E) c σ) := by
  have hinj : Function.Injective (relab (E := E) c σ) := by
    intro τ τ' hττ'
    unfold relab embF at hττ'
    ext x
    have h1 := congrArg (fun f : E →+* ℂ => f x) hττ'
    simp only [RingHom.comp_apply] at h1
    exact congrArg Subtype.val (σ.injective h1)
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

private lemma entry_abs (p0 j s t h : ℕ) :
    |(((if p0 ≤ j then (s : ℤ) + (h : ℤ) else -(t : ℤ) - (h : ℤ) : ℤ)) : ℝ)| =
      (((if p0 ≤ j then s else t : ℕ)) : ℝ) + (h : ℝ) := by
  split_ifs with hj
  · push_cast
    exact abs_of_nonneg (by positivity)
  · push_cast
    rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) t, Nat.cast_nonneg (α := ℝ) h])]
    ring

theorem laU_bounds (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) (B : ℕ)
    (hB : ∑ τ, ∑ i ∈ Finset.range r, a (τ, i) ≤ B) :
    (∑ τ, (U.X k).spread (laU U a n k) τ) ≤ (B : ℝ) + Fintype.card (U.X k).Ψ * n ∧
      (∑ τ, ∑ i, |((laU U a n k τ i : ℤ) : ℝ)|) ≤ (B : ℝ) + Fintype.card (U.X k).Ψ * r * n / 2 := by
  unfold laU
  have hp : (U.X k).p0 ≤ r := (U.X k).p0_le
  have hbij := relab_bijective (E := E) c σ
  have hm2 : 2 * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
    have : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    exact_mod_cast this
  have htot : ∑ τ : (U.X k).Ψ, (∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ.1, i) + ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) (conjEmb τ.1), i)) ≤ B := by
    have hinvb : Function.Bijective (Function.invFun (relab (E := E) c σ)) :=
      ⟨(Function.rightInverse_invFun hbij.2).injective, (Function.leftInverse_invFun hbij.1).surjective⟩
    calc _ = ∑ τ : (U.X k).Ψ, ((fun τ' => ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ', i)) τ.1 +
            (fun τ' => ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ', i)) (ComplexEmbedding.conjugate τ.1)) := rfl
      _ = ∑ τ, (fun τ' => ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ', i)) τ :=
          sum_cm (U.X k) (fun τ' => ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ', i))
      _ = ∑ τ, ∑ i ∈ Finset.range r, a (τ, i) := Fintype.sum_bijective _ hinvb _ _ (fun _ => rfl)
      _ ≤ B := hB
  have hsum : ∑ τ : (U.X k).Ψ, ∑ j : Fin r, (((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) ≤ (B : ℝ) := by
    calc _ ≤ ∑ τ : (U.X k).Ψ, (((∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ.1, i) + ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) (conjEmb τ.1), i)) : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro τ _
          rw [← Nat.cast_sum]
          exact_mod_cast sum_row_le r (U.X k).p0 hp (fun i => a (Function.invFun (relab c σ) τ.1, i))
            (fun i => a (Function.invFun (relab c σ) (conjEmb τ.1), i))
      _ ≤ (B : ℝ) := by
          rw [← Nat.cast_sum]
          exact_mod_cast htot
  have h0 : (0 : ℝ) ≤ Fintype.card (U.X k).Ψ := by positivity
  have hr0 : (0 : ℝ) ≤ r := by positivity
  constructor
  · calc _ ≤ ∑ τ : (U.X k).Ψ, (∑ j : Fin r, (((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) + 2 * ((n / 2 : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro τ _
          unfold ReciprocityTheory.ChartRestriction.G.FD.Data.spread
          exact spread_le _ _ _ (by positivity) (fun j => by positivity) (fun j => entry_abs _ _ _ _ _)
      _ ≤ (B : ℝ) + Fintype.card (U.X k).Ψ * n := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          nlinarith [hsum, mul_le_mul_of_nonneg_left hm2 h0]
  · calc _ = ∑ τ : (U.X k).Ψ, ∑ j : Fin r, ((((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) + ((n / 2 : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro τ _
          apply Finset.sum_congr rfl
          intro j _
          exact entry_abs _ _ _ _ _
      _ ≤ (B : ℝ) + Fintype.card (U.X k).Ψ * r * n / 2 := by
          have e : ∀ τ : (U.X k).Ψ, ∑ j : Fin r, ((((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) + ((n / 2 : ℕ) : ℝ)) = ∑ j : Fin r, (((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) + r * ((n / 2 : ℕ) : ℝ) := by
            intro τ
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Finset.sum_congr rfl (fun τ _ => e τ), Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
          nlinarith [hsum, mul_le_mul_of_nonneg_left hm2 (mul_nonneg h0 hr0)]

theorem sum_wtA_le {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (m : ℕ) :
    ∑ τ, ∑ i ∈ Finset.range m, wtA w (τ, i) ≤ WeightAlgebra.DF w := by
  classical
  unfold wtA WeightAlgebra.DF WeightAlgebra.degP ext0
  have key : ∀ (q : ℕ) (g : Fin q → ℕ),
      ∑ i ∈ Finset.range m, (if h : i < q then g ⟨i, h⟩ else 0) ≤ ∑ i, g i := by
    intro q g
    calc _ ≤ ∑ i ∈ Finset.range q, (if h : i < q then g ⟨i, h⟩ else 0) := by
          apply Finset.sum_le_sum_of_ne_zero
          intro i _ hi
          rw [Finset.mem_range]
          by_contra hc
          exact hi (dif_neg hc)
      _ = ∑ i, g i := by
          rw [Finset.sum_range]
          simp
  rw [Finset.sum_congr rfl (fun τ _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_le_sum (fun t _ => ?_)
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact add_le_add (key _ _) (key _ _)

theorem laU_wtA_size : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp, (∑ τ, ((T.U j σ).X k).spread (laU (T.U j σ) (wtA w) w.n k) τ) ≤ (WeightAlgebra.DF w : ℝ) + D.R.f * w.n ∧ (∑ τ, ∑ i, |((laU (T.U j σ) (wtA w) w.n k τ i : ℤ) : ℝ)|) ≤ (WeightAlgebra.DF w : ℝ) + D.R.f * D.R.r * w.n / 2 := by
  intro D T h j hj w σ hσ k
  have h2 := two_mul_card_cm ((T.U j σ).X k)
  have h3 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    have h4 : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.der.finrank_E
    rw [h4]
    simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
    ring
  have hc : (Fintype.card ((T.U j σ).X k).Ψ : ℝ) = D.R.f := by
    have : Fintype.card ((T.U j σ).X k).Ψ = D.R.f := by omega
    exact_mod_cast this
  have hb := laU_bounds (T.U j σ) (wtA w) w.n k (WeightAlgebra.DF w) (sum_wtA_le w _)
  rw [hc] at hb
  exact hb

end GlobalTheory.RunIn.WtSize
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModelWeightSizeSpreadBoundStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelWeight_size_spread_bound : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp, (∑ τ, ((T.U j σ).X k).spread (laU (T.U j σ) (wtA w) w.n k) τ) ≤ (WeightAlgebra.DF w : ℝ) + D.R.f * w.n ∧ (∑ τ, ∑ i, |((laU (T.U j σ) (wtA w) w.n k τ i : ℤ) : ℝ)|) ≤ (WeightAlgebra.DF w : ℝ) + D.R.f * D.R.r * w.n / 2 := by
  first | exact @GlobalTheory.RunIn.WtSize.laU_wtA_size | exact GlobalTheory.RunIn.WtSize.laU_wtA_size | (intros; apply GlobalTheory.RunIn.WtSize.laU_wtA_size <;> assumption)
end
end
