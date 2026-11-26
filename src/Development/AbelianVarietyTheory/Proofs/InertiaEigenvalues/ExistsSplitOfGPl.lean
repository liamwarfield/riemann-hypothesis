module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DatEqOfPhiHat
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaClassSumDominantWeightIsCuspForm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSecOfMoveInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitOfGPl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain GlobalTheory.HeightCounting
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FormInner

section Plain

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

open GlobalTheory.InertUmax


omit [IsCMField L] in
theorem exists_trunc (b : AFplus L) : ∃ c : AFplus L, (∀ w, c w ∈ w.adicCompletionIntegers (maximalRealSubfield L)) ∧
    ∀ w, b w ∈ w.adicCompletionIntegers (maximalRealSubfield L) → c w = b w := by
  have h : ∀ w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), ∃ z : w.adicCompletion (maximalRealSubfield L),
      z ∈ w.adicCompletionIntegers (maximalRealSubfield L) ∧ (b w ∈ w.adicCompletionIntegers (maximalRealSubfield L) → z = b w) := by
    intro w
    by_cases hw : b w ∈ w.adicCompletionIntegers (maximalRealSubfield L)
    · exact ⟨b w, hw, fun _ => rfl⟩
    · exact ⟨0, zero_mem _, fun h => absurd h hw⟩
  choose z h1 h2 using h
  exact ⟨⟨z, Filter.Eventually.of_forall h1⟩, h1, h2⟩

theorem exists_int_off (z : AL L) : ∃ S : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L))), ∃ Y ∈ ALint L,
    ∀ w ∉ S, ReciprocityTheory.Aut.compAt L w z = ReciprocityTheory.Aut.compAt L w Y := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨∅, 0, zero_mem _, fun _ _ => rfl⟩
  | add x y hx hy =>
    obtain ⟨S, Y, hY, h⟩ := hx
    obtain ⟨S', Y', hY', h'⟩ := hy
    refine ⟨S ∪ S', Y + Y', add_mem hY hY', fun w hw => ?_⟩
    rw [Finset.mem_union, not_or] at hw
    rw [map_add (f := _), map_add (f := _), h w hw.1, h' w hw.2]
  | tmul x a =>
    obtain ⟨m, hm, o, ho⟩ := GlobalTheory.FinTypCount.exists_nat_smul_int x
    have hm' : (m : maximalRealSubfield L) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    obtain ⟨b, hb⟩ : ∃ b : AFplus L, b = (m : maximalRealSubfield L)⁻¹ • a := ⟨_, rfl⟩
    have e : (x ⊗ₜ[maximalRealSubfield L] a : AL L) = (o : L) ⊗ₜ[maximalRealSubfield L] b := by
      rw [ho, hb, ← Nat.cast_smul_eq_nsmul (maximalRealSubfield L), TensorProduct.smul_tmul, smul_inv_smul₀ hm']
    have hfin : {w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) |
        b w ∉ w.adicCompletionIntegers (maximalRealSubfield L)}.Finite := Filter.eventually_cofinite.1 b.2
    obtain ⟨c, hc, hc'⟩ := exists_trunc b
    refine ⟨hfin.toFinset, (o : L) ⊗ₜ[maximalRealSubfield L] c, GlobalTheory.FinTypCount.tmul_mem_ALint o hc, fun w hw => ?_⟩
    rw [e, compAt_tmul, compAt_tmul, hc' w (by simpa using hw)]

theorem mem_ALint_of_comp (z : AL L) (h : ∀ w, ∃ Y ∈ ALint L, ReciprocityTheory.Aut.compAt L w Y = ReciprocityTheory.Aut.compAt L w z) : z ∈ ALint L := by
  classical
  obtain ⟨S, Y, hY, hS⟩ := exists_int_off z
  choose Z hZ e using h
  have key : z - (Y + ∑ v ∈ S, (Z v - Y) * ((1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v 1)) = 0 := by
    apply eq_zero_of_compAt
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_add (f := _), map_sum]
    simp only [map_mul, compAt_tmul]
    by_cases hw : w ∈ S
    · rw [Finset.sum_eq_single w (fun v _ hv => by rw [sgl_ne L v 1 (Ne.symm hv), TensorProduct.tmul_zero, mul_zero])
        (fun h => absurd hw h), sgl_same, ← Algebra.TensorProduct.one_def, mul_one, map_sub, e]
      ring
    · rw [Finset.sum_eq_zero fun v hv => by
        rw [sgl_ne L v 1 (fun h : w = v => hw (h ▸ hv)), TensorProduct.tmul_zero, mul_zero], hS w hw]
      ring
  rw [sub_eq_zero.1 key]
  exact add_mem hY (Subring.sum_mem _ fun v _ => mul_mem (sub_mem (hZ v) hY) (one_tmul_sgl_mem L v 1 (one_mem _)))

theorem le_Umax_of_prod {J : Subgroup (GAf L n)} (hJ : NG.IsProdLevel J)
    (h : ∀ v, ∀ κ ∈ J, TrivOutside {v} κ → κ ∈ Umax L n) : J ≤ Umax L n := by
  intro κ hκ i j
  refine mem_ALint_of_comp _ fun w => ?_
  obtain ⟨κ', h1, h2, h3⟩ := hJ κ hκ w
  exact ⟨_, h w κ' h1 h2 i j, congrFun (congrFun h3 i) j⟩

theorem mem_Umax_of_para (s : SplitPlace L) {r : ℕ} {κ : GAf L n} (h1 : TrivOutside {s.v} κ) (h2 : NG.ParaRT s r (s.loc n κ)) :
    κ ∈ Umax L n := by
  have h := GlobalTheory.HeckeStdFacts.mem_GLint_iff.1 h2.1
  exact GlobalTheory.HeckeStdFacts.mem_Umax_of_loc s κ h1 h.1 (fun i j => by
    rw [map_inv]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h.2 i j))

end Plain

theorem exists_split_of_gPl (D : D7) : ∀ v ∈ Formalism.L2.gPl D, ∃ (k : Fin 2) (u : D.nd.PlG k) (s : SplitPlace D.host.E),
    s.v = v ∧ s.w = D.naut.plGw k u := by
  rintro v ⟨w, hw, k, hk⟩
  obtain ⟨u, hu⟩ := GlobalTheory.DimPartsCompare.cover k w hk
  obtain ⟨s, hs⟩ := GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D ⟨k, u⟩
  refine ⟨k, u, s, HeightOneSpectrum.ext ?_, hs⟩
  rw [← s.w_under, hs]
  refine Eq.trans ?_ hw
  rcases hu with rfl | rfl
  · rfl
  · ext a
    refine GlobalTheory.DimPartsCompare.isConjPl_cPl _ _ _ ?_
    rw [GlobalTheory.SplitPlaceOver.host_conj_eq']
    exact ((IsCMField.complexConj D.host.E).commutes (a : maximalRealSubfield D.host.E)).symm

theorem level_le_Umax {D : D7} {M : MtFam D} {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E}
    {Q : D.what₂.places.Pl → Finset (PlE D.host)} (h : MtInput D M tup Q) (w : D.what₂.places.Pl) (j : Fin D.R.m) :
    (M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)).J ≤ Umax D.host.E D.R.nV := by
  refine le_Umax_of_prod (h.prod w j) fun v κ hκ hv => ?_
  by_cases hg : v ∈ Formalism.L2.gPl D
  · obtain ⟨k, u, s, rfl, hs⟩ := exists_split_of_gPl D v hg
    obtain ⟨ψ₀, ξ, -, -, hl⟩ := h.uni w j k u s hs
    exact mem_Umax_of_para s hv ((hl.mem κ hv).1 hκ).1
  by_cases hq : v ∈ qPl D (tup (D.what₂.muTw w) j)
  · obtain ⟨s, ξ, rfl, -, hl⟩ := h.para w j v hq
    exact mem_Umax_of_para s hv ((hl.mem κ hv).1 hκ)
  · refine (h.hyp w j κ fun u hu => hv u ?_).1.1 hκ
    rintro rfl
    exact hu fun h' => h'.elim hg hq

end GlobalTheory.FormInner

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspCoefficient
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspOfThetaSum
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ThetaSumDescent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

noncomputable def evHom {S : Type} [CommRing S] [_root_.IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) : Rul Xo c →+* S where
  toFun f := evR Xo c f y
  map_one' := evalAt_one _ _ y
    (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c S y)
  map_mul' f f' := evalAt_mul _ _ f f' y
  map_zero' := evalAt_zero _ _ y
  map_add' f f' := evalAt_add _ _ f f' y

noncomputable def secZero (Xo : Moduli Dw l) (c : Coeff l) : Subring (Rul Xo c) :=
  { (sec Xo c 0 0).toAddSubgroup with
    one_mem' := ⟨fun _ _ φ _ _ _ => (map_one φ).symm, fun p t _ _ _ => by
      have h0 : wchar (S := p.R) (ex Dw 0 0) t = 1 := Finset.prod_eq_one fun i _ => by cases i <;> exact pow_zero _
      rw [h0, one_mul]
      rfl⟩
    mul_mem' := fun ha hb => by simpa using sec_mul Xo c 0 0 0 0 ha hb }

theorem cases_of_pow_succ {z : ℂ} {e : ℕ} (he : 0 < e) (hz : z ^ (e + 1) = z) :
    ‖z + 1 - z ^ e‖ = 1 ∧ ‖1 - (z ^ e + z ^ e)‖ = 1 := by
  by_cases h0 : z = 0
  · simp [h0, he.ne']
  · have h1 : z ^ e = 1 := mul_right_cancel₀ h0 (by rw [← pow_succ, hz, one_mul])
    have h2 : ‖z‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg z) he.ne').1 (by rw [← norm_pow, h1, norm_one])
    rw [h1]
    norm_num [h2]

theorem evR_eq_of_marked_pow [inst : Algebra c.F ℂ] (hσ : GoodEmb c (algebraMap c.F ℂ)) (hA : l.A = 1) {f : Rul Xo c}
    (hf : f ∈ sec Xo c 0 0) {m : ℕ} (hm0 : 0 < m) (hfm : f ^ (m + 1) = f) {r g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {L : Lt E r} (hr : 1 ≤ r)
    (hs : IsSympl X bas) {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hm : ∀ a, mk a ∈ L) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hx' : x' ∈ X.dom) {y y' : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x' L y')
    (hk : A.Marked mk) (hk' : A'.Marked mk) : evR Xo c f y = evR Xo c f y' := by
  obtain ⟨σ, rfl⟩ : ∃ σ : c.F →+* ℂ, inst = σ.toAlgebra := ⟨algebraMap c.F ℂ, Algebra.algebra_ext _ _ fun _ => rfl⟩
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hf' : f ∈ secZero Xo c := hf
  have hz : ∀ z : FrPt Xo c ℂ, evHom z f ^ (m + 1) = evHom z f := fun z => by rw [← map_pow, hfm]
  have e1 : ∀ z : FrPt Xo c ℂ, evR Xo c (f + 1 - f ^ m) z = evHom z f + 1 - evHom z f ^ m := fun z => by
    change evHom z _ = _
    simp only [(evHom z).map_sub, (evHom z).map_add, (evHom z).map_one, (evHom z).map_pow]
  have e2 : ∀ z : FrPt Xo c ℂ, evR Xo c (1 - (f ^ m + f ^ m)) z = 1 - (evHom z f ^ m + evHom z f ^ m) := fun z => by
    change evHom z _ = _
    simp only [(evHom z).map_sub, (evHom z).map_add, (evHom z).map_one, (evHom z).map_pow]
  have h1 := evR_eq_of_marked σ hσ hA (f := f + 1 - f ^ m) (show _ ∈ secZero Xo c from sub_mem (add_mem hf' (one_mem _)) (pow_mem hf' m))
    (fun z => (congrArg norm (e1 z)).trans (cases_of_pow_succ hm0 (hz z)).1) hr hs hm x hx x' hx' y y' A A' hk hk'
  have h2 := evR_eq_of_marked σ hσ hA (f := 1 - (f ^ m + f ^ m))
    (show _ ∈ secZero Xo c from sub_mem (one_mem _) (add_mem (pow_mem hf' m) (pow_mem hf' m)))
    (fun z => (congrArg norm (e2 z)).trans (cases_of_pow_succ hm0 (hz z)).2) hr hs hm x hx x' hx' y y' A A' hk hk'
  rw [e1, e1] at h1
  rw [e2, e2] at h2
  change evHom y f = evHom y' f
  linear_combination h1 - (1 / 2 : ℂ) * h2


set_option maxHeartbeats 1000000 in
theorem mem_cusp_of_thetaSum (d : DeltaDat Xo c n) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (hr1 : 1 ≤ r)
    (hU : ∀ σ, GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) (hA : l.A = 1) (hlev : d.IsLev) (hA₂ : d.l₂.A = 1)
    [StarRing (𝓞 E)] (hnab : IsNab d.Xo₂ d.c₂ d.nab₂) (Λ : GenLat E n) (N : ℕ) (hun : Λ.Unimod) (hT : Λ.TrivAt d.l₂.M)
    (hO : Λ.LevOK N d.l₂.M) (a : (E →+* ℂ) × ℕ → ℕ) (hD : Dom a n) (hL : LastPos Dw a)
    {T : Type} [Fintype T] (cs : T → Rul d.Xo₂ d.c₂) (m : ℕ) (hm : 0 < m) (w : T → (Fin n → LevQ Dw d.l₂) → c.F)
    (P : T → MvPolynomial (LtN Dw n) c.F) (hcs : ∀ t, cs t ∈ sec d.Xo₂ d.c₂ 0 0 ∧ cs t ^ (m + 1) = cs t)
    (hP : ∀ t, P t ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    (f : Rul Xo c) (hsec : f ∈ sec Xo c a n)
    (hval : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
      (∀ x : c.F, algebraMap d.c₂.F k (d.eF x) = algebraMap c.F k x) →
      ∀ (y : FrPt Xo c k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → ∃ v : T → k,
        (∀ t, thLaValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w t q)) Λ N
          (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (P t)) y₂ (v t)) ∧
        evR Xo c f y = ∑ t, evR d.Xo₂ d.c₂ (cs t) y₂ * v t) :
    f ∈ Formalism.L2.PjFree.cusp Xo c U a n := by
  have hci := GlobalTheory.chartIndependence_unconditional
  refine (Formalism.L2.PjFree.mem_cusp Xo c U a n f).2
    ⟨hsec, fun σ hσ => Formalism.L2.PjFree.holCusp_mem_holSub _ _ fun k => ?_⟩
  have hu := hU σ hσ
  obtain ⟨W⟩ := nonempty_uw hu
  letI : Algebra c.F ℂ := σ.toAlgebra
  letI A₂ : Algebra d.c₂.F ℂ := (σ.comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  have halg : ∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t := fun t => by
    change σ (d.eF.symm (d.eF t)) = σ t
    rw [AlgEquiv.symm_apply_apply]
  have hcomp : (algebraMap d.c₂.F ℂ).comp (d.eF : c.F →+* d.c₂.F) = σ := RingHom.ext fun t => halg t
  have hσ₂ : GoodEmb d.c₂ (algebraMap d.c₂.F ℂ) := by
    have h1 : d.eF (IntermediateField.inclusion c.le (baseKA l).ρ) =
        IntermediateField.inclusion d.c₂.le (baseKA d.l₂).ρ := Subtype.ext rfl
    change algebraMap d.c₂.F ℂ (IntermediateField.inclusion d.c₂.le (baseKA d.l₂).ρ) = _
    rw [← h1, halg]
    exact hσ
  have hn : Even n := hD.2
  obtain ⟨-, hsd, hmk, -⟩ := uw_lattice E H Dw l Xo c σ r (U σ) hσ hu hr1 W k
  obtain ⟨Dc, hDe, hk⟩ := exists_dic E H Dw l c σ r W.g n ((U σ).X k) a W.e hσ hu.1 (hu.2.1 k).1
    (hu.2.1 k).2 hsd hD
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' := ShortRead.halfIntegralGenerator_add_conj_eq_one H
  have hM : 0 < d.l₂.M := lt_of_lt_of_le (by norm_num) d.l₂.three_le
  have hΛ : Λ.La ∈ Vset E n d.l₂.M := (GenLatCmp.genLat_vset E n Λ.La).2.1 _ N hM hun hT hO
  obtain ⟨v, hv⟩ :=
    (TensVac.vacua E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hsd 1 _ (Base.stdL_mem_Vset n 1)).1
  obtain ⟨x₁, hx₁⟩ := (GlobalTheory.frames_isConnected E r ((U σ).X k)).nonempty
  obtain ⟨b, -, hx₀, hux₀⟩ := exists_unitFr_rmul ((U σ).X k) hx₁
  obtain ⟨A₀, hAm, -⟩ := uw_anFib E H Dw l Xo c σ r (U σ) hσ hu hr1 W k Dc.bas Dc.idx Dc.sympl
    (hDe ▸ Dc.per_eq) (hDe ▸ Dc.ty_eq) ⟨_, hx₀⟩ hux₀
  obtain ⟨z₀, hz₀⟩ := hlev.2.2.2.2.2.2.1 ℂ halg (unC (U σ) k ⟨_, hx₀⟩)
  obtain ⟨B₀, -, mk₂, hmk₂, hB₀, hover⟩ := Lift.anFib_lift E H Dw l Xo c n d halg hlev r _ _ Dc.bas Dc.idx W.e _ _
    _ A₀ Dc.sympl hx₀ hsd z₀ hz₀ _ hAm
  obtain ⟨Y, hY⟩ := (DualMark.dual_marking E H Dw d.l₂ r _ _ mk₂ _ hsd hmk₂
    (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 n N hO.1.pos
  obtain ⟨ρ, hρ, hnorm⟩ := VacNorm.norm_factor_eq E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hsd v hv
  have hpt : ∀ x (hx : x ∈ ((U σ).X k).dom), IsUnitFr ((U σ).X k) x → ∃ κ : ℂ, ‖κ‖ = ρ ∧
      ∃ (A : AnFib ((U σ).X k) Dc.bas Dc.idx W.e x ((U σ).X k).Λ (unC (U σ) k ⟨x, hx⟩)) (θ : (Fin W.g → ℂ) → ℂ),
        A.Marked (W.mark k) ∧ A.Reads 1 (unC (U σ) k ⟨x, hx⟩).s θ ∧
        ∀ z : Fin n → Fin W.g → ℂ, ∏ b, θ (z b) = κ * thA ((U σ).X k) Dc.bas Dc.idx v x z := by
    intro x hx hux
    obtain ⟨A, hA, θ, hθ, hmean⟩ := uw_anFib E H Dw l Xo c σ r (U σ) hσ hu hr1 W k Dc.bas Dc.idx Dc.sympl
      (hDe ▸ Dc.per_eq) (hDe ▸ Dc.ty_eq) ⟨x, hx⟩ hux
    have hT := isTheta1_of_reads_generator E H Dw l Xo c r _ _ Dc.bas Dc.idx W.e x _ _ A Dc.sympl hx hsd θ hθ
    obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hsd v hv x hx θ hT
    exact ⟨κ, hnorm x hx hux θ κ hT hmean hκ, A, θ, hA, hθ, hκ⟩
  choose κ hκ hpt using hpt
  obtain ⟨C, -, hCe⟩ := Const.exists_const ((U σ).X k) (Formalism.L2.PjFree.laU (U σ) a n k) ρ hρ κ hκ
  have hG := fun j => ShortRead.sb_gphi Dc.idx Dc.sympl hn hw hw' hsd hΛ hv.1 (fun q => σ (w j q)) Y
  have hth := fun j => theta_holomorphic_weight E r _ _ _ Dc.hr Dc.bas Dc.idx n Dc.sympl hn _ _ _ (hG j) _ (Dc.mem _ (hP j))
  rw [Dc.wt_eq] at hth
  have hs := hu.2.2.2.2.1 a n hD f hsec k
  let co : T → ℂ := fun j => evR d.Xo₂ d.c₂ (cs j) z₀ * algebraMap d.c₂.F ℂ
    (1⁻¹ * ((Λ.mIdx N r : d.c₂.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw d.l₂) : d.c₂.F))⁻¹ * (Λ.zCard N r : d.c₂.F))
  have hrd := hCe (Formalism.L2.PjFree.rdU (U σ) f k) (fun x => ∑ j, co j * thP ((U σ).X k) Dc.hr Dc.bas Dc.idx
      (gphi ((U σ).X k) Dc.bas (H.w0 : E) Λ.La ((U σ).X k).Λ v (fun q => σ (w j q)) Y)
      (MvPolynomial.rename Dc.eL (MvPolynomial.map σ (P j))) x) hs.1
    (DifferentiableOn.fun_sum fun j _ => (hth j).1.const_mul _) (fun x hx b hb => ⟨hs.2.1 x hx b hb, by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hth j).2.1 x hx b hb, mul_left_comm]
      rfl⟩) (by
      intro x hx hux
      obtain ⟨A, θ, hAk, hθ, hprod⟩ := hpt x hx hux
      obtain ⟨y₂, B, hy₂, hB, hrd⟩ := Reach.exists_lift_of_reached d halg hσ₂ hlev hA hA₂ hr1 A Dc.sympl hx hsd hmk hAk
        hmk₂ hover hx₀ B₀ hz₀ hB₀
      obtain ⟨vc, hvc, hev⟩ := hval ℂ halg _ y₂ hy₂
      have hrd' : Formalism.L2.PjFree.rdU (U σ) f k x = evR Xo c f (unC (U σ) k ⟨x, hx⟩) := dif_pos hx
      rw [hrd', hev, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw d.l₂ d.Xo₂ d.c₂ r _ _ Dc.bas Dc.idx W.e x _ y₂ B Dc.sympl hx hsd _ n Dc.hr Dc.eL
        hu.1 hn (hDe ▸ Dc.dir_eq) d.nab₂ hnab θ v _ (hrd θ hθ) hv hprod mk₂ hmk₂ hB Λ.La hΛ N hO Y hY a _
        ((GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hP j)) _ 1 (vc j) (hvc j)
      rw [h, MvPolynomial.map_map, hcomp, evR_eq_of_marked_pow hσ₂ hA₂ (hcs j).1 hm (hcs j).2 hr1 Dc.sympl hmk₂.mem hx hx₀
        B B₀ hB hB₀]
      simp only [halg, co]
      change _ * (_ * _ * thP _ _ _ _ (gphi _ _ _ _ _ _ (fun q => σ (w j q)) _) _ _) = _
      ring)
  have hwt : Formalism.L2.PjFree.laU (U σ) a n k = wtOf ((U σ).X k) Dc.hr Dc.k Dc.k' n := Dc.wt_eq.symm
  rw [hwt] at hs ⊢
  refine CuspSum.mem_SS_of_eq_sum_thP E r ((U σ).X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hn Dc.k Dc.k' ?_ T
    _ _ (fun j => ShortRead.sb_smul (C * co j) (hG j)) (fun j => Dc.mem _ (hP j)) _ (fun x hx => ?_) hs.2.2
  · rcases Nat.eq_zero_or_pos Dw.p with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (hk hL h0)
  · rw [hrd x hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ShortRead.theta_smul₂ Dc.hr Dc.idx Dc.sympl hn (hG j) (Dc.mem _ (hP j)) hx, mul_assoc C]

end GlobalTheory.ThetaSumDescent
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.ThetaSumDescent

theorem exists_cusp_thetaSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), 1 ≤ r → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → l.A = 1 → ∀ [StarRing (𝓞 E)] (a : (E →+* ℂ) × ℕ → ℕ) (n N : ℕ) (dδ : DeltaDat Xo c n) (La : GenLat E n) (T : Type) [Fintype T] (cs : T → Rul dδ.Xo₂ dδ.c₂) (e : ℕ) (w : T → (Fin n → LevQ Dw dδ.l₂) → c.F) (P : T → MvPolynomial (LtN Dw n) c.F), Dom a n → LastPos Dw a → dδ.IsLev → dδ.l₂.A = 1 → IsNab dδ.Xo₂ dδ.c₂ dδ.nab₂ → La.Unimod → La.TrivAt dδ.l₂.M → La.LevOK N dδ.l₂.M → 0 < e → (∀ t, cs t ∈ sec dδ.Xo₂ dδ.c₂ 0 0 ∧ cs t ^ (e + 1) = cs t) → (∀ t, P t ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → SumInv dδ cs w P → ∃ f ∈ cusp Xo c U a n, (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k], (∀ x : c.F, algebraMap dδ.c₂.F k (dδ.eF x) = algebraMap c.F k x) → ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y → ∃ v : T → k, (∀ t, thLaValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w t q)) La N (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (P t)) y₂ (v t)) ∧ evR Xo c f y = ∑ t, evR dδ.Xo₂ dδ.c₂ (cs t) y₂ * v t) ∧ ∀ f' ∈ sec Xo c a n, (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k], (∀ x : c.F, algebraMap dδ.c₂.F k (dδ.eF x) = algebraMap c.F k x) → ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y → ∃ v : T → k, (∀ t, thLaValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w t q)) La N (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (P t)) y₂ (v t)) ∧ evR Xo c f' y = ∑ t, evR dδ.Xo₂ dδ.c₂ (cs t) y₂ * v t) → f' = f := by
  intro E _ _ _ H Dw l Xo c r U hr hU hA _ a n N d La T _ cs e w P hD hL hlev hA₂ hnab hun hT hO he hcs hP hinv
  obtain ⟨f, hf, hval⟩ := exists_sec_thetaSum d hlev hnab La N hun hT hO a cs w P (fun t => (hcs t).1) hP hinv
  refine ⟨f, ?_, hval, fun f' hf' hval' => ?_⟩
  · rw [← Formalism.L2.PjFree.cusp_ofPj]
    exact mem_cusp_of_thetaSum d (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) hr
      (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (hU σ hσ)) hA hlev hA₂ hnab La N hun hT hO a hD hL cs e he w P hcs hP
      f hf hval
  · refine GlobalTheory.ClassSumUnique.sec_eq_of_geometric hf' hf fun k _ _ _ y => ?_
    letI : Algebra d.c₂.F k := ((algebraMap c.F k).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
    have hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a => by
      show algebraMap c.F k (d.eF.symm (d.eF a)) = _
      rw [AlgEquiv.symm_apply_apply]
    obtain ⟨y₂, hy⟩ := hlev.2.2.2.2.2.2.1 k hk y
    obtain ⟨v, hv, e₁⟩ := hval k hk y y₂ hy
    obtain ⟨v', hv', e₂⟩ := hval' k hk y y₂ hy
    rw [e₁, e₂]
    unfold thLaValAt at hv hv'
    exact sum_values_eq d.nab₂ hnab La N hun hT hO a _
      (fun t => (GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hP t)) _ _ 1 y₂ _ _ _ _ hv hv' fun _ _ => rfl

section Shift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} {A : Type} [AddCommGroup A]

end Shift

section Marks

open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Member
open scoped TensorProduct

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} {A : Type} [AddCommGroup A] [DecidableEq A]

end Marks

end GlobalTheory.ThetaSumDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotLeOpenSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotLeOpenSubgroup
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DelGlob

theorem finite_not_ine_le_of_isOpen : ∀ (Ω : Type) [Field Ω] (k : Type) [Field k] [NumberField k] [Algebra k Ω]
    [IsAlgClosure k Ω] (N : Subgroup (G k Ω)), IsOpen (N : Set (G k Ω)) →
    {w : HeightOneSpectrum (𝓞 k) | ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ¬ Ine (F := k) A ≤ N}.Finite := by
  intro Ω _ k _ _ _ _ N hN
  obtain ⟨L, hL, hLN⟩ := (krullTopology_mem_nhds_one_iff k Ω (N : Set (G k Ω))).1 (hN.mem_nhds N.one_mem)
  haveI : FiniteDimensional k L := hL
  refine (GlobalTheory.InertiaAlmostAll.finite_ramified k Ω L).subset ?_
  rintro w ⟨B, hB, h⟩
  exact ⟨B, hB, fun h' => h fun x hx => hLN (h' hx)⟩

end GlobalTheory.DelGlob
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotLeOpenSubgroupStatement
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GlobalTheory.DelGlob
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_places_inertia_not_le_openSubgroup : ∀ (Ω : Type) [Field Ω] (k : Type) [Field k] [NumberField k] [Algebra k Ω] [IsAlgClosure k Ω] (N : Subgroup (G k Ω)), IsOpen (N : Set (G k Ω)) → {w : HeightOneSpectrum (𝓞 k) | ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ¬ Ine (F := k) A ≤ N}.Finite := by
  first | exact @GlobalTheory.DelGlob.finite_not_ine_le_of_isOpen | exact GlobalTheory.DelGlob.finite_not_ine_le_of_isOpen | (intros; apply GlobalTheory.DelGlob.finite_not_ine_le_of_isOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsValuationEqOfIneFixes
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Pointwise
noncomputable section
namespace GlobalTheory.InertFixVal

theorem exists_mem_Ine_lift_int {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) (M : Type*) [Field M] [Algebra F M]
    [Algebra M Ω] [IsScalarTower F M Ω] [FiniteDimensional F M] [IsGalois F M] (τ : M ≃ₐ[F] M)
    (h : ∀ x : 𝓞 M, A.valuation (algebraMap M Ω (τ (x : M)) - algebraMap M Ω (x : M)) < 1) :
    ∃ σ ∈ Ine (F := F) A, ∀ x : M, σ (algebraMap M Ω x) = algebraMap M Ω (τ x) := by
  haveI : NumberField M := NumberField.of_module_finite F M
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : IsAlgClosure M Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) M⟩
  let σ₁ : Ω ≃ₐ[F] Ω := τ.liftNormal Ω
  have h₁ : ∀ x : M, σ₁ (algebraMap M Ω x) = algebraMap M Ω (τ x) := fun x => τ.liftNormal_commutes Ω x
  obtain ⟨g, hg⟩ := GlobalTheory.InertiaLift.exists_smul_eq (F := M) (A := A) (A' := σ₁⁻¹ • A) (by
    intro x
    rw [smul_valuation_lt_one_iff, inv_inv]
    change A.valuation (algebraMap M Ω (x : M)) < 1 ↔ A.valuation (σ₁ (algebraMap M Ω (x : M))) < 1
    rw [h₁]
    have hx := h x
    constructor
    · intro hl
      simpa using Valuation.map_add_lt _ hx hl
    · intro hl
      simpa using Valuation.map_sub_lt _ hl hx)
  let σ₂ : Ω ≃ₐ[F] Ω := σ₁ * g.restrictScalars F
  have h₂ : ∀ x : M, σ₂ (algebraMap M Ω x) = algebraMap M Ω (τ x) := fun x => by
    rw [← h₁]
    exact congrArg σ₁ (g.commutes x)
  have h₂' : ∀ y, A.valuation (σ₂ y) < 1 ↔ A.valuation y < 1 := fun y => by
    rw [← hg y, smul_valuation_lt_one_iff, inv_inv]
    rfl
  obtain ⟨k, hk, hk'⟩ := GlobalTheory.InertiaLift.exists_congr (F := M) (A := A) σ₂.toRingEquiv h₂' (by
    intro x
    change A.valuation (σ₂ (algebraMap M Ω (x : M)) - algebraMap M Ω (x : M)) < 1
    rw [h₂]
    exact h x)
  have hkinv : ∀ y, A.valuation (k.symm y) < 1 ↔ A.valuation y < 1 := fun y => by
    rw [← valuation_apply_lt_one_iff hk, k.apply_symm_apply]
  refine ⟨k.symm.restrictScalars F * σ₂, GlobalTheory.InertiaLift.mem_Ine_of_integral
    (GlobalTheory.InertiaLift.mem_Dec_of_lt fun y => ?_) fun b hb => ?_, fun x => ?_⟩
  · change A.valuation (k.symm (σ₂ y)) < 1 ↔ _
    rw [hkinv, h₂']
  · change A.valuation (k.symm (σ₂ b) - b) < 1
    rw [← valuation_apply_lt_one_iff hk, map_sub, k.apply_symm_apply, Valuation.map_sub_swap]
    exact hk' b hb
  · change k.symm (σ₂ (algebraMap M Ω x)) = _
    rw [h₂]
    exact k.symm.commutes (τ x)

def primeUnder {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) (M : Type*) [Field M] [NumberField M] [Algebra M Ω] :
    Ideal (𝓞 M) :=
  Ideal.comap (((algebraMap M Ω).comp (algebraMap (𝓞 M) M)).codRestrict A.toSubring fun x =>
    mem_of_isIntegral_int A (x.isIntegral_coe.map (algebraMap M Ω).toIntAlgHom)) (IsLocalRing.maximalIdeal A)

theorem mem_primeUnder {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) (M : Type*) [Field M] [NumberField M]
    [Algebra M Ω] (x : 𝓞 M) : x ∈ primeUnder A M ↔ A.valuation (algebraMap M Ω (x : M)) < 1 := by
  rw [primeUnder, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

theorem ramificationIdx_eq_one {K Ω L : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (hv : IsPlaceOver A v) (hw : IsPlaceOver A w)
    (hI : ∀ σ ∈ Ine (F := K) A, ∀ x : L, σ (algebraMap L Ω x) = algebraMap L Ω x) :
    w.asIdeal.LiesOver v.asIdeal ∧ w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  let N : IntermediateField K Ω := IntermediateField.normalClosure K L Ω
  let M : Type := N
  haveI : FiniteDimensional K M := inferInstance
  haveI : NumberField M := NumberField.of_module_finite K M
  haveI : IsGalois K M := IsGalois.normalClosure K L Ω
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  let P : Ideal (𝓞 M) := primeUnder A M
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hPv : P.under (𝓞 K) = v.asIdeal := by
    ext x
    rw [Ideal.mem_comap, mem_primeUnder, ← hv x]
    congr! 2
  have hPw : P.under (𝓞 L) = w.asIdeal := by
    ext x
    rw [Ideal.mem_comap, mem_primeUnder, ← hw x]
    congr! 2
  haveI hPv' : P.LiesOver v.asIdeal := ⟨hPv.symm⟩
  haveI hPw' : P.LiesOver w.asIdeal := ⟨hPw.symm⟩
  haveI hwv : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hPw, Ideal.under_under, hPv]⟩
  refine ⟨hwv, ?_⟩
  have hv0 := v.ne_bot
  have hw0 := w.ne_bot
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hv0 P
  have := v.isMaximal
  have := w.isMaximal
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hv0
  have : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hw0
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[K] M) v.asIdeal P
  have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[L] M) w.asIdeal P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (M ≃ₐ[K] M)] at h1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (M ≃ₐ[L] M)] at h2
  have h3 := Ideal.ramificationIdx_tower (R := 𝓞 K) w.asIdeal P

  have hfix : ∀ τ ∈ P.toAddSubgroup.inertia (M ≃ₐ[K] M), ∀ x : L, τ (algebraMap L M x) = algebraMap L M x := by
    intro τ hτ x
    obtain ⟨σ, hσ, hστ⟩ := exists_mem_Ine_lift_int A M τ fun y => by
      have := (mem_primeUnder A M _).1 (hτ y)
      have e : ((τ • y - y : 𝓞 M) : M) = τ (y : M) - (y : M) := rfl
      rw [← map_sub, ← e]
      exact this
    apply (algebraMap M Ω).injective
    rw [← hστ, ← IsScalarTower.algebraMap_apply, hI σ hσ x]
  let f : P.toAddSubgroup.inertia (M ≃ₐ[K] M) → P.toAddSubgroup.inertia (M ≃ₐ[L] M) := fun τ =>
    ⟨{ (τ : M ≃ₐ[K] M).toRingEquiv with commutes' := hfix τ τ.2 }, fun y => τ.2 y⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply AlgEquiv.ext
    intro y
    exact DFunLike.congr_fun (congrArg Subtype.val hab) y
  have h4 := Nat.card_le_card_of_injective f hf
  rw [h1, h2, h3] at h4
  have hpos : 0 < P.ramificationIdx (𝓞 K) := h1 ▸ Nat.card_pos
  rw [h3] at hpos
  have ha : w.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have hb : P.ramificationIdx (𝓞 L) ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have hle : w.asIdeal.ramificationIdx (𝓞 K) ≤ 1 := by
    by_contra hc
    push_neg at hc
    have : 2 * P.ramificationIdx (𝓞 L) ≤ w.asIdeal.ramificationIdx (𝓞 K) * P.ramificationIdx (𝓞 L) :=
      Nat.mul_le_mul_right _ hc
    omega
  omega

end GlobalTheory.InertFixVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LFactorRecCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LFactorRecCompatible
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem isSpherical_iff_unr_of_lawsLit : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ x : IrrGL (k := w.adicCompletion E), IsSpherical x.rep ↔ (rc x).unr := by
  intro hEx hMS hSC hZP hGL hBZ E Ω _ _ _ _ _ A w h a ha e rc H x
  constructor
  · intro hs
    obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.main hBZ (w.adicCompletion E) x.1
      ⟨x.2.rep.V, x.2.rep.ρ, x.2.rep.smooth, x.2.rep.irr⟩ hs
    rw [GlobalTheory.T.epsilon_factor_rec_compatible hEx hMS hSC hZP hGL hBZ E Ω A w h a ha e rc H x α hα]
    exact (WD.unr_mk _).2 (WDRep.unr_diag _)
  · intro hu
    obtain ⟨α, hα⟩ := GlobalTheory.T.unramified_weilDeligne_eq_diagonal_inv E Ω A w h (rc x) hu
    obtain ⟨π, hπ⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake (k := w.adicCompletion E) α
    have φ := equivRep π
    have hπ' : HasSatake (cls π).rep α := ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hπ.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hπ.2.2⟩
    have e1 := GlobalTheory.T.epsilon_factor_rec_compatible hEx hMS hSC hZP hGL hBZ E Ω A w h a ha e rc H (cls π) α hπ'
    have e2 : cls π = x := H.bij.1 (e1.trans hα.symm)
    rw [← e2]
    exact hπ'.2.1

end GlobalTheory.LocLanglands
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LFactorRecCompatibleStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.l_factor_rec_compatible : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ x : IrrGL (k := w.adicCompletion E), IsSpherical x.rep ↔ (rc x).unr := by
  first | exact @GlobalTheory.LocLanglands.isSpherical_iff_unr_of_lawsLit | exact GlobalTheory.LocLanglands.isSpherical_iff_unr_of_lawsLit | (intros; apply GlobalTheory.LocLanglands.isSpherical_iff_unr_of_lawsLit <;> assumption)
end
end
