module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSumAlt.NormUnitsOfCalculation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.IdemProj

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [SigmaFinite μ]

theorem integral_inv_of_support (K : Subgroup G) (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G))
    (f : G → ℂ) (hf : Continuous f) (hs : ∀ x, f x ≠ 0 → x ∈ K) :
    ∫ x, f x⁻¹ ∂μ = ∫ x, f x ∂μ := by
  have hKcl : IsClosed (K : Set G) := K.isClosed_of_isOpen ho
  have hu : Continuous ((K : Set G).indicator fun _ => (1 : ℂ)) :=
    (IsClopen.continuous_indicator ⟨hKcl, ho⟩ continuous_const)
  set u : G → ℂ := (K : Set G).indicator fun _ => (1 : ℂ) with hu_def

  set Φ : G × G → ℂ := fun z => f z.2⁻¹ * u (z.1 * z.2) with hΦ_def
  have hΦc : Continuous Φ := (hf.comp continuous_snd.inv).mul (hu.comp continuous_mul)
  have hΦs : HasCompactSupport Φ := by
    refine HasCompactSupport.intro (hc.prod hc) fun z hz => ?_
    by_cases h2 : f z.2⁻¹ = 0
    · simp [hΦ_def, h2]
    · have hb : z.2 ∈ K := by simpa using K.inv_mem (hs _ h2)
      have ha : z.1 ∉ K := fun ha => hz ⟨ha, hb⟩
      have : z.1 * z.2 ∉ K := fun h => ha ((K.mul_mem_cancel_right hb).1 h)
      simp [hΦ_def, hu_def, this]
  have hΦi : Integrable Φ (μ.prod μ) := hΦc.integrable_of_hasCompactSupport hΦs
  have hT := measurePreserving_prod_inv_mul_swap μ μ
  have hΦTi : Integrable (fun z : G × G => Φ (z.2, z.2⁻¹ * z.1)) (μ.prod μ) :=
    (hT.integrable_comp hΦc.aestronglyMeasurable).2 hΦi
  have hswap : ∫ z, Φ (z.2, z.2⁻¹ * z.1) ∂(μ.prod μ) = ∫ z, Φ z ∂(μ.prod μ) := by
    conv_rhs => rw [← hT.map_eq]
    rw [integral_map hT.measurable.aemeasurable]
    rw [hT.map_eq]; exact hΦc.aestronglyMeasurable
  set c : ℂ := ∫ a, u a ∂μ with hc_def
  have hcne : c ≠ 0 := by
    rw [hc_def, hu_def, integral_indicator_const _ hKcl.measurableSet]
    have hpos : 0 < μ (K : Set G) := ho.measure_pos μ ⟨1, K.one_mem⟩
    have hfin : μ (K : Set G) ≠ ⊤ := hc.measure_lt_top.ne
    have : μ.real (K : Set G) ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hpos.ne', hfin⟩
    simpa [Complex.real_smul] using this
  have hleft : ∫ z, Φ z ∂(μ.prod μ) = (∫ b, f b⁻¹ ∂μ) * c := by
    rw [integral_prod_symm Φ hΦi, ← integral_mul_const]
    congr 1; funext b
    simp only [hΦ_def]
    rw [integral_const_mul]
    by_cases h2 : f b⁻¹ = 0
    · simp [h2]
    · have hb : b ∈ K := by simpa using K.inv_mem (hs _ h2)
      congr 1
      rw [hc_def]
      congr 1; funext a
      classical
      simp only [hu_def, Set.indicator_apply, SetLike.mem_coe, K.mul_mem_cancel_right hb]
  have hright : ∫ z, Φ (z.2, z.2⁻¹ * z.1) ∂(μ.prod μ) = (∫ x, f x ∂μ) * c := by
    rw [integral_prod _ hΦTi]
    simp only [hΦ_def, _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
    rw [hc_def, ← integral_const_mul]
    congr 1; funext x
    rw [integral_mul_const, integral_mul_left_eq_self (fun y => f y) x⁻¹]
  have := hswap
  rw [hleft, hright] at this
  exact (mul_right_cancel₀ hcne this).symm

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]


omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] in
theorem inner_rep (π : G → (H →L[ℂ] H)) (h1 : π 1 = 1) (hm : ∀ a b, π (a * b) = π a * π b)
    (hn : ∀ g v, ‖π g v‖ = ‖v‖) (g : G) (x y : H) : ⟪x, π g y⟫_ℂ = ⟪π g⁻¹ x, y⟫_ℂ := by
  have hback : π g (π g⁻¹ x) = x := by
    have := congrArg (fun S : H →L[ℂ] H => S x) (hm g g⁻¹)
    simp only [mul_inv_cancel, h1, ContinuousLinearMap.one_apply, ContinuousLinearMap.mul_apply] at this
    exact this.symm
  let U : H →ₗᵢ[ℂ] H := ⟨(π g).toLinearMap, hn g⟩
  calc ⟪x, π g y⟫_ℂ = ⟪U (π g⁻¹ x), U y⟫_ℂ := by
        show ⟪x, π g y⟫_ℂ = ⟪π g (π g⁻¹ x), π g y⟫_ℂ
        rw [hback]
    _ = ⟪π g⁻¹ x, y⟫_ℂ := U.inner_map_map _ _

theorem op_idem (K : Subgroup G) (hc : IsCompact (K : Set G))
    (π : G → (H →L[ℂ] H)) (h1 : π 1 = 1) (hm : ∀ a b, π (a * b) = π a * π b)
    (hn : ∀ g v, ‖π g v‖ = ‖v‖) (hπ : ∀ v, Continuous fun g => π g v)
    (e : G → ℂ) (he : Continuous e) (hs : ∀ x, e x ≠ 0 → x ∈ K)
    (hee : ∀ x, ∫ y, e y * e (y⁻¹ * x) ∂μ = e x) (T : H →L[ℂ] H)
    (hT : ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, e g * ⟪x, π g y⟫_ℂ ∂μ) : T.comp T = T := by
  ext y
  refine ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply, hT x (T y)]
  have step : ∀ g, ⟪x, π g (T y)⟫_ℂ = ∫ h, e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ ∂μ := by
    intro g
    have shift := integral_mul_left_eq_self (μ := μ) (fun h => e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ) g
    simp only [inv_mul_cancel_left] at shift
    rw [inner_rep π h1 hm hn g, hT, ← shift]
    congr 1; funext h
    rw [hm, ContinuousLinearMap.mul_apply, inner_rep π h1 hm hn g]
  have hint : Integrable (Function.uncurry fun g h => e g * (e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ))
      (μ.prod μ) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (he.comp continuous_fst).mul ((he.comp (continuous_fst.inv.mul continuous_snd)).mul
        (continuous_const.inner ((hπ y).comp continuous_snd)))
    · refine HasCompactSupport.intro (hc.prod hc) ?_
      rintro ⟨g, h⟩ hgh
      simp only [Function.uncurry_apply_pair]
      by_cases hg : g ∈ K
      · have hh : h ∉ K := fun hh => hgh ⟨hg, hh⟩
        have h0 : e (g⁻¹ * h) = 0 := by
          by_contra hne
          exact hh (by simpa using K.mul_mem hg (hs _ hne))
        simp [h0]
      · have h0 : e g = 0 := by
          by_contra hne
          exact hg (hs _ hne)
        simp [h0]
  calc ∫ g, e g * ⟪x, π g (T y)⟫_ℂ ∂μ
      = ∫ g, ∫ h, e g * (e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ) ∂μ ∂μ := by
        congr 1; funext g
        rw [step g, integral_const_mul]
    _ = ∫ h, ∫ g, e g * (e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ h, e h * ⟪x, π h y⟫_ℂ ∂μ := by
        congr 1; funext h
        simp_rw [← mul_assoc]
        rw [integral_mul_const, hee]
    _ = ⟪x, T y⟫_ℂ := (hT x y).symm

theorem op_symm (K : Subgroup G) (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G))
    (π : G → (H →L[ℂ] H)) (h1 : π 1 = 1) (hm : ∀ a b, π (a * b) = π a * π b)
    (hn : ∀ g v, ‖π g v‖ = ‖v‖) (hπ : ∀ v, Continuous fun g => π g v)
    (e : G → ℂ) (he : Continuous e) (hs : ∀ x, e x ≠ 0 → x ∈ K)
    (hst : ∀ x, e x⁻¹ = star (e x)) (T : H →L[ℂ] H)
    (hT : ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, e g * ⟪x, π g y⟫_ℂ ∂μ) (x y : H) :
    ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
  have hF : Continuous fun g => e g * ⟪x, π g y⟫_ℂ := he.mul (continuous_const.inner (hπ y))
  have hFs : ∀ g, e g * ⟪x, π g y⟫_ℂ ≠ 0 → g ∈ K := fun g hg => hs g (left_ne_zero_of_mul hg)
  conv_lhs => rw [← inner_conj_symm]
  rw [hT y x, ← integral_conj, hT x y, ← integral_inv_of_support μ K hc ho _ hF hFs]
  congr 1; funext g
  show (starRingEnd ℂ) (e g * ⟪y, π g x⟫_ℂ) = e g⁻¹ * ⟪x, π g⁻¹ y⟫_ℂ
  rw [map_mul, inner_conj_symm, starRingEnd_apply, ← hst g, inner_rep π h1 hm hn g⁻¹, inv_inv]


omit [T2Space G] in
theorem op_fixed (π : G → (H →L[ℂ] H)) (h1 : π 1 = 1) (hm : ∀ a b, π (a * b) = π a * π b)
    (hn : ∀ g v, ‖π g v‖ = ‖v‖) (e : G → ℂ) (T : H →L[ℂ] H)
    (hT : ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, e g * ⟪x, π g y⟫_ℂ ∂μ) (k : G) (hk : ∀ h, e (k * h) = e h) :
    (π k).comp T = T := by
  ext y
  refine ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply, inner_rep π h1 hm hn k, hT, hT]
  have key : ∀ g, e g * ⟪π k⁻¹ x, π g y⟫_ℂ = e (k * g) * ⟪x, π (k * g) y⟫_ℂ := by
    intro g
    rw [hk g, hm, ContinuousLinearMap.mul_apply, inner_rep π h1 hm hn k]
  simp_rw [key]
  exact integral_mul_left_eq_self (fun h => e h * ⟪x, π h y⟫_ℂ) k


omit [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem eventually_left_inv (K : Subgroup G) (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G))
    (e : G → ℂ) (he : IsLocallyConstant e) (hs : ∀ x, e x ≠ 0 → x ∈ K) :
    ∀ᶠ k in nhds (1 : G), ∀ h, e (k * h) = e h := by
  have hloc : ∀ h ∈ (K : Set G), ∀ᶠ z : G × G in nhds ((1 : G), h), e (z.1 * z.2) = e z.2 := by
    intro h _
    have hfib : ∀ᶠ y in nhds h, e y = e h := he.eventually_eq h
    have ht : Filter.Tendsto (fun z : G × G => z.1 * z.2) (nhds ((1 : G), h)) (nhds h) := by
      simpa using (continuous_mul (M := G)).tendsto ((1 : G), h)
    have ha := ht.eventually hfib
    have hb : ∀ᶠ z : G × G in nhds ((1 : G), h), e z.2 = e h :=
      (continuous_snd.tendsto ((1 : G), h)).eventually hfib
    filter_upwards [ha, hb] with z hz1 hz2
    rw [hz1, hz2]
  have hK : ∀ᶠ k in nhds (1 : G), ∀ h ∈ (K : Set G), e (k * h) = e h :=
    hc.eventually_forall_of_forall_eventually hloc
  have hmem : ∀ᶠ k in nhds (1 : G), k ∈ (K : Set G) := ho.mem_nhds K.one_mem
  filter_upwards [hK, hmem] with k hk hkK h
  by_cases hh : h ∈ (K : Set G)
  · exact hk h hh
  · have e1 : e h = 0 := by
      by_contra hne
      exact hh (hs h hne)
    have e2 : e (k * h) = 0 := by
      by_contra hne
      exact hh (by simpa using K.mul_mem (K.inv_mem hkK) (hs _ hne))
    rw [e1, e2]

end General

theorem re_orth_proj : ∀ B : RowsAut, IsOrthProjOnto B.Re (LinearMap.range (B.Re : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund)) ∧ (∀ g : B.I.Ginf, B.Re.comp (B.R (g, 1)) = (B.R (g, 1)).comp B.Re) ∧ ∃ g : ℕ, 1 ≤ g ∧ ∀ k ∈ B.I.Kg g, (B.R (1, k)).comp B.Re = B.Re := by
  intro B
  obtain ⟨hT2, -, hSC, hKc, hKo, ⟨K, hK⟩, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨hR1, hRm, hRn, hRc, -⟩ := GlobalTheory.T.rightRegularRep_unitary_stronglyContinuous B
  obtain ⟨hlc, hconv, hst, -, hsupp, -, -⟩ := B.e_adm
  obtain ⟨-, hRe⟩ := B.Re_spec
  have hKc' : IsCompact (K : Set B.I.Gf) := by rw [hK]; exact hKc
  have hKo' : IsOpen (K : Set B.I.Gf) := by rw [hK]; exact hKo
  have hs : ∀ x, B.e x ≠ 0 → x ∈ K := by
    intro x hx
    rw [← SetLike.mem_coe, hK]
    exact hsupp x hx
  have h1 : B.R (1, 1) = 1 := hR1
  have hm : ∀ a b : B.I.Gf, B.R (1, a * b) = B.R (1, a) * B.R (1, b) := by
    intro a b
    rw [← hRm, Prod.mk_mul_mk, one_mul]
  have hn : ∀ (g : B.I.Gf) v, ‖B.R (1, g) v‖ = ‖v‖ := fun g v => hRn _ v
  have hπ : ∀ v, Continuous fun g : B.I.Gf => B.R (1, g) v :=
    fun v => (hRc v).comp (continuous_const.prodMk continuous_id)
  have he : Continuous B.e := hlc.continuous
  have hee : ∀ x, ∫ y, B.e y * B.e (y⁻¹ * x) ∂B.μf = B.e x := fun x => congrFun hconv x
  have hT : ∀ x y : B.I.L2 B.μf B.fund,
      ⟪x, B.Re y⟫_ℂ = ∫ g, B.e g * ⟪x, B.R (1, g) y⟫_ℂ ∂B.μf := hRe
  refine ⟨?_, ?_, ?_⟩
  · show B.Re.comp B.Re = B.Re ∧ (∀ x y, ⟪B.Re x, y⟫_ℂ = ⟪x, B.Re y⟫_ℂ) ∧ _
    exact ⟨op_idem B.μf K hKc' (fun g => B.R (1, g)) h1 hm hn hπ B.e he hs hee B.Re hT,
      fun x y => op_symm B.μf K hKc' hKo' (fun g => B.R (1, g)) h1 hm hn hπ B.e he hs hst B.Re hT x y,
      rfl⟩
  · intro g
    refine ContinuousLinearMap.ext fun y => ?_
    refine ext_inner_left ℂ fun x => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hT x,
      inner_rep B.R hR1 hRm hRn (g, 1) x, hT]
    congr 1; funext k
    have hcomm : ((1 : B.I.Ginf), k) * (g, 1) = (g, 1) * ((1 : B.I.Ginf), k) := by
      simp only [Prod.mk_mul_mk, one_mul, mul_one]
    rw [← inner_rep B.R hR1 hRm hRn (g, 1), ← ContinuousLinearMap.mul_apply,
      ← ContinuousLinearMap.mul_apply, ← hRm, ← hRm, hcomm]
  · obtain ⟨g, hg1, hgsub⟩ := B.I.topf_basis _ (eventually_left_inv K hKc' hKo' B.e hlc hs)
    exact ⟨g, hg1, fun k hk => op_fixed B.μf (fun g => B.R (1, g)) h1 hm hn B.e B.Re hT k
      (hgsub hk)⟩

end GlobalTheory.IdemProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGram
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGram
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.St

variable {D : D7}

theorem hspace_gram_det_ne {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
    S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : S.frame.equivFun.symm v = 0 := by
    refine S.nondeg.2 _ fun x => ?_
    have hx : ∀ i, S.hT (S.frame i) (S.frame.equivFun.symm v) = 0 := fun i => by
      have := congrFun h0 i
      simpa [Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, mul_comm] using this
    rw [← S.frame.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_zero,
      Finset.sum_const_zero]
  exact (LinearEquiv.map_eq_zero_iff _).1 this

theorem hform_crd_setting (X : HidaSetting D) (v w : (VS D).V) :
    X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd v) (X.crd w)) = (VS D).hT v w := by
  conv_rhs => rw [← X.bas.sum_repr v, ← X.bas.sum_repr w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Formalism.UG.hform, map_mul, HidaSetting.crd, crdOf, starRingEnd_apply, X.ιE_conj, RingEquiv.apply_symm_apply,
    X.J_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]
  ring

theorem gram_entry {A : Type} [CommRing A] {n ι : Type} [Fintype n] (σ : A →+* A) (Q : Matrix n ι A)
    (J : Matrix n n A) (k l : ι) :
    ((Q.map σ)ᵀ * J * Q) k l = Formalism.UG.hform σ J (fun i => Q i k) (fun i => Q i l) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Formalism.UG.hform, Finset.sum_mul]
  exact Finset.sum_comm

def famQ (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) → (VS D).V :=
  Sum.elim (qFr wt) (Sum.elim X.eX (Sum.elim X.fY fun _ => X.zu u))

end GlobalTheory.St

namespace GlobalTheory.St
variable {D : D7}

theorem hT_symm_zero {x y : (VS D).V} (h : (VS D).hT x y = 0) : (VS D).hT y x = 0 := by
  rw [← (VS D).herm.eq x y, h, map_zero]

theorem hT_wt_symm (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hiso : ∀ x y, (VS D).hT (wt x) (wt y) = (VS D).hT x y)
    (x y : (VS D).V) : (VS D).hT (wt.symm x) y = (VS D).hT x (wt y) := by
  rw [← hiso, LinearEquiv.apply_symm_apply]

theorem hT_qFr_qFr (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hiso : ∀ x y, (VS D).hT (wt x) (wt y) = (VS D).hT x y)
    (a b : Fin (D.R.N 0)) : (VS D).hT (qFr wt a) (qFr wt b) = Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) a b := by
  rw [qFr, hT_wt_symm wt hiso, qFr, LinearEquiv.apply_symm_apply, xFr, xFr,
    D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega)]
  rfl

theorem hT_qFr_rest (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hw : WittX X u wt)
    (a : Fin (D.R.N 0)) (k : Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) :
    (VS D).hT (qFr wt a) (famQ X u wt (Sum.inr k)) = 0 := by
  obtain ⟨hiso, he, hf, hz⟩ := hw
  rw [qFr, hT_wt_symm wt hiso]
  rcases k with b | b | b
  · simp only [famQ, Sum.elim_inr, Sum.elim_inl, he]; exact (D.sp.hyp_orthX b _).1
  · simp only [famQ, Sum.elim_inr, Sum.elim_inl, hf]; exact (D.sp.hyp_orthX b _).2
  · simp only [famQ, Sum.elim_inr, hz, Formalism.BasicNotions.D7.zmOf, LinearMap.map_smul]
    rw [xFr, D.sp.zm_orth, smul_zero]

end GlobalTheory.St

namespace GlobalTheory.St
variable {D : D7}

theorem hT_fe (X : HidaSetting D) (a b : Fin D.R.rS) :
    (VS D).hT (X.fY a) (X.eX b) = if b = a then 1 else 0 := by
  rw [← (VS D).herm.eq (X.eX b) (X.fY a), X.ef]
  split_ifs <;> simp

theorem hT_ze (X : HidaSetting D) (u : D.what₂.Word) (b : Fin D.R.rS) : (VS D).hT (X.zu u) (X.eX b) = 0 :=
  hT_symm_zero (X.zu_orth u b).1

theorem hT_zf (X : HidaSetting D) (u : D.what₂.Word) (b : Fin D.R.rS) : (VS D).hT (X.zu u) (X.fY b) = 0 :=
  hT_symm_zero (X.zu_orth u b).2

theorem hT_zz_ne (X : HidaSetting D) (u : D.what₂.Word) : (VS D).hT (X.zu u) (X.zu u) ≠ 0 := by
  rw [X.zu_norm, neg_ne_zero, Nat.cast_ne_zero]
  exact ((D.mem u).A.T_prime).ne_zero

def gramR (X : HidaSetting D) (u : D.what₂.Word) :
    Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E :=
  Matrix.of fun k l => X.ιE.symm ((VS D).hT (Sum.elim X.eX (Sum.elim X.fY fun _ => X.zu u) k)
    (Sum.elim X.eX (Sum.elim X.fY fun _ => X.zu u) l))

def gramRinv (X : HidaSetting D) (u : D.what₂.Word) :
    Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E :=
  Matrix.of fun k l => match k, l with
    | Sum.inl a, Sum.inr (Sum.inl b) => if a = b then 1 else 0
    | Sum.inr (Sum.inl a), Sum.inl b => if a = b then 1 else 0
    | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => (X.ιE.symm ((VS D).hT (X.zu u) (X.zu u)))⁻¹
    | _, _ => 0

theorem gramR_mul_inv (X : HidaSetting D) (u : D.what₂.Word) : gramR X u * gramRinv X u = 1 := by
  have ht : X.ιE.symm ((VS D).hT (X.zu u) (X.zu u)) ≠ 0 := by
    rw [Ne, RingEquiv.map_eq_zero_iff]; exact hT_zz_ne X u
  ext (a | a | a) (b | b | b) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, gramR, gramRinv, X.ee, X.ff, X.ef, hT_fe, hT_ze, hT_zf,
      X.zu_orth, Matrix.one_apply, ht, eq_comm]

end GlobalTheory.St

namespace GlobalTheory.St
variable {D : D7}

theorem qFrame_basis_gram : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ (Q : Matrix (Fin X.B.I.n) (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) X.B.I.E) (Qi : Matrix (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) (Fin X.B.I.n) X.B.I.E) (G' : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E), Q * Qi = 1 ∧ Qi * Q = 1 ∧ (∀ j i, Q i (Sum.inl j) = X.crd (qFr wt j) i) ∧ (∀ a i, Q i (Sum.inr (Sum.inl a)) = X.eR a i) ∧ (∀ a i, Q i (Sum.inr (Sum.inr (Sum.inl a))) = X.fR a i) ∧ (∀ i, Q i (Sum.inr (Sum.inr (Sum.inr ()))) = X.zR u i) ∧ IsUnit G'.det ∧ (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q = Matrix.fromBlocks ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) 0 0 G' := by
  intro D X u wt hw
  classical
  let Q : Matrix (Fin X.B.I.n) (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) X.B.I.E :=
    Matrix.of fun i k => X.crd (famQ X u wt k) i
  have hiso := hw.1

  have hM : (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q =
      Matrix.fromBlocks ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) 0 0 (gramR X u) := by
    ext k l
    rw [gram_entry]
    apply X.ιE.injective
    rw [show (fun i => Q i k) = X.crd (famQ X u wt k) from rfl, show (fun i => Q i l) = X.crd (famQ X u wt l) from rfl,
      hform_crd_setting]
    rcases k with a | k <;> rcases l with b | l
    · simp only [Matrix.fromBlocks_apply₁₁, Matrix.map_apply, RingEquiv.apply_symm_apply]
      exact hT_qFr_qFr wt hiso a b
    · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, map_zero]
      exact hT_qFr_rest X u wt hw a l
    · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, map_zero]
      exact hT_symm_zero (hT_qFr_rest X u wt hw b k)
    · simp only [Matrix.fromBlocks_apply₂₂, gramR, Matrix.of_apply, RingEquiv.apply_symm_apply]
      rfl

  have hA : ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).det ≠ 0 := by
    have h1 : ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).det =
        X.ιE.symm.toRingHom (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).det := by
      rw [RingHom.map_det]; rfl
    rw [h1]
    refine (map_ne_zero _).2 ?_
    unfold Formalism.L2.Forms.gramN
    rw [Matrix.det_reindex_self]
    exact hspace_gram_det_ne _
  have hG : IsUnit (gramR X u).det := Matrix.isUnit_det_of_right_inverse (gramR_mul_inv X u)
  have hMu : IsUnit ((Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q).det := by
    rw [hM, Matrix.det_fromBlocks_zero₂₁]
    exact (isUnit_iff_ne_zero.2 hA).mul hG

  have hcard : Fintype.card (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) = X.B.I.n := by
    rw [X.n_eq, ← dimS_eq, Formalism.BasicNotions.Ranks.N_zero]
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  let σ := Fintype.equivFinOfCardEq hcard
  let P := Q.submatrix σ id
  have hQ : Q = P.submatrix σ.symm id := by
    ext i k; simp [P]
  have hconj : (Q.map (starRingEnd X.B.I.E))ᵀ = Qᴴ := by
    ext i k
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
    exact starRingEnd_apply _
  have hPJ : (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q = Pᴴ * X.B.I.J.submatrix σ σ * P := by
    have hJ : X.B.I.J = (X.B.I.J.submatrix σ σ).submatrix σ.symm σ.symm := by
      simp [Matrix.submatrix_submatrix]
    rw [hconj, hQ, Matrix.conjTranspose_submatrix]
    conv_lhs => rw [hJ]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hP : IsUnit P.det := by
    rw [hPJ, Matrix.det_mul, Matrix.det_mul] at hMu
    exact isUnit_of_mul_isUnit_right hMu
  refine ⟨Q, (P⁻¹).submatrix id σ.symm, gramR X u, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, hG, hM⟩
  · rw [hQ, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_nonsing_inv _ hP,
      Matrix.submatrix_one_equiv]
  · rw [hQ, Matrix.submatrix_mul_equiv, Matrix.nonsing_inv_mul _ hP, Matrix.submatrix_id_id]

end GlobalTheory.St
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGramStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnWittFrame_basis_blockGram : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ (Q : Matrix (Fin X.B.I.n) (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) X.B.I.E) (Qi : Matrix (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) (Fin X.B.I.n) X.B.I.E) (G' : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E), Q * Qi = 1 ∧ Qi * Q = 1 ∧ (∀ j i, Q i (Sum.inl j) = X.crd (qFr wt j) i) ∧ (∀ a i, Q i (Sum.inr (Sum.inl a)) = X.eR a i) ∧ (∀ a i, Q i (Sum.inr (Sum.inr (Sum.inl a))) = X.fR a i) ∧ (∀ i, Q i (Sum.inr (Sum.inr (Sum.inr ()))) = X.zR u i) ∧ IsUnit G'.det ∧ (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q = Matrix.fromBlocks ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) 0 0 G' := by
  first | exact @GlobalTheory.St.qFrame_basis_gram | exact GlobalTheory.St.qFrame_basis_gram | (intros; apply GlobalTheory.St.qFrame_basis_gram <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousRepresentativeProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousRepresentativeProperties
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.ContRepUniq

theorem lintegral_enorm_sq_eq {X : Type} [MeasurableSpace X] (μ : Measure X) (F : Lp ℂ 2 μ) :
    ∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (‖F‖ ^ 2) := by
  rw [Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top F),
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top (Lp.aestronglyMeasurable F)]
  have h2 : ((2 : ENNReal).toReal) = 2 := by norm_num
  simp only [h2, ← ENNReal.rpow_two]
  rw [← ENNReal.rpow_mul]
  norm_num

theorem contRep_unique_linear : ∀ (B : RowsAut), (∀ F f f', IsContRep B F f → IsContRep B F f' → f = f') ∧ (∀ F F' f f' (c : ℂ), IsContRep B F f → IsContRep B F' f' → IsContRep B (F + c • F') (fun x => f x + c * f' x)) ∧ (∀ F f g, IsContRep B F f → IsContRep B (B.R g F) (fun x => f (x * g))) ∧ ∀ F f, IsContRep B F f → f =ᵐ[B.I.muA B.μf] B.I.ext F ∧ ∫⁻ x in B.fund, ‖f x‖ₑ ^ 2 ∂(B.I.muA B.μf) = ENNReal.ofReal (‖F‖ ^ 2) := by
  intro B
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F f f' hf hf'
    exact ((GlobalTheory.ExtContRep.ext_ae_eq_contRep B F f hf).2.1 f' hf').symm
  · intro F F' f f' c hf hf'
    refine ⟨hf.1.add (continuous_const.mul hf'.1), ?_, ?_⟩
    · intro γ hγ x
      show f (γ * x) + c * f' (γ * x) = f x + c * f' x
      rw [hf.2.1 γ hγ x, hf'.2.1 γ hγ x]
    · filter_upwards [Lp.coeFn_add F (c • F'), Lp.coeFn_smul c F', hf.2.2, hf'.2.2]
        with x h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, h3, h4]
  · intro F f g hf
    exact (GlobalTheory.ExtContRep.ext_ae_eq_contRep B F f hf).2.2.1 g
  · intro F f hf
    refine ⟨(GlobalTheory.ExtContRep.ext_ae_eq_contRep B F f hf).1.symm, ?_⟩
    refine Eq.trans ?_ (lintegral_enorm_sq_eq ((B.I.muA B.μf).restrict B.fund) F)
    refine lintegral_congr_ae ?_
    filter_upwards [hf.2.2] with x hx
    rw [hx]

end GlobalTheory.ContRepUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousRepresentativePropertiesStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_representative_properties : ∀ (B : RowsAut), (∀ F f f', IsContRep B F f → IsContRep B F f' → f = f') ∧ (∀ F F' f f' (c : ℂ), IsContRep B F f → IsContRep B F' f' → IsContRep B (F + c • F') (fun x => f x + c * f' x)) ∧ (∀ F f g, IsContRep B F f → IsContRep B (B.R g F) (fun x => f (x * g))) ∧ ∀ F f, IsContRep B F f → f =ᵐ[B.I.muA B.μf] B.I.ext F ∧ ∫⁻ x in B.fund, ‖f x‖ₑ ^ 2 ∂(B.I.muA B.μf) = ENNReal.ofReal (‖F‖ ^ 2) := by
  first | exact @GlobalTheory.ContRepUniq.contRep_unique_linear | exact GlobalTheory.ContRepUniq.contRep_unique_linear | (intros; apply GlobalTheory.ContRepUniq.contRep_unique_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralFiniteAdeleIsoCommutesWithConjugation
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigRMemOAd
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.IotaConj

theorem sigR_inclE {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (R : Type) [CommRing R] [Algebra F R] (x : E) :
    sigR σ R (inclE (F := F) R x) = inclE (F := F) R (σ x) := by
  simp [sigR, inclE]

theorem sigR_mem_OAd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {a : E ⊗[F] Ad F} (ha : a ∈ OAd F E) : sigR σ (Ad F) a ∈ OAd F E := by

  have key : OAd F E ≤ (OAd F E).comap (sigR σ (Ad F)) := by
    show tensInt (F := F) (Ad F) (intOE E) (intAd F) ≤
      (tensInt (F := F) (Ad F) (intOE E) (intAd F)).comap (sigR σ (Ad F))
    refine (Subring.closure_le).2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨z, rfl⟩ := hx
      have hint : IsIntegral ℤ (σ (algebraMap (𝓞 E) E z)) :=
        (RingOfIntegers.isIntegral_coe z).map (σ : E →+* E).toIntAlgHom
      refine Subring.subset_closure (Or.inl ⟨⟨σ (algebraMap (𝓞 E) E z), ⟨⟨_, hint⟩, rfl⟩⟩, ?_⟩)
      simp [sigR]
    · refine Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, ?_⟩)
      simp [sigR]
  exact key ha

theorem iota_sigR (F E F' E' : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E']
    (σ : E →ₐ[F] E) (σ' : E' →ₐ[F'] E') (e : E ≃+* E') (ι : E ⊗[F] Ad F ≃+* E' ⊗[F'] Ad F')
    (he : ∀ x, e (σ x) = σ' (e x))
    (hι : ∀ x, ι (inclE (F := F) (Ad F) x) = inclE (F := F') (Ad F') (e x))
    (hO : ∀ a, a ∈ OAd F E ↔ ι a ∈ OAd F' E') (a : E ⊗[F] Ad F) :
    ι (sigR σ (Ad F) a) = sigR σ' (Ad F') (ι a) := by
  obtain ⟨-, h2, -, h4, -⟩ := GlobalTheory.T.integralExtensionFiniteAdeles_basic_properties F E
  obtain ⟨-, -, h3', -, -⟩ := GlobalTheory.T.integralExtensionFiniteAdeles_basic_properties F' E'

  set D : E ⊗[F] Ad F → E' ⊗[F'] Ad F' :=
    fun b => ι (sigR σ (Ad F) b) - sigR σ' (Ad F') (ι b) with hD
  have Dadd : ∀ b c, D (b + c) = D b + D c := by
    intro b c; simp only [hD, map_add (f := _)]; abel
  have Dmul : ∀ (m : ℕ) b, D ((m : E ⊗[F] Ad F) * b) = (m : E' ⊗[F'] Ad F') * D b := by
    intro m b; simp only [hD, map_mul, map_natCast]; ring
  have Dincl : ∀ x : E, D (inclE (F := F) (Ad F) x) = 0 := by
    intro x; simp only [hD, sigR_inclE, hι, he, sub_self]
  have DO : ∀ b ∈ OAd F E, D b ∈ OAd F' E' := by
    intro b hb
    exact Subring.sub_mem _ ((hO _).1 (sigR_mem_OAd σ hb)) (sigR_mem_OAd σ' ((hO _).1 hb))
  have Dzero : ∀ b ∈ OAd F E, D b = 0 := by
    intro b hb
    refine h3' (D b) fun m hm => ?_
    obtain ⟨x, t, ht, hbt⟩ := h2 b hb m hm
    exact ⟨D t, DO t ht, by rw [hbt, Dadd, Dincl, Dmul, zero_add]⟩
  obtain ⟨m, hm, hma⟩ := h4 a
  have h0 : (m : E' ⊗[F'] Ad F') * D a = 0 := by rw [← Dmul]; exact Dzero _ hma
  have hu : IsUnit (m : E' ⊗[F'] Ad F') := by
    rw [← map_natCast (inclE (F := F') (E := E') (Ad F')) m]
    exact (IsUnit.mk0 (m : E') (Nat.cast_ne_zero.2 hm.ne')).map _
  have hDa : D a = 0 := hu.mul_right_eq_zero.1 h0
  simp only [hD] at hDa
  exact sub_eq_zero.1 hDa

end GlobalTheory.St.G.IotaConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralFiniteAdeleIsoCommutesWithConjugation
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.IotaSigmaCompatibility

theorem iotaA_sigA : ∀ (D : D7) (X : HidaSetting D)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA →
    ∀ a, ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D)
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιA a) := by
  intro D X ιA h a
  have he : ∀ x : X.B.I.E, X.ιE (X.B.I.cm.sig x) = Formalism.L2.Forms.sigD D (X.ιE x) := by
    intro x
    have h1 : X.B.I.cm.sig x = star x := rfl
    have h2 : Formalism.L2.Forms.sigD D (X.ιE x) = star (X.ιE x) := rfl
    rw [h1, h2, X.ιE_conj, Formalism.BasicNotions.bridge_star_holds D.R D.host]
  exact GlobalTheory.St.G.IotaConj.iota_sigR X.B.I.F X.B.I.E D.host.F D.host.E X.B.I.cm.sig
    (Formalism.L2.Forms.sigD D) X.ιE ιA he h.1 h.2 a

end GlobalTheory.St.G.IotaSigmaCompatibility
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralFiniteAdeleIsoCommutesWithConjugationStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFiniteAdeleIso_commutes_with_conjugation : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ a, ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιA a) := by
  first | exact @GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA | exact GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA | (intros; apply GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightConvolutionOperatorAeEqIntegralAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightConvolutionOperatorAeEqIntegralAdelic
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.ConvKernel

section General

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {ν : Measure X} {μ : Measure Y}

theorem integrable_prod_restrict [SFinite ν] [SFinite μ] (K : X → Y → ℂ)
    (hK : AEStronglyMeasurable (fun p : X × Y => K p.1 p.2) (ν.prod μ))
    (r : Y → Lp ℂ 2 ν) (hr : ∀ g, (r g : X → ℂ) =ᵐ[ν] fun x => K x g) (C : ℝ)
    (hC : ∀ g, ‖r g‖ ≤ C) (φ : Y → ℂ) (hφ : Integrable φ μ) (s : Set X) (hs : ν s < ⊤) :
    Integrable (fun p : X × Y => φ p.2 * K p.1 p.2) ((ν.restrict s).prod μ) := by
  have hK' : AEStronglyMeasurable (fun p : X × Y => K p.1 p.2) ((ν.restrict s).prod μ) :=
    hK.mono_ac (Measure.AbsolutelyContinuous.prod
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self) Measure.AbsolutelyContinuous.rfl)
  have hm : AEStronglyMeasurable (fun p : X × Y => φ p.2 * K p.1 p.2) ((ν.restrict s).prod μ) :=
    (hφ.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul hK'
  refine ⟨hm, ?_⟩
  set M : ENNReal := ENNReal.ofReal C * (ν s) ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal)
    with hM
  have hMfin : M ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    refine ENNReal.rpow_ne_top_of_nonneg ?_ hs.ne
    norm_num
  have hb : ∀ g, ∫⁻ x, ‖K x g‖ₑ ∂(ν.restrict s) ≤ M := by
    intro g
    have e1 : ∫⁻ x, ‖K x g‖ₑ ∂(ν.restrict s) = eLpNorm (r g : X → ℂ) 1 (ν.restrict s) := by
      rw [eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable (r g)).restrict]
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae (s := s) (hr g)] with x hx
      rw [hx]
    have e2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν.restrict s) (p := 1) (q := 2)
      (f := (r g : X → ℂ)) (by norm_num) (Lp.aestronglyMeasurable (r g)).restrict
    rw [Measure.restrict_apply_univ] at e2
    rw [e1]
    refine e2.trans ?_
    refine mul_le_mul' ?_ le_rfl
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    have h3 := hC g
    rw [Lp.norm_def] at h3
    rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (r g))]
    exact ENNReal.ofReal_le_ofReal h3
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hm.enorm]
  calc ∫⁻ g, ∫⁻ x, ‖φ g * K x g‖ₑ ∂(ν.restrict s) ∂μ ≤ ∫⁻ g, ‖φ g‖ₑ * M ∂μ := by
        refine lintegral_mono fun g => ?_
        simp only [enorm_mul]
        rw [lintegral_const_mul' _ _ enorm_ne_top]
        exact mul_le_mul' le_rfl (hb g)
    _ = (∫⁻ g, ‖φ g‖ₑ ∂μ) * M := lintegral_mul_const' _ _ hMfin
    _ < ⊤ := ENNReal.mul_lt_top hφ.2 hMfin.lt_top

theorem weak_integral_ae_eq [SigmaFinite ν] [SFinite μ] (K : X → Y → ℂ)
    (hK : AEStronglyMeasurable (fun p : X × Y => K p.1 p.2) (ν.prod μ))
    (r : Y → Lp ℂ 2 ν) (hr : ∀ g, (r g : X → ℂ) =ᵐ[ν] fun x => K x g) (C : ℝ)
    (hC : ∀ g, ‖r g‖ ≤ C) (φ : Y → ℂ) (hφ : Integrable φ μ) (t : Lp ℂ 2 ν)
    (ht : ∀ u : Lp ℂ 2 ν, ⟪u, t⟫_ℂ = ∫ g, φ g * ⟪u, r g⟫_ℂ ∂μ) :
    (∀ᵐ x ∂ν, Integrable (fun g => φ g * K x g) μ) ∧
      (t : X → ℂ) =ᵐ[ν] fun x => ∫ g, φ g * K x g ∂μ := by
  have hI := integrable_prod_restrict K hK r hr C hC φ hφ
  refine ⟨?_, ?_⟩
  · refine ae_of_forall_measure_lt_top_ae_restrict _ fun s _ hs => ?_
    exact (hI s hs).prod_right_ae
  · refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ hs => ?_) (fun s _ hs => ?_)
      (fun s hsm hs => ?_)
    · exact integrableOn_Lp_of_measure_ne_top t (by norm_num) hs.ne
    · exact (hI s hs).integral_prod_left
    · have h := ht (indicatorConstLp 2 hsm hs.ne (1 : ℂ))
      simp only [L2.inner_indicatorConstLp_one] at h
      rw [h, integral_integral_swap (f := fun x g => φ g * K x g) (hI s hs)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only
      rw [integral_const_mul]
      congr 1
      exact integral_congr_ae (ae_restrict_of_ae (hr g))

end General

theorem rconv_eq_integral : ∀ (B : RowsAut) (φ : B.I.GA → ℂ) (T : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund), B.I.IsRConv B.μf B.fund B.R φ T → ∀ y : B.I.L2 B.μf B.fund, (∀ᵐ x ∂((B.I.muA B.μf).restrict B.fund), Integrable (fun g => φ g * B.I.ext y (x * g)) (B.I.muA B.μf)) ∧ (T y : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund] fun x => ∫ g, φ g * B.I.ext y (x * g) ∂(B.I.muA B.μf) := by
  intro B φ T hT y
  obtain ⟨hT2, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨hl, -⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf
  obtain ⟨-, -, hn, -, hext⟩ := GlobalTheory.T.rightRegularRep_unitary_stronglyContinuous B
  have : BorelSpace B.I.GA := inferInstance
  have : (B.I.muA B.μf).IsMulLeftInvariant := ⟨hl⟩
  have : SigmaFinite (B.I.muA B.μf) := by
    unfold AutInst.muA; infer_instance
  have hq : Measure.QuasiMeasurePreserving (fun p : B.I.GA × B.I.GA => p.1 * p.2)
      (((B.I.muA B.μf).restrict B.fund).prod (B.I.muA B.μf)) (B.I.muA B.μf) :=
    Measure.quasiMeasurePreserving_snd.comp
      (measurePreserving_prod_mul ((B.I.muA B.μf).restrict B.fund)
        (B.I.muA B.μf)).quasiMeasurePreserving
  exact weak_integral_ae_eq (fun x g => B.I.ext y (x * g))
    ((hext y).2.comp_quasiMeasurePreserving hq) (fun g => B.R g y) (fun g => B.R_spec g y) ‖y‖
    (fun g => (hn g y).le) φ hT.1 (T y) (fun u => hT.2 u y)

end GlobalTheory.ConvKernel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightConvolutionOperatorAeEqIntegralAdelicStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightConvolution_operator_ae_eq_integral_adelic : ∀ (B : RowsAut) (φ : B.I.GA → ℂ) (T : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund), B.I.IsRConv B.μf B.fund B.R φ T → ∀ y : B.I.L2 B.μf B.fund, (∀ᵐ x ∂((B.I.muA B.μf).restrict B.fund), Integrable (fun g => φ g * B.I.ext y (x * g)) (B.I.muA B.μf)) ∧ (T y : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund] fun x => ∫ g, φ g * B.I.ext y (x * g) ∂(B.I.muA B.μf) := by
  first | exact @GlobalTheory.ConvKernel.rconv_eq_integral | exact GlobalTheory.ConvKernel.rconv_eq_integral | (intros; apply GlobalTheory.ConvKernel.rconv_eq_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqFundamentalDomainInter
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqFundamentalDomainInter
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.CovolRat

theorem covol_eq_inter_fund : ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund A : Set I.GA), I.IsFundDom (I.muA μf) fund → MeasurableSet A → (∀ γ ∈ I.GFset, ∀ x ∈ A, γ * x ∈ A) → covol I.GFset (I.muA μf) A = I.muA μf (A ∩ fund) ∧ 0 < I.muA μf fund := by
  intro I μf _ _ fund A hfund hA hinv
  obtain ⟨hleft, -, -, -, hopen⟩ := GlobalTheory.AdelicUnimod.adelic_unimodular I μf
  obtain ⟨⟨Γ, hΓ⟩, hcount, -⟩ := GlobalTheory.RatDiscrete.subgroup_countable_discrete I
  obtain ⟨hmeas, hcov, hdisj⟩ := hfund

  have hm : ∀ γ, γ ∈ Γ ↔ γ ∈ I.GFset := fun γ => by rw [← hΓ]; exact SetLike.mem_coe.symm
  refine ⟨?_, ?_⟩
  · have key := GlobalTheory.covol_eq_measure_inter_fund I.GA Γ (I.muA μf) fund A (by rw [hΓ]; exact hcount)
      (fun γ _ => hleft γ) hmeas
      (fun y => by obtain ⟨γ, hγ, h⟩ := hcov y; exact ⟨γ, (hm γ).2 hγ, h⟩)
      (fun γ hγ h1 => hdisj γ ((hm γ).1 hγ) h1) hA (fun γ hγ x hx => hinv γ ((hm γ).1 hγ) x hx)
    rw [hΓ] at key
    exact key
  ·
    rw [pos_iff_ne_zero]
    intro h0
    have hpre : ∀ γ : I.GA, I.muA μf ((fun y => γ * y) ⁻¹' fund) = 0 := by
      intro γ
      rw [← Measure.map_apply (measurable_const_mul γ) hmeas, hleft γ, h0]
    have hsub : (Set.univ : Set I.GA) ⊆ ⋃ γ ∈ I.GFset, (fun y => γ * y) ⁻¹' fund := by
      intro y _
      obtain ⟨γ, hγ, h⟩ := hcov y
      exact Set.mem_biUnion hγ h
    have hnull : I.muA μf Set.univ = 0 :=
      measure_mono_null hsub ((measure_biUnion_null_iff hcount).2 fun γ _ => hpre γ)
    have hpos := hopen Set.univ isOpen_univ ⟨1, trivial⟩
    rw [hnull] at hpos
    exact lt_irrefl _ hpos

end GlobalTheory.CovolRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqFundamentalDomainInterStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter : ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund A : Set I.GA), I.IsFundDom (I.muA μf) fund → MeasurableSet A → (∀ γ ∈ I.GFset, ∀ x ∈ A, γ * x ∈ A) → covol I.GFset (I.muA μf) A = I.muA μf (A ∩ fund) ∧ 0 < I.muA μf fund := by
  first | exact @GlobalTheory.CovolRat.covol_eq_inter_fund | exact GlobalTheory.CovolRat.covol_eq_inter_fund | (intros; apply GlobalTheory.CovolRat.covol_eq_inter_fund <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFiniteCharacterInverseExpTrace
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFiniteCharacterInverseExpTrace
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.St.G

theorem trace_cm_eq_add_star {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (x : E) :
    algebraMap F E (Algebra.trace F E x) = x + star x := by
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hc.deg2
  have : Algebra.IsQuadraticExtension F E := ⟨hc.deg2⟩
  classical
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom hc.sig hc.sig
    (by ext y; simp [Formalism.BasicNotions.CMData.sig]) (by ext y; simp [Formalism.BasicNotions.CMData.sig])
  have hs : ∀ y, s y = star y := fun y => rfl
  have hne : (1 : E ≃ₐ[F] E) ≠ s := by
    intro h
    have hall : ∀ y : E, y ∈ (algebraMap F E).range := fun y => (hc.fixed y).1 (by
      rw [← hs, ← h]; rfl)
    have h1 : Module.finrank F E = 1 := by
      apply finrank_eq_one (1 : E) one_ne_zero
      intro w
      obtain ⟨a, ha⟩ := hall w
      exact ⟨a, by rw [Algebra.smul_def, mul_one, ha]⟩
    rw [hc.deg2] at h1
    omega
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hc.deg2]
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, hcard]
  rw [trace_eq_sum_automorphisms, huniv, Finset.sum_pair hne, hs]
  rfl

theorem psiEinf_eq_exp_trace (I : Formalism.MainNotions.S.AutInst) (y : I.E) :
    psiEinf I y = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ I.E y : ℚ) : ℂ)) := by
  have := I.cm.totReal
  rw [show psiEinf I y = PI.ScPsiExists.psiEinf I y from rfl, PI.ScPsiExists.UnitaryGroupMassFormula.psiEinf_eq,
    PI.ScPsiExists.UnitaryGroupMassFormula.sHom_coe]
  have h2 : ∀ v, I.φ v y + star (I.φ v y) =
      v.embedding (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed y) := by
    intro v
    rw [← I.φ_over, PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, map_add (f := _), I.cm.cmUnram.2.1 (I.φ v) y]
    rfl
  have h3 : PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed y = Algebra.trace I.F I.E y := by
    apply (algebraMap I.F I.E).injective
    rw [PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, trace_cm_eq_add_star I.cm]
  rw [Finset.sum_congr rfl (fun v _ => h2 v), PI.ScPsiExists.UnitaryGroupMassFormula.sum_embedding_eq_trace, h3,
    Algebra.trace_trace]
  rfl

theorem psiEf_transport_rat : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ x : D.host.E, X.psiEf (ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) x)) * Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E x : ℚ) : ℂ)) = 1 := by
  intro D X ιA hA x
  have h1 : ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) x) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm x) := by
    rw [RingEquiv.symm_apply_eq, hA.1 (X.ιE.symm x), X.ιE.apply_symm_apply]
  have htr : Algebra.trace ℚ D.host.E x = Algebra.trace ℚ X.B.I.E (X.ιE.symm x) := by
    conv_lhs => rw [← X.ιE.apply_symm_apply x]
    exact Algebra.trace_eq_of_algEquiv X.ιE.toRatAlgEquiv (X.ιE.symm x)
  rw [h1, htr, ← psiEinf_eq_exp_trace]
  exact X.psiEf_rat (X.ιE.symm x)

end GlobalTheory.St.G

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFiniteCharacterInverseExpTraceStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedFiniteCharacter_inverse_exp_trace : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ x : D.host.E, X.psiEf (ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) x)) * Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E x : ℚ) : ℂ)) = 1 := by
  first | exact @GlobalTheory.St.G.psiEf_transport_rat | exact GlobalTheory.St.G.psiEf_transport_rat | (intros; apply GlobalTheory.St.G.psiEf_transport_rat <;> assumption)
end
end
