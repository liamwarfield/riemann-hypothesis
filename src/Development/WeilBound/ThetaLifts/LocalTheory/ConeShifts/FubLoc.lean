module

public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ExtendByZeroOnSubsetApplyCoe
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupTwoModelsRationalRealUnipotentDictio

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ContinuousFc
section -- merged from Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.FubTate
noncomputable section

namespace PositivityTheory.ThKG.Fub

open MeasureTheory Topology Filter

theorem one_of_compact {G : Type} [Group G] [TopologicalSpace G] (f : G →* NNReal) (hf : Continuous f) {K : Set G} (hK : IsCompact K)
    {x : G} (hx : ∀ n : ℤ, x ^ n ∈ K) : f x = 1 := by
  obtain ⟨C, hC⟩ := (hK.image hf).bddAbove
  have key : ∀ y : G, (∀ n : ℕ, y ^ n ∈ K) → f y ≤ 1 := fun y hy => by
    by_contra h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 h)
    exact absurd (hC ⟨_, hy n, map_pow f y n⟩) (not_le.2 hn)
  have h1 := key x fun n => by simpa using hx n
  have h2 := key x⁻¹ fun n => by simpa using hx (-n)
  have h3 : f x * f x⁻¹ = 1 := by rw [← map_mul]; simp
  refine le_antisymm h1 ?_
  calc (1 : NNReal) = f x * f x⁻¹ := h3.symm
    _ ≤ f x * 1 := by gcongr
    _ = f x := mul_one _

theorem circle_one {z : Circle} (h : ∀ n : ℕ, ‖((z ^ n : Circle) : ℂ) - 1‖ < 1) : z = 1 := by
  by_contra hz
  have h0 : (z : ℂ) - 1 ≠ 0 := fun e => hz (Circle.coe_eq_one.1 (sub_eq_zero.1 e))
  have hre : ∀ n : ℕ, 1 / 2 < ((z : ℂ) ^ n).re := fun n => by
    have h1 := h n
    rw [Circle.coe_pow] at h1
    have h2 : ‖(z : ℂ) ^ n‖ = 1 := by rw [norm_pow, Circle.norm_coe, one_pow]
    have h3 := Complex.sq_norm ((z : ℂ) ^ n - 1)
    have h4 := Complex.sq_norm ((z : ℂ) ^ n)
    rw [Complex.normSq_apply] at h3 h4
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h3
    nlinarith [norm_nonneg ((z : ℂ) ^ n - 1)]
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ‖(z : ℂ) - 1‖)
  have hp : 0 < ‖(z : ℂ) - 1‖ := norm_pos_iff.2 h0
  have e : (∑ i ∈ Finset.range N, (z : ℂ) ^ i) * (z - 1) = z ^ N - 1 := geom_sum_mul _ _
  have h1 : (N : ℝ) / 2 ≤ ‖∑ i ∈ Finset.range N, (z : ℂ) ^ i‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    have := Finset.card_nsmul_le_sum (Finset.range N) (fun i => ((z : ℂ) ^ i).re) (1 / 2) fun i _ => (hre i).le
    simpa [div_eq_mul_inv] using this
  have h2 : ‖(z : ℂ) ^ N - 1‖ < 1 := by simpa using h N
  rw [← e, norm_mul] at h2
  rw [div_lt_iff₀ hp] at hN
  nlinarith

theorem pow_mem_of_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G))
    {K : Set G} (hK : IsCompact K) {x : G} (hx : ∀ n : ℕ, x ^ n ∈ K) : ∃ k : ℕ, 0 < k ∧ x ^ k ∈ U := by
  haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  have hf : ((QuotientGroup.mk : G → G ⧸ U) '' K).Finite := (hK.image QuotientGroup.continuous_mk).finite_of_discrete
  obtain ⟨i, j, hij, e⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem (f := fun n : ℕ => (QuotientGroup.mk (x ^ n) : G ⧸ U))
    (fun n => Set.mem_image_of_mem _ (hx n)) hf
  refine ⟨j - i, by omega, ?_⟩
  have := QuotientGroup.eq.1 e
  rwa [show x ^ j = x ^ i * x ^ (j - i) by rw [← pow_add]; congr 1; omega, inv_mul_cancel_left] at this

theorem tate {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (γ : Measure H) [γ.IsMulLeftInvariant] (o : H → ℤ) (ho : ∀ x y, o (x * y) = o x + o y) (hU : IsOpen {x | o x = 0})
    (h1 : γ {x | o x = 0} = 1) (ϖ : H) (hϖ : o ϖ = 1) (χ : H →* ℂ) (hχ : ∀ x, o x = 0 → χ x = 1) (ht : ‖χ ϖ‖ < 1) (m : ℤ) :
    Integrable (fun x => (if m ≤ o x then (1 : ℂ) else 0) * χ x) γ ∧
      ∫ x, (if m ≤ o x then (1 : ℂ) else 0) * χ x ∂γ = χ ϖ ^ m * (1 - χ ϖ)⁻¹ := by
  let O : H →* Multiplicative ℤ := MonoidHom.mk' (fun x => Multiplicative.ofAdd (o x)) fun x y => by rw [ho]; rfl
  have oz : ∀ (k : ℤ) x, o (ϖ ^ k * x) = k + o x := fun k x => by
    have := map_zpow O ϖ k
    have h2 : o (ϖ ^ k) = k := by
      have h3 := congrArg Multiplicative.toAdd this
      simpa [O, hϖ] using h3
    rw [ho, h2]
  have h0 : χ ϖ ≠ 0 := fun e => by
    have := map_mul χ ϖ ϖ⁻¹
    rw [mul_inv_cancel, map_one, e, zero_mul] at this
    exact one_ne_zero this
  let A : ℕ → Set H := fun k => {x | o x = m + k}
  have hA : ∀ k, A k = (fun x => ϖ ^ (-(m + k)) * x) ⁻¹' {x | o x = 0} := fun k => Set.ext fun x => by
    simp only [A, Set.mem_setOf_eq, Set.mem_preimage, oz]; omega
  have mA : ∀ k, MeasurableSet (A k) := fun k => by
    rw [hA]; exact (hU.preimage (continuous_const.mul continuous_id)).measurableSet
  have vA : ∀ k, γ (A k) = 1 := fun k => by rw [hA, measure_preimage_mul, h1]
  have cA : ∀ k, ∀ x ∈ A k, χ x = χ ϖ ^ m * χ ϖ ^ k := fun k x hx => by
    have := hχ _ ((hA k ▸ hx : x ∈ (fun x => ϖ ^ (-(m + k)) * x) ⁻¹' {x | o x = 0}))
    rw [map_mul, map_zpow, zpow_neg, inv_mul_eq_one₀ (zpow_ne_zero _ h0)] at this
    rw [← this, zpow_add₀ h0, zpow_natCast]
  have dA : Pairwise (Function.onFun Disjoint A) := fun i j hij => Set.disjoint_left.2 fun x h h' => hij (by
    simp only [A, Set.mem_setOf_eq] at h h'; omega)
  have eU : (fun x => (if m ≤ o x then (1 : ℂ) else 0) * χ x) = (⋃ k, A k).indicator χ := funext fun x => by
    by_cases h : m ≤ o x
    · rw [if_pos h, one_mul, Set.indicator_of_mem (Set.mem_iUnion.2 ⟨(o x - m).toNat, by simp only [A, Set.mem_setOf_eq]; omega⟩)]
    · rw [if_neg h, zero_mul, Set.indicator_of_notMem fun h' => by
        obtain ⟨k, hk⟩ := Set.mem_iUnion.1 h'
        simp only [A, Set.mem_setOf_eq] at hk; omega]
  have iA : ∀ k, IntegrableOn χ (A k) γ := fun k =>
    (integrableOn_const (C := χ ϖ ^ m * χ ϖ ^ k) (by rw [vA]; simp)).congr_fun (fun x hx => (cA k x hx).symm) (mA k)
  have sA : ∀ k, ∫ x in A k, χ x ∂γ = χ ϖ ^ m * χ ϖ ^ k := fun k => by
    rw [setIntegral_congr_fun (mA k) (cA k), setIntegral_const, Measure.real, vA]; simp
  have nA : ∀ k, ∫ x in A k, ‖χ x‖ ∂γ = ‖χ ϖ ^ m‖ * ‖χ ϖ‖ ^ k := fun k => by
    rw [setIntegral_congr_fun (mA k) (g := fun _ => ‖χ ϖ ^ m‖ * ‖χ ϖ‖ ^ k) fun x hx => by simp only [cA k x hx, norm_mul, norm_pow],
      setIntegral_const, Measure.real, vA]; simp
  have iU : IntegrableOn χ (⋃ k, A k) γ := integrableOn_iUnion_of_summable_integral_norm iA (by
    simp only [nA]; exact (summable_geometric_of_lt_one (norm_nonneg _) ht).mul_left _)
  rw [eU, integrable_indicator_iff (MeasurableSet.iUnion mA), integral_indicator (MeasurableSet.iUnion mA)]
  refine ⟨iU, (hasSum_integral_iUnion mA dA iU).unique ?_⟩
  simp only [sA]
  exact (hasSum_geometric_of_norm_lt_one ht).mul_left _

end PositivityTheory.ThKG.Fub

end
end

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKG.Fub GlobalTheory.Doubling

attribute [local instance] ae_ring ae_smul ae_t2 ae_lc ae_sc

theorem id_lc : LocallyCompactSpace (AE F E)ˣ := units_top.1
theorem id_sc : SecondCountableTopology (AE F E)ˣ := units_top.2
theorem id_borel : BorelSpace (AE F E)ˣ := ⟨rfl⟩

attribute [local instance] id_lc id_sc id_borel


variable (F E) in
def fc : AE F E →+* FiniteAdeleRing (𝓞 E) E := (finAdEquiv F E).toRingHom.comp (finTens F E)

def cw (w : HeightOneSpectrum (𝓞 E)) : AE F E →+* w.adicCompletion E := (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV E w).toRingHom.comp (fc F E)

theorem cw_def (w : HeightOneSpectrum (𝓞 E)) (x : AE F E) : cw w x = finAdEquiv F E (finTens F E x) w := rfl

theorem ae_ext {x y : AE F E} (h1 : infTens F E x = infTens F E y) (h2 : ∀ w, cw w x = cw w y) : x = y :=
  tens_ext h1 ((finAdEquiv F E).injective (FiniteAdeleRing.ext _ h2))

theorem cw_eq {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (x : AE F E) : cw w x = toCompl h (compFin F E v x) := by
  rw [cw_def, finAdEquiv_apply h]
  congr 1
  change ((Algebra.TensorProduct.map _ _).comp (Algebra.TensorProduct.map _ _)) _ = _
  rw [← Algebra.TensorProduct.map_comp]
  rfl

theorem continuous_fc : Continuous (fc F E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Af F)
  haveI : LocallyCompactSpace (Af F ⊗[F] E) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : T2Space (Af F ⊗[F] E) := e0.isEmbedding.t2Space
  have ho : IsOpenMap (finAdEquiv F E).symm :=
    AddMonoidHom.isOpenMap_of_sigmaCompact (finAdEquiv F E).symm.toAddEquiv.toAddMonoidHom (finAdEquiv F E).symm.surjective
      continuous_finAdEquiv_symm
  have h1 : Continuous (finAdEquiv F E) :=
    ((finAdEquiv F E).symm.toEquiv.toHomeomorphOfContinuousOpen continuous_finAdEquiv_symm ho).symm.continuous
  exact h1.comp (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (sndA F).toLinearMap (map_mul (sndA F)) continuous_snd)

def io (a : AF F) : AE F E := algebraMap (AF F) (AE F E) a

theorem cw_io (w : HeightOneSpectrum (𝓞 E)) (a : AF F) : cw w (io a : AE F E) = complMap rfl (evFin F (w.under (𝓞 F)) a) :=
  (finAdEquiv_tmul a.2 (1 : E) w).trans (by rw [map_one, mul_one]; rfl)

theorem inf_io {a : AF F} (h : a.1 = 0) : infTens F E (io a) = 0 := by
  show a.1 ⊗ₜ[F] (1 : E) = 0
  rw [h, TensorProduct.zero_tmul]

theorem io_mul (a b : AF F) : (io a * io b : AE F E) = io (a * b) := (map_mul _ _ _).symm
theorem io_idem {a : AF F} (h : a * a = a) : (io a * io a : AE F E) = io a := by rw [io_mul, h]
theorem io_orth {a b : AF F} (h : a * b = 0) : (io a * io b : AE F E) = 0 := by rw [io_mul, h]; exact map_zero _


variable (F) in
def ew (w : HeightOneSpectrum (𝓞 E)) : AE F E := extZero F E ((finAdEquiv F E).symm (1 - Neutral.B1.finiteSingle E w 0))

theorem inf_ew (w : HeightOneSpectrum (𝓞 E)) : infTens F E (ew F w) = 0 := infTens_extZero _

open Classical in
theorem cw_ew (u w : HeightOneSpectrum (𝓞 E)) : cw u (ew F w) = if u = w then 1 else 0 := by
  rw [cw_def, ew, finTens_extZero, RingEquiv.apply_symm_apply]
  show 1 - Neutral.B1.finiteSingle E w 0 u = _
  split_ifs with h
  · subst h; rw [finSingle_self, sub_zero]
  · rw [finSingle_ne h, sub_self]

theorem ew_idem (w : HeightOneSpectrum (𝓞 E)) : ew F w * ew F w = ew F w :=
  ae_ext (by rw [map_mul, inf_ew, mul_zero]) fun u => by rw [map_mul, cw_ew]; split_ifs <;> simp

theorem ew_orth {w w' : HeightOneSpectrum (𝓞 E)} (h : w ≠ w') : ew F w * ew F w' = 0 :=
  ae_ext (by rw [map_mul, inf_ew, zero_mul, map_zero]) fun u => by
    rw [map_mul, cw_ew, cw_ew, map_zero]
    split_ifs with h1 h2
    · exact absurd (h1.symm.trans h2) h
    all_goals simp

open Classical in
theorem cw_idem (w : HeightOneSpectrum (𝓞 E)) (v : Pl F) : cw w (io (idem F v) : AE F E) = if w.under (𝓞 F) = v then 1 else 0 := by
  rw [cw_io]
  split_ifs with h
  · subst h; rw [evFin_idem_self_k, map_one]
  · rw [evFin_idem_ne_k h, map_zero]

open Classical in
theorem cw_rest (w : HeightOneSpectrum (𝓞 E)) (T : Finset (Pl F)) :
    cw w (io (rest T) : AE F E) = if w.under (𝓞 F) ∈ T then 0 else 1 := by
  rw [cw_io, evFin_rest]; split_ifs <;> simp

theorem idem_eq_sum (v : Pl F) : (io (idem F v) : AE F E) = ∑ w ∈ Formalism.L2.Host.aboveF (L := E) F v, ew F w + 0 := by
  classical
  refine ae_ext (by rw [inf_io rfl, add_zero, map_sum, Finset.sum_eq_zero fun w _ => inf_ew w]) fun u => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [add_zero, map_sum, cw_idem]
  simp only [cw_ew, Finset.sum_ite_eq, mem_aboveF]

abbrev PI (a : AE F E) : (AE F E)ˣ →* (AE F E)ˣ := unitP (R := AE F E) a

theorem hom_PI {A : Type} [CommRing A] (φ : AE F E →+* A) {a : AE F E} (h : a * a = a) (l : (AE F E)ˣ) :
    φ (PI a l) = φ a * φ l + (1 - φ a) := by
  rw [coe_unitP h]; simp

theorem cw_PI_one {a : AE F E} (h : a * a = a) {w} (h1 : cw w a = 1) (l : (AE F E)ˣ) : cw w (PI a l : AE F E) = cw w (l : AE F E) := by
  rw [hom_PI _ h, h1]; simp

theorem cw_PI_zero {a : AE F E} (h : a * a = a) {w} (h1 : cw w a = 0) (l : (AE F E)ˣ) : cw w (PI a l : AE F E) = 1 := by
  rw [hom_PI _ h, h1]; simp

theorem cw_cases {a : AE F E} (h : a * a = a) (w) : cw w a = 0 ∨ cw w a = 1 :=
  IsIdempotentElem.iff_eq_zero_or_one.1 (show _ * _ = _ by rw [← map_mul, h])

def vw (w : HeightOneSpectrum (𝓞 E)) (l : (AE F E)ˣ) : WithZero (Multiplicative ℤ) := Valued.v (cw w (l : AE F E))

theorem vw_mul (w) (l l' : (AE F E)ˣ) : vw w (l * l') = vw w l * vw w l' := by simp [vw]
theorem vw_one (w) : vw w (1 : (AE F E)ˣ) = 1 := by simp [vw]
theorem vw_inv (w) (l : (AE F E)ˣ) : vw w l * vw w l⁻¹ = 1 := by rw [← vw_mul, mul_inv_cancel, vw_one]
theorem vw_ne (w) (l : (AE F E)ˣ) : vw w l ≠ 0 := left_ne_zero_of_mul_eq_one (vw_inv w l)


variable (F E) in
def UI : Subgroup (AE F E)ˣ where
  carrier := {l | ∀ w, vw w l = 1}
  one_mem' := vw_one
  mul_mem' h h' w := by rw [vw_mul, h w, h' w, one_mul]
  inv_mem' {l} h w := by have := vw_inv w l; rwa [h w, one_mul] at this

theorem mem_UI_iff (l : (AE F E)ˣ) : l ∈ UI F E ↔ (∀ w, vw w l ≤ 1) ∧ ∀ w, vw w l⁻¹ ≤ 1 :=
  ⟨fun h => ⟨fun w => (h w).le, fun w => ((UI F E).inv_mem h w).le⟩, fun h w => le_antisymm (h.1 w) (by
    calc 1 = vw w l * vw w l⁻¹ := (vw_inv w l).symm
      _ ≤ vw w l * 1 := mul_le_mul_right (h.2 w) _
      _ = vw w l := mul_one _)⟩

theorem isOpen_UI : IsOpen (UI F E : Set (AE F E)ˣ) := by
  have h : IsOpen {a : FiniteAdeleRing (𝓞 E) E | ∀ w, a w ∈ HeightOneSpectrum.adicCompletionIntegers E w} :=
    RestrictedProduct.isOpen_forall_mem fun w => Valued.isOpen_integer _
  have h1 := h.preimage (continuous_fc (F := F))
  have : (UI F E : Set (AE F E)ˣ) = (Units.val ⁻¹' (fc F E ⁻¹' {a | ∀ w, a w ∈ HeightOneSpectrum.adicCompletionIntegers E w})) ∩ ((fun l : (AE F E)ˣ => ((l⁻¹ : (AE F E)ˣ) : AE F E)) ⁻¹'
      (fc F E ⁻¹' {a | ∀ w, a w ∈ HeightOneSpectrum.adicCompletionIntegers E w})) := Set.ext fun l => mem_UI_iff l
  rw [this]
  exact (h1.preimage Units.continuous_val).inter (h1.preimage Units.continuous_coe_inv)

theorem sysI : Sys (PI (F := F) (E := E)) ⊤ (UI F E) fun a => a * a = a := by
  refine {
    cont a ha := unitInvariant_continuous ha
    comp a b ha hb := unitInvariant_comp ha hb
    zero := unitInvariant_zero
    add a b ha hb h := ⟨idem_add ha hb h, unitInvariant_add ha hb h⟩
    idem _ h := h
    cK := isClosed_univ
    mK _ _ _ _ := trivial
    mU := isOpen_UI.measurableSet
    one := (UI F E).one_mem
    mul _ h _ h' := (UI F E).mul_mem h h'
    pU := ?_ }
  intro a ha l hl w
  rcases cw_cases ha w with e | e
  · rw [vw, cw_PI_zero ha e, map_one]
  · rw [vw, cw_PI_one ha e]; exact hl w

theorem inf_of_part {a : AE F E} (ha : a * a = a) (h0 : infTens F E a = 0) {l : (AE F E)ˣ} (h : l ∈ part PI ⊤ a) :
    infTens F E l = 1 := by
  rw [← show PI a l = l from h.2, hom_PI _ ha, h0]; simp

theorem cpt_I {a : AE F E} (ha : a * a = a) (h0 : infTens F E a = 0) :
    IsCompact ((part PI ⊤ a : Set (AE F E)ˣ) ∩ UI F E) := by
  let j : FiniteAdeleRing (𝓞 E) E → AE F E := fun y => 1 - extZero F E 1 + extZero F E ((finAdEquiv F E).symm y)
  have hj : Continuous j := continuous_const.add (continuous_extZero.comp continuous_finAdEquiv_symm)
  have hS := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties E).1.image hj
  have hc := hS.prod (hS.image MulOpposite.continuous_op)
  have key : ∀ l ∈ (part PI ⊤ a : Set (AE F E)ˣ) ∩ UI F E, ∃ y, (∀ w, y w ∈ HeightOneSpectrum.adicCompletionIntegers E w) ∧
      j y = (l : AE F E) := fun l hl => ⟨fc F E l, fun w => (hl.2 w).le, tens_ext
        (by rw [inf_of_part ha h0 hl.1, map_add (f := _), map_sub, map_one, infTens_extZero, infTens_extZero, sub_zero, add_zero])
        (by rw [map_add (f := _), map_sub, map_one, finTens_extZero, finTens_extZero, sub_self, zero_add]
            exact (finAdEquiv F E).symm_apply_apply _)⟩
  refine (Units.isClosedEmbedding_embedProduct.isCompact_preimage hc).of_isClosed_subset
    ((sysI.closed ha).inter ((UI F E).isClosed_of_isOpen isOpen_UI)) fun l hl => ⟨key l hl, _, key l⁻¹
      ⟨Subgroup.inv_mem _ hl.1, (UI F E).inv_mem hl.2⟩, rfl⟩

theorem co_I {a : AE F E} (ha : a * a = a) (h0 : infTens F E a = 0) : CO PI ⊤ (UI F E : Set (AE F E)ˣ) a := by
  refine ⟨?_, isOpen_UI.preimage continuous_subtype_val⟩
  have := (sysI.closed ha).isClosedEmbedding_subtypeVal.isCompact_preimage (cpt_I ha h0)
  exact this.of_isClosed_subset (((UI F E).isClosed_of_isOpen isOpen_UI).preimage continuous_subtype_val) fun x hx => ⟨x.2, hx⟩

theorem coe_PI_io {a : AF F} (h : a * a = a) (l : (AE F E)ˣ) :
    (PI (io a) l : AE F E) = a • (l : AE F E) + (1 - a) • (1 : AE F E) := by
  rw [coe_unitP (io_idem h), smul_eq_mul, smul_eq_mul, Algebra.smul_def, Algebra.smul_def, map_sub, map_one]; rfl

theorem idAt_eq {R : Type} [Zero R] (ev : AF F → R) {a : AF F} (h : a * a = a) (hat : ∀ z : AE F E, At ev z ↔ a • z = z) :
    idAt E ev = part PI ⊤ (io a) := by
  have : {l : (AE F E)ˣ | At ev ((l : AE F E) - 1)} = ((part PI ⊤ (io a) : Subgroup (AE F E)ˣ) : Set (AE F E)ˣ) := Set.ext fun l => by
    show At ev ((l : AE F E) - 1) ↔ l ∈ part PI ⊤ (io a)
    rw [hat, fix_iff, ← coe_PI_io h, mem_part]
    exact ⟨fun e => ⟨trivial, Units.ext e⟩, fun e => congrArg Units.val e.2⟩
  rw [idAt, this, Subgroup.closure_eq]

theorem units_eq (v : Pl F) : {l : idAt E (evFin F v) | IsCompact (closure (Subgroup.zpowers l : Set (idAt E (evFin F v))))} =
    {l | l.1 ∈ (UI F E : Set (AE F E)ˣ)} := by
  have h := co_I (E := E) (io_idem (idem_idem v)) (inf_io rfl)
  rw [CO, ← idAt_eq (evFin F v) (idem_idem v) fun _ => at_fin_iff] at h
  refine Set.ext fun l => ⟨fun hl w => ?_, fun hl => h.1.of_isClosed_subset isClosed_closure (closure_minimal ?_ h.1.isClosed)⟩
  · obtain ⟨k, hk, hm⟩ := pow_mem_of_compact ((UI F E).subgroupOf _) h.2 hl fun n =>
      subset_closure (Subgroup.npow_mem_zpowers l n)
    have h1 : vw w (l.1 ^ k) = 1 := hm w
    rw [vw, Units.val_pow_eq_pow_val, map_pow, map_pow] at h1
    exact (pow_eq_one_iff_of_nonneg zero_le' hk.ne').1 h1
  · rintro _ ⟨n, rfl⟩
    exact (UI F E).zpow_mem hl n

theorem measEx_of (hS : StabEx) : MeasEx := by
  intro F E _ _ _ _ _ σ B n X r s hB hX K hK
  haveI := (ua_top (σ := σ) X.J).1
  haveI := (ua_top (σ := σ) X.J).2
  haveI := borelUA (σ := σ) X.J
  have hc := stab_compact hS hB hX hK
  have ei := kAt_eq K (evI F) real_idem fun _ => at_inf_iff
  have ef := fun v => kAt_eq K (evFin F v) (idem_idem v) fun _ => at_fin_iff
  have di := idAt_eq (E := E) (evI F) real_idem fun _ => at_inf_iff
  have df := fun v => idAt_eq (E := E) (evFin F v) (idem_idem v) fun _ => at_fin_iff
  have h1 : ∀ {a}, Gd a → ∀ S, S = part (PU σ X.J) K a → ∃ μ : Measure S, μ.IsHaarMeasure ∧ μ Set.univ = 1 := by
    rintro a ha S rfl
    have hp : Continuous (PU σ X.J a) :=
      ((unitInvariant_continuous ha.1).comp continuous_subtype_val).subtype_mk _
    have hclosed : IsClosed (part (PU σ X.J) K a : Set (UA σ X.J)) :=
      hc.isClosed.inter (isClosed_eq hp continuous_id)
    have : CompactSpace (part (PU σ X.J) K a) :=
      isCompact_iff_compactSpace.1 (hc.of_isClosed_subset hclosed fun _ h => h.1)
    exact exists_haar _ hclosed Set.univ trivial isCompact_univ isOpen_univ
  have h2 : ∀ S : Subgroup (AE F E)ˣ, ∀ P : Set S, (∃ μ : Measure S, μ.IsHaarMeasure ∧ μ P = 1) →
      ∃ μ : @Measure S (borel _), @Measure.IsHaarMeasure _ _ _ (borel _) μ ∧ μ P = 1 := fun S P h => by
    have : borel S = Subtype.instMeasurableSpace := (@BorelSpace.measurable_eq S _ Subtype.instMeasurableSpace (Subtype.borelSpace _)).symm
    rw [this]; exact h
  choose kf hkf using fun v => h1 (gd_idem v) _ (ef v)
  obtain ⟨ki, hki⟩ := h1 gd_real _ ei
  have h3 : ∀ v, ∃ μ : Measure (idAt E (evFin F v)), μ.IsHaarMeasure ∧ μ {l | l.1 ∈ (UI F E : Set (AE F E)ˣ)} = 1 := fun v => by
    have h := co_I (E := E) (io_idem (idem_idem v)) (inf_io rfl)
    have hcl := sysI.closed (io_idem (E := E) (idem_idem v))
    rw [CO, ← df v] at h
    rw [← df v] at hcl
    exact exists_haar _ hcl _ (UI F E).one_mem h.1 h.2
  choose xf hxf using fun v => h2 _ _ (h3 v)
  haveI : LocallyCompactSpace (idAt E (evI F)) := by
    have hcl := sysI.closed (io_idem (E := E) (real_idem (F := F)))
    rw [← di] at hcl; exact hcl.locallyCompactSpace
  letI : MeasurableSpace (idAt E (evI F)) := borel _
  haveI : BorelSpace (idAt E (evI F)) := ⟨rfl⟩
  exact ⟨⟨kf, xf, ki, Measure.haar⟩, hkf, fun v => ⟨(hxf v).1, by rw [units_eq]; exact (hxf v).2⟩, hki.1, inferInstance⟩

end PositivityTheory.ThKG.Loc.Cone

end
end

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKG.Fub
open GlobalTheory.Doubling hiding npow norm_npow npow_ne_zero

attribute [local instance] ae_ring ae_smul ae_t2 ae_lc ae_sc id_lc id_sc id_borel

theorem mem_part_iff {a : AE F E} (ha : a * a = a) (h0 : infTens F E a = 0) (l : (AE F E)ˣ) :
    l ∈ part PI ⊤ a ↔ infTens F E l = 1 ∧ ∀ w, cw w a = 0 → cw w (l : AE F E) = 1 := by
  refine ⟨fun h => ⟨inf_of_part ha h0 h, fun w hw => by rw [← show PI a l = l from h.2]; exact cw_PI_zero ha hw l⟩,
    fun h => ⟨trivial, Units.ext (ae_ext (show infTens F E (PI a l : AE F E) = infTens F E l by rw [hom_PI _ ha, h0, h.1]; simp) fun w => ?_)⟩⟩
  rcases cw_cases ha w with e | e
  · exact (cw_PI_zero ha e l).trans (h.2 w e).symm
  · exact cw_PI_one ha e l

theorem PI_mem {a : AE F E} (ha : a * a = a) (l : (AE F E)ˣ) : PI a l ∈ part PI ⊤ a :=
  ⟨trivial, by show PI a (PI a l) = PI a l; rw [unitInvariant_comp ha ha, ha]⟩

theorem PI_sum {ι : Type} [DecidableEq ι] (e : ι → AE F E) (he : ∀ i, e i * e i = e i) (ho : ∀ i j, i ≠ j → e i * e j = 0)
    (c : AE F E) (hc : c * c = c) (T : Finset ι) (hT : ∀ i ∈ T, e i * c = 0) (x : (AE F E)ˣ) :
    PI (∑ i ∈ T, e i + c) x = (∏ i ∈ T, PI (e i) x) * PI c x := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T hi ih =>
    have hT' : ∀ j ∈ T, e j * c = 0 := fun j hj => hT j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.prod_insert hi, add_assoc, mul_assoc, ← ih hT']
    refine unitInvariant_add (he i) (sysI.good_sum e he ho c hc T hT') ?_ x
    rw [mul_add, Finset.mul_sum, Finset.sum_eq_zero fun j hj => ho i j (fun e => hi (e ▸ hj)), hT i (Finset.mem_insert_self _ _),
      add_zero]

def wtH (ν : Chr F E) (z : ℕ) : (AE F E)ˣ →* ℂ where
  toFun := wt ν z
  map_one' := by simp [wt]
  map_mul' a b := by simp only [wt, map_mul, Circle.coe_mul, NNReal.coe_mul, Complex.ofReal_mul]; ring

theorem abs_UI {a : AE F E} (ha : a * a = a) (h0 : infTens F E a = 0) {l} (h : l ∈ part PI ⊤ a) (hu : l ∈ UI F E) : absE F E l = 1 :=
  one_of_compact (absE F E) continuous_absE (cpt_I ha h0) fun n => ⟨Subgroup.zpow_mem _ h n, Subgroup.zpow_mem _ hu n⟩

theorem cw_loc (u w : HeightOneSpectrum (𝓞 E)) (y : (w.adicCompletion E)ˣ) :
    cw u (locIdele F w y : AE F E) = Neutral.B1.finiteSingle E w y u := by
  rw [cw_def, finTens_locIdele]; rfl

theorem ew_zero {u w : HeightOneSpectrum (𝓞 E)} : cw u (ew F w) = 0 ↔ u ≠ w := by
  rw [cw_ew]; split_ifs with h <;> simp [h]

theorem loc_mem (w : HeightOneSpectrum (𝓞 E)) (y : (w.adicCompletion E)ˣ) : locIdele F w y ∈ part PI ⊤ (ew F w) :=
  (mem_part_iff (ew_idem w) (inf_ew w) _).2 ⟨infTens_locIdele w y, fun u hu => by rw [cw_loc, finSingle_ne (ew_zero.1 hu)]⟩

theorem nu_ew {ν : Chr F E} {w} (hν : UnrAt ν w) {l} (h : l ∈ part PI ⊤ (ew F w)) (hu : l ∈ UI F E) : ν l = 1 := by
  obtain ⟨h1, h2⟩ := (mem_part_iff (ew_idem w) (inf_ew w) _).1 h
  have e : l = locIdele F w (Units.map (cw w).toMonoidHom l) := Units.ext (ae_ext (h1.trans (infTens_locIdele _ _).symm) fun u => by
    rw [cw_loc]
    by_cases hu : u = w
    · subst hu; rw [finSingle_self]; rfl
    · rw [finSingle_ne hu, h2 u (ew_zero.2 hu)])
  have := hν (Units.map (cw w).toMonoidHom l) (hu w)
  rw [e]
  exact Circle.coe_eq_one.1 (congrArg Units.val this)


variable (F) in
def pw (w : HeightOneSpectrum (𝓞 E)) : (AE F E)ˣ := locIdele F w (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w))

theorem vw_pw (w : HeightOneSpectrum (𝓞 E)) : vw w (pw F w) = WithZero.exp (-1 : ℤ) := by
  rw [vw, pw, cw_loc, finSingle_self]; exact Formalism.L2.Host.unif_spec w

theorem abs_pw {B : Base F E} (hB : B.IsGood σ) (w : HeightOneSpectrum (𝓞 E)) :
    (absE F E (pw F w) : ℝ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)⁻¹ := by
  have hne : ∀ u, u ≠ w → cw u (pw F w : AE F E) = 1 := fun u hu => by rw [pw, cw_loc, finSingle_ne hu]
  have e : pw F w = ideleAt F E (w.under (𝓞 F)) (unitFin F E (w.under (𝓞 F)) (pw F w)) := by
    refine Units.ext (ae_ext ((infTens_locIdele _ _).trans (map_extUnit_zero (fstA F) _ _ (fun a => rfl) _).symm) fun u => ?_)
    by_cases hu : u.under (𝓞 F) = w.under (𝓞 F)
    · rw [cw_eq hu, cw_eq hu]
      exact congrArg _ (congrArg Units.val (unitFin_ideleAt_self _ (unitFin F E (w.under (𝓞 F)) (pw F w)))).symm
    · rw [hne u fun e => hu (e ▸ rfl), cw_eq rfl]
      rw [show compFin F E _ _ = 1 from congrArg Units.val (unitFin_ideleAt_ne hu _), map_one]
  have o1 : Formalism.UG.ordL (toCompl (rfl : w.under (𝓞 F) = _) (unitFin F E (w.under (𝓞 F)) (pw F w)).1) = 1 := by
    have h : Valued.v (toCompl (rfl : w.under (𝓞 F) = _) (unitFin F E (w.under (𝓞 F)) (pw F w)).1) = WithZero.exp (-1 : ℤ) := by
      rw [← vw_pw (F := F) w, vw, cw_eq rfl]; rfl
    rw [GlobalTheory.AbsInert.ordL_eq_neg_log (h ▸ WithZero.exp_ne_zero), h]; simp
  have hUn := hB.unram
  have hU : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 F)) :=
    GlobalTheory.LFun.isUnram_iff.2 fun w _ => Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
  rw [e, absE_ideleAt]
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt hU with hs | ⟨u, hi⟩
  · obtain ⟨w₁, w₂, hn, h1, h2⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    obtain ⟨w', hw', h'⟩ : ∃ w', w ≠ w' ∧ w'.under (𝓞 F) = w.under (𝓞 F) := by
      by_cases h : w = w₁
      exacts [⟨w₂, h ▸ hn, h2⟩, ⟨w₁, h, h1⟩]
    have o2 : Formalism.UG.ordL (toCompl h' (unitFin F E (w.under (𝓞 F)) (pw F w)).1) = 0 := by
      have h : toCompl h' (unitFin F E (w.under (𝓞 F)) (pw F w)).1 = 1 := (cw_eq h' _).symm.trans (hne w' hw'.symm)
      rw [h, GlobalTheory.AbsInert.ordL_eq_neg_log (by simp)]; simp
    rw [GlobalTheory.Doubling.AbsSplit.absEv_split F E σ hB.cm _ w rfl w' h' hw', o1, o2]
    simp [Formalism.UG.qV]
  · obtain rfl := (GlobalTheory.LFun.InertChart.under_eq_iff hi w).1 rfl
    rw [GlobalTheory.AbsInert.absEv_inert F E σ hB.cm _ w rfl hi, o1, GlobalTheory.LFun.InertChart.absNorm_eq hB.cm.2.2.1 hi]
    simp [Formalism.UG.qV]

theorem wt_pw {B : Base F E} (hB : B.IsGood σ) (ν : Chr F E) (z : ℕ) (w : HeightOneSpectrum (𝓞 E)) :
    wt ν z (pw F w) = (val ν w : ℂ) * npow w (-(z : ℂ)) := by
  rw [wt, abs_pw hB, npow, Complex.cpow_neg, Complex.cpow_natCast]
  push_cast
  rw [inv_pow]; rfl

def tw (ν : Chr F E) (z : ℕ) (m : ℤ) (w : HeightOneSpectrum (𝓞 E)) : ℂ :=
  ((val ν w : ℂ) * npow w (-(z : ℂ))) ^ m * (1 - (val ν w : ℂ) * npow w (-(z : ℂ)))⁻¹

theorem norm_t_lt (ν : Chr F E) {z : ℕ} (hz : 1 ≤ z) (w : HeightOneSpectrum (𝓞 E)) : ‖(val ν w : ℂ) * npow w (-(z : ℂ))‖ < 1 := by
  rw [norm_mul, norm_val, one_mul, norm_npow]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_absNorm w) (by simp; omega)

theorem tw_ne (ν : Chr F E) {z : ℕ} (hz : 1 ≤ z) (m : ℤ) (w : HeightOneSpectrum (𝓞 E)) : tw ν z m w ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (mul_ne_zero (Units.ne_zero _) (npow_ne_zero _ _))) (inv_ne_zero fun h => by
    have := norm_t_lt ν hz w
    rw [← sub_eq_zero.1 h] at this; simp at this)

open Classical in
theorem locW {B : Base F E} (hB : B.IsGood σ) {ν : Chr F E} {z : ℕ} (hz : 1 ≤ z) {w} (hν : UnrAt ν w) (m : ℤ)
    (γ : Measure (part (PI (F := F)) ⊤ (ew F w))) (hγ : γ.IsHaarMeasure ∧ γ {x | x.1 ∈ (UI F E : Set (AE F E)ˣ)} = 1) :
    Integrable (fun x : part PI ⊤ (ew F w) => (if vw w x.1 ≤ WithZero.exp (-m) then (1 : ℂ) else 0) * wt ν z x.1) γ ∧
      ∫ x : part PI ⊤ (ew F w), (if vw w x.1 ≤ WithZero.exp (-m) then (1 : ℂ) else 0) * wt ν z x.1 ∂γ = tw ν z m w := by
  haveI := hγ.1
  have hs : ∀ x : part (PI (F := F)) ⊤ (ew F w), -WithZero.log (vw w x.1) = 0 ↔ x.1 ∈ UI F E := fun x => by
    refine ⟨fun h u => ?_, fun h => by rw [h w]; simp⟩
    by_cases hu : u = w
    · subst hu; rw [← WithZero.exp_log (vw_ne u x.1), neg_eq_zero.1 h]; rfl
    · rw [vw, ((mem_part_iff (ew_idem w) (inf_ew w) _).1 x.2).2 u (ew_zero.2 hu), map_one]
  have hs' : {x : part (PI (F := F)) ⊤ (ew F w) | -WithZero.log (vw w x.1) = 0} = {x | x.1 ∈ (UI F E : Set (AE F E)ˣ)} := Set.ext hs
  have := tate γ (fun x => -WithZero.log (vw w x.1)) (fun x y => by
      rw [Subgroup.coe_mul, vw_mul, WithZero.log_mul (vw_ne _ _) (vw_ne _ _)]; ring)
    (by rw [hs']; exact isOpen_UI.preimage continuous_subtype_val) (by rw [hs']; exact hγ.2) ⟨pw F w, loc_mem w _⟩
    (by show -WithZero.log (vw w (pw F w)) = 1; rw [vw_pw]; simp) ((wtH ν z).comp (Subgroup.subtype _))
    (fun x hx => by
      show wt ν z x.1 = 1
      rw [wt, nu_ew hν x.2 ((hs x).1 hx), abs_UI (ew_idem w) (inf_ew w) x.2 ((hs x).1 hx)]; simp)
    (by show ‖wt ν z (pw F w)‖ < 1; rw [wt_pw hB]; exact norm_t_lt ν hz w) m
  have e : ∀ x : part (PI (F := F)) ⊤ (ew F w), m ≤ -WithZero.log (vw w x.1) ↔ vw w x.1 ≤ WithZero.exp (-m) := fun x => by
    rw [← WithZero.log_le_iff_le_exp (vw_ne _ _)]; omega
  simp only [e] at this
  refine ⟨this.1, this.2.trans ?_⟩
  show wt ν z (pw F w) ^ m * (1 - wt ν z (pw F w))⁻¹ = _
  rw [wt_pw hB, tw]

theorem inf_sum (W : Finset (HeightOneSpectrum (𝓞 E))) {c : AE F E} (h0 : infTens F E c = 0) :
    infTens F E (∑ w ∈ W, ew F w + c) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), h0, add_zero, map_sum, Finset.sum_eq_zero fun w _ => inf_ew w]

open Classical in
theorem prodW {B : Base F E} (hB : B.IsGood σ) {ν : Chr F E} {z : ℕ} (hz : 1 ≤ z) (W : Finset (HeightOneSpectrum (𝓞 E)))
    (hν : ∀ w ∈ W, UnrAt ν w) (m : HeightOneSpectrum (𝓞 E) → ℤ) {c : AE F E} (hc : c * c = c) (h0 : infTens F E c = 0)
    (hW : ∀ w ∈ W, ew F w * c = 0) (hνc : ∀ l ∈ part PI ⊤ c, l ∈ UI F E → ν l = 1) (b : AE F E) (hb : b = ∑ w ∈ W, ew F w + c)
    (μ : Measure (part (PI (F := F)) ⊤ b)) (hμ : μ.IsHaarMeasure ∧ μ {x | x.1 ∈ (UI F E : Set (AE F E)ˣ)} = 1) :
    Integrable (fun x : part PI ⊤ b => (if (∀ w ∈ W, vw w x.1 ≤ WithZero.exp (-m w)) ∧ PI c x.1 ∈ UI F E then (1 : ℂ) else 0) *
      wt ν z x.1) μ ∧
    ∫ x : part PI ⊤ b, (if (∀ w ∈ W, vw w x.1 ≤ WithZero.exp (-m w)) ∧ PI c x.1 ∈ UI F E then (1 : ℂ) else 0) * wt ν z x.1 ∂μ =
      ∏ w ∈ W, tw ν z (m w) w := by
  have hex := fun {a : AE F E} (ha : a * a = a) (h0 : infTens F E a = 0) =>
    exists_haar _ (sysI.closed ha) _ (UI F E).one_mem (co_I ha h0).1 (co_I ha h0).2
  choose γ hγ using fun w => hex (ew_idem w) (inf_ew (F := F) w)
  obtain ⟨β, hβ⟩ := hex hc h0
  have mU : MeasurableSet {x : part (PI (F := F)) ⊤ c | x.1 ∈ (UI F E : Set (AE F E)ˣ)} :=
    (isOpen_UI.preimage continuous_subtype_val).measurableSet
  have eg : (fun x : part (PI (F := F)) ⊤ c => (if x.1 ∈ UI F E then (1 : ℂ) else 0)) =
      Set.indicator {x | x.1 ∈ (UI F E : Set (AE F E)ˣ)} fun _ => 1 := funext fun x => by simp [Set.indicator_apply]
  obtain ⟨p1, p2⟩ := sysI.prod (ew F) ew_idem (fun _ _ => ew_orth) c hc γ hγ β hβ W hW
    (fun T' h => co_I (sysI.good_sum _ ew_idem (fun _ _ => ew_orth) c hc T' fun w hw => hW w (h hw)) (inf_sum T' h0)) b hb μ hμ
    (fun w x => (if vw w x ≤ WithZero.exp (-m w) then (1 : ℂ) else 0) * wt ν z x) (fun x => if x ∈ UI F E then 1 else 0)
    (fun w hw => (locW hB hz (hν w hw) (m w) _ (hγ w)).1)
    (by rw [eg, integrable_indicator_iff mU]; exact integrableOn_const (by rw [hβ.2]; simp))
  rw [Finset.prod_congr rfl fun w hw => (locW hB hz (hν w hw) (m w) _ (hγ w)).2, eg, integral_indicator mU, setIntegral_const,
    Measure.real, hβ.2] at p2
  have e : (fun x : part (PI (F := F)) ⊤ b => (if (∀ w ∈ W, vw w x.1 ≤ WithZero.exp (-m w)) ∧ PI c x.1 ∈ UI F E then (1 : ℂ) else 0) *
      wt ν z x.1) = fun x : part PI ⊤ b => (∏ w ∈ W, (if vw w (PI (ew F w) x.1) ≤ WithZero.exp (-m w) then (1 : ℂ) else 0) *
        wt ν z (PI (ew F w) x.1)) * (if PI c x.1 ∈ UI F E then 1 else 0) := funext fun x => by
    have hv : ∀ w, vw w (PI (ew F w) x.1) = vw w x.1 := fun w => by
      rw [vw, cw_PI_one (ew_idem w) (by rw [cw_ew, if_pos rfl])]; rfl
    by_cases hu : PI c x.1 ∈ UI F E
    · have hx : x.1 = (∏ w ∈ W, PI (ew F w) x.1) * PI c x.1 := by
        rw [← PI_sum _ ew_idem (fun _ _ => ew_orth) c hc W hW, ← hb]; exact x.2.2.symm
      have hw : wt ν z x.1 = ∏ w ∈ W, wt ν z (PI (ew F w) x.1) := by
        have := congrArg (wtH ν z) hx
        rw [map_mul, map_prod] at this
        refine this.trans ?_
        show _ * wt ν z _ = _
        rw [wt, hνc _ (PI_mem hc _) hu, abs_UI hc h0 (PI_mem hc _) hu]
        simp [wtH]
      simp only [hv, hu, and_true, if_true, mul_one, Finset.prod_mul_distrib, Finset.prod_boole, hw]
    · simp [hu]
  rw [e]
  exact ⟨p1, p2.trans (by simp)⟩


open Classical in
def ab (T : Finset (Pl F)) : Finset (HeightOneSpectrum (𝓞 E)) := T.biUnion (Formalism.L2.Host.aboveF (L := E) F)

theorem mem_ab {T : Finset (Pl F)} {w : HeightOneSpectrum (𝓞 E)} : w ∈ ab T ↔ w.under (𝓞 F) ∈ T := by
  simp [ab, mem_aboveF]

open Classical in
theorem rest_split {T T' : Finset (Pl F)} (h : T ⊆ T') :
    (io (rest T) : AE F E) = ∑ w ∈ ab (T' \ T), ew F w + io (rest T') := by
  refine ae_ext (by rw [inf_io (rest_fst _), inf_sum _ (inf_io (rest_fst _))]) fun u => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum, cw_rest, cw_rest]
  simp only [cw_ew, Finset.sum_ite_eq, mem_ab, Finset.mem_sdiff]
  by_cases h1 : u.under (𝓞 F) ∈ T
  · simp [h1, h h1]
  · by_cases h2 : u.under (𝓞 F) ∈ T' <;> simp [h1, h2]

theorem ew_rest {T : Finset (Pl F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) ∈ T) : ew F w * io (rest T) = 0 :=
  ae_ext (by rw [map_mul, inf_ew, zero_mul, map_zero]) fun u => by
    rw [map_mul, cw_ew, cw_rest, map_zero]
    split_ifs with h1 h2
    · simp
    · exact absurd (h1 ▸ h) h2
    all_goals simp

theorem rest_zero {T : Finset (Pl F)} {w : HeightOneSpectrum (𝓞 E)} : cw w (io (rest T) : AE F E) = 0 ↔ w.under (𝓞 F) ∈ T := by
  rw [cw_rest]; split_ifs with h <;> simp [h]

theorem nu_rest {ν : Chr F E} (hc : Continuous ν) {T : Finset (Pl F)} (hν : UnrOff ν (T : Set (Pl F))) {l}
    (h : l ∈ part PI ⊤ (io (rest T))) (hu : l ∈ UI F E) : ν l = 1 := by
  classical
  have hi := fun T : Finset (Pl F) => io_idem (E := E) (rest_idem T)
  have h0 := fun T : Finset (Pl F) => inf_io (E := E) (rest_fst T)
  have mono : ∀ {A A' : Finset (Pl F)}, A ⊆ A' → ((part PI ⊤ (io (rest A')) : Subgroup (AE F E)ˣ) : Set (AE F E)ˣ) ∩ UI F E ⊆
      ((part PI ⊤ (io (rest A)) : Subgroup (AE F E)ˣ) : Set (AE F E)ˣ) ∩ UI F E := by
    intro A A' hA x hx
    have h1 := (mem_part_iff (hi A') (h0 A') x).1 hx.1
    exact ⟨(mem_part_iff (hi A) (h0 A) x).2 ⟨h1.1, fun w hw => h1.2 w (rest_zero.2 (hA (rest_zero.1 hw)))⟩, hx.2⟩
  obtain ⟨T₀, hT₀⟩ := exists_subset_nhds_of_isCompact'
    (V := fun A : Finset (Pl F) => ((part PI ⊤ (io (rest A)) : Subgroup (AE F E)ˣ) : Set (AE F E)ˣ) ∩ UI F E)
    (fun A A' => ⟨A ∪ A', mono Finset.subset_union_left, mono Finset.subset_union_right⟩) (fun A => cpt_I (hi A) (h0 A))
    (fun A => (cpt_I (hi A) (h0 A)).isClosed) (U := {x | ‖(ν x : ℂ) - 1‖ < 1}) <| mem_nhdsSet_iff_forall.mpr fun x hx => by
      have hx' := Set.mem_iInter.1 hx
      obtain rfl : x = 1 := Units.ext (ae_ext (by rw [((mem_part_iff (hi ∅) (h0 ∅) x).1 (hx' ∅).1).1, Units.val_one, map_one])
        fun w => by
          rw [((mem_part_iff (hi _) (h0 _) x).1 (hx' {w.under (𝓞 F)}).1).2 w (rest_zero.2 (Finset.mem_singleton_self _)),
            Units.val_one, map_one])
      exact (isOpen_lt ((continuous_subtype_val.comp hc).sub continuous_const).norm continuous_const).mem_nhds
        (show ‖((ν 1 : Circle) : ℂ) - 1‖ < 1 by rw [map_one]; simp)
  have hx : l = (∏ w ∈ ab ((T ∪ T₀) \ T), PI (ew F w) l) * PI (io (rest (T ∪ T₀))) l := by
    rw [← PI_sum _ ew_idem (fun _ _ => ew_orth) _ (hi _) _ fun w hw => ew_rest (Finset.mem_sdiff.1 (mem_ab.1 hw)).1,
      ← rest_split Finset.subset_union_left]
    exact h.2.symm
  rw [hx, map_mul, map_prod, Finset.prod_eq_one fun w hw => nu_ew (hν w (Finset.mem_sdiff.1 (mem_ab.1 hw)).2) (PI_mem (ew_idem w) _)
    (sysI.pU _ (ew_idem w) _ hu), one_mul]
  refine circle_one fun n => ?_
  rw [← map_pow]
  exact hT₀ (mono Finset.subset_union_right ⟨Subgroup.pow_mem _ (PI_mem (hi _) _) n, Subgroup.pow_mem _ (sysI.pU _ (hi _) _ hu) n⟩)

end PositivityTheory.ThKG.Loc.Cone

end
