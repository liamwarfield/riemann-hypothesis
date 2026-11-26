module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutCuspOfMemCusp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open Formalism.IndefR.Mult GlobalTheory.Grid

namespace GlobalTheory.FinLift

variable {D : D7}

theorem autCusp_of_mem_cusp (N : Node D) (θ : InfFam D) {Φ : N.Maps} (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) :
    IsAutFun N.V (Φ v) ∧ IsCuspFun N.V (Φ v) := by
  obtain ⟨T, hT, rfl⟩ := Submodule.mem_map.1 hΦ
  replace hT := (GlobalTheory.MultMem.mem_mult_iff D θ N.V N.S N.M ∅ 1 T).1 hT
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
    exact ⟨(GlobalTheory.MultMem.isAutFunSm_smul r (hT.aut f)).toIsAutFun, GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp f)⟩
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact ⟨GlobalTheory.RowLift.isAutFun_add hx.1 hy.1, GlobalTheory.MultMem.isCuspFun_add hx.1 hy.1 hx.2 hy.2⟩

theorem autCusp_sum (V : HSp D) {ι : Type} (s : Finset ι) (φ : ι → GA D V → ℂ) (h : ∀ i ∈ s, IsAutFun V (φ i) ∧ IsCuspFun V (φ i)) :
    IsAutFun V (∑ i ∈ s, φ i) ∧ IsCuspFun V (∑ i ∈ s, φ i) :=
  Finset.sum_induction φ (fun ψ => IsAutFun V ψ ∧ IsCuspFun V ψ)
    (fun a b ha hb => ⟨GlobalTheory.RowLift.isAutFun_add ha.1 hb.1, GlobalTheory.MultMem.isCuspFun_add ha.1 hb.1 ha.2 hb.2⟩)
    ⟨GlobalTheory.RowLift.isAutFun_zero V, fun r C hC μ 𝓕 hμ h𝓕 g => by simp⟩ h

end GlobalTheory.FinLift

namespace GlobalTheory.FinLift

variable {D : D7}

theorem thetaKO_sum {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T)
    {ι : Type} (s : Finset ι) (x : ι → WO S T → ℂ) : thetaKO om g h (∑ i ∈ s, x i) = ∑ i ∈ s, thetaKO om g h (x i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [thetaKO, map_sum, Finset.sum_apply]

theorem lift_finSum {θ : InfFam D} {A B : Node D} {P : Type} {m : A.MeasDat} {n : ℕ}
    (K : Fin n → P → GA D B.V → GA D A.V → ℂ) (It : P → SmT A.M → SmT B.M)
    (hK : ∀ l, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsMult θ m (K l) It) (ps : Fin n → P) {n' : ℕ} (Fs : Fin n' → A.Maps)
    (vs : Fin n' → SmT A.M) (hF : ∀ k, Fs k ∈ A.Cusp θ) :
    (∀ h, IntegrableOn (fun g => (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g) m.fd m.ν) ∧
    IsAutFun B.V (fun h => ∫ g in m.fd, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g ∂m.ν) ∧
    IsCuspFun B.V (fun h => ∫ g in m.fd, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g ∂m.ν) := by
  choose F' h using fun l k => hK l (Fs k) (hF k)
  have hF' := fun l k => (h l k).1
  have hI := fun l k => (h l k).2
  have hsplit : ∀ h g, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g = ∑ l, ∑ k, K l (ps l) h g * Fs k (vs k) g :=
    fun h g => by rw [Finset.sum_mul_sum]
  have hint : ∀ h, IntegrableOn (fun g => (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g) m.fd m.ν := fun h => by
    simp_rw [hsplit]
    exact integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun k _ => (hI l k (ps l) (vs k) h).1
  have heq : (fun h => ∫ g in m.fd, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g ∂m.ν) =
      ∑ l, ∑ k, F' l k (It (ps l) (vs k)) := by
    funext h
    simp_rw [hsplit]
    rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun k _ => (hI l k (ps l) (vs k) h).1]
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_finsetSum _ fun k _ => (hI l k (ps l) (vs k) h).1]
    exact Finset.sum_congr rfl fun k _ => (hI l k (ps l) (vs k) h).2
  rw [heq]
  exact ⟨hint, autCusp_sum B.V _ _ fun l _ => by
    simpa only [Finset.sum_apply] using autCusp_sum B.V _ _ fun k _ => autCusp_of_mem_cusp B θ (hF' l k) _⟩

end GlobalTheory.FinLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridDownArrowThetaFunctionFockDenseOfLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridDownArrowThetaFunctionFockDenseOfLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ArrowFockDense

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.ChainFr GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.FockDensity

theorem dense_level : ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ (t : T) i j, i ≤ D.R.m → j < D.R.m → ∀ (U : AddSubgroup (WO (G.V i j).V (G.V i (j + 1)).V)), IsOpen (U : Set (WO (G.V i j).V (G.V i (j + 1)).V)) → ∀ Φ ∈ GlobalTheory.Size.thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U, ∀ (μ : Measure (WO (G.V i j).V (G.V i (j + 1)).V)) (𝓕 : Set (WO (G.V i j).V (G.V i (j + 1)).V)), IsCovolOne (ratL (G.V i (j + 1)).V (G.V i j).V) μ 𝓕 → ∀ (d : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧ (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) ∈ GlobalTheory.Size.thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U ∧ GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d ((∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) - Φ) < ENNReal.ofReal ε := by
  intro D G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj U hU Φ hΦ μ 𝓕 hm d ε hε
  have hω : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hG.arrows.th t i j hi hj).weil
  have hψ : IsStdChar D R.ψ (-1) := hω.std
  have hθ : IsInfFam R.θ := hRB.inf
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D (G.V i (j + 1)).V (G.V i j).V
  haveI : BorelSpace (WO (G.V i j).V (G.V i (j + 1)).V) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, hm.2.2]; exact ENNReal.one_lt_top⟩
  have e0 : coeL R.ψ _ _ (toB hψ Φ hΦ.1) = Φ := coe_toB hψ Φ hΦ.1
  have hF : toB hψ Φ hΦ.1 ∈ (GlobalTheory.Size.thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U).comap (coeL R.ψ _ _) := by
    rw [Submodule.mem_comap, e0]
    exact hΦ
  obtain ⟨g, h1, h2, h3⟩ := dense_vec h hψ (Fr.ofModel (G.V i j).M) (Fr.ofModel (G.V i (j + 1)).M) hU
    (toL2 _ _ (μ.restrict 𝓕))
    (fun v F => by
      rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2]
      exact lintegral_rhoB hψ μ 𝓕 hm.1 hm.2.1 _ F)
    (fun a : D.what₂.Tau × Fin (G.V i (j + 1)).V.rank × Fin (G.V i j).V.rank × Bool =>
      atPl a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))) d hF
    (ENNReal.ofReal_pos.2 hε)
  have e1 : ∀ F : BB R.ψ (G.V i j).V (G.V i (j + 1)).V,
      l2O μ 𝓕 (coeL R.ψ _ _ F) = ‖toL2 _ _ (μ.restrict 𝓕) F‖ₑ := fun F =>
    (eLpNorm_congr_ae (BoundedContinuousFunction.coeFn_toLp 2 (μ.restrict 𝓕) ℂ F.1)).symm.trans (Lp.enorm_def _).symm
  have e2 : Φ - coeL R.ψ _ _ g = coeL R.ψ _ _ (toB hψ Φ hΦ.1 - g) := by rw [LinearMap.map_sub, e0]
  have hS : sobO R.ψ R.θ μ 𝓕 d (Φ - coeL R.ψ _ _ g) < ENNReal.ofReal ε := by
    refine lt_of_eq_of_lt ?_ h3
    simp only [sobO, wordSum, e2, coe_word h hψ hU _ (sub_mem hF h2), e1]

  obtain ⟨n, c, gs, hgs⟩ := Submodule.mem_span_set'.1 (Submodule.mem_comap.1 h1)
  choose f₀ P hv hl hP using fun l => (gs l).2
  refine ⟨n, f₀, fun l => c l • P l, fun l => hv l, ?_, ?_⟩
  · have e3 : (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f₀ l) (c l • P l)) = coeL R.ψ _ _ g := by
      rw [← hgs]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hP l, map_smul]
      rfl
    rw [e3]
    exact h2
  · have e3 : (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f₀ l) (c l • P l)) - Φ =
        (-1 : ℂ) • (Φ - coeL R.ψ _ _ g) := by
      rw [← hgs, neg_one_smul, neg_sub]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hP l, map_smul]
      rfl
    rw [e3, sobO_smul, enorm_neg, enorm_one, one_mul]
    exact hS

end GlobalTheory.ArrowFockDense
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridDownArrowThetaFunctionFockDenseOfLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridDownArrow_thetaFunction_fock_dense_of_level : ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ (t : T) i j, i ≤ D.R.m → j < D.R.m → ∀ (U : AddSubgroup (WO (G.V i j).V (G.V i (j + 1)).V)), IsOpen (U : Set (WO (G.V i j).V (G.V i (j + 1)).V)) → ∀ Φ ∈ GlobalTheory.Size.thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U, ∀ (μ : Measure (WO (G.V i j).V (G.V i (j + 1)).V)) (𝓕 : Set (WO (G.V i j).V (G.V i (j + 1)).V)), IsCovolOne (ratL (G.V i (j + 1)).V (G.V i j).V) μ 𝓕 → ∀ (d : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧ (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) ∈ GlobalTheory.Size.thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U ∧ GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d ((∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) - Φ) < ENNReal.ofReal ε := by
  first | exact @GlobalTheory.ArrowFockDense.dense_level | exact GlobalTheory.ArrowFockDense.dense_level | (intros; apply GlobalTheory.ArrowFockDense.dense_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharTrivialOnIdempotentIntegralUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharTrivialOnIdempotentIntegralUnits
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChrOff

theorem idem_apply_eq_one {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (a : FiniteAdeleRing (𝓞 E) E) (ha : a * a = a)
    (h : ∀ x ∈ P.asIdeal, x ≠ 0 →
      ¬ ∀ Q, Valued.v ((a * algebraMap E (FiniteAdeleRing (𝓞 E) E) ((x : E)⁻¹)) Q) ≤ 1) : a P = 1 := by
  have h01 : ∀ Q, a Q ≠ 0 → a Q = 1 := fun Q hQ =>
    mul_left_cancel₀ hQ (by rw [← GlobalTheory.PlaceIdem.mul_ap, ha, mul_one])
  refine h01 P fun h0 => ?_
  obtain ⟨n, hn, x, hx⟩ := GlobalTheory.IdemRes.exists_pow_eq_span P.asIdeal P.ne_bot
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl] at hx
    exact P.ne_bot (pow_eq_zero_iff hn.ne' |>.1 hx)
  refine h x (Ideal.pow_le_self hn.ne' (hx ▸ Ideal.mem_span_singleton_self x)) hx0 fun Q => ?_
  rw [GlobalTheory.PlaceIdem.mul_ap]
  by_cases hQ : a Q = 0
  · rw [hQ, zero_mul, map_zero]; exact zero_le
  · rw [h01 Q hQ, one_mul, GlobalTheory.PlaceIdem.val_inv_le_one Q hx0]
    intro hxQ
    have := Q.isPrime
    have h1 : P.asIdeal ^ n ≤ Q.asIdeal := by rw [hx]; exact (Ideal.span_singleton_le_iff_mem _).2 hxQ
    have h2 : P.asIdeal ≤ Q.asIdeal := Ideal.IsPrime.le_of_pow_le h1
    have h3 : P = Q := HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h2)
    exact hQ (h3 ▸ h0)

variable {D : D7}

theorem exists_conj_mem {P P' : Pl D.host.E} (h : Formalism.IndefR.Lev.IsConjPl P P') {x : 𝓞 D.host.E}
    (hx : x ∈ P'.asIdeal) : ∃ y ∈ P.asIdeal, D.sp.cm.sig (y : D.host.E) = (x : D.host.E) := by
  let s : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (D.sp.cm.sig : D.host.E →+* D.host.E)
  have hs : ∀ y, (s y : D.host.E) = star (y : D.host.E) := fun _ => rfl
  have hle : P.asIdeal ≤ P'.asIdeal.comap s := fun c hc => by
    obtain ⟨c', hc', e⟩ := h c hc
    have : s c = c' := RingOfIntegers.ext (by rw [hs, e])
    rw [Ideal.mem_comap, this]; exact hc'
  have he := P.isMaximal.eq_of_le (Ideal.comap_ne_top s P'.isPrime.ne_top) hle
  have hss : s (s x) = x := RingOfIntegers.ext (by rw [hs, hs, star_star])
  refine ⟨s x, ?_, congrArg Subtype.val hss⟩
  rw [he, Ideal.mem_comap, hss]; exact hx

section
variable (ι : (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
  (h1 : ∀ x : D.host.E, ι ((1 : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x) =
    algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x)
  (h2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1)
include h1 h2

theorem comp_eq_one {f : AE D} (hf : f * f = f) (P : Pl D.host.E)
    (h : ∀ x ∈ P.asIdeal, x ≠ 0 → finPart D (f * incA D ((x : D.host.E)⁻¹)) ∉ intAE D) :
    ι (finPart D f) P = 1 := by
  refine idem_apply_eq_one P _ (by rw [← map_mul, ← RingHom.map_mul, hf]) fun x hx hx0 hc => h x hx hx0 ?_
  have e : finPart D (incA D ((x : D.host.E)⁻¹)) = (1 : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((x : D.host.E)⁻¹) := rfl
  rw [h2, RingHom.map_mul, map_mul, e, h1]
  exact hc

theorem comp_idem {f : AE D} {P : Pl D.host.E} (hf : Formalism.L2.NTheta.IsIdemAt f P) : ι (finPart D f) P = 1 :=
  comp_eq_one ι h1 h2 hf.1.1 P fun x hx hx0 => (hf.2 x hx0).1 hx

theorem comp_conj_idem {f : AE D} {P P' : Pl D.host.E} (hf : Formalism.L2.NTheta.IsIdemAt f P)
    (hc : Formalism.IndefR.Lev.IsConjPl P P') : ι (finPart D (cA D f)) P' = 1 := by
  refine comp_eq_one ι h1 h2 (by rw [← RingHom.map_mul, hf.1.1]) P' fun x hx hx0 hi => ?_
  obtain ⟨y, hy, hyx⟩ := exists_conj_mem hc hx
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hx0 (RingOfIntegers.ext (hyx.symm.trans (map_zero _)))
  refine (hf.2 y hy0).1 hy ?_
  have e : cA D (incA D ((y : D.host.E)⁻¹)) = incA D ((x : D.host.E)⁻¹) := by
    rw [← hyx, ← map_inv₀ D.sp.cm.sig]; rfl
  rw [← e, ← RingHom.map_mul, GlobalTheory.PlaceIdem.finPart_cA] at hi
  have := GlobalTheory.PlaceIdem.sig_mem D hi
  rwa [GlobalTheory.PlaceIdem.sig_sig] at this

end

theorem exists_idem_mul {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    ∃ f : AE D, Formalism.L2.NTheta.IsIdemAt f PP ∧ f * (e + cA D e) = f ∧ cA D f * (e + cA D e) = cA D f := by
  obtain ⟨⟨es, h1, h2⟩, h3⟩ := he
  have h4 : es PP * e = es PP := by
    rw [h2]
    refine GlobalTheory.PlaceModelSum.mul_sum_orth (fun i hi => (h1 i hi).1) (fun i hi j hj hij => ?_) hPP
    refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 i hi).1 (h1 j hj).1).resolve_left fun h => hij ?_
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
    · rw [(h1 i hi).2 x hx, (h1 j hj).2 x hx, h]
  have h5 : es PP * (e + cA D e) = es PP := by
    rw [mul_add, h4, ← h4, mul_assoc, h3, mul_zero, add_zero]
  refine ⟨es PP, h1 PP hPP, h5, ?_⟩
  have h6 := congrArg (cA D) h5
  rwa [RingHom.map_mul, RingHom.map_add, cA_cA, add_comm] at h6

theorem unrOff_of_unrAt : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (P : Finset (Pl D.host.E)) (e : AE D), ChrEq c χ → IsIdemSum e P → (∀ PP', PP' ∉ P → (∀ PP ∈ P, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → χ.UnrAt PP') → UnrOff (e + cA D e) c := by
  intro D c χ P₀ e hc he hu x hx1 hx2 hx3 hb
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  have hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    intro P
    have a := (h2 _).1 hx2 P
    have b := (h2 _).1 hx3 P
    have e : ι (finPart D (x : AE D)) * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := by
      rw [← map_mul]
      have : ι (finPart D (x : AE D)) P * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P = 1 :=
        congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) e
      rw [this, map_one]
    refine le_antisymm a ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e'.symm
      _ ≤ Valued.v (ι (finPart D (x : AE D)) P) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _
  have hone : ∀ (f : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)), f * (e + cA D e) = f → ι (finPart D f) P = 1 →
      ι (finPart D (x : AE D)) P = 1 := by
    intro f P hf hP
    have e1 : f * (x : AE D) = f := by rw [← hf, mul_assoc, hb]
    have e2 : ι (finPart D f) * ι (finPart D (x : AE D)) = ι (finPart D f) := by
      rw [← map_mul, ← RingHom.map_mul, e1]
    have e3 : ι (finPart D f) P * ι (finPart D (x : AE D)) P = ι (finPart D f) P :=
      congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) e2
    rwa [hP, one_mul] at e3
  have hunr : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ι (finPart D (x : AE D)) P ≠ 1 → χ.UnrAt P := by
    intro P hP
    refine hu P (fun hm => hP ?_) fun PP hm hcj => hP ?_
    · obtain ⟨f, f1, f2, -⟩ := exists_idem_mul he hm
      exact hone f P f2 (comp_idem ι h1 h2 f1)
    · obtain ⟨f, f1, -, f3⟩ := exists_idem_mul he hm
      exact hone _ P f3 (comp_conj_idem ι h1 h2 f1 hcj)
  have key := hprod x hx1 S (fun P => if ι (finPart D (x : AE D)) P = 1 then 1 else k P) (fun P hP => by
    by_cases h : ι (finPart D (x : AE D)) P = 1
    · rw [if_pos h, h, Units.val_one, map_one, map_one, map_one, sub_self, map_zero]
      exact ⟨rfl, zero_le⟩
    · rw [if_neg h]
      exact ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Subtype.ext
  refine key.trans (Finset.prod_eq_one fun P hP => ?_)
  by_cases h : ι (finPart D (x : AE D)) P = 1
  · rw [if_pos h, map_one, Units.val_one]
  · rw [if_neg h]
    have a' : Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) := (hS P hP).1
    rw [hv P] at a'
    have hun : Formalism.L2.Host.IsUnitAt P (Formalism.L2.Host.atFin P (k P)) := by
      show Valued.v (((k P : D.host.E)) : P.adicCompletion D.host.E) = _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← a']
    show ((χ.loc P (Formalism.L2.Host.atFin P (k P)) : ℂˣ) : ℂ) = 1
    rw [hunr P h _ hun, Units.val_one]

end GlobalTheory.ChrOff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharTrivialOnIdempotentIntegralUnitsStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_trivial_on_idempotentIntegralUnits : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (P : Finset (Pl D.host.E)) (e : AE D), ChrEq c χ → IsIdemSum e P → (∀ PP', PP' ∉ P → (∀ PP ∈ P, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → χ.UnrAt PP') → UnrOff (e + cA D e) c := by
  first | exact @GlobalTheory.ChrOff.unrOff_of_unrAt | exact GlobalTheory.ChrOff.unrOff_of_unrAt | (intros; apply GlobalTheory.ChrOff.unrOff_of_unrAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjThetaKOMulCuspIntegrableOnFst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ColConv

open GlobalTheory.Grid

theorem measDat_haar_fd {D : D7} {N : Node D} {m : N.MeasDat} {df : Prop} {K : Subgroup (GL (Fin N.V.rank) (Lev.EAf D))}
    (h : m.Is df K) : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν := by
  by_cases hd : df
  · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
  · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {θ : InfFam D} {u : WO S T → ℂ}

theorem thetaKO_mul_cusp_integrableOn_fst (hP : GlobalTheory.Published.CuspRapidDecay) (hω : IsWeilDatumO ψ S T χS χT om)
    (hθ : IsInfFam θ) {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν) (hu : IsThetaFunO ψ S T u) {y : GA D S → ℂ} (hy : IsAutFunSm θ S y)
    (hc : IsCuspFun S y) (x : GA D T) : IntegrableOn (fun g => thetaKO om g x u * y g) 𝓕 ν := by
  have : BorelSpace (GA D S) := ⟨rfl⟩
  exact (GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hy hc).integrableOn_modGrowth_mul hν h𝓕
    (GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_modGrowth_fst hθ hω hu x)
    (GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hω hu x)
    (GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_continuous_fst hω hu x).measurable.aestronglyMeasurable

theorem measX_haar_fd {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GridPre R}
    (hG : G.Is) (j : ℕ) (hj : j ≤ D.R.m) :
    (G.measX j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.Xp j).V) (G.measX j).fd (G.measX j).ν := by
  cases j with
  | zero => exact measDat_haar_fd (hG.meas.P D.R.m le_rfl)
  | succ j => exact measDat_haar_fd (hG.meas.X j hj)

end GlobalTheory.ColConv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOneParameterUnitaryCoordinateAction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOneParameterUnitaryCoordinateAction
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

namespace GlobalTheory.ArchLine

theorem continuous_archAct_line : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W), ∀ γ ∈ Lines σ W,
    ∀ v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
      Continuous fun t : ℝ => archAct M (γ (Multiplicative.ofAdd t)) v := by
  intro F E _ _ _ _ _ σ n d X W M γ hγ v
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have hγc : Continuous fun t : ℝ => γ (Multiplicative.ofAdd t) := hγ.1.comp continuous_ofAdd
  have hm : Continuous fun t : ℝ => (mat (γ (Multiplicative.ofAdd t)))ᵀ :=
    ((Units.continuous_val.comp continuous_subtype_val).comp hγc).matrix_transpose
  have he : Continuous M.co.e := IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hev : Continuous (evI F) := by
    change Continuous fun a : AF F => InfiniteAdeleRing.ringEquiv_mixedSpace F a.1
    refine Continuous.comp ?_ continuous_fst
    change Continuous fun x : InfiniteAdeleRing F =>
      ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
       (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
  have hl : Continuous (locV : (Fin n × Fin d → AF F) → _) := continuous_pi fun i => hev.comp (continuous_apply i)
  show Continuous fun t : ℝ =>
    (locV (M.co.e (mat (1 : UA σ X.J) * M.co.e.symm (liftV v.1, liftV v.2) * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1,
     locV (M.co.e (mat (1 : UA σ X.J) * M.co.e.symm (liftV v.1, liftV v.2) * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2)
  exact ((hl.comp continuous_fst).prodMk (hl.comp continuous_snd)).comp
    (he.comp (continuous_const.matrix_mul hm))

end GlobalTheory.ArchLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOneParameterUnitaryCoordinateActionStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_oneParameter_unitary_coordinate_action : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W), ∀ γ ∈ Lines σ W,
    ∀ v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
      Continuous fun t : ℝ => archAct M (γ (Multiplicative.ofAdd t)) v := by
  exact @GlobalTheory.ArchLine.continuous_archAct_line
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionLinearMul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionLinearMul
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

noncomputable section

namespace GlobalTheory.ArchLine

theorem archAct_linear_mul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W),
    (∀ (h : UA σ W.J) (v v' : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M h (v + v') = archAct M h v + archAct M h v') ∧
    (∀ (h : UA σ W.J) (c : ℝ) (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M h (c • v) = c • archAct M h v) ∧
    (∀ (h h' : UA σ W.J) (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M (h * h') v = archAct M h (archAct M h' v)) := by
  intro F E _ _ _ _ _ σ n d X W M
  refine ⟨fun h v v' => ?_, fun h c v => ?_, fun h h' v => ?_⟩
  · unfold archAct
    rw [Prod.fst_add, Prod.snd_add, lift_add, lift_add, ← Prod.mk_add_mk, map_add (f := _)]
    simp only [actAB, Matrix.mul_add, Matrix.add_mul]
    rw [coordI_add]
  · unfold archAct
    rw [Prod.smul_fst, Prod.smul_snd, lift_smul, lift_smul, ← Prod.smul_mk, map_smul]
    simp only [actAB, Matrix.mul_smul, Matrix.smul_mul]
    rw [coordI_smul]
  · unfold archAct
    rw [lift_coordI]
    simp only [actAB, Matrix.mul_smul, Matrix.smul_mul, coordI_one]
    congr 1
    simp only [one_mul, Units.val_one, Subgroup.coe_one, Subgroup.coe_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    simp only [Matrix.one_mul]

end GlobalTheory.ArchLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionLinearMulStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_archimedean_coordinate_action_linear_mul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W),
    (∀ (h : UA σ W.J) (v v' : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M h (v + v') = archAct M h v + archAct M h v') ∧
    (∀ (h : UA σ W.J) (c : ℝ) (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M h (c • v) = c • archAct M h v) ∧
    (∀ (h h' : UA σ W.J) (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M (h * h') v = archAct M h (archAct M h' v)) := by
  intro F E _ _ _ _ _ σ n d X W M
  exact GlobalTheory.ArchLine.archAct_linear_mul M
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionSymplectic
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionSymplectic
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

namespace GlobalTheory.ArchLine

theorem hTens_actAB_unitary {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {JA : Matrix α α E} {JB : Matrix β β E}
    (p : UG c JA × UG c JB) (x y : Matrix α β E) :
    hTens c JA JB (actAB c p x) (actAB c p y) = hTens c JA JB x y := by
  have tr : ∀ N : Matrix α α E, ∑ i, ∑ k, JA i k * N i k = (JAᵀ * N).trace := fun N => by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_comm
  have h1 : ((p.1 : GL α E) : Matrix α α E)ᵀ * JA * ((p.1 : GL α E) : Matrix α α E).map c = JA := p.1.2
  have h2 : ((p.2 : GL β E) : Matrix β β E)ᵀ * JB * ((p.2 : GL β E) : Matrix β β E).map c = JB := p.2.2
  rw [Coord.hTens_eq, Coord.hTens_eq, tr, tr, actAB, actAB]
  generalize ((p.1 : GL α E) : Matrix α α E) = g at h1 ⊢
  generalize ((p.2 : GL β E) : Matrix β β E) = h at h2 ⊢
  have e1 : ((g * y * hᵀ).map c)ᵀ = h.map c * (y.map c)ᵀ * (g.map c)ᵀ := by
    rw [Matrix.map_mul (f := c), Matrix.map_mul (f := c), Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rfl
  have e2 : JAᵀ * (g * x * hᵀ * JB * (h.map c * (y.map c)ᵀ * (g.map c)ᵀ)) =
      JAᵀ * g * (x * (hᵀ * JB * h.map c) * (y.map c)ᵀ) * (g.map c)ᵀ := by simp only [Matrix.mul_assoc]
  have e3 : (g.map c)ᵀ * (JAᵀ * g) = JAᵀ := by
    conv_rhs => rw [← h1]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [e1, e2, h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, e3]

theorem omega_archAct {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (h : UA σ W.J)
    (v v' : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    omega (trP F (Fin n × Fin d)) (archAct M h v) (archAct M h v') = omega (trP F (Fin n × Fin d)) v v' := by
  have hv := coordI_lift M v
  have hv' := coordI_lift M v'
  conv_rhs => rw [← hv, ← hv']
  rw [archAct, archAct, omega_coordI, omega_coordI]
  simp only [sympM, symp, hTens_actAB_unitary]

end GlobalTheory.ArchLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionSymplecticStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_archimedean_coordinate_action_symplectic : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (h : UA σ W.J)
    (v v' : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
    omega (trP F (Fin n × Fin d)) (archAct M h v) (archAct M h v') = omega (trP F (Fin n × Fin d)) v v' := by
  first | exact @GlobalTheory.ArchLine.omega_archAct | exact GlobalTheory.ArchLine.omega_archAct | (intros; apply GlobalTheory.ArchLine.omega_archAct <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOneParameterArchimedeanWeilOperator
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOneParameterArchimedeanWeilOperator
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

noncomputable section

namespace GlobalTheory.ArchLine.OpCont

theorem evI_fin {F : Type} [Field F] [NumberField F] : evI F ((0, 1) : AF F) = 0 :=
  map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem snd_eq_zero_of_at {F : Type} [Field F] [NumberField F] {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) :
    (z i).2 = 0 := by
  have := congrArg Prod.snd (congrFun (hz (0, 1) evI_fin) i)
  change (((0, 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F).2 * (z i).2) = (0 : AF F).2 at this
  rw [one_mul] at this
  exact this

def intInd {F : Type} [Field F] [NumberField F] (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))).indicator 1

theorem intInd_mem {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    intInd (F := F) κ ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  set B := Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) with hB
  have hO : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ => GroundTheory.Global.isOpen_integralFiniteAdeles
  have hK : IsCompact B := isCompact_univ_pi fun _ => GroundTheory.Global.isCompact_integralFiniteAdeles F
  have hC : IsClosed B := hK.isClosed
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ B
  · refine ⟨_, hO, hx, fun y hy => ?_⟩
    simp only [intInd, ← hB, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]
  · refine ⟨_, hC.isOpen_compl, hx, fun y hy => ?_⟩
    simp only [intInd, ← hB, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

end GlobalTheory.ArchLine.OpCont

namespace GlobalTheory.ArchLine

theorem archOp_apply_continuous : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) → ∀ γ ∈ Lines σ W,
    ∀ (f : SInf F (Fin n × Fin d)) (x : Fin n × Fin d → mixedEmbedding.mixedSpace F),
      Continuous fun t : ℝ => archOp om (γ (Multiplicative.ofAdd t)) f x := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hW hex γ hγ f x
  have hC := hW.2.2

  set r₀ : (Fin n × Fin d → AF F) → ℂ := fun y => GlobalTheory.ArchLine.OpCont.intInd (F := F) (Fin n × Fin d) (fun i => (y i).2)
    with hr₀
  have hr₀1 : ∀ y : Fin n × Fin d → AF F, (∀ i, (y i).2 = 0) → r₀ y = 1 := by
    intro y hy
    have : (fun i => (y i).2) = 0 := funext hy
    simp only [hr₀, this, GlobalTheory.ArchLine.OpCont.intInd]
    rw [Set.indicator_of_mem (show (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
      fun _ : Fin n × Fin d => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) from
        fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
    rfl
  have hrest : ∀ g : SInf F (Fin n × Fin d), Rest (evI F) (g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r₀ := by
    intro g
    refine ⟨fun y z hz => ?_, ?_⟩
    · have : (fun i => ((y + z) i).2) = fun i => (y i).2 := by
        funext i
        change (y i).2 + (z i).2 = (y i).2
        rw [GlobalTheory.ArchLine.OpCont.snd_eq_zero_of_at hz i, add_zero]
      simp only [hr₀, this]
    · exact Submodule.subset_span ⟨g, GlobalTheory.ArchLine.OpCont.intInd _, GlobalTheory.ArchLine.OpCont.intInd_mem _, rfl⟩

  let l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => Φ (liftV x), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hl : l ∈ (adeleClass F).adm (Fin n × Fin d) := by
    intro g _
    refine ⟨g 0 • ((BoundedContinuousFunction.evalCLM ℂ x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)), fun f' => ?_⟩
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    show pureA F f' g (liftV x) = _
    simp only [pureA, liftV, RingEquiv.apply_symm_apply]
    change f' x * g 0 = g 0 * f' x
    ring
  have hφ : tens (evI F) (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r₀ ∈ (adeleClass F).sp (Fin n × Fin d) :=
    (hrest f).2
  have hcont := hC l hl _ hφ
  have hpath : Continuous fun t : ℝ => (((1 : UA σ X.J), γ (Multiplicative.ofAdd t)) : UA σ X.J × UA σ W.J) :=
    continuous_const.prodMk (hγ.1.comp continuous_ofAdd)
  have key := hcont.comp hpath
  convert key using 1
  funext t
  have hh : γ (Multiplicative.ofAdd t) ∈ UAt σ W (evI F) := hγ.2 _
  have ha := acts_archOp om (γ (Multiplicative.ofAdd t)) f (hex _ hh f) r₀ (hrest f)
  simp only [Function.comp_apply]
  show _ = om _ _ (liftV x)
  change _ = om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑f) r₀) (liftV x)
  rw [ha]
  have h1 : r₀ (liftV x) = 1 := hr₀1 _ fun i => rfl
  have h2 : (fun i => evI F (liftV x i)) = x := by
    funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _
  simp only [tens, h1, h2, mul_one]

end GlobalTheory.ArchLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOneParameterArchimedeanWeilOperatorStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_oneParameter_archimedean_weilOperator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) → ∀ γ ∈ Lines σ W,
    ∀ (f : SInf F (Fin n × Fin d)) (x : Fin n × Fin d → mixedEmbedding.mixedSpace F),
      Continuous fun t : ℝ => archOp om (γ (Multiplicative.ofAdd t)) f x := by
  first | exact @GlobalTheory.ArchLine.archOp_apply_continuous | exact GlobalTheory.ArchLine.archOp_apply_continuous | (intros; apply GlobalTheory.ArchLine.archOp_apply_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilOperatorsLinearOneMul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilOperatorsLinearOneMul
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

noncomputable section

namespace GlobalTheory.ArchLine.Laws

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def intInd (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))).indicator 1

theorem intInd_mem (κ : Type) [Fintype κ] :
    intInd (F := F) κ ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  have hOo : IsOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) := by
    unfold GroundTheory.Global.integralFiniteAdeles
    exact RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring (v.adicCompletion F))
  have hOc : IsCompact (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    GroundTheory.Global.isCompact_integralFiniteAdeles F
  have hOcl : IsClosed (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    hOc.isClosed
  have hU : IsClopen (Set.pi Set.univ fun _ : κ =>
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))) :=
    ⟨isClosed_set_pi fun _ _ => hOcl, isOpen_set_pi Set.finite_univ fun _ _ => hOo⟩
  show IsLocallyConstant (intInd (F := F) κ) ∧ HasCompactSupport (intInd (F := F) κ)
  refine ⟨(LocallyConstant.indicator (1 : LocallyConstant (κ → FiniteAdeleRing (𝓞 F) F) ℂ) hU).isLocallyConstant, ?_⟩
  exact HasCompactSupport.intro' (isCompact_univ_pi fun _ => hOc) hU.isClosed
    fun x hx => Set.indicator_of_notMem hx _

theorem snd_eq_zero_of_at {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  let u : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
  have hu : evI F u = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h0 : u * z i = 0 := congrFun (hz u hu) i
  have h1 : (u * z i).2 = (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 := rfl
  rw [h0, one_mul] at h1
  exact h1.symm

def refFun (κ : Type) : (κ → AF F) → ℂ := fun x => intInd κ (fun i => (x i).2)

theorem refFun_rest {κ : Type} [Fintype κ] (f : SInf F κ) :
    Rest (evI F) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (refFun κ) := by
  refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, intInd κ, intInd_mem κ, rfl⟩⟩
  show intInd κ (fun i => (x i + z i).2) = intInd κ (fun i => (x i).2)
  congr 1
  funext i
  change (x i).2 + (z i).2 = (x i).2
  rw [snd_eq_zero_of_at hz i, add_zero]

theorem refFun_lift {κ : Type} (t : κ → mixedEmbedding.mixedSpace F) : refFun κ (liftV t) = 1 := by
  show intInd κ (fun i => (liftV t i).2) = 1
  unfold intInd
  rw [Set.indicator_of_mem]
  · rfl
  · intro i _
    change (0 : FiniteAdeleRing (𝓞 F) F) ∈ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))
    exact zero_mem _

theorem tens_lift {κ : Type} (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (t : κ → mixedEmbedding.mixedSpace F) :
    tens (evI F) φ (refFun κ) (liftV t) = φ t := by
  show φ (fun i => evI F (liftV t i)) * refFun κ (liftV t) = φ t
  rw [refFun_lift, mul_one]
  congr 1
  funext i
  exact RingEquiv.apply_symm_apply _ _

theorem eq_of_tens {κ : Type} [Fintype κ] {f₁ f₂ : SInf F κ}
    (h : tens (evI F) (f₁ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (refFun κ) = tens (evI F) (f₂ : _ → ℂ) (refFun κ)) :
    f₁ = f₂ := by
  ext t
  have key := congrFun h (liftV t)
  rwa [tens_lift, tens_lift] at key

theorem tens_add {κ : Type} [Fintype κ] (f f' : SInf F κ) (r : (κ → AF F) → ℂ) :
    tens (evI F) (⇑(f + f') : (κ → mixedEmbedding.mixedSpace F) → ℂ) r = tens (evI F) ⇑f r + tens (evI F) ⇑f' r := by
  funext x
  change (f + f') (fun i => evI F (x i)) * r x = f (fun i => evI F (x i)) * r x + f' (fun i => evI F (x i)) * r x
  rw [SchwartzMap.add_apply, add_mul]

theorem tens_smul {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ) (r : (κ → AF F) → ℂ) :
    tens (evI F) (⇑(c • f) : (κ → mixedEmbedding.mixedSpace F) → ℂ) r = c • tens (evI F) ⇑f r := by
  funext x
  change (c • f) (fun i => evI F (x i)) * r x = c • (f (fun i => evI F (x i)) * r x)
  rw [SchwartzMap.smul_apply, smul_mul_assoc]

theorem img (om : Rep σ X W) (h : UA σ W.J) (f : SInf F (Fin n × Fin d))
    (hx : ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) ⇑f ⇑f₁) :
    om (1, h) (tens (evI F) ⇑f (refFun _)) = tens (evI F) ⇑(archOp om h f) (refFun _) := acts_archOp om h f hx _ (refFun_rest f)

theorem archOp_eq_of_acts (om : Rep σ X W) (h : UA σ W.J) (f f₁ : SInf F (Fin n × Fin d))
    (hA : Acts (evI F) (om (1, h)) ⇑f ⇑f₁) : archOp om h f = f₁ := by
  apply eq_of_tens
  rw [← img om h f ⟨f₁, hA⟩]
  exact hA _ (refFun_rest f)

end GlobalTheory.ArchLine.Laws

namespace GlobalTheory.ArchLine


open GlobalTheory.ArchLine.Laws in
theorem archOp_laws : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) →
    (∀ h ∈ UAt σ W (evI F), ∀ f f' : SInf F (Fin n × Fin d), archOp om h (f + f') = archOp om h f + archOp om h f') ∧
    (∀ h ∈ UAt σ W (evI F), ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)), archOp om h (c • f) = c • archOp om h f) ∧
    (∀ f : SInf F (Fin n × Fin d), archOp om 1 f = f) ∧
    (∀ h ∈ UAt σ W (evI F), ∀ h' ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d),
      archOp om (h * h') f = archOp om h (archOp om h' f)) := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om _ hex
  refine ⟨fun h hh f f' => ?_, fun h hh c f => ?_, fun f => ?_, fun h hh h' hh' f => ?_⟩
  · apply eq_of_tens
    rw [tens_add, ← img om h (f + f') (hex h hh _), ← img om h f (hex h hh f), ← img om h f' (hex h hh f'),
      tens_add, map_add]
  · apply eq_of_tens
    rw [tens_smul, ← img om h (c • f) (hex h hh _), ← img om h f (hex h hh f), tens_smul, map_smul]
  · apply archOp_eq_of_acts
    intro r _
    have e1 : om (1, 1) = 1 := map_one om
    rw [e1]
    rfl
  · have hmul : h * h' ∈ UAt σ W (evI F) := by
      intro u hu
      have e : mat (h * h') - 1 = (mat h - 1) * mat h' + (mat h' - 1) := by
        change mat h * mat h' - 1 = _
        noncomm_ring
      have a1 : u • (mat h - 1) = 0 := (show ∀ u, evI F u = 0 → u • (mat h - 1) = 0 from hh) u hu
      have a2 : u • (mat h' - 1) = 0 := (show ∀ u, evI F u = 0 → u • (mat h' - 1) = 0 from hh') u hu
      rw [e, smul_add, ← Matrix.smul_mul, a1, a2, zero_mul, add_zero]
    apply eq_of_tens
    rw [← img om (h * h') f (hex _ hmul f), ← img om h (archOp om h' f) (hex h hh _),
      ← img om h' f (hex h' hh' f)]
    have e2 : ((1 : UA σ X.J), h * h') = (1, h) * (1, h') := by rw [Prod.mk_mul_mk, one_mul]
    rw [e2, map_mul]
    rfl

end GlobalTheory.ArchLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilOperatorsLinearOneMulStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_weilOperators_linear_one_mul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) →
    (∀ h ∈ UAt σ W (evI F), ∀ f f' : SInf F (Fin n × Fin d), archOp om h (f + f') = archOp om h f + archOp om h f') ∧
    (∀ h ∈ UAt σ W (evI F), ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)), archOp om h (c • f) = c • archOp om h f) ∧
    (∀ f : SInf F (Fin n × Fin d), archOp om 1 f = f) ∧
    (∀ h ∈ UAt σ W (evI F), ∀ h' ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d),
      archOp om (h * h') f = archOp om h (archOp om h' f)) := by
  first | exact @GlobalTheory.ArchLine.archOp_laws | exact GlobalTheory.ArchLine.archOp_laws | (intros; apply GlobalTheory.ArchLine.archOp_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersAtRealPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersAtRealPlaces
open Formalism.BasicNotions

namespace GlobalTheory

theorem vacChar_of_record : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D :=
  GlobalTheory.T.thetaVacuumCharacters_realPlaces

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersAtRealPlacesStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaVacuumCharacters_atRealPlaces : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D := by
  first | exact @GlobalTheory.vacChar_of_record | exact GlobalTheory.vacChar_of_record | (intros; apply GlobalTheory.vacChar_of_record <;> assumption)
end
end
