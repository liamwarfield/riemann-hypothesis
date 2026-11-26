module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsClassicalLevelDataCoverSelfDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLaws

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Real Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.Base

open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.SW.Lev

variable {D : D7}

theorem cc_sqrt (D : D7) : cc D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  rw [cc_eq_conj]; exact D.host.conj_sqrtMinusD

theorem star_eq_cc (x : D.host.E) : star x = cc x := rfl

theorem exists_ideal (D : D7) : ∃ 𝔪 : Ideal (𝓞 D.host.E), 𝔪 ≠ ⊤ ∧ 𝔪 ≠ ⊥ ∧ IsCoprime 𝔪 (conjI 𝔪) ∧
    IsCoprime 𝔪 (Ideal.span {2}) := by
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hs := D.host.sqrtMinusD_sq
  have hi : IsIntegral ℤ D.host.sqrtMinusD := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hs]
    exact (isIntegral_natCast _).neg
  let s : 𝓞 D.host.E := ⟨_, hi⟩
  have hb : bar (2 + s) = 2 - s := by
    apply RingOfIntegers.ext
    rw [map_add (f := _), map_ofNat, sub_eq_add_neg]
    simp only [map_add (f := _), map_neg]
    congr 1
    exact (coe_bar s).trans (cc_sqrt D)
  have hs2 : s ^ 2 = -(D.host.d : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    simp only [map_pow, map_neg, map_natCast]
    exact hs
  have hn : (2 + s) * (2 - s) = ((4 + D.host.d : ℕ) : 𝓞 D.host.E) := by
    push_cast
    linear_combination -hs2
  have hm : ((4 + D.host.d : ℕ) : 𝓞 D.host.E) ∈ Ideal.span {2 + s} :=
    hn ▸ Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  obtain ⟨k, hk⟩ : ∃ k, D.host.d = 16 * k + 7 := ⟨D.host.d / 16, by omega⟩
  refine ⟨Ideal.span {2 + s}, fun h => ?_, fun h => ?_, ?_, ?_⟩
  · have h1 := Ideal.span_singleton_eq_top.1 h
    have h2 := h1.mul (h1.map bar)
    rw [hb, hn] at h2
    have h3 : IsUnit (algebraMap ℤ (𝓞 D.host.E) ((4 + D.host.d : ℕ) : ℤ)) := by rwa [map_natCast]
    have h4 := Int.isUnit_iff.1 (isUnit_of_map_unit _ _ h3)
    omega
  · rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hm
    omega
  · have h1 : 2 - s ∈ conjI (Ideal.span {2 + s}) := by
      rw [mem_conjI, ← hb, bar_bar]
      exact Ideal.mem_span_singleton_self _
    refine Ideal.isCoprime_iff_exists.2 ⟨3 * ((4 + D.host.d : ℕ) : 𝓞 D.host.E) - (12 * k + 8) * (2 + s),
      sub_mem (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)),
      -(12 * k + 8) * (2 - s), Ideal.mul_mem_left _ _ h1, ?_⟩
    rw [hk]
    push_cast
    ring
  · exact GlobalTheory.LevelTied.cop_of_nat (a := 4 + D.host.d) (b := 2)
      (Nat.coprime_two_right.2 (Nat.odd_iff.2 (by omega))) hm (Ideal.mem_span_singleton_self _)

theorem exists_level {r : ℕ} (X : Data D.host.E r) : ∃ Lv : GlobalTheory.SW.Level X, IdemTwo Lv.w := by
  obtain ⟨𝔪, h1, h2, h3, h4⟩ := exists_ideal D
  obtain ⟨β, hβ, hβ'⟩ := GlobalTheory.LevelTied.exists_frame X 𝔪 h2
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨w1, w2, w3, -, k, hk⟩ := GlobalTheory.quadratic_refinement.2 (D.host.d : ℤ) D.host.sqrtMinusD (by omega)
    (by rw [Int.cast_natCast]; exact D.host.sqrtMinusD_sq) (cc_sqrt D)
  refine ⟨⟨𝔪, h1, h2, h3, h4, β, hβ, hβ', ⊤, 1, (1 + D.host.sqrtMinusD) / 2, w1, w2⟩, k,
    isIntegral_intCast k, ?_⟩
  refine w3.trans ?_
  rw [hk]
  push_cast
  ring

theorem cartan_of_on {k : ℕ} {G B s : Matrix (Fin k) (Fin k) ℂ} (hs : s * s = 1) (hs' : sᴴ = s)
    (h : Bᴴ * G * B = s) : IsCartanInv G (B * s * B⁻¹) := by
  have hB : IsUnit B.det := by
    have : (s * (Bᴴ * G)) * B = 1 := by rw [Matrix.mul_assoc, h, hs]
    exact Matrix.isUnit_det_of_left_inverse this
  have e1 := Matrix.mul_nonsing_inv B hB
  have e2 := Matrix.nonsing_inv_mul B hB
  generalize B⁻¹ = A at e1 e2
  have e3 : Aᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, e1, conjTranspose_one]
  have hG : G = Aᴴ * s * A := by
    rw [← h]
    calc G = (Aᴴ * Bᴴ) * G * (B * A) := by rw [e1, e3, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hGs : G * (B * s * A) = Aᴴ * A := by
    rw [hG]
    calc _ = Aᴴ * (s * (A * B) * s) * A := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [e2, Matrix.mul_one, hs, Matrix.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · calc _ = B * (s * (A * B) * s) * A := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [e2, Matrix.mul_one, hs, Matrix.mul_one, e1]
  · rw [Matrix.mul_assoc, hGs, conjTranspose_mul, conjTranspose_mul, hs', hG]
    have e4 : Bᴴ * Aᴴ = 1 := by rw [← conjTranspose_mul, e2, conjTranspose_one]
    calc _ = Aᴴ * (s * (Bᴴ * Aᴴ)) * A := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [e4, Matrix.mul_one]
  · rw [hGs]
    exact Matrix.PosDef.conjTranspose_mul_self A
      (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2
        (Matrix.isUnit_det_of_left_inverse e1)))

theorem sgnM_sq {r : ℕ} (X : Data D.host.E r) : sgnM X * sgnM X = 1 := by
  rw [sgnM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  unfold sgn
  split_ifs <;> simp

theorem sgnM_herm {r : ℕ} (X : Data D.host.E r) : (sgnM X)ᴴ = sgnM X := by
  rw [sgnM, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp

theorem mem_Dinv {z : D.host.E} : z ∈ Dinv D ↔ ∀ c : 𝓞 D.host.E, ∃ m : ℤ, Algebra.trace ℚ D.host.E (z * c) = m := by
  rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0)]
  constructor
  · intro h c
    obtain ⟨m, hm⟩ := h (c : D.host.E) ((FractionalIdeal.mem_one_iff (S := nonZeroDivisors (𝓞 D.host.E))).mpr ⟨c, rfl⟩)
    exact ⟨m, by rw [← Algebra.traceForm_apply, ← hm]; rfl⟩
  · rintro h a ha
    obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff (S := nonZeroDivisors (𝓞 D.host.E))).mp ha
    obtain ⟨m, hm⟩ := h c
    exact ⟨m, by rw [Algebra.traceForm_apply]; exact hm.symm⟩

theorem dual_of_selfD {r : ℕ} {X : Data D.host.E r} (hk : X.κ0 = 2 * D.host.xi0) {L : Lt D.host.E r}
    (hL : SelfD X L) (y : Fin r → D.host.E) : y ∈ L ↔ ∀ z ∈ L, D.host.xi0 * herm X.Gm y z ∈ Dinv D := by
  have e : ∀ u v, EF X u v = -Algebra.trace ℚ D.host.E (D.host.xi0 * herm X.Gm u v) := fun u v => by
    rw [EF_def, hk, mul_div_cancel_left₀ _ two_ne_zero, neg_mul, map_neg]
  constructor
  · intro hy z hz
    refine mem_Dinv.2 fun c => ?_
    obtain ⟨m, hm⟩ := (hL.2 _).1 (L.smul_mem c hy) z hz
    rw [e, O_smul, herm_smul_left] at hm
    refine ⟨-m, ?_⟩
    rw [Int.cast_neg, ← hm, neg_neg]
    congr 1
    ring
  · intro h
    refine (hL.2 _).2 fun z hz => ?_
    obtain ⟨m, hm⟩ := mem_Dinv.1 (h z hz) 1
    refine ⟨-m, ?_⟩
    rw [e, Int.cast_neg, ← hm]
    simp

theorem sum_eq_herm (T : HSp D) (x y : Fin T.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * T.gram i j * y j = herm T.gramᵀ y x := by
  rw [herm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [star_eq_cc, transpose_apply]
  ring

theorem selfDualC_latP {T : HSp D} {X : Data D.host.E T.rank} (hG : X.Gm = T.gramᵀ) (hk : X.κ0 = 2 * D.host.xi0)
    {L : Lt D.host.E T.rank} (hL : SelfD X L) (hsp : Submodule.span D.host.E (L : Set (Fin T.rank → D.host.E)) = ⊤) :
    IsSelfDualC T (lattice₂ D L) := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hF := dual_of_selfD hk hL
  rw [hG] at hF
  refine ⟨Submodule.IsLattice.of_fg D.host.E (localLattice_fg D L hL.1), fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · exact ⟨⟨_, localLattice_form_integral hP _ L hF hy hx⟩, (sum_eq_herm T x y).symm⟩
  · refine mem_dual_localLattice_of_forall hP _ L hF fun x hx => ?_
    obtain ⟨b, hb⟩ := h x hx
    rw [← sum_eq_herm, ← hb]
    exact b.2

theorem star_mem_stdL {n : ℕ} {v : Fin n → D.host.E} (hv : v ∈ stdL D.host.E n) : star v ∈ stdL D.host.E n :=
  (GlobalTheory.SW.Base.mem_stdL _).2 fun a => int_cc D ((GlobalTheory.SW.Base.mem_stdL _).1 hv a)

theorem selfDualC_stdL {S : HSp D} (hS : S.gram = 1) : IsSelfDualC S (stdL D.host.E S.rank) := by
  have e : ∀ x y : Fin S.rank → D.host.E, ∑ i, ∑ j, star (x i) * S.gram i j * y j = ∑ i, star (x i) * y i :=
    fun x y => by simp [hS, Matrix.one_apply]
  refine ⟨Submodule.IsLattice.of_fg D.host.E (Submodule.fg_span (Set.finite_range _)), fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [e]
    exact ⟨⟨∑ i, star (x i) * y i, IsIntegral.sum _ fun i _ => ((GlobalTheory.SW.Base.mem_stdL _).1 (star_mem_stdL hx) i).mul ((GlobalTheory.SW.Base.mem_stdL _).1 hy i)⟩, rfl⟩
  · refine (GlobalTheory.SW.Base.mem_stdL _).2 fun a => ?_
    obtain ⟨b, hb⟩ := h (Pi.single a 1) (Submodule.subset_span ⟨a, rfl⟩)
    rw [e, Finset.sum_eq_single a (fun i _ hi => by simp [hi]) (by simp)] at hb
    have : y a = b := by simp [hb]
    rw [this]
    exact b.2

theorem hatA_le {S T : HSp D} (hS : S.gram = 1) (L : Lt D.host.E T.rank) :
    hatA S T (tens (stdL D.host.E S.rank) L) ≤ latO S T (stdL D.host.E S.rank) (lattice₂ D L) fun _ => True := by
  have key : ∀ y ∈ tens (stdL D.host.E S.rank) L,
      yᵀ ∈ GlobalTheory.LatVac.latRat S T (stdL D.host.E S.rank) (lattice₂ D L) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨v, hv, u, hu, rfl⟩ := hy
      rw [lat_eq_span Formalism.IndefR.Fin.factPrincipalDatum L] at hu
      induction hu using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨a, ha, t, ht, rfl⟩ := hu
        refine AddSubgroup.subset_closure ⟨a, ha, _, star_mem_stdL hv, t, ht, ?_⟩
        ext i j
        simp [GlobalTheory.LatVac.genMap, hS, Matrix.one_apply, vecMulVec_apply, mul_comm, mul_left_comm]
      | zero => simp
      | add u u' _ _ h h' => rw [vecMulVec_add, transpose_add]; exact add_mem h h'
      | smul c u _ h =>
        rw [O_smul, vecMulVec_smul, transpose_smul]
        exact GlobalTheory.LatVac.smul_mem_latRat c h
    | zero => exact zero_mem _
    | add _ _ _ _ h h' => rw [transpose_add]; exact add_mem h h'
    | neg _ _ h => rw [transpose_neg]; exact neg_mem h
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, y, hy, rfl⟩
  exact GlobalTheory.LatVac.finTens_mem_latO hα (key y hy)

theorem exists_base {S T : HSp D} (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X) (B : C.Bas) (hB : C.IsB B) :
    ∃ f', C.IsBase Lv B f' := by
  have hsd : SelfD C.X (Lv.sh C.X.Λ) := selfD_idq Lv.ne_bot Lv.proper Lv.cop (selfD_of_sympl C.sympl)
  have hsp : Submodule.span D.host.E (Lv.sh C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ := by
    obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Lv.ne_bot
    have hp0' : (p : D.host.E) ≠ 0 := by simpa using hp0
    rw [eq_top_iff, ← C.X.Λ_span, Submodule.span_le]
    exact fun v hv => (Submodule.smul_mem_iff _ hp0').1
      (Submodule.subset_span (smul_le_idq _ _ _ (Submodule.smul_mem_smul hp hv)))
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero C.ψ C.θ C.std C.inf S T (fun _ => 1) (C.sB B)
    (fun τ => by
      have : gramAt D S τ = 1 := by rw [gramAt, C.m.gS]; exact Matrix.map_one _ (map_zero _) (map_one _)
      rw [this]
      exact ⟨Matrix.one_mul _, by simp, by rw [Matrix.one_mul]; exact Matrix.PosDef.one⟩)
    (fun τ => cartan_of_on (sgnM_sq _) (sgnM_herm _) (hB τ)) _ _ (selfDualC_stdL C.m.gS)
    (selfDualC_latP C.m.gT C.m.ka hsd hsp)
  have h1 := hf 1
  simp only [one_mul] at h1
  have hle := hatA_le C.m.gS (Lv.sh C.X.Λ)
  exact ⟨f, h1.1, f0, h1.2.2, fun u hu => h1.2.1.1 u (hle hu), fun e he u hu => h1.2.1.2 e he u (hle hu)⟩

theorem isFam_one {S T : HSp D} (C : Ctx S T) : C.IsFam (fun _ : Fin 1 => 1) := by
  refine ⟨⟨0, 0, fun _ => ?_⟩, fun u _ z w => by simp⟩
  rw [map_one]
  refine Harm.mem_rowHighest_iff.2 ⟨Harm.isHarmonic_C 1, fun t a => ?_, fun t b => ?_,
    fun _ _ _ _ _ => map_one _, fun _ _ _ _ _ => map_one _⟩
  · simpa [Harm.partOf] using MvPolynomial.isWeightedHomogeneous_one ℂ _
  · simpa [Harm.partOf] using MvPolynomial.isWeightedHomogeneous_one ℂ _

theorem level_base_fam : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∃ Lv : GlobalTheory.SW.Level C.X, IdemTwo Lv.w) ∧ (∀ (Lv : GlobalTheory.SW.Level C.X) (B : C.Bas), C.IsB B → ∃ f', C.IsBase Lv B f') ∧ C.IsFam (fun _ : Fin 1 => 1) :=
  fun _ _ _ C => ⟨exists_level C.X, exists_base C, isFam_one C⟩

end GlobalTheory.Ker.Base

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HarmonicConnectionValueEqPolynomialDerivative
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HarmonicConnectionValueEqPolynomialDerivative
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem nab_harm_val_eq_polyDeriv : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (th : Fin n → (Fin g → ℂ) → ℂ), (∀ b, A.Reads ((N : ℤ) ^ 2) (F b) (th b)) → ∑ m ∈ P.support, algebraMap c.F ℂ (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) = I2.polyDeriv (MvPolynomial.map (algebraMap c.F ℂ) P) (fun ℓ => (Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1) : Fin n → Fin g → ℂ)) (fun z => ∏ b, th b (z b)) 0 := by
  intro hC E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A h1 h2 h3 _ nab hn n N a P hP
  obtain ⟨Φ, -, -, -, -, -, hRd, -⟩ := GlobalTheory.T.exists_analyticFrame_of_analyticFibre E H Dw l Xo c r g X bas idx e x L y A h1 h2 h3
  have hk : ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) := by push_cast; rfl
  rw [hk]
  intro F th hF
  have key := GlobalTheory.T.harmonicValue_canonicalConnection_eq_polyDeriv hC E H Dw l Xo c y g _ e Φ nab hn (N ^ 2) n F th
    (fun b => (hRd _ _ _).2 (hF b)) a P hP
  rw [key]
  congr 1

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HarmonicConnectionValueEqPolynomialDerivativeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicConnectionValue_eq_polynomial_derivative : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (th : Fin n → (Fin g → ℂ) → ℂ), (∀ b, A.Reads ((N : ℤ) ^ 2) (F b) (th b)) → ∑ m ∈ P.support, algebraMap c.F ℂ (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) = I2.polyDeriv (MvPolynomial.map (algebraMap c.F ℂ) P) (fun ℓ => (Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1) : Fin n → Fin g → ℂ)) (fun z => ∏ b, th b (z b)) 0 := by
  first | exact @GlobalTheory.Dict.nab_harm_val_eq_polyDeriv | exact GlobalTheory.Dict.nab_harm_val_eq_polyDeriv | (intros; apply GlobalTheory.Dict.nab_harm_val_eq_polyDeriv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorOriginEqPolyDeriv
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorOriginEqPolyDeriv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.FockOrigin

theorem prod_C_mul_X {σ σ' : Type} [DecidableEq σ'] (c : σ → ℂ) (f : σ → σ') (L : List σ) :
    (L.map fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v)).prod =
      (L.map c).prod • MvPolynomial.monomial (Multiset.toFinsupp ((L.map f : List σ') : Multiset σ')) (1 : ℂ) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.map_cons,
      ← Multiset.cons_coe, ← Multiset.singleton_add, map_add, Multiset.toFinsupp_singleton,
      MvPolynomial.X, MvPolynomial.C_mul', smul_mul_smul_comm, MvPolynomial.monomial_mul, one_mul]

theorem polyDeriv_aeval_monomial {σ σ' W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (c : σ → ℂ) (f : σ → σ') (u : σ' → W) {θ : W → ℂ} (hθ : ContDiff ℂ (⊤ : ℕ∞) θ) (m : σ →₀ ℕ) (x : W) :
    I2.polyDeriv (MvPolynomial.aeval (fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v))
      (MvPolynomial.monomial m (1 : ℂ))) u θ x =
      ((Finsupp.toMultiset m).toList.map c).prod *
        I2.itD θ ((Finsupp.toMultiset m).toList.map fun v => u (f v)) x := by
  have h1 := prod_C_mul_X (fun _ : σ => (1 : ℂ)) id (Finsupp.toMultiset m).toList
  simp only [map_one, one_mul, id, List.map_id, List.map_const',
    List.prod_replicate, one_pow, one_smul, Multiset.coe_toList, Finsupp.toMultiset_toFinsupp] at h1
  rw [← h1, map_list_prod, List.map_map]
  have h2 : (⇑(MvPolynomial.aeval (fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v)) :
      MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ' ℂ) ∘ fun v => MvPolynomial.X v) =
      fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v) := by
    funext v; simp
  rw [h2, prod_C_mul_X, I2.polyDeriv_smul, I2.polyDeriv_monomial_one, I2.pdTerm_eq_itD,
    Multiset.toFinsupp_toMultiset]
  congr 1
  refine congrFun (I2.ct_itD_perm hθ ?_) x
  have h3 : ((Finsupp.toMultiset m).toList.map fun v => u (f v)) =
      ((Finsupp.toMultiset m).toList.map f).map u := by rw [List.map_map]; rfl
  rw [h3]
  refine List.Perm.map u ?_
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList]

theorem fvec_zero_eq_polyDeriv : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ (G : WO S T → ℂ) (θ : (Fin S.rank → Fin C.g → ℂ) → ℂ), Differentiable ℂ θ → (∀ w, IsRealPt w → G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * θ (C.zOf (C.xB B) w)) → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, C.fvec B G Q 0 = I2.polyDeriv (C.toH Q) (letterDir C.X C.hr C.idx) θ 0 := by
  intro D S T C B hB G θ hθ hG Q
  obtain ⟨R, -, -, hadd, -⟩ := GlobalTheory.KerReal.real_points D S T C
  obtain ⟨-, -, -, -, hdir, -⟩ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB
  set x := C.xB B with hx0
  let f : FVar D T.rank S.rank → Harm.Var C.X.Ψ C.q0 C.X.p0 (Fin S.rank) :=
    fun v => (C.m.e v.1, (rowIdx C.hr).symm v.2.1, v.2.2)
  let c : FVar D T.rank S.rank → ℂ := fun v => ((2 / fockScale D v.1 : ℝ) : ℂ)
  let u : FVar D T.rank S.rank → Fin S.rank → Fin C.g → ℂ := fun v => letterDir C.X C.hr C.idx (f v)
  let lam : FVar D T.rank S.rank → (Fin S.rank → Fin C.g → ℂ) → ℂ := fun v z =>
    -(π * ∑ k, hx C.X C.bas C.idx x (u v k) (z k))
  let Dl : FVar D T.rank S.rank → ((Fin S.rank → Fin C.g → ℂ) → ℂ) → (Fin S.rank → Fin C.g → ℂ) → ℂ :=
    fun l Φ z => lam l z * Φ z + (1 / 2 : ℂ) * (fderiv ℝ Φ z (u l) - I * fderiv ℝ Φ z (I • u l))
  have hlam : ∀ l, (∀ a b, lam l (a + b) = lam l a + lam l b) ∧
      ∀ (t : ℂ) a, lam l (t • a) = conj t * lam l a := by
    intro l
    refine ⟨fun a b => ?_, fun t a => ?_⟩
    · simp only [lam, GlobalTheory.Dict.hx, Pi.add_apply, mulVec_add, star_add, dotProduct_add,
        Finset.sum_add_distrib]
      ring
    · simp only [lam, GlobalTheory.Dict.hx, Pi.smul_apply, mulVec_smul, star_smul, dotProduct_smul,
        smul_eq_mul, ← Finset.mul_sum, RCLike.star_def]
      ring
  have hops := GlobalTheory.Ker.CreOp.foldr_creation_zero _ _ u lam θ hlam hθ Dl (fun _ _ _ => rfl)
  let A := aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) (fun _ => 1) B
  have key : ∀ L : List (FVar D T.rank S.rank), ∀ w, IsRealPt w →
      L.foldr (fun i g => A i g) G w =
        gaussR C.X C.bas C.idx x (C.zOf x w) * ((L.map c).prod * L.foldr Dl θ (C.zOf x w)) := by
    intro L
    induction L with
    | nil => intro w hw; simpa using hG w hw
    | cons a L ih =>
      intro w hw
      have hd : Differentiable ℝ (L.foldr Dl θ) := (hops L).1.differentiable (by simp)
      have h := (GlobalTheory.T.annihilation_creation_periodCoordinates D S T C B hB _ (fun z => (L.map c).prod * L.foldr Dl θ z)
        (hd.const_mul _) ih a.1 (unitMap 1 (B a.1) a.2.1 a.2.2) (u a) (hdir a.1 a.2.1 a.2.2).symm w hw).2
      rw [List.foldr_cons]
      change ((fockScale D a.1 : ℂ)⁻¹) * crea (heisO C.ψ S T) C.θ a.1 (cplxO 1 (C.sB B a.1))
        (unitMap 1 (B a.1) a.2.1 a.2.2) (L.foldr (fun i g => A i g) G) w = _
      rw [h, fderiv_const_mul (hd _)]
      simp only [List.foldr_cons, List.map_cons, List.prod_cons, _root_.smul_apply, smul_eq_mul]
      simp only [Dl, lam, c, ← hx0]
      push_cast
      ring
  have h0 : C.zOf x 0 = 0 := by
    have h1 : C.realPt 0 = 0 := by
      have := hadd 0 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    funext k i
    simp only [Ctx.zOf, h1, zR, Pi.zero_apply, mulVec_zero]
    split_ifs
    · simp [hermC]
    · rfl
  have hr0 : IsRealPt (0 : WO S T) := by
    unfold IsRealPt
    ext i j
    simp
  have hg0 : gaussR C.X C.bas C.idx x (0 : Fin S.rank → Fin C.g → ℂ) = 1 := by
    simp [gaussR, GlobalTheory.Dict.hx]
  have hsm := I2.contDiff_of_diff hθ
  induction Q using MvPolynomial.induction_on' with
  | add P P' hP hP' =>
    rw [map_add (f := _), I2.polyDeriv_add, ← hP, ← hP', Ctx.fvec, map_add (f := _)]
    rfl
  | monomial m a =>
    have e : MvPolynomial.monomial m a = a • MvPolynomial.monomial m (1 : ℂ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, I2.polyDeriv_smul, Ctx.fvec, map_smul, Pi.smul_apply, smul_eq_mul]
    congr 1
    have h2 : pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun _ => 1) B G
        (MvPolynomial.monomial m (1 : ℂ)) = opPow A m G := by
      have := (MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ).constr_basis ℂ
        (fun k => opPow A k G) m
      rwa [MvPolynomial.coe_basisMonomials] at this
    rw [h2, opPow, key _ 0 hr0, h0, hg0, one_mul, (hops _).2]
    refine Eq.trans ?_ (polyDeriv_aeval_monomial c f _ hsm m 0).symm
    congr 1
    rw [I2.ct_iter_eq_itD_ofFn]
    congr 1
    exact List.ofFn_getElem_eq_map _ u

end GlobalTheory.Ker.FockOrigin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorOriginEqPolyDerivStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialVector_origin_eq_polyDeriv : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ (G : WO S T → ℂ) (θ : (Fin S.rank → Fin C.g → ℂ) → ℂ), Differentiable ℂ θ → (∀ w, IsRealPt w → G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * θ (C.zOf (C.xB B) w)) → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, C.fvec B G Q 0 = I2.polyDeriv (C.toH Q) (letterDir C.X C.hr C.idx) θ 0 := by
  first | exact @GlobalTheory.Ker.FockOrigin.fvec_zero_eq_polyDeriv | exact GlobalTheory.Ker.FockOrigin.fvec_zero_eq_polyDeriv | (intros; apply GlobalTheory.Ker.FockOrigin.fvec_zero_eq_polyDeriv <;> assumption)
end
end
