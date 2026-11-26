module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNetDimensionAndPointCountBound
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmFamilyFunctionalsDetectLowCoefficients
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.DegreeInfimum.PlaceDegreeSums
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.KerCorePf
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcDatumFamilyFunctionalBoundedLinearOnCuspFor
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsBoundedByPowerOfAtLeastTwoInvD4ep0
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj hiding Unf GoodEmb
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.SplitConst

def PB (X : ℝ) (k : ℕ) (a : ℝ) : Prop := 2 ≤ X ∧ 0 ≤ a ∧ a ≤ X ^ k

variable {X a b : ℝ} {i j : ℕ}

theorem PB.mono (h : PB X i a) (hij : i ≤ j) : PB X j a :=
  ⟨h.1, h.2.1, h.2.2.trans (pow_le_pow_right₀ (by linarith [h.1]) hij)⟩

theorem PB.of_le (h : PB X i a) (hb : 0 ≤ b) (hba : b ≤ a) : PB X i b := ⟨h.1, hb, hba.trans h.2.2⟩

theorem PB.add (h : PB X i a) (h' : PB X j b) : PB X (max i j + 1) (a + b) := by
  have h1 := (h.mono (le_max_left i j)).2.2
  have h2 := (h'.mono (le_max_right i j)).2.2
  have h3 : 0 ≤ X ^ max i j := pow_nonneg (by linarith [h.1]) _
  refine ⟨h.1, add_nonneg h.2.1 h'.2.1, ?_⟩
  rw [pow_succ]
  nlinarith [h.1]

theorem PB.mul (h : PB X i a) (h' : PB X j b) : PB X (i + j) (a * b) := by
  refine ⟨h.1, mul_nonneg h.2.1 h'.2.1, ?_⟩
  rw [pow_add]
  exact mul_le_mul h.2.2 h'.2.2 h'.2.1 (h.2.1.trans h.2.2)

theorem PB.pow (h : PB X i a) (n : ℕ) : PB X (i * n) (a ^ n) := by
  refine ⟨h.1, pow_nonneg h.2.1 _, ?_⟩
  rw [pow_mul]
  exact pow_le_pow_left₀ h.2.1 h.2.2 _

theorem PB.const (hX : 2 ≤ X) (k : ℕ) (ha : 0 ≤ a) (h : a ≤ 2 ^ k) : PB X k a :=
  ⟨hX, ha, h.trans (pow_le_pow_left₀ (by norm_num) hX _)⟩

theorem PB.base (hX : 2 ≤ X) (ha : 0 ≤ a) (h : a ≤ X) : PB X 1 a := ⟨hX, ha, by simpa using h⟩

theorem PB.sqrt (h : PB X i a) : PB X i (Real.sqrt a) := by
  refine ⟨h.1, Real.sqrt_nonneg _, ?_⟩
  have h1 : 1 ≤ X ^ i := one_le_pow₀ (by linarith [h.1])
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith [h.2.2]

theorem PB.log (h : PB X i a) (ha : 1 ≤ a) : PB X i (Real.log a) :=
  h.of_le (Real.log_nonneg ha) (by linarith [Real.log_le_sub_one_of_pos (show 0 < a by linarith)])

theorem PB.log_le {Z : ℝ} (h : PB (Real.exp Z) i a) (ha : 0 < a) : Real.log a ≤ i * Z := by
  have := Real.log_le_log ha h.2.2
  rwa [Real.log_pow, Real.log_exp] at this

theorem rpow_le_self {d s : ℝ} (hd : 1 ≤ d) (hs : 1 ≤ s) : d ^ (1 / s) ≤ d := by
  have := Real.rpow_le_rpow_of_exponent_le hd (show 1 / s ≤ 1 by rw [div_le_one (by linarith)]; exact hs)
  simpa using this

theorem isBoundedByPowerOfAtLeastTwo_inv_d4ep0 {g d f NA NC c w : ℝ} (hX : 2 ≤ X) (hg : 1 ≤ g) (hd : 1 ≤ d) (hf : 1 ≤ f) (hNA : 1 ≤ NA)
    (hNC : 1 ≤ NC) (hc : 0 < c) (hw : 1 ≤ w) (hg' : g ≤ X) (hd' : d ≤ X) (hf' : f ≤ X) (hNA' : NA ≤ X)
    (hNC' : NC ≤ X) (hc' : c ≤ X) (hw' : w ≤ X) : PB X 50 (flowEpsilonBound g d f NA NC c w)⁻¹ := by
  have pg := PB.base hX (by linarith) hg'
  have pd := PB.base hX (by linarith) hd'
  have pf := PB.base hX (by linarith) hf'
  have pNA := PB.base hX (by linarith) hNA'
  have pNC := PB.base hX (by linarith) hNC'
  have pc := PB.base hX hc.le hc'
  have pw := PB.base hX (by linarith) hw'
  have p1 : PB X 0 1 := PB.const hX 0 (by norm_num) (by norm_num)
  have p2 : PB X 1 2 := PB.const hX 1 (by norm_num) (by norm_num)
  have p4 : PB X 2 4 := PB.const hX 2 (by norm_num) (by norm_num)
  have prd : PB X 1 (d ^ (1 / (2 * f))) :=
    pd.of_le (Real.rpow_nonneg (by linarith) _) (rpow_le_self hd (by linarith))
  have pN0 := pg.mul (pd.pow 2)
  have pH := (pNC.pow 2).mul (p2.add (((p4.mul (pf.pow 4)).mul (prd.pow 2)).mul (pNA.pow 2)))
  have pK' := (pN0.mul pH).mul ((p2.mul pc).add p1)
  have pK := p1.add pK'
  have pN2 := p4.mul pf
  have pl := ((p2.mul pK).mul pN2).log (by nlinarith [pK'.2.1])
  have pR := ((pw.add (pN2.mul pl)).add pN2).add p2
  have pD := ((((pN0.pow 2).mul (pNC.pow 2)).mul pc).mul pR).mono (j := 50) (by norm_num)
  unfold flowEpsilonBound
  simp only []
  rcases min_choice (1 : ℝ) _ with h | h <;> rw [h]
  · rw [inv_one]; exact p1.mono (by norm_num)
  · rw [inv_div]
    refine pD.of_le (div_nonneg pD.2.1 (by positivity)) (div_le_self pD.2.1 (one_le_pow₀ hf))

theorem rh_inv {c w : ℝ} (hX : 2 ≤ X) (hc : 0 < c) (hw : 1 ≤ w) (hc' : c ≤ X) (hw' : w ≤ X) :
    PB X 8 (d6rh c w)⁻¹ := by
  have pc := PB.base hX hc.le hc'
  have pw := PB.base hX (by linarith) hw'
  have p12 : PB X 4 12 := PB.const hX 4 (by norm_num) (by norm_num)
  have ppi : PB X 2 Real.pi := PB.const hX 2 Real.pi_pos.le (by linarith [Real.pi_le_four])
  unfold d6rh
  rw [one_div, inv_inv]
  exact ((p12.mul ppi).mul (pc.add pw)).mono (by norm_num)

end GlobalTheory.SplitConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.QuotientBoundOfKillDetectConstantRoom
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.QbridgeOfNumGood
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM

theorem ndeg_eq_places {K : Type} [Field K] [NumberField K] (N : MLine K) (hN : N.Good)
    (hc : ∀ σ : K →+* ℂ, N.n ((starRingEnd ℂ).comp σ) = N.n σ) :
    ((∑ᶠ w : HeightOneSpectrum (𝓞 K), (-(FractionalIdeal.count K w N.I : ℝ)) * logN w) -
      ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (N.n σ.embedding)) / (Module.finrank ℚ K : ℝ) = N.ndeg := by
  have h1 : (∑ᶠ w : HeightOneSpectrum (𝓞 K), (-(FractionalIdeal.count K w N.I : ℝ)) * logN w) =
      -Real.log ((FractionalIdeal.absNorm N.I : ℚ) : ℝ) := by
    simp_rw [neg_mul]
    rw [finsum_neg_distrib, PlaceDegreeSums.sum_count_log_norm _ hN.1]
  have h2 : ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (N.n σ.embedding) =
      ∑ τ : K →+* ℂ, Real.log (N.n τ) := by
    rw [PlaceDegreeSums.sum_infinite_places_mult (fun σ => Real.log (N.n σ.embedding))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rcases InfinitePlace.embedding_mk_eq τ with h | h
    · rw [h]
    · rw [h]
      exact congrArg Real.log (hc τ)
  rw [h1, h2, MLine.ndeg, MLine.deg]

theorem qbridge_of_numGood : ∀ (D : D7) (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Ch Ah Cc Ac Tt cc : ℝ) (be : HeightOneSpectrum (𝓞 B.KO) → ℝ) (Carch Bdeg : ℝ), Submodule.IsFullLattice B.KO (B.Mlat j ka) → (∀ la, 0 ≤ be la) → (Function.support be).Finite → (∑ᶠ la, be la * WeightFamilies.lnN B la) / WeightFamilies.degO B ≤ WeightFamilies.PPv D large₂ Cc Ac * ka.size → (∀ τ F, B.supN j ka ((starRingEnd ℂ).comp τ) F = B.supN j ka τ F) → WeightFamilies.PPv D large₂ Ch Ah * ka.size + Carch + Bdeg + Real.log (WeightFamilies.rhoP B CR Tt cc j ka : ℝ) / 2 ≤ WeightFamilies.PPv D large₂ Cc Ac * ka.size → (∀ F : B.Cusp j ka, F ∉ WeightFamilies.MggK B CR Tt cc j ka → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra B.KO K₁) (φ : B.Cusp j ka →ₗ[B.KO] K₁), WeightFamilies.MggK B CR Tt cc j ka ≤ LinearMap.ker φ ∧ φ F ≠ 0 ∧ NumGood (B.Mlat j ka : Set (B.Cusp j ka)) (B.supN j ka) be Carch Bdeg K₁ φ) → QBridgeAt large₂ B j ka CR Ch Ah Cc Ac Tt cc := by
  intro D large₂ B j ka CR Ch Ah Cc Ac Tt cc be Carch Bdeg hlat hbe hbefin hbesum hconj hroom hdet
  classical
  obtain ⟨K₁, _, _, _, ρ, g, cf, hfam, hcf, hker, hdim⟩ := kerCore_holds B.KO (B.Cusp j ka)
    (WeightFamilies.MggK B CR Tt cc j ka)
    (fun K₁ _ _ _ φ => WeightFamilies.MggK B CR Tt cc j ka ≤ LinearMap.ker φ ∧
      NumGood (B.Mlat j ka : Set (B.Cusp j ka)) (B.supN j ka) be Carch Bdeg K₁ φ)
    (fun _ _ _ _ _ h => h.1)
    (fun v hv => by
      by_contra hn
      obtain ⟨K₁, _, _, _, φ, h1, h2, h3⟩ := hdet v hn
      exact h2 (hv K₁ φ ⟨h1, h3⟩))
    (fun K' K₁ _ _ _ _ _ _ e f hf => ⟨e.toLinearMap.comp f, ⟨fun v hv => by
      have := LinearMap.mem_ker.1 (hf.1 hv)
      simp [LinearMap.mem_ker, this], GlobalTheory.T.isNumberFieldFunctionalBounded_comp_extension _ _ _ _ _ _ _ K' K₁ e f hf.2⟩, fun _ => rfl⟩)
  let _ := hlat
  have hrk : WeightFamilies.rhoP B CR Tt cc j ka + Module.finrank B.KO (WeightFamilies.MggK B CR Tt cc j ka) =
      Module.finrank B.KO (B.Cusp j ka) :=
    LocalQuotientRank.rank_QuotMW (K := B.KO) (B.Mlat j ka) hlat.fg (Submodule.IsFullLattice.span_eq_top (A := B.KO) (M := B.Mlat j ka)) (WeightFamilies.MggK B CR Tt cc j ka)
  have hρ : ρ = WeightFamilies.rhoP B CR Tt cc j ka := by omega
  subst hρ
  choose N hG hd hc hint harch using fun i => (hfam i).2
  refine ⟨K₁, inferInstance, inferInstance, inferInstance, cf, be,
    fun i w => -(FractionalIdeal.count K₁ w (N i).I : ℝ), fun i σ => Real.log ((N i).n σ.embedding), Carch, Bdeg,
    hker, hbe, hbefin, hbesum, fun i => ?_, fun la w hw i F hF hne => ?_, hconj, fun σ i F hF hne => ?_,
    fun i => ?_, hroom⟩
  · refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (N i).I)).subset fun w hw h => hw ?_
    simp [h]
  · rw [hcf] at hne ⊢
    exact (hint i la w hw F hF hne).trans_eq (sub_eq_add_neg _ _)
  · rw [hcf] at hne ⊢
    rw [← InfinitePlace.norm_embedding_eq]
    exact harch i σ.embedding F hF hne
  · rw [ndeg_eq_places (N i) (hG i) (hc i)]
    exact hd i

end GlobalTheory.ArcCM
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM

theorem room_of_bounds {z k Ch Ah C₀ A₀ Cd Ad Carch Bdeg lρ beSum : ℝ} (hz : 1 ≤ z) (hk : 0 ≤ k) (hCh : 0 ≤ Ch)
    (hC₀ : 0 ≤ C₀) (hCd : 0 ≤ Cd) (h1 : Carch ≤ C₀ * z ^ A₀ * k) (h2 : Bdeg ≤ C₀ * z ^ A₀ * k)
    (h3 : lρ ≤ Cd * z ^ Ad * k) (h4 : beSum ≤ C₀ * z ^ A₀ * k) :
    Ch * z ^ Ah * k + Carch + Bdeg + lρ / 2 ≤ (Ch + 3 * C₀ + Cd) * z ^ (max Ah (max A₀ Ad)) * k ∧
      beSum ≤ (Ch + 3 * C₀ + Cd) * z ^ (max Ah (max A₀ Ad)) * k := by
  set Ac := max Ah (max A₀ Ad)
  have hmono : ∀ A, A ≤ Ac → z ^ A ≤ z ^ Ac := fun A hA => Real.rpow_le_rpow_of_exponent_le hz hA
  have hAh : z ^ Ah ≤ z ^ Ac := hmono _ (le_max_left _ _)
  have hA₀ : z ^ A₀ ≤ z ^ Ac := hmono _ (le_trans (le_max_left _ _) (le_max_right _ _))
  have hAd : z ^ Ad ≤ z ^ Ac := hmono _ (le_trans (le_max_right _ _) (le_max_right _ _))
  have hzA : 0 ≤ z ^ Ac := Real.rpow_nonneg (by linarith) _
  have e0 : Ch * z ^ Ah * k ≤ Ch * z ^ Ac * k :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAh hCh) hk
  have e1 : C₀ * z ^ A₀ * k ≤ C₀ * z ^ Ac * k :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA₀ hC₀) hk
  have e2 : Cd * z ^ Ad * k ≤ Cd * z ^ Ac * k :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAd hCd) hk
  have p0 : 0 ≤ Ch * z ^ Ac * k := mul_nonneg (mul_nonneg hCh hzA) hk
  have p1 : 0 ≤ C₀ * z ^ Ac * k := mul_nonneg (mul_nonneg hC₀ hzA) hk
  have p2 : 0 ≤ Cd * z ^ Ac * k := mul_nonneg (mul_nonneg hCd hzA) hk
  have e : (Ch + 3 * C₀ + Cd) * z ^ Ac * k = Ch * z ^ Ac * k + 3 * (C₀ * z ^ Ac * k) + Cd * z ^ Ac * k := by ring
  rw [e]
  constructor <;> linarith

theorem log₂ {D : D7} (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ)
    (hlat : Submodule.IsLattice B.KO (B.Mlat j ka)) :
    Real.log (WeightFamilies.rhoP B CR Tt cc j ka : ℝ) ≤ Real.log (Module.finrank B.KO (B.Cusp j ka) : ℝ) := by
  have hrk := LocalQuotientRank.rank_quot (F := B.KO) (B.Mlat j ka) hlat.fg
    (WeightFamilies.MggK B CR Tt cc j ka)
  have hdim : WeightFamilies.rhoP B CR Tt cc j ka ≤ Module.finrank B.KO (B.Cusp j ka) :=
    (hrk ▸ Nat.le_add_right _ _).trans (Submodule.finrank_le _)
  rcases Nat.eq_zero_or_pos (WeightFamilies.rhoP B CR Tt cc j ka) with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hdim)

theorem qat_of_kill_detect : Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (large₂ : SizeData₂ D) (Ck Ch Ah C₀ A₀ Cd Ad : ℝ), GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m → Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB h) j ka → KillQ h j ka CR Tt cc → DetectQ h j ka CR Tt cc → 1 ≤ zBase large₂ → 0 ≤ C₀ → 0 ≤ Cd → RoomAt large₂ j ka CR Tt cc C₀ A₀ →
    Real.log (@Module.finrank T.Q.c.F ((recB h).Cusp j ka) _
      ((recB h).acgC j ka).toAddCommMonoid ((recB h).modC j ka) : ℝ) ≤
      WeightFamilies.PPv D large₂ Cd Ad * ka.size →
    Formalism.MainNotions.Gaps.EtaleWeightGaps.QAt large₂ (recB h) j ka CR Ck Ch Ah (Ch + 3 * C₀ + Cd) (max Ah (max A₀ Ad)) Tt cc := by
  intro hK D T h j ka CR Tt cc large₂ Ck Ch Ah C₀ A₀ Cd Ad hG hj hjm hlat hkill hdet hz hC₀ hCd hroom hdim
  intro hCR hOb hn hlast hsize hT hc hTc
  have hzpos : 0 < zBase large₂ := by linarith
  have hCh : 0 ≤ Ch := by
    have h1 : (1 : ℝ) ≤ WeightFamilies.degO (recB h) := by
      unfold WeightFamilies.degO
      exact_mod_cast Module.finrank_pos
    have h2 : 0 ≤ Ch * zBase large₂ ^ Ah := (Real.log_nonneg h1).trans hOb.1
    exact nonneg_of_mul_nonneg_left h2 (Real.rpow_pos_of_pos hzpos _)
  have hA : (GlobalTheory.ArcCM.absA (T.Q.Dw j) (wtA ka) : ℝ) ≤ ka.size := by
    have h1 := absA_add_le_size T h.pins hj ka
    have h2 : (0 : ℝ) ≤ (fdeg D.host.E : ℝ) * ka.n := by positivity
    linarith
  have hk : (0 : ℝ) ≤ ka.size := (Nat.cast_nonneg _).trans hA
  have hnpos : 0 < nAt D j ka CR Tt cc := Nat.succ_pos _
  obtain ⟨hfin, hsum⟩ := beSum_holds D.host.E (recB h).KO (nAt D j ka CR Tt cc)
    (GlobalTheory.ArcCM.absA (T.Q.Dw j) (wtA ka)) hnpos
  have hP₀ : 0 ≤ C₀ * zBase large₂ ^ A₀ := mul_nonneg hC₀ (Real.rpow_pos_of_pos hzpos _).le
  have hsum' := hsum.trans ((mul_le_mul_of_nonneg_right hroom.2.2 (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hA hP₀))
  have hlog := log₂ (recB h) j ka CR Tt cc hlat.toIsLattice
  obtain ⟨hr1, hr2⟩ := room_of_bounds (Ah := Ah) hz hk hCh hC₀ hCd hroom.1 hroom.2.1 (hlog.trans hdim) hsum'
  refine qat_of_bridge' large₂ (recB h) j ka CR Ck Ch Ah _ _ Tt cc hlat
    (qbridge_of_numGood D large₂ (recB h) j ka CR Ch Ah _ _ Tt cc
      (beOf D.host.E (nAt D j ka CR Tt cc) (GlobalTheory.ArcCM.absA (T.Q.Dw j) (wtA ka)))
      (CarchAt D j ka CR Tt cc) (BdegAt large₂ j ka CR Tt cc) hlat (fun la => ?_) hfin hr2
      (recB_supN_conj h j ka) hr1 fun F hF => ?_) hCR hOb hn hlast hsize hT hc hTc
  · unfold beOf
    positivity
  · by_contra hno
    refine hF (hdet F fun K₁ i1 i2 i3 d hd => ?_)
    by_contra hne
    have hle : cutR T.C j ka ≤ sec (T.Q.Xo j) T.Q.c (wtA ka) ka.n :=
      (cutR_le T.C j ka).trans (cusp_le_sec _ _ _ _ _)
    obtain ⟨⟨ψ, hψ⟩, hdeg⟩ :=
      cfOf_linear_and_degree hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d (wtA ka) ka.n
    let φ := ψ.comp (Submodule.inclusion hle)
    have hφ : ∀ G : (recB h).Cusp j ka, φ G = cfOf d.yF d.μ d.jj G.1 := fun G => hψ _
    refine hno ⟨K₁, i1, i2, i3, φ, fun G hGm => ?_, ?_, ?_⟩
    · exact (hφ G).trans (hkill K₁ d hd G hGm)
    · exact fun h0 => hne ((hφ F).symm.trans h0)
    · obtain ⟨hstd, ⟨s⟩⟩ := hd
      obtain ⟨hgood, -, -, -, -, hf, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
      obtain ⟨hpq, hr, -⟩ := hnum j hj
      have hLa := RunNum.one_le_LaAt D j ka CR Tt cc
      have hc : 0 ≤ pDeg large₂.logOm + (1 / 2) * Real.log (LaAt D j ka CR Tt cc) := by
        have := Real.log_nonneg hLa
        unfold pDeg
        positivity
      have hμ := hdeg F.1 (hle F.2) hne
      obtain ⟨hN, hNd⟩ := valLine_ndeg_le hK _ _ _ _ _ K₁ _ _ _ _ _ _ _ s large₂.logOm d.μ ka.n hLa
        (lamDegSt_logOm₂ hK D T large₂ h.pins)
      refine ⟨s.valLine d.μ ka.n, hN, hNd.trans ?_,
        GlobalTheory.T.cmValueLine_length_conj_eq hK _ _ _ _ _ K₁ _ _ _ _ _ _ _ s _ _, ?_, ?_⟩
      · unfold BdegAt
        refine mul_le_mul_of_nonneg_left ?_ hc
        rw [hμ, hf, hpq, Nat.mul_div_cancel_left _ two_pos]
        push_cast
        exact RunNum.absA_add_le_size T h.pins j hj ka
      · intro la w hw G hGm hne'
        rw [hφ] at hne' ⊢
        exact GlobalTheory.T.cmArcDatum_functional_finite_integrality_bound hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d _ _ _ s
          (modelsAt_of_good_level hK _ _ _ _ _ _ (hpq ▸ hr) hgood) hstd hLa la w hw (wtA ka) ka.n G.1
          ⟨hle G.2, fun v hv => hGm la v hv⟩ hne'
      · intro em G _ hne'
        have hpos : 0 < (recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) G := by
          refine lt_of_le_of_ne ((recB h).supN_nonneg j ka _ G) fun h0 => hne' ?_
          rw [((recB h).supN_eq_zero j ka _ G).1 h0.symm]
          exact map_zero _
        have harch := RunNum.arch_all hK h j ka CR Tt cc hG hj K₁ d hstd s em G
        rw [hφ] at hne' ⊢
        have hnorm : 0 < ‖em (cfOf d.yF d.μ d.jj G.1)‖ := norm_pos_iff.2 ((map_ne_zero em).2 hne')
        have hlog := Real.log_le_log (mul_pos hnorm (hN.2 em)) harch
        rwa [Real.log_mul hnorm.ne' (hN.2 em).ne', Real.log_mul hpos.ne' (Real.exp_pos _).ne',
          Real.log_exp] at hlog

end GlobalTheory.ArcCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExtendEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcFunctionalVanishesLowFourierJacobi
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcFunctionalVanishesLowFourierJacobi
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj hiding Unf GoodEmb
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcKill

theorem eq_zero_of_eval_off {σ : Type} {P Q : MvPolynomial σ ℂ} (hQ : Q ≠ 0)
    (h : ∀ x, MvPolynomial.eval x Q ≠ 0 → MvPolynomial.eval x P = 0) : P = 0 := by
  have : P * Q = 0 := MvPolynomial.funext fun x => by
    rw [map_mul, map_zero]
    by_cases hx : MvPolynomial.eval x Q = 0
    · rw [hx, mul_zero]
    · rw [h x hx, zero_mul]
  exact (mul_eq_zero.1 this).resolve_right hQ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem coeff_eq_zero_of_invBl (S : Finset (ArcLt Dw →₀ ℕ)) (f : (ArcLt Dw →₀ ℕ) → ℂ)
    (h : ∀ x : ArcLt Dw → ℂ, InvBl x → ∑ mo ∈ S, f mo * ∏ v ∈ mo.support, x v ^ mo v = 0) : ∀ mo ∈ S, f mo = 0 := by
  classical
  let Q : MvPolynomial (ArcLt Dw) ℂ := ∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) =>
    (MvPolynomial.X (⟨τ, (i, k)⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) ℂ)).det
  have hQe : ∀ x : ArcLt Dw → ℂ, MvPolynomial.eval x Q ≠ 0 ↔ InvBl x := fun x => by
    rw [map_prod, Finset.prod_ne_zero_iff]
    refine forall_congr' fun τ => ?_
    have : (MvPolynomial.eval x).mapMatrix (Matrix.of fun i k : Fin (Dw.mult τ) =>
        (MvPolynomial.X (⟨τ, (i, k)⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) ℂ)) =
        Matrix.of fun i k : Fin (Dw.mult τ) => x ⟨τ, (i, k)⟩ := by
      ext i k : 2
      simp
    rw [RingHom.map_det, this]
    simp
  have hone : InvBl (Dw := Dw) fun v => (1 : Matrix (Fin (Dw.mult v.1)) (Fin (Dw.mult v.1)) ℂ) v.2.1 v.2.2 :=
    fun τ => (Matrix.det_one (n := Fin (Dw.mult τ)) (R := ℂ)).trans_ne one_ne_zero
  have hQ : Q ≠ 0 := fun h0 => (hQe _).2 hone (by rw [h0, map_zero])
  have hP : ∑ mo ∈ S, MvPolynomial.monomial mo (f mo) = 0 := eq_zero_of_eval_off hQ fun x hx => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← h x ((hQe x).1 hx)]
    exact Finset.sum_congr rfl fun mo _ => MvPolynomial.eval_monomial
  intro mo hmo
  have := congrArg (AddMonoidAlgebra.coeff · mo) hP
  rw [MvPolynomial.coeff_sum] at this
  simpa [MvPolynomial.coeff_monomial, hmo] using this

theorem cfOf_eq_zero : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (em : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (em.comp (algebraMap c.F K₁)) r) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Fam n' La c₁ d → GoodEmb c (em.comp (algebraMap c.F K₁)) → IsUnf U → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ F ∈ sec Xo c a' n, (∀ k, rdU U F k ∈ (U.X k).SSgt (laU U a' n k) c₁) → cfOf d.yF d.μ d.jj F = 0 := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ em r U a' n hfam hgood hunf hdom htv F hF hS
  obtain ⟨⟨hover, -, hpush⟩, ⟨s⟩⟩ := hfam
  obtain ⟨k, ξ', fr, u₁, κ, hu, hiso, -, hfr, hmain⟩ := GlobalTheory.T.arcDatum_sectionValue_coeff_eq_fourierJacobi hK.laws hK.laws2 hK.ubc hK.laws5 hK.n5
    E H Dw l Xo c K₁ d em r U s.ξ s.ν₀ a' n (hK.ev E H Dw l Xo c) hgood hunf hover s.tan hpush s.rk s.ξ_ne s.beta
    hdom htv
  have hν : ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re ≤ c₁ := by
    have h1 := TraceFormIndependence.trace_re (U.X k) s.ν₀
    have h2 := s.tr
    rw [h1, ← Finset.mul_sum] at h2
    linarith
  have h0 : ∀ x, InvBl x → ajAt d em F x = 0 := fun x hx => by
    have := hmain F hF (hS k).1.1 x hx
    rw [(hS k).2 ξ' hiso _ hν _ (hfr x hx), mul_zero] at this
    exact (mul_eq_zero.1 this).resolve_right (zpow_ne_zero _ hu)
  unfold cfOf
  by_cases hmo : d.μ ∈ (arcNum (evR Xo c F d.yF)).support
  · exact (map_eq_zero em).1 (coeff_eq_zero_of_invBl _
      (fun mo => em (((arcNum (evR Xo c F d.yF)).coeff mo).coeff d.jj)) h0 _ hmo)
  · rw [MvPolynomial.notMem_support_iff.1 hmo]
    rfl

end GlobalTheory.ArcKill
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcFunctionalVanishesLowFourierJacobiStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj hiding Unf GoodEmb
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmArcFunctional_vanishes_low_fourierJacobi : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (em : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (em.comp (algebraMap c.F K₁)) r) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Fam n' La c₁ d → GoodEmb c (em.comp (algebraMap c.F K₁)) → IsUnf U → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ F ∈ sec Xo c a' n, (∀ k, rdU U F k ∈ (U.X k).SSgt (laU U a' n k) c₁) → cfOf d.yF d.μ d.jj F = 0 := by
  first | exact @GlobalTheory.ArcKill.cfOf_eq_zero | exact GlobalTheory.ArcKill.cfOf_eq_zero | (intros; apply GlobalTheory.ArcKill.cfOf_eq_zero <;> assumption)
end
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM

theorem exists_extend_embedding {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K] [Algebra F K]
    (σ : F →+* ℂ) : ∃ em : K →+* ℂ, em.comp (algebraMap F K) = σ := by
  letI : Algebra F ℂ := σ.toAlgebra
  haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  let f : K →ₐ[F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨f.toRingHom, RingHom.ext fun x => f.commutes x⟩

theorem killQ_of_gamAt : Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m → KillQ h j ka CR Tt cc := by
  intro hK D T h j ka CR Tt cc hG hj hm K₁ _ _ _ d hd F hF
  have key : ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
      (∀ k, rdU (T.U j σ) F.1 k ∈ ((T.U j σ).X k).SSgt (laU (T.U j σ) (wtA ka) ka.n k) (WeightFamilies.c1 D CR Tt cc j)) →
      cfOf d.yF d.μ d.jj F.1 = 0 := by
    intro σ hσ hr
    obtain ⟨em, rfl⟩ := exists_extend_embedding (K := K₁) σ
    have hc : F.1 ∈ T.C j ka := cutR_le T.C j ka F.2
    exact GlobalTheory.T.cmArcFunctional_vanishes_low_fourierJacobi hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d _ _ _ em _
      (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) (wtA ka) ka.n hd hσ (h.unf j hj _ hσ) (dom_wtA ka)
      (GlobalTheory.TransvPrinc.transvIn_of_hasPrinc _ _ _ _ (T.Q.Xo j) T.Q.c _ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) (wtA ka) ka.n
        (hG j hj _ hσ) (h.chiTriv j hj _ hσ _ _ (dom_wtA ka))) F.1 hc.1 hr
  exact key T.σ₀ T.good_σ₀ ((GlobalTheory.T.mem_forms_low_coeffs_vanish_iff_fourierJacobi D T h j ka CR Tt cc hj hm F).2.1 hF)

end GlobalTheory.ArcCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPolynomialBoundRunConstantsDegreeFourStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPolynomialBoundRunConstantsDegreeFour
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LogLeSelf
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM.Room

theorem assemble (K M P z s lc lL lr lR lo ld ln : ℝ) (hz : 1 ≤ z) (hP : z ≤ P) (hK : 1 ≤ K) (hM : 0 ≤ M)
    (hs : 1 ≤ s) (hc : lc ≤ K * z) (hL : lL ≤ M * P) (hr : lr ≤ K * z) (hR : lR ≤ z) (ho : lo ≤ K * z)
    (hd : ld ≤ K * z) (hn : ln ≤ M * P) :
    4 * Real.pi + (lc / 2 + lL + lr + lR) * s ≤ (17 + 2 * K + M) * P * s ∧
    ((1 + lo) / 2 + (1 / 2) * lL) * s ≤ (17 + 2 * K + M) * P * s ∧
    ld + ln ≤ (17 + 2 * K + M) * P := by
  have hKz : K * z ≤ K * P := mul_le_mul_of_nonneg_left hP (by linarith)
  have hKP : 0 ≤ K * P := by nlinarith
  have hMP : 0 ≤ M * P := mul_nonneg hM (by linarith)
  have hpi := Real.pi_le_four
  refine ⟨?_, ?_, ?_⟩
  · have h1 : lc / 2 + lL + lr + lR ≤ (1 + 2 * K + M) * P := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ s)
    have h3 : 1 ≤ P * s := by nlinarith
    nlinarith
  · refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    nlinarith
  · nlinarith

theorem log_le_self' {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ x := Real.log_le_self hx

end GlobalTheory.ArcCM.Room
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj hiding Unf GoodEmb
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.SplitConst

theorem constants_bounded_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 g NA NC : ℕ) (c₁ w Z : ℝ), 3 ≤ r → 1 ≤ p0 → p0 ≤ r → 1 ≤ g → 1 ≤ NA → 1 ≤ NC → 0 < c₁ → 1 ≤ w → 1 ≤ Z → (fdeg E : ℝ) ≤ Z → (r : ℝ) ≤ Z → Real.log (dE E) ≤ Z → Real.log g ≤ Z → Real.log NA ≤ Z → Real.log NC ≤ Z → Real.log c₁ ≤ Z → Real.log w ≤ Z → Real.log (nQ E r g NA NC c₁ w) ≤ 200 * Z ^ 2 ∧ Real.log (LaQ E r p0 g NA NC c₁ w) ≤ 200 * Z ^ 2 := by
  intro E _ _ _ r p0 g NA NC c w Z hr hp hpr hg hNA hNC hc hw hZ hfZ hrZ hdZ hgZ hNAZ hNCZ hcZ hwZ
  have hZX : Z + 1 ≤ Real.exp Z := Real.add_one_le_exp Z
  set X := Real.exp Z with hXdef
  have hX : 2 ≤ X := by linarith
  have le_of_log : ∀ a : ℝ, 0 < a → Real.log a ≤ Z → a ≤ X := fun a ha h => (Real.log_le_iff_le_exp ha).1 h
  have hd : 1 ≤ dE E := by
    unfold dE
    have := NumberField.discr_ne_zero E
    have h2 : (1 : ℤ) ≤ |NumberField.discr E| := Int.one_le_abs this
    exact_mod_cast h2
  have hn : 2 ≤ Module.finrank ℚ E := by
    have h1 := (letI : Module.Free (NumberField.maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (NumberField.maximalRealSubfield E) E)
    have h2 : Module.finrank (NumberField.maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
    have h3 : 0 < Module.finrank ℚ (NumberField.maximalRealSubfield E) := Module.finrank_pos
    rw [h2] at h1
    omega
  have hf : (1 : ℝ) ≤ fdeg E := by
    have : 1 ≤ fdeg E := by unfold fdeg; omega
    exact_mod_cast this
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hNA1 : (1 : ℝ) ≤ NA := by exact_mod_cast hNA
  have hNC1 : (1 : ℝ) ≤ NC := by exact_mod_cast hNC
  have hd' := le_of_log _ (by linarith) hdZ
  have hg' := le_of_log _ (by linarith) hgZ
  have hNA' := le_of_log _ (by linarith) hNAZ
  have hNC' := le_of_log _ (by linarith) hNCZ
  have hc' := le_of_log _ hc hcZ
  have hw' := le_of_log _ (by linarith) hwZ
  have hf' : (fdeg E : ℝ) ≤ X := by linarith
  have pe := isBoundedByPowerOfAtLeastTwo_inv_d4ep0 hX hg1 hd hf hNA1 hNC1 hc hw hg' hd' hf' hNA' hNC' hc' hw'
  have ph := rh_inv hX hc hw hc' hw'
  have pd := PB.base hX (by linarith) hd'
  have pf := PB.base hX (by linarith) hf'
  have pNA := PB.base hX (by linarith) hNA'
  have pNC := PB.base hX (by linarith) hNC'
  have pr : PB X 1 ((r - 2 : ℕ) : ℝ) := by
    refine PB.base hX (by positivity) ?_
    have : ((r - 2 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 2
    linarith
  have prd : PB X 1 (rdE E) :=
    pd.of_le (Real.rpow_nonneg (by linarith) _) (rpow_le_self hd (by
      have : 1 ≤ Module.finrank ℚ E := by omega
      exact_mod_cast this))
  have p1 : PB X 0 1 := PB.const hX 0 (by norm_num) (by norm_num)
  have p2 : PB X 1 2 := PB.const hX 1 (by norm_num) (by norm_num)
  have p4 : PB X 2 4 := PB.const hX 2 (by norm_num) (by norm_num)
  have p40 : PB X 6 40 := PB.const hX 6 (by norm_num) (by norm_num)
  have p1000 : PB X 10 1000 := PB.const hX 10 (by norm_num) (by norm_num)
  set ep := flowEpsilonBound g (dE E) (fdeg E) NA NC c w
  set rh := d6rh c w
  have hZ2 : Z ≤ Z ^ 2 := by nlinarith
  constructor
  · have pm := (((pf.mul (((p2.mul pf).mul pr).pow 3)).mul pd).mul pNA).mul ((pNC.pow 2).mul prd |>.mul pe).sqrt
    have py := (p1000.mul pm).mul ph
    have hy : 1000 * frameIndexBound r (fdeg E) (dE E) (rdE E) NA NC ep / rh =
        1000 * ((fdeg E : ℝ) * (2 * (fdeg E : ℝ) * ((r - 2 : ℕ) : ℝ)) ^ 3 * dE E * NA * √((NC : ℝ) ^ 2 * rdE E * ep⁻¹)) * rh⁻¹ := by
      unfold frameIndexBound
      rw [div_eq_mul_inv, div_eq_mul_inv, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]
    rw [← hy] at py
    have pn : PB X 100 (nQ E r g NA NC c w : ℝ) := by
      refine (((py.add p1).add p1).mono (by norm_num)).of_le (by positivity) ?_
      unfold nQ
      push_cast
      have := Nat.ceil_lt_add_one py.2.1
      linarith
    have := pn.log_le (by unfold nQ; positivity)
    push_cast at this
    nlinarith
  · have pmu := ((p4.mul ((pf.mul pr).pow 3)).mul pd).mul pe.sqrt
    have pb := ((p2.mul (((p4.mul pr.sqrt).mul pmu).mul (p40.mul ph))).mono (j := 100) (by norm_num)).pow (2 * p0 - 1)
    have hy : d6La r p0 (fdeg E) (dE E) ep rh =
        (2 * (4 * √((r - 2 : ℕ) : ℝ) * (4 * ((fdeg E : ℝ) * ((r - 2 : ℕ) : ℝ)) ^ 3 * dE E * √(ep⁻¹)) * (40 * rh⁻¹))) ^
          (2 * p0 - 1) := by
      unfold d6La ReciprocityTheory.MultiplicativeHeights.approxR d5mu
      rw [div_eq_mul_inv _ (rh / 40), inv_div, div_eq_mul_inv 40, div_eq_mul_inv, ← Real.sqrt_inv]
    rw [← hy] at pb
    have pL : PB X (100 * (2 * p0 - 1)) (LaQ E r p0 g NA NC c w) := by
      unfold LaQ
      rcases max_choice (1 : ℝ) _ with h | h <;> rw [h]
      · exact p1.mono (Nat.zero_le _)
      · exact pb
    have h1 := pL.log_le (lt_of_lt_of_le one_pos (le_max_left _ _))
    have h2 : ((100 * (2 * p0 - 1) : ℕ) : ℝ) ≤ 200 * r := by
      have : 100 * (2 * p0 - 1) ≤ 200 * r := by omega
      exact_mod_cast this
    have h3 : ((100 * (2 * p0 - 1) : ℕ) : ℝ) * Z ≤ (200 * Z) * Z :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith

theorem constants_bounded_four : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 g NA NC : ℕ) (c₁ w Z : ℝ), 3 ≤ r → 1 ≤ p0 → p0 ≤ r → 1 ≤ g → 1 ≤ NA → 1 ≤ NC → 0 < c₁ → 1 ≤ w → 1 ≤ Z → (fdeg E : ℝ) ≤ Z → (r : ℝ) ≤ Z → Real.log (dE E) ≤ Z → Real.log g ≤ Z → Real.log NA ≤ Z → Real.log NC ≤ Z → Real.log c₁ ≤ Z → Real.log w ≤ Z → Real.log (nQ E r g NA NC c₁ w) ≤ 200 * Z ^ (4 : ℝ) ∧ Real.log (LaQ E r p0 g NA NC c₁ w) ≤ 200 * Z ^ (4 : ℝ) := by
  intro E _ _ _ r p0 g NA NC c w Z hr hp hpr hg hNA hNC hc hw hZ hfZ hrZ hdZ hgZ hNAZ hNCZ hcZ hwZ
  obtain ⟨h1, h2⟩ := constants_bounded_sq E r p0 g NA NC c w Z hr hp hpr hg hNA hNC hc hw hZ hfZ hrZ hdZ hgZ
    hNAZ hNCZ hcZ hwZ
  have h3 : Z ^ 2 ≤ Z ^ (4 : ℝ) := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
  constructor <;> linarith

end GlobalTheory.SplitConst

end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM.Room


set_option maxHeartbeats 1000000 in
theorem room_four : ∃ C₀ : ℝ → ℝ → ℝ → ℝ, (∀ a b c, 0 ≤ C₀ a b c) ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CA CR Ck Tt cc : ℝ), WeightAlgebra.ParA large₂ CA → Real.log (Ideal.absNorm D.host.ccK) ≤ large₂.sc.L → InR D j → j < D.R.m → 3 ≤ D.R.r → 0 ≤ CR → ka.size ≤ Ck * (D.R.k : ℝ) * (D.R.f : ℝ) * large₂.sc.b → 0 < Tt → 0 < cc → Tt * cc ≤ 1 → 1 ≤ zBase large₂ ∧ RoomAt large₂ j ka CR Tt cc (C₀ CA CR Ck) 4 := by
  set C : ℝ := 200 with hCdef
  set A : ℝ := 4 with hAdef
  have hC : 0 ≤ C := by norm_num [hCdef]
  have hA : 1 ≤ A := by norm_num [hAdef]
  have H := GlobalTheory.SplitConst.constants_bounded_four
  rw [← hCdef, ← hAdef] at H
  refine ⟨fun a b c => 17 + 2 * (20 + |a| + |b| * |a| + |c|) + C * (20 + |a| + |b| * |a| + |c|) ^ A,
    fun a b c => by positivity, ?_⟩
  intro D large₂ j ka CA CR Ck Tt cc hpar hNC hj hjm hr3 hCR hka hT hcc hTc
  obtain ⟨-, -, hdE, -, hg, -, hOm, -, -, -⟩ := hpar
  have : IsCMField D.host.E := D.host.isCMField_hostE
  set K : ℝ := 20 + |CA| + |CR| * |CA| + |Ck| with hKdef
  have ha0 := abs_nonneg CA
  have hb0 := abs_nonneg CR
  have hc0 := abs_nonneg Ck
  have hab0 : 0 ≤ |CR| * |CA| := mul_nonneg hb0 ha0
  have hK : 20 ≤ K := by rw [hKdef]; linarith
  have hL1 : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hfN : 1 ≤ D.R.f := by
    have hn : 1 ≤ D.R.n := D.R.ord_pos
    unfold Ranks.f
    have := Nat.one_le_two_pow (n := D.R.e)
    omega
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hfN
  have hr1 : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 1 ≤ D.R.r)
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hkr : (D.R.k : ℝ) ≤ D.R.r := by
    have : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
    exact_mod_cast this
  have hp1 : 1 ≤ (D.R.sigW j).2 := by unfold Ranks.sigW; simp only; omega
  have hpr : (D.R.sigW j).2 ≤ D.R.r := by unfold Ranks.sigW Ranks.r; simp only; omega
  set z : ℝ := zBase large₂ with hz
  have hzdef : z = (D.R.f : ℝ) * D.R.r * large₂.sc.L := rfl
  have hfr1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le hf1 hr1
  have hfrz : (D.R.f : ℝ) * D.R.r ≤ z := le_mul_of_one_le_right (by linarith) hL1
  have hLz : large₂.sc.L ≤ z := le_mul_of_one_le_left (by linarith) hfr1
  have hz1 : 1 ≤ z := by linarith
  have hfz : (D.R.f : ℝ) ≤ z := (le_mul_of_one_le_right (by linarith) hr1).trans hfrz
  have hrz : (D.R.r : ℝ) ≤ z := (le_mul_of_one_le_left (by linarith) hf1).trans hfrz
  have hzK : 20 * z ≤ K * z := mul_le_mul_of_nonneg_right hK (by linarith)
  have hKz : K * z = 20 * z + |CA| * z + |CR| * |CA| * z + |Ck| * z := by rw [hKdef]; ring
  have haz : 0 ≤ |CA| * z := by positivity
  have habz : 0 ≤ |CR| * |CA| * z := by positivity
  have hcz : 0 ≤ |Ck| * z := by positivity
  have hd : Real.log |((discr D.host.E : ℤ) : ℝ)| ≤ |CA| * z := by
    refine hdE.trans ?_
    rw [← hzdef]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have hd1 : (1 : ℝ) ≤ |((discr D.host.E : ℤ) : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero D.host.E)
    exact_mod_cast this
  have hd0 : 0 ≤ Real.log |((discr D.host.E : ℤ) : ℝ)| := Real.log_nonneg hd1
  have hrd0 : 0 < D.host.rdE := (rdE_pos_le D).1
  have hrd : Real.log D.host.rdE ≤ |CA| * z := by
    have h1 := logdE_eq_rd D
    have h2 : logdE D = Real.log |((discr D.host.E : ℤ) : ℝ)| := rfl
    rw [h2] at h1
    have h3 : 0 ≤ Real.log D.host.rdE := by
      exact nonneg_of_mul_nonneg_right (h1 ▸ hd0) (by linarith)
    exact (le_mul_of_one_le_left h3 (by linarith)).trans (h1 ▸ hd)
  have hfdeg : fdeg D.host.E = D.R.f := by
    unfold fdeg
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    omega
  have hg0 := (D.host.g_prime 0).one_le
  have hg1 := (D.host.g_prime 1).one_le
  have hlg : Real.log ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ≤ K * z := by
    have e0 : ((D.host.g 0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : D.host.g 0 ≠ 0)
    have e1 : ((D.host.g 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : D.host.g 1 ≠ 0)
    rw [Nat.cast_mul, Real.log_mul e0 e1]
    have := hg 0
    have := hg 1
    linarith
  have hNA : (((discr D.host.E).natAbs : ℕ) : ℝ) = |((discr D.host.E : ℤ) : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hNA1 : 1 ≤ (discr D.host.E).natAbs := Int.natAbs_pos.2 (discr_ne_zero D.host.E)
  have hNC1 : 1 ≤ Ideal.absNorm D.host.ccK :=
    Nat.one_le_iff_ne_zero.2 (fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
  have hρ1 : (1 : ℝ) ≤ WeightFamilies.rho D j := by exact_mod_cast hp1
  have hρr : (WeightFamilies.rho D j : ℝ) ≤ D.R.r := by exact_mod_cast hpr
  have hdP : (WeightFamilies.dP D j : ℝ) = 2 * D.R.f * WeightFamilies.rho D j := by unfold WeightFamilies.dP; push_cast; ring
  have hdP1 : (1 : ℝ) ≤ WeightFamilies.dP D j := by
    rw [hdP]; exact one_le_mul_of_one_le_of_one_le (by linarith) hρ1
  have hdPz : (WeightFamilies.dP D j : ℝ) ≤ 2 * z := by
    have := mul_le_mul_of_nonneg_left hρr (by linarith : (0 : ℝ) ≤ D.R.f)
    rw [hdP]; linarith
  have hRR : 0 < WeightFamilies.RRv D CR := Real.rpow_pos_of_pos hrd0 _
  have hc1 : 0 < WeightFamilies.c1 D CR Tt cc j := by unfold WeightFamilies.c1; positivity
  have hlc : Real.log (WeightFamilies.c1 D CR Tt cc j) ≤ K * z := by
    have h1 : WeightFamilies.c1 D CR Tt cc j ≤ WeightFamilies.RRv D CR * (WeightFamilies.dP D j : ℝ) ^ 2 * (WeightFamilies.rho D j : ℝ) := by
      have h0 : 0 < WeightFamilies.RRv D CR * (WeightFamilies.dP D j : ℝ) ^ 2 * (WeightFamilies.rho D j : ℝ) := by positivity
      have : WeightFamilies.c1 D CR Tt cc j =
          (WeightFamilies.RRv D CR * (WeightFamilies.dP D j : ℝ) ^ 2 * (WeightFamilies.rho D j : ℝ)) * (Tt * cc) / 2 := by
        unfold WeightFamilies.c1; ring
      rw [this]
      have := mul_le_of_le_one_right h0.le hTc
      linarith
    refine (Real.log_le_log hc1 h1).trans ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have h2 : Real.log (WeightFamilies.RRv D CR) = CR * Real.log D.host.rdE := Real.log_rpow hrd0 _
    have h3 : CR * Real.log D.host.rdE ≤ |CR| * |CA| * z := by
      rw [abs_of_nonneg hCR, mul_assoc]
      exact mul_le_mul_of_nonneg_left hrd hCR
    have h4 := log_le_self' (by linarith : (0 : ℝ) ≤ WeightFamilies.dP D j)
    have h5 := log_le_self' (by linarith : (0 : ℝ) ≤ WeightFamilies.rho D j)
    push_cast
    linarith
  have hs1 := ka.one_le_size
  have hlw : Real.log (ka.size + D.R.r) ≤ K * z := by
    have hb1 : 1 ≤ large₂.sc.b := Real.one_le_exp (by linarith)
    have h1 : Ck * (D.R.k : ℝ) * (D.R.f : ℝ) ≤ |Ck| * z := by
      rw [mul_assoc]
      refine mul_le_mul (le_abs_self _) ?_ (by positivity) hc0
      have := mul_le_mul_of_nonneg_right hkr (by linarith : (0 : ℝ) ≤ D.R.f)
      linarith
    have h2 : ka.size ≤ |Ck| * z * large₂.sc.b := hka.trans (mul_le_mul_of_nonneg_right h1 (by linarith))
    have h3 : ka.size + D.R.r ≤ (|Ck| * z + z) * large₂.sc.b := by
      have := le_mul_of_one_le_right (by linarith : (0 : ℝ) ≤ z) hb1
      linarith
    refine (Real.log_le_log (by linarith) h3).trans ?_
    rw [Real.log_mul (by positivity) (by positivity)]
    have h4 : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
    have h5 := log_le_self' (by linarith : (0 : ℝ) ≤ |Ck| * z + z)
    linarith
  obtain ⟨hn, hLa⟩ := H D.host.E D.R.r (D.R.sigW j).2 (D.host.g 0 * D.host.g 1) (discr D.host.E).natAbs
    (Ideal.absNorm D.host.ccK) (WeightFamilies.c1 D CR Tt cc j) (ka.size + D.R.r) (K * z) hr3 hp1 hpr
    (Nat.mul_pos hg0 hg1) hNA1 hNC1 hc1 (by linarith) (by linarith) (by rw [hfdeg]; linarith) (by linarith)
    (by unfold dE; linarith) hlg (by rw [hNA]; linarith) (by linarith) hlc hlw
  rw [Real.mul_rpow (by linarith) (by linarith), ← mul_assoc] at hn hLa
  have hP : z ≤ z ^ A := by
    have := Real.rpow_le_rpow_of_exponent_le hz1 hA
    rwa [Real.rpow_one] at this
  have hmax : Real.log (max 1 (WeightFamilies.c1 D CR Tt cc j)) ≤ K * z := by
    rcases max_choice 1 (WeightFamilies.c1 D CR Tt cc j) with h | h <;> rw [h]
    · rw [Real.log_one]; linarith
    · exact hlc
  have ho : |large₂.logOm| ≤ K * z := by
    have : CA * large₂.sc.L ≤ |CA| * z := mul_le_mul (le_abs_self _) hLz (by linarith) ha0
    linarith
  have hR : Real.log (D.R.r : ℝ) ≤ z := (log_le_self' (by linarith)).trans hrz
  refine ⟨hz1, ?_⟩
  exact assemble K (C * K ^ A) (z ^ A) z ka.size _ _ (Real.log D.host.rdE) _ _ _ _ hz1 hP (by linarith)
    (by positivity) hs1 hmax hLa (by linarith) hR ho (by linarith) hn

end GlobalTheory.ArcCM.Room
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_bound_runConstants_degree_four : ∃ C₀ : ℝ → ℝ → ℝ → ℝ, (∀ a b c, 0 ≤ C₀ a b c) ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CA CR Ck Tt cc : ℝ), WeightAlgebra.ParA large₂ CA → Real.log (Ideal.absNorm D.host.ccK) ≤ large₂.sc.L → InR D j → j < D.R.m → 3 ≤ D.R.r → 0 ≤ CR → ka.size ≤ Ck * (D.R.k : ℝ) * (D.R.f : ℝ) * large₂.sc.b → 0 < Tt → 0 < cc → Tt * cc ≤ 1 → 1 ≤ zBase large₂ ∧ GlobalTheory.ArcCM.RoomAt large₂ j ka CR Tt cc (C₀ CA CR Ck) 4 := by
  first | exact @GlobalTheory.ArcCM.Room.room_four | exact GlobalTheory.ArcCM.Room.room_four | (intros; apply GlobalTheory.ArcCM.Room.room_four <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RecursivePageLatticeBound
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

set_option autoImplicit false

namespace GlobalTheory.RunJoin


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem qAt_run : ∃ Cq : ℝ → ℝ → ℝ, ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → j < D.R.m → LatAt (recB h.toLawsCore) j ka → QAt large₂ (recB h.toLawsCore) j ka 7 H.CK 1 4 (Cq H.CA H.CK) 4 Tn (cc D large₂ C2 A2 7 wL) := by
  obtain ⟨C₀, hC₀, hroom⟩ := GlobalTheory.T.exists_polynomial_bound_runConstants_degree_four
  refine ⟨fun a b => 1 + 3 * C₀ a 7 b + 1041, ?_⟩
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP hjm hL hCR hO hn hlast hsz hT hc hTc
  have h3 : 3 ≤ D.R.r := le_trans (by norm_num) hP.r8
  have hcc : Real.log (Ideal.absNorm D.host.ccK) ≤ large₂.sc.L := by
    obtain ⟨Q, -, -⟩ := hP.page
    exact Q.ccK_log
  obtain ⟨hZ, hR⟩ := hroom D large₂ j ka H.CA 7 H.CK Tn (cc D large₂ C2 A2 7 wL) hP.hyp.1 hcc hj hjm h3 hCR hsz hT hc hTc
  obtain ⟨-, -, -, -, -, -, -, -, hdim, -⟩ := GlobalTheory.RunJoin.net_at_run D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP
  have hG := GlobalTheory.RunIn.gamAt_of_lawsCore D T.toCore h.toLawsCore
  have hK := GlobalTheory.T.arithmeticCMKnownTheorems_proof
  have hpp : 1041 * Zb D large₂ ^ 3 ≤ WeightFamilies.PPv D large₂ 1041 3 * ka.size := by
    have e : WeightFamilies.PPv D large₂ 1041 3 = 1041 * Zb D large₂ ^ 3 := by
      unfold WeightFamilies.PPv
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rfl
    rw [e]
    have hZ' : (1 : ℝ) ≤ Zb D large₂ := hZ
    exact le_mul_of_one_le_right (by positivity) ka.one_le_size
  have key := GlobalTheory.ArcCM.qat_of_kill_detect hK D T.toCore h.toLawsCore j ka 7 Tn
    (cc D large₂ C2 A2 7 wL) large₂ H.CK 1 4 (C₀ H.CA 7 H.CK) 4 1041 3
    hG hj hjm hL (GlobalTheory.ArcCM.killQ_of_gamAt hK D T.toCore h.toLawsCore j ka 7 Tn _ hG hj hjm)
    (GlobalTheory.ArcCM.detectQ_of_known hK D T.toCore h.toLawsCore j ka 7 Tn _ hG hj hjm h3 hT hc)
    hZ (hC₀ _ _ _) (by norm_num) hR
    (le_trans hdim hpp)
  have e4 : max (4 : ℝ) (max 4 3) = 4 := by norm_num
  rw [e4] at key
  exact key hCR hO hn hlast hsz hT hc hTc

end GlobalTheory.RunJoin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RecursivePageLatticeBoundStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.recursive_page_lattice_bound : ∃ Cq : ℝ → ℝ → ℝ, ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → j < D.R.m → LatAt (recB h.toLawsCore) j ka → QAt large₂ (recB h.toLawsCore) j ka 7 H.CK 1 4 (Cq H.CA H.CK) 4 Tn (cc D large₂ C2 A2 7 wL) := by
  first | exact @GlobalTheory.RunJoin.qAt_run | exact GlobalTheory.RunJoin.qAt_run | (intros; apply GlobalTheory.RunJoin.qAt_run <;> assumption)
end
