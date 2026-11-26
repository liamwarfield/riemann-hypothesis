module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorOfNefFibresAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfAddFormalGroupLawEvalPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivHomDivisibleByPowOfKillsPowTorsion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyWeightsBoundedDifference
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyLogSumWeightUniformlyBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyLogSumWeightUniformlyBounded
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem abs_log_sum_pow_le {D : ℕ} (v : Fin (D + 1) → ℝ) (hv : ∀ l, 0 ≤ v l) {m M : ℝ} (hm : 0 < m) (hM : 1 ≤ M)
    (hvM : ∀ l, v l ≤ M) (hvm : ∃ l, m ≤ v l) {e n : ℕ} (he : 0 < e) (hn : 1 ≤ n) :
    |((e : ℝ) * n)⁻¹ * Real.log (∑ l, v l ^ (2 * n))| ≤ Real.log (D + 1) + 2 * Real.log M + 2 * |Real.log m| := by
  obtain ⟨l₀, hl₀⟩ := hvm
  have hD : 0 ≤ Real.log (D + 1 : ℝ) := Real.log_nonneg (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
  have hM' : 0 ≤ Real.log M := Real.log_nonneg hM
  have hlo : m ^ (2 * n) ≤ ∑ l, v l ^ (2 * n) :=
    (pow_le_pow_left₀ hm.le hl₀ _).trans
      (Finset.single_le_sum (f := fun l => v l ^ (2 * n)) (fun l _ => pow_nonneg (hv l) _) (Finset.mem_univ l₀))
  have hhi : ∑ l, v l ^ (2 * n) ≤ (D + 1 : ℝ) * M ^ (2 * n) := by
    refine (Finset.sum_le_sum (g := fun _ => M ^ (2 * n)) fun l _ => pow_le_pow_left₀ (hv l) (hvM l) _).trans ?_
    simp
  have hp : 0 < m ^ (2 * n) := pow_pos hm _
  have h1 := Real.log_le_log hp hlo
  have h2 := Real.log_le_log (hp.trans_le hlo) hhi
  rw [Real.log_pow] at h1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h2
  push_cast at h1 h2
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hen : (n : ℝ) ≤ e * n := le_mul_of_one_le_left (by linarith) he'
  have ha := abs_nonneg (Real.log m)
  have hb := neg_abs_le (Real.log m)
  rw [abs_mul, abs_of_nonneg (by positivity), inv_mul_le_iff₀ (by positivity)]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hen (by positivity))
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hn') hD, mul_nonneg (sub_nonneg.2 hn') hM',
    mul_nonneg (sub_nonneg.2 hn') ha, mul_nonneg (zero_le_one.trans hn') (sub_nonneg.2 hb)]

theorem can_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∀ (σ : k →+* ℂ) (y : CxPts p σ), |((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n))| ≤ B := by
  intro k _ X _ p D hX P e x hx
  have hnn : ∀ (σ : k →+* ℂ) (y : CxPts p σ) l, 0 ≤ P.nu e 0 σ y (x l) := fun σ y l => by
    rw [← norm_val]; exact norm_nonneg _
  have hc := fun l => (GlobalTheory.HSAmp.continuous_val_and_bounded k X p D hX P e 0).2 (x l) (hx.mem l)
  choose C hC using fun l => (hc l).2
  have hlow : ∀ σ : k →+* ℂ, ∃ κ : ℝ, 0 < κ ∧ ∀ y : CxPts p σ, κ ≤ ∑ l, P.nu e 0 σ y (x l) := fun σ => by
    haveI := hX.compactSpace σ
    have hcont : Continuous fun y : CxPts p σ => ∑ l, P.nu e 0 σ y (x l) :=
      continuous_finsetSum _ fun l _ => (hc l).1 σ
    have hpos : ∀ y : CxPts p σ, 0 < ∑ l, P.nu e 0 σ y (x l) := fun y => by
      obtain ⟨l, hl⟩ := hx.cover (under y)
      exact Finset.sum_pos' (fun l _ => hnn σ y l) ⟨l, Finset.mem_univ _,
        ((GlobalTheory.HSAmp.nv_rules k X p P e 0 (x l) (hx.mem l)).2.2.2.2 (x l) (hx.mem l) σ y hl).2⟩
    rcases isEmpty_or_nonempty (CxPts p σ) with h | h
    · exact ⟨1, one_pos, fun y => h.elim y⟩
    · obtain ⟨y₀, -, hy₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hcont.continuousOn
      exact ⟨_, hpos y₀, fun y => hy₀ (Set.mem_univ y)⟩
  choose κ hκ hκ' using hlow
  haveI := hX.finite_emb
  haveI := Fintype.ofFinite (k →+* ℂ)
  have hs : 0 ≤ ∑ σ, (κ σ)⁻¹ := Finset.sum_nonneg fun σ _ => (inv_pos.2 (hκ σ)).le
  have hκ₀ : ∀ σ, (1 + ∑ σ, (κ σ)⁻¹)⁻¹ ≤ κ σ := fun σ => by
    refine inv_le_of_inv_le₀ (hκ σ) ?_
    have := Finset.single_le_sum (f := fun σ => (κ σ)⁻¹) (fun σ _ => (inv_pos.2 (hκ σ)).le) (Finset.mem_univ σ)
    linarith
  have hs' : 0 ≤ ∑ l, |C l| := Finset.sum_nonneg fun l _ => abs_nonneg _
  have hM : 1 ≤ 1 + ∑ l, |C l| := by linarith
  refine ⟨Real.log (D + 1) + 2 * Real.log (1 + ∑ l, |C l|) + 2 * |Real.log ((1 + ∑ σ, (κ σ)⁻¹)⁻¹ / (D + 1))|, ?_,
    fun n hn σ y => abs_log_sum_pow_le _ (hnn σ y) (by positivity) hM (fun l => ?_) ?_ hx.pos hn⟩
  · have h1 : 0 ≤ Real.log (D + 1 : ℝ) := Real.log_nonneg (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
    have h2 := Real.log_nonneg hM
    positivity
  · have := Finset.single_le_sum (f := fun l => |C l|) (fun l _ => abs_nonneg _) (Finset.mem_univ l)
    linarith [hC l σ y, le_abs_self (C l)]
  · obtain ⟨l, -, hl⟩ := Finset.exists_le_of_sum_le (s := Finset.univ) Finset.univ_nonempty
      (f := fun _ : Fin (D + 1) => (1 + ∑ σ, (κ σ)⁻¹)⁻¹ / (D + 1 : ℝ)) (g := fun l => P.nu e 0 σ y (x l)) (by
        refine le_trans (le_of_eq ?_) ((hκ₀ σ).trans (hκ' σ y))
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp)
    exact ⟨l, hl⟩

end GlobalTheory.HSAmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyLogSumWeightUniformlyBoundedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubiniStudy_log_sum_weight_uniformly_bounded : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∀ (σ : k →+* ℂ) (y : CxPts p σ), |((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n))| ≤ B := by
  first | exact @GlobalTheory.HSAmp.can_bound | exact GlobalTheory.HSAmp.can_bound | (intros; apply GlobalTheory.HSAmp.can_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothAtFubiniStudyLogSumWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothAtFubiniStudyLogSumWeight
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.CanSmooth

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {y : CxPts p σ}

theorem cInfAt_log {f : CxPts p σ → ℝ} (h : CInfAt f y) (hpos : 0 < f y) :
    CInfAt (fun z => Real.log (f z)) y := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have hFy : 0 < F (fun a => ev p σ W (g a) y) := h₅.eq_of_nhds ▸ hpos
  refine ⟨W, ι, inferInstance, g, fun v => Real.log (F v), O ∩ F ⁻¹' Set.Ioi 0, h₁,
    h₄.continuousOn.isOpen_inter_preimage h₂ isOpen_Ioi, ⟨h₃, hFy⟩,
    (h₄.mono Set.inter_subset_left).log fun v hv => (ne_of_gt hv.2), ?_⟩
  filter_upwards [h₅] with z hz
  rw [hz]

theorem cInfAt_sum {ι : Type} [DecidableEq ι] (s : Finset ι) {f : ι → CxPts p σ → ℝ}
    (h : ∀ l ∈ s, CInfAt (f l) y) : CInfAt (fun z => ∑ l ∈ s, f l z) y := by
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const (p := p) (0 : ℝ) y
  | insert a s ha ih =>
    have e : (fun z => ∑ l ∈ insert a s, f l z) = fun z => f a z + ∑ l ∈ s, f l z :=
      funext fun z => Finset.sum_insert ha
    rw [e]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun l hl => h l (Finset.mem_insert_of_mem hl))

theorem cInfAt_normSq_ratVal [IsIntegral X] {g : X.functionField} (hg : RegAt (under y) g) :
    CInfAt (fun z : CxPts p σ => ‖ratVal g z‖ ^ 2) y := by
  obtain ⟨U, hU, a, rfl⟩ := hg.exists_fnOf
  have hyU : y ∈ ptsIn p σ U := mem_ptsIn.2 hU
  have h₁ : CInfAt (fun z => ‖ev p σ U a z‖ ^ 2) y :=
    ⟨U, Unit, inferInstance, fun _ => a, fun v => ‖v ()‖ ^ 2, Set.univ, hyU, isOpen_univ, trivial,
      ((contDiff_apply ℝ (fun _ => ℂ) ()).norm_sq ℂ).contDiffOn, EventuallyEq.rfl⟩
  refine h₁.congr ?_
  filter_upwards [(isOpen_ptsIn U).mem_nhds hyU] with z hz
  rw [ratVal_fnOf hz]

end GlobalTheory.HSAmp.CanSmooth

namespace GlobalTheory.HSAmp


open CanSmooth in
theorem cInfAt_canWeight : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p) (D e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ n : ℕ, 1 ≤ n → ∀ (σ : k →+* ℂ) (y : CxPts p σ), CInfAt (fun z : CxPts p σ => ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ z (x l) ^ (2 * n))) y := by
  intro k _ X _ p P D e x hx n _ σ y
  set i := pick (P.L.φ σ).isLB y
  set j := pick (P.A.φ σ).isLB y
  have hi : y ∈ ptsIn p σ (P.L.B.U i) := mem_pick _ y
  have hj : y ∈ ptsIn p σ (P.A.B.U j) := mem_pick _ y
  have hφ : CInfAt ((P.L.φ σ).φ i) y := P.L.cInf σ i y hi
  have hterm : ∀ l, CInfAt (fun z => P.nu e 0 σ z (x l) ^ (2 * n)) y := by
    intro l
    have hreg : RegAt (under y) (P.loc e 0 (x l) i j) := hx.mem l _ i j (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have h₂ := (cInfAt_normSq_ratVal hreg).comp₂ hφ
      (G := fun w => w.1 ^ n * Real.exp (-((e : ℝ) * n) * w.2))
      ((contDiff_fst.pow n).mul ((contDiff_const.mul contDiff_snd).exp))
    refine h₂.congr ?_
    filter_upwards [(isOpen_ptsIn _).mem_nhds hi, (isOpen_ptsIn _).mem_nhds hj] with z hzi hzj
    rw [nu_eq k X p P e 0 (x l) (hx.mem l) σ z i j hzi hzj, mul_pow, pow_mul, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hsum : CInfAt (fun z => ∑ l, P.nu e 0 σ z (x l) ^ (2 * n)) y :=
    cInfAt_sum Finset.univ fun l _ => hterm l
  obtain ⟨l₀, hl₀⟩ := hx.cover (under y)
  have hpos₀ : 0 < P.nu e 0 σ y (x l₀) :=
    mul_pos (norm_pos_iff.2 (ratVal_ne_zero (hl₀ _ _ (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)))) (Real.exp_pos _)
  have hpos : 0 < ∑ l, P.nu e 0 σ y (x l) ^ (2 * n) :=
    lt_of_lt_of_le (pow_pos hpos₀ _)
      (Finset.single_le_sum (f := fun l => P.nu e 0 σ y (x l) ^ (2 * n))
        (fun l _ => (even_two_mul n).pow_nonneg _) (Finset.mem_univ l₀))
  exact (cInfAt_log hsum hpos).const_mul _

end GlobalTheory.HSAmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothAtFubiniStudyLogSumWeightStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPointsSmoothAt_fubiniStudy_log_sum_weight : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p) (D e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ n : ℕ, 1 ≤ n → ∀ (σ : k →+* ℂ) (y : CxPts p σ), CInfAt (fun z : CxPts p σ => ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ z (x l) ^ (2 * n))) y := by
  first | exact @GlobalTheory.HSAmp.cInfAt_canWeight | exact GlobalTheory.HSAmp.cInfAt_canWeight | (intros; apply GlobalTheory.HSAmp.cInfAt_canWeight <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyWeightsBoundedDifference
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

theorem nu_conjPt {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) (a b : ℤ)
    {f : X.functionField} (hf : f ∈ P.H a b) {σ σ' : k →+* ℂ} {y : CxPts p σ} {y' : CxPts p σ'}
    (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) : P.nu a b σ' y' f = P.nu a b σ y f := by
  have hi := mem_pick (P.L.φ σ).isLB y
  have hj := mem_pick (P.A.φ σ).isLB y
  have hi' := CxPts.mem_ptsIn_conj h hi
  have hj' := CxPts.mem_ptsIn_conj h hj
  have hreg := hf _ _ _ (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
  rw [GlobalTheory.VolBr.nu_eq k X p P a b f hf σ' y' _ _ hi' hj', GlobalTheory.VolBr.nu_eq k X p P a b f hf σ y _ _ hi hj,
    ratVal_conj h hreg, Complex.norm_conj, P.L.conj σ σ' _ y y' h hi, P.A.conj σ σ' _ y y' h hj]

theorem exists_isCan_bdd : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∃ u : SmFn p, IsCan P e n x u ∧ ∀ σ y, |u.u σ y| ≤ B := by
  intro k _ X _ p D hX P e x hx
  obtain ⟨B, hB, hb⟩ := GlobalTheory.T.fubiniStudy_log_sum_weight_uniformly_bounded k X p D hX P e x hx
  refine ⟨B, hB, fun n hn => ⟨⟨fun σ y => ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n)),
    fun σ y => GlobalTheory.T.complexPointsSmoothAt_fubiniStudy_log_sum_weight k X p P D e x hx n hn σ y, fun σ σ' i y y' h _ => ?_⟩, fun σ y => rfl, fun σ y => hb n hn σ y⟩⟩
  change ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ' y' (x l) ^ (2 * n)) =
    ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n))
  simp only [nu_conjPt P _ _ (hx.mem _) h]

end GlobalTheory.HSAmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyWeightsBoundedDifferenceStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fubiniStudyWeights_bounded_difference : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∃ u : SmFn p, IsCan P e n x u ∧ ∀ σ y, |u.u σ y| ≤ B := by
  first | exact @GlobalTheory.HSAmp.exists_isCan_bdd | exact GlobalTheory.HSAmp.exists_isCan_bdd | (intros; apply GlobalTheory.HSAmp.exists_isCan_bdd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowerGaloisExtSymplecticLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowerGaloisExtSymplecticLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.LevelPrimePower

theorem iterate_fixes {A : Type} [CommGroup A] (f : A →* A) (ℓ : ℕ) (hf : ∀ x, x ^ ℓ = 1 → f x = x) (e : ℕ) :
    ∀ x : A, x ^ ℓ ^ (e + 1) = 1 → f^[ℓ ^ e] x = x := by
  induction e with
  | zero => intro x hx; simpa using hf x (by simpa using hx)
  | succ e ih =>
    intro x hx
    let h : A →* A := ((show Monoid.End A from f) ^ ℓ ^ e : Monoid.End A)
    have hh : ∀ a, h a = f^[ℓ ^ e] a := fun a => congrFun (Monoid.End.coe_pow A f _) a
    have h1 : h x ^ ℓ = x ^ ℓ := by
      rw [← map_pow, hh]
      exact ih _ (by rw [← pow_mul, ← pow_succ', hx])
    have hy : (h x / x) ^ ℓ = 1 := by rw [div_pow, h1, div_self']
    have h2 : h (h x / x) = h x / x := by
      rw [hh]
      exact ih _ (by rw [pow_succ', pow_mul, hy, one_pow])
    have h3 : ∀ n : ℕ, h^[n] x = x * (h x / x) ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ihn =>
        rw [Function.iterate_succ_apply', ihn, map_mul, map_pow, h2, pow_succ', ← _root_.mul_assoc,
          mul_div_cancel]
    have h4 : (h : A → A) = f^[ℓ ^ e] := funext hh
    rw [pow_succ, Function.iterate_mul, ← h4, h3, hy, _root_.mul_one]

theorem exists_normal {G A : Type} [Group G] [CommGroup A] (ρ : G → A →* A) (h1 : ∀ x, ρ 1 x = x)
    (hm : ∀ σ τ x, ρ (σ * τ) x = ρ σ (ρ τ x)) (ℓ e : ℕ) (hf : ∀ σ x, x ^ ℓ = 1 → ρ σ x = x) :
    ∃ H : Subgroup G, H.Normal ∧ (∀ σ, σ ^ ℓ ^ e ∈ H) ∧ ∀ σ ∈ H, ∀ x, x ^ ℓ ^ e = 1 → ρ σ x = x := by
  let H : Subgroup G :=
    { carrier := {σ | ∀ x, x ^ ℓ ^ e = 1 → ρ σ x = x}
      one_mem' := fun x _ => h1 x
      mul_mem' := fun {a b} ha hb x hx => by rw [hm, hb x hx, ha x hx]
      inv_mem' := fun {a} ha x hx => by
        conv_lhs => rw [← ha x hx, ← hm, inv_mul_cancel, h1] }
  refine ⟨H, ⟨fun a ha g x hx => ?_⟩, fun σ x hx => ?_, fun σ hσ => hσ⟩
  · rw [hm, hm, ha _ (by rw [← map_pow, hx, map_one]), ← hm, mul_inv_cancel, h1]
  · have hp : ∀ (n : ℕ) x, ρ (σ ^ n) x = (ρ σ)^[n] x := by
      intro n
      induction n with
      | zero => intro x; simpa using h1 x
      | succ n ih => intro x; rw [pow_succ, hm, ih, Function.iterate_succ_apply]
    rw [hp]
    exact iterate_fixes _ ℓ (hf σ) e x (by rw [pow_succ, pow_mul, hx, one_pow])

theorem exists_factor_fixedField {F L : Type} [Field F] [Field L] [Algebra F L] (H : Subgroup (L ≃ₐ[F] L))
    {Y : Scheme.{0}} (y : Sp L ⟶ Y) (h : ∀ σ ∈ H, spMap σ.toAlgHom.toRingHom ≫ y = y) :
    ∃ z : Sp (IntermediateField.fixedField H) ⟶ Y, spMap (algebraMap (IntermediateField.fixedField H) L) ≫ z = y := by
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L Y).symm.surjective y
  have hy : (Scheme.SpecToEquivOfField L Y).symm ⟨p, φ⟩ = Spec.map φ ≫ Y.fromSpecResidueField p := rfl
  rw [hy] at h ⊢
  have hmem : ∀ b, φ.hom b ∈ IntermediateField.fixedField H := by
    intro b
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have h1 := h σ hσ
    rw [← Category.assoc, cancel_mono, ← Spec.map_comp, Spec.map_inj] at h1
    exact congrArg (fun ψ => ψ.hom b) h1
  refine ⟨Spec.map (CommRingCat.ofHom (φ.hom.codRestrict (IntermediateField.fixedField H) hmem)) ≫
    Y.fromSpecResidueField p, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

theorem exists_intermediate {F L : Type} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {S : Scheme.{0}} (X : Over S) [GrpObj X] [IsCommMonObj X] (s₀ : Sp F ⟶ S) (s : Sp L ⟶ S)
    (hs : s = spMap (algebraMap F L) ≫ s₀) (ℓ e : ℕ) (hℓ : ℓ.Prime) (ζ₀ : F) (hζ : IsPrimitiveRoot ζ₀ ℓ)
    (hfix : ∀ z : Over.mk s ⟶ X, z ^ ℓ = 1 → ∃ w : Sp F ⟶ X.left, spMap (algebraMap F L) ≫ w = z.left) :
    ∃ M : IntermediateField F L, IsGalois F M ∧ (∃ d, Module.finrank F M = ℓ ^ d) ∧
      (∀ u : Lˣ, u ^ ℓ ^ e = 1 → (u : L) ∈ M) ∧
      ∀ z : Over.mk s ⟶ X, z ^ ℓ ^ e = 1 → ∃ w : Sp M ⟶ X.left, spMap (algebraMap M L) ≫ w = z.left := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hσ : ∀ σ : L ≃ₐ[F] L, spMap σ.toAlgHom.toRingHom ≫ spMap (algebraMap F L) = spMap (algebraMap F L) := by
    intro σ
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact σ.commutes a
  let t : (L ≃ₐ[F] L) → (Over.mk s ⟶ Over.mk s) := fun σ => Over.homMk (spMap σ.toAlgHom.toRingHom) (by
    show spMap σ.toAlgHom.toRingHom ≫ s = s
    rw [hs, ← Category.assoc, hσ])
  let ρ : (L ≃ₐ[F] L) → (Over.mk s ⟶ X) →* (Over.mk s ⟶ X) := fun σ =>
    { toFun := fun x => t σ ≫ x
      map_one' := MonObj.comp_one _
      map_mul' := fun x y => MonObj.comp_mul _ _ _ }
  have hρ : ∀ σ x, (ρ σ x).left = spMap σ.toAlgHom.toRingHom ≫ x.left := fun _ _ => rfl
  obtain ⟨H₁, n₁, p₁, f₁⟩ := exists_normal ρ
    (fun x => Over.OverMorphism.ext (by
      rw [hρ]
      exact (congrArg (· ≫ x.left) (Spec.map_id (CommRingCat.of L))).trans (Category.id_comp _)))
    (fun σ τ x => Over.OverMorphism.ext (by
      rw [hρ, hρ, hρ]
      erw [← Category.assoc, ← Spec.map_comp]
      rfl)) ℓ e
    (fun σ x hx => Over.OverMorphism.ext (by
      obtain ⟨w, hw⟩ := hfix x hx
      rw [hρ, ← hw]
      erw [← Category.assoc, hσ]))
  obtain ⟨H₂, n₂, p₂, f₂⟩ := exists_normal (fun σ : L ≃ₐ[F] L => Units.map σ.toAlgHom.toRingHom.toMonoidHom)
    (fun x => rfl) (fun σ τ x => rfl) ℓ e
    (fun σ x hx => Units.ext (by
      have hx' : (x : L) ^ ℓ = 1 := by rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
      obtain ⟨i, -, hi⟩ := (hζ.map_of_injective (algebraMap F L).injective).eq_pow_of_pow_eq_one hx'
      show σ (x : L) = x
      rw [← hi, ← map_pow, σ.commutes]))
  let H := H₁ ⊓ H₂
  haveI : H.Normal := inferInstanceAs (H₁ ⊓ H₂).Normal
  have hP : IsPGroup ℓ ((L ≃ₐ[F] L) ⧸ H) := by
    intro g
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨p₁ σ, p₂ σ⟩
  refine ⟨IntermediateField.fixedField H, inferInstance, ?_, fun u hu => ?_, fun z hz => ?_⟩
  · obtain ⟨d, hd⟩ := IsPGroup.iff_card.1 hP
    refine ⟨d, ?_⟩
    rw [← hd, ← IsGalois.card_aut_eq_finrank]
    exact (Nat.card_congr (IsGalois.normalAutEquivQuotient H).toEquiv).symm
  · rw [IntermediateField.mem_fixedField_iff]
    exact fun σ hσ => congrArg Units.val (f₂ σ hσ.2 u hu)
  · exact exists_factor_fixedField H _ fun σ hσ => congrArg CommaMorphism.left (f₁ σ hσ.1 z hz)

theorem exists_level_primePower : ∀ {Ω₁ : Type} [Field Ω₁] [CharZero Ω₁] {R₁ : Type} [CommRing R₁] (emb : R₁ →+* Ω₁) (P₁ : PolAV (Sp R₁)) (ℓ M K : ℕ), ℓ.Prime → 0 < M → ℓ ∣ M → (∃ e, K = ℓ ^ e) → (∃ ζ₀ : Ω₁, IsPrimitiveRoot ζ₀ M) → (∀ (E : Type) [Field E] [IsAlgClosed E] (x : Sp E ⟶ Sp R₁) (z : Over.mk x ⟶ P₁.A), z ^ M = 1 → ∃ y : baseOver (Sp R₁) ⟶ P₁.A, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R₁)) ≫ y = z) → ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra Ω₁ Ω₂) (Q : PolAV (Sp Ω₂)) (φ : Q.A.left ⟶ P₁.A.left) (ζ : Ω₂ˣ), FiniteDimensional Ω₁ Ω₂ ∧ IsGalois Ω₁ Ω₂ ∧ (∃ e, Module.finrank Ω₁ Ω₂ = ℓ ^ e) ∧ IsPrimitiveRoot ζ K ∧ Q.g = P₁.g ∧ IsGrpPullback Q.A P₁.A (spMap ((algebraMap Ω₁ Ω₂).comp emb)) φ ∧ LBIso Q.L (P₁.L.pull φ) ∧ Nonempty (Out.Level Q K (unitOn ζ)) := by
  intro F _ _ R₁ _ emb P₁ ℓ N K hℓ hN hℓN ⟨e, hK⟩ ⟨ζ₀, hζ₀⟩ hsec
  have hK0 : 0 < K := hK ▸ pow_pos hℓ.pos e
  have := P₁.isAb.comm
  obtain ⟨L, _, _, Q₃, φ₃, ζ₃, hfd, hgal, hζ₃, -, h₃, -, ⟨lev⟩⟩ := LevelGalois.exists_level_galois emb P₁ K hK0
  obtain ⟨c, rfl⟩ := hℓN
  have hζ₁ : IsPrimitiveRoot (ζ₀ ^ c) ℓ := hζ₀.pow hN (Nat.mul_comm _ _)
  have hs : spMap ((algebraMap F L).comp emb) = spMap (algebraMap F L) ≫ spMap emb := (GlobalTheory.spMap_comp_spMap _ _).symm
  obtain ⟨M, hMgal, hdeg, hroot, hpts⟩ := exists_intermediate P₁.A (spMap emb) (spMap ((algebraMap F L).comp emb)) hs
    ℓ e hℓ _ hζ₁ (fun z hz => by
      let τ := algebraMap L (AlgebraicClosure L)
      let k : Over.mk (spMap τ ≫ spMap ((algebraMap F L).comp emb)) ⟶ Over.mk (spMap ((algebraMap F L).comp emb)) :=
        Over.homMk (spMap τ) rfl
      obtain ⟨y, hy⟩ := hsec _ _ (k ≫ z) (by rw [← MonObj.comp_pow, pow_mul, hz, one_pow, MonObj.comp_one])
      exact ⟨spMap emb ≫ y.left, (cancel_epi (spMap τ)).1 (by
        have hy' : (spMap τ ≫ spMap ((algebraMap F L).comp emb)) ≫ y.left = spMap τ ≫ z.left :=
          congrArg CommaMorphism.left hy
        rw [← hy', hs]
        simp only [Category.assoc])⟩)
  rw [← hK] at hroot hpts
  haveI : CharZero M := (algebraMap F M).charZero_iff (algebraMap F M).injective |>.1 inferInstance
  have hB := GlobalTheory.laws_without_cohomology.2.2.1
  let ζ' : M := ⟨ζ₃, hroot ζ₃ hζ₃.pow_eq_one⟩
  have hζ' : IsPrimitiveRoot ζ' K :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap M L) (IsPrimitiveRoot.coe_units_iff.2 hζ₃)
      (algebraMap M L).injective
  obtain ⟨ζ, hζe⟩ := hζ'.isUnit hK0.ne'
  have hζ : IsPrimitiveRoot ζ K := IsPrimitiveRoot.coe_units_iff.1 (hζe ▸ hζ')
  obtain ⟨Q, φ, hQ⟩ := exists_isPolFibre hB ((algebraMap F M).comp emb) P₁
  obtain ⟨Q', ψ, hQ'⟩ := exists_isPolFibre hB (algebraMap M (AlgebraicClosure M)) Q
  refine ⟨M, inferInstance, inferInstance, Q, φ, ζ, inferInstance, hMgal, hdeg, hζ, hQ.1, hQ.2.1, hQ.2.2.symm,
    LevelGalois.nonempty_level_of_rational Q K hK0 ζ hζ Q' ψ hQ' fun y hy => by
    let σ := algebraMap M (AlgebraicClosure M)
    let τ' : L →ₐ[M] AlgebraicClosure M := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    let τ : L →+* AlgebraicClosure M := τ'.toRingHom
    have hτ : spMap τ ≫ spMap (algebraMap M L) = spMap σ := by
      rw [GlobalTheory.spMap_comp_spMap]
      exact congrArg spMap (RingHom.ext τ'.commutes)
    have hML : spMap (algebraMap M L) ≫ spMap ((algebraMap F M).comp emb) = spMap ((algebraMap F L).comp emb) := by
      rw [GlobalTheory.spMap_comp_spMap]
      rfl
    have hPg : IsGrpPullback Q.A P₁.A (spMap ((algebraMap F M).comp emb)) φ := hQ.2.1
    have hQg : IsGrpPullback Q'.A Q.A (spMap σ) ψ := hQ'.2.1
    let y₀ := ObjPull.pushEquiv hPg _ (ObjPull.pushEquiv hQg (𝟙_ _) y)
    have hy₀ : y₀ ^ K = 1 := by simp only [y₀, ← map_pow, hy, map_one]
    let j : Over.mk ((Over.mk (spMap τ)).hom ≫ spMap ((algebraMap F L).comp emb)) ⟶
        Over.mk (((𝟙_ (Over (Sp (AlgebraicClosure M)))).hom ≫ spMap σ) ≫ spMap ((algebraMap F M).comp emb)) :=
      Over.homMk (𝟙 _) (by
        show 𝟙 _ ≫ (𝟙 _ ≫ spMap σ) ≫ _ = spMap τ ≫ _
        rw [Category.id_comp, Category.id_comp, ← hML, ← hτ, Category.assoc])
    let y₁ := j ≫ y₀
    have hy₁ : y₁ ^ K = 1 := by rw [← MonObj.comp_pow, hy₀, MonObj.comp_one]
    have hy₁l : y₁.left = (y.left ≫ ψ) ≫ φ := Category.id_comp _
    let y₂ := (ObjPull.pushEquiv h₃ (Over.mk (spMap τ))).symm y₁
    obtain ⟨a, ha⟩ := lev.span _ (spMap τ) y₂ (by rw [← map_pow, hy₁, map_one])
    rw [← GenSpread.comp_linComb] at ha
    set v := linComb lev.pt (fun i => (a i : ℕ)) with hv
    have hvl : spMap τ ≫ v.left = y₂.left := congrArg CommaMorphism.left ha
    let z : Over.mk (spMap ((algebraMap F L).comp emb)) ⟶ P₁.A := Over.homMk (v.left ≫ φ₃) (by
      rw [Category.assoc, h₃.1.w, ← Category.assoc, Over.w v]
      exact Category.id_comp _)
    let k : Over.mk ((Over.mk (spMap τ)).hom ≫ spMap ((algebraMap F L).comp emb)) ⟶
        Over.mk (spMap ((algebraMap F L).comp emb)) := Over.homMk (spMap τ) rfl
    have hzl : spMap τ ≫ z.left = y₁.left := by
      rw [← ObjPull.pushEquiv_symm_left h₃ _ y₁]
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ₃) hvl)
    have hkz : k ≫ z = y₁ := Over.OverMorphism.ext hzl
    have hz : z ^ K = 1 := by
      have h : k ≫ z ^ K = k ≫ 1 := by rw [MonObj.comp_pow, hkz, hy₁, MonObj.comp_one]
      exact Over.OverMorphism.ext ((cancel_epi (spMap τ)).1 (congrArg CommaMorphism.left h))
    obtain ⟨w, hw⟩ := hpts z hz
    have hw2 : w ≫ P₁.A.hom = 𝟙 _ ≫ spMap ((algebraMap F M).comp emb) := by
      refine (cancel_epi (spMap (algebraMap M L))).1 ?_
      rw [← Category.assoc, hw, Over.w z, Category.id_comp, hML]
      rfl
    let x : 𝟙_ (Over (Sp M)) ⟶ Q.A := Over.homMk (hPg.1.lift w (𝟙 _) hw2) (hPg.1.lift_snd _ _ _)
    have hxl : x.left ≫ φ = w := hPg.1.lift_fst _ _ _
    refine ⟨x, ?_⟩
    apply Over.OverMorphism.ext
    refine hQg.1.hom_ext ?_ ?_
    · rw [ObjPull.secPull_left]
      refine hPg.1.hom_ext ?_ ?_
      · rw [Category.assoc, hxl, ← hy₁l, ← hzl, ← hw, ← Category.assoc, hτ]
      · rw [Category.assoc, Over.w x, Category.assoc, hQg.1.w, ← Category.assoc, Over.w y]
        exact (Category.comp_id _).trans (Category.id_comp _).symm
    · rw [Over.w, Over.w]⟩

end GlobalTheory.LevelPrimePower
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowerGaloisExtSymplecticLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primePower_galois_ext_symplecticLevel : ∀ {Ω₁ : Type} [Field Ω₁] [CharZero Ω₁] {R₁ : Type} [CommRing R₁] (emb : R₁ →+* Ω₁) (P₁ : PolAV (Sp R₁)) (ℓ M K : ℕ), ℓ.Prime → 0 < M → ℓ ∣ M → (∃ e, K = ℓ ^ e) → (∃ ζ₀ : Ω₁, IsPrimitiveRoot ζ₀ M) → (∀ (E : Type) [Field E] [IsAlgClosed E] (x : Sp E ⟶ Sp R₁) (z : Over.mk x ⟶ P₁.A), z ^ M = 1 → ∃ y : baseOver (Sp R₁) ⟶ P₁.A, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R₁)) ≫ y = z) → ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra Ω₁ Ω₂) (Q : PolAV (Sp Ω₂)) (φ : Q.A.left ⟶ P₁.A.left) (ζ : Ω₂ˣ), FiniteDimensional Ω₁ Ω₂ ∧ IsGalois Ω₁ Ω₂ ∧ (∃ e, Module.finrank Ω₁ Ω₂ = ℓ ^ e) ∧ IsPrimitiveRoot ζ K ∧ Q.g = P₁.g ∧ IsGrpPullback Q.A P₁.A (spMap ((algebraMap Ω₁ Ω₂).comp emb)) φ ∧ LBIso Q.L (P₁.L.pull φ) ∧ Nonempty (Out.Level Q K (unitOn ζ)) := by
  first | exact @GlobalTheory.LevelPrimePower.exists_level_primePower | exact GlobalTheory.LevelPrimePower.exists_level_primePower | (intros; apply GlobalTheory.LevelPrimePower.exists_level_primePower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawOfIsLawOf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawOfIsLawOf
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.Chart

variable {p : ℕ} {k : Type} [CommRing k] {d : ℕ} {G : PDivGroup p k}

def firstFactor (A : Type) [CommRing A] [Bialgebra k A] : A ⊗[k] A →ₐ[k] A :=
  Algebra.TensorProduct.lift (AlgHom.id k A) ((Algebra.ofId k A).comp (Bialgebra.counitAlgHom k A))
    (fun _ _ => Commute.all _ _)

theorem firstFactor_comul (A : Type) [CommRing A] [Bialgebra k A] (a : A) :
    firstFactor A (Coalgebra.comul (R := k) a) = a := by
  have h : (firstFactor A).toLinearMap =
      (TensorProduct.rid k A).toLinearMap ∘ₗ (Coalgebra.counit (R := k) (A := A)).lTensor A := by
    apply TensorProduct.ext'
    intro a b
    simp [firstFactor, Algebra.smul_def, mul_comm]
  have := LinearMap.congr_fun h (Coalgebra.comul (R := k) a)
  simp only [AlgHom.toLinearMap_apply] at this
  rw [this, LinearMap.comp_apply, Coalgebra.lTensor_counit_comul]
  simp

end GlobalTheory.Katz.Chart

namespace GlobalTheory.Katz.Chart

variable {p : ℕ} {k : Type} [CommRing k] {d : ℕ} {G : PDivGroup p k}

theorem firstFactor_ev₂ (c : Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d ⊕ Fin d) k) :
    firstFactor (G.A n) (c.ev₂ n f) =
      c.ev n (at2 f (fun i => (X i : MvPowerSeries (Fin d) k)) (fun _ => 0)) := by
  have hy : ∀ j : Fin d ⊕ Fin d, IsNilpotent ((Sum.elim (c.x n) (fun _ => (0 : G.A n))) j) := by
    intro j; cases j with
    | inl i => exact c.nil n i
    | inr i => exact IsNilpotent.zero
  have h2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).2 (G.A n) (firstFactor (G.A n))
    (c.x₂ n) (c.nil₂ n) _ hy (by
      intro j; cases j with
      | inl i => simp [Chart.x₂, firstFactor]
      | inr i => simp [Chart.x₂, firstFactor, c.aug]) f
  have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n)).1 (Fin d) (c.ev n)
    (fun t => by rw [Chart.ev, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact c.nil n t)
    (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) k)) (fun _ => 0))
    (by intro j; cases j with
      | inl i => exact constantCoeff_X i
      | inr i => exact map_zero _)
    _ hy (by
      intro j; cases j with
      | inl i => simp [Chart.ev, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]
      | inr i => simp) f
  exact h2.trans h1.symm

end GlobalTheory.Katz.Chart

namespace GlobalTheory

theorem Katz.Chart.isLaw_of_isLawOf : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → IsLaw μ := by
  intro p k _ d G c μ hμ
  have hcomp : ∀ (n : ℕ) (i : Fin d), pullbackTwo (G.res n) (Coalgebra.comul (R := k) (c.x (n + 1) i))
      = Coalgebra.comul (R := k) (c.x n i) := fun n i => by
    rw [pullTwo_comul, c.res]
  refine ⟨((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).1, ?_, ?_, ?_⟩
  · funext i
    obtain ⟨f, -, huniq⟩ := (GlobalTheory.T.functions_eq_series_in_chart p k d G c).2.2 (fun n => c.x n i) (fun n => c.res n i)
    have hX : ∀ n, c.ev n (X i) = c.x n i := fun n => GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate _ _ _ _ _ i
    have hA : ∀ n, c.ev n (op μ (fun i => (X i : MvPowerSeries (Fin d) k)) (fun _ => 0) i) =
        c.x n i := fun n => by
      rw [op, ← firstFactor_ev₂, hμ, firstFactor_comul]
    exact (huniq _ hA).trans (huniq _ hX).symm
  · intro i
    obtain ⟨s, -, huniq⟩ := (GlobalTheory.T.chart_square_coordinates_present_levels p k d G c).2 (fun n => Coalgebra.comul (R := k) (c.x n i))
      (fun n => hcomp n i)
    have h1 : ∀ n, c.ev₂ n (Katz.swap (μ i)) = Coalgebra.comul (R := k) (c.x n i) := fun n => by
      rw [((GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k d G c) n).2.2.1, hμ, Coalgebra.comm_comul]
    exact (huniq _ h1).trans (huniq _ (fun n => hμ n i)).symm
  · funext i
    have hinj := (GlobalTheory.T.eq_zero_of_eval_cube_levels p k d G c).2
      (op μ (op μ x1 x2) x3 i - op μ x1 (op μ x2 x3) i) (fun n h => by
        rw [map_sub, ((GlobalTheory.T.connectedPDivGroupChart_coboundaryTwo_coord p k d G c μ hμ n h).2 i), sub_self])
    exact sub_eq_zero.1 hinj

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawOfIsLawOfStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCommFormalGroupLaw_of_isLawOf : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → IsLaw μ := by
  first | exact @GlobalTheory.Katz.Chart.isLaw_of_isLawOf | exact GlobalTheory.Katz.Chart.isLaw_of_isLawOf | (intros; apply GlobalTheory.Katz.Chart.isLaw_of_isLawOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductionIndependentOfSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorRationalSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorRationalSections
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt.Denom

variable {Y : Scheme.{0}} [IsIntegral Y]

theorem exists_sec_tens {L M : LB Y} (hL : L.IsLB) (hM : M.IsLB) {r : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) (u : M.Sec) (hu : genericPoint Y ∈ nonzeroLocus u)
    (hE : (divOfRatSec hL hr + divOfSec hM u hu).Eff) :
    ∃ (t : (tens L M).Sec) (ht : genericPoint Y ∈ nonzeroLocus t), ∀ i j, genericPoint Y ∈ L.U i →
      genericPoint Y ∈ M.U j → ratOfSec t ht (i, j) = r i * ratOfSec u hu j := by
  have P := (presents_divOfRatSec hL hr).tens (presents_divOfRatSec hM (isRatSec_ratOfSec u hu))
  obtain ⟨t, ht⟩ := P.exists_rat_eq (f := 1) (CartierDiv.mem_sections.2 fun x => hE x)
  have hη : genericPoint Y ∈ nonzeroLocus t :=
    (P.generatesAt_rat_iff t).1 (ht ▸ CartierDiv.generatesAt_genericPoint _ one_ne_zero)
  refine ⟨t, hη, fun i j hi hj => Units.ext ?_⟩
  have e := P.rat_mul t (i, j) ⟨hi, hj⟩
  rw [ht, one_mul] at e
  rw [val_ratOfSec (show genericPoint Y ∈ (tens L M).U (i, j) from ⟨hi, hj⟩), ← e]

theorem gen_mem_secPow {L : LB Y} (hL : L.IsLB) (t : L.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
    (m : ℕ) : genericPoint Y ∈ nonzeroLocus (Cartier.secPow t m) := by
  obtain ⟨i, hi⟩ := exists_chart hL (genericPoint Y)
  have hj : genericPoint Y ∈ (lbPow L m).U (fun _ => i) := (lbPow_U L m _).ge hi
  refine (mem_nonzeroLocus_iff _ _ hj).2 ((unitAt_fnOf_iff hj hj _).1 (unitAt_genericPoint ?_))
  show fnOf _ hj (resG Y _ (t.f i) ^ m) ≠ 0
  rw [map_pow, fnOf_resG]
  exact pow_ne_zero _ (fnOf_sec_ne_zero ht hi)

theorem divOfSec_secPow {L : LB Y} (hL : L.IsLB) (t : L.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
    (m : ℕ) (hm : genericPoint Y ∈ nonzeroLocus (Cartier.secPow t m)) :
    divOfSec (isLB_lbPow hL m) (Cartier.secPow t m) hm = m • divOfSec hL t ht := by
  refine CartierDiv.ext_of_isEqn fun x => ?_
  obtain ⟨i, hi⟩ := exists_chart hL x
  have hj : x ∈ (lbPow L m).U (fun _ => i) := (lbPow_U L m _).ge hi
  have e : ratOfSec (Cartier.secPow t m) hm (fun _ => i) = ratOfSec t ht i ^ m := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, val_ratOfSec (gen_mem hi), val_ratOfSec (gen_mem hj)]
    show fnOf _ (gen_mem hj) (resG Y _ (t.f i) ^ m) = _
    rw [map_pow, fnOf_resG]
  refine ⟨ratOfSec t ht i ^ m, ?_,
    ((presents_divOfRatSec hL (isRatSec_ratOfSec t ht)).isEqn i x hi).nsmul m⟩
  rw [← e]
  exact (presents_divOfRatSec (isLB_lbPow hL m) (isRatSec_ratOfSec _ hm)).isEqn _ x hj

theorem exists_open_regularAt {L : LB Y} (hL : L.IsLB) {r : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) :
    ∃ W : Y.Opens, genericPoint Y ∈ W ∧ ∀ x ∈ W, (divOfRatSec hL hr).RegularAt x 1 := by
  obtain ⟨i, hi⟩ := exists_chart hL (genericPoint Y)
  obtain ⟨U, hU, a, ha⟩ := (regAt_genericPoint (r i : Y.functionField)).exists_fnOf
  refine ⟨L.U i ⊓ U, ⟨hi, hU⟩, fun x hx => ?_⟩
  refine ((presents_divOfRatSec hL hr).isEqn i x hx.1).regularAt_iff.2 ?_
  rw [one_mul, ← ha]
  exact regAt_fnOf hx.2 _ a

end GlobalTheory.MixHt.Denom


open GlobalTheory.MixHt.Denom in
theorem GlobalTheory.MixHt.exists_common_denom : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y]
    (q : Y ⟶ Sp k), IsAmb q → ∀ (N : HermLB q) (r r' : N.B.ι → Y.functionFieldˣ), IsRatSec N.B r →
    IsRatSec N.B r' → ∃ (A : HermLB q) (u : A.B.Sec) (t t' : (N.tens A).B.Sec)
    (hu : genericPoint Y ∈ nonzeroLocus u) (ht : genericPoint Y ∈ nonzeroLocus t)
    (ht' : genericPoint Y ∈ nonzeroLocus t'), ∀ (i : N.B.ι) (j : A.B.ι), genericPoint Y ∈ N.B.U i →
    genericPoint Y ∈ A.B.U j → ratOfSec t ht (i, j) = r i * ratOfSec u hu j ∧
      ratOfSec t' ht' (i, j) = r' i * ratOfSec u hu j := by
  intro k _ Y _ q hq N r r' hr hr'
  obtain ⟨n₀, j, hj, hjq⟩ := hq.isProjOver
  let H₀ : HermLB (PSpace.str k n₀) :=
    .fs _ (isAmple_projective_O_one k n₀).isLB (ProjSpace.coord k n₀)
      (ProjSpace.iSup_nonzeroLocus_coord k n₀) (fun _ => 1) (fun _ => by simp)
      (fun _ => ⟨1, one_mem _, by rw [mul_one, Matrix.map_one _ (map_zero _) (map_one _)]⟩)
  let H : HermLB q := H₀.pull j hjq
  have hH : IsAmpleLB H.B := (isAmple_projective_O_one k n₀).pull_of_isClosedImmersion j
  haveI := hH.compactSpace
  obtain ⟨W, hW, hWr⟩ := exists_open_regularAt N.isLB hr
  obtain ⟨W', hW', hWr'⟩ := exists_open_regularAt N.isLB hr'
  obtain ⟨n, -, t, ht, hle, -⟩ :=
    hH.exists_affine_le (x := genericPoint Y) (U := W ⊓ W') ⟨hW, hW'⟩
  have hL := isLB_lbPow H.isLB n
  obtain ⟨N₁, h₁⟩ := EffDiff.eventually_eff_add_nsmul hL t ht _ fun x hx => hWr x (hle hx).1
  obtain ⟨N₂, h₂⟩ := EffDiff.eventually_eff_add_nsmul hL t ht _ fun x hx => hWr' x (hle hx).2
  have hu := gen_mem_secPow hL t ht (max N₁ N₂)
  have hD := divOfSec_secPow hL t ht (max N₁ N₂) hu
  obtain ⟨s, hs, e⟩ := exists_sec_tens N.isLB (isLB_lbPow hL _) hr (Cartier.secPow t (max N₁ N₂)) hu
    (by rw [hD]; exact h₁ _ (le_max_left _ _))
  obtain ⟨s', hs', e'⟩ := exists_sec_tens N.isLB (isLB_lbPow hL _) hr' (Cartier.secPow t (max N₁ N₂)) hu
    (by rw [hD]; exact h₂ _ (le_max_right _ _))
  exact ⟨(H.pow n).pow (max N₁ N₂), Cartier.secPow t (max N₁ N₂), s, s', hu, hs, hs',
    fun i j hi hj => ⟨e i j hi hj, e' i j hi hj⟩⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorRationalSectionsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_rational_sections : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (N : HermLB q) (r r' : N.B.ι → Y.functionFieldˣ), IsRatSec N.B r → IsRatSec N.B r' → ∃ (A : HermLB q) (u : A.B.Sec) (t t' : (N.tens A).B.Sec) (hu : genericPoint Y ∈ nonzeroLocus u) (ht : genericPoint Y ∈ nonzeroLocus t) (ht' : genericPoint Y ∈ nonzeroLocus t'), ∀ (i : N.B.ι) (j : A.B.ι), genericPoint Y ∈ N.B.U i → genericPoint Y ∈ A.B.U j → ratOfSec t ht (i, j) = r i * ratOfSec u hu j ∧ ratOfSec t' ht' (i, j) = r' i * ratOfSec u hu j := by
  first | exact @GlobalTheory.MixHt.exists_common_denom | exact GlobalTheory.MixHt.exists_common_denom | (intros; apply GlobalTheory.MixHt.exists_common_denom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductionIndependentOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem recVal_indep_sec : ArchInteg → ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y]
    [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T,
    IsMix q (e + 1) T → ∀ (N : HermLB q) (L : Fin (e + 1) → HermLB q) (r : N.B.ι → Y.functionFieldˣ)
    (hr : IsRatSec N.B r) (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'),
    recVal (T (e + 1) L) L N hr = recVal (T (e + 1) L) L N hr' := by
  intro hI hR k _ Y _ _ q hq e hd T hT N L r hr r' hr'
  haveI : IsNoetherian Y := hq.isNoetherian
  have step1 : ∀ (P : HermLB q) (t t' : P.B.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
      (ht' : genericPoint Y ∈ nonzeroLocus t'),
      recVal (T (e + 1) L) L P (isRatSec_ratOfSec t ht) = recVal (T (e + 1) L) L P (isRatSec_ratOfSec t' ht') := by
    intro P t t' ht ht'
    have hS := (GlobalTheory.ZH.finite_notMem_coheight_le_one (nonzeroLocus t) ⟨_, ht⟩).union
      (GlobalTheory.ZH.finite_notMem_coheight_le_one (nonzeroLocus t') ⟨_, ht'⟩)
    obtain ⟨A, s, u, hs, hu⟩ := GlobalTheory.T.exists_tensor_sections_nonvanishing_finite_set k Y q hq (L 0) _ (hS.insert (genericPoint Y))
    have hgs : genericPoint Y ∈ nonzeroLocus s := hs (Set.mem_insert _ _)
    have hgu : genericPoint Y ∈ nonzeroLocus u := hu (Set.mem_insert _ _)
    have cs : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus t ∨ z ∈ nonzeroLocus s := fun z hz => by
      by_cases h : z ∈ nonzeroLocus t
      · exact Or.inl h
      · exact Or.inr (hs (Set.mem_insert_of_mem _ (Or.inl ⟨h, hz.le⟩)))
    have cs' : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus t' ∨ z ∈ nonzeroLocus s := fun z hz => by
      by_cases h : z ∈ nonzeroLocus t'
      · exact Or.inl h
      · exact Or.inr (hs (Set.mem_insert_of_mem _ (Or.inr ⟨h, hz.le⟩)))
    have cu : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus t ∨ z ∈ nonzeroLocus u := fun z hz => by
      by_cases h : z ∈ nonzeroLocus t
      · exact Or.inl h
      · exact Or.inr (hu (Set.mem_insert_of_mem _ (Or.inl ⟨h, hz.le⟩)))
    have cu' : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus t' ∨ z ∈ nonzeroLocus u := fun z hz => by
      by_cases h : z ∈ nonzeroLocus t'
      · exact Or.inl h
      · exact Or.inr (hu (Set.mem_insert_of_mem _ (Or.inr ⟨h, hz.le⟩)))
    have r1 := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT P ((L 0).tens A) (Fin.tail L) t s ht hgs cs
    have r1' := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT P ((L 0).tens A) (Fin.tail L) t' s ht' hgs cs'
    have r2 := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT P A (Fin.tail L) t u ht hgu cu
    have r2' := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT P A (Fin.tail L) t' u ht' hgu cu'
    have a1 := GlobalTheory.T.inductiveMixedHeight_tensor_additive hI k Y q hq e hd T hT P _ (isRatSec_ratOfSec t ht) (L 0) A (Fin.tail L)
    have a1' := GlobalTheory.T.inductiveMixedHeight_tensor_additive hI k Y q hq e hd T hT P _ (isRatSec_ratOfSec t' ht') (L 0) A (Fin.tail L)
    rw [← Fin.cons_self_tail L]
    linarith
  obtain ⟨A, u, t, t', hu, ht, ht', hrel⟩ := GlobalTheory.T.exists_common_denominator_rational_sections k Y q hq N r r' hr hr'
  have v1 := GlobalTheory.T.inductiveArakelovFormula_rhs_tensor_additive hI k Y q hq (e + 1) hd (T (e + 1) L) L N A r hr _ (isRatSec_ratOfSec u hu) _
    (isRatSec_ratOfSec t ht) fun i j hi hj => (hrel i j hi hj).1
  have v2 := GlobalTheory.T.inductiveArakelovFormula_rhs_tensor_additive hI k Y q hq (e + 1) hd (T (e + 1) L) L N A r' hr' _ (isRatSec_ratOfSec u hu) _
    (isRatSec_ratOfSec t' ht') fun i j hi hj => (hrel i j hi hj).2
  have s1 := step1 (N.tens A) t t' ht ht'
  linarith

end GlobalTheory.MixHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductionIndependentOfSectionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedHeightInduction_independent_of_section : ArchInteg → ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (N : HermLB q) (L : Fin (e + 1) → HermLB q) (r : N.B.ι → Y.functionFieldˣ) (hr : IsRatSec N.B r) (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'), recVal (T (e + 1) L) L N hr = recVal (T (e + 1) L) L N hr' := by
  first | exact @GlobalTheory.MixHt.recVal_indep_sec | exact GlobalTheory.MixHt.recVal_indep_sec | (intros; apply GlobalTheory.MixHt.recVal_indep_sec <;> assumption)
end
end
