module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralWeierstrassChartXyUnitSeries
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsSymmetricOfSymmetryGenerator
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MultiplicativeShiftEqTranslateBySmallPoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubst

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffBoundedTaylorEllipticOfPoles
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffBoundedTaylorEllipticOfPoles
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.EllBdd

variable {q : ℕ} [Fact q.Prime]

theorem bd_C (a : ℂ_[q]) : Bd ‖a‖ (C a : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_C]
  split_ifs <;> simp

theorem bd_mono {A B : ℝ} {f : ℂ_[q]⟦X⟧} (h : Bd A f) (hAB : A ≤ B) : Bd B f :=
  fun n => (h n).trans hAB

theorem bd_X_pow (k : ℕ) : Bd 1 (X ^ k : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_X_pow]
  split_ifs <;> simp

theorem bd_one_mul {f g : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (hg : Bd 1 g) : Bd 1 (f * g) := by
  simpa using ((sup_norm_laws q).1 f g 1 1 hf hg).2

theorem bd_one_add {f g : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (hg : Bd 1 g) : Bd 1 (f + g) := by
  simpa using ((sup_norm_laws q).1 f g 1 1 hf hg).1

theorem bd_one_pow {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (k : ℕ) : Bd 1 (f ^ k) := by
  induction k with
  | zero => simpa using (bd_X_pow (q := q) 0)
  | succ k ih => rw [pow_succ]; exact bd_one_mul ih hf

theorem bd_one_sum {α : Type*} (s : Finset α) (f : α → ℂ_[q]⟦X⟧) (h : ∀ i ∈ s, Bd 1 (f i)) :
    Bd 1 (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Bd 1) (fun _ _ => bd_one_add) (fun n => by simp) h

theorem bdd_mul {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f * g) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hA hB).2⟩

theorem bdd_add {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f + g) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hA hB).1⟩

theorem bdd_sum {α : Type*} (s : Finset α) (f : α → ℂ_[q]⟦X⟧) (h : ∀ i ∈ s, Bdd (f i)) :
    Bdd (∑ i ∈ s, f i) :=
  Finset.sum_induction f Bdd (fun _ _ => bdd_add) ⟨0, fun n => by simp⟩ h

theorem hat_one (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (hℓ : constantCoeff ℓ = 0) :
    hat ι ℓ (fun _ => 1) = 1 := by
  have h1 : tay (fun _ => 1) = 1 := by
    ext n
    rw [tay, coeff_mk, coeff_one, iteratedDeriv_const]
    split_ifs with h
    · simp [h]
    · simp
  have hs : HasSubst ℓ := HasSubst.of_constantCoeff_zero' hℓ
  rw [hat, h1, map_one, ← coe_substAlgHom hs, map_one]

theorem prod_coeff_le (ι : ℂ ≃+* ℂ_[q]) {m : ℕ} (a : Fin m → ℂ) (ha : ∀ i, ‖ι (a i)‖ ≤ 1) (n : ℕ) :
    ‖ι ((∏ i, (Polynomial.X - Polynomial.C (a i))).coeff n)‖ ≤ 1 := by
  revert n
  refine Finset.prod_induction _ (fun p : Polynomial ℂ => ∀ n, ‖ι (p.coeff n)‖ ≤ 1) ?_ ?_ ?_
  · intro p r hp hr n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Polynomial.coeff_mul, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
    intro x _
    rw [map_mul, norm_mul]
    exact mul_le_one₀ (hp _) (norm_nonneg _) (hr _)
  · intro n
    rw [Polynomial.coeff_one]
    split_ifs <;> simp
  · intro i _ n
    rcases n with _ | _ | n
    · simpa using ha i
    · simp
    · simp [Polynomial.coeff_X]

theorem bdd_hat_of_ell : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (φ : ℂ → ℂ), M.Chart ℓ → Ell M.L φ → AnalyticAt ℂ φ 0 → (∀ p, meromorphicOrderAt φ p < 0 → ¬ M.Small p) → Bdd (hat M.ι ℓ φ) := by
  intro q _ M ℓ φ hC hE hA hP
  obtain ⟨m, P, A, B, hPi, hz⟩ := GlobalTheory.EllipticModel.exists_mul_prod_eq_xy q M φ hC.1 hE
  obtain ⟨-, v, xs, ys, -, hxs, hys, -, hx0, -, -, -, -, hmain⟩ := GlobalTheory.MomOne.ChartXY.chart_xy q M ℓ hC
  set D : Polynomial ℂ := ∏ i, (Polynomial.X - Polynomial.C (M.x (P i))) with hD
  have hmon : D.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hdeg : D.natDegree = m := by
    rw [hD, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
    simp
  have hint : ∀ n, ‖M.ι (D.coeff n)‖ ≤ 1 := by
    refine prod_coeff_le M.ι (fun i => M.x (P i)) fun i => ?_
    by_contra h
    exact hP _ (hPi i).2 (Or.inr (not_le.mp h))
  have key := hmain φ A B (max A.natDegree B.natDegree) hA (le_max_left _ _) (le_max_right _ _)
    (fun _ => 1) analyticAt_const D m hdeg.le (by simpa using hz 0)
  set k := max A.natDegree B.natDegree
  set S := ∑ i ∈ Finset.range (m + 1), C (M.ι (D.coeff i)) * X ^ (2 * (m - i)) * xs ^ i with hS
  have hS1 : Bd 1 S := bd_one_sum _ _ fun i _ =>
    bd_one_mul (bd_one_mul (bd_mono (bd_C _) (hint i)) (bd_X_pow _)) (bd_one_pow hxs i)
  have hS0 : ‖constantCoeff S‖ = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, Finset.sum_range_succ, map_add (f := _), map_sum, Finset.sum_eq_zero, zero_add]
    · have : D.coeff m = 1 := by rw [← hdeg]; exact hmon.coeff_natDegree
      simp [this, hx0]
    · intro i hi
      have : 2 * (m - i) ≠ 0 := by have := Finset.mem_range.mp hi; omega
      simp [this]
  have hR : Bdd (hat M.ι ℓ φ * X ^ (2 * k + 3) * S) := by
    rw [key, hat_one M.ι ℓ hC.2.1, one_mul]
    refine bdd_mul ⟨_, bd_X_pow _⟩ (bdd_sum _ _ fun i _ => bdd_add ?_ ?_)
    · exact bdd_mul (bdd_mul ⟨_, bd_C _⟩ ⟨_, bd_X_pow _⟩) ⟨_, bd_one_pow hxs i⟩
    · exact bdd_mul (bdd_mul (bdd_mul ⟨_, bd_C _⟩ ⟨_, bd_X_pow _⟩) ⟨_, bd_one_pow hxs i⟩) ⟨_, hys⟩
  obtain ⟨R, hR⟩ := hR
  refine ⟨R, (sup_norm_laws q).2.2.2.2.2 _ S (2 * k + 3) R hS1 hS0 ?_⟩
  rwa [show X ^ (2 * k + 3) * S * hat M.ι ℓ φ = hat M.ι ℓ φ * X ^ (2 * k + 3) * S by ring]

end GlobalTheory.MomOne.EllBdd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffBoundedTaylorEllipticOfPolesStatement
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (φ : ℂ → ℂ), M.Chart ℓ → Ell M.L φ → AnalyticAt ℂ φ 0 → (∀ p, meromorphicOrderAt φ p < 0 → ¬ M.Small p) → Bdd (hat M.ι ℓ φ) := by
  first | exact @GlobalTheory.MomOne.EllBdd.bdd_hat_of_ell | exact GlobalTheory.MomOne.EllBdd.bdd_hat_of_ell | (intros; apply GlobalTheory.MomOne.EllBdd.bdd_hat_of_ell <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPelUnifOfUnifPow
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_pelUnif_of_unifPow : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (n : ℕ) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' t.G n) (U' : Unif (maximalIdeal V) D' A' G') (_PU : UnifPowOf3 pD pA pG U' P.U), letI := H.starRing; ∀ [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∃ (oA' : A'.OAct (𝓞 E)), (∀ (a : 𝓞 E) (i : Fin n), oA'.act a ≫ pA.pr i = pA.pr i ≫ P.oA.act a) ∧ ∃ (t' : SAB H (Sp V)) (P' : PELUnif (maximalIdeal V) t'), t'.G = G' ∧ HEq t'.grp (inferInstance : GrpObj G') ∧ HEq t'.comm (inferInstance : IsCommMonObj G') ∧ P'.D = D' ∧ HEq P'.mod (inferInstance : Module (𝓞 E) D'.toPre.X) ∧ HEq P'.oD oD' ∧ P'.A = A' ∧ HEq P'.oA oA' ∧ HEq P'.U U' := by
  intro _ _ _ _ V _ _ _ _ E _ _ _ H t P n D' A' G' _ _ pD pA pG U' Q
  letI := H.starRing
  intro md oD' hxi hoD
  have hx : ∀ (a : 𝓞 E) (x : D'.toPre.X), pD.xe (a • x) = a • pD.xe x := fun a x => funext fun i => hxi a x i
  obtain ⟨act', hact⟩ := (GlobalTheory.exists_powAct _ _ _ n pG).2 _ t.act
  have iso : LBIso U'.LG.L (boxLB t.PP.L pG.pr) := by
    rw [← P.bundle]; exact ⟨Q.wL, Q.wL_gen⟩
  let t' : SAB H (Sp V) :=
    { G := G'
      semi := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ n pG t.semi
      act := act'
      PP := U'.LG
      cub := U'.cubG
      sym := isSymmetric_of_symmetry_generator U'.LG U'.symG U'.symG_gen U'.symG_rig
      adj := fun a => GlobalTheory.PowAdj.lbIso_cube_pow _ _ _ n pG _ _ t.PP.isLB U'.LG.isLB iso _ _ _ _ (hact a) (hact (H.bar a)) (t.adj a)
      prim := GlobalTheory.PowPrimitive.lbIso_cube_pow _ _ _ n pG _ _ t.PP.isLB U'.LG.isLB iso _ _ (hact H.w0) t.prim }
  obtain ⟨rA, hrA⟩ := (GlobalTheory.exists_powAct _ _ _ n pA.toIsPowGrp).1 _ P.oA.toRingAct
  let oA' : A'.OAct (𝓞 E) :=
    { toRingAct := rA
      rosati := fun a => GlobalTheory.rosatiAdj_pow _ _ _ n pA.toIsPowGrp _ _ P.A.isLB A'.isLB ⟨pA.w, pA.w_gen⟩ _ _ _ _ (hrA a)
        (hrA (star a)) (P.oA.rosati a) }
  let P' : PELUnif (maximalIdeal V) t' :=
    { D := D'
      oD := oD'
      A := A'
      oA := oA'
      U := U'
      bundle := rfl
      lin := GlobalTheory.oLinear_of_unifPow V (maximalIdeal V) n _ _ _ _ _ _ pD pA pG U' P.U Q _ hx P.oD oD' P.oA oA'
        t.act.toRingAct act'.toRingAct hoD hrA hact P.lin
      w0 := GlobalTheory.PsiWZeroProd.main V n _ _ pD _ hx P.oD oD' hoD H.w0 P.w0 }
  exact ⟨oA', hrA, t', P', rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesShiftEqTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesShiftEqTranslate
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

noncomputable section
namespace GlobalTheory.MomOne.Transfer
variable {q : ℕ} [Fact q.Prime]

def Tr (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (ζ : ℂ_[q]) (p : ℂ) (F : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ (fun z => F (z + p)) 0 ∧ Bdd (hat ι ℓ F) ∧
    hat ι ℓ (fun z => F (z + p)) = shiftS ζ (hat ι ℓ F)

lemma bdd_add {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f + g) := by
  obtain ⟨A, hf⟩ := hf
  obtain ⟨B, hg⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hf hg).1⟩

lemma bdd_mul {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f * g) := by
  obtain ⟨A, hf⟩ := hf
  obtain ⟨B, hg⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hf hg).2⟩

section
variable {ι : ℂ ≃+* ℂ_[q]} {ℓ : ℂ_[q]⟦X⟧} {ζ : ℂ_[q]} {p : ℂ}

lemma Tr.const (h0 : constantCoeff ℓ = 0) (c : ℂ) : Tr ι ℓ ζ p (fun _ => c) := by
  have h := (TaylorRead.hat_laws q ι ℓ h0).2.1 c
  refine ⟨analyticAt_const, analyticAt_const, ⟨‖ι c‖, fun n => ?_⟩, ?_⟩
  · rw [h, coeff_C]
    split_ifs <;> simp
  · rw [h, Shift.shiftS_C]

lemma Tr.add (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {F G : ℂ → ℂ} (hF : Tr ι ℓ ζ p F)
    (hG : Tr ι ℓ ζ p G) : Tr ι ℓ ζ p (fun z => F z + G z) := by
  have h := (TaylorRead.hat_laws q ι ℓ h0).1
  obtain ⟨f1, f2, f3, f4⟩ := hF
  obtain ⟨g1, g2, g3, g4⟩ := hG
  refine ⟨f1.add g1, f2.add g2, ?_, ?_⟩
  · rw [(h _ _ f1 g1).1]; exact bdd_add f3 g3
  · rw [(h _ _ f1 g1).1, (h _ _ f2 g2).1, f4, g4, Shift.shiftS_add hζ f3 g3]

lemma Tr.mul (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {F G : ℂ → ℂ} (hF : Tr ι ℓ ζ p F)
    (hG : Tr ι ℓ ζ p G) : Tr ι ℓ ζ p (fun z => F z * G z) := by
  have h := (TaylorRead.hat_laws q ι ℓ h0).1
  obtain ⟨f1, f2, f3, f4⟩ := hF
  obtain ⟨g1, g2, g3, g4⟩ := hG
  refine ⟨f1.mul g1, f2.mul g2, ?_, ?_⟩
  · rw [(h _ _ f1 g1).2.1]; exact bdd_mul f3 g3
  · rw [(h _ _ f1 g1).2.1, (h _ _ f2 g2).2.1, f4, g4, Shift.shiftS_mul hζ f3 g3]

lemma Tr.pow (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {F : ℂ → ℂ} (hF : Tr ι ℓ ζ p F) (n : ℕ) :
    Tr ι ℓ ζ p (fun z => F z ^ n) := by
  induction n with
  | zero => simpa using Tr.const (ι := ι) (ζ := ζ) (p := p) h0 1
  | succ n ih => simpa only [pow_succ] using Tr.mul h0 hζ ih hF

lemma Tr.sum (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) (F : ℕ → ℂ → ℂ) (hF : ∀ i, Tr ι ℓ ζ p (F i))
    (n : ℕ) : Tr ι ℓ ζ p (fun z => ∑ i ∈ Finset.range n, F i z) := by
  induction n with
  | zero => simpa using Tr.const (ι := ι) (ζ := ζ) (p := p) h0 0
  | succ n ih => simpa only [Finset.sum_range_succ] using Tr.add h0 hζ ih (hF n)

lemma exists_homog (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {u w : ℂ → ℂ} (hu : Tr ι ℓ ζ p u)
    (hw : Tr ι ℓ ζ p w) (A : Polynomial ℂ) :
    ∃ (k : ℕ) (F : ℂ → ℂ), Tr ι ℓ ζ p F ∧ ∀ z x : ℂ, x * w z = u z → F z = A.eval x * w z ^ k := by
  refine ⟨A.natDegree, fun z => ∑ i ∈ Finset.range (A.natDegree + 1),
    A.coeff i * (u z ^ i * w z ^ (A.natDegree - i)), ?_, fun z x hx => ?_⟩
  · exact Tr.sum h0 hζ (fun i z => A.coeff i * (u z ^ i * w z ^ (A.natDegree - i)))
      (fun i => Tr.mul h0 hζ (Tr.const h0 _) (Tr.mul h0 hζ (hu.pow h0 hζ i) (hw.pow h0 hζ _))) _
  · rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ A.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hi'
    rw [← hx, hj, Nat.add_sub_cancel_left]
    ring

lemma exists_quot (h0 : constantCoeff ℓ = 0) (h1 : coeff 1 ℓ ≠ 0) {f D N : ℂ → ℂ} (S : ℂ_[q]⟦X⟧)
    (hf : MeromorphicAt f 0) (hD : AnalyticAt ℂ D 0) (hN : AnalyticAt ℂ N 0)
    (hD0 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), D z ≠ 0) (he : ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z * D z = N z)
    (hS : S * hat ι ℓ D = hat ι ℓ N) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = f z) ∧ hat ι ℓ ψ = S := by
  obtain ⟨h, hc, hid, hcc, -⟩ := TaylorRead.hat_laws q ι ℓ h0
  have hDne : hat ι ℓ D ≠ 0 := by
    intro hz
    have e : hat ι ℓ D = hat ι ℓ (fun _ => 0) := by rw [hz, hc]; simp
    have e2 := (h _ _ hD analyticAt_const).2.2.2 h1 e
    obtain ⟨z, hz1, hz2⟩ := (hD0.and (e2.filter_mono nhdsWithin_le_nhds)).exists
    exact hz1 hz2
  have hpow : ∀ n : ℕ, hat ι ℓ (fun z => z ^ n) = ℓ ^ n := by
    intro n
    induction n with
    | zero => simpa using hc 1
    | succ n ih =>
      simp only [pow_succ]
      rw [(h (fun z => z ^ n) (fun z => z) (by fun_prop) (by fun_prop)).2.1, ih, hid]
  have key : ∀ (n : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g 0 → (∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = z ^ n * f z) →
      hat ι ℓ g = ℓ ^ n * S := by
    intro n g hg hge
    apply mul_right_cancel₀ hDne
    rw [mul_assoc, hS, ← hpow, ← (h _ _ hg hD).2.1, ← (h (fun z => z ^ n) N (by fun_prop) hN).2.1]
    refine (h _ _ (hg.mul hD) (AnalyticAt.mul (by fun_prop) hN)).2.2.1 ?_
    filter_upwards [hge, he] with z a b
    show g z * D z = z ^ n * N z
    rw [a, ← b, mul_assoc]
  have main : ∀ (n : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g 0 → (∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = z ^ n * f z) →
      ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = f z) ∧ hat ι ℓ ψ = S := by
    intro n
    induction n with
    | zero =>
      intro g hg hge
      exact ⟨g, hg, by simpa using hge, by simpa using key 0 g hg hge⟩
    | succ n ih =>
      intro g hg hge
      have hg0 : g 0 = 0 := by
        have := congrArg constantCoeff (key _ g hg hge)
        rw [hcc] at this
        simpa [h0] using this
      obtain ⟨s, hs⟩ := hg
      refine ih (dslope g 0) ⟨_, hs.has_fpower_series_dslope_fslope⟩ ?_
      filter_upwards [hge, self_mem_nhdsWithin] with z a hz
      have hz' : z ≠ 0 := hz
      rw [dslope_of_ne _ hz', slope_def_field, hg0, a]
      field_simp
      ring
  obtain ⟨n, hn⟩ := hf
  exact main n _ hn (Filter.Eventually.of_forall fun z => by simp)
end

lemma x_ne (M : Mdl q) (hM : M.Ok) (c z₀ : ℂ) : ∀ᶠ z in 𝓝[≠] z₀, M.x z - c ≠ 0 := by
  obtain ⟨-, -, hx, -, u0, w0, du, -, hs⟩ := uw_elliptic_flow q M hM
  have hm : Meromorphic (fun z => M.x z - c) := fun z => (hx.1 z).sub (MeromorphicAt.const c z)
  have h0 : meromorphicOrderAt (fun z => M.x z - c) 0 ≠ ⊤ := by
    intro ht
    rw [meromorphicOrderAt_eq_top_iff] at ht
    obtain ⟨au, aw, -, -, e1, e2⟩ := hs 0 (Or.inl M.L.lattice.zero_mem)
    have dw : deriv M.w 0 = 0 := by
      have := e2.self_of_nhds.2.2
      simpa [u0, w0] using this
    have e3 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), M.u z = c * M.w z := by
      filter_upwards [ht, e1] with z a b
      rw [← b.2.2.1, sub_eq_zero.mp a]
    have e4 : M.u =ᶠ[𝓝 0] fun z => c * M.w z := by
      rw [eventually_nhdsWithin_iff] at e3
      filter_upwards [e3] with z a
      by_cases hz : z = 0
      · simp [hz, u0, w0]
      · exact a hz
    have := e4.deriv_eq
    rw [du, deriv_const_mul _ aw.differentiableAt, dw, mul_zero] at this
    exact hM.1 this
  have h1 := hm.exists_meromorphicOrderAt_ne_top_iff_forall.1 ⟨0, h0⟩ z₀
  rcases (hm z₀).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd (meromorphicOrderAt_eq_top_iff.2 h) h1
  · exact h

lemma tendsto_add_punct (p : ℂ) : Filter.Tendsto (fun z : ℂ => z + p) (𝓝[≠] 0) (𝓝[≠] p) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Filter.Tendsto (fun z : ℂ => z + p) (𝓝 0) (𝓝 (0 + p)) :=
      (continuous_id.add continuous_const).tendsto 0
    rw [zero_add] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using hz

theorem shift_eq_hat_translate : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω ζ : ℂ_[q]) (p : ℂ) (φ : ℂ → ℂ), M.MChart ω → M.At ω ζ p → Ell M.L φ → AnalyticAt ℂ φ 0 → Bdd (hat M.ι (C ω * logS) φ) → ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = φ (z + p)) ∧ hat M.ι (C ω * logS) ψ = shiftS ζ (hat M.ι (C ω * logS) φ) := by
  intro q _ M ω ζ p φ hch hat' hφ hφ0 hφb
  have hM : M.Ok := hch.1
  have h0 : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := hch.2.1
  have hζ : ‖ζ - 1‖ < 1 := hat'.2.1
  obtain ⟨h1, v, xs, ys, -, -, bys, -, -, cys, -, hwy, -⟩ := GlobalTheory.T.integral_weierstrass_chart_xy_unit_series q M _ hch
  obtain ⟨tu, tw⟩ := GlobalTheory.T.multiplicativeShift_eq_translate_by_small_point q M ω ζ p hch hat'
  obtain ⟨m, P, A, B, -, hAB⟩ := GlobalTheory.T.exists_ellipticFunction_mul_prod_eq_xy q M φ hM hφ
  obtain ⟨-, -, -, -, -, -, -, -, hs⟩ := uw_elliptic_flow q M hM
  obtain ⟨au0, aw0, -, -, e0, -⟩ := hs 0 (Or.inl M.L.lattice.zero_mem)
  obtain ⟨aup, awp, -, -, ep, -⟩ := hs p hat'.1
  have htr : AnalyticAt ℂ (fun z : ℂ => z + p) 0 := by fun_prop
  have hu : Tr M.ι (C ω * logS) ζ p M.u :=
    ⟨au0, aup.comp_of_eq htr (zero_add p), ⟨1, hch.2.2.1⟩, tu⟩
  have hw : Tr M.ι (C ω * logS) ζ p M.w := by
    refine ⟨aw0, awp.comp_of_eq htr (zero_add p), ⟨1, ?_⟩, tw⟩
    refine (sup_norm_laws q).2.2.2.2.2 _ ys 0 1 bys cys ?_
    rw [pow_zero, one_mul, mul_comm, hwy]
    intro n
    rw [map_neg, norm_neg, coeff_X_pow]
    split_ifs <;> simp
  set Q : Polynomial ℂ := ∏ i, (Polynomial.X - Polynomial.C (M.x (P i))) with hQ
  obtain ⟨a, FQ, tQ, eQ⟩ := exists_homog h0 hζ hu hw Q
  obtain ⟨b, FA, tA, eA⟩ := exists_homog h0 hζ hu hw A
  obtain ⟨c, FB, tB, eB⟩ := exists_homog h0 hζ hu hw B
  have tD : Tr M.ι (C ω * logS) ζ p (fun z => FQ z * M.w z ^ (b + c + 1)) :=
    tQ.mul h0 hζ (hw.pow h0 hζ _)
  have tN : Tr M.ι (C ω * logS) ζ p
      (fun z => M.w z ^ a * (FA z * M.w z ^ (c + 1) + (-1) * (FB z * M.w z ^ b))) :=
    (hw.pow h0 hζ _).mul h0 hζ ((tA.mul h0 hζ (hw.pow h0 hζ _)).add h0 hζ
      ((Tr.const h0 (-1)).mul h0 hζ (tB.mul h0 hζ (hw.pow h0 hζ _))))
  have hid : ∀ z, (z ∉ M.L.lattice ∧ M.y z ≠ 0 ∧ M.x z * M.w z = M.u z ∧ M.y z * M.w z = -1) →
      φ z * Q.eval (M.x z) = A.eval (M.x z) + B.eval (M.x z) * M.y z →
      φ z * (FQ z * M.w z ^ (b + c + 1)) =
        M.w z ^ a * (FA z * M.w z ^ (c + 1) + (-1) * (FB z * M.w z ^ b)) := by
    intro z e1 e2
    rw [eQ z _ e1.2.2.1, eA z _ e1.2.2.1, eB z _ e1.2.2.1, ← e1.2.2.2]
    linear_combination M.w z ^ (a + b + c + 1) * e2
  have h := (TaylorRead.hat_laws q M.ι _ h0).1
  refine exists_quot h0 h1 _ ?_ tD.2.1 tN.2.1 ?_ ?_ ?_
  · exact MeromorphicAt.comp_analyticAt (f := φ) (g := fun z => z + p) (hφ.1 _) htr
  · have hQ0 : ∀ᶠ z in 𝓝[≠] p, ∀ i, M.x z - M.x (P i) ≠ 0 :=
      Filter.eventually_all.2 fun i => x_ne M hM _ p
    refine (tendsto_add_punct p).eventually (p := fun z => FQ z * M.w z ^ (b + c + 1) ≠ 0) ?_
    filter_upwards [hQ0, ep] with z a1 a2
    have hw0 : M.w z ≠ 0 := by
      intro hz
      have := a2.2.2.2
      rw [hz] at this
      simp at this
    rw [eQ z _ a2.2.2.1]
    refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ hw0)) (pow_ne_zero _ hw0)
    rw [hQ, Polynomial.eval_prod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by simpa using a1 i
  · exact (tendsto_add_punct p).eventually ((ep.and (hAB p)).mono fun z hz => hid z hz.1 hz.2)
  · rw [tD.2.2.2, tN.2.2.2, ← Shift.shiftS_mul hζ hφb tD.2.2.1, ← (h _ _ hφ0 tD.1).2.1]
    congr 1
    exact (h _ _ (hφ0.mul tD.1) tN.1).2.2.1 ((e0.and (hAB 0)).mono fun z hz => hid z hz.1 hz.2)

end GlobalTheory.MomOne.Transfer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesShiftEqTranslateStatement
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cpTransportedTaylorSeries_shift_eq_translate : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω ζ : ℂ_[q]) (p : ℂ) (φ : ℂ → ℂ), M.MChart ω → M.At ω ζ p → Ell M.L φ → AnalyticAt ℂ φ 0 → Bdd (hat M.ι (C ω * logS) φ) → ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = φ (z + p)) ∧ hat M.ι (C ω * logS) ψ = shiftS ζ (hat M.ι (C ω * logS) φ) := by
  first | exact @GlobalTheory.MomOne.Transfer.shift_eq_hat_translate | exact GlobalTheory.MomOne.Transfer.shift_eq_hat_translate | (intros; apply GlobalTheory.MomOne.Transfer.shift_eq_hat_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MeasureOfProducts
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.ProdMeasure
variable {q : ℕ} [Fact q.Prime]

theorem hasSum_pi_prod : ∀ (g : ℕ) (u : Fin g → ℕ → ℂ_[q]) (s : Fin g → ℂ_[q]),
    (∀ i, HasSum (u i) (s i)) → HasSum (fun ν : Fin g → ℕ => ∏ i, u i (ν i)) (∏ i, s i) := by
  haveI : NonarchimedeanRing ℂ_[q] := ⟨NonarchimedeanAddGroup.is_nonarchimedean⟩
  intro g
  induction g with
  | zero =>
    intro u s _
    simpa using hasSum_fintype (fun ν : Fin 0 → ℕ => ∏ i, u i (ν i))
  | succ g ih =>
    intro u s h
    have h1 := (h 0).mul_of_nonarchimedean (ih (fun i => u i.succ) (fun i => s i.succ) fun i => h _)
    rw [← (Fin.consEquiv (fun _ : Fin (g + 1) => ℕ)).hasSum_iff, Fin.prod_univ_succ]
    convert h1 using 1
    funext p
    simp [Fin.consEquiv, Fin.prod_univ_succ]

theorem bd_one_pow {f : ℂ_[q]⟦X⟧} (h : Bd 1 f) (a : ℕ) : Bd 1 (f ^ a) := by
  induction a with
  | zero =>
    intro n
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ a ih =>
    have := ((sup_norm_laws q).1 _ _ _ _ ih h).2
    rwa [mul_one, ← pow_succ] at this

theorem shiftS_pow {ζ : ℂ_[q]} (hζ : ‖ζ - 1‖ < 1) {f : ℂ_[q]⟦X⟧} (h : Bd 1 f) (a : ℕ) :
    shiftS ζ (f ^ a) = shiftS ζ f ^ a := by
  have H := Shift.shift_laws q ζ hζ
  induction a with
  | zero => simpa using H.2.2.1 1
  | succ a ih => rw [pow_succ, (H.2.1 _ _ ⟨1, bd_one_pow h a⟩ ⟨1, h⟩).2, ih, pow_succ]

theorem hat_pow (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (hl : constantCoeff ℓ = 0) (G : ℂ → ℂ)
    (hG : AnalyticAt ℂ G 0) (a : ℕ) : hat ι ℓ (fun z => G z ^ a) = hat ι ℓ G ^ a := by
  have H := TaylorRead.hat_laws q ι ℓ hl
  induction a with
  | zero => simpa using H.2.1 1
  | succ a ih =>
    simp only [pow_succ]
    rw [(H.1 (fun z => G z ^ a) G (hG.pow a) hG).2.1, ih]

theorem prod_fiber_pow {g k : ℕ} (σ : Fin k → Fin g) (x : Fin g → ℂ_[q]) :
    ∏ l, x (σ l) = ∏ i, x i ^ (Finset.univ.filter (fun l => σ l = i)).card := by
  rw [← Finset.prod_fiberwise Finset.univ σ (fun l => x (σ l))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_const]
  exact Finset.prod_congr rfl fun l hl => by rw [(Finset.mem_filter.mp hl).2]

theorem measure_of_products : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (δ : ℂ) (Ω : ℂ_[q]) (θ : ℂ → ℂ), 0 < d → δ ≠ 0 → Ω ≠ 0 → Differentiable ℂ θ → ThetaLaws ι d (Ω / ι δ) θ → ∀ (g m : ℕ) (a : Fin g → ℕ) (c : Fin m → ℂ) (t : Fin m → Fin g → ℂ), (∀ j i, PrimeTo d q (t j i)) → ∃ μ : C(Fin g → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q], (∀ B : ℝ, 0 ≤ B → (‖μ‖ ≤ B ↔ ∀ ν : Fin g → ℕ, ‖∑ j, ι (c j) * ∏ i, coeff (ν i) (hat ι (C (Ω / ι δ) * logS) (U1 d (t j i) θ) ^ a i)‖ ≤ B)) ∧ ∀ (n s : ℕ) (y : Fin g → ℂ), Nat.Coprime s q → (∀ j i, InOK d ((s : ℂ) * t j i)) → (∀ i, Good ι d n s (y i)) → ∀ (k : ℕ) (ys : Fin k → Fin g → ℂ) (F : C(Fin g → ℤ_[q], ℂ_[q])), (∀ A, F A = (∏ i, ι (kap1 d 1 (y i)) ^ (PadicInt.toZModPow n (A i)).val) * ∏ l, (Ω⁻¹ * ∑ i, ι (ys l i) * zc (A i))) → ι (iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∑ j, c j * ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) 0 (fun l => δ⁻¹ • ys l)) = μ F := by
  intro d q _ ι δ Ω θ hd hδ hΩ hθ hL g m a c t ht
  set ω : ℂ_[q] := Ω / ι δ with hω
  have hS : ∀ j i, Bd 1 (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i) :=
    fun j i => bd_one_pow (hL.1 _ (ht j i)) _
  obtain ⟨μ, hμ1, hμ2⟩ := GlobalTheory.MultiMahler.exists_measure_of_bounded_moments q g
    (fun ν => ∑ j, ι (c j) * ∏ i, coeff (ν i) (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i))
    ⟨∑ j, ‖ι (c j)‖, fun ν => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by
      rw [norm_mul, norm_prod]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hS j i _))⟩
  refine ⟨μ, hμ1, ?_⟩
  intro n s y hs hst hy k ys F hF
  have hl : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
    simp [logS, ← coeff_zero_eq_constantCoeff_apply]
  have hdiff : ∀ j i, Differentiable ℂ (W1 d (y i) (U1 d (t j i) θ)) := fun j i =>
    ((heisenbergOne d hd).2.2.1 _ _ ((heisenbergOne d hd).2.2.1 _ _ hθ).1).2
  have hroot : ∀ i, ι (kap1 d 1 (y i)) ^ (q ^ n) = 1 := fun i =>
    (hL.2.1 0 (y i) n s hs ⟨0, 0, by simp⟩ (hy i)).1
  have hf : ∀ (i : Fin g) (e : ℕ), ∃ f : C(ℤ_[q], ℂ_[q]),
      (∀ A, f A = ι (kap1 d 1 (y i)) ^ (PadicInt.toZModPow n A).val * zc A ^ e) ∧
      ∀ j, HasSum (fun r : ℕ => coeff r (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i) *
        (fwdDiff (1 : ℤ_[q]))^[r] f 0)
        (ω ^ e * ι (iteratedDeriv e (fun z => W1 d (y i) (U1 d (t j i) θ) z ^ a i) 0)) := by
    intro i e
    obtain ⟨f, hf, -⟩ := GlobalTheory.T.twisted_measure_moments_eq_shifted_series_jets q 0 _ n e ⟨0, fun r => by simp⟩ (hroot i)
    refine ⟨f, hf, fun j => ?_⟩
    obtain ⟨f', hf', h⟩ := GlobalTheory.T.twisted_measure_moments_eq_shifted_series_jets q _ _ n e ⟨1, hS j i⟩ (hroot i)
    obtain rfl : f' = f := by ext A; rw [hf, hf']
    have han := (hdiff j i).analyticAt 0
    rw [shiftS_pow (ShiftComp.norm_sub_one_lt_of_root (hroot i)) (hL.1 _ (ht j i)),
      ← (hL.2.1 _ _ n s hs (hst j i) (hy i)).2, ← hat_pow ι _ hl _ han,
      (hat_multiplicative_chart q ι ω (fun z => W1 d (y i) (U1 d (t j i) θ) z ^ a i)
        (han.pow (a i))).2.1 e] at h
    exact h
  choose f hf1 hf2 using hf
  let P : (Fin k → Fin g) → C(Fin g → ℤ_[q], ℂ_[q]) := fun σ =>
    ⟨fun A => ∏ i, f i (Finset.univ.filter (fun l => σ l = i)).card (A i), by fun_prop⟩
  have hP : ∀ σ, μ (P σ) = ∑ j, ι (c j) * ∏ i, (ω ^ (Finset.univ.filter (fun l => σ l = i)).card *
      ι (iteratedDeriv (Finset.univ.filter (fun l => σ l = i)).card
        (fun z => W1 d (y i) (U1 d (t j i) θ) z ^ a i) 0)) := by
    intro σ
    refine (hμ2 (fun i => f i (Finset.univ.filter (fun l => σ l = i)).card) (P σ) fun _ => rfl).unique ?_
    have := hasSum_sum (s := Finset.univ) fun j _ =>
      (hasSum_pi_prod g _ _ fun i => hf2 i (Finset.univ.filter (fun l => σ l = i)).card j).mul_left (ι (c j))
    simp only [Finset.sum_mul, mul_assoc]
    simp only [Finset.prod_mul_distrib] at this ⊢
    exact this
  have hFP : F = ∑ σ : Fin k → Fin g, (∏ l, Ω⁻¹ * ι (ys l (σ l))) • P σ := by
    ext A
    rw [hF]
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply,
      smul_eq_mul, P, ContinuousMap.coe_mk, hf1, Finset.mul_sum]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib (f := fun i => ι (kap1 d 1 (y i)) ^ (PadicInt.toZModPow n (A i)).val),
      ← prod_fiber_pow σ (fun i => zc (A i))]
    simp only [← mul_assoc]
    rw [Finset.prod_mul_distrib (g := fun l => zc (A (σ l)))]
    ring
  have hcd : ∀ j, ContDiff ℂ k (fun z : Fin g → ℂ => ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) :=
    fun j => contDiff_prod fun i _ => (((hdiff j i).contDiff).comp (contDiff_apply ℂ (fun _ => ℂ) i)).pow _
  have hit : iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∑ j, c j * ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) 0
      = ∑ j, c j • iteratedFDeriv ℂ k
        (fun z : Fin g → ℂ => ∏ i, W1 d (y i) (U1 d (t j i) θ) (z i) ^ a i) 0 := by
    rw [iteratedFDeriv_sum (fun j _ => contDiff_const.mul (hcd j)), Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact iteratedFDeriv_const_smul_apply' (a := c j) (x := 0) (hcd j).contDiffAt
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hit, hFP, map_sum μ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, hP, smul_eq_mul, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.smul_apply, Finset.mul_sum, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.CoordProdDeriv.iteratedFDeriv_prod_coord g k
    (fun i z => W1 d (y i) (U1 d (t j i) θ) z ^ a i) _ (fun i => (hdiff j i).pow _)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.mul_sum, map_sum, map_mul, map_prod, Pi.smul_apply, smul_eq_mul, map_inv₀]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib (f := fun i => ω ^ (Finset.univ.filter (fun l => σ l = i)).card),
    ← prod_fiber_pow σ (fun _ => ω)]
  have e : ∏ l, (ι δ)⁻¹ * ι (ys l (σ l)) = (∏ l, Ω⁻¹ * ι (ys l (σ l))) * ∏ _l : Fin k, ω := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [hω]; field_simp
  rw [e]
  ring

end GlobalTheory.MomOne.ProdMeasure
end
end
