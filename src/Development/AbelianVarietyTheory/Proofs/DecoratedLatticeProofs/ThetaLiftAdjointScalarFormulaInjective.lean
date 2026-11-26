module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarsOfGivenData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftAdjointKeepsSphericalPartsOffTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SingleSplitLabMemSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpanPoly

open Polynomial

theorem coeff_heckePolyOf_le (n q : ℕ) (a : ℕ → ℂ) {i : ℕ} (hi : i ≤ n) :
    (Formalism.L2.Col.heckePolyOf n q a).coeff i = (-1) ^ i * (q : ℂ) ^ (i * (i - 1) / 2) * a i := by
  unfold Formalism.L2.Col.heckePolyOf
  rw [finsetSum_coeff, Finset.sum_eq_single i]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro b _ hb
    rw [coeff_C_mul_X_pow, if_neg (Ne.symm hb)]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

theorem heckePolyOf_eq_zero (n q : ℕ) (a : ℕ → ℂ) (h : ∀ k ≤ n, a k = 0) :
    Formalism.L2.Col.heckePolyOf n q a = 0 := by
  unfold Formalism.L2.Col.heckePolyOf
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [h k (by simpa [Nat.lt_succ_iff] using hk)]
  simp

theorem single_mem_span (nX nY q : ℕ) (hq : q ≠ 0) (c : ℂ) (hc : c ≠ 0) (B : Polynomial ℂ) (hB : B ≠ 0)
    (z : ℕ → ℕ → ℂ)
    (h : ∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf nX q (fun k => ∑ j ∈ Finset.range (nY + 1), z k j * a j) =
      (Formalism.L2.Col.heckePolyOf nY q a).comp (Polynomial.C c * Polynomial.X) * B)
    (j : Fin (nY + 1)) :
    Pi.single j (1 : ℂ) ∈ Submodule.span ℂ (Set.range fun k : Fin (nX + 1) => fun i : Fin (nY + 1) => z k i) := by
  by_contra hj
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hj inferInstance
  set a : ℕ → ℂ := fun i => if hi : i < nY + 1 then f (Pi.single ⟨i, hi⟩ 1) else 0 with ha
  have hfv : ∀ k : ℕ, f (fun i : Fin (nY + 1) => z k i) = ∑ i ∈ Finset.range (nY + 1), z k i * a i := by
    intro k
    rw [← Fin.sum_univ_eq_sum_range (fun i => z k i * a i)]
    conv_lhs => rw [show (fun i : Fin (nY + 1) => z k i) = ∑ i : Fin (nY + 1), z k i • Pi.single i (1 : ℂ) by
      ext m; simp [Finset.sum_apply, Pi.single_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := Fin.is_le i
    simp [ha, hi]
  have hzero : ∀ k ≤ nX, ∑ i ∈ Finset.range (nY + 1), z k i * a i = 0 := by
    intro k hk
    rw [← hfv k]
    have hm : f (fun i : Fin (nY + 1) => z k i) ∈ Submodule.map f (Submodule.span ℂ (Set.range fun k : Fin (nX + 1) => fun i : Fin (nY + 1) => z k i)) :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨⟨k, by omega⟩, rfl⟩)
    rw [hmap] at hm
    simpa using hm
  have h0 := h a
  rw [heckePolyOf_eq_zero _ _ _ hzero] at h0
  have hcomp : (Formalism.L2.Col.heckePolyOf nY q a).comp (Polynomial.C c * Polynomial.X) = 0 := by
    rcases mul_eq_zero.1 h0.symm with h1 | h1
    · exact h1
    · exact absurd h1 hB
  have hco := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p j) hcomp
  simp only [comp_C_mul_X_coeff, coeff_zero] at hco
  rw [coeff_heckePolyOf_le _ _ _ (Nat.lt_succ_iff.1 j.isLt)] at hco
  have hqc : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have haj : a j = 0 := by
    simpa [hc, hqc] using hco
  apply hf
  have hjle := Fin.is_le j
  simpa [ha, hjle] using haj

end GlobalTheory.SpanPoly

namespace GlobalTheory.SpanPoly

theorem single_splitLab_mem_span : ∀ (nX nY q : ℕ), q ≠ 0 → ∀ (c : ℂ), c ≠ 0 → ∀ (B : Polynomial ℂ), B ≠ 0 → ∀ (z : ℕ → ℕ → ℂ), (∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf nX q (fun k => ∑ j ∈ Finset.range (nY + 1), z k j * a j) = (Formalism.L2.Col.heckePolyOf nY q a).comp (Polynomial.C c * Polynomial.X) * B) → ∀ j ≤ nY, Finsupp.single (splitLab nY j) (1 : ℂ) ∈ Submodule.span ℂ ((fun k => GlobalTheory.Hk3.splitC nY (z k)) '' Set.Iic nX) := by
  intro nX nY q hq c hc B hB z h j hj
  let φ : (Fin (nY + 1) → ℂ) →ₗ[ℂ] (List ℤ →₀ ℂ) :=
    ∑ i : Fin (nY + 1), (Finsupp.lsingle (splitLab nY i)).comp (LinearMap.proj i)
  have hφz : ∀ k, φ (fun i : Fin (nY + 1) => z k i) = GlobalTheory.Hk3.splitC nY (z k) := by
    intro k
    unfold GlobalTheory.Hk3.splitC
    rw [← Fin.sum_univ_eq_sum_range (fun i => Finsupp.single (splitLab nY i) (z k i))]
    simp [φ]
  have hφe : φ (Pi.single (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (nY + 1)) 1) = Finsupp.single (splitLab nY j) (1 : ℂ) := by
    simp only [φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Finsupp.lsingle_apply]
    rw [Finset.sum_eq_single (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (nY + 1))]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  rw [← hφe]
  have hm := Submodule.mem_map_of_mem (f := φ) (single_mem_span nX nY q hq c hc B hB z h ⟨j, Nat.lt_succ_of_le hj⟩)
  rw [Submodule.map_span] at hm
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  exact ⟨k, Set.mem_Iic.2 (Nat.lt_succ_iff.1 k.isLt), (hφz k).symm⟩

end GlobalTheory.SpanPoly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EigSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EigSpan

theorem eig_span : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H), (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) → ∀ P, GlobalTheory.Hk3.Good R t P → ∀ (a : List ℤ → ℂ) (w : R.HE.H) (s : Set (List ℤ →₀ ℂ)), (∀ c ∈ s, h P c w = GlobalTheory.Hk3.evC (Yc D 0) P a c • w) → ∀ c ∈ Submodule.span ℂ s, h P c w = GlobalTheory.Hk3.evC (Yc D 0) P a c • w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t h hh P hP a w s hs c hc
  have inj : Function.Injective R.HE.e := hC.models.HE.1
  have hkAdd : ∀ c c' : List ℤ →₀ ℂ, GlobalTheory.Hk3.hk (Yc D 0) P (c + c') = GlobalTheory.Hk3.hk (Yc D 0) P c + GlobalTheory.Hk3.hk (Yc D 0) P c' :=
    fun c c' => by
      unfold GlobalTheory.Hk3.hk
      exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)
  have hkSmul : ∀ (z : ℂ) (c : List ℤ →₀ ℂ), GlobalTheory.Hk3.hk (Yc D 0) P (z • c) = z • GlobalTheory.Hk3.hk (Yc D 0) P c :=
    fun z c => by
      unfold GlobalTheory.Hk3.hk
      rw [Finsupp.sum_smul_index', Finsupp.smul_sum]
      · simp only [smul_eq_mul, mul_smul]
      · intro; exact zero_smul _ _
  have hkZero : GlobalTheory.Hk3.hk (Yc D 0) P 0 = 0 := by
    unfold GlobalTheory.Hk3.hk; exact Finsupp.sum_zero_index
  have evAdd : ∀ c c' : List ℤ →₀ ℂ, GlobalTheory.Hk3.evC (Yc D 0) P a (c + c') = GlobalTheory.Hk3.evC (Yc D 0) P a c + GlobalTheory.Hk3.evC (Yc D 0) P a c' :=
    fun c c' => by
      unfold GlobalTheory.Hk3.evC
      exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by split_ifs <;> ring)
  have evSmul : ∀ (z : ℂ) (c : List ℤ →₀ ℂ), GlobalTheory.Hk3.evC (Yc D 0) P a (z • c) = z * GlobalTheory.Hk3.evC (Yc D 0) P a c :=
    fun z c => by
      unfold GlobalTheory.Hk3.evC
      rw [Finsupp.sum_smul_index', Finsupp.mul_sum]
      · exact Finsupp.sum_congr fun d _ => by split_ifs <;> simp [mul_assoc]
      · intro; simp
  have evZero : GlobalTheory.Hk3.evC (Yc D 0) P a 0 = 0 := by
    unfold GlobalTheory.Hk3.evC; exact Finsupp.sum_zero_index
  have pAdd : ∀ L L' x, postOn (R.MY 0) (L + L') x = postOn (R.MY 0) L x + postOn (R.MY 0) L' x := by
    intro L L' x; ext v; simp [postOn]
  have pSmul : ∀ (z : ℂ) L x, postOn (R.MY 0) (z • L) x = z • postOn (R.MY 0) L x := by
    intro z L x; ext v; simp [postOn]
  have pZero : ∀ x, postOn (R.MY 0) 0 x = 0 := by
    intro x; ext v; simp [postOn]
  have hAdd : ∀ c c', h P (c + c') w = h P c w + h P c' w := fun c c' =>
    inj (by rw [hh P hP, map_add (f := _), hh P hP, hh P hP, hkAdd, pAdd])
  have hSmul : ∀ (z : ℂ) c, h P (z • c) w = z • h P c w := fun z c =>
    inj (by rw [hh P hP, map_smul, hh P hP, hkSmul, pSmul])
  have hZero : h P 0 w = 0 := inj (by rw [hh P hP, hkZero, pZero, map_zero])
  induction hc using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => rw [hZero, evZero, zero_smul]
  | add x y _ _ hx hy => rw [hAdd, hx, hy, evAdd, add_smul]
  | smul z x _ hx => rw [hSmul, hx, evSmul, mul_smul]

end GlobalTheory.EigSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfSplitVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.SplitLabels

open GlobalTheory.Hk3 GlobalTheory.Hk3.LabDet

theorem evC_single_lab {D : D7} (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) (d : List ℤ) (hd : IsLab V P d) :
    evC V P a (Finsupp.single d 1) = a d := by
  unfold evC
  rw [Finsupp.sum_single_index (by simp), if_pos hd, one_mul]

theorem eq_of_split_vec : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H), (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) → ∀ P, GlobalTheory.Hk3.Good R t P → Formalism.DivisionValues.conjPl P ≠ P → ∀ (c : Pl D.host.E → List ℤ → ℂ) (x w : R.HE.H), x ≠ 0 → (∀ P', GlobalTheory.Hk3.Good R t P' → ∀ cc, h P' cc x = GlobalTheory.Hk3.evC (Yc D 0) P' (fun d => c P' (dualLab d)) cc • x) → (∀ k ≤ (Yc D 0).rank, h P (Finsupp.single (splitLab (Yc D 0).rank k) 1) w = GlobalTheory.Hk3.evC (Yc D 0) P (fun d => c P (dualLab d)) (Finsupp.single (splitLab (Yc D 0).rank k) 1) • w ∧ h (Formalism.DivisionValues.conjPl P) (Finsupp.single (splitLab (Yc D 0).rank k) 1) w = GlobalTheory.Hk3.evC (Yc D 0) (Formalism.DivisionValues.conjPl P) (fun d => c (Formalism.DivisionValues.conjPl P) (dualLab d)) (Finsupp.single (splitLab (Yc D 0).rank k) 1) • w) → ∀ d, GlobalTheory.Hk3.IsLab (Yc D 0) P d → h P (Finsupp.single d 1) w = c P (dualLab d) • w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t h hh P hP hcP c x w hx0 hxe hw d hd
  obtain ⟨-, hgood, -, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev
  have hPA : Good R A.μ0 P := (hgood t P hP).2.2
  have hPc : Good R t (Formalism.DivisionValues.conjPl P) := (hgood t P hP).2.1
  obtain ⟨n, hβ⟩ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  have hlev := GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hβ P
    (by rw [Nat.cast_pow]; exact fun hm => (hgood _ P hPA).1 (P.isPrime.mem_of_pow_mem n hm))
    (fun PP hPP => hPA PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
  have inj : Function.Injective R.HE.e := hC.models.HE.1
  have hmem : ∀ y, R.HE.e y ∈ Mult R.θ (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) :=
    fun y => goodPart_le _ _ _ _ _ (hC.models.HE.2.1 ▸ LinearMap.mem_range_self _ y)
  have hfix : ∀ y, ∀ k ∈ hyp (Yc D 0) P, rRep (R.MY 0) k (R.HE.e y) = R.HE.e y := fun y k hk =>
    mult_lev _ _ _ _ _ (hmem y) k (hlev.1 k hk).1 (hlev.1 k hk).2
  have hop : ∀ P', Good R t P' → ∀ e y, opOf (rRep (R.MY 0)) P' (Finsupp.single e 1) (R.HE.e y) =
      R.HE.e (h P' (Finsupp.single e 1) y) := by
    intro P' hP' e y
    rw [opOf_single, sum_rRep, hh P' hP', GlobalTheory.Hk3.OpsRows.hk_single]
    rfl
  have hu : R.HE.e x ≠ 0 := fun h0 => hx0 (inj (by rw [h0, map_zero]))
  obtain ⟨a, ha, hae⟩ := GlobalTheory.SplitGen.gen_split (Yc D 0) P hcP (MMap (R.MY 0)) (rRep (R.MY 0)) d
  obtain ⟨l, h1, h2⟩ := adjoin_common _ (R.HE.e x) (R.HE.e w) (by
    rintro y ⟨k, hk, rfl | rfl⟩
    · refine ⟨evC (Yc D 0) P (fun d => c P (dualLab d)) (Finsupp.single (splitLab (Yc D 0).rank k) 1), ?_, ?_⟩
      · rw [hop P hP, hxe P hP, map_smul]
      · rw [hop P hP, (hw k hk).1, map_smul]
    · have hc := (GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel (Yc D 0) P).2.2 (Finsupp.single (splitLab (Yc D 0).rank k) 1) _ (rRep (R.MY 0))
      have hdc : dualC (Finsupp.single (splitLab (Yc D 0).rank k) 1) =
          Finsupp.single (dualLab (splitLab (Yc D 0).rank k)) 1 := by
        unfold dualC
        rw [Finsupp.mapDomain_single]
      rw [hdc] at hc
      rw [← hc _ (hfix x), ← hc _ (hfix w)]
      refine ⟨evC (Yc D 0) (Formalism.DivisionValues.conjPl P) (fun d => c (Formalism.DivisionValues.conjPl P) (dualLab d))
        (Finsupp.single (splitLab (Yc D 0).rank k) 1), ?_, ?_⟩
      · rw [hop _ hPc, hxe _ hPc, map_smul]
      · rw [hop _ hPc, (hw k hk).2, map_smul]) a ha
  rw [hae _ (hfix x), hop P hP, hxe P hP, evC_single_lab _ _ _ _ hd, map_smul] at h1
  have hl : l = c P (dualLab d) := (smul_left_injective ℂ hu h1).symm
  rw [hae _ (hfix w), hop P hP, hl, ← map_smul] at h2
  exact inj h2

end GlobalTheory.Hk3.SplitLabels

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftAdjointPreservesHeckeEigenvectorsMatche
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftAdjointPreservesHeckeEigenvectorsMatche
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Hk3


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Hk3.SysE.matched_keeps_eigen : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H), (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) → GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R t) h → ∀ P, GlobalTheory.Hk3.Good R t P → ∀ (cX c0 : List ℤ →₀ ℂ), GlobalTheory.Hk3.MatchE R t P cX c0 → ∀ (x : R.HE.H) (l : ℂ), h P c0 x = l • x → h P c0 (R.Th t (LinearMap.adjoint (R.Th t) x)) = l • R.Th t (LinearMap.adjoint (R.Th t) x) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t h hh hhn P hg cX c0 hM x l hx
  have injE : Function.Injective R.HE.e := hC.models.HE.1
  have hX01 := (GlobalTheory.DefiniteOps.definite_ops R F hC.lev hC.fam hC.models).1 t
  rcases hX01 with ⟨hX, hXo, hXn⟩
  have comm : ∀ y, R.Th t (hX P cX y) = h P c0 (R.Th t y) := by
    intro y
    apply injE
    exact (hM y (hX P cX y) (hXo P hg cX y)).trans (hh P hg c0 (R.Th t y)).symm
  have eX : LinearMap.adjoint (hX P cX) = hX P (dualC (Finsupp.mapRange star (star_zero ℂ) cX)) := hXn.2 P hg cX
  have cX' : Commute (hX P cX) (hX P (dualC (Finsupp.mapRange star (star_zero ℂ) cX))) := hXn.1 P P hg hg _ _
  have nX : Commute (hX P cX) (LinearMap.adjoint (hX P cX)) :=
    @Eq.subst (Module.End ℂ (R.HX t).H) (fun B => Commute (hX P cX) B) _ _ eX.symm cX'
  have eE : LinearMap.adjoint (h P c0) = h P (dualC (Finsupp.mapRange star (star_zero ℂ) c0)) := hhn.2 P hg c0
  have cE : Commute (h P c0) (h P (dualC (Finsupp.mapRange star (star_zero ℂ) c0))) := hhn.1 P P hg hg _ _
  have nE : Commute (h P c0) (LinearMap.adjoint (h P c0)) :=
    @Eq.subst (Module.End ℂ R.HE.H) (fun B => Commute (h P c0) B) _ _ eE.symm cE
  have up : hX P cX (LinearMap.adjoint (R.Th t) x) = l • LinearMap.adjoint (R.Th t) x :=
    GlobalTheory.T.eigenvector_adjoint_intertwiner_normal_operators (R.Th t) (fun _ : Unit => hX P cX) (fun _ : Unit => h P c0)
      (fun _ u => comm u) (fun _ => nX) (fun _ => nE) () l x hx
  have c1 := comm (LinearMap.adjoint (R.Th t) x)
  have c2 : R.Th t (hX P cX (LinearMap.adjoint (R.Th t) x)) = l • R.Th t (LinearMap.adjoint (R.Th t) x) := by
    exact (congrArg (R.Th t) up).trans ((R.Th t).map_smul l _)
  exact c1.symm.trans c2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftAdjointPreservesHeckeEigenvectorsMatcheStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftAdjoint_preserves_heckeEigenvectors_matchedPair : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H), (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) → GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R t) h → ∀ P, GlobalTheory.Hk3.Good R t P → ∀ (cX c0 : List ℤ →₀ ℂ), GlobalTheory.Hk3.MatchE R t P cX c0 → ∀ (x : R.HE.H) (l : ℂ), h P c0 x = l • x → h P c0 (R.Th t (LinearMap.adjoint (R.Th t) x)) = l • R.Th t (LinearMap.adjoint (R.Th t) x) := by
  first | exact @GlobalTheory.Hk3.SysE.matched_keeps_eigen | exact GlobalTheory.Hk3.SysE.matched_keeps_eigen | (intros; apply GlobalTheory.Hk3.SysE.matched_keeps_eigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftAdjointKeepsSphericalPartsOffTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KeptRows
open GlobalTheory.Hk3

section Transfer
open Polynomial GlobalTheory.Hk3.SplitChain
open _root_.Formalism.L2.Col (heckePolyOf blockPoly)

theorem blockPoly_ne_zero (ν : ℂ) (q t : ℕ) : blockPoly ν q t ≠ 0 := by
  intro h
  have h0 : Polynomial.eval 0 (blockPoly ν q t) = 1 := by
    unfold blockPoly
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_one
    intro c _
    simp
  rw [h, eval_zero] at h0
  exact zero_ne_one h0


set_option maxHeartbeats 1000000 in
theorem transfer_good {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A) (hL : GlobalTheory.Chain.LiftInteg D) (hC : Core R F) (hS : SchurAll R) (t : T) (P : Pl D.host.E) (hG : Good R t P)
    (hP : Formalism.DivisionValues.conjPl P ≠ P) :
    ∃ (z : ℕ → ℕ → ℂ) (c : ℂ) (B : ℂ[X]), c ≠ 0 ∧ B ≠ 0 ∧
      (∀ k, k ≤ D.sp.X'.rank → MatchE R t P (Finsupp.single (splitLab D.sp.X'.rank k) 1) (splitC (Yc D 0).rank (z k))) ∧
      ∀ a : ℕ → ℂ, heckePolyOf D.sp.X'.rank (Ideal.absNorm P.asIdeal)
          (fun k => ∑ j ∈ Finset.range ((Yc D 0).rank + 1), z k j * a j) =
        (heckePolyOf (Yc D 0).rank (Ideal.absNorm P.asIdeal) a).comp (C c * X) * B := by
  obtain ⟨q, hq⟩ : ∃ q, q = Ideal.absNorm P.asIdeal := ⟨_, rfl⟩
  rw [← hq]
  have hq0 : q ≠ 0 := by
    rw [hq]
    exact fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨-, g2, -, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev
  have hG' := (g2 t _ hG).2.1
  obtain ⟨u1, u2⟩ := GlobalTheory.T.splittingCharacters_unramified_offLevels R F hC.lev t _ hG
  obtain ⟨v1, v2⟩ := GlobalTheory.T.splittingCharacters_unramified_offLevels R F hC.lev t _ hG'
  have hm := D.R.two_le_m
  have hP' : Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl P) ≠ Formalism.DivisionValues.conjPl P := by rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]; exact hP.symm
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt (Formalism.DivisionValues.conjPl P) (by
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
    exact fun h => hP' (HeightOneSpectrum.ext h))
  obtain ⟨ϖ, h1, h2⟩ : ∃ ϖ ∈ (Formalism.DivisionValues.conjPl P).asIdeal, ϖ ∉ (Formalism.DivisionValues.conjPl P).asIdeal ^ 2 :=
    SetLike.exists_of_lt (Ideal.pow_lt_self _ (Formalism.DivisionValues.conjPl P).ne_bot (Formalism.DivisionValues.conjPl P).isPrime.ne_top 2 le_rfl)
  have h0 : (ϖ : D.host.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 fun h => h2 (h ▸ zero_mem _)
  obtain ⟨x, hx⟩ : ∃ x : (AE D)ˣ, (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) :=
    ⟨Formalism.L2.JoinChr.locU he.1.1 (Units.mk0 _ h0), by
      rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, Units.val_mk0]; ring⟩
  have hY : ∀ j, j ≤ D.R.m → (Yc D j).rank = D.R.r + j * D.R.t := fun j hj => by
    rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj]; rfl
  have hX : D.sp.X'.rank = D.R.r + D.R.m * D.R.t := D.sp.X'_rank
  have hn : ∀ j, D.R.r + (j + 1) * D.R.t = D.R.r + j * D.R.t + D.R.t := fun j => by ring
  let μ := R.toLevCh.mu t
  let ν : ℕ → ℂ := fun i => (((Lift.chrStep μ R.eta (i + 1)).1 x : ℂ) * (Real.sqrt q : ℂ) ^ (D.R.r + i * D.R.t))⁻¹
  let s : ℕ → ℂ := fun i => ν i * (((Lift.chrStep μ R.eta (i + 1)).2 x : ℂ) * (Real.sqrt q : ℂ) ^ (D.R.r + (i + 1) * D.R.t))
  obtain ⟨W, w0, w1⟩ := exists_chain D.R.m (fun j => D.R.r + j * D.R.t)
    fun j => stepMat q (D.R.r + j * D.R.t) D.R.t (ν j) (s j)
  have hmm : D.R.m - 1 + 1 = D.R.m := by omega
  have hfix : FixAll R t P := by
    refine ⟨fun k hk => ?_, ?_, fun i => ?_⟩
    · have := unrPl_step (u2 (k + 1) (by omega) hk.le) u1
      exact (GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace _ _ _ _ _ _ _ (hC.chain.ωY t k hk) hP this.1 this.2).1
    · have := unrPl_step (u2 D.R.m (by omega) le_rfl) u1
      exact (GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace _ _ _ _ _ _ _ (hC.chain.ωX t) hP this.1 this.2).1
    · have := u2 ((i : ℕ) + 1) (by omega) i.2
      exact (GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace _ _ _ _ _ _ _ (hC.thP.ωP i t) hP this (unrPl_mul_inv this u1)).1
  have hσ : ((Real.sqrt q : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hq0)))
  have hs0 : ∀ i, s i ≠ 0 := fun i =>
    mul_ne_zero (inv_ne_zero (mul_ne_zero (Circle.coe_ne_zero _) (pow_ne_zero _ hσ)))
      (mul_ne_zero (Circle.coe_ne_zero _) (pow_ne_zero _ hσ))
  refine ⟨W 0, ∏ i ∈ Finset.Ico 0 D.R.m, s i,
    ∏ i ∈ Finset.Ico 0 D.R.m, blockPoly (ν i * (q : ℂ) ^ (D.R.r + i * D.R.t) * ∏ l ∈ Finset.Ico (i + 1) D.R.m, s l) q D.R.t,
    Finset.prod_ne_zero_iff.2 fun i _ => hs0 i, Finset.prod_ne_zero_iff.2 fun i _ => blockPoly_ne_zero _ _ _,
    fun k hk => ?_, fun a => ?_⟩
  · rw [hY 0 (Nat.zero_le _)]
    refine GlobalTheory.T.matchE_of_chainStep_matches R F hL hC hS t _ hG hfix _ (fun j => splitC (D.R.r + j * D.R.t) (W j k)) ?_ fun j hj => ?_
    · have hW := hC.chain.ωX t
      have h3 := step_match (ν := ν (D.R.m - 1)) (s := s (D.R.m - 1)) hW hP (unrPl_step (u2 D.R.m (by omega) le_rfl) u1)
        (unrPl_step (v2 D.R.m (by omega) le_rfl) v1) he h1 h2 hx (hY _ (Nat.sub_le _ _)) hX
        (by rw [← hn, hmm]) hq (by simp only [ν, hmm, μ]) (by simp only [s, hmm, μ]) (W D.R.m k)
      rw [funext (w0 k), ← hX, splitC_delta hk] at h3
      have h4 := funext (w1 (D.R.m - 1) (by omega) k)
      simp only [hmm] at h4
      rw [funext (w0 k), ← hX] at h4
      simp only [h4]
      exact h3
    · have h3 := step_match (ν := ν j) (s := s j) (hC.chain.ωY t j hj) hP (unrPl_step (u2 (j + 1) (by omega) hj.le) u1)
        (unrPl_step (v2 (j + 1) (by omega) hj.le) v1) he h1 h2 hx (hY _ (by omega)) (hY _ hj.le)
        (hn j) hq rfl rfl (W (j + 1) k)
      simp only [funext (w1 j (by omega) k)]
      exact h3
  · have h3 := chain_poly q D.R.t D.R.m (fun j => D.R.r + j * D.R.t) hn ν s W w0 w1 D.R.m 0 (zero_add _) a
    rw [hX, hY 0 (Nat.zero_le _), h3]

end Transfer


set_option maxHeartbeats 1000000 in
theorem kept : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), Core R F → (∀ t P, Good R t P → Formalism.DivisionValues.conjPl P = P → FixAll R t P) → Kept R := by
  intro hCR hHU D G _ _ Pl0 T A Ks _ _ _ R F hC hFix t c x hx
  have hS : SchurAll R := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCR R
  have hLI := GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hCR D
  have H1 := GlobalTheory.Hk3.OpsRowsTuple.exists_ops_tuple R F hC hS t
  cases H1 with
  | intro h H2 =>
  have hh := H2.1
  have hn := H2.2.1
  have he := H2.2.2.1
  have hin := H2.2.2.2
  by_cases hx0 : x = 0
  · rw [hx0, map_zero, map_zero]
    exact Submodule.zero_mem _
  have hxe : ∀ P, Good R t P → ∀ cc, h P cc x = evC (Yc D 0) P (fun d => c P (dualLab d)) cc • x :=
    fun P hP cc => he c P hP cc x hx
  have hmatch : ∀ P, Good R t P → ∀ cX c0, MatchE R t P cX c0 →
      h P c0 (R.Th t (LinearMap.adjoint (R.Th t) x)) =
        evC (Yc D 0) P (fun d => c P (dualLab d)) c0 • R.Th t (LinearMap.adjoint (R.Th t) x) :=
    fun P hP cX c0 hM => GlobalTheory.T.thetaLiftAdjoint_preserves_heckeEigenvectors_matchedPair R F hC t h hh hn P hP cX c0 hM x _ (hxe P hP c0)
  have evS : ∀ P d, IsLab (Yc D 0) P d →
      evC (Yc D 0) P (fun d => c P (dualLab d)) (Finsupp.single d 1) = c P (dualLab d) := by
    intro P d hd
    unfold GlobalTheory.Hk3.evC
    rw [Finsupp.sum_single_index (by simp), if_pos hd, one_mul]
  have gp := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  have hsplit : ∀ P, Good R t P → Formalism.DivisionValues.conjPl P ≠ P → ∀ k ≤ (Yc D 0).rank,
      h P (Finsupp.single (splitLab (Yc D 0).rank k) 1) (R.Th t (LinearMap.adjoint (R.Th t) x)) =
        evC (Yc D 0) P (fun d => c P (dualLab d)) (Finsupp.single (splitLab (Yc D 0).rank k) 1) •
          R.Th t (LinearMap.adjoint (R.Th t) x) := by
    intro P hP hs k hk
    have HZ := transfer_good R F hLI hC hS t P hP hs
    cases HZ with
    | intro z Hz =>
    cases Hz with
    | intro c0 Hz =>
    cases Hz with
    | intro B Hz =>
    have hz := Hz.2.2.1
    have hq : Ideal.absNorm P.asIdeal ≠ 0 := fun e => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
    have hspan := GlobalTheory.SpanPoly.single_splitLab_mem_span _ _ _ hq c0 Hz.1 B Hz.2.1 z Hz.2.2.2 k hk
    refine GlobalTheory.EigSpan.eig_span R F hC t h hh _ hP _ _ _ ?_ _ hspan
    rintro _ ⟨j, hj, rfl⟩
    exact hmatch _ hP _ _ (hz j hj)
  refine hin c (R.Th t (LinearMap.adjoint (R.Th t) x)) fun P d hP hd => ?_
  by_cases hs : Formalism.DivisionValues.conjPl P = P
  · have HM := (GlobalTheory.Hk3.TwoSidedInert.twoSided_of_inert hHU R F hLI hC hS t P hP hs (hFix t P hP hs)).1.2
      (Finsupp.single d 1)
    cases HM with
    | intro cX hM =>
    have e1 := hmatch P hP cX _ hM
    exact e1.trans (congrArg (fun z : ℂ => z • R.Th t (LinearMap.adjoint (R.Th t) x)) (evS P d hd))
  · have hcP : Good R t (Formalism.DivisionValues.conjPl P) := (gp.2.1 t P hP).2.1
    have hcs : Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl P) ≠ Formalism.DivisionValues.conjPl P := by
      rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl P]
      exact fun e => hs e.symm
    exact GlobalTheory.Hk3.SplitLabels.eq_of_split_vec R F hC t h hh P hP hs c x _ hx0 hxe (fun k hk => ⟨hsplit P hP hs k hk, hsplit _ hcP hcs k hk⟩) d hd

end GlobalTheory.KeptRows

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftAdjointKeepsSphericalPartsOffTupleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_adjoint_keeps_spherical_parts_off_tuple : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ t P, GlobalTheory.Hk3.Good R t P → Formalism.DivisionValues.conjPl P = P → GlobalTheory.Hk3.FixAll R t P) → Kept R := by
  first | exact @GlobalTheory.KeptRows.kept | exact GlobalTheory.KeptRows.kept | (intros; apply GlobalTheory.KeptRows.kept <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepPositiveScalarStandingHypotheses
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepPositiveScalarStandingHypotheses
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.ScalarsRow

theorem scalars_of_heckeFormNS : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite →
    GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram →
    GlobalTheory.Published.UnramifiedDoublingGL → (∀ D : D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D) →
    ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
      [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R := by
  intro hDS hHCF hHCM hCW hCusp hHowe hUD hHk D G _ _ Pl0 T A Ks _ _ _ R F hG
  obtain ⟨L, ⟨P⟩⟩ := hG.params
  exact GlobalTheory.T.thetaChain_steps_positive_multiple_of_LValue hHCF hCusp hDS hHCM hCW hHowe hUD R F hG
    (GlobalTheory.Core.Rk.GapOfNodes.harishChandraNodesFarApart_of_cubic_node_gap D (by simpa using P.nodeGap_ge_cubic_rank)) (hHk D)

theorem scalars : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → (∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D') → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → D.host.ccK = ⊤ → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R := by
  intro hDS hHCF hHCM hCW hCusp hHowe _ hHk _ hUD D G _ _ Pl0 T A Ks _ _ _ R F hG _
  exact scalars_of_heckeFormNS hDS hHCF hHCM hCW hCusp hHowe hUD hHk R F hG

end GlobalTheory.Core.Rk.ScalarsRow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepPositiveScalarStandingHypothesesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStep_positive_scalar_standingHypotheses : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → (∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D') → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → D.host.ccK = ⊤ → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R := by
  first | exact @GlobalTheory.Core.Rk.ScalarsRow.scalars | exact GlobalTheory.Core.Rk.ScalarsRow.scalars | (intros; apply GlobalTheory.Core.Rk.ScalarsRow.scalars <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpInjOfBForm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.UpInjScal

theorem exists_lvals {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hsc : GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R) (t : T) (c : GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.EigSys D)
    (hne : GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c ≠ ⊥) :
    ∃ z : Fin D.R.m → ℝ, (∀ i, 0 < z i) ∧ ∀ i, IsLval R i t c (z i) := by
  obtain ⟨κ, -, hs⟩ := hsc
  obtain ⟨⟨B, hB⟩, hall⟩ := hs t c hne
  obtain ⟨hstep, htop⟩ := hall B hB
  have h : ∀ i : Fin D.R.m, ∃ l, GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.IsLValue R t B ((i : ℕ) + 1) l := by
    intro i
    by_cases hi : (i : ℕ) + 1 < D.R.m
    · obtain ⟨l, hl, -⟩ := hstep i hi
      exact ⟨l, hl⟩
    · have e : (i : ℕ) + 1 = D.R.m := by omega
      obtain ⟨l, hl, -⟩ := htop
      exact ⟨l, by rw [e]; exact hl⟩
  choose z hz using h
  exact ⟨z, fun i => (hz i).2.1, fun i => ⟨B, hB, hz i⟩⟩

end GlobalTheory.Core.Rk.UpInjScal


open GlobalTheory.Hk3 in
theorem GlobalTheory.Core.Rk.upInj_of_bForm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R → ∀ SF, GlobalTheory.Hk3.IsSF R SF → BForm R SF → UpInj R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hI hsc SF hSF hB
  obtain ⟨κ₀, hκ₀, hE⟩ := hB
  have hM := hC.models
  have hs : ∀ (t : T) (c : Eig D), ∃ s : ℝ, 0 < s ∧ ∀ x ∈ EEc R SF c, R.Th t (LinearMap.adjoint (R.Th t) x) = ((s : ℝ) : ℂ) • x := by
    intro t c
    by_cases hne : GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c = ⊥
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      have h1 : R.HE.e x ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c :=
        (GlobalTheory.ChainScalar.mem_rowPart (R := R) hM.HE).1 (GlobalTheory.ChainScalar.eec_le (R := R) hSF t c hM.HE hx)
      rw [hne, Submodule.mem_bot] at h1
      have hx0 : x = 0 := hM.HE.1 (h1.trans (LinearMap.map_zero _).symm)
      subst hx0
      exact ((congrArg (R.Th t) (LinearMap.map_zero _)).trans (LinearMap.map_zero _)).trans (smul_zero _).symm
    · have hz0 : ∃ z : Fin D.R.m → ℝ, (∀ i, 0 < z i) ∧ ∀ i, IsLval R i t c (z i) :=
        GlobalTheory.Core.Rk.UpInjScal.exists_lvals (T := T) R hsc t c hne
      obtain ⟨z, hz, hl⟩ := hz0
      exact ⟨κ₀ * ∏ i, z i, mul_pos hκ₀ (Finset.prod_pos fun i _ => hz i), hE t c z hl⟩
  intro t
  choose s hs0 hsE using hs t
  refine (injective_iff_map_eq_zero _).2 fun x h0 => ?_
  obtain ⟨h, -, -, hsp, -⟩ := GlobalTheory.Hk3.OpsRows.exists_opsE R F hC hS SF hSF
  refine GlobalTheory.AdjointInjectiveOfParts.adjoint_inj_of_parts (R.Th t) (fun c => EEc R SF c) (fun c => ((s c : ℝ) : ℂ))
    (fun c => Complex.ofReal_ne_zero.2 (hs0 c).ne') (fun c x hx => hsE c x hx) ?_ h0
  rw [hsp]; trivial
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftAdjointScalarFormulaInjective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.UpInjRow

theorem upInj : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → (∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D') → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → D.host.ccK = ⊤ → R.Sb = R.Pg → (∀ t P, GlobalTheory.Hk3.Good R t P → Formalism.DivisionValues.conjPl P = P → GlobalTheory.Hk3.FixAll R t P) → ∀ SF, GlobalTheory.Hk3.IsSF R SF → BForm R SF ∧ UpInj R := by
  intro hDS hHCF hHCM hCW hCRD hHowe hWS hHecke hSEC hUD D G _ _ Pl0 T A Ks _ _ _ R F hGiv hcc _hSb hFix SF hSF
  have hSc := GlobalTheory.T.thetaChainStep_positive_scalar_standingHypotheses hDS hHCF hHCM hCW hCRD hHowe hWS hHecke hSEC hUD R F hGiv hcc
  have hK := GlobalTheory.T.thetaLift_adjoint_keeps_spherical_parts_off_tuple hCRD hHowe R F hGiv.core hFix
  have hS := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCRD R
  have hB := GlobalTheory.ChainScalar.bForm R F hGiv.core hS hSc hK SF hSF
  exact ⟨hB, GlobalTheory.Core.Rk.upInj_of_bForm R F hGiv.core hS hGiv.irr hSc SF hSF hB⟩

end GlobalTheory.Core.Rk.UpInjRow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftAdjointScalarFormulaInjectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_adjoint_scalarFormula_injective : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → (∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D') → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → D.host.ccK = ⊤ → R.Sb = R.Pg → (∀ t P, GlobalTheory.Hk3.Good R t P → Formalism.DivisionValues.conjPl P = P → GlobalTheory.Hk3.FixAll R t P) → ∀ SF, GlobalTheory.Hk3.IsSF R SF → BForm R SF ∧ UpInj R := by
  first | exact @GlobalTheory.Core.Rk.UpInjRow.upInj | exact GlobalTheory.Core.Rk.UpInjRow.upInj | (intros; apply GlobalTheory.Core.Rk.UpInjRow.upInj <;> assumption)
end
