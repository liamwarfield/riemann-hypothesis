module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PZeroSetNull
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsUnitOfNumMem
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogRenameCoordPow
public import GroundTheory.HeightsAndTheta.Heights.Intersections.RegularizedCurvature

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ThmIExistsFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace ThmIExists

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem hermLine_ext {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  cases ha
  cases hh
  rfl

theorem tensor_right_comm (A B C : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) :
    (A.tensor B).tensor C = (A.tensor C).tensor B :=
  hermLine_ext (add_right_comm _ _ _) (funext fun _ => mul_right_comm _ _ _)

theorem tensor_tensor_comm (A B C D : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) :
    (A.tensor B).tensor (C.tensor D) = (A.tensor C).tensor (B.tensor D) :=
  hermLine_ext (add_add_add_comm _ _ _ _) (funext fun _ => mul_mul_mul_comm _ _ _ _)

theorem smooth_tensor {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) :=
  hA.mul hB

def segreLine (m : ℕ) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι :=
  ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun _ => (m : ℤ))

theorem segreLine_a (m : ℕ) : (segreLine m : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι).a = fun _ => (m : ℤ) := rfl

theorem isSmoothHerm_segreLine (m : ℕ) : IsSmoothHerm (segreLine m : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) := by
  have hfun : (segreLine m : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι).h =
      fun z => ∏ k, Real.sqrt (∑ i : ι k, ‖z ⟨k, i⟩‖ ^ 2) ^ m := by
    funext z
    simp only [segreLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics, fsMetric, zpow_natCast, EuclideanSpace.norm_eq]
  unfold IsSmoothHerm
  rw [hfun]
  refine contDiffOn_prod fun k _ => (ContDiffOn.sqrt ?_ fun z hz => ?_).pow m
  · exact (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      (contDiff_apply ℝ (fun _ => ℂ) (⟨k, i⟩ : Σ k, ι k))).contDiffOn
  · obtain ⟨i, hi⟩ := hz k
    exact (Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩).ne'

theorem exists_form {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (b : K → ℕ) :
    ∃ s : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s b ∧ s ∉ P := by
  classical
  have hrel := hP.2.1.2.2
  have hpr : P.IsPrime := hP.2.1.1
  refine ⟨ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow (fun k => (hrel k).choose) b,
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_xpow _ _, fun h => ?_⟩
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow, Ideal.IsPrime.prod_mem_iff] at h
  obtain ⟨k, _, hk⟩ := h
  exact (hrel k).choose_spec (hpr.mem_of_pow_mem _ hk)


open Classical in
def secOf (P : Ideal (MRing ι)) (b : K → ℕ) : MRing ι :=
  if h : ∃ s : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s b ∧ s ∉ P then h.choose else 0

theorem secOf_spec {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (b : K → ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (secOf P b) b ∧ secOf P b ∉ P := by
  have h := exists_form hP b
  rw [secOf, dite_eq_left h]
  exact h.choose_spec

theorem sec_mul {P : Ideal (MRing ι)} (hpr : P.IsPrime) {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {s t : MRing ι}
    (hs : IsSectionOn P A s) (ht : IsSectionOn P B t) : IsSectionOn P (A.tensor B) (s * t) := by
  obtain ⟨a, ha, has, hsP⟩ := hs
  obtain ⟨b, hb, hbt, htP⟩ := ht
  refine ⟨a + b, fun k => ?_, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul has hbt, fun h => ?_⟩
  · simp [ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ha, hb]
  · rcases hpr.mem_or_mem h with h | h
    exacts [hsP h, htP h]

theorem sec_congr {P : Ideal (MRing ι)} {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {s : MRing ι} (h : A = B)
    (hs : IsSectionOn P A s) : IsSectionOn P B s := h ▸ hs

def shift (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) : ℕ := ∑ k, (A.a k).natAbs

def upDeg (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) : K → ℕ := fun k => (A.a k + shift A).toNat

theorem upDeg_cast (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (k : K) : ((upDeg A k : ℕ) : ℤ) = A.a k + shift A := by
  rw [upDeg, Int.toNat_of_nonneg]
  have h1 : (A.a k).natAbs ≤ shift A :=
    Finset.single_le_sum (f := fun k => (A.a k).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have h2 : -((A.a k).natAbs : ℤ) ≤ A.a k := by
    rw [Int.natCast_natAbs]; exact neg_abs_le _
  omega

theorem isSectionOn_up {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) :
    IsSectionOn P (A.tensor (segreLine (shift A))) (secOf P (upDeg A)) :=
  ⟨upDeg A, fun _ => by simp [ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, segreLine_a, upDeg_cast], (secOf_spec hP _).1,
    (secOf_spec hP _).2⟩

theorem isSectionOn_segre {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (m : ℕ) :
    IsSectionOn P (segreLine m) (secOf P fun _ => m) :=
  ⟨fun _ => m, fun _ => rfl, (secOf_spec hP _).1, (secOf_spec hP _).2⟩

def lift {n : ℕ} (J : Ideal (MRing ι) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ) :
    Ideal (MRing ι) → (m : ℕ) → (Fin m → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ :=
  fun W m L => if h : m = n then J W (L ∘ Fin.cast h.symm) else 0

theorem lift_self {n : ℕ} (J : Ideal (MRing ι) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ) (W : Ideal (MRing ι))
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) : lift J W n L = J W L := by
  simp only [lift]
  rfl

theorem recR_congr {I J : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ} {n : ℕ}
    (h : ∀ W L, I W n L = J W n L) (P : Ideal (MRing ι)) (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (s : MRing ι) : recR I P L A s = recR J P L A s := by
  unfold recR
  simp only [h]

def step {n : ℕ} (J : Ideal (MRing ι) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ) (P : Ideal (MRing ι))
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) : ℝ :=
  recR (lift J) P L (A.tensor (segreLine (shift A))) (secOf P (upDeg A)) -
    recR (lift J) P L (segreLine (shift A)) (secOf P fun _ => shift A)

def fam : (n : ℕ) → Ideal (MRing ι) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => fun P L => step (fam n) P (Fin.init L) (L (Fin.last n))

def famI : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ := fun P n L => fam n P L

theorem famI_snoc (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) :
    famI P (n + 1) (Fin.snoc L A) =
      recR famI P L (A.tensor (segreLine (shift A))) (secOf P (upDeg A)) -
        recR famI P L (segreLine (shift A)) (secOf P fun _ => shift A) := by
  have hc : ∀ (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι), recR (lift (fam n)) P L B s = recR famI P L B s :=
    fun B s => recR_congr (fun W L' => lift_self (fam n) W L') P L B s
  have hs : famI P (n + 1) (Fin.snoc L A) = step (fam n) P L A := by
    simp only [famI, fam, Fin.init_snoc, Fin.snoc_last]
  rw [hs, step, hc, hc]

def LastAddAt (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ) (n : ℕ) : Prop :=
  ∀ (P : Ideal (MRing ι)) (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    I P (n + 1) (Fin.snoc L (A.tensor B)) = I P (n + 1) (Fin.snoc L A) + I P (n + 1) (Fin.snoc L B)

def WDAt (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ) (n : ℕ) : Prop :=
  ∀ (P : Ideal (MRing ι)) (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s t : MRing ι),
    IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm B →
    IsSectionOn P B s → IsSectionOn P B t → recR I P L B s = recR I P L B t

section Steps

variable (hMul : RMulStatement) {n : ℕ} (hwd : WDAt (famI (ι := ι)) n)
include hMul hwd

theorem famI_eq_diff {P : Ideal (MRing ι)} (hP : IsArithVar P (n + 1)) {L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hL : ∀ j, IsSmoothHerm (L j)) {A C : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (hC : IsSmoothHerm C)
    {t c : MRing ι} (ht : IsSectionOn P (A.tensor C) t) (hc : IsSectionOn P C c) :
    famI P (n + 1) (Fin.snoc L A) = recR famI P L (A.tensor C) t - recR famI P L C c := by
  have hpr : P.IsPrime := hP.2.1.1
  set H : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := segreLine (shift A)
  have hH : IsSmoothHerm H := isSmoothHerm_segreLine _
  have hu := isSectionOn_segre hP (shift A)
  have ht0 := isSectionOn_up hP A
  have e1 := hMul K ι famI P n L (A.tensor H) C _ _ hP hL (smooth_tensor hA hH) hC ht0 hc
  have e2 := hMul K ι famI P n L (A.tensor C) H _ _ hP hL (smooth_tensor hA hC) hH ht hu
  have e3 : recR famI P L ((A.tensor H).tensor C) (secOf P (upDeg A) * c) =
      recR famI P L ((A.tensor C).tensor H) (t * secOf P fun _ => shift A) := by
    rw [tensor_right_comm A H C]
    exact hwd P L _ _ _ hP hL (smooth_tensor (smooth_tensor hA hC) hH)
      (sec_congr (tensor_right_comm A H C) (sec_mul hpr ht0 hc)) (sec_mul hpr ht hu)
  rw [famI_snoc]
  linarith

theorem hasRAt_famI : HasRAt (famI (ι := ι)) n := by
  intro P L A s hP hL hA hs
  have hpr : P.IsPrime := hP.2.1.1
  have hH : IsSmoothHerm (segreLine (shift A) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) := isSmoothHerm_segreLine _
  have hu := isSectionOn_segre hP (shift A)
  rw [famI_eq_diff hMul hwd hP hL hA hH (sec_mul hpr hs hu) hu,
    hMul K ι famI P n L A _ s _ hP hL hA hH hs hu]
  ring

theorem lastAddAt_famI : LastAddAt (famI (ι := ι)) n := by
  intro P L A B hP hL hA hB
  have hpr : P.IsPrime := hP.2.1.1
  set Ha : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := segreLine (shift A)
  set Hb : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := segreLine (shift B)
  have hHa : IsSmoothHerm Ha := isSmoothHerm_segreLine _
  have hHb : IsSmoothHerm Hb := isSmoothHerm_segreLine _
  have hua := isSectionOn_segre hP (shift A)
  have hub := isSectionOn_segre hP (shift B)
  have hta := isSectionOn_up hP A
  have htb := isSectionOn_up hP B
  have htab : IsSectionOn P ((A.tensor B).tensor (Ha.tensor Hb))
      (secOf P (upDeg A) * secOf P (upDeg B)) :=
    sec_congr (tensor_tensor_comm A Ha B Hb) (sec_mul hpr hta htb)
  rw [famI_eq_diff hMul hwd hP hL (smooth_tensor hA hB) (smooth_tensor hHa hHb) htab (sec_mul hpr hua hub),
    famI_eq_diff hMul hwd hP hL hA hHa hta hua, famI_eq_diff hMul hwd hP hL hB hHb htb hub,
    tensor_tensor_comm A B Ha Hb,
    hMul K ι famI P n L _ _ _ _ hP hL (smooth_tensor hA hHa) (smooth_tensor hB hHb) hta htb,
    hMul K ι famI P n L _ _ _ _ hP hL hHa hHb hua hub]
  ring

end Steps

theorem wdAt_zero (hD1 : RegularityIndependence.Statement) : WDAt (famI (ι := ι)) 0 := by
  intro P L B s t hP _ _ hs ht
  have hL : L = Fin.elim0 := funext fun j => j.elim0
  subst hL
  exact hD1 K ι famI P B s t hP hs ht

theorem all_dims (hD1 : RegularityIndependence.Statement) (hMul : RMulStatement)
    (hstep : ∀ n, HasRAt (famI (ι := ι)) n → LastAddAt (famI (ι := ι)) n → WDAt (famI (ι := ι)) (n + 1))
    (n : ℕ) : WDAt (famI (ι := ι)) n ∧ HasRAt (famI (ι := ι)) n ∧ LastAddAt (famI (ι := ι)) n := by
  induction n with
  | zero =>
    have h0 := wdAt_zero (ι := ι) hD1
    exact ⟨h0, hasRAt_famI hMul h0, lastAddAt_famI hMul h0⟩
  | succ n ih =>
    have h1 := hstep n ih.2.1 ih.2.2
    exact ⟨h1, hasRAt_famI hMul h1, lastAddAt_famI hMul h1⟩

theorem isRFamily_famI (hD1 : RegularityIndependence.Statement) (hMul : RMulStatement)
    (hstep : ∀ n, HasRAt (famI (ι := ι)) n → LastAddAt (famI (ι := ι)) n → WDAt (famI (ι := ι)) (n + 1)) :
    IsRFamily (famI (ι := ι)) :=
  ⟨fun P n L A B hP hL hA hB => (all_dims hD1 hMul hstep n).2.2 P L A B hP hL hA hB,
    fun P n L A s a hP hL hA ha hs hsP =>
      (all_dims hD1 hMul hstep n).2.1 P L A s hP hL hA ⟨a, ha, hs, hsP⟩⟩

end ThmIExists

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ProofOfNoethPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityLocalFinite.proof (hD : regularityLocalDimension_holds.Statement) : RegularityLocalFinite.Statement := by
  intro K _ ι _ P s a W y hP hs hsP hW hy hy0
  obtain ⟨hloc, hnoeth, hdim⟩ := hD K ι P s a W hP hs hsP hW
  have := hloc
  have := hnoeth
  have : P.IsPrime := hP.2.1.1
  have : IsDomain (locRing P W) := inferInstance
  have : Ring.KrullDimLE 1 (locRing P W) := ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq hdim
  have hfinRes : Finite (IsLocalRing.ResidueField (locRing P W)) :=
    (regularityLocalResidue_holds.proof K ι P s a W (fun i => i.elim0) hP hs hsP hW).1
  letI := hfinRes
  have hy0' : (⟨y, hy⟩ : locRing P W) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  have hfin : Module.length (locRing P W) (locRing P W ⧸ locIdeal P W y) ≠ ⊤ := by
    rw [locIdeal_eq_span hy, span_singleton_eq_range_lsmul]
    exact ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top (locRing P W) hy0'
  have hcard := card_eq_card_residueField_pow_length (locRing P W ⧸ locIdeal P W y) hfin
  have hpos : 0 < Nat.card (IsLocalRing.ResidueField (locRing P W)) := Nat.card_pos
  apply Nat.finite_of_card_ne_zero
  rw [hcard]
  exact pow_ne_zero _ hpos.ne'

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingChartLoc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem LocRingChartLoc.proof : LocRingChartLoc.Statement := by
  classical
  intro K _ ι _ P W hP hW hPW hrel
  let L := FractionRing (MRing ι ⧸ P)
  let q : MRing ι →+* L := (algebraMap (MRing ι ⧸ P) L).comp (Ideal.Quotient.mk P)
  have hq : ∀ f, f ∉ W → q f ≠ 0 := fun f hf h => hf (hPW (by
    rwa [RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h))
  have hnz : ∀ v, v ∉ W → Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P) := fun v hv =>
    mem_nonZeroDivisors_of_ne_zero fun h => hv (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))

  have hfrac : ∀ u v a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog u a → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog v a → v ∉ W → q u / q v ∈ locRing P W := by
    intro u v a hu hv hvW
    refine Subring.subset_closure ⟨u, v, a, hnz v hvW, hvW, hu, hv, ?_⟩
    rw [IsFractionRing.mk'_eq_div]
    rfl
  choose c hc using hrel

  let g : (Σ k, ι k) → L := fun p => q (X p) / q (X ⟨p.1, c p.1⟩)
  let B : Subring L := Subring.closure (Set.range g)
  have hTB : Subring.closure ((Finset.univ.image g : Finset L) : Set L) = B := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hBS : B ≤ locRing P W := Subring.closure_le.mpr (by
    rintro _ ⟨p, rfl⟩
    exact hfrac _ _ _ (AvoidRing.isMultiHomog_X p.1 p.2) (AvoidRing.isMultiHomog_X p.1 (c p.1)) (hc p.1))
  let θ : MRing ι →+* L := eval₂Hom (Int.castRingHom L) g
  have hθB : ∀ f, θ f ∈ B := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => rw [eval₂Hom_C, eq_intCast]; exact intCast_mem _ r
    | add f₁ f₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul_X f p hf => rw [map_mul, eval₂Hom_X']; exact mul_mem hf (Subring.subset_closure ⟨p, rfl⟩)

  have hkey : ∀ u a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog u a → q u = θ u * q (∏ k, X ⟨k, c k⟩ ^ a k) := by
    intro u a hu
    conv_lhs => rw [u.as_sum]
    conv_rhs => rw [u.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.sum_mul, map_prod]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hT : ∏ k, q (X ⟨k, c k⟩ ^ a k) = ∏ p : Σ k, ι k, q (X ⟨p.1, c p.1⟩) ^ m p := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show q (X ⟨k, c k⟩ ^ a k) = ∏ y, q (X ⟨k, c k⟩) ^ m ⟨k, y⟩
      rw [map_pow, Finset.prod_pow_eq_pow_sum, hu m hm k]
    have hθm : θ (monomial m (AddMonoidAlgebra.coeff u m)) = ((AddMonoidAlgebra.coeff u m : ℤ) : L) * ∏ p, g p ^ m p := by
      rw [show θ _ = eval₂ (Int.castRingHom L) g _ from rfl, eval₂_monomial, eq_intCast,
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    have hqm : q (monomial m (AddMonoidAlgebra.coeff u m)) = ((AddMonoidAlgebra.coeff u m : ℤ) : L) * ∏ p, q (X p) ^ m p := by
      rw [monomial_eq, map_mul, map_finsuppProd, Finsupp.prod_fintype _ _ (fun _ => by simp)]
      simp only [map_pow]
      congr 1
      exact eq_intCast (q.comp C) _
    rw [hT, hθm, hqm, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← mul_pow]
    congr 1
    exact (div_mul_cancel₀ _ (hq _ (hc p.1))).symm
  refine ⟨Finset.univ.image g, hTB ▸ hBS, fun z hz => ?_⟩
  rw [hTB]
  obtain ⟨u, v, a, hu, hv, hvW, hzv⟩ := LocRingFrac.proof K ι P W hP hW hPW z hz
  have hTW := AvoidRing.coordProd_not_mem hW c hc a
  have hu' := hkey u a hu
  have hv' := hkey v a hv
  have hinv := hfrac _ v a (AvoidRing.isMultiHomog_coordProd c a) hv hvW
  have hθv : θ v ≠ 0 := fun h => hq v hvW (by rw [hv', h, zero_mul])
  refine ⟨θ u, hθB u, θ v, hθB v, hθv, ?_, ?_⟩
  · have he : (θ v)⁻¹ = q (∏ k, X ⟨k, c k⟩ ^ a k) / q v := by
      rw [eq_div_iff (hq v hvW), hv', ← mul_assoc, inv_mul_cancel₀ hθv, one_mul]
    rw [he]
    exact hinv
  · apply mul_right_cancel₀ (hq _ hTW)
    rw [mul_assoc, ← hv', ← hu']
    exact hzv

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PRegCurvBound
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian RegularizedCurvature MvPolynomial

theorem RegCurvBound.proof (hB : TorusInvLevi.Statement) : RegCurvBound.Statement := by
  intro K _ ι _ E t ht hE
  classical
  have hUo := isOpen_noZeroBlock (ι := ι)
  have hlogH : ∀ M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, IsSmoothHerm M → ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      ContDiffAt ℝ 2 (fun y => Real.log (M.h y)) z := fun M hM z hz =>
    ((hM.contDiffAt (hUo.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)).log (M.pos z hz).ne'
  set u : ((Σ k, ι k) → ℂ) → ℝ := fun y => Real.log (E.h y) + ∑ k, (-(E.a k : ℝ)) * F k y with hu
  have hu2 : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ContDiffAt ℝ 2 u z := fun z hz =>
    (levi_add_sum _ F (fun k => -(E.a k : ℝ)) (hlogH E hE z hz) (contDiffAt_F hz) 0 Finset.univ).1

  have hinv : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      u (fun p => c p.1 * z p) = u z := by
    intro c z hc hz
    have hcn : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
    have hF : ∀ k, F k (fun p => c p.1 * z p) = Real.log ‖c k‖ + F k z := by
      intro k
      show Real.log ((fsMetric (ι := ι k)).ρ (c k • fun i => z ⟨k, i⟩)) =
        Real.log ‖c k‖ + Real.log ((fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩))
      rw [(fsMetric (ι := ι k)).smul, Real.log_mul (hcn k) (rho_pos hz k).ne']
    have hh : Real.log (E.h (fun p => c p.1 * z p)) =
        ∑ k, (E.a k : ℝ) * Real.log ‖c k‖ + Real.log (E.h z) := by
      rw [E.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hcn k))
        (E.pos z hz).ne', Real.log_prod (fun k _ => zpow_ne_zero _ (hcn k))]
      simp only [Real.log_zpow]
    rw [hu]
    show Real.log (E.h (fun p => c p.1 * z p)) + ∑ k, (-(E.a k : ℝ)) * F k (fun p => c p.1 * z p) =
      Real.log (E.h z) + ∑ k, (-(E.a k : ℝ)) * F k z
    rw [hh]
    simp only [hF, mul_add, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
    ring
  obtain ⟨C, hC⟩ := hB K ι u (fun z hz => (hu2 z hz).contDiffWithinAt) hinv

  have hΦ : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ w,
      leviForm (fun y => ∑ k, Real.log ((fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩))) z w =
        ∑ k, ReciprocityTheory.AnForm.levi (F k) z w := by
    intro z hz w
    have h := (levi_add_sum (fun _ => (0 : ℝ)) F (fun _ => 1) contDiffAt_const (contDiffAt_F hz) w
      Finset.univ).2
    simp only [zero_add, one_mul, levi_const] at h
    exact h

  set N : ℕ := ⌈|C| + ∑ k, |(E.a k : ℝ)|⌉₊ with hN
  have hNk : ∀ k, C ≤ (E.a k : ℝ) + N := by
    intro k
    have h1 : |C| + ∑ k, |(E.a k : ℝ)| ≤ N := Nat.le_ceil _
    have h2 : |(E.a k : ℝ)| ≤ ∑ k, |(E.a k : ℝ)| :=
      Finset.single_le_sum (f := fun k => |(E.a k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have h3 := le_abs_self C
    have h4 := neg_abs_le (E.a k : ℝ)
    linarith
  refine ⟨N, fun ε hε => ?_⟩
  set R : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := regLine E t ht ε with hR
  have hRs : IsSmoothHerm R := isSmoothHerm_regLine hE hε
  intro z hz v
  have hW0 : 0 ≤ ∑ k, ReciprocityTheory.AnForm.levi (F k) z v :=
    Finset.sum_nonneg fun k _ => levi_F_nonneg hz k v

  have hLW : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log (E.h y)) z v +
      N * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
    have hs := levi_add_sum u F (fun k => (E.a k : ℝ)) (hu2 z hz) (contDiffAt_F hz) v Finset.univ
    have hfun : (fun y => u y + ∑ k, (E.a k : ℝ) * F k y) = fun y => Real.log (E.h y) := by
      funext y
      simp only [hu, neg_mul, Finset.sum_neg_distrib]
      ring
    rw [hfun] at hs
    have hC' : |ReciprocityTheory.AnForm.levi u z v| ≤ C * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
      rw [← hΦ z hz v]
      exact hC z hz v
    have hsum : 0 ≤ ∑ k, ((E.a k : ℝ) + N - C) * ReciprocityTheory.AnForm.levi (F k) z v :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by linarith [hNk k]) (levi_F_nonneg hz k v)
    have hexp : ∑ k, (E.a k : ℝ) * ReciprocityTheory.AnForm.levi (F k) z v + N * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v =
        ∑ k, ((E.a k : ℝ) + N - C) * ReciprocityTheory.AnForm.levi (F k) z v +
          C * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h5 := neg_abs_le (ReciprocityTheory.AnForm.levi u z v)
    rw [hs.2]
    linarith

  have hΦ1 : ContDiffAt ℝ 2 (fun y => Real.log (E.h y) + 1 * Real.log (R.h y)) z :=
    (hlogH E hE z hz).add (contDiffAt_const.mul (hlogH R hRs z hz))
  obtain ⟨μ, hμ0, hμ1, hμ⟩ := levi_logSum (h := E.h)
    (T := fun y => eval y (map (Int.castRingHom ℂ) t))
    (Φ := fun y => Real.log (E.h y) + 1 * Real.log (R.h y)) (hlogH E hE z hz)
    (by filter_upwards [hUo.mem_nhds hz] with y hy; exact E.pos y hy) (analyticAt_eval_map t z) hε hΦ1
    (fun y => by rw [hR, log_regLine_h, secNorm, one_mul]) v

  have hs := levi_add_sum (fun y => Real.log (E.h y) + 1 * Real.log (R.h y)) F (fun _ => (N : ℝ)) hΦ1
    (contDiffAt_F hz) v Finset.univ
  have hev : (fun y => Real.log (((E.tensor R).tensor
      (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun _ => (N : ℤ)))).h y)) =ᶠ[𝓝 z]
      fun y => (Real.log (E.h y) + 1 * Real.log (R.h y)) + ∑ k, (N : ℝ) * F k y := by
    filter_upwards [hUo.mem_nhds hz] with y hy
    show Real.log ((E.h y * R.h y) * ∏ k, (fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩) ^ ((N : ℤ))) = _
    rw [Real.log_mul (mul_pos (E.pos y hy) (R.pos y hy)).ne'
        (Finset.prod_pos fun k _ => zpow_pos (rho_pos hy k) _).ne',
      Real.log_mul (E.pos y hy).ne' (R.pos y hy).ne',
      Real.log_prod (fun k _ => (zpow_pos (rho_pos hy k) _).ne')]
    simp only [Real.log_zpow, F, Int.cast_natCast, one_mul]
  rw [laplacian_line_eq_levi (hs.1.congr_of_eventuallyEq hev) v, ReciprocityTheory.AnForm.levi_congr hev v, hs.2,
    ← Finset.mul_sum]
  have hmu : 0 ≤ μ * ReciprocityTheory.AnForm.levi (fun y => Real.log (E.h y)) z v +
      N * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
    rcases le_or_gt 0 (ReciprocityTheory.AnForm.levi (fun y => Real.log (E.h y)) z v) with hL0 | hL0
    · exact add_nonneg (mul_nonneg hμ0 hL0) (mul_nonneg (Nat.cast_nonneg _) hW0)
    · nlinarith
  linarith

end GroundTheory.Heights₂.Heights.Inter
end
end
