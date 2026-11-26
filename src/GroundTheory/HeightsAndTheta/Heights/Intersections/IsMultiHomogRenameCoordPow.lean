module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagPivot
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStC
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LeviOneEqLaplacianThm

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogRenameCoordPow
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace PushforwardArithIntersection

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


open Classical in
def blkW : (Σ k, ι k) → K → ℕ := fun p => Pi.single p.1 1


open Classical in
theorem isMultiHomog_of_wh {s : MRing ι} {a : K → ℕ} (h : IsWeightedHomogeneous (blkW (ι := ι)) s a) :
    IsMultiHomog s a := by
  intro m hm k
  rw [← h (mem_support_iff.mp hm), Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
    Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [blkW]
  · intro b _ hb
    simp [blkW, Ne.symm hb]
  · simp


omit [Fintype K] in
open Classical in
theorem sum_single_eq_extend {K₀ : Type} [Fintype K₀] (κ : K₀ → K) (hκ : Function.Injective κ) (α : K₀ → ℕ) :
    (∑ k, α k • (Pi.single (κ k) 1 : K → ℕ)) = Function.extend κ α 0 := by
  funext k'
  rw [Finset.sum_apply]
  by_cases h : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := h
    rw [hκ.extend_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hκ.ne hb]
    · simp
  · rw [Function.extend_apply' _ _ _ h]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk : k' ≠ κ k := fun e => h ⟨k, e.symm⟩
    simp [hk]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem wh_prod_X_pow {K₀ : Type} [Fintype K₀] (q : K₀ → Σ k, ι k) (α : K₀ → ℕ) :
    IsWeightedHomogeneous (blkW (ι := ι)) (∏ k, (X (q k) : MRing ι) ^ α k) (∑ k, α k • blkW (q k)) :=
  IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_X ℤ _ (q k)).pow (α k)

theorem isMultiHomog_coordPow (i : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) α := by
  have h := wh_prod_X_pow (ι := ι) (fun k => ⟨k, i k⟩) α
  have e : (∑ k, α k • blkW (ι := ι) ⟨k, i k⟩) = α := by
    funext k
    simp only [blkW, Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [e] at h
  exact isMultiHomog_of_wh h


omit [∀ k, Fintype (ι k)] in
theorem isMultiHomog_rename_coordPow {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (i : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k)) (Function.extend κ α 0) := by
  have h := wh_prod_X_pow (ι := ι') (fun k => v ⟨k, i k⟩) α
  have e : (∑ k, α k • blkW (ι := ι') (v ⟨k, i k⟩)) = Function.extend κ α 0 := by
    simp only [blkW, hv.2.2.1]
    exact sum_single_eq_extend κ hv.1 α
  rw [e] at h
  simp only [map_prod, map_pow, rename_X]
  exact isMultiHomog_of_wh h


omit [∀ k, Fintype (ι k)] in
theorem coordPow_not_mem {V : Ideal (MRing ι)} (hV : V.IsPrime) (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ V) (α : K → ℕ) : (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) ∉ V := by
  intro h
  obtain ⟨k, -, hk⟩ := (hV.prod_mem_iff).mp h
  exact hi k (hV.mem_of_pow_mem _ hk)

theorem isSmoothHerm_pull {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {A : HermLine ι} {A' : HermLine ι'} (hA : IsSmoothHerm A) (h : IsPullHerm κ v A A') :
    IsSmoothHerm A' := by
  have e : A'.h = A.h ∘ fun z' p => z' (v p) := funext h.2
  unfold IsSmoothHerm
  rw [e]
  refine hA.comp (contDiff_pi.2 fun p => contDiff_apply ℝ (fun _ => ℂ) (v p)).contDiffOn ?_
  intro z' hz'
  simp only [Set.mem_ofPred_eq] at hz' ⊢
  intro k
  obtain ⟨i', hi'⟩ := hz' (κ k)
  obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨pi, by rw [hp]; exact hi'⟩

theorem genDegAt_zero (h0 : ArithVarZeroStatement) (I : AllFam) : GenDegAt I 0 := by
  intro K _ ι _ K' _ ι' _ κ v P' G J L L' _ hP'
  exact absurd hP' (h0 K' ι' P')

theorem genDegAt_succ (hRat : RatR.Statement) (hCyc : ArithmeticIntersectionCycle.Statement) (hInt : ArithmeticIntersectionIntegral.Statement)
    (I : AllFam) (hI : I.IsFamily) (n : ℕ) (ih : GenDegAt I n) : GenDegAt I (n + 1) := by
  intro K _ ι _ K' _ ι' _ κ v P' G J L L' hv hP' hP hJ hL hLL'
  have hrel := hP.2.1.2.2
  choose i hi using hrel
  have hPp : (imageZ v P').IsPrime := hP.2.1.1
  let α : K → ℕ := fun k => ((L (Fin.last n)).a k).toNat
  let β : K → ℕ := fun k => (-(L (Fin.last n)).a k).toNat
  have hfP := coordPow_not_mem hPp i hi α
  have hgP := coordPow_not_mem hPp i hi β
  have hfP' : rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) ∉ P' := fun h => hfP (Ideal.mem_comap.mpr h)
  have hgP' : rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ β k) ∉ P' := fun h => hgP (Ideal.mem_comap.mpr h)
  have hsec : IsRatSectionOn (imageZ v P') (L (Fin.last n)) (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k)
      (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ β k) :=
    ⟨α, β, isMultiHomog_coordPow i α, isMultiHomog_coordPow i β, hfP, hgP,
      fun k => Int.toNat_sub_toNat_neg _⟩
  have hsec' : IsRatSectionOn P' (L' (Fin.last n)) (rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k))
      (rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ β k)) := by
    refine ⟨_, _, isMultiHomog_rename_coordPow hv i α, isMultiHomog_rename_coordPow hv i β, hfP', hgP',
      fun k' => ?_⟩
    rw [(hLL' (Fin.last n)).1, pullDeg]
    by_cases h : ∃ k, κ k = k'
    · obtain ⟨k, rfl⟩ := h
      rw [hv.1.extend_apply, hv.1.extend_apply, hv.1.extend_apply]
      exact Int.toNat_sub_toNat_neg _
    · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
      simp
  have hL' : ∀ j, IsSmoothHerm (L' j) := fun j => isSmoothHerm_pull hv (hL j) (hLL' j)
  have e1 := hRat K' ι' (I K' ι') (hI K' ι') P' n (Fin.init L') (L' (Fin.last n)) _ _ hP'
    (fun j => hL' _) (hL' _) hsec'
  have e2 := hRat K ι (I K ι) (hI K ι) (imageZ v P') n (Fin.init L) (L (Fin.last n)) _ _ hP
    (fun j => hL _) (hL _) hsec
  rw [Fin.snoc_init_self] at e1 e2
  rw [e1, e2, recRRat, recRRat,
    hCyc I hI n ih K ι K' ι' κ v P' G J (Fin.init L) (Fin.init L') _ α hv hP' hP hJ (fun j => hL _)
      (fun j => hLL' _) (isMultiHomog_coordPow i α) hfP,
    hCyc I hI n ih K ι K' ι' κ v P' G J (Fin.init L) (Fin.init L') _ β hv hP' hP hJ (fun j => hL _)
      (fun j => hLL' _) (isMultiHomog_coordPow i β) hgP,
    hInt K ι K' ι' κ v P' n G J (Fin.init L) (Fin.init L') (L (Fin.last n)) (L' (Fin.last n)) _ _ hv hP' hP
      hJ (fun j => hL _) (fun j => hLL' _) (hL _) (hLL' _) hsec]
  ring

end PushforwardArithIntersection

theorem PushforwardArithIntersection.proof (h0 : ArithVarZeroStatement) (hRat : RatR.Statement) (hCyc : ArithmeticIntersectionCycle.Statement)
    (hInt : ArithmeticIntersectionIntegral.Statement) : PushforwardArithIntersection.Statement := by
  unfold PushforwardArithIntersection.Statement GenDegStatement
  intro I hI K _ ι _ K' _ ι' _ κ v P' d G J L L' hv hP' hP hJ hL hLL'
  have key : ∀ n, GenDegAt I n := fun n =>
    Nat.rec (PushforwardArithIntersection.genDegAt_zero h0 I) (fun n ih => PushforwardArithIntersection.genDegAt_succ hRat hCyc hInt I hI n ih) n
  exact key d K ι K' ι' κ v P' G J L L' hv hP' hP hJ hL hLL'

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFSecRed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFSecAt (I : AllFam) (r : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin (r + 1) → HermLine ι')
    (s : MRing ι') (a : K' → ℕ),
    IsBlockMap κ v → IsArithVar P' (d + (r + 1)) → IsArithVar (imageZ v P') d → IsFieldIntersection J →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) →
    (∀ k, (N (Fin.last r)).a k = a k) → IsMultiHomog s a → s ∉ P' →
    I K' ι' P' (d + (r + 1)) (Fin.append L' N) =
      (J (fibreIdeal κ G) (r + 1) (fun j => fibreDeg κ (N j).a) : ℝ) * I K ι (imageZ v P') d L

def PFSecRed.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ r : ℕ, PFSecAt I r → PFAt I (r + 1)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.IsPrimeSpanXb
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def GenericPointExists.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')),
    W'.IsPrime → Nonempty (GenFibre v W')

section Inhabitants

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem imageZ_id (W : Ideal (MRing ι)) : imageZ (ι := ι) (ι' := ι) id W = W := by
  ext f
  simp [imageZ, rename_id]

def genFibreIdOf (W : Ideal (MRing ι)) [W.IsPrime] : GenFibre (ι := ι) (ι' := ι) id W where
  Φ := FnField W
  Φ' := FnField W
  x := genPt W
  x' := genPt W
  ker_x := by
    rw [imageZ_id]
    ext f
    rw [RingHom.mem_ker, aeval_genPt]
    exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk W) f
  gen c := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι ⧸ W) c
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨f, g, ?_, ?_⟩
    · rw [aeval_genPt]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    · rw [aeval_genPt, aeval_genPt]
  genericFibre_ker_target := by
    ext f
    rw [RingHom.mem_ker, aeval_genPt]
    exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk W) f
  compat _ := rfl

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.LeOfHeightMapEqZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityDivisorSupportClosed.le_of_height_map_eq_zero {A : Type*} [CommRing A] {P Q : Ideal A} [P.IsPrime]
    (h : (Q.map (Ideal.Quotient.mk P)).height = 0) : Q ≤ P := by
  intro x hx
  rw [Ideal.height_eq_zero_iff_eq_bot] at h
  have : Ideal.Quotient.mk P x ∈ Q.map (Ideal.Quotient.mk P) := Ideal.mem_map_of_mem _ hx
  rwa [h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this

theorem RegularityDivisorSupportClosed.not_add_add {m : ℕ} {a b : ℕ∞} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ((m : WithBot ℕ∞) + (a : WithBot ℕ∞)) + (b : WithBot ℕ∞) = ((m + 1 : ℕ) : WithBot ℕ∞)) :
    False := by
  have h' : (m : ℕ∞) + a + b = ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
  induction a using ENat.recTopCoe with
  | top => simp at h'; exact ENat.natCast_ne_top (m + 1) (by exact_mod_cast h'.symm)
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp at h'; exact ENat.natCast_ne_top (m + 1) (by exact_mod_cast h'.symm)
    | coe b =>
      have : m + a + b = m + 1 := by exact_mod_cast h'
      have : a ≠ 0 := by exact_mod_cast ha
      have : b ≠ 0 := by exact_mod_cast hb
      omega

theorem RegularityDivisorSupportClosed.proof : RegularityDivisorSupportClosed.Statement := by
  intro K _ ι _ P s a W hP hs hsP
  obtain ⟨-, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP
  have := hPp
  have hsW' : ∀ {Q : Ideal (MRing ι)}, P ⊔ Ideal.span {s} ≤ Q → s ∈ Q := fun h =>
    h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  constructor
  · rintro ⟨hWmin, hWrel⟩
    have h1 := dim_quot_minimal_add_one P W s hsP hWmin
    rw [hPdim] at h1
    refine ⟨⟨⟨hWmin.1.1, isMultiHomogIdeal_of_mem_minimalPrimes hPh hs hWmin, hWrel⟩,
      withBot_eq_of_add_one (by rw [h1, Nat.add_comm])⟩, le_sup_left.trans hWmin.1.2, hsW' hWmin.1.2⟩
  · rintro ⟨⟨⟨hWp, -, hWrel⟩, hWdim⟩, hPW, hsW⟩
    have hle : P ⊔ Ideal.span {s} ≤ W := sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hsW)
    refine ⟨⟨⟨hWp, hle⟩, fun Q hQ hQW => ?_⟩, hWrel⟩
    have := hQ.1
    have hPQ : P ≤ Q := le_sup_left.trans hQ.2
    have e1 := mvPolynomialInt_dimFormula P Q hPQ
    have e2 := mvPolynomialInt_dimFormula Q W hQW
    rw [hPdim] at e1
    rw [hWdim] at e2
    by_contra hWQ
    have ha : (W.map (Ideal.Quotient.mk Q)).height ≠ 0 := fun h0 =>
      hWQ (RegularityDivisorSupportClosed.le_of_height_map_eq_zero h0)
    have hb : (Q.map (Ideal.Quotient.mk P)).height ≠ 0 := fun h0 =>
      hsP (RegularityDivisorSupportClosed.le_of_height_map_eq_zero h0 (hsW' hQ.2))
    rw [← e2] at e1
    exact RegularityDivisorSupportClosed.not_add_add ha hb (by rw [e1, Nat.add_comm])

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace LocRingLocal

set_option linter.unusedSectionVars false

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

end LocRingLocal

theorem LocRingLocal.proof (hF : LocRingFrac.Statement) : LocRingLocal.Statement := by
  intro K _ ι _ P W hP hW hPW
  have := hP
  set F := FractionRing (MRing ι ⧸ P)
  have hnzd : ∀ w : MRing ι, w ∉ W → Ideal.Quotient.mk P w ∈ nonZeroDivisors (MRing ι ⧸ P) := fun w hw =>
    mem_nonZeroDivisors_of_ne_zero fun h => hw (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hne : ∀ w : MRing ι, w ∉ W → algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P w) ≠ 0 := fun w hw =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hnzd w hw)
  have key : ∀ (y : locRing P W) (u v : MRing ι) (a : K → ℕ), IsMultiHomog u a → IsMultiHomog v a → v ∉ W →
      (y : F) * algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P v) = algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P u) →
      (IsUnit y ↔ u ∉ W) := by
    intro y u v a hu hv hvW hy
    constructor
    · rintro hunit huW
      obtain ⟨y', hyy'⟩ := hunit.exists_right_inv
      obtain ⟨u', v', a', -, -, hv'W, hy'⟩ := hF K ι P W hP hW hPW y' y'.2
      have h1 : ((y * y' : locRing P W) : F) = 1 := by rw [hyy']; rfl
      have h2 : algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (v * v')) =
          algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (u * u')) := by
        rw [map_mul, map_mul, map_mul, map_mul, ← hy, ← hy']
        rw [Subring.coe_mul] at h1
        linear_combination (-(algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P v) *
          algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P v'))) * h1
      have h3 := Ideal.Quotient.eq.mp (IsFractionRing.injective (MRing ι ⧸ P) F h2)
      have h4 : v * v' ∈ W := by
        have := W.add_mem (hPW h3) (W.mul_mem_right u' huW)
        simpa using this
      rcases hW.mem_or_mem h4 with h | h
      · exact hvW h
      · exact hv'W h
    · intro huW
      have hz : IsLocalization.mk' F (Ideal.Quotient.mk P v) (⟨_, hnzd u huW⟩ : nonZeroDivisors (MRing ι ⧸ P)) ∈
          locRing P W := Subring.subset_closure ⟨v, u, a, hnzd u huW, huW, hv, hu, rfl⟩
      refine IsUnit.of_mul_eq_one (a := y) ⟨_, hz⟩ (Subtype.ext ?_)
      have hspec := IsLocalization.mk'_spec F (Ideal.Quotient.mk P v)
        (⟨_, hnzd u huW⟩ : nonZeroDivisors (MRing ι ⧸ P))
      simp only [Subring.coe_mul, Subring.coe_one]
      apply mul_right_cancel₀ (hne u huW)
      rw [one_mul, mul_assoc, hspec, hy]
  refine ⟨?_, key⟩
  refine IsLocalRing.of_nonunits_add fun x y hx hy => ?_
  obtain ⟨u, v, a, hu, hv, hvW, hxe⟩ := hF K ι P W hP hW hPW x x.2
  obtain ⟨u', v', a', hu', hv', hv'W, hye⟩ := hF K ι P W hP hW hPW y y.2
  have huW : u ∈ W := by
    by_contra h
    exact hx ((key x u v a hu hv hvW hxe).mpr h)
  have hu'W : u' ∈ W := by
    by_contra h
    exact hy ((key y u' v' a' hu' hv' hv'W hye).mpr h)
  have hvv' : v * v' ∉ W := fun h => (hW.mem_or_mem h).elim hvW hv'W
  have hsum : ((x + y : locRing P W) : F) * algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (v * v')) =
      algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (u * v' + u' * v)) := by
    simp only [Subring.coe_add, map_mul, (algebraMap (MRing ι ⧸ P) F).map_add,
      (Ideal.Quotient.mk P).map_add]
    rw [← hxe, ← hye]
    ring
  have hnum : IsMultiHomog (u * v' + u' * v) (a + a') :=
    LocRingLocal.isMultiHomog_add (AvoidRing.isMultiHomog_mul hu hv')
      (add_comm a' a ▸ AvoidRing.isMultiHomog_mul hu' hv)
  intro hunit
  exact (key (x + y) _ _ (a + a') hnum (AvoidRing.isMultiHomog_mul hv hv') hvv' hsum).mp hunit
    (W.add_mem (W.mul_mem_right v' huW) (W.mul_mem_right v hu'W))

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PDeLeSemiPos
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem pot_cons {e : ℕ} (M : HermLine ι) (L : Fin e → HermLine ι) :
    pot (Fin.cons M L : Fin (e + 1) → HermLine ι) = Fin.cons (fun z => Real.log (M.h z)) (pot L) := by
  funext j z
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [pot]

theorem forall_cons {m : ℕ} {p : HermLine ι → Prop} {M : HermLine ι} {N : Fin m → HermLine ι}
    (hM : p M) (hN : ∀ j, p (N j)) : ∀ j, p ((Fin.cons M N : Fin (m + 1) → HermLine ι) j) :=
  fun j => Fin.cases (by simpa using hM) (fun i => by simpa using hN i) j

theorem ptsIntegral_neg {e : ℕ} (Q : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (f : ((Σ k, ι k) → ℂ) → ℝ) : ptsIntegral Q φ (fun z => -f z) = -ptsIntegral Q φ f := by
  have key : ∀ (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) y w,
      sheetDensity Q Ψ φ (fun z => -f z) y w = -sheetDensity Q Ψ φ f y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs <;> simp
  unfold ptsIntegral ptsIntegralAt
  split_ifs
  · simp only [key, finsum_neg_distrib, MeasureTheory.integral_neg]
  · simp

theorem log_h_eq_neg_logNorm_one (D : HermLine ι) :
    (fun z => Real.log (D.h z)) = fun z => -logNorm D 1 z := by
  funext z
  simp [logNorm, Real.log_inv]

theorem isSectionOn_one {Q : Ideal (MRing ι)} {d : ℕ} (hQ : IsArithVar Q d) {D : HermLine ι}
    (hDa : D.a = 0) : IsSectionOn Q D 1 := by
  refine ⟨0, fun k => by simp [hDa], fun m hm k => ?_,
    fun h => hQ.2.1.1.ne_top ((Ideal.eq_top_iff_one Q).2 h)⟩
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem ptsIntegral_add_first_log (hAdd : PtsAddFirst.Statement) {Q : Ideal (MRing ι)} {e : ℕ}
    {L : Fin e → HermLine ι} {M N D : HermLine ι} (hQ : IsArithVar Q (e + 2))
    (hL : ∀ j, IsSmoothHerm (L j)) (hM : IsSmoothHerm M) (hN : IsSmoothHerm N) (hD : IsSmoothHerm D)
    (hDa : D.a = 0) :
    ptsIntegral Q (Fin.cons (fun z => Real.log ((M.tensor N).h z)) (pot L)) (fun z => Real.log (D.h z)) =
      ptsIntegral Q (Fin.cons (fun z => Real.log (M.h z)) (pot L)) (fun z => Real.log (D.h z)) +
        ptsIntegral Q (Fin.cons (fun z => Real.log (N.h z)) (pot L)) (fun z => Real.log (D.h z)) := by
  rw [log_h_eq_neg_logNorm_one D, ptsIntegral_neg, ptsIntegral_neg, ptsIntegral_neg,
    hAdd K ι Q e L M N D 1 hQ hL hM hN hD (isSectionOn_one hQ hDa)]
  ring

theorem tendsto_finsum_of_finite {α : Type*} {p : α → Prop} (hp : {W | p W}.Finite) {f : ℝ → α → ℝ}
    {g : α → ℝ} {l : Filter ℝ} (h : ∀ W, p W → Tendsto (fun ε => f ε W) l (𝓝 (g W))) :
    Tendsto (fun ε => ∑ᶠ (W) (_ : p W), f ε W) l (𝓝 (∑ᶠ (W) (_ : p W), g W)) := by
  have e : ∀ u : α → ℝ, ∑ᶠ (W) (_ : p W), u W = ∑ W ∈ hp.toFinset, u W :=
    fun u => finsum_mem_eq_finite_toFinset_sum u hp
  have e1 : (fun ε => ∑ᶠ (W) (_ : p W), f ε W) = fun ε => ∑ W ∈ hp.toFinset, f ε W :=
    funext fun ε => e (f ε)
  rw [e1, e g]
  exact tendsto_finsetSum _ fun W hW => h W (hp.mem_toFinset.mp hW)

theorem DeLeSemiPos.proof (hPL1 : ArithmeticPoincareLelongFormula) (hSt : StokesStatement) (hAdd : PtsAddFirst.Statement)
    (hLim : PtsRegLimit.Statement) (hMono : PtsMonoSemiPos.Statement) (hCurv : RegCurvBound.Statement)
    (hNot : HorizNotMem.Statement) : DeLeSemiPos.Statement := by
  intro K _ ι _ P n L A A' s s' hP hL hLp hA hA' hs hs' hnc
  obtain ⟨a, haA, hsa, hsP⟩ := id hs
  obtain ⟨a', haA', hsa', hs'P⟩ := id hs'
  have ht : ∃ b : K → ℕ, (∀ k, A.a k = b k) ∧ IsMultiHomog s b := ⟨a, haA, hsa⟩
  have ht' : ∃ b : K → ℕ, (∀ k, A'.a k = b k) ∧ IsMultiHomog s' b := ⟨a', haA', hsa'⟩
  obtain ⟨C, hC⟩ := hCurv K ι A' s' ht' hA'
  have hT := isSmoothHerm_ofMetrics_fs (ι := ι) (fun _ => (C : ℤ))
  generalize HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun _ => (C : ℤ)) = T at hC hT
  have hfin : ∀ t : MRing ι, {W | W ∈ divSupp P t ∧ IsHorizontal W}.Finite :=
    fun t => (divSupp_finite P t).subset fun W h => h.1

  have e1 : ∀ ε : ℝ, 0 < ε →
      ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L)) (logNorm A s) =
        ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s) +
          ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
              ptsIntegral W (pot L) (fun z => Real.log ((regLine A' s' ht' ε).h z))) -
            ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L))
              (fun z => Real.log ((regLine A' s' ht' ε).h z))) +
          ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s) := by
    intro ε hε
    have hB : IsSmoothHerm (regLine A' s' ht' ε) := isSmoothHerm_regLine hA' hε
    rw [pot_cons, hAdd K ι P n L _ T A s hP hL (isSmoothHerm_tensor hA' hB) hT hA hs,
      hAdd K ι P n L A' _ A s hP hL hA' hB hA hs, hPL1 K ι P n L A _ s hP hL hA hB rfl hs]
  have h1 : Tendsto
      (fun ε => ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L)) (logNorm A s))
      (𝓝[>] 0)
      (𝓝 (ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s) +
        ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
            ptsIntegral W (pot L) (logNorm A' s')) -
          ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm A' s')) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s))) := by
    have ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _ := eventually_mem_nhdsWithin.mono fun ε hε => (e1 ε hε).symm
    refine Tendsto.congr' ev ((tendsto_const_nhds.add
      ((tendsto_finsum_of_finite (hfin s) fun W hW => ?_).sub ?_)).add tendsto_const_nhds)
    · exact (hLim K ι W n L A' s' ht' ((divSuppArith K ι P (n + 1) A s W hP hs hW.1).1 hW.2) hL hA'
        (hNot K ι P (n + 2) s s' W hP hsP hs'P hnc hW.1 hW.2)).const_mul _
    · have h := hLim K ι P (n + 1) (Fin.cons A L) A' s' ht' hP (forall_cons hA hL) hA' hs'P
      rwa [pot_cons] at h

  have h2 : ∀ δ : ℝ, 0 < δ →
      ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s) +
        ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
            ptsIntegral W (pot L) (logNorm A' s')) -
          ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm A' s')) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s) ≤
      (∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
          ptsIntegral W (pot L) (fun z => Real.log ((regLine A s ht δ).h z))) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
          (fun z => Real.log ((regLine A s ht δ).h z)) := by
    intro δ hδ
    have hD : IsSmoothHerm (regLine A s ht δ) := isSmoothHerm_regLine hA hδ
    have hlimD := hLim K ι P (n + 1) (Fin.cons (regLine A s ht δ) L) A' s' ht' hP (forall_cons hD hL) hA'
      hs'P
    rw [pot_cons, hPL1 K ι P n L A' _ s' hP hL hA' hD rfl hs'] at hlimD
    have hR : Tendsto
        (fun ε => ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L))
          (fun z => Real.log ((regLine A s ht δ).h z))) (𝓝[>] 0)
        (𝓝 (ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L))
            (fun z => Real.log ((regLine A s ht δ).h z)) +
          ((∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
              ptsIntegral W (pot L) (fun z => Real.log ((regLine A s ht δ).h z))) -
            ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L))
              (fun z => Real.log ((regLine A s ht δ).h z))) +
          ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
            (fun z => Real.log ((regLine A s ht δ).h z)))) := by
      have eR : ∀ ε : ℝ, 0 < ε →
          ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L))
              (fun z => Real.log ((regLine A s ht δ).h z)) +
            ptsIntegral P (Fin.cons (fun z => Real.log ((regLine A s ht δ).h z)) (pot L))
              (fun z => Real.log ((regLine A' s' ht' ε).h z)) +
            ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
              (fun z => Real.log ((regLine A s ht δ).h z)) =
          ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L))
            (fun z => Real.log ((regLine A s ht δ).h z)) := by
        intro ε hε
        have hB : IsSmoothHerm (regLine A' s' ht' ε) := isSmoothHerm_regLine hA' hε
        rw [pot_cons, ptsIntegral_add_first_log hAdd hP hL (isSmoothHerm_tensor hA' hB) hT hD rfl,
          ptsIntegral_add_first_log hAdd hP hL hA' hB hD rfl,
          hSt K ι P n L (regLine A s ht δ) (regLine A' s' ht' ε) hP hL hD hB rfl rfl]
      have ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _ := eventually_mem_nhdsWithin.mono fun ε hε => eR ε hε
      exact Tendsto.congr' ev ((tendsto_const_nhds.add hlimD).add tendsto_const_nhds)
    have hle := le_of_tendsto_of_tendsto h1 hR (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hMono K ι P (n + 1) _ A (regLine A s ht δ) s hP
        (forall_cons (isSmoothHerm_tensor (isSmoothHerm_tensor hA' (isSmoothHerm_regLine hA' hε)) hT) hL)
        (forall_cons (hC ε hε) hLp) hA hs hD rfl
        (fun z hz h0 => logNorm_le_log_regLine_h hδ.le hz.1 h0))
    linarith

  have h3 : Tendsto
      (fun δ => (∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
          ptsIntegral W (pot L) (fun z => Real.log ((regLine A s ht δ).h z))) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
          (fun z => Real.log ((regLine A s ht δ).h z))) (𝓝[>] 0)
      (𝓝 ((∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
          ptsIntegral W (pot L) (logNorm A s)) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s))) := by
    refine (tendsto_finsum_of_finite (hfin s') fun W hW => ?_).add ?_
    · exact (hLim K ι W n L A s ht ((divSuppArith K ι P (n + 1) A' s' W hP hs' hW.1).1 hW.2) hL hA
        (hNot K ι P (n + 2) s' s W hP hs'P hsP (fun W h h' => hnc W h' h) hW.1 hW.2)).const_mul _
    · have h := hLim K ι P (n + 1) (Fin.cons T L) A s ht hP (forall_cons hT hL) hA hsP
      rwa [pot_cons] at h
  have h4 := ge_of_tendsto h3 (by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact h2 δ hδ)
  unfold De
  linarith

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PSemiPosTwist
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian

namespace SemipositiveTwist

set_option linter.unusedSectionVars false

section Blocks

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_noZeroBlock : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have h : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [h]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

def blk (k : K) : ((Σ k, ι k) → ℂ) →L[ℂ] (ι k → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) ⟨k, i⟩

def F (k : K) (y : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log ((fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩))

theorem blk_ne {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    (fun i => z ⟨k, i⟩ : ι k → ℂ) ≠ 0 := by
  obtain ⟨i, hi⟩ := hz k
  exact fun h0 => hi (congrFun h0 i)

theorem rho_pos {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    0 < (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) :=
  (fsMetric (ι := ι k)).pos _ (blk_ne hz k)

theorem rho_eq (k : K) (y : (Σ k, ι k) → ℂ) :
    (fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩) = Real.sqrt (∑ i, ‖y ⟨k, i⟩‖ ^ 2) := by
  simp [fsMetric, EuclideanSpace.norm_eq]

theorem contDiffAt_F {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    ContDiffAt ℝ 2 (F k) z := by
  have hρ : ContDiffAt ℝ 2 (fsMetric (ι := ι k)).ρ (blk (ι := ι) k z) :=
    ((GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.isSmoothMetric_fs (J := ι k)).contDiffAt
      (isOpen_ne.mem_nhds (blk_ne hz k))).of_le (WithTop.coe_le_coe.2 le_top)
  have hφ := hρ.log (rho_pos hz k).ne'
  have hFk : F k = (fun u => Real.log ((fsMetric (ι := ι k)).ρ u)) ∘ blk (ι := ι) k := rfl
  rw [hFk]
  exact hφ.comp z ((blk (ι := ι) k).restrictScalars ℝ).contDiff.contDiffAt

theorem levi_F_nonneg {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K)
    (w : (Σ k, ι k) → ℂ) : 0 ≤ ReciprocityTheory.AnForm.levi (F k) z w := by
  have hρ : ContDiffAt ℝ 2 (fsMetric (ι := ι k)).ρ (blk (ι := ι) k z) :=
    ((GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.isSmoothMetric_fs (J := ι k)).contDiffAt
      (isOpen_ne.mem_nhds (blk_ne hz k))).of_le (WithTop.coe_le_coe.2 le_top)
  have hφ := hρ.log (rho_pos hz k).ne'
  have hFk : F k = (fun u => Real.log ((fsMetric (ι := ι k)).ρ u)) ∘ blk (ι := ι) k := rfl
  rw [hFk, ReciprocityTheory.AnForm.levi_comp w ((blk (ι := ι) k).analyticAt z) hφ]
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.leviForm_log_fs_nonneg (blk_ne hz k) _

end Blocks

section Levi

variable {J : Type} [Fintype J]

theorem levi_add_sum {K : Type} {z : J → ℂ} (g : (J → ℂ) → ℝ) (f : K → (J → ℂ) → ℝ) (c : K → ℝ)
    (hg : ContDiffAt ℝ 2 g z) (hf : ∀ k, ContDiffAt ℝ 2 (f k) z) (w : J → ℂ) (s : Finset K) :
    ContDiffAt ℝ 2 (fun y => g y + ∑ k ∈ s, c k * f k y) z ∧
      ReciprocityTheory.AnForm.levi (fun y => g y + ∑ k ∈ s, c k * f k y) z w =
        ReciprocityTheory.AnForm.levi g z w + ∑ k ∈ s, c k * ReciprocityTheory.AnForm.levi (f k) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hg
  | insert a s ha ih =>
    have heq : (fun y => g y + ∑ k ∈ insert a s, c k * f k y) =
        fun y => (fun y' => g y' + ∑ k ∈ s, c k * f k y') y + c a * f a y := by
      funext y
      rw [Finset.sum_insert ha]
      ring
    rw [heq, ReciprocityTheory.AnForm.levi_add_smul (c a) ih.1 (hf a) w, ih.2, Finset.sum_insert ha]
    exact ⟨ih.1.add (contDiffAt_const.mul (hf a)), by ring⟩

theorem levi_zero_fun (z w : J → ℂ) : ReciprocityTheory.AnForm.levi (fun _ : J → ℂ => (0 : ℝ)) z w = 0 := by
  simp [ReciprocityTheory.AnForm.levi]

theorem laplacian_line_eq_levi {φ : (J → ℂ) → ℝ} {z : J → ℂ} (hφ : ContDiffAt ℝ 2 φ z) (v : J → ℂ) :
    Δ (fun t : ℂ => φ (z + t • v)) 0 = 4 * ReciprocityTheory.AnForm.levi φ z v := by
  have h1 : ReciprocityTheory.AnForm.levi (fun w : Fin 1 → ℂ => φ (z + w 0 • v)) (fun _ => 0) (Pi.single 0 1) =
      Δ (fun t : ℂ => φ (z + t • v)) 0 / 4 :=
    ReciprocityTheory.AnForm.A.leviOne (fun t : ℂ => φ (z + t • v)) 0
  set L : (Fin 1 → ℂ) →L[ℂ] (J → ℂ) :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight v with hL
  have hτ : AnalyticAt ℂ (fun w => z + L w) (fun _ => 0) :=
    analyticAt_const.add (L.analyticAt _)
  have hτ0 : z + L (fun _ => (0 : ℂ)) = z := by
    simp [hL]
  have hcomp : (fun w : Fin 1 → ℂ => φ (z + w 0 • v)) = φ ∘ fun w => z + L w := by
    funext w
    simp [hL]
  have hD : fderiv ℂ (fun w => z + L w) (fun _ => 0) (Pi.single 0 1) = v := by
    rw [((L.hasFDerivAt).const_add z).fderiv]
    simp [hL]
  have hφ' : ContDiffAt ℝ 2 φ (z + L (fun _ => 0)) := by
    rw [hτ0]
    exact hφ
  rw [hcomp, ReciprocityTheory.AnForm.levi_comp _ hτ hφ', hτ0, hD] at h1
  linarith

end Levi

end SemipositiveTwist


open SemipositiveTwist in
theorem SemiPosTwist.proof (hB : TorusInvLevi.Statement) : SemiPosTwist.Statement := by
  intro K _ ι _ M hM
  classical
  have hUo := isOpen_noZeroBlock (ι := ι)
  set u : ((Σ k, ι k) → ℂ) → ℝ := fun y => Real.log (M.h y) + ∑ k, (-(M.a k : ℝ)) * F k y with hu
  have hlogM : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      ContDiffAt ℝ 2 (fun y => Real.log (M.h y)) z := fun z hz =>
    ((hM.contDiffAt (hUo.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)).log (M.pos z hz).ne'
  have hu2 : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ContDiffAt ℝ 2 u z := fun z hz =>
    (levi_add_sum _ F (fun k => -(M.a k : ℝ)) (hlogM z hz) (contDiffAt_F hz) 0 Finset.univ).1

  have hinv : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      u (fun p => c p.1 * z p) = u z := by
    intro c z hc hz
    have hcn : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
    have hF : ∀ k, F k (fun p => c p.1 * z p) = Real.log ‖c k‖ + F k z := by
      intro k
      show Real.log ((fsMetric (ι := ι k)).ρ (c k • fun i => z ⟨k, i⟩)) =
        Real.log ‖c k‖ + Real.log ((fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩))
      rw [(fsMetric (ι := ι k)).smul, Real.log_mul (hcn k) (rho_pos hz k).ne']
    have hh : Real.log (M.h (fun p => c p.1 * z p)) =
        ∑ k, (M.a k : ℝ) * Real.log ‖c k‖ + Real.log (M.h z) := by
      rw [M.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hcn k))
        (M.pos z hz).ne', Real.log_prod (fun k _ => zpow_ne_zero _ (hcn k))]
      simp only [Real.log_zpow]
    rw [hu]
    show Real.log (M.h (fun p => c p.1 * z p)) + ∑ k, (-(M.a k : ℝ)) * F k (fun p => c p.1 * z p) =
      Real.log (M.h z) + ∑ k, (-(M.a k : ℝ)) * F k z
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
    simp only [zero_add, one_mul, levi_zero_fun] at h
    exact h

  set N : ℕ := ⌈|C| + ∑ k, |(M.a k : ℝ)|⌉₊ with hN
  have hNk : ∀ k, C ≤ (M.a k : ℝ) + N := by
    intro k
    have h1 : |C| + ∑ k, |(M.a k : ℝ)| ≤ N := Nat.le_ceil _
    have h2 : |(M.a k : ℝ)| ≤ ∑ k, |(M.a k : ℝ)| :=
      Finset.single_le_sum (f := fun k => |(M.a k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have h3 := le_abs_self C
    have h4 := neg_abs_le (M.a k : ℝ)
    linarith
  set T : HermLine ι := HermLine.sqMetric (fun _ => N) with hT
  have hlogT : ∀ y : (Σ k, ι k) → ℂ, (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      Real.log (T.h y) = ∑ k, (N : ℝ) * F k y := by
    intro y hy
    have h : T.h y = ∏ k, (fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩) ^ N := by
      simp only [hT, HermLine.sqMetric, rho_eq]
    rw [h, Real.log_prod (fun k _ => pow_ne_zero _ (rho_pos hy k).ne')]
    simp only [Real.log_pow, F]
  refine ⟨T, isSmoothHerm_sqMetric _, ?_, ?_⟩
  · intro z hz v
    have hs := levi_add_sum (fun _ => (0 : ℝ)) F (fun _ => (N : ℝ)) contDiffAt_const (contDiffAt_F hz) v
      Finset.univ
    beta_reduce at hs
    have hev : (fun y => Real.log (T.h y)) =ᶠ[𝓝 z] fun y => 0 + ∑ k, (N : ℝ) * F k y := by
      filter_upwards [hUo.mem_nhds hz] with y hy
      rw [hlogT y hy, zero_add]
    rw [laplacian_line_eq_levi (hs.1.congr_of_eventuallyEq hev) v, ReciprocityTheory.AnForm.levi_congr hev v,
      hs.2, levi_zero_fun, zero_add]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (Nat.cast_nonneg _) (levi_F_nonneg hz k v))
  · intro z hz v
    have hs := levi_add_sum u F (fun k => (M.a k : ℝ) + N) (hu2 z hz) (contDiffAt_F hz) v Finset.univ
    beta_reduce at hs
    have hev : (fun y => Real.log ((M.tensor T).h y)) =ᶠ[𝓝 z]
        fun y => u y + ∑ k, ((M.a k : ℝ) + N) * F k y := by
      filter_upwards [hUo.mem_nhds hz] with y hy
      show Real.log (M.h y * T.h y) = _
      rw [Real.log_mul (M.pos y hy).ne' (T.pos y hy).ne', hlogT y hy, hu]
      simp only [add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      ring
    rw [laplacian_line_eq_levi (hs.1.congr_of_eventuallyEq hev) v, ReciprocityTheory.AnForm.levi_congr hev v, hs.2]
    have hC' : |ReciprocityTheory.AnForm.levi u z v| ≤ C * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
      rw [← hΦ z hz v]
      exact hC z hz v
    have hsum : 0 ≤ ∑ k, ((M.a k : ℝ) + N - C) * ReciprocityTheory.AnForm.levi (F k) z v :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by linarith [hNk k]) (levi_F_nonneg hz k v)
    have hexp : ∑ k, ((M.a k : ℝ) + N) * ReciprocityTheory.AnForm.levi (F k) z v =
        ∑ k, ((M.a k : ℝ) + N - C) * ReciprocityTheory.AnForm.levi (F k) z v +
          C * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h5 := neg_abs_le (ReciprocityTheory.AnForm.levi u z v)
    linarith

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagPivotIdentity
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def FlagPivotIdentity.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) (S : PluckerBlocks n n j),
    flagMinor M j S * ∏ a ∈ Finset.Iic j, leadMinor M a = leadMinor M j * flagMinor (pivotMatrix M) j S

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end
