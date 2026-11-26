module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsDimZero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGraphChangeOfModel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefProductNonneg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRealFormsOnPoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RealFormsOnPoints.proof (hN : ComplexFormsOnPoints.Statement)
    (hB : IndependentModBaseChange.Statement) : RealFormsOnPoints.Statement := by
  intro K _ ι _ Ω _ y d e r g hP hg hli c hc
  obtain ⟨_, ⟨hprime, -, hrel⟩, -, -⟩ := hP

  have hZ : LinearIndependent ℤ (fun i => Ideal.Quotient.mk (mCoordIdeal y) (g i)) := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro n hn
    apply hli n
    have hmem : ∑ i, n i • g i ∈ mCoordIdeal y := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      simpa only [map_zsmul] using hn
    have h0 : mConeMap y (∑ i, n i • g i) = 0 := hmem
    have hsum : mConeMap y (∑ i, n i • g i) =
        MvPolynomial.C (∑ i, n i • aeval y (g i)) * ∏ k, MvPolynomial.X k ^ e k := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, ProjLine.mConeMap_eq_of_isMultiHomog y (hg i), map_zsmul, smul_mul_assoc]
    rw [hsum] at h0
    have hX : (∏ k, MvPolynomial.X k ^ e k : MvPolynomial K Ω) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)
    exact (MvPolynomial.C_eq_zero).mp ((mul_eq_zero.mp h0).resolve_right hX)

  have hC := hB _ (mCoordIdeal y) r g hZ
  set I := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℂ)) with hI

  have hF : (∑ i, (c i : ℂ) • MvPolynomial.map (Int.castRingHom ℂ) (g i)) ∈ I := by
    refine hN K ι _ hprime hrel _ fun z hz => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simpa only [smul_eval] using hc z hz
  rw [Fintype.linearIndependent_iff] at hC
  funext i
  have h := hC (fun i => (c i : ℂ)) (by
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hF
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hF, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Ideal.Quotient.mkₐ_eq_mk ℂ, map_smul]) i
  exact_mod_cast h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKoszulCech
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace KoszulCech

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, LinearOrder (ι k)]

def frontCell {n : ℕ} (I : KH.Cell K ι n) : KH.Cell K ι 0 :=
  ⟨fun k => {(I.1 k).min' (I.2.1 k)}, fun _ => Finset.singleton_nonempty _, by simp⟩

def restrict0 {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (z : KH.CechC S ι M 0) {n : ℕ}
    (I : KH.Cell K ι n) : LocalizedModule (KH.cellMon S I.1) M :=
  KH.cellRes S M (frontCell I).1 I.1 (z (frontCell I))


variable (S ι) in
abbrev KosC (V : Ideal (MRingOver S ι)) (R p n : ℕ) : Type :=
  {J : Finset (Fin R) // J.card = p} → KH.CechC S ι (MRingOver S ι ⧸ V) n

def kosSign {R : ℕ} (J : Finset (Fin R)) (j : Fin R) : ℤ :=
  (-1) ^ (J.filter (· < j)).card

def kosD {V : Ideal (MRingOver S ι)} {R : ℕ} (z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0) (p n : ℕ) :
    KosC S ι V R (p + 1) n →+ KosC S ι V R p n where
  toFun φ J I := ∑ j : Fin R, if h : j ∈ J.1 then 0 else
    (kosSign J.1 j : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) *
      (restrict0 (z j) I * φ ⟨insert j J.1, by rw [Finset.card_insert_of_notMem h, J.2]⟩ I)
  map_zero' := by
    funext J I
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs
    · rfl
    · exact (congrArg (fun x => (kosSign J.1 j : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) * x)
        (mul_zero (restrict0 (z j) I))).trans (mul_zero _)
  map_add' φ ψ := by
    funext J I
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · exact (add_zero 0).symm
    · exact (congrArg (fun x => (kosSign J.1 j : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) * x)
        (mul_add (restrict0 (z j) I) _ _)).trans (mul_add _ _ _)

variable [LinearOrder K]


variable (S ι) in
def kosCech (V : Ideal (MRingOver S ι)) (R p n : ℕ) : KosC S ι V R p n →+ KosC S ι V R p (n + 1) :=
  (KH.cechD S ι (MRingOver S ι ⧸ V) n).toAddMonoidHom.compLeft _

variable [∀ k, Fintype (ι k)]


variable (S ι) in
def kosPart (V : Ideal (MRingOver S ι)) (R : ℕ) (α c : K → ℤ) (p n : ℕ) : AddSubgroup (KosC S ι V R p n) :=
  (Submodule.pi Set.univ fun _ => KH.cechCc ι (KH.quotPart S V) (c - (p : ℤ) • α) n).toAddSubgroup

end KoszulCech

open KoszulCech

def KoszulCechComplex.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (α : K → ℤ) (R : ℕ)
    (z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0),
    (∀ j, z j ∈ KH.cechZc ι (KH.quotPart S V) α 0) →
    ∀ (c : K → ℤ) (p n : ℕ),
      (∀ φ ∈ kosPart S ι V R α c (p + 1) n, kosD z p n φ ∈ kosPart S ι V R α c p n) ∧
      (∀ φ, kosCech S ι V R p n (kosD z p n φ) = kosD z p (n + 1) (kosCech S ι V R (p + 1) n φ)) ∧
      (∀ φ, kosD z p n (kosD z (p + 1) n φ) = 0)

section Inhabitants

namespace KoszulCech

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]


end KoszulCech

open KoszulCech

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageTop
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

namespace BlockImageTop

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {κ : Type} [Fintype κ]

theorem isMultiHomog_blockForms (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) (q : Σ k, GlobalTheory κ k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (blockForms k₀ M q) (blockDeg k₀ 1) := by
  classical
  intro m hm k
  obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at ht
  have hmt := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
  subst hmt
  by_cases hk : k = k₀
  · subst hk
    simp [blockDeg, Finsupp.single_apply]
  · simp [blockDeg, hk, Sigma.ext_iff]

theorem sub_mem_mCoordIdeal {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix κ) (ι k₀) ℤ}
    {N : Matrix (ι k₀) (Ix κ) ℤ} {x : Ix κ → Ω} (h : IsBlockImage y k₀ M N x) (i : ι k₀) :
    X ⟨k₀, i⟩ - ∑ j, C (N i j) * blockForms k₀ M j ∈ mCoordIdeal y := by
  have hf : ∀ j, mConeMap y (blockForms k₀ M j) = MvPolynomial.C (x j) * MvPolynomial.X k₀ := by
    intro j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h.1 j, map_sum, Finset.sum_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [blockForms, mConeMap, map_sum, mul_assoc]
  have hX : mConeMap y (X ⟨k₀, i⟩) = MvPolynomial.C (y ⟨k₀, i⟩) * MvPolynomial.X k₀ := by
    simp [mConeMap]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [mCoordIdeal, RingHom.mem_ker, map_sub, map_sum]
  simp only [map_mul, hf]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hX, h.2 i, map_sum, Finset.sum_mul, sub_eq_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mConeMap, mul_assoc]

theorem isBasePtFree_blockForms {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix κ) (ι k₀) ℤ}
    {N : Matrix (ι k₀) (Ix κ) ℤ} {x : Ix κ → Ω} (h : IsBlockImage y k₀ M N x) :
    IsBasePtFree (mCoordIdeal y) (blockForms k₀ M) := by
  intro k₂ i
  refine ⟨1, ?_⟩
  rw [pow_one, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k₀)]
  refine Ideal.mul_mem_right _ _ ?_
  have hspan : ∑ j, C (N (i k₀) j) * blockForms k₀ M j ∈
      Ideal.span (Set.range fun j : GlobalTheory κ k₂ => blockForms k₀ M ⟨k₂, j⟩) := by
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j.2, ?_⟩)
    cases k₂
    rfl
  have := Ideal.add_mem _ (Ideal.mem_sup_left (sub_mem_mCoordIdeal h (i k₀))) (Ideal.mem_sup_right hspan)
  rwa [sub_add_cancel] at this

theorem isSmoothHerm_ofCone {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) :
    IsSmoothHerm (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofCone m) := by
  refine hm.mono fun z hz => ?_
  obtain ⟨i, hi⟩ := hz ()
  exact fun h0 => hi (congrFun h0 _)

theorem formApply_blockForms (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) (z : (Σ k, ι k) → ℂ) :
    formApply (blockForms k₀ M) z = blockMapC k₀ M z := by
  funext q
  simp [formApply, blockForms, blockMapC]

end BlockImageTop


open BlockImageTop in
theorem BlockImageTop.proof (hCM : GraphChangeOfModel.Statement) (hIm : BlockGraphImage.Statement)
    (hDeg : BlockGraphDeg.Statement) : BlockImageTop.Statement := by
  intro D K _ _ ι _ Ω _ _ κ _ I y k₀ A M N x m hI hP hB hx hBI ha hA hm hh
  obtain ⟨G, J, hJ, hJ1⟩ := hDeg D K ι Ω κ y k₀ M N x hP hB hx hBI
  have himg := hIm K ι Ω κ y k₀ M N x hBI
  have key := hCM I hI K ι Unit (GlobalTheory κ) (mCoordIdeal y) (D + 1) (blockForms k₀ M) (fun _ => blockDeg k₀ 1) G J
    (fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofCone m) (fun _ => A) hP (isMultiHomog_blockForms k₀ M) (isBasePtFree_blockForms hBI)
    (by rw [himg]; exact hx) hJ (fun _ => isSmoothHerm_ofCone hm) (fun _ => hA)
    (fun _ k => by
      rw [ha]
      by_cases hk : k = k₀ <;> simp [unitDeg, blockDeg, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofCone, hk])
    (fun _ z hz => by rw [hh z hz, formApply_blockForms]; rfl)
  rw [himg, hJ1] at key
  simpa [top] using key

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKleimanNefF
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace KleimanNefF

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiProjPrime_dvr [DecidableEq K] {V : Ideal (MRingOver F ι)} (hV : IsMultiProjPrime V) :
    NumbersDVR.IsMultiProjPrime (R := F) (ι := ι) V :=
  ⟨hV.1, (NumbersDVR.VocabMultiHomogIdeal.proof NumbersDVR.VocabMultiHomog.proof F K ι V).1 hV.2.1, hV.2.2⟩

theorem isProjVarF_of_mem_support [DecidableEq K] {V : Ideal (MRingOver F ι)} {n : ℕ}
    (hV : IsProjVarF V (n + 1)) {f g : MRingOver F ι} {bf bg : K → ℕ}
    (hf : NumbersDVR.IsMultiHomog f bf) (hg : NumbersDVR.IsMultiHomog g bg) (hfV : f ∉ V) (hgV : g ∉ V)
    {W : Ideal (MRingOver F ι)} (hW : W ∈ (ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv V f g).support) :
    IsProjVarF W n := by
  have hVd := isMultiProjPrime_dvr hV.1
  have hrel : FieldNumbers.relDim V = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    (FieldNumbers.CutRegular.relDim_eq_natCast_iff V (n + 1)).2 hV.2
  have key : ∀ (s : MRingOver F ι) (b : K → ℕ), NumbersDVR.IsMultiHomog s b → s ∉ V →
      ReciprocityTheory.ChartRestriction.G.Geo.divCycle V s W ≠ 0 → IsProjVarF W n := by
    intro s b hs hsV hne
    have hne' : NumbersDVR.divCycle V s W ≠ 0 := by
      rw [← NumbersDVR.VocabDivCycle.proof F K ι V s W]
      exact_mod_cast hne
    obtain ⟨hW1, hW2⟩ := FieldNumbers.DivCycleSupport.full F K ι V hVd n hrel b s hs hsV W hne'
    exact ⟨⟨hW1.isPrime, (NumbersDVR.VocabMultiHomogIdeal.proof NumbersDVR.VocabMultiHomog.proof F K ι W).2
      hW1.multiHomog, hW1.relevant⟩, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W n).1 hW2⟩
  rw [Finsupp.mem_support_iff, ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply,
    Finsupp.mapRange_apply] at hW
  by_cases hfW : ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f W = 0
  · refine key g bg hg hgV fun h => hW ?_
    rw [hfW, h]
    simp
  · exact key f bf hf hfV hfW

theorem eq_intNum [DecidableEq K] {I : IFamily F ι} (hI : IsFieldIntersection I) :
    ∀ (n : ℕ) (V : Ideal (MRingOver F ι)) (L : Fin n → K → ℤ), IsProjVarF V n →
      I V n L = NumbersDVR.intNum F V L := by
  have hJ : IsFieldIntersection (F := F) (ι := ι) (fun V _ L => NumbersDVR.intNum F V L) :=
    NumbersDVR.IntNumIsFieldIntersection.full F K ι
  intro n
  induction n with
  | zero =>
    intro V L hV
    choose i hi using hV.1.2.2
    exact (hI.1 V L i hV hi).trans (hJ.1 V L i hV hi).symm
  | succ n ih =>
    intro V L hV
    obtain ⟨bf, bg, f, g, hf, hg, hfV, hgV, hb⟩ :=
      FieldNumbers.ExistsForm.full F K ι V (isMultiProjPrime_dvr hV.1) (L (Fin.last n))
    have hs : IsRatSection V (L (Fin.last n)) f g :=
      ⟨bf, bg, (NumbersDVR.VocabMultiHomog.proof F K ι f bf).2 hf,
        (NumbersDVR.VocabMultiHomog.proof F K ι g bg).2 hg, hfV, hgV, fun k => congrFun hb k⟩
    have e1 : I V (n + 1) L = ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval (fun W => I W n (Fin.init L))
        (ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv V f g) := by
      have h := hI.2 V n (Fin.init L) (L (Fin.last n)) f g hV hs
      rwa [Fin.snoc_init_self] at h
    have e2 : NumbersDVR.intNum F V L = ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval
        (fun W => NumbersDVR.intNum F W (Fin.init L)) (ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv V f g) := by
      have h := hJ.2 V n (Fin.init L) (L (Fin.last n)) f g hV hs
      rwa [Fin.snoc_init_self] at h
    rw [e1, e2, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval]
    refine Finsupp.sum_congr fun W hW => ?_
    rw [ih W _ (isProjVarF_of_mem_support hV hf hg hfV hgV hW)]

theorem map_update_add₂ {I : IFamily F ι} (hI : IsFieldIntersection I) {V : Ideal (MRingOver F ι)} {n : ℕ}
    (hV : IsProjVarF V n) (L : Fin n → K → ℤ) (j : Fin n) (x y : K → ℤ) :
    I V n (Function.update L j (x + y)) = I V n (Function.update L j x) + I V n (Function.update L j y) := by
  classical
  rw [eq_intNum hI n V _ hV, eq_intNum hI n V _ hV, eq_intNum hI n V _ hV]
  have hVd := isMultiProjPrime_dvr hV.1
  exact FieldNumbers.IntNumAdd.full F K ι V hVd.multiHomog hVd.relevant n
    ((FieldNumbers.CutRegular.relDim_eq_natCast_iff V n).2 hV.2) L j x y

theorem nsmul_position {I : IFamily F ι} (hI : IsFieldIntersection I) {V : Ideal (MRingOver F ι)} {n : ℕ}
    (hV : IsProjVarF V n) (L : Fin n → K → ℤ) (j : Fin n) (m : ℕ) (x : K → ℤ) :
    I V n (Function.update L j ((m : ℤ) • x)) = m * I V n (Function.update L j x) := by
  induction m with
  | zero =>
    have h := map_update_add₂ hI hV L j 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, zero_smul, zero_mul]
    linarith
  | succ m ih =>
    rw [Nat.cast_succ, add_smul, one_smul, map_update_add₂ hI hV, ih]
    ring

end KleimanNefF

theorem KleimanNefF.proof (hKA : KH.KAmpStatement) (hGP : GeneratedProductNonneg.Statement) :
    KH.KleimanNefFStatement := by
  classical
  intro F _ K _ ι _ I V n a hI hV hnef
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  let H : K → ℤ := fun _ => ((1 : ℕ) : ℤ)
  let c : Finset (Fin n) → ℤ := fun S => I V n (fun i => if i ∈ S then H else a i)
  have key : ∀ q : ℕ, 1 ≤ q → 0 ≤ ∑ S : Finset (Fin n), (q : ℤ) ^ Sᶜ.card * c S := by
    intro q hq
    have hamp := fun j => hKA F K ι I V n (a j) q 1 hI hV (hnef j) hq le_rfl
    choose p hp hgen _ using hamp
    let B : Fin n → K → ℤ := fun j => p j • (q • a j + H)
    have hB : 0 ≤ I V n B := hGP F K ι I V n B hI hV hgen
    have hposition : ∀ (L : Fin n → K → ℤ) (i : Fin n), I V n (Function.update L i (B i)) =
        ((q : ℤ) * p i) * I V n (Function.update L i (a i)) + (p i : ℤ) * I V n (Function.update L i H) := by
      intro L i
      have e : B i = ((q * p i : ℕ) : ℤ) • a i + ((p i : ℕ) : ℤ) • H := by
        funext k
        simp only [B, Pi.add_apply, Pi.smul_apply]
        simp only [H, nsmul_eq_mul, smul_eq_mul]
        push_cast
        ring
      rw [e, KleimanNefF.map_update_add₂ hI hV, KleimanNefF.nsmul_position hI hV, KleimanNefF.nsmul_position hI hV]
      push_cast
      ring
    have hexp := Kleiman.sum_expand_positions (I V n) B a (fun _ => H) (fun i => (q : ℤ) * p i)
      (fun i => (p i : ℤ)) hposition
    have hw : ∀ S : Finset (Fin n), (∏ i ∈ S, (p i : ℤ)) * (∏ i ∈ Sᶜ, ((q : ℤ) * p i)) =
        (∏ i, (p i : ℤ)) * (q : ℤ) ^ Sᶜ.card := by
      intro S
      rw [Finset.prod_mul_distrib, Finset.prod_const, ← mul_assoc, mul_comm _ ((q : ℤ) ^ _), mul_assoc,
        Finset.prod_mul_prod_compl, mul_comm]
    simp only [hw, mul_assoc] at hexp
    rw [← Finset.mul_sum] at hexp
    have hprod : 0 < ∏ i, (p i : ℤ) := Finset.prod_pos fun i _ => by exact_mod_cast hp i
    rw [hexp] at hB
    exact (mul_nonneg_iff_of_pos_left hprod).mp hB
  have h0 := Kleiman.nonneg_of_poly c key
  simpa [c] using h0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecMRankBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SecMRankBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem finite_secM (y : (Σ k, ι k) → Ω) (d : K → ℕ) : Module.Finite ℤ (secM y d) := by
  have h := SectionLatticeFinite.secM_fg y d
  rw [← AddSubgroup.toIntSubmodule_toAddSubgroup (secM y d), ← Submodule.fg_iff_addSubgroup_fg] at h
  exact Module.Finite.iff_fg.mpr h


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_eq_zero_of_mem {y : (Σ k, ι k) → Ω} {g : MRing ι} (hg : g ∈ mCoordIdeal y) :
    aeval y g = 0 := by
  have hext : ((aeval fun _ : K => (1 : Ω)).restrictScalars ℤ).comp (mConeMap y) = aeval y :=
    MvPolynomial.algHom_ext fun p => by simp [mConeMap]
  have h0 : mConeMap y g = 0 := hg
  rw [← hext, AlgHom.comp_apply, h0, map_zero]

variable [DecidableEq K]

theorem finrank_secM_le [CharZero Ω] (y : (Σ k, ι k) → Ω) (d : K → ℕ) :
    Module.finrank ℤ (secM y d) ≤
      Module.finrank ℚ (NumbersDVR.gradedPiece (KH.genIdeal y) d) := by
  have hI : ∀ f ∈ KH.genIdeal y, aeval y f = 0 := by
    have hle : KH.genIdeal y ≤ RingHom.ker (aeval y : MRingOver ℚ ι →ₐ[ℚ] Ω) := by
      unfold KH.genIdeal
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq]
      change aeval y (map (algebraMap ℤ ℚ) g) = 0
      rw [aeval_map_algebraMap]
      exact aeval_eq_zero_of_mem hg
    exact fun f hf => hle hf
  let ψ : (MRingOver ℚ ι ⧸ KH.genIdeal y) →ₗ[ℚ] Ω :=
    (Ideal.Quotient.liftₐ (KH.genIdeal y) (aeval y) hI).toLinearMap
  let V := NumbersDVR.gradedPiece (KH.genIdeal y) d
  have : FiniteDimensional ℚ V := (FieldNumbers.GradedFinite.proof ℚ K ι (KH.genIdeal y) d).1
  let R : Submodule ℚ Ω := V.map ψ
  have : FiniteDimensional ℚ R := Module.Finite.iff_fg.mpr ((Module.Finite.iff_fg.mp inferInstance).map ψ)
  have hsub : ∀ s ∈ secM y d, s ∈ R := by
    intro s hs
    have hspan : Submodule.span ℤ {s | ∃ g : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d ∧ aeval y g = s} ≤
        R.restrictScalars ℤ := by
      rw [Submodule.span_le]
      rintro _ ⟨g, hg, rfl⟩
      refine ⟨Ideal.Quotient.mk _ (map (Int.castRingHom ℚ) g), ⟨map (Int.castRingHom ℚ) g, ?_, rfl⟩, ?_⟩
      · rw [SetLike.mem_coe, mem_weightedHomogeneousSubmodule]
        exact (Bridge.isMultiHomog_iff _ _).mpr fun m hm k => hg m (support_map_subset _ _ hm) k
      · change aeval y (map (Int.castRingHom ℚ) g) = aeval y g
        rw [← algebraMap_int_eq, aeval_map_algebraMap]
    exact hspan hs
  have := finite_secM y d
  have : Module.IsTorsionFree ℤ (secM y d) :=
    Function.Injective.moduleIsTorsionFree (secM y d).subtype Subtype.val_injective (fun _ _ => rfl)
  let bs := Module.Free.chooseBasis ℤ (secM y d)
  let v : Module.Free.ChooseBasisIndex ℤ (secM y d) → Ω := fun i => (bs i : Ω)
  have hliZ : LinearIndependent ℤ v :=
    bs.linearIndependent.map' (secM y d).subtype.toIntLinearMap
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hliQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
  rw [Module.finrank_eq_card_chooseBasisIndex, ← finrank_span_eq_card hliQ]
  calc Module.finrank ℚ (Submodule.span ℚ (Set.range v)) ≤ Module.finrank ℚ R :=
        Submodule.finrank_mono (Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i => hsub _ (bs i).2))
    _ ≤ Module.finrank ℚ V := Submodule.finrank_map_le ψ V

theorem proof (h : GenericFibreVar.Statement) : SecMRankBound.Statement := by
  intro K _ ι _ Ω _ y D b hvar hb
  classical

  have hchar : CharZero Ω := by
    refine charZero_of_inj_zero fun n hn => ?_
    have hmem : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
      simp [mCoordIdeal, RingHom.mem_ker, mConeMap]
      rw [← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
    rw [hvar.2.2.1, Ideal.mem_bot] at hmem
    exact_mod_cast hmem
  refine ⟨fun m => finite_secM y _, ?_⟩

  obtain ⟨⟨hprime, hhom, -⟩, hdim⟩ := h K ι Ω y D hvar
  have hlt : ringKrullDim (MRingOver ℚ ι ⧸ KH.genIdeal y) <
      (((D + 1) + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [hdim]
    exact_mod_cast (by omega : D + Fintype.card K < D + 1 + Fintype.card K)
  have hdeg := NumbersDVR.HilbDegBound.full ℚ K ι (D + 1) (KH.genIdeal y) hprime
    ((Bridge.isMultiHomogIdeal_iff _).mpr hhom) hlt
  obtain ⟨a₀, C, hC⟩ := DegLTGrowth.proof K (D + 1) _ hdeg
  have hexp : ((D + 1 : ℕ) : ℝ) - 1 = ((D : ℕ) : ℝ) := by push_cast; ring

  have hrank : ∀ m : ℕ, (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ) ≤
      |(NumbersDVR.hilbFn (KH.genIdeal y) (fun k => ((m * b k : ℕ) : ℤ)) : ℝ)| := by
    intro m
    have e := (FieldNumbers.GradedFinite.proof ℚ K ι (KH.genIdeal y) (fun k => m * b k)).2
    have hle := finrank_secM_le y (fun k => m * b k)
    calc (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ)
        ≤ (Module.finrank ℚ (NumbersDVR.gradedPiece (KH.genIdeal y) (fun k => m * b k)) : ℝ) := by
          exact_mod_cast hle
      _ = |(NumbersDVR.hilbFn (KH.genIdeal y) (fun k => ((m * b k : ℕ) : ℤ)) : ℝ)| := by
          rw [e]; simp
  set B : ℝ := ∑ k, (b k : ℝ) with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun k _ => by positivity
  set M0 : ℝ := ∑ j ∈ Finset.range a₀, (Module.finrank ℤ (secM y (fun k => j * b k)) : ℝ) with hM0def
  have hM0 : 0 ≤ M0 := Finset.sum_nonneg fun j _ => by positivity
  have hC1 : 0 ≤ max C 0 * (B + 1) ^ D := by positivity
  refine ⟨max C 0 * (B + 1) ^ D + M0, by positivity, fun m => ?_⟩
  have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
  have hpow1 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ D := one_le_pow₀ (by linarith)
  rcases lt_or_ge m a₀ with hm | hm
  ·
    have h1 : (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ) ≤ M0 :=
      Finset.single_le_sum (f := fun j => (Module.finrank ℤ (secM y (fun k => j * b k)) : ℝ))
        (fun j _ => by positivity) (Finset.mem_range.mpr hm)
    nlinarith
  ·
    have hg := hC (fun k => m * b k) (fun k => le_trans hm (Nat.le_mul_of_pos_right m (hb k)))
    rw [hexp, Real.rpow_natCast] at hg
    have hsum : (∑ k, (((m * b k : ℕ)) : ℝ)) = m * B := by
      rw [hBdef, Finset.mul_sum]; push_cast; rfl
    have hX : (m : ℝ) * B + 1 ≤ (B + 1) * ((m : ℝ) + 1) := by nlinarith
    have hXpow : ((m : ℝ) * B + 1) ^ D ≤ ((B + 1) * ((m : ℝ) + 1)) ^ D :=
      pow_le_pow_left₀ (by positivity) hX D
    calc (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ)
        ≤ |(NumbersDVR.hilbFn (KH.genIdeal y) (fun k => ((m * b k : ℕ) : ℤ)) : ℝ)| := hrank m
      _ ≤ C * ((∑ k, (((m * b k : ℕ)) : ℝ)) + 1) ^ D := hg
      _ = C * ((m : ℝ) * B + 1) ^ D := by rw [hsum]
      _ ≤ max C 0 * ((m : ℝ) * B + 1) ^ D :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * ((B + 1) * ((m : ℝ) + 1)) ^ D :=
          mul_le_mul_of_nonneg_left hXpow (le_max_right _ _)
      _ = max C 0 * (B + 1) ^ D * ((m : ℝ) + 1) ^ D := by rw [mul_pow]; ring
      _ ≤ (max C 0 * (B + 1) ^ D + M0) * ((m : ℝ) + 1) ^ D := by nlinarith

theorem full : SecMRankBound.Statement := proof GenericFibreVar.proof

end SecMRankBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneQuotientBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

namespace HyperplaneQuotientBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
  {y : (Σ k, ι k) → Ω}


omit [∀ k, Fintype (ι k)] in
theorem mul_mem {b b' : K → ℤ} {s t : Ω} (hs : s ∈ chartLatQ y b 1) (ht : t ∈ chartLatQ y b' 1) :
    s * t ∈ chartLatQ y (b + b') 1 := by
  intro c hc
  have h := Subalgebra.mul_mem _ (hs c hc) (ht c hc)
  have heq : s * t * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b + b') k)) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b' k))) := by
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    simp only [Pi.add_apply]
    ring
  rw [heq]
  exact h


omit [∀ k, Fintype (ι k)] in
theorem pow_mem {e : K → ℤ} {σ : Ω} (hσ : σ ∈ chartLatQ y e 1) (n : ℕ) :
    σ ^ n ∈ chartLatQ y ((n : ℤ) • e) 1 := by
  induction n with
  | zero =>
    intro c _
    simp
  | succ n ih =>
    have h := mul_mem ih hσ
    have hb : (n : ℤ) • e + e = ((n + 1 : ℕ) : ℤ) • e := by
      push_cast
      rw [add_smul, one_smul]
    rw [hb] at h
    rw [pow_succ]
    exact h


omit [∀ k, Fintype (ι k)] in
theorem pow_regular {c : ∀ k, ι k} {e : K → ℤ} {σ : Ω} (hσ : σ ∈ chartLatQ y e 1)
    (hreg : ∀ (b : K → ℤ) (s : Ω), s ∈ chartLatQ y b 1 →
      σ * s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b + e - 1) 1 → s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b - 1) 1)
    (n : ℕ) (b : K → ℤ) (s : Ω) (hs : s ∈ chartLatQ y b 1)
    (h : σ ^ n * s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b + (n : ℤ) • e - 1) 1) :
    s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b - 1) 1 := by
  induction n generalizing b s with
  | zero => simpa using h
  | succ n ih =>
    have hσs : σ * s ∈ chartLatQ y (b + e) 1 := by
      have h' := mul_mem hσ hs
      rwa [add_comm e b] at h'
    refine hreg b s hs (ih (b + e) (σ * s) hσs ?_)
    have hb : b + ((n + 1 : ℕ) : ℤ) • e - 1 = b + e + (n : ℤ) • e - 1 := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [hb, pow_succ, mul_assoc] at h
    exact h

theorem finiteDimensional (hF : SectionLatticeFinite.Statement) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) (b : K → ℤ) :
    FiniteDimensional ℚ (chartLatQ y b 1) := by
  classical
  obtain ⟨G, hG, hGfin⟩ := (AddSubgroup.fg_iff (chartLat y b 1)).mp (hF K ι Ω y b 1 hy)
  have := FiniteDimensional.span_of_finite ℚ hGfin
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ G) fun s hs => ?_
  obtain ⟨N, hN, hNs⟩ := ChartDenominator.proof K ι Ω y b 1 s hs
  have hmem : (N : Ω) * s ∈ Submodule.span ℚ G := by
    rw [← hG] at hNs
    exact (AddSubgroup.closure_le (Submodule.span ℚ G).toAddSubgroup).mpr Submodule.subset_span hNs
  have hN0 : (N : Ω) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hs' : s = ((N : ℚ)⁻¹) • ((N : Ω) * s) := by
    rw [Rat.smul_def]
    push_cast
    field_simp
  rw [hs']
  exact Submodule.smul_mem _ _ hmem

theorem mem_chartDivSec {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℤ) (s : chartLatQ y b 1) :
    s ∈ chartDivSec y c b ↔ (s : Ω) / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b - 1) 1 := by
  have hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  simp only [chartDivSec, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map,
    LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨t, ht, hts⟩
    rw [← hts, mul_div_cancel_left₀ _ hm0]
    exact ht
  · intro h
    exact ⟨_, h, mul_div_cancel₀ _ hm0⟩

theorem finrank_quot_add_le {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℤ)
    [FiniteDimensional ℚ (chartLatQ y b 1)] :
    Module.finrank ℚ (chartLatQ y b 1 ⧸ chartDivSec y c b) + Module.finrank ℚ (chartLatQ y (b - 1) 1) ≤
      Module.finrank ℚ (chartLatQ y b 1) := by
  have hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hmem : ∀ t ∈ chartLatQ y (b - 1) 1, (∏ k, y ⟨k, c k⟩) * t ∈ chartLatQ y b 1 :=
    fun t ht => mul_mem_chartLatQ b ht
  let φ : chartLatQ y (b - 1) 1 →ₗ[ℚ] chartDivSec y c b :=
    { toFun := fun t => ⟨⟨(∏ k, y ⟨k, c k⟩) * t, hmem t t.2⟩,
        Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨t, t.2, rfl⟩)⟩
      map_add' := fun s t => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Submodule.coe_add, mul_add]
      map_smul' := fun r t => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply, mul_smul_comm] }
  have hinj : Function.Injective φ := fun s t h => by
    have h' := congrArg (fun x : chartDivSec y c b => ((x : chartLatQ y b 1) : Ω)) h
    exact Subtype.ext (mul_left_cancel₀ hm0 h')
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 := Submodule.finrank_quotient_add_finrank (chartDivSec y c b)
  omega

theorem finrank_quot_le {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {b d b' : K → ℤ} (hbd : b + d = b') {τ : Ω}
    (hτ : τ ∈ chartLatQ y d 1)
    (hreg : ∀ s ∈ chartLatQ y b 1, τ * s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b' - 1) 1 →
      s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b - 1) 1)
    [FiniteDimensional ℚ (chartLatQ y b' 1)] :
    Module.finrank ℚ (chartLatQ y b 1 ⧸ chartDivSec y c b) ≤
      Module.finrank ℚ (chartLatQ y b' 1 ⧸ chartDivSec y c b') := by
  subst hbd
  have hmem : ∀ s ∈ chartLatQ y b 1, τ * s ∈ chartLatQ y (b + d) 1 := fun s hs => by
    have h := mul_mem hτ hs
    rwa [add_comm d b] at h
  let φ : chartLatQ y b 1 →ₗ[ℚ] chartLatQ y (b + d) 1 :=
    { toFun := fun s => ⟨τ * s, hmem s s.2⟩
      map_add' := fun s t => Subtype.ext (mul_add _ _ _)
      map_smul' := fun r s => Subtype.ext (mul_smul_comm r τ (s : Ω)) }
  have hle : chartDivSec y c b ≤ (chartDivSec y c (b + d)).comap φ := by
    intro s hs
    rw [Submodule.mem_comap, mem_chartDivSec hc]
    rw [mem_chartDivSec hc] at hs
    have h := mul_mem hτ hs
    rw [show d + (b - 1) = b + d - 1 by abel] at h
    show τ * (s : Ω) / _ ∈ _
    rw [mul_div_assoc]
    exact h
  have hinj : Function.Injective (Submodule.mapQ _ _ φ hle) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H s =>
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, mem_chartDivSec hc] at hx
      rw [Submodule.Quotient.mk_eq_zero, mem_chartDivSec hc]
      exact hreg s s.2 hx
  exact LinearMap.finrank_le_finrank_of_injective hinj

end HyperplaneQuotientBound


open HyperplaneQuotientBound in
theorem HyperplaneQuotientBound.proof (hR : HyperplaneRegularSection.Statement)
    (hS : DiagonalSectionDifference.Statement) (hF : SectionLatticeFinite.Statement) :
    HyperplaneQuotientBound.Statement := by
  intro K _ ι _ Ω _ _ y D a c hD hV _ hc
  obtain ⟨M, hM1, hMa⟩ : ∃ M : ℕ, 1 ≤ M ∧ ∀ k, a k ≤ M := by
    refine ⟨(∑ k, (a k).toNat) + 1, Nat.le_add_left _ _, fun k => ?_⟩
    have h1 : (a k).toNat ≤ ∑ k, (a k).toNat :=
      Finset.single_le_sum (f := fun k => (a k).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have h2 := Int.self_le_toNat (a k)
    have h3 : ((a k).toNat : ℤ) ≤ ((∑ k, (a k).toNat : ℕ) : ℤ) := by exact_mod_cast h1
    push_cast at h3 ⊢
    omega
  set e : K → ℕ := fun k => ((M : ℤ) - a k).toNat with he
  have hek : ∀ k, (e k : ℤ) = M - a k := fun k => Int.toNat_of_nonneg (sub_nonneg.mpr (hMa k))
  obtain ⟨σ, -, hσ, hreg⟩ := hR K ι Ω y c e hc
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => ⟨c k, hc k⟩
  obtain ⟨C, hC⟩ := hS K ι Ω y D hD hV
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  refine ⟨C * (M : ℝ) ^ (D - 1), eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
  have hbd : (n : ℤ) • a + (n : ℤ) • (fun k => (e k : ℤ)) = ((n * M : ℕ) : ℤ) • (1 : K → ℤ) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hek, Pi.one_apply]
    push_cast
    ring
  have := finiteDimensional hF hy (((n * M : ℕ) : ℤ) • (1 : K → ℤ))
  have h1 := finrank_quot_le hc hbd (pow_mem hσ n) (fun s hs h => pow_regular hσ hreg n _ s hs (by rwa [← hbd] at h))
  have h2 := finrank_quot_add_le hc (((n * M : ℕ) : ℤ) • (1 : K → ℤ))
  have h3 := hN (n * M) (le_trans hn (Nat.le_mul_of_pos_right n hM1))
  have h1' : (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1 ⧸ chartDivSec y c ((n : ℤ) • a)) : ℝ) ≤
      (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ)) 1 ⧸
        chartDivSec y c (((n * M : ℕ) : ℤ) • (1 : K → ℤ))) : ℝ) := by exact_mod_cast h1
  have h2' : (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ)) 1 ⧸
        chartDivSec y c (((n * M : ℕ) : ℤ) • (1 : K → ℤ))) : ℝ) +
      (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ) - 1) 1) : ℝ) ≤
      (Module.finrank ℚ (chartLatQ y (((n * M : ℕ) : ℤ) • (1 : K → ℤ)) 1) : ℝ) := by exact_mod_cast h2
  have hpow : ((n * M : ℕ) : ℝ) ^ (D - 1) = (M : ℝ) ^ (D - 1) * (n : ℝ) ^ (D - 1) := by
    push_cast
    ring
  rw [hpow] at h3
  nlinarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedEffectiveSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GeneratedEffectiveSection.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver F ι)) (a : K → ℤ),
    IsMultiProjPrime V → KH.GeneratedV F V a →
    ∃ f g : MRingOver F ι, IsRatSection V a f g ∧ ∀ W, 0 ≤ ratDiv V f g W

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEuclideanSectionsPower
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter MeasureTheory

theorem EuclideanSectionsPower.proof (hL : SectionL2Lattice.Statement) (hP : TensorPowerL2Degree.Statement) :
    EuclideanSectionsPower.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 II hD hII har hb hA hc
  obtain ⟨μ, m, hμ, hcon, hZ, hm, hdeg⟩ := hP K ι Ω y D A P0 II hD hII har hb hA hc
  obtain ⟨r, φ, hinj, hdisc, hlat, hsup, hmul, hrank, hnorm⟩ :=
    hL K ι Ω y D A har hb hA.semipos.1.continuousOn μ hμ hcon hZ
  refine ⟨r, φ, hinj, hdisc, hlat, hsup, hmul, hrank, m, hm, fun ε hε => ?_⟩
  filter_upwards [hdeg ε hε] with q hq
  intro _ _
  exact hq (r (m * q)) (φ (m * q)) (hinj _) (hnorm _)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockVeronese
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PowerBlockVeronese.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ (N : ℕ) (v : Fin N → Ω),
      AddSubgroup.closure (Set.range v) = chartLat y a m ∧
      KH.GeneratesOn y (fun k => (m : ℤ) * a k) v ∧
      ∀ n : ℕ, 1 ≤ n → chartLat y a (m * n) = secM (addBlock y v) (blockDeg (none : Option K) n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockCoeffCycle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockCoeffCycle.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric ℂ (Ix κ)) (c : κ) (l : Ix κ → ℤ),
    I.IsFamily → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    ∀ i ≤ D, twoBlockCoeff I x (matAct B x) m m' D i = twoBlockVert x (matAct B x) c l (twoBlockDegList D i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
