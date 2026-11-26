module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersectionInt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionPointValue
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMixSt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountLattice
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRealFormsOnPoints

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CechHcSubsingletonOfBij
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace H1VanishingDevissage

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

theorem cechHc_subsingleton_iff (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ) :
    Subsingleton (KH.cechHc ι 𝓜 c n) ↔ KH.cechZc ι 𝓜 c n ≤ KH.cechBc ι 𝓜 c n := by
  show Subsingleton (_ ⧸ _) ↔ _
  rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]


omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem locPart_shift (𝓜 : (K → ℤ) → Submodule S M) (T : Submonoid (MRingOver S ι)) (c x : K → ℤ) :
    KH.locPart ι (fun d => 𝓜 (d + c)) T x = KH.locPart ι 𝓜 T (x + c) := by
  have h : ∀ a : K → ℕ, x + (fun k => (a k : ℤ)) + c = x + c + fun k => (a k : ℤ) :=
    fun _ => add_right_comm _ _ _
  simp only [KH.locPart, h]


omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem cechCc_shift (𝓜 : (K → ℤ) → Submodule S M) (c x : K → ℤ) (n : ℕ) :
    KH.cechCc ι (fun d => 𝓜 (d + c)) x n = KH.cechCc ι 𝓜 (x + c) n := by
  simp only [KH.cechCc, locPart_shift]

theorem cechHc_shift_iff (𝓜 : (K → ℤ) → Submodule S M) (c x : K → ℤ) (n : ℕ) :
    Subsingleton (KH.cechHc ι (fun d => 𝓜 (d + c)) x n) ↔ Subsingleton (KH.cechHc ι 𝓜 (x + c) n) := by
  rw [cechHc_subsingleton_iff, cechHc_subsingleton_iff]
  cases n <;> simp only [KH.cechZc, KH.cechBc, cechCc_shift]


omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem isMGraded_shift {𝓜 : (K → ℤ) → Submodule S M} (h : KH.IsMGraded S ι 𝓜) (c : K → ℤ) :
    KH.IsMGraded S ι (fun d => 𝓜 (d + c)) := by
  refine ⟨?_, fun a d p m hp hm => ?_⟩
  · have h1 := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top 𝓜).1 h.1
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
      ⟨h1.1.comp (add_left_injective c), ?_⟩
    rw [← h1.2]
    exact (Equiv.addRight c).iSup_comp (g := 𝓜)
  · have := h.2 a (d + c) p m hp hm
    rwa [add_right_comm] at this

theorem cechHc_subsingleton_of_bij (hSES : KH.CechSESStatement)
    {A B : Type} [AddCommGroup A] [Module (MRingOver S ι) A] [Module S A] [IsScalarTower S (MRingOver S ι) A]
    [AddCommGroup B] [Module (MRingOver S ι) B] [Module S B] [IsScalarTower S (MRingOver S ι) B]
    (𝓐 : (K → ℤ) → Submodule S A) (𝓑 : (K → ℤ) → Submodule S B) (g : A →ₗ[MRingOver S ι] B)
    (hA : KH.IsMGraded S ι 𝓐) (hB : KH.IsMGraded S ι 𝓑) (hg : KH.IsMGradedMap S ι 𝓐 𝓑 g)
    (hinj : Function.Injective g) (hsurj : Function.Surjective g) (c : K → ℤ) (n : ℕ)
    (h : Subsingleton (KH.cechHc ι 𝓐 c n)) : Subsingleton (KH.cechHc ι 𝓑 c n) := by
  have hhG : KH.IsMGradedMap S ι 𝓑 (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) 0 :=
    fun _ _ _ => Submodule.zero_mem _
  have hex : LinearMap.range g = LinearMap.ker (0 : B →ₗ[MRingOver S ι] PUnit) := by
    rw [LinearMap.range_eq_top.2 hsurj, LinearMap.ker_zero]
  have hU' : Subsingleton (KH.cechHc ι (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) c n) := by
    have : Subsingleton (KH.CechC S ι PUnit n) :=
      ⟨fun f g => funext fun I => Subsingleton.elim (α := LocalizedModule _ PUnit) _ _⟩
    refine ⟨fun x y => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [Subsingleton.elim x y]
  exact (hSES S K ι A B PUnit 𝓐 𝓑 _ g 0 hA hB isMGraded_punit hg hhG hinj
    (fun _ => ⟨0, Subsingleton.elim _ _⟩) hex c n).1 h hU'

end H1VanishingDevissage

theorem H1VanishingDevissage.proof (hPF : KH.PrimeFiltStatement) (hSES : KH.CechSESStatement)
    (hGQ : GradedSubquot.Statement) : H1VanishingDevissage.Statement := by
  intro S _ K _ _ ι _ _ V N hS hP M _ _ _ _ 𝓜 hfin hgr hV e
  obtain ⟨r, m, c, 𝔭, hm, h𝔭, hcol, hspan⟩ := hPF S K ι M 𝓜 hS hfin hgr
  let G : ℕ → Set M := fun j => m '' {l | (l : ℕ) < j}
  let F : ℕ → Submodule (MRingOver S ι) M := fun j => Submodule.span _ (G j)
  have hGh : ∀ j, ∀ x ∈ G j, ∃ c', x ∈ 𝓜 c' := by
    rintro j _ ⟨l, -, rfl⟩
    exact ⟨c l, hm l⟩
  have hFmono : ∀ {i j : ℕ}, i ≤ j → F i ≤ F j := fun hij =>
    Submodule.span_mono (Set.image_mono fun l (hl : (l : ℕ) < _) => lt_of_lt_of_le hl hij)
  have hgrF : ∀ j, KH.IsMGraded S ι (subGrading 𝓜 (F j)) := fun j =>
    (hGQ S K ι M 𝓜 (G j) (G j) hgr (hGh j) (hGh j) le_rfl).1
  have key : ∀ j ≤ r, ∃ c₁ : ℕ, ∀ n : ℕ, c₁ ≤ n →
      Subsingleton (KH.cechHc ι (subGrading 𝓜 (F j)) (e + n • N) 1) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hF0 : F 0 = ⊥ := by simp [F, G]
      refine ⟨0, fun n _ => (h1_vanish_generated_of_localized_subsingleton
        (fun _ _ => loc_subsingleton_of_kill (Submonoid.one_mem _) fun y => ?_) _ _).1⟩
      rw [one_smul]
      have hy : (y : M) ∈ (⊥ : Submodule (MRingOver S ι) M) := by
        rw [← hF0]
        exact y.2
      exact Submodule.coe_eq_zero.mp ((Submodule.mem_bot _).1 hy)
    | succ j ih =>
      intro hj
      obtain ⟨c₀, hc₀⟩ := ih (Nat.le_of_succ_le hj)
      let l : Fin r := ⟨j, hj⟩
      let L : Submodule (MRingOver S ι) (F (j + 1)) := (F j).comap (F (j + 1)).subtype
      have hq := (hGQ S K ι M 𝓜 (G j) (G (j + 1)) hgr (hGh j) (hGh (j + 1)) (hFmono (Nat.le_succ j))).2
      have hml : m l ∈ F (j + 1) := Submodule.subset_span ⟨l, Nat.lt_succ_self j, rfl⟩

      let ψ : MRingOver S ι →ₗ[MRingOver S ι] (F (j + 1) ⧸ L) :=
        LinearMap.toSpanSingleton _ _ (L.mkQ ⟨m l, hml⟩)
      have hψ : ∀ p, ψ p = L.mkQ (p • ⟨m l, hml⟩) := fun p => (L.mkQ.map_smul p _).symm
      have hker : ∀ p, ψ p = 0 ↔ p ∈ 𝔭 l := by
        intro p
        rw [hψ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hcol l p
      let φ : (MRingOver S ι ⧸ 𝔭 l) →ₗ[MRingOver S ι] (F (j + 1) ⧸ L) :=
        (𝔭 l).liftQ ψ fun p hp => (LinearMap.mem_ker).2 ((hker p).2 hp)
      have hφ : ∀ p, φ (Ideal.Quotient.mk (𝔭 l) p) = ψ p := fun _ => rfl
      have hinj : Function.Injective φ := LinearMap.ker_eq_bot.1
        (Submodule.ker_liftQ_eq_bot _ _ _ fun p hp => (hker p).1 (LinearMap.mem_ker.1 hp))

      have hdec : ∀ y ∈ F (j + 1), ∃ p : MRingOver S ι, y - p • m l ∈ F j := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨l', hl', rfl⟩ := hx
          rcases Nat.lt_succ_iff_lt_or_eq.1 hl' with h | h
          · exact ⟨0, by rw [zero_smul, sub_zero]; exact Submodule.subset_span ⟨l', h, rfl⟩⟩
          · exact ⟨1, by rw [one_smul, show l' = l from Fin.ext h, sub_self]; exact (F j).zero_mem⟩
        | zero => exact ⟨0, by rw [zero_smul, sub_zero]; exact (F j).zero_mem⟩
        | add x y _ _ hx hy =>
          obtain ⟨p, hp⟩ := hx
          obtain ⟨p', hp'⟩ := hy
          refine ⟨p + p', ?_⟩
          have : x + y - (p + p') • m l = (x - p • m l) + (y - p' • m l) := by rw [add_smul]; abel
          rw [this]
          exact (F j).add_mem hp hp'
        | smul a x _ hx =>
          obtain ⟨p, hp⟩ := hx
          refine ⟨a * p, ?_⟩
          rw [mul_smul, ← smul_sub]
          exact (F j).smul_mem a hp
      have hsurj : Function.Surjective φ := by
        intro q
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective L q
        obtain ⟨p, hp⟩ := hdec y y.2
        refine ⟨Ideal.Quotient.mk (𝔭 l) p, ?_⟩
        rw [hφ, hψ, Submodule.mkQ_apply, Submodule.Quotient.eq]
        show ((p • ⟨m l, hml⟩ - y : F (j + 1)) : M) ∈ F j
        rw [Submodule.coe_sub, Submodule.coe_smul, ← neg_sub]
        exact (F j).neg_mem hp
      obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℕ, ∀ n : ℕ, c₂ ≤ n →
          Subsingleton (KH.cechHc ι (quotGrading (subGrading 𝓜 (F (j + 1))) L) (e + n • N) 1) := by
        by_cases hrel : IsMultiProjPrime (𝔭 l)
        ·
          obtain ⟨c₂, hc₂⟩ := hP (𝔭 l) hrel (hV.trans (h𝔭 l).2.2) (e + -c l)
          have hA := isMGraded_shift (QuotPartGraded.proof S K ι (𝔭 l) (h𝔭 l).2.1) (-c l)
          have hG : KH.IsMGradedMap S ι (fun d => KH.quotPart S (𝔭 l) (d + -c l))
              (quotGrading (subGrading 𝓜 (F (j + 1))) L) φ := by
            intro d x hx
            refine (Submodule.span_le (p := (quotGrading (subGrading 𝓜 (F (j + 1))) L d).comap
              (φ.restrictScalars S))).2 ?_ hx
            rintro _ ⟨p, ⟨h0, hp⟩, rfl⟩
            refine ⟨p • ⟨m l, hml⟩, ?_, (hψ p).symm⟩
            have h := hgr.2 _ (c l) p (m l) hp (hm l)
            have hd : c l + (fun k => (((d + -c l) k).toNat : ℤ)) = d := by
              funext k
              have := h0 k
              simp only [Pi.add_apply, Pi.neg_apply] at this ⊢
              rw [Int.toNat_of_nonneg this]
              ring
            rw [hd] at h
            exact h
          refine ⟨c₂, fun n hn => cechHc_subsingleton_of_bij hSES _ _ φ hA hq hG hinj hsurj _ _ ?_⟩
          rw [cechHc_shift_iff, show e + n • N + -c l = e + -c l + n • N by abel]
          exact hc₂ n hn
        · have hirr : ¬ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (𝔭 l) := fun h => hrel ⟨(h𝔭 l).1, (h𝔭 l).2.1, h⟩
          simp only [ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant, not_forall, not_exists, not_not] at hirr
          obtain ⟨k, hk⟩ := hirr
          refine ⟨0, fun n _ => (h1_vanish_generated_of_localized_subsingleton (fun _ I => ?_) _ _).1⟩
          obtain ⟨i, hi⟩ := I.2.1 k
          refine loc_subsingleton_of_kill (Submonoid.subset_closure ⟨k, i, hi, rfl⟩) fun y => ?_
          obtain ⟨y, rfl⟩ := hsurj y
          obtain ⟨p', rfl⟩ := Ideal.Quotient.mk_surjective y
          rw [← LinearMap.map_smul, show (X ⟨k, i⟩ : MRingOver S ι) • Ideal.Quotient.mk (𝔭 l) p' =
            Ideal.Quotient.mk (𝔭 l) (X ⟨k, i⟩ * p') from rfl, hφ]
          exact (hker _).2 (Ideal.mul_mem_right _ _ (hk i))
      refine ⟨max c₀ c₂, fun n hn => ?_⟩
      let g := Submodule.inclusion (hFmono (Nat.le_succ j))
      have hex : LinearMap.range g = LinearMap.ker L.mkQ := by
        rw [Submodule.range_inclusion, Submodule.ker_mkQ]
      have hgG : KH.IsMGradedMap S ι (subGrading 𝓜 (F j)) (subGrading 𝓜 (F (j + 1))) g := fun _ _ hx => hx
      have hhG : KH.IsMGradedMap S ι (subGrading 𝓜 (F (j + 1))) (quotGrading (subGrading 𝓜 (F (j + 1))) L)
          L.mkQ := fun _ _ hx => Submodule.mem_map_of_mem hx
      exact (hSES S K ι _ _ _ _ _ _ g L.mkQ (hgrF j) (hgrF (j + 1)) hq hgG hhG
        (Submodule.inclusion_injective _) (Submodule.mkQ_surjective _) hex (e + n • N) 1).1
        (hc₀ n (le_of_max_le_left hn)) (hc₂ n (le_of_max_le_right hn))
  have hFr : F r = ⊤ := by
    rw [← hspan]
    simp [F, G]
  obtain ⟨c₁, hc₁⟩ := key r le_rfl
  exact ⟨c₁, fun n hn => cechHc_subsingleton_of_bij hSES _ 𝓜 (F r).subtype (hgrF r) hgr (fun _ _ hx => hx)
    (Submodule.injective_subtype _) (fun y => ⟨⟨y, hFr ▸ Submodule.mem_top⟩, rfl⟩) _ _ (hc₁ n hn)⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionNormSqExtension
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionNormSqExtension.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (m N : ℕ) (v : Fin N → Ω),
    IsSmoothHerm A → IsConjInvariantH A →
    (∀ j, v j ∈ chartLat y A.a m) → KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v →
    ∃ S : ((Σ k, ι k) → ℂ) → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S {x | ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0} ∧
      (∀ x : (Σ k, ι k) → ℂ, (∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) → 0 < S x) ∧
      (∀ (c : K → ℂ) (x : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → S (fun p => c p.1 * x p) = S x) ∧
      (∀ x : (Σ k, ι k) → ℂ, S (fun p => (starRingEnd ℂ) (x p)) = S x) ∧
      (∀ x ∈ mcPts (mCoordIdeal y), S x = ∑ j, secNormAt y A m (v j) x ^ 2) ∧
      ∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ w : (Σ k, addIdx ι N k) → ℂ,
        IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (addBlock y v)) z w →
        leviForm (fun z' : (Σ k, addIdx ι N k) → ℂ =>
            Real.log (∑ j, ‖z' ⟨none, j⟩‖ ^ 2) / 2 - Real.log (S (basePart₂ z')) / 2) z w =
          (m : ℝ) * leviForm (fun x => Real.log (A.h x)) (basePart₂ z) (basePart₂ w)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftNefBig
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

set_option linter.unusedSectionVars false

namespace ShiftedNefBig

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem geoNum_one_add (W : Ideal (MRing ι)) (a b : K → ℤ) (q : ℤ) :
    geoNum 1 W (fun _ => q • a + b) = q * geoNum 1 W (fun _ => a) + geoNum 1 W (fun _ => b) := by
  simp only [geoNum]
  split_ifs with h
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
      mul_assoc]
  · simp

theorem geoNum_one_one_nonneg (W : Ideal (MRing ι)) : 0 ≤ geoNum 1 W (fun _ => (1 : K → ℤ)) := by
  simp only [geoNum]
  split_ifs with h
  · refine Finset.sum_nonneg fun k _ => mul_nonneg zero_le_one ?_
    refine finsum_nonneg fun W' => finsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) ?_
    split_ifs <;> positivity
  · exact le_rfl

end ShiftedNefBig


open ShiftedNefBig in
theorem ShiftNefBig.proof (hD : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement)
    (hB : NefPlusAmpleDegree.Statement) : ShiftNefBig.Statement := by
  intro K _ ι _ Ω _ y D A P0 _ har _ hP0 hs hnef hc q _
  have ha : (HermLine.zcomb A (fsH ι) (q : ℤ) 1).a = (q : ℤ) • A.a + 1 := by
    show (q : ℤ) • A.a + (1 : ℤ) • (fsH ι).a = _
    rw [one_smul]
    rfl
  refine ⟨hP0, PerturbSemipos.proof K ι P0 (mCoordIdeal y) A q 1 hs (Nat.cast_nonneg q) zero_le_one,
    HermLine.zcomb_isConjInvariantH hc (fsH_isConjInvariantH ι) _ _, ?_, ?_⟩
  · rw [ha]
    intro W hW hPW hch hdim
    rw [geoNum_one_add]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg q) (hnef W hW hPW hch hdim)) (geoNum_one_one_nonneg W)
  · rw [ha]
    exact hB K ι (mCoordIdeal y) D A.a har (nefOnGenericDeg_of_semipos NefOnGenericOfSemipos.proof hD hP0 hs) q

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResolutionPotentials
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem resLift_continuousOn (d : HSMDatum D Ω κ) (x : d.R.X) (p : Ix κ) :
    ContinuousOn (fun z => d.R.lift x z p) (d.R.U x) := by
  intro z hz
  obtain ⟨j, hj⟩ := d.R.A.cover z
  have hzt : d.R.A.chart j z ∈ (d.R.A.chart j).target := (d.R.A.chart j).map_source hj
  have hc : ContinuousAt ((fun z => d.R.lift x z p) ∘ (d.R.A.chart j).symm) (d.R.A.chart j z) :=
    (d.R.holo x p j _ ⟨hzt, by rwa [Set.mem_preimage, (d.R.A.chart j).left_inv hj]⟩).continuousAt
  have h := ((d.R.A.chart j).symm.continuousAt_iff_continuousAt_comp_right
    (f := fun z => d.R.lift x z p) (x := z) (by simpa using hj)).mpr (by simpa using hc)
  exact h.continuousWithinAt

theorem resLift_contDiffOn (d : HSMDatum D Ω κ) (x : d.R.X) (j : Fin d.R.A.n) :
    ContDiffOn ℝ ∞ (fun y => d.R.lift x ((d.R.A.chart j).symm y))
      ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x) :=
  contDiffOn_pi.mpr fun p => ((d.R.holo x p j).contDiffOn_of_completeSpace).restrict_scalars ℝ

theorem resPot_smoothOn (d : HSMDatum D Ω κ) {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m)
    (x : d.R.X) : d.R.A.SmoothOn ((resPot d m).U x) ((resPot d m).φ x) := fun j => by
  have hne : ∀ y ∈ (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x,
      d.R.lift x ((d.R.A.chart j).symm y) ∈ {z : Ix κ → ℂ | z ≠ 0} :=
    fun y hy => gaamix_ne_zero_of_mcPts (d.R.mem x _ hy.2)
  exact (hm.comp (resLift_contDiffOn d x j) hne).log fun y hy => (m.pos _ (hne y hy)).ne'

theorem isPotential_resPot (d : HSMDatum D Ω κ) {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) :
    IsPotential d.R.A (resPot d m) := by
  refine ⟨resPot_smoothOn d hm, fun x x' y hy => ?_⟩
  have hy' : y ∈ d.R.U x ∩ d.R.U x' := hy
  obtain ⟨p, hp⟩ := (d.R.mem x' y hy'.2).1 ()
  obtain ⟨c, hc, hcy⟩ := d.R.compat x x' y hy'
  have hnum : d.R.lift x y ⟨(), p⟩ ≠ 0 := by
    rw [hcy]
    exact mul_ne_zero (hc ()) hp
  set r : ℂ := d.R.lift x y ⟨(), p⟩ / d.R.lift x' y ⟨(), p⟩ with hr_def
  have hr : r ≠ 0 := div_ne_zero hnum hp
  have hO : IsOpen (d.R.U x ∩ d.R.U x') := (d.R.isOpen_U x).inter (d.R.isOpen_U x')
  let q : d.R.X → ℂ := fun z => d.R.lift x z ⟨(), p⟩ / d.R.lift x' z ⟨(), p⟩ / r
  let W : Set d.R.X :=
    {z | z ∈ d.R.U x ∩ d.R.U x' ∧ d.R.lift x' z ⟨(), p⟩ ≠ 0 ∧ q z ∈ Complex.slitPlane}
  have hW : IsOpen W := by
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    have hn : ContinuousAt (fun z => d.R.lift x z ⟨(), p⟩) z :=
      ((resLift_continuousOn d x _).mono Set.inter_subset_left).continuousAt (hO.mem_nhds hz.1)
    have hd : ContinuousAt (fun z => d.R.lift x' z ⟨(), p⟩) z :=
      ((resLift_continuousOn d x' _).mono Set.inter_subset_right).continuousAt (hO.mem_nhds hz.1)
    filter_upwards [hO.mem_nhds hz.1, hd.eventually_ne hz.2.1,
      ((hn.div hd hz.2.1).div_const r).eventually_mem (Complex.isOpen_slitPlane.mem_nhds hz.2.2)]
      with w h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hyW : y ∈ W := by
    refine ⟨hy', hp, ?_⟩
    have h1 : q y = 1 := div_self hr
    rw [h1]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simp))
  let G : d.R.X → ℂ := fun z => Complex.log (q z) + ((Real.log ‖r‖ : ℝ) : ℂ)
  refine ⟨W, hW, hyW, G, fun j y' hy'' => ?_, fun z hz => ?_⟩
  · have hz : (d.R.A.chart j).symm y' ∈ W := hy''.2
    have hn : AnalyticAt ℂ (fun y'' => d.R.lift x ((d.R.A.chart j).symm y'') ⟨(), p⟩) y' :=
      d.R.holo x _ j y' ⟨hy''.1, hz.1.1⟩
    have hd : AnalyticAt ℂ (fun y'' => d.R.lift x' ((d.R.A.chart j).symm y'') ⟨(), p⟩) y' :=
      d.R.holo x' _ j y' ⟨hy''.1, hz.1.2⟩
    have hq : AnalyticAt ℂ (fun y'' => q ((d.R.A.chart j).symm y'')) y' :=
      (hn.div hd hz.2.1).div analyticAt_const hr
    have hl : AnalyticAt ℂ (Complex.log ∘ fun y'' => q ((d.R.A.chart j).symm y'')) y' :=
      AnalyticAt.comp (f := fun y'' => q ((d.R.A.chart j).symm y'')) (analyticAt_clog hz.2.2) hq
    exact hl.add analyticAt_const
  · have hzW : z ∈ W := hz.1.1
    obtain ⟨c', hc', hcz⟩ := d.R.compat x x' z hzW.1
    have hpos : 0 < m.ρ (d.R.lift x' z) := m.pos _ (gaamix_ne_zero_of_mcPts (d.R.mem x' z hzW.1.2))
    have hsm : d.R.lift x z = c' () • d.R.lift x' z := by
      rw [hcz]
      funext w
      rfl
    have hqz : q z = c' () / r := by
      show d.R.lift x z ⟨(), p⟩ / d.R.lift x' z ⟨(), p⟩ / r = _
      rw [hsm, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hzW.2.1, mul_one]
    show Real.log (m.ρ (d.R.lift x z)) - Real.log (m.ρ (d.R.lift x' z)) = (G z).re
    rw [hsm, m.smul, Real.log_mul (norm_ne_zero_iff.mpr (hc' ())) hpos.ne', add_sub_cancel_right]
    show Real.log ‖c' ()‖ = (Complex.log (q z) + ((Real.log ‖r‖ : ℝ) : ℂ)).re
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, hqz, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr (hc' ())) (norm_ne_zero_iff.mpr hr)]
    ring

theorem continuous_logRatio_resPt (d : HSMDatum D Ω κ) {m₀ m₁ : ConeMetric ℂ (Ix κ)}
    (h₀ : IsSmoothMetric m₀) (h₁ : IsSmoothMetric m₁) :
    Continuous fun y => logRatio m₀ m₁ (resPt d y) := by
  refine continuous_iff_continuousAt.2 fun y0 => ?_
  have hU : d.R.U y0 ∈ 𝓝 y0 := (d.R.isOpen_U y0).mem_nhds (d.R.mem_U y0)
  have hL : ContinuousOn (d.R.lift y0) (d.R.U y0) :=
    continuousOn_pi.2 fun p => resLift_continuousOn d y0 p
  have hlog : ContinuousOn (fun y => logRatio m₀ m₁ (d.R.lift y0 y)) (d.R.U y0) :=
    (gbamix_smooth_logRatio h₀ h₁).continuousOn.comp hL
      fun y hy => gaamix_ne_zero_of_mcPts (d.R.mem y0 y hy)
  have heq : (fun y => logRatio m₀ m₁ (d.R.lift y0 y)) =ᶠ[𝓝 y0]
      fun y => logRatio m₀ m₁ (resPt d y) := by
    filter_upwards [hU] with y hy
    obtain ⟨c, hc, hcy⟩ := d.R.compat y y0 y ⟨d.R.mem_U y, hy⟩
    show _ = logRatio m₀ m₁ (d.R.lift y y)
    rw [hcy, gbamix_logRatio_deg c _ hc]
  exact (hlog.continuousAt hU).congr heq

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftQuotientBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

section Mul

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
  {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k}


omit [∀ k, Fintype (ι k)] in
theorem mul_mem_chartLatQ_add {B γ : K → ℤ} {g s : Ω} (hg : g ∈ chartLatQ y γ 1) (hs : s ∈ chartLatQ y B 1) :
    g * s ∈ chartLatQ y (B + γ) 1 := by
  intro c' hc'
  have hk : ∀ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (B + γ) k)) =
      y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * γ k)) * y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * B k)) := by
    intro k
    rw [← zpow_add₀ (hc' k)]
    congr 1
    simp only [Pi.add_apply]
    ring
  have heq : g * s * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (B + γ) k)) =
      (g * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * γ k))) * (s * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * B k))) := by
    simp only [hk, Finset.prod_mul_distrib]
    ring
  rw [heq]
  exact Subalgebra.mul_mem _ (hg c' hc') (hs c' hc')

theorem finrank_quot_le_of_regular {B γ : K → ℤ} {g : Ω} [FiniteDimensional ℚ (chartLatQ y (B + γ) 1)]
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hg : g ∈ chartLatQ y γ 1)
    (hreg : ∀ s : Ω, s ∈ chartLatQ y B 1 → g * s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (B + γ - 1) 1 →
      s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (B - 1) 1) :
    Module.finrank ℚ (chartLatQ y B 1 ⧸ chartDivSec y c B) ≤
      Module.finrank ℚ (chartLatQ y (B + γ) 1 ⧸ chartDivSec y c (B + γ)) := by
  let φ : chartLatQ y B 1 →ₗ[ℚ] chartLatQ y (B + γ) 1 :=
    { toFun := fun s => ⟨g * s, mul_mem_chartLatQ_add hg s.2⟩
      map_add' := fun s t => Subtype.ext (mul_add _ _ _)
      map_smul' := fun r s => Subtype.ext (mul_smul_comm r g (s : Ω)) }
  have hle : chartDivSec y c B ≤ (chartDivSec y c (B + γ)).comap φ := by
    intro s hs
    obtain ⟨t, ht, hts⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hs)
    refine Submodule.mem_comap.mpr (Submodule.mem_comap.mpr (Submodule.mem_map.mpr
      ⟨g * t, ?_, ?_⟩))
    · have h := mul_mem_chartLatQ_add hg ht
      rwa [show B - 1 + γ = B + γ - 1 by abel] at h
    · change (∏ k, y ⟨k, c k⟩) * (g * t) = g * (s : Ω)
      have hts' : (∏ k, y ⟨k, c k⟩) * t = (s : Ω) := hts
      rw [← hts']
      ring
  refine LinearMap.finrank_le_finrank_of_injective (f := Submodule.mapQ _ _ φ hle) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  rw [Submodule.Quotient.mk_eq_zero]
  have hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  obtain ⟨t, ht, hts⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hx)
  have hts' : (∏ k, y ⟨k, c k⟩) * t = g * (s : Ω) := hts
  have hu := hreg s s.2 (by rwa [← hts', mul_div_cancel_left₀ _ hm0])
  refine Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨_, hu, ?_⟩)
  change (∏ k, y ⟨k, c k⟩) * ((s : Ω) / ∏ k, y ⟨k, c k⟩) = (s : Ω)
  exact mul_div_cancel₀ _ hm0

end Mul

theorem ShiftQuotientBound.proof (hfin : SectionLatticeFinite.Statement) (hQ : HyperplaneQuotientBound.Statement)
    (hR : HyperplaneRegularSection.Statement) : ShiftQuotientBound.Statement := by
  intro K _ ι _ Ω _ _ y D a b c hD hV hB hc
  obtain ⟨C₀, hC₀⟩ := hQ K ι Ω y D (fun _ => 1) c hD hV hB hc
  set N : ℕ := 1 + ∑ k, (a k).natAbs with hN
  set M : ℕ := ∑ k, (b k).natAbs with hM
  have hN1 : 1 ≤ N := by omega
  have ht : Tendsto (fun n : ℕ => n * N + M) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp only [id]; nlinarith [Nat.zero_le n, hN1]) tendsto_id
  refine ⟨|C₀| * ((N + M : ℕ) : ℝ) ^ (D - 1),
    ((ht.eventually hC₀).and (eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ => ?_⟩
  set B : K → ℤ := (n : ℤ) • a + b with hBdef
  set γ : K → ℤ := (((n * N + M : ℕ) : ℤ) • fun _ => (1 : ℤ)) - B with hγdef
  have hγ : ∀ k, 0 ≤ γ k := by
    intro k
    have ha : (a k).natAbs ≤ ∑ j, (a j).natAbs :=
      Finset.single_le_sum (f := fun j => (a j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have hb : (b k).natAbs ≤ ∑ j, (b j).natAbs :=
      Finset.single_le_sum (f := fun j => (b j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have ha' : a k < (N : ℤ) :=
      calc a k ≤ (a k).natAbs := Int.le_natAbs
        _ ≤ ((∑ j, (a j).natAbs : ℕ) : ℤ) := by exact_mod_cast ha
        _ < (N : ℤ) := by rw [hN]; exact_mod_cast (by omega : ∑ j, (a j).natAbs < 1 + ∑ j, (a j).natAbs)
    have hb' : b k ≤ (M : ℤ) :=
      calc b k ≤ (b k).natAbs := Int.le_natAbs
        _ ≤ (M : ℤ) := by rw [hM]; exact_mod_cast hb
    simp only [hγdef, hBdef, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left ha'.le (Int.natCast_nonneg n)]
  obtain ⟨g, -, hg, hreg⟩ := hR K ι Ω y c (fun k => (γ k).toNat) hc
  have he : (fun k => ((γ k).toNat : ℤ)) = γ := funext fun k => Int.toNat_of_nonneg (hγ k)
  rw [he] at hg hreg
  have := finiteDimensional_chartLatQ hfin (fun k => ⟨c k, hc k⟩) (B + γ)
  have h1 := finrank_quot_le_of_regular hc hg (hreg B)
  rw [show B + γ = ((n * N + M : ℕ) : ℤ) • fun _ => (1 : ℤ) by rw [hγdef]; abel] at h1
  have h2 : (Module.finrank ℚ (chartLatQ y B 1 ⧸ chartDivSec y c B) : ℝ) ≤ C₀ * ((n * N + M : ℕ) : ℝ) ^ (D - 1) :=
    le_trans (by exact_mod_cast h1) hn
  have h3 : ((n * N + M : ℕ) : ℝ) ≤ ((N + M : ℕ) : ℝ) * (n : ℝ) := by
    have : n * N + M ≤ (N + M) * n := by nlinarith
    exact_mod_cast this
  calc (Module.finrank ℚ (chartLatQ y B 1 ⧸ chartDivSec y c B) : ℝ)
      ≤ |C₀| * ((n * N + M : ℕ) : ℝ) ^ (D - 1) :=
        h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    _ ≤ |C₀| * (((N + M : ℕ) : ℝ) * (n : ℝ)) ^ (D - 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h3 _) (abs_nonneg _)
    _ = |C₀| * ((N + M : ℕ) : ℝ) ^ (D - 1) * (n : ℝ) ^ (D - 1) := by rw [mul_pow, mul_assoc]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedRestrict
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GeneratedRestrict

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

abbrev locMap {M N : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N] (T : Submonoid (MRingOver S ι)) (g : M →ₗ[MRingOver S ι] N) :
    LocalizedModule T M →ₗ[MRingOver S ι] LocalizedModule T N :=
  IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M) (LocalizedModule.mkLinearMap T N) g

section General

variable {M N : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N]

theorem locMap_mk (T : Submonoid (MRingOver S ι)) (g : M →ₗ[MRingOver S ι] N) (m : M) (t : T) :
    locMap T g (LocalizedModule.mk m t) = LocalizedModule.mk (g m) t := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.map_mk', ← IsLocalizedModule.mk_eq_mk']

theorem locMap_cellRes (g : M →ₗ[MRingOver S ι] N) (J I : ∀ k, Finset (ι k))
    (x : LocalizedModule (KH.cellMon S J) M) :
    locMap (KH.cellMon S I) g (KH.cellRes S M J I x) = KH.cellRes S N J I (locMap (KH.cellMon S J) g x) := by
  by_cases h : KH.cellMon S J ≤ KH.cellMon S I
  · induction x using LocalizedModule.induction_on with
    | h m t =>
      rw [GenTwistGenerated.cellRes_mk h, locMap_mk, locMap_mk, GenTwistGenerated.cellRes_mk h]
  · unfold KH.cellRes
    rw [dite_eq_right h, dite_eq_right h]
    simp

end General

variable {V W : Ideal (MRingOver S ι)}

abbrev quotMap (hVW : V ≤ W) : (MRingOver S ι ⧸ V) →ₗ[MRingOver S ι] (MRingOver S ι ⧸ W) :=
  (Ideal.Quotient.factorₐ (MRingOver S ι) hVW).toLinearMap

theorem quotMap_mul (hVW : V ≤ W) (x y : MRingOver S ι ⧸ V) :
    quotMap hVW (x * y) = quotMap hVW x * quotMap hVW y := by
  simp [quotMap]

theorem quotMap_smul (hVW : V ≤ W) (s : S) (x : MRingOver S ι ⧸ V) :
    quotMap hVW (s • x) = s • quotMap hVW x :=
  LinearMap.map_smul_of_tower _ s x

theorem locMap_smul (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) (s : S)
    (x : LocalizedModule T (MRingOver S ι ⧸ V)) :
    locMap T (quotMap hVW) (s • x) = s • locMap T (quotMap hVW) x := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    rw [LocalizedModule.smul'_mk, locMap_mk, locMap_mk, LocalizedModule.smul'_mk, quotMap_smul]

theorem locMap_mul (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) (x y : LocalizedModule T (MRingOver S ι ⧸ V)) :
    locMap T (quotMap hVW) (x * y) = locMap T (quotMap hVW) x * locMap T (quotMap hVW) y := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    induction y using LocalizedModule.induction_on with
    | h m' t' =>
      rw [LocalizedModule.mk_mul_mk, locMap_mk, locMap_mk, locMap_mk, LocalizedModule.mk_mul_mk, quotMap_mul]

theorem locMap_one (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) :
    locMap T (quotMap hVW) (1 : LocalizedModule T (MRingOver S ι ⧸ V)) = 1 := by
  have e : ∀ (P : Type) [CommRing P] [Algebra (MRingOver S ι) P],
      (1 : LocalizedModule T P) = LocalizedModule.mk 1 1 := fun _ _ _ => OreLocalization.one_def
  have h1 : quotMap hVW (1 : MRingOver S ι ⧸ V) = 1 := by simp [quotMap]
  rw [e, e, locMap_mk, h1]

theorem cechD_cechMap {M N : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N] (g : M →ₗ[MRingOver S ι] N) (n : ℕ) (f : KH.CechC S ι M n) :
    KH.cechD S ι N n (KH.cechMap S ι g n f) = KH.cechMap S ι g (n + 1) (KH.cechD S ι M n f) := by
  funext I
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [KH.cechD, KH.cechMap, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · exact (congrArg (fun y => KH.faceSign I.1 k i • y) (locMap_cellRes g _ I.1 (f ⟨_, h⟩))).symm.trans
      (map_zsmul (locMap (KH.cellMon S I.1) g) _ _).symm
  · simp

theorem quotMap_mem_quotPart (hVW : V ≤ W) {c : K → ℤ} {x : MRingOver S ι ⧸ V}
    (hx : x ∈ KH.quotPart S V c) : quotMap hVW x ∈ KH.quotPart S W c := by
  unfold KH.quotPart at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    exact Submodule.subset_span ⟨p, hp, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx => rw [quotMap_smul]; exact Submodule.smul_mem _ s hx

theorem locMap_mem_locPart (hVW : V ≤ W) (T : Submonoid (MRingOver S ι)) {c : K → ℤ}
    {x : LocalizedModule T (MRingOver S ι ⧸ V)} (hx : x ∈ KH.locPart ι (KH.quotPart S V) T c) :
    locMap T (quotMap hVW) x ∈ KH.locPart ι (KH.quotPart S W) T c := by
  unfold KH.locPart at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    rw [locMap_mk]
    exact GenTwistGenerated.mk_mem_locPart _ t a ht (quotMap_mem_quotPart hVW hm)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx => rw [locMap_smul]; exact Submodule.smul_mem _ s hx

end GeneratedRestrict


open GeneratedRestrict in
theorem GeneratedRestrict.proof : GeneratedRestrict.Statement := by
  intro S _ K _ _ ι _ _ V W a hVW hV I
  obtain ⟨r, z, u, hz, hu, h1⟩ := hV I
  refine ⟨r, fun j => KH.cechMap S ι (quotMap hVW) 0 (z j), fun j => locMap _ (quotMap hVW) (u j),
    fun j => ?_, fun j => locMap_mem_locPart hVW _ (hu j), ?_⟩
  · obtain ⟨hzc, hzd⟩ := hz j
    refine GenTwistGenerated.mem_cechZc_zero (fun J => ?_) ?_
    · exact locMap_mem_locPart hVW _ ((Submodule.mem_pi.mp hzc) J (Set.mem_univ _))
    · rw [cechD_cechMap, LinearMap.mem_ker.mp hzd, map_zero]
  · have hc : ∀ j, KH.cechMap S ι (quotMap hVW) 0 (z j) I = locMap _ (quotMap hVW) (z j I) := fun j => rfl
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hc, ← locMap_mul, ← map_sum, h1, locMap_one]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedNefGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GeneratedNefGeneric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    NefOnGenericDeg (mCoordIdeal y) a

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockOldPartSurj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PowerBlockOldPartSurj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (m N : ℕ) (v : Fin N → Ω),
    (∀ j, v j ∈ chartLat y a m) → KH.GeneratesOn y (fun k => (m : ℤ) * a k) v →
    ∀ x ∈ mcPts (mCoordIdeal y), ∃ z ∈ mcPts (mCoordIdeal (addBlock y v)), basePart₂ z = x

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecCochReduce
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SecCochReduce.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (p : ℕ) (a : K → ℤ),
    ∀ s ∈ chartLat y a 1,
      FibreReduction.redCoch y p 0 (GenOnFibres.secCoch y ℤ s a) = GenOnFibres.secCoch y (ZMod p) s a

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionFormsIndependent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockResolutionFormsIndependent.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (n r : ℕ) (b : Fin r → MvPolynomial (Σ k, ι k) ℚ),
    IsSecBasisM d.y d.k₀ n b → ∀ a : Fin r → ℂ,
    (∀ y : d.R.X, ∑ k, a k * eval (blockPt d y) (map (algebraMap ℚ ℂ) (b k)) = 0) → a = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockGraphFibreRatio
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def BlockGraphFibreRatio.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (κ : Type) [Fintype κ] (y : (Σ k, ι k) → Ω) (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ → IsBlockImage y k₀ M N x →
    ∀ (G : GenFibre (inrV (ι := ι) (ι₂ := GlobalTheory κ)) (graphIdeal (mCoordIdeal y) (blockForms k₀ M))) (k : K) (i j : ι k),
      G.x' ⟨Sum.inl k, j⟩ ≠ 0 → G.x' ⟨Sum.inl k, i⟩ / G.x' ⟨Sum.inl k, j⟩ ∈ (algebraMap G.Φ G.Φ').range

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockPieceIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockPieceIndex.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ) (l : Ix κ → ℤ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    ∀ a b : ℕ, twoBlockStep x (matAct B x) a b =
      Real.log (modPieceCard (twoBlockMOuter x (matAct B x) c) (twoBlockMInner x (matAct B x) l) ![a + 1, b + 1])

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKoszulCechExact
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KoszulCech

noncomputable section

def KoszulCechExact.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (α : K → ℤ) (R : ℕ)
    (z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0),
    (∀ I : KH.Cell K ι 0, ∃ u : Fin R → LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V),
      (∀ j, u j ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-α)) ∧ ∑ j, u j * z j I = 1) →
    ∀ (c : K → ℤ) (n : ℕ),
      (∀ φ ∈ kosPart S ι V R α c 0 n, ∃ ψ ∈ kosPart S ι V R α c 1 n, kosD z 0 n ψ = φ) ∧
      (∀ p : ℕ, ∀ φ ∈ kosPart S ι V R α c (p + 1) n, kosD z p n φ = 0 →
        ∃ ψ ∈ kosPart S ι V R α c (p + 2) n, kosD z (p + 1) n ψ = φ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
