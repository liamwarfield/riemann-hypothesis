module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByForm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumOfFiltration
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumVanish
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem IntNumVanish.proof (h1 : HilbDegBound.Statement.{u})
    (h2 : HilbFnVanishBlock.Statement.{u}) (h3 : DegLTClosure.Statement)
    (h4 : EventualValueFacts.Statement) : IntNumVanish.Statement.{u} := by
  intro F _ K _ _ ι _ n Q hQ hQh hcase bs

  suffices hdeg : DegLT (hilbFn Q) n by
    exact (h4 K (mixedDiff bs (hilbFn Q)) 0 0).1 (hdeg bs)
  rcases hcase with hirr | hdim
  ·
    have hblock : ∃ k, ∀ i : ι k, (X ⟨k, i⟩ : MRing ι F) ∈ Q := by
      by_contra hne
      exact hirr fun k => by_contra fun h => hne ⟨k, fun i => by_contra fun hi => h ⟨i, hi⟩⟩
    obtain ⟨k, hk⟩ := hblock
    have hzero : (0 : (K → ℤ) → ℤ) =ᶠ[Filter.atTop] hilbFn Q := by
      filter_upwards [Filter.eventually_ge_atTop (fun _ : K => (1 : ℤ))] with m hm
      exact (h2 F K ι Q k hk m (hm k)).symm
    exact (h3 K n 0 (hilbFn Q) 0 0).2.2.2.2 hzero (degLT_zero n)
  · exact h1 F K ι n Q hQ hQh hdim

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PAssociatedMultiHomogPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem AssociatedMultiHomogPrime.proof (h1 : MultiHomogPrimeCriterion.Statement.{u})
    (h2 : ColonMultiHomog.Statement.{u}) : AssociatedMultiHomogPrime.Statement.{u} := by
  intro F _ K _ _ ι _ J hJ hJtop
  classical

  let A : Set (Ideal (MRing ι F)) :=
    {Q | ∃ (f : MRing ι F) (s : K → ℕ), IsMultiHomog f s ∧ f ∉ J ∧ Q = J.colon {f}}
  have hne : A.Nonempty := by
    refine ⟨J.colon {1}, 1, 0, ?_, ?_, rfl⟩
    · exact isWeightedHomogeneous_one F (blockWeight ι)
    · intro h
      exact hJtop ((Ideal.eq_top_iff_one J).2 h)
  have hnoeth : IsNoetherianRing (MRing ι F) := inferInstance
  obtain ⟨Q, ⟨f, s, hf, hfJ, rfl⟩, hmax⟩ :=
    (set_has_maximal_iff_noetherian (R := MRing ι F) (M := MRing ι F)).2 hnoeth A hne
  refine ⟨f, s, hf, hfJ, ?_⟩
  apply h1 F K ι (J.colon {f}) (h2 F K ι J f s hJ hf)
  · intro htop
    apply hfJ
    have h1mem : (1 : MRing ι F) ∈ J.colon {f} := by rw [htop]; exact Submodule.mem_top
    simpa using (Submodule.mem_colon_singleton.1 h1mem)
  · intro a b sa sb _ hb hab
    by_cases hbQ : b ∈ J.colon {f}
    · exact Or.inr hbQ
    left
    have hbf : b * f ∉ J := by
      intro h
      apply hbQ
      exact Submodule.mem_colon_singleton.2 (by simpa [smul_eq_mul] using h)
    have hform : IsMultiHomog (b * f) (sb + s) := hb.mul hf
    have hle : J.colon {f} ≤ J.colon {b * f} := by
      intro x hx
      have hx' : x * f ∈ J := by simpa [smul_eq_mul] using Submodule.mem_colon_singleton.1 hx
      refine Submodule.mem_colon_singleton.2 ?_
      have : b * (x * f) ∈ J := J.mul_mem_left b hx'
      simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using this
    have heq : J.colon {f} = J.colon {b * f} := by
      by_contra hne'
      exact hmax _ ⟨b * f, sb + s, hform, hbf, rfl⟩ (lt_of_le_of_ne hle hne')
    rw [heq]
    refine Submodule.mem_colon_singleton.2 ?_
    have hab' : a * b * f ∈ J := by simpa [smul_eq_mul] using Submodule.mem_colon_singleton.1 hab
    simpa [smul_eq_mul, mul_assoc] using hab'

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHilbFnCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem HilbFnCut.proof (h1 : GradedPieceQuot.Statement.{u}) (h2 : CutPieces.Statement.{u}) :
    HilbFnCut.Statement.{u} := by
  intro F _ K _ _ ι _ I x e hI hx hnzd m
  by_cases hm : ∀ k, 0 ≤ m k
  · set n : K → ℕ := fun k => (m k).toNat with hn
    have hA := h1 F K ι (I ⊔ Ideal.span {x}) n
    have hB := h1 F K ι I n
    have hC := h2 F K ι I x e n hI hx hnzd
    have hL : hilbFn (I ⊔ Ideal.span {x}) m =
        (Module.finrank F (gradedPiece (I ⊔ Ideal.span {x}) n) : ℤ) := by
      unfold hilbFn; rw [if_pos hm]
    have hM : hilbFn I m = (Module.finrank F (gradedPiece I n) : ℤ) := by
      unfold hilbFn; rw [if_pos hm]
    rw [hL, hM, hA, hB]
    by_cases he : e ≤ n
    · have hme : ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k := by
        intro k
        have h1k := he k
        have h0 := hm k
        simp only [Pi.sub_apply, hn] at h1k ⊢
        omega
      have hq : (fun k => ((m - fun k => (e k : ℤ)) k).toNat) = n - e := by
        funext k
        have h1k := he k
        have h0 := hm k
        simp only [Pi.sub_apply, hn] at h1k ⊢
        omega
      have hN : hilbFn I (m - fun k => (e k : ℤ)) =
          (Module.finrank F (gradedPiece I (n - e)) : ℤ) := by
        unfold hilbFn; rw [if_pos hme, hq]
      rw [hN, h1 F K ι I (n - e)]
      rw [if_pos he] at hC
      rw [hC]
      ring
    · have hme : ¬ ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k := by
        intro hall
        apply he
        intro k
        have h1k := hall k
        have h0 := hm k
        simp only [Pi.sub_apply, hn] at h1k ⊢
        omega
      have hN : hilbFn I (m - fun k => (e k : ℤ)) = 0 := by
        unfold hilbFn; rw [if_neg hme]
      rw [hN]
      rw [if_neg he] at hC
      rw [hC]
      ring
  · obtain ⟨k, hk⟩ := not_forall.mp hm
    have hme : ¬ ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k := by
      intro hall
      have := hall k
      simp only [Pi.sub_apply] at this
      omega
    unfold hilbFn
    rw [if_neg hm, if_neg hm, if_neg hme, sub_zero]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRelevantDimGe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem RelevantDimGe.proof (h1 : BlockAdjoinPrime.Statement.{u}) : RelevantDimGe.Statement.{u} := by
  intro R _ K _ _ ι Q hQ
  classical
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  let B : ℕ → Set K := fun j => {k | (e k : ℕ) < j}
  let J : ℕ → Ideal (MRing ι R) := fun j =>
    Q ⊔ Ideal.span {p | ∃ v : Σ k, ι k, v.1 ∈ B j ∧ p = X v}
  have hJ : ∀ j, (J j).IsPrime ∧ ∀ v : Σ k, ι k, v.1 ∉ B j → (X v ∈ J j ↔ X v ∈ Q) :=
    fun j => h1 R K ι Q (B j) hQ.isPrime hQ.multiHomog
  have hle : ∀ j, Q ≤ J j := fun j => le_sup_left
  have hmono : ∀ j, J j ≤ J (j + 1) := fun j =>
    sup_le_sup_left (Ideal.span_mono (by
      rintro p ⟨v, hv, rfl⟩
      exact ⟨v, lt_trans hv (Nat.lt_succ_self _), rfl⟩)) _
  have hstrict : ∀ j (hj : j < Fintype.card K), J j < J (j + 1) := by
    intro j hj
    refine lt_of_le_of_ne (hmono j) ?_
    obtain ⟨i, hi⟩ := hQ.relevant (e.symm ⟨j, hj⟩)
    intro heq
    have hmem : (X ⟨e.symm ⟨j, hj⟩, i⟩ : MRing ι R) ∈ J (j + 1) :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨⟨e.symm ⟨j, hj⟩, i⟩, by simp [B], rfl⟩)
    rw [← heq] at hmem
    exact hi (((hJ j).2 ⟨e.symm ⟨j, hj⟩, i⟩ (by simp [B])).1 hmem)
  let f : Fin (Fintype.card K + 1) → PrimeSpectrum.zeroLocus (R := MRing ι R) (Q : Set (MRing ι R)) :=
    fun j => ⟨⟨J j, (hJ j).1⟩, hle j⟩
  have hf : StrictMono f := by
    refine Fin.strictMono_iff_lt_succ.2 fun j => ?_
    show J j < J (j + 1)
    exact hstrict j j.isLt
  rw [ringKrullDim_quotient]
  exact Order.LTSeries.length_le_krullDim (LTSeries.mk (Fintype.card K) f hf)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDegLTEventuallyConst
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

namespace DegLTEventuallyConst

theorem eq_of_unitSteps_eq_zero {K : Type} [Fintype K] [DecidableEq K] (g : (K → ℤ) → ℤ)
    (N : K → ℤ) (h : ∀ m, N ≤ m → ∀ k, g m - g (m - Pi.single k 1) = 0) :
    ∀ d : ℕ, ∀ m, N ≤ m → ∑ k, (m k - N k).toNat = d → g m = g N := by
  intro d
  induction d with
  | zero =>
    intro m hm hs
    have hmN : m = N := by
      funext k
      have hk : (m k - N k).toNat = 0 := (Finset.sum_eq_zero_iff.mp hs) k (Finset.mem_univ k)
      have hle : N k ≤ m k := hm k
      omega
    rw [hmN]
  | succ d ih =>
    intro m hm hs
    obtain ⟨k, -, hk⟩ : ∃ k ∈ Finset.univ, (m k - N k).toNat ≠ 0 := by
      by_contra hne
      push Not at hne
      rw [Finset.sum_eq_zero hne] at hs
      omega
    obtain ⟨m', hm'⟩ : ∃ m' : K → ℤ, m' = m - Pi.single k (1 : ℤ) := ⟨_, rfl⟩
    have hm'k : m' k = m k - 1 := by simp [hm']
    have hm'j : ∀ j, j ≠ k → m' j = m j := by
      intro j hj
      simp [hm', hj]
    have hkk : N k + 1 ≤ m k := by omega
    have hNm' : N ≤ m' := by
      intro j
      show N j ≤ m' j
      by_cases hj : j = k
      · rw [hj, hm'k]
        omega
      · rw [hm'j j hj]
        exact hm j
    have hs' : ∑ j, (m' j - N j).toNat = d := by
      have e1 := Finset.add_sum_erase Finset.univ (fun j => (m j - N j).toNat) (Finset.mem_univ k)
      have e2 := Finset.add_sum_erase Finset.univ
        (fun j => (m' j - N j).toNat) (Finset.mem_univ k)
      have e3 : ∑ j ∈ Finset.univ.erase k, (m' j - N j).toNat =
          ∑ j ∈ Finset.univ.erase k, (m j - N j).toNat :=
        Finset.sum_congr rfl fun j hj => by rw [hm'j j (Finset.ne_of_mem_erase hj)]
      simp only [hm'k] at e2
      omega
    have step : g m - g m' = 0 := by rw [hm']; exact h m hm k
    rw [← ih _ hNm' hs']
    omega

theorem proof (h1 : MixedDiffLinear.Statement) : DegLTEventuallyConst.Statement := by
  intro K _ _ n f hf bs
  have hev : ∀ k : K, ∀ᶠ m in Filter.atTop,
      mixedDiff bs f m - mixedDiff bs f (m - Pi.single k 1) = 0 := by
    intro k
    have hk := hf (Matrix.vecCons (Pi.single k 1) bs)
    rw [(h1 K n bs f 0 0 0 (Pi.single k 1)).2.2.2.2] at hk
    exact hk
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Filter.eventually_all.mpr hev)
  exact ⟨mixedDiff bs f N, Filter.eventually_atTop.mpr ⟨N, fun m hm =>
    eq_of_unitSteps_eq_zero (mixedDiff bs f) N (fun m hm => hN m hm) _ m hm rfl⟩⟩

end DegLTEventuallyConst

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHilbDegBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace HilbDegBound

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isHomogeneous_of_isMultiHomogIdeal {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) :
    I.IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) := by
  classical
  have e : I = Ideal.span
      {g | ∃ f ∈ I, ∃ b, g = weightedHomogeneousComponent (blockWeight ι) b f} := by
    apply le_antisymm
    · intro f hf
      rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      exact Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨f, hf, b, rfl⟩
    · rw [Ideal.span_le]
      rintro g ⟨f, hf, b, rfl⟩
      exact hI f hf b
  rw [e]
  refine Ideal.homogeneous_span _ _ fun x hx => ?_
  obtain ⟨f, -, b, rfl⟩ := hx
  exact ⟨b, weightedHomogeneousComponent_isWeightedHomogeneous b f⟩

theorem isMultiHomogIdeal_sup_span {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {s : MRing ι F} {c : K → ℕ} (hs : IsMultiHomog s c) :
    IsMultiHomogIdeal (I ⊔ Ideal.span {s}) := by
  classical
  have h2 : (Ideal.span {s}).IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) :=
    Ideal.homogeneous_span _ _ fun x hx => ⟨c, (Set.mem_singleton_iff.mp hx) ▸ hs⟩
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem
    (h := (isHomogeneous_of_isMultiHomogIdeal hI).sup h2) (hp := hf) (m := b)

theorem lt_of_add_one_le_natCast {x : WithBot ℕ∞} {N : ℕ} (h : x + 1 ≤ N) : x < N := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have e : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [e, ← WithBot.coe_natCast, WithBot.coe_le_coe] at h
      exact absurd h (not_le.mpr (ENat.natCast_lt_top N))
    | coe a =>
      have : a + 1 ≤ N := by exact_mod_cast h
      exact_mod_cast (show a < N by omega)

theorem le_natCast_of_lt_natCast_succ {x : WithBot ℕ∞} {N : ℕ}
    (h : x < ((N + 1 : ℕ) : WithBot ℕ∞)) : x ≤ N := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      rw [← WithBot.coe_natCast, WithBot.coe_lt_coe] at h
      exact absurd h (not_lt.mpr le_top)
    | coe a =>
      have : a < N + 1 := by exact_mod_cast h
      exact_mod_cast (show a ≤ N by omega)


omit [Fintype K] [DecidableEq K] in
theorem degLT_listSum (h6 : DegLTClosure.Statement) {α : Type*} (n : ℕ)
    (g : α → (K → ℤ) → ℤ) (l : List α) (hl : ∀ a ∈ l, DegLT (g a) n) :
    DegLT (fun m => (l.map fun a => g a m).sum) n := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact degLT_zero n
  | cons a l ih =>
    have e : (fun m => ((a :: l).map fun a => g a m).sum) =
        g a + fun m => (l.map fun a => g a m).sum := by
      funext m
      simp
    rw [e]
    exact (h6 K n _ _ 0 0).1 (hl a (by simp)) (ih fun b hb => hl b (by simp [hb]))

end Lemmas

end HilbDegBound


open HilbDegBound in
theorem HilbDegBound.proof (h1 : HilbFnVanishBlock.Statement.{u}) (h2 : HilbFnCut.Statement.{u})
    (h3 : PrimeFiltration.Statement.{u}) (h4 : DimStrictDrop.Statement.{u})
    (h5 : RelevantDimGe.Statement.{u}) (h6 : DegLTClosure.Statement)
    (h7 : DegLTOfUnitSteps.Statement) : HilbDegBound.Statement.{u} := by
  intro F _ K _ _ ι _ n

  have irr : ∀ (n : ℕ) (Q : Ideal (MRing ι F)), ¬ IsRelevant Q → DegLT (hilbFn Q) n := by
    intro n Q hrel
    unfold IsRelevant at hrel
    push Not at hrel
    obtain ⟨k, hk⟩ := hrel
    have hev : (0 : (K → ℤ) → ℤ) =ᶠ[Filter.atTop] hilbFn Q := by
      filter_upwards [Filter.eventually_ge_atTop (1 : K → ℤ)] with m hm
      exact (h1 F K ι Q k hk m (hm k)).symm
    exact (h6 K n 0 _ 0 0).2.2.2.2 hev (degLT_zero n)
  induction n with
  | zero =>
    intro Q hQ hQh hdim
    by_cases hrel : IsRelevant Q
    · exfalso
      have hge := h5 F K ι Q ⟨hQ, hQh, hrel⟩
      rw [Nat.zero_add] at hdim
      exact absurd hge (not_le.mpr hdim)
    · exact irr 0 Q hrel
  | succ n ih =>
    intro Q hQ hQh hdim
    by_cases hrel : IsRelevant Q
    swap
    · exact irr _ Q hrel
    have hdimle : ringKrullDim (MRing ι F ⧸ Q) ≤ ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      have e : n + 1 + Fintype.card K = n + Fintype.card K + 1 := by omega
      rw [e] at hdim
      exact le_natCast_of_lt_natCast_succ hdim
    apply h7 K n
    intro k
    obtain ⟨i, hi⟩ := hrel k
    have hx : IsMultiHomog (X ⟨k, i⟩ : MRing ι F) (Pi.single k 1) := isWeightedHomogeneous_X _ _ _
    have hnzd : ∀ y, (X ⟨k, i⟩ : MRing ι F) * y ∈ Q → y ∈ Q :=
      fun y hy => (hQ.mem_or_mem hy).resolve_left hi
    have hcut := h2 F K ι Q (X ⟨k, i⟩) (Pi.single k 1) hQh hx hnzd
    have hJ : IsMultiHomogIdeal (Q ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι F)}) :=
      isMultiHomogIdeal_sup_span hQh hx
    have hs : (fun j => ((Pi.single k 1 : K → ℕ) j : ℤ)) = (Pi.single k 1 : K → ℤ) := by
      funext j
      by_cases h : j = k <;> simp [h]
    have heq : diffStep (Pi.single k 1) (hilbFn Q) =
        hilbFn (Q ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι F)}) := by
      funext m
      rw [hcut m, hs]
      rfl
    rw [heq]
    obtain ⟨l, hl1, hl2, -⟩ := h3 F K ι _ hJ
    obtain ⟨G, hG⟩ : ∃ G : Ideal (MRing ι F) × (K → ℕ) → (K → ℤ) → ℤ,
        G = fun p => shiftFn (fun j => (p.2 j : ℤ)) (hilbFn p.1) := ⟨_, rfl⟩
    have hfun : hilbFn (Q ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι F)}) = fun m =>
        (l.map fun p => G p m).sum := by
      funext m
      rw [hl2 m, hG]
      rfl
    rw [hfun]
    apply degLT_listSum h6 n G l
    intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := hl1 p hp
    rw [hG]
    refine (h6 K n (hilbFn p.1) 0 0 _).2.2.1 ?_
    refine ih p.1 hp1 hp2 ?_
    have hlt : Q < p.1 := by
      refine lt_of_le_of_ne (le_sup_left.trans hp3) fun h => hi ?_
      rw [h]
      exact hp3 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have := hQ
    have := hp1
    have hd := h4 (MRing ι F) Q p.1 hlt
    exact lt_of_add_one_le_natCast (hd.trans hdimle)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHilbFnVanishBlock
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem exists_block_var_of_weight_pos {K : Type} [DecidableEq K] {ι : K → Type}
    (d : (Σ k, ι k) →₀ ℕ) (k : K) (h : 1 ≤ Finsupp.weight (blockWeight ι) d k) :
    ∃ v : Σ k, ι k, v.1 = k ∧ d v ≠ 0 := by
  by_contra hne
  push Not at hne
  have h0 : Finsupp.weight (blockWeight ι) d k = 0 := by
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun v hv => ?_
    have hv1 : v.1 ≠ k := fun e => (Finsupp.mem_support_iff.mp hv) (hne v e)
    simp [blockWeight, hv1]
  omega

theorem mem_of_block_vars_mem {F : Type u} [Field F] {K : Type} [DecidableEq K] {ι : K → Type}
    (Q : Ideal (MRing ι F)) (k : K) (hX : ∀ i, (X ⟨k, i⟩ : MRing ι F) ∈ Q) (m : K → ℕ)
    (hm : 1 ≤ m k) (f : MRing ι F) (hf : f ∈ weightedHomogeneousSubmodule F (blockWeight ι) m) :
    f ∈ Q := by
  have hspan : Ideal.span ((X : (Σ k, ι k) → MRing ι F) '' {v | v.1 = k}) ≤ Q := by
    rw [Ideal.span_le]
    rintro _ ⟨⟨k', i⟩, hv, rfl⟩
    simp only [Set.mem_ofPred_eq] at hv
    subst hv
    exact hX i
  apply hspan
  rw [mem_ideal_span_X_image]
  intro d hd
  rw [mem_weightedHomogeneousSubmodule] at hf
  have hw : Finsupp.weight (blockWeight ι) d = m := hf (Finsupp.mem_support_iff.mp hd)
  obtain ⟨v, hv, hdv⟩ := exists_block_var_of_weight_pos d k (by rw [hw]; exact hm)
  exact ⟨v, hv, hdv⟩

theorem HilbFnVanishBlock.proof : HilbFnVanishBlock.Statement.{u} := by
  intro F _ K _ _ ι _ Q k hX m hm
  unfold hilbFn
  split_ifs with h
  · have hbot : gradedPiece Q (fun k => (m k).toNat) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
      have hfQ : f ∈ Q := mem_of_block_vars_mem Q k hX _ (by omega) f hf
      simpa using (Ideal.Quotient.eq_zero_iff_mem).mpr hfQ
    rw [hbot, finrank_bot]
    rfl
  · rfl

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDiffStepExpansion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

namespace DiffStepExpansion

variable {K : Type}

lemma listSum_apply {α : Type} (l : List α) (F : α → (K → ℤ) → ℤ) (m : K → ℤ) :
    (l.map F).sum m = (l.map fun t => F t m).sum := by
  induction l with
  | nil => simp
  | cons t l ih => simp [ih]

def expand [DecidableEq K] (l : List ((K × (K → ℤ)) × ℤ)) (f : (K → ℤ) → ℤ) : (K → ℤ) → ℤ :=
  (l.map fun t => t.2 • shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)).sum

lemma expand_apply [DecidableEq K] (l : List ((K × (K → ℤ)) × ℤ)) (f : (K → ℤ) → ℤ)
    (m : K → ℤ) :
    expand l f m = (l.map fun t => t.2 * diffStep (Pi.single t.1.1 1) f (m - t.1.2)).sum := by
  unfold expand
  rw [listSum_apply]
  rfl

def expandable (K : Type) [DecidableEq K] : AddSubgroup (K → ℤ) where
  carrier := {b | ∃ l : List ((K × (K → ℤ)) × ℤ), ∀ f, diffStep b f = expand l f}
  zero_mem' := ⟨[], fun f => by funext m; simp [diffStep, expand]⟩
  add_mem' := by
    rintro a c ⟨la, ha⟩ ⟨lc, hc⟩
    refine ⟨la ++ lc.map (fun t => ((t.1.1, t.1.2 + a), t.2)), fun f => ?_⟩
    funext m
    have h1 := congrFun (ha f) m
    have h2 := congrFun (hc f) (m - a)
    simp only [diffStep] at h1 h2 ⊢
    rw [expand_apply] at h1 h2
    rw [expand_apply, List.map_append, List.sum_append, List.map_map, ← h1]
    have h3 : (lc.map ((fun t : (K × (K → ℤ)) × ℤ =>
          t.2 * diffStep (Pi.single t.1.1 1) f (m - t.1.2)) ∘
          fun t => ((t.1.1, t.1.2 + a), t.2))).sum =
        (lc.map fun t => t.2 * diffStep (Pi.single t.1.1 1) f (m - a - t.1.2)).sum := by
      congr 1
      apply List.map_congr_left
      intro t _
      simp only [Function.comp_apply]
      congr 2
      abel
    rw [h3, ← h2]
    have : m - (a + c) = m - a - c := by abel
    rw [this]
    ring
  neg_mem' := by
    rintro c ⟨lc, hc⟩
    refine ⟨lc.map (fun t => ((t.1.1, t.1.2 - c), -t.2)), fun f => ?_⟩
    funext m
    have h2 := congrFun (hc f) (m + c)
    simp only [diffStep] at h2 ⊢
    rw [expand_apply] at h2
    rw [expand_apply, List.map_map]
    have h3 : (lc.map ((fun t : (K × (K → ℤ)) × ℤ =>
          t.2 * diffStep (Pi.single t.1.1 1) f (m - t.1.2)) ∘
          fun t => ((t.1.1, t.1.2 - c), -t.2))).sum =
        -(lc.map fun t => t.2 * diffStep (Pi.single t.1.1 1) f (m + c - t.1.2)).sum := by
      clear hc h2
      induction lc with
      | nil => simp
      | cons t l ih =>
        simp only [List.map_cons, List.sum_cons, Function.comp_apply] at ih ⊢
        have e : m - (t.1.2 - c) = m + c - t.1.2 := by abel
        rw [ih, e]
        ring
    rw [h3, ← h2]
    have e1 : m + c - c = m := by abel
    have e2 : m - -c = m + c := by abel
    rw [e1, e2]
    ring

lemma single_mem [DecidableEq K] (k : K) : (Pi.single k 1 : K → ℤ) ∈ expandable K :=
  ⟨[((k, 0), 1)], fun f => by funext m; simp [expand, shiftFn]⟩

theorem proof : DiffStepExpansion.Statement := by
  intro K _ _ b
  have hb : b ∈ expandable K := by
    rw [← Finset.univ_sum_single b]
    refine AddSubgroup.sum_mem _ fun k _ => ?_
    have : (Pi.single k (b k) : K → ℤ) = b k • (Pi.single k 1 : K → ℤ) := by
      ext j
      by_cases h : j = k <;> simp [h]
    rw [this]
    exact AddSubgroup.zsmul_mem _ (single_mem k) _
  obtain ⟨l, hl⟩ := hb
  exact ⟨l, fun f => hl f⟩

end DiffStepExpansion

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumAssoc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem IntNumAssoc.list_sum_finset_sum {α β : Type*} (l : List α) (s : Finset β)
    (f : α → β → ℤ) :
    (l.map fun a => ∑ b ∈ s, f a b).sum = ∑ b ∈ s, (l.map fun a => f a b).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Finset.sum_add_distrib]

theorem IntNumAssoc.list_sum_ite_enat {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P] :
    (l.map fun a => if P a then (1 : ℕ∞) else 0).sum =
      ((l.map fun a => if P a then (1 : ℕ) else 0).sum : ℕ) := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : P a <;> simp [h, ih]

theorem IntNumAssoc.list_sum_ite_mul {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P]
    (c : ℤ) :
    (l.map fun a => if P a then c else 0).sum =
      ((l.map fun a => if P a then (1 : ℕ) else 0).sum : ℤ) * c := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : P a <;> simp [h, ih, add_mul]

theorem IntNumAssoc.proof (h1 : PrimeFiltration.Statement.{u})
    (h2 : IntNumOfFiltration.Statement.{u}) (h3 : MultAtPrimeAtMinimal.Statement.{u})
    (h4 : IntNumVanish.Statement.{u}) (h5 : TopDimMinimal.Statement.{u})
    (h6 : HilbDegBound.Statement.{u}) : IntNumAssoc.Statement.{u} := by
  classical
  intro F _ K _ _ ι _ n J hJ hdim bs
  obtain ⟨l, hl, hhilb, hmult⟩ := h1 F K ι J hJ
  have hdimp : ∀ p ∈ l, ringKrullDim (MRing ι F ⧸ p.1) <
      ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := fun p hp =>
    lt_of_le_of_lt (ringKrullDim_le_of_surjective (Ideal.Quotient.factor (hl p hp).2.2)
      (Ideal.Quotient.factor_surjective (hl p hp).2.2)) hdim
  have hdeg : ∀ p ∈ l, DegLT (hilbFn p.1) (n + 1) := fun p hp =>
    h6 F K ι (n + 1) p.1 (hl p hp).1 (hl p hp).2.1 (hdimp p hp)
  rw [h2 F K ι n J l hdeg hhilb bs]
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MRing ι F) J
  have hp : ∀ p ∈ l, intNum F p.1 bs =
      ∑ W ∈ hfin.toFinset, if p.1 = W then (if IsRelevant W then intNum F W bs else 0) else 0 := by
    intro p hpl
    rw [Finset.sum_ite_eq]
    by_cases hz : intNum F p.1 bs = 0
    · rw [hz]
      simp
    · have := (hl p hpl).1
      have hrel : IsRelevant p.1 := by
        by_contra hr
        exact hz (h4 F K ι n p.1 (hl p hpl).1 (hl p hpl).2.1 (Or.inl hr) bs)
      have hbig : ¬ ringKrullDim (MRing ι F ⧸ p.1) <
          ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := fun hs =>
        hz (h4 F K ι n p.1 (hl p hpl).1 (hl p hpl).2.1 (Or.inr hs) bs)
      have hJ' : ringKrullDim (MRing ι F ⧸ J) <
          ((n + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
        have e : n + Fintype.card K + 1 = n + 1 + Fintype.card K := by omega
        rw [e]
        exact hdim
      have hmin := h5 _ J p.1 (n + Fintype.card K) (hl p hpl).2.2 hJ' hbig
      rw [if_pos (hfin.mem_toFinset.mpr hmin), if_pos hrel]
  have hl2 : (l.map fun p => intNum F p.1 bs) = l.map fun p =>
      ∑ W ∈ hfin.toFinset, if p.1 = W then (if IsRelevant W then intNum F W bs else 0) else 0 :=
    List.map_congr_left hp
  rw [hl2, IntNumAssoc.list_sum_finset_sum]
  have hsupp : Function.support (fun W => idealCycle J W * intNum F W bs) ⊆
      (hfin.toFinset : Set (Ideal (MRing ι F))) := by
    intro W hW
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra hn
    apply Function.mem_support.mp hW
    unfold idealCycle
    rw [dite_eq_right (fun h => hn h.1), zero_mul]
  unfold cycEval
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun W hW => ?_
  have hWm : W ∈ J.minimalPrimes := hfin.mem_toFinset.mp hW
  have : W.IsPrime := hWm.1.1
  rw [IntNumAssoc.list_sum_ite_mul]
  unfold idealCycle
  by_cases hr : IsRelevant W
  · rw [dite_eq_left ⟨hWm, hr⟩, if_pos hr]
    have hcount : multAt J W = (l.map fun p => if p.1 = W then (1 : ℕ∞) else 0).sum := by
      rw [hmult W]
      congr 1
      apply List.map_congr_left
      intro p hpl
      have := (hl p hpl).1
      exact h3 F K ι J p.1 W (hl p hpl).2.2 hWm
    rw [hcount, IntNumAssoc.list_sum_ite_enat, ENat.toNat_natCast]
  · rw [dite_eq_right (fun h => hr h.2), if_neg hr]
    simp

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPrimeFiltration
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem decompose_blockWeight {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*}
    (r : MRing ι R) (b : K → ℕ) :
    (DirectSum.decompose (weightedHomogeneousSubmodule R (blockWeight ι)) r b : MRing ι R) =
      weightedHomogeneousComponent (blockWeight ι) b r :=
  weightedDecomposition.decompose'_apply R (blockWeight ι) r b

theorem isMultiHomogIdeal_iff_isHomogeneous {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K]
    {ι : K → Type*} (I : Ideal (MRing ι R)) :
    IsMultiHomogIdeal I ↔ I.IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) := by
  constructor
  · intro h b r hr
    rw [decompose_blockWeight]
    exact h r hr b
  · intro h r hr b
    rw [← decompose_blockWeight]
    exact h b hr

theorem isMultiHomogIdeal_sup_span {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K]
    {ι : K → Type*} {J : Ideal (MRing ι R)} {f : MRing ι R} {s : K → ℕ}
    (hJ : IsMultiHomogIdeal J) (hf : IsMultiHomog f s) :
    IsMultiHomogIdeal (J ⊔ Ideal.span {f}) := by
  rw [isMultiHomogIdeal_iff_isHomogeneous] at hJ ⊢
  refine hJ.sup (Ideal.homogeneous_span _ _ ?_)
  rintro x rfl
  exact ⟨s, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf⟩

theorem multAt_top {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
    (W : Ideal (MRing ι R)) [W.IsPrime] : multAt (⊤ : Ideal (MRing ι R)) W = 0 := by
  unfold multAt
  have : Subsingleton (MRing ι R ⧸ (⊤ : Ideal (MRing ι R))) :=
    Ideal.Quotient.subsingleton_iff.mpr rfl
  exact Module.length_eq_zero

theorem PrimeFiltration.proof (h1 : AssociatedMultiHomogPrime.Statement.{u})
    (h2 : FiltrationStepHilb.Statement.{u}) (h3 : FiltrationStepLength.Statement.{u})
    (h4 : ColonMultiHomog.Statement.{u}) : PrimeFiltration.Statement.{u} := by
  intro F _ K _ _ ι _ J
  have : WellFoundedGT (Ideal (MRing ι F)) := inferInstance
  induction J using WellFoundedGT.induction
  rename_i J ih
  intro hJ
  by_cases hT : J = ⊤
  · subst hT
    refine ⟨[], by simp, fun m => by simp [hilbFn_top], fun W _ => by simp [multAt_top]⟩
  obtain ⟨f, s, hf, hfJ, hQ⟩ := h1 F K ι J hJ hT
  have hQh : IsMultiHomogIdeal (J.colon {f}) := h4 F K ι J f s hJ hf
  have hJQ : J ≤ J.colon {f} := fun x hx =>
    Submodule.mem_colon_singleton.mpr (J.mul_mem_right f hx)
  have hlt : J < J ⊔ Ideal.span {f} :=
    SetLike.lt_iff_le_and_exists.mpr
      ⟨le_sup_left, f, Ideal.mem_sup_right (Ideal.mem_span_singleton_self f), hfJ⟩
  obtain ⟨l', hl'1, hl'2, hl'3⟩ := ih _ hlt (isMultiHomogIdeal_sup_span hJ hf)
  refine ⟨(J.colon {f}, s) :: l', ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨hQ, hQh, hJQ⟩
    · obtain ⟨a, b, c⟩ := hl'1 p hp
      exact ⟨a, b, le_sup_left.trans c⟩
  · intro m
    rw [h2 F K ι J f s hJ hf m, hl'2 m, List.map_cons, List.sum_cons, add_comm]
  · intro W _
    rw [h3 F K ι J W f, hl'3 W, List.map_cons, List.sum_cons, add_comm]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem MixedDiffLinear.full : MixedDiffLinear.Statement := MixedDiffLinear.proof

theorem DegLTClosure.full : DegLTClosure.Statement := DegLTClosure.proof MixedDiffLinear.full

theorem DiffStepExpansion.full : DiffStepExpansion.Statement := DiffStepExpansion.proof

theorem DegLTOfUnitSteps.full : DegLTOfUnitSteps.Statement :=
  DegLTOfUnitSteps.proof DiffStepExpansion.full MixedDiffLinear.full DegLTClosure.full

theorem DegLTEventuallyConst.full : DegLTEventuallyConst.Statement :=
  DegLTEventuallyConst.proof MixedDiffLinear.full

theorem EventualValueFacts.full : EventualValueFacts.Statement := EventualValueFacts.proof

theorem HilbFnVanishBlock.full : HilbFnVanishBlock.Statement.{u} := HilbFnVanishBlock.proof

theorem GradedPieceQuot.full : GradedPieceQuot.Statement.{u} := GradedPieceQuot.proof

theorem CutPieces.full : CutPieces.Statement.{u} := CutPieces.proof

theorem HilbFnCut.full : HilbFnCut.Statement.{u} := HilbFnCut.proof GradedPieceQuot.full CutPieces.full

theorem MultiHomogPrimeCriterion.full : MultiHomogPrimeCriterion.Statement.{u} :=
  MultiHomogPrimeCriterion.proof

theorem ColonMultiHomog.full : ColonMultiHomog.Statement.{u} := ColonMultiHomog.proof

theorem AssociatedMultiHomogPrime.full : AssociatedMultiHomogPrime.Statement.{u} :=
  AssociatedMultiHomogPrime.proof MultiHomogPrimeCriterion.full ColonMultiHomog.full

theorem FiltrationStepHilb.full : FiltrationStepHilb.Statement.{u} := FiltrationStepHilb.proof

theorem FiltrationStepLength.full : FiltrationStepLength.Statement.{u} := FiltrationStepLength.proof

theorem PrimeFiltration.full : PrimeFiltration.Statement.{u} :=
  PrimeFiltration.proof AssociatedMultiHomogPrime.full FiltrationStepHilb.full
    FiltrationStepLength.full ColonMultiHomog.full

theorem MultAtPrimeAtMinimal.full : MultAtPrimeAtMinimal.Statement.{u} := MultAtPrimeAtMinimal.proof

theorem DimStrictDrop.full : DimStrictDrop.Statement.{u} := DimStrictDrop.proof

theorem BlockAdjoinPrime.full : BlockAdjoinPrime.Statement.{u} := BlockAdjoinPrime.proof

theorem RelevantDimGe.full : RelevantDimGe.Statement.{u} := RelevantDimGe.proof BlockAdjoinPrime.full

theorem HilbDegBound.full : HilbDegBound.Statement.{u} :=
  HilbDegBound.proof HilbFnVanishBlock.full HilbFnCut.full PrimeFiltration.full DimStrictDrop.full
    RelevantDimGe.full DegLTClosure.full DegLTOfUnitSteps.full

theorem TopDimMinimal.full : TopDimMinimal.Statement.{u} := TopDimMinimal.proof DimStrictDrop.full

theorem IntNumOfFiltration.full : IntNumOfFiltration.Statement.{u} :=
  IntNumOfFiltration.proof MixedDiffLinear.full DegLTEventuallyConst.full EventualValueFacts.full

theorem GradedPieceFree.full : GradedPieceFree.Statement.{u} := GradedPieceFree.proof

theorem SpecialPieceRank.full : SpecialPieceRank.Statement.{u} :=
  SpecialPieceRank.proof GradedPieceFree.full

theorem GenericPieceRank.full : GenericPieceRank.Statement.{u} := GenericPieceRank.proof

theorem SpecialIdealMultiHomog.full : SpecialIdealMultiHomog.Statement.{u} :=
  SpecialIdealMultiHomog.proof

theorem SpecialIdealCorresp.full : SpecialIdealCorresp.Statement.{u} := SpecialIdealCorresp.proof

theorem SpecialIdealSurj.full : SpecialIdealSurj.Statement.{u} := SpecialIdealSurj.proof

theorem SpecialMultAt.full : SpecialMultAt.Statement.{u} := SpecialMultAt.proof

theorem SpecialCycleEval.full : SpecialCycleEval.Statement.{u} :=
  SpecialCycleEval.proof SpecialIdealCorresp.full SpecialIdealSurj.full SpecialMultAt.full

theorem SpecialDimBound.full : SpecialDimBound.Statement.{u} := SpecialDimBound.proof

theorem IntNumVanish.full : IntNumVanish.Statement.{u} :=
  IntNumVanish.proof HilbDegBound.full HilbFnVanishBlock.full DegLTClosure.full EventualValueFacts.full

theorem IntNumAssoc.full : IntNumAssoc.Statement.{u} :=
  IntNumAssoc.proof PrimeFiltration.full IntNumOfFiltration.full MultAtPrimeAtMinimal.full
    IntNumVanish.full TopDimMinimal.full HilbDegBound.full

theorem CutByForm.full : CutByForm.Statement.{u} :=
  CutByForm.proof IntNumAssoc.full HilbFnCut.full MixedDiffLinear.full

theorem ConservationOfNumber.full : ConservationOfNumber.Statement.{u} :=
  ConservationOfNumber.proof IntNumAssoc.full SpecialCycleEval.full SpecialPieceRank.full
    GenericPieceRank.full SpecialIdealMultiHomog.full SpecialDimBound.full

end GroundTheory.Heights₂.Heights.NumbersDVR
