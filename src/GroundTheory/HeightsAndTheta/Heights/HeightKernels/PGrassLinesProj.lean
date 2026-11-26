module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointLengthSteps

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassLinesProj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace GrassmannianLinesProjective

def single (m : ℕ) (c : Fin (m + 1)) : PlIdx 1 m :=
  ⟨{Fin.cast (Nat.add_comm m 1) c}, Finset.card_singleton _⟩

theorem single_injective (m : ℕ) : Function.Injective (single m) := by
  intro c c' h
  have := congrArg Subtype.val h
  simpa [single] using this

theorem single_surjective (m : ℕ) : Function.Surjective (single m) := by
  rintro ⟨I, hI⟩
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hI
  exact ⟨Fin.cast (Nat.add_comm 1 m) a, Subtype.ext (by simp [single])⟩

def blk : Unit → Fin 1 := fun _ => 0

def coordMap (m : ℕ) : (Σ _ : Unit, Fin (m + 1)) → (Σ _ : Fin 1, PlIdx 1 m) :=
  fun p => ⟨0, single m p.2⟩

theorem coordMap_surjective (m : ℕ) : Function.Surjective (coordMap m) := by
  rintro ⟨k, I⟩
  obtain ⟨c, rfl⟩ := single_surjective m I
  refine ⟨⟨(), c⟩, ?_⟩
  rw [Subsingleton.elim k 0]
  rfl

theorem isBlockMap (m : ℕ) : IsBlockMap blk (coordMap m) := by
  refine ⟨fun _ _ _ => Subsingleton.elim _ _, ?_, fun _ => rfl, fun q _ => coordMap_surjective m q⟩
  rintro ⟨⟨⟩, c⟩ ⟨⟨⟩, c'⟩ h
  simp only [coordMap, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  rw [single_injective m h]

theorem card_plIdx (m : ℕ) : Fintype.card (PlIdx 1 m) = m + 1 := by
  rw [Fintype.card_subtype, ← Finset.powerset_univ, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, Nat.choose_one_right, add_comm]

theorem ringKrullDim_mring {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ringKrullDim (MRing ι) = ((1 + Fintype.card (Σ k, ι k) : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField,
    Nat.card_eq_fintype_card]
  push_cast
  rfl

theorem grassIdeal_eq_bot (m : ℕ) : grassIdeal 1 1 m = ⊥ := by
  have hA := GrassArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) 1 1 m le_rfl
  by_contra hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hle := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (grassIdeal 1 1 m))
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero hx0) (Ideal.Quotient.eq_zero_iff_mem.mpr hx)
  rw [hA.2.2.2, ringKrullDim_mring, Fintype.card_sigma] at hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, card_plIdx, smul_eq_mul] at hle
  have h' : ((1 * 1 * m + 1 + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ ((1 + 1 * (m + 1) : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast hle
  have h'' : 1 * 1 * m + 1 + 1 + 1 ≤ 1 + 1 * (m + 1) := by exact_mod_cast h'
  omega

theorem isArithVar_bot (m : ℕ) : IsArithVar (⊥ : Ideal (MRing (PBlk (m + 1)))) (m + 1) := by
  refine ⟨⟨()⟩, ⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun _ => ⟨0, ?_⟩⟩, ?_, ?_⟩
  · rw [Ideal.mem_bot]
    exact X_ne_zero _
  · exact Ideal.comap_bot_of_injective _ (C_injective _ _)
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), ringKrullDim_mring]
    congr 1
    simp
    omega

theorem isPullHerm (m : ℕ) :
    IsPullHerm blk (coordMap m) (fsMulti (PBlk (m + 1))) (fsMulti (plBlocks 1 1 m)) := by
  refine ⟨?_, fun z => ?_⟩
  · funext k
    rw [Subsingleton.elim k (blk ())]
    show (1 : ℤ) = Function.extend blk (fun _ => (1 : ℤ)) 0 (blk ())
    exact (Function.Injective.extend_apply (f := blk) (fun _ _ _ => Subsingleton.elim _ _)
      (fun _ => (1 : ℤ)) (0 : Fin 1 → ℤ) ()).symm
  · simp only [fsMulti, HermLine.ofMetrics, fsMetric, Fintype.prod_unique, zpow_one, coordMap]
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    exact ((Equiv.ofBijective _ ⟨single_injective m, single_surjective m⟩).sum_comp
      (fun i => ‖z ⟨0, i⟩‖ ^ 2)).symm

theorem blockFnField_le (m : ℕ) :
    blockFnField (grassCoord 1 1 m) ≤ blockFnField (grassCoord 1 1 m ∘ coordMap m) := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro t ⟨p, q, -, rfl⟩
  obtain ⟨p', rfl⟩ := coordMap_surjective m p
  obtain ⟨q', rfl⟩ := coordMap_surjective m q
  exact IntermediateField.subset_adjoin _ _ ⟨p', q', Subsingleton.elim _ _, rfl⟩

end GrassmannianLinesProjective


open GrassmannianLinesProjective in
theorem GrassLinesProj.proof (hPF : PFCoordStatement) : GrassLinesProj.Statement := by
  intro m II hII
  have hd : 1 * 1 * m + 1 = m + 1 := by ring
  have hA : IsArithVar (grassIdeal 1 1 m) (m + 1) := by
    rw [← hd]
    exact GrassArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) 1 1 m le_rfl
  have himg : imageZ (coordMap m) (grassIdeal 1 1 m) = ⊥ := by
    rw [grassIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ (rename_injective _ (isBlockMap m).2.1)
  have hB : IsArithVar (imageZ (coordMap m) (grassIdeal 1 1 m)) (m + 1) := by
    rw [himg]
    exact isArithVar_bot m
  have h := hPF II hII Unit (PBlk (m + 1)) (Fin 1) (plBlocks 1 1 m) blk (coordMap m) (GrassField 1 1 m)
    (grassCoord 1 1 m) (m + 1) (fun _ => fsMulti (PBlk (m + 1))) (fun _ => fsMulti (plBlocks 1 1 m))
    (isBlockMap m) hA hB (fun _ => FsLineSmooth.proof _ _) (fun _ => isPullHerm m)
  rw [IntermediateField.relfinrank_eq_one_iff.mpr (blockFnField_le m),
    show mCoordIdeal (grassCoord 1 1 m) = grassIdeal 1 1 m from rfl, himg, Nat.cast_one, one_mul] at h
  rw [hd]
  exact h

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopStacked
section -- merged from GroundTheory.PowerSubgroups.CountableNeighbourhoods.ExistsCover
namespace GroundTheory.Variant₂.N1

open NumberField

theorem exists_ne_zero_smul_mem {K : Type} [Field K] [NumberField K] {i : ℕ}
    (L : Submodule (RingOfIntegers K) (Fin i → K))
    (hL : Submodule.span K (L : Set (Fin i → K)) = ⊤) (v : Fin i → K) :
    ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • v ∈ L := by
  let T : Submodule K (Fin i → K) :=
    { carrier := {v | ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • v ∈ L}
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro a b ⟨d₁, h₁, ha⟩ ⟨d₂, h₂, hb⟩
        refine ⟨d₁ * d₂, mul_ne_zero h₁ h₂, ?_⟩
        rw [smul_add]
        refine L.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact L.smul_mem _ ha
        · rw [mul_smul]; exact L.smul_mem _ hb
      smul_mem' := by
        rintro c v ⟨d, hd, hv⟩
        obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers K)) c
        refine ⟨(b : RingOfIntegers K) * d, mul_ne_zero (nonZeroDivisors.coe_ne_zero b) hd, ?_⟩
        have key : ((b : RingOfIntegers K) * d) • (c • v) = a • (d • v) := by
          rw [← algebraMap_smul K ((b : RingOfIntegers K) * d) (c • v), ← algebraMap_smul K a (d • v),
            ← algebraMap_smul K d v, smul_smul, smul_smul]
          congr 1
          simp only [map_mul] at hab ⊢
          rw [← hab]
          ring
        rw [key]
        exact L.smul_mem _ hv }
  have hT : Submodule.span K (L : Set (Fin i → K)) ≤ T :=
    Submodule.span_le.2 fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩
  rw [hL] at hT
  exact hT Submodule.mem_top

theorem exists_cover {K : Type} [Field K] [NumberField K] {i : ℕ}
    {F X : GroundTheory.Heights₂.Heights.HermLattice K i} :
    X.lattice < F.lattice →
      ∃ w ∈ F.lattice,
        w ∉ X.lattice ∧
          ∀ (N : Submodule (NumberField.RingOfIntegers K) (Fin i → K)),
            X.lattice ≤ N →
              N ≤ X.lattice ⊔ NumberField.RingOfIntegers K ∙ w →
                N = X.lattice ∨ N = X.lattice ⊔ NumberField.RingOfIntegers K ∙ w := by
  classical
  intro hXF
  obtain ⟨s, hs⟩ := F.fg

  obtain ⟨d, hd0, hdX⟩ : ∃ d : RingOfIntegers K, d ≠ 0 ∧ ∀ f ∈ F.lattice, d • f ∈ X.lattice := by
    choose e he hem using fun v => exists_ne_zero_smul_mem X.lattice X.span_eq v
    refine ⟨∏ g ∈ s, e g, Finset.prod_ne_zero_iff.2 fun g _ => he g, fun f hf => ?_⟩
    rw [← hs] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      rw [← Finset.mul_prod_erase s e (Finset.mem_coe.1 hx), mul_comm, mul_smul]
      exact X.lattice.smul_mem _ (hem x)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact X.lattice.add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact X.lattice.smul_mem a hx
  have : Finite (RingOfIntegers K ⧸ Ideal.span {d}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by rwa [Ne, Ideal.span_singleton_eq_bot])

  let rep := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {d}))
  let P : (s → RingOfIntegers K ⧸ Ideal.span {d}) → (Fin i → K) :=
    fun q => ∑ a : s, rep (q a) • (a : Fin i → K)
  have key : ∀ v ∈ F.lattice, ∃ q, v - P q ∈ X.lattice := by
    intro v hv
    rw [← hs, Submodule.mem_span_finset'] at hv
    obtain ⟨c, rfl⟩ := hv
    refine ⟨fun a => Ideal.Quotient.mk _ (c a), ?_⟩
    have ht : ∀ a, ∃ t, t * d = c a - rep (Ideal.Quotient.mk _ (c a)) := fun a =>
      Ideal.mem_span_singleton'.1
        (Ideal.Quotient.eq.1 (Function.surjInv_eq (Ideal.Quotient.mk_surjective) _).symm)
    choose t ht using ht
    have hsum : ∑ a : s, c a • (a : Fin i → K) - P (fun a => Ideal.Quotient.mk _ (c a)) =
        d • ∑ a : s, t a • (a : Fin i → K) := by
      simp only [P]
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← sub_smul, ← ht a, mul_comm, mul_smul]
    rw [hsum]
    apply hdX
    rw [← hs]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span a.2)

  let S : Set (Submodule (RingOfIntegers K) (Fin i → K)) :=
    {N | X.lattice < N ∧ N ≤ F.lattice}
  let g : Submodule (RingOfIntegers K) (Fin i → K) → Set (s → RingOfIntegers K ⧸ Ideal.span {d}) :=
    fun N => {q | P q ∈ N}
  have sub : ∀ N₁ N₂ : Submodule (RingOfIntegers K) (Fin i → K), X.lattice ≤ N₁ →
      N₁ ≤ F.lattice → X.lattice ≤ N₂ → g N₁ ⊆ g N₂ → N₁ ≤ N₂ := by
    intro N₁ N₂ h₁ hF h₂ hg v hv
    obtain ⟨q, hq⟩ := key v (hF hv)
    have hPq : P q ∈ N₁ := by
      have := N₁.sub_mem hv (h₁ hq)
      rwa [sub_sub_cancel] at this
    have hPq₂ : P q ∈ N₂ := hg hPq
    have := N₂.add_mem (h₂ hq) hPq₂
    rwa [sub_add_cancel] at this
  have hinj : Set.InjOn g S := by
    intro N₁ h₁ N₂ h₂ h
    exact le_antisymm (sub N₁ N₂ h₁.1.le h₁.2 h₂.1.le h.subset)
      (sub N₂ N₁ h₂.1.le h₂.2 h₁.1.le h.symm.subset)
  have hfin : S.Finite := Set.Finite.of_finite_image (Set.toFinite (g '' S)) hinj
  obtain ⟨N, hN⟩ := hfin.exists_minimal ⟨F.lattice, hXF, le_rfl⟩
  obtain ⟨w, hwN, hwX⟩ := SetLike.exists_of_lt hN.1.1
  refine ⟨w, hN.1.2 hwN, hwX, fun N' h1 h2 => ?_⟩
  have hle : X.lattice ⊔ RingOfIntegers K ∙ w ≤ N :=
    sup_le hN.1.1.le ((Submodule.span_singleton_le_iff_mem _ _).2 hwN)
  by_cases h : N' = X.lattice
  · exact Or.inl h
  · right
    have hlt : X.lattice < N' := lt_of_le_of_ne h1 (Ne.symm h)
    have hNN' := hN.2 ⟨hlt, (h2.trans hle).trans hN.1.2⟩ (h2.trans hle)
    exact le_antisymm h2 (hle.trans hNN')

end GroundTheory.Variant₂.N1
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

namespace TopDualStacked

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

def DegForm (F G : HermLattice K i) : Prop :=
  ∀ (T T' : Type) [Fintype T] [DecidableEq T] [Fintype T'] [DecidableEq T']
    (b : Module.Basis T ℤ (dualLattice F)) (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T' ℤ (dualLattice G))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine G.withStdMetric b' hb') =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (F.withStdMetric.degree - G.withStdMetric.degree) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

theorem DegForm.trans {F G H : HermLattice K i} (h₁ : DegForm F G) (h₂ : DegForm G H) : DegForm F H := by
  intro T T' _ _ _ _ b hb b' hb' II hi hII
  obtain ⟨S, hS, hdS, ⟨c⟩⟩ := DualLatticeBasisExists.proof K i G
  have hc := DualEmbBijective.proof K i G S c
  have e₂ := h₂ S T' c hc b' hb' II hi hII
  have e₁ := h₁ T S b hb c hc II hi hII
  linarith

theorem degForm_self (hBasis : DualTopBasisChange.Statement) (F : HermLattice K i) : DegForm F F := by
  intro T T' _ _ _ _ b hb b' hb' II hi hII
  have e := hBasis K i F.withStdMetric T T' b hb b' hb' II hi hII
  rw [sub_self, zero_mul, add_zero]
  exact e

theorem withStdMetric_eq {F G : HermLattice K i} (h : F.lattice = G.lattice) :
    F.withStdMetric = G.withStdMetric := by
  cases F
  cases G
  cases h
  rfl

theorem degForm_iff (F G : HermLattice K i) : DegForm F G ↔ DegForm F.withStdMetric G.withStdMetric :=
  Iff.rfl

theorem degForm_of_eq (hBasis : DualTopBasisChange.Statement) {F G : HermLattice K i}
    (h : G.lattice = F.lattice) : DegForm F G := by
  rw [degForm_iff, withStdMetric_eq h]
  exact degForm_self hBasis _

theorem degForm_of_cover (hSimple : DualTopSimpleSub.Statement) {F G : HermLattice K i}
    (hlt : G.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), G.lattice ≤ N → N ≤ F.lattice → N = G.lattice ∨ N = F.lattice) :
    DegForm F G :=
  fun T T' _ _ _ _ b hb b' hb' II hi hII => hSimple K i F G T T' b hb b' hb' II hi hII hlt hcov

theorem exists_cover {F X : HermLattice K i} (hlt : X.lattice < F.lattice) :
    ∃ w ∈ F.lattice, w ∉ X.lattice ∧ ∀ N : Submodule (𝓞 K) (Fin i → K), X.lattice ≤ N →
      N ≤ X.lattice ⊔ Submodule.span (𝓞 K) {w} → N = X.lattice ∨ N = X.lattice ⊔ Submodule.span (𝓞 K) {w} :=
  _root_.GroundTheory.Variant₂.N1.exists_cover hlt

def addVector (X : HermLattice K i) (w : Fin i → K) : HermLattice K i where
  lattice := X.lattice ⊔ Submodule.span (𝓞 K) {w}
  fg := X.fg.sup (Submodule.fg_span_singleton w)
  span_eq := eq_top_iff.mpr (X.span_eq ▸ Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_left))
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

theorem degForm_of_le (hSimple : DualTopSimpleSub.Statement) (hBasis : DualTopBasisChange.Statement)
    (F G : HermLattice K i) (hle : G.lattice ≤ F.lattice) : DegForm F G := by
  have : IsNoetherian (𝓞 K) F.lattice := isNoetherian_of_fg_of_noetherian _ F.fg
  suffices h : ∀ N : Submodule (𝓞 K) F.lattice, ∀ G : HermLattice K i,
      G.lattice = N.map F.lattice.subtype → DegForm F G by
    refine h (G.lattice.comap F.lattice.subtype) G ?_
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hle]
  intro N
  refine WellFoundedGT.induction
    (motive := fun N : Submodule (𝓞 K) F.lattice => ∀ G : HermLattice K i,
      G.lattice = N.map F.lattice.subtype → DegForm F G) N ?_
  intro N IH G hG
  by_cases hGF : G.lattice = F.lattice
  · exact degForm_of_eq hBasis hGF
  have hlt : G.lattice < F.lattice :=
    lt_of_le_of_ne (hG ▸ Submodule.map_subtype_le _ _) hGF
  obtain ⟨w, hwF, hwG, hcov⟩ := exists_cover hlt
  have hG'F : (addVector G w).lattice ≤ F.lattice :=
    sup_le hlt.le ((Submodule.span_singleton_le_iff_mem _ _).mpr hwF)
  have hGG' : G.lattice < (addVector G w).lattice :=
    lt_of_le_of_ne le_sup_left fun h =>
      hwG (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self w))
  have hNG : N = G.lattice.comap F.lattice.subtype := by
    rw [hG, Submodule.comap_map_eq_of_injective F.lattice.injective_subtype]
  have hN : N < (addVector G w).lattice.comap F.lattice.subtype := by
    rw [hNG]
    refine lt_of_le_of_ne (Submodule.comap_mono hGG'.le) fun h => hGG'.ne ?_
    have h2 := congrArg (Submodule.map F.lattice.subtype) h
    rwa [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.mpr hlt.le,
      inf_eq_right.mpr hG'F] at h2
  have h1 : DegForm F (addVector G w) :=
    IH _ hN (addVector G w) (by rw [Submodule.map_comap_subtype, inf_eq_right.mpr hG'F])
  exact h1.trans (degForm_of_cover hSimple hGG' hcov)

end TopDualStacked


open TopDualStacked in
theorem DualTopStacked.proof (hSimple : DualTopSimpleSub.Statement) (hBasis : DualTopBasisChange.Statement)
    (hDeg : DualStackedDegree.Statement) : DualTopStacked.Statement := by
  intro K _ _ i F F' T _ _ b hb b' hb' a II hi hII hle hab
  have e := degForm_of_le hSimple hBasis F F' hle T T b hb b' hb' II hi hII
  rw [hDeg K i F F' T b b' a hle hab] at e
  exact e

end

end GroundTheory.Heights₂.Heights
end
