module

public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
public import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolume
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.DiscOrder

section General

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

theorem idxN_eq_card (A B : Submodule R W) : idxN A B = Nat.card (A ⧸ B.comap A.subtype) := rfl

theorem idxN_mul {A B C : Submodule R W} (h1 : A ≤ B) (h2 : B ≤ C) :
    idxN B A * idxN C B = idxN C A :=
  AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr h1)
    ((Submodule.toAddSubgroup_le _ _).mpr h2)

theorem idxN_eq_one {A B : Submodule R W} : idxN A B = 1 ↔ A ≤ B :=
  AddSubgroup.relIndex_eq_one.trans (Submodule.toAddSubgroup_le _ _)

theorem exists_max_of_covBy {X Y : Submodule R W} (h : X ⋖ Y) :
    ∃ P : Ideal R, P.IsMaximal ∧ (∀ r : R, r ∈ P ↔ ∀ y ∈ Y, r • y ∈ X) ∧ idxN Y X = Nat.card (R ⧸ P) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 ((covBy_iff_quot_is_simple h.le).1 h)
  refine ⟨P, hP, fun r => ⟨fun hr y hy => ?_, fun hr => ?_⟩, by rw [idxN_eq_card]; exact Nat.card_congr e.toEquiv⟩
  · have : r • (Submodule.Quotient.mk ⟨y, hy⟩ : Y ⧸ X.comap Y.subtype) = 0 := by
      apply e.injective
      rw [map_smul, map_zero]
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective P (e (Submodule.Quotient.mk ⟨y, hy⟩))
      rw [← ha, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact P.mul_mem_right a hr
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    exact this
  · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk 1))
    have h0 : r • e.symm (Submodule.Quotient.mk 1) = 0 := by
      rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hr y y.2
    rw [← map_smul, EmbeddingLike.map_eq_zero_iff, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at h0
    simpa using h0

theorem exists_covBy {X Y : Submodule R W} (hY : Y.FG) (h : X < Y) : ∃ Z, X ≤ Z ∧ Z ⋖ Y := by
  have := CompleteLattice.Iic_coatomic_of_compact_element ((Submodule.fg_iff_compact Y).1 hY)
  rcases eq_top_or_exists_le_coatom (⟨X, h.le⟩ : Set.Iic Y) with e | ⟨Z, hZ, hle⟩
  · exact absurd (congrArg Subtype.val e) h.ne
  · exact ⟨Z.1, hle, (covBy_iff_coatom_Iic Z.2).2 hZ⟩

end General

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] [FiniteDimensional K V] in
theorem idxN_ne_zero {X Y : Submodule (𝓞 K) V} (hX : Submodule.IsFullLattice K X) (hY : Y.FG) :
    idxN Y X ≠ 0 := by
  obtain ⟨d, hd, hdY⟩ := indexBasic_denom (nonZeroDivisors (𝓞 K)) Y X hY
    (by rw [indexBasic_locS_top (K := K) X (Submodule.IsFullLattice.span_eq_top (A := K) (M := X))]; exact le_top)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  have hn : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd0
  have : Module.Finite (𝓞 K) Y := Module.Finite.iff_fg.mpr hY
  have : Module.Finite ℤ (Y ⧸ X.comap Y.subtype) := Module.Finite.trans (𝓞 K) _
  have : Finite (Y ⧸ X.comap Y.subtype) := by
    apply Module.finite_of_fg_torsion
    intro q
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (X.comap Y.subtype) q
    refine ⟨⟨(Ideal.absNorm (Ideal.span {d}) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn)⟩, ?_⟩
    change (Ideal.absNorm (Ideal.span {d}) : ℤ) • Submodule.mkQ (X.comap Y.subtype) y = 0
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change (Ideal.absNorm (Ideal.span {d}) : ℤ) • (y : V) ∈ X
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 K), ← hc, mul_smul]
    exact X.smul_mem c (hdY y y.2)
  rw [idxN_eq_card]
  exact Nat.card_pos.ne'

omit [StarRing K] [FiniteDimensional K V] in
theorem lattice_between {X Y Z : Submodule (𝓞 K) V} (hX : Submodule.IsFullLattice K X)
    (hY : Submodule.IsFullLattice K Y) (h1 : X ≤ Z) (h2 : Z ≤ Y) : Submodule.IsFullLattice K Z :=
  Submodule.IsFullLattice.of_le_of_fg K h1 (hY.fg.of_le h2)

variable (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate)
include hs hn

theorem dual_covBy {X Y : Submodule (𝓞 K) V} (hX : Submodule.IsFullLattice K X)
    (hY : Submodule.IsFullLattice K Y) (hc : X ⋖ Y) : dual h Y ⋖ dual h X := by
  have dl := dualLattice (𝓞 K) K V h hs hn star_algebraMap_ringOfIntegers_mem_range
  have an := (dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range).1
  refine ⟨lt_of_le_of_ne (an _ _ hc.le) fun e => hc.ne ?_, fun Z h1 h2 => ?_⟩
  · rw [← (dl X hX).2.1, ← e, (dl Y hY).2.1]
  · have hZ := lattice_between (dl Y hY).1 (dl X hX).1 h1.le h2.le
    have a1 := an _ _ h1.le
    have a2 := an _ _ h2.le
    rw [(dl Y hY).2.1] at a1
    rw [(dl X hX).2.1] at a2
    rcases hc.eq_or_eq a2 a1 with e | e
    · exact h2.ne (by rw [← e, (dl Z hZ).2.1])
    · exact h1.ne (by rw [← e, (dl Z hZ).2.1])

theorem idxN_dual_of_covBy {X Y : Submodule (𝓞 K) V} (hX : Submodule.IsFullLattice K X)
    (hY : Submodule.IsFullLattice K Y) (hc : X ⋖ Y) : idxN (dual h X) (dual h Y) = idxN Y X := by
  obtain ⟨P, hP, hPm, hPi⟩ := exists_max_of_covBy hc
  obtain ⟨Q, hQ, hQm, hQi⟩ := exists_max_of_covBy (dual_covBy h hs hn hX hY hc)
  set σ := locBasic_sigma (genusCovol_hinj (K := K)) star_algebraMap_ringOfIntegers_mem_range with hσ
  have hσσ : ∀ r, σ (σ r) = r := fun r => genusCovol_hinj (by
    rw [locBasic_sigma_spec, locBasic_sigma_spec, star_star])
  let e : 𝓞 K ≃+* 𝓞 K := RingEquiv.ofBijective σ (Function.Involutive.bijective hσσ)
  have hle : P ≤ Q.comap σ := by
    intro r hr
    rw [Ideal.mem_comap, hQm]
    intro x hx
    rw [dualBasic_mem_dual] at hx ⊢
    intro y hy
    have := hx _ ((hPm r).1 hr y hy)
    rw [genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range] at this
    rw [genusBasic_hsmul_right]
    exact this
  have hPQ : P = Q.comap σ := hP.eq_of_le (Ideal.comap_ne_top σ hQ.ne_top) hle
  have hm : Q = P.map (e : 𝓞 K →+* 𝓞 K) := by
    rw [hPQ]
    exact (Ideal.map_comap_of_surjective σ e.surjective Q).symm
  rw [hPi, hQi]
  exact (Nat.card_congr (Ideal.quotientEquiv P Q e hm).toEquiv).symm

theorem idxN_dual {X : Submodule (𝓞 K) V} (hX : Submodule.IsFullLattice K X) : ∀ (n : ℕ)
    (Y : Submodule (𝓞 K) V), Submodule.IsFullLattice K Y → X ≤ Y → idxN Y X = n →
    idxN (dual h X) (dual h Y) = n := by
  have an := (dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range).1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y hY hle hi
  rcases hle.eq_or_lt with rfl | hlt
  · rw [← hi, idxN_eq_one.2 le_rfl, idxN_eq_one.2 le_rfl]
  obtain ⟨Z, hXZ, hc⟩ := exists_covBy hY.fg hlt
  have hZ := lattice_between hX hY hXZ hc.le
  have m1 := idxN_mul hXZ hc.le
  have n1 := idxN_ne_zero hX hZ.fg
  have n2 := idxN_ne_zero hZ hY.fg
  have n3 : idxN Y Z ≠ 1 := fun e => hc.lt.not_ge (idxN_eq_one.1 e)
  have hlt' : idxN Z X < n := by
    rw [← hi, ← m1]
    exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero n1) (by omega)
  rw [← idxN_mul (an _ _ hc.le) (an _ _ hXZ), ih _ hlt' Z hZ hXZ rfl, idxN_dual_of_covBy h hs hn hZ hY hc,
    ← hi, ← m1, mul_comm]

end GlobalTheory.Mass.DiscOrder

namespace GlobalTheory.Mass.DiscOrder

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ M : Submodule (𝓞 K) V, IsIntLat h M → discN h M ≠ 0 ∧ (discN h M = 1 ↔ IsUnimodular h M) ∧ (∀ M' : Submodule (𝓞 K) V, IsIntLat h M' → M ≤ M' → idxN M' M ≠ 0 ∧ discN h M = discN h M' * idxN M' M ^ 2) ∧ (∀ N ∈ genus h M, IsIntLat h N ∧ discN h N = discN h M) ∧ (∀ P : Ideal (𝓞 K), P.IsMaximal → ((discN h M : ℕ) : 𝓞 K) ∉ P → IsUnimodularAt h P M) ∧ (∀ M' : Submodule (𝓞 K) V, IsIntLat h M' → M ≤ M' → ∀ P : Ideal (𝓞 K), P.IsMaximal → IsUnimodularAt h P M → loc (K := K) P M = loc (K := K) P M') := by
  intro K V _ _ _ _ _ _ _ _ h _ hs hn M hM
  have dl := dualLattice (𝓞 K) K V h hs hn star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨an, -, -, hint, huni⟩ := dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  have ld := locDual (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  have hMd := (hint M).1 hM.2
  have h0 : ∀ N, IsIntLat h N → discN h N ≠ 0 := fun N hN => idxN_ne_zero hN.1 (dl N hN.1).1.fg
  refine ⟨h0 M hM, ?_, fun M' hM' hle => ⟨idxN_ne_zero hM.1 hM'.1.fg, ?_⟩, fun N hN => ?_,
    fun P hP hd => ?_, fun M' hM' hle P hP hu => ?_⟩
  · rw [huni, discN, idxN_eq_one]
    exact ⟨fun e => ⟨hM.2, e⟩, fun e => e.2⟩
  · have hMd' := (hint M').1 hM'.2
    rw [discN, discN, ← idxN_mul (hle.trans hMd') (an _ _ hle), ← idxN_mul hle hMd',
      idxN_dual h hs hn hM.1 _ M' hM'.1 hle rfl]
    ring
  · have hNi : IsIntLat h N := ⟨hN.1,
      (((genusBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range).2.2 M N hM.1.fg hN.1.fg hN.2).2).1 hM.2⟩
    refine ⟨hNi, genusCovol_lemmaS _ M (dual h M) N (dual h N) hMd ((hint N).1 hNi.2) rfl (h0 M hM)
      (h0 N hNi) fun P hP => ?_⟩
    obtain ⟨g, hg, hgL⟩ := hN.2 P hP
    have hle := locBasic_hcompl_le (K := K) P
    have key : ∀ A B : Submodule (𝓞 K) V, gmap g (loc (K := K) P A) = loc (K := K) P B →
        gmap g (locS P.primeCompl A) = locS P.primeCompl B := by
      intro A B e
      rw [← genusCovol_locS_locS hle A, gmap_locS_comm]
      change locS P.primeCompl (gmap g (loc (K := K) P A)) = _
      rw [e]
      exact genusCovol_locS_locS hle B
    obtain ⟨a1, a2, -, -, -⟩ := isomAct (𝓞 K) K V h g hg M
    have hgM : (gmap g M).FG := hM.1.fg.map ((g : V →ₗ[K] V).restrictScalars (𝓞 K))
    have b1 := (ld (gmap g M) hgM).1 P hP.isPrime
    have b2 := (ld N hN.1.fg).1 P hP.isPrime
    refine ⟨_, g.injective, genusCovol_addData g _ _ (key _ _ hgL), genusCovol_addData g _ _ (key _ _ ?_)⟩
    rw [b2.1, ← b2.2, ← hgL, ← a2 P, b1.2, ← b1.1, a1, (isomAct (𝓞 K) K V h g hg (dual h M)).2.1 P]
  · have b := (ld M hM.1.fg).1 P hP.isPrime
    rw [IsUnimodularAt, b.2, ← b.1]
    refine le_antisymm ((locBasic_locS_mono _ fun x hx => ?_).trans (locBasic_locS_idem _ M).le)
      (locBasic_locS_mono _ hMd)
    refine ⟨(discN h M : 𝓞 K), Submonoid.subset_closure ⟨hd, fun t ht => ?_⟩, ?_⟩
    · have : t = (discN h M : 𝓞 K) := genusCovol_hinj (by rw [ht]; simp)
      rwa [this]
    · rw [Nat.cast_smul_eq_nsmul]
      have := AddSubgroup.nsmul_index_mem (H := M.toAddSubgroup.addSubgroupOf (dual h M).toAddSubgroup) ⟨x, hx⟩
      exact this
  · have b := (ld M hM.1.fg).1 P hP.isPrime
    rw [IsUnimodularAt, b.2, ← b.1] at hu
    refine le_antisymm (locBasic_locS_mono _ hle) ?_
    rw [← hu]
    exact locBasic_locS_mono _ (((hint M').1 hM'.2).trans (an _ _ hle))

end GlobalTheory.Mass.DiscOrder
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodulaStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ M : Submodule (𝓞 K) V, IsIntLat h M → discN h M ≠ 0 ∧ (discN h M = 1 ↔ IsUnimodular h M) ∧ (∀ M' : Submodule (𝓞 K) V, IsIntLat h M' → M ≤ M' → idxN M' M ≠ 0 ∧ discN h M = discN h M' * idxN M' M ^ 2) ∧ (∀ N ∈ genus h M, IsIntLat h N ∧ discN h N = discN h M) ∧ (∀ P : Ideal (𝓞 K), P.IsMaximal → ((discN h M : ℕ) : 𝓞 K) ∉ P → IsUnimodularAt h P M) ∧ (∀ M' : Submodule (𝓞 K) V, IsIntLat h M' → M ≤ M' → ∀ P : Ideal (𝓞 K), P.IsMaximal → IsUnimodularAt h P M → loc (K := K) P M = loc (K := K) P M') := by
  first | exact @GlobalTheory.Mass.DiscOrder.main | exact GlobalTheory.Mass.DiscOrder.main | (intros; apply GlobalTheory.Mass.DiscOrder.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumMonoSubadditive
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumMonoSubadditive
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.OrbMono

theorem orbSum_eq (G α : Type) [Group G] [MulAction G α] (X : Set α) (N : α → ℝ≥0∞) :
    orbSum G X N = ∑' q : MulAction.orbitRel.Quotient G α,
      if Quotient.out q ∈ X then
        ((ENat.card (MulAction.stabilizer G (Quotient.out q)) : ℕ∞) : ℝ≥0∞)⁻¹ * N (Quotient.out q)
      else 0 := by
  exact (tsum_subtype {q : MulAction.orbitRel.Quotient G α | Quotient.out q ∈ X}
    (fun q => ((ENat.card (MulAction.stabilizer G (Quotient.out q)) : ℕ∞) : ℝ≥0∞)⁻¹ *
      N (Quotient.out q))).trans (tsum_congr fun q => by simp [Set.indicator_apply])

theorem main : ∀ (G α : Type) [Group G] [MulAction G α] , (∀ (X Y : Set α) (N N' : α → ℝ≥0∞), X ⊆ Y → (∀ x ∈ X, N x ≤ N' x) → orbSum G X N ≤ orbSum G Y N') ∧ (∀ (X : Set α) (B : ℝ≥0∞), orbSum G X (fun _ => B) = B * orbMass G X) ∧ (∀ (ι : Type) (s : Finset ι) (X : Set α) (Xi : ι → Set α) (N : α → ℝ≥0∞), X ⊆ ⋃ i ∈ s, Xi i → orbSum G X N ≤ ∑ i ∈ s, orbSum G (Xi i) N) ∧ (∀ (X : Set α) (s : Set α), (∀ x ∈ X, ∃ y ∈ s, ∃ g : G, g • y = x) → orbMass G X ≤ ((s.encard : ℕ∞) : ℝ≥0∞)) ∧ (∀ (X : Set α) (N N' : α → ℝ≥0∞), orbSum G X (fun x => N x + N' x) = orbSum G X N + orbSum G X N') := by
  intro G α _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X Y N N' hXY hN
    simp only [orbSum_eq]
    refine ENNReal.tsum_le_tsum fun q => ?_
    by_cases hq : Quotient.out q ∈ X
    · rw [if_pos hq, if_pos (hXY hq)]
      gcongr
      exact hN _ hq
    · rw [if_neg hq]
      exact zero_le
  · intro X B
    simp only [orbMass, orbSum]
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun q => by rw [mul_one, mul_comm]
  · intro ι s X Xi N hX
    simp only [orbSum_eq]
    rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
    refine ENNReal.tsum_le_tsum fun q => ?_
    by_cases hq : Quotient.out q ∈ X
    · obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.1 (hX hq)
      refine le_trans ?_ (Finset.single_le_sum (fun j _ => zero_le) hi)
      simp [hq, hqi]
    · rw [if_neg hq]
      exact zero_le
  · intro X s hs
    have key : ∀ q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
        ∃ y : s, (Quotient.mk _ (y : α) : MulAction.orbitRel.Quotient G α) = q.1 := by
      rintro ⟨q, hq⟩
      obtain ⟨y, hy, g, hg⟩ := hs _ hq
      refine ⟨⟨y, hy⟩, ?_⟩
      exact (Quotient.sound (MulAction.orbitRel_apply.2 ⟨g⁻¹, by simp [← hg]⟩)).trans
        (Quotient.out_eq q)
    choose φ hφ using key
    have hinj : Function.Injective φ := by
      intro a b h
      apply Subtype.ext
      rw [← hφ a, ← hφ b, h]
    calc orbMass G X
        = ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
            ((ENat.card (MulAction.stabilizer G (Quotient.out q.1)) : ℕ∞) : ℝ≥0∞)⁻¹ * 1 := rfl
      _ ≤ ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
            (fun _ : s => (1 : ℝ≥0∞)) (φ q) := by
          refine ENNReal.tsum_le_tsum fun q => ?_
          rw [mul_one]
          apply ENNReal.inv_le_one.2
          have h1 : (1 : ℕ∞) ≤ ENat.card (MulAction.stabilizer G (Quotient.out q.1)) :=
            (ENat.one_le_card_iff_nonempty _).2 ⟨1⟩
          exact_mod_cast h1
      _ ≤ ∑' _ : s, (1 : ℝ≥0∞) := (by refine' _root_.le_trans _ (_root_.tsum_comp_le_tsum_of_injective hinj _); exact _root_.le_rfl)
      _ = s.encard := ENNReal.tsum_set_one s
  · intro X N N'
    simp only [orbSum]
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun q => mul_add _ _ _

end GlobalTheory.Mass.OrbMono
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumMonoSubadditiveStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive : ∀ (G α : Type) [Group G] [MulAction G α] , (∀ (X Y : Set α) (N N' : α → ℝ≥0∞), X ⊆ Y → (∀ x ∈ X, N x ≤ N' x) → orbSum G X N ≤ orbSum G Y N') ∧ (∀ (X : Set α) (B : ℝ≥0∞), orbSum G X (fun _ => B) = B * orbMass G X) ∧ (∀ (ι : Type) (s : Finset ι) (X : Set α) (Xi : ι → Set α) (N : α → ℝ≥0∞), X ⊆ ⋃ i ∈ s, Xi i → orbSum G X N ≤ ∑ i ∈ s, orbSum G (Xi i) N) ∧ (∀ (X : Set α) (s : Set α), (∀ x ∈ X, ∃ y ∈ s, ∃ g : G, g • y = x) → orbMass G X ≤ ((s.encard : ℕ∞) : ℝ≥0∞)) ∧ (∀ (X : Set α) (N N' : α → ℝ≥0∞), orbSum G X (fun x => N x + N' x) = orbSum G X N + orbSum G X N') := by
  first | exact @GlobalTheory.Mass.OrbMono.main | exact GlobalTheory.Mass.OrbMono.main | (intros; apply GlobalTheory.Mass.OrbMono.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeQuotientGensAndIntermediateCount
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeQuotientGensAndIntermediateCount
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.LatticeGens

section Dedekind
variable {R V : Type*} [CommRing R] [IsDedekindDomain R] [AddCommGroup V] [Module R V]

theorem exists_gens_of_between (A : Submodule R V) (m : R) (hm : m ≠ 0) (t : Finset V) :
    (∀ x ∈ t, m • x ∈ A) → ∀ L : Submodule R V, A ≤ L → L ≤ A ⊔ Submodule.span R (t : Set V) →
      ∃ t' : Finset V, t'.card ≤ t.card ∧ L = A ⊔ Submodule.span R (t' : Set V) := by
  induction t using Finset.induction_on with
  | empty =>
    intro _ L h1 h2
    exact ⟨∅, le_rfl, le_antisymm h2 (by simpa using h1)⟩
  | insert x t hx ih =>
    intro ht L h1 h2
    obtain ⟨t', hc, ht'⟩ := ih (fun y hy => ht y (Finset.mem_insert_of_mem hy))
      (L ⊓ (A ⊔ Submodule.span R (t : Set V))) (le_inf h1 le_sup_left) inf_le_right
    set I : Ideal R := (A ⊔ Submodule.span R (t : Set V)).comap (LinearMap.toSpanSingleton R V x)
      with hI
    set J : Ideal R := (L ⊔ Submodule.span R (t : Set V)).comap (LinearMap.toSpanSingleton R V x)
      with hJ
    have hIJ : I ≤ J := Submodule.comap_mono (sup_le_sup_right h1 _)
    have hI0 : I ≠ 0 := by
      intro h
      have : m ∈ I := Submodule.mem_sup_left (ht x (Finset.mem_insert_self _ _))
      rw [h] at this
      exact hm (by simpa using this)
    obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hIJ hI0
    have haJ : a ∈ J := by
      rw [← ha]; exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self a)
    obtain ⟨l, hl, s, hs, hls⟩ := Submodule.mem_sup.1 haJ
    have hls' : l + s = a • x := hls
    refine ⟨insert l t', ?_, le_antisymm ?_ ?_⟩
    · rw [Finset.card_insert_of_notMem hx]
      exact (Finset.card_insert_le _ _).trans (by omega)
    · intro y hy
      have hy2 := h2 hy
      rw [Finset.coe_insert, Submodule.span_insert] at hy2
      obtain ⟨a0, ha0, z, hz, rfl⟩ := Submodule.mem_sup.1 hy2
      obtain ⟨w, hw, s0, hs0, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hw
      have hr : r ∈ J := by
        have : r • x = ((a0 + (r • x + s0)) - a0) - s0 := by abel
        change r • x ∈ L ⊔ Submodule.span R (t : Set V)
        rw [this]
        exact sub_mem (Submodule.mem_sup_left (sub_mem hy (h1 ha0))) (Submodule.mem_sup_right hs0)
      rw [← ha] at hr
      obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.1 hr
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.1 hj
      have hi' : i • x ∈ A ⊔ Submodule.span R (t : Set V) := hi
      have key : a0 + ((i + k * a) • x + s0) - k • l ∈
          L ⊓ (A ⊔ Submodule.span R (t : Set V)) := by
        refine ⟨sub_mem hy (L.smul_mem _ hl), ?_⟩
        have : a0 + ((i + k * a) • x + s0) - k • l = a0 + i • x + s0 + k • s := by
          rw [add_smul, mul_smul, ← hls', smul_add]; abel
        rw [this]
        exact add_mem (add_mem (add_mem (Submodule.mem_sup_left ha0) hi')
          (Submodule.mem_sup_right hs0)) (Submodule.mem_sup_right (Submodule.smul_mem _ _ hs))
      rw [ht'] at key
      have hle : A ⊔ Submodule.span R (t' : Set V) ≤
          A ⊔ Submodule.span R ((insert l t' : Finset V) : Set V) :=
        sup_le_sup_left (Submodule.span_mono (by simp)) _
      have hl' : k • l ∈ A ⊔ Submodule.span R ((insert l t' : Finset V) : Set V) :=
        Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      simpa using add_mem (hle key) hl'
    · rw [Finset.coe_insert, Submodule.span_insert]
      refine sup_le h1 (sup_le ?_ ?_)
      · exact (Submodule.span_singleton_le_iff_mem _ _).2 hl
      · exact (le_sup_right.trans ht'.ge).trans inf_le_left

end Dedekind

section Count
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem idxN_smul_mem (A B : Submodule R V) {x : V} (hx : x ∈ B) :
    ((idxN B A : ℕ) : R) • x ∈ A := by
  rw [Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_relIndex_mem A.toAddSubgroup (K := B.toAddSubgroup) hx

theorem card_map_mkQ (A B : Submodule R V) : Nat.card (B.map A.mkQ) = idxN B A := by
  have h := AddSubgroup.relIndex_ker (K := B.toAddSubgroup) A.mkQ.toAddMonoidHom
  have hk : A.mkQ.toAddMonoidHom.ker = A.toAddSubgroup := by
    ext x; simp
  rw [hk] at h
  unfold idxN
  rw [h]
  rfl

theorem encard_between_le (A B : Submodule R V) (hn : idxN B A ≠ 0) (e : ℕ)
    (h : ∀ L, A ≤ L → L ≤ B →
      ∃ t' : Finset V, t'.card ≤ e ∧ L = A ⊔ Submodule.span R (t' : Set V)) :
    {L | A ≤ L ∧ L ≤ B}.encard ≤ ((idxN B A ^ e : ℕ) : ℕ∞) := by
  have hfin : Finite (B.map A.mkQ) := Nat.finite_of_card_ne_zero (by rwa [card_map_mkQ])
  let Φ : (Fin e → B.map A.mkQ) → Submodule R V := fun f =>
    (Submodule.span R (Set.range fun i => (f i : V ⧸ A))).comap A.mkQ
  have hsub : {L | A ≤ L ∧ L ≤ B} ⊆ Φ '' Set.univ := by
    rintro L ⟨h1, h2⟩
    obtain ⟨t, hc, ht⟩ := h L h1 h2
    obtain ⟨emb⟩ : Nonempty (t ↪ Fin e) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hc)
    let g : Fin e → V := Function.extend emb (fun x => (x : V)) 0
    have hg : ∀ i, g i ∈ Submodule.span R (t : Set V) := by
      intro i
      by_cases hi : ∃ x, emb x = i
      · obtain ⟨x, rfl⟩ := hi
        simp only [g, emb.injective.extend_apply]
        exact Submodule.subset_span x.2
      · simp only [g, Function.extend_apply' _ _ _ hi]
        simp
    have hspan : Submodule.span R (Set.range g) = Submodule.span R (t : Set V) := by
      refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
      · rintro _ ⟨i, rfl⟩; exact hg i
      · intro x hx
        exact ⟨emb ⟨x, hx⟩, by simp only [g, emb.injective.extend_apply]⟩
    have hgB : ∀ i, g i ∈ B := fun i => h2 (by rw [ht]; exact Submodule.mem_sup_right (hg i))
    refine ⟨fun i => ⟨A.mkQ (g i), Submodule.mem_map_of_mem (hgB i)⟩, trivial, ?_⟩
    have : (Set.range fun i => A.mkQ (g i)) = A.mkQ '' Set.range g := by
      rw [← Set.range_comp]; rfl
    change (Submodule.span R (Set.range fun i => A.mkQ (g i))).comap A.mkQ = L
    rw [this, ← Submodule.map_span, Submodule.comap_map_mkQ, hspan, ← ht]
  calc {L | A ≤ L ∧ L ≤ B}.encard ≤ (Φ '' Set.univ).encard := Set.encard_le_encard hsub
    _ ≤ (Set.univ : Set (Fin e → B.map A.mkQ)).encard := Set.encard_image_le _ _
    _ = _ := by
      rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.card_fun, card_map_mkQ]
      simp

end Count

theorem exists_scaled_span (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (B : Submodule (𝓞 K) V) (hB : B.FG) :
    ∃ (c : 𝓞 K) (t : Finset V), c ≠ 0 ∧ t.card ≤ Module.finrank K V ∧ (∀ x ∈ t, c • x ∈ B) ∧
      B ≤ Submodule.span (𝓞 K) (t : Set V) := by
  obtain ⟨b, hbB, hspan, hli⟩ := exists_linearIndependent K (B : Set V)
  have hbf : b.Finite := hli.setFinite
  obtain ⟨s, rfl⟩ := hbf.exists_finset_coe
  have hcard : s.card ≤ Module.finrank K V := LinearIndependent.finset_card_le_finrank hli
  obtain ⟨G, rfl⟩ := hB
  have h1 : ∀ x ∈ G, ∃ c : 𝓞 K, c ≠ 0 ∧ c • x ∈ Submodule.span (𝓞 K) (s : Set V) := by
    intro x hx
    have hx' : x ∈ Submodule.span K (s : Set V) := by
      rw [hspan]; exact Submodule.subset_span (Submodule.subset_span hx)
    obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ _ hx'
    exact ⟨c, nonZeroDivisors.coe_ne_zero c, hc⟩
  choose! f hf0 hf using h1
  set c : 𝓞 K := ∏ x ∈ G, f x with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 hf0
  have hcK : algebraMap (𝓞 K) K c ≠ 0 := by simpa using hc0
  have hcG : ∀ x ∈ G, c • x ∈ Submodule.span (𝓞 K) (s : Set V) := by
    intro x hx
    rw [hc, ← Finset.prod_erase_mul _ _ hx, mul_smul]
    exact Submodule.smul_mem _ _ (hf x hx)
  let φ : V →ₗ[𝓞 K] V := (LinearMap.lsmul K V (algebraMap (𝓞 K) K c)⁻¹).restrictScalars (𝓞 K)
  have hφ : ∀ x, φ (c • x) = x := by
    intro x
    simp only [φ, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
    rw [← algebraMap_smul K c x, smul_smul, inv_mul_cancel₀ hcK, one_smul]
  refine ⟨c, s.image φ, hc0, Finset.card_image_le.trans hcard, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    rw [← map_smul, hφ]
    exact hbB hy
  · rw [Submodule.span_le]
    intro x hx
    rw [Finset.coe_image, ← Submodule.map_span, ← hφ x]
    exact Submodule.mem_map_of_mem (hcG x hx)

theorem gens_and_count : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (A B : Submodule (𝓞 K) V), A ≤ B → idxN B A ≠ 0 → (B.FG → ∃ t : Finset V, t.card ≤ Module.finrank K V ∧ B = A ⊔ Submodule.span (𝓞 K) (t : Set V)) ∧ ∀ (e : ℕ) (t : Finset V), t.card ≤ e → B = A ⊔ Submodule.span (𝓞 K) (t : Set V) → ({L | A ≤ L ∧ L ≤ B}.encard ≤ ((idxN B A ^ e : ℕ) : ℕ∞)) ∧ ∀ L, A ≤ L → L ≤ B → ∃ t' : Finset V, t'.card ≤ e ∧ L = A ⊔ Submodule.span (𝓞 K) (t' : Set V) := by
  intro K V _ _ _ _ _ _ _ A B hAB hn
  have hn' : ((idxN B A : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hn
  refine ⟨fun hB => ?_, fun e t hc ht => ?_⟩
  · obtain ⟨c, t, hc0, hcard, hcB, hBt⟩ := exists_scaled_span K V B hB
    obtain ⟨t', h1, h2⟩ := exists_gens_of_between A (((idxN B A : ℕ) : 𝓞 K) * c)
      (mul_ne_zero hn' hc0) t
      (fun x hx => by rw [mul_smul]; exact idxN_smul_mem A B (hcB x hx)) B hAB
      (hBt.trans le_sup_right)
    exact ⟨t', h1.trans hcard, h2⟩
  · have key : ∀ L, A ≤ L → L ≤ B →
        ∃ t' : Finset V, t'.card ≤ e ∧ L = A ⊔ Submodule.span (𝓞 K) (t' : Set V) := by
      intro L h1 h2
      obtain ⟨t', h3, h4⟩ := exists_gens_of_between A _ hn' t
        (fun x hx => idxN_smul_mem A B
          (by rw [ht]; exact Submodule.mem_sup_right (Submodule.subset_span hx))) L h1
        (h2.trans ht.le)
      exact ⟨t', h3.trans hc, h4⟩
    exact ⟨encard_between_le A B hn e key, key⟩

end GlobalTheory.Mass.LatticeGens
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeQuotientGensAndIntermediateCountStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_quotient_gens_and_intermediate_count : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (A B : Submodule (𝓞 K) V), A ≤ B → idxN B A ≠ 0 → (B.FG → ∃ t : Finset V, t.card ≤ Module.finrank K V ∧ B = A ⊔ Submodule.span (𝓞 K) (t : Set V)) ∧ ∀ (e : ℕ) (t : Finset V), t.card ≤ e → B = A ⊔ Submodule.span (𝓞 K) (t : Set V) → ({L | A ≤ L ∧ L ≤ B}.encard ≤ ((idxN B A ^ e : ℕ) : ℕ∞)) ∧ ∀ L, A ≤ L → L ≤ B → ∃ t' : Finset V, t'.card ≤ e ∧ L = A ⊔ Submodule.span (𝓞 K) (t' : Set V) := by
  first | exact @GlobalTheory.Mass.LatticeGens.gens_and_count | exact GlobalTheory.Mass.LatticeGens.gens_and_count | (intros; apply GlobalTheory.Mass.LatticeGens.gens_and_count <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassEqWeightedSumFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassEqWeightedSumFibres
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.OrbFib

section
variable {G γ : Type} [Group G] [MulAction G γ]

end

variable {G α β : Type} [Group G] [MulAction G α] [MulAction G β]

theorem _root_.GlobalTheory.Mass.OrbFib.key (π : α → β)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x) (x : α) (k : G) :
    ((ENat.card (MulAction.stabilizer G (k • π x)) : ℕ∞) : ℝ≥0∞) =
      (((MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard : ℕ∞) : ℝ≥0∞) *
        ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞) := by
  have hkx : π (k • x) = k • π x := hπ k x
  have e1 : MulAction.stabilizer (MulAction.stabilizer G (k • π x)) (k • x) ≃
      MulAction.stabilizer G (k • x) :=
    { toFun := fun h => ⟨(h.1 : G), h.2⟩
      invFun := fun g => ⟨⟨g.1, by
          rw [MulAction.mem_stabilizer_iff, ← hkx, ← hπ,
            MulAction.mem_stabilizer_iff.1 g.2]⟩, g.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e2 : MulAction.stabilizer G (k • x) ≃ MulAction.stabilizer G x := by
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    exact ((MulAction.stabilizer G x).equivMapOfInjective _
      (MulAut.conj k).injective).toEquiv.symm
  have e3 : MulAction.orbit (MulAction.stabilizer G (k • π x)) (k • x) =
      MulAction.orbit G x ∩ π ⁻¹' {k • π x} := by
    ext z
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨⟨(h : G) * k, ?_⟩, ?_⟩
      · show ((h : G) * k) • x = (h : G) • (k • x)
        exact mul_smul _ _ _
      · show π ((h : G) • (k • x)) = k • π x
        rw [hπ, hkx]
        exact h.2
    · rintro ⟨⟨g, rfl⟩, hz⟩
      have hz' : g • π x = k • π x := by rw [← hπ]; exact hz
      refine ⟨⟨g * k⁻¹, ?_⟩, ?_⟩
      · rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_smul, hz']
      · show (g * k⁻¹) • (k • x) = g • x
        rw [mul_smul, inv_smul_smul]
  have e4 : (MulAction.stabilizer G (k • π x) ⧸
      MulAction.stabilizer (MulAction.stabilizer G (k • π x)) (k • x)) ≃
      (MulAction.orbit G x ∩ π ⁻¹' {k • π x} : Set α) :=
    (MulAction.orbitEquivQuotientStabilizer _ (k • x)).symm.trans (Set.equivOfEq e3)
  have hcard : ENat.card (MulAction.stabilizer G (k • π x)) =
      (MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard *
        ENat.card (MulAction.stabilizer G x) := by
    rw [Set.encard, ← ENat.card_congr e4, ← ENat.card_congr (e1.trans e2), ← ENat.card_prod]
    exact ENat.card_congr Subgroup.groupEquivQuotientProdSubgroup
  rw [hcard]
  exact ENat.toENNReal_mul _ _

theorem _root_.GlobalTheory.Mass.OrbFib.mem_orbit_out (q : MulAction.orbitRel.Quotient G α) (x : α) :
    x ∈ MulAction.orbit G (Quotient.out q) ↔ (Quotient.mk (MulAction.orbitRel G α) x) = q := by
  constructor
  · intro h
    exact (Quotient.sound h).trans (Quotient.out_eq q)
  · intro h
    exact Quotient.exact (h.trans (Quotient.out_eq q).symm)

theorem _root_.GlobalTheory.Mass.OrbFib.encard_orbits (X : Set α) (hX : _root_.GlobalTheory.Mass.Stable G X)
    (S : Set α) :
    (((X ∩ S).encard : ℕ∞) : ℝ≥0∞) =
      ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
        (((MulAction.orbit G (Quotient.out q.1) ∩ S).encard : ℕ∞) : ℝ≥0∞) := by
  have hmem : ∀ (q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X}) (a : α),
      a ∈ MulAction.orbit G (Quotient.out q.1) → a ∈ X := by
    rintro q a ⟨g, rfl⟩
    exact hX g _ q.2
  have h1 : ∀ T : Set α, ((T.encard : ℕ∞) : ℝ≥0∞) =
      ∑' a : α, T.indicator (fun _ => (1 : ℝ≥0∞)) a := by
    intro T
    rw [← ENNReal.tsum_set_one]
    exact tsum_subtype T (fun _ => (1 : ℝ≥0∞))
  simp_rw [h1]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  by_cases haS : a ∈ S
  · by_cases haX : a ∈ X
    · have hq0 : Quotient.out (Quotient.mk (MulAction.orbitRel G α) a) ∈ X := by
        obtain ⟨g, hg⟩ := Quotient.mk_out (s := MulAction.orbitRel G α) a
        rw [← hg]
        exact hX g a haX
      rw [Set.indicator_of_mem (show a ∈ X ∩ S from ⟨haX, haS⟩), tsum_eq_single
        (⟨Quotient.mk _ a, hq0⟩ : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X})]
      · rw [Set.indicator_of_mem]
        exact ⟨(_root_.GlobalTheory.Mass.OrbFib.mem_orbit_out _ a).2 rfl, haS⟩
      · intro q hq
        rw [Set.indicator_of_notMem]
        rintro ⟨h, -⟩
        exact hq (Subtype.ext ((_root_.GlobalTheory.Mass.OrbFib.mem_orbit_out _ a).1 h).symm)
    · rw [Set.indicator_of_notMem (fun h : a ∈ X ∩ S => haX h.1)]
      symm
      refine ENNReal.tsum_eq_zero.2 fun q => ?_
      rw [Set.indicator_of_notMem]
      rintro ⟨h, -⟩
      exact haX (hmem q a h)
  · rw [Set.indicator_of_notMem (fun h : a ∈ X ∩ S => haS h.2)]
    symm
    refine ENNReal.tsum_eq_zero.2 fun q => ?_
    rw [Set.indicator_of_notMem]
    rintro ⟨-, h⟩
    exact haS h

end GlobalTheory.Mass.OrbFib

namespace GlobalTheory.Mass

variable {G α β : Type} [Group G] [MulAction G α] [MulAction G β] in
private theorem tsum_inv_card_stabilizer_mul_encard_orbit_fibre (π : α → β)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x) (Y : Set β) (hY : _root_.GlobalTheory.Mass.Stable G Y)
    (hfin : ∀ y ∈ Y, Finite (MulAction.stabilizer G y)) (x : α) (hx : π x ∈ Y) :
    ∑' r : {r : MulAction.orbitRel.Quotient G β // Quotient.out r ∈ Y},
      ((ENat.card (MulAction.stabilizer G (Quotient.out r.1)) : ℕ∞) : ℝ≥0∞)⁻¹ *
        (((MulAction.orbit G x ∩ π ⁻¹' {Quotient.out r.1}).encard : ℕ∞) : ℝ≥0∞) =
      ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞)⁻¹ := by
  obtain ⟨k, hk⟩ := Quotient.mk_out (s := MulAction.orbitRel G β) (π x)
  have hr0 : Quotient.out (Quotient.mk (MulAction.orbitRel G β) (π x)) ∈ Y := by
    rw [← hk]
    exact hY k _ hx
  rw [tsum_eq_single ⟨_, hr0⟩]
  · dsimp only
    rw [← hk, _root_.GlobalTheory.Mass.OrbFib.key π hπ x k]
    have hyY : k • π x ∈ Y := hY k _ hx
    have hfy := hfin _ hyY
    have hyT : ((ENat.card (MulAction.stabilizer G (k • π x)) : ℕ∞) : ℝ≥0∞) ≠ ⊤ := by
      haveI := hfy
      rw [ENat.card_eq_coe_natCard]
      simp
    rw [_root_.GlobalTheory.Mass.OrbFib.key π hπ x k] at hyT
    have hc0 : ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞) ≠ 0 := by
      have : ENat.card (MulAction.stabilizer G x) ≠ 0 := by
        rw [Ne, ENat.card_eq_zero_iff_empty, not_isEmpty_iff]
        exact ⟨1⟩
      simpa using this
    have he0 : (((MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard : ℕ∞) : ℝ≥0∞) ≠ 0 := by
      have hmem : k • x ∈ MulAction.orbit G x ∩ π ⁻¹' {k • π x} :=
        ⟨⟨k, rfl⟩, by simp [hπ]⟩
      have : (MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard ≠ 0 :=
        Set.encard_ne_zero.2 ⟨_, hmem⟩
      simpa using this
    have heT : (((MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard : ℕ∞) : ℝ≥0∞) ≠ ⊤ := by
      intro h
      apply hyT
      rw [h, ENNReal.top_mul hc0]
    rw [ENNReal.mul_inv (Or.inl he0) (Or.inl heT), mul_right_comm,
      ENNReal.inv_mul_cancel he0 heT, one_mul]
  · intro r hr
    have hempty : MulAction.orbit G x ∩ π ⁻¹' {Quotient.out r.1} = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      rintro ⟨g, rfl⟩ hz
      apply hr
      apply Subtype.ext
      rw [hπ] at hz
      have hmem : π x ∈ MulAction.orbit G (Quotient.out r.1) :=
        ⟨g⁻¹, by rw [← hz]; exact inv_smul_smul g (π x)⟩
      exact ((_root_.GlobalTheory.Mass.OrbFib.mem_orbit_out r.1 (π x)).1 hmem).symm
    rw [hempty]
    simp

theorem _root_.GlobalTheory.Mass.orbMass_eq_orbSum_fibre : ∀ (G α β : Type) [Group G] [MulAction G α]
    [MulAction G β] (X : Set α) (Y : Set β) (π : α → β), (∀ (g : G) x, π (g • x) = g • π x) →
    _root_.GlobalTheory.Mass.Stable G X → _root_.GlobalTheory.Mass.Stable G Y → Set.MapsTo π X Y →
    (∀ y ∈ Y, Finite (MulAction.stabilizer G y)) →
    _root_.GlobalTheory.Mass.orbMass G X =
      _root_.GlobalTheory.Mass.orbSum G Y (fun y => (((X ∩ π ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞)) := by
  intro G α β _ _ _ X Y π hπ hX hY hmaps hfin
  unfold _root_.GlobalTheory.Mass.orbMass _root_.GlobalTheory.Mass.orbSum
  dsimp only
  have step : ∀ r : {r : MulAction.orbitRel.Quotient G β // Quotient.out r ∈ Y},
      ((ENat.card (MulAction.stabilizer G (Quotient.out r.1)) : ℕ∞) : ℝ≥0∞)⁻¹ *
        (((X ∩ π ⁻¹' {Quotient.out r.1}).encard : ℕ∞) : ℝ≥0∞) =
      ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
        ((ENat.card (MulAction.stabilizer G (Quotient.out r.1)) : ℕ∞) : ℝ≥0∞)⁻¹ *
          (((MulAction.orbit G (Quotient.out q.1) ∩ π ⁻¹' {Quotient.out r.1}).encard : ℕ∞) :
            ℝ≥0∞) := by
    intro r
    rw [_root_.GlobalTheory.Mass.OrbFib.encard_orbits X hX, ENNReal.tsum_mul_left]
  rw [tsum_congr step, ENNReal.tsum_comm]
  refine tsum_congr fun q => ?_
  rw [mul_one]
  exact (tsum_inv_card_stabilizer_mul_encard_orbit_fibre π hπ Y hY hfin _ (hmaps q.2)).symm

end GlobalTheory.Mass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassEqWeightedSumFibresStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres : ∀ (G α β : Type) [Group G] [MulAction G α] [MulAction G β] (X : Set α) (Y : Set β) (π : α → β), (∀ (g : G) x, π (g • x) = g • π x) → Stable G X → Stable G Y → Set.MapsTo π X Y → (∀ y ∈ Y, Finite (MulAction.stabilizer G y)) → orbMass G X = orbSum G Y (fun y => (((X ∩ π ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞)) := by
  first | exact @GlobalTheory.Mass.orbMass_eq_orbSum_fibre | exact GlobalTheory.Mass.orbMass_eq_orbSum_fibre | (intros; apply GlobalTheory.Mass.orbMass_eq_orbSum_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMassEqSumFrameClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMassEqSumFrameClasses
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem mass_eq_sumCls : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ h ∈ S.St, ∀ Λ, S.IsTerm d Λ → P Λ → P (h • Λ)) → S.mass d P = S.sumCls fun C => S.nT d C P := by
  intro F _ _ _ _ _ E _ _ _ L r k S d P hP
  have hK : S.K0 ≤ S.St := inf_le_left.trans inf_le_left
  have key := mass_orbits_eq_tsum_fiber S.St S.K0 (fun Λ => S.IsTerm d Λ ∧ P Λ) (S.Fr d) hK
    (by
      rintro h hh Λ ⟨ht, hp⟩
      obtain ⟨ht', -, -, -, hFr, -⟩ := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d Λ ht h hh
      have hlat := (TermBasic.term_basic L r k S d Λ ht).1.1
      exact ⟨⟨ht', hP h hh Λ ht hp⟩, hFr, ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 Λ hlat).2.2 h hh⟩)
    (by
      rintro Λ ⟨ht, -⟩
      have tb := TermBasic.term_basic L r k S d Λ ht
      have hA := (GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 Λ tb.1.1
      have hC := (GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).2 (S.Fr d Λ) tb.2.2.2.2.2.2.1.1
      exact ⟨hA.1, hA.2.1, hC.1, hC.2.1⟩)
  beta_reduce at key
  unfold Frames.mass Frames.mu
  refine Eq.trans ?_ (key.trans ?_)
  · exact tsum_congr fun o => by split_ifs <;> rfl
  unfold Frames.sumCls Frames.nT Frames.wC
  refine tsum_congr fun c => ?_
  by_cases hc : S.IsIntCls c.out
  · rw [if_pos hc]
    have hs : {x | (S.IsTerm d x ∧ P x) ∧ S.Fr d x = c.out}
        = {Λ | S.IsTerm d Λ ∧ P Λ ∧ S.Fr d Λ = c.out} := by
      ext Λ
      simp only [Set.mem_ofPred_eq, and_assoc]
    rw [hs]
  · rw [if_neg hc]
    have hs : {x | (S.IsTerm d x ∧ P x) ∧ S.Fr d x = c.out} = (∅ : Set (Submodule L.O S.V)) := by
      ext Λ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨ht, -⟩, hF⟩
      exact hc (hF ▸ (TermBasic.term_basic L r k S d Λ ht).2.2.2.2.2.2.1)
    rw [hs, Set.encard_empty]
    simp

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMassEqSumFrameClassesStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianMass_eq_sum_frameClasses : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ h ∈ S.St, ∀ Λ, S.IsTerm d Λ → P Λ → P (h • Λ)) → S.mass d P = S.sumCls fun C => S.nT d C P := by
  first | exact @GlobalTheory.HL.mass_eq_sumCls | exact GlobalTheory.HL.mass_eq_sumCls | (intros; apply GlobalTheory.HL.mass_eq_sumCls <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousMultilinearMapOfInnerProd
open Formalism.MainNotions.S NumberField
open scoped InnerProductSpace

namespace GlobalTheory

theorem eq_of_inner_eq_on_dense_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {s : Set E} (hs : Dense (Submodule.span ℂ s : Set E)) {a b : E}
    (h : ∀ y ∈ s, ⟪y, a⟫_ℂ = ⟪y, b⟫_ℂ) : a = b := by
  have h1 : ∀ y ∈ Submodule.span ℂ s, ⟪y, a⟫_ℂ = ⟪y, b⟫_ℂ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h y hy
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, inner_add_left, hy, hz]
    | smul c y _ hy => rw [inner_smul_left, inner_smul_left, hy]
  have h2 : (fun y : E => ⟪y, a⟫_ℂ) = fun y => ⟪y, b⟫_ℂ :=
    Continuous.ext_on hs (by fun_prop) (by fun_prop) h1
  exact ext_inner_left ℂ fun y => congrFun h2 y

theorem exists_continuousMultilinearMap_of_inner_prod {ι : Type*} [Fintype ι] {H : ι → Type*}
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (t : (∀ v, H v) → E)
    (hin : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range t) : Set E)) :
    ∃ m : ContinuousMultilinearMap ℂ H E, (∀ x, m x = t x) ∧ ∀ x, ‖t x‖ = ∏ v, ‖x v‖ := by
  have hn : ∀ x, ‖t x‖ = ∏ v, ‖x v‖ := by
    intro x
    have h := hin x x
    simp only [inner_self_eq_norm_sq_to_K] at h
    have h' : ‖t x‖ ^ 2 = (∏ v, ‖x v‖) ^ 2 := by
      rw [← Finset.prod_pow]
      exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (Finset.prod_nonneg fun v _ => norm_nonneg _)
      two_ne_zero).1 h'
  have hu : ∀ [DecidableEq ι] (y x : ∀ v, H v) (i : ι) (a : H i),
      ⟪t y, t (Function.update x i a)⟫_ℂ =
        ⟪y i, a⟫_ℂ * ∏ j ∈ Finset.univ.erase i, ⟪y j, x j⟫_ℂ := by
    intro _ y x i a
    rw [hin, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  let m : MultilinearMap (RingHom.id ℂ) H E :=
    { toFun := t
      map_update_add' := by
        intro _ x i a b
        refine eq_of_inner_eq_on_dense_span hd ?_
        rintro _ ⟨y, rfl⟩
        rw [inner_add_right, hu, hu, hu, inner_add_right, add_mul]
      map_update_smul' := by
        intro _ x i c a
        refine eq_of_inner_eq_on_dense_span hd ?_
        rintro _ ⟨y, rfl⟩
        rw [RingHom.id_apply, inner_smul_right, hu, hu, inner_smul_right, mul_assoc] }
  refine ⟨m.mkContinuous 1 fun x => ?_, fun x => rfl, hn⟩
  rw [one_mul]
  exact (hn x).le

theorem rowsAut_tens_continuousMultilinear :
    ∀ B : RowsAut, ∃ m : ContinuousMultilinearMap ℂ B.H B.Hs,
      (∀ x, m x = B.tens x) ∧ ∀ x, ‖B.tens x‖ = ∏ v, ‖x v‖ := fun B =>
  exists_continuousMultilinearMap_of_inner_prod B.tens B.tens_spec.1 B.tens_spec.2.2

end GlobalTheory
end
