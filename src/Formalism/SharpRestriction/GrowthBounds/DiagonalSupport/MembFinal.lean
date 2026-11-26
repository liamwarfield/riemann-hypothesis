module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDegF
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembVB
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDd
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ThresholdGeOddPosition

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembershipOfThreeParts
section -- merged from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.DecIdentity
section -- merged from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SumMulSumProd
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

theorem ceil_le_of_geZ {x : WithTop ℤ} {t : ℝ} (h : geZ x t) : ((⌈t⌉ : ℤ) : WithTop ℤ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe k => exact WithTop.coe_le_coe.2 (Int.ceil_le.2 (h k rfl))

section Tr

variable {O : Type} [CommRing O] {J : ℕ} {n : ℕ}

theorem back_rename (j : ZMod J) (X : MvPolynomial ((ZMod J × ℤ) × Fin n) O)
    (hX : X ∈ supported O {v : (ZMod J × ℤ) × Fin n | v.1.1 = j}) :
    rename (fun v : ℤ × Fin n => ((j, v.1), v.2)) (rename (fun v : (ZMod J × ℤ) × Fin n => (v.1.2, v.2)) X) = X := by
  rw [MvPolynomial.supported_eq_range_rename] at hX
  obtain ⟨Y, hY⟩ := hX
  rw [← hY]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.rename_rename]
  refine congrArg (fun f => (rename (R := O) f) Y) ?_
  funext v
  obtain ⟨⟨⟨a, b⟩, c⟩, hv⟩ := v
  simp only [Set.mem_setOf_eq] at hv
  subst hv
  rfl

private theorem twistSub_rename_eq {R : Type} [CommRing R] {ι κ : Type} {n : ℕ} (LL : Letters ι) (LK : Letters κ)
    (S : Set ι) (T : Set κ) (g : κ → ι) (hvec : ∀ y, LL.vec (g y) = LK.vec y) (hS : ∀ y, g y ∈ S ↔ y ∈ T)
    (k : Fin n) (X' : MvPolynomial (κ × Fin n) R) :
    twistSub LL S k (rename (R := R) (fun v : κ × Fin n => (g v.1, v.2)) X') =
      rename (R := GLLaurent R n) (fun v : κ × Fin n => (g v.1, v.2)) (twistSub LK T k X') := by
  have h : (twistSub LL S k).comp (rename (R := R) (fun v : κ × Fin n => (g v.1, v.2))).toRingHom =
      (rename (R := GLLaurent R n) (fun v : κ × Fin n => (g v.1, v.2))).toRingHom.comp (twistSub LK T k) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [twistSub]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, twistSub,
        eval₂Hom_X', hS, hvec]
      split_ifs <;> simp [map_sum]
  exact congrArg (fun φ => φ X') h

private theorem sDegs_rename_eq_of_injective {R : Type} [CommRing R] {ι κ : Type} {n : ℕ} (LL : Letters ι) (LK : Letters κ)
    (S : Set ι) (T : Set κ) (g : κ → ι) (hg : Function.Injective g) (hvec : ∀ y, LL.vec (g y) = LK.vec y)
    (hS : ∀ y, g y ∈ S ↔ y ∈ T) (k : Fin n) (X' : MvPolynomial (κ × Fin n) R) :
    sDegs LL S k (rename (fun v : κ × Fin n => (g v.1, v.2)) X') = sDegs LK T k X' := by
  have hinj : Function.Injective (fun v : κ × Fin n => (g v.1, v.2)) := fun a b h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (hg h.1) h.2
  unfold sDegs
  rw [twistSub_rename_eq LL LK S T g hvec hS k X', MvPolynomial.support_rename_of_injective hinj,
    Finset.image_biUnion]
  simp only [MvPolynomial.coeff_rename_mapDomain _ hinj]

theorem seg_val [NeZero n] (j : ZMod J) (X' : MvPolynomial (ℤ × Fin n) O) (P : ℤ → Prop) :
    valS (LSeg J) {i | i.1 = j ∧ P i.2} (rename (fun v : ℤ × Fin n => ((j, v.1), v.2)) X') = valS LZ {y | P y} X' ∧
    lam1S (LSeg J) {i | i.1 = j ∧ P i.2} (rename (fun v : ℤ × Fin n => ((j, v.1), v.2)) X') = lam1S LZ {y | P y} X' := by
  have h1 : ∀ k, sDegs (LSeg J) {i | i.1 = j ∧ P i.2} k (rename (fun v : ℤ × Fin n => ((j, v.1), v.2)) X') =
      sDegs LZ {y | P y} k X' := fun k =>
    sDegs_rename_eq_of_injective (LSeg J) LZ _ _ (fun y : ℤ => (j, y)) (fun a b h => (Prod.mk.inj h).2) (fun y => rfl)
      (fun y => by simp) k X'
  exact ⟨by simp only [valS, h1], by simp only [lam1S, h1]⟩

end Tr

section XGs

variable {O : Type} [CommRing O] [IsDomain O] {ι G : Type} (π : ι → G) {n : ℕ} [NeZero n] (LL : Letters ι)
  (Cv Cl : G → Set (Set ι × ℤ)) (F : MvPolynomial (ι × Fin n) O)

theorem XG_supported (j : G) (x : MvPolynomial (ι × Fin n) O) (hx : x ∈ XG π LL Cv Cl F j) :
    x ∈ supported O {v : ι × Fin n | π v.1 = j} := by
  rw [MvPolynomial.mem_supported]
  intro v hv
  obtain ⟨d, hd, hvd⟩ := (MvPolynomial.mem_vars_iff_mem_support v).mp (Finset.mem_coe.mp hv)
  obtain ⟨mo', -, rfl⟩ := Finset.mem_image.mp (hx.1 d hd)
  rw [Finsupp.mem_support_iff] at hvd
  show π v.1 = j
  by_contra hne
  exact hvd (by simp [partOf, Finsupp.filter_apply, hne])

theorem XG_part (j : G) (x : MvPolynomial (ι × Fin n) O) (hx : x ∈ XG π LL Cv Cl F j) (mo : ι × Fin n →₀ ℕ)
    (hmo : mo ∈ x.support) : ∃ mo' ∈ F.support, partOf π j mo' = mo :=
  Finset.mem_image.1 (hx.1 mo hmo)

theorem partOf_apply_pos (j : G) (mo : ι × Fin n →₀ ℕ) (v : ι × Fin n) (hv : π v.1 = j) : partOf π j mo v = mo v := by
  unfold partOf
  exact Finsupp.filter_apply_pos _ _ hv

end XGs

theorem support_homComp {R : Type} [CommRing R] {ι : Type} {n : ℕ} (δ : ι → ℕ) (F : MvPolynomial (ι × Fin n) R)
    (mo : ι × Fin n →₀ ℕ) (h : mo ∈ (homComp δ F).support) : mo ∈ F.support ∧ ∀ i, multideg mo i = δ i := by
  have hc := MvPolynomial.mem_support_iff.mp h
  simp only [homComp, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_filter] at hc
  split_ifs at hc with hm
  · exact hm
  · exact absurd rfl hc

section Ph

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] (K : ℕ) {J : ℕ}

theorem PhiPl_seg (j : ZMod J) (A : MvPolynomial (ℤ × Fin r) O) :
    PhiPl Fr p O K J (rename (fun v : ℤ × Fin r => ((j, v.1), v.2)) A) = phSeg O K p Fr (segZ j) (plEmb O r K A) := by
  simp only [PhiPl, phSeg, plEmb, MvPolynomial.aeval_rename, Function.comp_def]

theorem PhiNo_seg (j : ZMod J) (B : MvPolynomial (ℤ × Fin K) O) :
    PhiNo Fr p O K J (rename (fun v : ℤ × Fin K => ((j, v.1), v.2)) B) = phSeg O K p Fr (segZ j) (nmEmb O r K B) := by
  simp only [PhiNo, phSeg, nmEmb, MvPolynomial.aeval_rename, Function.comp_def]

end Ph

theorem segZ_cast {J : ℕ} [NeZero J] (t : ℕ) (ht : t < J) : segZ (((t : ℤ) : ZMod J)) = (t : ℤ) := by
  simp only [segZ, Int.cast_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ht]

theorem cast_segZ {J : ℕ} [NeZero J] (j : ZMod J) : ((segZ j : ℤ) : ZMod J) = j := by
  simp only [segZ, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem prod_range_zmod {M : Type} [CommMonoid M] {J : ℕ} [NeZero J] (g : ℤ → M) :
    ∏ t ∈ Finset.range J, g (t : ℤ) = ∏ j : ZMod J, g (segZ j) := by
  symm
  refine Finset.prod_nbij' (fun j => j.val) (fun t => (t : ZMod J)) ?_ ?_ ?_ ?_ ?_
  · intro j _
    simp [ZMod.val_lt]
  · intro t _
    simp
  · intro j _
    simp [ZMod.natCast_zmod_val]
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_range] at ht
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt ht]
  · intro j _
    rfl

theorem sum_mul_sum_prod {M : Type} [CommRing M] {G : Type} [Fintype G] {N1 N2 : ℕ} (a : Fin N1 → G → M)
    (b : Fin N2 → G → M) :
    (∑ i, ∏ j, a i j) * (∑ i, ∏ j, b i j) =
      ∑ q : Fin (N1 * N2), ∏ j, (a (finProdFinEquiv.symm q).1 j * b (finProdFinEquiv.symm q).2 j) := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv finProdFinEquiv _ _ (fun p => ?_)
  simp [Finset.prod_mul_distrib]

section SegDec

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {J : ℕ} [NeZero J] {n : ℕ} [NeZero n]

theorem seg_dec (hA : ATL) (hS : ValSlice) (F : MvPolynomial ((ZMod J × ℤ) × Fin n) O)
    (Cv Cl : ZMod J → Set ((ℤ → Prop) × ℤ))
    (hv : ∀ j, ∀ q ∈ Cv j, ((q.2 : ℤ) : WithTop ℤ) ≤ valS (LSeg J) {i | i.1 = j ∧ q.1 i.2} F)
    (hl : ∀ j, ∀ q ∈ Cl j, lam1S (LSeg J) {i | i.1 = j ∧ q.1 i.2} F ≤ ((q.2 : ℤ) : WithBot ℤ)) :
    ∃ (N : ℕ) (A' : Fin N → ZMod J → MvPolynomial (ℤ × Fin n) O),
      (∀ i j, (∀ mo ∈ (A' i j).support, ∃ mo' ∈ F.support, ∀ x c, mo (x, c) = mo' ((j, x), c)) ∧
        (∀ q ∈ Cv j, ((q.2 : ℤ) : WithTop ℤ) ≤ valS LZ {y | q.1 y} (A' i j)) ∧
        (∀ q ∈ Cl j, lam1S LZ {y | q.1 y} (A' i j) ≤ ((q.2 : ℤ) : WithBot ℤ))) ∧
      F = ∑ i, ∏ j, rename (fun v : ℤ × Fin n => ((j, v.1), v.2)) (A' i j) := by
  classical
  let Cv' : ZMod J → Set (Set (ZMod J × ℤ) × ℤ) := fun j =>
    (fun q : (ℤ → Prop) × ℤ => ({i : ZMod J × ℤ | i.1 = j ∧ q.1 i.2}, q.2)) '' Cv j
  let Cl' : ZMod J → Set (Set (ZMod J × ℤ) × ℤ) := fun j =>
    (fun q : (ℤ → Prop) × ℤ => ({i : ZMod J × ℤ | i.1 = j ∧ q.1 i.2}, q.2)) '' Cl j
  obtain ⟨N, A, hA', hF⟩ := decGen (O := O) (Prod.fst : ZMod J × ℤ → ZMod J) (LSeg J) Cv' Cl' F hA hS
    (by
      rintro j q ⟨q0, -, rfl⟩ i hi
      exact hi.1)
    (by
      rintro j q ⟨q0, -, rfl⟩ i hi
      exact hi.1)
    (by
      rintro j q ⟨q0, hq0, rfl⟩
      exact hv j q0 hq0)
    (by
      rintro j q ⟨q0, hq0, rfl⟩
      exact hl j q0 hq0)
  have hback : ∀ i j, rename (fun v : ℤ × Fin n => ((j, v.1), v.2))
      (rename (fun v : (ZMod J × ℤ) × Fin n => (v.1.2, v.2)) (A i j)) = A i j := fun i j =>
    back_rename j (A i j) (XG_supported Prod.fst (LSeg J) Cv' Cl' F j (A i j) (hA' i j))
  refine ⟨N, fun i j => rename (fun v : (ZMod J × ℤ) × Fin n => (v.1.2, v.2)) (A i j), fun i j => ?_, ?_⟩
  · have hmem : A i j ∈ XG Prod.fst (LSeg J) Cv' Cl' F j := hA' i j
    refine ⟨?_, ?_, ?_⟩
    · intro mo hmo
      have hinj : Function.Injective (fun v : ℤ × Fin n => ((j, v.1), v.2)) := fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1.2 h.2
      have h2 : Finsupp.mapDomain (fun v : ℤ × Fin n => ((j, v.1), v.2)) mo ∈ (A i j).support := by
        rw [← hback i j, MvPolynomial.support_rename_of_injective hinj]
        exact Finset.mem_image_of_mem _ hmo
      obtain ⟨mo', hmo', he⟩ := XG_part Prod.fst (LSeg J) Cv' Cl' F j (A i j) hmem _ h2
      refine ⟨mo', hmo', fun x c => ?_⟩
      have h4 : partOf Prod.fst j mo' ((j, x), c) =
          Finsupp.mapDomain (fun v : ℤ × Fin n => ((j, v.1), v.2)) mo ((j, x), c) := by
        rw [he]
      rw [partOf_apply_pos Prod.fst j mo' ((j, x), c) rfl,
        Finsupp.mapDomain_apply_of_injective hinj mo (x, c)] at h4
      exact h4.symm
    · intro q hq
      have h3 := hmem.2.1 _ ⟨q, hq, rfl⟩
      dsimp only at h3
      rw [← hback i j, (seg_val j _ q.1).1] at h3
      exact h3
    · intro q hq
      have h3 := hmem.2.2 _ ⟨q, hq, rfl⟩
      dsimp only at h3
      rw [← hback i j, (seg_val j _ q.1).2] at h3
      exact h3
  · conv_lhs => rw [hF]
    refine Finset.sum_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    exact (hback i j).symm

end SegDec

end Formalism.MainNotions.Proposition5Numerics
end
end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

section At

variable (p : ℕ) {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
  {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (dNo : TL J Dt.nL r → ℕ)
  (ka : ZMod J → ℕ → Fin K → ℤ)
  (No : MvPolynomial (TL J Dt.nL r × Fin K) O) (Go : MvPolynomial (ML J Dt.nL r × Fin r) O)

theorem plane_dec (hA : ATL) (hS : ValSlice) (hC : ValComp) (hVB : ValBd p O Fr deg Y N₁ G' cP Dt ka No Go)
    (hSp : SuppOK p O Fr Dt dNo No Go) (δ : ZMod J × ℤ → ℕ) :
    ∃ (N : ℕ) (A' : Fin N → ZMod J → MvPolynomial (ℤ × Fin r) O),
      (∀ i j, PlOK p O Fr deg Y N₁ G' cP Dt ka δ j (A' i j)) ∧
      homComp δ (xiPl Fr O Dt.nL Go) = ∑ i, ∏ j, rename (fun v : ℤ × Fin r => ((j, v.1), v.2)) (A' i j) := by
  obtain ⟨hV1, hV2, -⟩ := hVB
  obtain ⟨hSp1, -⟩ := hSp
  let Cv : ZMod J → Set ((ℤ → Prop) × ℤ) := fun j =>
    {q | ∃ u < Dt.nL j + r, q = ((fun y => y < pU p O Fr Dt j u), ⌈tauU p O Fr deg Y N₁ G' cP Dt ka j u⌉)} ∪
    {q | ∃ u < Dt.nL j, q = ((fun y => y ≤ pU p O Fr Dt j u), ⌈tauU p O Fr deg Y N₁ G' cP Dt ka j (u + 1)⌉)}
  have hCv : ∀ j, ∀ q ∈ Cv j, ((q.2 : ℤ) : WithTop ℤ) ≤
      valS (LSeg J) {i | i.1 = j ∧ q.1 i.2} (homComp δ (xiPl Fr O Dt.nL Go)) := by
    intro j q hq
    rcases hq with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact le_trans (ceil_le_of_geZ (hV1 j u hu))
        (hC O (ZMod J × ℤ) r (LSeg J) (SLt j (pU p O Fr Dt j u)) (xiPl Fr O Dt.nL Go) δ).1
    · exact le_trans (ceil_le_of_geZ (hV2 j u hu))
        (hC O (ZMod J × ℤ) r (LSeg J) (SLe j (pU p O Fr Dt j u)) (xiPl Fr O Dt.nL Go) δ).1
  obtain ⟨N, A', hA', hF⟩ := seg_dec hA hS (homComp δ (xiPl Fr O Dt.nL Go)) Cv (fun _ => ∅) hCv
    (fun j q hq => by simp at hq)
  refine ⟨N, A', fun i j => ?_, hF⟩
  obtain ⟨hsup, hv, -⟩ := hA' i j
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [MvPolynomial.mem_supported]
    intro v hv'
    obtain ⟨mo, hmo, hvmo⟩ := (MvPolynomial.mem_vars_iff_mem_support v).mp (Finset.mem_coe.mp hv')
    obtain ⟨mo', hmo', he⟩ := hsup mo hmo
    have hF' := (support_homComp δ _ mo' hmo').1
    have hne : mo' ((j, v.1), v.2) ≠ 0 := by
      rw [← he]
      exact Finsupp.mem_support_iff.mp hvmo
    exact hSp1 mo' hF' ((j, v.1), v.2) (Finsupp.mem_support_iff.mpr hne)
  · intro mo hmo x
    obtain ⟨mo', hmo', he⟩ := hsup mo hmo
    rw [← (support_homComp δ _ mo' hmo').2 (j, x)]
    simp only [multideg, he]
  · intro u hu
    exact hv ((fun y => y < pU p O Fr Dt j u), ⌈tauU p O Fr deg Y N₁ G' cP Dt ka j u⌉)
      (Or.inl ⟨u, hu, rfl⟩)
  · intro u hu
    exact hv ((fun y => y ≤ pU p O Fr Dt j u), ⌈tauU p O Fr deg Y N₁ G' cP Dt ka j (u + 1)⌉)
      (Or.inr ⟨u, hu, rfl⟩)

theorem normal_dec (hA : ATL) (hS : ValSlice) (hVB : ValBd p O Fr deg Y N₁ G' cP Dt ka No Go)
    (hSp : SuppOK p O Fr Dt dNo No Go) :
    ∃ (N : ℕ) (B' : Fin N → ZMod J → MvPolynomial (ℤ × Fin K) O),
      (∀ i j, NoOK p O Fr cP Dt dNo ka j (B' i j)) ∧
      xiNo Fr O K Dt.nL No = ∑ i, ∏ j, rename (fun v : ℤ × Fin K => ((j, v.1), v.2)) (B' i j) := by
  obtain ⟨-, -, hV3⟩ := hVB
  obtain ⟨-, hSp2⟩ := hSp
  let Cl : ZMod J → Set ((ℤ → Prop) × ℤ) := fun j =>
    {q | ∃ u < Dt.nL j + r, q = ((fun y => y < pU p O Fr Dt j u), ka j u 0 + 4 * (cP : ℤ))} ∪
    {q | ∃ u < Dt.nL j + r, q = ((fun y => y ≤ pU p O Fr Dt j u), ka j (u + 1) 0 + 4 * (cP : ℤ))}
  have hCl : ∀ j, ∀ q ∈ Cl j,
      lam1S (LSeg J) {i | i.1 = j ∧ q.1 i.2} (xiNo Fr O K Dt.nL No) ≤ ((q.2 : ℤ) : WithBot ℤ) := by
    intro j q hq
    rcases hq with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact (hV3 j u hu).1
    · exact (hV3 j u hu).2
  obtain ⟨N, B', hB', hF⟩ := seg_dec hA hS (xiNo Fr O K Dt.nL No) (fun _ => ∅) Cl
    (fun j q hq => by simp at hq) hCl
  refine ⟨N, B', fun i j => ?_, hF⟩
  obtain ⟨hsup, -, hl⟩ := hB' i j
  refine ⟨?_, ?_, fun u hu => ⟨?_, ?_⟩⟩
  · rw [MvPolynomial.mem_supported]
    intro v hv'
    obtain ⟨mo, hmo, hvmo⟩ := (MvPolynomial.mem_vars_iff_mem_support v).mp (Finset.mem_coe.mp hv')
    obtain ⟨mo', hmo', he⟩ := hsup mo hmo
    have hne : mo' ((j, v.1), v.2) ≠ 0 := by
      rw [← he]
      exact Finsupp.mem_support_iff.mp hvmo
    exact (hSp2 mo' hmo').1 ((j, v.1), v.2) (Finsupp.mem_support_iff.mpr hne)
  · intro mo hmo x
    obtain ⟨mo', hmo', he⟩ := hsup mo hmo
    rw [← (hSp2 mo' hmo').2 (j, x)]
    simp only [multideg, he]
  · exact hl ((fun y => y < pU p O Fr Dt j u), ka j u 0 + 4 * (cP : ℤ)) (Or.inl ⟨u, hu, rfl⟩)
  · exact hl ((fun y => y ≤ pU p O Fr Dt j u), ka j (u + 1) 0 + 4 * (cP : ℤ)) (Or.inr ⟨u, hu, rfl⟩)

theorem dec_identity {N1 N2 : ℕ} (A' : Fin N1 → ZMod J → MvPolynomial (ℤ × Fin r) O)
    (B' : Fin N2 → ZMod J → MvPolynomial (ℤ × Fin K) O) :
    ∑ q : Fin (N1 * N2), ∏ t ∈ Finset.range J, phSeg O K p Fr (t : ℤ)
        (plEmb O r K (A' (finProdFinEquiv.symm q).1 (((t : ℤ)) : ZMod J)) *
          nmEmb O r K (B' (finProdFinEquiv.symm q).2 (((t : ℤ)) : ZMod J))) =
      PhiPl Fr p O K J (∑ i, ∏ j, rename (fun v : ℤ × Fin r => ((j, v.1), v.2)) (A' i j)) *
        PhiNo Fr p O K J (∑ i, ∏ j, rename (fun v : ℤ × Fin K => ((j, v.1), v.2)) (B' i j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_prod, PhiPl_seg, PhiNo_seg]
  rw [sum_mul_sum_prod]
  refine Finset.sum_congr rfl fun q _ => ?_
  refine (prod_range_zmod (fun t : ℤ => phSeg O K p Fr t
    (plEmb O r K (A' (finProdFinEquiv.symm q).1 (t : ZMod J)) *
      nmEmb O r K (B' (finProdFinEquiv.symm q).2 (t : ZMod J))))).trans ?_
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [cast_segZ, map_mul]

end At

theorem restDecG_of (hA : ATL) (hS : ValSlice) (hC : ValComp) (hVB : RestValBdG) (hXX : RestXXG) (hDd : RestDdG) :
    RestDecG := by
  intro p _ n' r K _ _ _ O _ _ _ S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J _ Dt dPl dNo ka rho No Go hMH δ hocc
  obtain ⟨hvb, hsp⟩ := hVB p O S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH
  have hxx := hXX p O S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka hMH.1
  have hdd := hDd p O S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH δ hocc
  have hJ : J = Fr.J := hMH.1.1.1
  obtain ⟨N1, A', hA1, hA2⟩ := plane_dec p O Fr deg Y N₁ G' cP Dt dNo ka No Go hA hS hC hvb hsp δ
  obtain ⟨N2, B', hB1, hB2⟩ := normal_dec p O Fr deg Y N₁ G' cP Dt dNo ka No Go hA hS hvb hsp
  refine ⟨N1 * N2, fun jz x => ((δ ((jz : ZMod J), x) + dNoOf p O Fr Dt dNo ((jz : ZMod J), x) : ℕ) : ℝ),
    fun q jz => plEmb O r K (A' (finProdFinEquiv.symm q).1 (jz : ZMod J)) *
      nmEmb O r K (B' (finProdFinEquiv.symm q).2 (jz : ZMod J)),
    fun jz x => δ ((jz : ZMod J), x) + dNoOf p O Fr Dt dNo ((jz : ZMod J), x), ?_, ?_, ?_⟩
  · intro q j hj
    have h := hxx δ (((j : ℤ)) : ZMod J) _ _ (hA1 (finProdFinEquiv.symm q).1 _) (hB1 (finProdFinEquiv.symm q).2 _)
    rw [segZ_cast j (by rw [hJ]; exact hj)] at h
    exact h
  · intro j hj x hx hWL
    have hs := segZ_cast (J := J) j (by rw [hJ]; exact hj)
    have h := hdd (((j : ℤ)) : ZMod J) x (by rw [hs]; exact hx) (by rw [hs]; exact hWL)
    rw [hs] at h
    exact h
  · rw [hA2, hB2, ← hJ]
    exact dec_identity p O Fr A' B'

end Formalism.MainNotions.Proposition5Numerics
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ProjectionMemPartialSpan
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

namespace PartialSpanProjection

variable {O : Type} [CommRing O] {σ : Type}

theorem exists_retraction [IsDomain O] [IsPrincipalIdealRing O] (X : Submodule O (MvPolynomial σ O))
    (s : Finset (σ →₀ ℕ)) (hs : ∀ x ∈ X, x.support ⊆ s)
    (hsat : ∀ (c : O) (x : MvPolynomial σ O), c ≠ 0 → c • x ∈ X → x ∈ X) :
    ∃ q : MvPolynomial σ O →ₗ[O] MvPolynomial σ O, (∀ A, q A ∈ X) ∧ ∀ x ∈ X, q x = x := by
  let e : (s → O) →ₗ[O] MvPolynomial σ O := Fintype.linearCombination O (fun m : s => monomial m.1 (1 : O))
  let r : MvPolynomial σ O →ₗ[O] (s → O) := LinearMap.pi (fun m => lcoeff O m.1)
  have her : ∀ x : MvPolynomial σ O, x.support ⊆ s → e (r x) = x := by
    intro x hx
    simp only [e, r, Fintype.linearCombination_apply, LinearMap.pi_apply, lcoeff_apply]
    rw [Finset.sum_coe_sort s (fun m => AddMonoidAlgebra.coeff x m • monomial m (1 : O))]
    conv_rhs => rw [← support_sum_monomial_coeff x]
    symm
    refine (Finset.sum_subset hx ?_).trans ?_
    · intro m _ hm
      rw [notMem_support_iff.1 hm, monomial_zero]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_monomial, smul_eq_mul, mul_one]
  let X' : Submodule O (s → O) := X.comap e
  have htf : Module.IsTorsionFree O ((s → O) ⧸ X') := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro c m h
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      rw [Submodule.Quotient.mk_eq_zero]
      show e f ∈ X
      apply hsat c _ hc
      have h' : e (c • f) ∈ X := h
      rwa [map_smul] at h'
  obtain ⟨g, hg⟩ := X'.mkQ.exists_rightInverse_of_surjective (Submodule.range_mkQ X')
  let ρ : (s → O) →ₗ[O] (s → O) := LinearMap.id - g ∘ₗ X'.mkQ
  have hρ1 : ∀ f, ρ f ∈ X' := by
    intro f
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h := LinearMap.congr_fun hg (X'.mkQ f)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
    simp only [ρ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h, sub_self]
  have hρ2 : ∀ f ∈ X', ρ f = f := by
    intro f hf
    have h : X'.mkQ f = 0 := by rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hf
    simp only [ρ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h, map_zero, sub_zero]
  refine ⟨e ∘ₗ ρ ∘ₗ r, fun A => hρ1 _, fun x hx => ?_⟩
  have h1 := her x (hs x hx)
  have h2 : r x ∈ X' := by
    show e (r x) ∈ X
    rwa [h1]
  simp only [LinearMap.comp_apply]
  rw [hρ2 _ h2, h1]

theorem supp_of_mem {S : Set σ} {A : MvPolynomial σ O} (hA : A ∈ supported O S) {a : σ →₀ ℕ}
    (ha : a ∈ A.support) : ∀ v ∈ a.support, v ∈ S := by
  intro v hv
  exact (MvPolynomial.mem_supported.1 hA) ((MvPolynomial.mem_vars_iff_mem_support v).2 ⟨a, ha, hv⟩)

theorem monomial_mem {S : Set σ} {a : σ →₀ ℕ} (c : O) (ha : ∀ v ∈ a.support, v ∈ S) :
    monomial a c ∈ supported O S := by
  rw [MvPolynomial.mem_supported]
  intro v hv
  obtain ⟨m, hm, hvm⟩ := (MvPolynomial.mem_vars_iff_mem_support v).1 hv
  have hma : m = a := Finset.mem_singleton.1 (MvPolynomial.support_monomial_subset hm)
  subst hma
  exact ha v hvm

variable {ι : Type} (π : σ → ι)

def pj (j : ι) (q : MvPolynomial σ O →ₗ[O] MvPolynomial σ O) : MvPolynomial σ O →ₗ[O] MvPolynomial σ O :=
  (basisMonomials σ O).constr O
    (fun m => q (monomial (m.filter (fun v => π v = j)) 1) * monomial (m.filter (fun v => π v ≠ j)) 1)

theorem pj_monomial (j : ι) (q : MvPolynomial σ O →ₗ[O] MvPolynomial σ O) (m : σ →₀ ℕ) (c : O) :
    pj π j q (monomial m c) =
      c • (q (monomial (m.filter (fun v => π v = j)) 1) * monomial (m.filter (fun v => π v ≠ j)) 1) := by
  have e : monomial m c = c • (basisMonomials σ O m) := by
    rw [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, pj, Module.Basis.constr_basis]

theorem pj_mono_mul (j : ι) (q : MvPolynomial σ O →ₗ[O] MvPolynomial σ O) {a b : σ →₀ ℕ}
    (ha : ∀ v ∈ a.support, π v = j) (hb : ∀ v ∈ b.support, π v ≠ j) (ca cb : O) :
    pj π j q (monomial a ca * monomial b cb) = q (monomial a ca) * monomial b cb := by
  have h1 : (a + b).filter (fun v => π v = j) = a := by
    ext v
    simp only [Finsupp.filter_apply, Finsupp.add_apply]
    by_cases hv : π v = j
    · rw [if_pos hv]
      have : b v = 0 := by
        by_contra h
        exact hb v (Finsupp.mem_support_iff.2 h) hv
      rw [this, add_zero]
    · rw [if_neg hv]
      by_contra h
      exact hv (ha v (Finsupp.mem_support_iff.2 (Ne.symm h)))
  have h2 : (a + b).filter (fun v => π v ≠ j) = b := by
    ext v
    simp only [Finsupp.filter_apply, Finsupp.add_apply]
    by_cases hv : π v = j
    · rw [if_neg (not_not.2 hv)]
      have : b v = 0 := by
        by_contra h
        exact hb v (Finsupp.mem_support_iff.2 h) hv
      exact this.symm
    · rw [if_pos hv]
      have : a v = 0 := by
        by_contra h
        exact hv (ha v (Finsupp.mem_support_iff.2 h))
      rw [this, zero_add]
  rw [monomial_mul, pj_monomial, h1, h2]
  have e : monomial a ca = ca • monomial a (1 : O) := by rw [smul_monomial, smul_eq_mul, mul_one]
  have e' : monomial b cb = cb • monomial b (1 : O) := by rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, e', map_smul, smul_mul_smul_comm, mul_comm ca cb, mul_smul]

theorem pj_mul (j : ι) (q : MvPolynomial σ O →ₗ[O] MvPolynomial σ O) {A M : MvPolynomial σ O}
    (hA : A ∈ supported O {v | π v = j}) (hM : M ∈ supported O {v | π v ≠ j}) :
    pj π j q (A * M) = q A * M := by
  have eA := A.as_sum
  have eM := M.as_sum
  calc pj π j q (A * M)
      = pj π j q ((∑ a ∈ A.support, monomial a (AddMonoidAlgebra.coeff A a)) * ∑ b ∈ M.support, monomial b (AddMonoidAlgebra.coeff M b)) := by
        rw [← eA, ← eM]
    _ = ∑ a ∈ A.support, ∑ b ∈ M.support, pj π j q (monomial a (AddMonoidAlgebra.coeff A a) * monomial b (AddMonoidAlgebra.coeff M b)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Finset.sum_mul_sum, map_sum]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum]
    _ = ∑ a ∈ A.support, ∑ b ∈ M.support, q (monomial a (AddMonoidAlgebra.coeff A a)) * monomial b (AddMonoidAlgebra.coeff M b) :=
        Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb =>
          pj_mono_mul π j q (supp_of_mem hA ha) (supp_of_mem hM hb) _ _
    _ = q A * M := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← Finset.sum_mul_sum, ← map_sum, ← eA, ← eM]

theorem pj_fix (j : ι) (q : MvPolynomial σ O →ₗ[O] MvPolynomial σ O) (Xj : Submodule O (MvPolynomial σ O))
    (hX : ∀ x ∈ Xj, x ∈ supported O {v | π v = j}) (hq : ∀ x ∈ Xj, q x = x) {F : MvPolynomial σ O}
    (hF : F ∈ Submodule.span O {y | ∃ x ∈ Xj, ∃ M ∈ supported O {v | π v ≠ j}, y = x * M}) :
    pj π j q F = F := by
  induction hF using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, M, hM, rfl⟩ := hy
    rw [pj_mul π j q (hX x hx) hM, hq x hx]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _), hy, hz]
  | smul c y _ hy => rw [map_smul, hy]

def W (X : ι → Submodule O (MvPolynomial σ O)) (S : Finset ι) : Submodule O (MvPolynomial σ O) :=
  Submodule.span O {y | ∃ x : ι → MvPolynomial σ O, (∀ j, x j ∈ X j) ∧
    ∃ M ∈ supported O {v | π v ∉ S}, y = (∏ j ∈ S, x j) * M}

theorem projection_mem_partial_span (X : ι → Submodule O (MvPolynomial σ O)) (hX : ∀ j, ∀ x ∈ X j, x ∈ supported O {v | π v = j})
    (S : Finset ι) (j : ι) (hj : j ∉ S) (q : MvPolynomial σ O →ₗ[O] MvPolynomial σ O) (hq : ∀ A, q A ∈ X j)
    {G : MvPolynomial σ O} (hG : G ∈ W π X S) : pj π j q G ∈ W π X (insert j S) := by
  have hle : W π X S ≤ (W π X (insert j S)).comap (pj π j q) := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨x, hx, M, hM, rfl⟩
    show pj π j q ((∏ i ∈ S, x i) * M) ∈ W π X (insert j S)
    have hP : (∏ i ∈ S, x i) ∈ supported O {v | π v ≠ j} := by
      refine Subalgebra.prod_mem _ fun i hi => ?_
      refine supported_mono ?_ (hX i _ (hx i))
      intro v hv
      have hv' : π v = i := hv
      show π v ≠ j
      rw [hv']
      rintro rfl
      exact hj hi
    have hsum : (∏ i ∈ S, x i) * M = ∑ b ∈ M.support,
        monomial (b.filter (fun v => π v = j)) (AddMonoidAlgebra.coeff M b) *
          ((∏ i ∈ S, x i) * monomial (b.filter (fun v => π v ≠ j)) 1) := by
      conv_lhs => rw [← support_sum_monomial_coeff M]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_left_comm, monomial_mul, mul_one, Finsupp.filter_add_filter_not]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    refine Submodule.sum_mem _ fun b hb => ?_
    have hb1 : monomial (b.filter (fun v => π v = j)) (AddMonoidAlgebra.coeff M b) ∈ supported O {v | π v = j} := by
      refine monomial_mem _ fun v hv => ?_
      rw [Finsupp.support_filter, Finset.mem_filter] at hv
      exact hv.2
    have hb2 : ∀ v ∈ (b.filter (fun v => π v ≠ j)).support, π v ≠ j ∧ v ∈ b.support := by
      intro v hv
      rw [Finsupp.support_filter, Finset.mem_filter] at hv
      exact ⟨hv.2, hv.1⟩
    have hb3 : monomial (b.filter (fun v => π v ≠ j)) (1 : O) ∈ supported O {v | π v ≠ j} :=
      monomial_mem _ fun v hv => (hb2 v hv).1
    rw [pj_mul π j q hb1 (Subalgebra.mul_mem _ hP hb3)]
    refine Submodule.subset_span
      ⟨Function.update x j (q (monomial (b.filter (fun v => π v = j)) (AddMonoidAlgebra.coeff M b))), ?_,
        monomial (b.filter (fun v => π v ≠ j)) 1, ?_, ?_⟩
    · intro i
      by_cases hi : i = j
      · subst hi
        rw [Function.update_self]
        exact hq _
      · rw [Function.update_of_ne hi]
        exact hx i
    · refine monomial_mem _ fun v hv => ?_
      show π v ∉ insert j S
      rw [Finset.mem_insert, not_or]
      exact ⟨(hb2 v hv).1, supp_of_mem hM hb v (hb2 v hv).2⟩
    · rw [Finset.prod_insert hj, Function.update_self, mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Function.update_of_ne]
      rintro rfl
      exact hj hi
  exact hle hG

end PartialSpanProjection


open PartialSpanProjection in
theorem atl : ATL := by
  intro O _ _ _ ι σ _ _ π X hX hfin hsat F hF
  have hq : ∀ j, ∃ q : MvPolynomial σ O →ₗ[O] MvPolynomial σ O, (∀ A, q A ∈ X j) ∧ ∀ x ∈ X j, q x = x := by
    intro j
    obtain ⟨s, hs⟩ := hfin j
    exact exists_retraction (X j) s hs (hsat j)
  choose q hq1 hq2 using hq
  have hW : ∀ S : Finset ι, F ∈ W π X S := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine Submodule.subset_span ⟨fun _ => 0, fun j => (X j).zero_mem, F, ?_, ?_⟩
      · rw [mem_supported]
        intro v _
        exact Finset.notMem_empty _
      · rw [Finset.prod_empty, one_mul]
    | insert j S hj ih =>
      have h := projection_mem_partial_span π X hX S j hj (q j) (hq1 j) ih
      rwa [pj_fix π j (q j) (X j) (hX j) (hq2 j) (hF j)] at h
  have hle : W π X Finset.univ ≤
      Submodule.span O {y | ∃ x : ι → MvPolynomial σ O, (∀ j, x j ∈ X j) ∧ y = ∏ j, x j} := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨x, hx, M, hM, rfl⟩
    have hemp : {v | π v ∉ (Finset.univ : Finset ι)} = (∅ : Set σ) := by
      ext v
      simp
    rw [hemp, supported_empty] at hM
    obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 hM
    have : (∏ j, x j) * algebraMap O (MvPolynomial σ O) c = c • ∏ j, x j := by
      rw [Algebra.smul_def, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
  exact hle (hW Finset.univ)

end Formalism.MainNotions.Proposition5Numerics
end
end

noncomputable section

namespace Formalism.MainNotions.Proposition5Numerics

theorem decomposition_of_three_parts (hVB : RestValBdG) (hXX : RestXXG) (hDd : RestDdG) : RestDecG :=
  restDecG_of atl valSlice valComp hVB hXX hDd

theorem membership_of_three_parts (hVB : RestValBdG) (hXX : RestXXG) (hDd : RestDdG) (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) :
    RestMemb D CLa Ck Crk Cdeg :=
  membership_of_four_parts (decomposition_of_three_parts hVB hXX hDd) restAlgG restDegG restLabG D CLa Ck Crk Cdeg

end Formalism.MainNotions.Proposition5Numerics
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembXXb
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

namespace XXb

section At

variable (p : ℕ) {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
  {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)

def Mx (j : ZMod J) (x : ℤ) : ℤ :=
  if h : ∃ u, u < Dt.nL j + r ∧ pU p O Fr Dt j u = x then
    (if Even x then ka j (Classical.choose h + 1) 0 + 4 * (cP : ℤ) else ka j (Classical.choose h) 0 + 4 * (cP : ℤ))
  else 0

theorem Mx_even {L₁ N₁' : ℕ} (hV : Fr.Valid L₁ N₁') (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < Dt.nL j + r) (he : Even (pU p O Fr Dt j u)) :
    Mx p O Fr cP Dt ka j (pU p O Fr Dt j u) = ka j (u + 1) 0 + 4 * (cP : ℤ) := by
  have hinj : ∀ a b, a < Dt.nL j + r → b < Dt.nL j + r → pU p O Fr Dt j a = pU p O Fr Dt j b → a = b := by
    intro a b ha hb hab
    unfold pU at hab
    rw [hnL j] at ha hb hab
    rcases lt_trichotomy a b with h1 | h1 | h1
    · exact absurd hab (ne_of_lt ((posU_lt_iff hV (segZ j) a b ha hb).mpr h1))
    · exact h1
    · exact absurd hab (ne_of_gt ((posU_lt_iff hV (segZ j) b a hb ha).mpr h1))
  have hex : ∃ u', u' < Dt.nL j + r ∧ pU p O Fr Dt j u' = pU p O Fr Dt j u := ⟨u, hu, rfl⟩
  have hc := Classical.choose_spec hex
  have heq : Classical.choose hex = u := hinj _ _ hc.1 hu hc.2
  unfold Mx
  rw [dite_eq_left hex, if_pos he, heq]

theorem Mx_odd {L₁ N₁' : ℕ} (hV : Fr.Valid L₁ N₁') (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < Dt.nL j + r) (he : ¬ Even (pU p O Fr Dt j u)) :
    Mx p O Fr cP Dt ka j (pU p O Fr Dt j u) = ka j u 0 + 4 * (cP : ℤ) := by
  have hinj : ∀ a b, a < Dt.nL j + r → b < Dt.nL j + r → pU p O Fr Dt j a = pU p O Fr Dt j b → a = b := by
    intro a b ha hb hab
    unfold pU at hab
    rw [hnL j] at ha hb hab
    rcases lt_trichotomy a b with h1 | h1 | h1
    · exact absurd hab (ne_of_lt ((posU_lt_iff hV (segZ j) a b ha hb).mpr h1))
    · exact h1
    · exact absurd hab (ne_of_gt ((posU_lt_iff hV (segZ j) b a hb ha).mpr h1))
  have hex : ∃ u', u' < Dt.nL j + r ∧ pU p O Fr Dt j u' = pU p O Fr Dt j u := ⟨u, hu, rfl⟩
  have hc := Classical.choose_spec hex
  have heq : Classical.choose hex = u := hinj _ _ hc.1 hu hc.2
  unfold Mx
  rw [dite_eq_left hex, if_neg he, heq]

theorem cond_at {TT : Finset (Fin n')} {L₁ L₂ : ℕ} {d : Fin n' → ℕ}
    (hM : MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card)
    (δ : ZMod J × ℤ → ℕ) (j : ZMod J) (A : MvPolynomial (ℤ × Fin r) O) (B : MvPolynomial (ℤ × Fin K) O)
    (hPl : PlOK p O Fr deg Y N₁ G' cP Dt ka δ j A) (hNo : NoOK p O Fr cP Dt dNo ka j B) (u : ℕ)
    (hu : u < Dt.nL j + r) (hx : pU p O Fr Dt j u ∈ Fr.letters (segZ j)) (hW : ¬ Fr.IsW (segZ j) (pU p O Fr Dt j u)) :
    (Even (pU p O Fr Dt j u) →
      lam1S LZ {y | y ≤ pU p O Fr Dt j u} B ≤ ((Mx p O Fr cP Dt ka j (pU p O Fr Dt j u) : ℤ) : WithBot ℤ) ∧
      ((Mx p O Fr cP Dt ka j (pU p O Fr Dt j u) + (mStar p Fr (r + K) N₁ (p ^ G') cP : ℤ) : ℤ) : WithTop ℤ) ≤
        valS LZ {y | y < pU p O Fr Dt j u} A) ∧
    (¬ Even (pU p O Fr Dt j u) →
      lam1S LZ {y | y < pU p O Fr Dt j u} B ≤ ((Mx p O Fr cP Dt ka j (pU p O Fr Dt j u) : ℤ) : WithBot ℤ) ∧
      ((Mx p O Fr cP Dt ka j (pU p O Fr Dt j u) + (mStar p Fr (r + K) N₁ (p ^ G') cP : ℤ) : ℤ) : WithTop ℤ) ≤
        valS LZ {y | y ≤ pU p O Fr Dt j u} A) ∧
    geR (valS LZ {y | y < pU p O Fr Dt j u} A)
      (Bo p Fr deg (segZ j) (pU p O Fr Dt j u) / 2 - sl p Fr deg Y (r + K) (segZ j) (pU p O Fr Dt j u)) := by
  have hV := hM.frames.2.1
  have hr1 : 1 ≤ r := by have := hM.two_le_r; omega
  have hc0 : (0 : ℝ) ≤ (cP : ℝ) := Nat.cast_nonneg _
  have hs : 128 * (cP : ℝ) ≤ slU Fr p deg Y (r + K) Dt.nL j u := hM.margin (segZ j) _ hx hW
  refine ⟨fun he => ?_, fun he => ?_, ?_⟩
  · rw [Mx_even p O Fr cP Dt ka hV hnL j u hu he]
    refine ⟨(hNo.2.2 u hu).2, int_le_val ?_ (hPl.2.2.1 u hu)⟩
    have h1 := threshold_ge_even_position Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j u he
    have h2 := ar1 _ _ _ _ _ h1 hs
    unfold tauU
    push_cast
    exact h2
  · rw [Mx_odd p O Fr cP Dt ka hV hnL j u hu he]
    have huN : u < Dt.nL j := by
      by_contra hcon
      exact he (posU_even hV (segZ j) (Dt.nL j) u (by omega) hu)
    refine ⟨(hNo.2.2 u hu).1, int_le_val ?_ (hPl.2.2.2 u huN)⟩
    obtain ⟨l1, l2⟩ := posU_letter hV hr1 (segZ j) (Dt.nL j) (hnL j) (u + 1) (by omega)
    have hs' : 128 * (cP : ℝ) ≤ slU Fr p deg Y (r + K) Dt.nL j (u + 1) := hM.margin (segZ j) _ l1 l2
    have h1 := threshold_ge_odd_position Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j u he
    have h2 := ar1 _ _ _ _ _ h1 hs'
    unfold tauU
    push_cast
    exact h2
  · refine geR_of_ceil ?_ (hPl.2.2.1 u hu)
    have h1 := th_ge_B Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j u
    exact ar3 _ _ _ _ h1 hs hc0

end At

end XXb


open XXb in
theorem restXXG_b : RestXXG := by
  intro p _ n' r K _ _ _ O _ _ _ S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J _ Dt dPl dNo ka hT δ j A B hPl hNo
  have hV := hM.frames.2.1
  have hr1 : 1 ≤ r := by have := hM.two_le_r; omega
  have hnL := hT.1.2.1
  have hdeg : ∀ mm ∈ (plEmb O r K A * nmEmb O r K B).support, ∀ x,
      ∑ c : Fin (r + K), mm (x, c) = δ (j, x) + dNoOf p O Fr Dt dNo (j, x) ∧
      ordDeg mm x ≤ δ (j, x) + dNoOf p O Fr Dt dNo (j, x) := by
    intro mm hmm x
    obtain ⟨ua, hua, ub, hub, h⟩ := XXb.deg_mul A B mm hmm
    have e1 : ∑ c : Fin r, mm (x, Fin.castAdd K c) = δ (j, x) := by
      rw [← hPl.2.1 ua hua x]
      exact Finset.sum_congr rfl fun c _ => (h x).1 c
    have e2 : ∑ c : Fin K, mm (x, Fin.natAdd r c) = dNoOf p O Fr Dt dNo (j, x) := by
      rw [← hNo.2.1 ub hub x]
      exact Finset.sum_congr rfl fun c _ => (h x).2 c
    refine ⟨by rw [Fin.sum_univ_add, e1, e2], ?_⟩
    unfold ordDeg
    split_ifs
    · rw [e2]; omega
    · rw [e1]; omega
  refine ⟨?_, ?_⟩
  · unfold XX'
    refine Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨A, B, XXb.Mx p O Fr cP Dt ka j, hPl.1, hNo.1, ?_, rfl⟩, ?_⟩
    · intro x hx hW
      obtain ⟨u, hu, rfl⟩ := XXb.exists_posU hV hr1 (segZ j) (Dt.nL j) (hnL j) x hx hW
      exact XXb.cond_at p O Fr deg Y N₁ G' cP Dt dNo ka hM hnL δ j A B hPl hNo u hu hx hW
    · rw [mem_restrictSupport_iff]
      intro mm hmm x _ _
      show (ordDeg mm x : ℝ) ≤ ((δ (j, x) + dNoOf p O Fr Dt dNo (j, x) : ℕ) : ℝ)
      exact Nat.cast_le.2 (hdeg mm hmm x).2
  · rw [mem_restrictSupport_iff]
    intro mm hmm x _
    exact (hdeg mm hmm x).1

end Formalism.MainNotions.Proposition5Numerics
end
end

noncomputable section

namespace Formalism.MainNotions.Proposition5Numerics

theorem restMemb (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestMemb D CLa Ck Crk Cdeg :=
  membership_of_three_parts restValBdG restXXG_b restDdG_holds D CLa Ck Crk Cdeg

end Formalism.MainNotions.Proposition5Numerics
