module

public import Formalism.LocalToGlobal.CharacterGerms.BlockMembershipNormOne

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePHaDefs
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.HaP

open MvPolynomial Formalism.L2.Pj

def SatRetrSt : Prop :=
  ∀ (ι : Type) [Fintype ι] (W : Submodule ℤ (ι → ℤ)), (∀ (z : ℤ) (x : ι → ℤ), z ≠ 0 → z • x ∈ W → x ∈ W) →
    ∃ ρ : (ι → ℤ) →ₗ[ℤ] (ι → ℤ), (∀ x, ρ x ∈ W) ∧ ∀ x ∈ W, ρ x = x

def RowInvUpSt : Prop :=
  ∀ (Ty : Type) (r : Ty → ℕ) (n : ℕ) (K : Type) [Field K] [CharZero K] (P : MvPolynomial (Letter Ty r n) K),
    (∀ (σ : Ty) (i i' : Fin (r σ)), i' < i → ∀ q : ℚ, rowShift r n K σ i i' (q : K) P = P) → RowInv r n K P

end Formalism.L2.FormalSeriesBounds.HaP
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePHaSpan
section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePDescSpanSt
section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePDescJet
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.DescP

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Jet

variable {k : Type} [CommRing k] {n d : ℕ}

def HiOrd (K : ℕ) (g : PS k n d) : Prop :=
  ∀ μ : Fin n × Fin d →₀ ℕ, μ.degree < K → coeff μ g = 0

theorem HiOrd.mono {K K' : ℕ} {g : PS k n d} (h : HiOrd K' g) (hK : K ≤ K') : HiOrd K g := fun μ hμ => h μ (lt_of_lt_of_le hμ hK)

theorem HiOrd.mul_left {K : ℕ} {g : PS k n d} (h : HiOrd K g) (a : PS k n d) : HiOrd K (a * g) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun pq hpq => ?_
  have hpq' : pq.1 + pq.2 = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hpq
  have h2 : Finsupp.degree pq.2 < K :=
    lt_of_le_of_lt (by rw [← hpq', map_add (f := _)]; exact Nat.le_add_left _ _) hμ
  rw [h _ h2, mul_zero]

theorem HiOrd.sum {K : ℕ} {α : Type} (s : Finset α) (g : α → PS k n d) (h : ∀ i ∈ s, HiOrd K (g i)) :
    HiOrd K (∑ i ∈ s, g i) := by
  intro μ hμ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_eq_zero fun i hi => h i hi μ hμ

theorem HiOrd.deriv {K : ℕ} {g : PS k n d} (h : HiOrd (K + 1) g) (i : Fin n × Fin d) :
    HiOrd K (MvPowerSeries.pderiv (R := k) i g) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_pderiv, h _ (by rw [map_add (f := _), Finsupp.degree_single]; omega), zero_mul]

theorem HiOrd.dofN {K : ℕ} {g : PS k n d} (h : HiOrd (K + 1) g) (F : Fin d → PS k 2 d) (b : Fin n)
    (u : Fin d → k) : HiOrd K (DofN F b u g) := by
  unfold DofN
  exact HiOrd.sum _ _ fun j _ => (h.deriv _).mul_left _

theorem HiOrd.iter (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) :
    ∀ (j K : ℕ) (g : PS k n d), HiOrd (K + j) g → HiOrd K ((DofN F b u)^[j] g)
  | 0, K, g, h => h
  | j + 1, K, g, h => by
    rw [Function.iterate_succ_apply]
    exact HiOrd.iter F b u j K _ (HiOrd.dofN (K := K + j) (by rw [add_assoc]; exact h) F b u)

theorem HiOrd.foldr (F : Fin d → PS k 2 d) {ι : Type} (cp : ι → Fin n) (u : ι → Fin d → k) (m : ι →₀ ℕ) :
    ∀ (L : List ι) (K : ℕ) (g : PS k n d), HiOrd (K + (L.map m).sum) g →
      HiOrd K (L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) g)
  | [], K, g, h => by simpa using h
  | l :: L, K, g, h => by
    rw [List.foldr_cons]
    refine HiOrd.iter F (cp l) (u l) (m l) K _ (HiOrd.foldr F cp u m L (K + m l) g ?_)
    rw [List.map_cons, List.sum_cons] at h
    rw [add_assoc]
    exact h

theorem HiOrd.dmonN (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (m : ι →₀ ℕ) {K : ℕ} {g : PS k n d} (h : HiOrd (K + m.degree) g) : HiOrd K (DmonN F cp u m g) := by
  unfold DmonN
  refine HiOrd.foldr F cp u m _ K g ?_
  rw [Finset.sum_map_toList, ← Finsupp.degree_eq_sum]
  exact h

theorem const_dpolyN_eq_zero (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) {g : PS k n d} (h : HiOrd (P.totalDegree + 1) g) :
    constantCoeff (DpolyN F cp u P g) = 0 := by
  unfold DpolyN
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hd : Finsupp.degree m ≤ P.totalDegree := by
    have h1 := MvPolynomial.le_totalDegree hm
    rw [Finsupp.degree_apply]
    exact h1
  have h1 : HiOrd 1 (DmonN F cp u m g) := HiOrd.dmonN F cp u m (h.mono (by omega))
  rw [map_mul, ← coeff_zero_eq_constantCoeff_apply (DmonN F cp u m g), h1 0 (by simp), mul_zero]

theorem dofN_add (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (f g : PS k n d) :
    DofN F b u (f + g) = DofN F b u f + DofN F b u g := by
  simp only [DofN, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem dofN_smul (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (c : k) (f : PS k n d) :
    DofN F b u (c • f) = c • DofN F b u f := by
  simp only [DofN, Derivation.map_smul, Finset.smul_sum, mul_smul_comm]

theorem iter_add (A : PS k n d → PS k n d) (hA : ∀ f g, A (f + g) = A f + A g) :
    ∀ (j : ℕ) (f g : PS k n d), A^[j] (f + g) = A^[j] f + A^[j] g
  | 0, f, g => rfl
  | j + 1, f, g => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, hA,
      iter_add A hA j]

theorem iter_smul (A : PS k n d → PS k n d) (hA : ∀ (c : k) f, A (c • f) = c • A f) :
    ∀ (j : ℕ) (c : k) (f : PS k n d), A^[j] (c • f) = c • A^[j] f
  | 0, c, f => rfl
  | j + 1, c, f => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hA, iter_smul A hA j]

theorem foldr_add (F : Fin d → PS k 2 d) {ι : Type} (cp : ι → Fin n) (u : ι → Fin d → k) (m : ι →₀ ℕ) :
    ∀ (L : List ι) (f g : PS k n d),
      L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) (f + g) =
        L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) f + L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) g
  | [], f, g => rfl
  | l :: L, f, g => by
    rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, foldr_add F cp u m L f g,
      iter_add _ (dofN_add F (cp l) (u l))]

theorem foldr_smul (F : Fin d → PS k 2 d) {ι : Type} (cp : ι → Fin n) (u : ι → Fin d → k) (m : ι →₀ ℕ) :
    ∀ (L : List ι) (c : k) (f : PS k n d),
      L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) (c • f) =
        c • L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) f
  | [], c, f => rfl
  | l :: L, c, f => by
    rw [List.foldr_cons, List.foldr_cons, foldr_smul F cp u m L c f,
      iter_smul _ (dofN_smul F (cp l) (u l))]

theorem dpolyN_add (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (f g : PS k n d) :
    DpolyN F cp u P (f + g) = DpolyN F cp u P f + DpolyN F cp u P g := by
  simp only [DpolyN, DmonN, foldr_add, mul_add, Finset.sum_add_distrib]

theorem dpolyN_smul (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (c : k) (f : PS k n d) :
    DpolyN F cp u P (c • f) = c • DpolyN F cp u P f := by
  simp only [DpolyN, DmonN, foldr_smul, mul_smul_comm, Finset.smul_sum]

def nabL (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (G : PS k n d) : PS k n d →ₗ[k] k where
  toFun f := constantCoeff (DpolyN F cp u P (f * G))
  map_add' f g := by
    rw [add_mul, dpolyN_add, map_add (f := _)]
  map_smul' c f := by
    rw [smul_mul_assoc, dpolyN_smul, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
      map_smul]
    rfl

def cst (D : ℕ) : Fin n × Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => D

theorem hiOrd_sub_trunc (f : PS k n d) (D : ℕ) :
    HiOrd (D + 1) (f - ((trunc' k (cst D) f : MvPolynomial _ k) : PS k n d)) := by
  intro μ hμ
  rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc', if_pos, sub_self]
  intro i
  have h1 : μ i ≤ Finsupp.degree μ := Finsupp.le_degree i μ
  simp [cst]
  omega

theorem coe_eq_sum (p : MvPolynomial (Fin n × Fin d) k) :
    (p : PS k n d) = ∑ μ ∈ p.support, AddMonoidAlgebra.coeff p μ • monomial μ (1 : k) := by
  ext ν
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.coeff_coe, map_sum]
  simp only [map_smul, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · simpa using h

theorem nabL_trunc (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (G : PS k n d) (f : PS k n d) :
    nabL F cp u P G f = ∑ μ ∈ (trunc' k (cst P.totalDegree) f).support,
      AddMonoidAlgebra.coeff (trunc' k (cst P.totalDegree) f) μ * nabL F cp u P G (monomial μ (1 : k)) := by
  set T : PS k n d := ((trunc' k (cst P.totalDegree) f : MvPolynomial _ k) : PS k n d) with hTdef
  have h0 : nabL F cp u P G (f - T) = 0 := by
    show constantCoeff (DpolyN F cp u P ((f - T) * G)) = 0
    rw [mul_comm]
    exact const_dpolyN_eq_zero F cp u P ((hiOrd_sub_trunc f P.totalDegree).mul_left G)
  have hsplit : nabL F cp u P G f = nabL F cp u P G (f - T) + nabL F cp u P G T := by
    rw [← map_add (f := _), sub_add_cancel]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsplit, h0, zero_add, hTdef, coe_eq_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

theorem dpolyN_sub (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (g : PS k n d) (S : Finset (ι →₀ ℕ)) (hS : P.support ⊆ S) :
    DpolyN F cp u P g = ∑ m ∈ S, MvPowerSeries.C (P.coeff m) * DmonN F cp u m g := by
  unfold DpolyN
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul]

theorem const_dpolyN_lin (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    {α : Type} (s : Finset α) (c : α → k) (Q : α → MvPolynomial ι k) (g : PS k n d) :
    constantCoeff (DpolyN F cp u (∑ i ∈ s, c i • Q i) g) =
      ∑ i ∈ s, c i * constantCoeff (DpolyN F cp u (Q i) g) := by
  set S := (∑ i ∈ s, c i • Q i).support ∪ s.biUnion (fun i => (Q i).support) with hS
  rw [dpolyN_sub F cp u _ g S Finset.subset_union_left]
  have hQ : ∀ i ∈ s, DpolyN F cp u (Q i) g = ∑ m ∈ S, MvPowerSeries.C ((Q i).coeff m) * DmonN F cp u m g :=
    fun i hi => dpolyN_sub F cp u _ g S
      (fun m hm => Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, hi, hm⟩))
  have hR : ∑ i ∈ s, c i * constantCoeff (DpolyN F cp u (Q i) g) =
      ∑ i ∈ s, c i * constantCoeff (∑ m ∈ S, MvPowerSeries.C ((Q i).coeff m) * DmonN F cp u m g) :=
    Finset.sum_congr rfl fun i hi => by rw [hQ i hi]
  rw [hR]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, MvPowerSeries.constantCoeff_C, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_smul, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

end Jet

theorem exists_fin_sum {α M : Type} [AddCommMonoid M] (s : Finset α) (g : α → M) :
    ∃ (N : ℕ) (e : Fin N → α), (∀ j, e j ∈ s) ∧ ∑ x ∈ s, g x = ∑ j, g (e j) := ⟨s.card, fun j => (s.equivFin.symm j : α), fun j => (s.equivFin.symm j).2, by
    rw [← Finset.sum_coe_sort s, ← Equiv.sum_comp s.equivFin.symm]⟩

end Formalism.L2.FormalSeriesBounds.DescP
end
end

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def HaSpanSt : Prop :=
  ∀ (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (n : ℕ) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
    (K : Type) [Field K] [CharZero K] (O : Subring K), ∀ P ∈ HaO r n K O cc isX a,
    ∃ (m : ℕ) (c : Fin m → K) (Z : Fin m → MvPolynomial (Letter Ty r n) ℤ), (∀ i, c i ∈ O) ∧
      (∀ i (K' : Type) [Field K'] [CharZero K'], MvPolynomial.map (Int.castRingHom K') (Z i) ∈ HHa r n K' cc isX a) ∧
      P = ∑ i, c i • MvPolynomial.map (Int.castRingHom K) (Z i)

section Nab

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def gofY (Y : FBChart C V O dd) (n : ℕ) : PS C n dd :=
  FB.expS C (((Y.k : ℕ) : C) • ∑ b : Fin n, ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0))

theorem nab_eq_nabL (Y : FBChart C V O dd) (Ls : LetSys C dd) (n : ℕ) (g : PS C n dd) (P : MvPolynomial (Ls.ι n) C) :
    Y.nab Ls n g P = DescP.nabL (Y.B.FK C) (Ls.cp n) (Ls.uv n) P (gofY Y n) g :=
  rfl

end Nab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem descSpanSt_of (hS : HaSpanSt) : DescSpanSt Xo c := by
  intro T io y C3 C _ _ V ι _hι k Y _hY a n P hP f hf
  have : CharZero T.Fr := charZero_of_inj_zero fun x hx => by
    have h1 := congrArg ι hx
    rwa [map_natCast, map_zero, Nat.cast_eq_zero] at h1
  obtain ⟨m, cc, Z, hc, hZ, hPe⟩ :=
    hS (E →+* ℂ) Dw.mult n ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) C V.RR P hP
  let Q : Fin m → MvPolynomial (LtN Dw n) T.Fr := fun i => MvPolynomial.map (Int.castRingHom T.Fr) (Z i)
  have hmap : ∀ i, MvPolynomial.map ι (Q i) = MvPolynomial.map (Int.castRingHom C) (Z i) := by
    intro i
    simp only [Q]
    rw [MvPolynomial.map_map, RingHom.ext_int (ι.comp (Int.castRingHom T.Fr)) (Int.castRingHom C)]
  let Ls := chartLetterSystem C3 V ι a
  let tc : (Fin n × Fin (chD C3.ch) →₀ ℕ) → C := fun μ =>
    AddMonoidAlgebra.coeff (MvPowerSeries.trunc' C (DescP.cst P.totalDegree) f) μ
  have hP2 : ∀ g : PS C n (chD C3.ch),
      Y.nab Ls n g P = ∑ i, cc i * Y.nab Ls n g (MvPolynomial.map ι (Q i)) := by
    intro g
    have hg : ∀ i, Y.nab Ls n g (MvPolynomial.map ι (Q i)) = Y.nab Ls n g (MvPolynomial.map (Int.castRingHom C) (Z i)) :=
      fun i => congrArg (Y.nab Ls n g) (hmap i)
    simp only [hg, nab_eq_nabL]
    show MvPowerSeries.constantCoeff (DpolyN (Y.B.FK C) (Ls.cp n) (Ls.uv n) P (g * gofY Y n)) =
      ∑ i, cc i * MvPowerSeries.constantCoeff
        (DpolyN (Y.B.FK C) (Ls.cp n) (Ls.uv n) (MvPolynomial.map (Int.castRingHom C) (Z i)) (g * gofY Y n))
    rw [hPe]
    exact DescP.const_dpolyN_lin (Y.B.FK C) (Ls.cp n) (Ls.uv n) Finset.univ cc _ (g * gofY Y n)
  have hmono : ∀ μ : Fin n × Fin (chD C3.ch) →₀ ℕ,
      (MvPowerSeries.monomial μ (1 : C) : PS C n (chD C3.ch)) =
        MvPowerSeries.map ι (MvPowerSeries.monomial μ (1 : T.Fr)) := by
    intro μ
    rw [MvPowerSeries.map_monomial, ι.map_one]
  let S := (MvPowerSeries.trunc' C (DescP.cst P.totalDegree) f).support
  let g' : (Fin n × Fin (chD C3.ch) →₀ ℕ) × Fin m → C := fun x =>
    (tc x.1 * cc x.2) * Y.nab Ls n (MvPowerSeries.map ι (MvPowerSeries.monomial x.1 (1 : T.Fr)))
      (MvPolynomial.map ι (Q x.2))
  have hmain : Y.nab Ls n f P = ∑ x ∈ S ×ˢ (Finset.univ : Finset (Fin m)), g' x := by
    rw [Finset.sum_product, nab_eq_nabL, DescP.nabL_trunc]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← nab_eq_nabL, hP2, hmono μ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [g', tc]
    ring
  obtain ⟨N, e, _he, hsum⟩ := DescP.exists_fin_sum (S ×ˢ (Finset.univ : Finset (Fin m))) g'
  refine ⟨N, fun j => tc (e j).1 * cc (e j).2, fun j => Q (e j).2,
    fun j => MvPowerSeries.monomial (e j).1 (1 : T.Fr), ?_, ?_, ?_, ?_⟩
  · intro j
    have htc : V.Ge 0 (tc (e j).1) := by
      simp only [tc]
      rw [MvPowerSeries.coeff_trunc']
      split_ifs
      · exact hf _
      · exact VF.Ge.zero 0
    exact VF.Ge.mul_int htc (hc (e j).2)
  · intro j
    refine ⟨hZ (e j).2 T.Fr, fun μ => ?_⟩
    simp only [Q]
    rw [MvPolynomial.coeff_map, eq_intCast]
    exact ⟨((AddMonoidAlgebra.coeff (Z (e j).2) μ : ℤ) : T.V), map_intCast _ _⟩
  · intro j μ
    rw [MvPowerSeries.coeff_monomial]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · rw [hmain, hsum]

end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.HaP

open MvPolynomial Formalism.L2.Pj

section Sub

variable {Ty : Type} (r : Ty → ℕ) (n : ℕ) (k : Type) [Field k] (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)

theorem hha_zero : (0 : MvPolynomial (Letter Ty r n) k) ∈ HHa r n k cc isX a := by
  refine ⟨Submodule.zero_mem _, fun σ i i' _ t => map_zero _, fun m hm => by simp at hm⟩

theorem hha_add {P Q : MvPolynomial (Letter Ty r n) k} (hP : P ∈ HHa r n k cc isX a) (hQ : Q ∈ HHa r n k cc isX a) :
    P + Q ∈ HHa r n k cc isX a := by
  obtain ⟨hP1, hP2, hP3⟩ := hP
  obtain ⟨hQ1, hQ2, hQ3⟩ := hQ
  refine ⟨Submodule.add_mem _ hP1 hQ1, fun σ i i' hii t => ?_, fun m hm => ?_⟩
  · rw [map_add (f := _), hP2 σ i i' hii t, hQ2 σ i i' hii t]
  · rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hP3 m h
    · exact hQ3 m h

theorem hha_smul (c : k) {P : MvPolynomial (Letter Ty r n) k} (hP : P ∈ HHa r n k cc isX a) :
    c • P ∈ HHa r n k cc isX a := by
  obtain ⟨hP1, hP2, hP3⟩ := hP
  refine ⟨Submodule.smul_mem _ c hP1, fun σ i i' hii t => ?_, fun m hm => hP3 m (support_smul hm)⟩
  rw [map_smul, hP2 σ i i' hii t]

end Sub

section Maps

variable {Ty : Type} (r : Ty → ℕ) (n : ℕ)

theorem lap_map {k k' : Type} [Field k] [Field k'] (φ : k →+* k') (τ τ' : Ty) (a0 : Fin (r τ)) (a1 : Fin (r τ'))
    (p : MvPolynomial (Letter Ty r n) k) :
    lap r n k' 1 τ τ' a0 a1 (map φ p) = map φ (lap r n k 1 τ τ' a0 a1 p) := by
  simp [lap, Matrix.one_apply, pderiv_map]

theorem rowShift_map {k k' : Type} [Field k] [Field k'] (φ : k →+* k') (σ0 : Ty) (i i' : Fin (r σ0)) (t : k)
    (p : MvPolynomial (Letter Ty r n) k) :
    rowShift r n k' σ0 i i' (φ t) (map φ p) = map φ (rowShift r n k σ0 i i' t p) := by
  simp only [rowShift, aeval_def, algebraMap_eq, map_eval₂]
  congr 1
  funext ℓ
  simp only [Function.comp_apply]
  split_ifs <;> simp

end Maps

section Comp

variable {K : Type} [Field K] [CharZero K] {σ : Type}

def comp (lam : K →ₗ[ℚ] ℚ) (P : MvPolynomial σ K) : MvPolynomial σ ℚ :=
  ∑ m ∈ P.support, monomial m (lam (P.coeff m))

theorem coeff_comp (lam : K →ₗ[ℚ] ℚ) (P : MvPolynomial σ K) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (comp lam P) m = lam (AddMonoidAlgebra.coeff P m) := by
  by_cases h : AddMonoidAlgebra.coeff P m = 0 <;> simp [comp, coeff_monomial, h]

theorem comp_zero (lam : K →ₗ[ℚ] ℚ) : comp lam (0 : MvPolynomial σ K) = 0 := by
  simp [comp]

theorem comp_sum (lam : K →ₗ[ℚ] ℚ) {α : Type} (s : Finset α) (f : α → MvPolynomial σ K) :
    comp lam (∑ i ∈ s, f i) = ∑ i ∈ s, comp lam (f i) := by
  ext m
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coeff_comp, coeff_sum, map_sum]

theorem comp_smul_map (lam : K →ₗ[ℚ] ℚ) (c : K) (p : MvPolynomial σ ℚ) :
    comp lam (c • map (algebraMap ℚ K) p) = lam c • p := by
  ext m
  simp only [coeff_comp, coeff_smul, coeff_map, smul_eq_mul]
  rw [mul_comm c, ← Algebra.smul_def, map_smul, smul_eq_mul]
  exact mul_comm _ _

theorem comp_comm (lam : K →ₗ[ℚ] ℚ) (Φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (Ψ : MvPolynomial σ ℚ →ₗ[ℚ] MvPolynomial σ ℚ)
    (h : ∀ m, Φ (monomial m 1) = map (algebraMap ℚ K) (Ψ (monomial m 1))) (P : MvPolynomial σ K) :
    comp lam (Φ P) = Ψ (comp lam P) := by
  have hP : P = ∑ m ∈ P.support, AddMonoidAlgebra.coeff P m • monomial m (1 : K) := by
    conv_lhs => rw [P.as_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_monomial, smul_eq_mul, mul_one]
  have hc : comp lam P = ∑ m ∈ P.support, lam (AddMonoidAlgebra.coeff P m) • monomial m (1 : ℚ) := by
    unfold comp
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_monomial, smul_eq_mul, mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hc, map_sum]
  conv_lhs => rw [hP]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, comp_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul Φ, h, comp_smul_map, map_smul Ψ]

variable {Ty : Type} (r : Ty → ℕ) (n : ℕ) {cc : Ty → Ty} {isX : Ty → Prop} {a : Ty → ℕ → ℕ}

theorem comp_mem (lam : K →ₗ[ℚ] ℚ) {P : MvPolynomial (Letter Ty r n) K} (hP : P ∈ HHa r n K cc isX a) :
    comp lam P ∈ HHa r n ℚ cc isX a := by
  obtain ⟨h1, h2, h3⟩ := hP
  have hmono : ∀ m : Letter Ty r n →₀ ℕ, monomial m (1 : K) = map (algebraMap ℚ K) (monomial m (1 : ℚ)) := by
    intro m
    rw [map_monomial, (algebraMap ℚ K).map_one]
  refine ⟨?_, fun σ i i' hii t => ?_, fun m hm => ?_⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h1 ⊢
    intro τ hτ a0 a1
    have hc := comp_comm lam (lap r n K 1 τ (cc τ) a0 a1) (lap r n ℚ 1 τ (cc τ) a0 a1)
      (fun m => by rw [hmono, lap_map]) P
    rw [h1 τ hτ a0 a1, comp_zero] at hc
    exact hc.symm
  · have hc := comp_comm lam (rowShift r n K σ i i' (algebraMap ℚ K t)).toLinearMap
      (rowShift r n ℚ σ i i' t).toLinearMap (fun m => by
        simp only [AlgHom.toLinearMap_apply]
        rw [hmono, rowShift_map]) P
    simp only [AlgHom.toLinearMap_apply] at hc
    rw [h2 σ i i' hii] at hc
    exact hc.symm
  · rw [mem_support_iff, coeff_comp] at hm
    exact h3 m (mem_support_iff.mpr fun h0 => hm (by rw [h0, map_zero]))

end Comp

section Up

variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {cc : Ty → Ty} {isX : Ty → Prop} {a : Ty → ℕ → ℕ}

theorem map_mem (hR : RowInvUpSt) (K : Type) [Field K] [CharZero K] (p : MvPolynomial (Letter Ty r n) ℚ)
    (hp : p ∈ HHa r n ℚ cc isX a) : map (algebraMap ℚ K) p ∈ HHa r n K cc isX a := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨?_, hR Ty r n K _ fun σ i i' hii q => ?_, fun m hm => h3 m (support_map_subset _ _ hm)⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h1 ⊢
    intro τ hτ a0 a1
    rw [lap_map, h1 τ hτ a0 a1, map_zero]
  · have e : ((q : ℚ) : K) = algebraMap ℚ K q := (eq_ratCast (algebraMap ℚ K) q).symm
    rw [e, rowShift_map, h2 σ i i' hii q]

theorem map_int_mem (hR : RowInvUpSt) (K : Type) [Field K] [CharZero K] (z : MvPolynomial (Letter Ty r n) ℤ)
    (hz : map (Int.castRingHom ℚ) z ∈ HHa r n ℚ cc isX a) : map (Int.castRingHom K) z ∈ HHa r n K cc isX a := by
  have e : map (Int.castRingHom K) z = map (algebraMap ℚ K) (map (Int.castRingHom ℚ) z) := by
    rw [map_map, RingHom.ext_int (Int.castRingHom K) ((algebraMap ℚ K).comp (Int.castRingHom ℚ))]
  rw [e]
  exact map_mem hR K _ hz

end Up

section Poly

variable {L : Type}

def poly {R : Type} [CommRing R] (Bd : Finset (L →₀ ℕ)) (v : Bd → R) : MvPolynomial L R :=
  ∑ b : Bd, monomial b.1 (v b)

theorem coeff_poly {R : Type} [CommRing R] (Bd : Finset (L →₀ ℕ)) (v : Bd → R) (m : L →₀ ℕ) :
    AddMonoidAlgebra.coeff (poly Bd v) m = if h : m ∈ Bd then v ⟨m, h⟩ else 0 := by
  unfold poly
  rw [coeff_sum]
  simp only [coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨m, h⟩]
    · simp
    · intro b _ hb
      rw [ite_eq_right]
      intro hbm
      exact hb (Subtype.ext hbm)
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · apply Finset.sum_eq_zero
    intro b _
    rw [ite_eq_right]
    intro hbm
    exact h (hbm ▸ b.2)

theorem coeff_map_poly {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (Bd : Finset (L →₀ ℕ)) (v : Bd → R)
    (m : L →₀ ℕ) : AddMonoidAlgebra.coeff (map φ (poly Bd v)) m = if h : m ∈ Bd then φ (v ⟨m, h⟩) else 0 := by
  rw [coeff_map, coeff_poly, apply_dite φ, map_zero]

end Poly

section Main

variable {Ty : Type} (r : Ty → ℕ) (n : ℕ) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)

def Wsub (Bd : Finset (Letter Ty r n →₀ ℕ)) : Submodule ℤ (Bd → ℤ) where
  carrier := {z | map (Int.castRingHom ℚ) (poly Bd z) ∈ HHa r n ℚ cc isX a}
  add_mem' := by
    intro x y hx hy
    have e : map (Int.castRingHom ℚ) (poly Bd (x + y)) =
        map (Int.castRingHom ℚ) (poly Bd x) + map (Int.castRingHom ℚ) (poly Bd y) := by
      ext m
      simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_map_poly]
      split_ifs <;> simp
    show map (Int.castRingHom ℚ) (poly Bd (x + y)) ∈ HHa r n ℚ cc isX a
    rw [e]
    exact hha_add r n ℚ cc isX a hx hy
  zero_mem' := by
    have e : map (Int.castRingHom ℚ) (poly Bd (0 : Bd → ℤ)) = 0 := by
      ext m
      rw [AddMonoidAlgebra.coeff_zero, coeff_map_poly]
      split_ifs <;> simp
    show map (Int.castRingHom ℚ) (poly Bd (0 : Bd → ℤ)) ∈ HHa r n ℚ cc isX a
    rw [e]
    exact hha_zero r n ℚ cc isX a
  smul_mem' := by
    intro c x hx
    have e : map (Int.castRingHom ℚ) (poly Bd (c • x)) = (c : ℚ) • map (Int.castRingHom ℚ) (poly Bd x) := by
      ext m
      rw [coeff_smul, coeff_map_poly, coeff_map_poly]
      split_ifs <;> simp
    show map (Int.castRingHom ℚ) (poly Bd (c • x)) ∈ HHa r n ℚ cc isX a
    rw [e]
    exact hha_smul r n ℚ cc isX a _ hx

theorem wsub_sat (Bd : Finset (Letter Ty r n →₀ ℕ)) (z : ℤ) (x : Bd → ℤ) (hz : z ≠ 0)
    (hx : z • x ∈ Wsub r n cc isX a Bd) : x ∈ Wsub r n cc isX a Bd := by
  have e : map (Int.castRingHom ℚ) (poly Bd (z • x)) = (z : ℚ) • map (Int.castRingHom ℚ) (poly Bd x) := by
    ext m
    rw [coeff_smul, coeff_map_poly, coeff_map_poly]
    split_ifs <;> simp
  have hx' : map (Int.castRingHom ℚ) (poly Bd (z • x)) ∈ HHa r n ℚ cc isX a := hx
  rw [e] at hx'
  have hz' : (z : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hz
  have h2 := hha_smul r n ℚ cc isX a ((z : ℚ)⁻¹) hx'
  rw [smul_smul, inv_mul_cancel₀ hz', one_smul] at h2
  show map (Int.castRingHom ℚ) (poly Bd x) ∈ HHa r n ℚ cc isX a
  exact h2

end Main

section Assembly

theorem exists_clear (s : Type) [Fintype s] (u : s → ℚ) :
    ∃ N : ℕ, N ≠ 0 ∧ ∃ z : s → ℤ, ∀ b, (z b : ℚ) = N * u b := by
  refine ⟨∏ b, (u b).den, Finset.prod_ne_zero_iff.mpr fun b _ => (u b).den_nz,
    fun b => (∏ b' ∈ Finset.univ.erase b, ((u b').den : ℤ)) * (u b).num, fun b => ?_⟩
  have hq : u b * ((u b).den : ℚ) = ((u b).num : ℚ) := Rat.mul_den_eq_num (u b)
  rw [← Finset.mul_prod_erase Finset.univ (fun b' => (u b').den) (Finset.mem_univ b)]
  push_cast
  rw [← hq]
  ring

private theorem fix_sum_lemma {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : (ι → ℤ) →ₗ[ℤ] (ι → ℤ)) (z : ι → ℤ)
    (hz : ρ z = z) (j : ι) : z j = ∑ b, z b * ρ (Pi.single b 1) j := by
  have hz' : z = ∑ b, z b • (Pi.single b (1 : ℤ) : ι → ℤ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  calc z j = ρ z j := (congrFun hz j).symm
    _ = ρ (∑ b, z b • (Pi.single b (1 : ℤ) : ι → ℤ)) j := by rw [← hz']
    _ = ∑ b, z b * ρ (Pi.single b 1) j := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem haSpanSt_of (hS : SatRetrSt) (hR : RowInvUpSt) : HaSpanSt := by
  unfold HaSpanSt
  intro Ty _ r n cc isX a K _ _ O P hP
  obtain ⟨hPH, hPO⟩ := hP
  obtain ⟨Bd, hBd⟩ : ∃ Bd, Bd = P.support := ⟨_, rfl⟩
  obtain ⟨ρ, hρW, hρfix⟩ := hS Bd (Wsub r n cc isX a Bd) (fun z x hz hx => wsub_sat r n cc isX a Bd z x hz hx)
  have key : ∀ j : Bd, AddMonoidAlgebra.coeff P j.1 = ∑ b : Bd, AddMonoidAlgebra.coeff P b.1 * ((ρ (Pi.single b 1) j : ℤ) : K) := by
    intro j
    rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff ℚ _).mp fun lam => ?_
    obtain ⟨N, hN, z, hz⟩ := exists_clear Bd (fun b => lam (AddMonoidAlgebra.coeff P b.1))
    have hzW : z ∈ Wsub r n cc isX a Bd := by
      have e : map (Int.castRingHom ℚ) (poly Bd z) = (N : ℚ) • comp lam P := by
        ext m
        rw [coeff_map_poly, coeff_smul, coeff_comp, smul_eq_mul]
        split_ifs with h
        · simpa using hz ⟨m, h⟩
        · have h0 : AddMonoidAlgebra.coeff P m = 0 := by
            by_contra hc
            exact h (by rw [hBd]; exact mem_support_iff.mpr hc)
          rw [h0, map_zero, mul_zero]
      show map (Int.castRingHom ℚ) (poly Bd z) ∈ HHa r n ℚ cc isX a
      rw [e]
      exact hha_smul r n ℚ cc isX a _ (comp_mem r n lam hPH)
    have hfix := fix_sum_lemma ρ z (hρfix z hzW) j
    have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    have hq : (z j : ℚ) = ∑ b, (z b : ℚ) * ((ρ (Pi.single b 1) j : ℤ) : ℚ) := by exact_mod_cast hfix
    simp only [hz] at hq
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, sub_eq_zero]
    have hl : lam (AddMonoidAlgebra.coeff P j.1) = ∑ b : Bd, lam (AddMonoidAlgebra.coeff P b.1) * ((ρ (Pi.single b 1) j : ℤ) : ℚ) := by
      apply mul_left_cancel₀ hN'
      rw [hq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hl]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hs : AddMonoidAlgebra.coeff P b.1 * ((ρ (Pi.single b 1) j : ℤ) : K) = (ρ (Pi.single b 1) j) • AddMonoidAlgebra.coeff P b.1 := by
      rw [zsmul_eq_mul, mul_comm]
    rw [hs, map_zsmul, zsmul_eq_mul, mul_comm]
  have hmain : P = ∑ b : Bd, AddMonoidAlgebra.coeff P b.1 • map (Int.castRingHom K) (poly Bd (ρ (Pi.single b 1))) := by
    ext m
    rw [coeff_sum]
    simp only [coeff_smul, coeff_map_poly, smul_eq_mul]
    by_cases h : m ∈ Bd
    · simp only [dite_eq_left h, eq_intCast]
      exact key ⟨m, h⟩
    · simp only [dite_eq_right h, mul_zero, Finset.sum_const_zero]
      by_contra hc
      exact h (by rw [hBd]; exact mem_support_iff.mpr hc)
  have hsum : ∑ i : Fin (Fintype.card Bd), P.coeff ((Fintype.equivFin Bd).symm i).1 •
      map (Int.castRingHom K) (poly Bd (ρ (Pi.single ((Fintype.equivFin Bd).symm i) 1))) =
      ∑ b : Bd, AddMonoidAlgebra.coeff P b.1 • map (Int.castRingHom K) (poly Bd (ρ (Pi.single b 1))) :=
    Equiv.sum_comp (Fintype.equivFin Bd).symm
      (fun b : Bd => AddMonoidAlgebra.coeff P b.1 • map (Int.castRingHom K) (poly Bd (ρ (Pi.single b 1))))
  refine ⟨Fintype.card Bd, fun i => P.coeff ((Fintype.equivFin Bd).symm i).1,
    fun i => poly Bd (ρ (Pi.single ((Fintype.equivFin Bd).symm i) 1)), fun i => hPO _,
    fun i K' _ _ => map_int_mem hR K' _ (hρW _), ?_⟩
  exact hmain.trans hsum.symm

end Assembly

end Formalism.L2.FormalSeriesBounds.HaP
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePHaLeaves
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.HaP

open MvPolynomial Formalism.L2.Pj

theorem satRetr : SatRetrSt := by
  intro ι _ W hW
  haveI : NoZeroSMulDivisors ℤ ((ι → ℤ) ⧸ W) := by
    refine ⟨fun {z x} h => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective W x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    by_cases hz : z = 0
    · exact Or.inl hz
    · right
      rw [Submodule.Quotient.mk_eq_zero]
      exact hW z x hz h
  haveI : Module.Free ℤ ((ι → ℤ) ⧸ W) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property W.mkQ LinearMap.id (Submodule.mkQ_surjective W)
  have hs' : ∀ y, W.mkQ (s y) = y := fun y => by rw [← LinearMap.comp_apply, hs, LinearMap.id_apply]
  refine ⟨(LinearMap.id - s ∘ₗ W.mkQ : (ι → ℤ) →ₗ[ℤ] (ι → ℤ)), fun x => ?_, fun x hx => ?_⟩
  · have h1 : W.mkQ ((LinearMap.id - s ∘ₗ W.mkQ : (ι → ℤ) →ₗ[ℤ] (ι → ℤ)) x) = 0 := by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hs', sub_self]
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
  · have h0 : W.mkQ x = 0 := by rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hx
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h0, map_zero, sub_zero]

theorem rowInvUp : RowInvUpSt := by
  unfold RowInvUpSt RowInv
  intro Ty r n K _ _ P hP σ i i' hii t
  classical
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : MvPolynomial (Letter Ty r n) K →ₐ[K] Polynomial (MvPolynomial (Letter Ty r n) K),
      ∀ ℓ : Letter Ty r n, Φ (X ℓ) = if ∃ b, ℓ = ⟨σ, (i, b)⟩ then
        Polynomial.C (X ℓ) + Polynomial.X * Polynomial.C (X ⟨σ, (i', ℓ.snd.2)⟩) else Polynomial.C (X ℓ) :=
    ⟨aeval _, fun ℓ => aeval_X _ _⟩
  have key : ∀ (s : K) (Q : MvPolynomial (Letter Ty r n) K),
      rowShift r n K σ i i' s Q = Polynomial.eval (C s) (Φ Q) := by
    intro s Q
    induction Q using MvPolynomial.induction_on with
    | C a =>
      have h1 := (rowShift r n K σ i i' s).commutes a
      have h2 := Φ.commutes a
      rw [MvPolynomial.algebraMap_eq] at h1 h2
      rw [h1, h2, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, Polynomial.eval_C]
    | add p q hp hq =>
      rw [map_add (f := _), map_add (f := _), Polynomial.eval_add, hp, hq]
    | mul_X p ℓ hp =>
      rw [map_mul, map_mul, Polynomial.eval_mul, hp, hΦ]
      congr 1
      have hx : rowShift r n K σ i i' s (X ℓ) = (aeval (R := K) fun ℓ : Letter Ty r n =>
          if ∃ b, ℓ = ⟨σ, (i, b)⟩ then (X ℓ + C s * X ⟨σ, (i', ℓ.snd.2)⟩ : MvPolynomial (Letter Ty r n) K)
          else (X ℓ : MvPolynomial (Letter Ty r n) K)) (X ℓ) := by
        unfold rowShift
        rfl
      rw [hx, aeval_X]
      split_ifs <;> simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] <;> ring
  have hQ : Φ P - Polynomial.C P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := Set.range (fun q : ℚ => (C (q : K) : MvPolynomial (Letter Ty r n) K)))
    · rintro _ ⟨q, rfl⟩
      simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C]
      rw [← key, hP σ i i' hii q, sub_self]
    · exact Set.infinite_range_of_injective fun a b h => Rat.cast_injective (MvPolynomial.C_injective _ _ h)
  rw [key t]
  have h := congrArg (Polynomial.eval (C t)) hQ
  rw [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_zero] at h
  exact sub_eq_zero.mp h

end Formalism.L2.FormalSeriesBounds.HaP
end
end

set_option autoImplicit false

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem descent_span : DescSpanSt Xo c :=
  descSpanSt_of (HaP.haSpanSt_of HaP.satRetr HaP.rowInvUp)

end Formalism.L2.FormalSeriesBounds
