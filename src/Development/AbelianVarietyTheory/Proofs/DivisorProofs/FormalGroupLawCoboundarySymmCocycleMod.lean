module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviWhittakerEqOneOfCuspidal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerateWhittakerDimParabolicInductionCuspidal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartEvalSquareProperties

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundarySymmCocycleMod
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundarySymmCocycleMod
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

namespace CobSymCoc

open GlobalTheory.Katz.CobCob

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem mvPowerSeriesMap_evalTwoGroups (φ : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map φ (at2 c u v) = at2 (map φ c) (fun i => map φ (u i)) (fun i => map φ (v i)) := by
  unfold at2
  rw [map_subst (elim_has hu hv)]
  congr 1
  funext k
  cases k <;> rfl

theorem map_op (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    map φ (op μ u v i) = op (fun j => map φ (μ j)) (fun j => map φ (u j)) (fun j => map φ (v j)) i :=
  mvPowerSeriesMap_evalTwoGroups φ (μ i) hu hv

theorem map_threeGroupsFirstVariables (φ : R →+* S) : (fun j => map φ (x1 (R := R) (d := d) j)) = x1 := by
  funext j; exact map_X φ _
theorem map_threeGroupsSecondVariables (φ : R →+* S) : (fun j => map φ (x2 (R := R) (d := d) j)) = x2 := by
  funext j; exact map_X φ _
theorem map_threeGroupsThirdVariables (φ : R →+* S) : (fun j => map φ (x3 (R := R) (d := d) j)) = x3 := by
  funext j; exact map_X φ _

theorem map_assocL (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (h : ∀ i, constantCoeff (μ i) = 0) :
    (fun i => map φ (op μ x1 (op μ x2 x3) i)) =
      op (fun j => map φ (μ j)) x1 (op (fun j => map φ (μ j)) x2 x3) := by
  funext i
  rw [map_op φ μ constantCoeff_threeGroupsFirstVariables (op_const h constantCoeff_threeGroupsSecondVariables constantCoeff_threeGroupsThirdVariables), map_threeGroupsFirstVariables]
  congr 1
  funext j
  rw [map_op φ μ constantCoeff_threeGroupsSecondVariables constantCoeff_threeGroupsThirdVariables, map_threeGroupsSecondVariables, map_threeGroupsThirdVariables]

theorem map_assocR (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (h : ∀ i, constantCoeff (μ i) = 0) :
    (fun i => map φ (op μ (op μ x1 x2) x3 i)) =
      op (fun j => map φ (μ j)) (op (fun j => map φ (μ j)) x1 x2) x3 := by
  funext i
  rw [map_op φ μ (op_const h constantCoeff_threeGroupsFirstVariables constantCoeff_threeGroupsSecondVariables) constantCoeff_threeGroupsThirdVariables, map_threeGroupsThirdVariables]
  congr 1
  funext j
  rw [map_op φ μ constantCoeff_threeGroupsFirstVariables constantCoeff_threeGroupsSecondVariables, map_threeGroupsFirstVariables, map_threeGroupsSecondVariables]

end CobSymCoc


open CobSymCoc CobCob in
theorem cob_symCoc_mod : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (f : MvPowerSeries (Fin d) Q), DIn N f → In (RingHom.ker θ * N) (cob2 (up Q μ) (cob1 (up Q μ) f)) ∧ swap (cob1 (up Q μ) f) = cob1 (up Q μ) f := by
  intro p _ B O Q _ _ _ _ θ hF d μ hL N f hf
  have hM : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp only [up, constantCoeff_map, hL.const i, map_zero]
  obtain ⟨A, Bs, -⟩ := formalGroupLawCoboundaryTwo_coboundaryOne_alt Q d (up Q μ) hM f
  refine ⟨?_, ?_⟩
  · rw [A]
    have eL : op (up Q μ) x1 (op (up Q μ) x2 x3) = up Q (op μ x1 (op μ x2 x3)) :=
      (map_assocL (algebraMap B Q) μ hL.const).symm
    have eR : op (up Q μ) (op (up Q μ) x1 x2) x3 = up Q (op μ (op μ x1 x2) x3) :=
      (map_assocR (algebraMap B Q) μ hL.const).symm
    rw [eL, eR]
    refine GlobalTheory.T.subst_sub_subst_mem_mul_of_coeff_sub_mem p B O Q θ hF (RingHom.ker θ) ?_ (Fin d) (Fin d ⊕ (Fin d ⊕ Fin d)) N f _ _ hf
      (op_const hL.const constantCoeff_threeGroupsFirstVariables (op_const hL.const constantCoeff_threeGroupsSecondVariables constantCoeff_threeGroupsThirdVariables))
      (op_const hL.const (op_const hL.const constantCoeff_threeGroupsFirstVariables constantCoeff_threeGroupsSecondVariables) constantCoeff_threeGroupsThirdVariables) ?_
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := hF.pd x (RingHom.mem_ker.1 hx)
      exact ⟨y, RingHom.mem_ker.2 hy, hxy⟩
    · intro i α
      rw [RingHom.mem_ker, ← coeff_map, map_sub]
      have h1 := congrFun (map_assocL θ μ hL.const) i
      have h2 := congrFun (map_assocR θ μ hL.const) i
      rw [h1, h2, hL.law.assoc, sub_self, map_zero]
  · have hs : (fun i => swap (up Q μ i)) = up Q μ := by
      funext i
      have e : map (algebraMap B Q) (swap (μ i)) = swap (map (algebraMap B Q) (μ i)) := by
        unfold swap
        rw [mvPowerSeriesMap_evalTwoGroups (algebraMap B Q) (μ i) (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)]
        simp only [map_X]
      show swap (map (algebraMap B Q) (μ i)) = map (algebraMap B Q) (μ i)
      rw [← e, hL.comm i]
    rw [hs, sub_self] at Bs
    exact sub_eq_zero.1 Bs

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundarySymmCocycleModStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupLawCoboundary_symmCocycle_mod : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (f : MvPowerSeries (Fin d) Q), DIn N f → In (RingHom.ker θ * N) (cob2 (up Q μ) (cob1 (up Q μ) f)) ∧ swap (cob1 (up Q μ) f) = cob1 (up Q μ) f := by
  first | exact @GlobalTheory.cob_symCoc_mod | exact GlobalTheory.cob_symCoc_mod | (intros; apply GlobalTheory.cob_symCoc_mod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalModuleActionLaws
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev.TanKill

theorem exists_mem_pow_forall_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (k : Type) [Field k] (β : R →+* k), ∃ c ∈ w0 ^ r, ∀ i, β (b.t i c) ≠ 0 := by
  intro p _ D R _ b w0 r hw k _ β
  classical
  by_contra hcon
  push_neg at hcon
  rcases Nat.eq_zero_or_pos D.a with ha | ha
  · obtain ⟨i, -⟩ := hcon 0 (zero_mem _)
    exact (Fin.elim0 (ha ▸ i))
  let i0 : Fin D.a := ⟨0, ha⟩
  have hsub : ((w0 ^ r : Ideal (𝓞 D.F)) : Set (𝓞 D.F)) ⊆
      ⋃ i ∈ ((Finset.univ : Finset (Fin D.a)) : Set (Fin D.a)), (RingHom.ker (β.comp (b.t i)) : Set (𝓞 D.F)) := by
    intro c hc
    obtain ⟨i, hi⟩ := hcon c hc
    exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_univ i)) (RingHom.mem_ker.mpr hi)
  obtain ⟨i, -, hi⟩ := (Ideal.subset_union_prime i0 i0 (fun i _ _ _ => RingHom.ker_isPrime _)).mp hsub
  have hi' : w0 ≤ RingHom.ker (β.comp (b.t i)) := (RingHom.ker_isPrime _).le_of_pow_le hi
  have hle : Ideal.span ((b.t i) '' (w0 : Set (𝓞 D.F))) ≤ RingHom.ker β := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    exact RingHom.mem_ker.mpr (RingHom.mem_ker.mp (hi' hy))
  rw [hw.2.2.1 i, top_le_iff] at hle
  exact RingHom.ker_ne_top β hle

theorem exists_mem_pow_add_eq_one : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (β : R →+* k) (r2 : ℤ), (r2 : k) = (D.tr : k) - β b.ρ → ∃ c ∈ w0 ^ r, ∃ e f : 𝓞 D.F, c + e * (D.ω - (r2 : 𝓞 D.F)) + f * (p : 𝓞 D.F) = 1 := by
  intro p _ D R _ b w0 r hw k _ _ _ β r2 hr2
  haveI : w0.IsMaximal := hw.1
  letI : Field (𝓞 D.F ⧸ w0) := Ideal.Quotient.field w0

  have hpQ : ((p : 𝓞 D.F ⧸ w0)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w0), Ideal.Quotient.eq_zero_iff_mem]; exact hw.2.1
  haveI : CharP (𝓞 D.F ⧸ w0) p := (CharP.charP_iff_prime_eq_zero (Fact.out)).mpr hpQ
  have hne : w0 ≠ ⊥ := by
    intro h
    have h1 := hw.2.1
    rw [h, Ideal.mem_bot] at h1
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h1
  haveI : Finite (𝓞 D.F ⧸ w0) := Ideal.finiteQuotientOfFreeOfNeBot w0 hne
  letI : Algebra (ZMod p) (𝓞 D.F ⧸ w0) := ZMod.algebra _ p
  letI : Algebra (ZMod p) k := ZMod.algebra _ p
  haveI : Algebra.IsAlgebraic (ZMod p) (𝓞 D.F ⧸ w0) := inferInstance
  let φ0 := IsAlgClosed.lift (M := k) (R := ZMod p) (S := 𝓞 D.F ⧸ w0)
  let φ : 𝓞 D.F →+* k := φ0.toRingHom.comp (Ideal.Quotient.mk w0)
  have hker : RingHom.ker φ = w0 := by
    ext y
    rw [RingHom.mem_ker]
    change φ0 (Ideal.Quotient.mk w0 y) = 0 ↔ y ∈ w0
    rw [map_eq_zero_iff φ0 φ0.toRingHom.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hφ := hw.2.2.2 k β φ hker

  let J : Ideal (𝓞 D.F) := Ideal.span {D.ω - (r2 : 𝓞 D.F), (p : 𝓞 D.F)}
  have hJ : w0 ⊔ J = ⊤ := by
    by_contra hsup
    have hle : J ≤ w0 := by
      have := hw.1.eq_of_le hsup le_sup_left
      exact this ▸ le_sup_right
    have hmem : D.ω - (r2 : 𝓞 D.F) ∈ w0 := hle (Ideal.subset_span (Set.mem_insert _ _))
    rw [← hker, RingHom.mem_ker, map_sub, map_intCast, hφ, hr2] at hmem
    have hρ : β b.ρ ^ 2 - (D.tr : k) * β b.ρ + (D.nm : k) = 0 := by
      have h := congrArg β b.ρ_root
      simpa using h
    have hd : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = 0 := by
      push_cast
      linear_combination (-((D.tr : k) - 2 * β b.ρ)) * hmem - 4 * hρ
    exact D.disc_p ((CharP.intCast_eq_zero_iff k p _).mp hd)
  have hJr : w0 ^ r ⊔ J = ⊤ := by
    have h := Ideal.isCoprime_iff_sup_eq.mpr hJ
    exact Ideal.isCoprime_iff_sup_eq.mp h.pow_left
  obtain ⟨c, hc, j, hj, hcj⟩ := Submodule.mem_sup.mp (hJr ▸ Submodule.mem_top : (1 : 𝓞 D.F) ∈ w0 ^ r ⊔ J)
  obtain ⟨e, f, hef⟩ := Ideal.mem_span_pair.mp hj
  exact ⟨c, hc, e, f, by rw [add_assoc, hef, hcj]⟩

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

theorem sum_eq_zero_of_eigen (T : Module.End k V) {I : Type} [DecidableEq I] (s : Finset I) :
    ∀ (w : I → V) (l : I → k), (∀ i ∈ s, T (w i) = l i • w i) → (∀ i ∈ s, l i ≠ 0) →
      T (∑ i ∈ s, w i) = 0 → ∑ i ∈ s, w i = 0 := by
  induction s using Finset.induction_on with
  | empty => intros; simp
  | insert j s hj ih =>
    intro w l hw hl hT
    rw [Finset.sum_insert hj] at hT ⊢
    have e : ∑ i ∈ s, (l i - l j) • w i = T (w j + ∑ i ∈ s, w i) - l j • (w j + ∑ i ∈ s, w i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_sum, hw j (Finset.mem_insert_self j s), smul_add, Finset.smul_sum,
        Finset.sum_congr rfl (fun i hi => hw i (Finset.mem_insert_of_mem hi))]
      simp only [sub_smul, Finset.sum_sub_distrib]
      abel
    have key := ih (fun i => (l i - l j) • w i) l
      (fun i hi => by rw [map_smul, hw i (Finset.mem_insert_of_mem hi), smul_comm])
      (fun i hi => hl i (Finset.mem_insert_of_mem hi))
      (by rw [e, map_sub, map_smul, hT, map_zero, smul_zero, sub_zero])
    rw [key, hT, zero_sub, eq_comm, neg_eq_zero] at e
    exact (smul_eq_zero.mp e).resolve_left (hl j (Finset.mem_insert_self j s))

end GlobalTheory.UPel.HT.EtLev.TanKill

namespace GlobalTheory.UPel.HT.EtLev.TanKill

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

lemma L_int {O : Type} [Ring O] (L : O →+* Module.End k V) (n : ℤ) (u : V) : L (n : O) u = (n : k) • u := by
  rw [map_intCast, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]

lemma L_nat {O : Type} [Ring O] (L : O →+* Module.End k V) (n : ℕ) (u : V) : L (n : O) u = (n : k) • u := by
  rw [map_natCast, Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]

theorem core {p : ℕ} [Fact p.Prime] (D : Datum p) {R : Type} [CommRing R] (b : Base D R) (w0 : Ideal (𝓞 D.F)) (r : ℕ)
    (hw : IsEtPlace b w0) [IsAlgClosed k] (β : R →+* k) (L : 𝓞 D.F →+* Module.End k V)
    (hlie : ∀ v, L D.ω v = β b.ρ • v → ∃ w : Fin D.a → V, (∀ i c, L c (w i) = β (b.t i c) • w i) ∧ v = ∑ i, w i)
    (v : V) (hv : ∀ c ∈ w0 ^ r, L c v = 0) : v = 0 := by
  by_cases hp : (p : k) = 0
  swap
  · have h := hv _ (Ideal.pow_mem_pow hw.2.1 r)
    rw [← Nat.cast_pow, L_nat] at h
    exact (smul_eq_zero.mp h).resolve_left (by rw [Nat.cast_pow]; exact pow_ne_zero _ hp)
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out)).mpr hp
  set Tω := L D.ω with hTω
  set ρ1 := β b.ρ with hρ1
  set ρ2 := (D.tr : k) - ρ1 with hρ2
  have hquad : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    have hb : D.bar D.ω = (D.tr : 𝓞 D.F) - D.ω := by rw [← D.tr_eq]; ring
    have h := D.nm_eq
    rw [hb] at h
    linear_combination (-1 : 𝓞 D.F) * h
  have hq : ∀ u, Tω (Tω u) = (D.tr : k) • Tω u - (D.nm : k) • u := by
    intro u
    have h := congrArg (fun f => f u) (congrArg L hquad)
    simp only [map_add (f := _), map_sub, map_mul, map_zero, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.zero_apply, L_int] at h
    rw [← hTω] at h
    rw [← sub_eq_zero, ← h]
    abel
  have hρ : ρ1 ^ 2 - (D.tr : k) * ρ1 + (D.nm : k) = 0 := by
    have h := congrArg β b.ρ_root
    simpa using h
  have hsum : ρ1 + ρ2 = D.tr := by rw [hρ2]; ring
  have hprod : ρ1 * ρ2 = D.nm := by rw [hρ2]; linear_combination (-1 : k) * hρ
  clear_value Tω ρ1 ρ2
  have hδ : ρ1 - ρ2 ≠ 0 := by
    intro h0
    have hd : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = 0 := by
      have : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = (ρ1 - ρ2) ^ 2 := by
        push_cast
        rw [← hsum, ← hprod]; ring
      rw [this, h0]; ring
    exact D.disc_p ((CharP.intCast_eq_zero_iff k p _).mp hd)
  have hcomm : ∀ c u, L c (Tω u) = Tω (L c u) := by
    intro c u
    rw [hTω, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  set v1 := (ρ1 - ρ2)⁻¹ • (Tω v - ρ2 • v) with hv1
  set v2 := (ρ1 - ρ2)⁻¹ • (ρ1 • v - Tω v) with hv2
  have hv12 : v = v1 + v2 := by
    rw [hv1, hv2, ← smul_add]
    have : Tω v - ρ2 • v + (ρ1 • v - Tω v) = (ρ1 - ρ2) • v := by rw [sub_smul]; abel
    rw [this, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  have e1 : Tω v1 = ρ1 • v1 := by
    rw [hv1, map_smul, map_sub, map_smul, hq, smul_comm ρ1]
    congr 1
    rw [← hsum, ← hprod]
    module
  have e2 : Tω v2 = ρ2 • v2 := by
    rw [hv2, map_smul, map_sub, map_smul, hq, smul_comm ρ2]
    congr 1
    rw [← hsum, ← hprod]
    module
  have k1 : ∀ c ∈ w0 ^ r, L c v1 = 0 := by
    intro c hc
    rw [hv1, map_smul, map_sub, map_smul, hcomm, hv c hc, map_zero, smul_zero, sub_zero, smul_zero]
  have k2 : ∀ c ∈ w0 ^ r, L c v2 = 0 := by
    intro c hc
    rw [hv2, map_smul, map_sub, map_smul, hcomm, hv c hc, map_zero, smul_zero, sub_zero, smul_zero]
  have z1 : v1 = 0 := by
    obtain ⟨c, hc, hne⟩ := exists_mem_pow_forall_ne_zero p D R b w0 r hw k β
    obtain ⟨w, hwe, hweq⟩ := hlie v1 e1
    rw [hweq]
    refine sum_eq_zero_of_eigen (L c) Finset.univ w (fun i => β (b.t i c)) (fun i _ => hwe i c)
      (fun i _ => hne i) ?_
    rw [← hweq]; exact k1 c hc
  have z2 : v2 = 0 := by
    obtain ⟨r0, hr0⟩ := D.split
    have hr0k : ((r0 : k) - ρ1) * ((r0 : k) - ρ2) = 0 := by
      have : ((r0 ^ 2 - D.tr * r0 + D.nm : ℤ) : k) = 0 := (CharP.intCast_eq_zero_iff k p _).mpr hr0
      push_cast at this
      linear_combination this - (r0 : k) * hsum + hprod
    obtain ⟨r2, hr2⟩ : ∃ r2 : ℤ, (r2 : k) = ρ2 := by
      rcases mul_eq_zero.mp hr0k with h | h
      · exact ⟨D.tr - r0, by push_cast; rw [hρ2]; linear_combination -h⟩
      · exact ⟨r0, by linear_combination h⟩
    obtain ⟨c, hc, e, f, hcef⟩ := exists_mem_pow_add_eq_one p D R b w0 r hw k β r2 (by rw [hr2, hρ2, hρ1])
    have h := congrArg (fun g => g v2) (congrArg L hcef)
    simp only [map_add (f := _), map_mul, map_sub, map_one, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.one_apply, L_int, L_nat, k2 c hc] at h
    simp only [zero_add, add_zero] at h
    rw [← hTω, e2, hr2, map_smul, sub_self, hp, zero_smul, map_zero, add_zero] at h
    exact h.symm
  rw [hv12, z1, z2, add_zero]

end GlobalTheory.UPel.HT.EtLev.TanKill

namespace GlobalTheory.UPel.HT.EtLev.TanKill

open GlobalTheory.TanPtMod

theorem tan_eq_one_of_etPlace : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (v : epsPtR x ⟶ o.A), spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → (∀ c ∈ w0 ^ r, v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → v = 1 := by
  intro p _ D R _ b N w0 r hw S s o k _ _ x v hv0 hv
  set β : R →+* k := (Spec.preimage (x ≫ s)).hom with hβ
  have hx : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  let L : 𝓞 D.F →+* Module.End k (Tan x o.A) := (actEnd o.act).comp (algebraMap (𝓞 D.F) D.O)
  have hL : ∀ c (u : Tan x o.A), (L c u).hom = u.hom ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) := fun _ _ => rfl
  have hlie : ∀ u : Tan x o.A, L D.ω u = β b.ρ • u →
      ∃ w : Fin D.a → Tan x o.A, (∀ i c, L c (w i) = β (b.t i c) • w i) ∧ u = ∑ i, w i := by
    intro u hu
    obtain ⟨w, hw1, hw2⟩ := o.lie k β x hx u.hom
      ⟨(mem_tanSub_iff x o.A _).mp u.hom_mem, by
        have := congrArg (fun t : Tan x o.A => t.hom.left) hu
        simpa [hL, GrpTangentPt.epsScalePt_left] using this⟩
    have hmem : ∀ i, w i ∈ tanSub x o.A := fun i => (mem_tanSub_iff x o.A _).mpr (hw1 i 0).1
    refine ⟨fun i => Tan.mk (w i) (hmem i), fun i c => Tan.ext (Over.OverMorphism.ext ((hw1 i c).2)), ?_⟩
    refine Tan.ext ?_
    rw [Tan.hom_sum, hw2, List.prod_ofFn]
    rfl
  have hmv : v ∈ tanSub x o.A := (mem_tanSub_iff x o.A _).mpr hv0
  have := core D b w0 r hw β L hlie (Tan.mk v hmv) (fun c hc => Tan.ext (by rw [hL]; exact hv c hc))
  exact congrArg Tan.hom this

end GlobalTheory.UPel.HT.EtLev.TanKill
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimParabolicInductionCuspidalEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimParabolicInductionCuspidalEqOne
open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL

theorem degenerateWhittakerDim_zero_eq_whittakerDim {F : Type} [Field F] {r : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ψ : AddChar F ℂ) (τ : Representation ℂ (GL (Fin r) F) V) : whCut ψ τ 0 = whDim ψ τ := by
  have h : ∀ g : GL (Fin r) F, edgeSum (cutEdge 0) g = edgeSum supEdge g := by
    intro g
    unfold edgeSum
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      if_congr (by simp [cutEdge, supEdge]) rfl rfl
  unfold whCut whDim
  rw [show (fun g : GL (Fin r) F => ψ (edgeSum (cutEdge 0) g)) = fun g => ψ (edgeSum supEdge g) from
    funext fun g => by rw [h]]

theorem numBlockSetsOfTotalSize_zero_eq_one {r : ℕ} (b : Fin r → ℕ) : splitDoublingNBlock b 0 = 1 := by
  unfold splitDoublingNBlock
  rw [Finset.card_eq_one]
  refine ⟨∅, ?_⟩
  ext J
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.card_eq_zero, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (h1 hx)
    have : i ∈ Finset.univ.filter fun i => b i ∈ J := by simp [hx]
    rw [h2] at this
    simp at this
  · rintro rfl
    simp

theorem whDim_parInd_eq_one : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → whDim ψ (parInd b σ) = 1 := by
  intro F _ _ ψ hψ r V _ _ _ b σ hσ
  rw [← degenerateWhittakerDim_zero_eq_whittakerDim, GlobalTheory.T.degenerateWhittakerDim_parabolicInduction_cuspidal F ψ hψ r V b σ hσ 0 (Or.inr rfl), numBlockSetsOfTotalSize_zero_eq_one,
    GlobalTheory.T.levi_whittaker_eq_one_of_cuspidal F ψ hψ r V b σ hσ]

end GlobalTheory.FinGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimParabolicInductionCuspidalEqOneStatement
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerSpaceDim_parabolicInduction_cuspidal_eq_one : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → whDim ψ (parInd b σ) = 1 := by
  first | exact @GlobalTheory.FinGL.whDim_parInd_eq_one | exact GlobalTheory.FinGL.whDim_parInd_eq_one | (intros; apply GlobalTheory.FinGL.whDim_parInd_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLevelGroupAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LebesgueSelfdualForDotCharacter
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev

theorem isEtLevOver_eq_of_mkQ_eq {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ} {T : Over S}
    {l : D.La → (T ⟶ o.A)} (h : IsEtLevOver o w0 r l) {z z' : D.La}
    (hz : (wSub D w0 r).mkQ z = (wSub D w0 r).mkQ z') : l z = l z' := by
  have hm : z - z' ∈ wSub D w0 r := by
    rw [← Submodule.Quotient.mk_eq_zero]; simpa [sub_eq_zero] using hz
  have := h.1 z' (z - z')
  rw [add_sub_cancel, h.2.2.1 _ hm, _root_.mul_one] at this
  exact this

theorem isEtLevOver_levAct (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (T : Over S)
    (l : D.La → (T ⟶ o.A)) (g : LevGrp D w0 r) (h : IsEtLevOver o w0 r l) :
    IsEtLevOver o w0 r (fun y => l (levAct g y)) := by
  have hq := fun {z z' : D.La} (hz : (wSub D w0 r).mkQ z = (wSub D w0 r).mkQ z') =>
    isEtLevOver_eq_of_mkQ_eq h hz
  refine ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x => ⟨fun y hy => ?_, fun gg hgg => ?_⟩⟩
  · rw [← h.1]; apply hq
    simp only [mkQ_levAct, map_add (f := _)]
  · rw [← h.2.1]; apply hq
    simp only [mkQ_levAct, map_smul]
  · have : levAct g x ∈ wSub D w0 r := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, mkQ_levAct,
        Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hx, map_zero]
    exact h.2.2.1 _ this
  · have h1 := (h.2.2.2 k x).1 _ hy
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, mkQ_levAct] at h1
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    exact (LinearEquiv.map_eq_zero_iff g).1 h1
  · obtain ⟨y, hy⟩ := (h.2.2.2 k x).2 gg hgg
    refine ⟨levAct g.symm y, ?_⟩
    rw [← hy]; congr 1; apply hq
    simp only [mkQ_levAct, LinearEquiv.apply_symm_apply]

end GlobalTheory.UPel.HT.EtLev
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_level_group_action : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (T : Over S) (l : D.La → (T ⟶ o.A)) (g : LevGrp D w0 r), IsEtLevOver o w0 r l → IsEtLevOver o w0 r (fun y => l (levAct g y)) := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.isEtLevOver_levAct) | (exact GlobalTheory.UPel.HT.EtLev.isEtLevOver_levAct) | (intros; apply GlobalTheory.UPel.HT.EtLev.isEtLevOver_levAct <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupChartIntegralAdditiveSeriesEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupChartIntegralAdditiveSeriesEqZero
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.IntAdd

theorem formalGroupLawCoboundaryOne_map_coefficients {R S : Type} [CommRing R] [CommRing S] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (h : ∀ i, constantCoeff (μ i) = 0) (r : R →+* S)
    (f : MvPowerSeries (Fin d) R) :
    map r (cob1 μ f) = cob1 (fun i => map r (μ i)) (map r f) := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero h),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem eq_zero_of_cob1_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ s : MvPowerSeries (Fin d) O, cob1 (up E c.μ) (map (algebraMap O E) s) = 0 → s = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c E _ _ hF s hs
  have h0 : cob1 c.μ s = 0 := by
    have hm := formalGroupLawCoboundaryOne_map_coefficients c.μ c.isLaw.const (algebraMap O E) s
    have hup : (fun i => map (algebraMap O E) (c.μ i)) = up E c.μ := rfl
    rw [hup, hs] at hm
    ext α
    apply hF.inj
    have := congrArg (coeff α) hm
    rw [coeff_map] at this
    rw [this]; simp
  have hp : (p : O) ≠ 0 := by
    intro h
    exact one_ne_zero (hF.sat 1 (by rw [h, zero_mul]))
  have hev : ∀ n, c.ev n s = 0 := fun n =>
    G.eq_zero_of_cobOne_eq_zero hp n (by
      rw [← (Chart.ev₂_eval p O G d c n s).2.2.2, h0, map_zero])
  ext α
  rw [coeff_zero]
  refine hF.eq_zero_of_forall_pow_dvd fun m => ?_
  obtain ⟨n, hn⟩ := c.ker m (α.degree + 1)
  exact hn s (hev n) α (Nat.lt_succ_self _)

end GlobalTheory.QLog.IntAdd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupChartIntegralAdditiveSeriesEqZeroStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroupChart_integral_additive_series_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ s : MvPowerSeries (Fin d) O, cob1 (up E c.μ) (map (algebraMap O E) s) = 0 → s = 0 := by
  first | exact @GlobalTheory.QLog.IntAdd.eq_zero_of_cob1_eq_zero | exact GlobalTheory.QLog.IntAdd.eq_zero_of_cob1_eq_zero | (intros; apply GlobalTheory.QLog.IntAdd.eq_zero_of_cob1_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogReduces
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogReduces
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

open CategoryTheory TensorProduct MvPowerSeries in
private lemma mem_quasiLog_iff (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : _root_.GlobalTheory.Katz.IsLaw μ)
    (f : MvPowerSeries (Fin d) (_root_.GlobalTheory.Katz.Fr p k)) :
    f ∈ _root_.GlobalTheory.Katz.quasiLog p h ↔
      f ∈ _root_.GlobalTheory.Katz.quasiInt p k (Fin d) ∧
        _root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f ∈
          _root_.GlobalTheory.Katz.intBy p k (Fin d ⊕ Fin d) 1 := by
  unfold _root_.GlobalTheory.Katz.quasiLog
  exact Iff.rfl

open CategoryTheory TensorProduct MvPowerSeries in
private lemma exists_lin_eq_algebraMap_of_mem_quasiInt (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    {d : ℕ} {f : MvPowerSeries (Fin d) (_root_.GlobalTheory.Katz.Fr p k)}
    (hf : f ∈ _root_.GlobalTheory.Katz.quasiInt p k (Fin d)) (i : Fin d) :
    ∃ a, _root_.GlobalTheory.Katz.lin f i = algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) a := by
  obtain ⟨a, ha⟩ := hf (Finsupp.single i 1) i
  exact ⟨a, by simpa [_root_.GlobalTheory.Katz.lin] using ha⟩

open CategoryTheory TensorProduct MvPowerSeries in
private lemma isCoc_of_red_cob1_quasiInt (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k)
    (h : _root_.GlobalTheory.Katz.IsLaw μ) (f : MvPowerSeries (Fin d) (_root_.GlobalTheory.Katz.Fr p k))
    (hf : f ∈ _root_.GlobalTheory.Katz.quasiInt p k (Fin d))
    (c : MvPowerSeries (Fin d ⊕ Fin d) k)
    (hc : _root_.GlobalTheory.Katz.Red p
      (_root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f) c) :
    _root_.GlobalTheory.Katz.IsCoc μ c := by
  obtain ⟨-, huniq, -, hadd, -, hdivp, -⟩ := _root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d)
  obtain ⟨-, huniq3, -, -, -, hdivp3, -⟩ :=
    _root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d ⊕ Fin d)
  obtain ⟨htwo, hswap⟩ := _root_.GlobalTheory.Katz.cob2_cob1_lift_mem_intBy_and_swap_sub_mem p k d μ h f hf
  obtain ⟨hcomm, -⟩ := _root_.GlobalTheory.Katz.red_coboundaries p k d μ
    h.const
  obtain ⟨hred2, hredswap⟩ := hcomm _ c hc
  unfold _root_.GlobalTheory.Katz.IsCoc
  refine ⟨huniq3 _ _ _ hred2 ((hdivp3 _).1 htwo), ?_⟩
  exact sub_eq_zero.1 (huniq _ _ _ (hadd _ _ _ _ hredswap hc).2 ((hdivp _).1 hswap))


open CategoryTheory TensorProduct MvPowerSeries in
theorem _root_.GlobalTheory.quasiLog_reduces : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : _root_.GlobalTheory.Katz.IsLaw μ), (∀ f ∈ _root_.GlobalTheory.Katz.quasiLog p h, ∃ c w, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f) c ∧ _root_.GlobalTheory.Katz.RedV p (_root_.GlobalTheory.Katz.lin f) w) ∧ ∀ f ∈ _root_.GlobalTheory.Katz.quasiLog p h, ∀ c, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) f) c → _root_.GlobalTheory.Katz.IsCoc μ c := by
  intro p _ k _ _ _ d μ h
  refine ⟨fun f hf => ?_, fun f hf c hc => ?_⟩
  · obtain ⟨hint, hcob⟩ := (mem_quasiLog_iff p k d μ h f).1 hf
    obtain ⟨c, hc⟩ := ((_root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d)).1 _).1 hcob
    choose a ha using exists_lin_eq_algebraMap_of_mem_quasiInt p k hint
    exact ⟨c, fun i => WittVector.constantCoeff (a i), hc, fun i => ⟨a i, ha i, rfl⟩⟩
  · exact isCoc_of_red_cob1_quasiInt p k d μ h f
      ((mem_quasiLog_iff p k d μ h f).1 hf).1 c hc

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogReducesStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLog_reduces_to_cocycle : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ), (∀ f ∈ quasiLog p h, ∃ c w, Red p (cob1 (fun i => Katz.lift p (μ i)) f) c ∧ RedV p (lin f) w) ∧ ∀ f ∈ quasiLog p h, ∀ c, Red p (cob1 (fun i => Katz.lift p (μ i)) f) c → IsCoc μ c := by
  first | exact @GlobalTheory.quasiLog_reduces | exact GlobalTheory.quasiLog_reduces | (intros; apply GlobalTheory.quasiLog_reduces <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtLevRelExistsUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtLevRelExistsUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

theorem exists_unique_quotAut {O M G : Type*} [Ring O] [AddCommGroup M] [Module O M] [Group G]
    (W : Submodule O M) (act : O → G → G) (L L' : M → G)
    (hadd : ∀ a b, L (a + b) = L a * L b) (hadd' : ∀ a b, L' (a + b) = L' a * L' b)
    (hsm : ∀ (c : O) a, L (c • a) = act c (L a)) (hsm' : ∀ (c : O) a, L' (c • a) = act c (L' a))
    (hker : ∀ a, L a = 1 ↔ a ∈ W) (hker' : ∀ a, L' a = 1 ↔ a ∈ W)
    (hsurj : ∀ a, ∃ b, L b = L' a) (hsurj' : ∀ a, ∃ b, L' b = L a) :
    ∃! g : (M ⧸ W) ≃ₗ[O] (M ⧸ W),
      ∀ y, L (Function.surjInv (Submodule.mkQ_surjective W) (g (W.mkQ y))) = L' y := by
  have key : ∀ {L : M → G}, (∀ a b, L (a + b) = L a * L b) → (∀ a, L a = 1 ↔ a ∈ W) →
      ∀ a b, L a = L b ↔ W.mkQ a = W.mkQ b := by
    intro L hadd hker a b
    have h : L a = L (a - b) * L b := by rw [← hadd, sub_add_cancel]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hker, h]
    constructor
    · intro e
      exact mul_right_cancel (e.trans (_root_.one_mul _).symm)
    · intro e
      rw [e, _root_.one_mul]
  have eq := key hadd hker
  choose z hz using hsurj
  let f₀ : M →ₗ[O] M ⧸ W :=
    { toFun := fun y => W.mkQ (z y)
      map_add' := fun a b => by
        rw [← map_add (f := _), ← eq, hadd, hz, hz, hz, hadd']
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← LinearMap.map_smul, ← eq, hsm, hz, hz, hsm'] }
  have hf₀ : W ≤ LinearMap.ker f₀ := by
    intro y hy
    rw [LinearMap.mem_ker]
    show W.mkQ (z y) = 0
    rw [← map_zero W.mkQ, ← eq, hz, (hker' y).2 hy, (hker 0).2 W.zero_mem]
  let f := W.liftQ f₀ hf₀
  have hf : ∀ y, f (W.mkQ y) = W.mkQ (z y) := fun y => rfl
  have bij : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro q hq
      obtain ⟨y, rfl⟩ := W.mkQ_surjective q
      rw [hf, ← map_zero W.mkQ, ← eq, hz, (hker 0).2 W.zero_mem, hker'] at hq
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hq
    · intro q
      obtain ⟨a, rfl⟩ := W.mkQ_surjective q
      obtain ⟨y, hy⟩ := hsurj' a
      exact ⟨W.mkQ y, by rw [hf, ← eq, hz, hy]⟩
  refine ⟨LinearEquiv.ofBijective f bij, ?_, ?_⟩
  · intro y
    rw [← hz y, eq, Function.surjInv_eq (Submodule.mkQ_surjective W)]
    rfl
  · intro g hg
    refine LinearEquiv.ext fun q => ?_
    obtain ⟨y, rfl⟩ := W.mkQ_surjective q
    rw [LinearEquiv.ofBijective_apply, hf, ← Function.surjInv_eq (Submodule.mkQ_surjective W) (g (W.mkQ y)),
      ← eq, hg y, hz]

theorem etLev_rel_existsUnique (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (k : Type) [Field k]
    [IsAlgClosed k] (x : Sp k ⟶ S) (l l' : D.La → (Over.mk x ⟶ o.A)) :
    IsEtLevOver o w0 r l → IsEtLevOver o w0 r l' → ∃! g : LevGrp D w0 r, ∀ y, l (levAct g y) = l' y := by
  intro hl hl'
  obtain ⟨hinj, hsur⟩ := hl.2.2.2 k (𝟙 _)
  obtain ⟨hinj', hsur'⟩ := hl'.2.2.2 k (𝟙 _)
  have canc : ∀ u v : Over.mk x ⟶ o.A,
      (Over.homMk (𝟙 _) rfl : Over.mk (𝟙 (Sp k) ≫ (Over.mk x).hom) ⟶ Over.mk x) ≫ u =
        (Over.homMk (𝟙 _) rfl : Over.mk (𝟙 (Sp k) ≫ (Over.mk x).hom) ⟶ Over.mk x) ≫ v → u = v := by
    intro u v h
    ext
    have := congrArg CommaMorphism.left h
    simpa using this
  have killed : ∀ (l₁ : D.La → (Over.mk x ⟶ o.A)), IsEtLevOver o w0 r l₁ → ∀ a, ∀ c ∈ w0 ^ r,
      ((Over.homMk (𝟙 _) rfl : Over.mk (𝟙 (Sp k) ≫ (Over.mk x).hom) ⟶ Over.mk x) ≫ l₁ a) ≫
        o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro l₁ h₁ a c hc
    rw [Category.assoc, ← h₁.2.1, h₁.2.2.1 _ (Submodule.subset_span ⟨c, hc, a, rfl⟩), comp_one]
  exact exists_unique_quotAut (wSub D w0 r) (fun c g => g ≫ o.act.act c) l l' hl.1 hl'.1 hl.2.1 hl'.2.1
    (fun a => ⟨fun h => hinj a (by rw [h, comp_one]), fun h => hl.2.2.1 a h⟩)
    (fun a => ⟨fun h => hinj' a (by rw [h, comp_one]), fun h => hl'.2.2.1 a h⟩)
    (fun a => by
      obtain ⟨y, hy⟩ := hsur _ (killed l' hl' a)
      exact ⟨y, canc _ _ hy⟩)
    (fun a => by
      obtain ⟨y, hy⟩ := hsur' _ (killed l hl a)
      exact ⟨y, canc _ _ hy⟩)

end GlobalTheory.UPel.HT.EtLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtLevRelExistsUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_levGrp_of_isEtLevOver : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (l l' : D.La → (Over.mk x ⟶ o.A)), IsEtLevOver o w0 r l → IsEtLevOver o w0 r l' → ∃! g : LevGrp D w0 r, ∀ y, l (levAct g y) = l' y := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.etLev_rel_existsUnique) | (exact GlobalTheory.UPel.HT.EtLev.etLev_rel_existsUnique) | (intros; apply GlobalTheory.UPel.HT.EtLev.etLev_rel_existsUnique  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IterateLinearPart
set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace GlobalTheory.LinearPartIteration

variable {R : Type} [CommRing R] {d : ℕ}

def part (F : MvPowerSeries (Fin d) R) (j : Fin d) : MvPowerSeries (Fin d) R :=
  fun α => if ∀ k < j, α k = 0 then coeff (α + Finsupp.single j 1) F else 0

theorem coeff_part (F : MvPowerSeries (Fin d) R) (j : Fin d) (α : Fin d →₀ ℕ) :
    coeff α (part F j) = if ∀ k < j, α k = 0 then coeff (α + Finsupp.single j 1) F else 0 := rfl

theorem constantCoeff_part (F : MvPowerSeries (Fin d) R) (j : Fin d) :
    constantCoeff (part F j) = coeff (Finsupp.single j 1) F := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_part]
  simp

theorem coeff_X_mul_part (F : MvPowerSeries (Fin d) R) (j : Fin d) (β : Fin d →₀ ℕ) :
    coeff β (X j * part F j) = if β j ≠ 0 ∧ ∀ k < j, β k = 0 then coeff β F else 0 := by
  classical
  rw [X_def, coeff_monomial_mul, one_mul, coeff_part]
  by_cases h : β j = 0
  · rw [if_neg, if_neg]
    · simp [h]
    · rw [Finsupp.single_le_iff]; omega
  · have hle : Finsupp.single j 1 ≤ β := by rw [Finsupp.single_le_iff]; omega
    rw [if_pos hle, tsub_add_cancel_of_le hle]
    have : (∀ k < j, (β - Finsupp.single j 1 : Fin d →₀ ℕ) k = 0) ↔ (β j ≠ 0 ∧ ∀ k < j, β k = 0) := by
      constructor
      · intro H
        refine ⟨h, fun k hk => ?_⟩
        have := H k hk
        rwa [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hk.ne, Nat.sub_zero] at this
      · intro H k hk
        rw [Finsupp.tsub_apply, H.2 k hk, Nat.zero_sub]
    simp only [this]

theorem eq_const_add_sum (F : MvPowerSeries (Fin d) R) :
    F = C (constantCoeff F) + ∑ j, X j * part F j := by
  classical
  ext β
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum, coeff_C]
  simp only [coeff_X_mul_part]
  by_cases hβ : β = 0
  · subst hβ
    simp
  · rw [if_neg hβ, zero_add]
    have hne : β.support.Nonempty := Finsupp.support_nonempty_iff.2 hβ
    have h0 : β (β.support.min' hne) ≠ 0 := Finsupp.mem_support_iff.1 (β.support.min'_mem hne)
    have h1 : ∀ k < β.support.min' hne, β k = 0 := fun k hk => by
      by_contra hk0
      exact absurd (β.support.min'_le k (Finsupp.mem_support_iff.2 hk0)) (not_le.2 hk)
    rw [Finset.sum_eq_single (β.support.min' hne), if_pos ⟨h0, h1⟩]
    · intro j _ hj
      rw [if_neg]
      rintro ⟨h2, h3⟩
      rcases lt_or_gt_of_ne hj with h | h
      · exact h2 (h1 j h)
      · exact h0 (h3 _ h)
    · simp

theorem iterate_linear_part : ∀ (p : ℕ) [Fact (Nat.Prime p)] (R : Type) [inst : CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ (i : Fin d), (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d ⊕ Fin d) R → R) (μ i) = (0 : R)) → ((GlobalTheory.Katz.op μ (fun (i : Fin d) ↦ MvPowerSeries.X i) fun (x : Fin d) ↦ (0 : MvPowerSeries (Fin d) R)) = fun (i : Fin d) ↦ MvPowerSeries.X i) → (∀ (i : Fin d), GlobalTheory.Katz.swap (μ i) = μ i) → ∀ (u : Fin d → R) (F : MvPowerSeries (Fin d) R), ∃ (r : R), (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) R → R) ((GlobalTheory.LawDer.invDer μ u)^[p] F) - ∑ j : Fin d, (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) R → R) ((GlobalTheory.LawDer.invDer μ u)^[p] (MvPowerSeries.X j)) * (MvPowerSeries.coeff fun₀ | j => (1 : ℕ) : MvPowerSeries (Fin d) R → R) F = (↑p : R) * r := by
  intro p hp R _ d μ h0 h1 _ u F
  obtain ⟨hadd, hsmul, hC⟩ := GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear R d μ h0 u
  let D : MvPowerSeries (Fin d) R →ₗ[R] MvPowerSeries (Fin d) R :=
    { toFun := GlobalTheory.LawDer.invDer μ u, map_add' := hadd, map_smul' := hsmul }
  have hD : ∀ G, (GlobalTheory.LawDer.invDer μ u)^[p] G = (D ^ p) G := fun G => by
    rw [Module.End.pow_apply]; rfl
  have hDC : ∀ a : R, (D ^ p) (C a) = 0 := fun a => by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hp.out.ne_zero
    rw [hn, pow_succ, Module.End.mul_apply, show D (C a) = 0 from hC a, map_zero]
  have key : ∀ j : Fin d, ∃ r : R, constantCoeff ((D ^ p)
      (X j * (part F j - C (coeff (Finsupp.single j 1) F)))) = p * r := fun j => by
    rw [← hD]
    exact GlobalTheory.T.constantCoeff_iterate_p_invariantDerivation_mul p R d μ h0 h1 u _ _ (by simp) (by simp [constantCoeff_part])
  choose r hr using key
  refine ⟨∑ j, r j, ?_⟩
  have hF : constantCoeff ((D ^ p) F) = ∑ j, constantCoeff ((D ^ p) (X j * part F j)) := by
    conv_lhs => rw [eq_const_add_sum F]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), hDC, zero_add, map_sum, map_sum]
  simp only [hD]
  rw [hF, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hr j, mul_sub, map_sub, map_sub, mul_comm (X j) (C _), ← smul_eq_C_mul, map_smul,
    ← coeff_zero_eq_constantCoeff_apply ((_ : R) • _), map_smul, coeff_zero_eq_constantCoeff_apply,
    smul_eq_mul, mul_comm (constantCoeff _)]

end GlobalTheory.LinearPartIteration
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationLinear
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LawDer.ConstLin

variable {R : Type} [CommRing R] {d : ℕ}

end GlobalTheory.LawDer.ConstLin

theorem GlobalTheory.LawDer.constantCoeff_iterate_invDer_sub_linear :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = (fun i => X i) → (∀ i, swap (μ i) = μ i) → ∀ (u : Fin d → R) (F : MvPowerSeries (Fin d) R), ∃ r : R, constantCoeff ((invDer μ u)^[p] F) - ∑ j, constantCoeff ((invDer μ u)^[p] (X j)) * coeff (Finsupp.single j 1) F = p * r := by
  first
  | exact @_root_.GlobalTheory.LinearPartIteration.iterate_linear_part
  | exact _root_.GlobalTheory.LinearPartIteration.iterate_linear_part
  | (apply _root_.GlobalTheory.LinearPartIteration.iterate_linear_part <;> assumption)
  | (intros; apply _root_.GlobalTheory.LinearPartIteration.iterate_linear_part <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LinearPartIteration.iterate_linear_part <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LinearPartIteration.iterate_linear_part ..)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationLinearStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_iterate_invariant_derivation_linear : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = (fun i => X i) → (∀ i, swap (μ i) = μ i) → ∀ (u : Fin d → R) (F : MvPowerSeries (Fin d) R), ∃ r : R, constantCoeff ((invDer μ u)^[p] F) - ∑ j, constantCoeff ((invDer μ u)^[p] (X j)) * coeff (Finsupp.single j 1) F = p * r := by
  first | exact @GlobalTheory.LawDer.constantCoeff_iterate_invDer_sub_linear | exact GlobalTheory.LawDer.constantCoeff_iterate_invDer_sub_linear | (intros; apply GlobalTheory.LawDer.constantCoeff_iterate_invDer_sub_linear <;> assumption)
end
end
