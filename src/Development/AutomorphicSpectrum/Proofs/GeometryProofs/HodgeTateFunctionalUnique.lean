module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalUnique
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalUnique
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.HT

private lemma valAt_sub' {B : Type} [CommRing B] {X : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valAt y U h (a - b) = valAt y U h a - valAt y U h b := by
  simp [valAt, map_sub]

private lemma exists_dual_of_dvd {R : Type} [CommRing R] [IsDomain R] {L : Type} [AddCommGroup L]
    [Module R L] (c : R) (hc : c ≠ 0) (d : Module.Dual R L) (h : ∀ e, c ∣ d e) :
    ∃ u : Module.Dual R L, d = c • u := by
  choose f hf using h
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    apply mul_left_cancel₀ hc
    rw [mul_add, ← hf, ← hf, ← hf, map_add (f := _)]
  · intro r x
    apply mul_left_cancel₀ hc
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← hf, map_smul, smul_eq_mul, hf x]
    ring
  · ext e
    show d e = c • f e
    rw [hf e, smul_eq_mul]

theorem isHT_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → (N : R) ≠ 0 → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M N χ w → (Γ.IsHT i M N χ w' ↔ ∃ u : Module.Dual R L, w' = w + N • u) := by
  intro R _ _ T _ _ Γ S G _ _ x N i hT hsm hN L _ _ M χ w w' hw
  obtain ⟨s, hs, hsv⟩ := hw
  constructor
  · rintro ⟨s', hs', hsv'⟩
    have hss : s' = s := by
      have h0 := GlobalTheory.T.section_eq_zero_of_values R T Γ ⊤ (s' - s) (fun t h => by
        rw [valAt_sub', hs' t, hs t, sub_self])
      exact sub_eq_zero.mp h0
    subst hss
    have hdvd : ∀ e, (N : R) ∣ w' e - w e := by
      intro e
      obtain ⟨v, hv1, hv2, hv3⟩ := hsv e
      obtain ⟨v', hv1', hv2', hv3'⟩ := hsv' e
      have hvv : v' = v := (GlobalTheory.T.existsUnique_tangent_dual_number R T Γ S G x N i hT L M e).unique ⟨hv1', hv2'⟩ ⟨hv1, hv2⟩
      subst hvv
      rw [hv3] at hv3'
      have h1 : Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e) = Ideal.Quotient.mk (Ideal.span {(N : R)}) (w' e) := by
        simpa using congrArg TrivSqZeroExt.snd hv3'
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
      exact h1.symm
    obtain ⟨u, hu⟩ := exists_dual_of_dvd (N : R) hN (w' - w) (fun e => by simpa using hdvd e)
    refine ⟨u, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul R, ← hu]
    abel
  · rintro ⟨u, rfl⟩
    refine ⟨s, hs, fun e => ?_⟩
    obtain ⟨v, hv1, hv2, hv3⟩ := hsv e
    refine ⟨v, hv1, hv2, ?_⟩
    have h0 : Ideal.Quotient.mk (Ideal.span {(N : R)}) ((N • u) e) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, ← Nat.cast_smul_eq_nsmul R,
        LinearMap.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
    rw [hv3, LinearMap.add_apply, map_add (f := _), h0, add_zero]

end GlobalTheory.CompanionTheory.Ar.BT.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalUniqueStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
alias GlobalTheory.T.hodge_tate_functional_unique_mod_smul := GlobalTheory.CompanionTheory.Ar.BT.HT.isHT_iff
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeVectorBundlePullback
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeVectorBundlePullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LatPull

theorem isVBOn_pull :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E]
      [Module Ω E] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X)
      (i : Ω →+* Ω') (E' : Type) [AddCommGroup E'] [Module Ω' E'] (j : E →+ E') (L : Lat ξ E) (T : Set (Cpt ξ))
      (r : ℕ) (V : Submodule Ω E), Dominates ξ' ξ f i → (∀ (a : Ω) e, j (a • e) = i a • j e) →
      (∀ (n : ℕ) (b : Fin n → E), LinearIndependent Ω b → LinearIndependent Ω' fun k => j (b k)) →
      L.IsVBOn T r V →
      (L.pull ξ' f j).IsVBOn {p' | ∃ h : genPt ξ ⤳ f p'.1, (⟨f p'.1, h⟩ : Cpt ξ) ∈ T} r
        (Submodule.span Ω' (j '' V)) := by
  intro X Ω _ ξ E _ _ X' Ω' _ ξ' f i E' _ _ j L T r V hd hj hli hvb p' hp'
  obtain ⟨h, hT⟩ := hp'
  obtain ⟨U, hU, b, hb, hfr⟩ := hvb _ hT
  have hind' : LinearIndependent Ω' fun k => j (b k) := hli r b (hfr _ hT hU).1
  have hbV : ∀ k, b k ∈ V := fun k => hb ▸ Submodule.subset_span ⟨k, rfl⟩
  have key : ∀ v ∈ Submodule.span Ω (Set.range b),
      j v ∈ Submodule.span Ω' (Set.range fun k => j (b k)) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact add_mem hx hy
    | smul a x _ hx =>
      rw [hj]
      exact Submodule.smul_mem _ _ hx
  refine ⟨f ⁻¹ᵁ U, hU, fun k => j (b k), ?_, ?_⟩
  · apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨b k, hbV k, rfl⟩
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨v, hv, rfl⟩
      exact key v (by rw [hb]; exact hv)
  · rintro q' ⟨h', hT'⟩ hq'
    refine ⟨hind', ?_⟩
    have hL := (hfr _ hT' hq').2
    obtain ⟨h2, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q'
    have key' : ∀ e ∈ Submodule.span (regAt ξ ⟨f q'.1, h'⟩) (Set.range b),
        j e ∈ Submodule.span (regAt ξ' q') (Set.range fun k => j (b k)) := by
      intro e he
      induction he using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        exact Submodule.subset_span ⟨k, rfl⟩
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add (f := _)]
        exact add_mem hx hy
      | smul a x _ hx =>
        have e1 : j (a • x) = (⟨i a, hreg a a.2⟩ : regAt ξ' q') • j x := hj a x
        rw [e1]
        exact Submodule.smul_mem _ _ hx
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨h3, e, he, rfl⟩
      exact key' e (by rw [← hL]; exact he)
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      refine Submodule.subset_span ⟨h', b k, ?_, rfl⟩
      rw [hL]
      exact Submodule.subset_span ⟨k, rfl⟩

end GlobalTheory.CompanionTheory.Ar.LatPull
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeVectorBundlePullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.lattice_vector_bundle_pullback := GlobalTheory.CompanionTheory.Ar.LatPull.isVBOn_pull
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIntegralAdeleLimitCompatibleIntSystem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem eigSp_comp_ringEquiv : ∀ (R E O : Type) [CommRing R] [AddCommGroup E] [Module R E] [CommRing O] (ρ : O →+* Module.End R E) (s : O ≃+* O) (τ : O →+* R), eigSp (ρ.comp s.toRingHom) (τ.comp s.toRingHom) = eigSp ρ τ := by
  intro R E O _ _ _ _ ρ s τ
  unfold eigSp
  exact s.surjective.iInf_comp (fun b => LinearMap.ker (ρ b - τ b • LinearMap.id))

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTrdegFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTrdegFormula
open GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.FlagTrdeg

open scoped IntermediateField.algebraAdjoinAdjoin

theorem card_below_diagonal (n : ℕ) :
    Fintype.card {lk : Fin n × Fin n // lk.2 < lk.1} = n * (n - 1) / 2 := by
  rw [show Fintype.card {lk : Fin n × Fin n // lk.2 < lk.1} = Fintype.card (Σ a : Fin n, {b : Fin n // b < a}) from
    Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun a b : Fin n => b < a), Fintype.card_sigma]
  have h : ∀ a : Fin n, Fintype.card {b : Fin n // b < a} = a := by
    intro a
    rw [Fintype.card_subtype]
    have e : (Finset.univ.filter fun b : Fin n => b < a) = Finset.Iio a := by
      ext b
      simp
    rw [e, Fin.card_Iio]
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

theorem isTranscendenceBasis_of_adjoin {k K ι : Type} [Field k] [Field K] [Algebra k K] {x : ι → K}
    (hx : AlgebraicIndependent k x)
    (h : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range x)) K) :
    IsTranscendenceBasis k x := by
  rw [hx.isTranscendenceBasis_iff_isAlgebraic]
  exact (IsFractionRing.comap_isAlgebraic_iff (A := ↥(Algebra.adjoin k (Set.range x)))
    (K := ↥(IntermediateField.adjoin k (Set.range x))) (C := K)).2 h

theorem trdeg_of_isGenericFlag (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (E : Type) [AddCommGroup E]
    [Module Ω₀ E] (E' : Type) [AddCommGroup E'] [Module Ω E'] (j : E →+ E') (S : Type) [Fintype S]
    (r : S → ℕ) (V : S → Submodule Ω₀ E) (b₀ : ∀ σ, Fin (r σ) → E') (d : ℕ)
    (hg : IsGenericFlag (Ω' := Ω) j V b₀ d) :
    Algebra.trdeg Ω₀ Ω = ((∑ σ, r σ * (r σ - 1) / 2 : ℕ) : Cardinal) := by
  obtain ⟨c, u, -, -, -, -, hdiag, hup, -, hind, hd, hfr⟩ := hg
  have heq : IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨⟨σ, l, k⟩, rfl⟩
      rcases lt_trichotomy k l with hkl | hkl | hkl
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, ⟨(l, k), hkl⟩⟩, rfl⟩
      · subst hkl
        simp only [hdiag]
        exact one_mem _
      · simp only [hup σ l k hkl]
        exact zero_mem _
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨⟨σ, ⟨⟨l, k⟩, hkl⟩⟩, rfl⟩
      exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, (l, k)⟩, rfl⟩
  haveI : Module.Finite (IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) Ω :=
    Module.finite_of_finrank_pos (by rw [hfr]; exact hd)
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) Ω :=
    Algebra.IsAlgebraic.of_finite _ _
  rw [heq] at halg
  have hb := isTranscendenceBasis_of_adjoin hind halg
  rw [← hb.cardinalMk_eq_trdeg, Cardinal.mk_fintype, Fintype.card_sigma]
  simp only [card_below_diagonal]

end GlobalTheory.CompanionTheory.Ar.FlagTrdeg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTrdegFormulaStatement
open GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.generic_flag_trdeg_formula := GlobalTheory.CompanionTheory.Ar.FlagTrdeg.trdeg_of_isGenericFlag
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerDegree
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerDegree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TensDeg

lemma zpow_mem_of_unit {Ω : Type} [Field Ω] (R : Subring Ω) {u : Ω} (h : u ∈ R) (h' : u⁻¹ ∈ R) (n : ℤ) :
    u ^ n ∈ R := by
  cases n with
  | ofNat n => simpa using pow_mem h n
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow]
    exact pow_mem h' _

lemma exists_unit_of_span_eq {Ω : Type} [Field Ω] (R : Subring Ω) {s t : Ω} (ht : t ≠ 0)
    (h : Submodule.span R {s} = Submodule.span R {t}) : ∃ u, u ∈ R ∧ u⁻¹ ∈ R ∧ s = u * t := by
  have h1 : s ∈ Submodule.span R {t} := h ▸ Submodule.mem_span_singleton_self s
  have h2 : t ∈ Submodule.span R {s} := h ▸ Submodule.mem_span_singleton_self t
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 h2
  have ha' : (a : Ω) * t = s := ha
  have hb' : (b : Ω) * s = t := hb
  have hba : (b : Ω) * a = 1 := by
    apply mul_right_cancel₀ ht
    rw [_root_.mul_assoc, ha', hb', _root_.one_mul]
  refine ⟨a, a.2, ?_, ha'.symm⟩
  rw [inv_eq_of_mul_eq_one_left hba]
  exact b.2

lemma zpow_finset_sum {Ω I : Type} [Field Ω] {x : Ω} (hx : x ≠ 0) (s : Finset I) (f : I → ℤ) :
    x ^ (∑ i ∈ s, f i) = ∏ i ∈ s, x ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ hx, ih]

end GlobalTheory.CompanionTheory.Ar.TensDeg


open GlobalTheory.CompanionTheory.Ar.TensDeg in
theorem GlobalTheory.CompanionTheory.Ar.Lat.tens_isDegOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (I : Type) [Fintype I] (Λ : I → Lat ξ Ω) (T : Set (Cpt ξ)) (d : I → K → ℤ) (e : I → Ω), (∀ i, (Λ i).IsDegOn T y (d i) (e i)) → ∀ a : I → ℤ, (Lat.tens Λ a).IsDegOn T y (∑ i, a i • d i) (∏ i, e i ^ a i) := by
  intro X Ω _ ξ K _ J y I _ Λ T d e h a
  have he : ∀ i, e i ≠ 0 := fun i => (h i).1
  refine ⟨Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (he i), ?_⟩
  intro p hp c hc
  have hc0 : ∏ k, y ⟨k, c k⟩ ≠ 0 := hc.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc0 k (Finset.mem_univ k)
  let g : I → Ω := fun i => (∏ k, y ⟨k, c k⟩ ^ d i k) • e i
  have hg0 : ∀ i, g i ≠ 0 := fun i =>
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) (he i)
  have hgen : ∀ i, (Λ i).IsGenAt p (g i) := fun i => ⟨hg0 i, (h i).2 p hp c hc⟩
  have hG : (∏ k, y ⟨k, c k⟩ ^ (∑ i, a i • d i) k) • (∏ i, e i ^ a i) = ∏ i, g i ^ a i := by
    simp only [g, smul_eq_mul, mul_zpow, Finset.prod_mul_distrib]
    congr 1
    simp_rw [← Finset.prod_zpow]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Finset.sum_apply, zpow_finset_sum (hy k)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, zpow_mul]
  rw [hG]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro t ⟨s, hs, rfl⟩
    choose u hu hu' hsu using fun i =>
      exists_unit_of_span_eq (regAt ξ p) (hg0 i) ((hs i).2.symm.trans (hgen i).2)
    have hm : ∏ i, u i ^ a i ∈ regAt ξ p :=
      prod_mem fun i _ => zpow_mem_of_unit _ (hu i) (hu' i) _
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hm⟩, ?_⟩
    show (∏ i, u i ^ a i) * ∏ i, g i ^ a i = ∏ i, s i ^ a i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hsu i, mul_zpow]
  · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 (Submodule.subset_span ⟨g, hgen, rfl⟩))
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerDegreeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.lattice_tensor_power_degree := GlobalTheory.CompanionTheory.Ar.Lat.tens_isDegOn
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerLineBundle
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerLineBundle
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace LatTens

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem div_mem_of_isGenAt {Λ : Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : Λ.IsGenAt p s)
    (ht : Λ.IsGenAt p t) : s / t ∈ regAt ξ p := by
  obtain ⟨_, hsΛ⟩ := hs
  obtain ⟨ht0, htΛ⟩ := ht
  have hmem : s ∈ Submodule.span (regAt ξ p) ({t} : Set Ω) := by
    rw [← htΛ, hsΛ]
    exact Submodule.mem_span_singleton_self s
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
  have hr' : (r : Ω) * t = s := by
    exact hr
  rw [← hr', mul_div_assoc, div_self ht0, _root_.mul_one]
  exact r.2

theorem zpow_mem_of_inv_mem {R : Subring Ω} {u : Ω} (h : u ∈ R) (h' : u⁻¹ ∈ R) (a : ℤ) : u ^ a ∈ R := by
  cases a with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using pow_mem h n
  | negSucc n => simpa only [zpow_negSucc, inv_pow] using pow_mem h' (n + 1)

theorem tens_eq_span {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) :
    Lat.tens Λ a p = Submodule.span (regAt ξ p) {∏ i, s i ^ a i} := by
  rw [show Lat.tens Λ a p = Submodule.span (regAt ξ p)
      {t | ∃ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) ∧ t = ∏ i, s i ^ a i} from rfl]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro t ⟨s', hs', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨⟨∏ i, (s' i / s i) ^ a i, ?_⟩, ?_⟩
    · refine prod_mem fun i _ => zpow_mem_of_inv_mem (div_mem_of_isGenAt (hs' i) (hs i)) ?_ (a i)
      rw [inv_div]
      exact div_mem_of_isGenAt (hs i) (hs' i)
    · show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = ∏ i, s' i ^ a i
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← mul_zpow, div_mul_cancel₀ _ (hs i).1]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨s, hs, rfl⟩

theorem isGenAt_tens {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨?_, tens_eq_span Λ a p s hs⟩
  exact Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hs i).1

theorem mem_finset_inf {I : Type} (S : Finset I) (U : I → X.Opens) (x : X) :
    x ∈ S.inf U ↔ ∀ i ∈ S, x ∈ U i := by
  classical
  refine Finset.induction_on S ?_ ?_
  · rw [Finset.inf_empty]
    exact ⟨fun _ i hi => by simp at hi, fun _ => TopologicalSpace.Opens.mem_top x⟩
  · intro j S' _ ih
    rw [Finset.inf_insert, TopologicalSpace.Opens.mem_inf, ih]
    rw [Finset.forall_mem_insert]

theorem isGenAt_of_isFrameAt {Λ : Lat ξ Ω} {b : Fin 1 → Ω} {p : Cpt ξ} (h : Λ.IsFrameAt b p) :
    Λ.IsGenAt p (b 0) := by
  refine ⟨LinearIndependent.ne_zero 0 h.1, ?_⟩
  rw [h.2, Set.range_unique, Subsingleton.elim (default : Fin 1) 0]

theorem isFrameAt_of_isGenAt {Λ : Lat ξ Ω} {c : Ω} {p : Cpt ξ} (h : Λ.IsGenAt p c) :
    Λ.IsFrameAt (fun _ : Fin 1 => c) p := by
  refine ⟨linearIndependent_unique_iff.mpr h.1, ?_⟩
  rw [h.2, Set.range_const]

theorem tens_isVBOn (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (I : Type)
    [Fintype I] (Λ : I → Lat ξ Ω) (T : Set (Cpt ξ)) (h : ∀ i, (Λ i).IsVBOn T 1 ⊤) (a : I → ℤ) :
    (Lat.tens Λ a).IsVBOn T 1 ⊤ ∧ ∀ p ∈ T, ∀ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) →
      (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨?_, fun p _ s hs => isGenAt_tens Λ a p s hs⟩
  intro p hp
  choose U hpU b _ hfr using fun i => h i p hp
  refine ⟨Finset.univ.inf U, (mem_finset_inf _ _ _).mpr fun i _ => hpU i,
    fun _ => ∏ i, b i 0 ^ a i, ?_, ?_⟩
  · have hc : (∏ i, b i 0 ^ a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ =>
      zpow_ne_zero _ (LinearIndependent.ne_zero 0 (hfr i p hp (hpU i)).1)
    rw [Set.range_const, eq_top_iff]
    intro y _
    rw [Submodule.mem_span_singleton]
    exact ⟨y / ∏ i, b i 0 ^ a i, by rw [smul_eq_mul, div_mul_cancel₀ _ hc]⟩
  · intro q hq hqU
    rw [mem_finset_inf] at hqU
    exact isFrameAt_of_isGenAt (isGenAt_tens Λ a q (fun i => b i 0) fun i =>
      isGenAt_of_isFrameAt (hfr i q hq (hqU i (Finset.mem_univ i))))

end LatTens

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerLineBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.lattice_tensor_power_line_bundle := GlobalTheory.CompanionTheory.Ar.LatTens.tens_isVBOn
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieChart
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

def LieChart {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (x : Sp R ⟶ S) (f : R) : Prop :=
  ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P) (_ : Module (Localization.Away f) P)
    (_ : IsScalarTower R (Localization.Away f) P) (_ : Module.Finite (Localization.Away f) P)
    (_ : Module.Projective (Localization.Away f) P)
    (m : ∀ (C : Type) [CommRing C] [Algebra R C], IsUnit (algebraMap R C f) →
      LieModel G (spMap (algebraMap R C) ≫ x) (P →ₗ[R] C)),
    ∀ (C C' : Type) [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C']
      (hC : IsUnit (algebraMap R C f)) (hC' : IsUnit (algebraMap R C' f)) (c : C →ₐ[R] C') (w : P →ₗ[R] C),
      ((m C' hC').pt (c.toLinearMap ∘ₗ w)).left = spMap (dualMap c.toRingHom) ≫ ((m C hC).pt w).left

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTriangularChange
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTriangularChange
namespace GlobalTheory.CompanionTheory.Ar.FlagChange

open GlobalTheory.CompanionTheory.Ar

theorem exists_coeff_of_mem_step {L Li : Type} [Field L] [AddCommGroup Li] [Module L Li] {r : ℕ}
    (g : Fin r → Li) (n : ℕ) (x : Li) (hx : x ∈ flagStep L g n) :
    ∃ c : Fin r → L, (∀ k : Fin r, n ≤ (k : ℕ) → c k = 0) ∧ x = ∑ k, c k • g k := by
  unfold flagStep at hx
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination L).1 hx
  refine ⟨l, fun k hk => ?_, ?_⟩
  · by_contra h
    have : k ∈ ({k : Fin r | (k : ℕ) < n} : Set (Fin r)) :=
      hl (Finsupp.mem_support_iff.2 h)
    exact absurd this (not_lt.2 hk)
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul L (g i))]

theorem adapted_triangular (L Li : Type) [Field L] [AddCommGroup Li] [Module L Li] (r : ℕ)
    (f b g : Fin r → Li) (v w : Matrix (Fin r) (Fin r) L)
    (_hf : LinearIndependent L f) (hb : LinearIndependent L b)
    (_hv1 : ∀ k, v k k = 1) (_hv0 : ∀ l k, l < k → v l k = 0)
    (hw0 : ∀ l k, k < l → w l k = 0) (hwd : ∀ k, w k k ≠ 0)
    (hg : ∀ k, g k = ∑ j, (v * w) j k • f j)
    (hflag : ∀ i : ℕ, flagStep L b i = flagStep L g i) :
    ∃ Tm : Matrix (Fin r) (Fin r) L, (∀ i, b i = ∑ m, Tm i m • ∑ j, v j m • f j) ∧
      (∀ i m, i < m → Tm i m = 0) ∧ ∀ i, Tm i i ≠ 0 := by
  have hC : ∀ i : Fin r, ∃ c : Fin r → L,
      (∀ k : Fin r, (i : ℕ) + 1 ≤ (k : ℕ) → c k = 0) ∧ b i = ∑ k, c k • g k := fun i =>
    exists_coeff_of_mem_step g _ _ (by
      rw [← hflag]
      exact Submodule.subset_span ⟨i, by simp, rfl⟩)
  choose C hC0 hCb using hC
  have hgW : ∀ k, g k = ∑ m, w m k • ∑ j, v j m • f j := by
    intro k
    rw [hg k]
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  refine ⟨Matrix.of fun i m => ∑ k, C i k * w m k, fun i => ?_, fun i m him => ?_, fun i => ?_⟩
  · generalize hW : (fun m => ∑ j, v j m • f j) = W at *
    have hW' : ∀ m, ∑ j, v j m • f j = W m := fun m => congrFun hW m
    simp only [hW'] at hgW ⊢
    calc b i = ∑ k, C i k • ∑ m, w m k • W m :=
          (hCb i).trans (Finset.sum_congr rfl fun k _ => by rw [hgW k])
      _ = ∑ m, (∑ k, C i k * w m k) • W m := by
          simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
          exact Finset.sum_comm
      _ = _ := rfl
  · show ∑ k, C i k * w m k = 0
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ≤ i
    · rw [hw0 m k (lt_of_le_of_lt hk him), mul_zero]
    · rw [hC0 i k (not_le.1 hk), zero_mul]
  · have hdiag : ∑ k, C i k * w i k = C i i * w i i := by
      refine Finset.sum_eq_single i (fun k _ hki => ?_) (fun h => absurd (Finset.mem_univ i) h)
      rcases lt_or_gt_of_ne hki with h | h
      · rw [hw0 i k h, mul_zero]
      · rw [hC0 i k h, zero_mul]
    show ∑ k, C i k * w i k ≠ 0
    rw [hdiag]
    refine mul_ne_zero (fun h0 => ?_) (hwd i)
    have hmem : b i ∈ flagStep L g i := by
      rw [hCb i]
      refine Submodule.sum_mem _ fun k _ => ?_
      by_cases hk : (k : ℕ) < i
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
      · have hz : C i k = 0 := by
          rcases eq_or_lt_of_le (not_lt.1 hk) with h | h
          · rw [show k = i from Fin.ext h.symm, h0]
          · exact hC0 i k h
        rw [hz, zero_smul]
        exact Submodule.zero_mem _
    rw [← hflag] at hmem
    exact hb.notMem_span_image (s := {k | (k : ℕ) < i}) (x := i) (by simp) hmem

end GlobalTheory.CompanionTheory.Ar.FlagChange
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTriangularChangeStatement
alias GlobalTheory.T.generic_flag_triangular_change := GlobalTheory.CompanionTheory.Ar.FlagChange.adapted_triangular
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EtaleSpaceCohomologyEqZeroOfSimplicialRowExact
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

namespace FlagGr

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}

theorem coeff_eq_zero {b : Fin r → E} (hb : LinearIndependent Ω b) {s : ℕ} (c : Fin r → Ω)
    (h : ∑ k, c k • b k ∈ flagStep Ω b s) (k : Fin r) (hk : ¬ (k : ℕ) < s) : c k = 0 := by
  obtain ⟨l, hl, hl'⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).1 h
  have h1 : ∑ k, (l k) • b k = ∑ k, c k • b k := by
    rw [← hl', Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
  have h2 := (Fintype.linearIndependent_iff.1 hb) (fun k => l k - c k)
    (by simp [sub_smul, Finset.sum_sub_distrib, h1]) k
  have h3 : l k = 0 := (Finsupp.mem_supported' Ω l).1 hl k hk
  simpa [h3] using h2

theorem mem_step (b : Fin r → E) {s : ℕ} {k : Fin r} (hk : (k : ℕ) < s) : b k ∈ flagStep Ω b s :=
  Submodule.subset_span ⟨k, hk, rfl⟩

theorem step_mono (b : Fin r → E) {s s' : ℕ} (h : s ≤ s') : flagStep Ω b s ≤ flagStep Ω b s' :=
  Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk h)

theorem eq_zero_of_smul_mem {b : Fin r → E} (hb : LinearIndependent Ω b) (i : Fin r) {t : Ω}
    (h : t • b i ∈ flagStep Ω b i) : t = 0 := by
  have := coeff_eq_zero hb (s := i) (Pi.single i t) (by simpa [Pi.single_apply] using h) i (lt_irrefl _)
  simpa using this

theorem step_top (b : Fin r → E) : flagStep Ω b r = Submodule.span Ω (Set.range b) := by
  unfold flagStep
  congr 1
  ext x
  simp

theorem range_castLE (b : Fin r → E) {s : ℕ} (hs : s ≤ r) :
    Set.range (b ∘ Fin.castLE hs) = b '' {k | (k : ℕ) < s} := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨Fin.castLE hs k, k.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

theorem exists_diag (b : Fin r → E) (i : Fin r) {e : E} (he : e ∈ flagStep Ω b (i + 1)) :
    ∃ t : Ω, e - t • b i ∈ flagStep Ω b i := by
  have hs : b '' {k : Fin r | (k : ℕ) < i + 1} = insert (b i) (b '' {k : Fin r | (k : ℕ) < i}) := by
    rw [← Set.image_insert_eq]
    congr 1
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Fin.ext_iff]
    omega
  unfold flagStep at he
  rw [hs, Submodule.mem_span_insert] at he
  obtain ⟨t, z, hz, rfl⟩ := he
  exact ⟨t, by simpa [flagStep] using hz⟩

theorem span_inf_step (R : Subring Ω) {b : Fin r → E} (hb : LinearIndependent Ω b) (s : ℕ) :
    Submodule.span R (Set.range b) ⊓ (flagStep Ω b s).restrictScalars R =
      Submodule.span R (b '' {k | (k : ℕ) < s}) := by
  apply le_antisymm
  · rintro e ⟨he, he'⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 he
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : (k : ℕ) < s
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
    · have h0 : (c k : Ω) = 0 := coeff_eq_zero hb (fun k => (c k : Ω)) he' k hk
      have : c k = 0 := Subtype.ext h0
      simp [this]
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨Submodule.subset_span ⟨k, rfl⟩, mem_step b hk⟩

theorem gr_eq (R : Subring Ω) {b b₀ : Fin r → E} (hb : LinearIndependent Ω b) (hb₀ : LinearIndependent Ω b₀)
    (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) (i : Fin r) {t : Ω} (ht : b i - t • b₀ i ∈ flagStep Ω b₀ i) :
    Submodule.span R {u : Ω | ∃ e ∈ Submodule.span R (Set.range b), e - u • b₀ i ∈ flagStep Ω b₀ i} =
      Submodule.span R {t} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro u ⟨e, he, hu⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 he
    have h1 : ∑ k, c k • b k ∈ flagStep Ω b (i + 1) := by
      rw [hF]
      have := Submodule.add_mem _ (step_mono b₀ (Nat.le_succ _) hu)
        (Submodule.smul_mem _ u (mem_step b₀ (Nat.lt_succ_self (i : ℕ))))
      simpa using this
    have h2 : ∑ k, c k • b k - (c i : Ω) • b i ∈ flagStep Ω b₀ i := by
      rw [← hF, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      have : ∑ k ∈ Finset.univ.erase i, c k • b k ∈ flagStep Ω b i := by
        refine Submodule.sum_mem _ fun k hk => ?_
        have hki : k ≠ i := Finset.ne_of_mem_erase hk
        change (c k : Ω) • b k ∈ _
        by_cases hk' : (k : ℕ) < i
        · exact Submodule.smul_mem _ _ (mem_step b hk')
        · have h0 : (c k : Ω) = 0 := coeff_eq_zero hb (fun k => (c k : Ω)) h1 k (by
            have : (k : ℕ) ≠ i := fun h => hki (Fin.ext h)
            omega)
          simp [h0]
      have e2 : c i • b i = (c i : Ω) • b i := rfl
      rw [e2, add_sub_cancel_right]
      exact this
    have h3 : ((c i : Ω) * t - u) • b₀ i ∈ flagStep Ω b₀ i := by
      have := Submodule.sub_mem _ (Submodule.sub_mem _ hu h2) (Submodule.smul_mem _ (c i : Ω) ht)
      convert this using 1
      rw [sub_smul, smul_sub, mul_smul]
      abel
    have h4 := eq_zero_of_smul_mem hb₀ i h3
    exact Submodule.mem_span_singleton.2 ⟨c i, sub_eq_zero.1 h4⟩
  · refine Submodule.span_mono ?_
    rintro _ rfl
    exact ⟨b i, Submodule.subset_span ⟨i, rfl⟩, ht⟩

end FlagGr


open FlagGr in
theorem Lat.IsFlagVBOn.isVBOn_gr_inter : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (b₀ : Fin r → E), LinearIndependent Ω b₀ → L.IsFlagVBOn T b₀ → L.IsVBOn T r (Submodule.span Ω (Set.range b₀)) ∧ (∀ i, (L.gr b₀ i).IsVBOn T 1 ⊤) ∧ ∀ s : ℕ, s ≤ r → (L.inter (flagStep Ω b₀ s)).IsVBOn T s (flagStep Ω b₀ s) := by
  intro X Ω _ ξ E _ _ L T r b₀ hb₀ hL
  refine ⟨fun p hp => ?_, fun i p hp => ?_, fun s hs p hp => ?_⟩
  · obtain ⟨U, hU, b, hF, hb⟩ := hL p hp
    exact ⟨U, hU, b, by rw [← step_top, hF, step_top], hb⟩
  · obtain ⟨U, hU, b, hF, hb⟩ := hL p hp
    have hli := (hb p hp hU).1
    obtain ⟨t, ht⟩ := exists_diag b₀ i (e := b i) (hF _ ▸ mem_step b (Nat.lt_succ_self (i : ℕ)))
    have ht0 : t ≠ 0 := by
      rintro rfl
      have : (1 : Ω) • b i ∈ flagStep Ω b i := by simpa [hF] using ht
      exact one_ne_zero (eq_zero_of_smul_mem hli i this)
    have hr : Set.range (fun _ : Fin 1 => t) = {t} := Set.range_const
    refine ⟨U, hU, fun _ => t, ?_, fun q hq hqU => ⟨?_, ?_⟩⟩
    · rw [hr, eq_top_iff]
      intro x _
      exact Submodule.mem_span_singleton.2 ⟨x / t, by simp [ht0]⟩
    · exact linearIndependent_unique_iff.2 ht0
    · rw [hr]
      unfold Lat.gr
      rw [(hb q hq hqU).2]
      exact gr_eq _ hli hb₀ hF i ht
  · obtain ⟨U, hU, b, hF, hb⟩ := hL p hp
    have hli := (hb p hp hU).1
    refine ⟨U, hU, b ∘ Fin.castLE hs, ?_, fun q hq hqU => ⟨hli.comp _ (Fin.castLE_injective hs), ?_⟩⟩
    · rw [range_castLE, ← hF]
      rfl
    · unfold Lat.inter
      rw [(hb q hq hqU).2, range_castLE, ← hF]
      exact span_inf_step _ hli s

end GlobalTheory.CompanionTheory.Ar
end
end
