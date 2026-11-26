module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeInvariantLinearEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeInvariantLinearEquiv
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv

open GlobalTheory.CompanionTheory.Ar.Crv

variable {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]
  {V' : Type} [AddCommGroup V'] [Module K V']

def tr (e : V ≃ₗ[K] V') (b : Module.Basis (Fin (Module.finrank K V)) K V) :
    Module.Basis (Fin (Module.finrank K V')) K V' :=
  (b.map e).reindex (finCongr e.finrank_eq)

theorem isLatOf_tr (e : V ≃ₗ[K] V') {i : C.I} {b : Module.Basis (Fin (Module.finrank K V)) K V}
    {L : AddSubgroup V} {L' : AddSubgroup V'} (hb : IsLatOf C i b L)
    (h : ∀ x, x ∈ L ↔ e x ∈ L') : IsLatOf C i (tr e b) L' := by
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [← h, hb]
  simp only [tr, Module.Basis.repr_reindex_apply, Module.Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  exact ⟨fun H q => H _, fun H q => by simpa using H (finCongr e.finrank_eq q)⟩

theorem det_tr (e : V ≃ₗ[K] V') (a b : Module.Basis (Fin (Module.finrank K V)) K V) :
    (tr e a).det (tr e b) = a.det b := by
  unfold tr
  rw [Module.Basis.coe_reindex, Module.Basis.det_reindex, Module.Basis.det_map]
  congr 1
  funext i
  simp

theorem deg_equiv : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (e : V ≃ₗ[K] V'),
    IsBun C L → (∀ i x, x ∈ L i ↔ e x ∈ L' i) → IsBun C L' ∧ deg C L' = deg C L := by
  intro K _ C V _ _ _ V' _ _ _ L L' e ⟨hl, b0, hb0⟩ h
  choose b hb using hl
  have hb' : ∀ i, IsLatOf C i (tr e (b i)) (L' i) := fun i => isLatOf_tr C e (hb i) (h i)
  refine ⟨⟨fun i => ⟨_, hb' i⟩, tr e b0,
    hb0.subset fun i hi hc => hi (isLatOf_tr C e hc (h i))⟩, ?_⟩
  rw [Inhab.deg_eq C _ hb', Inhab.deg_eq C _ hb]
  set c := (Module.finBasis K V').det (tr e (Module.finBasis K V)) with hc
  have hc0 : c ≠ 0 := ((Module.finBasis K V').isUnit_det _).ne_zero
  have hd0 : ∀ i, (Module.finBasis K V).det (b i) ≠ 0 := fun i =>
    ((Module.finBasis K V).isUnit_det _).ne_zero
  have h1 : ∀ i, (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V').det (tr e (b i)))) =
      (C.w i : ℤ) * WithZero.log (C.v i c) +
        (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (b i))) := by
    intro i
    rw [← Module.Basis.det_mul_det _ (tr e (Module.finBasis K V)), det_tr, ← hc, map_mul,
      WithZero.log_mul ((Valuation.ne_zero_iff _).2 hc0) ((Valuation.ne_zero_iff _).2 (hd0 i)),
      mul_add]
  simp only [h1]
  rw [finsum_add_distrib, C.prod c hc0, zero_add]
  · exact (C.fin c hc0).subset fun i hi h1 => hi (by simp [h1])
  · refine (hb0.union (C.fin _ ((Module.finBasis K V).isUnit_det b0).ne_zero)).subset
      fun i hi => ?_
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
    apply hi
    show (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (b i))) = 0
    rw [← Module.Basis.det_mul_det _ b0, map_mul, hn.2, Inhab.v_det C hn.1 (hb i)]
    simp

end GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeInvariantLinearEquivStatement
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_invariant_linear_equiv : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (e : V ≃ₗ[K] V'), IsBun C L → (∀ i x, x ∈ L i ↔ e x ∈ L' i) → IsBun C L' ∧ deg C L' = deg C L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv.deg_equiv | exact GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv.deg_equiv | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv.deg_equiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsUniformDenominator
namespace GlobalTheory.CompanionTheory.Ar.Num.Reflexive

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E] [Module Ω E]

theorem mem_of_locally_mem (R : Subalgebra o Ω) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {k : ℕ} (f c : Fin k → Ω) (hf : ∀ l, f l ∈ R)
    (hc : ∀ l, c l ∈ R) (h1 : ∑ l, c l * f l = 1) (v : E) (hv : ∀ l, ∃ n : ℕ, f l ^ n • v ∈ L) :
    v ∈ L := by
  let I : Ideal R :=
    { carrier := {a | (a : Ω) • v ∈ L}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, AddMemClass.coe_add, add_smul] at *
        exact L.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun a b hb => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, MulMemClass.coe_mul, mul_smul] at *
        exact hL _ a.2 _ hb }
  have hrad : ∀ l, (⟨f l, hf l⟩ : R) ∈ I.radical := fun l => by
    obtain ⟨n, hn⟩ := hv l
    exact ⟨n, by simpa [I] using hn⟩
  have hone : (1 : R) ∈ I.radical := by
    have : (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * ⟨f l, hf l⟩ := by
      apply Subtype.ext
      simp [h1]
    rw [this]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hrad l)
  obtain ⟨n, hn⟩ := hone
  simpa [I] using hn

theorem exists_uniform_pow (R : Subalgebra o Ω) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {ι : Type*} [Finite ι] (g : Ω) (hg : g ∈ R) (x : ι → E)
    (hx : ∀ i, ∃ n : ℕ, g ^ n • x i ∈ L) : ∃ n : ℕ, ∀ i, g ^ n • x i ∈ L := by
  classical
  have := Fintype.ofFinite ι
  choose n hn using hx
  refine ⟨∑ i, n i, fun i => ?_⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le'
    (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  rw [hd, pow_add, mul_smul]
  exact hL _ (R.pow_mem hg d) _ (hn i)

theorem exists_uniform_denominator (R : Subalgebra o Ω) (r : ℕ) (L : AddSubgroup E)
    (h : LocFree R r L) (g : Ω) (hg : g ∈ R) (ψ : Module.Dual Ω E)
    (hψ : ∀ e ∈ L, ∃ n : ℕ, g ^ n * ψ e ∈ R) : ∃ m : ℕ, ∀ e ∈ L, g ^ m * ψ e ∈ R := by
  classical
  obtain ⟨hL, k, f, c, hf, hc, h1, hb⟩ := h
  choose b _ _ hb using hb
  let R' : AddSubgroup Ω := R.toSubring.toAddSubgroup
  have hR' : ∀ a ∈ R, ∀ e ∈ R', a • e ∈ R' := fun a ha e he => R.mul_mem ha he
  have hbL : ∀ j q, ∃ n : ℕ, f j ^ n • b j q ∈ L := fun j q => by
    refine (hb j (b j q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
    · by_cases hq : q' = q
      · subst hq; simp
      · simp [hq]
    · simp [Pi.single_apply]
  choose N hN using hbL
  obtain ⟨m, hm⟩ := exists_uniform_pow R R' hR' g hg
    (fun p : Fin k × Fin r => ψ (f p.1 ^ N p.1 p.2 • b p.1 p.2)) (fun p => hψ _ (hN p.1 p.2))
  refine ⟨m, fun e he => ?_⟩
  refine mem_of_locally_mem R R' hR' f c hf hc h1 _ fun j => ?_
  obtain ⟨a, ha, rfl⟩ := (hb j e).1 ⟨0, by simpa using he⟩
  have key : ∀ q, ∃ n : ℕ, f j ^ n • (g ^ m * (a q * ψ (b j q))) ∈ R' := fun q => by
    obtain ⟨n, hn⟩ := ha q
    refine ⟨n + N j q, ?_⟩
    have h2 : g ^ m * ψ (f j ^ N j q • b j q) ∈ R := hm (j, q)
    have h3 := R.mul_mem hn h2
    have h4 : f j ^ (n + N j q) • (g ^ m * (a q * ψ (b j q)))
        = f j ^ n * a q * (g ^ m * ψ (f j ^ N j q • b j q)) := by
      simp only [map_smul, smul_eq_mul]; ring
    rw [h4]; exact h3
  obtain ⟨n, hn⟩ := exists_uniform_pow R R' hR' (f j) (hf j) _ key
  refine ⟨n, ?_⟩
  have h5 : f j ^ n • (g ^ m * ψ (∑ q, a q • b j q))
      = ∑ q, f j ^ n • (g ^ m * (a q * ψ (b j q))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  rw [h5]
  exact R'.sum_mem fun q _ => hn q

theorem locFree_reflexive : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] (r : ℕ) (L : AddSubgroup E), LocFree R r L → ∀ v : E, (∀ ψ : Module.Dual Ω E, (∀ e ∈ L, ψ e ∈ R) → ψ v ∈ R) → v ∈ L := by
  intro o Ω _ _ _ R E _ _ r L h v hv
  have h' := h
  obtain ⟨hL, k, f, c, hf, hc, h1, hb⟩ := h'
  refine mem_of_locally_mem R L hL f c hf hc h1 v fun l => ?_
  obtain ⟨b, hli, hsp, hb⟩ := hb l
  let B : Module.Basis (Fin r) Ω E := Module.Basis.mk hli hsp.ge
  have hB : ∀ q, B q = b q := fun q => Module.Basis.mk_apply _ _ q
  refine (hb v).2 ⟨fun q => B.coord q v, fun q => ?_, ?_⟩
  · obtain ⟨m, hm⟩ := exists_uniform_denominator R r L h (f l) (hf l) (B.coord q) fun e he => by
      obtain ⟨a, ha, rfl⟩ := (hb e).1 ⟨0, by simpa using he⟩
      have : B.coord q (∑ q, a q • b q) = a q := by
        simp only [← hB, Module.Basis.coord_apply]
        exact congrFun (B.repr_sum_self a) q
      rw [this]; exact ha q
    exact ⟨m, by simpa using hv (f l ^ m • B.coord q) (by simpa using hm)⟩
  · simp only [← hB, Module.Basis.coord_apply]
    exact (B.sum_repr v).symm

end GlobalTheory.CompanionTheory.Ar.Num.Reflexive
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeOfFiniteProjective
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeOfFiniteProjective
namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj

open GlobalTheory.CompanionTheory.Ar.Num TensorProduct

theorem exists_local_basis {R L : Type} [CommRing R] [IsDomain R] [AddCommGroup L] [Module R L]
    [Module.Finite R L] [Module.Projective R L] (p : Ideal R) [p.IsPrime] :
    ∃ (n : ℕ) (m : Fin n → L) (s : R), s ∉ p ∧ LinearIndependent R m ∧
      ∀ x : L, s • x ∈ Submodule.span R (Set.range m) := by
  classical
  let Rp := Localization.AtPrime p
  let Lp := LocalizedModule p.primeCompl L
  let f : L →ₗ[R] Lp := LocalizedModule.mkLinearMap p.primeCompl L
  haveI : Module.Free Rp Lp := Module.free_of_flat_of_isLocalRing
  let β := Module.finBasis Rp Lp
  choose ms hms using fun i => IsLocalizedModule.mk'_surjective p.primeCompl f (β i)
  let m : Fin (Module.finrank Rp Lp) → L := fun i => (ms i).1
  let u : Fin (Module.finrank Rp Lp) → Rpˣ := fun i => (IsLocalization.map_units Rp (ms i).2).unit
  have hβ : ∀ i, β.unitsSMul u i = f (m i) := by
    intro i
    rw [Module.Basis.unitsSMul_apply, ← hms i, Units.smul_def]
    simp only [u, IsUnit.unit_spec, algebraMap_smul, Function.uncurry]
    exact IsLocalizedModule.mk'_cancel' f _ _
  have hfun : (β.unitsSMul u : _ → Lp) = f ∘ m := funext hβ
  have hli : LinearIndependent R m := by
    have h1 : LinearIndependent Rp (f ∘ m) := hfun ▸ (β.unitsSMul u).linearIndependent
    have h2 : LinearIndependent R (f ∘ m) := h1.restrict_scalars' R
    exact h2.of_comp f
  have hsp : ∀ x : L, ∃ s : R, s ∉ p ∧ s • x ∈ Submodule.span R (Set.range m) := by
    intro x
    have h1 : f x ∈ (Submodule.span R (Set.range m)).localized' Rp p.primeCompl f := by
      rw [Submodule.localized'_span, ← Set.range_comp, ← hfun, (β.unitsSMul u).span_eq]
      trivial
    obtain ⟨y, hy, s, hs⟩ := (Submodule.mem_localized' _ _ _ _ _).1 h1
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at hs
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := p.primeCompl) hs
    refine ⟨(c * s : p.primeCompl), (c * s).2, ?_⟩
    rw [Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, ← hc]
    exact Submodule.smul_mem _ _ hy
  choose s hs hs' using hsp
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := R) (M := L)
  refine ⟨_, m, ∏ t ∈ T, s t, ?_, hli, ?_⟩
  · exact Submonoid.prod_mem p.primeCompl (fun t _ => hs t)
  · intro x
    have hx : x ∈ Submodule.span R (T : Set L) := hT ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem t ht =>
      rw [← Finset.prod_erase_mul T s ht, mul_smul]
      exact Submodule.smul_mem _ _ (hs' t)
    | zero => simp
    | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    | smul a b _ hb => rw [smul_comm]; exact Submodule.smul_mem _ _ hb

theorem flat_field {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) :
    Module.Flat R Ω := by
  letI : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω
  haveI : Module.Flat R (FractionRing R) := IsLocalization.flat _ (nonZeroDivisors R)
  haveI : Module.Free (FractionRing R) Ω := Module.Free.of_divisionRing _ _
  haveI : Module.Flat (FractionRing R) Ω := Module.Flat.of_free
  exact Module.Flat.trans R (FractionRing R) Ω

theorem exists_chart {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type}
    [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E) [Module.Finite R L] [Module.Projective R L]
    (hr : Module.finrank Ω E = r) (hb : IsBaseChange Ω L.subtype) (p : Ideal R) [p.IsPrime] :
    ∃ s : R, s ∉ p ∧ ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, (s : Ω) ^ n • e ∈ L.toAddSubgroup) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, (s : Ω) ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q := by
  classical
  obtain ⟨n, m, s, hs, hli, hsp⟩ := exists_local_basis (L := L) p
  haveI := flat_field R
  have hs0 : (s : Ω) ≠ 0 := fun h => hs (by
    have : s = 0 := Subtype.ext h
    rw [this]; exact p.zero_mem)
  let b : Fin n → E := fun i => (m i : E)
  have hli' : LinearIndependent Ω b := by
    have h1 := (Module.Flat.linearIndependent_one_tmul (S := Ω) hli).map' hb.equiv.toLinearMap
      (LinearEquiv.ker _)
    have hfun : b = (⇑hb.equiv.toLinearMap ∘ fun x => (1 : Ω) ⊗ₜ[R] m x) := by
      funext i
      simp [b, IsBaseChange.equiv_tmul]
    rw [hfun]
    exact h1
  have key : ∀ x : L, ∃ a : Fin n → R, (s : Ω) • (x : E) = ∑ q, (a q : Ω) • b q := by
    intro x
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hsp x)
    refine ⟨a, ?_⟩
    have := congrArg (fun z : L => (z : E)) ha
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  have hspan : Submodule.span Ω (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro e _
    induction e using hb.inductionOn with
    | tmul x =>
      obtain ⟨a, ha⟩ := key x
      rw [← Submodule.smul_mem_iff _ hs0]
      simp only [Submodule.subtype_apply]
      rw [ha]
      exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
    | smul c x hx => exact Submodule.smul_mem _ _ (hx trivial)
    | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  have hn : n = r := by
    rw [← hr, Module.finrank_eq_card_basis (Module.Basis.mk hli' hspan.ge), Fintype.card_fin]
  subst hn
  refine ⟨s, hs, b, hli', hspan, fun e => ⟨?_, ?_⟩⟩
  · rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := key ⟨_, hk⟩
    refine ⟨fun q => ((s : Ω) ^ (k + 1))⁻¹ * a q, fun q => ⟨k + 1, ?_⟩, ?_⟩
    · rw [mul_inv_cancel_left₀ (pow_ne_zero _ hs0)]; exact (a q).2
    · simp only [mul_smul]
      rw [← Finset.smul_sum, ← ha, smul_smul, smul_smul, mul_assoc, ← pow_succ',
        inv_mul_cancel₀ (pow_ne_zero _ hs0), one_smul]
  · rintro ⟨a, ha, rfl⟩
    choose k hk using ha
    refine ⟨∑ q, k q, ?_⟩
    rw [Finset.smul_sum]
    refine L.toAddSubgroup.sum_mem fun q _ => ?_
    have h1 : (s : Ω) ^ (∑ q, k q) * a q ∈ R := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ q), pow_add, mul_assoc]
      exact R.mul_mem (R.pow_mem s.2 _) (hk q)
    rw [smul_smul]
    exact L.smul_mem (⟨_, h1⟩ : R) (m q).2

theorem locFree_of_projective : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E), Module.Finite R L → Module.Projective R L → Module.finrank Ω E = r → IsBaseChange Ω L.subtype → LocFree R r L.toAddSubgroup := by
  intro o Ω _ _ _ R E _ _ r L _ _ hr hb
  classical
  refine ⟨fun a ha e he => L.smul_mem (⟨a, ha⟩ : R) he, ?_⟩
  let P : R → Prop := fun s => ∃ b : Fin r → E, LinearIndependent Ω b ∧
      Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, (s : Ω) ^ n • e ∈ L.toAddSubgroup) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, (s : Ω) ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q
  have htop : Ideal.span {s | P s} = ⊤ := by
    by_contra h
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨s, hs, hP⟩ := exists_chart R r L hr hb p
    exact hs (hle (Ideal.subset_span hP))
  have h1 : (1 : R) ∈ Submodule.span R {s | P s} := by
    change (1 : R) ∈ Ideal.span {s | P s}
    rw [htop]; trivial
  obtain ⟨k, c, g, hg⟩ := Submodule.mem_span_set'.1 h1
  refine ⟨k, fun l => ((g l : R) : Ω), fun l => (c l : Ω), fun l => (g l : R).2, fun l => (c l).2, ?_,
    fun l => (g l).2⟩
  have := congrArg (fun z : R => (z : Ω)) hg
  simpa using this

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeOfFiniteProjectiveStatement
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_free_of_finite_projective : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E), Module.Finite R L → Module.Projective R L → Module.finrank Ω E = r → IsBaseChange Ω L.subtype → LocFree R r L.toAddSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.locFree_of_projective | exact GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.locFree_of_projective | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.locFree_of_projective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumMemLoc
namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeExt

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω]

section One

variable {E : Type*} [AddCommGroup E] [Module Ω E]

def loc (R : Subalgebra o Ω) (f : Ω) (hf : f ∈ R) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) : AddSubgroup E where
  carrier := {e | ∃ n : ℕ, f ^ n • e ∈ L}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [pow_add, mul_comm, mul_smul]; exact hL _ (R.pow_mem hf _) _ hn
    · rw [pow_add, mul_smul]; exact hL _ (R.pow_mem hf _) _ hm
  neg_mem' := by
    rintro x ⟨n, hn⟩
    exact ⟨n, by rw [smul_neg]; exact L.neg_mem hn⟩

theorem mem_loc {R : Subalgebra o Ω} {f : Ω} {hf : f ∈ R} {L : AddSubgroup E}
    {hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L} {e : E} :
    e ∈ loc R f hf L hL ↔ ∃ n : ℕ, f ^ n • e ∈ L := Iff.rfl

theorem sum_mem_loc {R : Subalgebra o Ω} {f : Ω} (hf : f ∈ R) {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r : ℕ} (a : Fin r → Ω) (b : Fin r → E)
    (ha : ∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) (hb : ∀ q, ∃ n : ℕ, f ^ n • b q ∈ L) :
    ∃ n : ℕ, f ^ n • (∑ q, a q • b q) ∈ L := by
  rw [← mem_loc (hf := hf) (hL := hL)]
  refine AddSubgroup.sum_mem _ fun q _ => ?_
  obtain ⟨n, hn⟩ := ha q
  obtain ⟨m, hm⟩ := hb q
  refine ⟨n + m, ?_⟩
  have h := hL _ hn _ hm
  rw [smul_smul] at h
  rw [smul_smul]
  convert h using 2
  ring

def FreeOn (R : Subalgebra o Ω) (f : Ω) (L : AddSubgroup E) {r : ℕ} (b : Fin r → E) : Prop :=
  LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
    ∀ e, (∃ n : ℕ, f ^ n • e ∈ L) ↔
      ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q

theorem FreeOn.basis_mem {R : Subalgebra o Ω} {f : Ω} {L : AddSubgroup E} {r : ℕ} {b : Fin r → E}
    (h : FreeOn R f L b) (q : Fin r) : ∃ n : ℕ, f ^ n • b q ∈ L := by
  classical
  refine (h.2.2 _).2 ⟨Pi.single q 1, fun p => ⟨0, ?_⟩, ?_⟩
  · by_cases hp : p = q
    · subst hp; simp
    · simp [Pi.single_eq_of_ne hp]
  · simp [Pi.single_apply, ite_smul]

theorem exists_coord {r : ℕ} {b : Fin r → E} (h : Submodule.span Ω (Set.range b) = ⊤) (e : E) :
    ∃ a : Fin r → Ω, e = ∑ q, a q • b q := by
  have he : e ∈ Submodule.span Ω (Set.range b) := h ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 he
  exact ⟨a, ha.symm⟩

theorem FreeOn.mul {R : Subalgebra o Ω} {f g : Ω} (hf : f ∈ R) (hg : g ∈ R) {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r : ℕ} {b : Fin r → E}
    (h : FreeOn R f L b) : FreeOn R (f * g) L b := by
  refine ⟨h.1, h.2.1, fun e => ⟨?_, ?_⟩⟩
  · rintro ⟨n, hn⟩
    by_cases hg0 : g = 0
    · obtain ⟨a, ha⟩ := exists_coord h.2.1 e
      exact ⟨a, fun q => ⟨1, by simp [hg0]⟩, ha⟩
    · rw [mul_pow, mul_smul] at hn
      obtain ⟨a, ha, he⟩ := (h.2.2 _).1 ⟨n, hn⟩
      refine ⟨fun q => (g ^ n)⁻¹ * a q, fun q => ?_, ?_⟩
      · obtain ⟨m, hm⟩ := ha q
        refine ⟨n + m, ?_⟩
        have h1 := R.mul_mem (R.mul_mem (R.pow_mem hf n) (R.pow_mem hg m)) hm
        convert h1 using 1
        have : g ^ n ≠ 0 := pow_ne_zero _ hg0
        field_simp
        ring
      · simp only [mul_smul]
        rw [← Finset.smul_sum, ← he, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hg0), one_smul]
  · rintro ⟨a, ha, rfl⟩
    refine sum_mem_loc (R.mul_mem hf hg) hL a b ha fun q => ?_
    obtain ⟨n, hn⟩ := h.basis_mem q
    refine ⟨n, ?_⟩
    rw [mul_pow, mul_comm, mul_smul]
    exact hL _ (R.pow_mem hg _) _ hn

end One

variable {E E₁ E₂ : Type*} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁]
  [AddCommGroup E₂] [Module Ω E₂]

theorem freeOn_ext {R : Subalgebra o Ω} {f : Ω} (hf : f ∈ R) (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hiq : LinearMap.range i = LinearMap.ker q) {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r₁ r₂ : ℕ} {b₁ : Fin r₁ → E₁} {b₂ : Fin r₂ → E₂}
    (h₁ : FreeOn R f (L.comap i.toAddMonoidHom) b₁) (h₂ : FreeOn R f (L.map q.toAddMonoidHom) b₂) :
    ∃ b : Fin (r₁ + r₂) → E, FreeOn R f L b := by
  have hlift : ∀ p, ∃ t : E, q t = b₂ p ∧ ∃ n : ℕ, f ^ n • t ∈ L := by
    intro p
    by_cases hf0 : f = 0
    · obtain ⟨t, ht⟩ := hq (b₂ p)
      exact ⟨t, ht, 1, by simp [hf0]⟩
    · obtain ⟨n, s, hs, hs'⟩ := h₂.basis_mem p
      have hs'' : q s = f ^ n • b₂ p := hs'
      refine ⟨(f ^ n)⁻¹ • s, ?_, n, ?_⟩
      · rw [map_smul, hs'', smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hf0), one_smul]
      · rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hf0), one_smul]; exact hs
  choose t ht htL using hlift
  have hqi : ∀ x, q (i x) = 0 := fun x => by
    have : i x ∈ LinearMap.ker q := hiq ▸ LinearMap.mem_range_self i x
    exact this
  have hsum : ∀ (a₁ : Fin r₁ → Ω) (a₂ : Fin r₂ → Ω),
      ∑ p, Fin.append a₁ a₂ p • Fin.append (fun p => i (b₁ p)) t p
        = i (∑ p, a₁ p • b₁ p) + ∑ p, a₂ p • t p := by
    intro a₁ a₂
    rw [Fin.sum_univ_add]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  have hker : ∀ (e : E) (a₂ : Fin r₂ → Ω), q e = ∑ p, a₂ p • b₂ p →
      ∃ x, i x = e - ∑ p, a₂ p • t p := by
    intro e a₂ he
    have : e - ∑ p, a₂ p • t p ∈ LinearMap.range i := by
      rw [hiq, LinearMap.mem_ker, map_sub, he]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, ht]
    exact this
  refine ⟨Fin.append (fun p => i (b₁ p)) t, ?_, ?_, fun e => ⟨?_, ?_⟩⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_add] at hg
    simp only [Fin.append_left, Fin.append_right] at hg
    have h2 : ∑ p, g (Fin.natAdd r₁ p) • b₂ p = 0 := by
      have := congrArg q hg
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, hqi, ht] using this
    have h2' := Fintype.linearIndependent_iff.1 h₂.1 _ h2
    have h1 : ∑ p, g (Fin.castAdd r₂ p) • b₁ p = 0 := by
      apply hi
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, h2'] using hg
    have h1' := Fintype.linearIndependent_iff.1 h₁.1 _ h1
    intro p
    refine Fin.addCases (fun p => h1' p) (fun p => h2' p) p
  · rw [eq_top_iff]
    intro e _
    obtain ⟨a₂, ha₂⟩ := exists_coord h₂.2.1 (q e)
    obtain ⟨x, hx⟩ := hker e a₂ ha₂
    obtain ⟨a₁, ha₁⟩ := exists_coord h₁.2.1 x
    refine (Submodule.mem_span_range_iff_exists_fun Ω).2 ⟨Fin.append a₁ a₂, ?_⟩
    rw [hsum, ← ha₁, hx, sub_add_cancel]
  · rintro ⟨n, hn⟩
    obtain ⟨a₂, ha₂R, ha₂⟩ := (h₂.2.2 (q e)).1 ⟨n, f ^ n • e, hn, by simp⟩
    obtain ⟨x, hx⟩ := hker e a₂ ha₂
    have hxL : i x ∈ loc R f hf L hL := by
      rw [hx]
      exact AddSubgroup.sub_mem _ ⟨n, hn⟩ (sum_mem_loc hf hL a₂ t ha₂R htL)
    obtain ⟨m, hm⟩ := hxL
    obtain ⟨a₁, ha₁R, ha₁⟩ := (h₁.2.2 x).1 ⟨m, by
      rw [AddSubgroup.mem_comap]; simpa using hm⟩
    refine ⟨Fin.append a₁ a₂, fun p => ?_, ?_⟩
    · refine Fin.addCases (fun p => ?_) (fun p => ?_) p
      · simpa using ha₁R p
      · simpa using ha₂R p
    · rw [hsum, ← ha₁, hx, sub_add_cancel]
  · rintro ⟨a, ha, rfl⟩
    refine sum_mem_loc hf hL a _ ha fun p => ?_
    refine Fin.addCases (fun p => ?_) (fun p => ?_) p
    · obtain ⟨n, hn⟩ := h₁.basis_mem p
      rw [AddSubgroup.mem_comap] at hn
      exact ⟨n, by simpa using hn⟩
    · simpa using htL p

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₁ E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] [AddCommGroup E₂] [Module Ω E₂] (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂), Function.Injective i → Function.Surjective q → LinearMap.range i = LinearMap.ker q → ∀ (L : AddSubgroup E) (r₁ r₂ : ℕ), (∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) → LocFree R r₁ (L.comap i.toAddMonoidHom) → LocFree R r₂ (L.map q.toAddMonoidHom) → LocFree R (r₁ + r₂) L := by
  intro o Ω _ _ _ R E E₁ E₂ _ _ _ _ _ _ i q hi hq hiq L r₁ r₂ hL
  rintro ⟨hL₁, k₁, f₁, c₁, hf₁, hc₁, hs₁, hb₁⟩ ⟨hL₂, k₂, f₂, c₂, hf₂, hc₂, hs₂, hb₂⟩
  refine ⟨hL, k₁ * k₂,
    fun l => f₁ (finProdFinEquiv.symm l).1 * f₂ (finProdFinEquiv.symm l).2,
    fun l => c₁ (finProdFinEquiv.symm l).1 * c₂ (finProdFinEquiv.symm l).2,
    fun l => R.mul_mem (hf₁ _) (hf₂ _), fun l => R.mul_mem (hc₁ _) (hc₂ _), ?_, fun l => ?_⟩
  · rw [Equiv.sum_comp finProdFinEquiv.symm
      (fun p : Fin k₁ × Fin k₂ => c₁ p.1 * c₂ p.2 * (f₁ p.1 * f₂ p.2)), Fintype.sum_prod_type,
      ← mul_one (1 : Ω)]
    conv_rhs => rw [← hs₁]; enter [2]; rw [hs₁, ← hs₂]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  · obtain ⟨b₁, h₁⟩ := hb₁ (finProdFinEquiv.symm l).1
    obtain ⟨b₂, h₂⟩ := hb₂ (finProdFinEquiv.symm l).2
    have h₁' := FreeOn.mul (hf₁ _) (hf₂ (finProdFinEquiv.symm l).2) hL₁ h₁
    have h₂' := FreeOn.mul (hf₂ _) (hf₁ (finProdFinEquiv.symm l).1) hL₂ h₂
    rw [mul_comm] at h₂'
    exact freeOn_ext (R.mul_mem (hf₁ _) (hf₂ _)) i q hi hq hiq hL h₁' h₂'

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeExt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsPowPrincipal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCountSpanSingletonEqMul
open NumberField IsDedekindDomain

namespace GlobalTheory.RootIdeal

theorem exists_pow_eq_spanSingleton (K : Type) [Field K] [NumberField K]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hJ : J ≠ 0) :
    ∃ (h : ℕ) (x : K), 0 < h ∧ x ≠ 0 ∧
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x = J ^ h := by
  classical
  let u : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ := Units.mk0 J hJ
  have hpos : 0 < orderOf (ClassGroup.mk K u) := orderOf_pos _
  have h1 : ClassGroup.mk K (u ^ orderOf (ClassGroup.mk K u)) = 1 := by
    rw [map_pow, pow_orderOf_eq_one]
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := h1.principal
  have hJh : ((u ^ orderOf (ClassGroup.mk K u) : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = J ^ orderOf (ClassGroup.mk K u) := by
    simp [u]
  have key : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x =
      J ^ orderOf (ClassGroup.mk K u) := by
    rw [← hJh]
    apply FractionalIdeal.coeToSubmodule_injective
    dsimp only
    rw [FractionalIdeal.coe_spanSingleton, hx]
  refine ⟨_, x, hpos, ?_, key⟩
  rintro rfl
  rw [FractionalIdeal.spanSingleton_zero] at key
  exact pow_ne_zero _ hJ key.symm

theorem exists_count_spanSingleton_eq_mul (K : Type) [Field K] [NumberField K]
    (r : HeightOneSpectrum (𝓞 K) →₀ ℚ) :
    ∃ (n : ℕ) (x : K), 0 < n ∧ x ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K),
      ((FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x) : ℤ) : ℚ) = n * r v := by
  classical
  set d : ℕ := ∏ v ∈ r.support, (r v).den with hd
  have hdpos : 0 < d := Finset.prod_pos (fun v _ => (r v).pos)
  have hdvd : ∀ v, (r v).den ∣ d := by
    intro v
    by_cases hv : v ∈ r.support
    · exact Finset.dvd_prod_of_mem _ hv
    · rw [Finsupp.notMem_support_iff.mp hv]
      simp
  let e : HeightOneSpectrum (𝓞 K) →₀ ℤ :=
    Finsupp.mapRange (fun q : ℚ => q.num * ((d / q.den : ℕ) : ℤ)) (by simp) r
  have he : ∀ v, ((e v : ℤ) : ℚ) = d * r v := by
    intro v
    simp only [e, Finsupp.mapRange_apply]
    have hden : ((r v).den : ℚ) ≠ 0 := by exact_mod_cast (r v).pos.ne'
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div (hdvd v) hden]
    conv_rhs => rw [← Rat.num_div_den (r v)]
    field_simp
  set J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    e.prod (fun v n => ((v.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n)
    with hJdef
  have hJ0 : J ≠ 0 := by
    rw [hJdef, Finsupp.prod, Finset.prod_ne_zero_iff]
    intro v _
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  have hcount : ∀ v, FractionalIdeal.count K v J = e v := fun v =>
    FractionalIdeal.count_finsuppProd K v e
  obtain ⟨h, x, hh, hx0, hxJ⟩ := exists_pow_eq_spanSingleton K J hJ0
  refine ⟨h * d, x, Nat.mul_pos hh hdpos, hx0, fun v => ?_⟩
  rw [hxJ, FractionalIdeal.count_pow, hcount, Int.cast_mul, Int.cast_natCast, he]
  push_cast
  ring

end GlobalTheory.RootIdeal
end

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_pow_principal : ∀ (F : Type) [Field F] [NumberField F]
    (r : HeightOneSpectrum (𝓞 F) →₀ ℚ), ∃ (M : ℕ) (α : F), 0 < M ∧ α ≠ 0 ∧
      ∀ v : HeightOneSpectrum (𝓞 F), ∃ n : ℤ, (n : ℚ) = M * r v ∧
        v.valuation F α = WithZero.exp (-n) := by
  intro F _ _ r
  obtain ⟨M, α, hM, hα, h⟩ := GlobalTheory.RootIdeal.exists_count_spanSingleton_eq_mul F r
  exact ⟨M, α, hM, hα, fun v => ⟨_, h v, GlobalTheory.Idele.valuation_eq_exp_neg_count v hα⟩⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SmulMemSpanOver
namespace GlobalTheory.CompanionTheory.Ar.Num.SpanExact

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω]
  {E E₂ : Type*} [AddCommGroup E] [Module Ω E] [AddCommGroup E₂] [Module Ω E₂]

theorem smul_mem_spanOver (R : Subalgebra o Ω) (S : Set E) {a : Ω} (ha : a ∈ R) {v : E}
    (hv : v ∈ spanOver R S) : a • v ∈ spanOver R S := by
  unfold spanOver at hv ⊢
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, e, he, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * b, R.mul_mem ha hb, e, he, by rw [mul_smul]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem map_spanOver (R : Subalgebra o Ω) (S : Set E) (q : E →ₗ[Ω] E₂) :
    (spanOver R S).map q.toAddMonoidHom = spanOver R (q '' S) := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨v, ⟨a, ha, e, he, rfl⟩, rfl⟩
    exact ⟨a, ha, q e, ⟨e, he, rfl⟩, by simp⟩
  · rintro ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨a • e, ⟨a, ha, e, he, rfl⟩, by simp⟩

theorem local_step (R R₁ : Subalgebra o Ω) (hR : R ≤ R₁) (q : E →ₗ[Ω] E₂) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r : ℕ} (f : Ω) (hf : f ∈ R) (b : Fin r → E₂)
    (hb : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = ⊤)
    (hloc : ∀ e, (∃ n : ℕ, f ^ n • e ∈ L.map q.toAddMonoidHom) ↔
        ∃ a : Fin r → Ω, (∀ j, ∃ n : ℕ, f ^ n * a j ∈ R) ∧ e = ∑ j, a j • b j)
    {v : E} (hv : v ∈ spanOver R₁ (L : Set E)) (hq : q v = 0) :
    ∃ m : ℕ, f ^ m • v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := by
  classical
  have h1 : ∀ j, ∃ n : ℕ, ∃ s ∈ L, q s = f ^ n • b j := by
    intro j
    obtain ⟨n, s, hs, hs'⟩ := (hloc (b j)).2 ⟨Pi.single j 1, fun k => ⟨0, by
      by_cases h : k = j
      · subst h; simpa using R.one_mem
      · simpa [h] using R.zero_mem⟩, by simp [Pi.single_apply]⟩
    exact ⟨n, s, hs, hs'⟩
  choose n s hs hqs using h1
  set N := ∑ j, n j with hN
  have hle : ∀ j, n j ≤ N := fun j =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  let t : Fin r → E := fun j => f ^ (N - n j) • s j
  have ht : ∀ j, t j ∈ L := fun j => hL _ (R.pow_mem hf _) _ (hs j)
  have hqt : ∀ j, q (t j) = f ^ N • b j := fun j => by
    simp only [t, map_smul, hqs, smul_smul, ← pow_add, Nat.sub_add_cancel (hle j)]
  let B : Module.Basis (Fin r) Ω E₂ := Module.Basis.mk hb hsp.ge
  let σ : E₂ →ₗ[Ω] E := B.constr Ω t
  have hσ : ∀ j, σ (b j) = t j := fun j => by
    have : b j = B j := by simp [B]
    rw [this]; simp [σ]
  set S := spanOver R₁ {e | e ∈ L ∧ q e = 0} with hS
  have hup : ∀ (w : E) (m k : ℕ), f ^ m • w ∈ S → f ^ (k + m) • w ∈ S := fun w m k h => by
    rw [pow_add, mul_smul]
    exact smul_mem_spanOver R₁ _ (R₁.pow_mem (hR hf) _) h
  have key : ∃ m : ℕ, f ^ m • (f ^ N • v - σ (q v)) ∈ S := by
    clear hq
    unfold spanOver at hv
    induction hv using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, e, he, rfl⟩ := hx
      obtain ⟨c, hc, hce⟩ := (hloc (q e)).1 ⟨0, e, he, by simp⟩
      choose p hp using hc
      set M := ∑ j, p j with hM
      have hle' : ∀ j, p j ≤ M := fun j =>
        Finset.single_le_sum (f := p) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have hp' : ∀ j, f ^ M * c j ∈ R := fun j => by
        rw [← Nat.sub_add_cancel (hle' j), pow_add, mul_assoc]
        exact R.mul_mem (R.pow_mem hf _) (hp j)
      refine ⟨M, AddSubgroup.subset_closure ⟨a, ha, f ^ M • (f ^ N • e - σ (q e)), ⟨?_, ?_⟩, ?_⟩⟩
      · rw [smul_sub]
        refine sub_mem (hL _ (R.pow_mem hf _) _ (hL _ (R.pow_mem hf _) _ he)) ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hce, map_sum, Finset.smul_sum]
        refine sum_mem fun j _ => ?_
        rw [map_smul, smul_smul, hσ]
        exact hL _ (hp' j) _ (ht j)
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_smul, map_sub, map_smul, hce, map_sum, map_sum, Finset.smul_sum]
        simp only [map_smul, hσ, hqt]
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_zero, smul_zero]
        intro j _
        rw [smul_comm, sub_self]
      · simp only [map_smul]
        module
    | zero => exact ⟨0, by simpa using S.zero_mem⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, hm⟩ := hx
      obtain ⟨k, hk⟩ := hy
      refine ⟨k + m, ?_⟩
      have h2 := hup _ _ m hk
      rw [add_comm] at h2
      convert add_mem (hup _ _ k hm) h2 using 1
      simp only [map_add (f := _)]
      module
    | neg x _ hx =>
      obtain ⟨m, hm⟩ := hx
      refine ⟨m, ?_⟩
      convert neg_mem hm using 1
      simp only [map_neg]
      module
  obtain ⟨m, hm⟩ := key
  refine ⟨m + N, ?_⟩
  simpa [hq, smul_smul, pow_add] using hm

theorem mem_spanOver_ker (R R₁ : Subalgebra o Ω) (hR : R ≤ R₁) (q : E →ₗ[Ω] E₂) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r : ℕ} (hF : LocFree R r (L.map q.toAddMonoidHom))
    {v : E} (hv : v ∈ spanOver R₁ (L : Set E)) (hq : q v = 0) :
    v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := by
  obtain ⟨-, k, f, c, hf, hc, hsum, hl⟩ := hF
  let J : Ideal R :=
    { carrier := {a | (a : Ω) • v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0}}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Subalgebra.coe_add, add_smul] at ha hb ⊢
        exact add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun a b hb => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, MulMemClass.coe_mul, mul_smul] at hb ⊢
        exact smul_mem_spanOver R₁ _ (hR a.2) hb }
  have h1 : (1 : R) ∈ J.radical := by
    have : (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * ⟨f l, hf l⟩ := by
      apply Subtype.ext
      simp [hsum]
    rw [this]
    refine sum_mem fun l _ => Ideal.mul_mem_left _ _ ?_
    obtain ⟨b, hb, hsp, hloc⟩ := hl l
    obtain ⟨m, hm⟩ := local_step R R₁ hR q L hL (f l) (hf l) b hb hsp hloc hv hq
    exact ⟨m, hm⟩
  obtain ⟨m, hm⟩ := h1
  have : ((1 ^ m : R) : Ω) • v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := hm
  simpa using this

theorem span_comap_exact : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R R₁ : Subalgebra o Ω), R ≤ R₁ → ∀ {E E₁ E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] [AddCommGroup E₂] [Module Ω E₂] (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂), Function.Injective i → LinearMap.range i = LinearMap.ker q → ∀ (L : AddSubgroup E) (r₂ : ℕ), (∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) → LocFree R r₂ (L.map q.toAddMonoidHom) → (spanOver R₁ (L : Set E)).comap i.toAddMonoidHom = spanOver R₁ (L.comap i.toAddMonoidHom : Set E₁) ∧ (spanOver R₁ (L : Set E)).map q.toAddMonoidHom = spanOver R₁ (L.map q.toAddMonoidHom : Set E₂) := by
  intro o Ω _ _ _ R R₁ hR E E₁ E₂ _ _ _ _ _ _ i q hi hex L r₂ hL hF
  refine ⟨?_, ?_⟩
  · have himg : i '' (L.comap i.toAddMonoidHom : Set E₁) = {e | e ∈ L ∧ q e = 0} := by
      ext e
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx, by rw [← LinearMap.mem_ker, ← hex]; exact ⟨x, rfl⟩⟩
      · rintro ⟨he, hq⟩
        rw [← LinearMap.mem_ker, ← hex] at hq
        obtain ⟨x, rfl⟩ := hq
        exact ⟨x, he, rfl⟩
    have hmap := map_spanOver R₁ (L.comap i.toAddMonoidHom : Set E₁) i
    rw [himg] at hmap
    ext x
    constructor
    · intro hx
      have hq : q (i x) = 0 := by rw [← LinearMap.mem_ker, ← hex]; exact ⟨x, rfl⟩
      have := mem_spanOver_ker R R₁ hR q L hL hF (v := i x) hx hq
      rw [← hmap] at this
      obtain ⟨y, hy, hxy⟩ := this
      obtain rfl : y = x := hi hxy
      exact hy
    · intro hx
      have h1 : i x ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := by
        rw [← hmap]; exact ⟨x, hx, rfl⟩
      have h2 : spanOver R₁ {e | e ∈ L ∧ q e = 0} ≤ spanOver R₁ (L : Set E) :=
        AddSubgroup.closure_mono fun w ⟨a, ha, e, he, hw⟩ => ⟨a, ha, e, he.1, hw⟩
      exact h2 h1
  · rw [map_spanOver, AddSubgroup.coe_map]
    rfl

end GlobalTheory.CompanionTheory.Ar.Num.SpanExact
end
