module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocForms
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HsSum
noncomputable def UpperTheory.Reformulated.B.Qh70.Hs :
    {L V ι : Type} →
      [inst : Field L] →
        [inst_1 : Algebra ℂ L] →
          [inst_2 : AddCommGroup V] → [_root_.Module L V] → Subalgebra ℂ L → Finset ι → (ι → V) → V → Prop :=
    fun {L V ι : Type} [Field L] [Algebra ℂ L] [AddCommGroup V] [_root_.Module L V] (B : Subalgebra ℂ L) (P : Finset ι)
        (g : ι → V) (w : V) ↦
      ∃ (c : ι → L), (∀ (S : ι), c S ∈ B) ∧ w = ∑ S ∈ P, c S • g S

theorem UpperTheory.Reformulated.B.Qh70.Hs_sum :
    ∀ {L V ι : Type} [inst : Field L] [inst_1 : Algebra ℂ L] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module L V]
      {B : Subalgebra ℂ L} {P : Finset ι} {g : ι → V} {α : Type} (s : Finset α) (f : α → V),
      (∀ a ∈ s, UpperTheory.Reformulated.B.Qh70.Hs B P g (f a)) → UpperTheory.Reformulated.B.Qh70.Hs B P g (∑ a ∈ s, f a) := by
  intro L V ι _ _ _ _ B P g α s f h
  refine Finset.sum_induction f (UpperTheory.Reformulated.B.Qh70.Hs B P g) ?_ ?_ h
  · rintro a b ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    refine ⟨fun S => c S + d S, fun S => B.add_mem (hc S) (hd S), ?_⟩
    simp only [add_smul, Finset.sum_add_distrib]
  · exact ⟨fun _ => 0, fun _ => B.zero_mem, by simp⟩
end

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section LocFormsAux

private def Hs {L V ι : Type} [Field L] [Algebra ℂ L] [AddCommGroup V] [Module L V]
    (B : Subalgebra ℂ L) (P : Finset ι) (g : ι → V) (w : V) : Prop :=
  ∃ c : ι → L, (∀ S, c S ∈ B) ∧ w = ∑ S ∈ P, c S • g S

variable {L V ι : Type} [Field L] [Algebra ℂ L] [AddCommGroup V] [Module L V]
  {B : Subalgebra ℂ L} {P : Finset ι} {g : ι → V}

private lemma Hs_zero : Hs B P g 0 := ⟨fun _ => 0, fun _ => B.zero_mem, by simp⟩

private lemma Hs_add {w w' : V} (h : Hs B P g w) (h' : Hs B P g w') : Hs B P g (w + w') := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  exact ⟨fun S => c S + c' S, fun S => B.add_mem (hc S) (hc' S), by
    simp [add_smul, Finset.sum_add_distrib]⟩

private lemma Hs_smul {b : L} (hb : b ∈ B) {w : V} (h : Hs B P g w) : Hs B P g (b • w) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun S => b * c S, fun S => B.mul_mem hb (hc S), by
    simp [Finset.smul_sum, mul_smul]⟩

private lemma Hs_single [DecidableEq ι] {S : ι} (hS : S ∈ P) : Hs B P g (g S) :=
  ⟨fun T => if T = S then 1 else 0, fun T => by dsimp only; split_ifs <;> simp [B.one_mem, B.zero_mem], by
    simp [ite_smul, Finset.sum_ite_eq', hS]⟩

private lemma Hs_sum {α : Type} (s : Finset α) (f : α → V) (h : ∀ a ∈ s, Hs B P g (f a)) :
    Hs B P g (∑ a ∈ s, f a) :=
  _root_.UpperTheory.Reformulated.B.Qh70.Hs_sum s f h

private lemma alt_sorted {V : Type} [AddCommGroup V] [Module L V] {d : ℕ} (t : Fin d → V)
    (S : Finset (Fin d)) (f : Fin S.card → Fin d) (hf : Function.Injective f)
    (hS : ∀ a, f a ∈ S) :
    ∃ n : ℤ, ExteriorAlgebra.ιMulti L S.card (fun a => t (f a)) =
      (n : L) • ExteriorAlgebra.ιMulti L S.card (fun a => t (S.orderEmbOfFin rfl a)) := by
  set σ := Tuple.sort f
  have hs : StrictMono (f ∘ σ) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
  have hu : f ∘ σ = S.orderEmbOfFin rfl :=
    Finset.orderEmbOfFin_unique rfl (fun a => hS _) hs
  have hp := (ExteriorAlgebra.ιMulti L S.card (M := V)).map_perm (fun a => t (f a)) σ
  have hv : ((fun a => t (f a)) ∘ σ) = fun a => t (S.orderEmbOfFin rfl a) := by
    funext a
    simpa using congrArg t (congrFun hu a)
  rw [hv] at hp
  refine ⟨((Equiv.Perm.sign σ : ℤˣ) : ℤ), ?_⟩
  rw [hp, Int.cast_smul_eq_zsmul, ← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]

private lemma alt_expand {V : Type} [AddCommGroup V] [Module L V] {q d : ℕ} (t : Fin d → V)
    (c : Fin q → Fin d → L) :
    ExteriorAlgebra.ιMulti L q (fun j => ∑ l, c j l • t l) =
      ∑ f : Fin q → Fin d, (∏ j, c j (f j)) • ExteriorAlgebra.ιMulti L q (fun j => t (f j)) := by
  have h := (ExteriorAlgebra.ιMulti L q (M := V)).toMultilinearMap.map_sum
    (fun j l => c j l • t l)
  simp only [AlternatingMap.coe_multilinearMap] at h
  rw [h]
  refine Finset.sum_congr rfl fun f _ => ?_
  exact (ExteriorAlgebra.ιMulti L q (M := V)).toMultilinearMap.map_smul_univ _ _

end LocFormsAux

theorem UpperTheory.Gal.productCup_of_system.locForms_of :
    LocOne → LocForms := by
  intro hone F L _ _ _ _ _ _ d x hfc hr e q w
  have ht : ∀ j, tt L x j ∈ loc (rB ℂ L (xv x) {0}) e.1 := fun j =>
    ⟨1, by simp, by simpa [tt] using tco_mem ℂ L (xv x) j⟩
  constructor
  · intro hw
    change Hs _ _ _ w
    refine Submodule.span_induction ?_ Hs_zero (fun _ _ _ _ => Hs_add) ?_ hw
    · rintro _ ⟨b, hb, v, hv, rfl⟩
      refine Hs_smul hb ?_
      choose c hcB hcD using fun j => hone F L d x hfc hr e (v j) (hv j)
      simp only [hcD]
      rw [alt_expand]
      refine Hs_sum _ _ fun f _ => Hs_smul (Subalgebra.prod_mem _ fun j _ => hcB j _) ?_
      by_cases hf : Function.Injective f
      · obtain ⟨S, hS⟩ : ∃ S, S = Finset.univ.image f := ⟨_, rfl⟩
        have hcard : S.card = q := by
          rw [hS, Finset.card_image_of_injective _ hf]; simp
        subst hcard
        obtain ⟨n, hn⟩ := alt_sorted (L := L) (fun l => D ℂ L (tt L x l)) S f hf
          (fun a => by simp [hS])
        rw [hn]
        exact Hs_smul (intCast_mem _ n) (Hs_single (g := dtS L x) (by simp))
      · have : ¬ Function.Injective (fun j => D ℂ L (tt L x (f j))) := fun h =>
          hf fun a b hab => h (by simp [hab])
        rw [AlternatingMap.map_eq_zero_of_not_injective _ _ this]
        exact Hs_zero
    · intro a w _ h
      rw [← algebraMap_smul L a w]
      exact Hs_smul (Subalgebra.algebraMap_mem _ a) h
  · rintro ⟨c, hc, rfl⟩
    refine Submodule.sum_mem _ fun S hS => ?_
    have hcard := (Finset.mem_powersetCard.1 hS).2
    subst hcard
    exact Submodule.subset_span ⟨c S, hc S, fun a => tt L x (S.orderEmbOfFin rfl a),
      fun j => ht _, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PResVal
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section ResValAux
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}

private noncomputable def mono (x : Fin (d + 1) → F) (a : Fin d → ℕ) : F := ∏ l, (x l.succ / x 0) ^ a l

private lemma mono_zero (x : Fin (d + 1) → F) : mono x 0 = 1 := by simp [mono]

private lemma mono_add (x : Fin (d + 1) → F) (a b : Fin d → ℕ) : mono x (a + b) = mono x a * mono x b := by
  simp [mono, pow_add, Finset.prod_mul_distrib]

private lemma mono_closure (x : Fin (d + 1) → F) (hx : x 0 ≠ 0) (y : F)
    (hy : y ∈ Submonoid.closure {y | ∃ i ∈ ({0} : Finset (Fin (d + 1))), ∃ j, y = x j / x i}) :
    ∃ a, y = mono x a := by
  induction hy using Submonoid.closure_induction with
  | mem z hz =>
    obtain ⟨i, hi, j, rfl⟩ := hz
    rw [Finset.mem_singleton] at hi
    subst hi
    cases j using Fin.cases with
    | zero => exact ⟨0, by rw [mono_zero, div_self hx]⟩
    | succ l =>
      refine ⟨Pi.single l 1, ?_⟩
      simp only [mono]
      rw [Finset.prod_eq_single l]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · simp
  | one => exact ⟨0, (mono_zero x).symm⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    exact ⟨a + b, (mono_add x a b).symm⟩

private lemma rho_mono (x : Fin (d + 1) → F) (hx : x 0 ≠ 0) (ρ : F →ₗ[ℂ] ℂ) (hρ : IsRes ℂ x ρ) (a : Fin d → ℕ)
    (ha : a ≠ 0) : ρ (mono x a) = 0 := by
  obtain ⟨_, hρ2⟩ := hρ
  set m : Fin (d + 1) → ℤ := Fin.cons (-(∑ l, (a l : ℤ))) (fun l => (a l : ℤ)) with hm
  have hsum : ∑ j, m j = 0 := by
    rw [Fin.sum_univ_succ]
    simp [hm]
  have hne : m ≠ 0 := by
    intro h
    apply ha
    funext l
    simpa [hm] using congrFun h l.succ
  have heq : mono x a = ∏ j, x j ^ m j := by
    rw [Fin.prod_univ_succ]
    simp only [hm, Fin.cons_zero, Fin.cons_succ, zpow_natCast, zpow_neg, mono, div_pow,
      Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
    rw [show (∑ l, (a l : ℤ)) = ((∑ l, a l : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]
    ring
  rw [heq]
  exact hρ2 m hsum hne

end ResValAux

theorem UpperTheory.Gal.productCup_of_system.resVal_of :
    ValBasic → ResVal := by
  intro hval F K _ _ _ _ _ _ d x hfc ρ hρ e f hf
  obtain ⟨_, _, hBval, _⟩ := hval K (rB ℂ K (xv x) {0}) e.1
  have hx0 : xv x 0 ≠ 0 := (x 0).ne_zero
  have hmemB : ∀ g ∈ rA ℂ (xv x) {0}, algebraMap F K g ∈ rB ℂ K (xv x) {0} := by
    intro g hg
    exact (isIntegral_algebraMap : IsIntegral (rA ℂ (xv x) {0}) (algebraMap (rA ℂ (xv x) {0}) K ⟨g, hg⟩))
  have hspan : ∀ g, g ∈ rA ℂ (xv x) {0} ↔ g ∈ Submodule.span ℂ
      (Submonoid.closure {y | ∃ i ∈ ({0} : Finset (Fin (d + 1))), ∃ j, y = xv x j / xv x i} : Set F) := by
    intro g
    rw [← Algebra.adjoin_eq_span]
    rfl
  have hmono : ∀ (a : Fin d → ℕ) (h : algebraMap F K (mono (xv x) a) ∈ rB ℂ K (xv x) {0}),
      e.1 ⟨_, h⟩ = ρ (mono (xv x) a) := by
    intro a h
    by_cases ha : a = 0
    · subst ha
      have h1 : (⟨algebraMap F K (mono (xv x) 0), h⟩ : rB ℂ K (xv x) {0}) = 1 :=
        Subtype.ext (by simp [mono_zero])
      rw [h1, map_one, mono_zero, hρ.1]
    · rw [rho_mono (xv x) hx0 ρ hρ a ha]
      have h1 : (⟨algebraMap F K (mono (xv x) a), h⟩ : rB ℂ K (xv x) {0}) =
          ∏ l, (⟨algebraMap F K (xv x l.succ / xv x 0), tco_mem ℂ K (xv x) l⟩ : rB ℂ K (xv x) {0}) ^ a l :=
        Subtype.ext (by simp [mono, map_prod, map_pow])
      rw [h1, map_prod]
      obtain ⟨l, hl⟩ : ∃ l, a l ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact ha (funext hc)
      exact Finset.prod_eq_zero (Finset.mem_univ l) (by rw [map_pow, e.2 l, zero_pow hl])
  have key : ∀ g (hg : g ∈ Submodule.span ℂ
      (Submonoid.closure {y | ∃ i ∈ ({0} : Finset (Fin (d + 1))), ∃ j, y = xv x j / xv x i} : Set F))
      (h : algebraMap F K g ∈ rB ℂ K (xv x) {0}), e.1 ⟨_, h⟩ = ρ g := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem y hy =>
      intro h
      obtain ⟨a, rfl⟩ := mono_closure (xv x) hx0 y hy
      exact hmono a h
    | zero =>
      intro h
      have h1 : (⟨algebraMap F K 0, h⟩ : rB ℂ K (xv x) {0}) = 0 := Subtype.ext (map_zero _)
      rw [h1, map_zero, map_zero]
    | add y z hy hz ihy ihz =>
      intro h
      have hy' := hmemB y ((hspan y).2 hy)
      have hz' := hmemB z ((hspan z).2 hz)
      have h1 : (⟨algebraMap F K (y + z), h⟩ : rB ℂ K (xv x) {0}) = ⟨_, hy'⟩ + ⟨_, hz'⟩ :=
        Subtype.ext (map_add _ _ _)
      rw [h1, map_add (f := _), map_add (f := _), ihy hy', ihz hz']
    | smul r y hy ihy =>
      intro h
      have hy' := hmemB y ((hspan y).2 hy)
      have h1 : (⟨algebraMap F K (r • y), h⟩ : rB ℂ K (xv x) {0}) = r • ⟨_, hy'⟩ := by
        apply Subtype.ext
        show algebraMap F K (r • y) = r • algebraMap F K y
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
      rw [h1, map_smul, map_smul, ihy hy']
  have hfB := hmemB f hf
  have hv := hBval ⟨_, hfB⟩
  rw [key f ((hspan f).1 hf) hfB] at hv
  exact hv
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.TraceEqZeroOfBot
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DlogBasisAndVanishingAboveDimension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DlogBasisAndVanishingAboveDimension
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD

theorem IsFinCover.dlog_basis_and_vanish : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → (∃ b : Module.Basis (Fin d) K Ω[K⁄k], ∀ j, b j = (algebraMap F K (x j.succ / x 0))⁻¹ • D k K (algebraMap F K (x j.succ / x 0))) ∧ ∀ q, d < q → ∀ y ∈ ⋀[K]^q Ω[K⁄k], y = 0 := by
  intro k _ _ F K _ _ _ _ _ _ d x h
  obtain ⟨b, hb⟩ := h.exists_basis
  have hu : ∀ j : Fin d, (algebraMap F K (x j.succ / x 0))⁻¹ ≠ 0 := fun j =>
    inv_ne_zero ((map_ne_zero _).2 (div_ne_zero (h.pd.ne _) (h.pd.ne 0)))
  haveI : Module.Finite K Ω[K⁄k] := Module.Finite.of_basis b
  refine ⟨⟨b.unitsSMul (fun j => Units.mk0 _ (hu j)), fun j => ?_⟩, fun q hq y hy => ?_⟩
  · rw [Module.Basis.unitsSMul_apply, hb]
    rfl
  · rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨m, rfl⟩ := hz
      apply AlternatingMap.map_linearDependent
      intro hli
      have h1 := hli.fintype_card_le_finrank
      rw [Module.finrank_eq_card_basis b] at h1
      simp at h1
      omega
    | zero => rfl
    | add a c _ _ ha hc => rw [ha, hc, add_zero]
    | smul r a _ ha => rw [ha, smul_zero]

end GlobalTheory.PD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DlogBasisAndVanishingAboveDimensionStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dlog_basis_and_vanishing_above_dimension : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → (∃ b : Module.Basis (Fin d) K Ω[K⁄k], ∀ j, b j = (algebraMap F K (x j.succ / x 0))⁻¹ • D k K (algebraMap F K (x j.succ / x 0))) ∧ ∀ q, d < q → ∀ y ∈ ⋀[K]^q Ω[K⁄k], y = 0 := by
  first | (exact @GlobalTheory.PD.IsFinCover.dlog_basis_and_vanish) | (exact GlobalTheory.PD.IsFinCover.dlog_basis_and_vanish) | (intros; apply GlobalTheory.PD.IsFinCover.dlog_basis_and_vanish <;> assumption)
end
end

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem omB_eq_bot {K : Type} [Field K] [Algebra ℂ K] (B : Subalgebra ℂ K) (a : ℕ)
    (hv : ∀ y ∈ ⋀[K]^a Ω[K⁄ℂ], y = 0) : omB ℂ K B a = ⊥ := by
  unfold omB
  rw [Submodule.span_eq_bot]
  rintro y ⟨b, -, v, -, rfl⟩
  rw [hv _ (ExteriorAlgebra.ιMulti_range K a ⟨_, rfl⟩), smul_zero]

private theorem trace_eq_zero_of_bot {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (G : Finset ι → Submodule ℂ E) (hG : ∀ I, G I = ⊥) (p : ℤ)
    (f : (cech G).H p →ₗ[ℂ] (cech G).H p) : LinearMap.trace ℂ _ f = 0 := by
  have hZ : ∀ z ∈ (cech G).Z p, z = 0 := by
    intro z hz
    have hC : z ∈ cechC G p := (Submodule.mem_inf.1 hz).1
    rw [cechC, Submodule.mem_pi] at hC
    funext s
    have h1 := hC s (Set.mem_univ s)
    split_ifs at h1 <;> simpa [hG] using h1
  haveI : Subsingleton ((cech G).Z p) :=
    ⟨fun a b => Subtype.ext ((hZ a a.2).trans (hZ b b.2).symm)⟩
  haveI : Subsingleton ((cech G).H p) :=
    (Submodule.Quotient.mk_surjective _).subsingleton
  rw [Subsingleton.elim f 0, map_zero]

private theorem coeff_det_eq_zero {d a : ℕ} (hlt : d < a) (B : Matrix (Fin d) (Fin d) ℂ) :
    (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • B.map Polynomial.C)).coeff a = 0 := by
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
    Finset.powersetCard_eq_empty.2 (by simpa using hlt), Finset.sum_empty]

private theorem val_div {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ)
    (c g : L) (hc : c ∈ B) (hg : g ∈ B) (hne : e ⟨c, hc⟩ ≠ 0) (t : ℂ)
    (h : e ⟨g, hg⟩ = e ⟨c, hc⟩ * t) (hc0 : c ≠ 0) : Val B e (g / c) t := by
  have hcg : c * (g / c) = g := by
    rw [mul_comm]
    exact div_mul_cancel₀ g hc0
  have hmem : c * (g / c) ∈ B := by
    rw [hcg]
    exact hg
  refine ⟨c, hc, hmem, hne, ?_⟩
  have hsub : (⟨c * (g / c), hmem⟩ : B) = ⟨g, hg⟩ := Subtype.ext hcg
  rw [hsub, h]

theorem UpperTheory.Gal.productCup_of_system.field0_of :
    FieldLe → ValBasic → Field0 := by
  intro hLe _
  intro d a F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ x j2 hK hK' hred hnf hz hfix Fx hFx hgen A hA hdet u hu hfd
  by_cases had : a ≤ d
  · have hne : ∀ i, x i ≠ 0 := hK.pd.ne
    let xu : Fin (d + 1) → Fˣ := fun i => Units.mk0 (x i) (hne i)
    have hY : Y1 xu j2 Fx A :=
      { covZ := hK
        covY := hK'
        cov := by
          intro i e
          obtain ⟨j, hj⟩ := hred i e
          refine ⟨j, fun v hv => ?_⟩
          obtain ⟨b, hb, he, hbv⟩ := hj v hv
          exact ⟨⟨b, hb⟩, he, hbv⟩
        red := hnf
        off := hz
        orig := hfix
        fx := hFx
        tan := by
          intro e he m
          obtain ⟨c, hc, g, hg, hec, hsum, hgl⟩ := hA e he m
          have hc0 : c ≠ 0 := by
            rintro rfl
            apply hec
            have h0 : (⟨0, hc⟩ : rB ℂ K' x {0}) = 0 := rfl
            rw [h0, map_zero]
          refine ⟨fun l => g l / c, fun l => val_div _ _ c (g l) hc (hg l) hec _ (hgl l) hc0, ?_⟩
          show j2 (algebraMap F K (x m.succ / x 0)) = ∑ l, g l / c * algebraMap F K' (x l.succ / x 0)
          apply mul_left_cancel₀ hc0
          rw [hsum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← mul_assoc, mul_comm c, div_mul_cancel₀ _ hc0]
        det := hdet }
    exact hLe F K K' d xu j2 Fx A hY a had u hu
  · push_neg at had
    have hv := (GlobalTheory.T.dlog_basis_and_vanishing_above_dimension ℂ F K d x hK).2 a had
    refine (Finset.sum_eq_zero fun p _ => ?_).trans (Finset.sum_eq_zero fun e _ => ?_).symm
    · rw [trace_eq_zero_of_bot _ (fun I => omB_eq_bot _ a hv) _ (u p), mul_zero]
    · rw [coeff_det_eq_zero had, zero_div]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ChineseRemainderFiniteCover
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsOfLi
theorem UpperTheory.Reformulated.B.Qe54.exists_of_li :
    ∀ {Q ι : Type} [inst : AddCommGroup Q]
    [inst_1 : _root_.Module ℂ Q] [Finite ι] (f : ι → Q →ₗ[ℂ] ℂ),
    LinearIndependent ℂ f → ∀ (v : ι → ℂ), ∃ (q : Q), ∀ (i : ι), (f i : Q → ℂ) q = v i := by
  intro Q ι _ _ _ f hf v
  classical
  have := Fintype.ofFinite ι
  have hs : Function.Surjective (LinearMap.pi f : Q →ₗ[ℂ] (ι → ℂ)) := by
    rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
    intro φ hφ
    have hsum : ∑ i, φ (fun j => if i = j then 1 else 0) • f i = 0 := by
      ext q
      have h1 : φ (LinearMap.pi f q) = 0 := LinearMap.congr_fun hφ q
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      simpa [LinearMap.sum_apply, mul_comm] using h1
    have h0 := Fintype.linearIndependent_iff.1 hf _ hsum
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp [h0]
  obtain ⟨q, hq⟩ := hs v
  exact ⟨q, fun i => congrFun hq i⟩
end

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem exists_of_li {Q ι : Type} [AddCommGroup Q] [Module ℂ Q] [Finite ι] (f : ι → Q →ₗ[ℂ] ℂ)
    (h : LinearIndependent ℂ f) (v : ι → ℂ) : ∃ q, ∀ i, f i q = v i :=
  _root_.UpperTheory.Reformulated.B.Qe54.exists_of_li f h v

private theorem chineseRemainder_finiteCover {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K]
    [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) (hc : IsFinCover ℂ K x) :
    Finite (fib ℂ K x) ∧ ∀ v : fib ℂ K x → ℂ, ∃ h : rB ℂ K x {0}, ∀ e, e.1 h = v e := by
  set_option synthInstance.maxHeartbeats 200000 in
    classical
    let I : Ideal (rB ℂ K x {0}) :=
      Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K x j⟩ : rB ℂ K x {0}))
    let mk : rB ℂ K x {0} →ₐ[ℂ] (rB ℂ K x {0} ⧸ I) := Ideal.Quotient.mkₐ ℂ I
    have hfin := (GlobalTheory.T.finite_cover_chart_smooth_normal ℂ F K d x hc {0} (Finset.singleton_nonempty 0)).1
    have hmem : ∀ y (hy : y ∈ rA ℂ x {0}), algebraMap F K y ∈ rB ℂ K x {0} := fun y hy =>
      (integralClosure (rA ℂ x {0}) K).algebraMap_mem ⟨y, hy⟩
    have hA : ∀ y (hy : y ∈ rA ℂ x {0}), ∃ c : ℂ,
        mk ⟨algebraMap F K y, hmem y hy⟩ = algebraMap ℂ _ c := by
      intro y hy
      refine Algebra.adjoin_induction (p := fun y hy => ∃ c : ℂ,
        mk ⟨algebraMap F K y, hmem y hy⟩ = algebraMap ℂ _ c) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨i, hi, j, rfl⟩
        obtain rfl : i = 0 := Finset.mem_singleton.1 hi
        induction j using Fin.cases with
        | zero =>
          refine ⟨1, ?_⟩
          rw [map_one, ← map_one mk]
          congr 1
          ext
          simp [div_self (hc.pd.ne 0)]
        | succ j =>
          refine ⟨0, ?_⟩
          rw [map_zero]
          exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
      · intro r
        refine ⟨r, ?_⟩
        rw [← mk.commutes r]
        congr 1
        ext
        simp [← IsScalarTower.algebraMap_apply]
      · rintro a b ha hb ⟨c, hc1⟩ ⟨c', hc2⟩
        refine ⟨c + c', ?_⟩
        have e : (⟨algebraMap F K (a + b), hmem _ (add_mem ha hb)⟩ : rB ℂ K x {0}) =
            ⟨_, hmem a ha⟩ + ⟨_, hmem b hb⟩ := Subtype.ext (map_add _ _ _)
        exact (congrArg mk e).trans (by rw [map_add mk, hc1, hc2, map_add (algebraMap ℂ _)])
      · rintro a b ha hb ⟨c, hc1⟩ ⟨c', hc2⟩
        refine ⟨c * c', ?_⟩
        have e : (⟨algebraMap F K (a * b), hmem _ (mul_mem ha hb)⟩ : rB ℂ K x {0}) =
            ⟨_, hmem a ha⟩ * ⟨_, hmem b hb⟩ := Subtype.ext (map_mul _ _ _)
        exact (congrArg mk e).trans (by rw [map_mul, hc1, hc2, map_mul])
    have hQ : Module.Finite ℂ (rB ℂ K x {0} ⧸ I) := by
      obtain ⟨s, hs⟩ := hfin.fg_top
      let g : integralClosure (rA ℂ x {0}) K → (rB ℂ K x {0} ⧸ I) := fun y => mk ⟨y.1, y.2⟩
      have key : ∀ y, y ∈ Submodule.span (rA ℂ x {0}) (s : Set (integralClosure (rA ℂ x {0}) K)) →
          g y ∈ Submodule.span ℂ (g '' (s : Set (integralClosure (rA ℂ x {0}) K))) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
        | zero =>
          have h0 : g 0 = 0 := map_zero mk
          rw [h0]
          exact Submodule.zero_mem _
        | add a b _ _ ha hb =>
          have : g (a + b) = g a + g b := by
            simp only [g, ← map_add (f := _)]
            rfl
          rw [this]
          exact Submodule.add_mem _ ha hb
        | smul a y _ hy =>
          obtain ⟨c, hc1⟩ := hA a.1 a.2
          have e : (⟨((a • y : integralClosure (rA ℂ x {0}) K)).1, ((a • y : integralClosure (rA ℂ x {0}) K)).2⟩ : rB ℂ K x {0}) = ⟨_, hmem a.1 a.2⟩ * ⟨y.1, y.2⟩ :=
            Subtype.ext (Algebra.smul_def a y.1)
          have : g (a • y) = c • g y :=
            (congrArg mk e).trans (by rw [map_mul, hc1, ← Algebra.smul_def])
          rw [this]
          exact Submodule.smul_mem _ _ hy
      refine ⟨⟨(s.image g), ?_⟩⟩
      rw [eq_top_iff]
      rintro q -
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
      have := key ⟨b.1, b.2⟩ (hs ▸ Submodule.mem_top)
      rw [Finset.coe_image]
      exact this
    have hker : ∀ e : fib ℂ K x, ∀ a ∈ I, e.1 a = 0 := by
      intro e a ha
      have : I ≤ RingHom.ker (e.1 : rB ℂ K x {0} →+* ℂ) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨j, rfl⟩
        exact e.2 j
      exact this ha
    let L : fib ℂ K x → ((rB ℂ K x {0} ⧸ I) →ₐ[ℂ] ℂ) := fun e => Ideal.Quotient.liftₐ I e.1 (hker e)
    have hL : ∀ e b, L e (mk b) = e.1 b := fun e b => by
      first | rfl | exact Ideal.Quotient.lift_mk _ _ _
    have hinj : Function.Injective L := by
      intro e e' h
      refine Subtype.ext (AlgHom.ext fun b => ?_)
      rw [← hL, ← hL, h]
    have li : LinearIndependent ℂ (fun e => (L e).toLinearMap) :=
      (linearIndependent_algHom_toLinearMap' ℂ (rB ℂ K x {0} ⧸ I) ℂ).comp L hinj
    have hF : Finite (fib ℂ K x) := li.finite
    refine ⟨hF, fun v => ?_⟩
    obtain ⟨q, hq⟩ := exists_of_li _ li v
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨b, fun e => ?_⟩
    rw [← hq e, ← hL]
    rfl

theorem UpperTheory.Gal.productCup_of_system.cRT_of :
    CRT := by
  intro F K _ _ _ _ _ _ d x hc
  exact chineseRemainder_finiteCover (xv x) hc
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocEq
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section LocEqAux
variable {L : Type} [Field L] [Algebra ℂ L]

private def locRes {R B : Subalgebra ℂ L} (h : R ≤ B) (e : B →ₐ[ℂ] ℂ) : R →ₐ[ℂ] ℂ :=
  e.comp (Subalgebra.inclusion h)

private lemma loc_val_eq {R B : Subalgebra ℂ L} (h : R ≤ B) (e : B →ₐ[ℂ] ℂ)
    (hB : B ≤ loc R (locRes h e)) :
    loc B e = loc R (locRes h e) ∧ ∀ v c, Val B e v c ↔ Val R (locRes h e) v c := by
  have key : ∀ {b v : L} (hb : b ∈ B) (hbv : b * v ∈ B),
      ∃ t : L, ∃ (ht : t ∈ B), e ⟨t, ht⟩ ≠ 0 ∧ t * b ∈ R ∧ t * b * v ∈ R := by
    intro b v hb hbv
    obtain ⟨⟨r, hr⟩, hr0, hrb⟩ := hB hb
    obtain ⟨⟨r', hr'⟩, hr'0, hr'bv⟩ := hB hbv
    refine ⟨r' * r, B.mul_mem (h hr') (h hr), ?_, ?_, ?_⟩
    · rw [show (⟨r' * r, B.mul_mem (h hr') (h hr)⟩ : B) = ⟨r', h hr'⟩ * ⟨r, h hr⟩ from rfl, map_mul]
      exact mul_ne_zero hr'0 hr0
    · rw [mul_assoc]
      exact R.mul_mem hr' hrb
    · have hre : r' * r * b * v = r * (r' * (b * v)) := by ring
      rw [hre]
      exact R.mul_mem hr hr'bv
  refine ⟨le_antisymm ?_ ?_, fun v c => ⟨?_, ?_⟩⟩
  · rintro v ⟨⟨b, hb⟩, hb0, hbv⟩
    obtain ⟨t, ht, ht0, htb, htbv⟩ := key hb hbv
    refine ⟨⟨t * b, htb⟩, ?_, htbv⟩
    show e ⟨t * b, h htb⟩ ≠ 0
    rw [show (⟨t * b, h htb⟩ : B) = ⟨t, ht⟩ * ⟨b, hb⟩ from rfl, map_mul]
    exact mul_ne_zero ht0 hb0
  · rintro v ⟨⟨r, hr⟩, hr0, hrv⟩
    exact ⟨⟨r, h hr⟩, hr0, h hrv⟩
  · rintro ⟨b, hb, hbv, hb0, hval⟩
    obtain ⟨t, ht, ht0, htb, htbv⟩ := key hb hbv
    refine ⟨t * b, htb, htbv, ?_, ?_⟩
    · show e ⟨t * b, h htb⟩ ≠ 0
      rw [show (⟨t * b, h htb⟩ : B) = ⟨t, ht⟩ * ⟨b, hb⟩ from rfl, map_mul]
      exact mul_ne_zero ht0 hb0
    · show e ⟨t * b * v, h htbv⟩ = e ⟨t * b, h htb⟩ * c
      rw [show (⟨t * b * v, h htbv⟩ : B) = ⟨t, ht⟩ * ⟨b * v, hbv⟩ from Subtype.ext (mul_assoc _ _ _),
        show (⟨t * b, h htb⟩ : B) = ⟨t, ht⟩ * ⟨b, hb⟩ from rfl, map_mul, map_mul, hval, mul_assoc]
  · rintro ⟨r, hr, hrv, hr0, hval⟩
    exact ⟨r, h hr, h hrv, hr0, hval⟩

end LocEqAux

section LocEqAux2

private lemma mem_rB_of {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L]
    [IsScalarTower ℂ F L] {d : ℕ} (x : Fin (d + 1) → F) (I : Finset (Fin (d + 1))) {f : F}
    (hf : f ∈ rA ℂ x I) : algebraMap F L f ∈ rB ℂ L x I := by
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  have hx : algebraMap F L f = algebraMap (rA ℂ x I) L ⟨f, hf⟩ := rfl
  rw [hx]
  exact isIntegral_algebraMap

private lemma div_mem_rA {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} (x : Fin (d + 1) → F)
    {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (j : Fin (d + 1)) :
    x j / x i ∈ rA ℂ x I :=
  Algebra.subset_adjoin ⟨i, hi, j, rfl⟩

end LocEqAux2

theorem UpperTheory.Gal.productCup_of_system.locEq_of :
    ValBasic → RYBasic → LocEq := by
  intro hV hY F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY0 I J i hi e
  obtain ⟨hRY0, -, hmono, h4, h5⟩ := hY F K K' d x j2 hY0
  have hRB : rB ℂ K' (xv x) {i} ≤ RY (xv x) j2 I J := by
    have hle := hmono {i} I ∅ J (Finset.singleton_subset_iff.mpr hi) (Finset.empty_subset _)
    rwa [hRY0] at hle
  obtain ⟨hRloc, -, -, hinv⟩ := hV K' (rB ℂ K' (xv x) {i}) (locRes hRB e)
  obtain ⟨j, hj⟩ := hY0.cov i (locRes hRB e)
  have hIB : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J := le_sup_left
  have hR2B : R2 (xv x) j2 J ≤ RY (xv x) j2 I J := le_sup_right
  have unit_lemma : ∀ {y w w' : K'}, w ∈ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) →
      w' ∈ RY (xv x) j2 I J → w * w' = 1 → y * w ∈ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) →
      y ∈ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) := by
    intro y w w' hw hw' hww hyw
    obtain ⟨⟨b, hbR⟩, hb0, hbw⟩ := hw
    have hne : locRes hRB e ⟨b * w, hbw⟩ ≠ 0 := by
      intro h0
      have hprod : e ⟨b * w, hRB hbw⟩ * e ⟨w', hw'⟩ = e ⟨b, hRB hbR⟩ := by
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        show b * w * w' = b
        rw [mul_assoc, hww, mul_one]
      rw [show e ⟨b * w, hRB hbw⟩ = 0 from h0, zero_mul] at hprod
      exact hb0 hprod.symm
    have hval : Val (rB ℂ K' (xv x) {i}) (locRes hRB e) w
        (locRes hRB e ⟨b * w, hbw⟩ / locRes hRB e ⟨b, hbR⟩) := by
      refine ⟨b, hbR, hbw, hb0, ?_⟩
      field_simp
    obtain ⟨hw0, hwinv⟩ := hinv w _ hval (div_ne_zero hne hb0)
    have hy : y = (y * w) * w⁻¹ := by field_simp
    rw [hy]
    exact Subalgebra.mul_mem _ hyw hwinv
  have hI : rB ℂ K' (xv x) I ≤ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) := by
    intro y hy
    obtain ⟨N, hN⟩ := ((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K' d (xv x) hY0.covY I i hi).2 y).1 hy
    refine unit_lemma (w := algebraMap F K' (∏ a ∈ I, xv x a / xv x i) ^ N)
      (w' := algebraMap F K' (∏ a ∈ I, xv x i / xv x a) ^ N) ?_ ?_ ?_ (hRloc hN)
    · exact hRloc (Subalgebra.pow_mem _ (mem_rB_of (L := K') (xv x) {i}
        (Subalgebra.prod_mem _ (fun a _ => div_mem_rA (xv x) (Finset.mem_singleton_self i) a))) N)
    · exact hIB (Subalgebra.pow_mem _ (mem_rB_of (L := K') (xv x) I
        (Subalgebra.prod_mem _ (fun a ha => div_mem_rA (xv x) ha i))) N)
    · rw [← mul_pow, ← map_mul, ← Finset.prod_mul_distrib]
      rw [Finset.prod_eq_one (fun a _ => by
        rw [div_mul_div_comm, mul_comm (xv x a), div_self (mul_ne_zero (x i).ne_zero (x a).ne_zero)])]
      rw [map_one, one_pow]
  have hR2 : ∀ S : Finset (Fin (d + 1)), S ⊆ J →
      R2 (xv x) j2 (insert j S) ≤ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.insert_empty]
      exact hj
    | insert m S hmS ih =>
      intro hS y hy
      rw [Finset.insert_comm] at hy
      obtain ⟨N, hN⟩ := h5 (insert j S) j (Finset.mem_insert_self _ _) m y hy
      have hmJ : m ∈ J := hS (Finset.mem_insert_self _ _)
      refine unit_lemma (w := j2 (algebraMap F K (xv x m / xv x j)) ^ N)
        (w' := j2 (algebraMap F K (xv x j / xv x m)) ^ N) ?_ ?_ ?_
        (ih (fun a ha => hS (Finset.mem_insert_of_mem ha)) hN)
      · exact Subalgebra.pow_mem _ (hj (h4 {j} _ (mem_rB_of (L := K) (xv x) {j}
          (div_mem_rA (xv x) (Finset.mem_singleton_self j) m))).2) N
      · exact Subalgebra.pow_mem _ (hR2B (h4 J _ (mem_rB_of (L := K) (xv x) J
          (div_mem_rA (xv x) hmJ j))).2) N
      · rw [← mul_pow, ← map_mul, ← map_mul, div_mul_div_comm, mul_comm (xv x m),
          div_self (mul_ne_zero (x j).ne_zero (x m).ne_zero), map_one, map_one, one_pow]
  have hB : RY (xv x) j2 I J ≤ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) := by
    refine le_trans (hmono I I J (insert j J) (subset_refl _) (Finset.subset_insert _ _)) ?_
    exact sup_le hI (hR2 J (subset_refl _))
  obtain ⟨h1, h2⟩ := loc_val_eq hRB e hB
  exact ⟨locRes hRB e, h1, h2⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PYCols
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma pk_mem' {d : ℕ} {I : Finset (Fin (d + 1))} (h : I.Nonempty) : pk I ∈ I := by
  rw [pk, dite_eq_left h]
  exact Finset.min'_mem I h

private lemma pk_zero' {d : ℕ} : pk ({0} : Finset (Fin (d + 1))) = 0 := by
  simp [pk]

private lemma inSp_sub {S κ κ' : Type} [CommRing S] [Algebra ℂ S] [Fintype κ] [Fintype κ']
    (R : Subalgebra ℂ S) (r : κ → S) (f : κ' → κ) {g : S} (h : InSp R (fun a => r (f a)) g) : InSp R r g := by
  classical
  obtain ⟨a, ha, rfl⟩ := h
  refine ⟨fun l => ∑ b ∈ Finset.univ.filter (fun b => f b = l), a b, fun l => R.sum_mem fun b _ => ha b, ?_⟩
  simp only [Finset.sum_mul]
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := f) (f := fun b => a b * r (f b))]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun b hb => ?_
  rw [(Finset.mem_filter.mp hb).2]

private lemma inSp_self {S κ : Type} [CommRing S] [Algebra ℂ S] [Fintype κ]
    (R : Subalgebra ℂ S) (r : κ → S) (l : κ) : InSp R r (r l) := by
  classical
  refine ⟨fun l' => if l' = l then 1 else 0, fun l' => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  · simp

private lemma col_of_kos (hRS : RS) {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) {κ : Type} [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → S) (I J : Finset (Fin (d + 1))) (m : ℤ)
    (h : (kos T.act (T.M I J) (T.r n z (pk I) (pk J))).Z m ≤ (kos T.act (T.M I J) (T.r n z (pk I) (pk J))).B m) :
    (T.colCx n z I J).Z m ≤ (T.colCx n z I J).B m := by
  intro c hc
  have H := hRS S E T.act κ (T.M I J) (T.u n (pk I) (pk J)) (T.r n z (pk I) (pk J)) z (fun l => rfl) m c
  exact H.2.2.1.2 (h (H.2.1.1 hc))

private lemma admissible_append {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) {κ κ' : Type} [LinearOrder κ] [LinearOrder κ'] (n : κ → ℕ × ℕ) (z : κ → S)
    (n' : κ' → ℕ × ℕ) (z' : κ' → S) (h : T.admitted n z) (h' : T.admitted n' z') : T.admitted (app n n') (app z z') := by
  intro i j l
  rcases hl : ofLex l with a | a
  · have := h i j a
    simpa [Sys.r, Sys.u, app, hl] using this
  · have := h' i j a
    simpa [Sys.r, Sys.u, app, hl] using this

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] {d : ℕ}
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')

private lemma gS_X (i : Fin (d + 1)) :
    Units.map ((gS j2 : K ⊗[ℂ] K →ₐ[ℂ] K') : K ⊗[ℂ] K →* K') ((sysZ K x 0).X i) = (sysY x j2 d).X i := by
  ext
  simp [sysZ, sysY, gS, ← IsScalarTower.algebraMap_apply]

private lemma gS_Y (i : Fin (d + 1)) :
    Units.map ((gS j2 : K ⊗[ℂ] K →ₐ[ℂ] K') : K ⊗[ℂ] K →* K') ((sysZ K x 0).Y i) = (sysY x j2 d).Y i := by
  ext
  simp [sysZ, sysY, gS]

private lemma gS_r {κ : Type} [LinearOrder κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K) (i j : Fin (d + 1)) (k : κ) :
    gS j2 ((sysZ K x 0).r n z i j k) = (sysY x j2 d).r n (fun l => gS j2 (z l)) i j k := by
  simp only [Sys.r, Sys.u, map_mul]
  congr 1
  have := congrArg (fun v : K'ˣ => ((v⁻¹ : K'ˣ) : K'))
    (show Units.map ((gS j2 : K ⊗[ℂ] K →ₐ[ℂ] K') : K ⊗[ℂ] K →* K')
        ((sysZ K x 0).X i ^ (n k).1 * (sysZ K x 0).Y j ^ (n k).2) =
        (sysY x j2 d).X i ^ (n k).1 * (sysY x j2 d).Y j ^ (n k).2 by
      rw [map_mul, map_pow, map_pow, gS_X x j2, gS_Y x j2])
  simpa [Units.coe_map_inv] using this

private lemma rT (i j : Fin (d + 1)) (l : Fin d) (hi : i = 0) :
    (sysY x j2 d).r n10 (gT x j2) i j l = tt K' x l := by
  subst hi
  simp [Sys.r, Sys.u, n10, gT, sysY, tt, div_eq_mul_inv]

private lemma cols_gen (hKE : YKE) (hOk : SysOk) (hRS : RS) (h0 : Y0 x j2) (hG : (sysY x j2 d).Good)
    {κ : Type} [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → K') (ha : (sysY x j2 d).admitted n z)
    (I J : Finset (Fin (d + 1))) (hI : I.Nonempty) (hJ : J.Nonempty) :
    ((∀ e : RY (xv x) j2 I J →ₐ[ℂ] ℂ, (∀ l, Val (RY (xv x) j2 I J) e ((sysY x j2 d).r n z (pk I) (pk J) l) 0) →
        ∃ e0, Over x j2 e e0 ∧ ∀ l, InSp (loc (rB ℂ K' (xv x) {0}) e0.1) ((sysY x j2 d).r n z (pk I) (pk J)) (tt K' x l)) →
      KE ((sysY x j2 d).colCx n z I J) d) ∧
    ((∀ e : RY (xv x) j2 I J →ₐ[ℂ] ℂ, ¬ ∀ l, Val (RY (xv x) j2 I J) e ((sysY x j2 d).r n z (pk I) (pk J) l) 0) →
      ∀ m, ((sysY x j2 d).colCx n z I J).Z m ≤ ((sysY x j2 d).colCx n z I J).B m) := by
  have hr : ∀ l, (sysY x j2 d).r n z (pk I) (pk J) l ∈ RY (xv x) j2 I J :=
    ((hOk d K' (DR ℂ K') (sysY x j2 d) κ n z hG ha).2.1 I J _ (pk_mem' hI) _ (pk_mem' hJ)).1
  have hk := hKE F K K' d x j2 h0 κ ((sysY x j2 d).r n z (pk I) (pk J)) I J hI hr
  exact ⟨fun h m hm => col_of_kos hRS _ n z I J m (hk.1 h m hm),
    fun h m => col_of_kos hRS _ n z I J m fun c hc => hk.2.1 m c hc fun e he => absurd he (h e)⟩

end

theorem UpperTheory.Gal.productCup_of_system.yCols_of :
    YKE → PtG → PtT → FixLoc → GMap → ThMuLat → SysOk → RS → RYBasic → YCols := by
  intro hKE hPtG hPtT hFix hGM hTh hOk hRS hRY F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY κ _ _ n z hZ
  have h0 : Y0 x j2 := hY.toY0
  have hG : (sysY x j2 d).Good := (hRY F K K' d x j2 h0).2.1 d
  have hA0 : (sysY x j2 d).admitted n11 (sysY x j2 d).mu := (hTh d K' (DR ℂ K') (sysY x j2 d) hG).1
  have hAz : (sysY x j2 d).admitted n (fun l => gS j2 (z l)) := fun i j k => by
    have h2 := (hGM F K K' d x j2 h0 0 (Nat.zero_le _)).2.2.1 {i} {j} _ (hZ.adm i j k)
    rw [gS_r] at h2
    exact h2
  have hA1 : (sysY x j2 d).admitted (app n11 n) (gG x j2 z) := admissible_append _ _ _ _ _ hA0 hAz
  have hA2 : (sysY x j2 d).admitted n10 (gT x j2) := fun i j l => by
    have := hG.memX {i} {j} (Finset.singleton_nonempty j) i (Finset.mem_singleton_self i) l.succ
    simpa [Sys.r, Sys.u, n10, gT] using this
  have hA3 : (sysY x j2 d).admitted (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) := admissible_append _ _ _ _ _ hA1 hA2
  refine ⟨hA1, hA2, hA3, fun I J hI hJ => ?_⟩
  have c1 := cols_gen x j2 hKE hOk hRS h0 hG _ _ hA1 I J hI hJ
  have c2 := cols_gen x j2 hKE hOk hRS h0 hG _ _ hA2 I J hI hJ
  have c3 := cols_gen x j2 hKE hOk hRS h0 hG _ _ hA3 I J hI hJ
  have hi := pk_mem' hI
  have hj := pk_mem' hJ
  have pG : ∀ e : RY (xv x) j2 I J →ₐ[ℂ] ℂ,
      (∀ l, Val (RY (xv x) j2 I J) e ((sysY x j2 d).r (app n11 n) (gG x j2 z) (pk I) (pk J) l) 0) →
      J = {0} ∧ ∃ e0 ∈ Fx, Over x j2 e e0 :=
    fun e he => hPtG F K K' d x j2 Fx A hY κ n z hZ I J _ hi _ hj e he
  have pT : ∀ e : RY (xv x) j2 I J →ₐ[ℂ] ℂ,
      (∀ l, Val (RY (xv x) j2 I J) e ((sysY x j2 d).r n10 (gT x j2) (pk I) (pk J) l) 0) →
      ∃ e0, Over x j2 e e0 :=
    fun e he => hPtT F K K' d x j2 h0 I J _ hi _ hj e he
  refine ⟨c1.1 ?_, c2.1 ?_, c3.1 ?_, fun hne m => ⟨c1.2 ?_ m, c3.2 ?_ m⟩⟩
  · intro e he
    obtain ⟨hJ0, e0, he0, hO⟩ := pG e he
    refine ⟨e0, hO, fun l => ?_⟩
    rw [hO.1, hJ0, pk_zero']
    obtain ⟨N, -, -, -, hN⟩ := hFix F K K' d x j2 Fx A hY e0 he0
    exact inSp_sub _ ((sysY x j2 d).r (app n11 n) (gG x j2 z) 0 0) (fun a => toLex (Sum.inl (dj 0 a))) (hN l)
  · intro e he
    obtain ⟨e0, hO⟩ := pT e he
    refine ⟨e0, hO, fun l => ?_⟩
    rw [← rT x j2 (pk I) (pk J) l (by rw [hO.1, pk_zero'])]
    exact inSp_self _ _ l
  · intro e he
    obtain ⟨e0, hO⟩ := pT e fun l => he (toLex (Sum.inr l))
    refine ⟨e0, hO, fun l => ?_⟩
    rw [← rT x j2 (pk I) (pk J) l (by rw [hO.1, pk_zero'])]
    exact inSp_sub _ ((sysY x j2 d).r (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) (pk I) (pk J))
      (fun a => toLex (Sum.inr a)) (inSp_self _ ((sysY x j2 d).r n10 (gT x j2) (pk I) (pk J)) l)
  · intro e he
    obtain ⟨hJ0, e0, -, hO⟩ := pG e he
    exact hne.elim (fun h => h hO.1) (fun h => h hJ0)
  · intro e he
    obtain ⟨hJ0, e0, -, hO⟩ := pG e fun l => he (toLex (Sum.inl l))
    exact hne.elim (fun h => h hO.1) (fun h => h hJ0)
end
