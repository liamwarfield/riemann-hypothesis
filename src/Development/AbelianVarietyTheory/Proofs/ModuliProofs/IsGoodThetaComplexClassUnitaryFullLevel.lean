module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GoodThetaClassOfLatticeFamilies
public import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsFiniteUnitaryClassesOfDualEqSmul
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELObjectOfPrimitivePeriodMapUniformised
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPeriodsComplexPELObject

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteMarkedDataInGenus
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteClassesOfTraceFormDualEq
namespace GlobalTheory.DatumClasses

section Varying

open Module Submodule NumberField GlobalTheory.HermClass

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_finite_classes_of_forms {V : Type} [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] {α : Type*}
    (h : α → V →ₗ[E] V →ₗ⋆[E] E) (hs : ∀ a x y, h a y x = star (h a x y))
    (hnd : ∀ a y, (∀ x, h a y x = 0) → y = 0) {N : ℤ} (hN : N ≠ 0)
    (Λ : α → Submodule ℤ V)
    (hfg : ∀ a, (Λ a).FG) (hsp : ∀ a, span E (Λ a : Set V) = ⊤)
    (hO : ∀ a, ∀ c : E, IsIntegral ℤ c → ∀ x ∈ Λ a, c • x ∈ Λ a)
    (hint : ∀ a, ∀ x ∈ Λ a, ∀ y ∈ Λ a, IsIntegral ℤ (h a x y))
    (hdual : ∀ a y, (∀ x ∈ Λ a, IsIntegral ℤ (h a y x)) → (N : E) • y ∈ Λ a) :
    ∃ S : Set α, S.Finite ∧ ∀ a, ∃ s ∈ S, ∃ γ : V ≃ₗ[E] V, (∀ x y, h s (γ x) (γ y) = h a x y) ∧
      ∀ x, x ∈ Λ a ↔ γ x ∈ Λ s := by
  classical
  set n := finrank E V with hn
  obtain ⟨D, hD, hD0, H⟩ := exists_finite_orthogonal_lengths (E := E) n hN
  obtain ⟨M, hM, hMD⟩ := exists_int_mul_isIntegral E (hD.image fun a => a⁻¹)
  choose v hvΛ hvo hvD using fun a =>
    H V (h a) (Λ a) rfl (hs a) (hnd a) (hfg a) (hsp a) (hO a) (hint a) (hdual a)
  have hv0 : ∀ a i, h a (v a i) (v a i) ≠ 0 := fun a i h0 => hD0 (h0 ▸ hvD a i)
  have hsum : ∀ a (c : Fin n → E) j,
      h a (∑ i, c i • v a i) (v a j) = c j * h a (v a j) (v a j) := by
    intro a c j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [hvo a i j hij]
    · simp
  have hli : ∀ a, LinearIndependent E (v a) := fun a => Fintype.linearIndependent_iff.2
    fun c hc j => by
      have := hsum a c j
      rw [hc, map_zero, LinearMap.zero_apply] at this
      exact (mul_eq_zero.1 this.symm).resolve_right (hv0 a j)
  let B : α → Basis (Fin n) E V := fun a =>
    basisOfLinearIndependentOfCardEqFinrank' (v a) (hli a) (by simp [hn])
  have hB : ∀ a i, B a i = v a i := fun a i => by simp [B]
  let φ : α → V ≃ₗ[E] (Fin n → E) := fun a => (B a).equivFun
  have hφ : ∀ a c, (φ a).symm c = ∑ i, c i • v a i := fun a c => by
    simp [φ, Basis.equivFun_symm_apply, hB]
  have hform : ∀ a c c', h a ((φ a).symm c) ((φ a).symm c') =
      ∑ j, star (c' j) * (c j * h a (v a j) (v a j)) := fun a c c' => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hφ, hφ, map_sum (h a _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smulₛₗ, hsum, starRingEnd_apply, smul_eq_mul]
  let L : α → Submodule ℤ (Fin n → E) := fun a => (Λ a).map ((φ a).toLinearMap.restrictScalars ℤ)
  have hL : ∀ a c, c ∈ L a ↔ (φ a).symm c ∈ Λ a := fun a c =>
    ⟨by rintro ⟨x, hx, rfl⟩; simpa using hx, fun hc => ⟨_, hc, by simp⟩⟩
  let L₀ : Submodule ℤ (Fin n → E) :=
    Submodule.pi Set.univ fun _ => Subalgebra.toSubmodule (integralClosure ℤ E)
  have hL₀ : L₀.FG := Submodule.fg_pi fun _ => fg_integers E
  have hLF : ∀ a, L₀ ≤ L a ∧ ∀ x ∈ L a, (M : E) • x ∈ L₀ := fun a => by
    refine ⟨fun c hc => ?_, fun c hc j _ => ?_⟩
    · rw [hL, hφ]
      exact sum_mem fun i _ => hO a _ (hc i trivial) _ (hvΛ a i)
    · have h1 := hint a _ ((hL a c).1 hc) _ (hvΛ a j)
      rw [hφ, hsum] at h1
      have h2 := (hMD _ ⟨_, hvD a j, rfl⟩).mul h1
      change IsIntegral ℤ ((M : E) * c j)
      rwa [mul_mul_mul_comm, inv_mul_cancel₀ (hv0 a j), mul_one] at h2
  have hF := finite_between (E := E) L₀ hL₀ hM
  obtain ⟨S, hS, hSa⟩ := exists_finite_representatives
    (fun a => ((fun i => h a (v a i) (v a i), L a) :
      (Fin n → E) × Submodule ℤ (Fin n → E))) (by
    refine ((Set.Finite.pi' fun _ : Fin n => hD).prod hF).subset ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨hvD a, hLF a⟩)
  refine ⟨S, hS, fun a => ?_⟩
  obtain ⟨s, hs, he⟩ := hSa a
  simp only [Prod.mk.injEq] at he
  obtain ⟨h1, h2⟩ := he
  refine ⟨s, hs, (φ a).trans (φ s).symm, fun x x' => ?_, fun x => ?_⟩
  · rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hform]
    conv_rhs => rw [← (φ a).symm_apply_apply x, ← (φ a).symm_apply_apply x', hform]
    exact Finset.sum_congr rfl fun j _ => by rw [congrFun h1 j]
  · rw [LinearEquiv.trans_apply, ← hL, h2, hL, LinearEquiv.symm_apply_apply]

end Varying

section Matrices

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.MultiplicativeHeights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_finite_classes_of_traceFormDual_eq {α : Type*} {ξ0 : E} (h0 : ξ0 ≠ 0)
    (G : α → Matrix (Fin r) (Fin r) E) (hG : ∀ s a b, cc (G s a b) = G s b a)
    (hdet : ∀ s, (G s).det ≠ 0) (Λ : α → Submodule (𝓞 E) (Fin r → E))
    (hΛ : ∀ s, IsLattice (Λ s)) (hself : ∀ s, traceFormDual ξ0 (G s) (Λ s) = Λ s) :
    ∃ S : Set α, S.Finite ∧ ∀ a, ∃ s ∈ S, ∃ γ : (Fin r → E) ≃ₗ[E] (Fin r → E),
      (∀ x y, herm (G s) (γ x) (γ y) = herm (G a) x y) ∧ ∀ x, x ∈ Λ a ↔ γ x ∈ Λ s := by
  classical
  have hc : ∀ x : E, cc x = star x := fun _ => rfl
  obtain ⟨D, hD, hDa⟩ := HermClass.exists_int_mul_isIntegral_of_trace E
  obtain ⟨M, hM, hMa⟩ := HermClass.exists_int_mul_isIntegral E (Set.toFinite {-ξ0, (-ξ0)⁻¹})
  have hN : M * D ≠ 0 := mul_ne_zero hM hD
  have hN' : ((M * D : ℤ) : E) ≠ 0 := by exact_mod_cast hN
  choose h hh using fun s => exists_sesquilinear_eq_herm (G s)
  have hs : ∀ s x y, h s y x = star (h s x y) := fun s x y => by
    rw [hh, hh, ← hc, ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_conj (G s) (hG s)]
  have hnd : ∀ s y, (∀ x, h s y x = 0) → y = 0 := fun s y hy =>
    ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.eq_zero_of_herm (G s) (hdet s) y fun x => by rw [← hh, hy]
  obtain ⟨S, hS, H⟩ := exists_finite_classes_of_forms (fun s => ((M * D : ℤ) : E) • h s)
    (fun s x y => by simp [hs s x y])
    (fun s y hy => hnd s y fun x => by
      have := hy x
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left hN')
    (mul_ne_zero hM hN) (fun a => (Λ a).restrictScalars ℤ)
    (fun a => by
      have : Module.Finite (𝓞 E) (Λ a) := Module.Finite.iff_fg.2 (hΛ a).1
      exact Module.Finite.iff_fg.1 (Module.Finite.trans (R := ℤ) (𝓞 E) (Λ a)))
    (fun a => (hΛ a).2) (fun a c hc x hx => (Λ a).smul_mem (⟨c, hc⟩ : 𝓞 E) hx)
    (fun a x hx y hy => by
      have h1 : IsIntegral ℤ ((D : E) * (-ξ0 * herm (G a) x y)) := hDa _ fun t ht => by
        have h2 : t • x ∈ traceFormDual ξ0 (G a) (Λ a) := by
          rw [hself]; exact (Λ a).smul_mem (⟨t, ht⟩ : 𝓞 E) hx
        obtain ⟨k, hk⟩ := mem_traceFormDual.1 h2 y hy
        exact ⟨k, by rw [← hk, EFf_smul_eq_trace, mul_comm]⟩
      have h3 := (hMa _ (Or.inr rfl)).mul h1
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hh]
      have h4 : ((M * D : ℤ) : E) * herm (G a) x y =
          (M : E) * (-ξ0)⁻¹ * ((D : E) * (-ξ0 * herm (G a) x y)) := by
        push_cast; field_simp
      rw [h4]; exact h3)
    (fun a y hy => by
      change _ ∈ Λ a
      rw [← hself, mem_traceFormDual]
      intro x hx
      have h1 := hy x hx
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hh] at h1
      have h2 := (hMa _ (Or.inl rfl)).mul h1
      have h3 := Algebra.isIntegral_trace (R := ℤ) (L := ℚ) h2
      obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
      refine ⟨k, ?_⟩
      rw [EFf_smul_eq_trace, ← eq_intCast (algebraMap ℤ ℚ), hk]
      congr 1
      push_cast; ring)
  refine ⟨S, hS, fun a => ?_⟩
  obtain ⟨s, hsS, γ, h1, h2⟩ := H a
  refine ⟨s, hsS, γ, fun x y => ?_, h2⟩
  have := h1 x y
  simp only [LinearMap.smul_apply, smul_eq_mul, hh] at this
  exact mul_left_cancel₀ hN' this

end Matrices

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem finite_data_of_signature :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ),
      ∃ (n : ℕ) (Di : Fin n → Datum H), (∀ i, (Di i).p = p ∧ (Di i).q = q) ∧
        ∀ D' : Datum H, D'.p = p → D'.q = q →
          ∃ (i : Fin n) (e : D'.La ≃ₗ[𝓞 E] (Di i).La),
            ∀ x y, (Di i).EF (e x) (e y) = D'.EF x y := by
  intro E _ _ _ H p q
  obtain ⟨ξ0, hξ, h0⟩ := FD.exists_imag (E := E)
  let α := {D : Datum H // D.p = p ∧ D.q = q}
  have hemb : ∀ a : α, ∃ φ : a.1.La →ₗ[𝓞 E] (Fin (p + q) → E), IsLatticeEmb φ := by
    rintro ⟨D, rfl, rfl⟩
    exact datum_exists_isLatticeEmb D
  choose φ hφ using hemb
  have spec := fun a : α => datum_gram_spec a.1 (hφ a) h0 hξ
  obtain ⟨S, hS, HS⟩ := exists_finite_classes_of_traceFormDual_eq h0
    (fun a : α => (hφ a).gram ξ0 a.1.EF) (fun a => (spec a).1) (fun a => (spec a).2.1)
    (fun a => LinearMap.range (φ a)) (fun a => (hφ a).2)
    (fun a => (perfect_iff_traceFormDual_eq h0 (spec a).2.1 (hφ a).2).mp (spec a).2.2.2)
  obtain ⟨n, f, hf⟩ := hS.fin_param
  refine ⟨n, fun i => (f i).1, fun i => (f i).2, fun D' hp hq => ?_⟩
  obtain ⟨s, hs, g, h1, h2⟩ := HS ⟨D', hp, hq⟩
  obtain ⟨i, rfl⟩ : s ∈ Set.range f := hf.2 ▸ hs
  set a : α := ⟨D', hp, hq⟩
  have hmap : (LinearMap.range (φ a)).map (g.restrictScalars (𝓞 E)).toLinearMap =
      LinearMap.range (φ (f i)) := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h2 x).1 hx
    · intro hv
      exact ⟨g.symm v, (h2 _).2 (by simpa using hv), by simp⟩
  let e : D'.La ≃ₗ[𝓞 E] (f i).1.La := (LinearEquiv.ofInjective (φ a) (hφ a).1).trans
    (((g.restrictScalars (𝓞 E)).ofSubmodules _ _ hmap).trans
      (LinearEquiv.ofInjective (φ (f i)) (hφ (f i)).1).symm)
  have he : ∀ x, φ (f i) (e x) = g (φ a x) := fun x => by
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.ofInjective_symm_apply]
    rfl
  refine ⟨i, e, fun x y => ?_⟩
  have : (((f i).1.EF (e x) (e y) : ℤ) : ℚ) = D'.EF x y := by
    rw [← (spec (f i)).2.2.1, he, he, FD.EFf, h1, ← FD.EFf, (spec a).2.2.1]
  exact_mod_cast this

end GlobalTheory.DatumClasses
end

namespace GlobalTheory.MarkedGenus

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem exists_fin_representatives {α β : Type*} [Finite β] (c : α → β) :
    ∃ (r : ℕ) (g : Fin r → α), ∀ a, ∃ j, c (g j) = c a := by
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin (Set.range c)
  refine ⟨r, fun j => (e.symm j).2.choose, fun a => ⟨e ⟨c a, a, rfl⟩, ?_⟩⟩
  rw [(e.symm (e ⟨c a, a, rfl⟩)).2.choose_spec, Equiv.symm_apply_apply]

theorem finite_linearMap {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [Module.Finite R M] [Finite N] : Finite (M →ₗ[R] N) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  refine Finite.of_injective (fun φ : M →ₗ[R] N => fun x : (s : Set M) => φ x) ?_
  intro φ ψ h
  exact LinearMap.ext_on hs (fun x hx => congrFun h ⟨x, hx⟩)

theorem finite_quotient_nsmul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite ℤ R] [Module.Finite R M] {k : ℕ} (hk : 0 < k) :
    Finite (M ⧸ LinearMap.range (k • (LinearMap.id : M →ₗ[R] M))) := by
  set P := LinearMap.range (k • (LinearMap.id : M →ₗ[R] M))
  have hfin : Module.Finite ℤ (M ⧸ P) := Module.Finite.trans R (M ⧸ P)
  have hfg : AddGroup.FG (M ⧸ P) := Module.Finite.iff_addGroup_fg.mp hfin
  refine AddCommGroup.finite_of_fg_isAddTorsion _ (fun q => ?_)
  refine (isOfFinAddOrder_iff_nsmul_eq_zero).mpr ⟨k, hk, ?_⟩
  induction q using Submodule.Quotient.induction_on with
  | H m =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨m, by simp⟩

private lemma match_mod_lemma {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {k n : ℕ} (Dr : Fin n → Datum H) {A B : Datum H} (j1 j2 : Fin n)
    (e1 : A.La ≃ₗ[𝓞 E] (Dr j1).La) (e2 : B.La ≃ₗ[𝓞 E] (Dr j2).La)
    (he1 : ∀ x y, (Dr j1).EF (e1 x) (e1 y) = A.EF x y) (he2 : ∀ x y, (Dr j2).EF (e2 x) (e2 y) = B.EF x y)
    (fA : D.La →ₗ[𝓞 E] A.La) (fB : D.La →ₗ[𝓞 E] B.La)
    (h : (⟨j1, (LinearMap.range (k • (LinearMap.id : (Dr j1).La →ₗ[𝓞 E] (Dr j1).La))).mkQ.comp
        (e1.toLinearMap.comp fA)⟩ :
        Σ j : Fin n, D.La →ₗ[𝓞 E] ((Dr j).La ⧸ LinearMap.range (k • (LinearMap.id : (Dr j).La →ₗ[𝓞 E] (Dr j).La)))) =
      ⟨j2, (LinearMap.range (k • (LinearMap.id : (Dr j2).La →ₗ[𝓞 E] (Dr j2).La))).mkQ.comp
        (e2.toLinearMap.comp fB)⟩) :
    ∃ e : B.La ≃ₗ[𝓞 E] A.La, (∀ x y, A.EF (e x) (e y) = B.EF x y) ∧ ∀ x, ∃ y, e (fB x) = fA x + k • y := by
  obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp h
  have hm := eq_of_heq hh
  refine ⟨e2.trans e1.symm, fun x y => ?_, fun x => ?_⟩
  · rw [← he1]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, he2]
  · have hx := LinearMap.congr_fun hm x
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe] at hx
    rw [Submodule.Quotient.eq] at hx
    obtain ⟨z, hz⟩ := hx
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hz
    refine ⟨-(e1.symm z), e1.injective ?_⟩
    have h2 : e2 (fB x) = e1 (fA x) - k • z := by rw [hz]; abel
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, map_add (f := _), map_neg, map_nsmul, h2,
      smul_neg, sub_eq_add_neg]

theorem finite_marked_data_in_genus :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (k : ℕ) (ζ : ℂ), 0 < k → ∃ (r : ℕ) (Di : Fin r → Datum H) (fi : ∀ i, ℕ → D.La →ₗ[𝓞 E] (Di i).La) (νi : Fin r → ℕ → ℤ), (∀ i, ((Di i).p = D.p ∧ (Di i).q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, fi i (n * m) x = fi i n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, fi i n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = fi i n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ (Di i).EF (fi i n x) (fi i n x') - νi i n * D.EF x x') ∧ ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (νi i k : ℂ) / k)) ∧ ∀ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') → ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k) → ∃ (i : Fin r) (e : D'.La ≃ₗ[𝓞 E] (Di i).La), (∀ x y, (Di i).EF (e x) (e y) = D'.EF x y) ∧ ∀ x, ∃ y, e (f k x) = fi i k x + k • y := by
  intro E _ _ _ H D k ζ hk
  obtain ⟨n, Dr, hDr, hcls⟩ := GlobalTheory.DatumClasses.finite_data_of_signature E H D.p D.q
  let Q : Fin n → Type := fun j =>
    (Dr j).La ⧸ LinearMap.range (k • (LinearMap.id : (Dr j).La →ₗ[𝓞 E] (Dr j).La))
  have hQ : ∀ j, Finite (D.La →ₗ[𝓞 E] Q j) := fun j => by
    have := D.fin
    have := (Dr j).fin
    have : Finite (Q j) := finite_quotient_nsmul hk
    exact finite_linearMap
  let Cond : (D' : Datum H) → (ℕ → D.La →ₗ[𝓞 E] D'.La) → (ℕ → ℤ) → Prop := fun D' f ν =>
    (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧
      (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧
      ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧
    ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k)
  let α := {a : Σ D' : Datum H, (ℕ → D.La →ₗ[𝓞 E] D'.La) × (ℕ → ℤ) // Cond a.1 a.2.1 a.2.2}
  choose jf ef hef using fun a : α => hcls a.1.1 a.2.1.1 a.2.1.2.1
  let c : α → Σ j : Fin n, (D.La →ₗ[𝓞 E] Q j) := fun a =>
    ⟨jf a, (LinearMap.range (k • (LinearMap.id : (Dr (jf a)).La →ₗ[𝓞 E] (Dr (jf a)).La))).mkQ.comp
      ((ef a).toLinearMap.comp (a.1.2.1 k))⟩
  obtain ⟨r, g, hg⟩ := exists_fin_representatives c
  refine ⟨r, fun i => (g i).1.1, fun i => (g i).1.2.1, fun i => (g i).1.2.2, fun i => (g i).2, ?_⟩
  intro D' f ν hc hζ
  obtain ⟨i, hi⟩ := hg ⟨⟨D', f, ν⟩, hc, hζ⟩
  exact ⟨i, match_mod_lemma Dr _ _ (ef (g i)) (ef ⟨⟨D', f, ν⟩, hc, hζ⟩) (hef (g i)) (hef _) _ _ hi⟩

end GlobalTheory.MarkedGenus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ImAdjointOfSpan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ConjBound

open GlobalTheory.EigenNorm

variable {g : ℕ}

theorem im_adjoint_of_span (Hm : Matrix (Fin g) (Fin g) ℂ) (t u : Fin g → ℂ) (S : Set (Fin g → ℂ))
    (hS : Submodule.span ℝ S = ⊤)
    (h : ∀ z ∈ S, ∀ w ∈ S, (hermForm Hm (t * z) w).im = (hermForm Hm z (u * w)).im) (z w : Fin g → ℂ) :
    (hermForm Hm (t * z) w).im = (hermForm Hm z (u * w)).im := by
  have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
  have hw : w ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
  have hr : ∀ (r : ℝ) (v : Fin g → ℂ), r • v = (r : ℂ) • v := fun r v => by
    funext i; simp
  induction hz, hw using Submodule.span_induction₂ with
  | mem_mem z w hz hw => exact h z hz w hw
  | zero_left w _ => simp [hermForm]
  | zero_right z _ => simp [hermForm]
  | add_left z z' w _ _ _ h1 h2 =>
    rw [mul_add, hermForm_add_left, hermForm_add_left, Complex.add_im, Complex.add_im, h1, h2]
  | add_right z w w' _ _ _ h1 h2 =>
    rw [mul_add, hermForm_add_right, hermForm_add_right, Complex.add_im, Complex.add_im, h1, h2]
  | smul_left r z w _ _ h1 =>
    rw [hr, mul_smul_comm, hermForm_smul_left, hermForm_smul_left, Complex.im_ofReal_mul, Complex.im_ofReal_mul, h1]
  | smul_right r z w _ _ h1 =>
    rw [hr, mul_smul_comm, hermForm_smul_right, hermForm_smul_right, Complex.conj_ofReal, Complex.im_ofReal_mul,
      Complex.im_ofReal_mul, h1]

theorem hermForm_eq_sum (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z w = ∑ i, ∑ j, z i * Hm i j * starRingEnd ℂ (w j) := by
  simp [hermForm, dotProduct, Matrix.mulVec, Finset.mul_sum, _root_.mul_assoc]

theorem entry_comm (Hm : Matrix (Fin g) (Fin g) ℂ) (t : Fin g → ℂ)
    (h : ∀ z w, (hermForm Hm (t * z) w).im = (hermForm Hm z (star t * w)).im) (i j : Fin g) :
    t i * Hm i j = Hm i j * t j := by
  have key : ∀ s : ℂ, (s * (t i * Hm i j)).im = (s * (Hm i j * t j)).im := fun s => by
    have := h (Pi.single i s) (Pi.single j 1)
    rw [hermForm_eq_sum, hermForm_eq_sum] at this
    simp only [Pi.mul_apply, Pi.single_apply, Pi.star_apply, mul_ite, mul_zero, _root_.mul_one, ite_mul, zero_mul,
      apply_ite (starRingEnd ℂ), map_zero, map_one, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      RCLike.star_def, Complex.conj_conj] at this
    convert this using 2 <;> ring
  have h1 := key 1
  have h2 := key Complex.I
  rw [_root_.one_mul, _root_.one_mul] at h1
  rw [Complex.I_mul_im, Complex.I_mul_im] at h2
  exact Complex.ext h2 h1

theorem re_lt_of_comm (Hm : Matrix (Fin g) (Fin g) ℂ) (t : Fin g → ℂ) (κ : ℝ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hc : ∀ i j, t i * Hm i j = Hm i j * t j) (ht : ∀ i, ‖t i‖ ^ 2 < κ) (y : Fin g → ℂ) (hy : y ≠ 0) :
    (hermForm Hm (t * y) (t * y)).re < κ * (hermForm Hm y y).re := by
  let s : Fin g → ℂ := fun i => (Real.sqrt (κ - ‖t i‖ ^ 2) : ℝ)
  have hs0 : ∀ i, s i ≠ 0 := fun i => by
    have : 0 < Real.sqrt (κ - ‖t i‖ ^ 2) := Real.sqrt_pos.2 (sub_pos.2 (ht i))
    exact Complex.ofReal_ne_zero.2 this.ne'
  have hsy : s * y ≠ 0 := fun h0 => hy (by
    funext i
    have := congrFun h0 i
    simpa [hs0 i] using this)
  have hss : ∀ i, s i * starRingEnd ℂ (s i) + t i * starRingEnd ℂ (t i) = κ := fun i => by
    rw [Complex.mul_conj', Complex.mul_conj']
    have : ‖s i‖ ^ 2 = κ - ‖t i‖ ^ 2 := by
      simp only [s, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact Real.sq_sqrt (sub_pos.2 (ht i)).le
    rw [← Complex.ofReal_pow, this]
    push_cast; ring
  have hsum : hermForm Hm (s * y) (s * y) + hermForm Hm (t * y) (t * y) = κ * hermForm Hm y y := by
    simp only [hermForm_eq_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h0 : Hm i j = 0
    · simp [h0]
    · have hij : t i = t j := by
        have := hc i j
        rw [mul_comm] at this
        exact mul_left_cancel₀ h0 this
      have hsij : s i = s j := by simp only [s, hij]
      simp only [Pi.mul_apply, map_mul, hij, hsij, ← hss j]
      ring
  have h1 := hpos _ hsy
  have h2 := congrArg Complex.re hsum
  rw [Complex.add_re, Complex.re_ofReal_mul] at h2
  linarith

theorem exists_action_lt :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Q : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 E) (κ : ℕ), (∀ (c : 𝓞 E) x i, Q (c • x) i = ty i (c : E) * Q x i) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D.EF x y) → (∀ τ : E →+* ℂ, ‖τ (a : E)‖ ^ 2 < κ) → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (a • x)) ∧ ∀ y, y ≠ 0 → (hermForm Hm (F y) (F y)).re < κ * (hermForm Hm y y).re := by
  intro E _ _ _ H D g ty Q Hm a κ hlin ⟨_, _, hspan, _, hpos, him⟩ hκ
  let t : Fin g → ℂ := fun i => ty i (a : E)
  have h1 : ∀ x, t * Q x = Q (a • x) := fun x => funext fun i => (hlin a x i).symm
  have h2 : ∀ x, star t * Q x = Q (H.bar a • x) := fun x => funext fun i => by
    rw [hlin, H.bar_eq, IsCMField.complexEmbedding_complexConj]; rfl
  refine ⟨LinearMap.mulLeft ℂ t, h1, fun y hy => ?_⟩
  refine re_lt_of_comm Hm t κ hpos (entry_comm Hm t (im_adjoint_of_span Hm t (star t) _ hspan ?_))
    (fun i => hκ (ty i)) y hy
  rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
  rw [h1, h2, him, him, D.adj]

end GlobalTheory.ConjBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsTypeFnOfRank
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_isTypeFn_of_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ), Nonempty ((Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) → ∃ ty : Fin g → (E →+* ℂ), IsTypeFn H D.p D.q ty := by
  intro E _ _ _ H D g ⟨e⟩
  obtain ⟨g', ty, h, -, P, -, hinj, hdisc, hspan, -⟩ := GlobalTheory.PeriodExists.exists_typeFn_period H D
  let L : Submodule ℤ (Fin g' → ℂ) := LinearMap.range P.toIntLinearMap
  have : DiscreteTopology L := hdisc
  have : IsZLattice ℝ L := ⟨by
    have : (L : Set (Fin g' → ℂ)) = Set.range P := by ext; simp [L]
    rw [this]; exact hspan⟩
  have h1 := ZLattice.rank ℝ L
  have h2 : Module.finrank ℤ L = 2 * g := by
    rw [← (e.trans (LinearEquiv.ofInjective P.toIntLinearMap hinj)).finrank_eq]
    simp
  have h3 : Module.finrank ℝ (Fin g' → ℂ) = 2 * g' := by
    rw [Module.finrank_pi_fintype]; simp [mul_comm]
  obtain rfl : g' = g := by omega
  exact ⟨ty, h⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGoodThetaComplexClassUnitaryFullLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PelGood

theorem exists_domain {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D D' : Datum H) {g : ℕ}
    (ty : Fin g → (E →+* ℂ)) (hty : IsTypeFn H D.p D.q ty) (hp : D'.p = D.p) (hq : D'.q = D.q) :
    ∃ (B : Set (Fin D.dim → ℂ)) (P : (Fin D.dim → ℂ) → (D'.La →+ (Fin g → ℂ))), IsOpen B ∧ Convex ℝ B ∧
      IsHolPeriods D' ty B P ∧ ∀ P', IsPeriod D' ty P' →
        ∃! b, b ∈ B ∧ ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' a = h (P b a) := by
  have hd : D.dim = D'.dim := by rw [Datum.dim, Datum.dim, hp, hq]
  rw [hd]
  exact exists_period_domain_param E H D' g ty (by rw [hp, hq]; exact hty)

theorem isPeriod_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D D' : Datum H} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {Q : D.La →+ (Fin g → ℂ)} (hQ : IsPeriod D ty Q) (e : D.La ≃ₗ[𝓞 E] D'.La)
    (he : ∀ x y, D'.EF (e x) (e y) = D.EF x y) :
    IsPeriod D' ty (Q.comp e.symm.toAddEquiv.toAddMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, Hm, h5, h6, h7⟩ := hQ
  have hr : Set.range (Q.comp e.symm.toAddEquiv.toAddMonoidHom) = Set.range Q :=
    e.symm.surjective.range_comp Q
  have hr' : (Q.comp e.symm.toAddEquiv.toAddMonoidHom).range = Q.range :=
    SetLike.ext' hr
  refine ⟨fun a x i => ?_, h2.comp e.symm.injective, by rw [hr']; exact h3, by rw [hr]; exact h4, Hm, h5, h6,
    fun x y => ?_⟩
  · change Q (e.symm (a • x)) i = _ * Q (e.symm x) i
    rw [map_smul, h1]
  · change (hermForm Hm (Q (e.symm x)) (Q (e.symm y))).im = _
    rw [h7, ← he, e.apply_symm_apply, e.apply_symm_apply]

theorem exp_eq_zpow (k : ℕ) (hk : 0 < k) (m ν s : ℤ) (h : (k : ℤ) ∣ m - ν * s) :
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / (k : ℂ)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (ν : ℂ) / k) ^ s := by
  obtain ⟨c, hc⟩ := h
  have hm : m = ν * s + k * c := by linarith
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [← Complex.exp_int_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-c, ?_⟩
  rw [hm]
  push_cast
  field_simp
  ring

theorem goodClass_pelClass : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∃ (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ), ∀ n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → GoodClass em (PELClass (b := b) D a bas ρ em) Mat κ w w' D.dim := by
  intro L1 L2 hΘ hU E _ _ _ H D g J _ a w w' bas hpq hbas hw hw' _
  obtain ⟨ty, hty⟩ := exists_isTypeFn_of_rank E H D g ⟨bas⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℕ, ∀ (j : J) (τ : E →+* ℂ), ‖τ (a j : E)‖ ^ 2 < κ := by
    obtain ⟨M, hM⟩ := (Set.finite_range (fun x : J × (E →+* ℂ) => ‖x.2 (a x.1 : E)‖ ^ 2)).bddAbove
    obtain ⟨κ, hκ⟩ := exists_nat_gt M
    exact ⟨κ, fun j τ => (hM ⟨(j, τ), rfl⟩).trans_lt hκ⟩
  let Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ :=
    fun j i' i => bas.symm (a j • bas (Pi.single i 1)) i'
  have hMat : ∀ j i, a j • bas (Pi.single i 1) = ∑ i', Mat j i' i • bas (Pi.single i' 1) := by
    intro j i
    apply bas.symm.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, LinearEquiv.symm_apply_apply]
    ext i₀
    simp [Mat, Finset.sum_apply, Pi.single_apply]
  refine ⟨Mat, κ, fun n hn hodd => ?_⟩
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.goodThetaClass_of_lattice_families L1 L2 hΘ hU g J Mat κ n w w' hn hodd
  refine ⟨j₀, fun j hj N' hN o _ b em ρ hρ => ?_⟩
  have hk : 0 < N' ^ 2 := by rw [hN]; exact pow_pos (pow_pos hn.pos _) _
  obtain ⟨r, Di, fi, νi, hfam, hall⟩ := MarkedGenus.finite_marked_data_in_genus E H D (N' ^ 2) (em (b.ζ : o)) hk
  choose B P hBo hBc hBh hBu using fun i => exists_domain D (Di i) ty hty (hfam i).1.1 (hfam i).1.2.1
  have hH : ∀ i bb, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, bb ∈ B i →
      (Function.Injective (P i bb) ∧ DiscreteTopology (P i bb).range ∧ Submodule.span ℝ (Set.range (P i bb)) = ⊤ ∧
        Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
        ∀ x y, (hermForm Hm (P i bb x) (P i bb y)).im = (Di i).EF x y) := by
    intro i bb
    by_cases hb : bb ∈ B i
    · obtain ⟨-, h2, h3, h4, Hm, h5⟩ := (hBh i).1 bb hb
      exact ⟨Hm, fun _ => ⟨h2, h3, h4, h5⟩⟩
    · exact ⟨0, fun h => (hb h).elim⟩
  choose Hm hHm using hH
  refine hj₀ j hj N' hN o b em _ D.dim r (fun i => (Di i).La) (fun i => (Di i).EF)
    (fun i i₁ => fi i (N' ^ 2) (bas (Pi.single i₁ 1))) (fun i j x => a j • x) B P Hm
    (fun t t' ht hm => (pelClass_prim_and_iso E H D o g _ J b em w w' a bas ρ t ht).2 t' hm)
    (fun t ht => (pelClass_prim_and_iso E H D o g _ J b em w w' a bas ρ t ht).1 hw hw') (fun i => ?_) (fun t ht => ?_)
  · refine ⟨(Di i).unimod, hBo i, (hBc i).isPreconnected, (hBh i).2, fun x => ?_, fun x y => ?_, fun i₁ i₂ => ?_,
      fun j₁ i₁ => ⟨0, ?_⟩, fun bb hb => ⟨hHm i bb hb, fun j₁ => ?_⟩, fun bb hb z hz hh => ?_, fun bb hb t hu hp => ?_⟩
    · rw [← add_smul, hw, hw', HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, one_smul]
    · rw [hw, hw', (Di i).adj]
    · rw [(hfam i).2]
      apply exp_eq_zpow _ hk
      rw [← hbas]
      exact (hfam i).1.2.2.2.2 _ hk _ _
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [smul_zero, add_zero, ← map_smul, hMat, map_sum]
        simp only [map_zsmul]
    · exact ConjBound.exists_action_lt E H (Di i) g ty (P i bb) (Hm i bb) (a j₁) κ ((hBh i).1 bb hb).1 (hHm i bb hb)
        (hκ j₁)
    · exact (hBu i _ ((hBh i).1 z hz)).unique ⟨hb, hh⟩ ⟨hz, LinearEquiv.refl _ _, fun _ => rfl⟩
    · exact GlobalTheory.T.isPELObject_of_primitive_periodMap_uniformised L1 L2 hΘ hU E H D o g _ J b em w w' a bas ρ ty t (Di i) (fi i) (νi i) (P i bb) (Hm i bb)
        hpq hw hρ hty (hfam i).1 (hfam i).2 ((hBh i).1 bb hb) (hHm i bb hb) hu hp
  · obtain ⟨D', f, ν, Q, Hm', hgen, hζ, hper, hpol, hu⟩ :=
      GlobalTheory.T.exists_periods_complexPELObject L1 L2 hΘ hU E H D o g _ J b em w w' a bas ρ ty t hw hw' hρ hty ht
    obtain ⟨i, e, he, hef⟩ := hall D' f ν hgen hζ
    obtain ⟨bb, ⟨hb, h, hh⟩, -⟩ := hBu i _ (isPeriod_comp hper e he)
    refine ⟨i, bb, hb, ?_⟩
    refine UnifTransport.transport_uniformisation o g (N' ^ 2) J b em w w' t D'.La D'.EF
      (fun i₁ => f (N' ^ 2) (bas (Pi.single i₁ 1))) (fun j x => a j • x) Q Hm' (Di i).La (Di i).EF
      (fun i₁ => fi i (N' ^ 2) (bas (Pi.single i₁ 1))) (fun j x => a j • x) (P i bb) (Hm i bb) e.toAddEquiv h.symm
      hpol (hHm i bb hb) (fun x => ?_) he (fun j x => e.map_smul _ _) (fun i₁ => hef _) hu
    rw [LinearEquiv.eq_symm_apply, ← hh]
    exact congrArg Q (e.symm_apply_apply x)

end GlobalTheory.PelGood
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGoodThetaComplexClassUnitaryFullLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGoodThetaComplexClass_unitaryFullLevel : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∃ (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ), ∀ n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → GoodClass em (PELClass (b := b) D a bas ρ em) Mat κ w w' D.dim := by
  first | exact @GlobalTheory.PelGood.goodClass_pelClass | exact GlobalTheory.PelGood.goodClass_pelClass | (intros; apply GlobalTheory.PelGood.goodClass_pelClass <;> assumption)
end
