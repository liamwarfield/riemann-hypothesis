module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinI
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinC
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinF
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCSt

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinR
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open NumberField Module Formalism.MainNotions.ModuliIntegralCharts ComplexConjugate

variable {E : Type} [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
  {ι : Type} [Fintype ι] [DecidableEq ι]

def bs (b : Basis ι ℤ Y) (a : ι) : Y →ₗ[ℤ] ℝ := Algebra.linearMap ℤ ℝ ∘ₗ b.coord a

theorem bs_apply (b : Basis ι ℤ Y) (a : ι) (y : Y) : bs b a y = (b.repr y a : ℝ) := by
  simp [bs]

theorem gram_expand (b : Basis ι ℤ Y) (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (v w : Y) :
    ∑ a, ∑ c, β (b a) (b c) * (bs b a v * bs b c w) = β v w := by
  conv_rhs => rw [← b.sum_repr v, ← b.sum_repr w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, bs_apply, zsmul_eq_mul,
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

section Repro

variable {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
include hcj

theorem repro_sigma (b : Basis ι ℤ Y) (β : SymB cj Y) (σ : E →+* ℂ) (y z : Y) :
    ∑ a, ∑ c, ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) : ℂ) *
      (comp (bs b a) σ y * conj (comp (bs b c) σ z)) =
      comp ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ).flip z) σ y := by
  set B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ := (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) with hB
  obtain ⟨_, hbal⟩ := β.2

  have hj : ∀ j, ∑ i, (B (RingOfIntegers.basis E i • y) (RingOfIntegers.basis E j • z) : ℂ) * σ (ed E i)
      = star (σ (RingOfIntegers.basis E j : E)) * comp (B.flip z) σ y := by
    intro j
    obtain ⟨c, hc⟩ := cj_integral hcj (RingOfIntegers.basis E j)
    have hcc : ((RingOfIntegers.basis E j : 𝓞 E) : E) = cj (c : E) := by rw [hc, cj_cj hcj]
    have e : ∀ i, B (RingOfIntegers.basis E i • y) (RingOfIntegers.basis E j • z) =
        B (RingOfIntegers.basis E i • (c • y)) z := by
      intro i
      rw [← hbal c _ hcc, smul_comm]
    simp_rw [e]
    rw [show ∑ i, (B (RingOfIntegers.basis E i • (c • y)) z : ℂ) * σ (ed E i) = comp (B.flip z) σ (c • y)
      from rfl, comp_smul, hc, hcj]
  have e2 : ∀ c, conj (comp (bs b c) σ z) =
      ∑ j, (bs b c (RingOfIntegers.basis E j • z) : ℂ) * conj (σ (ed E j)) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      simp [comp, map_sum]
  have expand : ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) *
      (comp (bs b a) σ y * conj (comp (bs b c) σ z)) =
      ∑ j, conj (σ (ed E j)) * ∑ i, (B (RingOfIntegers.basis E i • y) (RingOfIntegers.basis E j • z) : ℂ) *
        σ (ed E i) := by
    simp_rw [← gram_expand b B (RingOfIntegers.basis E _ • y) (RingOfIntegers.basis E _ • z)]
    simp_rw [e2]
    simp only [comp, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul, Complex.ofReal_sum,
      Complex.ofReal_mul]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]; arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [expand]
  simp_rw [hj]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  have ho := ortho σ σ
  simp only [if_true, integralBasis_apply] at ho
  have : ∑ j, conj (σ (ed E j)) * star (σ (RingOfIntegers.basis E j : E)) = 1 := by
    have := congrArg conj ho
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, map_mul] using this
  rw [this, one_mul]

theorem fock_reproducing_formula (b : Basis ι ℤ Y) (β : SymB cj Y) (y z : Y) :
    ∑ a, ∑ c, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) * Pf E (bs b a) (bs b c) y z =
      2 * (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y z := by
  obtain ⟨hs, _⟩ := β.2
  set B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ := (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) with hB
  have key : ∀ σ : E →+* ℂ, ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) *
      (comp (bs b a) σ y * conj (comp (bs b c) σ z) + comp (bs b c) σ y * conj (comp (bs b a) σ z)) =
      2 * comp (B.flip z) σ y := by
    intro σ
    simp only [mul_add, Finset.sum_add_distrib]
    have sw : ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) * (comp (bs b c) σ y * conj (comp (bs b a) σ z)) =
        ∑ a, ∑ c, ((B (b a) (b c) : ℝ) : ℂ) * (comp (bs b a) σ y * conj (comp (bs b c) σ z)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => ?_
      rw [hs (b w) (b x)]
    rw [sw, repro_sigma hcj b β σ y z]
    ring
  unfold Pf
  have e : ∀ a c, B (b a) (b c) *
      (∑ σ : E →+* ℂ, (comp (bs b a) σ y * conj (comp (bs b c) σ z) +
        comp (bs b c) σ y * conj (comp (bs b a) σ z))).re =
      (∑ σ : E →+* ℂ, ((B (b a) (b c) : ℝ) : ℂ) * (comp (bs b a) σ y * conj (comp (bs b c) σ z) +
        comp (bs b c) σ y * conj (comp (bs b a) σ z))).re := by
    intro a c
    rw [← Complex.re_ofReal_mul, Finset.mul_sum]
  simp_rw [e]
  simp_rw [← Complex.re_sum]
  conv_lhs => arg 1; arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp_rw [key]
  rw [← Finset.mul_sum, sum_comp]
  simp [LinearMap.flip_apply]

theorem l_expand (b : Basis ι ℤ Y) (l : SymB cj Y →ₗ[ℝ] ℝ) (β : SymB cj Y) :
    l β = ∑ a, ∑ c, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) * (l (Pm hcj (bs b a) (bs b c)) / 2) := by
  have hsum : β = ∑ a, ∑ c, ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) / 2) • Pm hcj (bs b a) (bs b c) := by
    apply Subtype.ext
    apply LinearMap.ext₂
    intro y z
    have hP : ∀ (η ζ : Y →ₗ[ℤ] ℝ), ((Pm hcj η ζ : SymB cj Y) : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y z = Pf E η ζ y z :=
      fun _ _ => rfl
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply, hP,
      smul_eq_mul]
    have := fock_reproducing_formula hcj b β y z
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, this]
    ring
  conv_lhs => rw [hsum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

end Repro

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCTie
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts

section Comparison₂

variable {E : Type} [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
  {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Y)

def coordT (x y : Y) : ι × ι → ℤ := fun p => b.repr x p.1 * b.repr y p.2

theorem coordT_add_left (x x' y : Y) : coordT b (x + x') y = coordT b x y + coordT b x' y := by
  funext p
  simp only [coordT, map_add (f := _), Finsupp.add_apply, Pi.add_apply, add_mul]

theorem coordT_add_right (x y y' : Y) : coordT b x (y + y') = coordT b x y + coordT b x y' := by
  funext p
  simp only [coordT, map_add (f := _), Finsupp.add_apply, Pi.add_apply, mul_add]

theorem coordT_smul_left (k : ℤ) (x y : Y) : coordT b (k • x) y = k • coordT b x y := by
  funext p
  simp only [coordT, map_zsmul, Finsupp.smul_apply, smul_eq_mul, Pi.smul_apply]
  ring

theorem coordT_smul_right (k : ℤ) (x y : Y) : coordT b x (k • y) = k • coordT b x y := by
  funext p
  simp only [coordT, map_zsmul, Finsupp.smul_apply, smul_eq_mul, Pi.smul_apply]
  ring

def evB (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) : (ι × ι → ℤ) →ₗ[ℤ] ℝ where
  toFun n := ∑ p, (n p : ℝ) * B (b p.1) (b p.2)
  map_add' n n' := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' k n := by simp [Finset.mul_sum, mul_assoc]

theorem evB_apply (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (n : ι × ι → ℤ) :
    evB b B n = ∑ p, (n p : ℝ) * B (b p.1) (b p.2) := rfl

theorem evB_coordT (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x y : Y) : evB b B (coordT b x y) = B x y := by
  rw [evB_apply, Fintype.sum_prod_type]
  have hx := b.sum_repr x
  have hy := b.sum_repr y
  calc _ = ∑ i, ∑ j, ((b.repr x i : ℝ) * (b.repr y j : ℝ)) * B (b i) (b j) := by
          simp only [coordT, Int.cast_mul]
    _ = B x y := by
      conv_rhs => rw [← hx, ← hy]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring

def annS (cj : E → E) : Submodule ℤ (ι × ι → ℤ) :=
  ⨅ β : SymB cj Y, LinearMap.ker (evB b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ))

theorem mem_annS (cj : E → E) (n : ι × ι → ℤ) :
    n ∈ annS b cj ↔ ∀ β : SymB cj Y, evB b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) n = 0 := by
  simp only [annS, Submodule.mem_iInf, LinearMap.mem_ker]

theorem noZero_annS (cj : E → E) : NoZeroSMulDivisors ℤ ((ι × ι → ℤ) ⧸ annS b cj) := by
  refine ⟨fun {k} {q} h => ?_⟩
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  by_cases hk : k = 0
  · exact Or.inl hk
  right
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_annS] at h
  rw [Submodule.Quotient.mk_eq_zero, mem_annS]
  intro β
  have h1 := h β
  rw [map_zsmul, zsmul_eq_mul, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd (Int.cast_eq_zero.mp h1) hk
  · exact h1

def formOf (f : (ι × ι → ℤ) →ₗ[ℤ] ℤ) : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ :=
  LinearMap.mk₂ ℤ (fun x y => ((f (coordT b x y) : ℤ) : ℝ))
    (fun x x' y => by simp [coordT_add_left])
    (fun k x y => by rw [coordT_smul_left, map_zsmul]; simp [zsmul_eq_mul])
    (fun x y y' => by simp [coordT_add_right])
    (fun k x y => by rw [coordT_smul_right, map_zsmul]; simp [zsmul_eq_mul])

theorem formOf_apply (f : (ι × ι → ℤ) →ₗ[ℤ] ℤ) (x y : Y) :
    formOf b f x y = ((f (coordT b x y) : ℤ) : ℝ) := rfl

theorem formOf_mem (cj : E → E) (f : ((ι × ι → ℤ) ⧸ annS b cj) →ₗ[ℤ] ℤ) :
    formOf b (f ∘ₗ (annS b cj).mkQ) ∈ SymB cj Y := by
  have key : ∀ x y x' y' : Y, (∀ β : SymB cj Y, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) x y =
      (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) x' y') →
      formOf b (f ∘ₗ (annS b cj).mkQ) x y = formOf b (f ∘ₗ (annS b cj).mkQ) x' y' := by
    intro x y x' y' h
    rw [formOf_apply, formOf_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    congr 2
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, mem_annS]
    intro β
    rw [map_sub, evB_coordT, evB_coordT, h β, sub_self]
  have mem : ∀ β : SymB cj Y, (∀ a d : Y, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a d = (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) d a) ∧
      ∀ (c c' : 𝓞 E), (c' : E) = cj c → ∀ (a d : Y),
        (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (c • a) d = (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a (c' • d) := fun β => β.2
  refine ⟨fun a d => key a d d a fun β => (mem β).1 a d,
    fun c c' hc a d => key _ _ _ _ fun β => (mem β).2 c c' hc a d⟩

end Comparison₂

theorem phiCTie_holds : PhiCTieStatement := by
  intro E _ _ cj Y _ _ _ _ l hl
  classical
  let b := Module.Free.chooseBasis ℤ Y
  let A := annS b cj
  have : NoZeroSMulDivisors ℤ ((_ × _ → ℤ) ⧸ A) := noZero_annS b cj
  have : Module.Free ℤ ((_ × _ → ℤ) ⧸ A) := Module.free_of_finite_type_torsion_free'
  let eb := Module.Free.chooseBasis ℤ ((_ × _ → ℤ) ⧸ A)
  let βk : Module.Free.ChooseBasisIndex ℤ ((_ × _ → ℤ) ⧸ A) → SymB cj Y := fun k =>
    ⟨formOf b (eb.coord k ∘ₗ A.mkQ), formOf_mem b cj _⟩
  have hint : ∀ k, ∃ z : ℤ, l (βk k) = z := fun k =>
    hl (βk k) (fun x y => ⟨_, formOf_apply b _ x y⟩)
  choose z hz using hint
  obtain ⟨n, hn⟩ := Submodule.Quotient.mk_surjective A (∑ k, z k • eb k)
  let e := (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ Y × Module.Free.ChooseBasisIndex ℤ Y)).symm
  refine ⟨Fintype.card (Module.Free.ChooseBasisIndex ℤ Y × Module.Free.ChooseBasisIndex ℤ Y),
    fun t => n (e t) • b (e t).1, fun t => b (e t).2, fun β => ?_⟩
  have hR : ∑ t, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (n (e t) • b (e t).1) (b (e t).2) =
      evB b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) n := by
    rw [e.sum_comp (fun p => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (n p • b p.1) (b p.2)), evB_apply]
    simp [zsmul_eq_mul]
  rw [hR]
  have hle : A ≤ LinearMap.ker (evB b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)) := iInf_le _ β
  let ψ := A.liftQ (evB b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)) hle
  have hψ : ∀ m, ψ (Submodule.Quotient.mk m) = evB b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) m := fun m =>
    Submodule.liftQ_apply _ _ _
  have hβ : β = ∑ k, ψ (eb k) • βk k := by
    apply Subtype.ext
    apply LinearMap.ext₂
    intro x y
    rw [Submodule.coe_sum, LinearMap.sum_apply, LinearMap.sum_apply]
    simp only [Submodule.coe_smul, LinearMap.smul_apply, βk, formOf_apply, LinearMap.comp_apply,
      Submodule.mkQ_apply, Module.Basis.coord_apply, smul_eq_mul]
    rw [← evB_coordT b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) x y, ← hψ]
    conv_lhs => rw [← eb.sum_repr (Submodule.Quotient.mk (coordT b x y))]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  calc l β = l (∑ k, ψ (eb k) • βk k) := congrArg l hβ
    _ = ∑ k, ψ (eb k) * (z k : ℝ) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, hz, smul_eq_mul]
    _ = evB b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) n := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hψ, hn, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, zsmul_eq_mul, mul_comm]

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinE
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open Matrix

theorem bessel2 {d : ℕ} (v p q : Fin d → ℝ) (hv : v ⬝ᵥ v = 1) (hp : p ⬝ᵥ p = 1)
    (hpq : p ⬝ᵥ q = 0) (hq : 0 < q ⬝ᵥ q) :
    (v ⬝ᵥ p) ^ 2 * (q ⬝ᵥ q) + (v ⬝ᵥ q) ^ 2 ≤ q ⬝ᵥ q := by
  have hr : 0 ≤ ((q ⬝ᵥ q) • v - ((q ⬝ᵥ q) * (v ⬝ᵥ p)) • p - (v ⬝ᵥ q) • q) ⬝ᵥ
      ((q ⬝ᵥ q) • v - ((q ⬝ᵥ q) * (v ⬝ᵥ p)) • p - (v ⬝ᵥ q) • q) := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hqp : q ⬝ᵥ p = 0 := by rw [dotProduct_comm]; exact hpq
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm p v, dotProduct_comm q v, hv, hp, hpq, hqp] at hr
  nlinarith [hr, hq]

theorem halfTrace_holds : HalfTraceStatement := by
  intro d L G K R hLR hR hG hKG hKL hK x
  have hRi : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR
  have hiR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hR
  have hRt : Rᵀ * (R⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, hiR, Matrix.transpose_one]
  have htR : (R⁻¹)ᵀ * Rᵀ = 1 := by rw [← Matrix.transpose_mul, hRi, Matrix.transpose_one]

  have hCpsd : (R * G * Rᵀ).PosSemidef := by
    have := hG.mul_mul_conjTranspose_same R
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hCtr : trace (R * G * Rᵀ) = trace (L * G) := by
    rw [Matrix.trace_mul_cycle, hLR]
  have hJ' : (R⁻¹)ᵀ * K * Rᵀ = -(R * Kᵀ * R⁻¹) := by
    have h2 : (R⁻¹)ᵀ * (K * L) * R⁻¹ = (R⁻¹)ᵀ * (-(L * Kᵀ)) * R⁻¹ := by rw [hKL]
    rw [hLR] at h2
    have e1 : (R⁻¹)ᵀ * (K * (Rᵀ * R)) * R⁻¹ = (R⁻¹)ᵀ * K * Rᵀ := by
      simp only [Matrix.mul_assoc, hRi, Matrix.mul_one]
    have e2 : (R⁻¹)ᵀ * (-(Rᵀ * R * Kᵀ)) * R⁻¹ = -(R * Kᵀ * R⁻¹) := by
      rw [Matrix.mul_neg, Matrix.neg_mul]
      congr 1
      simp only [← Matrix.mul_assoc, htR, Matrix.one_mul]
    rw [← e1, h2, e2]
  have hJskew : ((R⁻¹)ᵀ * K * Rᵀ)ᵀ = -((R⁻¹)ᵀ * K * Rᵀ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose, hJ', neg_neg, Matrix.mul_assoc]
  have hCJ : (R * G * Rᵀ) * ((R⁻¹)ᵀ * K * Rᵀ) = ((R⁻¹)ᵀ * K * Rᵀ) * (R * G * Rᵀ) := by
    have l1 : (R * G * Rᵀ) * ((R⁻¹)ᵀ * K * Rᵀ) = R * (G * K) * Rᵀ := by
      calc (R * G * Rᵀ) * ((R⁻¹)ᵀ * K * Rᵀ) = R * G * (Rᵀ * (R⁻¹)ᵀ) * K * Rᵀ := by
            simp only [Matrix.mul_assoc]
        _ = R * (G * K) * Rᵀ := by rw [hRt, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    have l2 : ((R⁻¹)ᵀ * K * Rᵀ) * (R * G * Rᵀ) = R * (G * K) * Rᵀ := by
      calc ((R⁻¹)ᵀ * K * Rᵀ) * (R * G * Rᵀ) = (R⁻¹)ᵀ * (K * (Rᵀ * R)) * G * Rᵀ := by
            simp only [Matrix.mul_assoc]
        _ = (R⁻¹)ᵀ * (-(Rᵀ * R * Kᵀ)) * G * Rᵀ := by rw [← hLR, hKL, hLR]
        _ = -(((R⁻¹)ᵀ * Rᵀ) * R * (Kᵀ * G) * Rᵀ) := by
            simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
        _ = R * (G * K) * Rᵀ := by
            rw [htR, hKG, Matrix.one_mul]
            simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [l1, l2]
  have hJdet : IsUnit ((R⁻¹)ᵀ * K * Rᵀ).det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose]
    exact ((Matrix.isUnit_nonsing_inv_det R hR).mul hK).mul hR
  set C := R * G * Rᵀ with hCdef
  set J := (R⁻¹)ᵀ * K * Rᵀ with hJdef
  have hJinj : ∀ v : Fin d → ℝ, J *ᵥ v = 0 → v = 0 := by
    intro v hv
    have : (J⁻¹ * J) *ᵥ v = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    rwa [Matrix.nonsing_inv_mul J hJdet, Matrix.one_mulVec] at this
  have hH : C.IsHermitian := hCpsd.1
  have hCt : Cᵀ = C := by
    have := hH.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hsym : ∀ v w : Fin d → ℝ, (C *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (C *ᵥ w) := by
    intro v w
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hCt, dotProduct_comm]

  let ev : Fin d → (Fin d → ℝ) := fun j => ⇑(hH.eigenvectorBasis j)
  let lam : Fin d → ℝ := hH.eigenvalues
  have hCev : ∀ j, C *ᵥ ev j = lam j • ev j := fun j => hH.mulVec_eigenvectorBasis j
  have hort : ∀ i j, ev i ⬝ᵥ ev j = if j = i then 1 else 0 := by
    intro i j
    have := (orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal) j i
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    simpa [ev, star_trivial] using this
  have hinner : ∀ (v : Fin d → ℝ) j,
      inner ℝ (WithLp.toLp 2 v) (hH.eigenvectorBasis j) = ev j ⬝ᵥ v := by
    intro v j
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [ev, star_trivial]
  have hinner' : ∀ (v : Fin d → ℝ) j,
      inner ℝ (hH.eigenvectorBasis j) (WithLp.toLp 2 v) = ev j ⬝ᵥ v := by
    intro v j
    rw [real_inner_comm]; exact hinner v j
  have hquad : ∀ v : Fin d → ℝ, v ⬝ᵥ (C *ᵥ v) = ∑ j, lam j * (ev j ⬝ᵥ v) ^ 2 := by
    intro v
    have h := hH.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 v) (WithLp.toLp 2 (C *ᵥ v))
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simp only [hinner, hinner', star_trivial, WithLp.ofLp_toLp] at h
    rw [dotProduct_comm, ← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dotProduct_comm (ev j), ← hsym, hCev, smul_dotProduct, smul_eq_mul, dotProduct_comm v]
    ring
  have hpars : ∀ v : Fin d → ℝ, ∑ j, (ev j ⬝ᵥ v) ^ 2 = v ⬝ᵥ v := by
    intro v
    have h := hH.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 v) (WithLp.toLp 2 v)
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simp only [hinner, hinner', star_trivial, WithLp.ofLp_toLp] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hlam0 : ∀ j, 0 ≤ lam j := fun j => hCpsd.eigenvalues_nonneg j
  have htr : trace C = ∑ j, lam j := by simpa using hH.trace_eq_sum_eigenvalues

  have hlam : ∀ i, lam i ≤ trace C / 2 := by
    intro i
    set u := J *ᵥ ev i with hu
    have hCu : C *ᵥ u = lam i • u := by
      rw [hu, Matrix.mulVec_mulVec, hCJ, ← Matrix.mulVec_mulVec, hCev, Matrix.mulVec_smul]
    have hvu : ev i ⬝ᵥ u = 0 := by
      have h1 : ev i ⬝ᵥ u = (Jᵀ *ᵥ ev i) ⬝ᵥ ev i := by
        rw [hu, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
      rw [hJskew, Matrix.neg_mulVec, neg_dotProduct, ← hu, dotProduct_comm] at h1
      have h2 : u ⬝ᵥ ev i = 0 := by linarith
      rw [dotProduct_comm]; exact h2
    have hv1 : ev i ⬝ᵥ ev i = 1 := by rw [hort, if_pos rfl]
    have hu0 : u ≠ 0 := by
      intro h0
      have : ev i = 0 := hJinj _ (by rw [← hu, h0])
      rw [this, dotProduct_zero] at hv1
      exact zero_ne_one hv1
    have huu : 0 < u ⬝ᵥ u := by
      rcases (show 0 ≤ u ⬝ᵥ u from Finset.sum_nonneg fun k _ => mul_self_nonneg _).lt_or_eq with h | h
      · exact h
      · exact absurd (dotProduct_self_eq_zero.mp h.symm) hu0
    have hq1 : u ⬝ᵥ (C *ᵥ u) = lam i * (u ⬝ᵥ u) := by
      rw [hCu, dotProduct_smul, smul_eq_mul]
    have hq2 := hquad u
    have hsum1 : ∑ j, lam j * ((ev j ⬝ᵥ ev i) ^ 2 * (u ⬝ᵥ u)) = lam i * (u ⬝ᵥ u) := by
      simp only [hort]
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    have hbes : ∑ j, lam j * ((ev j ⬝ᵥ ev i) ^ 2 * (u ⬝ᵥ u) + (ev j ⬝ᵥ u) ^ 2) ≤
        ∑ j, lam j * (u ⬝ᵥ u) := by
      refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hlam0 j)
      exact bessel2 (ev j) (ev i) u (by rw [hort, if_pos rfl]) hv1 hvu huu
    simp only [mul_add, Finset.sum_add_distrib] at hbes
    rw [hsum1, ← hq2, hq1, ← Finset.sum_mul, ← htr] at hbes
    nlinarith

  have hcore : ∀ w : Fin d → ℝ, w ⬝ᵥ (C *ᵥ w) ≤ trace C / 2 * (w ⬝ᵥ w) := by
    intro w
    rw [hquad, ← hpars, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hlam j) (sq_nonneg _)

  have hx : x ⬝ᵥ (G *ᵥ x) = ((R⁻¹)ᵀ *ᵥ x) ⬝ᵥ (C *ᵥ ((R⁻¹)ᵀ *ᵥ x)) := by
    have e1 : C *ᵥ ((R⁻¹)ᵀ *ᵥ x) = R *ᵥ (G *ᵥ x) := by
      rw [hCdef, Matrix.mulVec_mulVec, Matrix.mul_assoc, hRt, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    rw [e1, Matrix.dotProduct_mulVec ((R⁻¹)ᵀ *ᵥ x) R, ← Matrix.mulVec_transpose,
      Matrix.mulVec_mulVec, hRt, Matrix.one_mulVec]
  rw [hx]
  have := hcore ((R⁻¹)ᵀ *ᵥ x)
  rw [hCtr] at this
  linarith

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
end
end

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open NumberField Module Formalism.MainNotions.ModuliIntegralCharts Matrix

variable {E : Type} [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y] {d : ℕ}

def muC (E : Type) [Field E] [NumberField E] : ℝ :=
  Real.sqrt ((finrank ℚ E : ℝ) * ((((discr E).natAbs : ℝ) ^ 2)⁻¹) ^ ((1 : ℝ) / finrank ℚ E) / 2)

theorem muC_sq : muC E ^ 2 =
    (finrank ℚ E : ℝ) * ((((discr E).natAbs : ℝ) ^ 2)⁻¹) ^ ((1 : ℝ) / finrank ℚ E) / 2 := by
  unfold muC
  rw [Real.sq_sqrt]
  positivity

theorem muC_pos : 0 < muC E := by
  unfold muC
  apply Real.sqrt_pos.mpr
  have h1 : (0 : ℝ) < finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have h0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E)
  have h2 : (0 : ℝ) < (((discr E).natAbs : ℝ) ^ 2)⁻¹ := by positivity
  positivity

theorem repr_left (b : Basis (Fin d) ℤ Y) (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (y z : Y) :
    ∑ j, (b.repr y j : ℝ) * β (b j) z = β y z := by
  conv_rhs => rw [← b.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul]

theorem repr_right (b : Basis (Fin d) ℤ Y) (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (y z : Y) :
    ∑ j, β z (b j) * (b.repr y j : ℝ) = β z y := by
  conv_rhs => rw [← b.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, zsmul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem repr_smul_expand (b : Basis (Fin d) ℤ Y) (u : 𝓞 E) (y : Y) (a : Fin d) :
    (b.repr (u • y) a : ℝ) = ∑ j, (b.repr y j : ℝ) * (b.repr (u • b j) a : ℝ) := by
  have h : u • y = ∑ j, b.repr y j • (u • b j) := by
    conv_lhs => rw [← b.sum_repr y]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm u (b.repr y j) (b j)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum, Finsupp.finsetSum_apply, Int.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, Finsupp.smul_apply, smul_eq_mul, Int.cast_mul]

def Kmat (b : Basis (Fin d) ℤ Y) (u : 𝓞 E) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun a c => (b.repr (u • b c) a : ℝ)

theorem Kmat_mul (b : Basis (Fin d) ℤ Y) (u v : 𝓞 E) : Kmat b u * Kmat b v = Kmat b (u * v) := by
  ext a c
  simp only [Kmat, Matrix.mul_apply, Matrix.of_apply]
  rw [mul_smul, repr_smul_expand b u (v • b c) a]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem Kmat_nat (b : Basis (Fin d) ℤ Y) (N : ℕ) : Kmat b (N : 𝓞 E) = (N : ℝ) • 1 := by
  ext a c
  simp only [Kmat, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [show ((N : 𝓞 E) • b c) = N • b c from Nat.cast_smul_eq_nsmul _ _ _, map_nsmul, b.repr_self,
    Finsupp.smul_apply, Finsupp.single_apply]
  by_cases h : a = c
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem Kmat_det (b : Basis (Fin d) ℤ Y) (θ : 𝓞 E) (hθ : θ ≠ 0) : IsUnit (Kmat b θ).det := by
  have hint : IsIntegral ℤ θ := by
    first
    | exact NumberField.RingOfIntegers.isIntegral θ
    | exact Algebra.IsIntegral.isIntegral θ
  have hc0 : (minpoly ℤ θ).coeff 0 ≠ 0 := by
    intro h0c
    obtain ⟨r, hr⟩ := Polynomial.X_dvd_iff.mpr h0c
    rcases (minpoly.irreducible hint).isUnit_or_isUnit hr with hu | hu
    · exact Polynomial.not_isUnit_X hu
    · have h := minpoly.aeval ℤ θ
      rw [hr, map_mul, Polynomial.aeval_X] at h
      exact hθ (((hu.map (Polynomial.aeval θ)).mul_left_eq_zero).mp h)
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := minpoly ℤ θ)
  have h0 : Polynomial.aeval θ (minpoly ℤ θ) = 0 := minpoly.aeval ℤ θ
  have h1 : θ * Polynomial.aeval θ q = -(((minpoly ℤ θ).coeff 0 : ℤ) : 𝓞 E) := by
    have h := congrArg (Polynomial.aeval θ) hq
    simp only [map_sub, Polynomial.aeval_C, map_mul, Polynomial.aeval_X, h0, zero_sub,
      eq_intCast, map_intCast] at h
    linear_combination -h
  have h2 : θ * (-(Polynomial.aeval θ q) * (((minpoly ℤ θ).coeff 0 : ℤ) : 𝓞 E)) =
      (((minpoly ℤ θ).coeff 0).natAbs ^ 2 : ℕ) := by
    have hc : ((((minpoly ℤ θ).coeff 0).natAbs ^ 2 : ℕ) : 𝓞 E) =
        (((minpoly ℤ θ).coeff 0 : ℤ) : 𝓞 E) ^ 2 := by
      have h' : ((((minpoly ℤ θ).coeff 0).natAbs ^ 2 : ℕ) : ℤ) = ((minpoly ℤ θ).coeff 0) ^ 2 := by
        push_cast
        first
        | exact sq_abs _
        | exact Int.natAbs_sq _
      rw [← Int.cast_natCast, h', Int.cast_pow]
    rw [hc]
    linear_combination (-(((minpoly ℤ θ).coeff 0 : ℤ) : 𝓞 E)) * h1
  have h3 := Kmat_mul b θ (-(Polynomial.aeval θ q) * (((minpoly ℤ θ).coeff 0 : ℤ) : 𝓞 E))
  rw [h2, Kmat_nat] at h3
  have h4 := congrArg Matrix.det h3
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h4
  have hN : ((((minpoly ℤ θ).coeff 0).natAbs ^ 2 : ℕ) : ℝ) ^ Fintype.card (Fin d) ≠ 0 := by
    have : ((minpoly ℤ θ).coeff 0).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hc0
    positivity
  rw [isUnit_iff_ne_zero]
  intro h
  rw [h, zero_mul] at h4
  exact hN h4.symm

theorem bs_comp (b : Basis (Fin d) ℤ Y) (u : 𝓞 E) (a : Fin d) :
    bs b a ∘ₗ smulZ u = ∑ j, Kmat b u a j • bs b j := by
  ext y
  have h1 : ∀ (a : Fin d) (z : Y), bs b a z = (b.repr z a : ℝ) := fun a z => by
    simp [bs]
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, h1,
    smul_eq_mul]
  have h2 : smulZ u y = u • y := rfl
  rw [h2, repr_smul_expand]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
  rfl

section Main

variable {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
include hcj

theorem Pm_comm (η ζ : Y →ₗ[ℤ] ℝ) : Pm hcj η ζ = Pm hcj ζ η := by
  apply Subtype.ext
  apply LinearMap.ext₂
  intro a c
  simp only [Pm_apply]
  exact Pf_comm η ζ a c

theorem Pm_skew (θ : 𝓞 E) (hθ : ∀ σ : E →+* ℂ, star (σ (θ : E)) = -σ (θ : E))
    (η ζ : Y →ₗ[ℤ] ℝ) : Pm hcj (η ∘ₗ smulZ θ) ζ = -Pm hcj η (ζ ∘ₗ smulZ θ) := by
  apply Subtype.ext
  apply LinearMap.ext₂
  intro a c
  simp only [Submodule.coe_neg, LinearMap.neg_apply, Pm_apply]
  exact Pf_skew θ hθ η ζ a c

theorem main_ineq (hne : ∃ z : E, cj z ≠ z) [Module.Free ℤ Y] [Module.Finite ℤ Y] (hd : 0 < d)
    (b : Basis (Fin d) ℤ Y) (β : SymB cj Y)
    (hG : (Matrix.of fun a c => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c)).PosDef)
    (l : SymB cj Y →ₗ[ℝ] ℝ)
    (hint : ∀ β' : SymB cj Y, (∀ a c, ∃ z : ℤ, (β' : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) →
      ∃ z : ℤ, l β' = z)
    (hpos : ∀ β' : SymB cj Y, (∀ a, 0 ≤ (β' : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → β' ≠ 0 → 0 < l β')
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : Fin d → Fin d → ℤ, LinearIndependent ℤ c ∧ ∀ j,
      (fun i => (c j i : ℝ)) ⬝ᵥ ((Matrix.of fun a c => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c)) *ᵥ
        fun i => (c j i : ℝ)) ≤ (1 / 2) * l β * ((d : ℝ) / muC E + δ) ^ 2 := by
  classical
  obtain ⟨m, x, x', htie⟩ := phiCTie_holds E cj Y l hint
  obtain ⟨θ, hθ0, hθ⟩ := exists_theta hcj hne
  have hθs : ∀ σ : E →+* ℂ, star (σ (θ : E)) = -σ (θ : E) := fun σ => by rw [← hcj, hθ, map_neg]
  set G := Matrix.of fun a c => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) with hGdef
  set L : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun a c => l (Pm hcj (bs b a) (bs b c)) / 2 with hLdef
  set K := Kmat b θ with hKdef
  have hPmsum : ∀ t : Fin d → ℝ, Pm hcj (∑ a, t a • bs b a) (∑ a, t a • bs b a) =
      ∑ a, ∑ c, (t a * t c) • Pm hcj (bs b a) (bs b c) := by
    intro t
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
      smul_smul]
    rw [Finset.sum_comm (f := fun x y => (t x * t y) • Pm hcj (bs b y) (bs b x))]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by rw [mul_comm]
  have hLq : ∀ t : Fin d → ℝ, t ⬝ᵥ (L *ᵥ t) =
      l (Pm hcj (∑ a, t a • bs b a) (∑ a, t a • bs b a)) / 2 := by
    intro t
    rw [hPmsum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, dotProduct, Matrix.mulVec, hLdef, Matrix.of_apply,
      Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  have hbs_ne : ∀ t : Fin d → ℝ, t ≠ 0 → ∑ a, t a • bs b a ≠ 0 := by
    intro t ht h0
    apply ht
    funext a
    have h1 := LinearMap.congr_fun h0 (b a)
    simpa [bs_apply, Basis.repr_self, Finsupp.single_apply, LinearMap.sum_apply] using h1
  have hLsym : ∀ a c, L a c = L c a := by
    intro a c
    simp only [hLdef, Matrix.of_apply, Pm_comm hcj (bs b a) (bs b c)]
  have hLpd : L.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun t ht => ?_
    · exact Matrix.IsHermitian.ext fun i j => by rw [star_trivial, hLsym]
    · rw [star_trivial, hLq]
      have := hpos _ (Pm_psd hcj _) (Pm_ne_zero hcj (hbs_ne t ht))
      linarith
  obtain ⟨R, hRdet, hLR⟩ := whiten_holds d L hLpd
  have hKG : Kᵀ * G = -(G * K) := by
    ext a c
    simp only [hKdef, hGdef, Kmat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.neg_apply]
    rw [repr_left b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (θ • b a) (b c),
      repr_right b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (θ • b c) (b a)]
    have hbal := β.2.2 θ (-θ) (by rw [hθ]; exact map_neg (algebraMap (𝓞 E) E) θ) (b a) (b c)
    rw [hbal, neg_smul, map_neg]
  have hKL : K * L = -(L * Kᵀ) := by
    ext a c
    have e1 : (K * L) a c = l (Pm hcj (bs b a ∘ₗ smulZ θ) (bs b c)) / 2 := by
      rw [bs_comp b θ a]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        Matrix.mul_apply, hLdef, hKdef, Matrix.of_apply, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : (L * Kᵀ) a c = l (Pm hcj (bs b a) (bs b c ∘ₗ smulZ θ)) / 2 := by
      rw [bs_comp b θ c]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply, hLdef,
        hKdef, Matrix.of_apply, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Matrix.neg_apply, e1, e2, Pm_skew hcj θ hθs, map_neg]
    ring
  have hKdet : IsUnit K.det := Kmat_det b θ (fun h => hθ0 (by rw [h]; simp))
  have htr : trace (L * G) = l β := by
    rw [l_expand hcj b l β]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hLdef, hGdef, Matrix.of_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [β.2.1 (b c) (b a)]
    ring
  have hlow : ∀ t : Fin d → ℤ, t ≠ 0 →
      muC E ^ 2 ≤ (fun i => (t i : ℝ)) ⬝ᵥ (L *ᵥ fun i => (t i : ℝ)) := by
    intro t ht
    rw [hLq, muC_sq]
    have hη : ∑ a, (t a : ℝ) • bs b a = Algebra.linearMap ℤ ℝ ∘ₗ (∑ a, t a • b.coord a) := by
      refine LinearMap.ext fun y => ?_
      simp [bs_apply, LinearMap.sum_apply, Basis.coord_apply]
    have hν : (∑ a, t a • b.coord a) ≠ 0 := by
      intro h0
      apply ht
      funext a
      have h1 := LinearMap.congr_fun h0 (b a)
      simpa [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, LinearMap.sum_apply] using h1
    rw [hη]
    have := lower_bound hcj l hpos x x' htie _ hν
    linarith
  obtain ⟨c, hcli, hcb⟩ := shortDual_holds d L R (muC E) hd hLR hRdet muC_pos hlow δ hδ
  refine ⟨c, hcli, fun j => ?_⟩
  have h1 := halfTrace_holds d L G K R hLR hRdet hG.posSemidef hKG hKL hKdet (fun i => (c j i : ℝ))
  rw [htr] at h1
  have hlβ : 0 ≤ l β := by
    by_cases h0 : β = 0
    · rw [h0, map_zero]
    · refine (hpos β (fun y => ?_) h0).le
      have h2 := hG.posSemidef.dotProduct_mulVec_nonneg (fun a => bs b a y)
      rw [star_trivial] at h2
      have h3 : (fun a => bs b a y) ⬝ᵥ (G *ᵥ fun a => bs b a y) =
          (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y y := by
        rw [← gram_expand b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y y]
        simp only [dotProduct, Matrix.mulVec, hGdef, Matrix.of_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
      linarith
  calc _ ≤ _ := h1
    _ ≤ (1 / 2) * l β * ((d : ℝ) / muC E + δ) ^ 2 :=
        mul_le_mul_of_nonneg_left (hcb j) (by linarith)

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
