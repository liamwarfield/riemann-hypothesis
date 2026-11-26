module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.QuotientTorusMinimumBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofSpanCondition
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofTorMkCIsQuotientMap

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZeroModeAddLattice
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZeroModeAddRealSpan
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZmGAddI
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.IKDiscrete
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

def IK {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) : Submodule ℤ (IR I) :=
  I.comap ((IR I).subtype.toAddMonoidHom.toIntLinearMap)

theorem mem_IK {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)} {x : IR I} :
    x ∈ IK I ↔ (x : Vsp dim) ∈ I := Iff.rfl

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

theorem IK_discrete (hI : IsSplit P I) : DiscreteTopology (IK I) := by
  let f : IK I → X.L := fun x => ⟨((x : IR I) : Vsp X.dim), hI.le (mem_IK.1 x.2)⟩
  have hc : Continuous f :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hinj : Function.Injective f := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  exact DiscreteTopology.of_continuous_injective hc hinj

theorem IK_span : Submodule.span ℝ (IK I : Set (IR I)) = ⊤ := by
  apply Submodule.map_injective_of_injective (IR I).injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  show _ = Submodule.span ℝ (I : Set (Vsp X.dim))
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact mem_IK.1 hz
  · intro hy
    exact ⟨⟨y, Submodule.subset_span hy⟩, mem_IK.2 hy, rfl⟩

def Ib (hI : IsSplit P I) : Module.Basis (Fin (Module.finrank ℝ (IR I))) ℝ (IR I) :=
  haveI := IK_discrete hI
  haveI : IsZLattice ℝ (IK I) := ⟨IK_span⟩
  haveI := ZLattice.module_free ℝ (IK I)
  (Module.Basis.ofZLatticeBasis ℝ (IK I) (Module.Free.chooseBasis ℤ (IK I))).reindex
    (Fintype.equivFinOfCardEq (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ]))

theorem Ib_span (hI : IsSplit P I) : Submodule.span ℤ (Set.range (Ib hI)) = IK I := by
  unfold Ib
  rw [Module.Basis.range_reindex, Module.Basis.ofZLatticeBasis_span]

theorem Ib_mem (hI : IsSplit P I) (i : Fin (Module.finrank ℝ (IR I))) :
    ((Ib hI i : IR I) : Vsp X.dim) ∈ I := by
  have h : Ib hI i ∈ IK I := by
    rw [← Ib_span hI]
    exact Submodule.subset_span (Set.mem_range_self i)
  exact mem_IK.1 h

theorem Ib_det_ne (hI : IsSplit P I) : (Col.ob (IR I)).toBasis.det (Ib hI) ≠ 0 := ((Module.Basis.is_basis_iff_det _).1 ⟨(Ib hI).linearIndependent, (Ib hI).span_eq⟩).ne_zero

def zmG (I : Submodule ℤ (Vsp X.dim)) (s : (Fin 1 → Vsp X.dim) → ℂ) (v : Vsp X.dim) : ℂ :=
  s (fun _ => v) * Complex.exp (-(Real.pi / 2) * Col.S (IR I) v)

def zmBox (d : ℕ) : Set (Fin d → ℝ) := {x | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}

def zmC (hI : IsSplit P I) (s : (Fin 1 → Vsp X.dim) → ℂ) (n : Fin (Module.finrank ℝ (IR I)) → ℤ)
    (v : Vsp X.dim) : ℂ :=
  ∫ t in zmBox (Module.finrank ℝ (IR I)),
    Complex.exp (-(2 * Real.pi * Complex.I * ∑ i, (n i : ℂ) * (t i : ℂ))) *
      zmG I s (v + ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim))

def zmB (hI : IsSplit P I) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ :=
  fun t => zmC hI s 0 (Col.jj (IR I) t)

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

theorem z_add {ι : Type} [Fintype ι] (K : Submodule ℝ (EuclideanSpace ℂ ι)) (k : Fin (dK K))
    (v w : EuclideanSpace ℂ ι) : z K k (v + w) = z K k v + z K k w := by
  simp [z, Hf, add_mul, Finset.sum_add_distrib]

theorem z_rsmul {ι : Type} [Fintype ι] (K : Submodule ℝ (EuclideanSpace ℂ ι)) (k : Fin (dK K))
    (t : ℝ) (v : EuclideanSpace ℂ ι) : z K k (t • v) = t * z K k v := by
  simp [z, Hf, Finset.mul_sum, mul_assoc]

theorem z_sum {ι : Type} [Fintype ι] (K : Submodule ℝ (EuclideanSpace ℂ ι)) (k : Fin (dK K))
    {κ : Type} (F : Finset κ) (f : κ → EuclideanSpace ℂ ι) :
    z K k (∑ j ∈ F, f j) = ∑ j ∈ F, z K k (f j) := by
  classical
  refine Finset.induction_on F ?_ ?_
  · simp [z, Hf]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, z_add, ih]

theorem conj_eq (ξ : ℂ) : (starRingEnd ℂ) ξ = ξ - 2 * (ξ.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp <;> ring

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

def gaugeExp (I : Submodule ℤ (Vsp X.dim)) (γ v : Vsp X.dim) : ℂ :=
  -(2 * Real.pi * Complex.I * ∑ k, ((z (IR I) k γ).im : ℂ) * z (IR I) k v) -
    Real.pi * Complex.I * ∑ k, z (IR I) k γ * ((z (IR I) k γ).im : ℂ) +
    Real.pi * Hf (p2 (IR I) v) (p2 (IR I) γ) + Real.pi * Hf (p2 (IR I) γ) (p2 (IR I) γ) / 2

private theorem Hf_add_left_euclidean {ι : Type} [Fintype ι] (x x' y : EuclideanSpace ℂ ι) :
    Hf (x + x') y = Hf x y + Hf x' y := by
  simp [Hf, add_mul, Finset.sum_add_distrib]

private theorem Hf_real_smul_left {ι : Type} [Fintype ι] (t : ℝ) (x y : EuclideanSpace ℂ ι) :
    Hf (t • x) y = t * Hf x y := by
  simp [Hf, Finset.mul_sum, mul_assoc]

private theorem Hf_add_right_euclidean {ι : Type} [Fintype ι] (x y y' : EuclideanSpace ℂ ι) :
    Hf x (y + y') = Hf x y + Hf x y' := by
  simp [Hf, mul_add, Finset.sum_add_distrib]

private theorem Hf_real_smul_right' {ι : Type} [Fintype ι] (t : ℝ) (x y : EuclideanSpace ℂ ι) :
    Hf x (t • y) = t * Hf x y := by
  simp [Hf, Finset.mul_sum, mul_left_comm]

private theorem Hf_im_eq_zero_on_IR_of_isSplit (hI : IsSplit P I) :
    ∀ a ∈ IR I, ∀ b ∈ IR I, (Hf a b).im = 0 := by
  intro a ha b hb
  change a ∈ Submodule.span ℝ (I : Set (Vsp X.dim)) at ha
  change b ∈ Submodule.span ℝ (I : Set (Vsp X.dim)) at hb
  induction hb using Submodule.span_induction with
  | mem y hy =>
    induction ha using Submodule.span_induction with
    | mem x hx => exact hI.iso x hx y hy
    | zero => simp [Hf]
    | add x x' _ _ h1 h2 => rw [Hf_add_left_euclidean, Complex.add_im, h1, h2, add_zero]
    | smul t x _ h => rw [Hf_real_smul_left, Complex.im_ofReal_mul, h, mul_zero]
  | zero => simp [Hf]
  | add y y' _ _ h1 h2 => rw [Hf_add_right_euclidean, Complex.add_im, h1, h2, add_zero]
  | smul t y _ h => rw [Hf_real_smul_right', Complex.im_ofReal_mul, h, mul_zero]

theorem zmG_add (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    {γ : Vsp X.dim} (hγ : γ ∈ X.L) (v : Vsp X.dim) :
    zmG I s (v + γ) = (X.eps γ : ℂ) * Complex.exp (gaugeExp I γ v) * zmG I s v := by
  have hsec := hs.2 (fun _ => γ) (fun _ => hγ) (fun _ => v)
  have hfun : (fun _ : Fin 1 => v + γ) = (fun _ => v) + (fun _ => γ) := rfl
  have hkey : ∀ a b c d : ℂ, a + b = c + d →
      (X.eps γ : ℂ) * Complex.exp a * s (fun _ => v) * Complex.exp b =
        (X.eps γ : ℂ) * Complex.exp c * (s (fun _ => v) * Complex.exp d) := by
    intro a b c d h
    have hab : Complex.exp a * Complex.exp b = Complex.exp c * Complex.exp d := by
      rw [← Complex.exp_add, ← Complex.exp_add, h]
    linear_combination ((X.eps γ : ℂ) * s (fun _ => v)) * hab
  have e1 : ∑ k, z (IR I) k v * (starRingEnd ℂ) (z (IR I) k γ) =
      ∑ k, z (IR I) k v * z (IR I) k γ -
        2 * Complex.I * ∑ k, ((z (IR I) k γ).im : ℂ) * z (IR I) k v := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conj_eq]
    ring
  have e2 : ∑ k, z (IR I) k γ * (starRingEnd ℂ) (z (IR I) k γ) =
      ∑ k, z (IR I) k γ ^ 2 -
        2 * Complex.I * ∑ k, z (IR I) k γ * ((z (IR I) k γ).im : ℂ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conj_eq]
    ring
  have e3 : Col.S (IR I) (v + γ) =
      Col.S (IR I) v + 2 * ∑ k, z (IR I) k v * z (IR I) k γ + ∑ k, z (IR I) k γ ^ 2 := by
    simp only [Col.S, z_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  unfold zmG
  rw [hfun, hsec]
  simp only [Fin.prod_univ_one, pow_one]
  apply hkey
  simp only [HC, Fin.sum_univ_one, Nat.cast_one, one_mul]
  rw [e3, Col.Hf_decomp (K := IR I) (Hf_im_eq_zero_on_IR_of_isSplit hI) v γ, Col.Hf_decomp (K := IR I) (Hf_im_eq_zero_on_IR_of_isSplit hI) γ γ, e1, e2]
  unfold gaugeExp
  push_cast
  ring

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

theorem z_eq_inner {ι : Type} [Fintype ι] (K : Submodule ℝ (EuclideanSpace ℂ ι)) (k : Fin (dK K))
    (v : EuclideanSpace ℂ ι) : z K k v = innerSL ℂ (e K k) v := by
  unfold z e Hf
  rw [innerSL_apply_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply]

theorem zmG_differentiable {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    Differentiable ℂ (zmG I s) := by
  unfold zmG
  have hs' : Differentiable ℂ s := (show Differentiable ℂ s ∧ _ from hs).1
  have h1 : Differentiable ℂ fun v : Vsp X.dim => s fun _ => v :=
    hs'.comp (differentiable_pi.2 fun _ => differentiable_id)
  refine h1.mul (Differentiable.cexp (Differentiable.const_mul ?_ _))
  unfold S
  have hz : ∀ k, Differentiable ℂ fun v : Vsp X.dim => z (IR I) k v ^ 2 := by
    intro k
    refine Differentiable.pow ?_ 2
    have hk : z (IR I) k = ⇑(innerSL ℂ (e (IR I) k)) :=
      funext fun v => z_eq_inner _ _ _
    rw [hk]
    exact (innerSL ℂ (e (IR I) k)).differentiable
  first
    | exact Differentiable.fun_sum fun k _ => hz k
    | exact Differentiable.sum fun k _ => hz k

theorem zmG_continuous {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    Continuous (zmG I s) := (zmG_differentiable hs).continuous

def tb (hI : IsSplit P I) (t : Fin (Module.finrank ℝ (IR I)) → ℝ) : Vsp X.dim :=
  ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim)

theorem tb_mem (hI : IsSplit P I) (t : Fin (Module.finrank ℝ (IR I)) → ℝ) : tb hI t ∈ IR I :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Ib hI i).2

theorem tb_add (hI : IsSplit P I) (t t' : Fin (Module.finrank ℝ (IR I)) → ℝ) :
    tb hI (t + t') = tb hI t + tb hI t' := by
  simp only [tb, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem tb_int (hI : IsSplit P I) (n : Fin (Module.finrank ℝ (IR I)) → ℤ) :
    tb hI (fun i => (n i : ℝ)) ∈ I := by
  unfold tb
  refine Submodule.sum_mem _ fun i _ => ?_
  have hK : (Ib hI i : IR I) ∈ IK I := by
    simp only [Ib, Module.Basis.reindex_apply, Module.Basis.ofZLatticeBasis_apply]
    exact SetLike.coe_mem _
  have hmem : ((Ib hI i : IR I) : Vsp X.dim) ∈ I := hK
  rw [Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ hmem

theorem zmC_eq (hI : IsSplit P I) (s : (Fin 1 → Vsp X.dim) → ℂ) (n) (v : Vsp X.dim) :
    zmC hI s n v = ∫ t in zmBox (Module.finrank ℝ (IR I)),
      Complex.exp (-(2 * Real.pi * Complex.I * ∑ i, (n i : ℂ) * (t i : ℂ))) * zmG I s (v + tb hI t) := rfl

theorem fib_continuous (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (v : Vsp X.dim) : Continuous fun t : Fin (Module.finrank ℝ (IR I)) → ℝ => zmG I s (v + tb hI t) := by
  refine (zmG_continuous hs).comp (continuous_const.add ?_)
  unfold tb
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

private lemma im_inner_eq_zero_on_real_span (S₀ : Set (Vsp X.dim))
    (hS : ∀ x ∈ S₀, ∀ y ∈ S₀, (inner ℂ x y).im = 0) :
    ∀ x ∈ Submodule.span ℝ S₀, ∀ y ∈ Submodule.span ℝ S₀, (inner ℂ x y).im = 0 := by
  have key : ∀ x : Vsp X.dim, (∀ y ∈ S₀, (inner ℂ x y).im = 0) →
      ∀ y ∈ Submodule.span ℝ S₀, (inner ℂ x y).im = 0 := by
    intro x hx y hy
    let f : Vsp X.dim →ₗ[ℝ] ℝ := Complex.imLm.comp ((innerSL ℂ x).toLinearMap.restrictScalars ℝ)
    have hf : ∀ u, f u = (inner ℂ x u).im := fun u => rfl
    have hle : Submodule.span ℝ S₀ ≤ LinearMap.ker f := by
      rw [Submodule.span_le]
      intro u hu
      rw [SetLike.mem_coe, LinearMap.mem_ker, hf]
      exact hx u hu
    have h := hle hy
    rwa [LinearMap.mem_ker, hf] at h
  intro x hx y hy
  have h1 : ∀ u ∈ S₀, (inner ℂ y u).im = 0 := by
    intro u hu
    have h := key u (hS u hu) y hy
    rw [← inner_conj_symm, Complex.conj_im, h, neg_zero]
  have h := key y h1 x hx
  rw [← inner_conj_symm, Complex.conj_im, h, neg_zero]

private lemma Hf_eq_inner_swap {ι : Type} [Fintype ι] (x y : EuclideanSpace ℂ ι) : Hf y x = inner ℂ x y := by
  unfold Hf
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply]

private lemma zmG_add_mem_of_isSplit (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (w γ : Vsp X.dim) (hγI : γ ∈ I) : zmG I s (w + γ) = zmG I s w := by
  have hγR : γ ∈ IR I := Submodule.subset_span hγI
  have hreal : ∀ x ∈ IR I, ∀ y ∈ IR I, (inner ℂ x y).im = 0 := by
    refine im_inner_eq_zero_on_real_span (I : Set (Vsp X.dim)) ?_
    intro x hx y hy
    have h := hI.iso y hy x hx
    rwa [Hf_eq_inner_swap] at h
  have hz : ∀ k u, z (IR I) k u = inner ℂ (e (IR I) k) u := by
    intro k u
    rw [z_eq_inner, innerSL_apply_apply]
  have hzadd : ∀ k (u u' : Vsp X.dim), z (IR I) k (u + u') = z (IR I) k u + z (IR I) k u' := by
    intro k u u'
    rw [hz, hz, hz, inner_add_right]
  let b := stdOrthonormalBasis ℝ (IR I)
  have heb : ∀ k : Fin (dK (IR I)), e (IR I) k = ((b k : IR I) : Vsp X.dim) := fun k => rfl
  have he_mem : ∀ k : Fin (dK (IR I)), e (IR I) k ∈ IR I := fun k => (b k).2
  obtain ⟨γ', hγ'⟩ : ∃ γ' : IR I, (γ' : Vsp X.dim) = γ := ⟨⟨γ, hγR⟩, rfl⟩
  have hexp : γ = ∑ k : Fin (dK (IR I)), (b.repr γ' k) • ((b k : IR I) : Vsp X.dim) := by
    have h := congrArg (fun x : IR I => (x : Vsp X.dim)) (b.sum_repr γ')
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [← hγ', ← h]
  have hzγ : ∀ k : Fin (dK (IR I)), z (IR I) k γ = ((b.repr γ' k : ℝ) : ℂ) := by
    intro k
    rw [hz]
    apply Complex.ext
    · rw [Complex.ofReal_re, OrthonormalBasis.repr_apply_apply, ← hγ', Submodule.coe_inner, heb]
      first
        | exact (real_inner_eq_re_inner (𝕜 := ℂ) _ _).symm
        | (rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
           refine Finset.sum_congr rfl fun i _ => ?_
           first
             | (rw [RCLike.inner_apply, Complex.inner, mul_comm])
             | (rw [RCLike.inner_apply, Complex.inner])
             | exact (real_inner_eq_re_inner (𝕜 := ℂ) _ _).symm
             | simp [Complex.inner, RCLike.inner_apply, mul_comm])
    · rw [Complex.ofReal_im]
      exact hreal _ (he_mem k) _ hγR
  have hstar : ∀ u : Vsp X.dim, ∑ k : Fin (dK (IR I)), z (IR I) k u * z (IR I) k γ = Hf u γ := by
    intro u
    rw [Hf_eq_inner_swap]
    conv_rhs => rw [hexp]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    first
      | (rw [hzγ, hz, heb, ← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal, mul_comm])
      | (rw [hzγ, hz, heb, ← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal, mul_comm]; rfl)
      | (rw [hzγ, hz, heb, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, RCLike.conj_ofReal,
          mul_comm]; congr 1)
  have hS : ∀ u : Vsp X.dim, S (IR I) (u + γ) = S (IR I) u + 2 * Hf u γ + Hf γ γ := by
    intro u
    unfold S
    rw [← hstar u, ← hstar γ, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hzadd]
    ring
  have hHC : ∀ a c : Vsp X.dim, HC (fun _ : Fin 1 => a) (fun _ => c) = Hf a c := by
    intro a c
    unfold HC Hf
    simp
  have hsec : s (fun _ => w + γ) =
      Complex.exp (↑Real.pi * Hf w γ + ↑Real.pi * Hf γ γ / 2) * s (fun _ => w) := by
    have h := (show Differentiable ℂ s ∧ _ from hs).2 (fun _ => γ) (fun _ => hI.le hγI) (fun _ => w)
    simpa [hHC, hI.eps γ hγI, Pi.add_def] using h
  unfold zmG
  rw [hsec, hS w]
  rw [show ∀ (a c d : ℂ), Complex.exp a * c * Complex.exp d = c * Complex.exp (a + d) from
    fun a c d => by rw [Complex.exp_add]; ring]
  congr 2
  ring

theorem fib_periodic (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (v : Vsp X.dim) (t : Fin (Module.finrank ℝ (IR I)) → ℝ) (n : Fin (Module.finrank ℝ (IR I)) → ℤ) :
    zmG I s (v + tb hI (t + fun i => (n i : ℝ))) = zmG I s (v + tb hI t) := by
  rw [tb_add, ← add_assoc]
  exact zmG_add_mem_of_isSplit hI hs _ _ (tb_int hI n)

theorem zeroMode_add_realSpan (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (v : Vsp X.dim) {a : Vsp X.dim} (ha : a ∈ IR I) : zmC hI s 0 (v + a) = zmC hI s 0 v := by
  set c := (Ib hI).repr ⟨a, ha⟩ with hc
  have hac : a = tb hI (fun i => c i) := by
    have h := congrArg Subtype.val ((Ib hI).sum_repr ⟨a, ha⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [tb]; exact h.symm
  simp only [zmC_eq, Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, mul_zero,
    neg_zero, Complex.exp_zero, one_mul]
  have hsh := tof_box_shift (fun t => zmG I s (v + tb hI t)) (fib_continuous hI hs v)
    (fun t n => fib_periodic hI hs v t n) (fun i => c i)
  rw [zmBox]
  rw [← hsh]
  congr 1
  funext t
  rw [hac, add_assoc, ← tb_add, add_comm t]

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

private theorem Hf_im_eq_zero_of_mem_IR_of_isSplit (hI : IsSplit P I) {x y : Vsp X.dim} (hx : x ∈ IR I) (hy : y ∈ IR I) :
    (Hf x y).im = 0 := by
  have hadd : ∀ a b c : Vsp X.dim, (Hf (a + b) c).im = (Hf a c).im + (Hf b c).im := by
    intro a b c
    simp [Hf, add_mul, Finset.sum_add_distrib]
  have hsmul : ∀ (r : ℝ) (a c : Vsp X.dim), (Hf (r • a) c).im = r * (Hf a c).im := by
    intro r a c
    simp [Hf, Finset.mul_sum, mul_assoc]
  have hzero : ∀ c : Vsp X.dim, (Hf 0 c).im = 0 := by
    intro c
    simp [Hf]
  have step1 : ∀ w ∈ I, ∀ v ∈ IR I, (Hf v w).im = 0 := by
    intro w hw v hv
    change v ∈ Submodule.span ℝ (I : Set (Vsp X.dim)) at hv
    induction hv using Submodule.span_induction with
    | mem a ha => exact hI.iso a ha w hw
    | zero => exact hzero w
    | add a b _ _ ha hb => rw [hadd, ha, hb, add_zero]
    | smul r a _ ha => rw [hsmul, ha, mul_zero]
  have step2 : (Hf y x).im = 0 := by
    change y ∈ Submodule.span ℝ (I : Set (Vsp X.dim)) at hy
    induction hy using Submodule.span_induction with
    | mem a ha => rw [Hf_conj, Complex.conj_im, step1 a ha x hx, neg_zero]
    | zero => exact hzero x
    | add a b _ _ ha hb => rw [hadd, ha, hb, add_zero]
    | smul r a _ ha => rw [hsmul, ha, mul_zero]
  rw [Hf_conj, Complex.conj_im, step2, neg_zero]

private theorem Hf_real_combination_left_im {κ : Type} [Fintype κ] (γ : Vsp X.dim) (r : κ → ℝ) (w : κ → Vsp X.dim) :
    (Hf (∑ k, r k • w k) γ).im = ∑ k, r k * (Hf (w k) γ).im := by
  simp [Hf, Complex.im_sum, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

theorem z_of_K (hI : IsSplit P I) (k : Fin (dK (IR I))) {b : Vsp X.dim} (hb : b ∈ IR I) :
    z (IR I) k b = ((inner ℝ (e (IR I) k) b : ℝ) : ℂ) := by
  have hek : e (IR I) k ∈ IR I := (ob (IR I) k).2
  apply Complex.ext
  · rw [Complex.ofReal_re]
    simp [z, Hf, real_inner_eq_re_inner, PiLp.inner_apply, Complex.mul_re, mul_comm]
  · rw [Complex.ofReal_im]
    exact Hf_im_eq_zero_of_mem_IR_of_isSplit hI hb hek

theorem sum_im_coord_mul (hI : IsSplit P I) (γ : Vsp X.dim) {b : Vsp X.dim} (hb : b ∈ IR I) :
    ∑ k, ((z (IR I) k γ).im : ℂ) * z (IR I) k b = ((Hf γ b).im : ℂ) := by
  have hexp : b = ∑ k, (inner ℝ (e (IR I) k) b) • e (IR I) k := by
    have h := congrArg Subtype.val ((ob (IR I)).sum_repr' ⟨b, hb⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    exact h.symm
  have hR : ∑ k, (z (IR I) k γ).im * inner ℝ (e (IR I) k) b = (Hf γ b).im := by
    have h1 : (Hf γ b).im = -(Hf b γ).im := by
      rw [Hf_conj γ b, Complex.conj_im, neg_neg]
    rw [h1]
    conv_rhs => rw [hexp]
    rw [Hf_real_combination_left_im, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have h2 : (Hf (e (IR I) k) γ).im = -(z (IR I) k γ).im := by
      simp only [z]
      rw [Hf_conj (e (IR I) k) γ, Complex.conj_im, neg_neg]
    rw [h2]
    ring
  simp_rw [z_of_K hI _ hb]
  exact_mod_cast hR

theorem gaugeExp_add_tb (hI : IsSplit P I) (γ v : Vsp X.dim) (t : Fin (Module.finrank ℝ (IR I)) → ℝ) :
    gaugeExp I γ (v + tb hI t) = gaugeExp I γ v -
      2 * Real.pi * Complex.I * ∑ i, ((Hf γ ((Ib hI i : IR I) : Vsp X.dim)).im : ℂ) * (t i : ℂ) := by
  have hmem : tb hI t ∈ IR I :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Ib hI i).2)
  have hzadd : ∀ k (x y : Vsp X.dim), z (IR I) k (x + y) = z (IR I) k x + z (IR I) k y := by
    intro k x y
    simp [z, Hf, add_mul, Finset.sum_add_distrib]
  have hcs : ∀ (r : ℝ) (x : Vsp X.dim), ((r : ℂ) • x) = r • x := by
    intro r x
    ext i
    simp [Complex.real_smul]
  have hp1 : ∀ w ∈ IR I, p1 (IR I) w = w := by
    intro w hw
    have hexp := congrArg Subtype.val ((ob (IR I)).sum_repr' ⟨w, hw⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at hexp
    simp only [p1]
    conv_rhs => rw [← hexp]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [z_of_K hI k hw, hcs]
    all_goals rfl
  have hp1add : ∀ x y : Vsp X.dim, p1 (IR I) (x + y) = p1 (IR I) x + p1 (IR I) y := by
    intro x y
    simp only [p1, hzadd, add_smul, Finset.sum_add_distrib]
  have hp2 : p2 (IR I) (v + tb hI t) = p2 (IR I) v := by
    simp only [p2, hp1add, hp1 _ hmem]
    abel
  have him : (Hf γ (tb hI t)).im = ∑ i, (Hf γ ((Ib hI i : IR I) : Vsp X.dim)).im * t i := by
    rw [Hf_conj (tb hI t) γ, Complex.conj_im]
    simp only [tb]
    rw [Hf_real_combination_left_im, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Hf_conj γ ((Ib hI i : IR I) : Vsp X.dim), Complex.conj_im]
    ring
  have hsplit : ∑ k, ((z (IR I) k γ).im : ℂ) * z (IR I) k (v + tb hI t) =
      ∑ k, ((z (IR I) k γ).im : ℂ) * z (IR I) k v + ((Hf γ (tb hI t)).im : ℂ) := by
    rw [← sum_im_coord_mul hI γ hmem, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hzadd, mul_add]
  unfold gaugeExp
  rw [hp2, hsplit, him]
  push_cast
  ring

theorem zmC_add (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    {γ : Vsp X.dim} (hγ : γ ∈ X.L) (m : Fin (Module.finrank ℝ (IR I)) → ℤ)
    (hm : ∀ i, (Hf γ ((Ib hI i : IR I) : Vsp X.dim)).im = m i)
    (n : Fin (Module.finrank ℝ (IR I)) → ℤ) (v : Vsp X.dim) :
    zmC hI s n (v + γ) = (X.eps γ : ℂ) * Complex.exp (gaugeExp I γ v) * zmC hI s (n + m) v := by
  have hg : ∀ t : Fin (Module.finrank ℝ (IR I)) → ℝ,
      gaugeExp I γ (v + ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim)) =
        gaugeExp I γ v - 2 * Real.pi * Complex.I * ∑ i, ((m i : ℤ) : ℂ) * (t i : ℂ) := by
    intro t
    have h := gaugeExp_add_tb hI γ v t
    simp only [tb] at h
    simp only [h, hm, Complex.ofReal_intCast]
  have hN : ∀ t : Fin (Module.finrank ℝ (IR I)) → ℝ,
      ∑ i, (((n + m) i : ℤ) : ℂ) * (t i : ℂ) =
        ∑ i, ((n i : ℤ) : ℂ) * (t i : ℂ) + ∑ i, ((m i : ℤ) : ℂ) * (t i : ℂ) := by
    intro t
    simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
  simp only [zmC]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  try dsimp only
  have hv : v + γ + ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim) =
      (v + ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim)) + γ := by
    abel
  rw [hv, zmG_add hI hs hγ, hg t, hN t]
  simp only [mul_add, neg_add, Complex.exp_add, Complex.exp_neg, Complex.exp_sub]
  ring

theorem zeroMode_add_lattice (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    {x : Vsp X.dim} (hx : x ∈ Col.Ip X I) (v : Vsp X.dim) :
    zmC hI s 0 (v + x) = (X.eps x : ℂ) *
      Complex.exp (Real.pi * Hf (p2 (IR I) v) (p2 (IR I) x) + Real.pi * Hf (p2 (IR I) x) (p2 (IR I) x) / 2) *
        zmC hI s 0 v := by
  have hx' : x ∈ X.L ∧ ∀ a ∈ I, (Hf x a).im = 0 := hx
  have hadd : ∀ a b c : Vsp X.dim, (Hf (a + b) c).im = (Hf a c).im + (Hf b c).im := by
    intro a b c
    simp [Hf, add_mul, Finset.sum_add_distrib]
  have hsmul : ∀ (r : ℝ) (a c : Vsp X.dim), (Hf (r • a) c).im = r * (Hf a c).im := by
    intro r a c
    simp [Hf, Finset.mul_sum, mul_assoc]
  have hzero : ∀ c : Vsp X.dim, (Hf 0 c).im = 0 := by
    intro c
    simp [Hf]
  have hIm : ∀ a ∈ IR I, (Hf a x).im = 0 := by
    intro a ha
    change a ∈ Submodule.span ℝ (I : Set (Vsp X.dim)) at ha
    induction ha using Submodule.span_induction with
    | mem b hb => rw [Hf_conj x b, Complex.conj_im, hx'.2 b hb, neg_zero]
    | zero => exact hzero x
    | add a b _ _ ha hb => rw [hadd, ha, hb, add_zero]
    | smul r a _ ha => rw [hsmul, ha, mul_zero]
  have hzx : ∀ k, (z (IR I) k x).im = 0 := by
    intro k
    have hek : e (IR I) k ∈ IR I := (ob (IR I) k).2
    simp only [z]
    rw [Hf_conj (e (IR I) k) x, Complex.conj_im, hIm _ hek, neg_zero]
  have hg : ∀ w, gaugeExp I x w =
      Real.pi * Hf (p2 (IR I) w) (p2 (IR I) x) + Real.pi * Hf (p2 (IR I) x) (p2 (IR I) x) / 2 := by
    intro w
    unfold gaugeExp
    simp only [hzx, Complex.ofReal_zero, zero_mul, mul_zero, Finset.sum_const_zero, neg_zero,
      zero_sub, sub_zero, zero_add]
    try ring
  have hzadd : ∀ k (a b : Vsp X.dim), z (IR I) k (a + b) = z (IR I) k a + z (IR I) k b := by
    intro k a b
    simp [z, Hf, add_mul, Finset.sum_add_distrib]
  have hcs : ∀ (r : ℝ) (a : Vsp X.dim), ((r : ℂ) • a) = r • a := by
    intro r a
    ext i
    simp [Complex.real_smul]
  have hp1 : ∀ w ∈ IR I, p1 (IR I) w = w := by
    intro w hw
    have hexp := congrArg Subtype.val ((ob (IR I)).sum_repr' ⟨w, hw⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at hexp
    simp only [p1]
    conv_rhs => rw [← hexp]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [z_of_K hI k hw, hcs]
    all_goals rfl
  have hp1add : ∀ a b : Vsp X.dim, p1 (IR I) (a + b) = p1 (IR I) a + p1 (IR I) b := by
    intro a b
    simp only [p1, hzadd, add_smul, Finset.sum_add_distrib]
  have hp2 : ∀ t : Fin (Module.finrank ℝ (IR I)) → ℝ,
      p2 (IR I) (v + ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim)) = p2 (IR I) v := by
    intro t
    have hmem : ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim) ∈ IR I :=
      Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Ib hI i).2)
    simp only [p2, hp1add, hp1 _ hmem]
    abel
  simp only [zmC]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  try dsimp only
  have hv : v + x + ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim) =
      (v + ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim)) + x := by
    abel
  rw [hv, zmG_add hI hs hx'.1, hg, hp2 t]
  ring

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col Topology

noncomputable section

theorem tof_box_int_differentiable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {d : ℕ} {G : V → ℂ} (hG : Differentiable ℂ G)
    {φ : (Fin d → ℝ) → V} (hφ : Continuous φ) :
    Differentiable ℂ (fun v => ∫ t in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}, G (v + φ t)) := by
  intro x₀
  have hcd : ContDiff ℂ (1 : ℕ) G := contDiff_of_differentiable_fd hG 1
  have hG' : Continuous (fderiv ℂ G) := hcd.continuous_fderiv (by norm_num)
  set B := {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} with hB
  have hBsub : B ⊆ Set.Icc 0 1 := fun x hx => ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩
  have hIcc : IsCompact (Set.Icc (0 : Fin d → ℝ) 1) := isCompact_Icc
  have hBm : MeasurableSet B := tof_box_measurable d
  have hfin : volume B < ⊤ := (measure_mono hBsub).trans_lt hIcc.measure_lt_top
  haveI : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hfin.ne
  have hKc : IsCompact ((fun p : V × (Fin d → ℝ) => p.1 + φ p.2) ''
      (Metric.closedBall x₀ 1 ×ˢ Set.Icc 0 1)) :=
    ((isCompact_closedBall x₀ 1).prod hIcc).image (continuous_fst.add (hφ.comp continuous_snd))
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hG'.continuousOn
  have hcont : ∀ x, Continuous fun t => G (x + φ t) := fun x =>
    hG.continuous.comp (continuous_const.add hφ)
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict B)
    (F := fun v t => G (v + φ t)) (F' := fun v t => fderiv ℂ G (v + φ t)) (x₀ := x₀)
    (bound := fun _ => C) (Metric.ball_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x => (hcont x).aestronglyMeasurable)
    (((hcont x₀).continuousOn.integrableOn_compact hIcc).mono_set hBsub)
    ((hG'.comp (continuous_const.add hφ)).aestronglyMeasurable)
    ((ae_restrict_iff' hBm).2 (Filter.Eventually.of_forall fun t ht x hx =>
      hC _ ⟨(x, t), ⟨Metric.ball_subset_closedBall hx, hBsub ht⟩, rfl⟩))
    (integrable_const C)
    (Filter.Eventually.of_forall fun t x _ => by
      have h1 := (hG (x + φ t)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (φ t))
      simp only [ContinuousLinearMap.comp_id] at h1
      exact h1)
  exact h.differentiableAt

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

theorem tb_continuous (hI : IsSplit P I) : Continuous (tb hI) := by
  unfold tb
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

theorem zeroMode_eq_fiber_integral (hI : IsSplit P I) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    zmC hI s 0 = fun v => ∫ t in {x : Fin (Module.finrank ℝ (IR I)) → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
      zmG I s (v + tb hI t) := by
  funext v
  simp [zmC, zmBox]
  rfl

theorem zeroMode_differentiable (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    Differentiable ℂ (zmC hI s 0) := by
  have hz : ∀ k, Differentiable ℂ (fun v : Vsp X.dim => Col.z (IR I) k v) := by
    intro k
    unfold Col.z Hf
    exact Differentiable.fun_sum fun i _ =>
      ((EuclideanSpace.proj i : Vsp X.dim →L[ℂ] ℂ).differentiable).mul_const _
  have hS : Differentiable ℂ (fun v => Col.S (IR I) v) := by
    unfold Col.S
    exact Differentiable.fun_sum fun k _ => (hz k).pow 2
  have hG : Differentiable ℂ (zmG I s) := by
    unfold zmG
    exact (hs.1.comp (differentiable_pi.2 fun _ => differentiable_id)).mul
      ((differentiable_const _).mul hS).cexp
  rw [zeroMode_eq_fiber_integral hI s]
  exact tof_box_int_differentiable hG (tb_continuous hI)

theorem zeroMode_add_real_direction (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (w : Vsp X.dim) (k : Fin (dK (IR I))) (ζ : ℂ) :
    zmC hI s 0 (w + ζ • e (IR I) k) = zmC hI s 0 w := by
  set ψ : ℂ → ℂ := fun ζ => zmC hI s 0 (w + ζ • e (IR I) k) with hψ
  have hdiff : Differentiable ℂ ψ :=
    (zeroMode_differentiable hI hs).comp ((differentiable_const _).add (differentiable_id.smul_const _))
  have hreal : ∀ ζ (t : ℝ), ψ (ζ + t) = ψ ζ := fun ζ t => by
    simp only [hψ]
    rw [add_smul, ← add_assoc, show ((t : ℂ)) • e (IR I) k = t • e (IR I) k from
      (Complex.coe_smul t _)]
    exact zeroMode_add_realSpan hI hs _ (Submodule.smul_mem _ _ (e_mem _ k))
  have hder : ∀ ζ, deriv ψ ζ = 0 := fun ζ => by
    have h1 : HasDerivAt (fun z => ψ (ζ + z)) (deriv ψ ζ) ((0 : ℝ) : ℂ) := by
      have := (hdiff (ζ + ((0 : ℝ) : ℂ))).hasDerivAt
      simpa using (this.comp_const_add ζ ((0 : ℝ) : ℂ))
    have h2 := h1.comp_ofReal
    have h3 : (fun y : ℝ => ψ (ζ + (y : ℂ))) = fun _ => ψ ζ := funext fun y => hreal ζ y
    rw [h3] at h2
    exact (h2.unique (hasDerivAt_const _ _)).symm ▸ rfl
  have := is_const_of_deriv_eq_zero hdiff hder ζ 0
  simpa [hψ] using this

theorem zeroMode_proj_two (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (v : Vsp X.dim) : zmC hI s 0 v = zmC hI s 0 (p2 (IR I) v) := by
  have hL : ∀ (L : Finset (Fin (dK (IR I)))) (c : Fin (dK (IR I)) → ℂ) (w : Vsp X.dim),
      zmC hI s 0 (w + ∑ k ∈ L, c k • e (IR I) k) = zmC hI s 0 w := by
    intro L c w
    induction L using Finset.induction_on with
    | empty => simp
    | insert a L ha ih =>
      rw [Finset.sum_insert ha, add_comm (c a • e (IR I) a), ← add_assoc, zeroMode_add_real_direction hI hs, ih]
  have hp : p2 (IR I) v = v + ∑ k, (-(z (IR I) k v)) • e (IR I) k := by
    simp only [p2, p1, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [hp, hL]

theorem proj_two_embedding (t : EuclideanSpace ℂ (Fin (gB (IR I)))) : p2 (IR I) (jj (IR I) t) = jj (IR I) t := by
  have hmem : jj (IR I) t ∈ V2 (IR I) := ((ob2 (IR I)).repr.symm t).2
  have hz : ∀ k, z (IR I) k (jj (IR I) t) = 0 := by
    intro k
    have h0 : inner ℂ (e (IR I) k) (jj (IR I) t) = 0 :=
      (Submodule.mem_orthogonal _ _).1 hmem _ (Submodule.subset_span ⟨k, rfl⟩)
    rw [PiLp.inner_apply] at h0
    simp only [z, Hf]
    rw [← h0]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  simp only [p2, p1, hz, zero_smul, Finset.sum_const_zero, sub_zero]

theorem jj_differentiable : Differentiable ℂ (jj (IR I)) := by
  exact ((V2 (IR I)).subtypeL.comp
    ((ob2 (IR I)).repr.symm.toContinuousLinearEquiv : EuclideanSpace ℂ (Fin (gB (IR I))) →L[ℂ] V2 (IR I))).differentiable

end ZM

open ZM in
theorem zeroMode_mem_sections [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
    {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I) (hP : Ext.PackingCount)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    ZM.zmB hI s ∈ (Col.YB hI hP 1).Sec 1 := by
  have hK := hK_of hI
  refine ⟨(zeroMode_differentiable hI hs).comp jj_differentiable, fun γ hγ t => ?_⟩
  obtain ⟨x, hx, rfl⟩ := mem_GB.1 ((YB_lat hI hP 1).1 hγ)
  simp only [zmB]
  rw [jj_add, jj_wmap' hK]
  have hp1 : p1 (IR I) x ∈ IR I := proj_one_mem_realSpan hx
  rw [← zeroMode_add_realSpan hI hs (jj (IR I) t + p2 (IR I) x) hp1,
    show jj (IR I) t + p2 (IR I) x + p1 (IR I) x = jj (IR I) t + x by rw [p2]; abel]
  rw [zeroMode_add_lattice hI hs hx, proj_two_embedding, YB_ka hI hP 1 hx, pow_one]
  have h1 : Hf t (wmap (IR I) x) = Hf (jj (IR I) t) (p2 (IR I) x) := by
    conv_lhs => rw [← wmap_jj (IR I) t]
    rw [Hf_wmap hK, proj_two_embedding]
  have h2 : Hf (wmap (IR I) x) (wmap (IR I) x) = Hf (p2 (IR I) x) (p2 (IR I) x) := Hf_wmap hK x x
  simp only [Nat.cast_one, one_mul]
  rw [h1, h2]

end

end ReciprocityTheory.ChartRestriction.G.I2
