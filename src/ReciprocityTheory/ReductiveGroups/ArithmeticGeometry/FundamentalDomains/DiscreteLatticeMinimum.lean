module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LatticeSpanMembership

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealTangentSpace
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace RealTangentSpace

open NumberField Complex Module
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

def Usub (z : Frame X.Ψ r) (ξ : Fin r → E) : Submodule ℝ (X.Ψ → Fin r → ℂ) where
  carrier := X.Uz z ξ
  add_mem' := MajorantOperators.add_mem
  zero_mem' := MajorantOperators.zero_mem z ξ
  smul_mem' c u hu := by
    have hs : c • u = fun τ => (c : ℂ) • u τ := by
      funext τ
      exact (Pi.smul_apply c u τ).trans (Complex.coe_smul c (u τ)).symm
    rw [hs]
    exact MajorantOperators.smul_fam_mem (fun _ => (c : ℂ)) hu

def VT (z : Frame X.Ψ r) (ξ : Fin r → E) : Type := ↥(Usub (X := X) z ξ)

variable (z : Frame X.Ψ r) (ξ : Fin r → E)

noncomputable instance : AddCommGroup (VT (X := X) z ξ) := inferInstanceAs (AddCommGroup ↥(Usub (X := X) z ξ))
noncomputable instance : Module ℝ (VT (X := X) z ξ) := inferInstanceAs (Module ℝ ↥(Usub (X := X) z ξ))
instance : FiniteDimensional ℝ (VT (X := X) z ξ) :=
  inferInstanceAs (FiniteDimensional ℝ ↥(Usub (X := X) z ξ))

def VT.val {z : Frame X.Ψ r} {ξ : Fin r → E} (u : VT (X := X) z ξ) : X.Ψ → Fin r → ℂ :=
  (u : ↥(Usub (X := X) z ξ)).1

theorem VT.val_mem {z : Frame X.Ψ r} {ξ : Fin r → E} (u : VT (X := X) z ξ) : u.val ∈ X.Uz z ξ := by
  exact (u : ↥(Usub (X := X) z ξ)).2

def VT.mk {z : Frame X.Ψ r} {ξ : Fin r → E} (u : X.Ψ → Fin r → ℂ) (hu : u ∈ X.Uz z ξ) :
    VT (X := X) z ξ := (⟨u, hu⟩ : ↥(Usub (X := X) z ξ))

@[simp] theorem VT.val_mk {z : Frame X.Ψ r} {ξ : Fin r → E} (u : X.Ψ → Fin r → ℂ)
    (hu : u ∈ X.Uz z ξ) : (VT.mk u hu).val = u := rfl

theorem VT.ext {z : Frame X.Ψ r} {ξ : Fin r → E} {u v : VT (X := X) z ξ} (h : u.val = v.val) :
    u = v := by
  exact Subtype.ext h

@[simp] theorem VT.val_add {z : Frame X.Ψ r} {ξ : Fin r → E} (u v : VT (X := X) z ξ) :
    (u + v).val = u.val + v.val := rfl

@[simp] theorem VT.val_smul {z : Frame X.Ψ r} {ξ : Fin r → E} (c : ℝ) (u : VT (X := X) z ξ) :
    (c • u).val = c • u.val := rfl

@[simp] theorem VT.val_sub {z : Frame X.Ψ r} {ξ : Fin r → E} (u v : VT (X := X) z ξ) :
    (u - v).val = u.val - v.val := rfl

variable [hz : Fact (z ∈ X.dom)]

@[instance_reducible]
noncomputable def core : InnerProductSpace.Core ℝ (VT (X := X) z ξ) where
  inner u v := MajorantOperators.gI z u.val v.val
  conj_inner_symm u v := by
    simp only [starRingEnd_apply, star_trivial]
    exact MajorantOperators.gI_comm hz.out _ _
  re_inner_nonneg u := by
    simp only [RCLike.re_to_real]
    rw [MajorantOperators.gI_self hz.out]
    exact Finset.sum_nonneg fun τ _ => MajorantOperators.maj_nonneg hz.out τ _
  add_left u v w := by
    show MajorantOperators.gI z (u.val + v.val) w.val = _
    exact MajorantOperators.gI_add_left z _ _ _
  smul_left u v c := by
    show MajorantOperators.gI z (c • u.val) v.val = _
    rw [MajorantOperators.gI_smul_left]
    simp
  definite u h := by
    rw [MajorantOperators.gI_self hz.out] at h
    have h0 : ∀ τ ∈ Finset.univ, X.maj z τ (u.val τ) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => MajorantOperators.maj_nonneg hz.out τ _).mp h
    apply VT.ext
    funext τ
    by_contra hne
    exact (X.maj_pos hz.out τ hne).ne' (h0 τ (Finset.mem_univ τ))

noncomputable instance : NormedAddCommGroup (VT (X := X) z ξ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (VT (X := X) z ξ) _ _ _ (core z ξ)

noncomputable instance : InnerProductSpace ℝ (VT (X := X) z ξ) :=
  InnerProductSpace.ofCore (core z ξ).toCore

theorem inner_eq (u v : VT (X := X) z ξ) : inner ℝ u v = MajorantOperators.gI z u.val v.val := rfl

theorem norm_sq_eq (u : VT (X := X) z ξ) : ‖u‖ ^ 2 = ∑ τ, X.maj z τ (u.val τ) := by
  rw [← real_inner_self_eq_norm_sq, inner_eq, MajorantOperators.gI_self hz.out]

theorem maj_le_norm_sq (u : VT (X := X) z ξ) (τ : X.Ψ) : X.maj z τ (u.val τ) ≤ ‖u‖ ^ 2 := by
  rw [norm_sq_eq]
  exact Finset.single_le_sum (fun σ _ => MajorantOperators.maj_nonneg hz.out σ _) (Finset.mem_univ τ)

omit hz in
theorem ucomp_add (u v : X.Ψ → Fin r → ℂ) :
    X.ucomp z ξ (u + v) = X.ucomp z ξ u + X.ucomp z ξ v := by
  have hHf : ∀ (σ : X.Ψ) (a b w : Fin r → ℂ),
      X.Hf z σ (a + b) w = X.Hf z σ a w + X.Hf z σ b w := by
    intro σ a b w
    rw [Data.Hf, Data.Hf, Data.Hf, Data.ppos_add, ← hermC_add_left]
    congr 1
    rw [smul_add]
    abel
  funext τ
  simp only [Data.ucomp, Data.aproj, Data.lineV, Pi.add_apply, Pi.sub_apply, hHf, add_div, add_smul]
  abel

omit hz in
theorem ucomp_smul (a : ℝ) (u : X.Ψ → Fin r → ℂ) : X.ucomp z ξ (a • u) = a • X.ucomp z ξ u := by
  have hHf : ∀ (σ : X.Ψ) (c : ℂ) (v w : Fin r → ℂ), X.Hf z σ (c • v) w = c * X.Hf z σ v w := by
    intro σ c v w
    have hp : X.ppos z σ (c • v) = c • X.ppos z σ v := by
      simp only [Data.ppos, hermC_smul_left, Finset.smul_sum, smul_smul, mul_assoc, ← Finset.mul_sum]
    rw [Data.Hf, Data.Hf, hp, ← hermC_smul_left]
    congr 1
    rw [smul_sub, smul_smul, smul_smul, mul_comm]
  funext τ
  simp only [Data.ucomp, Data.aproj, Data.lineV, Pi.sub_apply, Pi.smul_apply, ← Complex.coe_smul,
    hHf]
  rw [smul_sub, mul_div_assoc, mul_smul]

theorem embV_add (u v : Fin r → E) : X.embV (u + v) = X.embV u + X.embV v := by
  funext τ a
  simp [Data.embV, Data.emb]

omit hz in
theorem embV_mem_Iperp {μ : Fin r → E} (hμ : μ ∈ X.Λp ξ) : X.embV μ ∈ X.Iperp ξ := by
  have hk : herm X.Gm μ ξ = 0 := AddMonoidHom.mem_ker.mp (AddSubgroup.mem_inf.mp hμ).2
  show ∀ τ : X.Ψ, hermC τ.1 X.Gm (X.embV μ τ) (Data.emb τ.1 ξ) = 0
  intro τ
  simp only [Data.embV]
  rw [hermC_emb, hk, map_zero]

noncomputable def phi (hξ : X.IsIso ξ) : X.Λp ξ →+ VT (X := X) z ξ :=
  AddMonoidHom.mk' (fun μ => VT.mk (X.ucomp z ξ (X.embV μ))
      (orthogonal_lattice_decomposition r X ξ hξ z hz.out _ (embV_mem_Iperp ξ μ.2)))
    (fun μ ν => VT.ext (by
      simp only [VT.val_mk, VT.val_add, AddSubgroup.coe_add]
      rw [embV_add, ucomp_add]))

theorem phi_val (hξ : X.IsIso ξ) (μ : X.Λp ξ) : (phi z ξ hξ μ).val = X.ucomp z ξ (X.embV μ) := by
  rfl

noncomputable def Lat (hξ : X.IsIso ξ) : Submodule ℤ (VT (X := X) z ξ) :=
  (phi z ξ hξ).range.toIntSubmodule

theorem mem_Lat (hξ : X.IsIso ξ) {a : VT (X := X) z ξ} : a ∈ Lat z ξ hξ ↔ ∃ μ, phi z ξ hξ μ = a := by
  show a ∈ (phi z ξ hξ).range ↔ _
  exact AddMonoidHom.mem_range

private lemma Hf_smul_left_frame (y : Frame X.Ψ r) (σ : X.Ψ) (c : ℂ) (v w : Fin r → ℂ) :
    X.Hf y σ (c • v) w = c * X.Hf y σ v w := by
  have hp : X.ppos y σ (c • v) = c • X.ppos y σ v := by
    simp only [Data.ppos, hermC_smul_left, Finset.smul_sum, smul_smul, mul_assoc, ← Finset.mul_sum]
  rw [Data.Hf, Data.Hf, hp, ← hermC_smul_left]
  congr 1
  rw [smul_sub, smul_smul, smul_smul, mul_comm]

theorem ucomp_line (hξ : X.IsIso ξ) (e : E) : X.ucomp z ξ (X.embV (e • ξ)) = 0 := by
  funext τ
  have hξ0 : Data.emb τ.1 ξ ≠ 0 := by
    intro h
    apply hξ.2.2
    funext a
    have := congrFun h a
    simpa [Data.emb] using this
  have hpos : X.Hf z τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := by
    rw [X.Hf_self hz.out]
    exact_mod_cast (X.maj_pos hz.out τ hξ0).ne'
  have hw : X.embV (e • ξ) τ = τ.1 e • Data.emb τ.1 ξ := by
    funext a
    simp [Data.embV, Data.emb]
  simp only [Data.ucomp, Data.aproj, Data.lineV, Pi.sub_apply, Pi.zero_apply, hw, Hf_smul_left_frame,
    mul_div_assoc, div_self hpos, mul_one, sub_self]

theorem span_Lat (hD3 : IntegerApproximationCount (E := E)) (hξ : X.IsIso ξ) :
    Submodule.span ℝ (Lat z ξ hξ : Set (VT (X := X) z ξ)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  let S : VT (X := X) z ξ →ₗ[ℝ] (X.Ψ → Fin r → ℂ) :=
    { toFun := fun a => a.val
      map_add' := fun a b => VT.val_add a b
      map_smul' := fun c a => VT.val_smul c a }
  have hS : Function.Injective S := fun a b h => VT.ext h
  have h1 := LatticeSpanMembership.Uz_le_span hD3 hξ v.val_mem
  have h2 : Submodule.span ℝ (Set.range fun μ : X.Λp ξ => X.ucomp z ξ (X.embV μ)) ≤
      Submodule.map S (Submodule.span ℝ (Lat z ξ hξ : Set (VT (X := X) z ξ))) := by
    rw [Submodule.span_le]
    rintro _ ⟨μ, rfl⟩
    exact Submodule.mem_map_of_mem (Submodule.subset_span ((mem_Lat z ξ hξ).mpr ⟨μ, rfl⟩))
  obtain ⟨w, hw, hwv⟩ := h2 h1
  rwa [hS hwv] at hw

end RealTangentSpace

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DiscriminantTraceBounds
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace DiscriminantTraceBounds

open NumberField Complex Module Matrix
open scoped ComplexConjugate nonZeroDivisors

variable {E : Type} [Field E] [NumberField E]

theorem norm_mul_discr_ge {x : E} (hx : x ≠ 0)
    (htr : ∀ β : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (x * β) = m) :
    1 ≤ |Algebra.norm ℚ x| * |(NumberField.discr E : ℚ)| := by
  classical
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [← FractionalIdeal.coeIdeal_top, Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact top_ne_bot
  have hD0 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ h10
  have hmem : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual h10]
    intro a ha
    obtain ⟨β, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨m, hm⟩ := htr β
    refine ⟨m, ?_⟩
    rw [Algebra.traceForm_apply]
    simpa using hm.symm
  have hsp : FractionalIdeal.spanSingleton (𝓞 E)⁰ x ≤ FractionalIdeal.dual ℤ ℚ 1 :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hmem
  have hdiff := coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)
  have hJ : FractionalIdeal.spanSingleton (𝓞 E)⁰ x *
      (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E) ≤ 1 := by
    rw [hdiff]
    calc _ ≤ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) *
          (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E))⁻¹ := by
            first
            | exact mul_le_mul' hsp le_rfl
            | exact mul_right_mono hsp
            | exact FractionalIdeal.mul_right_mono _ hsp
      _ = 1 := mul_inv_cancel₀ hD0
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ
  have hJ0 : FractionalIdeal.spanSingleton (𝓞 E)⁰ x *
      (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    refine mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) ?_
    rw [hdiff]
    exact inv_ne_zero hD0
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    apply hJ0
    rw [← hI]
    simp
  have hnorm := congrArg FractionalIdeal.absNorm hI
  rw [FractionalIdeal.coeIdeal_absNorm, map_mul, FractionalIdeal.absNorm_span_singleton,
    FractionalIdeal.coeIdeal_absNorm, NumberField.absNorm_differentIdeal E (𝓞 E)] at hnorm
  have h1 : (1 : ℚ) ≤ (Ideal.absNorm I : ℚ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hI0 (Ideal.absNorm_eq_zero_iff.mp h))
  rw [hnorm] at h1
  have h2 : (((NumberField.discr E).natAbs : ℕ) : ℚ) = |(NumberField.discr E : ℚ)| := by
    rw [Nat.cast_natAbs]
    push_cast
    rfl
  rw [h2] at h1
  exact h1

theorem abs_norm_eq_pow {x : E} {a : ℝ} (h : ∀ σ : E →+* ℂ, ‖σ x‖ = a) :
    |((Algebra.norm ℚ x : ℚ) : ℝ)| = a ^ finrank ℚ E := by
  have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  have h2 : ‖algebraMap ℚ ℂ (Algebra.norm ℚ x)‖ = a ^ finrank ℚ E := by
    rw [h1, norm_prod, Finset.prod_congr rfl (fun σ _ => h σ.toRingHom), Finset.prod_const,
      Finset.card_univ, AlgHom.card]
  rw [← h2, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

section data

variable [IsCMField E] {r : ℕ} (X : DataX E r)

theorem exists_herm_ne (hr : 0 < r) : ∃ x ∈ X.L', ∃ y ∈ X.L', herm X.Gm x y ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hcc_add : ∀ a b : E, cc (a + b) = cc a + cc b := fun a b => by
    unfold cc
    exact map_add _ a b
  have hcc_mul : ∀ a b : E, cc (a * b) = cc a * cc b := fun a b => by
    unfold cc
    exact map_mul _ a b
  have hcc0 : cc (0 : E) = 0 := by
    unfold cc
    exact map_zero _
  have hcc1 : cc (1 : E) = 1 := by
    unfold cc
    exact map_one _
  have hadd2 : ∀ x y y' : Fin r → E, herm X.Gm x (y + y') = herm X.Gm x y + herm X.Gm x y' := by
    intro x y y'
    simp only [herm, Pi.add_apply, hcc_add, mul_add, Finset.sum_add_distrib]
  have hsmul2 : ∀ (x y : Fin r → E) (c : E), herm X.Gm x (c • y) = cc c * herm X.Gm x y := by
    intro x y c
    simp only [herm, Pi.smul_apply, smul_eq_mul, hcc_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hzero2 : ∀ x : Fin r → E, herm X.Gm x 0 = 0 := fun x => by simp [herm, hcc0]
  have hadd1 : ∀ x x' y : Fin r → E, herm X.Gm (x + x') y = herm X.Gm x y + herm X.Gm x' y := by
    intro x x' y
    simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hsmul1 : ∀ (x y : Fin r → E) (c : E), herm X.Gm (c • x) y = c * herm X.Gm x y := by
    intro x y c
    simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hzero1 : ∀ y : Fin r → E, herm X.Gm 0 y = 0 := fun y => by simp [herm]
  have hspan : Submodule.span E (X.L' : Set (Fin r → E)) = ⊤ := by
    rw [eq_top_iff, ← X.Λ_span]
    apply Submodule.span_le.mpr
    intro z hz
    have h1 := X.NA_sub z hz
    have hNA : (X.NA : E) ≠ 0 := Nat.cast_ne_zero.mpr X.NA_pos.ne'
    have hz' : z = (X.NA : E)⁻¹ • ((X.NA : E) • z) := by
      rw [smul_smul, inv_mul_cancel₀ hNA, one_smul]
    rw [hz']
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  have hall2 : ∀ x ∈ X.L', ∀ y, herm X.Gm x y = 0 := by
    intro x hx y
    have hy : y ∈ Submodule.span E (X.L' : Set (Fin r → E)) := by
      rw [hspan]
      exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact hcon x hx y hy
    | zero => exact hzero2 x
    | add y y' _ _ h1 h2 => rw [hadd2, h1, h2, add_zero]
    | smul c y _ h => rw [hsmul2, h, mul_zero]
  have hall : ∀ x y : Fin r → E, herm X.Gm x y = 0 := by
    intro x y
    have hx : x ∈ Submodule.span E (X.L' : Set (Fin r → E)) := by
      rw [hspan]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact hall2 x hx y
    | zero => exact hzero1 y
    | add x x' _ _ h1 h2 => rw [hadd1, h1, h2, add_zero]
    | smul c x _ h => rw [hsmul1, h, mul_zero]
  have hG : X.Gm = 0 := by
    ext a b
    have hval : herm X.Gm (Pi.single a 1) (Pi.single b 1) = X.Gm a b := by
      simp [herm, Pi.single_apply, apply_ite cc, hcc1, hcc0]
    rw [Matrix.zero_apply, ← hval]
    exact hall _ _
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  exact X.Gm_det (by rw [hG]; exact Matrix.det_zero)

private theorem herm_smul_left_eq_mul (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private theorem herm_smul_right_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G x (c • y) = cc c * herm G x y := by
  have hcc_mul : ∀ a b : E, cc (a * b) = cc a * cc b := fun a b => by
    unfold cc
    exact map_mul _ a b
  simp only [herm, Pi.smul_apply, smul_eq_mul, hcc_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem trace_int (hr : 0 < r) (c : 𝓞 E) :
    ∃ m : ℤ, Algebra.trace ℚ E ((X.NC : E) ^ 2 * X.ξ0 * c) = m := by
  classical
  set gens : Set (𝓞 E) := {c | ∃ x ∈ X.L', ∃ y ∈ X.L', (c : E) = herm X.Gm x y} with hgens
  set J : Ideal (𝓞 E) := Ideal.span gens with hJdef
  have hgen_mem : ∀ x ∈ X.L', ∀ y ∈ X.L', ∃ c ∈ J, (c : E) = herm X.Gm x y := by
    intro x hx y hy
    exact ⟨⟨herm X.Gm x y, X.L'_int x hx y hy⟩, Ideal.subset_span ⟨x, hx, y, hy, rfl⟩, rfl⟩
  have hJ0 : J ≠ ⊥ := by
    obtain ⟨x, hx, y, hy, hne⟩ := exists_herm_ne X hr
    obtain ⟨c, hc, hce⟩ := hgen_mem x hx y hy
    intro hbot
    rw [hbot, Ideal.mem_bot] at hc
    apply hne
    rw [← hce, hc]
    simp
  have hJf0 : (J : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact hJ0
  have hmemJf : ∀ c ∈ J, ((c : 𝓞 E) : E) ∈ (J : FractionalIdeal (𝓞 E)⁰ E) :=
    fun c hc => (FractionalIdeal.mem_coeIdeal _).mpr ⟨c, hc, rfl⟩
  have hinv : ∀ t ∈ (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹, ∀ x ∈ X.L', t • x ∈ X.L' := by
    intro t ht x hx
    apply X.L'_dual
    intro y hy
    rw [herm_smul_left_eq_mul]
    obtain ⟨c, hc, hce⟩ := hgen_mem x hx y hy
    have h1 := (FractionalIdeal.mem_inv_iff hJf0).mp ht _ (hmemJf c hc)
    obtain ⟨d, hd⟩ := (FractionalIdeal.mem_one_iff _).mp h1
    rw [← hce, ← hd]
    exact RingOfIntegers.isIntegral_coe d
  have hmul : ∀ t ∈ (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹, ∀ c ∈ J,
      t * (c : E) ∈ (J : FractionalIdeal (𝓞 E)⁰ E) := by
    intro t ht c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨x, hx, y, hy, hce⟩ := hc
      rw [hce, ← herm_smul_left_eq_mul]
      obtain ⟨c', hc', hce'⟩ := hgen_mem _ (hinv t ht x hx) y hy
      rw [← hce']
      exact hmemJf c' hc'
    | zero =>
      simp
    | add a b _ _ ha hb =>
      push_cast
      rw [mul_add]
      exact Submodule.add_mem _ ha hb
    | smul a c _ h =>
      rw [smul_eq_mul]
      push_cast
      rw [mul_left_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ a h
  have hle : (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹ * (J : FractionalIdeal (𝓞 E)⁰ E) ≤
      (J : FractionalIdeal (𝓞 E)⁰ E) := FractionalIdeal.mul_le.mpr fun t ht j hj => by
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hj
    exact hmul t ht c hc
  rw [inv_mul_cancel₀ hJf0] at hle
  have hJtop : J = ⊤ := by
    rw [eq_top_iff]
    rw [← FractionalIdeal.coeIdeal_top] at hle
    exact (FractionalIdeal.coeIdeal_le_coeIdeal E).mp hle
  have hccNC : cc (X.NC : E) = X.NC := by
    unfold cc
    exact map_natCast _ _
  have hP : ∀ c ∈ J, ∀ a : 𝓞 E, ∃ m : ℤ,
      Algebra.trace ℚ E ((X.NC : E) ^ 2 * X.ξ0 * ((a : E) * (c : E))) = m := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      intro a
      obtain ⟨x, hx, y, hy, hce⟩ := hc
      have hax : (a : E) • x ∈ X.L' := by
        rw [show (a : E) • x = a • x from algebraMap_smul E a x]
        exact X.L'.smul_mem a hx
      obtain ⟨k, hk⟩ := X.EF_int _ (X.NC_sub _ hax) _ (X.NC_sub _ hy)
      refine ⟨-k, ?_⟩
      unfold EFf at hk
      rw [herm_smul_left_eq_mul, herm_smul_right_fundamental_domains, herm_smul_left_eq_mul, hccNC] at hk
      have h2 : (X.NC : E) ^ 2 * X.ξ0 * ((a : E) * (c : E)) =
          -(-X.ξ0 * ((X.NC : E) * ((X.NC : E) * ((a : E) * herm X.Gm x y)))) := by
        rw [hce]
        ring
      rw [h2, map_neg, hk]
      push_cast
      ring
    | zero =>
      intro a
      exact ⟨0, by simp⟩
    | add c c' _ _ h1 h2 =>
      intro a
      obtain ⟨m1, hm1⟩ := h1 a
      obtain ⟨m2, hm2⟩ := h2 a
      refine ⟨m1 + m2, ?_⟩
      push_cast
      rw [mul_add, mul_add, map_add (f := _), hm1, hm2]
    | smul b c _ h =>
      intro a
      obtain ⟨m, hm⟩ := h (a * b)
      refine ⟨m, ?_⟩
      rw [← hm, smul_eq_mul]
      push_cast
      ring_nf
  obtain ⟨m, hm⟩ := hP c (by rw [hJtop]; exact Submodule.mem_top) 1
  refine ⟨m, ?_⟩
  rw [← hm]
  simp

theorem two_le_normSq_mul_rootDisc (hr : 0 < r) : 2 ≤ (X.NC : ℝ) ^ 2 * X.k0 * rdE E := by
  set n := finrank ℚ E with hn_def
  have hn : 0 < n := Module.finrank_pos
  have hNC : (0 : ℝ) < X.NC := Nat.cast_pos.mpr X.NC_pos
  have hx0 : ((X.NC : E) ^ 2 * X.ξ0) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr X.NC_pos.ne')) X.ξ0_ne
  have h1 := norm_mul_discr_ge hx0 (fun β => by
    obtain ⟨m, hm⟩ := trace_int X hr β
    exact ⟨m, hm⟩)
  have habs : ∀ σ : E →+* ℂ, ‖σ ((X.NC : E) ^ 2 * X.ξ0)‖ = (X.NC : ℝ) ^ 2 * (X.k0 / 2) := by
    intro σ
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast]
    congr 1
    by_cases hσ : σ ∈ X.Ψ
    · exact X.ξ0_abs ⟨σ, hσ⟩
    · have hc : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
        by_contra h'
        exact hσ ((X.cmType σ).mpr h')
      have h5 := X.ξ0_abs ⟨_, hc⟩
      simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at h5
      exact h5
  have h2 := abs_norm_eq_pow habs
  have h3 : (1 : ℝ) ≤ |((Algebra.norm ℚ ((X.NC : E) ^ 2 * X.ξ0) : ℚ) : ℝ)| * dE E := by
    unfold dE
    have h1' : ((1 : ℚ) : ℝ) ≤
        ((|Algebra.norm ℚ ((X.NC : E) ^ 2 * X.ξ0)| * |(NumberField.discr E : ℚ)| : ℚ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h1'
    exact h1'
  rw [h2] at h3
  have ha : 0 < (X.NC : ℝ) ^ 2 * (X.k0 / 2) := by
    have := X.minWeight_pos
    positivity
  have hd : 0 ≤ dE E := abs_nonneg _
  have h4 : 1 ≤ (((X.NC : ℝ) ^ 2 * (X.k0 / 2)) ^ n * dE E) ^ (1 / (n : ℝ)) :=
    Real.one_le_rpow h3 (by positivity)
  rw [Real.mul_rpow (by positivity) hd, ← Real.rpow_natCast, ← Real.rpow_mul ha.le,
    mul_one_div_cancel (by positivity), Real.rpow_one] at h4
  unfold rdE
  rw [← hn_def]
  nlinarith [h4]

end data

end DiscriminantTraceBounds

end ReciprocityTheory.ChartRestriction.G.FD
end

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace DiscreteLatticeMinimum

open NumberField Complex Module RealTangentSpace
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Y : DataX E r}
  (z : Frame Y.Ψ r) (ξ : Fin r → E) [hz : Fact (z ∈ Y.dom)]

noncomputable def Bmap : VT (X := Y.toData) z ξ →ₗ[ℝ] VT (X := Y.toData) z ξ where
  toFun u := VT.mk (MajorantOperators.Bop z u.val) (MajorantOperators.Bop_mem hz.out u.val_mem)
  map_add' u v := VT.ext (by simp [MajorantOperators.Bop_add])
  map_smul' c u := VT.ext (by simp [MajorantOperators.Bop_smul])

theorem Bmap_val (u : VT (X := Y.toData) z ξ) : (Bmap z ξ u).val = MajorantOperators.Bop z u.val := rfl

theorem Bmap_Bmap (u : VT (X := Y.toData) z ξ) : Bmap z ξ (Bmap z ξ u) = (-(Y.k0 ^ 2)) • u := by
  apply VT.ext
  rw [Bmap_val, Bmap_val, MajorantOperators.Bop_Bop hz.out]
  rfl

theorem inner_Bmap_right (u v : VT (X := Y.toData) z ξ) :
    inner ℝ u (Bmap z ξ v) = -inner ℝ (Bmap z ξ u) v := by
  rw [inner_eq, inner_eq, Bmap_val, Bmap_val, MajorantOperators.gI_Bop_right hz.out]

theorem norm_Bmap (u : VT (X := Y.toData) z ξ) : ‖Bmap z ξ u‖ = Y.k0 * ‖u‖ := by
  have h : ‖Bmap z ξ u‖ ^ 2 = (Y.k0 * ‖u‖) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, mul_pow, ← real_inner_self_eq_norm_sq, inner_eq, inner_eq,
      Bmap_val, MajorantOperators.gI_Bop_self hz.out]
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg Y.minWeight_pos.le (norm_nonneg _))
    two_ne_zero).1 h

theorem Bmap_injective : Function.Injective (Bmap z ξ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have h := norm_Bmap z ξ u
  rw [hu, norm_zero] at h
  have h2 : ‖u‖ = 0 := by
    rcases mul_eq_zero.1 h.symm with h3 | h3
    · exact absurd h3 Y.minWeight_pos.ne'
    · exact h3
  exact norm_eq_zero.1 h2

noncomputable def Bequiv : VT (X := Y.toData) z ξ ≃ₗ[ℝ] VT (X := Y.toData) z ξ :=
  LinearEquiv.ofBijective (Bmap z ξ) ⟨Bmap_injective z ξ,
    LinearMap.surjective_of_injective (Bmap_injective z ξ)⟩

variable {ξ} (hξ : Y.IsIso ξ)

theorem mem_Lat_of_int (hD3 : IntegerApproximationCount (E := E)) (y : VT (X := Y.toData) z ξ)
    (hy : ∀ a ∈ Lat z ξ hξ, ∃ m : ℤ, inner ℝ y (Bmap z ξ a) = m) : y ∈ Lat z ξ hξ := by
  classical
  have hval : ∀ ν : Y.Λp ξ, inner ℝ y (Bmap z ξ (phi z ξ hξ ν)) =
      (round (inner ℝ y (Bmap z ξ (phi z ξ hξ ν))) : ℝ) := by
    intro ν
    obtain ⟨m, hm⟩ := hy _ ((mem_Lat z ξ hξ).mpr ⟨ν, rfl⟩)
    rw [hm, round_intCast]
  let ψ : Y.Λp ξ →+ ℤ := AddMonoidHom.mk' (fun ν => round (inner ℝ y (Bmap z ξ (phi z ξ hξ ν))))
    (fun ν ν' => by
      obtain ⟨m1, hm1⟩ := hy _ ((mem_Lat z ξ hξ).mpr ⟨ν, rfl⟩)
      obtain ⟨m2, hm2⟩ := hy _ ((mem_Lat z ξ hξ).mpr ⟨ν', rfl⟩)
      show round _ = round _ + round _
      rw [map_add (f := _), map_add (f := _), inner_add_right, hm1, hm2, ← Int.cast_add, round_intCast, round_intCast,
        round_intCast])
  have hψ : ∀ ν, (ψ ν : ℝ) = inner ℝ y (Bmap z ξ (phi z ξ hξ ν)) := fun ν => (hval ν).symm
  have hvan : ∀ ν : Y.Λp ξ, (∃ e : E, (ν : Fin r → E) = e • ξ) → ψ ν = 0 := by
    rintro ν ⟨e, he⟩
    have h0 : phi z ξ hξ ν = 0 := VT.ext (by rw [phi_val, he, ucomp_line z ξ hξ e]; rfl)
    have := hψ ν
    rw [h0, map_zero, inner_zero_right] at this
    exact_mod_cast this
  obtain ⟨μ, hμ⟩ := (hermitian_dual_lattice_identity r Y ξ hξ).1 ψ hvan
  have hEF : ∀ ν : Y.Λp ξ,
      inner ℝ (Bmap z ξ y + Bmap z ξ (phi z ξ hξ μ)) (phi z ξ hξ ν) = 0 := by
    intro ν
    have h1 := hμ ν
    have h2 : ((EFf Y.ξ0 Y.Gm μ ν : ℚ) : ℝ) =
        inner ℝ (Bmap z ξ (phi z ξ hξ μ)) (phi z ξ hξ ν) := by
      rw [inner_eq, Bmap_val, phi_val, phi_val]
      exact MajorantOperators.EF_eq hz.out hξ.2.1 (LatticeSpanMembership.mem_Λp_iff.mp μ.2).2
        (LatticeSpanMembership.mem_Λp_iff.mp ν.2).2
    have h3 : (ψ ν : ℝ) = ((EFf Y.ξ0 Y.Gm μ ν : ℚ) : ℝ) := by exact_mod_cast h1
    rw [hψ, inner_Bmap_right, h2] at h3
    rw [inner_add_left]
    linarith
  set w := Bmap z ξ y + Bmap z ξ (phi z ξ hξ μ) with hw
  have hwall : ∀ a ∈ Submodule.span ℝ (Lat z ξ hξ : Set (VT (X := Y.toData) z ξ)),
      inner ℝ w a = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨ν, rfl⟩ := (mem_Lat z ξ hξ).mp ha
      exact hEF ν
    | zero => exact inner_zero_right _
    | add a b _ _ iha ihb => rw [inner_add_right, iha, ihb, add_zero]
    | smul c a _ iha => rw [inner_smul_right, iha, mul_zero]
  have hw0 : w = 0 := by
    have := hwall w (by rw [span_Lat z ξ hD3 hξ]; exact Submodule.mem_top)
    exact inner_self_eq_zero.mp this
  have hy0 : y + phi z ξ hξ μ = 0 := by
    apply Bmap_injective z ξ
    rw [map_add (f := _), ← hw, hw0, map_zero]
  have : y = phi z ξ hξ (-μ) := by
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_left hy0
  rw [this]
  exact (mem_Lat z ξ hξ).mpr ⟨-μ, rfl⟩

section lattice

variable (ep0 : ℝ) (hns : ∀ x ∈ Y.L', herm Y.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : Y.Ψ, ep0 ≤ Y.maj z τ (Y.ucomp z ξ (Y.embV x) τ))

include hns in
theorem min_norm (a : VT (X := Y.toData) z ξ) (ha : a ∈ Lat z ξ hξ) (ha0 : a ≠ 0) :
    Real.sqrt ep0 / Y.NA ≤ ‖a‖ := by
  obtain ⟨μ, rfl⟩ := (mem_Lat z ξ hξ).mp ha
  have hμ := LatticeSpanMembership.mem_Λp_iff.mp μ.2
  have hNA : (Y.NA : E) ≠ 0 := by exact_mod_cast Y.NA_pos.ne'
  have hNAr : (0 : ℝ) < Y.NA := by exact_mod_cast Y.NA_pos
  obtain ⟨τ, hτ⟩ := hns ((Y.NA : E) • (μ : Fin r → E)) (Y.NA_sub _ hμ.1)
    (by rw [HermitianTraceFormVanishing.herm_smul_left, hμ.2, mul_zero])
    (by
      intro e he
      apply ha0
      have hμe : (μ : Fin r → E) = ((Y.NA : E)⁻¹ * e) • ξ := by
        rw [mul_smul, ← he, smul_smul, inv_mul_cancel₀ hNA, one_smul]
      exact VT.ext (by rw [phi_val, hμe, ucomp_line z ξ hξ]; rfl))
  have hemb : Y.embV ((Y.NA : E) • (μ : Fin r → E)) = (Y.NA : ℝ) • Y.embV μ := by
    funext τ' b
    simp [Data.embV, Data.emb]
  rw [hemb, ucomp_smul, Pi.smul_apply, ← Complex.coe_smul, UnipotentCoefficientShift.maj_smul hz.out] at hτ
  have h2 := maj_le_norm_sq z ξ (phi z ξ hξ μ) τ
  rw [phi_val] at h2
  have h3 : ep0 ≤ (Y.NA * ‖phi z ξ hξ μ‖) ^ 2 := by
    rw [mul_pow]
    exact le_trans hτ (mul_le_mul_of_nonneg_left h2 (by positivity))
  have h4 := Real.sqrt_le_sqrt h3
  rw [Real.sqrt_sq (by positivity)] at h4
  rw [div_le_iff₀ hNAr]
  linarith

include hns in
theorem discrete_Lat (hep : 0 < ep0) : DiscreteTopology (Lat z ξ hξ) := by
  apply discreteTopology_of_isOpen_singleton_zero
  have hε : 0 < Real.sqrt ep0 / Y.NA :=
    div_pos (Real.sqrt_pos.mpr hep) (by exact_mod_cast Y.NA_pos)
  have hset : ({0} : Set (Lat z ξ hξ)) =
      Subtype.val ⁻¹' Metric.ball (0 : VT (X := Y.toData) z ξ) (Real.sqrt ep0 / Y.NA) := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro rfl
      simpa using hε
    · intro hx
      by_contra hne
      have := min_norm z hξ ep0 hns x.1 x.2 (fun h => hne (Subtype.ext h))
      linarith
  rw [hset]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

include hns in
theorem short_basis (hD3 : IntegerApproximationCount (E := E)) (hep : 0 < ep0) :
    ∃ y : Fin (finrank ℝ (VT (X := Y.toData) z ξ)) → VT (X := Y.toData) z ξ,
      LinearIndependent ℝ y ∧ (∀ i, y i ∈ Lat z ξ hξ) ∧
      ∀ i, ‖y i‖ ≤ (finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 2 /
        (Y.k0 * Real.sqrt ep0 / Y.NA) := by
  classical
  have := discrete_Lat z hξ ep0 hns hep
  have : IsZLattice ℝ (Lat z ξ hξ) := ⟨span_Lat z ξ hD3 hξ⟩
  have := ZLattice.module_free ℝ (Lat z ξ hξ)
  have := ZLattice.module_finite ℝ (Lat z ξ hξ)
  set n := finrank ℝ (VT (X := Y.toData) z ξ) with hn
  let bZ := Module.Free.chooseBasis ℤ (Lat z ξ hξ)
  let bR := bZ.ofZLatticeBasis ℝ (Lat z ξ hξ)
  have hspanR : Submodule.span ℤ (Set.range bR) = Lat z ξ hξ := bZ.ofZLatticeBasis_span ℝ _
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (Lat z ξ hξ)) = n :=
    (Module.finrank_eq_card_basis bR).symm
  let bF := bR.reindex (Fintype.equivFinOfCardEq hcard)
  have hspanF : Submodule.span ℤ (Set.range bF) = Lat z ξ hξ := by
    rw [Basis.range_reindex]
    exact hspanR
  let e := (stdOrthonormalBasis ℝ (VT (X := Y.toData) z ξ)).repr
  let b' := (bF.map (Bequiv z ξ)).map e.toLinearEquiv
  have hb'j : ∀ j, b' j = e (Bmap z ξ (bF j)) := fun j => by
    simp only [b', Basis.map_apply]
    rfl
  set lam := Y.k0 * Real.sqrt ep0 / Y.NA with hlam
  have hlam0 : 0 < lam := by
    have h1 := Y.minWeight_pos
    have h2 : (0 : ℝ) < Y.NA := by exact_mod_cast Y.NA_pos
    have h3 := Real.sqrt_pos.mpr hep
    positivity
  let f : VT (X := Y.toData) z ξ →ₗ[ℤ] EuclideanSpace ℝ (Fin n) :=
    ((e.toLinearEquiv.toLinearMap).comp (Bmap z ξ)).restrictScalars ℤ
  have hfr : f '' Set.range bF = Set.range b' := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun j => (hb'j j).symm)
  have hmin : ∀ x ∈ Submodule.span ℤ (Set.range b'), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    rw [← hfr, Submodule.span_image, hspanF] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hx0 (map_zero f)
    have hfa : ‖f a‖ = Y.k0 * ‖a‖ := by
      show ‖e (Bmap z ξ a)‖ = _
      rw [LinearIsometryEquiv.norm_map, norm_Bmap]
    rw [hfa, hlam, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (min_norm z hξ ep0 hns a ha ha0) Y.minWeight_pos.le
  obtain ⟨y, hli, hint, hnorm⟩ := T0.transference_dual b' lam hlam0 hmin
  refine ⟨fun i => e.symm (y i), ?_, ?_, ?_⟩
  · exact hli.map' e.symm.toLinearEquiv.toLinearMap e.symm.toLinearEquiv.ker
  · intro i
    apply mem_Lat_of_int z hξ hD3
    intro a ha
    rw [← hspanF] at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      obtain ⟨m, hm⟩ := hint i j
      refine ⟨m, ?_⟩
      rw [← hm, hb'j, ← LinearIsometryEquiv.inner_map_map e, LinearIsometryEquiv.apply_symm_apply]
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ iha ihb =>
      obtain ⟨m1, h1⟩ := iha
      obtain ⟨m2, h2⟩ := ihb
      exact ⟨m1 + m2, by rw [map_add (f := _), inner_add_right, h1, h2, Int.cast_add]⟩
    | smul c a _ iha =>
      obtain ⟨m, h⟩ := iha
      refine ⟨c * m, ?_⟩
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, h, Int.cast_mul]
  · intro i
    rw [LinearIsometryEquiv.norm_map]
    exact hnorm i


include hns in
theorem covering (hD3 : IntegerApproximationCount (E := E)) (hep : 0 < ep0) (d : VT (X := Y.toData) z ξ) :
    ∃ μ : Y.Λp ξ, ‖d - phi z ξ hξ μ‖ ≤ (finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 3 * Y.NA /
      (2 * Y.k0 * Real.sqrt ep0) := by
  classical
  rcases Nat.eq_zero_or_pos (finrank ℝ (VT (X := Y.toData) z ξ)) with h0 | hpos
  · have hsub : Subsingleton (VT (X := Y.toData) z ξ) := Module.finrank_zero_iff.mp h0
    refine ⟨0, ?_⟩
    rw [Subsingleton.elim (d - phi z ξ hξ 0) 0, norm_zero, h0]
    simp
  have : Nonempty (Fin (finrank ℝ (VT (X := Y.toData) z ξ))) := ⟨⟨0, hpos⟩⟩
  obtain ⟨y, hli, hyL, hyn⟩ := short_basis z hξ ep0 hns hD3 hep
  let yb := Basis.mk hli (hli.span_eq_top_of_card_eq_finrank (by simp)).ge
  have hyb : ∀ i, yb i = y i := fun i => Basis.mk_apply _ _ _
  set c := yb.repr d with hc
  set p : VT (X := Y.toData) z ξ := ∑ i, (round (c i) : ℤ) • y i with hp
  have hpL : p ∈ Lat z ξ hξ :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hyL i)
  obtain ⟨μ, hμ⟩ := (mem_Lat z ξ hξ).mp hpL
  refine ⟨μ, ?_⟩
  rw [hμ]
  have hd : d = ∑ i, c i • y i := by
    conv_lhs => rw [← yb.sum_repr d]
    simp only [hyb, hc]
  have hdiff : d - p = ∑ i, (c i - round (c i)) • y i := by
    rw [hd, hp, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_smul, ← Int.cast_smul_eq_zsmul ℝ]
  rw [hdiff]
  have hlam0 : 0 < Y.k0 * Real.sqrt ep0 / Y.NA := by
    have h1 := Y.minWeight_pos
    have h2 : (0 : ℝ) < Y.NA := by exact_mod_cast Y.NA_pos
    have h3 := Real.sqrt_pos.mpr hep
    positivity
  calc ‖∑ i, (c i - round (c i)) • y i‖ ≤ ∑ i, ‖(c i - round (c i)) • y i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (finrank ℝ (VT (X := Y.toData) z ξ)), (1 / 2) *
        ((finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 2 / (Y.k0 * Real.sqrt ep0 / Y.NA)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (abs_sub_round _) (hyn i) (norm_nonneg _) (by norm_num)
    _ = (finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 3 * Y.NA / (2 * Y.k0 * Real.sqrt ep0) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h1 := Y.minWeight_pos.ne'
        have h2 : (Y.NA : ℝ) ≠ 0 := by exact_mod_cast Y.NA_pos.ne'
        have h3 := (Real.sqrt_pos.mpr hep).ne'
        field_simp

end lattice

end DiscreteLatticeMinimum

end ReciprocityTheory.ChartRestriction.G.FD
