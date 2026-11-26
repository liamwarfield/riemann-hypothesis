module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricOnSet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFibrewiseNonvanishingThetaSectionOfSmoothMode

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

section ConeFacts

variable {X : Type} [AddCommGroup X]

theorem apply_eq_of_toReal_eq {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {c : Fin m → ℝ}
    {β : LinearMap.BilinForm ℤ X} (h : toReal β = ∑ i, c i • toReal (γ i)) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    (ℓ β : ℝ) = ∑ i, c i * ℓ (γ i) := by
  have h0 : ∑ i : Fin (m + 1), (Fin.cons (-1) c : Fin (m + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β γ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, LinearMap.id_apply, neg_one_smul, ← h, neg_add_cancel]
  have key := sum_mul_eq_zero_of_sum_toReal (fun _ _ hab => hab) ℓ h0
  rw [Fin.sum_univ_succ] at key
  simp only [Fin.cons_zero, Fin.cons_succ] at key
  linarith

theorem InRCone.apply_nonneg {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X}
    (h : InRCone γ β) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (hℓ : ∀ i, 0 ≤ ℓ (γ i)) : 0 ≤ ℓ β := by
  obtain ⟨c, hc, hβ⟩ := h
  have e := apply_eq_of_toReal_eq hβ ℓ
  have hr : (0 : ℝ) ≤ ℓ β := by
    rw [e]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (by exact_mod_cast hℓ i)
  exact_mod_cast hr

theorem inRCone_trans {m n : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {δ : Fin n → LinearMap.BilinForm ℤ X}
    (hδ : ∀ j, InRCone γ (δ j)) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone δ β) : InRCone γ β := by
  choose a ha hδe using hδ
  obtain ⟨b, hb, hβe⟩ := hβ
  refine ⟨fun i => ∑ j, b j * a j i, fun i => Finset.sum_nonneg fun j _ => mul_nonneg (hb j) (ha j i), ?_⟩
  rw [hβe]
  simp only [hδe, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

theorem eq_zero_of_toReal_rel {a b : ℕ} {u : Fin a → LinearMap.BilinForm ℤ X} {v : Fin b → LinearMap.BilinForm ℤ X}
    (hind : ∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0)
    {r : Fin a → ℝ} {s : Fin b → ℝ} (h : ∑ j, r j • toReal (u j) = ∑ k, s k • toReal (v k)) : r = 0 := by

  have hpt : ∀ x y : X, ∑ j, r j * (u j x y : ℝ) = ∑ k, s k * (v k x y : ℝ) := by
    intro x y
    have hxy := congrArg (fun B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ => B x y) h
    simpa [LinearMap.sum_apply, toReal_apply] using hxy

  suffices hf : ∀ (f : Module.Dual ℚ ℝ) (j : Fin a), f (r j) = 0 by
    funext j
    exact (Module.forall_dual_apply_eq_zero_iff ℚ (r j)).mp fun f => hf f j
  intro f
  have e : ∀ (t : ℝ) (n : ℤ), f (t * n) = n * f t := by
    intro t n
    rw [mul_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
  have hq : ∀ x y : X, ∑ j, ((u j x y : ℤ) : ℚ) * f (r j) = ∑ k, ((v k x y : ℤ) : ℚ) * f (s k) := by
    intro x y
    have hxy := congrArg f (hpt x y)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum] at hxy
    simpa only [e] using hxy

  let N : ℕ := (∏ j, (f (r j)).den) * ∏ k, (f (s k)).den
  have hN : (N : ℚ) ≠ 0 := by
    have : N ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => (f (r j)).den_nz)
      (Finset.prod_ne_zero_iff.mpr fun k _ => (f (s k)).den_nz)
    exact_mod_cast this
  have key : ∀ q : ℚ, q.den ∣ N → ((((N / q.den : ℕ) : ℤ) * q.num : ℤ) : ℚ) = N * q := by
    intro q hq'
    have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div hq' hd]
    rw [div_mul_eq_mul_div, mul_div_assoc, Rat.num_div_den]
  have hdr : ∀ j, (f (r j)).den ∣ N := fun j =>
    dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) _
  have hds : ∀ k, (f (s k)).den ∣ N := fun k =>
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) _
  let c : Fin a → ℤ := fun j => ((N / (f (r j)).den : ℕ) : ℤ) * (f (r j)).num
  let d : Fin b → ℤ := fun k => ((N / (f (s k)).den : ℕ) : ℤ) * (f (s k)).num
  have hc : ∀ j, (c j : ℚ) = N * f (r j) := fun j => key _ (hdr j)
  have hd : ∀ k, (d k : ℚ) = N * f (s k) := fun k => key _ (hds k)
  have hrel : ∑ j, c j • u j = ∑ k, d k • v k := by
    ext x y
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Int.cast_injective (α := ℚ)
    push_cast
    simp only [hc, hd]
    have := hq x y
    calc ∑ j, (N : ℚ) * f (r j) * (u j x y : ℚ) = N * ∑ j, ((u j x y : ℤ) : ℚ) * f (r j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = N * ∑ k, ((v k x y : ℤ) : ℚ) * f (s k) := by rw [this]
      _ = ∑ k, (N : ℚ) * f (s k) * (v k x y : ℚ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have h0 := hind d c hrel
  intro j
  have hcj : (c j : ℚ) = 0 := by rw [h0]; simp
  rw [hc j] at hcj
  have : (f (r j) : ℚ) = 0 := (mul_eq_zero.mp hcj).resolve_left hN
  exact_mod_cast this

end ConeFacts

section CellFacts

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem IsCell.reindex {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (h : IsCell bar φ γ) (e : Fin m' ≃ Fin m) :
    IsCell bar φ fun i => γ (e i) := by
  obtain ⟨hmem, hnn, hlin, hstr⟩ := h
  refine ⟨fun i => hmem (e i), fun i y => hnn (e i) y, ?_, ?_⟩
  · intro c hc
    convert hlin (fun i => c (e.symm i)) (fun i => hc _) using 1
    · congr 1
      funext x y
      exact Fintype.sum_equiv e _ _ (fun i => by simp)
    · exact Fintype.sum_equiv e _ _ (fun i => by simp)
  · obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hstr
    refine ⟨N, ℓ, hN, fun i => h1 (e i), h2, ?_⟩
    intro β hβ hβn heq
    obtain ⟨k, c, hk, hkc⟩ := h3 β hβ hβn heq
    refine ⟨k, fun i => c (e i), hk, ?_⟩
    rw [hkc]
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm

end CellFacts

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolCell

namespace GlobalTheory.PolFan

section Depth

variable {O : Type} [CommRing O] (bar : O → O) (ψ w : InvFun O)

def IsStarDepth {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (t : ℝ) : Prop :=
  0 ≤ t ∧ ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
    v ∈ balForms bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v ∧ B ∈ rcone γ ∧ B - t • toReal v ∈ rcone γ

def depthSet (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : Set ℝ :=
  {t | ∃ (X₁ : Type) (_ : AddCommGroup X₁) (_ : Module O X₁) (_ : Module.Finite O X₁) (r : (Fin n → O) →ₗ[O] X₁)
    (B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ), Function.Surjective r ∧ (∀ x, (∀ y, B₁ x y = 0) → x = 0) ∧
    (∀ a b, B a b = B₁ (r a) (r b)) ∧ IsStarDepth bar ψ w B₁ t}

variable {bar ψ w}

theorem depthSet_comp {n m : ℕ} {r : (Fin n → O) →ₗ[O] (Fin m → O)} (hr : Function.Surjective r)
    (B : (Fin m → O) → (Fin m → O) → ℝ) : depthSet bar ψ w n (fun a b => B (r a) (r b)) = depthSet bar ψ w m B := by
  ext t
  constructor
  · rintro ⟨X₁, i1, i2, i3, ρ, B₁, hρ, hrad, hB, hd⟩
    have hker : LinearMap.ker r ≤ LinearMap.ker ρ := by
      intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      refine hrad _ fun y => ?_
      obtain ⟨y', rfl⟩ := hρ y
      have h1 := hB x y'
      have h2 := hB 0 y'
      simp only [hx, map_zero, LinearMap.zero_apply] at h1 h2
      rw [← h1, h2]
    let ρ' : (Fin m → O) →ₗ[O] X₁ :=
      (LinearMap.ker r).liftQ ρ hker ∘ₗ (r.quotKerEquivOfSurjective hr).symm.toLinearMap
    have hρ' : ∀ a, ρ' (r a) = ρ a := fun a => by
      have : (r.quotKerEquivOfSurjective hr).symm (r a) = Submodule.Quotient.mk a := by
        rw [LinearEquiv.symm_apply_eq]; rfl
      simp only [ρ', LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
    refine ⟨X₁, i1, i2, i3, ρ', B₁, fun x => ?_, hrad, fun a b => ?_, hd⟩
    · obtain ⟨a, rfl⟩ := hρ x
      exact ⟨r a, hρ' a⟩
    · obtain ⟨a, rfl⟩ := hr a
      obtain ⟨b, rfl⟩ := hr b
      rw [hρ', hρ']
      exact hB a b
  · rintro ⟨X₁, i1, i2, i3, ρ, B₁, hρ, hrad, hB, hd⟩
    exact ⟨X₁, i1, i2, i3, ρ ∘ₗ r, B₁, hρ.comp hr, hrad, fun a b => hB (r a) (r b), hd⟩

theorem depthSet_zero (B : (Fin 0 → O) → (Fin 0 → O) → ℝ) : depthSet bar ψ w 0 B = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun t ⟨X₁, i1, i2, i3, ρ, B₁, hρ, _, _, _, _, _, v, _, _, _, hv, _⟩ => ?_
  haveI : Subsingleton X₁ := ⟨fun x y => by
    obtain ⟨a, rfl⟩ := hρ x
    obtain ⟨b, rfl⟩ := hρ y
    rw [Subsingleton.elim a b]⟩
  rw [InvFun.evalZ, w.eval_of_subsingleton] at hv
  exact zero_ne_one hv

variable (bar ψ w)

def starDepth : InvFun O where
  toFun n B := sSup (depthSet bar ψ w n B)
  inv n m r hr B := by rw [depthSet_comp hr]
  zero B := by rw [depthSet_zero, Real.sSup_empty]

def starFun (K D : ℕ) : InvFun O where
  toFun n B := D * (K * ψ.toFun n B + (starDepth bar ψ w).toFun n B)
  inv n m r hr B := by simp only [InvFun.inv _ _ _ r hr]
  zero B := by simp only [InvFun.zero, mul_zero, add_zero]

variable {bar ψ w}

theorem starDepth_toFun_nonneg (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : 0 ≤ (starDepth bar ψ w).toFun n B :=
  Real.sSup_nonneg fun _ h => h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1

theorem starDepth_eval_nonneg {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X → X → ℝ) :
    0 ≤ (starDepth bar ψ w).eval X B := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.eval_eq _ hr]
  exact starDepth_toFun_nonneg n _

theorem starFun_eval {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (K D : ℕ) (B : X → X → ℝ) :
    (starFun bar ψ w K D).eval X B = D * (K * ψ.eval X B + (starDepth bar ψ w).eval X B) := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.eval_eq _ hr, InvFun.eval_eq _ hr, InvFun.eval_eq _ hr]
  rfl

theorem starFun_evalZ {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (K D : ℕ)
    (β : LinearMap.BilinForm ℤ X) :
    (starFun bar ψ w K D).evalZ β = D * (K * ψ.evalZ β + (starDepth bar ψ w).evalZ β) :=
  starFun_eval K D _

theorem starFun_evalR {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (K D : ℕ)
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalR (starFun bar ψ w K D) B = D * (K * evalR ψ B + evalR (starDepth bar ψ w) B) :=
  starFun_eval K D _

theorem starDepth_zeroFun (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : (starDepth bar ψ (zeroFun O)).toFun n B = 0 := by
  have : depthSet bar ψ (zeroFun O) n B = ∅ :=
    Set.eq_empty_of_forall_notMem fun t ⟨X₁, i1, i2, i3, ρ, B₁, _, _, _, _, _, _, v, _, _, _, hv, _⟩ => by
      rw [zeroFun_evalZ] at hv
      exact zero_ne_one hv
  show sSup _ = 0
  rw [this, Real.sSup_empty]

end Depth

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem isTwInv_starFun {ψ w : InvFun (𝓞 E)} (hψ : IsTwInv H ψ) (hd : IsTwInv H (starDepth H.bar ψ w)) (K D : ℕ) :
    IsTwInv H (starFun H.bar ψ w K D) := fun σ hσ n B => by
  show _ * (_ * _ + _) = _ * (_ * _ + _)
  rw [hψ σ hσ n B, hd σ hσ n B]

end Twist

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LieBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open Classical in
def pointPoly (H : Host E) (Dw : Datum H) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ :=
  ∏ τ : GlobalTheory.AllWt.Psi H, (C ((-1 : ℝ) ^ Dw.mult τ.1) * X (τ.1, Dw.mult τ.1)) ^ (Dw.p + Dw.q - Dw.mult τ.1)

end GlobalTheory.LieBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Round

variable {O : Type} [CommRing O] (bar : O → O)

def IsMultCell (φ : InvFun O) (M : ℕ) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∃ h : IsCell bar φ δ, LinearIndependent ℤ δ ∧ (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) ∧
    cellMult bar (fun i => (⟨δ i, h.mem i⟩ : balForms bar X)) = M


variable (O) in
structure FormFamily : Type 1 where

  X : Type
  [acg : AddCommGroup X]
  [mod : Module O X]

  m : ℕ

  δ : Fin m → LinearMap.BilinForm ℤ X

attribute [instance] FormFamily.acg FormFamily.mod

variable {bar}

def FormFamily.Carries (c : FormFamily O) {X : Type} [AddCommGroup X] [Module O X] {m : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∃ (e : X ≃ₗ[O] c.X) (s : Fin m ≃ Fin c.m), ∀ i, δ i = pull e.toLinearMap (c.δ (s i))


variable (bar) in
def MultCellsAmong (q : ℕ) (φ : InvFun O) (M n : ℕ) : Prop :=
  ∃ R : Fin n → FormFamily O, ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
    Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar φ M δ → ∃ k, (R k).Carries δ

end Round

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteTypesViaFullHeckeAlgebraEigensystems
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteTypesViaFullHeckeAlgebraEigensystems
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3

theorem finiteTypes_of_full_heckeAlgebra_eigensystems : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → Formalism.BasicNotions.Rows.IsotRank D.what₂ → Lam3 Z := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hHost hIR
  have lab := GlobalTheory.T.exists_familyLabel_containing_finiteTypeParts h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  let cOf : D.what₂.FT → A3.fam3.base3.Ix := fun σ => (lab σ).choose
  have hc : ∀ σ, HasLab Y σ (cOf σ) := fun σ => (lab σ).choose_spec
  have rat := GlobalTheory.T.complexSpan_rationalLiftForms_eq_basePart h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  have ind := GlobalTheory.T.iSupIndep_finiteTypeComponents_thetaLiftForms h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  have dim := GlobalTheory.T.liftLabelPart_finrank_eq_rowsPart_finrank h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  have cnt := GlobalTheory.T.card_baseRows_label_eq_rowsPart_finrank h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost cOf hc
  have lam := GlobalTheory.T.liftScalar_eq_labelScalar h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  refine ⟨cOf, fun i c => ?_, fun i t σ ht hne => lam σ (cOf σ) i t (hc σ) ht hne, fun c => cnt c⟩
  have hind : iSupIndep (fun σ : {σ : D.what₂.FT // cOf σ = c} => D.what₂.isot ((i : ℕ) + 1) σ.1) :=
    (ind i).comp Subtype.val_injective
  refine ⟨hind, ?_⟩
  rw [rat i c]
  have hle : (⨆ σ : {σ : D.what₂.FT // cOf σ = c}, D.what₂.isot ((i : ℕ) + 1) σ.1) ≤ (R.Wp3 i c).comap (Y.mj.eW i) := by
    refine iSup_le fun σ => ?_
    have := (hc σ.1).1 i
    rw [σ.2] at this
    exact Submodule.map_le_iff_le_comap.1 this
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [dim i c, ← cnt c, Formalism.IndefR.Cx.finrank_iSup_eq_sum _ hind]
  rw [Finset.sum_subtype (Finset.univ.filter (fun σ => cOf σ = c)) (p := fun σ => cOf σ = c) (by simp)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  exact hIR ((i : ℕ) + 1) (by omega) (by omega) σ.1

end GlobalTheory.Mem.R3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteTypesViaFullHeckeAlgebraEigensystemsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteTypes_via_full_heckeAlgebra_eigensystems : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → Formalism.BasicNotions.Rows.IsotRank D.what₂ → Lam3 Z := by
  first | exact @GlobalTheory.Mem.R3.finiteTypes_of_full_heckeAlgebra_eigensystems | exact GlobalTheory.Mem.R3.finiteTypes_of_full_heckeAlgebra_eigensystems | (intros; apply GlobalTheory.Mem.R3.finiteTypes_of_full_heckeAlgebra_eigensystems <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPsiCoordinatesOfTauUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPsiCoordinatesOfTauUnits
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiFromTau

theorem exists_isTauCoord : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (a b : D.X),
    ∃ x, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b x := by
  intro R _ _ _ D a b
  have pick : ∀ (z : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A), ∃ i, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsIntChart D z i := by
    intro z
    have hc : z.left (closedPoint R) ∈ ⨆ i, D.P.L.U i := by
      rw [D.P.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    exact ⟨i, ((closedPoint_mem_iff (R := R) (z.left ⁻¹ᵁ D.P.L.U i)).1 hi).ge⟩
  obtain ⟨i1, h1⟩ := pick (D.c (a + b))
  obtain ⟨i2, h2⟩ := pick (D.c a)
  obtain ⟨i3, h3⟩ := pick (D.c b)
  obtain ⟨i4, h4⟩ := pick η[D.P.A]
  let j : ((PUnit ⊕ PUnit) ⊕ PUnit) ⊕ PUnit → D.P.L.ι := Sum.elim (Sum.elim (Sum.elim (fun _ => i1) (fun _ => i2)) (fun _ => i3)) (fun _ => i4)
  refine ⟨_, j, ?_, h1, h2, h3, h4, rfl⟩
  intro y _
  refine Set.mem_iInter.2 ?_
  rintro (((⟨⟩ | ⟨⟩) | ⟨⟩) | ⟨⟩)
  · exact h1 (Set.mem_univ (jK R y))
  · exact h2 (Set.mem_univ (jK R y))
  · exact h3 (Set.mem_univ (jK R y))
  · exact h4 (Set.mem_univ ((toUnit (TK R)).left y))

theorem associated_of_tau : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t)
    (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (g : R →+* W) (hg : Function.Injective g)
    (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') (ρ : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X),
    (∀ (a b : P.D.toPre.X) (x : (FractionRing R)ˣ) (x' : (FractionRing W)ˣ),
          GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P.D.toPre a b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P'.D.toPre (ρ a) (ρ b) x' →
          ∃ u : Wˣ, IsFractionRing.lift (A := R) (K := FractionRing R)
              (g := (algebraMap W (FractionRing W)).comp g) ((IsFractionRing.injective W (FractionRing W)).comp hg) (x : FractionRing R) =
            algebraMap W (FractionRing W) (u : W) * (x' : FractionRing W)) →
    ∀ (y : P.D.toPre.X) (r : R) (r' : W), PsiCoord P.D.toPre y r → PsiCoord P'.D.toPre (ρ y) r' → Associated (g r) r' := by
  intro E _ _ _ H R _ _ _ t P W _ _ _ g hg t' P' ρ hρ y r r' hr hr'
  letI := H.starRing
  obtain ⟨x, hx⟩ := exists_isTauCoord R P.D.toPre y (H.w0 • y)
  obtain ⟨x', hx'⟩ := exists_isTauCoord W P'.D.toPre (ρ y) (H.w0 • ρ y)
  have hx'' : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P'.D.toPre (ρ y) (ρ (H.w0 • y)) x' := by rwa [ρ.map_smul]
  obtain ⟨u, hu⟩ := hρ y (H.w0 • y) x x' hx hx''
  obtain ⟨u1, hu1⟩ := GlobalTheory.T.psiCoordinate_eq_unit_mul_tauCoordinate R P.D.toPre (𝓞 E) P.oD H.w0 P.w0 y r x hr hx
  obtain ⟨u2, hu2⟩ := GlobalTheory.T.psiCoordinate_eq_unit_mul_tauCoordinate W P'.D.toPre (𝓞 E) P'.oD H.w0 P'.w0 (ρ y) r' x' hr' hx'
  set φ := IsFractionRing.lift (A := R) (K := FractionRing R)
    (g := (algebraMap W (FractionRing W)).comp g) ((IsFractionRing.injective W (FractionRing W)).comp hg) with hφ
  have hφa : ∀ s : R, φ (algebraMap R (FractionRing R) s) = algebraMap W (FractionRing W) (g s) := fun s =>
    IsFractionRing.lift_algebraMap _ s
  have e1 := congrArg φ hu1
  rw [map_mul, hφa, hφa, hu] at e1
  let v : Wˣ := Units.map g.toMonoidHom u1 * u * u2⁻¹
  have key : g r = r' * (v : W) := by
    apply IsFractionRing.injective W (FractionRing W)
    have h2 : (x' : FractionRing W) = algebraMap W (FractionRing W) ((u2⁻¹ : Wˣ) : W) * algebraMap W (FractionRing W) r' := by
      rw [hu2, ← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]
    rw [e1, h2]
    simp only [v, Units.val_mul, map_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    ring
  exact Associated.symm ⟨v, key.symm⟩

end GlobalTheory.PsiFromTau
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPsiCoordinatesOfTauUnitsStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.associated_psi_coordinates_of_tau_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t)
    (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (g : R →+* W) (hg : Function.Injective g)
    (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') (ρ : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X),
    (∀ (a b : P.D.toPre.X) (x : (FractionRing R)ˣ) (x' : (FractionRing W)ˣ),
          GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P.D.toPre a b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P'.D.toPre (ρ a) (ρ b) x' →
          ∃ u : Wˣ, IsFractionRing.lift (A := R) (K := FractionRing R)
              (g := (algebraMap W (FractionRing W)).comp g) ((IsFractionRing.injective W (FractionRing W)).comp hg) (x : FractionRing R) =
            algebraMap W (FractionRing W) (u : W) * (x' : FractionRing W)) →
    ∀ (y : P.D.toPre.X) (r : R) (r' : W), PsiCoord P.D.toPre y r → PsiCoord P'.D.toPre (ρ y) r' → Associated (g r) r' := by
  first | exact @GlobalTheory.PsiFromTau.associated_of_tau | exact GlobalTheory.PsiFromTau.associated_of_tau | (intros; apply GlobalTheory.PsiFromTau.associated_of_tau <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

namespace CarDim

section Pull

variable {O : Type} [CommRing O] {bar : O → O} {ψ : InvFun O} {X X₁ : Type} [AddCommGroup X] [Module O X]
  [AddCommGroup X₁] [Module O X₁] {m : ℕ}

theorem isCell_pull_equiv [Module.Finite O X] [Module.Finite O X₁] {γ : Fin m → LinearMap.BilinForm ℤ X₁}
    (h : IsCell bar ψ γ) (e : X ≃ₗ[O] X₁) : IsCell bar ψ fun i => pull e.toLinearMap (γ i) :=
  ⟨fun i => pull_mem _ (h.mem i), fun i _ => h.nonneg i _, (linearOn_pull_iff e.surjective).2 h.linear,
    IsStrict.of_pull (r := e.symm.toLinearMap) e.symm.surjective (by simpa using h.strict)⟩

def pullLin (r : X →ₗ[O] X₁) : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun := pull r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem pullLin_apply (r : X →ₗ[O] X₁) (β : LinearMap.BilinForm ℤ X₁) : pullLin r β = pull r β := rfl

theorem pullLin_injective {r : X →ₗ[O] X₁} (hr : Function.Surjective r) : Function.Injective (pullLin r) :=
  fun β β' h => LinearMap.ext₂ fun a b => by
    obtain ⟨a, rfl⟩ := hr a
    obtain ⟨b, rfl⟩ := hr b
    exact LinearMap.congr_fun₂ h a b

theorem genRank_pull {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (γ : Fin m → LinearMap.BilinForm ℤ X₁) :
    genRank (fun i => pull r (γ i)) = genRank γ := by
  unfold genRank
  have e : Submodule.span ℤ (Set.range fun i => pull r (γ i)) = (Submodule.span ℤ (Set.range γ)).map (pullLin r) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [e]
  exact (Submodule.equivMapOfInjective _ (pullLin_injective hr) _).finrank_eq.symm

theorem inRCone_pull_iff {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {γ : Fin m → LinearMap.BilinForm ℤ X₁}
    {β : LinearMap.BilinForm ℤ X₁} : InRCone (fun i => pull r (γ i)) (pull r β) ↔ InRCone γ β := by
  refine exists_congr fun c => and_congr_right fun _ => ?_
  constructor
  · intro h
    refine LinearMap.ext₂ fun a b => ?_
    obtain ⟨a, rfl⟩ := hr a
    obtain ⟨b, rfl⟩ := hr b
    have := LinearMap.congr_fun₂ h a b
    simpa [LinearMap.sum_apply] using this
  · intro h
    refine LinearMap.ext₂ fun a b => ?_
    have := LinearMap.congr_fun₂ h (r a) (r b)
    simpa [LinearMap.sum_apply] using this

end Pull

section Rad

variable {O : Type} [CommRing O] {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]

def orad (β : LinearMap.BilinForm ℤ X) : Submodule O X where
  carrier := {x | ∀ (a : O) (y : X), β (a • x) y = 0}
  add_mem' := by
    intro x x' hx hx' a y
    rw [smul_add, map_add (f := _), LinearMap.add_apply, hx a y, hx' a y, add_zero]
  zero_mem' := by
    intro a y
    rw [smul_zero, map_zero, LinearMap.zero_apply]
  smul_mem' := by
    intro c x hx a y
    rw [smul_smul]
    exact hx _ y

theorem mem_orad {β : LinearMap.BilinForm ℤ X} {x : X} : x ∈ orad (O := O) β ↔ ∀ (a : O) (y : X), β (a • x) y = 0 :=
  Iff.rfl

theorem orad_pull {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (β : LinearMap.BilinForm ℤ X₁) :
    orad (pull r β) = (orad β).comap r := by
  ext x
  simp only [Submodule.mem_comap, mem_orad, pull_apply, map_smul]
  constructor
  · intro h a y
    obtain ⟨y, rfl⟩ := hr y
    exact h a y
  · intro h a y
    exact h a (r y)

def qEquiv {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (N : Submodule O X₁) : (X ⧸ N.comap r) ≃ₗ[O] (X₁ ⧸ N) :=
  (Submodule.quotEquivOfEq _ _ (by rw [LinearMap.ker_comp, Submodule.ker_mkQ])).trans
    ((N.mkQ ∘ₗ r).quotKerEquivOfSurjective (N.mkQ_surjective.comp hr))

end Rad

section Def

variable {O : Type} [CommRing O] (bar : O → O) (ψ : InvFun O)

def cdimSet (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (N : Submodule O X) (β : LinearMap.BilinForm ℤ X) :
    Set ℕ :=
  {k | ∃ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ (X ⧸ N)), IsCell bar ψ δ ∧ InRCone (fun i => pull N.mkQ (δ i)) β ∧
    genRank δ = k}

def cdimQ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (N : Submodule O X) (β : LinearMap.BilinForm ℤ X) : ℕ :=
  sInf (cdimSet bar ψ X N β)

variable {bar ψ}

theorem cdimSet_pull {X X₁ : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup X₁] [Module O X₁]
    [Module.Finite O X₁] {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (β : LinearMap.BilinForm ℤ X₁) :
    cdimSet bar ψ X (orad (pull r β)) (pull r β) = cdimSet bar ψ X₁ (orad β) β := by
  rw [orad_pull hr]
  set N := orad (O := O) β
  let e := qEquiv hr N
  have key : ∀ δ : LinearMap.BilinForm ℤ (X₁ ⧸ N),
      pull (N.comap r).mkQ (pull e.toLinearMap δ) = pull r (pull N.mkQ δ) := fun δ => rfl
  ext k
  constructor
  · rintro ⟨m, δ', h1, h2, rfl⟩
    refine ⟨m, fun i => pull e.symm.toLinearMap (δ' i), isCell_pull_equiv h1 e.symm, ?_,
      genRank_pull e.symm.surjective _⟩
    rw [← inRCone_pull_iff hr]
    convert h2 using 2 with i
    rw [← key, pull_pull_symm]
  · rintro ⟨m, δ, h1, h2, rfl⟩
    refine ⟨m, fun i => pull e.toLinearMap (δ i), isCell_pull_equiv h1 e, ?_, genRank_pull e.surjective _⟩
    simp only [key]
    exact (inRCone_pull_iff hr).2 h2

theorem zero_mem_cdimSet {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [Subsingleton X] (N : Submodule O X)
    (β : LinearMap.BilinForm ℤ X) : 0 ∈ cdimSet bar ψ X N β := by
  haveI : Subsingleton (X ⧸ N) := ⟨fun a b => by
    induction a using Submodule.Quotient.induction_on
    induction b using Submodule.Quotient.induction_on
    rename_i a b
    rw [Subsingleton.elim a b]⟩
  refine ⟨0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0, fun c _ => ?_, ?_⟩,
    ⟨Fin.elim0, fun i => i.elim0, ?_⟩, ?_⟩
  · rw [ψ.eval_of_subsingleton]
    simp
  · refine ⟨1, 0, one_pos, fun i => i.elim0, fun β' _ _ => ?_, fun β' _ _ _ => ⟨1, Fin.elim0, one_pos, ?_⟩⟩
    · simp [InvFun.evalZ, ψ.eval_of_subsingleton]
    · rw [Fin.sum_univ_zero, one_smul]
      exact LinearMap.ext₂ fun a b => by rw [Subsingleton.elim a 0]; simp
  · exact LinearMap.ext₂ fun a b => by rw [Subsingleton.elim a 0]; simp
  · simp [genRank]

end Def

section Fun

variable {O : Type} [CommRing O] (bar : O → O) (ψ : InvFun O)


open Classical in
def carFun : InvFun O where
  toFun n B := if h : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
      ∀ a b, B a b = β a b then (cdimQ bar ψ (Fin n → O) (orad h.choose) h.choose : ℝ) else 0
  inv n m r hr B := by
    obtain ⟨s, hs⟩ := Module.projective_lifting_property r LinearMap.id hr
    have hrs : ∀ a, r (s a) = a := fun a => LinearMap.congr_fun hs a
    by_cases h : ∃ β : LinearMap.BilinForm ℤ (Fin m → O), β ∈ balForms bar (Fin m → O) ∧ (∀ y, 0 ≤ β y y) ∧
        ∀ a b, B a b = β a b
    · have h' : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
          ∀ a b, B (r a) (r b) = β a b :=
        ⟨pull r h.choose, pull_mem r h.choose_spec.1, fun y => h.choose_spec.2.1 _, fun a b => h.choose_spec.2.2 _ _⟩
      rw [dite_eq_left h, dite_eq_left h']
      have e : h'.choose = pull r h.choose := LinearMap.ext₂ fun a b => by
        have h1 := h'.choose_spec.2.2 a b
        have h2 := h.choose_spec.2.2 (r a) (r b)
        rw [pull_apply]
        exact_mod_cast h1.symm.trans h2
      rw [e]
      unfold cdimQ
      rw [cdimSet_pull hr]
    · have h' : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
          ∀ a b, B (r a) (r b) = β a b := by
        rintro ⟨β, h1, h2, h3⟩
        exact h ⟨pull s β, pull_mem s h1, fun y => h2 _, fun a b => by rw [pull_apply, ← h3, hrs, hrs]⟩
      rw [dite_eq_right h, dite_eq_right h']
  zero B := by
    split_ifs with h
    · have := Nat.sInf_eq_zero.2 (Or.inl (zero_mem_cdimSet (bar := bar) (ψ := ψ) (orad h.choose) h.choose))
      unfold cdimQ
      rw [this, Nat.cast_zero]
    · rfl

variable {bar ψ}

theorem evalZ_carFun {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {β : LinearMap.BilinForm ℤ X}
    (hβ : β ∈ balForms bar X) (hp : ∀ y, 0 ≤ β y y) :
    (carFun bar ψ).evalZ β = cdimQ bar ψ X (orad β) β := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.evalZ, (carFun bar ψ).eval_eq hs]
  dsimp only [carFun]
  split_ifs with h
  · have e : h.choose = pull s β := LinearMap.ext₂ fun a b => by
      have := h.choose_spec.2.2 a b
      rw [pull_apply]
      exact_mod_cast this.symm
    rw [e]
    unfold cdimQ
    rw [cdimSet_pull hs]
  · exact absurd ⟨pull s β, pull_mem s hβ, fun y => hp _, fun a b => rfl⟩ h

end Fun

end CarDim

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntBilinFormToRealMemBalancedPsdCone
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntBilinFormToRealMemBalancedPsdCone
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem toReal_mem_psdCone_of_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type)
    [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
    (β : LinearMap.BilinForm ℤ X), β ∈ balForms H.bar X → (∀ y, 0 ≤ β y y) → toReal β ∈ psdCone (bar := H.bar) (X := X) := by
  intro E _ _ _ H X _ _ _ _ β hβ hp
  have h := ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 (fun _ => β) (fun _ => 1)
    (fun _ => hβ) (fun _ y => hp y) (fun _ => zero_le_one)
  simpa using h

end GlobalTheory.PolFan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntBilinFormToRealMemBalancedPsdConeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intBilinFormToReal_mem_balancedPsdCone : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (β : LinearMap.BilinForm ℤ X), β ∈ balForms H.bar X → (∀ y, 0 ≤ β y y) → toReal β ∈ psdCone (bar := H.bar) (X := X) := by
  first | exact @GlobalTheory.PolFan.toReal_mem_psdCone_of_nonneg | exact GlobalTheory.PolFan.toReal_mem_psdCone_of_nonneg | (intros; apply GlobalTheory.PolFan.toReal_mem_psdCone_of_nonneg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDerivChernConnectionInverseSymmetricG
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDerivChernConnectionInverseSymmetricG
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.HermFrame

open Filter

theorem del_del_comm {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {u : E → ℂ} {z : E} (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    GlobalTheory.del (fun x => GlobalTheory.del u x w) z v = GlobalTheory.del (fun x => GlobalTheory.del u x v) z w := by
  have h := GlobalTheory.differentiableAt_fderiv_of_contDiffAt_two hu
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have e : ∀ w, (fun x => GlobalTheory.del u x w) =
      fun x => (1 / 2 : ℂ) • (fderiv ℝ u x w - Complex.I • fderiv ℝ u x (Complex.I • w)) :=
    fun w => funext fun x => GlobalTheory.del_apply u x w
  have d : ∀ w, GlobalTheory.del (fun x => (1 / 2 : ℂ) • (fderiv ℝ u x w - Complex.I • fderiv ℝ u x (Complex.I • w))) z
      = (1 / 2 : ℂ) • (GlobalTheory.del (fun x => fderiv ℝ u x w) z
          - Complex.I • GlobalTheory.del (fun x => fderiv ℝ u x (Complex.I • w)) z) := fun w => by
    rw [GlobalTheory.del_const_smul _ ((h1 _).fun_sub ((h1 _).fun_const_smul Complex.I)),
      GlobalTheory.del_sub (h1 _) ((h1 _).fun_const_smul Complex.I), GlobalTheory.del_const_smul _ (h1 _)]
  rw [e w, e v, d w, d v]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, GlobalTheory.del_apply,
    GlobalTheory.fderiv_fderiv_apply hu]
  rw [hs.eq v w, hs.eq (Complex.I • v) w, hs.eq v (Complex.I • w),
    hs.eq (Complex.I • v) (Complex.I • w)]
  match_scalars <;> ring

theorem mdel_mdel_comm {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {m n : Type*} {A : E → Matrix m n ℂ} {z : E} (h : MContDiffAt 2 A z)
    (ξ η : E) : mdel (fun x => mdel A x η) z ξ = mdel (fun x => mdel A x ξ) z η := by
  ext a b
  exact del_del_comm (h a b) ξ η

theorem mdel_conn_inv_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E)
    (h2 : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (hs : ∀ᶠ x in 𝓝 z, (H x).IsSymm) (ξ η : E) :
    mdel (fun x => conn (fun y => (H y)⁻¹) x η) z ξ
      - mdel (fun x => conn (fun y => (H y)⁻¹) x ξ) z η
      = -(conn H z η * conn H z ξ - conn H z ξ * conn H z η)ᵀ := by
  have h1 : MContDiffAt 1 H z := h2.of_le one_le_two
  have hloc : ∀ ζ, (fun x => conn (fun y => (H y)⁻¹) x ζ) =ᶠ[𝓝 z]
      fun x => -((H x)⁻¹ * mdel H x ζ)ᵀ := fun ζ => by
    filter_upwards [h2.eventually_two, h2.eventually_isUnit hu, hs.eventually_nhds]
      with x hx2 hxu hxs
    have e : (fun y => (H y)⁻¹) =ᶠ[𝓝 x] fun y => GlobalTheory.HermFrame.dualGram (H y) :=
      hxs.mono fun y hy => by
        change (H y)⁻¹ = (H y)⁻¹ᵀ
        rw [transpose_nonsing_inv, hy.eq]
    rw [conn_congr e, conn_dual (hx2.of_le one_le_two) hxu, conn_eq_of_isSymm hxs]
  have hP : ∀ ζ, MContDiffAt 1 (fun x => mdel H x ζ) z := fun ζ => h2.mdel (by norm_num) ζ
  rw [mdel_congr (hloc η), mdel_congr (hloc ξ), mdel_neg, mdel_neg,
    mdel_transpose (fun x => (H x)⁻¹ * mdel H x η), mdel_transpose (fun x => (H x)⁻¹ * mdel H x ξ),
    mdel_mul (h1.inv hu) (hP η), mdel_mul (h1.inv hu) (hP ξ), mdel_inv h1 hu, mdel_inv h1 hu,
    mdel_mdel_comm h2 ξ η, conn_eq_of_isSymm hs, conn_eq_of_isSymm hs]
  have key : (H z)⁻¹ * mdel (fun x => mdel H x ξ) z η + -((H z)⁻¹ * mdel H z ξ * (H z)⁻¹) * mdel H z η
      - ((H z)⁻¹ * mdel (fun x => mdel H x ξ) z η + -((H z)⁻¹ * mdel H z η * (H z)⁻¹) * mdel H z ξ)
      = (H z)⁻¹ * mdel H z η * ((H z)⁻¹ * mdel H z ξ) - (H z)⁻¹ * mdel H z ξ * ((H z)⁻¹ * mdel H z η) := by
    noncomm_ring
  rw [← key, transpose_sub]
  abel

end GlobalTheory.HermFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDerivChernConnectionInverseSymmetricGStatement
open Matrix
open scoped ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicDeriv_chernConnection_inverseSymmetricGram : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E), GlobalTheory.HermFrame.MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) → ∀ ξ η, GlobalTheory.HermFrame.mdel (fun x => GlobalTheory.HermFrame.conn (fun y => (H y)⁻¹) x η) z ξ - GlobalTheory.HermFrame.mdel (fun x => GlobalTheory.HermFrame.conn (fun y => (H y)⁻¹) x ξ) z η = -(GlobalTheory.HermFrame.conn H z η * GlobalTheory.HermFrame.conn H z ξ - GlobalTheory.HermFrame.conn H z ξ * GlobalTheory.HermFrame.conn H z η)ᵀ := by
  first | exact @GlobalTheory.HermFrame.mdel_conn_inv_sub | exact GlobalTheory.HermFrame.mdel_conn_inv_sub | (intros; apply GlobalTheory.HermFrame.mdel_conn_inv_sub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdealAlongStalkPointEqMap
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TraitStalk

theorem idlAlong_spMap_fromSpecStalk : ∀ (T : Scheme.{0}) (v : T) (J : T.IdealSheafData) (W : Type) [CommRing W] [IsLocalRing W]
    (g : T.presheaf.stalk v →+* W), IsLocalHom g → idlAlong J (spMap g ≫ T.fromSpecStalk v) = (FinalTheorems.stalkId J v).map g :=
  fun _ v J _ _ _ g _ => GlobalTheory.PolDiv.idlAlong_fromSpecStalk J v g

end GlobalTheory.TraitStalk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteDvrInjectiveLocal
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.LocalCompletion

open IsLocalRing

theorem exists_cDvr_embedding : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O], IsIntegrallyClosed O → IsNoetherianRing O → ringKrullDim O = 1 → CharZero O → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (g : O →+* W), CDvr W ∧ Function.Injective g ∧ IsLocalHom g := by
  intro O _ _ _ hic hn hd h0
  haveI := hic
  haveI := hn
  haveI : IsDiscreteValuationRing O := GlobalTheory.CdvrExt.isDVR_of_ringKrullDim_eq_one hd
  have hinj := GlobalTheory.algebraMap_adicCompletion_injective_of_dvr O
  haveI : CharZero (AdicCompletion (maximalIdeal O) O) := charZero_of_injective_algebraMap hinj
  refine ⟨AdicCompletion (maximalIdeal O) O, inferInstance, inferInstance, inferInstance,
    algebraMap O (AdicCompletion (maximalIdeal O) O), ?_, hinj, inferInstance⟩
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.LocalCompletion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricChartsPolarizedModel
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.FanTheta

theorem isLB_detOm_of_smooth {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) (hpq : 1 ≤ D.p + D.q)
    (hsm : SmoothOfRelativeDimension D.dim (genStr Y)) : (GlobalTheory.FlagMod.detOm Y).IsLB := by
  have e : spMap (RingHom.id c.F) = 𝟙 _ := by
    simp [spMap]
  haveI : IsIso (spMap (RingHom.id c.F)) := by rw [e]; infer_instance
  haveI : IsIso (genι Y) := inferInstance
  have hs : SmoothOfRelativeDimension D.dim Y.s := by
    have hw : Y.s = inv (genι Y) ≫ genStr Y ≫ spMap (RingHom.id c.F) := by
      rw [← pullback.condition, IsIso.inv_hom_id_assoc]
    rw [hw]
    have := (inferInstance :
      SmoothOfRelativeDimension (0 + (D.dim + 0)) (inv (genι Y) ≫ genStr Y ≫ spMap (RingHom.id c.F)))
    simpa using this
  have hθ : GlobalTheory.Models.HasTheta Y.t.G Y.t.PP.L := GlobalTheory.T.hasFibrewiseNonvanishingThetaSection_of_smooth_model E H D hpq l Xo c Y hs
  exact GlobalTheory.FlagMod.isLB_detOm
    (GlobalTheory.PushInv.pushInvertible_of_model GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 GlobalTheory.allSixLaws.2.2.1 E H D l _ _ _ _ _ _ Y.oF _
      (RingHom.id c.F)
      ⟨Y.X, Y.s, Y.normal, Y.proj, Y.flat, Y.jQ, Y.jQ_over, Y.jQ_open, Y.jQ_dense, Y.t, Y.m, Y.ab_gen⟩
      ⟨⟨inferInstance, inferInstance⟩, inferInstance, inferInstance⟩ hθ)

end GlobalTheory.FanTheta
end
