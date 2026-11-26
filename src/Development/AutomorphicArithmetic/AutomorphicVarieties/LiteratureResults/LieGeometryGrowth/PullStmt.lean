module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullDefs
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open scoped ContDiff TensorProduct

namespace UpperTheory.V.Lit.Geo

section Abs

variable {V' V F : Type} [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def pb (H : V' → V) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V') : V' [⋀^Fin q]→L[ℝ] F :=
  (w (H p)).compContinuousLinearMap (fderiv ℝ H p)

theorem pb_apply (H : V' → V) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V') (v : Fin q → V') :
    pb H w p v = w (H p) fun i => fderiv ℝ H p (v i) := rfl

def flow (W : V → V) (t : ℝ) (p : V) : V := p + t • W p

def hk (W : V → V) (t : ℝ) {q : ℕ} (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) : V [⋀^Fin q]→L[ℝ] F :=
  ((w (flow W t p)).curryLeft (W p)).compContinuousLinearMap (fderiv ℝ (flow W t) p)

theorem hk_apply (W : V → V) (t : ℝ) {q : ℕ} (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) (v : Fin q → V) :
    hk W t w p v = w (flow W t p) (Matrix.vecCons (W p) fun i => fderiv ℝ (flow W t) p (v i)) := rfl

def hom (W : V → V) {q : ℕ} (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) : V [⋀^Fin q]→L[ℝ] F :=
  ∫ t in (0 : ℝ)..1, hk W t w p

def IsField (Y : Set V) (W : V → V) : Prop :=
  ContDiffOn ℝ ∞ W Y ∧ ∀ p ∈ Y, ∀ t ∈ Set.Icc (0 : ℝ) 1, flow W t p ∈ Y

end Abs

section Om

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} (G : Dr.Geo Γ V S d)

structure IsFlow (W : S → V → V) : Prop where
  field : ∀ s, IsField G.Y (W s)
  equiv : ∀ γ s, ∀ p ∈ G.Y, W (G.σ γ s) (G.ρ γ p) = G.ρ γ (W s p)
  homog : ∀ s (t : ℝ), 0 < t → ∀ p ∈ G.Y, W s (t • p) = t • W s p

theorem isFlow_zero : IsFlow G 0 :=
  ⟨fun _ => ⟨contDiffOn_const, fun p hp t _ => by simpa [flow] using hp⟩, fun _ _ _ _ => by simp, fun _ _ _ _ _ => by simp⟩


open Classical in
def toOm {q : ℕ} (z : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) : G.Om q :=
  if h : ∀ s, ContDiffOn ℝ ∞ (z s) G.Y then
    ⟨fun s => G.Y.indicator (z s), fun s =>
      ⟨(h s).congr fun _ hp => Set.indicator_of_mem hp _, fun _ hp => Set.indicator_of_notMem hp _⟩⟩
  else 0

theorem toOm_apply {q : ℕ} {z : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)} (h : ∀ s, ContDiffOn ℝ ∞ (z s) G.Y) (s : S) {p : V}
    (hp : p ∈ G.Y) : (toOm G z).1 s p = z s p := by
  rw [toOm, dite_eq_left h]
  exact Set.indicator_of_mem hp _

def pbOm (W : S → V → V) {q : ℕ} (w : G.Om q) : G.Om q := toOm G fun s => pb (flow (W s) 1) (w.1 s)

def homOm (W : S → V → V) {q : ℕ} (w : G.Om (q + 1)) : G.Om q := toOm G fun s => hom (W s) (w.1 s)

structure Good {q : ℕ} (w : G.Om q) : Prop where
  inv : ∀ γ, G.act q γ w = w
  basic : ∀ s, RadBasic G.Y (w.1 s)
  dbasic : ∀ s, RadBasic G.Y ((G.dOm q w).1 s)

end Om

section Ad

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

structure IsFld (U : Subgroup (GL (Fin a) (Af E))) (Y : GA E a → Herm E a) (C : ℝ) : Prop where
  sm : ∀ i j w, ∃ φ : Sm E a, (∀ g, φ.1 g = (Y g).1 i j w) ∧ BddDer φ
  left : ∀ γ t g, Y (ratGL E a γ * splitCentre E a t * g) = Y g
  cpt : ∀ (k : Kinf E a) g, adHerm k (Y (g * infGL E a (Unitary.toUnits k))) = Y g
  lev : ∀ u ∈ U, ∀ g, Y (g * finGL E a u) = Y g
  root : ∀ g (t : ℝ), |t| ≤ 1 → ∃ h : GL (Fin a) (Cinf E), h.val * star h.val = 1 + t • (Y g).1 ∧
    ‖toL h.val‖ ≤ C ∧ ‖toL (h⁻¹).val‖ ≤ C

theorem IsStep.fld {U : Subgroup (GL (Fin a) (Af E))} {f : GA E a → ℝ} {Y : GA E a → Herm E a} {C c f₀ : ℝ}
    (h : IsStep U f Y C c f₀) : IsFld U Y C := ⟨h.Y_sm, h.Y_left, h.Y_cpt, h.Y_lev, h.root⟩

theorem IsFld.neg {U : Subgroup (GL (Fin a) (Af E))} {Y : GA E a → Herm E a} {C : ℝ} (h : IsFld U Y C) :
    IsFld U (-Y) C := by
  refine { sm := ?_, left := ?_, cpt := ?_, lev := ?_, root := ?_ }
  · intro i j w
    obtain ⟨φ, h1, h2⟩ := h.sm i j w
    refine ⟨-φ, fun g => congrArg Neg.neg (h1 g), fun X l => ?_⟩
    obtain ⟨B, hB⟩ := h2 X l
    exact ⟨B, fun g => by rw [map_neg]; exact (norm_neg _).trans_le (hB g)⟩
  · exact fun γ t g => congrArg Neg.neg (h.left γ t g)
  · intro k g
    have e := congrArg Subtype.val (h.cpt k g)
    refine Subtype.ext ?_
    change k.1 * (-(Y (g * infGL E a (Unitary.toUnits k))).1) * star k.1 = -(Y g).1
    rw [mul_neg, neg_mul, ← e]
    rfl
  · exact fun u hu g => congrArg Neg.neg (h.lev u hu g)
  · intro g t ht
    obtain ⟨x, h1, h2⟩ := h.root g (-t) (by rwa [abs_neg])
    exact ⟨x, by rw [h1, neg_smul]; exact congrArg (1 + ·) (smul_neg t (Y g).1).symm, h2⟩

def FCorr (U : Subgroup (GL (Fin a) (Af E))) (Y : GA E a → Herm E a) (W : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a) : Prop :=
  ∀ (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)),
    W (x : GL (Fin a) (Af E) ⧸ U) (sand g (hOne E a)) = sand g (hv (Y (infGL E a g * finGL E a x)))

def Bd {Ξ : AlgRep E a} {q : ℕ} (α : Co Ξ q) (g : GA E a) (M : ℝ) : Prop :=
  ∀ X : Fin q → Herm E a, ‖ev (α X) (retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ M * ∏ i, ‖hv (X i)‖

theorem Bd.mono {Ξ : AlgRep E a} {q : ℕ} {α : Co Ξ q} {g : GA E a} {M M' : ℝ} (h : Bd α g M) (hM : M ≤ M') : Bd α g M' :=
  fun X => (h X).trans (mul_le_mul_of_nonneg_right hM (Finset.prod_nonneg fun _ _ => norm_nonneg _))

theorem Bd.sub {Ξ : AlgRep E a} {q : ℕ} {α β : Co Ξ q} {g : GA E a} {M M' : ℝ} (h : Bd α g M) (h' : Bd β g M') :
    Bd (α - β) g (M + M') := fun X => by
  rw [sub_apply, map_sub, Pi.sub_apply, add_mul]
  exact (norm_sub_le _ _).trans (add_le_add (h X) (h' X))

end Ad

end UpperTheory.V.Lit.Geo
end
end

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped ContDiff TensorProduct

namespace UpperTheory.V.Lit.Geo

def PbD : Prop :=
  ∀ (V' V F : Type) [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V'] [FiniteDimensional ℝ F] (q : ℕ) (H : V' → V)
    (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V'), ContDiffAt ℝ ∞ H p → ContDiffAt ℝ ∞ w (H p) →
    ContDiffAt ℝ ∞ (pb H w) p ∧ extDeriv (pb H w) p = pb H (extDeriv w) p

def HkSmooth : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ F] (Y : Set V), IsOpen Y → ∀ W : V → V, IsField Y W → ∀ (q : ℕ) (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F),
    ContDiffOn ℝ ∞ w Y → IsOpen {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y} ∧
      ContDiffOn ℝ ∞ (fun z : V × ℝ => hk W z.2 w z.1) {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y} ∧
      (∀ p ∈ Y, ContinuousOn (fun t => hk W t w p) (Set.Icc 0 1)) ∧ ContDiffOn ℝ ∞ (hom W w) Y

def ProdDer : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] (p : V) (t : ℝ),
    (∀ Ω : V × ℝ → (V × ℝ) [⋀^Fin 0]→L[ℝ] F, DifferentiableAt ℝ Ω (p, t) →
      HasDerivAt (fun r => (Ω (p, r)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ))
        (((extDeriv Ω (p, t)).curryLeft (0, 1)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ)) t) ∧
    ∀ (q : ℕ) (Ω : V × ℝ → (V × ℝ) [⋀^Fin (q + 1)]→L[ℝ] F), DifferentiableAt ℝ Ω (p, t) →
      HasDerivAt (fun r => (Ω (p, r)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ))
        (extDeriv (fun x => ((Ω (x, t)).curryLeft (0, 1)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ)) p +
          ((extDeriv Ω (p, t)).curryLeft (0, 1)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ)) t

def HomPt : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ F] (W : V → V) (p : V) (t : ℝ), ContDiffAt ℝ ∞ W p →
    (∀ w : V → V [⋀^Fin 0]→L[ℝ] F, ContDiffAt ℝ ∞ w (flow W t p) →
      HasDerivAt (fun r => pb (flow W r) w p) (hk W t (extDeriv w) p) t) ∧
    ∀ (q : ℕ) (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F), ContDiffAt ℝ ∞ w (flow W t p) →
      HasDerivAt (fun r => pb (flow W r) w p) (extDeriv (hk W t w) p + hk W t (extDeriv w) p) t

def HomForm : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ F] (Y : Set V), IsOpen Y → ∀ W : V → V, IsField Y W → ∀ p ∈ Y,
    (∀ w : V → V [⋀^Fin 0]→L[ℝ] F, ContDiffOn ℝ ∞ w Y → pb (flow W 1) w p - w p = hom W (extDeriv w) p) ∧
    ∀ (q : ℕ) (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F), ContDiffOn ℝ ∞ w Y →
      pb (flow W 1) w p - w p = extDeriv (hom W w) p + hom W (extDeriv w) p

def PbBasic : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ F] (Y : Set V), IsOpen Y → ∀ W : V → V, IsField Y W →
    (∀ t : ℝ, 0 < t → ∀ p ∈ Y, W (t • p) = t • W p) → ∀ q : ℕ,
    (∀ w : V → V [⋀^Fin q]→L[ℝ] F, RadBasic Y w → RadBasic Y (pb (flow W 1) w)) ∧
    ∀ w : V → V [⋀^Fin (q + 1)]→L[ℝ] F, ContDiffOn ℝ ∞ w Y → RadBasic Y w → RadBasic Y (hom W w)

def PbNat : Prop :=
  ∀ (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ F] (Y : Set V), IsOpen Y → ∀ (ρ : V →L[ℝ] V) (A : F →L[ℝ] F) (W W' : V → V), IsField Y W → IsField Y W' →
    (∀ p ∈ Y, ρ p ∈ Y) → (∀ p ∈ Y, W' (ρ p) = ρ (W p)) → ∀ q : ℕ,
    (∀ w w' : V → V [⋀^Fin q]→L[ℝ] F, (∀ p ∈ Y, ∀ v, w' (ρ p) (fun i => ρ (v i)) = A (w p v)) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ Y, ∀ v, pb (flow W' t) w' (ρ p) (fun i => ρ (v i)) = A (pb (flow W t) w p v)) ∧
    ∀ w w' : V → V [⋀^Fin (q + 1)]→L[ℝ] F, (∀ p ∈ Y, ∀ v, w' (ρ p) (fun i => ρ (v i)) = A (w p v)) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ Y, ∀ v, hk W' t w' (ρ p) (fun i => ρ (v i)) = A (hk W t w p v)) ∧
      (ContDiffOn ℝ ∞ w Y → ContDiffOn ℝ ∞ w' Y → ∀ p ∈ Y, ∀ v, hom W' w' (ρ p) (fun i => ρ (v i)) = A (hom W w p v))

def OmApply : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d)
    (W : S → V → V), IsFlow G W → ∀ q : ℕ,
    (∀ (w : G.Om q) s, ∀ p ∈ G.Y, (pbOm G W w).1 s p = pb (flow (W s) 1) (w.1 s) p) ∧
    ∀ (w : G.Om (q + 1)) s, ∀ p ∈ G.Y, (homOm G W w).1 s p = hom (W s) (w.1 s) p

def OmHom : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d)
    (W : S → V → V), IsFlow G W → (∀ (q : ℕ) (w : G.Om q), G.dOm q (pbOm G W w) = pbOm G W (G.dOm q w)) ∧
    (∀ (q : ℕ) (w : G.Om q), G.dOm (q + 1) (G.dOm q w) = 0) ∧
    (∀ w : G.Om 0, pbOm G W w - w = homOm G W (G.dOm 0 w)) ∧
    ∀ (q : ℕ) (w : G.Om (q + 1)), pbOm G W w - w = G.dOm q (homOm G W w) + homOm G W (G.dOm (q + 1) w)

def OmEquiv : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d)
    (W : S → V → V), IsFlow G W → ∀ (q : ℕ) (γ : Γ),
    (∀ w : G.Om q, G.act q γ (pbOm G W w) = pbOm G W (G.act q γ w)) ∧
    ∀ w : G.Om (q + 1), G.act q γ (homOm G W w) = homOm G W (G.act (q + 1) γ w)

def OmGood : Prop :=
  ∀ (Γ V S : Type) [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (d : ℕ) (G : Dr.Geo Γ V S d)
    (W : S → V → V), IsFlow G W → ∀ q : ℕ,
    (∀ w : G.Om q, Good G w → Good G (pbOm G W w) ∧ Good G (G.dOm q w)) ∧
    (∀ w w' : G.Om q, Good G w → Good G w' → Good G (w - w')) ∧
    ∀ w : G.Om (q + 1), Good G w → Good G (homOm G W w)

def LevD : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (q : ℕ) (α : Co Ξ q), IsLev U Ξ α → IsLev U Ξ (dCo (smLie Ξ) α) ∧ ∀ β : Co Ξ q, IsLev U Ξ β → IsLev U Ξ (α - β)

def LevGood : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a))
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ),
    (∀ α : Co Ξ q, IsLev U Ξ α → ∃ w : (geo ho U Ξ).Om q, Corr U Ξ α w.1 ∧ Good (geo ho U Ξ) w) ∧
    ∀ w : (geo ho U Ξ).Om q, Good (geo ho U Ξ) w → ∃ α : Co Ξ q, Corr U Ξ α w.1 ∧ IsLev U Ξ α

def FieldDef : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E)))
    (Y : GA E a → Herm E a) (C : ℝ), IsFld U Y C → ∃ W, FCorr U Y W

def FieldSm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E)))
    (Y : GA E a → Herm E a) (C : ℝ), IsFld U Y C → ∀ W, FCorr U Y W → ∀ s, ContDiffOn ℝ ∞ (W s) (cone E a)

def FieldFlow : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a))
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (Y : GA E a → Herm E a) (C : ℝ), IsFld U Y C → ∀ W, FCorr U Y W →
    IsFlow (geo ho U Ξ) W ∧ ∀ (g h : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) (t : ℝ),
      h.val * star h.val = 1 + t • (Y (infGL E a g * finGL E a x)).1 →
      flow (W (x : GL (Fin a) (Af E) ⧸ U)) t (sand g (hOne E a)) = sand (g * h) (hOne E a)

def FieldDer : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E)))
    (Y : GA E a → Herm E a) (C : ℝ), IsFld U Y C → ∃ B : ℝ, 0 ≤ B ∧ ∀ g : GA E a, ‖hv (Y g)‖ ≤ B ∧
      ∀ (c : ℝ → GL (Fin a) (Cinf E)) (X : Lie E a), c 0 = 1 → HasDerivAt (fun t => toL (c t).val) X 0 →
        ∃ Z : HV E a, ‖Z‖ ≤ B * ‖X‖ ∧ HasDerivAt (fun t => hv (Y (g * infGL E a (c t)))) Z 0

def FieldBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E)))
    (Y : GA E a → Herm E a) (C : ℝ), IsFld U Y C → ∀ W, FCorr U Y W → ∃ B : ℝ, 0 ≤ B ∧
      ∀ (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) (t : ℝ), |t| ≤ 1 → ∀ v : HV E a, ∃ v' : HV E a, ‖v'‖ ≤ B * ‖v‖ ∧
        fderiv ℝ (flow (W (x : GL (Fin a) (Af E) ⧸ U)) t) (sand g (hOne E a)) (sand g v) = sand g v'

def MatBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (C : ℝ), ∃ B : ℝ, 0 ≤ B ∧
    ∀ h : GL (Fin a) (Cinf E), ‖toL h.val‖ ≤ C → ‖toL (h⁻¹).val‖ ≤ C →
      (∀ y, ‖Ξ.mat h *ᵥ y‖ ≤ B * ‖y‖) ∧ (∀ v, ‖sand h v‖ ≤ B * ‖v‖) ∧ ∀ v, ‖sand h⁻¹ v‖ ≤ B * ‖v‖

def CentreVal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (r : ℝ), HasOne Ξ r → ∀ (q : ℕ) (α : Co Ξ q), IsLev U Ξ α → ∀ X (γ : GL (Fin a) E) (t : ℝ) (g : GA E a),
      ev (α X) (ratGL E a γ * splitCentre E a t * g) = Complex.exp (-(r * t)) • ev (α X) g

def RetrFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    (∀ g : GA E a, ∃ t : ℝ, (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1 = splitCentre E a t * g) ∧
    (∀ (γ : GL (Fin a) E) (t : ℝ) (g : GA E a),
      (GroundTheory.Automorphic.CuspidalSpectrum.retractOne (ratGL E a γ * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 =
        ratGL E a γ * (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1) ∧
    ∀ C : ℝ, ∃ T : ℝ, ∀ (g : GA E a) (h : GL (Fin a) (Cinf E)), ‖toL h.val‖ ≤ C → ‖toL (h⁻¹).val‖ ≤ C → ∃ t : ℝ, |t| ≤ T ∧
      (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1 * infGL E a h =
        splitCentre E a t * (GroundTheory.Automorphic.CuspidalSpectrum.retractOne (g * infGL E a h) : KernelIndexFullLattice.G1 E a).1

def CorrBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (C : ℝ) (q : ℕ), ∃ B : ℝ, 0 ≤ B ∧ ∀ (α : Co Ξ q) w, IsLev U Ξ α → Corr U Ξ α w →
      ∀ (g : GA E a) (y h : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) (M : ℝ),
        (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1 = infGL E a y * finGL E a x →
        ‖toL h.val‖ ≤ C → ‖toL (h⁻¹).val‖ ≤ C → 0 ≤ M → Bd α (g * infGL E a h) M → ∀ v : Fin q → HV E a,
          ‖Ξ.mat y⁻¹ *ᵥ w (x : GL (Fin a) (Af E) ⧸ U) (sand (y * h) (hOne E a)) fun i => sand y (v i)‖ ≤ B * M * ∏ i, ‖v i‖

def PbBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a))
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (Y : GA E a → Herm E a) (C : ℝ), IsFld U Y C → ∀ W, FCorr U Y W →
    ∀ q : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ (α α' : Co Ξ q) (w : (geo ho U Ξ).Om q), IsLev U Ξ α → Corr U Ξ α w.1 →
      Corr U Ξ α' (pbOm (geo ho U Ξ) W w).1 → ∀ (g : GA E a) (M : ℝ), 0 ≤ M →
      (∀ h : GL (Fin a) (Cinf E), h.val * star h.val = 1 + (Y g).1 → Bd α (g * infGL E a h) M) → Bd α' g (B * M)

def HomBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ho : IsOpen (cone E a))
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (Y : GA E a → Herm E a) (C : ℝ), IsFld U Y C → ∀ W, FCorr U Y W →
    ∀ q : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ (α : Co Ξ (q + 1)) (α' : Co Ξ q) (w : (geo ho U Ξ).Om (q + 1)), IsLev U Ξ α → Corr U Ξ α w.1 →
      Corr U Ξ α' (homOm (geo ho U Ξ) W w).1 → ∀ (g : GA E a) (M : ℝ), 0 ≤ M →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ h : GL (Fin a) (Cinf E), h.val * star h.val = 1 + t • (Y g).1 → Bd α (g * infGL E a h) M) →
      Bd α' g (B * M)

def StepCut : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E)))
    (f : GA E a → ℝ) (Y : GA E a → Herm E a) (C c f₀ : ℝ), IsStep U f Y C c f₀ → ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, ∃ u : Sm E a,
      IsCut U u ∧ ∀ g, (∀ X, ‖(lie E a X u).1 g‖ ≤ B * ‖X‖) ∧ (f g ≤ R → u.1 g = 1 ∧ ∀ X, (lie E a X u).1 g = 0) ∧
        (R + 1 ≤ f g → u.1 g = 0 ∧ ∀ X, (lie E a X u).1 g = 0)

end UpperTheory.V.Lit.Geo
