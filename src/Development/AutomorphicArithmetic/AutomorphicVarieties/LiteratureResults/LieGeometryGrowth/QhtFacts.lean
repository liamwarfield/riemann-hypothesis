module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConstantTermEqZeroOfIsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DExact
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrUniq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ExistsCurve

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem qht_le (g : GA E a) (γ : GL (Fin a) E) :
    qht g ≤ height (K := E) (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1) :=
  ciInf_le ⟨1, by rintro _ ⟨δ, rfl⟩; exact one_le_height _⟩ γ

private theorem one_le_qht (g : GA E a) : 1 ≤ qht g := le_ciInf fun _ => one_le_height _

private theorem retract_left (γ : GL (Fin a) E) (t : ℝ) (g : GA E a) :
    (retractOne (ratGL E a γ * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1 := by
  let y : KernelIndexFullLattice.G1 E a := ⟨ratGL E a γ, Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩⟩
  change (retractOne ((y : GA E a) * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = _
  rw [mul_assoc, retractOne_coe_mul, retractOne_mul, KernelIndexFullLattice.splitEq_holds E a t, retractOne_centralSection, one_mul]
  rfl

private theorem qht_left (γ : GL (Fin a) E) (t : ℝ) (g : GA E a) :
    qht (ratGL E a γ * splitCentre E a t * g) = qht g := by
  unfold qht
  rw [retract_left]
  refine Eq.trans ?_ ((Equiv.mulRight γ).iInf_comp
    (g := fun δ : GL (Fin a) E => height (K := E) (ratGL E a δ * (retractOne g : KernelIndexFullLattice.G1 E a).1)))
  refine congrArg _ (funext fun δ => ?_)
  rw [Equiv.coe_mulRight, map_mul, mul_assoc]

private theorem exists_split (g : GA E a) : ∃ t : ℝ, splitCentre E a t * g = (retractOne g : KernelIndexFullLattice.G1 E a).1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨0, Units.ext (Subsingleton.elim _ _)⟩
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  refine ⟨Real.log ((Reduction.detModule E a g)⁻¹).1 / (a * Module.finrank ℚ E), ?_⟩
  rw [KernelIndexFullLattice.splitEq_holds E a, coe_retractOne, ← centralSection_inv_mul_comm,
    ← map_inv (Reduction.centralSection E a)]
  refine congrArg (fun s => Reduction.centralSection E a s * g) (Subtype.ext ?_)
  change Real.exp _ = _
  rw [mul_div_cancel₀ _ (mul_pos h1 h2).ne', Real.exp_log ((Reduction.detModule E a g)⁻¹).2]

private theorem qht_mul {C : Set (GA E a)} (hC : IsCompact C) :
    ∃ B : ℝ, ∀ g : GA E a, ∀ h ∈ C, qht (g * h) ≤ B * qht g := by
  obtain ⟨M, hM⟩ := exists_height_le_of_isCompact (K := E) (n := a)
    (hC.image (continuous_subtype_val.comp (continuous_retractOne (K := E) (n := a))))
  have hc : 0 < heightConst E a := one_pos.trans_le one_le_heightConst
  refine ⟨heightConst E a * M, fun g h hh => ?_⟩
  have hm := hM _ ⟨h, hh, rfl⟩
  have hM0 : 0 < M := (height_pos _).trans_le hm
  rw [← div_le_iff₀' (mul_pos hc hM0)]
  refine le_ciInf fun γ => ?_
  rw [div_le_iff₀' (mul_pos hc hM0)]
  refine (qht_le _ γ).trans ?_
  rw [retractOne_mul, Subgroup.coe_mul, ← mul_assoc, mul_right_comm]
  exact (height_mul_le _ _).trans (mul_le_mul_of_nonneg_left hm (mul_pos hc (height_pos _)).le)

private theorem qht_proper (R : ℝ) : ∃ C : Set (GA E a), IsCompact C ∧
    ∀ g : GA E a, qht g ≤ R → ∃ γ t, ratGL E a γ * splitCentre E a t * g ∈ C := by
  obtain ⟨c, N, hc, h⟩ := UpperTheory.adelicNorm_vecMul_ge_of_height E a
  have hR : 0 < max 1 R + 1 := by positivity
  obtain ⟨C, hC, hC'⟩ := Reduction.exists_isCompact_forall_of_pos_le_height (K := E) (n := a)
    (ε := (c * (max 1 R + 1) ^ N)⁻¹) (by positivity)
  refine ⟨C, hC, fun g hg => ?_⟩
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt (hg.trans_lt ((le_max_right 1 R).trans_lt (lt_add_one _)))
  obtain ⟨t, ht⟩ := exists_split g
  obtain ⟨_, ⟨δ, rfl⟩, x, hx, e⟩ := hC' (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1)
    (mul_mem (Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩) (retractOne g).2) fun v hv => by
      rw [inv_le_iff_one_le_mul₀' (by positivity)]
      have h0 := h (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1) v hv
      have hp : 0 ≤ Reduction.height (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1) v := by
        by_contra hn
        have : 0 ≤ c * height (K := E) (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1) ^ N := by
          have := height_pos (K := E) (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1)
          positivity
        nlinarith [not_le.1 hn]
      exact h0.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (height_pos _).le hγ.le N) hc.le) hp)
  refine ⟨δ⁻¹ * γ, t, ?_⟩
  have e' : ratGL E a δ * x = ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1 := e
  rw [mul_assoc, ht, map_mul, mul_assoc, ← e', map_inv, inv_mul_cancel_left]
  exact hx

end UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.qhtFacts :
    QhtFacts := by
  intro E _ _ _ a
  exact ⟨one_le_qht, qht_left, fun _ hC => qht_mul hC, qht_proper⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
noncomputable section

open NumberField Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL

namespace UpperTheory.V.Lit.Geo.Pf

section Defs

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

structure CInv (F : GA E a → ℂ) : Prop where
  cont : Continuous F
  left : ∀ γ g, F (ratGL E a γ * g) = F g
  centre : ∀ t g, F (splitCentre E a t * g) = F g

structure SInv (φ : Sm E a) : Prop where
  left : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g
  centre : ∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g
  level : IsOpen {k | act (.fin k) φ = φ}

def Cs {M : Type} [Zero M] (F : GA E a → M) : Prop := ∃ R : ℝ, ∀ g, R < qht g → F g = 0

def QInt (μ : Measure (GA E a)) (F : GA E a → ℂ) : Prop :=
  Integrable (fun x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a) => F x.out) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)

def qint (μ : Measure (GA E a)) (F : GA E a → ℂ) : ℂ :=
  ∫ x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a), F x.out ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)

def TwInv (χ : HChar E) {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) : Prop := ∀ j, SInv (mulChi a χ (cmp j m))

def pt (χ : HChar E) {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) : ℂ :=
  (‖((chiDet a χ g : ℂˣ) : ℂ)‖ ^ 2 : ℝ) * (star (ev x g) ⬝ᵥ G *ᵥ ev y g)

theorem cmp_ev {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) (g : GA E a) : (cmp j m).1 g = ev m g j := by
  induction m using TensorProduct.inductionOn with
  | tmul φ v => simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

theorem ptIp_eq {Ξ : AlgRep E a} {q : ℕ} (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) {n : ℕ} (e : Fin n → Herm E a)
    (α β : Co Ξ q) (g : GA E a) :
    ptIp χ G e α β g = ∑ I : Fin q → Fin n, pt χ G (α fun i => e (I i)) (β fun i => e (I i)) g := by
  simp only [ptIp, pt, Finset.mul_sum]

theorem CInv.sum {ι : Type} (s : Finset ι) {F : ι → GA E a → ℂ} (h : ∀ i, CInv (F i)) : CInv fun g => ∑ i ∈ s, F i g :=
  ⟨continuous_finsetSum _ fun i _ => (h i).cont, fun γ g => Finset.sum_congr rfl fun i _ => (h i).left γ g,
    fun t g => Finset.sum_congr rfl fun i _ => (h i).centre t g⟩

theorem cs_pt_left (χ : HChar E) {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) {x : Sm E a ⊗[ℂ] (Fin d → ℂ)} (y : Sm E a ⊗[ℂ] (Fin d → ℂ))
    (h : Cs (ev x)) : Cs (pt χ G x y) :=
  h.imp fun _ hR g hg => by simp [pt, hR g hg]

theorem cs_pt_right (χ : HChar E) {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) (x : Sm E a ⊗[ℂ] (Fin d → ℂ)) {y : Sm E a ⊗[ℂ] (Fin d → ℂ)}
    (h : Cs (ev y)) : Cs (pt χ G x y) :=
  h.imp fun _ hR g hg => by simp [pt, hR g hg]

end Defs

def InvLie : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), SInv φ →
    CInv φ.1 ∧ ∀ X : Lie E a, SInv (lie E a X φ)

def BddInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (F : GA E a → ℂ), CInv F → (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → QInt μ F ∧ GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (latticeGL E a) μ F

def CsBdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ), CInv F →
    (Cs F ∨ ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖F g.1‖ ≤ C) → ∃ C : ℝ, ∀ g, ‖F g‖ ≤ C

def CsLie : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (X : Lie E a), Cs φ.1 → Cs (lie E a X φ).1

def ProdEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ ψ : Sm E a), ∃ θ : Sm E a,
    (∀ g, θ.1 g = starRingEnd ℂ (φ.1 g) * ψ.1 g) ∧
    ∀ (X : Lie E a) g, (lie E a X θ).1 g =
      starRingEnd ℂ ((lie E a X φ).1 g) * ψ.1 g + starRingEnd ℂ (φ.1 g) * (lie E a X ψ).1 g

def StokesFn : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (θ : Sm E a) (X : Lie E a), SInv θ → Cs θ.1 → qint μ (lie E a X θ).1 = 0

def LevInv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E), HasOne Ξ r → IsTw (a := a) r χ →
    ∀ (q : ℕ) (α : Co Ξ q), IsLev U Ξ α → ∀ X, TwInv χ (α X)

def PtInv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (χ : HChar E) (d : ℕ) (G : Matrix (Fin d) (Fin d) ℂ)
    (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)),
    (∀ g, pt χ G x y g = ∑ i, ∑ j, G i j *
      (starRingEnd ℂ ((mulChi a χ (cmp i x)).1 g) * (mulChi a χ (cmp j y)).1 g)) ∧
    ((TwInv χ x → TwInv χ y → CInv (pt χ G x y)) ∧
      ∀ θ : Sm E a, (∀ g, θ.1 g = pt χ G x y g) → TwInv χ x → TwInv χ y → SInv θ)

def TwLie : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E),
    IsTw (a := a) r χ → ∀ (X : Lie E a) (x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)), TwInv χ x →
      TwInv χ (smLie Ξ X x) ∧ TwInv χ (smAdj Ξ r X x)

def CsTens : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (r : ℝ) (X : Lie E a)
    (x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)), Cs (ev x) → Cs (ev (smLie Ξ X x)) ∧ Cs (ev (smAdj Ξ r X x))

def PtDiv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), IsTw (a := a) r χ → IsAdm Ξ G → ∀ x y : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ),
    ∃ θ : Sm E a, (∀ g, θ.1 g = pt χ G x y g) ∧ ∀ (X : Herm E a) g,
      (lie E a (toL X.1) θ).1 g = pt χ G x (smLie Ξ (toL X.1) y) g - pt χ G (smAdj Ξ r (toL X.1) x) y g

def AdjInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), IsTw (a := a) r χ → IsAdm Ξ G →
    ∀ (X : Herm E a) (x y : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)), TwInv χ x → TwInv χ y → Cs (ev x) ∨ Cs (ev y) →
      QInt μ (pt χ G x (smLie Ξ (toL X.1) y)) ∧ QInt μ (pt χ G (smAdj Ξ r (toL X.1) x) y) ∧
        qint μ (pt χ G x (smLie Ξ (toL X.1) y)) = qint μ (pt χ G (smAdj Ξ r (toL X.1) x) y)

def PtD : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a) (q : ℕ)
    (L : Lie E a →ₗ[ℝ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) (β : Co Ξ (q + 1)) (η : Co Ξ q) (g : GA E a),
    ptIp χ G e β (dCo L η) g = ((q : ℂ) + 1) * ∑ J : Fin q → Fin n, ∑ j,
        pt χ G (β (Matrix.vecCons (e j) fun i => e (J i))) (L (toL (e j).1) (η fun i => e (J i))) g ∧
      ptIp χ G e (del L e β) η g = ∑ J : Fin q → Fin n, ∑ j,
        pt χ G (L (toL (e j).1) (β (Matrix.vecCons (e j) fun i => e (J i)))) (η fun i => e (J i)) g

def ChiOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (χ : HChar E) (s : ℝ), χ.IsAbsPow s →
    ∀ g : KernelIndexFullLattice.G1 E a, ‖((chiDet a χ g.1 : ℂˣ) : ℂ)‖ = 1

def RapidBdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (χ : HChar E) (s : ℝ), χ.IsAbsPow s →
    ∀ (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a) (q : ℕ) (α β : Co Ξ q), Rapid α → Moderate β →
      ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖ptIp χ G e α β g.1‖ ≤ C

def ZeroInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (F : GA E a → ℂ), CInv F → (∀ g, ∃ t : ℝ, 0 ≤ t ∧ F g = t) → QInt μ F → qint μ F = 0 → ∀ g, F g = 0

def PtPos : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), IsAdm Ξ G → ∀ (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (q : ℕ) (α : Co Ξ q),
    (∀ g, ∃ t : ℝ, 0 ≤ t ∧ ptIp χ G e α α g = t) ∧ ((∀ g, ptIp χ G e α α g = 0) → α = 0)

theorem pairFacts_of_steps (h1 : BddInt) (h2 : CsBdd) (h3 : LevInv) (h4 : PtInv) (h5 : AdjInt) (h6 : PtD) (h7 : RapidBdd)
    (h8 : ZeroInt) (h9 : PtPos) : PairFacts := by
  intro E _ _ _ a ha μ _ U hU Ξ r χ G n e hD q
  have hv := h3 E a ha U hU Ξ r χ hD.one hD.tw
  have hc : ∀ α β : Co Ξ q, IsLev U Ξ α → IsLev U Ξ β → CInv (ptIp χ G e α β) := fun α β hα hβ => by
    rw [show ptIp χ G e α β = _ from funext (ptIp_eq χ G e α β)]
    exact CInv.sum _ fun I => (h4 E a χ _ G _ _).2.1 (hv q α hα _) (hv q β hβ _)
  refine ⟨fun α β hα hβ hr hm => ?_, fun α β hα hβ hs => ⟨?_, ?_⟩, fun α hα hi h0 => ?_, fun β η hβ hη hs => ?_⟩
  · obtain ⟨s, hs⟩ := hD.tw.1
    exact (h1 E a μ _ (hc α β hα hβ) (h2 E a _ (hc α β hα hβ) (.inr (h7 E a Ξ χ s hs G n e q α β hr hm)))).1
  · refine (h1 E a μ _ (hc α β hα hβ) (h2 E a _ (hc α β hα hβ) (.inl ?_))).1
    exact hs.imp fun R hR g hg => by simp [ptIp, hR _ g hg]
  · refine (h1 E a μ _ (hc β α hβ hα) (h2 E a _ (hc β α hβ hα) (.inl ?_))).1
    exact hs.imp fun R hR g hg => by simp [ptIp, hR _ g hg]
  · have hp := h9 E a Ξ χ G hD.adm n e hD.frame q α
    exact hp.2 (h8 E a μ _ (hc α α hα hα) hp.1 hi h0)
  · have hA := fun (J : Fin q → Fin n) (j : Fin n) => h5 E a μ Ξ r χ G hD.tw hD.adm (e j)
      (β (Matrix.vecCons (e j) fun i => e (J i))) (η fun i => e (J i)) (hv _ β hβ _) (hv _ η hη _)
      (hs.imp (fun h => h.imp fun R hR g hg => hR _ g hg) fun h => h.imp fun R hR g hg => hR _ g hg)
    simp only [pair, (h6 E a Ξ χ G n e q (smLie Ξ) β η _).1, (h6 E a Ξ χ G n e q (smAdj Ξ r) β η _).2]
    rw [integral_const_mul, integral_finsetSum _ fun J _ => integrable_finsetSum _ fun j _ => (hA J j).1,
      integral_finsetSum _ fun J _ => integrable_finsetSum _ fun j _ => (hA J j).2.1]
    congr 1
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [integral_finsetSum _ fun j _ => (hA J j).1, integral_finsetSum _ fun j _ => (hA J j).2.1]
    exact Finset.sum_congr rfl fun j _ => (hA J j).2.2

end UpperTheory.V.Lit.Geo.Pf
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PerNat
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr
open scoped TensorProduct

private theorem hd_map {Γ M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (P : M →ₗ[ℂ] N)
    (b : List Γ → M) : hd (fun z => P (b z)) = fun z => P (hd b z) := by
  funext z
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hd, map_sum, map_zsmul]

private theorem zig_map {Γ V S S' : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (G : Dr.Geo Γ V S d) (G' : Dr.Geo Γ V S' d) (f : S' → S) (P : ∀ q, G.Om q →ₗ[ℂ] G'.Om q)
    (ha : ∀ q γ w, P q (G.act q γ w) = G'.act q γ (P q w))
    (hD : ∀ q w, P (q + 1) (G.dOm q w) = G'.dOm q (P q w))
    (hi : ∀ c, P 0 (G.incl c) = G'.incl (c ∘ f)) (c : List Γ → S → Fin d → ℂ) (q : ℕ) :
    ∀ (k : ℕ) (u : List Γ → G.Om q), Zig G q k u c → Zig G' q k (fun z => P q (u z)) (fun z => c z ∘ f) := by
  induction q with
  | zero =>
    intro k u h z hz
    beta_reduce
    rw [h z hz, hi]
  | succ q ih =>
    rintro k u ⟨b, h1, h2, h3⟩
    refine ⟨fun z => P q (b z), fun γ z hz => ?_, fun z hz => ?_, ?_⟩
    · beta_reduce
      rw [h1 γ z hz, ha]
    · beta_reduce
      rw [← h2 z hz, hD]
    · rw [hd_map]
      exact ih _ _ h3

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private def pb (ho : IsOpen (cone E a)) (U U' : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (f : GL (Fin a) (Af E) ⧸ U' → GL (Fin a) (Af E) ⧸ U) (q : ℕ) : (geo ho U Ξ).Om q →ₗ[ℂ] (geo ho U' Ξ).Om q where
  toFun w := ⟨fun s => w.1 (f s), fun s => w.2 (f s)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem ev_rT {d : ℕ} (x : GL (Fin a) (Af E)) (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) :
    ev ((act (.fin x)).rTensor (Fin d → ℂ) m) g = ev m (g * finGL E a x) := by
  induction m using TensorProduct.inductionOn with
  | tmul φ v => rfl
  | add m m' h h' => simp only [map_add (f := _), Pi.add_apply, h, h']

private theorem rT_map' {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T A : Module.End ℂ W)
    (B : Module.End ℂ (Fin d → ℂ)) (h : A * T = T * A) (m : W ⊗[ℂ] (Fin d → ℂ)) :
    T.rTensor _ (TensorProduct.map A B m) = TensorProduct.map A B (T.rTensor _ m) := by
  induction m using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul]
    congr 1
    exact (LinearMap.congr_fun h φ).symm

private theorem cpt_fin (k : Kinf E a) (x : GL (Fin a) (Af E)) :
    act (.cpt k) * act (.fin x) = act (.fin x) * act (E := E) (.cpt k) := by
  change rt E a _ * rt E a _ = rt E a _ * rt E a _
  rw [← map_mul, ← map_mul]
  exact congrArg _ (infGL_comm _ _)

private theorem rT_lie (Ξ : AlgRep E a) (x : GL (Fin a) (Af E)) (X : Lie E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (smLie Ξ X m) = smLie Ξ X ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) m) := by
  have h1 := rT_map' (act (.fin x)) (lie E a X) LinearMap.id (lie_rt_fin X x) m
  have h2 := rT_map' (act (.fin x)) LinearMap.id (Matrix.toLin' (Ξ.dmat X)) rfl m
  change (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (_ + _) = _ + _
  rw [map_add (f := _)]
  exact congrArg₂ (· + ·) h1 h2

private theorem lev_fin {U U' : Subgroup (GL (Fin a) (Af E))} {x : GL (Fin a) (Af E)} (hx : ∀ u ∈ U', x⁻¹ * u * x ∈ U)
    (Ξ : AlgRep E a) {φ : Sm E a} (h : IsLevelFn U Ξ φ) : IsLevelFn U' Ξ (act (.fin x) φ) := by
  refine ⟨fun γ g => ?_, fun u hu => ?_, fun m hm => ?_⟩
  · change φ.1 (ratGL E a γ * g * finGL E a x) = φ.1 (g * finGL E a x)
    rw [mul_assoc, h.1]
  · refine Subtype.ext (funext fun g => ?_)
    have e : φ.1 (g * finGL E a x * finGL E a (x⁻¹ * u * x)) = φ.1 (g * finGL E a x) :=
      congrFun (congrArg Subtype.val (h.2.1 _ (hx u hu))) (g * finGL E a x)
    change φ.1 (g * finGL E a u * finGL E a x) = φ.1 (g * finGL E a x)
    rw [← e, mul_assoc, mul_assoc, ← map_mul, ← map_mul]
    congr 3
    group
  · have e : lie E a (oneL E a) (act (.fin x) φ) = act (.fin x) (lie E a (oneL E a) φ) :=
      LinearMap.congr_fun (lie_rt_fin (oneL E a) x) φ
    rw [e, h.2.2 m hm, map_smul]

end

theorem UpperTheory.V.Lit.Geo.perNat :
    PerNat := by
  intro E _ _ _ a U U' x hx Ξ q α hα
  refine ⟨⟨fun k X => ?_, fun X i hi => ?_, fun X => ?_⟩, ?_, fun c c' hc h => ?_⟩
  · change (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α _) = smK Ξ k ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α X))
    rw [hα.equiv k X]
    exact rT_map' _ _ _ (cpt_fin k x) _
  · change (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α X) = 0
    rw [hα.basic X i hi, map_zero]
  · change (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α X) ∈ _
    have hm := hα.val X
    generalize α X = m at hm
    induction hm using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨φ, v, hφ, rfl⟩ := hy
      exact Submodule.subset_span ⟨_, v, lev_fin hx Ξ hφ, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul s y _ hy => rw [map_smul]; exact Submodule.smul_mem _ s hy
  · refine AlternatingMap.ext fun X => ?_
    change _ = (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (dCo (smLie Ξ) α X)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dCo, AlternatingMap.alternatizeUncurryFin_apply, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
    exact (rT_lie Ξ x _ _).symm
  · obtain ⟨ho, w, hw, hz⟩ := h
    let f : GL (Fin a) (Af E) ⧸ U' → GL (Fin a) (Af E) ⧸ U := fun s =>
      Quotient.liftOn' s (fun y => ((y * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U)) fun y y' hy => by
        rw [QuotientGroup.leftRel_apply] at hy
        refine QuotientGroup.eq.2 ?_
        have := hx _ hy
        rwa [show (y * x)⁻¹ * (y' * x) = x⁻¹ * (y⁻¹ * y') * x by group]
    have hf : ∀ (g : GL (Fin a) (Af E)) s, f (g • s) = g • f s := fun g s => by
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
      change ((g * y * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) = ((g * (y * x) : GL (Fin a) (Af E)) : _ ⧸ U)
      rw [mul_assoc]
    have hc' : c' = fun z => c z ∘ f := by
      funext z s
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
      exact hc z y
    refine ⟨ho, pb ho U U' Ξ f q w, fun g y X => ?_, ?_⟩
    · change w.1 ((y * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) _ _ =
        Ξ.mat g *ᵥ ev ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) (α X)) _
      rw [ev_rT, mul_assoc, ← map_mul]
      exact hw g (y * x) X
    · rw [hc']
      refine zig_map (geo ho U Ξ) (geo ho U' Ξ) f (pb ho U U' Ξ f) (fun q γ w => ?_) (fun q w => rfl) (fun c => rfl) c q 0 _ hz
      refine Subtype.ext (funext fun s => funext fun p => ContinuousAlternatingMap.ext fun v => ?_)
      change _ *ᵥ w.1 ((geo ho U Ξ).σ γ⁻¹ (f s)) _ _ = _ *ᵥ w.1 (f ((geo ho U' Ξ).σ γ⁻¹ s)) _ _
      rw [geo_σ, geo_σ, hf]
      rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ZigClosed
open UpperTheory.V.Lit.Geo

namespace UpperTheory.V.Lit.Geo

open UpperTheory.V.Lit.Dr

section Hom

variable {Γ M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

omit [Module ℂ M] in
private theorem hd_cons (c : List Γ → M) (g : Γ) (t : List Γ) :
    hd c (g :: t) = c t - hd (fun s => c (g :: s)) t := by
  simp only [hd, List.length_cons, Finset.sum_range_succ', List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, pow_succ,
    pow_zero, one_smul, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib]
  abel

omit [Module ℂ M] in
private theorem hd_sub (c c' : List Γ → M) (x : List Γ) : hd (fun s => c s - c' s) x = hd c x - hd c' x := by
  simp only [hd, smul_sub, Finset.sum_sub_distrib]

omit [Module ℂ M] in
private theorem hd_hd (x : List Γ) : ∀ c : List Γ → M, hd (hd c) x = 0 := by
  induction x with
  | nil => intro c; simp [hd]
  | cons g t ih =>
    intro c
    rw [hd_cons]
    simp only [hd_cons]
    rw [hd_sub, ih]
    simp

private theorem hd_lin (c c' : List Γ → M) (s t : ℂ) : hd (s • c + t • c') = s • hd c + t • hd c' := by
  funext x
  simp only [hd, Pi.add_apply, Pi.smul_apply, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_comm s, smul_comm t]

private theorem map_hd (f : M →ₗ[ℂ] N) (c : List Γ → M) (c' : List Γ → N) (k : ℕ)
    (h : ∀ x : List Γ, x.length = k + 1 → f (c x) = c' x) (x : List Γ) (hx : x.length = k + 2) :
    f (hd c x) = hd c' x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hd, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h]
  rw [List.length_eraseIdx_of_lt (Finset.mem_range.1 hi), hx]; rfl

variable [Group Γ]

private theorem hequiv_hd (ρ : Representation ℂ Γ M) (k : ℕ) (c : List Γ → M) (h : HEquiv ρ k c) :
    HEquiv ρ (k + 1) (hd c) := fun γ x hx => by
  rw [map_hd (ρ γ) c (fun y => c (y.map (γ * ·))) k (fun y hy => (h γ y hy).symm) x hx]
  simp only [hd, List.length_map, List.eraseIdx_map]

private theorem lift_equiv (ρ : Representation ℂ Γ M) (ρ' : Representation ℂ Γ N) (f : M →ₗ[ℂ] N)
    (hf : ∀ γ m, f (ρ γ m) = ρ' γ (f m)) (k : ℕ) (u : List Γ → N) (hu : HEquiv ρ' k u)
    (h : ∀ x : List Γ, x.length = k + 1 → ∃ m, f m = u x) :
    ∃ b, HEquiv ρ k b ∧ ∀ x : List Γ, x.length = k + 1 → f (b x) = u x := by
  have h' : ∀ x : List Γ, ∃ m, x.length = k + 1 → f m = u x := fun x => by
    by_cases hx : x.length = k + 1
    · obtain ⟨m, hm⟩ := h x hx
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun e => absurd e hx⟩
  choose p hp using h'
  refine ⟨fun x => ρ (x.headD 1) (p (x.map ((x.headD 1)⁻¹ * ·))), fun γ x hx => ?_, fun x hx => ?_⟩
  · cases x with
    | nil => simp at hx
    | cons g t =>
      have e : (List.map (fun x => γ * x) (g :: t)).map ((γ * g)⁻¹ * ·) = (g :: t).map (g⁻¹ * ·) := by
        rw [List.map_map]
        congr 1
        funext y
        simp [mul_assoc]
      have e2 : (List.map (fun x => γ * x) (g :: t)).headD 1 = γ * g := rfl
      simp only [e2, e, List.headD_cons, map_mul, Module.End.mul_apply]
  · rw [hf, hp _ (by rw [List.length_map, hx]), hu _ _ hx, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]

end Hom

section Zig

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {d : ℕ}
  (G : Dr.Geo Γ V S d)

private theorem zig_ex (hc : Convex ℝ G.Y) (hn : G.Y.Nonempty) (q : ℕ) : ∀ (k : ℕ) (u : List Γ → G.Om q),
    HEquiv (G.act q) k u → (∀ x : List Γ, x.length = k + 1 → G.dOm q (u x) = 0) →
    (∀ x : List Γ, x.length = k + 2 → hd u x = 0) → ∃ c, Zig G q k u c := by
  induction q with
  | zero =>
    intro k u h1 h2 _
    obtain ⟨a1, -, a3⟩ := inclFacts Γ V S d G hc hn
    obtain ⟨b, -, hb⟩ := lift_equiv G.lev (G.act 0) G.incl a1 k u h1 fun x hx => (a3 _).1 (h2 x hx)
    exact ⟨b, fun x hx => (hb x hx).symm⟩
  | succ q ih =>
    intro k u h1 h2 h3
    obtain ⟨b, hb1, hb⟩ := lift_equiv (G.act q) (G.act (q + 1)) (G.dOm q) (dEquiv Γ V S d G q) k u h1
      fun x hx => (dExact Γ V S d G hc q _).1 (h2 x hx)
    obtain ⟨c, hc⟩ := ih (k + 1) (hd b) (hequiv_hd _ _ _ hb1)
      (fun x hx => (map_hd _ _ _ k hb x hx).trans (h3 x hx)) fun x _ => hd_hd x b
    exact ⟨c, b, hb1, hb, hc⟩

private theorem zig_coc (hc : Convex ℝ G.Y) (hn : G.Y.Nonempty) (q : ℕ) : ∀ (k n : ℕ) (u : List Γ → G.Om q) c,
    k + q = n → HEquiv (G.act q) k u → (∀ x : List Γ, x.length = k + 2 → hd u x = 0) → Zig G q k u c →
    HCoc G.lev n c := by
  induction q with
  | zero =>
    rintro k n u c rfl h1 h3 hz
    obtain ⟨a1, a2, -⟩ := inclFacts Γ V S d G hc hn
    refine ⟨fun γ x hx => a2 ?_, fun x hx => a2 ?_⟩
    · rw [a1, ← hz x hx, ← hz _ (by rw [List.length_map]; exact hx), h1 γ x hx]
    · rw [map_hd _ _ u k (fun y hy => (hz y hy).symm) x hx, h3 x hx, map_zero]
  | succ q ih =>
    rintro k n u c e - - ⟨b, hb1, -, hz⟩
    exact ih (k + 1) n (hd b) c (by omega) (hequiv_hd _ _ _ hb1) (fun x _ => hd_hd x b) hz

private theorem zig_closed (hc : Convex ℝ G.Y) (hn : G.Y.Nonempty) (q k : ℕ) (u : List Γ → G.Om q) c
    (hz : Zig G q k u c) (x : List Γ) (hx : x.length = k + 1) : G.dOm q (u x) = 0 := by
  cases q with
  | zero => exact ((inclFacts Γ V S d G hc hn).2.2 _).2 ⟨_, (hz x hx).symm⟩
  | succ q =>
    obtain ⟨b, -, hb, -⟩ := hz
    exact (dExact Γ V S d G hc q _).2 ⟨_, hb x hx⟩

omit [FiniteDimensional ℝ V] in
private theorem zig_lin (s t : ℂ) (q : ℕ) : ∀ (k : ℕ) (u u' : List Γ → G.Om q) c c',
    Zig G q k u c → Zig G q k u' c' → Zig G q k (s • u + t • u') (s • c + t • c') := by
  induction q with
  | zero =>
    intro k u u' c c' h h' x hx
    simp only [Pi.add_apply, Pi.smul_apply, h x hx, h' x hx]
    rw [← map_smul, ← map_smul, ← map_add (f := _)]
  | succ q ih =>
    rintro k u u' c c' ⟨b, h1, h2, h3⟩ ⟨b', h1', h2', h3'⟩
    refine ⟨s • b + t • b', fun γ x hx => ?_, fun x hx => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, map_add (f := _), map_smul, h1 γ x hx, h1' γ x hx]
    · simp only [Pi.add_apply, Pi.smul_apply, map_add (f := _), map_smul, h2 x hx, h2' x hx]
    · rw [hd_lin]
      exact ih _ _ _ _ _ h3 h3'

end Zig

private theorem hd_const {Γ M : Type} [AddCommGroup M] (w : M) (x : List Γ) (hx : x.length = 0 + 2) :
    hd (fun _ => w) x = 0 := by
  simp [hd, hx, Finset.sum_range_succ]

end UpperTheory.V.Lit.Geo

open UpperTheory.V.Lit.Dr in
theorem UpperTheory.V.Lit.Geo.perEx :
    PerEx := by
  intro E _ _ _ a U Ξ q
  have hc := (coneConvex E a).1
  have hn : (cone E a).Nonempty := ⟨_, hOne_mem_cone⟩
  refine ⟨fun α hα h0 => ?_, ?_, ?_⟩
  · have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
      obtain ⟨τ, -, hτ⟩ := locSec E a p hp
      exact hτ.mono fun x hx => ⟨τ x, hx⟩
    have hv : ∀ X, LeftInv (α X) ∧ RightInv U (α X) := fun X => (levelVal E a U Ξ _).1 (hα.val X)
    obtain ⟨w, hw, hw0⟩ := corrFwd E a U Ξ q α hα.equiv fun X => (hv X).2
    let w' : (geo ho U Ξ).Om q := ⟨w, fun s => ⟨corrSmooth E a U Ξ q _ w hw s, hw0 s⟩⟩
    have hw' : Corr U Ξ α w'.1 := hw
    have h := corrD E a ho U Ξ q _ _ hw'
    rw [h0] at h
    obtain ⟨c, hz⟩ := zig_ex (geo ho U Ξ) hc hn q 0 (fun _ => w')
      (fun γ _ _ => ((corrInv E a ho U Ξ q _ _ hw').1 (fun X => (hv X).1) γ).symm)
      (fun _ _ => (corrUniq E a ho U Ξ (q + 1)).2 0 _ 0 h (corr_zero U Ξ)) (hd_const w')
    exact ⟨c, ho, w', hw', hz⟩
  · rintro α c hα ⟨ho, w, hw, hz⟩
    have hv : ∀ X, LeftInv (α X) := fun X => ((levelVal E a U Ξ _).1 (hα.val X)).1
    constructor
    · have h := corrD E a ho U Ξ q _ _ hw
      rw [zig_closed (geo ho U Ξ) hc hn q 0 _ c hz [1] rfl] at h
      exact (corrUniq E a ho U Ξ (q + 1)).1 _ 0 _ h (corr_zero U Ξ)
    · rw [← geo_lev ho U Ξ]
      exact zig_coc (geo ho U Ξ) hc hn q 0 q _ c (zero_add q)
        (fun γ _ _ => ((corrInv E a ho U Ξ q _ _ hw).1 hv γ).symm) (hd_const w) hz
  · rintro α β c c' s t ⟨ho, w, hw, hz⟩ ⟨ho', w', hw', hz'⟩
    refine ⟨ho, s • w + t • w', ?_, zig_lin (geo ho U Ξ) s t q 0 _ _ _ _ hz hz'⟩
    have h := corr_sum U Ξ ![s, t] (α := ![α, β]) (w := ![w.1, w'.1]) (Fin.forall_fin_two.2 ⟨hw, hw'⟩)
    rw [Fin.sum_univ_two, Fin.sum_univ_two] at h
    exact h
end
