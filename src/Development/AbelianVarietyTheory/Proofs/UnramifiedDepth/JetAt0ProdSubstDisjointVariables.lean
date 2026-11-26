module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetAt0ProdRename
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CoeffSingleLawAdd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.IntegralFamilyFirstZeroSecond
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AddCurveStableOfIntegralGaugedFormalGroupLaw
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetAt0ProdSubstDisjointVariables
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetAt0ProdSubstDisjointVariables
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.JetProdSubst

theorem jetAt0_prod_subst : ∀ (C : Type) [Field C] (Orb : Type) [Fintype Orb] (σ : Orb → Type) [∀ o, Fintype (σ o)] (τ : Type) (e : ∀ o, σ o → τ), Function.Injective (fun x : (Σ o, σ o) => e x.1 x.2) → ∀ (P : ∀ o, MvPolynomial (σ o) C) (F : ∀ o, MvPowerSeries (σ o) C), jetAt0 (∏ o, MvPolynomial.rename (e o) (P o)) (∏ o, MvPowerSeries.subst (fun x : σ o => (MvPowerSeries.X (e o x) : MvPowerSeries τ C)) (F o)) = ∏ o, jetAt0 (P o) (F o) := by
  intro C _ Orb _ σ _ τ e he P F
  let e' : ∀ o, σ o ↪ τ := fun o => ⟨e o, fun x y h => by
    have h1 : (⟨o, x⟩ : Σ o, σ o) = ⟨o, y⟩ := he h
    simpa using h1⟩
  have hd : ∀ i j x y, e' i x = e' j y → i = j := fun i j x y h =>
    congrArg Sigma.fst (he (a₁ := ⟨i, x⟩) (a₂ := ⟨j, y⟩) h)
  rw [← GlobalTheory.JetProd.jetAt0_prod_rename e' hd]
  congr 1
  refine Finset.prod_congr rfl fun o _ => ?_
  rw [MvPowerSeries.rename_eq_subst]
  rfl

end GlobalTheory.JetProdSubst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetAt0ProdSubstDisjointVariablesStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetAt0_prod_subst_disjoint_variables : ∀ (C : Type) [Field C] (Orb : Type) [Fintype Orb] (σ : Orb → Type) [∀ o, Fintype (σ o)] (τ : Type) (e : ∀ o, σ o → τ), Function.Injective (fun x : (Σ o, σ o) => e x.1 x.2) → ∀ (P : ∀ o, MvPolynomial (σ o) C) (F : ∀ o, MvPowerSeries (σ o) C), jetAt0 (∏ o, MvPolynomial.rename (e o) (P o)) (∏ o, MvPowerSeries.subst (fun x : σ o => (MvPowerSeries.X (e o x) : MvPowerSeries τ C)) (F o)) = ∏ o, jetAt0 (P o) (F o) := by
  first | exact @GlobalTheory.JetProdSubst.jetAt0_prod_subst | exact GlobalTheory.JetProdSubst.jetAt0_prod_subst | (intros; apply GlobalTheory.JetProdSubst.jetAt0_prod_subst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PderivCoeffOptionEquivLeft
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open MvPowerSeries Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace GlobalTheory.CurveJet

variable {C : Type} [Field C] {dd m : ℕ}

def inT (σ : Type) (f : PowerSeries C) : MvPowerSeries (Option σ) C :=
  MvPowerSeries.subst (fun _ : Unit => (X none : MvPowerSeries (Option σ) C)) f

theorem inT_eq_rename (σ : Type) (f : PowerSeries C) :
    inT σ f = rename (fun _ : Unit => (none : Option σ)) f := by
  rw [inT, rename_eq_subst]
  rfl

theorem constantCoeff_inT (σ : Type) {f : PowerSeries C} (hf : PowerSeries.constantCoeff f = 0) :
    constantCoeff (inT σ f) = 0 := by
  rw [inT_eq_rename, constantCoeff_rename]
  exact hf

theorem optionEquivLeft_inT (σ : Type) (f : PowerSeries C) :
    optionEquivLeft σ C (inT σ f) = PowerSeries.map (MvPowerSeries.C : C →+* MvPowerSeries σ C) f := by
  classical
  ext n μ
  rw [coeff_coeff_optionEquivLeft, PowerSeries.coeff_map, coeff_C, inT_eq_rename]
  split_ifs with hμ
  · subst hμ
    let e : Unit ↪ Option σ := ⟨fun _ => none, fun _ _ _ => rfl⟩
    have he : Finsupp.optionElim n (0 : σ →₀ ℕ) = Finsupp.embDomain e (Finsupp.single () n) := by
      rw [Finsupp.embDomain_single, Finsupp.optionElim_zero]
      rfl
    rw [he]
    exact coeff_embDomain_rename e f (Finsupp.single () n)
  · apply coeff_rename_eq_zero
    rintro ⟨y, hy⟩
    apply hμ
    ext s
    have h1 : Finsupp.mapDomain (fun _ : Unit => (none : Option σ)) y (some s) = 0 :=
      Finsupp.mapDomain_of_notMem_range _ _ (by simp)
    rw [hy, Finsupp.optionElim_apply_some] at h1
    simpa using h1

theorem optionEquivLeft_rename_some {σ : Type} [Finite σ] (f : MvPowerSeries σ C) :
    optionEquivLeft σ C (rename (some : σ → Option σ) f) = PowerSeries.C f := by
  ext n μ
  rw [coeff_coeff_optionEquivLeft, PowerSeries.coeff_C]
  split_ifs with hn
  · subst hn
    have he : Finsupp.optionElim 0 μ = Finsupp.embDomain (Function.Embedding.some) μ := by
      ext t
      cases t <;> simp
    rw [he]
    exact coeff_embDomain_rename _ f μ
  · rw [map_zero]
    apply coeff_rename_eq_zero
    rintro ⟨y, hy⟩
    apply hn
    have h1 : Finsupp.mapDomain (some : σ → Option σ) y none = 0 :=
      Finsupp.mapDomain_of_notMem_range _ _ (by simp)
    rw [hy, Finsupp.optionElim_apply_none] at h1
    exact h1

theorem pderiv_coeff_optionEquivLeft {σ : Type} (f : MvPowerSeries (Option σ) C) (n : ℕ) (s : σ) :
    pderiv s (PowerSeries.coeff n (optionEquivLeft σ C f)) =
      PowerSeries.coeff n (optionEquivLeft σ C (pderiv (some s) f)) := by
  classical
  ext μ
  rw [coeff_pderiv, coeff_coeff_optionEquivLeft, coeff_coeff_optionEquivLeft, coeff_pderiv]
  have key : Finsupp.optionElim n (μ + Finsupp.single s 1) =
      Finsupp.optionElim n μ + Finsupp.single (some s) 1 := by
    ext t
    cases t <;> simp [Finsupp.single_apply]
  rw [key, Finsupp.optionElim_apply_some]

end GlobalTheory.CurveJet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AdmissibleRowsValueEqRowGauge
section -- merged from Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.ValOfKindIndep
noncomputable section
open scoped BigOperators
open Classical

namespace GlobalTheory.RowValueCheck

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

def Agree {σ : Type} (S : Set σ) (F F' : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, (∀ x, μ x ≠ 0 → x ∈ S) → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ F'

theorem Agree.mul {σ : Type} {S : Set σ} {F F' K K' : MvPowerSeries σ C} (h : Agree S F F')
    (h' : Agree S K K') : Agree S (F * K) (F' * K') := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have e : p.1 + p.2 = μ := by simpa using hp
  rw [h p.1 fun x hx => hμ x (by rw [← e]; simp; omega),
    h' p.2 fun x hx => hμ x (by rw [← e]; simp; omega)]

theorem Agree.pow {σ : Type} {S : Set σ} {F F' : MvPowerSeries σ C} (h : Agree S F F') (k : ℕ) :
    Agree S (F ^ k) (F' ^ k) := by
  induction k with
  | zero => intro μ _; simp
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem Agree.exp {σ : Type} {S : Set σ} {F F' : MvPowerSeries σ C} (h : Agree S F F') :
    Agree S (mvExp F) (mvExp F') := by
  intro μ hμ
  show (∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (F ^ k) / (k.factorial : C)) =
    ∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (F' ^ k) / (k.factorial : C)
  exact Finset.sum_congr rfl fun k _ => by rw [h.pow k μ hμ]

theorem Agree.prod {σ α : Type} {S : Set σ} (s : Finset α) {F F' : α → MvPowerSeries σ C}
    (h : ∀ i, Agree S (F i) (F' i)) : Agree S (∏ i ∈ s, F i) (∏ i ∈ s, F' i) := by
  induction s using Finset.induction_on with
  | empty => intro μ _; simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha]; exact (h a).mul ih

theorem agree_rowCopy {N : ℕ} (S : Set (Fin N × WV I)) (ρ : Fin N) (F F' : MvPowerSeries (WV I) C)
    (h : Agree {w | (ρ, w) ∈ S} F F') : Agree S (rowCopy ρ F) (rowCopy ρ F') := by
  intro μ hμ
  have hs : MvPowerSeries.HasSubst
      (fun w : WV I => (MvPowerSeries.X (ρ, w) : MvPowerSeries (Fin N × WV I) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by simp)
  unfold rowCopy
  rw [MvPowerSeries.coeff_subst hs, MvPowerSeries.coeff_subst hs]
  refine finsum_congr fun e => ?_
  by_cases he : ∀ x, e x ≠ 0 → (ρ, x) ∈ S
  · rw [h e he]
  · push Not at he
    obtain ⟨x, hx, hxS⟩ := he
    have h0 : μ (ρ, x) = 0 := by
      by_contra h1
      exact hxS (hμ _ h1)
    have hd : (MvPowerSeries.X (ρ, x) : MvPowerSeries (Fin N × WV I) C) ∣
        e.prod fun s k => (MvPowerSeries.X (ρ, s) : MvPowerSeries (Fin N × WV I) C) ^ k :=
      (dvd_pow_self _ hx).trans (Finset.dvd_prod_of_mem
        (fun s => (MvPowerSeries.X (ρ, s) : MvPowerSeries (Fin N × WV I) C) ^ e s)
        (Finsupp.mem_support_iff.2 hx))
    rw [MvPowerSeries.X_dvd_iff.1 hd μ h0]
    simp

def hOf (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) :
    Option (Fin 2 × ZMod d × ZMod d) → MvPowerSeries (WV I) C
  | some (g, a, a') => hL g a a'
  | none => 0

theorem valOf_eq (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) {N : ℕ}
    (P : MvPolynomial (Fin N × WV I) C) (kind : Fin N → Option (Fin 2 × ZMod d × ZMod d))
    (gr : Fin N → MvPowerSeries (WV I) C) :
    ValOf hL P kind gr =
      jetAt0 P (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ (hOf hL (kind ρ))))) := by
  unfold ValOf
  congr 1

end GlobalTheory.RowValueCheck
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AdmissibleRowsValueEqRowGauge
noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowVal

open GlobalTheory.RowValueCheck

theorem valOf_eq_hRow : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ) (H : X.Hyps V) (N : ℕ) (P : MvPolynomial (Fin N × WV I) C) (kind : Fin N → Option (Fin 2 × ZMod d × ZMod d)), RowsOK (X.rowData H).G (X.rowData H).Alt P kind → ∀ gr : Fin N → MvPowerSeries (WV I) C, ValOf (X.rowData H).hL P kind gr = jetAt0 P (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ X.hRow))) := by
  intro C _ V d _ I _ κ _ X H N P kind hk gr
  classical
  rw [valOf_eq]
  set S : Set (Fin N × WV I) := {x | ∃ μ ∈ P.support, μ x ≠ 0} with hS
  have key : ∀ ρ, Agree {w | (ρ, w) ∈ S} (hOf (X.rowData H).hL (kind ρ)) X.hRow := by
    intro ρ μ hμ
    rcases hr : kind ρ with _ | ⟨g, a, a'⟩
    · obtain ⟨g, hg⟩ := hk.2 ρ hr
      have h1 : ∀ w, μ w ≠ 0 → w.1 = g := fun w hw => by
        obtain ⟨ν, hν, hν'⟩ := hμ w hw
        exact hg ν hν w hν'
      show (0 : C) = _
      refine (H.axes μ ?_).symm
      have hg2 : g = 0 ∨ g = 1 := (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) g
      rcases hg2 with rfl | rfl
      · exact Or.inl fun w hw => h1 w (Finsupp.mem_support_iff.1 hw)
      · exact Or.inr fun w hw => h1 w (Finsupp.mem_support_iff.1 hw)
    · obtain ⟨-, -, hl⟩ := hk.1 ρ g a a' hr
      have h1 : ∀ w, μ w ≠ 0 → X.OnLf g a a' w := fun w hw => by
        obtain ⟨ν, hν, hν'⟩ := hμ w hw
        exact hl ν hν w hν'
      exact if_pos fun w hw => h1 w (Finsupp.mem_support_iff.1 hw)
  have hA := Agree.prod (S := S) Finset.univ (fun ρ =>
    Agree.mul (F := rowCopy ρ (gr ρ)) (F' := rowCopy ρ (gr ρ)) (fun _ _ => rfl)
      (agree_rowCopy S ρ _ _ (key ρ)).exp)
  unfold jetAt0
  exact Finset.sum_congr rfl fun μ hμ => by rw [hA μ fun x hx => ⟨μ, hμ, hx⟩]

end GlobalTheory.RowVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AdmissibleRowsValueEqRowGaugeStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleRows_value_eq_rowGauge : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ) (H : X.Hyps V) (N : ℕ) (P : MvPolynomial (Fin N × WV I) C) (kind : Fin N → Option (Fin 2 × ZMod d × ZMod d)), RowsOK (X.rowData H).G (X.rowData H).Alt P kind → ∀ gr : Fin N → MvPowerSeries (WV I) C, ValOf (X.rowData H).hL P kind gr = jetAt0 P (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ X.hRow))) := by
  first | exact @GlobalTheory.RowVal.valOf_eq_hRow | exact GlobalTheory.RowVal.valOf_eq_hRow | (intros; apply GlobalTheory.RowVal.valOf_eq_hRow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantDerivationsConstantInLogCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantDerivationsConstantInLogCoordinates
noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.InvDerivLog

open MvPowerSeries GlobalTheory.RowLawSquare ReciprocityTheory.ChartRestriction.G.TB.LogPf

variable {C : Type} [Field C] {dd : ℕ} {τ : Type}

open scoped MvPowerSeries.WithPiTopology in
private theorem pderiv_subst_of_zero_constantCoeff {σ : Type} [Fintype σ]
    {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries σ C) (t : τ) :
    pderiv t (subst a f) = ∑ s, subst a (pderiv s f) * pderiv t (a s) := by
  let : UniformSpace C := ⊥
  let : DiscreteUniformity C := ⟨rfl⟩
  have hsubst : Continuous (subst a : MvPowerSeries σ C → MvPowerSeries τ C) :=
    continuous_subst (hasSubst_of_constantCoeff_zero ha)
  have hderiv {ι : Type} (i : ι) :
      Continuous (pderiv (R := C) i : MvPowerSeries ι C → MvPowerSeries ι C) := by
    apply continuous_pi
    intro d
    change Continuous (fun g : MvPowerSeries ι C => coeff d (pderiv i g))
    simp only [coeff_pderiv]
    exact (WithPiTopology.continuous_coeff C _).mul continuous_const
  refine WithPiTopology.denseRange_toMvPowerSeries.induction_on f
    (isClosed_eq ((hderiv t).comp hsubst) (continuous_finsetSum _ fun s _ =>
      (hsubst.comp (hderiv s)).mul continuous_const)) ?_
  intro p
  simpa only [pderiv_coe, subst_coe] using Formalism.G.LogCR.pderiv_aeval p a t

theorem pderiv_substPointsPowerSeries_one {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) (f : PS C 1 dd) (t : τ) :
    pderiv (R := C) t (sb ![a] f) = ∑ l, sb ![a] (pderiv (R := C) ((0 : Fin 1), l) f) * pderiv (R := C) t (a l) := by
  unfold sb
  rw [pderiv_subst_of_zero_constantCoeff (fun p : Fin 1 × Fin dd => zc1 ha p.1 p.2),
    Fintype.sum_prod_type, Fin.sum_univ_one]
  rfl

theorem pderiv_substPointsPowerSeries_two {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) (f : PS C 2 dd) (t : τ) :
    pderiv (R := C) t (sb ![a, b] f) = ∑ l, sb ![a, b] (pderiv (R := C) ((0 : Fin 2), l) f) * pderiv (R := C) t (a l) +
      ∑ l, sb ![a, b] (pderiv (R := C) ((1 : Fin 2), l) f) * pderiv (R := C) t (b l) := by
  unfold sb
  rw [pderiv_subst_of_zero_constantCoeff (fun p : Fin 2 × Fin dd => zc2 ha hb p.1 p.2),
    Fintype.sum_prod_type, Fin.sum_univ_two]
  rfl

theorem sb_mul {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) (f g : PS C n dd) :
    sb a (f * g) = sb a f * sb a g := subst_mul (hasSubst_sb ha) f g

theorem sb_sum {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) {α : Type} (s : Finset α)
    (f : α → PS C n dd) : sb a (∑ x ∈ s, f x) = ∑ x ∈ s, sb a (f x) := by
  unfold sb
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← coe_substAlgHom (hasSubst_sb ha), map_sum]

theorem sb_zero {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) :
    sb a (0 : PS C n dd) = 0 := by
  unfold sb
  simp only [← coe_substAlgHom (hasSubst_sb ha), map_zero]

theorem sb_C {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (c : C) :
    sb a (MvPowerSeries.C c : PS C n dd) = MvPowerSeries.C c := by
  unfold sb
  rw [subst_C]

theorem zc_zero : Zc (0 : Fin dd → MvPowerSeries τ C) := fun _ => map_zero _

theorem sb_zeroPt (f : PS C 1 dd) :
    sb ![(0 : Fin dd → MvPowerSeries τ C)] f = MvPowerSeries.C (constantCoeff f) := by
  classical
  have hz := hasSubst_sb (zc1 (zc_zero (C := C) (dd := dd) (τ := τ)))
  ext e
  unfold sb
  rw [coeff_subst hz, finsum_eq_single _ 0]
  · simp [coeff_C, coeff_one]
  · intro x hx
    obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
      by_contra hc; push Not at hc; exact hx (Finsupp.ext hc)
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hp), map_zero, smul_zero]
    obtain ⟨j, i⟩ := p
    fin_cases j
    exact zero_pow hp

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd)

theorem zc_ex {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) : Zc (fun x => sb ![a] (Y.ex x)) :=
  fun x => cc_sb (zc1 ha) (Y.ex_const x)

theorem law_ex {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) (j : Fin dd) :
    sb ![fun x => sb ![a] (Y.ex x), fun x => sb ![b] (Y.ex x)] (Y.B.G.F j) = sb ![a + b] (Y.ex j) := by
  have h1 := ex_lg Y (zc_law Y (zc_ex Y ha) (zc_ex Y hb)) j
  simp only [← lg_law Y (zc_ex Y ha) (zc_ex Y hb), lg_ex Y ha, lg_ex Y hb] at h1
  exact h1.symm

theorem cc_pderiv_lg (i l : Fin dd) :
    constantCoeff (pderiv (R := C) ((0 : Fin 1), i) (Y.lg l)) = if l = i then 1 else 0 := by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, Y.lg_lin l _ (by simp), coeff_X]
  by_cases h : l = i
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right, zero_mul]
    intro h2
    rw [zero_add, Finsupp.single_left_inj one_ne_zero] at h2
    exact h (Prod.ext_iff.1 h2).2.symm

theorem cc_pderiv_ex (i l : Fin dd) :
    constantCoeff (pderiv (R := C) ((0 : Fin 1), i) (Y.ex l)) = if l = i then 1 else 0 := by
  classical
  have e : sb ![Y.ex] (Y.lg l) = X ((0 : Fin 1), l) := congrFun Y.lg_ex l
  have e2 := congrArg (fun f => constantCoeff (pderiv (R := C) ((0 : Fin 1), i) f)) e
  have hz : Zc Y.ex := Y.ex_const
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pderiv_substPointsPowerSeries_one hz, map_sum, map_mul] at e2
  have h3 : ∀ x, constantCoeff (sb ![Y.ex] (pderiv (R := C) ((0 : Fin 1), x) (Y.lg l))) = if l = x then 1 else 0 :=
    fun x => by
      unfold sb
      rw [cc_subst (fun p : Fin 1 × Fin dd => zc1 hz p.1 p.2), cc_pderiv_lg]
  simp only [h3, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at e2
  rw [e2]
  by_cases h : l = i
  · subst h; simp
  · rw [ite_eq_right h, pderiv_X_of_ne (by simpa using h), map_zero]

theorem inv_field_ex {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) (i j : Fin dd) :
    sb ![fun x => sb ![a] (Y.ex x), 0] (pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F j)) =
      sb ![a] (pderiv (R := C) ((0 : Fin 1), i) (Y.ex j)) := by
  classical
  have z0 : Zc (pt C (n := 2) dd 0) := zc_pt 0
  have z1 : Zc (pt C (n := 2) dd 1) := zc_pt 1
  have zs : Zc (pt C (n := 2) dd 0 + pt C (n := 2) dd 1) := fun x => by
    rw [Pi.add_apply, map_add (f := _), z0 x, z1 x, add_zero]
  have d0 : ∀ l, pderiv (R := C) ((1 : Fin 2), i) (pt C (n := 2) dd 0 l) = 0 := fun l =>
    pderiv_X_of_ne (by simp)
  have d1 : ∀ l, pderiv (R := C) ((1 : Fin 2), i) (pt C (n := 2) dd 1 l) = if l = i then 1 else 0 := fun l => by
    by_cases h : l = i
    · subst h; rw [ite_eq_left rfl]; exact pderiv_X_self
    · rw [ite_eq_right h]; exact pderiv_X_of_ne (by simpa using h)
  have e := congrArg (pderiv (R := C) ((1 : Fin 2), i)) (law_ex Y z0 z1 j)
  rw [pderiv_substPointsPowerSeries_two (zc_ex Y z0) (zc_ex Y z1), pderiv_substPointsPowerSeries_one zs] at e
  simp only [pderiv_substPointsPowerSeries_one z0, pderiv_substPointsPowerSeries_one z1, Pi.add_apply, map_add (f := _), d0, d1, mul_zero, Finset.sum_const_zero,
    zero_add, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at e
  have h2 := zc2 ha (zc_zero (C := C) (dd := dd) (τ := τ))
  have s1 : ∀ {b : Pt C 2 dd} (_ : Zc b) (f : PS C 1 dd),
      sb ![a, 0] (sb ![b] f) = sb ![fun i => sb ![a, 0] (b i)] f := fun hb f => substPointsPowerSeries_eval_one h2 hb f
  have s2 : ∀ {b c : Pt C 2 dd} (_ : Zc b) (_ : Zc c) (f : PS C 2 dd),
      sb ![a, 0] (sb ![b, c] f) = sb ![fun i => sb ![a, 0] (b i), fun i => sb ![a, 0] (c i)] f :=
    fun hb hc f => substPointsPowerSeries_eval_two h2 hb hc f
  have e2 := congrArg (sb ![a, 0]) e
  have p0 : (fun i => sb ![a, 0] (pt C dd 0 i)) = a := sb_pt' h2 0
  have p1 : (fun i => sb ![a, 0] (pt C dd 1 i)) = 0 := sb_pt' h2 1
  have ps : (fun i => sb ![a, 0] ((pt C (n := 2) dd 0 + pt C (n := 2) dd 1) i)) = a := by
    funext x
    rw [Pi.add_apply, sb_add h2, congrFun p0 x, congrFun p1 x, Pi.zero_apply, add_zero]
  have c0 : (fun x => (MvPowerSeries.C (constantCoeff (Y.ex x)) : MvPowerSeries τ C)) = 0 := by
    funext x
    rw [Y.ex_const, map_zero, Pi.zero_apply]
  rw [sb_sum h2, s1 zs, ps] at e2
  simp only [sb_mul h2, s2 (zc_ex Y z0) (zc_ex Y z1), s1 z0, s1 z1, p0, p1, sb_zeroPt, c0, cc_pderiv_ex,
    apply_ite MvPowerSeries.C, map_one, map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at e2
  exact e2

theorem subst_ex_DofN : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (n : ℕ) (W : Type) [Fintype W] (Z : Fin n × Fin dd → MvPowerSeries W C), (∀ s, MvPowerSeries.constantCoeff (Z s) = 0) → ∀ (b : Fin n) (u : Fin dd → C) (co : W → C), (∀ (b' : Fin n) (j : Fin dd), ∑ w, co w • MvPowerSeries.pderiv (R := C) w (Z (b', j)) = if b' = b then MvPowerSeries.C (u j) else 0) → ∀ G : PS C n dd, MvPowerSeries.subst (fun s : Fin n × Fin dd => MvPowerSeries.subst (fun j : Fin dd => Z (s.1, j)) (un1 (Y.ex s.2))) (DofN (Y.B.FK C) b u G) = ∑ w, co w • MvPowerSeries.pderiv (R := C) w (MvPowerSeries.subst (fun s : Fin n × Fin dd => MvPowerSeries.subst (fun j : Fin dd => Z (s.1, j)) (un1 (Y.ex s.2))) G) := by
  classical
  intro C _ _ V O _ _ dd Y n W _ Z hZ b u co hco G
  have hz : ∀ b' : Fin n, Zc (fun j => Z (b', j)) := fun b' j => hZ _
  let E : Fin n → Fin dd → MvPowerSeries W C := fun b' x => sb ![fun j => Z (b', j)] (Y.ex x)
  have hE : ∀ b', Zc (E b') := fun b' => zc_ex Y (hz b')
  have eE : (fun s : Fin n × Fin dd => subst (fun j : Fin dd => Z (s.1, j)) (un1 (Y.ex s.2))) =
      fun s => E s.1 s.2 := by
    funext s
    rw [RowLawSquare.subst_singlePointUncurry (hz s.1)]
    show _ = sb _ _
    unfold sb
    congr 1
    funext ⟨j, i⟩
    fin_cases j
    rfl
  rw [eE]
  show sb E _ = ∑ w, co w • pderiv (R := C) w (sb E G)
  have hD : ∀ (b' : Fin n) (j : Fin dd), ∑ w, co w • pderiv (R := C) w (E b' j) = if b' = b then
      ∑ i, MvPowerSeries.C (u i) * sb ![fun j => Z (b, j)] (pderiv (R := C) ((0 : Fin 1), i) (Y.ex j)) else 0 := by
    intro b' j
    simp only [E, pderiv_substPointsPowerSeries_one (hz b'), Finset.smul_sum, ← mul_smul_comm]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hco]
    split_ifs with h
    · subst h
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · simp
  have hR : ∑ w, co w • pderiv (R := C) w (sb E G) =
      ∑ p : Fin n × Fin dd, sb E (pderiv (R := C) p G) * ∑ w, co w • pderiv (R := C) w (E p.1 p.2) := by
    unfold sb
    simp only [pderiv_subst_of_zero_constantCoeff (a := fun p : Fin n × Fin dd => E p.1 p.2)
      (fun p => hE p.1 p.2), Finset.smul_sum, ← mul_smul_comm, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hR, Fintype.sum_prod_type, Finset.sum_eq_single b]
  · unfold DofN
    rw [sb_sum hE]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hD, ite_eq_left rfl, sb_mul hE, mul_comm, sb_sum hE]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sb_mul hE, sb_C, substPointsPowerSeries_eval_two hE (zc_pt b) zc_zero, sb_pt' hE, FK_self, ← inv_field_ex Y (hz b)]
    have : (fun i : Fin dd => sb E ((0 : Pt C n dd) i)) = 0 := funext fun _ => sb_zero hE
    rw [this]
  · intro b' _ h
    simp [hD, h]
  · simp

end GlobalTheory.InvDerivLog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantDerivationsConstantInLogCoordinatesStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantDerivations_constant_in_logCoordinates : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (n : ℕ) (W : Type) [Fintype W] (Z : Fin n × Fin dd → MvPowerSeries W C), (∀ s, MvPowerSeries.constantCoeff (Z s) = 0) → ∀ (b : Fin n) (u : Fin dd → C) (co : W → C), (∀ (b' : Fin n) (j : Fin dd), ∑ w, co w • MvPowerSeries.pderiv (R := C) w (Z (b', j)) = if b' = b then MvPowerSeries.C (u j) else 0) → ∀ G : PS C n dd, MvPowerSeries.subst (fun s : Fin n × Fin dd => MvPowerSeries.subst (fun j : Fin dd => Z (s.1, j)) (un1 (Y.ex s.2))) (DofN (Y.B.FK C) b u G) = ∑ w, co w • MvPowerSeries.pderiv (R := C) w (MvPowerSeries.subst (fun s : Fin n × Fin dd => MvPowerSeries.subst (fun j : Fin dd => Z (s.1, j)) (un1 (Y.ex s.2))) G) := by
  first | exact @GlobalTheory.InvDerivLog.subst_ex_DofN | exact GlobalTheory.InvDerivLog.subst_ex_DofN | (intros; apply GlobalTheory.InvDerivLog.subst_ex_DofN <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupCurveLogarithmsAddSubgroupResca
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupCurveLogarithmsAddSubgroupResca
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

noncomputable section

namespace GlobalTheory.RowLaw.CvGroup

variable {C : Type} [Field C]

theorem alongCv_congr {σ : Type} [Finite σ] {a b : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, PowerSeries.constantCoeff (b i) = 0) {n : ℕ}
    (hab : ∀ i, ∀ m < n, PowerSeries.coeff m (a i) = PowerSeries.coeff m (b i)) (f : MvPowerSeries σ C)
    (m : ℕ) (hm : m < n) :
    PowerSeries.coeff m (alongCv a f) = PowerSeries.coeff m (alongCv b f) := by
  unfold alongCv
  show MvPowerSeries.coeff (Finsupp.single () m) _ = MvPowerSeries.coeff (Finsupp.single () m) _
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha),
    MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hb)]
  refine finsum_congr fun e => ?_
  congr 1
  set J : Ideal (PowerSeries C) := Ideal.span {(PowerSeries.X : PowerSeries C) ^ n} with hJ
  have hq : ∀ i, Ideal.Quotient.mk J (a i) = Ideal.Quotient.mk J (b i) := by
    intro i
    rw [Ideal.Quotient.eq, hJ, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro k hk
    rw [map_sub, hab i k hk, sub_self]
  have hp : Ideal.Quotient.mk J (e.prod fun s k => a s ^ k) = Ideal.Quotient.mk J (e.prod fun s k => b s ^ k) := by
    unfold Finsupp.prod
    rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow, map_pow, hq]
  rw [Ideal.Quotient.eq, hJ, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at hp
  have := hp m hm
  rw [map_sub, sub_eq_zero] at this
  exact this

theorem alongCv_low {σ : Type} [Finite σ] {a : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) {n : ℕ}
    (hab : ∀ i, ∀ m < n, PowerSeries.coeff m (a i) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) (m : ℕ) (hm : m < n) :
    PowerSeries.coeff m (alongCv a f) = 0 := by
  rw [alongCv_congr (b := fun _ => 0) ha (fun _ => map_zero _) (fun i k hk => by rw [hab i k hk, map_zero]) f m hm,
    alongCv_zero hf, map_zero]

theorem constantCoeff_alongCv {σ : Type} [Finite σ] {a : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) : PowerSeries.constantCoeff (alongCv a f) = 0 :=
  constantCoeff_subst_zero (τ := Unit) ha hf

theorem alongCv_comp {σ : Type} [Finite σ] {a : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) {p : σ → MvPowerSeries σ C}
    (hp : ∀ i, MvPowerSeries.constantCoeff (p i) = 0) (f : MvPowerSeries σ C) :
    alongCv (fun i => alongCv a (p i)) f = alongCv a (MvPowerSeries.subst p f) := by
  unfold alongCv
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hp)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]

theorem alongCv_X {σ : Type} [Finite σ] {a : σ → PowerSeries C}
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (i : σ) :
    alongCv a (MvPowerSeries.X i) = a i := by
  unfold alongCv
  exact MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) i

variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {X : RawChart C d I κ}

theorem lg_const (H : RLaw X V) (i : κ) : MvPowerSeries.constantCoeff (X.lg i) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, H.lin i 0 (by simp),
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]

theorem ex_lg (H : RLaw X V) {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (i : κ) :
    alongCv (fun j => alongCv γ (X.lg j)) (X.ex i) = γ i := by
  rw [alongCv_comp hγ (lg_const H), H.exlg, alongCv_X hγ]

theorem lg_ex (H : RLaw X V) {a : κ → PowerSeries C} (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0) (i : κ) :
    alongCv (fun j => alongCv a (X.ex j)) (X.lg i) = a i := by
  rw [alongCv_comp ha H.exc, H.lgex, alongCv_X ha]

theorem coeff_lg_low (H : RLaw X V) {γ : κ → PowerSeries C} {n : ℕ} (hn : 1 ≤ n)
    (hγ : ∀ i, ∀ m < n, PowerSeries.coeff m (γ i) = 0) (i : κ) :
    PowerSeries.coeff n (alongCv γ (X.lg i)) = PowerSeries.coeff n (γ i) := by
  classical
  have hlg1 : ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) (X.lg i) = if j = i then 1 else 0 := fun j => by
    rw [H.lin i _ (by rw [Finsupp.degree_single]), MvPowerSeries.coeff_X]
    by_cases hji : j = i
    · rw [hji, if_pos rfl, if_pos rfl]
    · rw [if_neg hji, if_neg]
      intro h
      exact hji (Finsupp.single_left_injective one_ne_zero h)
  rw [coeff_alongCv_low hn hγ (lg_const H i)]
  simp only [hlg1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem approx_neg (H : RLaw X V) (hA : X.AddCvSt V) {γ : κ → PowerSeries C} (hγ : IsCv V γ) (n : ℕ) :
    ∃ δ : κ → PowerSeries C, IsCv V δ ∧
      ∀ i, ∀ m < n + 1, PowerSeries.coeff m (alongCv γ (X.lg i) + alongCv δ (X.lg i)) = 0 := by
  induction n with
  | zero =>
    refine ⟨γ, hγ, fun i m hm => ?_⟩
    have : m = 0 := by omega
    rw [this, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_add (f := _),
      constantCoeff_alongCv (fun i => (hγ i).1) (lg_const H i), add_zero]
  | succ n ih =>
    obtain ⟨δ, hδ, hlow⟩ := ih
    obtain ⟨s, hs, hL, -⟩ := hA γ δ hγ hδ
    have hs0 : ∀ i, PowerSeries.constantCoeff (s i) = 0 := fun i => (hs i).1
    have hslow : ∀ i, ∀ m < n + 1, PowerSeries.coeff m (s i) = 0 := by
      intro i m hm
      rw [← ex_lg H hs0 i]
      exact alongCv_low (fun j => constantCoeff_alongCv hs0 (lg_const H j))
        (fun j k hk => by rw [hL j]; exact hlow j k hk) (H.exc i) m hm
    have hε : IsCv V fun i => -s i := fun i =>
      ⟨by rw [map_neg, hs0, neg_zero], fun k => by rw [map_neg]; exact ((hs i).2 k).neg⟩
    have hεlow : ∀ i, ∀ m < n + 1, PowerSeries.coeff m (-s i) = 0 := fun i m hm => by
      rw [map_neg, hslow i m hm, neg_zero]
    obtain ⟨δ', hδ', hL', -⟩ := hA δ _ hδ hε
    refine ⟨δ', hδ', fun i m hm => ?_⟩
    rw [hL' i, ← add_assoc, map_add (f := _)]
    by_cases hmn : m < n + 1
    · rw [hlow i m hmn, alongCv_low (fun j => (hε j).1) hεlow (lg_const H i) m hmn, add_zero]
    · have : m = n + 1 := by omega
      rw [this, ← hL i, coeff_lg_low H (by omega) hslow, coeff_lg_low H (by omega) hεlow, map_neg, add_neg_cancel]

theorem exists_neg (H : RLaw X V) (hA : X.AddCvSt V) {γ : κ → PowerSeries C} (hγ : IsCv V γ) :
    ∃ δ : κ → PowerSeries C, IsCv V δ ∧ ∀ i, alongCv δ (X.lg i) = -alongCv γ (X.lg i) := by
  have h0 : ∀ j, PowerSeries.constantCoeff (-alongCv γ (X.lg j)) = 0 := fun j => by
    rw [map_neg, constantCoeff_alongCv (fun i => (hγ i).1) (lg_const H j), neg_zero]
  refine ⟨fun i => alongCv (fun j => -alongCv γ (X.lg j)) (X.ex i), fun i => ⟨constantCoeff_alongCv h0 (H.exc i), fun n => ?_⟩,
    lg_ex H h0⟩
  obtain ⟨δ, hδ, hlow⟩ := approx_neg H hA hγ n
  have hδ0 : ∀ i, PowerSeries.constantCoeff (δ i) = 0 := fun i => (hδ i).1
  rw [alongCv_congr (b := fun j => alongCv δ (X.lg j)) h0 (fun j => constantCoeff_alongCv hδ0 (lg_const H j))
    (n := n + 1) (fun j m hm => by
      have := hlow j m hm
      rw [map_add (f := _)] at this
      rw [map_neg]
      exact neg_eq_of_add_eq_zero_right this) _ n (Nat.lt_succ_self n), ex_lg H hδ0]
  exact (hδ i).2 n

theorem sg_const (H : RLaw X V) (v : κ → C) : MvPowerSeries.constantCoeff (X.sg v) = 0 :=
  X.constantCoeff_sg (H.axes 0) v

theorem isCv_zero {σ : Type} : IsCv V fun _ : σ => (0 : PowerSeries C) := fun _ =>
  ⟨map_zero _, fun n => by rw [map_zero]; exact VF.Ge.zero 0⟩

theorem zero_mem (H : RLaw X V) (g : Fin 2) : 0 ∈ Cv X V g :=
  ⟨fun _ => 0, fun _ => 0, isCv_zero, isCv_zero, fun i => alongCv_zero (lg_const H i), fun q => by
    rw [alongCv_zero (sg_const H _), sub_zero]; rfl⟩

theorem add_mem (H : RLaw X V) (hA : X.AddCvSt V) (g : Fin 2) :
    ∀ a ∈ Cv X V g, ∀ b ∈ Cv X V g, a + b ∈ Cv X V g := by
  rintro a ⟨γ, lam, hγ, hlam, h1, h2⟩ b ⟨γ', lam', hγ', hlam', h1', h2'⟩
  obtain ⟨γ'', hγ'', hL, hS⟩ := hA γ γ' hγ hγ'
  refine ⟨γ'', fun q => lam q + lam' q + (alongCv γ'' (X.sg (X.u (1 - g) q)) - alongCv γ (X.sg (X.u (1 - g) q)) -
    alongCv γ' (X.sg (X.u (1 - g) q))), hγ'', ?_, ?_, ?_⟩
  · intro q
    obtain ⟨c0, cI⟩ := hS (X.u (1 - g) q) (H.uint (1 - g) q)
    refine ⟨?_, fun n => ?_⟩
    · rw [map_add (f := _), map_add (f := _), (hlam q).1, (hlam' q).1, c0]
      simp
    · rw [map_add (f := _), map_add (f := _)]
      exact (((hlam q).2 n).add ((hlam' q).2 n)).add (cI n)
  · intro i
    rw [hL i, h1 i, h1' i]
    rfl
  · intro q
    show a.2 q + b.2 q = _
    rw [h2 q, h2' q]
    dsimp only
    abel

theorem neg_mem (H : RLaw X V) (hA : X.AddCvSt V) (g : Fin 2) : ∀ a ∈ Cv X V g, -a ∈ Cv X V g := by
  rintro a ⟨γ, lam, hγ, hlam, h1, h2⟩
  obtain ⟨δ, hδ, hneg⟩ := exists_neg H hA hγ
  obtain ⟨s, hs, hL, hS⟩ := hA γ δ hγ hδ
  have hs0 : s = fun _ => 0 := by
    funext i
    rw [← ex_lg H (fun j => (hs j).1) i]
    have : (fun j => alongCv s (X.lg j)) = fun _ => 0 := by
      funext j
      rw [hL j, hneg j, add_neg_cancel]
    rw [this, alongCv_zero (H.exc i)]
  refine ⟨δ, fun q => -lam q - (alongCv s (X.sg (X.u (1 - g) q)) - alongCv γ (X.sg (X.u (1 - g) q)) -
    alongCv δ (X.sg (X.u (1 - g) q))), hδ, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨c0, cI⟩ := hS (X.u (1 - g) q) (H.uint (1 - g) q)
    refine ⟨?_, fun n => ?_⟩
    · rw [map_sub, map_neg, (hlam q).1, c0]
      simp
    · rw [map_sub, map_neg]
      exact ((hlam q).2 n).neg.sub (cI n)
  · intro i
    rw [hneg i, h1 i]
    rfl
  · intro q
    show -a.2 q = _
    dsimp only
    rw [h2 q, hs0, alongCv_zero (sg_const H _)]
    abel

theorem rescale_mem (g : Fin 2) (s : C) (hs : V.Ge 0 s) : ∀ a ∈ Cv X V g,
    ((fun i => PowerSeries.rescale s (a.1 i), fun q => PowerSeries.rescale s (a.2 q)) :
      ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g := by
  rintro a ⟨γ, lam, hγ, hlam, h1, h2⟩
  have hτ : PowerSeries.constantCoeff (s • (PowerSeries.X : PowerSeries C)) = 0 := by simp
  have hcv : ∀ {σ : Type} (δ : σ → PowerSeries C), IsCv V δ → IsCv V fun i => PowerSeries.rescale s (δ i) := by
    intro σ δ hδ i
    refine ⟨?_, fun n => ?_⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, (hδ i).1, mul_zero]
    · rw [PowerSeries.coeff_rescale]
      exact (hs.pow n).mul_int ((hδ i).2 n)
  have hal : ∀ f, alongCv (fun i => PowerSeries.rescale s (γ i)) f = PowerSeries.rescale s (alongCv γ f) := by
    intro f
    simp only [PowerSeries.rescale_eq_subst]
    exact alongCv_repar (fun i => (hγ i).1) hτ f
  refine ⟨fun i => PowerSeries.rescale s (γ i), fun q => PowerSeries.rescale s (lam q), hcv γ hγ, hcv lam hlam, ?_, ?_⟩
  · intro i
    rw [hal, h1 i]
  · intro q
    show PowerSeries.rescale s (a.2 q) = _
    rw [hal, h2 q, map_sub]

end GlobalTheory.RowLaw.CvGroup

theorem GlobalTheory.RowLaw.cv_group : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, (0 ∈ Cv X V g) ∧ (∀ a ∈ Cv X V g, ∀ b ∈ Cv X V g, a + b ∈ Cv X V g) ∧ (∀ a ∈ Cv X V g, -a ∈ Cv X V g) ∧ (∀ s : C, V.Ge 0 s → ∀ a ∈ Cv X V g, ((fun i => PowerSeries.rescale s (a.1 i), fun q => PowerSeries.rescale s (a.2 q)) : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g) := by
  intro C _ V d _ I _ κ _ X H g
  have hA := GlobalTheory.T.addCurveStable_of_integralGaugedFormalGroupLaw C V d I κ X H
  exact ⟨CvGroup.zero_mem H g, CvGroup.add_mem H hA g, CvGroup.neg_mem H hA g, fun s hs => CvGroup.rescale_mem g s hs⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaugedFormalGroupCurveLogarithms_addSubgroup_rescale : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, (0 ∈ Cv X V g) ∧ (∀ a ∈ Cv X V g, ∀ b ∈ Cv X V g, a + b ∈ Cv X V g) ∧ (∀ a ∈ Cv X V g, -a ∈ Cv X V g) ∧ (∀ s : C, V.Ge 0 s → ∀ a ∈ Cv X V g, ((fun i => PowerSeries.rescale s (a.1 i), fun q => PowerSeries.rescale s (a.2 q)) : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g) := by
  first | exact @GlobalTheory.RowLaw.cv_group | exact GlobalTheory.RowLaw.cv_group | (intros; apply GlobalTheory.RowLaw.cv_group <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextPairingNondegenerateGeometricFibre
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem biext_pairing_nondegenerate_geometric_fibre :
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom → IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    ∀ (X : Scheme.{0}) (M : ReciprocityTheory.ChartRestriction.G.Semi.LB X), M.IsLB → ∀ (ψ : (G ⊗ Over.mk f).left ⟶ X)
      (σ : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb M (K := PUnit) (fun _ => (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ≫ ψ) (fun _ => 1))), σ.IsGen →
    (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ (Z : Scheme.{0}) (r : Z ⟶ (G ⊗ Over.mk f).left) (z : Z) (J : (Z ⟶ X) → M.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good M z J →
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ (r ≫ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) z J = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ r z J) → ∃ t : (M.pull ψ).Gen, t.IsGen) →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ) (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (x : Over.mk f ⟶ G), x ^ N = 1 →
    ∃ σ : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb P (K := PUnit) (fun _ => (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ≫ (lift (snd G (Over.mk f) ≫ x) (fst G (Over.mk f))).left) (fun _ => 1)), σ.IsGen ∧
      ∀ y : Over.mk f ⟶ G, y ^ N = 1 → (∀ (z : (Over.mk f).left) (J : ((Over.mk f).left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
        ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (x ^ k) (lift x y)).left z J = ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift (y ^ k) y)).left z J) →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (G ⊗ Over.mk f).left) (z : Z) (J : (Z ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ (r ≫ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) z J = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ r z J) →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P)
    (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom →
    IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    (∀ x : Over.mk f ⟶ G, (∃ t : (P.pull (lift (snd G (Over.mk f) ≫ x) (fst G (Over.mk f))).left).Gen, t.IsGen) → x = 1) →
    ∀ x : Over.mk f ⟶ G, x ^ N = 1 → (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ (z : (Over.mk f).left) (J : ((Over.mk f).left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
      ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (x ^ k) (lift x y)).left z J = ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift (y ^ k) y)).left z J) → x = 1) := by
  intro hD hS S G _ _ P β K _ _ f N hN hsm hfin hfl hsur hpr x hx hxy
  obtain ⟨σ, hσ, hinv⟩ := hS S G K f N P β x hx
  exact hpr x (hD S G K f N hN hsm hfin hfl hsur _ P β.isLB _ σ hσ
    (fun y hy => hinv y hy (hxy y hy)))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextValAxioms
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in
private theorem biextVal_pull {S : Scheme.{0}} {G : Over S} {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → ((G ⊗ G ⊗ G).left ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) {T T' : Over S} (ρ : T' ⟶ T)
    {z : T'.left} {J : (T'.left ⟶ X) → L.ι} (hJ : Good L z J) (x x' y : T ⟶ G) :
    val (LB.pullGen L φ ε t (lift x (lift x' y)).left) ρ.left z J =
      val t (lift (ρ ≫ x) (lift (ρ ≫ x') (ρ ≫ y))).left z J := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, comp_lift, comp_lift]


open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem biext_val_axioms :
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (T : Over S) (z : T.left)
    (J : (T.left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J → ∀ t₁ t₂ : (T ⟶ G) → (T ⟶ G) → (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
    (∀ x x' y, t₁ x x' y = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift x (lift x' y)).left z J) → (∀ x y y', t₂ x y y' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift y y')).left z J) →
    (∀ x x' x'' y, t₁ (x * x') x'' y * t₁ x x' y = t₁ x (x' * x'') y * t₁ x' x'' y) ∧ (∀ x x' y, t₁ x x' y = t₁ x' x y) ∧
    (∀ x y y' y'', t₂ x (y * y') y'' * t₂ x y y' = t₂ x y (y' * y'') * t₂ x y' y'') ∧ (∀ x y y', t₂ x y y' = t₂ x y' y) ∧
    (∀ x x' y y', t₁ x x' (y * y') * t₂ x y y' * t₂ x' y y' = t₂ (x * x') y y' * t₁ x x' y * t₁ x x' y')) := by
  intro S G _ _ P β T z J hJ t₁ t₂ h₁ h₂
  have a₀ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 0 = a := fun a b c d => by simp [x4]
  have a₁ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 1 = b := fun a b c d => by simp [x4]
  have a₂ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 2 = c := fun a b c d => by simp [x4]
  have a₃ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 3 = d := fun a b c d => by simp [x4]
  have b₀ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ padd G (x4 G 0) (x4 G 1) = a * b :=
    fun a b c d => (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁])
  have b₁ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ padd G (x4 G 1) (x4 G 2) = b * c :=
    fun a b c d => (MonObj.comp_mul _ _ _).trans (by rw [a₁, a₂])
  have b₂ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ padd G (x4 G 2) (x4 G 3) = c * d :=
    fun a b c d => (MonObj.comp_mul _ _ _).trans (by rw [a₂, a₃])
  have c₀ : ∀ a b c : T ⟶ G, lift a (lift b c) ≫ x3 G 0 = a := fun a b c => by simp [x3]
  have c₁ : ∀ a b c : T ⟶ G, lift a (lift b c) ≫ x3 G 1 = b := fun a b c => by simp [x3]
  have c₂ : ∀ a b c : T ⟶ G, lift a (lift b c) ≫ x3 G 2 = c := fun a b c => by simp [x3]
  simp only [h₁, h₂]
  refine ⟨fun x x' x'' y => ?_, fun x x' y => ?_, fun x y y' y'' => ?_, fun x y y' => ?_, fun x x' y y' => ?_⟩
  · have := val_corr hJ β.assoc1 (lift x (lift x' (lift x'' y))).left
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _)
      (biextVal_pull _ _ hJ _ _ _))).symm.trans (this.trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))))
    rwa [b₀, b₁, a₀, a₁, a₂, a₃] at e
  · have e := (val_corr hJ β.comm1 (lift x (lift x' y)).left).trans (biextVal_pull _ _ hJ _ _ _)
    rwa [c₀, c₁, c₂] at e
  · have := val_corr hJ β.assoc2 (lift x (lift y (lift y' y''))).left
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _)
      (biextVal_pull _ _ hJ _ _ _))).symm.trans (this.trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))))
    rwa [b₁, b₂, a₀, a₁, a₂, a₃] at e
  · have e := (val_corr hJ β.comm2 (lift x (lift y y')).left).trans (biextVal_pull _ _ hJ _ _ _)
    rwa [c₀, c₁, c₂] at e
  · have := val_corr hJ β.compat (lift x (lift x' (lift y y'))).left
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))) (biextVal_pull _ _ hJ _ _ _))).symm.trans
      (this.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))) (biextVal_pull _ _ hJ _ _ _))))
    rwa [b₀, b₂, a₀, a₁, a₂, a₃] at e

end GlobalTheory
end
