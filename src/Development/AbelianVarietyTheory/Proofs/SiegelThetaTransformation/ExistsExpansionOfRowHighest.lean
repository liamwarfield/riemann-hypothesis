module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NotIsIsoOfDefinite
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsExpansionOfRowHighest
section

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr

namespace GlobalTheory.Dict.CuspAny

theorem mem_minorSpan_of_rowHighest {T : Type} [Fintype T] {p q n : ℕ} {c : T → Fin p → ℕ}
    {c' : T → Fin q → ℕ} {P : Harm.Poly ℂ T p q (Fin n)} (hP : P ∈ Harm.rowHighest ℂ c c') :
    P ∈ GaussGauge.minorSpan (Fin n) c c' := by
  classical
  have h : p + q ≤ n + (p + q) := Nat.le_add_left _ _
  let A : Matrix (Fin n) (Fin (n + (p + q))) ℂ :=
    (1 : Matrix _ _ ℂ).submatrix (Fin.castAdd (p + q)) id
  have hA : A * Aᵀ = 1 := by
    ext i j
    simp [A, Matrix.mul_apply, Matrix.one_apply, eq_comm]
  have h1 : Harm.colSubst (fun _ : T => A) (fun _ => Aᵀ) P ∈ GaussGauge.minorSpan _ c c' :=
    GaussGauge.orbitSpan_le_minorSpan h c c'
      (Harm.rowHighest_eq_orbitSpan h c c' ℂ ▸ Harm.colSubst_mem_rowHighest (fun _ => hA) hP)
  have h2 : Harm.colSubst (fun _ : T => Aᵀ) (fun _ => A)
      (Harm.colSubst (fun _ : T => A) (fun _ => Aᵀ) P) = P := by
    rw [← AlgHom.comp_apply, Harm.colSubst_comp]
    simp only [hA]
    rw [Harm.colSubst_one, AlgHom.id_apply]
  rw [← h2]
  refine (Submodule.span_le (p := (GaussGauge.minorSpan (Fin n) c c').comap
    (Harm.colSubst (fun _ : T => Aᵀ) (fun _ => A)).toLinearMap)).2 ?_ h1
  rintro _ ⟨x, rfl⟩
  change Harm.colSubst (fun _ : T => Aᵀ) (fun _ => A) (Harm.minorProd c c' x.1 x.2) ∈
    GaussGauge.minorSpan (Fin n) c c'
  rw [Harm.colSubst_minorProd]
  exact GaussGauge.minorProd_mem_minorSpan _ _ _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {g : ℕ}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
  {q0 : ℕ} (hr : X.p0 + q0 = r) {n : ℕ} {c : X.Ψ → Fin q0 → ℕ} {c' : X.Ψ → Fin X.p0 → ℕ}

theorem exists_expansion_of_rowHighest (hs : IsSympl X bas) (hn : Even n)
    (hc : ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i)
    (a b : Fin n → Fin g → ℝ) {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)}
    (hP : P ∈ Harm.rowHighest ℂ c c') {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    ∃ (A : (Fin n → Fin g → ℤ) → ℂ) (ν : (Fin n → Fin g → ℤ) → X.Ψ → ℝ),
      (Summable fun m => ‖A m‖) ∧
      (∀ s : X.Ψ → ℝ, HasSum (fun m => A m * cexp (4 * Real.pi * I * ∑ τ, (ν m τ : ℂ) * s τ))
        (thFr X hr bas idx n a b P (X.flow ξ (fun τ => (s τ : ℂ)) x))) ∧
      ∀ m, A m ≠ 0 → ν m ≠ 0 := by
  obtain ⟨bas', S, hs', hA⟩ := exists_isAdapted hs hξ.2.1
  obtain ⟨a', b', κ, -, -, hκ⟩ := exists_thFr_eq_mul idx hr hs hs' hn a b
  obtain ⟨A, hA1, hA2, hA3⟩ := hA.exists_expansion hr idx hs' hξ n a' b'
    (Harm.isHarmonic_of_mem_rowHighest hP) (mem_minorSpan_of_rowHighest hP) hc hx
  refine ⟨fun m => κ * A m, _, ?_, fun s => ?_,
    fun m hm h0 => hm (mul_eq_zero_of_right κ (hA3 m h0))⟩
  · simpa only [norm_mul] using hA1.mul_left ‖κ‖
  · have hxs := (FlowCoefficientBounds.flow_real X hξ hx s 0).1
    rw [hκ P _ hxs]
    simpa only [mul_assoc] using (hA2 _ hxs).mul_left κ

theorem mem_SS_of_eq_sum_thFr {J : Type} (s : Finset J) (t : J → ℂ) (a b : J → Fin n → Fin g → ℝ)
    {P : J → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)} {Q : Frame X.Ψ r → ℂ} (hs : IsSympl X bas)
    (hn : Even n)
    (hc : ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i)
    (hP : ∀ j ∈ s, P j ∈ Harm.rowHighest ℂ c c')
    (hQ : ∀ x ∈ X.dom, Q x = ∑ j ∈ s, t j * thFr X hr bas idx n (a j) (b j) (P j) x)
    (hΓ : ∀ ga ∈ X.Γ, ∀ x ∈ X.dom, Q (lact ga x) = X.χ (wtOf X hr c c' n) ga * Q x) :
    Q ∈ X.SS (wtOf X hr c c' n) := by
  have hsec := isSec_of_eq_sum_thFr idx hr s t a b hs hP hQ hΓ
  refine FJZero.mem_SS_of_isModerate X _ Q hsec
    (isModerate_of_eq_sum_thFr idx hr s t a b hs hn hP hQ) fun ξ hξ x hx => ?_
  choose A ν h1 h2 h3 using fun j : s =>
    exists_expansion_of_rowHighest idx hr hs hn hc (a j) (b j) (hP j j.2) hξ hx
  have h4 (j : s) : Summable fun m => ‖t j * A j m‖ := by
    simpa only [norm_mul] using (h1 j).mul_left ‖t j‖
  refine FJZero.fj_eq_zero_of_isSec X _ Q hsec hξ hx
    (fun p : s × (Fin n → Fin g → ℤ) => t p.1 * A p.1 p.2)
    (hasSum_prod_of_fintype h4 fun j => (h4 j).of_norm.hasSum).1 (fun p => ν p.1 p.2)
    (fun u => ?_) 0 fun p hp => h3 _ _ (right_ne_zero_of_mul hp)
  rw [hQ _ (FlowCoefficientBounds.flow_real X hξ hx u 0).1, ← Finset.sum_coe_sort]
  refine (hasSum_prod_of_fintype
    (f := fun (j : s) m => t j * A j m * cexp (4 * Real.pi * I * ∑ τ, (ν j m τ : ℂ) * u τ))
    (fun j => ?_) fun j => ?_).2
  · refine (h4 j).congr fun m => ?_
    have h := FJZero.norm_expo (ν j m) u
    rw [FJZero.expo] at h
    rw [norm_mul (t j * A j m), h, mul_one]
  · simpa only [mul_assoc] using (h2 j u).mul_left (t j)

end GlobalTheory.Dict.CuspAny

end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.CuspAny

theorem mem_SS_of_eq_thP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ((∃ τ, ∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ k τ i) ∨ q0 = 0) → ∀ φ : TF n g, IsSB φ → ∀ P ∈ Harm.rowHighest ℂ k k', ∀ Q : Frame X.Ψ r → ℂ, (∀ x ∈ X.dom, Q x = thP X hr bas idx φ P x) → (∀ ga ∈ X.Γ, ∀ x ∈ X.dom, Q (lact ga x) = X.χ (wtOf X hr k k' n) ga * Q x) → Q ∈ X.SS (wtOf X hr k k' n) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn k k' hk φ hφ P hP Q hQ hΓ
  obtain ⟨m, a, b, t, h⟩ := (GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic E r X g q0 hr bas idx n hs hn).2 φ hφ
  rcases hk with ⟨τ, hτ⟩ | h0
  · exact CuspAny.mem_SS_of_eq_sum_thFr idx hr Finset.univ t (fun j k i => (a j k i : ℝ))
      (fun j k i => (b j k i : ℝ)) (P := fun _ => P) hs hn ⟨τ, Or.inl hτ⟩ (fun _ _ => hP)
      (fun x hx => (hQ x hx).trans (h P x hx)) hΓ
  · exact ThFr.mem_SS_of_eq_sum_thFr idx hr Finset.univ t (fun j k i => (a j k i : ℝ))
      (fun j k i => (b j k i : ℝ)) (P := fun _ => P) hs hn
      (Or.inr (CuspClass.not_isIso_of_definite X (by omega))) (fun _ _ => hP)
      (fun x hx => (hQ x hx).trans (h P x hx)) hΓ

end GlobalTheory.Dict.CuspAny
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaHeisenbergUnitaryColumnChange
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaHeisenbergUnitaryColumnChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ColHeis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

theorem hx_sum_left (x : Frame X.Ψ r) (z : Fin n → Fin g → ℂ) (w : Fin g → ℂ) :
    hx X bas idx x (∑ k, z k) w = ∑ k, hx X bas idx x (z k) w := by
  unfold hx
  rw [Matrix.mulVec_sum, sum_dotProduct]

theorem hx_sum_right (x : Frame X.Ψ r) (z : Fin g → ℂ) (w : Fin n → Fin g → ℂ) :
    hx X bas idx x z (∑ k, w k) = ∑ k, hx X bas idx x z (w k) := by
  unfold hx
  rw [Matrix.mulVec_sum, star_sum, Matrix.mulVec_sum, dotProduct_sum]

theorem hAct_eq_sum (h : Matrix (Fin n) (Fin n) E) (z : Fin n → Fin g → ℂ) (k : Fin n) :
    GlobalTheory.Dict.hAct X idx h z k = ∑ a, fun j => rowType X (idx j) (h k a) * z a j := by
  funext j
  rw [Finset.sum_apply]
  rfl

theorem hAct_add_smul (h : Matrix (Fin n) (Fin n) E) (z w : Fin n → Fin g → ℂ) (c : ℂ) (k : Fin n) :
    GlobalTheory.Dict.hAct X idx h (fun a => z a + c • w a) k =
      GlobalTheory.Dict.hAct X idx h z k + c • GlobalTheory.Dict.hAct X idx h w k := by
  funext j
  simp only [GlobalTheory.Dict.hAct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem sum_hx_hAct (x : Frame X.Ψ r)
    (hadj : ∀ (a : E) z w, hx X bas idx x (fun j => rowType X (idx j) a * z j) w =
      hx X bas idx x z (fun j => rowType X (idx j) (cc a) * w j))
    (h : Matrix (Fin n) (Fin n) E) (hh : ccT h * h = 1) (z w : Fin n → Fin g → ℂ) :
    ∑ k, hx X bas idx x (GlobalTheory.Dict.hAct X idx h z k) (GlobalTheory.Dict.hAct X idx h w k) =
      ∑ k, hx X bas idx x (z k) (w k) := by

  have key : ∀ k, hx X bas idx x (GlobalTheory.Dict.hAct X idx h z k) (GlobalTheory.Dict.hAct X idx h w k) =
      ∑ a, ∑ b, hx X bas idx x (z a) (fun j => rowType X (idx j) (cc (h k a) * h k b) * w b j) := by
    intro k
    rw [hAct_eq_sum, hAct_eq_sum, hx_sum_left]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hx_sum_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hadj]
    congr 1
    funext j
    rw [map_mul, _root_.mul_assoc]

  have hcol : ∀ a b, ∑ k, cc (h k a) * h k b = (1 : Matrix (Fin n) (Fin n) E) a b := by
    intro a b
    rw [← hh, Matrix.mul_apply]
    rfl
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  simp only [← hx_sum_right]
  congr 1
  funext j
  have hj : ∀ b, ∑ k, rowType X (idx j) (cc (h k a) * h k b) * w b j =
      rowType X (idx j) ((1 : Matrix (Fin n) (Fin n) E) a b) * w b j := by
    intro b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_mul, ← map_sum, hcol]
  simp only [Finset.sum_apply, hj, Matrix.one_apply, apply_ite, map_one, map_zero, ite_mul,
    _root_.one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem pv_mul_row (x : Frame X.Ψ r)
    (hsm : ∀ (a : E) v, pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j)
    (h : Matrix (Fin n) (Fin n) E) (y : Matrix (Fin n) (Fin r) E) (k : Fin n) :
    pv X idx x ((h * y) k) = GlobalTheory.Dict.hAct X idx h (fun a => pv X idx x (y a)) k := by
  have hrow : (h * y) k = ∑ a, h k a • y a := by
    funext i
    simp [Matrix.mul_apply, Finset.sum_apply]

  have hadd : pv X idx x (∑ a, h k a • y a) = ∑ a, pv X idx x (h k a • y a) := by
    funext j
    rw [Finset.sum_apply]
    exact (congrFun (map_sum (perLin X x) (fun a => h k a • y a) Finset.univ) (idx j)).trans
      (Finset.sum_apply _ _ _)
  rw [hrow, hadd, hAct_eq_sum]
  exact Finset.sum_congr rfl fun a _ => hsm (h k a) (y a)

end GlobalTheory.Dict.ColHeis


open GlobalTheory.Dict.ColHeis in
theorem GlobalTheory.Dict.thA_heisG_hAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ φ φ' : TF n g, IsSB φ → IsSB φ' → ∀ t : ℂ, ∀ x ∈ X.dom, (∀ z, thA X bas idx φ' x (hAct X idx h z) = t * thA X bas idx φ x z) → ∀ (y : Matrix (Fin n) (Fin r) E) z, thA X bas idx (heisG X bas (h * y) φ') x (hAct X idx h z) = t * thA X bas idx (heisG X bas y φ) x z := by
  intro E _ _ _ r X g bas idx n hS hn h hh φ φ' hφ hφ' t x hxd hrel y z
  obtain ⟨-, -, -, hadj, hsm, -⟩ := GlobalTheory.T.hermitianFormAtFrame_laws E r X g bas idx n hS hn x hxd
  have HL := (heisG_laws E r X g bas idx n hS hn).2.2.2
  rw [((HL (h * y) φ' hφ').2.2.2.2) x hxd (hAct X idx h z), ((HL y φ hφ).2.2.2.2) x hxd z]

  have hP : ∀ k, per X x ((h * y) k) ∘ idx = hAct X idx h (fun a => pv X idx x (y a)) k :=
    fun k => pv_mul_row X idx x hsm h y k
  simp only [hP]

  have hT : thA X bas idx φ' x (fun k => hAct X idx h z k + hAct X idx h (fun a => pv X idx x (y a)) k) =
      t * thA X bas idx φ x (fun k => z k + per X x (y k) ∘ idx) := by
    refine Eq.trans ?_ (hrel (fun k => z k + pv X idx x (y k)))
    congr 1
    funext k
    simpa using (hAct_add_smul X idx h z (fun a => pv X idx x (y a)) 1 k).symm
  rw [hT, mul_left_comm]
  refine congrArg (t * ·) (congrArg (· * _) (congrArg cexp (congrArg (fun s : ℂ => -((Real.pi : ℂ) * s)) ?_)))

  have hE : ∀ k, hAct X idx h z k + (1 / 2 : ℂ) • hAct X idx h (fun a => pv X idx x (y a)) k =
      hAct X idx h (fun a => z a + (1 / 2 : ℂ) • pv X idx x (y a)) k :=
    fun k => (hAct_add_smul X idx h z _ _ k).symm
  simp only [hE]
  exact sum_hx_hAct X bas idx x hadj h hh (fun a => z a + (1 / 2 : ℂ) • pv X idx x (y a))
    (fun a => pv X idx x (y a))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaHeisenbergUnitaryColumnChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_heisenberg_unitary_column_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ φ φ' : TF n g, IsSB φ → IsSB φ' → ∀ t : ℂ, ∀ x ∈ X.dom, (∀ z, thA X bas idx φ' x (hAct X idx h z) = t * thA X bas idx φ x z) → ∀ (y : Matrix (Fin n) (Fin r) E) z, thA X bas idx (heisG X bas (h * y) φ') x (hAct X idx h z) = t * thA X bas idx (heisG X bas y φ) x z := by
  first | exact @GlobalTheory.Dict.thA_heisG_hAct | exact GlobalTheory.Dict.thA_heisG_hAct | (intros; apply GlobalTheory.Dict.thA_heisG_hAct <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftOfProjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem exists_lift_of_projective {R P V Q : Type} [CommRing R] [AddCommGroup P] [Module R P] [Module.Projective R P]
    [AddCommGroup V] [Module R V] [Group Q] (act : R → Q → Q) (L : Submodule R V) (ev : P → Q) (φ : V → Q)
    (ev_add : ∀ a b, ev (a + b) = ev a * ev b) (ev_lin : ∀ (s : R) a, ev (s • a) = act s (ev a))
    (φ_add : ∀ a b, φ (a + b) = φ a * φ b) (φ_lin : ∀ (s : R) a, φ (s • a) = act s (φ a))
    (onto : ∀ a, ∃ v ∈ L, ev a = φ v) : ∃ mk : P →ₗ[R] V, ∀ a, mk a ∈ L ∧ ev a = φ (mk a) := by
  have hev0 : ev 0 = 1 := mul_left_cancel (a := ev 0) (by rw [_root_.mul_one, ← ev_add, add_zero])
  have hφ0 : φ 0 = 1 := mul_left_cancel (a := φ 0) (by rw [_root_.mul_one, ← φ_add, add_zero])

  let W : Submodule R (P × L) :=
    { carrier := {x | ev x.1 = φ (x.2 : V)}
      add_mem' := by
        rintro ⟨a, v⟩ ⟨b, w⟩ ha hb
        simp only [Set.mem_ofPred_eq, Prod.mk_add_mk, Submodule.coe_add] at *
        rw [ev_add, φ_add, ha, hb]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, Prod.fst_zero, Prod.snd_zero, ZeroMemClass.coe_zero]
        rw [hev0, hφ0]
      smul_mem' := by
        rintro s ⟨a, v⟩ ha
        simp only [Set.mem_ofPred_eq, Prod.smul_mk, Submodule.coe_smul] at *
        rw [ev_lin, φ_lin, ha] }
  let f : W →ₗ[R] P := (LinearMap.fst R P L).comp W.subtype
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨v, hv, he⟩ := onto a
    exact ⟨⟨(a, ⟨v, hv⟩), he⟩, rfl⟩
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨L.subtype.comp ((LinearMap.snd R P L).comp (W.subtype.comp h)), fun a => ⟨((h a : W) : P × L).2.2, ?_⟩⟩
  have h1 : ((h a : W) : P × L).1 = a := LinearMap.congr_fun hh a
  have h2 : ev ((h a : W) : P × L).1 = φ (((h a : W) : P × L).2 : V) := (h a).2
  rw [h1] at h2
  exact h2

private theorem pv_add_siegel_theta_transformation {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
    (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) (u v : Fin r → E) :
    pv X idx x (u + v) = pv X idx x u + pv X idx x v := by
  have hemb : ∀ τ : E →+* ℂ, ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (u + v) =
      ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ u + ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v := fun τ => by
    funext a
    simp [ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
  funext j
  simp only [pv, Function.comp_apply, Pi.add_apply, GlobalTheory.ThFr.per, hemb]
  split_ifs
  · simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
  · rw [Matrix.mulVec_add, Pi.add_apply]

theorem exists_mark : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∃ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk ∧ A.Marked mk := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL
  have := Dw.proj
  obtain ⟨-, I, -, -, hI⟩ := Xo.univ.geom ℂ y.x _ y.x_over

  obtain ⟨m, hm, c0, hc0, hmc⟩ : ∃ m ∈ l.Mb, ∃ c0 ∈ Mfr l, m + c0 = 1 := by
    have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ Mfr l := by rw [Mfr, l.coprime]; exact Submodule.mem_top
    exact Submodule.mem_sup.mp h1
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hME : (l.M : E) ≠ 0 := Nat.cast_ne_zero.mpr hM0.ne'
  have hMC : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM0.ne'
  have hex0 : A.ex 0 = 1 := mul_left_cancel (a := A.ex 0) (by rw [_root_.mul_one, ← A.ex_add, add_zero])
  have hexn : ∀ (n : ℕ) z, A.ex (n • z) = A.ex z ^ n := by
    intro n z
    induction n with
    | zero => rw [zero_smul, hex0, pow_zero]
    | succ n ih => rw [succ_nsmul, A.ex_add, ih, pow_succ]
  have hpvs : ∀ (a : E) (v : Fin r → E), pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j :=
    fun a v => pv_smul idx x a v
  have hinj : Function.Injective (pv X idx x) := (hx_laws E r X g bas idx 0 hs ⟨0, rfl⟩ x hx).2.2.2.2.2.1
  have hsv : ∀ (s : 𝓞 E) (v : Fin r → E), s • v = (s : E) • v := fun _ _ => rfl

  let φ : (Fin r → E) → (ptO Xo y.x ⟶ Xo.univ.t.G) := fun v => A.ex (pv X idx x ((l.M : E)⁻¹ • v))
  have hφadd : ∀ u v, φ (u + v) = φ u * φ v := fun u v => by
    simp only [φ, smul_add, pv_add_siegel_theta_transformation, A.ex_add]
  have hφlin : ∀ (s : 𝓞 E) v, φ (s • v) = φ v ≫ Xo.univ.t.act.act s := fun s v => by
    simp only [φ]
    rw [← A.ex_lin, ← hpvs, hsv, smul_comm]

  have heta : ∀ a, Xo.univ.eta a = Xo.univ.eta (c0 • a) := by
    intro a
    have h1 : a = c0 • a + m • a := by rw [← add_smul, add_comm, hmc, one_smul]
    conv_lhs => rw [h1]
    rw [Xo.univ.eta_add, Xo.univ.eta_ker (m • a) (Submodule.smul_mem_smul hm Submodule.mem_top),
      _root_.mul_one]
  have hlev : ∀ a, levPt Xo y.x a = I.ev l.M (c0 • a) := by
    intro a
    rw [levPt, heta a]
    exact hI _ (Submodule.smul_mem_smul hc0 Submodule.mem_top)
  obtain ⟨mk, hmk⟩ := exists_lift_of_projective (fun s q => q ≫ Xo.univ.t.act.act s) L
    (fun a => I.ev l.M (c0 • a)) φ (fun a b => by rw [smul_add, I.add])
    (fun s a => by rw [smul_comm c0 s a, I.lin]) hφadd hφlin (by
      intro a
      obtain ⟨z, hz⟩ := A.ex_onto (I.ev l.M (c0 • a))
      have hp : A.ex z ^ l.M = 1 := by
        rw [hz]
        exact (I.onto l.M hM0 _).mpr ⟨_, rfl⟩
      rw [← hexn] at hp
      obtain ⟨v, hv, hzv⟩ := (A.ex_ker _).mp hp
      refine ⟨v, hv, ?_⟩
      rw [← hz]
      show A.ex z = A.ex (pv X idx x ((l.M : E)⁻¹ • v))
      congr 1
      rw [hpvs, ← hzv]
      funext j
      simp only [Pi.smul_apply, nsmul_eq_mul, map_inv₀, map_natCast]
      rw [inv_mul_cancel_left₀ hMC])

  have hevmk : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), I.ev l.M a = φ (mk a) := by
    intro a ha
    rw [← hI a ha, ← (hmk a).2]
    exact hlev a

  have hdiff : ∀ u v, φ u = φ v → ∃ w ∈ L, u - v = l.M • w := by
    intro u v huv
    have h1 : φ (u - v) = 1 := by
      have h2 := hφadd (u - v) v
      rw [sub_add_cancel, huv] at h2
      exact mul_right_cancel (h2.symm.trans (_root_.one_mul _).symm)
    obtain ⟨w, hw, hw'⟩ := (A.ex_ker _).mp h1
    refine ⟨w, hw, ?_⟩
    have h3 := hinj hw'
    rw [← h3, ← Nat.cast_smul_eq_nsmul E, smul_inv_smul₀ hME]

  have hML : ∀ v ∈ Mfr l • L, ∃ u ∈ L, m • v = l.M • u := by
    intro v hv
    have h1 : m • v ∈ (l.Mb * Mfr l) • L := by
      rw [Submodule.mul_smul]
      exact Submodule.smul_mem_smul hm hv
    rw [Mfr, l.prod, Submodule.ideal_span_singleton_smul] at h1
    obtain ⟨u, hu, hu'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    exact ⟨u, hu, by rw [← hu', Nat.cast_smul_eq_nsmul]⟩
  refine ⟨mk, ⟨fun a => (hmk a).1, ?_, ?_⟩, fun a _ => (hlev a).trans (hmk a).2⟩
  · intro a ha hau
    obtain ⟨u, hu, hau⟩ := hau
    apply (I.ker l.M hM0 a).mp
    rw [hevmk a ha]
    show A.ex (pv X idx x ((l.M : E)⁻¹ • mk a)) = 1
    rw [hau, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hME]
    exact (A.ex_ker _).mpr ⟨u, hu, rfl⟩
  · intro v hv
    have hvL : v ∈ L := Submodule.smul_le_right hv
    have hp : φ v ^ l.M = 1 := by
      have h1 : l.M • pv X idx x ((l.M : E)⁻¹ • v) = pv X idx x v := by
        rw [hpvs]
        funext j
        simp only [Pi.smul_apply, nsmul_eq_mul, map_inv₀, map_natCast]
        rw [mul_inv_cancel_left₀ hMC]
      show A.ex (pv X idx x ((l.M : E)⁻¹ • v)) ^ l.M = 1
      rw [← hexn, h1]
      exact (A.ex_ker _).mpr ⟨v, hvL, rfl⟩
    obtain ⟨a0, ha0⟩ := (I.onto l.M hM0 (φ v)).mp hp
    have haM : c0 • a0 ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := Submodule.smul_mem_smul hc0 Submodule.mem_top
    have h3 : φ (mk (c0 • a0)) = φ (c0 • v) := by
      rw [← hevmk _ haM, I.lin, ha0, hφlin]
    obtain ⟨w, hw, hw'⟩ := hdiff _ _ h3.symm
    obtain ⟨u', hu', hmv⟩ := hML v hv
    refine ⟨c0 • a0, haM, u' + w, L.add_mem hu' hw, ?_⟩
    calc v = m • v + c0 • v := by rw [← add_smul, hmc, one_smul]
      _ = mk (c0 • a0) + (l.M • u' + l.M • w) := by rw [hmv, ← hw']; abel
      _ = mk (c0 • a0) + l.M • (u' + w) := by rw [smul_add]

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LeSupOfCoprime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ShVac

theorem le_sup_of_coprime {G : Type} [AddCommGroup G] {A B C : AddSubgroup G} {s m : ℕ}
    (h : s.Coprime m) (hB : ∀ y ∈ A, s • y ∈ B) (hC : ∀ y ∈ A, m • y ∈ C) :
    A ≤ (A ⊓ B) ⊔ (A ⊓ C) := by
  intro y hy
  obtain ⟨a, b, hab⟩ : IsCoprime (s : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 h
  have e : y = a • s • y + b • m • y := by
    rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, hab, one_smul]
  rw [e]
  exact AddSubgroup.add_mem_sup
    (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_inf.2 ⟨A.nsmul_mem hy _, hB y hy⟩) _)
    (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_inf.2 ⟨A.nsmul_mem hy _, hC y hy⟩) _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ}

omit [IsCMField E] in
theorem nsmul_tens {Λ Λ' : Lt E n} {L L' : Lt E r} {k : ℕ}
    (h : ∀ v ∈ Λ, ∀ u ∈ L, k • vecMulVec v u ∈ tens Λ' L') : ∀ y ∈ tens Λ L, k • y ∈ tens Λ' L' := by
  have : tens Λ L ≤ (tens Λ' L').comap (nsmulAddMonoidHom k) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨v, hv, u, hu, rfl⟩
    exact h v hv u hu
  exact fun y hy => this hy

omit [IsCMField E] in
theorem nsmul_tens_left {Λ Λ' : Lt E n} {L : Lt E r} {k : ℕ}
    (h : ∀ v ∈ Λ, (k : E) • v ∈ Λ') : ∀ y ∈ tens Λ L, k • y ∈ tens Λ' L :=
  nsmul_tens fun v hv u hu => AddSubgroup.subset_closure ⟨_, h v hv, u, hu, by
    ext i j; simp [vecMulVec_apply, _root_.mul_assoc]⟩

omit [IsCMField E] in
theorem nsmul_tens_right {Λ : Lt E n} {L L' : Lt E r} {k : ℕ}
    (h : ∀ u ∈ L, (k : 𝓞 E) • u ∈ L') : ∀ y ∈ tens Λ L, k • y ∈ tens Λ L' :=
  nsmul_tens fun v hv u hu => AddSubgroup.subset_closure ⟨v, hv, _, h u hu, by
    rw [Nat.cast_smul_eq_nsmul]
    ext i j; simp [vecMulVec_apply, mul_left_comm]⟩

omit [IsCMField E] in
theorem relIndex_half {P Q : Ideal (𝓞 E)} {L L' : Lt E r} {s : 𝓞 E}
    (hs : IsCoprime (Ideal.span {s}) P) (h : ∀ v ∈ L, s • v ∈ L') :
    (idq P Q L).toAddSubgroup.relIndex L.toAddSubgroup =
      (idq P Q L).toAddSubgroup.relIndex (L ⊓ L').toAddSubgroup ∧
    ∀ x ∈ L', x ∈ idq P Q L → x ∈ idq P Q L' := by
  obtain ⟨a, m, hm, e⟩ := Lev.cop_iff.1 hs
  have d (x : Fin r → E) : x = a • s • x + m • x := by
    rw [← mul_smul, ← add_smul, e, one_smul]
  constructor
  · refine Lev.relIndex_eq (fun x hx => hx.1) fun x (hx : x ∈ L) => ?_
    rw [d x]
    exact AddSubgroup.add_mem_sup ⟨L.smul_mem _ (L.smul_mem _ hx), L'.smul_mem _ (h x hx)⟩
      ⟨fun b _ => Submodule.smul_mem _ b (Submodule.smul_mem_smul hm hx), L.smul_mem _ hx⟩
  · intro x hx H b hb
    rw [d (b • x)]
    exact add_mem (Submodule.smul_mem _ _ (Lev.smul_map_mem LinearMap.id h (H b hb)))
      (Submodule.smul_mem_smul hm (L'.smul_mem _ hx))


omit [IsCMField E] in
theorem relIndex_shift {P Q : Ideal (𝓞 E)} {L L' : Lt E r} {s : 𝓞 E}
    (hs : IsCoprime (Ideal.span {s}) P) (h : ∀ v ∈ L, s • v ∈ L') (h' : ∀ v ∈ L', s • v ∈ L) :
    (idq P Q L).toAddSubgroup.relIndex L.toAddSubgroup =
      (idq P Q L').toAddSubgroup.relIndex L'.toAddSubgroup := by
  obtain ⟨h1, h2⟩ := relIndex_half (Q := Q) hs h
  obtain ⟨h3, h4⟩ := relIndex_half (Q := Q) hs h'
  rw [h1, h3, inf_comm L' L, ← AddSubgroup.inf_relIndex_right,
    ← AddSubgroup.inf_relIndex_right (idq P Q L').toAddSubgroup]
  congr 1
  ext x
  exact and_congr_left fun hx => ⟨h2 x hx.2, h4 x hx.1⟩

theorem eq_sqrt {k t : ℝ} (ht : 0 ≤ t) (h : k * t ^ 2 = 1) : t = √(k⁻¹) ∧ 0 < t := by
  refine ⟨?_, ht.lt_of_ne ?_⟩
  · rw [← eq_inv_of_mul_eq_one_right h, Real.sqrt_sq ht]
  · rintro rfl
    simp at h

theorem smul_eq_unitv {g : ℕ} {u : TF n g} (hu : IsSB u) (h1 : SW.ip u u = 1) {a : ℂ} (ha : 0 < ‖a‖) :
    a • u = ((‖a‖ : ℝ) : ℂ) • unitv (a • u) := by
  rw [unitv, TensVac.ip_smul_left _ hu (TensVac.sb_smul _ hu), TensVac.ip_smul_right _ hu hu, h1, _root_.mul_one,
    Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re, Real.sqrt_sq ha.le, smul_smul (_ : ℂ) (_ : ℂ)⁻¹,
    mul_inv_cancel₀ (by exact_mod_cast ha.ne'), one_smul]

theorem shift_vac : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : SW.Level X) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∃ (ρ : ℝ) (s : Lt E n → ℝ), 0 < ρ ∧ ∀ L ∈ D.lats, ∀ v : TF n g, IsVac X bas D.w (tens (stdL E n) L) v → ∃ t : ℂ, ‖t‖ = ρ ∧ ∀ Λ ∈ Vset E n M, 0 < s Λ ∧ projA X bas D.w (tens Λ (D.sh L)) (projA X bas D.w (tens Λ L) v) = (t * (s Λ : ℂ)) • unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L)) := by
  intro E _ _ _ r X g bas idx n hs hn D M _ hM v₀ hv₀
  have one {Λ} (h : Λ ∈ Vset E n M) : Λ ∈ Vset E n 1 := by
    obtain ⟨h1, h2, s, h3, -, h4⟩ := h
    exact ⟨h1, h2, s, h3, Nat.coprime_one_right s, h4⟩
  have hstd := Base.stdL_mem_Vset (E := E) n 1
  have hsh {L} (hL : L ∈ D.lats) : SelfD X (D.sh L) := Lev.selfD_idq D.ne_bot D.proper D.cop hL.1
  have vac := TensVac.vacua E r X g bas idx n hs hn D.w D.w_int D.w_tr
  have ten := GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hn D.w D.w_int D.w_tr
  have pp := GlobalTheory.Dict.ProjProj.proj_proj E r X g bas idx n hs hn D.w D.w_int D.w_tr
  have hΛ₀ : X.Λ ∈ D.lats := ⟨Lev.selfD_of_sympl hs, 1, Lev.cop_one, fun v hv => by simpa using hv,
    fun v hv => by simpa using hv⟩
  have key : ∀ L ∈ D.lats, ∀ v : TF n g, IsVac X bas D.w (tens (stdL E n) L) v →
      ‖SW.ip v (v₀ L)‖ = √((((D.sh X.Λ).toAddSubgroup.relIndex X.Λ.toAddSubgroup ^ n : ℕ) : ℝ)⁻¹) ∧
        0 < ‖SW.ip v (v₀ L)‖ := by
    intro L hL v hv
    have h := (vac L hL.1 1 _ hstd).2.2.2 _ (hsh hL) _ hstd v _ hv (hv₀ L hL)
    rw [((ten L hL.1 1 _ hstd).2.2.2.2.1 _ (hsh hL)).1] at h
    obtain ⟨-, s, h1, h2, h3⟩ := hL
    rw [Level.sh, relIndex_shift h1.of_mul_right_left h2 h3] at h
    exact eq_sqrt (norm_nonneg _) h
  refine ⟨_, fun Λ => √(((Λ.toAddSubgroup.relIndex (stdL E n).toAddSubgroup ^ r : ℕ) : ℝ)⁻¹), ?_,
    fun L hL v hv => ⟨_, (key L hL v hv).1, fun Λ hΛ => ?_⟩⟩
  · obtain ⟨v, hv⟩ := (vac _ hΛ₀.1 1 _ hstd).1
    exact (key _ hΛ₀ v hv).1 ▸ (key _ hΛ₀ v hv).2
  obtain ⟨⟨u, hu⟩, -, hp, -⟩ := vac _ (hsh hL) 1 _ (one hΛ)
  have h := (vac _ (hsh hL) 1 _ hstd).2.2.2 _ (hsh hL) _ (one hΛ) _ u (hv₀ L hL) hu
  rw [(ten _ (hsh hL) 1 _ hstd).2.2.2.2.2 _ (one hΛ)] at h
  obtain ⟨h1, h2⟩ := eq_sqrt (norm_nonneg _) h
  simp only [← h1]
  refine ⟨h2, ?_⟩
  obtain ⟨s, -, hc, s1, s2⟩ := hΛ.2.2
  have hM' : (M : 𝓞 E) ∈ conjI D.𝔪 := Lev.mem_conjI.2 (by rwa [map_natCast])
  have e1 := pp L L _ hL.1 hL.1 (hsh hL) _ hstd _ (one hΛ) _ (one hΛ)
    (le_sup_of_coprime hc (nsmul_tens_left s1) (nsmul_tens_right fun x hx =>
      Lev.smul_le_idq _ _ _ (Submodule.smul_mem_smul hM hx))) v hv
  have e2 := pp L _ _ hL.1 (hsh hL) (hsh hL) _ hstd _ hstd _ (one hΛ)
    (le_sup_of_coprime hc.symm (nsmul_tens_right fun x hx => Submodule.smul_le_right (hx _ hM'))
      (nsmul_tens_left s2)) v hv
  have b₀ := (hv₀ L hL).1
  rw [e1, ← e2, (vac _ (hsh hL) 1 _ hstd).2.2.1 v hv.1 _ (hv₀ L hL), hp _ (TensVac.sb_smul _ b₀) u hu,
    hp _ b₀ u hu, TensVac.ip_smul_left _ b₀ hu.1, mul_smul, mul_smul, ← smul_eq_unitv hu.1 hu.2.1 h2]

end GlobalTheory.Dict.ShVac
end
