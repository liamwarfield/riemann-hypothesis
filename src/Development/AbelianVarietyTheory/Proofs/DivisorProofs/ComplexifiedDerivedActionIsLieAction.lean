module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjInvol
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTranspose
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjOfTwistedNormConjHermitianTripleRegul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorISignatureConjApplyOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBlockGeneratorsLagrangianNormalF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLabelAtUnfolding
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGramSchmidtIndefiniteHermitianFrames

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionIsLieAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionIsLieAction
noncomputable section

namespace GlobalTheory.HolDict.LieAct

section

open Matrix Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.HolDict
open scoped InnerProductSpace ContDiff Topology

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {G : Mt n} {π : Mt n → (H →L[ℂ] H)}

theorem unit_of (hd : G.det ≠ 0) : IsUnit G := (Matrix.isUnit_iff_isUnit_det G).2 hd.isUnit

theorem exists_coef (hh : G.IsHermitian) (hd : G.det ≠ 0) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {v : H}
    (hv : v ∈ SmVec.smSub G π) (y : H) :
    ∃ D : Mt n →ₗ[ℝ] ℂ, ∀ X ∈ SmVec.lieG G, ⟪y, dRep π X v⟫_ℂ = D X := by
  have hG := unit_of hd
  have hH : ∀ τ : Unit, ((fun _ => G : Unit → Mt n) τ).IsHermitian ∧ ((fun _ => G : Unit → Mt n) τ).det ≠ 0 :=
    fun _ => ⟨hh, hd⟩
  let ev : Chart.Alg n Unit →* Mt n := Pi.evalMonoidHom (fun _ : Unit => Mt n) ()
  have hev : ∀ (t : ℝ) (Y : Chart.Alg n Unit), ev (NormedSpace.exp (t • Y)) = NormedSpace.exp (t • Y ()) :=
    fun t Y => Chart.exp_alg _ _
  obtain ⟨-, D, h1, -⟩ := Chart.chain (Chart.adj_anti hH) (Chart.adj_one hH) (Chart.adj_invol hH) Set.univ
    (by simp) (fun u => ⟪y, π (ev u) v⟫_ℂ)
    (fun k Y _ u hu => by
      have hY : ∀ i, (Y i : Chart.Alg n Unit) () ∈ SmVec.lieG G := fun i =>
        (Chart.skew_iff hH _).1 ((Chart.mem_skew _).1 (Y i).2) ()
      have hu' : ev u ∈ Formalism.QuantumDeterminants.UH G := (Chart.unit_iff hH _).1 hu ()
      simp only [map_mul, map_list_prod, List.map_ofFn, Function.comp_def, hev,
        SmVec.rep_mul hπ hu' (SmVec.expProd_mem_UH hG hY _)]
      exact contDiff_const.inner ℂ (((π (ev u)).restrictScalars ℝ).contDiff.comp (hv k _ hY)))
    (E := ℝ) (γ := fun _ => 1) (x := 0) contDiffAt_const
    (Filter.Eventually.of_forall fun _ => by rw [Chart.adj_one hH, mul_one])
  let c : Mt n →ₗ[ℝ] Chart.Alg n Unit := LinearMap.pi fun _ : Unit => (LinearMap.id : Mt n →ₗ[ℝ] Mt n)
  refine ⟨D.toLinearMap ∘ₗ c, fun X hX => ?_⟩
  have h2 := h1 (c X) ((Chart.skew_iff hH _).2 fun _ => hX)
  simp only [one_mul, hev] at h2
  have h3 := (hasDerivAt_const (0 : ℝ) y).inner ℂ (SmVec.hasDerivAt_dRep hv hX)
  rw [inner_zero_left, add_zero] at h3
  exact h3.deriv.symm.trans h2

theorem add_mem_lie {X Y : Mt n} (hX : X ∈ SmVec.lieG G) (hY : Y ∈ SmVec.lieG G) : X + Y ∈ SmVec.lieG G := by
  have h1 : Xᴴ * G + G * X = 0 := hX
  have h2 : Yᴴ * G + G * Y = 0 := hY
  show (X + Y)ᴴ * G + G * (X + Y) = 0
  rw [conjTranspose_add, add_mul, mul_add, add_add_add_comm, h1, h2, add_zero]

theorem smul_mem_lie (c : ℝ) {X : Mt n} (hX : X ∈ SmVec.lieG G) : c • X ∈ SmVec.lieG G := by
  have h1 : Xᴴ * G + G * X = 0 := hX
  show (c • X)ᴴ * G + G * (c • X) = 0
  rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, h1, smul_zero]

theorem neg_mem_lie {X : Mt n} (hX : X ∈ SmVec.lieG G) : -X ∈ SmVec.lieG G := by
  simpa using smul_mem_lie (-1) hX

theorem dRep_lin (hh : G.IsHermitian) (hd : G.det ≠ 0) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {v : H}
    (hv : v ∈ SmVec.smSub G π) (a : ℝ) {X Y : Mt n} (hX : X ∈ SmVec.lieG G) (hY : Y ∈ SmVec.lieG G) :
    dRep π (a • X + Y) v = (a : ℂ) • dRep π X v + dRep π Y v := by
  refine ext_inner_left ℂ fun y => ?_
  obtain ⟨D, hD⟩ := exists_coef hh hd hπ hv y
  rw [inner_add_right, inner_smul_right, hD _ (add_mem_lie (smul_mem_lie a hX) hY), hD _ hX, hD _ hY, map_add (f := _),
    map_smul, Complex.real_smul]

theorem conjH_parts (hd : G.det ≠ 0) {X Y : Mt n} (hX : X ∈ SmVec.lieG G) (hY : Y ∈ SmVec.lieG G) :
    conjH G (X + Complex.I • Y) = X + Complex.I • (-Y) := by
  have h : ∀ W ∈ SmVec.lieG G, G⁻¹ * Wᴴ * G = -W := fun W hW => by
    have h1 : Wᴴ * G + G * W = 0 := hW
    rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h1, Matrix.mul_neg,
      nonsing_inv_mul_cancel_left _ _ hd.isUnit]
  rw [conjH, conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, h X hX, h Y hY]
  simp [add_comm]

theorem dRepC_parts (hd : G.det ≠ 0) {X Y : Mt n} (hX : X ∈ SmVec.lieG G) (hY : Y ∈ SmVec.lieG G) (v : H) :
    dRepC G π (X + Complex.I • Y) v = dRep π X v + Complex.I • dRep π Y v := by
  have e1 : (1 / 2 : ℂ) • (X + Complex.I • Y + (X + Complex.I • (-Y))) = X := by module
  have e2 : (1 / (2 * Complex.I)) • (X + Complex.I • Y - (X + Complex.I • (-Y))) = Y := by
    have : X + Complex.I • Y - (X + Complex.I • (-Y)) = (2 * Complex.I) • Y := by module
    rw [this, smul_smul, one_div_mul_cancel (by simp), one_smul]
  rw [dRepC, conjH_parts hd hX hY, e1, e2]

theorem exists_parts (hh : G.IsHermitian) (hd : G.det ≠ 0) (Z : Mt n) :
    ∃ X ∈ SmVec.lieG G, ∃ Y ∈ SmVec.lieG G, Z = X + Complex.I • Y := by
  refine ⟨_, (SmVec.parts_mem (unit_of hd) hh Z).1, _, (SmVec.parts_mem (unit_of hd) hh Z).2, ?_⟩
  have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  rw [smul_smul, this]
  module

theorem zero_mem_lie : (0 : Mt n) ∈ SmVec.lieG G := by simp [SmVec.lieG]

theorem dRepC_real (hd : G.det ≠ 0) {X : Mt n} (hX : X ∈ SmVec.lieG G) (v : H) : dRepC G π X v = dRep π X v := by
  have := dRepC_parts (π := π) hd hX zero_mem_lie v
  simpa [dRep] using this

theorem dRepC_lin (hh : G.IsHermitian) (hd : G.det ≠ 0) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {v : H}
    (hv : v ∈ SmVec.smSub G π) (a : ℂ) (Z Z' : Mt n) :
    dRepC G π (a • Z + Z') v = a • dRepC G π Z v + dRepC G π Z' v := by
  obtain ⟨X, hX, Y, hY, rfl⟩ := exists_parts hh hd Z
  obtain ⟨X', hX', Y', hY', rfl⟩ := exists_parts hh hd Z'
  obtain ⟨p, q, rfl⟩ : ∃ p q : ℝ, a = p + q * Complex.I := ⟨a.re, a.im, (Complex.re_add_im a).symm⟩
  have e : ((p : ℂ) + q * Complex.I) • (X + Complex.I • Y) + (X' + Complex.I • Y') =
      (p • X + ((-q) • Y + X')) + Complex.I • (q • X + (p • Y + Y')) := by
    simp only [← Complex.coe_smul]
    match_scalars <;> first | ring1 | (push_cast; linear_combination (q : ℂ) * Complex.I_mul_I)
  have m1 := add_mem_lie (smul_mem_lie (-q) hY) hX'
  have m2 := add_mem_lie (smul_mem_lie p hY) hY'
  rw [e, dRepC_parts hd (add_mem_lie (smul_mem_lie p hX) m1) (add_mem_lie (smul_mem_lie q hX) m2),
    dRepC_parts hd hX hY, dRepC_parts hd hX' hY', dRep_lin hh hd hπ hv p hX m1, dRep_lin hh hd hπ hv q hX m2,
    dRep_lin hh hd hπ hv _ hY hX', dRep_lin hh hd hπ hv _ hY hY']
  match_scalars <;> first | ring1 | (push_cast; linear_combination (-q : ℂ) * Complex.I_mul_I)

theorem dRepC_vec (hh : G.IsHermitian) (hd : G.det ≠ 0) {v w : H} (hv : v ∈ SmVec.smSub G π)
    (hw : w ∈ SmVec.smSub G π) (a : ℂ) (Z : Mt n) :
    dRepC G π Z (a • v + w) = a • dRepC G π Z v + dRepC G π Z w := by
  obtain ⟨X, hX, Y, hY, rfl⟩ := exists_parts hh hd Z
  have hav := (SmVec.smSub G π).smul_mem a hv
  simp only [dRepC_parts hd hX hY, SmVec.dRep_add hav hw hX, SmVec.dRep_add hav hw hY, SmVec.dRep_smul a hv hX,
    SmVec.dRep_smul a hv hY]
  module

def lin (hh : G.IsHermitian) (hd : G.det ≠ 0) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {v : H}
    (hv : v ∈ SmVec.smSub G π) : Mt n →ₗ[ℂ] H where
  toFun Z := dRepC G π Z v
  map_add' Z Z' := by simpa using dRepC_lin hh hd hπ hv 1 Z Z'
  map_smul' a Z := by
    have h0 : dRepC G π 0 v = 0 := by rw [dRepC_real hd zero_mem_lie]; simp [dRep]
    simpa [h0] using dRepC_lin hh hd hπ hv a Z 0

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem hasDerivAt_conj {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (L : Mt n →ₗ[ℂ] E) (X Y : Mt n) :
    HasDerivAt (fun t : ℝ => L (NormedSpace.exp (t • -X) * Y * NormedSpace.exp (t • X))) (L (Y * X - X * Y)) 0 := by
  have h := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) 0).mul_const Y).mul (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
  have h2 := ((LinearMap.toContinuousLinearMap L).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h
  have e : NormedSpace.exp ((0 : ℝ) • -X) * -X * Y * NormedSpace.exp ((0 : ℝ) • X) +
      NormedSpace.exp ((0 : ℝ) • -X) * Y * (NormedSpace.exp ((0 : ℝ) • X) * X) = Y * X - X * Y := by
    simp [sub_eq_add_neg, add_comm]
  rw [← e]
  exact h2

theorem dRepC_bracket_real (hh : G.IsHermitian) (hd : G.det ≠ 0) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {v : H}
    (hv : v ∈ SmVec.smSub G π) {X Y : Mt n} (hX : X ∈ SmVec.lieG G) (hY : Y ∈ SmVec.lieG G) :
    dRepC G π (Y * X - X * Y) v = dRep π Y (dRep π X v) - dRep π X (dRep π Y v) := by
  have hG := unit_of hd
  have hXv := SmVec.dRep_mem hG hπ hv hX
  have hYv := SmVec.dRep_mem hG hπ hv hY
  have key : ∀ y ∈ SmVec.smSub G π,
      ⟪y, dRepC G π (Y * X - X * Y) v - (dRep π Y (dRep π X v) - dRep π X (dRep π Y v))⟫_ℂ = 0 := by
    intro y hy
    have h1 := (SmVec.hasDerivAt_dRep hy (neg_mem_lie hX)).inner ℂ (hasDerivAt_conj (lin hh hd hπ hv) X Y)
    have h2 := ((hasDerivAt_const (0 : ℝ) (dRep π Y y)).inner ℂ (SmVec.hasDerivAt_dRep hv hX)).neg
    have e : (fun t : ℝ => ⟪π (NormedSpace.exp (t • -X)) y,
        lin hh hd hπ hv (NormedSpace.exp (t • -X) * Y * NormedSpace.exp (t • X))⟫_ℂ) =
        -fun t : ℝ => ⟪dRep π Y y, π (NormedSpace.exp (t • X)) v⟫_ℂ := by
      funext t
      have hg := SmVec.exp_mem_UH hG hX t
      have hi : NormedSpace.exp (t • -X) = (NormedSpace.exp (t • X))⁻¹ := by rw [smul_neg, Matrix.exp_neg]
      have hu := (Matrix.isUnit_iff_isUnit_det _).1 (SmVec.isUnit_of_mem_UH hG hg)
      show ⟪_, dRepC G π _ v⟫_ℂ = -⟪_, _⟫_ℂ
      rw [hi, dRepC_real hd (SmVec.conj_mem_lieG hG hg hY), ← SmVec.rep_inner hπ hg,
        ← SmVec.rep_mul hπ hg (SmVec.inv_mem_UH hG hg), mul_nonsing_inv _ hu, SmVec.rep_one hπ,
        ← SmVec.dRep_rep hG hπ hv hg hY, SmVec.inner_dRep hG hπ hy (SmVec.rep_mem hG hπ hv hg) hY]
    rw [e] at h1
    have h3 := h1.unique h2
    have hn : dRep π (-X) y = -dRep π X y := by
      have := dRep_lin hh hd hπ hy (-1) hX zero_mem_lie
      simpa [show dRep π 0 y = 0 by simp [dRep]] using this
    simp only [zero_smul, NormedSpace.exp_zero, SmVec.rep_one hπ, inner_zero_left, add_zero, Matrix.one_mul,
      Matrix.mul_one, hn, inner_neg_left] at h3
    change ⟪y, dRepC G π _ v⟫_ℂ + -⟪_, dRepC G π Y v⟫_ℂ = _ at h3
    rw [dRepC_real hd hY] at h3
    rw [inner_sub_right, inner_sub_right, SmVec.inner_dRep hG hπ hy hXv hY, SmVec.inner_dRep hG hπ hy hYv hX]
    linear_combination h3
  refine sub_eq_zero.1 (inner_self_eq_zero.1 (key _ ?_))
  exact sub_mem (SmVec.dRepC_mem hG hh hπ _ hv) (sub_mem (SmVec.dRep_mem hG hπ hXv hY) (SmVec.dRep_mem hG hπ hYv hX))

theorem dRepC_bracket (hh : G.IsHermitian) (hd : G.det ≠ 0) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {v : H}
    (hv : v ∈ SmVec.smSub G π) (Z Z' : Mt n) :
    dRepC G π (Z * Z' - Z' * Z) v = dRepC G π Z (dRepC G π Z' v) - dRepC G π Z' (dRepC G π Z v) := by
  have hG := unit_of hd
  obtain ⟨X, hX, Y, hY, rfl⟩ := exists_parts hh hd Z
  obtain ⟨X', hX', Y', hY', rfl⟩ := exists_parts hh hd Z'
  have e : (X + Complex.I • Y) * (X' + Complex.I • Y') - (X' + Complex.I • Y') * (X + Complex.I • Y) =
      (X * X' - X' * X) + Complex.I • (X * Y' - Y' * X) + Complex.I • (Y * X' - X' * Y) +
        (Complex.I * Complex.I) • (Y * Y' - Y' * Y) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
    module
  have hl : ∀ W, dRepC G π W v = lin hh hd hπ hv W := fun _ => rfl
  have hs : ∀ {A B C : Mt n}, A ∈ SmVec.lieG G → B ∈ SmVec.lieG G → C ∈ SmVec.lieG G →
      dRep π A (dRep π B v + Complex.I • dRep π C v) = dRep π A (dRep π B v) + Complex.I • dRep π A (dRep π C v) :=
    fun hA hB hC => by
      rw [SmVec.dRep_add (SmVec.dRep_mem hG hπ hv hB) (Submodule.smul_mem _ _ (SmVec.dRep_mem hG hπ hv hC)) hA,
        SmVec.dRep_smul _ (SmVec.dRep_mem hG hπ hv hC) hA]
  rw [e, hl, map_add (f := _), map_add (f := _), map_add (f := _), map_smul, map_smul, map_smul, ← hl, ← hl, ← hl, ← hl,
    dRepC_bracket_real hh hd hπ hv hX' hX, dRepC_bracket_real hh hd hπ hv hY' hX,
    dRepC_bracket_real hh hd hπ hv hX' hY, dRepC_bracket_real hh hd hπ hv hY' hY]
  simp only [dRepC_parts hd hX hY, dRepC_parts hd hX' hY', hs hX hX' hY', hs hY hX' hY', hs hX' hX hY, hs hY' hX hY]
  module

theorem rep_dRepC (hh : G.IsHermitian) (hd : G.det ≠ 0) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {v : H}
    (hv : v ∈ SmVec.smSub G π) {g : Mt n} (hg : g ∈ Formalism.QuantumDeterminants.UH G) (Z : Mt n) :
    π g (dRepC G π Z v) = dRepC G π (g * Z * g⁻¹) (π g v) := by
  have hG := unit_of hd
  obtain ⟨X, hX, Y, hY, rfl⟩ := exists_parts hh hd Z
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (SmVec.isUnit_of_mem_UH hG hg)
  have hc : ∀ W ∈ SmVec.lieG G, g * W * g⁻¹ ∈ SmVec.lieG G := fun W hW => by
    have := SmVec.conj_mem_lieG hG (SmVec.inv_mem_UH hG hg) hW
    rwa [nonsing_inv_nonsing_inv _ hu] at this
  have he : ∀ W : Mt n, g⁻¹ * (g * W * g⁻¹) * g = W := fun W => by
    simp only [Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one, nonsing_inv_mul_cancel_left _ _ hu]
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, dRepC_parts hd hX hY, dRepC_parts hd (hc X hX) (hc Y hY),
    SmVec.dRep_rep hG hπ hv hg (hc X hX), SmVec.dRep_rep hG hπ hv hg (hc Y hY), he, he, map_add, map_smul]

theorem inner_dRepC (hh : G.IsHermitian) (hd : G.det ≠ 0) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {v w : H}
    (hv : v ∈ SmVec.smSub G π) (hw : w ∈ SmVec.smSub G π) (Z : Mt n) :
    ⟪dRepC G π Z v, w⟫_ℂ = -⟪v, dRepC G π (conjH G Z) w⟫_ℂ := by
  have hG := unit_of hd
  obtain ⟨X, hX, Y, hY, rfl⟩ := exists_parts hh hd Z
  have hn : dRep π (-Y) w = -dRep π Y w := by
    have := dRep_lin hh hd hπ hw (-1) hY zero_mem_lie
    simpa [show dRep π 0 w = 0 by simp [dRep]] using this
  rw [conjH_parts hd hX hY, dRepC_parts hd hX hY, dRepC_parts hd hX (neg_mem_lie hY), hn, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, inner_neg_right, SmVec.inner_dRep hG hπ hv hw hX,
    SmVec.inner_dRep hG hπ hv hw hY, Complex.conj_I]
  ring

end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem main : ∀ (n : ℕ) (Hm : Mt n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mt n → (H →L[ℂ] H)), Hm.IsHermitian → Hm.det ≠ 0 → IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ → ∀ v v', SmoothVec (lieH Hm) σ v → SmoothVec (lieH Hm) σ v' → (∀ (a : ℂ) (Z Z' : Mt n), dRepC Hm σ (a • Z + Z') v = a • dRepC Hm σ Z v + dRepC Hm σ Z' v ∧ dRepC Hm σ Z (a • v + v') = a • dRepC Hm σ Z v + dRepC Hm σ Z v' ∧ dRepC Hm σ (Z * Z' - Z' * Z) v = dRepC Hm σ Z (dRepC Hm σ Z' v) - dRepC Hm σ Z' (dRepC Hm σ Z v)) ∧ (∀ X ∈ lieH Hm, dRepC Hm σ X v = dRep σ X v) ∧ (∀ g ∈ Formalism.QuantumDeterminants.UH Hm, ∀ Z, σ g (dRepC Hm σ Z v) = dRepC Hm σ (g * Z * g⁻¹) (σ g v)) ∧ ∀ Z, ⟪dRepC Hm σ Z v, v'⟫_ℂ = -⟪v, dRepC Hm σ (conjH Hm Z) v'⟫_ℂ := by
  intro n Hm H _ _ _ σ hh hd hσ v v' hv hv'
  exact ⟨fun a Z Z' => ⟨dRepC_lin hh hd hσ hv a Z Z', dRepC_vec hh hd hv hv' a Z, dRepC_bracket hh hd hσ hv Z Z'⟩,
    fun X hX => dRepC_real hd hX v, fun g hg Z => rep_dRepC hh hd hσ hv hg Z, inner_dRepC hh hd hσ hv hv'⟩

end GlobalTheory.HolDict.LieAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionIsLieActionStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexifiedDerivedAction_isLieAction : ∀ (n : ℕ) (Hm : Mt n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mt n → (H →L[ℂ] H)), Hm.IsHermitian → Hm.det ≠ 0 → IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ → ∀ v v', SmoothVec (lieH Hm) σ v → SmoothVec (lieH Hm) σ v' → (∀ (a : ℂ) (Z Z' : Mt n), dRepC Hm σ (a • Z + Z') v = a • dRepC Hm σ Z v + dRepC Hm σ Z' v ∧ dRepC Hm σ Z (a • v + v') = a • dRepC Hm σ Z v + dRepC Hm σ Z v' ∧ dRepC Hm σ (Z * Z' - Z' * Z) v = dRepC Hm σ Z (dRepC Hm σ Z' v) - dRepC Hm σ Z' (dRepC Hm σ Z v)) ∧ (∀ X ∈ lieH Hm, dRepC Hm σ X v = dRep σ X v) ∧ (∀ g ∈ Formalism.QuantumDeterminants.UH Hm, ∀ Z, σ g (dRepC Hm σ Z v) = dRepC Hm σ (g * Z * g⁻¹) (σ g v)) ∧ ∀ Z, ⟪dRepC Hm σ Z v, v'⟫_ℂ = -⟪v, dRepC Hm σ (conjH Hm Z) v'⟫_ℂ := by
  first | exact @GlobalTheory.HolDict.LieAct.main | exact GlobalTheory.HolDict.LieAct.main | (intros; apply GlobalTheory.HolDict.LieAct.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorBaseLevelTwistedModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorBaseLevelTwistedModel
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.WType

theorem range_w0C_type : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → R.toRealDat.LUnif → ∀ i, LinearMap.range ((R.toCx3 F).w0C false i) = Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) ⊓ typeSubspace A3 (R.toCx3 F) i (R.gWx F i) F.P0 F.ψ0⁻¹ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hW hEx hU i
  obtain ⟨hC, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  have hI := (GlobalTheory.T.goodProjector_unitaryFormsModel_laws R.toRealDat F.lv2 hC hX i).1
  have hs : ∀ a, cj (twAt D.what₂.embLL A3.A.v0) (A3.A.fam.v0.embedding a) = sg0 D A3.A a := fun a => by
    show cj _ (A3.A.v0.embedding a) = _
    rw [emb_eq D.what₂.embLL A3.A.v0 a, cj_cj]
  rw [GlobalTheory.T.range_complex_points_level_forms_eq_good_forms R F hOk hW hU false i]
  ext x
  have hw := GlobalTheory.WatType.wat_iff_type R.toRealDat F.lv2 hOk.ok2 hC false i (Tw.out x)
  have hL : x ∈ Tw.sub (twAt D.what₂.embLL A3.A.v0) ((R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))).comap (R.HW i (sg0 D A3.A)).e) ↔ (R.HW i (sg0 D A3.A)).e (Tw.out x) ∈ R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) := Iff.rfl
  have hR : Tw.out x ∈ LinearMap.range (eH R.toRealDat i) ↔ eH R.toRealDat i (Tw.out x) = Tw.out x := by
    refine ⟨?_, fun h => ⟨_, h⟩⟩
    rintro ⟨y, hy⟩
    rw [← hy, ← Module.End.mul_apply, hI]
  have hT : x ∈ typeSubspace A3 (R.toCx3 F) i (R.gWx F i) F.P0 F.ψ0⁻¹ ↔ ∀ p : (F.lv2.lvl false).P, R.gW i (sg0 D A3.A) (p : G) (Tw.out x) = sg0 D A3.A ((((F.lv2.lvl false).ψ⁻¹ p : D.what₂.LLˣ)) : D.what₂.LL) • Tw.out x := by
    unfold typeSubspace
    refine (Submodule.mem_iInf (R := ℂ) (M := (R.toCx3 F).W i) _).trans (forall_congr' fun p => ?_)
    show R.gW i (sg0 D A3.A) (p : G) (Tw.out x) - cj (twAt D.what₂.embLL A3.A.v0) (A3.A.fam.v0.embedding ((F.ψ0⁻¹ p : D.what₂.LLˣ) : D.what₂.LL)) • Tw.out x = 0 ↔ _
    rw [sub_eq_zero, hs]
    rfl
  constructor
  · intro h
    rw [hL, hw] at h
    exact ⟨hR.2 h.1, hT.2 h.2⟩
  · intro h
    rw [hL, hw]
    exact ⟨hR.1 h.1, hT.1 h.2⟩

end GlobalTheory.WType

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorBaseLevelTwistedModelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_goodProjector_baseLevel_twistedModel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → R.toRealDat.LUnif → ∀ i, LinearMap.range ((R.toCx3 F).w0C false i) = Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) ⊓ typeSubspace A3 (R.toCx3 F) i (R.gWx F i) F.P0 F.ψ0⁻¹ := by
  first | exact @GlobalTheory.WType.range_w0C_type | exact GlobalTheory.WType.range_w0C_type | (intros; apply GlobalTheory.WType.range_w0C_type <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationPrincipalLevelEqCoreLevelOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationPrincipalLevelEqCoreLevelOpen
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolDict.PrincLev

def congGroup {D : D7} (V : HSp D) (N : ℕ) : Subgroup (GA D V) where
  carrier := {k | GlobalTheory.Member.FinCong V N k}
  one_mem' := GlobalTheory.Member.PrincLevel.finCong_one V N
  mul_mem' := fun ha hb => GlobalTheory.Member.PrincLevel.finCong_mul ha hb
  inv_mem' := fun ha => GlobalTheory.Member.PrincLevel.finCong_inv ha

theorem isOpen_congGroup {D : D7} (V : HSp D) {N : ℕ} (hN : 0 < N) : IsOpen (congGroup V N : Set (GA D V)) :=
  haveI : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  Subgroup.isOpen_of_mem_nhds _ (GlobalTheory.Member.PrincLevel.finCong_mem_nhds V hN)

theorem mem_of_isLevelK {D : D7} {V W : HSp D} (hV : V = W) {N : ℕ} {Kf : Subgroup (GA D V)} (hK : IsLevelK V N Kf)
    (k : GA D W) (h1 : k ∈ congGroup W N) (h2 : k ∈ GfC W) : cast (congrArg (GA D) hV.symm) k ∈ Kf := by
  subst hV
  exact (hK k).2 ⟨h2, h1⟩

theorem mem_levG_triv_iff {D : D7} {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    k ∈ levG (Wc D i) (L.βW i) (L.datWp i L.triv) ↔ IsLevelLift (Wc D i) (L.βW i) (L.datWp i L.triv) 1 k :=
  ⟨fun h => ⟨h.1, h.2.1, Subgroup.mem_bot.1 h.2.2⟩, fun h => ⟨h.1, h.2.1, Subgroup.mem_bot.2 h.2.2⟩⟩

theorem levChi_triv_eq_one {D : D7} {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    levChi (Wc D i) (L.βW i) (L.datWp i L.triv) k = 1 := by
  have h : ∀ x, ext1 L.triv.H L.triv.chi x = 1 := fun x => by
    unfold ext1; split_ifs <;> rfl
  unfold levChi levFn
  simp [LevCh.datWp, datY]
  exact h _


set_option maxHeartbeats 1000000 in
theorem principal_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, (∀ g : GA D (Wc D i), g ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) ↔ cast (congrArg (GA D) hV.symm) g ∈ T.Kf ((i : ℕ) + 1) (res T σ)) ∧ (∀ k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)), levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1) ∧ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) ≤ GfC (Wc D i) ∧ ∃ U : Subgroup (GA D (Wc D i)), IsOpen (U : Set (GA D (Wc D i))) ∧ ∀ k ∈ U, k ∈ GfC (Wc D i) → k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL _ ht hpb i σ hσ hV
  have key : ∀ g : GA D (Wc D i), g ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv) ↔
      cast (congrArg (GA D) hV.symm) g ∈ T.Kf ((i : ℕ) + 1) (res T σ) := fun g =>
    (mem_levG_triv_iff R.toLevCh i g).trans (GlobalTheory.T.level_character_embedding_compat T R κ v₀ hL ht hpb i (res T σ) hσ hV g)
  have hg : 0 < D.host.g 0 * D.host.g 1 := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  refine ⟨key, fun k _ => levChi_triv_eq_one R.toLevCh i k, fun k hk => hk.1,
    congGroup (Wc D i) (D.host.g 0 * D.host.g 1), isOpen_congGroup _ hg, fun k h1 h2 => (key k).2 ?_⟩
  exact mem_of_isLevelK hV (ht.laws.levelK _ (inR i) _ hσ) k h1 h2

end GlobalTheory.HolDict.PrincLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationPrincipalLevelEqCoreLevelOpenStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisation_principalLevel_eq_coreLevel_open : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, (∀ g : GA D (Wc D i), g ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) ↔ cast (congrArg (GA D) hV.symm) g ∈ T.Kf ((i : ℕ) + 1) (res T σ)) ∧ (∀ k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)), levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1) ∧ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) ≤ GfC (Wc D i) ∧ ∃ U : Subgroup (GA D (Wc D i)), IsOpen (U : Set (GA D (Wc D i))) ∧ ∀ k ∈ U, k ∈ GfC (Wc D i) → k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) := by
  first | exact @GlobalTheory.HolDict.PrincLev.principal_level | exact GlobalTheory.HolDict.PrincLev.principal_level | (intros; apply GlobalTheory.HolDict.PrincLev.principal_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairTermEqPointSumAnyTrivialisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairTermEqPointSumAnyTrivialisation
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

theorem term_eq_termAt : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (δ z : Gr G r), IsNrm G r P.atP δ z → P.term Kf f r K φ = P.termAt Kf f r K φ x t hx δ z := by
  intro p _ G P Kf f r K φ hr hf hφ x t hx δ z hn
  have hex : ∃ dz : Gr G r × Gr G r, IsNrm G r P.atP dz.1 dz.2 := ⟨(δ, z), hn⟩
  unfold term
  rw [dite_eq_left hex]
  set x₀ := P.trivAf.choose
  set t₀ := P.trivAf.choose_spec.choose
  have h₀ : Triv G (AfP p) P.β x₀ t₀ := P.trivAf.choose_spec.choose_spec
  set δ₀ := hex.choose.1
  set z₀ := hex.choose.2
  have hn₀ : IsNrm G r P.atP δ₀ z₀ := hex.choose_spec
  obtain ⟨_, hreg, hcent⟩ := GlobalTheory.T.similitudePair_regular_image_at_p p G P
  obtain ⟨g, hgx⟩ := GlobalTheory.T.hermitianTripleTrivializations_differ_by_group_point p G (AfP p) (P.β : G.C) x x₀ t t₀ hx h₀
  obtain ⟨g₂, hδ, hcz⟩ := GlobalTheory.T.twistedConj_of_twistedNormConj_hermitianTriple_regular p G r P.atP δ z δ₀ z₀ hr hreg hn hn₀
  have htw := GlobalTheory.T.map_centralizer_regular_twistedCentraliser p G r P.atP δ z hr hreg hn
  have hAf : P.toAf x₀ t₀ h₀ = (MulAut.conj g⁻¹⁻¹).toMonoidHom.comp (P.toAf x t hx) := by
    ext y : 1
    apply Subtype.ext
    apply Prod.ext
    · have e : x₀ = (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x := by rw [hgx, inv_mul_cancel_right]
      simp only [toAf, MonoidHom.comp_apply, MonoidHom.codRestrict_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, MonoidHom.prodMap, MonoidHom.prod_apply, Subgroup.coe_subtype]
      rw [e]; group
    · simp only [toAf, MonoidHom.comp_apply, MonoidHom.codRestrict_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, Prod.snd_mul, Prod.snd_inv, MonoidHom.prodMap, MonoidHom.prod_apply, Subgroup.coe_subtype]
      rw [mul_comm, inv_mul_cancel_left]
  have hQr : P.toQr r z₀ = (MulAut.conj g₂⁻¹).toMonoidHom.comp (P.toQr r z) := by
    ext y : 1
    have := hcz (locC G y.1) (hcent y)
    simp only [toQr, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [this]
  have hself : P.toAf x₀ t₀ h₀ P.self = g⁻¹⁻¹ * P.toAf x t hx P.self * g⁻¹ := by
    rw [hAf]; simp [MulAut.conj_apply]
  unfold termAt
  rw [hself, hAf, hQr, hδ]
  refine GlobalTheory.T.kottwitzIsogenyClassPointSum_conj_data _ _ _ _ _ _ _ _ _ _ _ hf hφ ?_ ?_
  · intro y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · exact y.2.1
    · exact mul_comm _ _
  · intro y
    have hm : P.toQr r z y ∈ GlobalTheory.BCT.twCent (sigG G r) δ := by
      rw [← htw]; exact ⟨locC G y.1, hcent y, rfl⟩
    exact hm

end GlobalTheory.LKMid.Pair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairTermEqPointSumAnyTrivialisationStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzPair_term_eq_pointSum_any_trivialisation : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (δ z : Gr G r), IsNrm G r P.atP δ z → P.term Kf f r K φ = P.termAt Kf f r K φ x t hx δ z := by
  first | (exact @GlobalTheory.LKMid.Pair.term_eq_termAt) | (exact GlobalTheory.LKMid.Pair.term_eq_termAt) | (intros; apply GlobalTheory.LKMid.Pair.term_eq_termAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjFormsRescale
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift

section Abstract

variable {K S V W W' : Type} [Field K] [AddCommGroup S] [Module K S] [AddCommGroup V] [Module K V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [NormedAddCommGroup W'] [InnerProductSpace ℂ W']

theorem rescale_span_eq {ι κ : Type} [Finite κ] (K0 : Subfield K) (f : Module.Basis ι K V) (b : Module.Basis κ K V)
    (h : ∀ i j, b.repr (f i) j ∈ K0) : Submodule.span K0 (Set.range f) = Submodule.span K0 (Set.range b) := by
  haveI : Finite ι := Finite.of_equiv κ (b.indexEquiv f)
  haveI := Fintype.ofFinite ι
  haveI := Fintype.ofFinite κ
  haveI : FiniteDimensional K0 (Submodule.span K0 (Set.range b)) := FiniteDimensional.span_of_finite K0 (Set.finite_range b)
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact (b.mem_span_iff_repr_mem K0 (f i)).2 fun j => ⟨⟨_, h i j⟩, rfl⟩
  · rw [finrank_span_eq_card (f.linearIndependent.restrict_scalars' K0),
      finrank_span_eq_card (b.linearIndependent.restrict_scalars' K0)]
    exact Fintype.card_congr (f.indexEquiv b)

theorem rescale_mem {ι κ : Type} [Finite κ] (K0 : Subfield K) (bS : Module.Basis ι K S) (b : Module.Basis κ K V)
    (e e' : S ≃ₗ[K] V) (h : ∀ i j, b.repr (e (bS i)) j ∈ K0) (h' : ∀ i j, b.repr (e' (bS i)) j ∈ K0) (a : κ) :
    e' (e.symm (b a)) ∈ Submodule.span K0 (Set.range b) := by
  have h1 := rescale_span_eq K0 (bS.map e) b h
  have h2 := rescale_span_eq K0 (bS.map e') b h'
  have h3 : b a ∈ Submodule.span K0 (Set.range (bS.map e)) := h1 ▸ Submodule.subset_span ⟨a, rfl⟩
  rw [← h2]
  generalize b a = x at h3
  induction h3 using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Submodule.subset_span ⟨i, by simp⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _)]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [Subfield.smul_def, map_smul, map_smul]
    exact Submodule.smul_mem _ r hx

theorem rescale_pair [StarRing K] {κ : Type} (b : κ → V) (σ : K →+* ℂ) (c₁ : V →ₛₗ[σ] W)
    (pair : V →ₗ⋆[K] V →ₗ[K] K) (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pair (b a) (b a')))
    {x y : V} (hx : x ∈ Submodule.span (Formalism.DivisionValues.cmMax K) (Set.range b))
    (hy : y ∈ Submodule.span (Formalism.DivisionValues.cmMax K) (Set.range b)) : inner ℂ (c₁ x) (c₁ y) = σ (pair x y) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a', rfl⟩ := hy
      exact hp a a'
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), inner_add_right, hx, hy, map_add (f := _), map_add (f := _)]
    | smul r x _ hx =>
      rw [Subfield.smul_def, LinearMap.map_smulₛₗ, inner_smul_right, hx, map_smul, smul_eq_mul, map_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), inner_add_left, hx, hy, map_add (f := _), LinearMap.add_apply, map_add (f := _)]
  | smul r x _ hx =>
    rw [Subfield.smul_def, LinearMap.map_smulₛₗ, inner_smul_left, hx, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, map_mul, ← r.2 σ]
    rfl

theorem rescale_inj {κ : Type} [Finite κ] (b : Module.Basis κ K V) (σ : K →+* ℂ) (c : V →ₛₗ[σ] W)
    (h : LinearIndependent ℂ fun a => c (b a)) : Function.Injective c := by
  haveI := Fintype.ofFinite κ
  refine (injective_iff_map_eq_zero c).2 fun x hx => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← b.sum_repr x, map_sum] at hx
  simp only [LinearMap.map_smulₛₗ] at hx
  have := Fintype.linearIndependent_iff.1 h _ hx
  exact b.ext_elem fun a => by simpa using this a

theorem rescale_span_top {κ : Type} [Finite κ] (b : Module.Basis κ K V) (σ : K →+* ℂ) (c : V →ₛₗ[σ] W) (φ : V ≃ₗ[K] V)
    (h : Submodule.span ℂ (Set.range fun a => c (b a)) = ⊤) :
    Submodule.span ℂ (Set.range fun a => c (φ (b a))) = ⊤ := by
  haveI := Fintype.ofFinite κ
  refine top_le_iff.1 (h ▸ Submodule.span_le.2 ?_)
  rintro _ ⟨a, rfl⟩
  have : b a = ∑ k, b.repr (φ.symm (b a)) k • φ (b k) := by
    conv_lhs => rw [← φ.apply_symm_apply (b a), ← b.sum_repr (φ.symm (b a))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  change c (b a) ∈ Submodule.span ℂ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [this, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem rescale_indep {κ : Type} [Finite κ] (u v : κ → W) (hi : LinearIndependent ℂ u)
    (hu : Submodule.span ℂ (Set.range u) = ⊤) (hv : Submodule.span ℂ (Set.range v) = ⊤) : LinearIndependent ℂ v := by
  haveI := Fintype.ofFinite κ
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge
    (Module.finrank_eq_card_basis (Module.Basis.mk hi hu.ge)).symm

theorem rescale_abstract [StarRing K] {ι κ : Type} [Finite κ] (bS : Module.Basis ι K S) (b : Module.Basis κ K V)
    (τ σ : K →+* ℂ) (p : S → W) (c0 c0' : V →ₛₗ[τ] W) (pair : V →ₗ⋆[K] V →ₗ[K] K) (q : S → S → K)
    (e e' : S ≃ₗ[K] V) (h : ∀ i j, b.repr (e (bS i)) j ∈ Formalism.DivisionValues.cmMax K)
    (h' : ∀ i j, b.repr (e' (bS i)) j ∈ Formalism.DivisionValues.cmMax K)
    (hc : ∀ x, p x = c0 (e x)) (hc' : ∀ x, p x = c0' (e' x))
    (hq : ∀ x y, pair (e x) (e y) = q x y) (hq' : ∀ x y, pair (e' x) (e' y) = q x y)
    (hi' : LinearIndependent ℂ fun a => c0' (b a)) (c₁ : V →ₛₗ[σ] W')
    (hi : LinearIndependent ℂ fun a => c₁ (b a)) (hs : Submodule.span ℂ (Set.range fun a => c₁ (b a)) = ⊤)
    (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pair (b a) (b a'))) :
    ∃ c₁' : V →ₛₗ[σ] W', (LinearIndependent ℂ fun a => c₁' (b a)) ∧
      Submodule.span ℂ (Set.range fun a => c₁' (b a)) = ⊤ ∧
      (∀ a a', inner ℂ (c₁' (b a)) (c₁' (b a')) = σ (pair (b a) (b a'))) ∧
      (∀ v', ∃ v, c0' v' = c0 v ∧ c₁ v' = c₁' v) ∧
      ∀ (r : V → V) (ρ : W → W) (ρ' : W' → W'), (∀ v, c0 (r v) = ρ (c0 v)) → (∀ v, c0' (r v) = ρ (c0' v)) →
        (∀ v, c₁ (r v) = ρ' (c₁ v)) → ∀ v, c₁' (r v) = ρ' (c₁' v) := by
  have hφ : ∀ v, c0' (e' (e.symm v)) = c0 v := fun v => by rw [← hc', hc, e.apply_symm_apply]
  have hs' := rescale_span_top b σ c₁ (e.symm.trans e') hs
  refine ⟨c₁.comp (e.symm.trans e').toLinearMap, rescale_indep _ _ hi hs hs', hs', fun a a' => ?_, fun v' => ?_,
    fun r ρ ρ' h0 h0' h1 v => ?_⟩
  · refine (rescale_pair b σ c₁ pair hp (rescale_mem _ bS b e e' h h' a) (rescale_mem _ bS b e e' h h' a')).trans ?_
    rw [hq', ← hq, e.apply_symm_apply, e.apply_symm_apply]
  · refine ⟨e (e'.symm v'), ?_, ?_⟩
    · rw [← hφ, e.symm_apply_apply, e'.apply_symm_apply]
    · simp
  · have : e' (e.symm (r v)) = r (e' (e.symm v)) := rescale_inj b τ c0' hi' (by rw [hφ, h0, h0', hφ])
    change c₁ (e' (e.symm (r v))) = ρ' (c₁ (e' (e.symm v)))
    rw [this, h1]

end Abstract

end GlobalTheory.GalLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChange
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjForms

theorem exists_conjChar {J K : Type} [Group J] [Field K] (σ₀ σ : K →+* ℂ) (χ : J →* ℂˣ)
    (hχ : ∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ)) :
    ∃ χ' : J →* ℂˣ, ∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ) ∧ σ y = ((χ' k : ℂˣ) : ℂ) := by
  choose y hy using hχ
  have h0 : ∀ k, σ (y k) ≠ 0 := fun k h => by
    have h1 := hy k
    rw [(map_eq_zero σ).1 h, map_zero] at h1
    exact (χ k).ne_zero h1.symm
  have hm : ∀ k k', y (k * k') = y k * y k' := fun k k' => σ₀.injective (by
    rw [map_mul, hy, hy, hy, map_mul, Units.val_mul])
  refine ⟨MonoidHom.mk' (fun k => Units.mk0 _ (h0 k)) fun k k' => Units.ext ?_, fun k => ⟨y k, hy k, rfl⟩⟩
  simp only [Units.val_mul, Units.val_mk0, hm, map_mul]

theorem exists_baseChange {G Γ W W' K M : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [FiniteDimensional ℂ W'] [Field K] [NumberField K] [StarRing K]
    [AddCommGroup M] [Module K M] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ} (σ : K →+* ℂ) {ρ : Γ →* Module.End ℂ W}
    (ρ' : Γ →* Module.End ℂ W') {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ₀ ρ J χ)
    (c₀ : M →ₛₗ[σ₀] W) (c₁ : M →ₛₗ[σ] W') (e : S.V ≃ₗ[K] M) (he : ∀ x, P.coef x = c₀ (e x))
    (hact : ∀ γ, ∃ T : M → M, (∀ v, c₀ (T v) = ρ γ (c₀ v)) ∧ ∀ v, c₁ (T v) = ρ' γ (c₁ v))
    (hχ : ∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ)) :
    ∃ (H : HMod (G → W')) (j : S.Forms →ₛₗ[σ] H.H),
      (∃ χ' : J →* ℂˣ, (∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ) ∧ σ y = ((χ' k : ℂˣ) : ℂ)) ∧
        H.Is (Bridge.AdForms ι ρ' J χ') (Bridge.adInner ι J P.y)) ∧
      ∀ x h, ∃ v, P.extL x h = c₀ v ∧ H.e (j x) h = c₁ v := by
  obtain ⟨χ', hχ'⟩ := exists_conjChar σ₀ σ χ hχ
  obtain ⟨H, hH⟩ := GlobalTheory.AdFormsModel.exists_hmod_adForms G Γ W' ι ρ' J χ' S.Cl P.y P.reps
    fun c => Finite.of_equiv _ (P.stabI c).toEquiv
  have hinj : Function.Injective c₀ := by
    intro v v' h
    obtain ⟨x, rfl⟩ := e.surjective v
    obtain ⟨x', rfl⟩ := e.surjective v'
    rw [← he, ← he] at h
    rw [GlobalTheory.PresBasic.coef_injective P h]
  have hv : ∀ (x : S.Forms) h, ∃ v, P.extL x h = c₀ v := by
    intro x h
    obtain ⟨y, hy, -⟩ := hχ' (P.decK h)
    obtain ⟨T, hT, -⟩ := hact (P.decG h)
    refine ⟨y • T (e ((x : S.Cl → S.V) (P.decC h))), ?_⟩
    rw [map_smulₛₗ, hy, hT, ← he]
    rfl
  choose v hv using hv
  obtain ⟨j, hj⟩ := GlobalTheory.HilbertModel.exists_lift_fun σ hH (fun x h => c₁ (v x h))
    (fun a b => by
      funext h
      have : v (a + b) h = v a h + v b h := hinj (by rw [map_add (f := _), ← hv, ← hv, ← hv, map_add (f := _)]; rfl)
      rw [this, map_add (f := _)]; rfl)
    (fun c a => by
      funext h
      have : v (c • a) h = c • v a h := hinj (by rw [map_smulₛₗ, ← hv, ← hv, map_smulₛₗ]; rfl)
      rw [this, map_smulₛₗ]; rfl)
    (fun a γ h k => by
      obtain ⟨y, hy, hy'⟩ := hχ' k
      obtain ⟨T, hT, hT'⟩ := hact γ
      have : v a (ι γ * h * k) = y • T (v a h) := hinj (by
        rw [map_smulₛₗ, hy, hT, ← hv, ← hv]
        exact GlobalTheory.PresBasic.extMem P a γ h k)
      show c₁ (v a (ι γ * h * k)) = _
      rw [this, map_smulₛₗ, hy', hT'])
  exact ⟨H, j, ⟨χ', hχ', hH⟩, fun x h => ⟨v x h, hv x h, congrFun (hj x) h⟩⟩

theorem factor_mem {I : Type} [Fintype I] {k : I → Type} [∀ a, CommRing (k a)] {r : ℕ} (hr : 0 < r) (S : Subfield ℂ)
    (c : ∀ a, (k a)ˣ →* ℂˣ)
    (h : ∀ g : ∀ a, GL (Fin r) (k a), (∏ a, ((c a (Matrix.GeneralLinearGroup.det (g a)) : ℂˣ) : ℂ)) ∈ S)
    (a : I) (u : (k a)ˣ) : ((c a u : ℂˣ) : ℂ) ∈ S := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨g, hg⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin r) (R := k a) u
  have h1 := h (Pi.mulSingle a g)
  rw [Finset.prod_eq_single a] at h1
  · rwa [Pi.mulSingle_eq_same, hg] at h1
  · intro b _ hb
    simp [Pi.mulSingle_eq_of_ne hb]
  · simp

theorem levFn_mem {D : D7} {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (L : LevDat D.host.E ℂ n) (S : Subfield ℂ)
    (hg : ∀ PP ∈ L.Pg, ∀ c u, ((L.cg c PP u : ℂˣ) : ℂ) ∈ S) (hq : L.Q = ∅) (x : GL (Fin n) (Lev.EAf D)) :
    ((levFn β (Lev.flag1L L) x : ℂˣ) : ℂ) ∈ S := by
  have h1 : ext1 (Lev.flag1L L).P.H (Lev.flag1L L).P.chi (rTup β (Lev.flag1L L) x) = 1 := Lev.subgroupCharExtension_one_apply _ _
  have h2 : (Lev.flag1L L).Q = ∅ := hq
  unfold levFn
  rw [h1, h2, one_mul, Finset.prod_empty, mul_one, Units.coe_prod]
  refine prod_mem fun PP hP => ?_
  rw [Units.coe_prod]
  exact prod_mem fun c _ => hg PP hP _ _

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_ratMat (V : HSp D) (γ : GQ V) : ∃ γE, Bridge.IsRatMat V γ γE := by
  obtain ⟨γ, hγ⟩ := γ
  unfold GQ HFinIn at hγ
  obtain ⟨g, -, hg⟩ := hγ
  exact ⟨g, hg.symm⟩

theorem chi_mem (R : RealDat D A Ks) (hW : R.grp_chiW) (i : Fin D.R.m) (PP : Pl D.host.E) (hP : PP ∈ R.Pg) (u : (kP PP)ˣ) :
    ((R.chi ((i : ℕ) + 1) PP u : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  refine factor_mem (I := R.Pg) (k := fun PP => kP PP.1) hr _ (fun PP => R.chi ((i : ℕ) + 1) PP.1) (fun g => ?_) ⟨PP, hP⟩ u
  have h := hW i (R.eG.symm g)
  rw [MulEquiv.apply_symm_apply] at h
  exact ⟨_, h⟩

theorem levChar_mem (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (hW : R.grp_chiW) (i : Fin D.R.m) (k : levJ R i A.μ0) :
    ∃ y, D.what₂.embLL y = (((levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k : ℂˣ) : ℂ) := by
  have hQ : R.Q A.μ0 = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP hP => ?_
    refine (hL.Q_ram A.μ0 PP).2 (Or.inl hP) ?_
    rw [hL.xi_base]
    intro x _
    rfl
  refine levFn_mem (R.βV i) (R.datVt i A.μ0) D.what₂.embLL.fieldRange (fun PP hP c u => ?_) hQ _
  show (((R.chi ((i : ℕ) + 1) PP u)⁻¹ : ℂˣ) : ℂ) ∈ _
  rw [Units.val_inv_eq_inv_val]
  exact inv_mem (chi_mem R hW i PP hP u)


end GlobalTheory.ConjForms

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastWeightPositive
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

theorem lastPos_wtA_of_kapIs : ∀ (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → KapIs κ → ∀ i : Fin D.R.m, LastPos (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) :=
  fun D T κ h hκ i =>
    GlobalTheory.lastPos_wtA_of_pins D T.Q h.pins _ (inR i) (κ i) (GlobalTheory.HolDict.lastPos_of_kapIs D κ hκ i)

end GlobalTheory.HolRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
noncomputable section

namespace GlobalTheory.XTermMaj

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def crd (x : AE F E) : Fin (Module.finrank F E) → AF F :=
  (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun x

def maj (N : ℕ) (U : Set (Fin (Module.finrank F E) → Af F)) (x : AE F E) : ENNReal :=
  U.indicator (fun _ => ENNReal.ofReal ((1 + ∑ i, ∑ v : InfinitePlace F, ‖(crd F E x i).1 v‖) ^ (-(N : ℝ))))
    (fun i => (crd F E x i).2)

end GlobalTheory.XTermMaj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CircleEqOneIffOfConj
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift

theorem circle_eq_one_iff_of_conj {K L : Type} [Field K] [Field L] [Algebra K L] (s t : L →+* ℂ) (a b : Circle) (y : K)
    (ha : (a : ℂ) = s (algebraMap K L y)) (hb : (b : ℂ) = t (algebraMap K L y)) : b = 1 ↔ a = 1 := by
  rw [← Circle.coe_eq_one, ← Circle.coe_eq_one, ha, hb, map_eq_one_iff t t.injective, map_eq_one_iff s s.injective]

theorem logHookSum_of_bijective {D : D7} (i : Fin D.R.m) (l : D.what₂.Tau → D.what₂.Tau) (hl : Function.Bijective l) :
    logHookSum i l = logHookSum i id := by
  have hs : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) :=
    fun ρ => D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  unfold logHookSum
  simp only [pW, qW, hs, id]
  exact hl.sum_comp (fun ρ => Real.log ((hookRows (D.R.sigW ((i : ℕ) + 1)).1 (aPl D i (D.R.sigW ((i : ℕ) + 1)).1 ρ) *
    hookRows (D.R.sigW ((i : ℕ) + 1)).2 (aMi D i (D.R.sigW ((i : ℕ) + 1)).1 (D.R.sigW ((i : ℕ) + 1)).2 ρ) : ℕ) : ℝ))

end GlobalTheory.GalLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchIff
noncomputable section

namespace GlobalTheory.ThK.PolynomialMatching

open scoped TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def PolMatchOn (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (T : Finset (Pl F)) (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ) : Prop :=
  ∃ (m m' : ℕ) (f : Fin m → SInf F _) (φ : Fin m → ∀ v : Pl F, (_ → Fv F v) → ℂ)
    (f' : Fin m' → SInf F _) (φ' : Fin m' → ∀ v : Pl F, (_ → Fv F v) → ℂ),
    (∀ i, f i ∈ G.M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = G.M.vac v) ∧
    (∀ j, f' j ∈ G.M'.Pol B.ψ B.emb ∧ (∀ v, φ' j v ∈ SB _) ∧ ∀ v ∉ T, φ' j v = G.M'.vac v) ∧
    Φ = ∑ i, pure (f i) (φ i) ∧ Φ' = ∑ j, pure (f' j) (φ' j) ∧
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v))

theorem polMatch_iff (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ) :
    PolMatch B G X R Rf Φ Φ' ↔ ∃ T : Finset (Pl F), X.T ⊆ T ∧ PolMatchOn B G X R Rf T Φ Φ' := Iff.rfl

end GlobalTheory.ThK.PolynomialMatching
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfConjOnFinite
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjCharUnique

theorem eq_of_conj_on_finite {D : D7} {σ : D.what₂.LL →+* ℂ} {μ μ' μ'' : (AE D)ˣ →* Circle}
    (h1 : IsHeckeChar D μ') (g1 : IsHeckeChar D μ'')
    (h : ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : D.what₂.LL,
      ((μ x : Circle) : ℂ) = D.what₂.embLL y ∧ ((μ' x : Circle) : ℂ) = σ y)
    (g : ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : D.what₂.LL,
      ((μ x : Circle) : ℂ) = D.what₂.embLL y ∧ ((μ'' x : Circle) : ℂ) = σ y) : μ' = μ'' := by
  refine MonoidHom.ext fun x => mul_inv_eq_one.1 (GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (μ' * μ''⁻¹)
    ⟨h1.1.mul g1.1.inv, fun k => mul_inv_eq_one.2 ((h1.2 k).trans (g1.2 k).symm)⟩
    (fun y hy => mul_inv_eq_one.2 ?_) x)
  obtain ⟨a, ha, ha'⟩ := h y hy
  obtain ⟨b, hb, hb'⟩ := g y hy
  obtain rfl : a = b := D.what₂.embLL.injective (ha.symm.trans hb)
  exact Subtype.ext (ha'.trans hb'.symm)

end GlobalTheory.ConjCharUnique
end
