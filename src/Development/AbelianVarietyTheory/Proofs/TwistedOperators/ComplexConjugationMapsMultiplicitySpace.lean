module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmStar
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjMult

section Rep

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

def realEquiv (c : H' ≃ₗᵢ⋆[ℂ] H) : H' ≃L[ℝ] H where
  toFun := c
  invFun := c.symm
  map_add' := map_add c
  map_smul' r x := by
    rw [← Complex.coe_smul, map_smulₛₗ]
    simp
  left_inv := c.symm_apply_apply
  right_inv := c.apply_symm_apply
  continuous_toFun := c.continuous
  continuous_invFun := c.symm.continuous

theorem expProd_mem (hJ : IsUnit J.det) {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i, (Xs i)ᴴ * J + J * Xs i = 0) (t : Fin k → ℝ) :
    (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ Formalism.QuantumDeterminants.UH J := by
  refine List.prod_induction _ (fun a b => mul_mem_UH J) (one_mem_UH J) fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  exact GlobalTheory.SmoothAutCheck.exp_mem_UH hJ (hX i) _

theorem smoothVec_conj (hJ : IsUnit J.det) (c : H' ≃ₗᵢ⋆[ℂ] H)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ w, c (σ' g w) = σ g (c w)) {w : H'}
    (hw : SmoothVec {X | Xᴴ * J + J * X = 0} σ' w) : SmoothVec {X | Xᴴ * J + J * X = 0} σ (c w) := by
  intro k Xs hX
  have := (realEquiv c).contDiff.comp (hw k Xs hX)
  convert this using 2 with t
  exact (hc _ (expProd_mem hJ hX t) w).symm

theorem span_conj (hJ : IsUnit J.det) (c : H' ≃ₗᵢ⋆[ℂ] H)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ w, c (σ' g w) = σ g (c w)) {w : H'}
    (hw : w ∈ Submodule.span ℂ {w | SmoothVec {X | Xᴴ * J + J * X = 0} σ' w}) :
    c w ∈ Submodule.span ℂ {w | SmoothVec {X | Xᴴ * J + J * X = 0} σ w} := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (smoothVec_conj hJ c hc hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

theorem dRep_conj (hJ : IsUnit J.det) (c : H' ≃ₗᵢ⋆[ℂ] H)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ w, c (σ' g w) = σ g (c w)) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : Xᴴ * J + J * X = 0) (w : H') : dRep σ X (c w) = c (dRep σ' X w) := by
  have e : (fun t : ℝ => σ (NormedSpace.exp (t • X)) (c w)) =
      realEquiv c ∘ fun t : ℝ => σ' (NormedSpace.exp (t • X)) w :=
    funext fun t => (hc _ (GlobalTheory.SmoothAutCheck.exp_mem_UH hJ hX t) w).symm
  rw [dRep, e, deriv, ContinuousLinearEquiv.comp_fderiv]
  rfl

theorem sobCont_conj (hJ : IsUnit J.det) (c : H' ≃ₗᵢ⋆[ℂ] H)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ w, c (σ' g w) = σ g (c w)) {ℓ : H →ₗ[ℂ] ℂ}
    (h : Sobolev₂ {X | Xᴴ * J + J * X = 0} σ ℓ) :
    ∃ ℓ' : H' →ₗ[ℂ] ℂ, Sobolev₂ {X | Xᴴ * J + J * X = 0} σ' ℓ' ∧ ∀ w, ℓ' w = star (ℓ (c w)) := by
  obtain ⟨S, C, hS, hC⟩ := h
  refine ⟨{ toFun := fun w => star (ℓ (c w))
            map_add' := fun x y => by simp
            map_smul' := fun a x => by rw [map_smulₛₗ, map_smul]; simp }, ⟨S, C, hS, fun w hw => ?_⟩, fun _ => rfl⟩
  have e : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, Xᴴ * J + J * X = 0) →
      l.foldr (dRep σ) (c w) = c (l.foldr (dRep σ') w) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons X l ih =>
      intro hl
      rw [List.foldr_cons, ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY), dRep_conj hJ c hc (hl X List.mem_cons_self),
        List.foldr_cons]
  have h1 := hC _ (smoothVec_conj hJ c hc hw)
  have h2 : (S.map fun l => ‖l.foldr (dRep σ) (c w)‖) = S.map fun l => ‖l.foldr (dRep σ') w‖ :=
    List.map_congr_left fun l hl => by rw [e l (hS l hl), c.norm_map]
  rw [h2] at h1
  exact (norm_star _).trans_le h1

theorem prod_conj {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g.det) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    l.prod * g = g * (l.map fun a => g⁻¹ * a * g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, mul_assoc, ih]
    simp only [mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hg]

theorem smoothVec_act (hJ : IsUnit J.det)
    (hm : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ g' ∈ Formalism.QuantumDeterminants.UH J, ∀ w, σ (g * g') w = σ g (σ g' w))
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH J) {w : H}
    (hw : SmoothVec {X | Xᴴ * J + J * X = 0} σ w) : SmoothVec {X | Xᴴ * J + J * X = 0} σ (σ g w) := by
  intro k Xs hX
  have hu := isUnit_of_UH hJ hg
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have hi : (g⁻¹)ᴴ * J * g⁻¹ = J := by
    have : (hu.unit⁻¹).1 ∈ Formalism.QuantumDeterminants.UH J := (UG J).inv_mem (x := hu.unit) hg
    rwa [Matrix.coe_units_inv] at this
  have hg' : gᴴ * J * g = J := hg
  have hX' : ∀ i, (g⁻¹ * Xs i * g)ᴴ * J + J * (g⁻¹ * Xs i * g) = 0 := fun i => by
    have h1 : (g⁻¹)ᴴ * J = J * g := by
      conv_rhs => rw [← hi]
      rw [Matrix.nonsing_inv_mul_cancel_right _ _ hd]
    have h2 : J * g⁻¹ = gᴴ * J := by
      conv_lhs => rw [← hg']
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ hd]
    have h3 : (Xs i)ᴴ * J + J * Xs i = 0 := hX i
    calc _ = gᴴ * (Xs i)ᴴ * ((g⁻¹)ᴴ * J) + J * g⁻¹ * Xs i * g := by
          simp only [Matrix.conjTranspose_mul, mul_assoc]
      _ = gᴴ * ((Xs i)ᴴ * J + J * Xs i) * g := by rw [h1, h2]; simp only [mul_add, add_mul, mul_assoc]
      _ = 0 := by rw [h3, mul_zero, zero_mul]
  have := ((σ g).restrictScalars ℝ).contDiff.comp (hw k _ hX')
  convert this using 2 with t
  change _ = σ g (σ _ w)
  rw [← hm _ (expProd_mem hJ hX t) _ hg, ← hm _ hg _ (expProd_mem hJ hX' t), prod_conj hd, List.map_ofFn]
  congr 5
  funext i
  rw [Function.comp_apply, ← Matrix.exp_conj' _ _ hu, mul_smul_comm, smul_mul_assoc]

end Rep

variable {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar}

theorem rep_one (M : DSModel V S) (τ : D.what₂.Tau) (w : M.H τ) : M.rep τ 1 w = w := by
  have h1 : M.σ τ 1 = 1 := (M.ds τ).2.2.1.1.1
  rw [DSModel.rep, mul_one, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), h1]
  rfl

theorem rep_mul (M : DSModel V S) (τ : D.what₂.Tau) : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, M.rep τ (g * g') w = M.rep τ g (M.rep τ g' w) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have key : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ UJset (M.ε τ) := fun g hg => by
    have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
    rw [← M.fr_gram τ] at hg'
    change _ * _ * _ = _
    calc _ = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
          simp only [Matrix.conjTranspose_mul, mul_assoc]
      _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
          rw [hg']; simp only [Matrix.conjTranspose_mul, mul_assoc]
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  intro g hg g' hg' w
  have h := (M.ds τ).2.2.1.1.2 _ (key g hg) _ (key g' hg')
  have e : M.fr τ * (g * g') * (M.fr τ)⁻¹ = (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * g' * (M.fr τ)⁻¹) := by
    simp only [mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  rw [DSModel.rep, e, h]
  rfl

theorem rep_mem_sm (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {w : M.H τ} (hw : w ∈ M.sm τ) : M.rep τ g w ∈ M.sm τ := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    exact Submodule.subset_span (smoothVec_act (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (rep_mul M τ) hg hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem value_mem_homFun {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M}
    (h : IsMultMap θ M J χ T) (v : M.Vec) : T v ∈ homFun θ V := by
  classical
  have h1 : ∀ y ∈ realMon θ V, ∀ v, ∃ v', ∀ x, T v (x * y) = T v' x := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem y hy =>
      obtain ⟨τ, g, hg, rfl⟩ := hy
      intro v
      exact ⟨_, fun x => (congrFun (h.equiv τ g hg v ⟨_, rep_mem_sm M τ hg (v τ).2⟩ rfl) x).symm⟩
    | one => exact fun v => ⟨v, fun x => by rw [mul_one]⟩
    | mul a b _ _ ha hb =>
      intro v
      obtain ⟨v₁, h₁⟩ := hb v
      obtain ⟨v₂, h₂⟩ := ha v₁
      exact ⟨v₂, fun x => by rw [← mul_assoc, h₁, h₂]⟩
  intro y hy τ x
  obtain ⟨u, hu⟩ := h1 y hy v
  simp only [hu]
  refine ⟨?_, fun g hg g' hg' => ?_⟩
  · have := congrFun (h.equiv τ 1 (one_mem_UH _) u (u τ) (rep_one M τ _).symm) x
    rw [Function.update_eq_self] at this
    exact this.symm
  · have a1 := congrFun (h.equiv τ g' hg' u ⟨_, rep_mem_sm M τ hg' (u τ).2⟩ rfl) (x * atTau θ V τ g)
    have a2 := congrFun (h.equiv τ (g * g') (mul_mem_UH _ hg hg') u ⟨_, rep_mem_sm M τ (mul_mem_UH _ hg hg') (u τ).2⟩ rfl) x
    have a3 := congrFun (h.equiv τ g hg (Function.update u τ ⟨_, rep_mem_sm M τ hg' (u τ).2⟩)
      ⟨_, rep_mem_sm M τ (mul_mem_UH _ hg hg') (u τ).2⟩ (by rw [Function.update_self]; exact rep_mul M τ g hg g' hg' _)) x
    rw [Function.update_idem] at a3
    exact a1.symm.trans (a3.symm.trans a2)

theorem conj_mult : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → (∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) ∧ ∀ J χ, ∀ T ∈ Mult θ M J χ, ∃ T' ∈ Mult θ M' J (fun k => star (χ k)), ∀ (v' : M'.Vec) (v : M.Vec), (∀ τ, (v τ : M.H τ) = c τ (v' τ)) → ∀ g, T' v' g = star (T v g) := by
  intro D V S S' θ M M' c hc
  classical
  have hs : ∀ τ {w : M'.H τ}, w ∈ M'.sm τ → c τ w ∈ M.sm τ := fun τ _ hw =>
    span_conj (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (c τ) (hc τ) hw
  refine ⟨fun τ w => ⟨hs τ, fun hw => ?_⟩, fun J χ T hT => ?_⟩
  · have := span_conj (σ := M'.rep τ) (σ' := M.rep τ) (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (c τ).symm
      (fun g hg w => (c τ).injective (by rw [hc τ g hg, (c τ).apply_symm_apply, (c τ).apply_symm_apply])) hw
    rwa [(c τ).symm_apply_apply] at this
  have h := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ T).1 hT
  let cs : ∀ τ, M'.sm τ → M.sm τ := fun τ w => ⟨c τ w, hs τ w.2⟩
  let cv : M'.Vec → M.Vec := fun v τ => cs τ (v τ)
  have hup : ∀ [DecidableEq D.what₂.Tau] (v : M'.Vec) τ w, cv (Function.update v τ w) = Function.update (cv v) τ (cs τ w) :=
    fun v τ w => funext fun ρ => Function.apply_update cs v τ w ρ
  let T' : MMap M' :=
    { toFun := fun v => star (T (cv v))
      map_update_add' := fun v τ x y => by
        have : cs τ (x + y) = cs τ x + cs τ y := Subtype.ext (map_add (c τ) _ _)
        rw [hup, hup, hup, this, T.map_update_add, star_add]
      map_update_smul' := fun v τ a x => by
        have : cs τ (a • x) = star a • cs τ x := Subtype.ext (map_smulₛₗ (c τ) _ _)
        rw [hup, hup, this, T.map_update_smul, star_smul]
        simp only [RingHom.id_apply, star_star] }
  have hT' : ∀ v, T' v = star (T (cv v)) := fun _ => rfl
  refine ⟨T', Submodule.subset_span ⟨fun v => isAutFunSm_star (h.aut _) (value_mem_homFun h _), fun v => ?_,
    fun v k hk g => ?_, fun τ g hg v w hw => ?_, fun τ v x => ?_⟩, fun v' v hv g => ?_⟩
  · intro r C hC μ 𝓕 hμ h𝓕 g
    have := h.cusp (cv v) r C hC μ 𝓕 hμ h𝓕 g
    change ∫ n in 𝓕, starRingEnd ℂ (T (cv v) ((n : GA D V) * g)) ∂μ = 0
    rw [integral_conj, this, map_zero]
  · rw [hT', Pi.star_apply, Pi.star_apply, h.lev _ k hk, star_mul']
  · rw [hT', hT', hup, h.equiv τ g hg (cv v) (cs τ w) (by change c τ w = _; rw [hw, hc τ g hg])]
    rfl
  · obtain ⟨ℓ, h1, h2⟩ := h.cont τ (cv v) x
    obtain ⟨ℓ', h3, h4⟩ := sobCont_conj (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (c τ) (hc τ) h1
    refine ⟨ℓ', h3, fun w => ?_⟩
    rw [h4, hT', hup, Pi.star_apply, ← h2]
  · have : cv v' = v := funext fun τ => Subtype.ext (hv τ).symm
    rw [hT', this, Pi.star_apply]

end GlobalTheory.ConjMult

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpaceStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexConjugation_maps_multiplicitySpace : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → (∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) ∧ ∀ J χ, ∀ T ∈ Mult θ M J χ, ∃ T' ∈ Mult θ M' J (fun k => star (χ k)), ∀ (v' : M'.Vec) (v : M.Vec), (∀ τ, (v τ : M.H τ) = c τ (v' τ)) → ∀ g, T' v' g = star (T v g) := by
  first | exact @GlobalTheory.ConjMult.conj_mult | exact GlobalTheory.ConjMult.conj_mult | (intros; apply GlobalTheory.ConjMult.conj_mult <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
noncomputable section

namespace GlobalTheory.Grow

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open GlobalTheory.AdelicU (EmbOver htInf htFin compInf compFin infProj opNorm)
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (infHt infNorm)
open GlobalTheory.SmoothForms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem infEmb_tmul_one_eq_extensionEmbedding {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {w : InfinitePlace F} {τ : E →+* ℂ} (hτ : τ.comp (algebraMap F E) = w.embedding)
    {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) (b : Ainf F) :
    θ (b ⊗ₜ[F] (1 : E)) = InfinitePlace.Completion.extensionEmbedding w (b w) := by
  have hc : Continuous fun b : Ainf F => InfinitePlace.Completion.extensionEmbedding w (b w) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
  have key := (InfiniteAdeleRing.denseRange_algebraMap F).equalizer hθ.2 hc ?_
  · exact congrFun key b
  funext x
  simp only [Function.comp_apply]
  rw [← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply', hθ.1,
    ← RingHom.comp_apply, hτ]
  simp

theorem htInf_eq_infMat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {w : InfinitePlace F} (t : EmbOver E w)
    [StarRing E] {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb t.1 θ) (g : HA (AF F) σ J) :
    htInf F w (bc (compInf F E w) (GlobalTheory.AdelicU.matHom _ σ J g)) =
      max 1 (max (opNorm (infMat σ J θ g)) (opNorm (infMat σ J θ g⁻¹))) := by
  have hre := infEmb_tmul_one_eq_extensionEmbedding t.2 hθ
  have hz : ∀ z : AF F ⊗[F] E, GlobalTheory.AdelicU.infEmb t (compInf F E w z) =
      θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have e : (fstA F a) ⊗ₜ[F] x = ((fstA F a) ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] x) := by simp
      simp only [GlobalTheory.AdelicU.compInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, GlobalTheory.AdelicU.infEmb_tmul]
      rw [e, map_mul, hre, hθ.1]
      rfl
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have hm : ∀ k : HA (AF F) σ J, ((bc (compInf F E w) (GlobalTheory.AdelicU.matHom _ σ J k) : GL (Fin n) _) :
      Matrix (Fin n) (Fin n) _).map (GlobalTheory.AdelicU.infEmb t) = infMat σ J θ k := by
    intro k
    ext i j
    exact hz _
  show max 1 (max (GlobalTheory.AdelicU.normInf F w _) (GlobalTheory.AdelicU.normInf F w _)) = _
  rw [GlobalTheory.AdelicU.normInf_eq_opNorm h t, GlobalTheory.AdelicU.normInf_eq_opNorm h t, ← map_inv (bc (compInf F E w)),
    ← map_inv (GlobalTheory.AdelicU.matHom _ σ J), hm, hm]

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (V : HSp D)

theorem htInf_eq_infHt (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g : GA D V) :
    htInf D.host.F (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
      (bc (compInf D.host.F D.host.E _) (Formalism.L2.Theta.matHom V g)) = infHt θ V τ g := by
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have ht : (tauE D τ).comp (algebraMap D.host.F D.host.E) =
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))).embedding :=
    (InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.mp (hcm.1.isReal _))).symm
  exact (htInf_eq_infMat hcm V.gram ⟨_, ht⟩ (hθ τ) g).trans rfl

private theorem htFin_eq_one_of_mem_GinfC {g : GA D V} (hg : g ∈ GinfC V) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    htFin D.host.F v (bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom V g)) = 1 := by
  have hk : Formalism.L2.Theta.finHom V g = 1 := hg
  have hz : ∀ z : AF D.host.F ⊗[D.host.F] D.host.E, compFin D.host.F D.host.E v z =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add y z hy hz => rw [map_add (f := _), map_add (f := _), map_add (f := _), hy, hz]
  have h1 : bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom V g) = 1 := by
    apply Units.ext
    ext i j
    have hij : Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
        (((Formalism.L2.Theta.matHom V g : GL _ _) : Matrix _ _ _) i j) =
        ((1 : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) : Matrix _ _ _) i j := by
      rw [← hk]; rfl
    show compFin D.host.F D.host.E v (((Formalism.L2.Theta.matHom V g : GL _ _) : Matrix _ _ _) i j) = _
    rw [hz, hij, Units.val_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [h1]
  refine (GlobalTheory.AdelicU.htOf_eq_one).2 ⟨?_, ?_⟩ <;> simpa using GlobalTheory.AdelicU.normFin_one_le D.host.F v

theorem height_eq_prod_infHt (hθ : IsInfFam θ) {g : GA D V} (hg : g ∈ GinfC V) :
    height V g = ∏ τ, (infHt θ V τ g : ℝ) := by
  have hinf : ∏ w, htInf D.host.F w (bc (compInf D.host.F D.host.E w) (Formalism.L2.Theta.matHom V g)) =
      ∏ τ, infHt θ V τ g :=
    (Fintype.prod_bijective _ (GlobalTheory.CMTypePlaces.places_bijective D) _ _
      fun τ => (htInf_eq_infHt V hθ τ g).symm).symm
  show ((GlobalTheory.AdelicU.heightGL D.host.F (Formalism.L2.Theta.matHom V g) : NNReal) : ℝ) = _
  rw [GlobalTheory.AdelicU.heightGL, hinf]
  simp only [htFin_eq_one_of_mem_GinfC V hg, finprod_one, mul_one, NNReal.coe_prod]

theorem normInf_le_height (hθ : IsInfFam θ) : ∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * height V g := by
  refine ⟨2 * (Fintype.card D.what₂.Tau * V.rank * V.rank : ℝ), fun g => ?_⟩
  have hb : ∀ τ, (infHt θ V τ g : ℝ) ≤ height V g := fun τ => by
    have := htInf_le_height V g (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
    rwa [htInf_eq_infHt V hθ τ g] at this
  have he : ∀ τ i j, ‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖ ≤
      2 * height V g := by
    intro τ i j
    have h1 := GlobalTheory.SmoothForms.NormInf.norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g) i j
    have h2 := GlobalTheory.SmoothForms.NormInf.norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g⁻¹) i j
    have h3 : infNorm θ V τ g ≤ infHt θ V τ g := le_max_of_le_right (le_max_left _ _)
    have h4 : infNorm θ V τ g⁻¹ ≤ infHt θ V τ g := le_max_of_le_right (le_max_right _ _)
    have h3' : (infNorm θ V τ g : ℝ) ≤ height V g := (NNReal.coe_le_coe.2 h3).trans (hb τ)
    have h4' : (infNorm θ V τ g⁻¹ : ℝ) ≤ height V g := (NNReal.coe_le_coe.2 h4).trans (hb τ)
    have e3 : (infNorm θ V τ g : ℝ) =
        ‖Matrix.toEuclideanCLM (n := Fin V.rank) (𝕜 := ℂ) (infMat D.sp.cm.sig V.gram (θ τ) g)‖ := rfl
    have e4 : (infNorm θ V τ g⁻¹ : ℝ) =
        ‖Matrix.toEuclideanCLM (n := Fin V.rank) (𝕜 := ℂ) (infMat D.sp.cm.sig V.gram (θ τ) g⁻¹)‖ := rfl
    linarith
  calc normInf θ V g = ∑ τ, ∑ i, ∑ j,
        (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := rfl
    _ ≤ ∑ _τ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, 2 * height V g := by
        gcongr with τ _ i _ j _
        exact he τ i j
    _ = 2 * (Fintype.card D.what₂.Tau * V.rank * V.rank : ℝ) * height V g := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem height_le_normInf_pow (hθ : IsInfFam θ) : ∃ d : ℕ, ∀ g ∈ GinfC V, height V g ≤ normInf θ V g ^ d := by
  rcases Nat.eq_zero_or_pos V.rank with h0 | hpos
  · refine ⟨0, fun g hg => ?_⟩
    rw [height_eq_prod_infHt V hθ hg, pow_zero]
    simp [GlobalTheory.SmoothForms.HeightCoset.infHt_rank_zero θ V h0]
  · refine ⟨Fintype.card D.what₂.Tau, fun g hg => ?_⟩
    rw [height_eq_prod_infHt V hθ hg, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun τ _ => NNReal.coe_nonneg _)
      (fun τ _ => GlobalTheory.SmoothForms.HeightCoset.infHt_le_normInf θ V hpos τ g)

theorem normInf_height_comparison (D : D7) (V : HSp D)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) :
    (∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * height V g) ∧
      ∃ (C : ℝ) (d : ℕ), ∀ g ∈ GinfC V, height V g ≤ C * (1 + normInf θ V g) ^ d := by
  obtain ⟨C, hC⟩ := normInf_le_height V hθ
  obtain ⟨d, hd⟩ := height_le_normInf_pow V hθ
  refine ⟨⟨C, hC⟩, 1, d, fun g hg => ?_⟩
  have h0 : 0 ≤ normInf θ V g := by
    unfold Formalism.L2.Theta.normInf
    positivity
  calc height V g ≤ normInf θ V g ^ d := hd g hg
    _ ≤ (1 + normInf θ V g) ^ d := pow_le_pow_left₀ h0 (by linarith) d
    _ = 1 * (1 + normInf θ V g) ^ d := (one_mul _).symm

private theorem exists_coset_bound_of_modGrowthExp (V : HSp D) {d : ℕ} (hd : ∀ g ∈ GinfC V, height V g ≤ normInf θ V g ^ d) {A : ℕ}
    {f : GA D V → ℂ} (hf : ModGrowthExp V A f) (x : GA D V) :
    ∃ C : ℝ, ∀ g ∈ GinfC V, ‖f (x * g)‖ ≤ C * normInf θ V g ^ (d * A) := by
  obtain ⟨C, hC⟩ := hf
  have hC0 : 0 ≤ C := nonneg_of_growth hC
  refine ⟨C * height V x ^ A, fun g hg => ?_⟩
  have h1 : height V (x * g) ≤ height V x * normInf θ V g ^ d :=
    (height_mul_le V x g).trans (mul_le_mul_of_nonneg_left (hd g hg) (height_pos V x).le)
  calc ‖f (x * g)‖ ≤ C * height V (x * g) ^ A := hC _
    _ ≤ C * (height V x * normInf θ V g ^ d) ^ A :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos V _).le h1 A) hC0
    _ = C * height V x ^ A * normInf θ V g ^ (d * A) := by rw [mul_pow, ← pow_mul]; ring

variable {V}

theorem exists_modGrowthExp_le_normInf_pow (hθ : IsInfFam θ) (A : ℕ) :
    ∃ N : ℕ, ∀ f : GA D V → ℂ, ModGrowthExp V A f →
      ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V, ‖f (x * g)‖ ≤ C * normInf θ V g ^ N := by
  obtain ⟨d, hd⟩ := height_le_normInf_pow V hθ
  exact ⟨d * A, fun f hf x => exists_coset_bound_of_modGrowthExp V hd hf x⟩

theorem UnifModGrowth.growth (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : UnifModGrowth V θ φ) :
    ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
        ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨N, hN⟩ := exists_modGrowthExp_le_normInf_pow (V := V) hθ A
  exact ⟨N, fun l hl x => hN _ (hA l hl) x⟩

theorem UnifModGrowth.isAutFunSm (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : UnifModGrowth V θ φ) (ha : IsAutFun V φ)
    (hs : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod))
    (hz : ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W) :
    IsAutFunSm θ V φ :=
  { toIsAutFun := ha, smooth := hs, zfin := hz, growth := h.growth hθ }

end GlobalTheory.Grow

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOnOne
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

variable {D : D7}

def TameOn (χ : (AE D)ˣ →* Circle) (e : AE D) (P : Finset (Pl D.host.E))
    (c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∀ hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
    toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → cA D e * (x : AE D) = cA D e →
    ∀ u : ∀ PP : Pl D.host.E, (kP PP)ˣ, (∀ PP ∈ P, (u PP : kP PP) = resS D.host.F PP ⟨toEAf D (x : AE D), hx⟩) →
      ((χ x : Circle) : ℂ) = ∏ PP ∈ P, ((c PP (u PP) : ℂˣ) : ℂ)

def vacScal {S T : HSp D} (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E))
    (cS cT : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (g : GA D S) (h : GA D T) : ℂ :=
  ∏ PP ∈ P, (((cT PP (Matrix.GeneralLinearGroup.det (redFn βS PP (finE S g))) : ℂˣ) : ℂ)⁻¹ *
    ((cS PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ))


open Classical in
def resChr {T0 : Type} (L : LevCh D T0) (t : T0) (n : ℕ) (PP : Pl D.host.E) : (kP PP)ˣ →* ℂˣ :=
  if PP ∈ L.Pg then (L.chi n PP)⁻¹ else L.xiR t PP

end GlobalTheory.StepLaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicitySpaceEqZeroOfApplyNonzeroTensorZero
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicitySpaceEqZeroOfApplyNonzeroTensorZero
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

noncomputable def tprodInnerFun {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] (w : ∀ i, E i) : (⨂[ℂ] i, E i) →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap (fun i => (innerSL ℂ (w i)).toLinearMap))

theorem tprodInnerFun_tprod {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] (w v : ∀ i, E i) :
    tprodInnerFun w (PiTensorProduct.tprod ℂ v) = ∏ i, ⟪w i, v i⟫_ℂ := by
  simp [tprodInnerFun]

theorem eq_zero_of_tprodInnerFun {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] (x : ⨂[ℂ] i, E i) (h : ∀ w, tprodInnerFun w x = 0) : x = 0 := by
  classical
  have hx : x ∈ Submodule.span ℂ (Set.range (PiTensorProduct.tprod ℂ (s := E))) := by
    rw [PiTensorProduct.span_tprod_eq_top]; trivial
  obtain ⟨n, f, g, hg⟩ := Submodule.mem_span_set'.1 hx
  choose v hv using fun j => (g j).2
  let W : ∀ i, Submodule ℂ (E i) := fun i => Submodule.span ℂ (Set.range fun j => v j i)
  haveI : ∀ i, FiniteDimensional ℂ (W i) := fun i =>
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let b := fun i => stdOrthonormalBasis ℂ (W i)
  have hexp : ∀ j i, v j i = ∑ k, ⟪(b i k : E i), v j i⟫_ℂ • (b i k : E i) := by
    intro j i
    have hm : v j i ∈ W i := Submodule.subset_span ⟨j, rfl⟩
    have := congrArg (fun z : W i => (z : E i)) ((b i).sum_repr' ⟨v j i, hm⟩)
    simpa using this.symm
  have hj : ∀ j, PiTensorProduct.tprod ℂ (v j) =
      ∑ k : ∀ i, Fin (Module.finrank ℂ (W i)),
        (∏ i, ⟪(b i (k i) : E i), v j i⟫_ℂ) • PiTensorProduct.tprod ℂ (fun i => (b i (k i) : E i)) := by
    intro j
    have e : v j = fun i => ∑ k, ⟪(b i k : E i), v j i⟫_ℂ • (b i k : E i) := funext (hexp j)
    conv_lhs => rw [e]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [MultilinearMap.map_smul_univ]
    simp only [RingHom.id_apply]
  have hx' : x = ∑ j, f j • PiTensorProduct.tprod ℂ (v j) := by
    rw [← hg]; simp [hv]
  have key : x = ∑ k : ∀ i, Fin (Module.finrank ℂ (W i)),
      tprodInnerFun (fun i => (b i (k i) : E i)) x • PiTensorProduct.tprod ℂ (fun i => (b i (k i) : E i)) := by
    conv_rhs => rw [hx']
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, tprodInnerFun_tprod, Finset.sum_smul]
    rw [Finset.sum_comm, hx']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hj j, Finset.smul_sum]
    simp [smul_smul]
  rw [key]; simp [h]

theorem eq_zero_of_integral_fundDomain {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure]
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (F : G → ℂ) (hc : Continuous F)
    (hinv : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) (hi : IntegrableOn (fun g => star (F g) * F g) 𝓕 μ)
    (h0 : ∫ g in 𝓕, star (F g) * F g ∂μ = 0) : F = 0 := by
  have e : ∀ g, star (F g) * F g = ((‖F g‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.conj_mul']; simp
  simp only [e] at hi h0
  rw [integral_complex_ofReal] at h0
  have h0' : ∫ g in 𝓕, ‖F g‖ ^ 2 ∂μ = 0 := by exact_mod_cast h0
  have hi' : Integrable (fun g => ‖F g‖ ^ 2) (μ.restrict 𝓕) := by
    have := Integrable.re hi
    simpa only [RCLike.re_to_complex, Complex.ofReal_re] using this
  have hae := (integral_eq_zero_iff_of_nonneg (fun g => by positivity) hi').1 h0'
  have hae' : ∀ᵐ g ∂μ.restrict 𝓕, F g = 0 := hae.mono fun g hg => by simpa using hg
  have ho : IsOpen {g | F g ≠ 0} := isOpen_ne_fun hc continuous_const
  have hz : μ {g | F g ≠ 0} = 0 := by
    refine h𝓕.measure_zero_of_invariant _ (fun γ => ?_) ?_
    · ext g
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp only [Set.mem_setOf_eq]
      rw [Subgroup.smul_def, smul_eq_mul, hinv _ (γ⁻¹).2]
    · rw [← Measure.restrict_apply ho.measurableSet]
      exact hae'
  have := (ho.measure_eq_zero_iff μ).1 hz
  funext g
  by_contra hg
  have : g ∈ {g | F g ≠ 0} := hg
  simp_all

theorem multT_eq_zero_of_apply_eq_zero : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ J χ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M J χ μ 𝓕 → ∀ u ∈ MultT θ M J χ, ∀ x : ⨂[ℂ] τ, M.sm τ, x ≠ 0 → u x = 0 → u = 0 := by
  intro D V S θ M J χ μ 𝓕 hθ hμ h𝓕 hS u hu x hx hux
  obtain ⟨-, -, -, hB, hG, -, hC⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  rw [mem_multT] at hu
  set T : MMap M := PiTensorProduct.lift.symm u with hT
  have hTv : ∀ v, T v = u (PiTensorProduct.tprod ℂ v) := fun v => by simp [hT]
  obtain ⟨c, hc⟩ := hS hθ hμ h𝓕 T hu T hu
  have hall : ∀ (w : M.Vec) (y : ⨂[ℂ] τ, M.sm τ), IntegrableOn (fun g => star (T w g) * u y g) 𝓕 μ ∧
      ∫ g in 𝓕, star (T w g) * u y g ∂μ = c * tprodInnerFun w y := by
    intro w y
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      obtain ⟨h1, h2⟩ := hc w v
      have e : (fun g => star (T w g) * u (r • PiTensorProduct.tprod ℂ v) g) =
          fun g => r * (star (T w g) * T v g) := by
        funext g; rw [map_smul, ← hTv]; simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [e]
      refine ⟨h1.const_mul r, ?_⟩
      rw [integral_const_mul, h2, map_smul, tprodInnerFun_tprod]
      simp only [Submodule.coe_inner, smul_eq_mul]; ring
    | add y z hy hz =>
      have e : (fun g => star (T w g) * u (y + z) g) =
          fun g => star (T w g) * u y g + star (T w g) * u z g := by
        funext g; rw [map_add (f := _)]; simp only [Pi.add_apply]; ring
      rw [e]
      refine ⟨hy.1.add hz.1, ?_⟩
      rw [integral_add hy.1 hz.1, hy.2, hz.2, map_add (f := _)]; ring
  have hc0 : c = 0 := by
    by_contra hne
    refine hx (eq_zero_of_tprodInnerFun x fun w => ?_)
    have := (hall w x).2
    rw [hux] at this
    simp only [Pi.zero_apply, mul_zero, integral_zero] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hne
  have hT0 : ∀ v, T v = 0 := by
    intro v
    obtain ⟨h1, h2, -⟩ := GlobalTheory.mult_value_left_cont_level θ M J χ T hu v
    refine eq_zero_of_integral_fundDomain (GQ V) μ 𝓕 h𝓕 (T v) h2 h1 (hc v v).1 ?_
    rw [(hc v v).2, hc0, zero_mul]
  refine PiTensorProduct.ext ?_
  ext v g
  simp [← hTv, hT0]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicitySpaceEqZeroOfApplyNonzeroTensorZeroStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicitySpace_eq_zero_of_apply_nonzero_tensor_zero : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ J χ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M J χ μ 𝓕 → ∀ u ∈ MultT θ M J χ, ∀ x : ⨂[ℂ] τ, M.sm τ, x ≠ 0 → u x = 0 → u = 0 := by
  first | exact @GlobalTheory.multT_eq_zero_of_apply_eq_zero | exact GlobalTheory.multT_eq_zero_of_apply_eq_zero | (intros; apply GlobalTheory.multT_eq_zero_of_apply_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.SmGL

structure SmRep (G : Type) [Group G] [TopologicalSpace G] : Type 1 where

  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]

  ρ : Representation ℂ G V
  smooth : IsSmooth ρ

attribute [instance] SmRep.acg SmRep.mod

def SmRep.ofIrr {G : Type} [Group G] [TopologicalSpace G] (σ : IrrRep G) : SmRep G :=
  ⟨σ.V, σ.ρ, σ.smooth⟩

section Inhabitant

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Inhabitant

end GlobalTheory.SmGL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnFundamentalDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CocompactIntegrable

theorem integrableOn_of_cocompact {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (𝓕 C : Set G)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : G, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (F : G → ℂ) (hF : Continuous F)
    (hinv : ∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) : IntegrableOn F 𝓕 μ := by
  have hle : μ 𝓕 ≤ μ C := by
    rw [h𝓕.measure_eq_tsum C]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    intro h hh
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨c, hc, rfl⟩, hh⟩
  have hfin : μ 𝓕 ≠ ⊤ := (hle.trans_lt hC.measure_lt_top).ne
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
  refine Measure.integrableOn_of_bounded (M := M) hfin hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun h => ?_)
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
  rw [hinv γ hγ]
  exact hM c hc

theorem integrableOn_fundamentalDomain : ∀ {D : D7} (V : HSp D) (μ : Measure (GA D V)) (𝓕 C : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → IsCompact C → (∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c) → ∀ F : GA D V → ℂ, Continuous F → (∀ γ ∈ GQ V, ∀ h, F (γ * h) = F h) → IntegrableOn F 𝓕 μ := by
  intro D V μ 𝓕 C hμ h𝓕 hC hcov F hF hinv
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  exact integrableOn_of_cocompact (GQ V) μ 𝓕 C h𝓕 hC hcov F hF hinv

end GlobalTheory.CocompactIntegrable
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtEqInfMat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilDeriv

theorem compAt_mt_eq_infMat {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) :
    compAt θ τ (mt V g) = infMat D.sp.cm.sig V.gram (θ τ) g := by
  ext i j
  simp only [compAt, Formalism.L2.Theta.mt, infMat, matHom, Matrix.map_apply]
  rfl

theorem om_dRho_infMat : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (g : GA D S) (h : GA D T) τ z f, IsThetaFunO ψ S T f → om (g, h) (Datum.dRho (heisO ψ S T) θ τ z f) = Datum.dRho (heisO ψ S T) θ τ (infMat D.sp.cm.sig T.gram (θ τ) h * z * infMat D.sp.cm.sig S.gram (θ τ) g⁻¹) (om (g, h) f) := by
  intro D ψ S T χS χT om hW θ hθ g h τ z f hf
  rw [← compAt_mt_eq_infMat θ τ T h, ← compAt_mt_eq_infMat θ τ S g⁻¹]
  exact GlobalTheory.WeilVacMove.om_dRho hW hθ g h τ z hf

end GlobalTheory.WeilDeriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityInnerProductUnitTwistedRightTranslat
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityInnerProductUnitTwistedRightTranslat
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isMultiplicityInner_of_unit_twist_shift : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ J χ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (κ : GA D V) (a : ℂ), ‖a‖ = 1 → Measure.map (fun g => g * κ) μ = μ → ∀ T ∈ Mult θ M J χ, ∀ T' ∈ Mult θ M J χ, ∀ U U' : MMap M, (∀ v g, U v g = a * T v (g * κ)) → (∀ v g, U' v g = a * T' v (g * κ)) → ∀ c, IsMultIP M μ 𝓕 T T' c → IsMultIP M μ 𝓕 U U' c := by
  intro D V S θ M J χ μ 𝓕 hμ h𝓕 κ a ha hκ T hT T' hT' U U' hU hU' c hc
  obtain ⟨hLC, hSC, hB, hC⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  unfold IsMultIP at hc ⊢
  intro v v'
  have haa : star a * a = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ha]
    norm_num
  have hfun : (fun g => star (U v g) * U' v' g) = fun g => star (T v (g * κ)) * T' v' (g * κ) := by
    funext g
    rw [hU, hU', star_mul']
    calc star a * star (T v (g * κ)) * (a * T' v' (g * κ))
        = (star a * a) * (star (T v (g * κ)) * T' v' (g * κ)) := by ring
      _ = star (T v (g * κ)) * T' v' (g * κ) := by rw [haa, one_mul]
  have hinv : ∀ γ ∈ GQ V, ∀ g, star (T v (γ * g)) * T' v' (γ * g) = star (T v g) * T' v' g := by
    intro γ hγ g
    rw [(GlobalTheory.mult_value_left_cont_level θ M J χ T hT v).1 γ hγ g,
      (GlobalTheory.mult_value_left_cont_level θ M J χ T' hT' v').1 γ hγ g]
  have key := GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ V) μ 𝓕 h𝓕 κ hκ
    (fun g => star (T v g) * T' v' g) hinv (hc v v').1
  rw [hfun]
  exact ⟨key.1, key.2.trans (hc v v').2⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityInnerProductUnitTwistedRightTranslatStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicityInnerProduct_unit_twisted_right_translation : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ J χ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (κ : GA D V) (a : ℂ), ‖a‖ = 1 → Measure.map (fun g => g * κ) μ = μ → ∀ T ∈ Mult θ M J χ, ∀ T' ∈ Mult θ M J χ, ∀ U U' : MMap M, (∀ v g, U v g = a * T v (g * κ)) → (∀ v g, U' v g = a * T' v (g * κ)) → ∀ c, IsMultIP M μ 𝓕 T T' c → IsMultIP M μ 𝓕 U U' c := by
  first | exact @GlobalTheory.isMultiplicityInner_of_unit_twist_shift | exact GlobalTheory.isMultiplicityInner_of_unit_twist_shift | (intros; apply GlobalTheory.isMultiplicityInner_of_unit_twist_shift <;> assumption)
end
end
