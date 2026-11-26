module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.CosBijPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.FirstChernHodgeTateFacts
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.IsFirstChernFamily

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PartialDerivativeAlgebra
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C5 PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq

set_option linter.unusedSectionVars false

namespace PositivityTheory.SiegelWeilFormula.Act.C6

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} {L : LD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}


variable (L) in
structure Hyp (nb : nA σ d.Y d.b → d.G) (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (w₁ : d.G)
    (cM : (Fin L.n → AE F E) × AF F → d.G) (δ : E) : Prop where
  nb : IsNMap d.b nb
  uM : ∀ u, ∃ a', inFrame d.b (uM u) = Matrix.fromBlocks (uA L u) 0 0 a'
  nb' : IsNMap L.b nb'
  wr : w₁ ∈ rat2 σ d.Y
  wf : ∃ a b : E, a ≠ 0 ∧ b ≠ 0 ∧ inFrame d.b w₁ = 1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 -
      Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 + Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) (inclR (F := F) (AF F) a) +
      Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) (inclR (F := F) (AF F) b)
  cf : ∀ c, ∃ A', inFrame d.b (cM c) = Matrix.fromBlocks (uA L c.1) (aB L δ c.2) 0 A'
  δ0 : δ ≠ 0


variable (L) in
abbrev Cr : Type := {c : (Fin L.n → AE F E) × AF F // c.1 ∈ L.ratV ∧ c.2 ∈ (algebraMap F (AF F)).range}


variable (L) in
def Fix (x : d.G) : Prop :=
  ∀ k, inFrame d.b x k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)

theorem fix_mul {x y : d.G} (hx : Fix L x) (hy : Fix L y) : Fix L (x * y) := by
  intro k
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply, Finset.sum_eq_single (Sum.inl L.i₀)]
  · rw [hy, Matrix.one_apply_eq, mul_one]; exact hx k
  · intro j _ hj; rw [hy j, Matrix.one_apply_ne hj, mul_zero]
  · simp

theorem fix_inv {x : d.G} (hx : Fix L x) : Fix L x⁻¹ := by
  intro k
  have h1 := congrFun (congrFun (GlobalTheory.EisBL.DoubledParabolic.inFrame_inv_mul d.b x) k) (Sum.inl L.i₀)
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inl L.i₀)] at h1
  · rw [hx, Matrix.one_apply_eq, mul_one] at h1; exact h1
  · intro j _ hj; rw [hx j, Matrix.one_apply_ne hj, mul_zero]
  · simp

theorem fix_j (g : G2 σ L.Y) : Fix L (L.j g) := by
  intro k
  exact (L.j_out g (Sum.inl L.i₀) (by simp) k).2

theorem lagrangian_condition_parabolic_iff {p g : d.G} (hp : p ∈ par2 σ d.Y) : LagrangianCondition L (p * g) ↔ LagrangianCondition L g := by
  constructor
  · intro h1
    have := lagrangian_condition_parabolic_mul L ((par2 σ d.Y).inv_mem hp) h1
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  · exact lagrangian_condition_parabolic_mul L hp

theorem not_lagrangian_w1_mul (h : Hyp L nb uM nb' w₁ cM δ) {g : d.G} (hg : Fix L g) : ¬ LagrangianCondition L (w₁ * g) := by
  intro hS
  obtain ⟨a₀, b₀, ha, hb, hW⟩ := h.wf
  have h1 := hS L.i₀
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply, Finset.sum_eq_single (Sum.inl L.i₀)] at h1
  · rw [hg, Matrix.one_apply_eq, mul_one, hW] at h1
    simp [Matrix.single_apply, Matrix.one_apply] at h1
    exact hb (kfour.inclR_injective (F := F) (by rw [h1, map_zero]))
  · intro j _ hj; rw [hg j, Matrix.one_apply_ne hj, mul_zero]
  · simp

theorem out_mk (d : SD σ) (γ : rat2 σ d.Y) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ rep (Quotient.mk _ γ : Cs d) = p * γ.1 := by
  exact rep_mk γ

theorem mk_eq_mk (d : SD σ) {γ γ' : rat2 σ d.Y} :
    (Quotient.mk _ γ : Cs d) = Quotient.mk _ γ' ↔ γ'.1 * γ.1⁻¹ ∈ par2 σ d.Y := by
  rw [Quotient.eq, QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
  simp

theorem rep_mem (d : SD σ) (q : Cs d) : rep q ∈ rat2 σ d.Y := (Quotient.out q).2

theorem mk_rep (d : SD σ) (q : Cs d) : (Quotient.mk _ ⟨rep q, rep_mem d q⟩ : Cs d) = q := Quotient.out_eq q

theorem mul_eq_zero_of_supp {ι : Type} [Fintype ι] (P : ι → Prop) {M N : Matrix ι ι (AE F E)}
    (hM : ∀ r l, ¬ P l → M r l = 0) (hN : ∀ l c, P l → N l c = 0) : M * N = 0 := by
  ext r c
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : P l
  · rw [hN l c hl, mul_zero]
  · rw [hM r l hl, zero_mul]

theorem w1_mul_j_comm (h : Hyp L nb uM nb' w₁ cM δ) (g : G2 σ L.Y) : w₁ * L.j g = L.j g * w₁ := by
  obtain ⟨a₀, b₀, ha, hb, hW⟩ := h.wf
  apply kunf.inFrame_injective d.b
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul]
  set W := inFrame d.b w₁
  set J := inFrame d.b (L.j g)
  have hJ := pad_j L g
  let P : Fin d.n ⊕ Fin d.n → Prop := fun l => l = Sum.inl L.i₀ ∨ l = Sum.inr L.i₀
  have hWo : ∀ r c, ¬ (P r ∧ P c) → (W - 1) r c = 0 := by
    intro r c hrc
    rw [Matrix.sub_apply, hW]
    simp only [P, not_and_or] at hrc
    rcases hrc with hr | hr <;> push_neg at hr <;>
      simp [Matrix.single_apply, Matrix.one_apply, hr.1, hr.2, Ne.symm hr.1, Ne.symm hr.2]
  have hJo : ∀ r c, (P r ∨ P c) → (J - 1) r c = 0 := by
    intro r c hrc
    rw [Matrix.sub_apply, sub_eq_zero]
    rcases hrc with (h | h) | (h | h)
    · exact hJ r c (Or.inl h)
    · exact hJ r c (Or.inr (Or.inl h))
    · exact hJ r c (Or.inr (Or.inr (Or.inl h)))
    · exact hJ r c (Or.inr (Or.inr (Or.inr h)))
  have e1 : (W - 1) * (J - 1) = 0 :=
    mul_eq_zero_of_supp P (fun r l hl => hWo r l fun h => hl h.2) (fun l c hl => hJo l c (Or.inl hl))
  have e2 : (J - 1) * (W - 1) = 0 :=
    mul_eq_zero_of_supp (fun l => ¬ P l) (fun r l hl => hJo r l (Or.inr (not_not.1 hl))) (fun l c hl => hWo l c fun h => hl h.1)
  have eW : W = 1 + (W - 1) := by abel
  have eJ : J = 1 + (J - 1) := by abel
  rw [eW, eJ]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, e1, e2]
  abel

theorem cA_inv' (hσ : ∀ x, σ (σ x) = x) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, hσ]
  | add a b ha hb => simp [map_add (f := _), ha, hb]

theorem uA_neg_mul (u : Fin L.n → AE F E) : uA L (-u) * uA L u = 1 := by
  have := C1.Au_mul L (-u) u
  simp only [neg_add_cancel] at this
  rw [show uA L (-u) * uA L u = C1.Au L (-u) * C1.Au L u from rfl, this]
  simp [C1.Au]

theorem cM_frame (h : Hyp L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) :
    inFrame d.b (cM c) = Matrix.fromBlocks (uA L c.1) (aB L δ c.2) 0 ((uA L (-c.1))ᵀ.map (cA σ)) := by
  obtain ⟨A', hA'⟩ := h.cf c
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  have h2 := kunf.frame_eq hε (cM c)
  rw [hA'] at h2
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one,
    Matrix.map_zero _ (map_zero (cA σ))] at h2
  have h1 : (uA L c.1)ᵀ * A'.map (cA σ) = 1 := (Matrix.fromBlocks_inj.1 h2).2.1
  have h1' : A'.map (cA σ) * (uA L c.1)ᵀ = 1 := mul_eq_one_comm.1 h1
  have hinv : (uA L c.1)ᵀ * (uA L (-c.1))ᵀ = 1 := by rw [← Matrix.transpose_mul, uA_neg_mul, Matrix.transpose_one]
  have e : A'.map (cA σ) = (uA L (-c.1))ᵀ := by
    calc A'.map (cA σ) = A'.map (cA σ) * ((uA L c.1)ᵀ * (uA L (-c.1))ᵀ) := by rw [hinv, Matrix.mul_one]
      _ = (uA L (-c.1))ᵀ := by rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
  have e2 : A' = (uA L (-c.1))ᵀ.map (cA σ) := by
    rw [← e, Matrix.map_map]
    ext i j
    simp [cA_inv' hσ]
  rw [hA', e2]

theorem fix_cM' (h : Hyp L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) : Fix L (cM c) := by
  intro k
  rw [cM_frame h]
  rcases k with k | k
  · simp [uA, Matrix.one_apply, Matrix.single_apply, Matrix.sum_apply, C4.em_ne L]
  · simp

theorem cM_rat' (h : Hyp L nb uM nb' w₁ cM δ) {c : (Fin L.n → AE F E) × AF F} (hu : c.1 ∈ L.ratV)
    (ha : c.2 ∈ (algebraMap F (AF F)).range) : cM c ∈ rat2 σ d.Y := by
  obtain ⟨u₀, hu₀⟩ := ComplexParameterFamilyContinuity.mem_ratVec.1 hu
  obtain ⟨a₀, ha₀⟩ := ha
  refine kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (u₀ j))
    (Matrix.single L.i₀ L.i₀ (a₀ • δ)) 0 ((1 + ∑ j, Matrix.single L.i₀ (L.em j) (-u₀ j))ᵀ.map σ)) ?_
  rw [cM_frame h, ← hu₀, ← ha₀, Afc.incM_fromBlocks, kfour.incM_zero]
  congr 1
  · ext i k
    simp [incM, uA, GlobalTheory.ThK.incV, Matrix.single_apply, Matrix.one_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  · ext i k
    simp only [incM, aB, Matrix.map_apply, Matrix.single_apply]
    split_ifs
    · show (algebraMap F (AF F) a₀) • ((1 : AF F) ⊗ₜ[F] δ) = (1 : AF F) ⊗ₜ[F] (a₀ • δ)
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one,
        ← Algebra.algebraMap_eq_smul_one]
    · simp
  · have hc (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := by
      show Algebra.TensorProduct.map _ _ ((1 : AF F) ⊗ₜ[F] a) = (1 : AF F) ⊗ₜ[F] σ a
      simp
    ext i k
    simp [incM, uA, GlobalTheory.ThK.incV, Matrix.single_apply, Matrix.one_apply, Matrix.sum_apply, hc]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [hc]

theorem emS_cM (h : Hyp L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) :
    (inFrame d.b (cM c)).submatrix (emS L) (emS L) = 1 := by
  ext r r'
  rcases r with k | k <;> rcases r' with k' | k' <;>
    simp [cM_frame h, emS, uA, aB, Matrix.one_apply, Matrix.single_apply, Matrix.sum_apply, C4.em_ne L, L.inj.eq_iff,
      Ne.symm (C4.em_ne L _)] <;> split_ifs <;> simp

end PositivityTheory.SiegelWeilFormula.Act.C6

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PhzEqFlat
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C4

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} (L : LD d)

theorem phz_eq_flat {s₁ z : ℂ} {f : d.G → ℂ} : phz d f s₁ z = flat d.a f s₁ z := by
  funext x
  simp only [phz, GlobalTheory.ThK.Dbl.flat, kunf.ht_eq]

theorem phz_law {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) :
    Law d.χ (z - s₁ + (s₁ + (d.n : ℂ) / 2)) (phz d f s₁ z) := by
  rw [phz_eq_flat]
  exact Law.flat hf.law d.ok.hgt (kunf.a_pos d) z

theorem phz_par {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {p : d.G} {t : GL (Fin d.n) (AE F E)}
    (hp : IsPar p t) (ht : Matrix.GeneralLinearGroup.det t = 1) (g : d.G) : phz d f s₁ z (p * g) = phz d f s₁ z g := by
  rw [phz_law hf z p t g hp, ht, map_one, map_one]
  simp

theorem phz_rat {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {p : d.G} (hp : p ∈ par2 σ d.Y)
    (hr : p ∈ rat2 σ d.Y) (g : d.G) : phz d f s₁ z (p * g) = phz d f s₁ z g :=
  (phz_law hf z).rat d.ok.hecke hp hr g

theorem key_id {nb : nA σ d.Y d.b → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} (hnb : IsNMap d.b nb)
    (hnb' : IsNMap L.b nb') {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) (h : G2 σ L.Y) (β : nA σ d.Y d.b) (u : Fin L.n → AE F E)
    (x : d.G) : ∃ p t, IsPar p t ∧ Matrix.GeneralLinearGroup.det t = 1 ∧
      L.j h * (nb β * (uM u * x)) = p * (L.j (h * nb' (prj L β)) * x) := by
  exact key_id_pf L hnb hnb' hU h β u x

theorem tr_sub {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T') (β : nA σ d.Y d.b) :
    Matrix.trace (T.1.1 * β.1) = Matrix.trace (T'.1.1 * (prj L β).1) := by
  obtain ⟨h0, h1⟩ := hT
  have hout : ∀ i, i ∉ Set.range L.em → i = L.i₀ := fun i hi => by
    by_contra h
    exact hi ((L.rng i).1 h)
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, prj_val, h1, Matrix.submatrix_apply]
  symm
  refine Fintype.sum_of_injective L.em L.inj _ _ (fun i hi => ?_) (fun a => ?_)
  · rw [hout i hi]
    simp [(h0 _).1]
  · refine Fintype.sum_of_injective L.em L.inj _ _ (fun k hk => ?_) (fun b => rfl)
    rw [hout k hk]
    simp [(h0 _).2]

theorem cos_bij : ∃ e : Cs L.sd ≃ {q : Cs d // LagrangianCondition L (rep q)}, ∀ q', ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧
    rep (e q').1 = p * L.j (rep q') := by
  exact cos_bij_pf L

end PositivityTheory.SiegelWeilFormula.Act.C4

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.LocCompactNA
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

set_option linter.unusedSectionVars false

namespace PositivityTheory.SiegelWeilFormula.Act.C1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isClosed_nA (d : SD σ) : IsClosed (nA σ d.Y d.b : Set (Matrix (Fin d.n) (Fin d.n) (AE F E))) := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hc : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have e : (nA σ d.Y d.b : Set (Matrix (Fin d.n) (Fin d.n) (AE F E))) =
      {β | βᵀ = -((((ε : ℤ) : AE F E)) • β.map (cA σ))} := Set.ext fun β => kunf.mem_nA_iff hε β
  rw [e]
  exact isClosed_eq continuous_id.matrix_transpose (((continuous_id.matrix_map hc).const_smul (((ε : ℤ) : AE F E))).neg)

instance locCompact_nA (d : SD σ) : LocallyCompactSpace (nA σ d.Y d.b) :=
  haveI : LocallyCompactSpace (Matrix (Fin d.n) (Fin d.n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin d.n → Fin d.n → AE F E))
  (isClosed_nA d).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem coef_periodic (d : SD σ) {nb : nA σ d.Y d.b → d.G} (hN : IsNMap d.b nb) (φ : d.G → ℂ)
    (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) (T : nF σ d.Y d.b) (g : d.G) (β₀ : nF σ d.Y d.b)
    (β : nA σ d.Y d.b) :
    φ (nb (β₀ +ᵥ β) * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * (β₀ +ᵥ β).1)))) =
      φ (nb β * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) := by
  have e1 : (β₀ +ᵥ β : nA σ d.Y d.b) = β₀.1 + β := rfl
  have e2 : ((β₀.1 + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = β₀.1.1 + β.1 := rfl
  rw [e1, kunf.nb_add hN, mul_assoc, hφ _ (kunf.nb_rat hN β₀.2), e2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add,
    AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, kunf.psi_rat d.ok.good.std T β₀, inv_one, one_mul]

variable {d : SD σ} {L : LD d}

theorem cj_mp {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) {v : Fin L.n → AE F E} (hv : v ∈ L.ratV) :
    MeasurePreserving (cj hU h.1 v) lam lam := by
  have := h.2.1
  refine ⟨(continuous_cj hU h.1 v).measurable, ?_⟩
  have hl := latHaar (nA σ d.Y d.b) lam (nF σ d.Y d.b) (cjE hU h.1 v) (fun x => ⟨fun hx => ?_, fun hx => cj_rat hU h.1 hv hx⟩)
    𝓖 h.2.2.1 (by rw [h.2.2.2]; exact one_ne_zero) (by rw [h.2.2.2]; exact ENNReal.one_ne_top)
  · exact hl
  · have := cj_rat hU h.1 (neg_mem hv) hx
    rwa [show cj hU h.1 (-v) (cjE hU h.1 v x) = x from cj_inv hU h.1 v x] at this

theorem fc_conj {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) (φ : d.G → ℂ) (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g)
    {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T') {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) (g : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * g) = fc d.B.ψ d.b nb lam 𝓖 φ T g := by
  have := h.2.1
  have : VAddInvariantMeasure (nF σ d.Y d.b) (nA σ d.Y d.b) lam := ⟨fun c s _ => measure_preimage_add lam c.1 s⟩
  let H : nA σ d.Y d.b → ℂ := fun β =>
    φ (nb β * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
  have e1 : ∀ β, φ (nb β * (uM u * g)) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) =
      H (cj hU h.1 u β) := by
    intro β
    have e : nb β * (uM u * g) = uM u * (nb (cj hU h.1 u β) * g) := by rw [nb_cj hU h.1 u β]; group
    simp only [H]
    rw [e, hφ _ (uM_rat hU hu), trace_cj hU h.1 hT]
  have hme : MeasurableEmbedding (cj hU h.1 u) := (cjE hU h.1 u).toHomeomorph.measurableEmbedding
  have himg : (cj hU h.1 u) '' 𝓖 = (cj hU h.1 (-u)) ⁻¹' 𝓖 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show cj hU h.1 (-u) (cj hU h.1 u x) ∈ 𝓖
      rwa [cj_inv]
    · intro hy
      refine ⟨cj hU h.1 (-u) y, hy, ?_⟩
      simpa using cj_inv hU h.1 (-u) y
  have hfd : IsAddFundamentalDomain (nF σ d.Y d.b) ((cj hU h.1 (-u)) ⁻¹' 𝓖) lam := by
    refine h.2.2.1.preimage_of_equiv (cj_mp h hU (neg_mem hu)).quasiMeasurePreserving
      (e := fun γ => ⟨cj hU h.1 u γ.1, cj_rat hU h.1 hu γ.2⟩) ⟨fun γ γ' hγ => ?_, fun γ => ?_⟩ fun γ x => ?_
    · have := congrArg (fun y : nF σ d.Y d.b => cj hU h.1 (-u) y.1) hγ
      simp only [cj_inv] at this
      exact Subtype.ext this
    · refine ⟨⟨cj hU h.1 (-u) γ.1, cj_rat hU h.1 (neg_mem hu) γ.2⟩, Subtype.ext ?_⟩
      simpa using cj_inv hU h.1 (-u) γ.1
    · show cj hU h.1 (-u) ((cj hU h.1 u γ.1) + x) = γ.1 + cj hU h.1 (-u) x
      rw [map_add (f := _), cj_inv]
  unfold fc
  simp_rw [e1]
  rw [← (cj_mp h hU hu).setIntegral_image_emb hme H 𝓖, himg,
    hfd.setIntegral_eq h.2.2.1 (fun β₀ β => coef_periodic d h.1 φ hφ T g β₀ β)]

end PositivityTheory.SiegelWeilFormula.Act.C1

end
end
