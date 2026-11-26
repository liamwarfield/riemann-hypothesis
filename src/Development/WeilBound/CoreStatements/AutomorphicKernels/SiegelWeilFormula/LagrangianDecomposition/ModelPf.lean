module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceVacuumIsLocalVacuumChart
public import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.ResAdm

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelPf
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem Bf_zero_left {m n : ℕ} (J : Matrix (Fin m) (Fin m) E) (Z : Mx F E m n) : Bf σ J 0 Z = 0 := by
  simp [Bf]

theorem tof_adapted {m n : ℕ} {A : Spc F E m} {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} (bs : Module.Basis (Fin 2) F E)
    (ψ : AddChar (AF F) ℂ)
    {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2)}
    (had : IsAdapted bs A Y b dd) (Φ : (Fin m × Fin n × Fin 2 → AF F) → ℂ) (X : Mx F E m n) :
    Tof ψ dd (ev0 _) b Φ X = Φ (crdB bs X) := by
  have e := had 0 X
  rw [Matrix.zero_mul, zero_add] at e
  change dd.e (X * (b.1.toCols₂.map (inclR (AF F)))ᵀ) = _ at e
  simp only [Tof, ev0, LinearMap.coe_mk, AddHom.coe_mk, Darboux.rho, schr, e, Bf_zero_left]
  simp

theorem crdB_eK {m n N : ℕ} (h : n + 1 = N) (bs : Module.Basis (Fin 2) F E) (X : Mx F E m N)
    (hX : ∀ a, X a (i0 h) = 0) :
    crdB bs X ∘ eK m h = Sum.elim (crdB bs (X.submatrix id (em0 h))) 0 := by
  funext k
  rcases k with ⟨a, i, t⟩ | ⟨a, t⟩
  · rfl
  · simp [crdB, eK, hX]

theorem crdB_surj {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (x : Fin m × Fin n × Fin 2 → AF F) :
    ∃ X : Mx F E m n, crdB bs X = x := by
  refine ⟨fun a i => (Algebra.TensorProduct.basis (AF F) bs).repr.symm (Finsupp.equivFunOnFinite.symm fun t => x (a, i, t)),
    funext fun k => ?_⟩
  simp [crdB]

theorem extend_zero_column {m n N : ℕ} (h : n + 1 = N) (X : Mx F E m n) : ∀ a, ext0 h X a (i0 h) = 0 := fun a => by
  simp [ext0, i0]

theorem extension_zero_sub {m n N : ℕ} (h : n + 1 = N) (X : Mx F E m n) : (ext0 h X).submatrix id (em0 h) = X := by
  funext a i
  simp [ext0, em0]

theorem modelEx_of (hS : SDarb) (hE : SEv) (hB : BigT) (hF : SliceFacts) (hO : OpBox) (hU : SubSplit)
    (hC : ChartFacts) (hG : SiegelSmall) (hA' : SmallS) : ModelEx := by
  intro hT hA F E _ _ _ _ _ σ d n h Y b j hn hs hb hε hj
  obtain ⟨ε, e1, e2⟩ := hε
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨dd0, had0, hr0⟩ := hS F E σ d.B d.bs d.m d.n d.A d.Y d.b ε d.r d.s d.ok.good d.ok.hm d.ok.hn d.ok.sign
    d.ok.frame e1
  obtain ⟨dd', had', hr'⟩ := hS F E σ d.B d.bs d.m n d.A Y b ε d.r d.s d.ok.good d.ok.hm hn hs hb e2
  obtain ⟨hev, hkill, htheta⟩ := hE F E σ d.B d.bs d.m n d.A Y b ε d.r d.s d.ok.good d.ok.hm hn hs hb e2 dd' had'
  obtain ⟨S0, S0', C, hC0, hop, hTf⟩ := hB hT hA F E σ d dd0 had0 hr0
  obtain ⟨c1, c2, c3, c4, -⟩ := hC F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had'

  let dd1 := GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm
  let S1 := GlobalTheory.TowU.RealComp.reix (eK d.m h) ∘ₗ S0
  let S1' := S0' ∘ₗ GlobalTheory.TowU.RealComp.reix (eK d.m h).symm
  have hop1 : GlobalTheory.TowU.IsOp d.B.ψ (fun w => dd1.e (d.dd.e.symm w)) S1 S1' :=
    GlobalTheory.TowU.RealComp.isOp_comp hop.1 (GlobalTheory.TowU.RealComp.isOp_reix d.B.ψ (eK d.m h))
  have hT1 : ∀ Φ ∈ d.sch, ∀ X, d.T Φ X = C * S1 Φ (crdB d.bs X ∘ eK d.m h) := fun Φ hΦ X => by
    rw [hTf Φ hΦ X]
    simp only [S1, LinearMap.comp_apply, GlobalTheory.TowU.RealComp.reix_apply]
    rw [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  have hw := d.ok.dbl.weil
  obtain ⟨om1, hom1⟩ := projHom (G := d.G) (fun x => S1 ∘ₗ d.om x ∘ₗ S1')
    (fun x φ hφ => hop1.pres _ (hw.2.1.pres x _ (hop1.pres' φ hφ)))
    (fun φ hφ => by simp [hop1.right φ hφ])
    (fun x y φ hφ => by
      simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply]
      rw [hop1.left _ (hw.2.1.pres y _ (hop1.pres' φ hφ))])
  have hsp1 : IsUSplitting (adeleClass F) d.B.ψ dd1 (actB (cA σ)) om1 :=
    GlobalTheory.TowU.isUSplitting_of_isOp hψ (fun w => by simp) hop1 hom1 hw.2.1
  have hsr1 : SiegelRule (cA σ) (adeleClass F) d.B.ψ (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) dd1 d.χ
      (diagCols (Fin d.n)) om1 :=
    GlobalTheory.TowU.siegelRule_of_isOp (fun w => by simp) hop1 hom1 hw.2.2

  obtain ⟨hsl1, hsl2, ⟨φ₀, hφ₀, hφ₀0, hφ₀n⟩, -⟩ := hF F (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2)
  have hbox := fun g => hO F d.B.ψ hψ _ _ _ _ dd1 d.G (actB (cA σ)) om1 hsp1.toIsSplitting c2 (j g) (c3 g) φ₀ hφ₀ hφ₀0

  let cg : G2 σ Y → ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) →ₗ[ℂ] ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) :=
    fun g => slice0 _ _ ∘ₗ om1 (j g) ∘ₗ PositivityTheory.ThKF0.Chr.boxL _ φ₀
  have hbx : ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2), boxFun φ' φ₀ ∈ schA F (K1 d.m n) := fun φ' hφ' =>
    GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ' hφ' φ₀ hφ₀
  have hsl0 : ∀ φ' : (Fin d.m × Fin n × Fin 2 → AF F) → ℂ, slice0 _ _ (boxFun φ' φ₀) = φ' := fun φ' => by
    funext x
    simp [slice0, boxFun, hφ₀0]
  have hcg : ∀ g φ', cg g φ' = slice0 _ _ (om1 (j g) (boxFun φ' φ₀)) := fun g φ' => rfl
  have hboxc : ∀ g, ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2),
      om1 (j g) (boxFun φ' φ₀) = boxFun (cg g φ') φ₀ := fun g φ' hφ' =>
    (hbox g).2 φ' hφ' φ₀ hφ₀
  obtain ⟨om', hom'⟩ := projHom cg
    (fun g φ' hφ' => hsl1 _ (hsp1.pres _ _ (hbx φ' hφ')))
    (fun φ' hφ' => by rw [hcg, map_one, map_one, Module.End.one_apply, hsl0])
    (fun g g' φ' hφ' => by
      rw [hcg, map_mul, map_mul, Module.End.mul_apply, hboxc g' φ' hφ', hcg g])
  have hboxom : ∀ g, ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2), om1 (j g) (boxFun φ' φ₀) = boxFun (om' g φ') φ₀ :=
    fun g φ' hφ' => by rw [hom' g φ' hφ', hboxc g φ' hφ']
  have hsp' : IsUSplitting (adeleClass F) d.B.ψ dd' (actB (cA σ)) om' :=
    hU F d.B.ψ hψ _ _ _ _ _ _ dd1 dd' (emb h b d.b) c1 d.G (G2 σ Y) (actB (cA σ)) (actB (cA σ)) j hj.1 c4 om1 om' hsp1
      φ₀ hφ₀ hφ₀0 hφ₀n (fun g => ⟨φ₀, hφ₀, hφ₀0, fun _ _ => rfl, hboxom g⟩)
  have hsg' := hG F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' om1 hsp1.toIsSplitting hsr1 φ₀ hφ₀ hφ₀0 om'
    hboxom
  obtain ⟨S', hS'1, hS'2⟩ := hA' hT F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' S1 S1' C hC0 hop1 hT1
  refine ⟨Fin d.m × Fin n × Fin 2, inferInstance, dd', om', S', ev0 _,
    ⟨hr', ⟨isLagr_diagCols _ _, hsp', hsg'⟩, hS'1, hev, hkill, hS'2, htheta⟩, ?_⟩

  intro Φ hΦ Φ' hΦ' hres g X hX
  have hS1Φ : S1 Φ ∈ schA F (K1 d.m n) := hop1.pres Φ hΦ
  have hsl : Φ' = C • slice0 _ _ (S1 Φ) := by
    funext x
    obtain ⟨X', rfl⟩ := crdB_surj d.bs x
    have e := hres (ext0 h X') (extend_zero_column h X')
    rw [extension_zero_sub, tof_adapted d.bs d.B.ψ had', hT1 Φ hΦ, crdB_eK h d.bs _ (extend_zero_column h X'), extension_zero_sub] at e
    rw [e]
    rfl
  rw [tof_adapted d.bs d.B.ψ had', hom' g Φ' hΦ', hT1 _ (hw.2.1.pres (j g) Φ hΦ), crdB_eK h d.bs X hX]
  have e1' : S1 (d.om (j g) Φ) = om1 (j g) (S1 Φ) := by
    rw [hom1 (j g) _ hS1Φ]
    simp only [LinearMap.comp_apply]
    rw [hop1.left Φ hΦ]
  rw [e1', show (Sum.elim (crdB d.bs (X.submatrix id (em0 h))) 0 : K1 d.m n → AF F) =
    Sum.elim (crdB d.bs (X.submatrix id (em0 h))) 0 from rfl]
  have e2' := congrFun ((hbox g).1 (S1 Φ) hS1Φ) (crdB d.bs (X.submatrix id (em0 h)))
  simp only [slice0, LinearMap.coe_mk, AddHom.coe_mk] at e2'
  rw [e2', hcg, hsl]
  simp only [slice0, LinearMap.coe_mk, AddHom.coe_mk]
  rw [GlobalTheory.SchwartzBox.boxFun_smul_left, map_smul]
  rfl

end PositivityTheory.SiegelWeilFormula.Ald

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelC
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelB
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelA
noncomputable section

open Matrix

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem block_index_inl_embedded {N n : ℕ} (h : n + 1 = N) (a : Fin n) : eB h (Sum.inl (em0 h a)) = Sum.inl (Sum.inl a) :=
  PositivityTheory.SiegelWeilFormula.Ald.eB_map h (Sum.inl a)

theorem block_index_inr_embedded {N n : ℕ} (h : n + 1 = N) (a : Fin n) : eB h (Sum.inr (em0 h a)) = Sum.inl (Sum.inr a) :=
  PositivityTheory.SiegelWeilFormula.Ald.eB_map h (Sum.inr a)

theorem blk_fromRows {R : Type*} [CommRing R] {N n : ℕ} (h : n + 1 = N) (P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (A : Matrix (Fin n) (Fin n) R)
    (hP : P * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin n) R) =
      Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin n) R) * A) :
    blk h P 1 * Matrix.fromRows (1 : Matrix (Fin N) (Fin N) R) (0 : Matrix (Fin N) (Fin N) R) =
      Matrix.fromRows (1 : Matrix (Fin N) (Fin N) R) (0 : Matrix (Fin N) (Fin N) R) *
        (Matrix.fromBlocks A 0 0 1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R).submatrix (eI h) (eI h) := by
  have hA : ∀ i j, P (Sum.inl i) (Sum.inl j) = A i j := by
    intro i j
    have := congrFun (congrFun hP (Sum.inl i)) j
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] using this
  have hB : ∀ i j, P (Sum.inr i) (Sum.inl j) = 0 := by
    intro i j
    have := congrFun (congrFun hP (Sum.inr i)) j
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] using this
  have key : ∀ c : Fin N, c = PositivityTheory.SiegelWeilFormula.Ald.i0 h ∨ ∃ j, c = PositivityTheory.SiegelWeilFormula.Ald.em0 h j := by
    intro c
    by_cases hc : c = PositivityTheory.SiegelWeilFormula.Ald.i0 h
    · exact Or.inl hc
    · obtain ⟨j, rfl⟩ := (PositivityTheory.SiegelWeilFormula.Ald.ne_last_iff_mem_range h c).1 hc
      exact Or.inr ⟨j, rfl⟩
  ext u c
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type]
  rcases u with a | a <;> rcases key a with rfl | ⟨i, rfl⟩ <;> rcases key c with rfl | ⟨j, rfl⟩ <;>
    simp [Matrix.one_apply, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, PositivityTheory.SiegelWeilFormula.Ald.block_index_inl_embedded,
      PositivityTheory.SiegelWeilFormula.Ald.block_index_inr_embedded, PositivityTheory.SiegelWeilFormula.Ald.block_index_inl_last, PositivityTheory.SiegelWeilFormula.Ald.block_index_inr_last,
      PositivityTheory.SiegelWeilFormula.Ald.index_embedded_equiv, PositivityTheory.SiegelWeilFormula.Ald.index_last_equiv, hA, hB]

theorem det_blkA {R : Type*} [CommRing R] {N n : ℕ} (h : n + 1 = N) (A : Matrix (Fin n) (Fin n) R) :
    ((Matrix.fromBlocks A 0 0 1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R).submatrix (eI h) (eI h)).det = A.det := by
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

set_option linter.unusedSectionVars false

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_mul {ι κ ν : Type} [Fintype κ] (M : Matrix ι κ E) (N : Matrix κ ν E) :
    incM F (M * N) = incM F M * incM F N := by
  simp only [incM]
  exact Matrix.map_mul (f := (inclR (F := F) (E := E) (AF F)))

theorem incM_diagCols (n : ℕ) :
    incM F (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) := by
  ext u k
  rcases u with u | u <;> simp [incM, diagCols, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all

theorem mul_fromRows_one_zero {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    M * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin n) R) = M.toCols₁ := by
  ext u k
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]

theorem frame_fromRows {n : ℕ} {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) :
    ∃ tb : GL (Fin n) E, incM F b.1 * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * incM F tb.1 := by
  obtain ⟨-, tb, htb0⟩ := hb
  have htb : b.1.toCols₁ = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) * tb.1 := htb0
  refine ⟨tb, ?_⟩
  have e : (incM F b.1).toCols₁ = incM F b.1.toCols₁ := rfl
  rw [mul_fromRows_one_zero, e, htb, incM_mul]
  congr 1
  ext u k
  rcases u with u | u <;> simp [incM, diagCols, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all

theorem frame_decomp {m n : ℕ} (b : GL (Fin n ⊕ Fin n) E) (w : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) :
    w = (frQ b w).toCols₁ * (incM F b.1.toCols₁)ᵀ + (frQ b w).toCols₂ * (incM F b.1.toCols₂)ᵀ := by
  have e1 : frQ b w * (incM F b.1)ᵀ = w := by
    change (w * (incM F (b⁻¹).1)ᵀ) * (incM F b.1)ᵀ = w
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, incM_mul_inv, Matrix.transpose_one, Matrix.mul_one]
  have e2 : incM F b.1 = Matrix.fromCols (incM F b.1.toCols₁) (incM F b.1.toCols₂) := by
    ext u v
    rcases v with v | v <;> rfl
  conv_lhs => rw [← e1, e2, Matrix.transpose_fromCols, ← Matrix.fromCols_toCols (frQ b w), Matrix.fromCols_mul_fromRows]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

set_option linter.unusedSimpArgs false

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cancel_l {ι κ : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) (X : Matrix ι κ (AE F E)) :
    incM F (b⁻¹).1 * (incM F b.1 * X) = X := by
  rw [← Matrix.mul_assoc, incM_inv_mul, Matrix.one_mul]

theorem cancel_l' {ι κ : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) (X : Matrix ι κ (AE F E)) :
    incM F b.1 * (incM F (b⁻¹).1 * X) = X := by
  rw [← Matrix.mul_assoc, incM_mul_inv, Matrix.one_mul]

theorem cancel_r' {ι κ : Type} [Fintype ι] [DecidableEq ι] (b : GL ι E) (X : Matrix κ ι (AE F E)) :
    X * incM F b.1 * incM F (b⁻¹).1 = X := by
  rw [Matrix.mul_assoc, incM_mul_inv, Matrix.mul_one]

theorem mat_of_inFrame {n : ℕ} {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (g : G2 σ Y) :
    g.1.1 = incM F b.1 * inFrame b g * incM F (b⁻¹).1 := by
  rw [inFrame_eq]
  simp only [Matrix.mul_assoc, cancel_l', incM_mul_inv, Matrix.mul_one]

theorem diag_of_frame {n : ℕ} (b : GL (Fin n ⊕ Fin n) E) (tb : GL (Fin n) E)
    (h : incM F b.1 * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * incM F tb.1) :
    (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) =
      incM F b.1 * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (tb⁻¹).1 := by
  rw [h, cancel_r']

theorem det_conj {ι : Type} [Fintype ι] [DecidableEq ι] (t : GL ι E) (X : Matrix ι ι (AE F E)) :
    (incM F t.1 * X * incM F (t⁻¹).1).det = X.det := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, incM_inv_mul, Matrix.det_one, one_mul]

theorem det_conj' {ι : Type} [Fintype ι] [DecidableEq ι] (t : GL ι E) (X : Matrix ι ι (AE F E)) :
    (incM F (t⁻¹).1 * X * incM F t.1).det = X.det := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, incM_mul_inv, Matrix.det_one, one_mul]

theorem jPar (d : SD σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b)
    {j : G2 σ Y →* d.G} (hj : IsJ d h b j) (p : G2 σ Y) (t : GL (Fin n) (AE F E))
    (hpt : p.1.1 * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * t.1) :
    ∃ t' : GL (Fin d.n) (AE F E), (j p).1.1 * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) =
      (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * t'.1 ∧
      Matrix.GeneralLinearGroup.det t' = Matrix.GeneralLinearGroup.det t := by
  obtain ⟨tb, hTb⟩ := frame_fromRows hb
  obtain ⟨td, hTd⟩ := frame_fromRows d.ok.frame
  set P := inFrame b p with hPdef
  set R0 := Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) with hR0
  set R0N := Matrix.fromRows (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) with hR0N
  set A : Matrix (Fin n) (Fin n) (AE F E) := incM F (tb⁻¹).1 * t.1 * incM F tb.1 with hA
  have hDn := diag_of_frame b tb hTb
  have hDN := diag_of_frame d.b td hTd
  have hp := mat_of_inFrame b p
  have hP : P * R0 = R0 * A := by
    have e := hpt
    rw [hp, hDn] at e
    have e2 : incM F b.1 * (P * R0) * incM F (tb⁻¹).1 = incM F b.1 * (R0 * A) * incM F (tb⁻¹).1 := by
      rw [hA]
      calc incM F b.1 * (P * R0) * incM F (tb⁻¹).1
          = incM F b.1 * P * incM F (b⁻¹).1 * (incM F b.1 * R0 * incM F (tb⁻¹).1) := by
            simp only [Matrix.mul_assoc, cancel_l, incM_mul_inv, incM_inv_mul, Matrix.mul_one]
        _ = incM F b.1 * R0 * incM F (tb⁻¹).1 * t.1 := e
        _ = incM F b.1 * (R0 * (incM F (tb⁻¹).1 * t.1 * incM F tb.1)) * incM F (tb⁻¹).1 := by
            simp only [Matrix.mul_assoc, cancel_l', incM_mul_inv, incM_inv_mul, Matrix.mul_one]
    have e3 := congrArg (fun X => incM F (b⁻¹).1 * X * incM F tb.1) e2
    simpa only [Matrix.mul_assoc, cancel_l, cancel_l', incM_mul_inv, incM_inv_mul, Matrix.mul_one] using e3
  have hblk := blk_fromRows h P A hP
  have hjp : inFrame d.b (j p) = blk h P 1 := eq_blk h _ _ (hj.2.1 p) (hj.2.2 p)
  have hjm := mat_of_inFrame d.b (j p)
  rw [hjp] at hjm
  set blkA := (Matrix.fromBlocks A 0 0 1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) (AE F E)).submatrix (eI h) (eI h)
    with hblkA
  set T : Matrix (Fin d.n) (Fin d.n) (AE F E) := incM F td.1 * blkA * incM F (td⁻¹).1 with hT
  have hdet : T.det = t.1.det := by
    rw [hT, det_conj, hblkA, det_blkA, hA, det_conj']
  have hu : IsUnit T.det := by
    rw [hdet, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.isUnit _
  refine ⟨Matrix.nonsingInvUnit T hu, ?_, ?_⟩
  · show (j p).1.1 * _ = _ * T
    rw [hjm, hDN]
    calc incM F d.b.1 * blk h P 1 * incM F (d.b⁻¹).1 * (incM F d.b.1 * R0N * incM F (td⁻¹).1)
        = incM F d.b.1 * (blk h P 1 * R0N) * incM F (td⁻¹).1 := by simp only [Matrix.mul_assoc, cancel_l, incM_mul_inv, incM_inv_mul, Matrix.mul_one]
      _ = incM F d.b.1 * (R0N * blkA) * incM F (td⁻¹).1 := by rw [hblk]
      _ = incM F d.b.1 * R0N * incM F (td⁻¹).1 * T := by
          rw [hT]; simp only [Matrix.mul_assoc, cancel_l, incM_mul_inv, incM_inv_mul, Matrix.mul_one]
  · ext
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet

end PositivityTheory.SiegelWeilFormula.Ald

end
end
