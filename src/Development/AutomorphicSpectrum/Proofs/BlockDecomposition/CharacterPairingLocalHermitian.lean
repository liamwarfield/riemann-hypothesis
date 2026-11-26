module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOfNumericsModel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterPairingLocalHermitian
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterPairingLocalHermitian
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.SplitPair

section gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evInf_trace [FiniteDimensional F E] (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    evInf F w (Algebra.trace (AF F) (AF F ⊗[F] E) z) =
      Algebra.trace w.Completion (w.Completion ⊗[F] E) (compInf F E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x =>
    have e : compInf F E w (a ⊗ₜ[F] x) = evInf F w a ⊗ₜ[F] x := rfl
    rw [e, GlobalTheory.OppLinChar.trace_tmul', GlobalTheory.OppLinChar.trace_tmul', map_mul, AlgHom.commutes]

theorem eq_single (v : HeightOneSpectrum (𝓞 F)) (y : AF F)
    (hi : ∀ w, evInf F w y = 0) (hf : ∀ v' ≠ v, evFin F v' y = 0) :
    y = pairA F 0 (singleV F v (evFin F v y)) := by
  classical
  refine Prod.ext (funext fun w => hi w) (GlobalTheory.AdelicU.af_ext fun u => ?_)
  by_cases h : u = v
  · subst h
    change _ = singleV F u _ u
    exact (RestrictedProduct.single_eq_same _ u _).symm
  · change _ = singleV F v _ u
    exact (hf u h).trans (RestrictedProduct.single_eq_of_ne _ _ h).symm

theorem cA_eq_sigR (σ : E →ₐ[F] E) (y : AF F ⊗[F] E) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ y = sigR (AF F) σ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem psi_half_trace {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F))
    (τ : E →ₐ[F] Fv F v) (ψ : AddChar (AF F) ℂ) {n : ℕ}
    (x : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (b : Matrix (Fin n) (Fin n) E)
    (hx : ∀ i j, sigR (AF F) σ (x j i) = x i j) (hb : ∀ i j, σ (b j i) = b i j)
    (hinf : ∀ w i j, compInf F E w (x i j) = 0) (hfin : ∀ v' ≠ v, ∀ i j, compFin F E v' (x i j) = 0) :
    ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (∑ i, ∑ j, x i j * inclR (AF F) (b j i))) =
      psiV F ψ v (∑ i, ∑ j, splitProj τ (compFin F E v (x i j)) * τ (b j i)) := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hcm.2.2.1
  set z : AF F ⊗[F] E := ∑ i, ∑ j, x i j * inclR (AF F) (b j i) with hz
  set a : Fv F v := ∑ i, ∑ j, splitProj τ (compFin F E v (x i j)) * τ (b j i) with ha
  have hzi : ∀ w, compInf F E w z = 0 := fun w => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hz, map_sum, map_mul, hinf, zero_mul, Finset.sum_const_zero]
  have hzf : ∀ v' ≠ v, compFin F E v' z = 0 := fun v' h => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hz, map_sum, map_mul, hfin v' h, zero_mul, Finset.sum_const_zero]
  have hpi : ∀ t : E →ₐ[F] Fv F v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t z =
      ∑ i, ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t (x i j) * t (b j i) := fun t => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hz, map_sum, map_mul, GlobalTheory.OppLinChar.piW_inclR]
  have h1 : splitProj τ (compFin F E v z) = a := hpi τ
  have h2 : splitProj (τ.comp σ) (compFin F E v z) = a := by
    refine (hpi (τ.comp σ)).trans ?_
    rw [ha, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    have e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) (x i j) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (x j i) := by
      rw [← hx i j, ← cA_eq_sigR]
      exact GlobalTheory.OppLinChar.piW_cA hcm τ (x j i)
    rw [e, AlgHom.comp_apply, hb i j]
    rfl
  set y : AF F := algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E) z with hy
  have hv : evFin F v y = a := by
    rw [hy, map_mul, AlgHom.commutes, GlobalTheory.OppLinChar.evFin_trace, GlobalTheory.OppLinChar.trace_split hcm τ, h1, h2,
      ← two_mul, ← mul_assoc, ← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul]
    norm_num
  have hs := eq_single v y
    (fun w => by rw [hy, map_mul, evInf_trace, hzi, map_zero, mul_zero])
    (fun v' h => by rw [hy, map_mul, GlobalTheory.OppLinChar.evFin_trace, hzf v' h, map_zero, mul_zero])
  rw [hv] at hs
  rw [hs]
  rfl

end gen

theorem pch_rat_split : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (ψ : AddChar (AF D.host.F) ℂ) (x : hermA D n),
    (∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) → (∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) →
    ∀ β : HermE D n, pch ψ x.1 (rat β.1) =
      psiV D.host.F ψ v (Matrix.trace (tauC τ x.1 * β.1.map τ)) := by
  intro D n v τ ψ x hinf hfin β
  have hx : ∀ i j, sigR (AF D.host.F) D.sp.cm.sig (x.1 j i) = x.1 i j := fun i j =>
    congrFun (congrFun x.2 i) j
  have hb : ∀ i j, D.sp.cm.sig (β.1 j i) = β.1 i j := fun i j => congrFun (congrFun β.2 i) j
  exact psi_half_trace (isCMExt_host D) v τ ψ x.1 β.1 hx hb hinf hfin

end GlobalTheory.CompanionTheory.Jp.SplitPair
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterPairingLocalHermitianStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_pairing_local_hermitian : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (ψ : AddChar (AF D.host.F) ℂ) (x : hermA D n), (∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) → (∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) → ∀ β : HermE D n, pch ψ x.1 (rat β.1) = psiV D.host.F ψ v (Matrix.trace (tauC τ x.1 * β.1.map τ)) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.SplitPair.pch_rat_split | exact GlobalTheory.CompanionTheory.Jp.SplitPair.pch_rat_split | (intros; apply GlobalTheory.CompanionTheory.Jp.SplitPair.pch_rat_split <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureGLRightScaling
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondColumnsMulBlockDiagonal
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Cov

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem jn_bl {a r : ℕ} (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) (g : Mx D t t) :
    mm (jn hn w v) (bl hn 1 0 0 g) = jn hn w (mm v g) := by
  simp only [jn, bl, mm]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
  simp

theorem jn_c (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) : jn hn (c1 hn U) (c2 hn U) = U := by
  ext i j
  obtain ⟨k, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases k with k | k <;> simp [jn, c1, c2]

theorem first_columns_join_eq (hn : W.rank + t = n) {a : ℕ} (w : Mx D a W.rank) (v : Mx D a t) : c1 hn (jn hn w v) = w := by
  ext i j
  simp [jn, c1]

theorem second_columns_join_eq (hn : W.rank + t = n) {a : ℕ} (w : Mx D a W.rank) (v : Mx D a t) : c2 hn (jn hn w v) = v := by
  ext i j
  simp [jn, c2]

theorem first_columns_mul_block_diagonal (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) (g : Mx D t t) :
    c1 hn (mm U (bl hn 1 0 0 g)) = c1 hn U := by
  conv_lhs => rw [← jn_c hn U, jn_bl, first_columns_join_eq]

theorem second_columns_mul_block_diagonal (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) (g : Mx D t t) :
    c2 hn (mm U (bl hn 1 0 0 g)) = mm (c2 hn U) g := by
  conv_lhs => rw [← jn_c hn U, jn_bl, second_columns_join_eq]

theorem map_char {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [T2Space A]
    [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) (c : ℝ≥0) (hc0 : c ≠ 0)
    (hc : addEquivAddHaarChar φ = c) : μ.map φ = c⁻¹ • μ := by
  haveI : TopologicalSpace.PseudoMetrizableSpace A := inferInstance
  haveI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have h4 := addEquivAddHaarChar_smul_map μ φ
  rw [hc] at h4
  conv_rhs => rw [← h4]
  rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]


set_option maxHeartbeats 1200000 in
theorem map_right (a b : ℕ) (μ : Measure (Mx D a b)) (hμ : μ.IsAddHaarMeasure) (g : GL (Fin b) (AE D)) :
    μ.map (fun y => mm y g.1) =
      ((absA D (Matrix.GeneralLinearGroup.det g))⁻¹ ^ a : ℝ≥0) • μ := by
  haveI := hμ
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D a b
  haveI : IsTopologicalAddGroup (Mx D a b) := i1
  haveI : LocallyCompactSpace (Mx D a b) := i2
  haveI : SecondCountableTopology (Mx D a b) := i3
  haveI : T2Space (Mx D a b) := i4
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hc : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE (1 : GL (Fin a) (AE D)) g) = absA D (Matrix.GeneralLinearGroup.det g) ^ a := by
    have := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) a b
      (1 : GL (Fin a) (AE D)) g
    simpa using this
  have hA : absA D (Matrix.GeneralLinearGroup.det g) ≠ 0 := (GlobalTheory.CompanionTheory.IwaAd.absA_pos _).ne'
  have e : (fun y : Mx D a b => mm y g.1) = GlobalTheory.ModuLR.lrCE (1 : GL (Fin a) (AE D)) g := by
    funext y
    rw [GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.one_mul]
  rw [e, inv_pow]
  exact map_char μ _ _ (pow_ne_zero _ hA) hc

end GlobalTheory.CompanionTheory.ColumnSplitting.Cov

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureGLRightScaling
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Cov

theorem map_two {γ δ : Type} [MeasurableSpace γ] [MeasurableSpace δ] (c : Measure γ) (e : Measure δ)
    [SFinite c] [SFinite e] (f : γ → γ) (h : δ → δ) (hf : Measurable f) (hh : Measurable h) (r s : ℝ≥0)
    (h1 : c.map f = r • c) (h2 : e.map h = s • e) :
    (c.prod e).map (Prod.map f h) = (r * s) • c.prod e := by
  rw [← Measure.map_prod_map c e hf hh, h1, h2]
  simp only [ENNReal.smul_def, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, ENNReal.coe_mul, smul_eq_mul]
  rw [mul_comm]

theorem map_id_prod {β γ : Type} [MeasurableSpace β] [MeasurableSpace γ] (b : Measure β) (X : Measure γ)
    [SFinite b] [SFinite X] (F : γ → γ) (hF : Measurable F) (k : ℝ≥0) (h : X.map F = k • X) :
    (b.prod X).map (Prod.map id F) = k • b.prod X := by
  rw [← Measure.map_prod_map b X measurable_id hF, h, Measure.map_id]
  simp only [ENNReal.smul_def, Measure.prod_smul_right]

theorem map_four {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (a : Measure α) (b : Measure β) (c : Measure γ) (e : Measure δ) [SFinite a] [SFinite b] [SFinite c] [SFinite e]
    (f : γ → γ) (h : δ → δ) (hf : Measurable f) (hh : Measurable h) (r s : ℝ≥0)
    (h1 : c.map f = r • c) (h2 : e.map h = s • e) :
    (a.prod (b.prod (c.prod e))).map (Prod.map id (Prod.map id (Prod.map f h))) =
      (r * s) • a.prod (b.prod (c.prod e)) := by
  have hm : Measurable (Prod.map f h) := hf.prodMap hh
  exact map_id_prod a _ _ (measurable_id.prodMap hm) _
    (map_id_prod b _ _ hm _ (map_two c e f h hf hh r s h1 h2))

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem zp_tau (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (g : Mx D t t) (h : GA D W) (U : Mx D t n) (y : Mx D W.rank t) :
    zp d hn x₀ (h, mm U (bl hn 1 0 0 g), mm y g) =
      ((zp d hn x₀ (h, U, y)).1, mm (zp d hn x₀ (h, U, y)).2 g) := by
  simp only [zp, first_columns_mul_block_diagonal, second_columns_mul_block_diagonal, mm, Matrix.add_mul, Matrix.mul_assoc]

theorem ac_tau (a b : ℕ) (k : GA D B) (z : Mx D B.rank a × Mx D B.rank b) (g : Mx D b b) :
    ac B k (z.1, mm z.2 g) = ((ac B k z).1, mm (ac B k z).2 g) := by
  simp only [ac, mm, Matrix.mul_assoc]

theorem measurable_right (a b : ℕ) (g : Mx D b b) : Measurable (fun y : Mx D a b => mm y g) := by
  obtain ⟨-, -, -, -, h5⟩ := top_mx (D := D) a b
  have hring := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact (continuous_id.matrix_mul continuous_const).measurable

theorem nuT_cov : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (g : GL (Fin t) (AE D)), (nuT hn I μ x₀).map (fun z => (z.1, mm z.2 g.1)) = ((absA D (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (W.rank + t) : ℝ≥0) • nuT hn I μ x₀ := by
  intro D n t B W d hn I μ hμ x₀ g
  obtain ⟨G, hG⟩ := GlobalTheory.CompanionTheory.WzLevi.exists_lv hn g
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, k2, k3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hBW : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have s1 := hf.1
  have s2 := I.haar
  have s3 := I.probK
  have s4 := hμ
  have hdet := GlobalTheory.CompanionTheory.WzLevi.det_lv hn g G hG
  have hsc1 := map_right t n I.μ₁ hf.1 G
  rw [hdet] at hsc1
  have hsc2 := map_right W.rank t μ hμ g
  have hm1 := measurable_right (D := D) t n G.1
  have hm2 := measurable_right (D := D) W.rank t g.1
  have hτ := map_four I.νK I.m I.μ₁ μ _ _ hm1 hm2 _ _ hsc1 hsc2
  have hτm : Measurable (Prod.map (id : I.l.K → I.l.K) (Prod.map (id : GA D W → GA D W)
      (Prod.map (fun y : Mx D t n => mm y G.1) (fun y : Mx D W.rank t => mm y g.1)))) :=
    measurable_id.prodMap (measurable_id.prodMap (hm1.prodMap hm2))
  have hπ := measurable_pi hn I x₀
  have hT : Measurable (fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, mm z.2 g.1)) :=
    measurable_fst.prodMk ((measurable_right (D := D) B.rank t g.1).comp measurable_snd)
  have hcomp : (fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, mm z.2 g.1)) ∘
      (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) =
      (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) ∘
        (Prod.map (id : I.l.K → I.l.K) (Prod.map (id : GA D W → GA D W)
          (Prod.map (fun y : Mx D t n => mm y G.1) (fun y : Mx D W.rank t => mm y g.1)))) := by
    funext ⟨k, h, U, y⟩
    simp only [Function.comp, Prod.map, id]
    rw [hG, zp_tau, ac_tau]
  unfold nuT
  rw [Measure.map_map hT hπ, hcomp, ← Measure.map_map hπ hτm]
  unfold Q0
  rw [hτ, Measure.map_smul, ← pow_add, add_comm t]
  exact hπ.aemeasurable

end GlobalTheory.CompanionTheory.ColumnSplitting.Cov

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureGLRightScalingStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_measure_GL_right_scaling : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (g : GL (Fin t) (AE D)), (nuT hn I μ x₀).map (fun z => (z.1, mm z.2 g.1)) = ((absA D (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (W.rank + t) : ℝ≥0) • nuT hn I μ x₀ := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.Cov.nuT_cov | exact GlobalTheory.CompanionTheory.ColumnSplitting.Cov.nuT_cov | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.Cov.nuT_cov <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermScaleMain
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSmulH
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

namespace GlobalTheory.CompanionTheory.HermSc

section Abstract

variable {M : Type} [AddCommGroup M] [TopologicalSpace M]

theorem sub_mem_ker (S : AddSubgroup M) (P : M →+ M) (hPm : ∀ x, P x ∈ S) (hPs : ∀ s ∈ S, P s = s) (x : M) :
    x - P x ∈ P.ker := by
  rw [AddMonoidHom.mem_ker, map_sub, hPs _ (hPm x), sub_self]

def imKer [IsTopologicalAddGroup M] (S : AddSubgroup M) (P : M →+ M) (hPc : Continuous P) (hPm : ∀ x, P x ∈ S)
    (hPs : ∀ s ∈ S, P s = s) : (S × P.ker) ≃ₜ+ M where
  toFun p := p.1.1 + p.2.1
  invFun x := (⟨P x, hPm x⟩, ⟨x - P x, sub_mem_ker S P hPm hPs x⟩)
  left_inv p := by
    have h2 : P p.2.1 = 0 := p.2.2
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change P (p.1.1 + p.2.1) = p.1.1
      rw [map_add (f := _), hPs _ p.1.2, h2, add_zero]
    · change (p.1.1 + p.2.1) - P (p.1.1 + p.2.1) = p.2.1
      rw [map_add (f := _), hPs _ p.1.2, h2, add_zero, add_sub_cancel_left]
  right_inv x := by
    change P x + (x - P x) = x
    abel
  map_add' p q := by
    change (p.1.1 + q.1.1) + (p.2.1 + q.2.1) = (p.1.1 + p.2.1) + (q.1.1 + q.2.1)
    abel
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (hPc.subtype_mk _).prodMk ((continuous_id.sub hPc).subtype_mk _)

theorem char_restr [IsTopologicalAddGroup M] [LocallyCompactSpace M] [SecondCountableTopology M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M] (S : AddSubgroup M) [LocallyCompactSpace S] (P : M →+ M)
    (hPc : Continuous P) (hPm : ∀ x, P x ∈ S) (hPs : ∀ s ∈ S, P s = s)
    (U : M ≃ₜ+ M) (hU : ∀ s ∈ S, U s ∈ S) (hU' : ∀ s ∈ S, U.symm s ∈ S) (hfix : ∀ x, P x = 0 → U x = x) :
    addEquivAddHaarChar (GlobalTheory.CompanionTheory.CgMod.restr S U hU hU') = addEquivAddHaarChar U := by
  haveI : SecondCountableTopology S := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space S := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : SecondCountableTopology P.ker := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space P.ker := Topology.IsEmbedding.subtypeVal.t2Space
  have hcl : IsClosed (P.ker : Set M) := by
    have : (P.ker : Set M) = P ⁻¹' {0} := by
      ext x; simp [AddMonoidHom.mem_ker]
    rw [this]
    exact isClosed_singleton.preimage hPc
  haveI : LocallyCompactSpace P.ker := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set Ψ := imKer S P hPc hPm hPs with hΨ
  set T := GlobalTheory.CompanionTheory.CgMod.restr S U hU hU' with hT
  have e : ((Ψ.symm.trans (GlobalTheory.ModuLR.prodCE T (ContinuousAddEquiv.refl P.ker))).trans Ψ) = U := by
    ext x
    obtain ⟨p, rfl⟩ := Ψ.surjective x
    change Ψ (GlobalTheory.ModuLR.prodCE T (ContinuousAddEquiv.refl P.ker) (Ψ.symm (Ψ p))) = U (Ψ p)
    have hl : Ψ.symm (Ψ p) = p := Ψ.left_inv p
    rw [hl]
    change U p.1.1 + p.2.1 = U (p.1.1 + p.2.1)
    rw [map_add (f := _), hfix _ p.2.2]
  rw [← e, GlobalTheory.ModuLR.addEquivAddHaarChar_transport Ψ, GlobalTheory.T.addEquivAddHaarChar_prodCongr, addEquivAddHaarChar_refl, mul_one]

end Abstract

section Main

open GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.HermVol GlobalTheory.CompanionTheory.CgMod PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

variable {D : D7} {n : ℕ}


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem char_herm [BorelSpace (Mx D n n)] [LocallyCompactSpace (hermA D n)] (a : GL (Fin n) (AE D)) :
    addEquivAddHaarChar (restr (hermA D n) (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹) (lr_herm a) (lr_herm_symm a)) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : LocallyCompactSpace (Mx D n n) := i2
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : T2Space (Mx D n n) := i4
  haveI : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  obtain ⟨d, e, hde, hd, he⟩ := exists_anti_units D
  have hsq := char_sq (hermA D n) (hermPartHom D n) continuous_hermPart hermPart_mem
    (fun s hs => hermPart_of_mem hs) (mulCE d e hde)
    (fun s hs => hermPart_anti hd hs) (fun s hs => hermPart_anti he hs)
    (fun x => hermPart_split he hde x) (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹)
    (lr_smul a d e hde) (lr_herm a) (lr_herm_symm a)
  have hlr : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n := by
    have h := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE _ _ D.sp.cm.sig (isCMExt_host D) n n a (ad a)⁻¹
    rw [h]
    exact congrArg (fun t => absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * t ^ n) (absA_det_ad_inv a)
  exact (pow_left_inj₀ zero_le zero_le two_ne_zero).1 ((hsq.trans hlr).trans (sq _).symm)

theorem smul_herm {e : AE D} (hc : cA D e = e) (x : hermA D n) : e • x.1 ∈ hermA D n := by
  change adj (e • x.1) = e • x.1
  have h : adj x.1 = x.1 := x.2
  rw [adj_smul, h, hc]

def smulH (e : AE D) (hc : cA D e = e) : hermA D n →+ hermA D n where
  toFun x := ⟨e • x.1, smul_herm hc x⟩
  map_zero' := Subtype.ext (smul_zero e)
  map_add' x y := Subtype.ext (smul_add e x.1 y.1)

set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_smulH (e : AE D) (hc : cA D e = e) : Continuous (smulH (n := n) e hc) :=
  ((continuous_const_smul e).comp continuous_subtype_val).subtype_mk _

theorem smul_sandwich (e : AE D) (A B x : Mx D n n) (h : e • x = x) : e • (A * x * B) = A * x * B := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, h]

theorem mul_fix {e : AE D} (g : GL (Fin n) (AE D)) (hg : e • (g.1 - 1) = g.1 - 1) (x : Mx D n n) (hx : e • x = 0) :
    g.1 * x = x := by
  have h : (g.1 - 1) * x = 0 := by
    rw [← hg, Matrix.smul_mul, ← Matrix.mul_smul, hx, Matrix.mul_zero]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
  exact h

theorem sandwich_fix {e : AE D} (g : GL (Fin n) (AE D)) (hg : e • (g.1 - 1) = g.1 - 1) (x : hermA D n)
    (hx : e • x.1 = 0) : g.1 * x.1 * adj g.1 = x.1 := by
  have h1 := mul_fix g hg x.1 hx
  have h2 : adj x.1 = x.1 := x.2
  have h3 : x.1 * adj g.1 = x.1 := by
    have := congrArg adj h1
    rwa [adj_mul, h2] at this
  rw [h1, h3]

end Main

end GlobalTheory.CompanionTheory.HermSc
end
end

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

namespace GlobalTheory.CompanionTheory.HermSc

section Main

open GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.HermVol GlobalTheory.CompanionTheory.CgMod PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem hermScale_main : PositivityTheory.Rg.Rsw.L.IdemEx → PositivityTheory.Rg.Rsw.Em.TopX → PositivityTheory.Rg.Rsw.Em.HermScale := by
  intro hid htop D t S e he lam hlam g hg
  obtain ⟨hee, hce⟩ := (hid D S).2 e he
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D t t
  haveI : IsTopologicalAddGroup (Mx D t t) := i1
  haveI : LocallyCompactSpace (Mx D t t) := i2
  haveI : SecondCountableTopology (Mx D t t) := i3
  haveI : T2Space (Mx D t t) := i4
  haveI : BorelSpace (Mx D t t) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D t) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D t) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : LocallyCompactSpace (hermA D t) :=
    (isClosed_hermA (D := D) (r := t)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨-, -, -, -, -, -, hb, hs2, hlc⟩ := htop D 0 0 t e
  haveI : BorelSpace (hermS D t e) := hb
  haveI : SecondCountableTopology (hermS D t e) := hs2
  haveI : LocallyCompactSpace (hermS D t e) := hlc
  haveI : T2Space (hermS D t e) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : lam.IsAddHaarMeasure := hlam
  set U := restr (hermA D t) (GlobalTheory.ModuLR.lrCE g (ad g)⁻¹) (lr_herm g) (lr_herm_symm g) with hUdef
  have hU : ∀ s ∈ hermS D t e, U s ∈ hermS D t e := fun s hs =>
    smul_sandwich e _ _ s.1 hs
  have hU' : ∀ s ∈ hermS D t e, U.symm s ∈ hermS D t e := fun s hs =>
    smul_sandwich e _ _ s.1 hs
  have hPm : ∀ x, smulH (n := t) e hce x ∈ hermS D t e := fun x => by
    change e • e • x.1 = e • x.1
    rw [smul_smul, hee]
  have hPs : ∀ s ∈ hermS D t e, smulH (n := t) e hce s = s := fun s hs => Subtype.ext hs
  have hfix : ∀ x, smulH (n := t) e hce x = 0 → U x = x := fun x hx =>
    Subtype.ext (sandwich_fix g hg x (congrArg Subtype.val hx))
  have hchar := char_restr (hermS D t e) (smulH e hce) (continuous_smulH e hce) hPm hPs U hU hU' hfix
  rw [char_herm g] at hchar
  set c := restr (hermS D t e) U hU hU' with hc
  refine ⟨c, fun x => rfl, ?_⟩
  have key := addEquivAddHaarChar_smul_map lam c
  have hne : addEquivAddHaarChar c ≠ 0 := (addEquivAddHaarChar_pos c).ne'
  have hmap : lam.map c = (addEquivAddHaarChar c)⁻¹ • lam := by
    calc lam.map c = ((addEquivAddHaarChar c)⁻¹ * addEquivAddHaarChar c) • lam.map c := by
          rw [inv_mul_cancel₀ hne, one_smul]
      _ = (addEquivAddHaarChar c)⁻¹ • lam := by rw [mul_smul, key]
  rw [hmap, hchar, inv_pow]

end Main

end GlobalTheory.CompanionTheory.HermSc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableThetaKernelProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableThetaKernelProduct
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

namespace Integ

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem det_bl {r t n : ℕ} (hn : r + t = n) (y : Mx D r t) :
    Matrix.det (bl hn 1 y 0 1 : Mx D n n) = 1 := by
  unfold bl
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

def blU {r t n : ℕ} (hn : r + t = n) (y : Mx D r t) : GL (Fin n) (AE D) :=
  ⟨bl hn 1 y 0 1, bl hn 1 (-y) 0 1, GlobalTheory.CompanionTheory.JacobiMaps.sh_mul hn _ _ rfl,
    GlobalTheory.CompanionTheory.JacobiMaps.sh_mul hn _ _ (neg_neg y).symm⟩

theorem det_blU {r t n : ℕ} (hn : r + t = n) (y : Mx D r t) (a : GL (Fin n) (AE D)) (ha : a.1 = bl hn 1 y 0 1) :
    Matrix.GeneralLinearGroup.det a = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, ha]
  exact det_bl hn y

theorem lintegral_comp_char_one {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) (hc : addEquivAddHaarChar φ = 1) (g : A → ℝ≥0∞) :
    ∫⁻ y, g (φ y) ∂μ = ∫⁻ y, g y ∂μ := by
  have key := addEquivAddHaarChar_smul_map μ φ
  rw [hc, one_smul] at key
  have hp : MeasurePreserving φ μ μ := ⟨φ.continuous.measurable, key⟩
  exact hp.lintegral_comp_emb φ.toHomeomorph.measurableEmbedding g

theorem lintegral_bl {a r t n : ℕ} (hn : r + t = n) (y : Mx D r t) (ν : Measure (Mx D a n))
    (hν : ν.IsAddHaarMeasure) (g : Mx D a n → ℝ≥0∞) :
    ∫⁻ U, g (mm U (bl hn 1 y 0 1)) ∂ν = ∫⁻ U, g U ∂ν := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := top_mx (D := D) a n
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let φ := GlobalTheory.ModuLR.lrCE (1 : GL (Fin a) (AE D)) (blU hn y)
  have hc : addEquivAddHaarChar φ = 1 := by
    have h := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) a n
      (1 : GL (Fin a) (AE D)) (blU hn y)
    rw [det_blU hn y (blU hn y) rfl] at h
    simpa only [map_one, one_pow, mul_one] using h
  have e : ∀ U : Mx D a n, mm U (bl hn 1 y 0 1) = φ U := fun U => by
    simp only [φ]
    rw [GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.one_mul]
    rfl
  simp only [e]
  exact lintegral_comp_char_one ν φ hc g

theorem jn_first {a r t n : ℕ} (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) :
    (jn hn w v).submatrix id (fun j => finCongr hn (Fin.castAdd t j)) = w := by
  ext i j
  simp [jn, Matrix.submatrix_apply, Matrix.fromCols]

theorem xu_bl (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (h : GA D W) (U : Mx D t n) (y : Mx D W.rank t) :
    mm (XU d hn x₀ h U) (bl hn 1 y 0 1) =
      mm d.jX (mm U (bl hn 1 y 0 1)) + mm d.j0 (mm (jn hn (ww W x₀ h) 0) (bl hn 1 y 0 1)) := by
  unfold XU
  simp only [mm]
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]

theorem inner_eq (hIkL : IkLint) (hJn : JnBl) {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) {θ : InfFam D}
    (hθ : IsInfFam θ) {M : Mx D B.rank n → ℂ} (hM : M ∈ schwartzA θ B.rank n)
    (hM0 : ∀ x, 0 ≤ (M x).re ∧ (M x).im = 0) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : GA D W)
    (y : Mx D W.rank t) :
    ∫⁻ U, ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm (XU d hn x₀ h U) (bl hn 1 y 0 1)))‖ₑ ∂I.νK ∂I.μ₁ =
      ‖ikp I M (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0))‖ₑ := by
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have hb : mm (jn hn (ww W x₀ h) 0) (bl hn 1 y 0 1) = jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0) :=
    hJn D n t _ _ hn _ _ y
  rw [← hb, ← hIkL D n t B W d I θ hθ M hM hM0]
  simp only [xu_bl]
  exact lintegral_bl hn y I.μ₁ hf.1
    (fun U => ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm d.jX U + mm d.j0 (mm (jn hn (ww W x₀ h) 0) (bl hn 1 y 0 1))))‖ₑ ∂I.νK)

theorem continuous_jn {a r t n : ℕ} (hn : r + t = n) :
    Continuous fun u : Mx D a r × Mx D a t => jn hn u.1 u.2 := by
  refine continuous_matrix fun i j => ?_
  change Continuous fun u : Mx D a r × Mx D a t =>
    Matrix.fromCols u.1 u.2 i ((finSumFinEquiv.trans (finCongr hn)).symm j)
  generalize (finSumFinEquiv.trans (finCongr hn)).symm j = s
  cases s with
  | inl k => exact continuous_fst.matrix_elem i k
  | inr k => exact continuous_snd.matrix_elem i k

theorem continuous_bl {r t n : ℕ} (hn : r + t = n) : Continuous fun y : Mx D r t => (bl hn 1 y 0 1 : Mx D n n) :=
  (continuous_const.matrix_fromBlocks continuous_id continuous_const continuous_const).matrix_submatrix _ _

theorem continuous_pt {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n)
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Continuous fun p : I.l.K × Par D n t W =>
      mm (mt B ((p.1 : GA D B)⁻¹)) (mm (XU d hn x₀ p.2.1 p.2.2.1) (bl hn 1 p.2.2.2 0 1)) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨-, g2, -, -, g5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hT := (top_mx (D := D) B.rank n).1
  have hU : Continuous fun p : I.l.K × Par D n t W => p.2.2.1 := continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hh : Continuous fun p : I.l.K × Par D n t W => p.2.1 := continuous_fst.comp continuous_snd
  have hy : Continuous fun p : I.l.K × Par D n t W => p.2.2.2 := continuous_snd.comp (continuous_snd.comp continuous_snd)
  have hX : Continuous fun p : I.l.K × Par D n t W => XU d hn x₀ p.2.1 p.2.2.1 :=
    (continuous_const.matrix_mul hU).add (continuous_const.matrix_mul
      ((continuous_jn hn).comp (((continuous_ww x₀).comp hh).prodMk continuous_const)))
  exact ((continuous_mt B).comp (continuous_subtype_val.comp continuous_fst).inv).matrix_mul
    (hX.matrix_mul ((continuous_bl hn).comp hy))

end Integ


open Integ in
theorem integrable_core : IkSch → Dom → OrbFin → Shift → IkLint → Fub4 → JnBl → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), x₀.det ≠ 0 → ∀ Φ ∈ schwartzA θ B.rank n, ∀ η ∈ schwartzA θ W.rank t, Integrable (core hn I x₀ Φ η) (I.νK.prod (Q0 I μ)) := by
  intro hIk hDom hOrb _ hIkL hFub hJn D n t B W d hn I θ hθ μ hμ x₀ hx₀ Φ hΦ η hη
  obtain ⟨M, hM, hM0, hMd⟩ := hDom D θ hθ B.rank n n id Function.injective_id Φ hΦ
  have hΨ : ikp I M ∈ schwartzA θ W.rank n := (hIk D n t B W d I θ hθ M hM).2
  obtain ⟨N, hN, -, hNd⟩ := hDom D θ hθ W.rank n W.rank (fun j => finCongr hn (Fin.castAdd t j))
    (fun a b h => by simpa using h) (ikp I M) hΨ

  obtain ⟨h1, h2⟩ := top_par (D := D) n t W
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hBG : BorelSpace (GA D W) := ⟨rfl⟩
  have hB : BorelSpace (GA D B) := ⟨rfl⟩
  have hK : BorelSpace I.l.K := Subtype.borelSpace _
  have o0 : OpensMeasurableSpace (Par D n t W) := h1.opensMeasurable
  have oK : OpensMeasurableSpace I.l.K := hK.opensMeasurable
  have e1 : SecondCountableTopologyEither I.l.K (Par D n t W) := ⟨Or.inr h2⟩
  have o1 : OpensMeasurableSpace (I.l.K × Par D n t W) := Prod.opensMeasurableSpace
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have := hf.1
  have := I.haar
  have := I.probK
  have hcM : Continuous M := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ M hM).1
  have hcΦ : Continuous Φ := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ Φ hΦ).1
  have hcη : Continuous η := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ η hη).1
  have hpt := continuous_pt (d := d) hn I x₀
  have hy : Continuous fun p : I.l.K × Par D n t W => p.2.2.2 := continuous_snd.comp (continuous_snd.comp continuous_snd)
  have hcore : Continuous (core hn I x₀ Φ η) :=
    (hcΦ.comp hpt).mul (Complex.continuous_conj.comp (hcη.comp hy))
  refine ⟨hcore.measurable.aestronglyMeasurable, ?_⟩

  set F : I.l.K × GA D W × Mx D t n × Mx D W.rank t → ℝ≥0∞ := fun p =>
    ‖M (mm (mt B ((p.1 : GA D B)⁻¹)) (mm (XU d hn x₀ p.2.1 p.2.2.1) (bl hn 1 p.2.2.2 0 1)))‖ₑ * ‖η p.2.2.2‖ₑ with hF
  have hFm : Measurable F :=
    (hcM.comp hpt).measurable.enorm.mul (hcη.comp hy).measurable.enorm
  have hle : ∀ p, ‖core hn I x₀ Φ η p‖ₑ ≤ F p := fun p => by
    simp only [core, hF, enorm_mul, RCLike.enorm_conj]
    gcongr
    rw [enorm_le_iff_norm_le]
    refine (hMd _).trans ?_
    simpa using Complex.re_le_norm _
  have hη' : ∫⁻ y, ‖η y‖ₑ ∂μ < ⊤ :=
    hasFiniteIntegral_iff_enorm.1 (GlobalTheory.CompanionTheory.WSum.integrable_schwartzA_haar D θ hθ W.rank t μ η hη).2
  have hN' : ∫⁻ h, ‖N (ww W x₀ h)‖ₑ ∂I.m < ⊤ := hOrb D θ hθ W I.m I.haar x₀ hx₀ N hN
  have hin : ∀ y h, ∫⁻ U, ∫⁻ k : I.l.K, F (k, h, U, y) ∂I.νK ∂I.μ₁ ≤ ‖N (ww W x₀ h)‖ₑ * ‖η y‖ₑ := fun y h => by
    simp only [hF]
    have e : ∀ U, ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm (XU d hn x₀ h U) (bl hn 1 y 0 1)))‖ₑ * ‖η y‖ₑ ∂I.νK =
        (∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm (XU d hn x₀ h U) (bl hn 1 y 0 1)))‖ₑ ∂I.νK) * ‖η y‖ₑ := fun U =>
      lintegral_mul_const' _ _ enorm_ne_top
    simp only [e]
    rw [lintegral_mul_const' _ _ enorm_ne_top, inner_eq hIkL hJn hn I hθ hM hM0 x₀ h y]
    gcongr
    rw [enorm_le_iff_norm_le]
    have h3 := hNd (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0))
    rw [jn_first] at h3
    exact h3.trans (Complex.re_le_norm _)
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ p, ‖core hn I x₀ Φ η p‖ₑ ∂(I.νK.prod (Q0 I μ))
      ≤ ∫⁻ p, F p ∂(I.νK.prod (Q0 I μ)) := lintegral_mono hle
    _ = ∫⁻ y, ∫⁻ h, ∫⁻ U, ∫⁻ k : I.l.K, F (k, h, U, y) ∂I.νK ∂I.μ₁ ∂I.m ∂μ :=
        (hFub I.l.K (GA D W) (Mx D t n) (Mx D W.rank t) I.νK I.m I.μ₁ μ).2 F hFm
    _ ≤ ∫⁻ y, ∫⁻ h, ‖N (ww W x₀ h)‖ₑ * ‖η y‖ₑ ∂I.m ∂μ :=
        lintegral_mono fun y => lintegral_mono fun h => hin y h
    _ = (∫⁻ h, ‖N (ww W x₀ h)‖ₑ ∂I.m) * ∫⁻ y, ‖η y‖ₑ ∂μ := by
        simp only [lintegral_mul_const' _ _ enorm_ne_top]
        rw [lintegral_const_mul' _ _ hN'.ne]
    _ < ⊤ := ENNReal.mul_lt_top hN' hη'

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableThetaKernelProductStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_theta_kernel_product : IkSch → Dom → OrbFin → Shift → IkLint → Fub4 → JnBl → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), x₀.det ≠ 0 → ∀ Φ ∈ schwartzA θ B.rank n, ∀ η ∈ schwartzA θ W.rank t, Integrable (core hn I x₀ Φ η) (I.νK.prod (Q0 I μ)) := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.integrable_core | exact GlobalTheory.CompanionTheory.ColumnSplitting.integrable_core | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.integrable_core <;> assumption)
end
end
