module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylFormulaStandardUnitaryGroupWeilDatum
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableThetaKernelWeilRangeStatement
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.CasimirOnParabolicInduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
public import Development.AutomorphicArithmetic.LocalEmbeddings.OppLagr

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSymmUnitaryChart
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSymmUnitaryChart
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.ChartSymm

theorem continuous_mat {D : D7} {n : ℕ} : Continuous (mat : G D n → Mx D (n + n) (n + n)) := by
  unfold GlobalTheory.StdUnn.mat
  exact Continuous.comp' Units.continuous_val continuous_induced_dom

private theorem gram_conjTranspose_eq_self {D : D7} (S : HSp D) :
    (Formalism.BasicNotions.HSpace.gram S).conjTranspose = Formalism.BasicNotions.HSpace.gram S := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Formalism.BasicNotions.HSpace.gram]
  exact S.herm.eq (S.frame j) (S.frame i)

private theorem fromRows_gram_mul_fromCols_eq_one_of_hypDec {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (μ : D.host.E)
    (hμ : μ ≠ 0) :
    Matrix.fromRows (d.e'.conjTranspose * Formalism.BasicNotions.HSpace.gram S)
        (μ⁻¹ • (d.e.conjTranspose * Formalism.BasicNotions.HSpace.gram S)) *
      Matrix.fromCols d.e (μ • d.e') = 1 := by
  have h1 : d.e'.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e = 1 := d.e'e
  have h0 : d.e.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e = 0 := d.ee
  have h0' : d.e'.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e' = 0 := d.e'e'
  have h2 : d.e.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e' = 1 := by
    have h := congrArg Matrix.conjTranspose h1
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose_eq_self,
      Matrix.conjTranspose_one] at h
    rw [Matrix.mul_assoc]
    exact h
  rw [Matrix.fromRows_mul_fromCols]
  simp only [Matrix.mul_smul, Matrix.smul_mul, h1, h0, h0', h2, smul_zero, smul_smul,
    inv_mul_cancel₀ hμ, mul_inv_cancel₀ hμ, one_smul, Matrix.fromBlocks_one]

theorem continuous_symm : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ (κ : GA D (dblSp A) ≃* G D A.rank), IsChart A μ κ →
    Continuous κ.symm := by
  intro D A μ hμ κ hκ
  have hL : ((Matrix.fromRows ((dblDec A).e'.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A))
        (μ⁻¹ • ((dblDec A).e.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A)))).submatrix
          finSumFinEquiv.symm id) * Tm A μ = 1 := by
    show _ * (Matrix.fromCols (dblDec A).e (μ • (dblDec A).e')).submatrix id finSumFinEquiv.symm = 1
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, fromRows_gram_mul_fromCols_eq_one_of_hypDec _ μ hμ.1,
      Matrix.submatrix_one_equiv]
  have hR := mul_eq_one_comm.mp hL
  set L := (Matrix.fromRows ((dblDec A).e'.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A))
        (μ⁻¹ • ((dblDec A).e.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A)))).submatrix
          finSumFinEquiv.symm id with hLdef
  have hTP : rat (Tm A μ) * rat L = (1 : Mx D (A.rank + A.rank) (A.rank + A.rank)) := by
    show (incA D).mapMatrix (Tm A μ) * (incA D).mapMatrix L = 1
    rw [← map_mul, hR, map_one]
  have key : ∀ h : G D A.rank, mt (dblSp A) (κ.symm h) = rat (Tm A μ) * mat h * rat L := by
    intro h
    have e := hκ (κ.symm h)
    rw [MulEquiv.apply_symm_apply] at e
    calc mt (dblSp A) (κ.symm h) = mt (dblSp A) (κ.symm h) * (rat (Tm A μ) * rat L) := by
          rw [hTP, Matrix.mul_one]
      _ = (mt (dblSp A) (κ.symm h) * rat (Tm A μ)) * rat L := by rw [Matrix.mul_assoc]
      _ = rat (Tm A μ) * mat h * rat L := by rw [← e]
  have hind : Topology.IsInducing (fun g : GA D (dblSp A) => matHom (dblSp A) g) := ⟨rfl⟩
  have hmi : Continuous (fun h : G D A.rank => mat h⁻¹) := by
    unfold GlobalTheory.StdUnn.mat
    simp only [map_inv]
    exact Units.continuous_coe_inv.comp continuous_induced_dom
  rw [hind.continuous_iff, Units.continuous_iff]
  constructor
  · have hf : (Units.val ∘ (fun g : GA D (dblSp A) => matHom (dblSp A) g) ∘ κ.symm) =
        fun h => rat (Tm A μ) * mat h * rat L := by
      funext h
      exact key h
    rw [hf]
    exact (continuous_const.matrix_mul continuous_mat).matrix_mul continuous_const
  · have hf : (fun h : G D A.rank => (((fun g : GA D (dblSp A) => matHom (dblSp A) g) ∘ κ.symm) h)⁻¹.val) =
        fun h => rat (Tm A μ) * mat h⁻¹ * rat L := by
      funext h
      simp only [Function.comp_apply]
      rw [← map_inv (matHom (dblSp A)), ← map_inv κ.symm]
      exact key h⁻¹
    rw [hf]
    exact (continuous_const.matrix_mul hmi).matrix_mul continuous_const

end GlobalTheory.CompanionTheory.ChartSymm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSymmUnitaryChartStatement
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_symm_unitary_chart : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ (κ : GA D (dblSp A) ≃* G D A.rank), IsChart A μ κ →
    Continuous κ.symm := by
  first | exact @GlobalTheory.CompanionTheory.ChartSymm.continuous_symm | exact GlobalTheory.CompanionTheory.ChartSymm.continuous_symm | (intros; apply GlobalTheory.CompanionTheory.ChartSymm.continuous_symm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtTorusTranslate
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtTorusTranslate
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.TorusDeriv

noncomputable def blockL (E : Type) [Field E] (r s : ℕ) : Lie E (r + s) :=
  ∑ i : Fin r, toL (Matrix.single (Fin.castAdd s i) (Fin.castAdd s i) (1 : Cinf E))

theorem blockL_apply (E : Type) [Field E] (r s : ℕ) (i j : Fin (r + s)) (w : InfinitePlace E) :
    blockL E r s i j w = if i = j then (if (i : ℕ) < r then (1 : ℂ) else 0) else 0 := by
  have e : blockL E r s i j w =
      ∑ k : Fin r, ((Matrix.single (Fin.castAdd s k) (Fin.castAdd s k) (1 : Cinf E)) i j) w := by
    simp only [blockL, Finset.sum_apply]
    rfl
  rw [e]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    by_cases hi : (i : ℕ) < r
    · rw [if_pos hi, Finset.sum_eq_single (⟨i, hi⟩ : Fin r)]
      · have : Fin.castAdd s (⟨i, hi⟩ : Fin r) = i := Fin.ext rfl
        simp [this]
      · intro b _ hb
        have : Fin.castAdd s b ≠ i := fun h => hb (Fin.ext (show (b : ℕ) = i from congrArg Fin.val h))
        simp [Matrix.single_apply, this]
      · simp
    · rw [if_neg hi]
      refine Finset.sum_eq_zero fun k _ => ?_
      have : Fin.castAdd s k ≠ i := fun h => hi (by rw [← h]; exact k.2)
      simp [Matrix.single_apply, this]
  · rw [if_neg hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : ¬ (Fin.castAdd s k = i ∧ Fin.castAdd s k = j) := fun h => hij (h.1.symm.trans h.2)
    simp [Matrix.single_apply, this]

theorem hasDerivAt_entries {ι : Type} [Fintype ι] {a : ℕ} (f : ℝ → Fin a → Fin a → ι → ℂ) (X : Fin a → Fin a → ι → ℂ)
    (h : ∀ i j w, HasDerivAt (fun t => f t i j w) (X i j w) 0) : HasDerivAt f X 0 :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun w => h i j w

theorem hasDerivAt_aInf (E : Type) [Field E] [NumberField E] (r s : ℕ) :
    HasDerivAt (fun t : ℝ => toL (aInf E (r + s) r t).val) (blockL E r s) 0 := by
  refine hasDerivAt_entries _ _ fun i j w => ?_
  rw [blockL_apply]
  have e : (fun t : ℝ => (toL (aInf E (r + s) r t).val) i j w) = fun t : ℝ =>
      if i = j then Complex.exp (if (i : ℕ) < r then (t : ℂ) else 0) else 0 := by
    funext t
    by_cases hij : i = j
    · subst hij
      simp [aInf]
    · simp [aInf, hij]
  rw [e]
  by_cases hij : i = j
  · simp only [if_pos hij]
    by_cases hi : (i : ℕ) < r
    · simp only [if_pos hi]
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).cexp
    · simp only [if_neg hi]
      simpa using hasDerivAt_const (0 : ℝ) (1 : ℂ)
  · simp only [if_neg hij]
    exact hasDerivAt_const _ _

theorem lie_blockL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) :
    lie E (r + s) (blockL E r s) =
      ∑ τ : E →+* ℂ, ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_comm, Finset.sum_congr rfl fun i _ => GlobalTheory.CompanionTheory.CapelliTrace.sum_Eop _ _, blockL, map_sum]
  rfl

theorem hasDerivAt_aT_right : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (F : Sm E (r + s)) (g : GA E (r + s)) (t : ℝ),
  HasDerivAt (fun t : ℝ => F.1 (g * aT E (r + s) r t))
    (((∑ τ : E →+* ℂ, ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i)) F).1 (g * aT E (r + s) r t)) t := by
  intro E _ _ _ r s F g t
  have h0 : aInf E (r + s) r 0 = 1 := Units.ext (by
    change Matrix.diagonal _ = 1
    rw [← Matrix.diagonal_one]
    congr 1
    funext i w
    simp)
  have h1 := hasDerivAt_curve F (g * aT E (r + s) r t) (aInf E (r + s) r) (blockL E r s) h0
    (hasDerivAt_aInf E r s)
  have h2 : HasDerivAt (fun u : ℝ => F.1 ((g * aT E (r + s) r t) * infGL E (r + s) (aInf E (r + s) r (u - t))))
      (lieD (blockL E r s) F.1 (g * aT E (r + s) r t)) t :=
    HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h1)
  rw [← lie_blockL]
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  have e : aT E (r + s) r u = aT E (r + s) r t * infGL E (r + s) (aInf E (r + s) r (u - t)) := by
    rw [← aT, ← PExpFin.aT_add]
    congr 1
    ring
  simp only []
  rw [e, mul_assoc]

end GlobalTheory.CompanionTheory.Conc.TorusDeriv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtTorusTranslateStatement
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_torus_translate : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (F : Sm E (r + s)) (g : GA E (r + s)) (t : ℝ),
  HasDerivAt (fun t : ℝ => F.1 (g * aT E (r + s) r t))
    (((∑ τ : E →+* ℂ, ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i)) F).1 (g * aT E (r + s) r t)) t := by
  first | exact @GlobalTheory.CompanionTheory.Conc.TorusDeriv.hasDerivAt_aT_right | exact GlobalTheory.CompanionTheory.Conc.TorusDeriv.hasDerivAt_aT_right | (intros; apply GlobalTheory.CompanionTheory.Conc.TorusDeriv.hasDerivAt_aT_right <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierGood
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierGood
noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisCM

open scoped TensorProduct NNReal Matrix NumberField.AdeleRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open PositivityTheory.RgEis

section Transport

variable {R R' : Type} [CommRing R] [CommRing R'] {ι : Type} [Fintype ι] [DecidableEq ι]

def glEquiv (e : R ≃+* R') : GL ι R ≃* GL ι R' := Units.mapEquiv (RingEquiv.mapMatrix e).toMulEquiv

theorem coe_glEquiv (e : R ≃+* R') (g : GL ι R) :
    ((glEquiv e g : GL ι R') : Matrix ι ι R') = (g : Matrix ι ι R).map e := rfl

theorem coe_glEquiv_inv (e : R ≃+* R') (g : GL ι R) :
    (((glEquiv e g)⁻¹ : GL ι R') : Matrix ι ι R') = ((g⁻¹ : GL ι R) : Matrix ι ι R).map e := by
  rw [← map_inv]; rfl

theorem mem_stab_iff (e : R ≃+* R') (s : Set ι) (g : GL ι R) :
    g ∈ stab R s ↔ glEquiv e g ∈ stab R' s := by
  change (∀ r ∉ s, ∀ c ∈ s, _ ∧ _) ↔ (∀ r ∉ s, ∀ c ∈ s, _ ∧ _)
  simp only [coe_glEquiv, coe_glEquiv_inv, Matrix.map_apply, EmbeddingLike.map_eq_zero_iff]

variable {E : Type} [Field E]

theorem mem_kGL_iff (A : Ad E R) (B : Ad E R') (e : R ≃+* R') (hO : ∀ x, x ∈ A.O ↔ e x ∈ B.O)
    (hφ : ∀ w, ∃ w', ∀ x, A.φ w x = B.φ w' (e x)) (hφ' : ∀ w', ∃ w, ∀ x, A.φ w x = B.φ w' (e x)) (g : GL ι R) :
    g ∈ A.kGL ι ↔ glEquiv e g ∈ B.kGL ι := by
  change ((∀ r c, _ ∧ _) ∧ ∀ w, _) ↔ ((∀ r c, _ ∧ _) ∧ ∀ w, _)
  simp only [coe_glEquiv, coe_glEquiv_inv, Matrix.map_apply, hO]
  refine and_congr_right fun _ => ⟨fun h w' => ?_, fun h w => ?_⟩
  · obtain ⟨w, hw⟩ := hφ' w'
    have : ((g : Matrix ι ι R).map e).map (B.φ w') = (g : Matrix ι ι R).map (A.φ w) := by
      ext r c; simp [hw]
    rw [this]; exact h w
  · obtain ⟨w', hw⟩ := hφ w
    have : (g : Matrix ι ι R).map (A.φ w) = ((g : Matrix ι ι R).map e).map (B.φ w') := by
      ext r c; simp [hw]
    rw [this]; exact h w'

theorem iwa_transport (A : Ad E R) (B : Ad E R') (e : R ≃+* R') (hk : ∀ g : GL ι R, g ∈ A.kGL ι ↔ glEquiv e g ∈ B.kGL ι)
    (s : Set ι) (h : Iwa (stab R' s) (B.kGL ι)) : Iwa (stab R s) (A.kGL ι) := by
  intro g
  obtain ⟨p, hp, k, hk', hg⟩ := h (glEquiv e g)
  refine ⟨(glEquiv e).symm p, ?_, (glEquiv e).symm k, ?_, ?_⟩
  · rw [mem_stab_iff e]; simpa using hp
  · rw [hk]; simpa using hk'
  · apply (glEquiv e).injective
    simp [hg]

variable [TopologicalSpace R] [TopologicalSpace R']

theorem continuous_glEquiv (e : R ≃+* R') (h : Continuous e) : Continuous (glEquiv (ι := ι) e) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id h)

theorem kcpt_transport (A : Ad E R) (B : Ad E R') (e : R ≃+* R') (h1 : Continuous e) (h2 : Continuous e.symm)
    (hk : ∀ g : GL ι R, g ∈ A.kGL ι ↔ glEquiv e g ∈ B.kGL ι) (h : IsCompact (B.kGL ι : Set (GL ι R'))) :
    IsCompact (A.kGL ι : Set (GL ι R)) := by
  let H : GL ι R ≃ₜ GL ι R' :=
    { toEquiv := (glEquiv e).toEquiv
      continuous_toFun := continuous_glEquiv e h1
      continuous_invFun := continuous_glEquiv e.symm h2 }
  have : (A.kGL ι : Set (GL ι R)) = H ⁻¹' (B.kGL ι : Set (GL ι R')) := by
    ext g; exact hk g
  rw [this]
  exact H.isCompact_preimage.2 h

end Transport

section CM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_inclR (σ : E →ₐ[F] E) (x : E) :
    cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [cA, inclR, Algebra.TensorProduct.map_tmul]

theorem cA_cA {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => simp [cA, Algebra.TensorProduct.map_tmul, GlobalTheory.OppLagr.conj_conj h]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

theorem continuous_cA (σ : E →ₐ[F] E) : Continuous (cA σ) := by
  haveI : Module.Finite (AF F) (AE F E) := inferInstance
  exact IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap

theorem cA_mem_intHat (σ : E →ₐ[F] E) {z : AE F E} (hz : z ∈ intHat F E) : cA σ z ∈ intHat F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, h1, h2, o, rfl⟩ := hz
    have ho : IsIntegral ℤ (σ (o : E)) := (RingOfIntegers.isIntegral_coe o).map σ
    refine AddSubgroup.subset_closure ⟨a, h1, h2, (⟨σ o, ho⟩ : 𝓞 E), ?_⟩
    rw [map_smul, cA_inclR]
    rfl
  | zero => simp [zero_mem]
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

end CM

theorem cmGood : StdGood → Dict → DictInf → CMGood := by
  intro hS hD hI F E _ _ _ _ _ σ χ c hcm _ hχ hres
  have hs := hS E
  obtain ⟨d1, d2, d3, d4, -⟩ := hD F E
  have hO : ∀ x, x ∈ (adCM σ χ).O ↔ eqv F E x ∈ (adStd E).O := fun x => Iff.rfl
  have hk : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : GL ι (AE F E)),
      g ∈ (adCM σ χ).kGL ι ↔ glEquiv (eqv F E) g ∈ (adStd E).kGL ι := fun ι _ _ g =>
    mem_kGL_iff _ _ _ hO (fun w => ⟨w, fun _ => rfl⟩) (fun w => ⟨w, fun _ => rfl⟩) g
  have hu : Continuous (Units.map (eqv F E).toRingHom.toMonoidHom) := Continuous.units_map _ d1
  have hi : ∀ x : Eˣ, Units.map (eqv F E).toRingHom.toMonoidHom (Units.map (inclR (F := F) (AF F)).toMonoidHom x) =
      Units.map (adStd E).i.toMonoidHom x := fun x => Units.ext (d3 x)
  obtain ⟨ξ, hξ⟩ := GlobalTheory.OppLagr.exists_isQuad hcm
  refine ⟨⟨?_, ?_, ?_, ?_, hχ.1, hχ.2, ?_, ?_⟩, cA_cA hcm, continuous_cA σ, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    apply hs.iinj
    change algebraMap E 𝔸[E] x = algebraMap E 𝔸[E] y
    rw [← d3, ← d3]
    exact congrArg _ hxy
  · intro x y
    change (adStd E).lg (Units.map _ (x * y)) = _
    rw [map_mul]
    exact hs.lgmul _ _
  · exact hs.lgcont.comp hu
  · intro x
    exact (congrArg (adStd E).lg (hi x)).trans (hs.lgi x)
  · intro ι _ _
    exact kcpt_transport _ _ (eqv F E) d1 d2 (hk ι) (hs.kcpt ι)
  · intro ι _ _ s
    exact iwa_transport _ _ (eqv F E) (hk ι) s (hs.iwa ι s)
  · intro x hx
    have h1 : finOne F • x ∈ intHat F E := (d4 x).1 hx
    refine (d4 _).2 ?_
    have h2 := cA_mem_intHat σ h1
    rwa [map_smul] at h2
  · intro w x
    exact (hI F E σ hcm).1 w x
  · intro x
    exact ⟨σ x, cA_inclR σ x⟩
  · intro x
    exact ResEtaPow.map_conj hξ hres x

end GlobalTheory.CompanionTheory.RgEisCM
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierGoodStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_multiplier_good : PositivityTheory.RgEis.StdGood → PositivityTheory.RgEis.Dict → PositivityTheory.RgEis.DictInf → PositivityTheory.RgEis.CMGood := by
  first | exact @GlobalTheory.CompanionTheory.RgEisCM.cmGood | exact GlobalTheory.CompanionTheory.RgEisCM.cmGood | (intros; apply GlobalTheory.CompanionTheory.RgEisCM.cmGood <;> assumption)
end
end
