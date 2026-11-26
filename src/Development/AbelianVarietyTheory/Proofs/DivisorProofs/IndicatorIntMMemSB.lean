module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersRamificationLevelPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrSumOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
noncomputable section

open MeasureTheory ValuativeRel Matrix Filter Topology
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip

namespace GlobalTheory.KSplit

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsSmU (χ : kˣ →* ℂˣ) : Prop := IsOpen (χ.ker : Set kˣ) ∧ ∀ x, ‖(χ x : ℂ)‖ = 1


variable (k) in
def intM (m n : Type) : Set (Matrix m n k) := {X | ∀ i j, X i j ∈ 𝒪[k]}

def IsEqv {n : ℕ} (ν : kˣ →* ℂˣ) (z : ℂ) (l : (Matrix (Fin n) (Fin n) k → ℂ) → ℂ) : Prop :=
  (∀ φ ∈ SB (Matrix (Fin n) (Fin n) k), ∀ φ' ∈ SB (Matrix (Fin n) (Fin n) k), l (φ + φ') = l φ + l φ') ∧
  (∀ c : ℂ, ∀ φ ∈ SB (Matrix (Fin n) (Fin n) k), l (c • φ) = c * l φ) ∧
  ∀ g₁ g₂ : GL (Fin n) k, ∀ φ ∈ SB (Matrix (Fin n) (Fin n) k),
    (ν (gdet g₁ * gdet g₂) : ℂ) * apow (gdet g₁ * gdet g₂) z * l (fun X => φ (g₁.val * X * g₂.val)) = l φ

def indSp (a a' : ℕ) (α β : kˣ →* ℂˣ) : Submodule ℂ (GL (Fin (a + a')) k → ℂ) where
  carrier := {f | (∀ (b : GL (Fin (a + a')) k) (A : GL (Fin a) k) (D : GL (Fin a') k) (N : Matrix (Fin a) (Fin a') k),
      b.val.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks A.val N 0 D.val → ∀ h, f (b * h) =
        (α (gdet A) : ℂ) * β (gdet D) * apow (gdet A) ((a' : ℂ) / 2) * apow (gdet D) (-(a : ℂ) / 2) * f h) ∧
    ∀ᶠ u in 𝓝 (1 : GL (Fin (a + a')) k), ∀ h, f (h * u) = f h}
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun b A D N hb h => ?_, (h2.and h2').mono fun u hu h => ?_⟩
    · simp only [Pi.add_apply, h1 b A D N hb, h1' b A D N hb, mul_add]
    · simp only [Pi.add_apply, hu.1, hu.2]
  zero_mem' := ⟨fun _ _ _ _ _ _ => by simp, Eventually.of_forall fun _ _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    refine ⟨fun b A D N hb h => ?_, h2.mono fun u hu h => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, h1 b A D N hb]; ring
    · simp only [Pi.smul_apply, hu]

def mapA {a : ℕ} (a' : ℕ) (l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ) (ν β : kˣ →* ℂˣ)
    (Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ) (h : GL (Fin (a + a')) k) : ℂ :=
  l fun g => omA ν β 1 h Φ (g * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))

section Frames

variable {R S D : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

theorem restrict_mem_SB {P : Matrix R D k} {P' : Matrix D R k} (hP : P * P' = 1) {Φ : Matrix R D k → ℂ}
    (hΦ : Φ ∈ SB (Matrix R D k)) : (fun g : Matrix R R k => Φ (g * P)) ∈ SB (Matrix R R k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have c1 : Continuous fun g : Matrix R R k => g * P := continuous_id.matrix_mul continuous_const
  have c2 : Continuous fun X : Matrix R D k => X * P' := continuous_id.matrix_mul continuous_const
  have e : IsClosedEmbedding fun g : Matrix R R k => g * P :=
    Function.LeftInverse.isClosedEmbedding (f := fun X : Matrix R D k => X * P')
      (fun g => by simp only [Matrix.mul_assoc, hP, Matrix.mul_one]) c2 c1
  exact ⟨hΦ.1.comp_continuous c1, hΦ.2.comp_isClosedEmbedding e⟩


omit [DecidableEq R] [DecidableEq D] in
theorem indicator_intM_mem_SB : (intM k R D).indicator (1 : Matrix R D k → ℂ) ∈ SB (Matrix R D k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hc : IsCompact (intM k R D) := isCompact_intMatrix
  have hK : IsClopen (intM k R D) := ⟨hc.isClosed, isOpen_intMatrix⟩
  exact ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hK).isLocallyConstant,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩

theorem exists_extend_SB {P : Matrix R D k} {Q : Matrix S D k} (hP : P * Pᵀ = 1) (hQ : P * Qᵀ = 0)
    (hPQ : Pᵀ * P + Qᵀ * Q = 1) {φ : Matrix R R k → ℂ} (hφ : φ ∈ SB (Matrix R R k)) :
    ∃ Φ ∈ SB (Matrix R D k), ∀ g, Φ (g * P) = φ g := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hI := indicator_intM_mem_SB (k := k) (R := R) (D := S)
  have c1 : Continuous fun X : Matrix R D k => X * Pᵀ := continuous_id.matrix_mul continuous_const
  have c2 : Continuous fun X : Matrix R D k => X * Qᵀ := continuous_id.matrix_mul continuous_const
  have c3 : Continuous fun x : Matrix R R k × Matrix R S k => x.1 * P + x.2 * Q :=
    (continuous_fst.matrix_mul continuous_const).add (continuous_snd.matrix_mul continuous_const)
  refine ⟨fun X => φ (X * Pᵀ) * (intM k R S).indicator 1 (X * Qᵀ),
    ⟨(hφ.1.comp_continuous c1).mul (hI.1.comp_continuous c2), ?_⟩, fun g => ?_⟩
  · refine HasCompactSupport.intro ((hφ.2.isCompact.prod hI.2.isCompact).image c3) fun X hX => ?_
    by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
    refine hX ⟨(X * Pᵀ, X * Qᵀ), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, ?_⟩
    simp only [Matrix.mul_assoc, ← Matrix.mul_add, hPQ, Matrix.mul_one]
  · simp only [Matrix.mul_assoc, hP, hQ, Matrix.mul_one, Matrix.mul_zero]
    rw [Set.indicator_of_mem (show (0 : Matrix R S k) ∈ intM k R S from fun _ _ => zero_mem _)]
    simp


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem frame_rel (σ : R ⊕ S ≃ D) : X0 k σ * (X0 k σ)ᵀ = 1 ∧ Y0 k σ * (Y0 k σ)ᵀ = 1 ∧ X0 k σ * (Y0 k σ)ᵀ = 0 ∧
    Y0 k σ * (X0 k σ)ᵀ = 0 ∧ (X0 k σ)ᵀ * X0 k σ + (Y0 k σ)ᵀ * Y0 k σ = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j; rw [frameMatrixFirstColumnBlock_mul_apply]; simp [X0, Matrix.one_apply, eq_comm]
  · ext i j; rw [frameMatrixSecondColumnBlock_mul_apply]; simp [Y0, Matrix.one_apply, eq_comm]
  · ext i j; simp [frameMatrixFirstColumnBlock_mul_apply, Y0]
  · ext i j; simp [frameMatrixSecondColumnBlock_mul_apply, X0]
  · ext i j
    obtain ⟨i | i, rfl⟩ := σ.surjective i <;> obtain ⟨j | j, rfl⟩ := σ.surjective j <;>
      simp [X0, Y0, Matrix.mul_apply, Matrix.one_apply, Function.swap, eq_comm]

end Frames

variable {a a' : ℕ} {z : ℂ} {ν α β : kˣ →* ℂˣ}

theorem restrict_X0 {Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ} (hΦ : Φ ∈ SB (Matrix (Fin a) (Fin (a + a')) k)) :
    (fun g : Matrix (Fin a) (Fin a) k => Φ (g * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))) ∈ SB _ :=
  restrict_mem_SB (frame_rel _).1 hΦ

theorem mapA_omA_right (l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ) (Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ)
    (x h : GL (Fin (a + a')) k) : mapA a' l ν β (omA ν β 1 x Φ) h = mapA a' l ν β Φ (h * x) := by
  unfold mapA
  rw [← omA_mul, one_mul]

end Local

section Adelic

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def locMat {v : Pl F} (t : E →ₐ[F] Fv F v) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (b : GL (Fin n) (Fv F v)) :
    UA σ J →* GL (Fin n) (Fv F v) where
  toFun g := b⁻¹ * Matrix.GeneralLinearGroup.map (piW t) g.1 * b
  map_one' := by simp
  map_mul' g h := by simp [mul_assoc]

theorem locMat_val {v : Pl F} (t : E →ₐ[F] Fv F v) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (b : GL (Fin n) (Fv F v))
    (g : UA σ J) : (locMat t b g).val = (b⁻¹).val * (mat g).map (piW t) * b.val := rfl

end Adelic

end GlobalTheory.KSplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.RecPair

theorem coe_eq_of_frame {D : D7} {V : HSp D} {β} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (h : IsSDFrame V β Λ 1) : (Λ : Set (Fin V.rank → D.host.E)) = L0c D V := by
  obtain ⟨c, -, -, -, h1, h2⟩ := h
  simp only [one_pow, Nat.cast_one, one_smul] at h1 h2
  exact Set.ext fun x => ⟨h2 x, h1 x⟩

theorem selfDual_of_coe {D : D7} {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (h : (Λ : Set (Fin V.rank → D.host.E)) = L0c D V) : IsSelfDualC V Λ := by
  obtain rfl : Λ = GlobalTheory.PlaceModel.latFrame V := SetLike.coe_injective (h.trans (GlobalTheory.PlaceModel.coe_latFrame V).symm)
  exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem under_ne {D : D7} {e : Formalism.L2.Theta.AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt e P) {v ε}
    (hv : GlobalTheory.WeilParts.NonSplitAt D v ε) : P.under (𝓞 D.host.F) ≠ v := by
  intro hP
  obtain ⟨w, hw, -, hc⟩ := GlobalTheory.RepsCompare.exists_splitAt_of_isIdemAt h
  obtain rfl : w = v := HeightOneSpectrum.ext (hc.symm.trans (congrArg HeightOneSpectrum.asIdeal hP))
  obtain ⟨⟨α, rfl, h3, h4⟩, hn⟩ := hv
  have : α = singleV D.host.F w 1 := GlobalTheory.SplitIdem.af_ext _ fun u => by
    by_cases hu : u = w
    · subst hu; rw [h3, GlobalTheory.LatVac.evalV_singleV_same]
    · rw [h4 u hu, GlobalTheory.LatVac.evalV_singleV_ne _ w _ hu]
  subst this
  exact hn ⟨e, h.1, hw.2.2⟩

theorem exp_mu {D : D7} {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (i : Fin D.R.m) (t : T0) (τ : D.what₂.Tau) :
    ∃ a : ℤ, HasInfExp D (L.mu t ((i : ℕ) + 1)) τ a := by
  have h1 : HasInfExp D (L.mu0 ((i : ℕ) + 1)) τ (-(D.hc τ).e i) := by
    obtain ⟨n, hn, hi⟩ := (L.C.isMu0 i).inf
    refine GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => -(D.hc τ).e i) (hL.mu0 i)
      ⟨fun τ => n (D.eTau τ), fun τ => ?_, fun k => ?_⟩ τ
    · simp only [hn, Formalism.L2.Host.eExp, Equiv.symm_apply_apply]
    · rw [hi k]
      exact (Equiv.prod_comp D.eTau (fun g => (Formalism.L2.Host.embPsi D.host g (k : D.host.E) /
        ((‖Formalism.L2.Host.embPsi D.host g (k : D.host.E)‖ : ℝ) : ℂ)) ^ n g)).symm
  have h2 : HasInfExp D (L.xi t) τ 0 := by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    have := D.host.isCMField_hostE
    refine GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun _ => 0) (hL.xi t) ⟨fun _ => 0, fun _ => by norm_num, fun k => ?_⟩ τ
    rw [GlobalTheory.TypeValues.inf_eq_one _ hn ho k]
    simp
  obtain ⟨z, hz⟩ := (D.hc τ).e_int i
  refine ⟨-z, ?_⟩
  have h3 := GlobalTheory.Mem.HeckeExp.hasInfExp_mul h1 h2
  rw [hz, add_zero, ← Int.cast_neg] at h3
  exact h3

end GlobalTheory.AdTh.RecPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.StdCharWeilDatum

section Char

variable {F : Type} [Field F] [NumberField F]

theorem at_pairA (x : Ainf F) : At (evI F) (pairA F x 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  show (u.1 * x, u.2 * 0) = ((0 : Ainf F), (0 : Af F))
  rw [h1, zero_mul, mul_zero]

theorem psi_pairA {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : Ainf F) :
    ψ (pairA F x 0) = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ)) :=
  hψ.2.2 _ (at_pairA x)

theorem norm_exp_real (r : ℝ) : ‖Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ))‖ = 1 := by
  have : -(2 * Real.pi * Complex.I) * (r : ℂ) = ((-(2 * Real.pi * r) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem norm_psi_inf {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : Ainf F) : ‖ψ (pairA F x 0)‖ = 1 := by
  rw [psi_pairA hψ]; exact norm_exp_real _

theorem pairA_split (x : AF F) : x = pairA F x.1 0 + pairA F 0 x.2 := by
  show x = ((x.1 + 0 : Ainf F), (0 + x.2 : Af F))
  rw [add_zero, zero_add]
  rfl

theorem norm_psi_fin {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (y : Af F) : ‖ψ (pairA F 0 y)‖ = 1 := by
  have hc : Continuous fun y : Af F => ‖ψ (pairA F 0 y)‖ :=
    (hψ.1.comp (continuous_const.prodMk continuous_id)).norm
  have hcl : IsClosed {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := isClosed_eq hc continuous_const
  have hrange : Set.range (algebraMap F (Af F)) ⊆ {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := by
    rintro _ ⟨a, rfl⟩
    have h1 := hψ.2.1 a
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, AddChar.map_add_eq_mul] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_psi_inf hψ, one_mul, norm_one] at h2
    exact h2
  have := hcl.closure_subset_iff.2 hrange
  rw [GlobalTheory.AdeleCharTwist.denseRange_fin.closure_range] at this
  exact this (Set.mem_univ y)

theorem norm_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : AF F) : ‖ψ x‖ = 1 := by
  rw [pairA_split x, AddChar.map_add_eq_mul, norm_mul, norm_psi_inf hψ, norm_psi_fin hψ, one_mul]

theorem exists_ne_one {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : ∃ x, ψ x ≠ 1 := by
  set n : ℕ := Module.finrank ℝ (mixedEmbedding.mixedSpace F)
  have hn : 0 < n := Module.finrank_pos
  set t : ℝ := 1 / (2 * n)
  refine ⟨pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t)) 0, ?_⟩
  rw [psi_pairA hψ, RingEquiv.apply_symm_apply, Algebra.trace_algebraMap]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have eR : (n • t : ℝ) = 1 / 2 := by
    rw [nsmul_eq_mul]
    simp only [t]
    rw [mul_one_div, div_eq_div_iff (by positivity) two_ne_zero]
    ring
  have e : ((n • t : ℝ) : ℂ) = 1 / 2 := by
    rw [eR]; push_cast; ring
  rw [e]
  have : -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2) = -(Real.pi * Complex.I) := by ring
  rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem isCharAF {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : IsCharAF F ψ :=
  ⟨hψ.1, norm_psi hψ, hψ.2.1, exists_ne_one hψ⟩

end Char

section Trace

variable {F : Type} [Field F] [NumberField F]

theorem sum_eq_trace (x : Ainf F) :
    ∑ v : InfinitePlace F, (v.mult : ℝ) * (InfinitePlace.Completion.extensionEmbedding v (x v)).re =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) := by
  classical
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  simp only [Algebra.trace_complex_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace F => w.IsReal)]
  congr 1
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isReal, Nat.cast_one, one_mul, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2,
      Complex.ofReal_re]
    simp
  · refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun w => InfinitePlace.not_isReal_iff_isComplex) _ _ fun w => ?_
    have h := InfinitePlace.mult_isComplex ⟨w.1, InfinitePlace.not_isReal_iff_isComplex.1 w.2⟩
    simp only at h
    rw [h]
    push_cast
    rfl

end Trace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sum_infFam [IsTotallyReal F] (B : Base F E) (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ))
    (hθ : Formalism.IndefR.DatumF.IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ) (x : Ainf F) :
    ∑ w, θ w (x ⊗ₜ[F] (1 : E)) =
      ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ) : ℂ) := by
  rw [← sum_eq_trace]
  push_cast
  refine Fintype.sum_congr _ _ fun w => ?_
  have hv : w.IsReal := IsTotallyReal.isReal w
  rw [GlobalTheory.DualPairCompare.gen_inf_val (B.emb w).1 w (B.emb w).2.symm (θ w) (hθ w) x,
    InfinitePlace.mult_isReal ⟨_, hv⟩, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv,
    Complex.ofReal_re]
  simp

theorem isStdCharF_of_isGood : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) := by
  intro F E _ _ _ _ _ σ B hB
  haveI : IsTotallyReal F := hB.cm.1
  refine ⟨isCharAF hB.std, ⟨?_, fun θ hθ x => ?_⟩⟩
  · choose θ hθ using fun w : InfinitePlace F =>
      GlobalTheory.DualPairCompare.gen_inf_exists (B.emb w).1 w (B.emb w).2.symm
    exact ⟨θ, hθ⟩
  · show B.ψ (pairA F x 0) = _
    rw [psi_pairA hB.std, sum_infFam B θ hθ x]
    congr 1
    push_cast
    ring

end GlobalTheory.StdCharWeilDatum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCMStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) := by
  first | exact @GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood | exact GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood | (intros; apply GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CommonModel


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.CommonModel.isProper_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R}
    (hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s) : IsProper s := by
  obtain ⟨N, i, hi, rfl⟩ := hs
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  infer_instance


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.CommonModel.exists_common {R : Type} [CommRing R] {Y W₀ : Scheme.{0}}
    (s₀ : W₀ ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (hs₀ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s₀) (i₀ : Y ⟶ W₀)
    {ι : Type} (P : ι → Scheme.{0}) (p : ∀ i, P i ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (f : ∀ i, Y ⟶ P i)
    (hp : ∀ i, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (p i))
    (hf : ∀ i, f i ≫ p i = i₀ ≫ s₀) (S : Finset ι) :
    ∃ (W : Scheme.{0}) (h : Y ⟶ W) (r : W ⟶ W₀), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (r ≫ s₀) ∧ h ≫ r = i₀ ∧
      ∀ i ∈ S, ∃ g : W ⟶ P i, h ≫ g = f i ∧ g ≫ p i = r ≫ s₀ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨W₀, i₀, 𝟙 W₀, by simpa using hs₀, by simp, by simp⟩
  | insert j S _ ih =>
    obtain ⟨W, h, r, hr, hhr, hg⟩ := ih
    have hc : h ≫ (r ≫ s₀) = f j ≫ p j := by
      rw [← Category.assoc, hhr, hf]
    refine ⟨pullback (r ≫ s₀) (p j), pullback.lift h (f j) hc, pullback.fst _ _ ≫ r, ?_, ?_, ?_⟩
    · rw [Category.assoc]
      exact _root_.GlobalTheory.ProjSpace.isProjOver_pullback hr (hp j)
    · rw [← Category.assoc, pullback.lift_fst, hhr]
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · refine ⟨pullback.snd _ _, pullback.lift_snd _ _ _, ?_⟩
        rw [Category.assoc, ← pullback.condition]
      · obtain ⟨g, hg₁, hg₂⟩ := hg i hi
        refine ⟨pullback.fst _ _ ≫ g, ?_, ?_⟩
        · rw [← Category.assoc, pullback.lift_fst, hg₁]
        · rw [Category.assoc, hg₂, Category.assoc]

end GlobalTheory.CommonModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GalLift.Vec

section Mat

open Matrix
open scoped ComplexOrder

theorem exists_isONBasis {n P Q : ℕ} {G s : Matrix (Fin n) (Fin n) ℂ} (h : IsCartanInv G s)
    (hs : Formalism.UG.HasSignature G P Q) : ∃ B : Matrix (Fin n) (Fin n) ℂ, IsONBasis G s B P := by
  obtain ⟨p, q, B, B', h1, h2, h3, h4⟩ := GlobalTheory.exists_basis_adapted_to_cartan_involution n G s h.1 h.2.1 h.2.2
  have hn : p + q = n := by
    have e := Matrix.trace_mul_comm B B'
    rw [h1, h2, Matrix.trace_one, Matrix.trace_one] at e
    simp only [Fintype.card_fin, Fintype.card_sum] at e
    exact_mod_cast e.symm
  subst hn
  let e : Fin p ⊕ Fin q ≃ Fin (p + q) := finSumFinEquiv
  have hsig : Formalism.UG.HasSignature G p q := by
    refine ⟨e.symm, ⟨B.submatrix e id, B'.submatrix id e, ?_, ?_⟩, ?_⟩
    · have : B.submatrix e id * B'.submatrix id e = (B * B').submatrix e e := by
        ext a b; simp [Matrix.mul_apply]
      rw [this, h1, Matrix.submatrix_one_equiv]
    · rw [Matrix.submatrix_mul_equiv, h2, Matrix.submatrix_id_id]
    · rw [Formalism.UG.P.cT_conj_eq, Matrix.reindex_apply, Equiv.symm_symm]
      show (B.submatrix e id)ᴴ * G.submatrix e e * B.submatrix e id = _
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h3,
        Matrix.submatrix_id_id]
      rfl
  obtain ⟨rfl, -⟩ := Formalism.UG.P.signature_unique _ G _ _ _ _ hsig hs
  let ε : Fin (p + q) → ℝ := fun a => Sum.elim (fun _ => 1) (fun _ => -1) (e.symm a)
  have hd : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e.symm e.symm =
      Matrix.diagonal fun a => (ε a : ℂ) := by
    ext a b
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [ε, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp
  refine ⟨B.submatrix id e.symm, ε, fun a => ?_, ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := e.surjective a
    rcases a with a | a
    · exact Or.inl ⟨by simp [ε], by simp [e]⟩
    · exact Or.inr ⟨by simp [ε], by simp [e]⟩
  · rw [← hd, ← h3]
    rfl
  · rw [← hd, Matrix.submatrix_mul_equiv]
    exact congrArg (fun M => Matrix.submatrix M id e.symm) h4

theorem isCartanInv_one {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G 1 B k) : IsCartanInv G 1 := by
  obtain ⟨e, he, h1, -⟩ := h
  have h2 : Bᴴ * G * B = 1 := by
    rw [h1, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases he a with h | h
    · simp [h.1]
    · exact absurd a.2 (not_lt.2 h.2)
  have hu : IsUnit B := IsUnit.of_mul_eq_one_right _ h2
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have h3 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h4 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h3, Matrix.conjTranspose_one]
  have hG : G = (B⁻¹)ᴴ * B⁻¹ := by
    calc G = ((B⁻¹)ᴴ * Bᴴ) * G * (B * B⁻¹) := by rw [h3, h4, Matrix.one_mul, Matrix.mul_one]
      _ = (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one]
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_nonsing_inv_iff.2 hu))

end Mat

variable {D : D7}

theorem theta_of_thetaAt {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ} {f₀ Φ f : WO S T → ℂ}
    (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f) (h₀ : IsThetaFunO ψ S T f₀) :
    IsThetaFunO ψ S T f := by
  let U : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {g | IsThetaFunO ψ S T g}
      add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
      zero_mem' := GlobalTheory.OrientedHeis.theta_zero
      smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg }
  let H : WO S T → (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := fun w =>
    { toFun := heisO ψ S T w
      map_add' := fun a b => funext fun x => mul_add _ _ _
      map_smul' := fun a b => funext fun x => mul_left_comm _ _ _ }
  show f ∈ U
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  let A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := LinearMap.pi fun w => l ∘ₗ H w
  have hA0 : ∀ g w, A g w = l (heisO ψ S T w g) := fun _ _ => rfl
  have hA : ∀ u g, A (heisO ψ S T u g) = heisO ψ S T u (A g) := fun u g => by
    funext w
    rw [hA0, GlobalTheory.OrientedHeis.heisO_heisO, map_smul]
    rfl
  have hf0 : A f₀ = 0 := by
    funext w
    exact (Submodule.mem_dualAnnihilator l).1 hl _ ((GlobalTheory.ThetaClosed.thetaClosed ψ θ hψ hθ S T f₀ h₀).1 w)
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ (Tm + A ∘ₗ Tm) :=
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.trans Φ hΦ x hx, hA x]
        exact ((H x).map_add _ _).symm
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.modul Φ hΦ y hy, hA y]
        exact ((H y).map_add _ _).symm
      vac := by
        rw [LinearMap.add_apply, LinearMap.comp_apply, hT.vac, hf0, add_zero] }
  have e1 : f = Tm Φ := hall Tm hT
  have e2 : f = (Tm + A ∘ₗ Tm) Φ := hall _ hT'
  rw [LinearMap.add_apply, LinearMap.comp_apply, ← e1] at e2
  have e3 := congrFun (left_eq_add.1 e2) 0
  rwa [hA0, GlobalTheory.OrientedHeis.heisO_zero] at e3

theorem theta_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) {S T : HSp D} (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (P : PolF D T.rank S.rank) : IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P) :=
  (GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
    (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun c _ => GlobalTheory.OrientedHeis.theta_smul c) _
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) 1
    (fun k _ hg => ⟨GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_sub
      (GlobalTheory.OrientedHeis.theta_dRho hθ hψ k.1 _ hg)
      (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ k.1 _ hg))), rfl⟩) f hf P).1

end GlobalTheory.GalLift.Vec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorFockVacuum
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.VecFock

open scoped ComplexOrder

theorem pureTensorL_one {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (f : X → ℂ) : pureTensorL A f 1 = f := by
  have : (1 : MvPolynomial ι ℂ) = MvPolynomial.basisMonomials ι ℂ 0 := by simp
  rw [this, pureTensorL, Module.Basis.constr_basis]
  simp [opPow]

theorem jm_mul_jm {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  cases ε a <;> simp

theorem jm_herm {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  cases h : ε a <;> simp [h]

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem isCartanInv_cart (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau) : IsCartanInv (gramAt D V τ) (cart M τ) := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 := Matrix.mul_nonsing_inv _ hu
  have h2 := Matrix.nonsing_inv_mul _ hu
  have hJ := jm_mul_jm (M.ε τ)
  have c1 : ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, M.fr τ * ((M.fr τ)⁻¹ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have cJ : ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, Formalism.REAL.Jm (M.ε τ) * (Formalism.REAL.Jm (M.ε τ) * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have c2 : ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one, Matrix.one_mul]
  rw [← M.fr_gram τ]
  unfold cart
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, c1, cJ, h2]
  · simp only [Matrix.conjTranspose_mul, jm_herm, Matrix.mul_assoc, c1, cJ, c2]
  · simp only [Matrix.mul_assoc, c1, cJ]
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2 (M.fr_unit τ))

theorem isONBasis_onb (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau) (p : ℕ)
    (h : ∀ a, M.ε τ a = decide ((a : ℕ) < p)) : IsONBasis (gramAt D V τ) (cart M τ) (onb M τ) p := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 := Matrix.mul_nonsing_inv _ hu
  have c2 : ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one, Matrix.one_mul]
  have hJ : (Matrix.diagonal fun a => (((if M.ε τ a then 1 else -1 : ℝ)) : ℂ)) = Formalism.REAL.Jm (M.ε τ) := by
    unfold Formalism.REAL.Jm
    congr 1
    funext a
    cases M.ε τ a <;> simp
  refine ⟨fun a => if M.ε τ a then 1 else -1, fun a => ?_, ?_, ?_⟩
  · by_cases ha : (a : ℕ) < p
    · left; simp [h, ha]
    · right; simp [h, ha, not_lt.1 ha]
  · rw [hJ, ← M.fr_gram τ]
    simp only [onb, Matrix.mul_assoc, c2, h1, Matrix.mul_one]
  · rw [hJ]
    simp only [onb, cart, Matrix.mul_assoc, h1, Matrix.mul_one]

end GlobalTheory.AdTh.VecFock
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelFormCompatBaseEmbedding
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem lastPos_of_kapIs {D : D7} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} (h : KapIs κ) (i : Fin D.R.m) :
    (κ i).LastPos := by
  intro τ a ha
  rw [(h i τ).1 a, show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (inR i).1 (inR i).2 _]
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  have hs : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + ((i : ℕ) + 1) - 1 := rfl
  have h1 : ¬ (a : ℕ) < D.R.k - 1 := by omega
  have h2 : (a : ℕ) - (D.R.k - 1) < D.R.m := by omega
  have h3 : (⟨(a : ℕ) - (D.R.k - 1), h2⟩ : Fin D.R.m) = i := Fin.ext (by show (a : ℕ) - (D.R.k - 1) = i; omega)
  have h4 : (((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℚ) = (a : ℕ) + 1 := by exact_mod_cast ha.symm
  have h5 := (D.hc τ).gap_be i
  simp only [aPl, if_pos a.2, Formalism.L2.NTheta.lamAt, dif_neg h1, dif_pos h2, h3, h4]
  rw [Int.le_toNat (Int.floor_nonneg.2 (by linarith)), Int.le_floor]
  push_cast
  linarith

theorem lastPos_wtA_of_pins {D : D7} (Q : Par D) (h : Q.Pins) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) (hw : w.LastPos) :
    Formalism.L2.Pj.LastPos (Q.Dw j) (wtA w) := by
  intro τ hτ hm
  obtain ⟨t, rfl⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi Q h.1 τ hτ
  have hmult : (Q.Dw j).mult (DV.tauEmb D t) = (D.R.sigW j).1 := by
    unfold Datum.mult
    have hτ' : (DV.tauEmb D t) (Q.H.rt : D.host.E) = Q.H.rt0 := hτ
    rw [if_pos hτ']
    exact (h.2.2.2 j hj).1
  rw [hmult] at hm ⊢
  have h1 : 1 ≤ w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ := hw t _ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
  have h2 : ext0 (w.aP t) ((D.R.sigW j).1 - 1) = w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ := by
    unfold ext0
    rw [dif_pos (by omega)]
  unfold wtA
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
  simp only [if_true]
  omega

section Frame

variable {D : D7} {W : HSp D} {S : D.what₂.Tau → Finset (ℚ × Bool)} (M : Formalism.IndefR.Mult.DSModel W S) {r : ℕ} (hr : W.rank = r)
  (X : Data D.host.E r) {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {p : ℕ}

theorem isInvOf_cart (hx : IsModelBaseFrameFamily M hr x₀) (hp : X.p0 + p = r) (hε : ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < p)) :
    IsInvOf W hr X (fun τ => x₀ τ.1) (cart M) := by
  intro ρ τ hτ
  have hq : nNeg (M.ε ρ) = X.p0 := (nNeg_shape (by omega) (hε ρ)).trans (by omega)
  have e : mat (Ψ := X.Ψ) (fun τ => x₀ τ.1) τ = x₀ (tauE D ρ) := by rw [← hτ]; rfl
  rw [e, hx.mul, cart, Formalism.REAL.Jm, torus_x0Mat, hx ρ]
  ext a c
  have hc := c.2
  simp only [sgnM, Matrix.neg_apply, mul_diagonal, reindex_apply, submatrix_apply, hε, hq, arr, sgn,
    finCongr_symm, finCongr_apply, Fin.val_cast]
  split_ifs with h1 h2 h3
  all_goals first | (simp at *; omega) | simp

theorem isBasOf_onb (hx : IsModelBaseFrameFamily M hr x₀) (hp : X.p0 + p = r) (hε : ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < p)) :
    IsBasOf W hr X hp (fun τ => x₀ τ.1) (onb M) := by
  intro ρ τ hτ k i a hi
  have hq : nNeg (M.ε ρ) = X.p0 := (nNeg_shape (by omega) (hε ρ)).trans (by omega)
  show _ = x₀ τ.1 _ _
  rw [hτ, hx ρ]
  simp only [x0Mat, reindex_apply, submatrix_apply, hq, finCongr_symm, finCongr_apply, id, Fin.cast_cast, Fin.cast_eq_self]
  congr 1
  apply Fin.ext
  rw [hi]
  rcases k with k | k
  · have hk := k.2
    have h1 : ((rowIdx hp (Sum.inl k) : Fin r) : ℕ) = X.p0 + k := by simp [rowIdx]
    unfold arr
    split_ifs with h
    · simp only [Fin.val_cast, h1] at h; omega
    · simp only [Fin.val_cast, h1, Sum.elim_inl]; omega
  · have hk := k.2
    have h1 : ((rowIdx hp (Sum.inr k) : Fin r) : ℕ) = X.p0 - (k + 1) := by simp [rowIdx]
    unfold arr
    split_ifs with h
    · simp only [Fin.val_cast, h1, Sum.elim_inr]; omega
    · simp only [Fin.val_cast, h1] at h; omega

end Frame


end GlobalTheory.AdTh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
open NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LFun.SphComp

theorem hasSatake_of_isLocComp : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ} (π : GlobalTheory.CuspRep.CuspSub E m) {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}, GlobalTheory.LFun.HasSatGL w (π.locRep w) B → ∀ {σ : GlobalTheory.CuspRep.SmIrr (GL (Fin m) (w.adicCompletion E))}, π.IsLocComp w σ → ∃ α : Fin m → ℂˣ, Finset.univ.val.map α = B ∧ GlobalTheory.SmGL.HasSatake σ.ρ α := by
  intro E _ _ _ m π w B hB σ hσ
  obtain ⟨f, hf0, hf⟩ := hσ
  obtain ⟨x, hx⟩ := hB.exists_vec

  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    refine (((GlobalTheory.CuspRep.isIrreducible_iff σ.ρ).1 σ.irred).2 _ fun g u hu => ?_).resolve_right fun h => hf0 ?_
    · rw [LinearMap.mem_ker] at hu ⊢; rw [hf, hu, map_zero]
    · exact LinearMap.ext fun u => by
        have : u ∈ LinearMap.ker f := h ▸ Submodule.mem_top
        simpa using this

  obtain ⟨v, hv0, hvK⟩ : ∃ v : σ.V, v ≠ 0 ∧ ∀ k ∈ (GlobalTheory.LFun.KGL w (n := m) : Set _), σ.ρ k v = v := by
    refine GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup ((GlobalTheory.CuspRep.finRep E m).comp (GlobalTheory.CuspRep.locGL E m w)) σ.ρ
      σ.irred (fun i : GlobalTheory.CuspRep.LocSph.Maps π w σ => i.1) (fun i g u => i.2.2 g u) _ (x : GlobalTheory.CuspRep.Sm E m)
      (fun h => hx.1 (Subtype.ext h)) (fun k hk => ?_) ?_
    · exact congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk)
    · rw [GlobalTheory.CuspRep.LocSph.iSup_range_eq π w σ ⟨f, hf0, hf⟩]; exact x.2
  have hfv : f v ≠ 0 := fun h => hv0 (hinj (h.trans (map_zero f).symm))
  have hs : GlobalTheory.LFun.IsSatVecGL w σ.ρ v B := GlobalTheory.LFun.IsSatVecGL.of_map f hf hinj
    (hB.2 _ (GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← hf, hvK k hk]) hfv)
  exact (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ (Fin m) σ.V σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_of_isSatVecGL ⟨σ.smooth, σ.irred⟩ hs)

end GlobalTheory.LFun.SphComp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory

theorem det_ne_zero_of_hasSig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  subst hrs
  intro hM
  have key := congrArg Matrix.det hA
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one,
    Fintype.card_fin] at key
  let e : Fin r ⊕ Fin s ≃ Fin (r + s) := finSumFinEquiv
  have hsub : (Aᵀ * M * A.map star).submatrix e.symm e.symm =
      (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star := by
    ext i j
    simp [Matrix.mul_apply, Matrix.submatrix, Matrix.transpose_apply]
  have h2 := congrArg Matrix.det hsub
  rw [Matrix.det_submatrix_equiv_self, key, Matrix.det_mul, Matrix.det_mul, hM, mul_zero, zero_mul] at h2
  exact pow_ne_zero _ (by norm_num) h2

theorem isUnit_det_of_isHerm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (X : Spc F E n) (r s : ℕ), X.IsHerm σ B r s → IsUnit X.J.det := by
  intro F E _ _ _ _ _ σ B n X r s hX
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := det_ne_zero_of_hasSig (hX.sig w)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  exact isUnit_iff_ne_zero.mpr fun h0 => h (by rw [h0, map_zero])

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpaceStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_det_gram_of_hermitianSelfDualLatticeSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (X : Spc F E n) (r s : ℕ), X.IsHerm σ B r s → IsUnit X.J.det := by
  first | exact @GlobalTheory.isUnit_det_of_isHerm | exact GlobalTheory.isUnit_det_of_isHerm | (intros; apply GlobalTheory.isUnit_det_of_isHerm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.PlaneSkew

variable {E : Type} [Field E] [NumberField E]

def lowLat {n n₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) E) (L : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (𝓞 E) (Fin n₁ → E) :=
  L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))

theorem mem_lowLat {n n₁ : ℕ} {ι : Matrix (Fin n) (Fin n₁) E} {L : Submodule (𝓞 E) (Fin n → E)} {u : Fin n₁ → E} :
    u ∈ lowLat ι L ↔ ι *ᵥ u ∈ L := Iff.rfl

def PrimAt (𝔓 : HeightOneSpectrum (𝓞 E)) {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E) : Prop :=
  (∀ s : E, s • x ∈ L → 𝔓.valuation E s ≤ 1) ∧ ∃ s : E, s • x ∈ L ∧ 𝔓.valuation E s = 1

end GlobalTheory.PlaneSkew
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
noncomputable section

namespace GlobalTheory.ThK.UnipDom

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def fA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → AE F E) : AE F E :=
  v ⬝ᵥ (incM F J *ᵥ fun i => cA σ (w i))

def coA (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁) (g : UA σ J) :
    Fin d₁ → AE F E :=
  fun j => fA σ J (mat g *ᵥ (incM F H'.ι *ᵥ Pi.single j 1)) (incV F H'.y)

def coC (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁) (g : UA σ J) : AE F E :=
  fA σ J (mat g *ᵥ incV F H'.y) (incV F H'.y)

end GlobalTheory.ThK.UnipDom
end
end
