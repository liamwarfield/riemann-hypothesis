module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeOfSmoothBorelKilled
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftWeightSizesEventuallyAlongFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWEigenpartEqRowsFullHecke
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainLocalDataIntegralOffLevels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityMapExtremalVectorHolomorphicType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityMapComplexRightDerivativeEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityMapComplexRightDerivativeEq
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.MultDer

theorem rderC_eq : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → ∀ (v : M.Vec) (τ : D.what₂.Tau) (Z : Mt V.rank) (y : M.sm τ), (y : M.H τ) = dRepC (gramAt D V τ) (M.rep τ) Z (v τ : M.H τ) → RderC θ V τ Z (T v) = T (Function.update v τ y) := by
  intro D θ V _ S M J χ T hT v τ Z y hy
  obtain ⟨hc, hU, -⟩ := GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ
  have hu := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  obtain ⟨hsp, hsm⟩ := GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv V.rank (gramAt D V τ) (M.H τ) (M.rep τ)
    (GlobalTheory.SmoothAutCheck.gramAt_herm V τ) hu.ne_zero hU
  have hv : SmoothVec (lieH (gramAt D V τ)) (M.rep τ) (v τ : M.H τ) := hsp _ (v τ).2
  obtain ⟨h1, -, -, h4⟩ := hsm _ hv
  funext g
  obtain ⟨ℓ, hℓ, hval⟩ := hT.cont τ v g
  have key : ∀ X ∈ lieAt V τ, Rder θ V τ X (T v) g = ℓ (dRep (M.rep τ) X (v τ : M.H τ)) := by
    intro X hX
    have e : (fun t : ℝ => T v (g * oneP θ V τ X t)) =
        fun t : ℝ => ℓ (M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ)) := by
      funext t
      have hm := GlobalTheory.SmoothAutCheck.exp_mem_UH hu hX t
      let w : M.sm τ := ⟨M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ), Submodule.subset_span (h1 _ hm)⟩
      have h := congrFun (hT.equiv τ _ hm v w rfl) g
      exact ((hval w).trans h).symm
    unfold Rder
    rw [e]
    exact (h4 ℓ hℓ X hX).deriv
  obtain ⟨p1, p2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  have h := hval y
  rw [hy] at h
  refine Eq.trans ?_ h
  unfold RderC dRepC
  rw [Pi.add_apply, Pi.smul_apply, key _ p1, key _ p2, map_add (f := _), map_smul]
  rfl

end GlobalTheory.MultDer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityMapComplexRightDerivativeEqStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicityMap_complexRightDerivative_eq : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → ∀ (v : M.Vec) (τ : D.what₂.Tau) (Z : Mt V.rank) (y : M.sm τ), (y : M.H τ) = dRepC (gramAt D V τ) (M.rep τ) Z (v τ : M.H τ) → RderC θ V τ Z (T v) = T (Function.update v τ y) := by
  first | exact @GlobalTheory.MultDer.rderC_eq | exact GlobalTheory.MultDer.rderC_eq | (intros; apply GlobalTheory.MultDer.rderC_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityMapExtremalVectorHolomorphicType
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultHol

section Local

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {Hm : ι → Mt n}

omit [Fintype ι] [DecidableEq ι] in
theorem one_mem_UG : (1 : ι → Mt n) ∈ UG Hm := fun τ => by
  show (1 : Mt n)ᴴ * Hm τ * 1 = Hm τ
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem mul_mem_UG {u u' : ι → Mt n} (hu : u ∈ UG Hm) (hu' : u' ∈ UG Hm) : u * u' ∈ UG Hm := fun τ => by
  have h1 : (u τ)ᴴ * Hm τ * u τ = Hm τ := hu τ
  have h2 : (u' τ)ᴴ * Hm τ * u' τ = Hm τ := hu' τ
  show (u τ * u' τ)ᴴ * Hm τ * (u τ * u' τ) = Hm τ
  calc _ = (u' τ)ᴴ * ((u τ)ᴴ * Hm τ * u τ) * u' τ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Hm τ := by rw [h1, h2]

omit [Fintype ι] in
theorem mulSingle_mem_UG (τ : ι) {g : Mt n} (hg : g ∈ Formalism.QuantumDeterminants.UH (Hm τ)) :
    (Pi.mulSingle τ g : ι → Mt n) ∈ UG Hm := fun ρ => by
  by_cases h : ρ = τ
  · subst h; simpa using hg
  · rw [Pi.mulSingle_eq_of_ne h]; exact one_mem_UG (Hm := Hm) ρ

omit [Fintype ι] [DecidableEq ι] in
theorem lift_prod {G : Type} [Group G] (L : (ι → Mt n) → G)
    (hL : ∀ u ∈ UG Hm, ∀ u' ∈ UG Hm, L (u * u') = L u * L u') (l : List (ι → Mt n)) (hl : ∀ u ∈ l, u ∈ UG Hm) :
    l.prod ∈ UG Hm ∧ L l.prod = (l.map L).prod := by
  induction l with
  | nil =>
    refine ⟨one_mem_UG, ?_⟩
    have h := hL 1 one_mem_UG 1 one_mem_UG
    rw [mul_one] at h
    simpa using h
  | cons a l ih =>
    have ha := hl a (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := ih fun u hu => hl u (List.mem_cons_of_mem _ hu)
    rw [List.prod_cons, List.map_cons, List.prod_cons]
    exact ⟨mul_mem_UG ha h1, by rw [hL a ha _ h1, h2]⟩

theorem parts_mem_lieH {G : Mt n} (hh : G.IsHermitian) (hd : G.det ≠ 0) (Z : Mt n) :
    (1 / 2 : ℂ) • (Z + conjH G Z) ∈ lieH G ∧ (1 / (2 * Complex.I)) • (Z - conjH G Z) ∈ lieH G := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hd
  have e1 : G * conjH G Z = -(Zᴴ * G) := by
    rw [conjH, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  have e2 : (conjH G Z)ᴴ * G = -(G * Z) := by
    have := congrArg conjTranspose e1
    simpa only [conjTranspose_mul, conjTranspose_neg, conjTranspose_conjTranspose, hh.eq] using this
  constructor
  · show _ + _ = _
    have s : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [conjTranspose_smul, s, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, conjTranspose_add, Matrix.add_mul,
      Matrix.mul_add, e1, e2]
    simp
  · show _ + _ = _
    have s : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
      simp
    rw [conjTranspose_smul, s, Matrix.smul_mul, Matrix.mul_smul, neg_smul, ← smul_neg, ← smul_add, conjTranspose_sub,
      Matrix.sub_mul, Matrix.mul_sub, e1, e2]
    have : -(Zᴴ * G - -(G * Z)) + (G * Z - -(Zᴴ * G)) = 0 := by abel
    rw [this, smul_zero]

end Local

theorem holAd_of_isMultMap : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → HolAd θ M w (T v) := by
  classical
  intro D θ V S M w v hθ hS hw hv J χ T hT g
  obtain ⟨L, -, hmul, -, -, hinv, hat, -, -, hG⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  have hexp : ∀ τ, ∀ X ∈ lieH (gramAt D V τ), ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
    fun τ X hX t => GlobalTheory.SmVec.exp_mem_UH ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hG τ).2)) hX t
  have hone : ∀ τ, ∀ X ∈ lieH (gramAt D V τ), ∀ t : ℝ,
      L (Pi.mulSingle τ (NormedSpace.exp (t • X))) = oneP θ V τ X t :=
    fun τ X hX t => (hat τ _ (hexp τ X hX t)).symm
  refine ⟨fun u => T v (g * L u), ?_, fun u hu => by simp only [hinv u hu]⟩
  refine GlobalTheory.T.holomorphicType_of_smooth_borelKilled _ _ _ _ _ _ (fun τ => ((GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.2.2 hS).1) _ ?_ ?_
  · intro k τs Xs hX u hu
    have h := (hT.aut v).smooth k τs Xs hX (g * L u)
    convert h using 2 with t
    obtain ⟨h1, h2⟩ := lift_prod L hmul
      (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : D.what₂.Tau → Mt V.rank)) (by
        intro x hx
        obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
        exact mulSingle_mem_UG _ (hexp _ _ (hX i) _))
    show T v (g * L (u * _)) = _
    rw [hmul u hu _ h1, h2, List.map_ofFn, mul_assoc]
    exact congrArg (fun F : Fin k → GA D V => T v (g * (L u * (List.ofFn F).prod))) (funext fun i => hone _ _ (hX i) _)
  · intro τ a c hac u hu
    have hder : ∀ X ∈ lieH (gramAt D V τ), der τ X (fun u => T v (g * L u)) u = Rder θ V τ X (T v) (g * L u) := by
      intro X hX
      unfold der Rder
      congr 1
      funext t
      show T v (g * L (u * _)) = _
      rw [hmul u hu _ (mulSingle_mem_UG _ (hexp _ _ hX _)), hone τ X hX, mul_assoc]
    obtain ⟨p1, p2⟩ := parts_mem_lieH (hG τ).1 (hG τ).2 (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹)
    have hk := (GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight D θ V S M w v hθ hS hw hv τ).2 a c hac
    have hd := GlobalTheory.T.multiplicityMap_complexRightDerivative_eq D θ V hθ S M J χ T hT v τ (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹)
      (if a = c then (w τ a : ℂ) • v τ else 0) (by rw [hk]; split_ifs <;> rfl)
    have e : derC (gramAt D V) τ (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (fun u => T v (g * L u)) u =
        RderC θ V τ (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (T v) (g * L u) := by
      unfold derC
      rw [hder _ p1, hder _ p2]
      rfl
    rw [e, hd]
    split_ifs
    · rw [T.map_update_smul, Function.update_eq_self]
      rfl
    · rw [T.map_update_zero]
      rfl

end GlobalTheory.MultHol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityMapExtremalVectorHolomorphicTypeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicityMap_extremalVector_holomorphicType : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → HolAd θ M w (T v) := by
  first | exact @GlobalTheory.MultHol.holAd_of_isMultMap | exact GlobalTheory.MultHol.holAd_of_isMultMap | (intros; apply GlobalTheory.MultHol.holAd_of_isMultMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersLeftMulGLIffIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersLeftMulGLIffIntegral
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

section Top

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {a : ℕ}

theorem isCompact_boundedGL (R : ℝ) :
    IsCompact {g : GLw a w | ∀ i j, ‖g.val i j‖ ≤ R ∧ ‖(g⁻¹).val i j‖ ≤ R} := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion E w
  have hK : IsCompact {A : Matrix (Fin a) (Fin a) (w.adicCompletion E) | ∀ i j, ‖A i j‖ ≤ R} := by
    have h : IsCompact (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a =>
        Metric.closedBall (0 : w.adicCompletion E) R) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    have e : {A : Matrix (Fin a) (Fin a) (w.adicCompletion E) | ∀ i j, ‖A i j‖ ≤ R} =
        (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a =>
          Metric.closedBall (0 : w.adicCompletion E) R) :=
      Set.ext fun A => ⟨fun hA i _ j _ => by simpa using hA i j, fun hA i j => by simpa using hA i trivial j trivial⟩
    rw [e]
    exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin a) (Fin a) (w.adicCompletion E))).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
    (MulOpposite.op_injective).mem_set_image]
  exact ⟨fun hg => ⟨fun i j => (hg i j).1, fun i j => (hg i j).2⟩, fun hg i j => ⟨hg.1 i j, hg.2 i j⟩⟩

theorem isCompact_closure_zpowers_iff (g : GLw a w) :
    IsCompact (closure (Subgroup.zpowers g : Set (GLw a w))) ↔
      ∃ R : ℝ, ∀ n : ℤ, ∀ i j, ‖(g ^ n).val i j‖ ≤ R := by
  constructor
  · intro hc
    have hb : ∀ i j : Fin a, ∃ C : ℝ, ∀ h ∈ closure (Subgroup.zpowers g : Set (GLw a w)), ‖h.val i j‖ ≤ C :=
      fun i j => hc.exists_bound_of_continuousOn (f := fun h : GLw a w => h.val i j)
        ((Units.continuous_val (M := Matrix (Fin a) (Fin a) (w.adicCompletion E))).matrix_elem i j).continuousOn
    choose C hC using hb
    refine ⟨∑ i, ∑ j, max (C i j) 0, fun n i j => ?_⟩
    have h1 := hC i j (g ^ n) (subset_closure (Subgroup.zpow_mem_zpowers g n))
    calc _ ≤ max (C i j) 0 := h1.trans (le_max_left _ _)
      _ ≤ ∑ j', max (C i j') 0 :=
        Finset.single_le_sum (f := fun j' => max (C i j') 0) (fun _ _ => le_max_right _ _) (Finset.mem_univ j)
      _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j', max (C i' j') 0)
        (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) (Finset.mem_univ i)
  · rintro ⟨R, hR⟩
    refine (isCompact_boundedGL R).closure_of_subset ?_
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    refine fun i j => ⟨hR n i j, ?_⟩
    rw [← _root_.zpow_neg]
    exact hR (-n) i j

end Top

section Alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : GlobalTheory.UnitLemma.InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

omit [IsCMField E] in
theorem norm_le_one_iff_mem (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (x : K.E) :
    ‖e x‖ ≤ 1 ↔ x ∈ (algebraMap K.O K.E).range := by
  rw [he]
  exact Valued.toNormedField.norm_le_one_iff


omit [IsCMField E] in
theorem exists_norm_ge (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (R : ℝ) :
    ∃ c : K.E, c ≠ 0 ∧ R ≤ ‖e c‖ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hπ0 : algebraMap K.O K.E π ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective K.O K.E)]
    exact hπ.ne_zero
  have hn : ¬ (algebraMap K.O K.E π)⁻¹ ∈ (algebraMap K.O K.E).range := by
    rintro ⟨o, ho⟩
    apply hπ.not_isUnit
    have h : π * o = 1 := IsFractionRing.injective K.O K.E (by rw [map_mul, ho, mul_inv_cancel₀ hπ0, map_one])
    exact isUnit_iff_exists_inv.2 ⟨o, h⟩
  have h1 : 1 < ‖e (algebraMap K.O K.E π)⁻¹‖ := by
    rw [← not_le, norm_le_one_iff_mem e he]
    exact hn
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R h1
  refine ⟨((algebraMap K.O K.E π)⁻¹) ^ n, pow_ne_zero _ (inv_ne_zero hπ0), ?_⟩
  rw [map_pow, norm_pow]
  exact hn.le


omit [IsCMField E] in
theorem exists_fg_of_crd_le (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (R : ℝ) :
    ∃ M : Submodule K.O B.A, M.FG ∧ ∀ y, (∀ i, ‖crd e b y i‖ ≤ R) → y ∈ M := by
  obtain ⟨c, hc0, hc⟩ := exists_norm_ge e he R
  refine ⟨Submodule.span K.O (Set.range fun j => c • b j), Submodule.fg_span (Set.finite_range _), fun y hy => ?_⟩
  have hec : e c ≠ 0 := by rwa [Ne, map_eq_zero_iff _ e.injective]
  rw [← b.sum_repr y]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hm : b.repr y j / c ∈ (algebraMap K.O K.E).range := by
    rw [← norm_le_one_iff_mem e he, map_div₀, norm_div, div_le_one (norm_pos_iff.2 hec)]
    exact (hy j).trans hc
  obtain ⟨o, ho⟩ := hm
  have : b.repr y j • b j = o • (c • b j) := by
    rw [← algebraMap_smul K.E o, smul_smul, ho, div_mul_cancel₀ _ hc0]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem isIntegral_of_bounded (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (u : B.A)
    (R : ℝ) (hR : ∀ n : ℕ, ∀ i j, ‖mulHom e b (u ^ n) i j‖ ≤ R) : IsIntegral K.O u := by
  obtain ⟨M, hMfg, hM⟩ := exists_fg_of_crd_le e b he (∑ j, R * ‖crd e b 1 j‖)
  have hle : Subalgebra.toSubmodule (Algebra.adjoin K.O {u}) ≤ M := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le, ← Submonoid.powers_eq_closure]
    rintro _ ⟨n, rfl⟩
    refine hM _ fun i => ?_
    have h1 : crd e b (u ^ n) = mulHom e b (u ^ n) *ᵥ crd e b 1 := by rw [← crd_mul, mul_one]
    rw [h1]
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hR n i j) (norm_nonneg _)
  haveI : IsNoetherian K.O M := isNoetherian_of_fg_of_noetherian M hMfg
  haveI : IsNoetherian K.O (Subalgebra.toSubmodule (Algebra.adjoin K.O {u})) := isNoetherian_of_le hle
  exact isIntegral_of_submodule_noetherian _ this u (Algebra.self_mem_adjoin_singleton K.O u)

theorem bounded_of_fg (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (M : Submodule K.O B.A)
    (hM : M.FG) : ∃ R : ℝ, ∀ y ∈ M, ∀ i j, ‖mulHom e b y i j‖ ≤ R := by
  obtain ⟨S, rfl⟩ := hM
  refine ⟨∑ y ∈ S, ∑ i, ∑ j, ‖mulHom e b y i j‖, fun x hx i j => ?_⟩
  obtain ⟨f, -, rfl⟩ := Submodule.mem_span_finset.1 hx
  have hsum : mulHom e b (∑ y ∈ S, f y • y) i j = ∑ y ∈ S, e (algebraMap K.O K.E (f y)) * mulHom e b y i j := by
    rw [mulHom_apply]
    simp only [mulHom_apply, Finset.sum_mul, smul_mul_assoc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← algebraMap_smul K.E (f _), map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul, map_mul]
  rw [hsum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [norm_mul]
  have h1 : ‖e (algebraMap K.O K.E (f y))‖ ≤ 1 := (norm_le_one_iff_mem e he _).2 ⟨f y, rfl⟩
  calc _ ≤ 1 * ‖mulHom e b y i j‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖mulHom e b y i j‖ := one_mul _
    _ ≤ ∑ j', ‖mulHom e b y i j'‖ :=
      Finset.single_le_sum (f := fun j' => ‖mulHom e b y i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖mulHom e b y i' j'‖ :=
      Finset.single_le_sum (f := fun i' => ∑ j', ‖mulHom e b y i' j'‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

end Alg

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : GlobalTheory.UnitLemma.InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

theorem mulGL_zpow_val (t : B.Aˣ) (n : ℤ) : ((mulGL e b t) ^ n).val = mulHom e b ((t ^ n : B.Aˣ) : B.A) := by
  rw [← map_zpow]
  rfl

theorem isCompact_closure_zpowers_mulGL_iff' (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1)
    (t : B.Aˣ) : IsCompact (closure (Subgroup.zpowers (mulGL e b t) : Set (GLw a w))) ↔
      t ∈ GlobalTheory.UnitLemma.intUnits K.O B.A := by
  rw [isCompact_closure_zpowers_iff]
  simp only [mulGL_zpow_val]
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨isIntegral_of_bounded e b he _ R fun n i j => ?_, isIntegral_of_bounded e b he _ R fun n i j => ?_⟩
    · have := hR n i j
      rwa [zpow_natCast, Units.val_pow_eq_pow_val] at this
    · have := hR (-(n : ℤ)) i j
      rwa [_root_.zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val] at this
  · rintro ⟨h1, h2⟩
    obtain ⟨R, hR⟩ := bounded_of_fg e b he _
      (fg_adjoin_of_finite (s := {(t : B.A), ((t⁻¹ : B.Aˣ) : B.A)}) (Set.toFinite _)
        (by rintro x (rfl | rfl); exacts [h1, h2]))
    refine ⟨R, fun n i j => hR _ ((Subalgebra.mem_toSubmodule _).2 ?_) i j⟩
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · rw [zpow_natCast, Units.val_pow_eq_pow_val]
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _)) k
    · rw [_root_.zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton _))) k

end Main

theorem isCompact_closure_zpowers_mulGL_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A) (t : B.Aˣ), IsCompact (closure (Subgroup.zpowers (GlobalTheory.TwOrbLat.mulGL e b t) : Set (GLw a w))) ↔ t ∈ GlobalTheory.UnitLemma.intUnits K.O B.A :=
  fun _ _ _ _ _ _ e he _ _ b t => isCompact_closure_zpowers_mulGL_iff' e b he t

end GlobalTheory.TwOrbLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersLeftMulGLIffIntegralStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_closure_zpowers_leftMulGL_iff_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A) (t : B.Aˣ), IsCompact (closure (Subgroup.zpowers (GlobalTheory.TwOrbLat.mulGL e b t) : Set (GLw a w))) ↔ t ∈ GlobalTheory.UnitLemma.intUnits K.O B.A := by
  first | exact @GlobalTheory.TwOrbLat.isCompact_closure_zpowers_mulGL_iff | exact GlobalTheory.TwOrbLat.isCompact_closure_zpowers_mulGL_iff | (intros; apply GlobalTheory.TwOrbLat.isCompact_closure_zpowers_mulGL_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseLevelVectorOfPrincipalLevelFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseLevelVectorOfPrincipalLevelFixed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section
namespace GlobalTheory.BaseVec

theorem coeff_conj_of_central {K : Type} [Field K] {H : Type} [Group H] (z : MonoidAlgebra K H)
    (hz : ∀ b, b * z = z * b) (g h : H) : z.coeff (g * h * g⁻¹) = z.coeff h := by
  have e := congrArg (fun y : MonoidAlgebra K H => y.coeff (g * h)) (hz (MonoidAlgebra.single g 1))
  simpa [mul_assoc] using e.symm

section Levels

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem baseLevelDatum_level_eq (P' : LevelP R.Pg D.R.r ℂ) : (R.dat0 P').P = P' := by
  simp [LevCh.dat0, datY]

theorem mem_levS (P' : LevelP R.Pg D.R.r ℂ) (x : GA D (Yc D 0)) :
    x ∈ levS _ (R.βY 0) (R.dat0 P') ↔ x ∈ GfC (Yc D 0) ∧ finE (Yc D 0) x ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv) ∧
      rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) x) ∈ P'.H := by
  show x ∈ GfC (Yc D 0) ∧ (finE (Yc D 0) x ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P') ∧
      rTup (R.βY 0) (R.dat0 P') (finE (Yc D 0) x) ∈ (R.dat0 P').P.H) ↔ _
  rw [baseLevelDatum_level_eq]
  rfl

theorem principalRowLevelCharacter_trivial (P' : LevelP R.Pg D.R.r ℂ) (x : GA D (Yc D 0)) :
    levChi _ (R.βY 0) (R.dat0 P') x = ((ext1 P'.H P'.chi (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) x)) : ℂˣ) : ℂ) := by
  simp [levChi, levFn, LevCh.dat0, datY]
  rfl

theorem conj_mem_principal {x y : GA D (Yc D 0)} (hx : x ∈ levS _ (R.βY 0) (R.dat0 R.triv)) (hy1 : y ∈ GfC (Yc D 0))
    (hy2 : finE (Yc D 0) y ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv)) :
    y⁻¹ * x * y ∈ levS _ (R.βY 0) (R.dat0 R.triv) := by
  rw [mem_levS] at hx ⊢
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hyi := Subgroup.inv_mem _ hy2
  refine ⟨(GfC _).mul_mem ((GfC _).mul_mem ((GfC _).inv_mem hy1) hx1) hy1, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyi hx2) hy2
  · rw [map_mul, map_mul, map_inv, rTup_mul (Subgroup.mul_mem _ hyi hx2) hy2, rTup_mul hyi hx2, rTup_inv hy2]
    have : rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) x) = 1 := Subgroup.mem_bot.1 hx3
    rw [this, mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _

theorem lift_div_principal {g0 : G0 R.Pg D.R.r} {κ κ' : GA D (Yc D 0)}
    (hκ : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ) (hκ' : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ') :
    κ⁻¹ * κ' ∈ levS _ (R.βY 0) (R.dat0 R.triv) := by
  rw [mem_levS]
  have hi := Subgroup.inv_mem _ hκ.2.1
  refine ⟨(GfC _).mul_mem ((GfC _).inv_mem hκ.1) hκ'.1, ?_, ?_⟩
  · rw [map_mul, map_inv]; exact Subgroup.mul_mem _ hi hκ'.2.1
  · refine Subgroup.mem_bot.2 ?_
    rw [map_mul, map_inv, rTup_mul hi hκ'.2.1, rTup_inv hκ.2.1, hκ.2.2, hκ'.2.2]
    exact inv_mul_cancel g0

end Levels


open Formalism.IndefR.principalLevelFrame in
theorem exists_base_vec : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) (π : Formalism.L2.NG.FinTyp D.host.E n) (v : Formalism.AUTREP.GAf D.host.E n → ℂ), v ∈ π.S → v ≠ 0 → principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 R.triv)) (fun _ => 1) v → (∀ κ : G → Formalism.AUTREP.GAf D.host.E n, (∀ g, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ (κ g))) → ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (κ g) v = v) → ∃ x ∈ π.S, x ≠ 0 ∧ principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 (R.levR F false))) (fun κ => levChi _ (R.βY 0) (R.dat0 (R.levR F false)) (PY.ψ κ)) x := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk hC hne n PY π v hvS hv0 hvT hgood
  classical
  have hL := GlobalTheory.DimFull.liftsY' hC
  have hex : ∀ g : G, ∃ κ : Formalism.AUTREP.GAf D.host.E n,
      IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ κ) := by
    intro g
    obtain ⟨κ, hκ⟩ := hL (R.eG g)
    obtain ⟨h, rfl⟩ := PY.onto κ hκ.1
    exact ⟨h, hκ⟩
  choose k hk using hex
  set J0 := PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 R.triv) with hJ0
  have hvfix : ∀ c ∈ J0, Formalism.L2.NG.rt D.host.E n c v = v := fun c hc => by
    simpa using hvT c hc
  set Ws : Submodule ℂ (Formalism.AUTREP.GAf D.host.E n → ℂ) :=
    Submodule.span ℂ (Set.range fun g => Formalism.L2.NG.rt D.host.E n (k g) v) with hWs
  have hfix : ∀ w ∈ Ws, ∀ c ∈ J0, Formalism.L2.NG.rt D.host.E n c w = w := by
    intro w hw c hc
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      have hc' : (k g)⁻¹ * c * k g ∈ J0 := by
        rw [hJ0, Set.mem_preimage]
        rw [map_mul, map_mul, map_inv]
        exact GlobalTheory.BaseVec.conj_mem_principal R hc (hk g).1 (hk g).2.1
      rw [rt_rt, show c * k g = k g * ((k g)⁻¹ * c * k g) by group, ← rt_rt, hvfix _ hc']
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | smul a x _ hx => rw [map_smul, hx]
  have hprod : ∀ g h, ∀ w ∈ Ws, Formalism.L2.NG.rt D.host.E n (k g) (Formalism.L2.NG.rt D.host.E n (k h) w) =
      Formalism.L2.NG.rt D.host.E n (k (g * h)) w := by
    intro g h w hw
    have hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (g * h)) (PY.ψ (k g * k h)) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [map_mul]; exact (GfC _).mul_mem (hk g).1 (hk h).1
      · rw [map_mul, map_mul]; exact Subgroup.mul_mem _ (hk g).2.1 (hk h).2.1
      · rw [map_mul, map_mul, rTup_mul (hk g).2.1 (hk h).2.1, (hk g).2.2, (hk h).2.2]
        exact (map_mul R.eG g h).symm
    have hc : (k (g * h))⁻¹ * (k g * k h) ∈ J0 := by
      rw [hJ0, Set.mem_preimage]
      rw [map_mul, map_inv]
      exact GlobalTheory.BaseVec.lift_div_principal R (hk (g * h)) hl
    rw [rt_rt, show k g * k h = k (g * h) * ((k (g * h))⁻¹ * (k g * k h)) by group, ← rt_rt, hfix w hw _ hc]
  have hk1 : k 1 ∈ J0 := by
    rw [hJ0, Set.mem_preimage, GlobalTheory.BaseVec.mem_levS]
    refine ⟨(hk 1).1, (hk 1).2.1, Subgroup.mem_bot.2 ?_⟩
    rw [(hk 1).2.2]
    exact map_one R.eG
  have hvWs : v ∈ Ws := by
    have : Formalism.L2.NG.rt D.host.E n (k 1) v ∈ Ws := Submodule.subset_span ⟨1, rfl⟩
    rwa [hvfix _ hk1] at this
  have hstab : ∀ g, ∀ w ∈ Ws, Formalism.L2.NG.rt D.host.E n (k g) w ∈ Ws := by
    intro g w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [hprod g h v hvWs]
      exact Submodule.subset_span ⟨g * h, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Ws.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Ws.smul_mem a hx
  let ρ : Representation ℂ G Ws :=
    { toFun := fun g => (Formalism.L2.NG.rt D.host.E n (k g)).restrict (fun w hw => hstab g w hw)
      map_one' := LinearMap.ext fun w => Subtype.ext (hfix w w.2 _ hk1)
      map_mul' := fun g h => LinearMap.ext fun w => Subtype.ext (hprod g h w w.2).symm }
  haveI : FiniteDimensional ℂ Ws := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hX : ∀ χ ∈ A.X, IsAbsIrrChar χ := hOk.irr
  have hcen : ∀ g h : G, RealDat.eC (A := A) D.what₂.embLL (g * h * g⁻¹) = RealDat.eC (A := A) D.what₂.embLL h := fun g h => by
    unfold RealDat.eC
    rw [GlobalTheory.BaseVec.coeff_conj_of_central _ (fun b => idemOf_central A.X hX b) g h]
  have hgoodv : ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (k g) v = v := hgood k hk
  have hgoodW : ∀ w ∈ Ws, ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (k g) w = w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      simp only [hprod _ h v hvWs]
      conv_rhs => rw [← hgoodv]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_smul, hprod h _ v hvWs]
      refine Fintype.sum_equiv (MulAut.conj h⁻¹).toEquiv _ _ fun g => ?_
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
      rw [hcen, show h * (h⁻¹ * g * h⁻¹⁻¹) = g * h by group]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add (f := _), smul_add, Finset.sum_add_distrib, hx, hy]
    | smul a x _ hx =>
      simp only [map_smul]
      simp only [smul_comm _ a, ← Finset.smul_sum, hx]
  have hbot : (⊤ : Submodule ℂ Ws) ≠ ⊥ := by
    intro h
    have h0 : (⟨v, hvWs⟩ : Ws) ∈ (⊥ : Submodule ℂ Ws) := h ▸ Submodule.mem_top
    exact hv0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h0))
  obtain ⟨u, -, hu0, hu⟩ := GlobalTheory.Hk3.exists_level_vector D.what₂.embLL A.X F.P0 F.ψ0 ρ ⊤ hX hne (fun _ => le_top) hbot
    (fun u _ => Subtype.ext (by
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      exact hgoodW u u.2))
  refine ⟨(u : Formalism.AUTREP.GAf D.host.E n → ℂ), ?_, fun h => hu0 (Subtype.ext h), ?_⟩
  · exact (Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact π.stable _ _ hvS)) u.2
  · intro κ hκ
    obtain ⟨h1, h2, h3⟩ := (GlobalTheory.BaseVec.mem_levS R _ (PY.ψ κ)).1 hκ
    have hgP : R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ))) ∈ F.P0 := h3
    have hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv)
        (R.eG (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ))))) (PY.ψ κ) :=
      ⟨h1, h2, (MulEquiv.apply_symm_apply R.eG _).symm⟩
    have hc : (k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ)))))⁻¹ * κ ∈ J0 := by
      rw [hJ0, Set.mem_preimage]
      rw [map_mul, map_inv]
      exact GlobalTheory.BaseVec.lift_div_principal R (hk _) hl
    have e1 : Formalism.L2.NG.rt D.host.E n κ (u : _ → ℂ) =
        Formalism.L2.NG.rt D.host.E n (k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ))))) u := by
      conv_lhs => rw [show κ = k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ)))) *
        ((k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ)))))⁻¹ * κ) by group]
      rw [← rt_rt, hfix u u.2 _ hc]
    have e2 := congrArg Subtype.val (hu ⟨_, hgP⟩)
    rw [e1]
    refine e2.trans ?_
    show _ = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F false)) (PY.ψ κ) • _
    rw [GlobalTheory.BaseVec.principalRowLevelCharacter_trivial, Submodule.coe_smul]
    congr 1
    exact ((congrArg (fun u : ℂˣ => (u : ℂ)) (extendOne_of_mem (R.levR F false).chi h3)).trans rfl).symm

end GlobalTheory.BaseVec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseLevelVectorOfPrincipalLevelFixedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseLevel_vector_of_principalLevel_fixed : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) (π : Formalism.L2.NG.FinTyp D.host.E n) (v : Formalism.AUTREP.GAf D.host.E n → ℂ), v ∈ π.S → v ≠ 0 → principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 R.triv)) (fun _ => 1) v → (∀ κ : G → Formalism.AUTREP.GAf D.host.E n, (∀ g, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ (κ g))) → ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (κ g) v = v) → ∃ x ∈ π.S, x ≠ 0 ∧ principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 (R.levR F false))) (fun κ => levChi _ (R.βY 0) (R.dat0 (R.levR F false)) (PY.ψ κ)) x := by
  first | exact @GlobalTheory.BaseVec.exists_base_vec | exact GlobalTheory.BaseVec.exists_base_vec | (intros; apply GlobalTheory.BaseVec.exists_base_vec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryCentralizerEquivNormOneTorus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryCentralizerEquivNormOneTorus
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.CentTorusModel

variable {K : UQ} (B : InvAlg K) {n : ℕ} (ψ : B.A ≃ₗ[K.E] (Fin n → K.E))

def mulMat (a : B.A) : Matrix (Fin n) (Fin n) K.E :=
  LinearMap.toMatrix' (ψ.toLinearMap ∘ₗ LinearMap.mulLeft K.E a ∘ₗ ψ.symm.toLinearMap)

theorem mulMat_mulVec (a y : B.A) : mulMat B ψ a *ᵥ ψ y = ψ (a * y) := by
  simp [mulMat, LinearMap.toMatrix'_mulVec]

theorem eq_mulMat {M : Matrix (Fin n) (Fin n) K.E} {a : B.A} (h : ∀ y, M *ᵥ ψ y = ψ (a * y)) :
    M = mulMat B ψ a := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  obtain ⟨y, rfl⟩ := ψ.surjective v
  simp only [Matrix.toLin'_apply, h, mulMat_mulVec]

theorem mulMat_one : mulMat B ψ 1 = 1 :=
  (eq_mulMat B ψ (fun y => by simp)).symm

theorem mulMat_mul (a b : B.A) : mulMat B ψ (a * b) = mulMat B ψ a * mulMat B ψ b :=
  (eq_mulMat B ψ (fun y => by rw [← Matrix.mulVec_mulVec, mulMat_mulVec, mulMat_mulVec, mul_assoc])).symm

def mulHom : B.A →* Matrix (Fin n) (Fin n) K.E where
  toFun := mulMat B ψ
  map_one' := mulMat_one B ψ
  map_mul' := mulMat_mul B ψ

theorem commutant (hs : B.P.Separable) (f : B.A →ₗ[K.E] B.A) (hf : ∀ y, f (B.g * y) = B.g * f y) (y : B.A) :
    f y = f 1 * y := by
  obtain ⟨b, hb⟩ := exists_basis_pow_of_separable K B hs
  have key : f = LinearMap.mulRight K.E (f 1) := by
    refine b.ext fun i => ?_
    rw [hb i, LinearMap.mulRight_apply]
    generalize (i : ℕ) = k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', hf, ih, mul_assoc]
  rw [key, LinearMap.mulRight_apply, LinearMap.mulRight_apply, one_mul, mul_comm]

theorem stdH_mulVec_eq (M : Matrix (Fin n) (Fin n) K.E) (u v : Fin n → K.E) :
    stdH K n (M *ᵥ u) (M *ᵥ v) = u ⬝ᵥ ((Mᵀ * M.map K.c) *ᵥ fun k => K.c (v k)) := by
  have h1 : (fun k => K.c ((M *ᵥ v) k)) = M.map K.c *ᵥ fun k => K.c (v k) := by
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum]
  have h2 : stdH K n (M *ᵥ u) (M *ᵥ v) = (M *ᵥ u) ⬝ᵥ fun k => K.c ((M *ᵥ v) k) := rfl
  rw [h2, h1, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm,
    Matrix.mulVec_mulVec]

theorem stdH_mulVec_iff (M : Matrix (Fin n) (Fin n) K.E) :
    (∀ u v, stdH K n (M *ᵥ u) (M *ᵥ v) = stdH K n u v) ↔ (M.map K.c)ᵀ * M = 1 := by
  constructor
  · intro h
    ext i j
    have := h (Pi.single j 1) (Pi.single i 1)
    simp [InertUnitOrb.stdH, Pi.single_apply] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← this]
    exact Finset.sum_congr rfl fun k _ => by simp [mul_comm]
  · intro h u v
    have h' : Mᵀ * M.map K.c = 1 := by
      have := congrArg (fun X => X.map K.c) h
      simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_one _ (map_zero K.c) (map_one K.c)] at this
      convert this using 2
      ext a b; simp [K.c_c]
    rw [stdH_mulVec_eq, h', Matrix.one_mulVec]
    rfl

theorem isom_iff {γ' : Matrix (Fin n) (Fin n) K.E} {x : B.Aˣ} (hm : IsModel B γ' x ψ) (a : B.A) :
    (∀ u v, stdH K n (mulMat B ψ a *ᵥ u) (mulMat B ψ a *ᵥ v) = stdH K n u v) ↔ a * B.σ a = 1 := by
  have hh := hm.2.2
  constructor
  · intro h
    have h2 : ∀ y z, B.herm x (a * y) (a * z) = B.herm x y z := by
      intro y z
      rw [← hh, ← hh, ← mulMat_mulVec, ← mulMat_mulVec]
      exact h _ _
    have h3 : ∀ z, B.herm x (a * B.σ a - 1) z = 0 := by
      intro z
      have := h2 1 z
      simp only [InvAlg.herm] at this ⊢
      rw [show (x : B.A) * (a * B.σ a - 1) * B.σ z = (x : B.A) * (a * 1) * B.σ (a * z) - x * 1 * B.σ z by
        rw [map_mul]; ring, map_sub, this, sub_self]
    have h4 : ψ (a * B.σ a - 1) = 0 := by
      funext k
      have := h3 (ψ.symm (Pi.single k 1))
      rw [← hh, ψ.apply_symm_apply] at this
      simpa [InertUnitOrb.stdH, Pi.single_apply] using this
    exact sub_eq_zero.mp ((LinearEquiv.map_eq_zero_iff ψ).mp h4)
  · intro h u v
    obtain ⟨y, rfl⟩ := ψ.surjective u
    obtain ⟨z, rfl⟩ := ψ.surjective v
    rw [mulMat_mulVec, mulMat_mulVec, hh, hh]
    simp only [InvAlg.herm, map_mul]
    congr 1
    calc (x : B.A) * (a * y) * (B.σ a * B.σ z) = x * y * B.σ z * (a * B.σ a) := by ring
      _ = _ := by rw [h, mul_one]

theorem map_map_symm {R S : Type} [Ring R] [Ring S] (e : R ≃+* S) (M : Matrix (Fin n) (Fin n) R) :
    (M.map e).map e.symm = M := by
  ext i j; simp

theorem map_symm_map {R S : Type} [Ring R] [Ring S] (e : R ≃+* S) (M : Matrix (Fin n) (Fin n) S) :
    (M.map e.symm).map e = M := by
  ext i j; simp

theorem unitary_map {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E}
    (e : K.E ≃+* w.adicCompletion E) (he : ∀ x, e (K.c x) = cj w (e x)) (M : Matrix (Fin n) (Fin n) K.E) :
    cT (cj w) (M.map e) * 1 * M.map e = 1 ↔ (M.map K.c)ᵀ * M = 1 := by
  have h1 : cT (cj w) (M.map e) = ((M.map K.c)ᵀ).map e := by
    ext i j; simp [cT, he]
  rw [h1, mul_one, ← Matrix.map_mul]
  constructor
  · intro h
    have : ((((M.map K.c)ᵀ * M).map e).map e.symm) = (1 : Matrix (Fin n) (Fin n) _).map e.symm := by rw [h]
    rw [map_map_symm] at this
    simpa using this
  · intro h
    rw [h]; simp

theorem cent_equiv_torus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∃ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, ∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y := by
  intro E _ _ _ _ w hw K e he _ n B ψ x γ hm hs
  have hUL : UL n w = UJ (cj w) 1 := by simp [UL, hw]
  let ρ : B.A →* Matrix (Fin n) (Fin n) (w.adicCompletion E) :=
    (e.toRingHom.mapMatrix : Matrix (Fin n) (Fin n) K.E →+* _).toMonoidHom.comp (mulHom B ψ)
  have hρa : ∀ a, ρ a = (mulMat B ψ a).map e := fun a => rfl
  have hγ' := eq_mulMat B ψ (fun y => (hm.2.1 y).symm)
  have hγ : (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = ρ B.g := by
    rw [hρa, ← hγ', map_symm_map]
  have hmem : ∀ u : B.Aˣ, u ∈ B.T → (Units.map ρ u : GLw n w) ∈ UL n w := by
    intro u hu
    rw [hUL]
    show cT (cj w) (((Units.map ρ u : GLw n w)) : Matrix (Fin n) (Fin n) _) * 1 * _ = 1
    rw [Units.coe_map, hρa, unitary_map e he, ← stdH_mulVec_iff, isom_iff B ψ hm]
    exact hu
  have hcent : ∀ (u : B.Aˣ) (hu : u ∈ B.T),
      (⟨Units.map ρ u, hmem u hu⟩ : UL n w) ∈ twCent (MonoidHom.id (UL n w)) γ := by
    intro u hu
    show _ * γ = γ * _
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, MonoidHom.id_apply, Units.coe_map, hγ]
    rw [← map_mul, ← map_mul, mul_comm]
  let φ : B.T →* twCent (MonoidHom.id (UL n w)) γ :=
    { toFun := fun u => ⟨⟨Units.map ρ u, hmem u u.2⟩, hcent u u.2⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext; apply Units.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext; apply Subtype.ext; apply Units.ext
        simp }
  have hφ : ∀ u : B.T, ((((φ u : twCent (MonoidHom.id (UL n w)) γ) : UL n w) : GLw n w) :
      Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (mulMat B ψ ((u : B.Aˣ) : B.A)).map e := fun u => rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 := congrArg (fun t : twCent (MonoidHom.id (UL n w)) γ =>
      (((t : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) hab
    simp only [hφ, map_map_symm] at h1
    have h2 : ψ (((a : B.Aˣ) : B.A) * 1) = ψ (((b : B.Aˣ) : B.A) * 1) := by
      rw [← mulMat_mulVec, ← mulMat_mulVec, h1]
    apply Subtype.ext; apply Units.ext
    simpa using ψ.injective h2
  have hsurj : Function.Surjective φ := by
    intro t
    set T : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (((t : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hT
    set T' := T.map e.symm with hT'
    have hc : T * (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) _) =
        (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) _) * T := by
      have := t.2
      change (t : UL n w) * γ = γ * (t : UL n w) at this
      have := congrArg (fun s : UL n w => ((s : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) this
      simpa using this
    have hc' : T' * mulMat B ψ B.g = mulMat B ψ B.g * T' := by
      rw [← hγ', hT', ← Matrix.map_mul, ← Matrix.map_mul, hc]
    let f : B.A →ₗ[K.E] B.A := ψ.symm.toLinearMap ∘ₗ Matrix.toLin' T' ∘ₗ ψ.toLinearMap
    have hfa : ∀ y, ψ (f y) = T' *ᵥ ψ y := by
      intro y; simp [f]
    have hf : ∀ y, f (B.g * y) = B.g * f y := by
      intro y
      apply ψ.injective
      rw [hfa, ← mulMat_mulVec, ← mulMat_mulVec, hfa, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc']
    have ha : ∀ y, T' *ᵥ ψ y = ψ (f 1 * y) := by
      intro y; rw [← hfa, commutant B hs f hf y]
    have hM := eq_mulMat B ψ ha
    have hTu : cT (cj w) T * 1 * T = 1 := by
      have hULmem : ∀ g : GLw n w, g ∈ UL n w → g ∈ UJ (cj w) 1 := fun g hg => by rwa [hUL] at hg
      exact hULmem _ (t : UL n w).2
    have hu : f 1 * B.σ (f 1) = 1 := by
      rw [← isom_iff B ψ hm, stdH_mulVec_iff, ← hM, ← unitary_map e he, hT', map_symm_map]
      exact hTu
    let u : B.Aˣ := ⟨f 1, B.σ (f 1), hu, by rw [mul_comm]; exact hu⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    change (mulMat B ψ (f 1)).map e = T
    rw [← hM, hT', map_symm_map]
  refine ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm, fun t y => ?_⟩
  have h1 : φ ((MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm t) = t :=
    (MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).apply_symm_apply t
  conv_rhs => rw [← h1]
  rw [hφ, map_map_symm, mulMat_mulVec]

end GlobalTheory.CentTorusModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryCentralizerEquivNormOneTorusStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localUnitaryCentralizer_equiv_normOneTorus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∃ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, ∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y := by
  first | exact @GlobalTheory.CentTorusModel.cent_equiv_torus | exact GlobalTheory.CentTorusModel.cent_equiv_torus | (intros; apply GlobalTheory.CentTorusModel.cent_equiv_torus <;> assumption)
end
end
