module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticone
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairInvolutionContinuous
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackChartFormula
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtZeroHeisenbergCMRealLineTheta
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.AlmostGoodOf

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientJacquetSegment
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientJacquetSegment
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegFineCons

theorem finSigmaFinEquiv_one_val {s : ℕ} (i : Fin s) (b : Fin 1) :
    ((finSigmaFinEquiv (m := s) (n := fun _ => 1) ⟨i, b⟩ : Fin _) : ℕ) = i := by
  rw [finSigmaFinEquiv_apply, Subsingleton.elim b 0]
  simp

theorem eq_one_of_sum_eq {s : ℕ} (c : Fin s → ℕ) (h1 : ∀ a, 1 ≤ c a) (h : ∑ a, c a = s) (a : Fin s) : c a = 1 := by
  have h2 : ∑ _a : Fin s, 1 = ∑ a, c a := by simpa using h.symm
  exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => h1 i)).1 h2 a (Finset.mem_univ a)).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem sum_concat_fst {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) :
    ∑ i, (concat c x i).1 = ∑ a, ∑ b, (x a b).1 := by
  rw [← Fintype.sum_sigma' (fun a b => (x a b).1)]
  exact Equiv.sum_comp finSigmaFinEquiv.symm (fun p : Σ a, Fin (c a) => (x p.1 p.2).1)


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem concat_finSigmaFinEquiv {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) (p : Σ a, Fin (c a)) :
    concat c x (finSigmaFinEquiv p) = x p.1 p.2 := by
  have key : ∀ q : Σ a, Fin (c a), q = p → x q.1 q.2 = x p.1 p.2 := by
    rintro _ rfl
    rfl
  exact key _ (Equiv.symm_apply_apply _ _)

theorem exists_cusp_word (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (y : IrrGL (k := k)) :
    ∃ (c : ℕ) (x : Fin c → IrrGL (k := k)) (hd : ∑ b, (x b).1 = y.1), (∀ b, (x b).IsCusp) ∧ 1 ≤ jm x hd y.rep := by
  obtain ⟨c, x, hd, hc, φ, hφ⟩ := GlobalTheory.CompanionTheory.SubEmb.subEmbedding k y.1 _ y.rep y.2.rep.smooth y.2.rep.irr
  have := Model.nontrivial_of_isIrreducible y.2.rep.irr
  obtain ⟨v, hv⟩ := exists_ne (0 : y.2.rep.V)
  exact ⟨c, x, hd, hc, GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA x hd _ y.2.rep.smooth φ
    ⟨v, fun h => hv (hφ (h.trans (map_zero φ).symm))⟩⟩

theorem equiv_piTensor_dec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Γ : Segment k) (hF : FineJac Γ) (u : IrrGL (k := k)) (hu : IsLSeg Γ u.rep) (hs : ∑ i, (dec Γ i).1 = u.1) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Levi k fun i => Fin ((dec Γ i).1)) X), ρ.IsIrreducible → IsSubquotient ρ (GlobalTheory.SmGL.jac (stdBlocks (fun i => (dec Γ i).1) hs) u.rep) → Nonempty (ρ.Equiv (piTensor fun i => (dec Γ i).rep)) := by
  intro k _ _ _ _ hA Γ hF u hu hs X _ _ ρ hi hsub
  have hsm : IsSmooth ρ := hsub.isSmooth (isSmooth_jac _ u.2.rep.smooth)
  obtain ⟨σ, ⟨E⟩⟩ := GlobalTheory.T.levi_irreducible_tensor_decomposition hA (fun i => (dec Γ i).1) (⟨X, ρ, hsm, hi⟩ : IrrRep _)
  replace E : ρ.Equiv (piTensor fun a => (σ a).rep.ρ) := E
  suffices hσ : σ = fun a => (dec Γ a).2 by
    subst hσ
    exact ⟨E⟩
  let y : Fin Γ.len → IrrGL (k := k) := fun i => ⟨(dec Γ i).1, σ i⟩
  have hy : ∑ a, (y a).1 = u.1 := hs
  have h1 : 1 ≤ jm y hy u.rep := Order.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2
    ((IsSubquotient.of_surjective E.toIntertwiningMap E.toLinearEquiv.surjective).trans hsub))
  choose c x hd hcusp hpos using fun a => exists_cusp_word hA (y a)
  have hcat : ∑ i, (concat c x i).1 = u.1 := by
    rw [sum_concat_fst, ← hy]
    exact Finset.sum_congr rfl fun a _ => hd a
  have h2 : 1 ≤ jm (concat c x) hcat u.rep := h1.trans
    (GlobalTheory.CompanionTheory.JmTrans.jm_le_jm_concat hA y hy c x hd hcat hpos u.rep u.2.rep.smooth
      (hasFiniteLength_of_isIrreducible u.2.rep.irr))
  obtain ⟨h, hcon⟩ := (hF u.rep hu).2 _ (concat c x) hcat (fun a => hcusp _ _) h2
  have hc0 : ∀ a, 1 ≤ c a := fun a => by
    refine Nat.one_le_iff_ne_zero.2 fun h0 => ?_
    have : IsEmpty (Fin (c a)) := by rw [h0]; exact Fin.isEmpty
    have h3 : (y a).1 = 0 := by rw [← hd a]; simp
    exact Γ.d_pos.ne' h3
  obtain rfl : c = fun _ => 1 := funext (eq_one_of_sum_eq c hc0 h)
  funext a
  have h3 : x a 0 = dec Γ (Fin.cast h (finSigmaFinEquiv ⟨a, 0⟩)) :=
    (concat_finSigmaFinEquiv _ x ⟨a, 0⟩).symm.trans (hcon (finSigmaFinEquiv ⟨a, 0⟩))
  have h4 : dec Γ (Fin.cast h (finSigmaFinEquiv ⟨a, 0⟩)) = dec Γ a :=
    congrArg _ (Fin.ext (finSigmaFinEquiv_one_val a 0))
  have h5 : x a 0 = y a := GlobalTheory.CompanionTheory.SegFine.eq_of_one_le_jm (y a) (y a).rep (.refl _) (x a) (hd a) (hpos a)
  have h6 : (⟨(dec Γ a).1, σ a⟩ : IrrGL (k := k)) = ⟨(dec Γ a).1, (dec Γ a).2⟩ := (h5.symm.trans h3).trans h4
  exact sigma_mk_injective (β := fun n => IrrCl (GL (Fin n) k)) h6

end GlobalTheory.CompanionTheory.SegFineCons

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientJacquetSegmentStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_subquotient_jacquet_segment : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Γ : Segment k) (hF : FineJac Γ) (u : IrrGL (k := k)) (hu : IsLSeg Γ u.rep) (hs : ∑ i, (dec Γ i).1 = u.1) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Levi k fun i => Fin ((dec Γ i).1)) X), ρ.IsIrreducible → IsSubquotient ρ (jac (stdBlocks (fun i => (dec Γ i).1) hs) u.rep) → Nonempty (ρ.Equiv (piTensor fun i => (dec Γ i).rep)) := by
  first | exact @GlobalTheory.CompanionTheory.SegFineCons.equiv_piTensor_dec | exact GlobalTheory.CompanionTheory.SegFineCons.equiv_piTensor_dec | (intros; apply GlobalTheory.CompanionTheory.SegFineCons.equiv_piTensor_dec <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinTestTw

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.FC GlobalTheory.CompanionTheory.FinLevelTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

theorem exists_lift (Y : ∀ w : Pl E, GLw n w) (hc : ∀ᶠ w : Pl E in cofinite, Y w ∈ GlobalTheory.LFun.KGL w (n := n)) :
    ∃ x : GL (Fin n) (Af E), ∀ w, GeneralLinearGroup.map (pLoc E w) x = Y w := by
  let M : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => (Y w).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => ((Y w)⁻¹).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).2 i j⟩
  have hloc : ∀ P Q : Matrix (Fin n) (Fin n) (Af E), (∀ w : Pl E, P.map (pLoc E w) = Q.map (pLoc E w)) → P = Q :=
    fun P Q h => Matrix.ext fun i j => Subtype.ext (funext fun w => congrFun (congrFun (h w) i) j)
  have hMM' : M * M' = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).mul_inv
  have hM'M : M' * M = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).inv_mul
  exact ⟨⟨M, M', hMM', hM'M⟩, fun w => Units.ext (Matrix.ext fun i j => rfl)⟩

theorem eventually_mem_KGL (g : GL (Fin n) (Af E)) :
    ∀ᶠ w : Pl E in cofinite, GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have h1 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w (g.1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => (g.1 i j).2
  have h2 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w ((g⁻¹).1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => ((g⁻¹).1 i j).2
  filter_upwards [h1, h2] with w h1 h2
  exact GlobalTheory.EulerTwRestr.mem_KGL_iff.2 ⟨fun i j => by rw [GlobalTheory.EulerTwRestr.loc_val]; exact h1 i j,
    fun i j => by rw [GlobalTheory.EulerTwRestr.loc_inv_val]; exact h2 i j⟩

theorem coe_pair_compact_subgroup (a b : ℕ) (w : Pl E) : (K2 a b w : Set (GLw a w × GLw b w)) =
    (GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)) ×ˢ (GlobalTheory.LFun.KGL w (n := b) : Set (GLw b w)) := Subgroup.coe_prod _ _

theorem mem_prod_Kf {x : Gf E a b} :
    x ∈ (Kf E a).prod (Kf E b) ↔ ∀ w : Pl E, atHom a b w x ∈ K2 a b w := by
  simp only [Subgroup.mem_prod, Kf, Subgroup.mem_iInf, Subgroup.mem_comap, forall_and]
  rfl

theorem isRestrW (a b : ℕ) :
    GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch (Gf E a b)) (atHom (E := E) a b) (K2 a b) := by
  have hset : {x : Gf E a b | ∀ w : Pl E, atHom a b w x ∈ K2 a b w} =
      (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) :=
    Set.ext fun x => (mem_prod_Kf (x := x)).symm.trans Subgroup.mem_prod
  refine ⟨fun w => w.elim, continuous_atHom, fun w => ?_, fun w => ?_, fun x y _ H => ?_, fun x => ?_, fun c y hy => ?_, ?_, fun C _ => ?_⟩
  · rw [coe_pair_compact_subgroup]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1
  · rw [coe_pair_compact_subgroup]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
  · exact Prod.ext (GlobalTheory.EulerTwRestr.gl_ext fun w => congrArg Prod.fst (H w))
      (GlobalTheory.EulerTwRestr.gl_ext fun w => congrArg Prod.snd (H w))
  · filter_upwards [eventually_mem_KGL x.1, eventually_mem_KGL x.2] with w h1 h2
    exact ⟨h1, h2⟩
  · obtain ⟨x₁, h₁⟩ := exists_lift (fun w => (y w).1) (hy.mono fun w h => h.1)
    obtain ⟨x₂, h₂⟩ := exists_lift (fun w => (y w).2) (hy.mono fun w h => h.2)
    exact ⟨(x₁, x₂), fun w => w.elim, fun w => Prod.ext (h₁ w) (h₂ w)⟩
  · rw [hset]
    exact GlobalTheory.CompanionTheory.EulerV.isOpen_Kf.prod GlobalTheory.CompanionTheory.EulerV.isOpen_Kf
  · have e : {x : Gf E a b | (∀ w, GlobalTheory.RestrMeas.noArch (Gf E a b) w x ∈ C w) ∧ ∀ w : Pl E, atHom a b w x ∈ K2 a b w} =
        (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) := by
      rw [← hset]
      exact Set.ext fun x => ⟨fun h => h.2, fun h => ⟨fun w => w.elim, h⟩⟩
    rw [e]
    exact GlobalTheory.CompanionTheory.EulerV.isCompact_Kf.prod GlobalTheory.CompanionTheory.EulerV.isCompact_Kf

theorem eventually_eq_indicator {φ : Fam E a b} (h : IsTestP φ) :
    ∀ᶠ w : Pl E in cofinite, φ w = (K2 a b w : Set (GLw a w × GLw b w)).indicator 1 := by
  obtain ⟨K₁, K₂, -, -, h⟩ := h
  exact h.2

theorem hasCompactSupport_loc {φ : Fam E a b} (h : IsTestP φ) (w : Pl E) : HasCompactSupport (φ w) := by
  obtain ⟨K₁, K₂, -, -, h⟩ := h
  exact (h.1 w).1

theorem factors_ne_zero {S : Set (Pl E)} {φ₁ φ₂ : Fam E a b} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) {y : Gf E a b}
    (hy : finFn S φ₁ φ₂ y ≠ 0) (w : Pl E) (hw : w ∈ S) :
    φ₁ w (atW w y) ≠ 0 ∧ (IsSplitAt w → φ₂ w (atW w (thP E a b y)) ≠ 0) := by
  set g : Pl E → ℂ := fun w => φ₁ w (atW w y) * if IsSplitAt w then φ₂ w (atW w (thP E a b y)) else 1 with hg
  have hone : ∀ᶠ w in cofinite, g w = 1 := by
    filter_upwards [eventually_eq_indicator h₁, eventually_eq_indicator h₂, (isRestrW a b).eventually_mem y,
      (isRestrW a b).eventually_mem (thP E a b y)] with w e₁ e₂ m₁ m₂
    have m₁' : atW w y ∈ (K2 a b w : Set (GLw a w × GLw b w)) := m₁
    have m₂' : atW w (thP E a b y) ∈ (K2 a b w : Set (GLw a w × GLw b w)) := m₂
    simp only [hg]
    rw [e₁, e₂, Set.indicator_of_mem m₁', Set.indicator_of_mem m₂']
    simp
  have hfin : (S ∩ Function.mulSupport g).Finite :=
    (eventually_cofinite.1 hone).subset fun w hw => hw.2
  have hz : g w ≠ 0 := by
    intro h0
    apply hy
    change ∏ᶠ w ∈ S, g w = 0
    rw [finprod_mem_eq_prod g hfin]
    exact Finset.prod_eq_zero (hfin.mem_toFinset.2 ⟨hw, by simp [Function.mem_mulSupport, h0]⟩) h0
  refine ⟨left_ne_zero_of_mul hz, fun hs => ?_⟩
  have hz' := right_ne_zero_of_mul hz
  rwa [if_pos hs] at hz'

end GlobalTheory.CompanionTheory.FinTestTw

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointsEqIffSameTorusOrbit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointsEqIffSameTorusOrbit
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.Orbit

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem exists_mem_blockChart (w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀) (k : Fin (m + 1)) :
    ∃ i, w ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) :=
  ⟨ptChart _ k, GlobalTheory.CxPts.mem_ptsIn.2 (mem_ptChart _ k)⟩

theorem exists_ne_zero_of_isUnder {w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ}
    (h : IsUnder w z) (k : Fin (m + 1)) : ∃ i, z ⟨k, i⟩ ≠ 0 :=
  (exists_mem_blockChart w k).imp fun i hi => (h k i).1.1 hi

theorem sameOrbit_of_isUnder {w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀} {z z' : (Σ k, Bk n k) → ℂ}
    (h : IsUnder w z) (h' : IsUnder w z') : SameOrbit z z' := by
  choose c hc using exists_mem_blockChart w
  refine ⟨fun k => z ⟨k, c k⟩ / z' ⟨k, c k⟩,
    fun k => div_ne_zero ((h k _).1.1 (hc k)) ((h' k _).1.1 (hc k)), ?_⟩
  funext ⟨k, j⟩
  have e := ((h k (c k)).2 j (hc k)).symm.trans ((h' k (c k)).2 j (hc k))
  have a := (h k _).1.1 (hc k)
  have b := (h' k _).1.1 (hc k)
  rw [div_eq_div_iff a b] at e
  show z ⟨k, j⟩ = z ⟨k, c k⟩ / z' ⟨k, c k⟩ * z' ⟨k, j⟩
  rw [div_mul_eq_mul_div, eq_div_iff b]
  linear_combination e

theorem eq_iff_sameOrbit (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y y' : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z z' : (Σ k, Bk n k) → ℂ)
    (h : IsUnder (PtsOver.map i rfl _ y) z) (h' : IsUnder (PtsOver.map i rfl _ y') z') :
    y = y' ↔ SameOrbit z z' := by
  constructor
  · rintro rfl
    exact sameOrbit_of_isUnder h h'
  · intro ho
    have e := (Under.existsUnique_isUnder m n z (exists_ne_zero_of_isUnder h)).unique h
      (isUnder_of_sameOrbit m n _ z' z h' ho)
    exact Subtype.ext ((cancel_mono i).1 (congrArg Subtype.val e))

end GlobalTheory.CompanionTheory.MixZ.Orbit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointsEqIffSameTorusOrbitStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_eq_iff_same_torus_orbit : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y y' : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z z' : (Σ k, Bk n k) → ℂ),
    IsUnder (PtsOver.map i rfl _ y) z → IsUnder (PtsOver.map i rfl _ y') z' → (y = y' ↔ SameOrbit z z') := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit | exact GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit | (intros; apply GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionary
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionary
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsHorizontal charOf)
open GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.CompanionTheory.MixZ.PtDictProof

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem C_mem_ptIdeal_iff (x : MP ℤ m n) (a : ℤ) :
    (C a : MRing (Bk n)) ∈ ptIdeal x ↔ (a : (MP ℤ m n).residueField x) = 0 := by
  rw [ptIdeal, ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal, RingHom.mem_ker, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap,
    MvPolynomial.aeval_C]
  have h : (algebraMap ℤ (MvPolynomial (Fin (m + 1)) ((MP ℤ m n).residueField x)) a) =
      MvPolynomial.C (a : (MP ℤ m n).residueField x) := by
    simp
  rw [h, MvPolynomial.C_eq_zero]

theorem evaluation_generic_injective (Z : Scheme.{0}) [IsIntegral Z] :
    Function.Injective (Z.evaluation ⊤ (genericPoint Z) (Opens.mem_top _)).hom := by
  rw [← Scheme.germ_residue, CommRingCat.hom_comp, RingHom.coe_comp]
  refine Function.Injective.comp ?_ (germ_injective_of_isIntegral Z _ _)
  exact RingHom.injective (Z.residue (genericPoint Z)).hom

theorem dim_closure_image_generic {X Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ X) [IsClosedImmersion j] :
    topologicalKrullDim (closure ({j (genericPoint Z)} : Set X)) = topologicalKrullDim Z := by
  have hg := (genericPoint_spec Z).image (f := j) j.isClosedEmbedding.continuous
  have hcl : closure ({j (genericPoint Z)} : Set X) = Set.range j := by
    have h1 : closure ({j (genericPoint Z)} : Set X) = closure (j '' Set.univ) := hg
    rw [h1, Set.image_univ]
    exact j.isClosedEmbedding.isClosed_range.closure_eq
  rw [hcl]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    j.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

theorem charZero_residueField_iff {Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ MP ℤ m n) :
    CharZero ((MP ℤ m n).residueField (j (genericPoint Z))) ↔ CharZero Γ(Z, ⊤) := by
  constructor
  · intro h
    haveI : CharZero (Z.residueField (genericPoint Z)) :=
      charZero_of_injective_ringHom (f := (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom)
        (RingHom.injective _)
    exact RingHom.charZero (Z.evaluation ⊤ (genericPoint Z) (Opens.mem_top _)).hom
  · intro h
    haveI : CharZero (Z.residueField (genericPoint Z)) :=
      charZero_of_injective_ringHom (evaluation_generic_injective Z)
    exact RingHom.charZero (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom

theorem charOf_prime {P : Ideal (MRing (Bk n))} [P.IsPrime] (h : ¬ IsHorizontal P) : (charOf P).Prime := by
  unfold charOf
  rw [← Int.prime_iff_natAbs_prime]
  exact Submodule.IsPrincipal.prime_generator_of_isPrime _ h

theorem C_charOf_mem (P : Ideal (MRing (Bk n))) : (C ((charOf P : ℕ) : ℤ) : MRing (Bk n)) ∈ P := by
  have hg := Submodule.IsPrincipal.generator_mem (P.comap (C : ℤ →+* MRing (Bk n)))
  obtain ⟨c, hc⟩ := Int.dvd_natAbs.mpr
    (dvd_refl (Submodule.IsPrincipal.generator (P.comap (C : ℤ →+* MRing (Bk n)))))
  have hmem : ((charOf P : ℕ) : ℤ) ∈ P.comap (C : ℤ →+* MRing (Bk n)) := by
    unfold charOf
    rw [hc]
    exact Ideal.mul_mem_right c _ hg
  exact Ideal.mem_comap.mp hmem

theorem charOf_cast_eq_zero {Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ MP ℤ m n) :
    ((charOf (ptIdeal (j (genericPoint Z))) : ℕ) : Γ(Z, ⊤)) = 0 := by
  have h1 := (C_mem_ptIdeal_iff (j (genericPoint Z)) _).mp (C_charOf_mem _)
  have h2 := congrArg (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom h1
  apply evaluation_generic_injective Z
  rw [map_natCast, map_zero]
  simpa using h2

end GlobalTheory.CompanionTheory.MixZ.PtDictProof

namespace GlobalTheory.CompanionTheory.MixZ


open GlobalTheory.CompanionTheory.MixZ.PtDictProof in
theorem ptDict : PtDict := by
  intro m n Z _ j _ d hd
  have hP := isMultiProjPrime_ptIdeal m n (j (genericPoint Z))
  haveI : (ptIdeal (j (genericPoint Z))).IsPrime := hP.1
  have hH : IsHorizontal (ptIdeal (j (genericPoint Z))) ↔ CharZero Γ(Z, ⊤) :=
    (ptIdeal_isHorizontal_iff m n _).trans (charZero_residueField_iff j)
  refine ⟨hP, hH, fun h => ?_, fun h => ⟨charOf_prime h, charOf_cast_eq_zero j⟩⟩
  have hc : CharZero ((MP ℤ m n).residueField (j (genericPoint Z))) :=
    (ptIdeal_isHorizontal_iff m n _).mp h
  have hdim : topologicalKrullDim (closure ({j (genericPoint Z)} : Set (MP ℤ m n))) = (d : ℕ) := by
    rw [dim_closure_image_generic j, hd]
  exact (GlobalTheory.T.closure_dim_iff_arithmetic_variety m n _ d hc).mp hdim

end GlobalTheory.CompanionTheory.MixZ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionaryStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_cycle_point_dictionary : GlobalTheory.CompanionTheory.MixZ.PtDict := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ptDict | exact GlobalTheory.CompanionTheory.MixZ.ptDict | (intros; apply GlobalTheory.CompanionTheory.MixZ.ptDict <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMultiplicityProductZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMultiplicityProductZero
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.CuspNotInd

open GroundTheory.Automorphic.Parabolic (levi parabolicInd)
open GroundTheory.Automorphic.Iwasawa (blockUpper)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unipotentRadical_ne_bot {n : ℕ} {γ : Fin n → ℕ} (hγ : ∃ i j, γ i ≠ γ j) :
    GroundTheory.Automorphic.Parabolic.unipotentRadical k n γ ≠ ⊥ := by
  have h : ∃ i j, γ i < γ j := by
    obtain ⟨i, j, hij⟩ := hγ
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h⟩
    · exact ⟨j, i, h⟩
  obtain ⟨i, j, hij⟩ := h
  have hne : i ≠ j := fun e => hij.ne (congrArg γ e)
  let g : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j 1)
    (by rw [Matrix.det_transvection_of_ne _ _ hne]; exact one_ne_zero)
  have hg : ∀ a b, (g : Matrix (Fin n) (Fin n) k) a b = (1 : Matrix (Fin n) (Fin n) k) a b +
      Matrix.single i j (1 : k) a b := fun a b => rfl
  intro hbot
  have hmem : g ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k n γ := by
    rw [GroundTheory.Automorphic.Parabolic.mem_unipotentRadical, GroundTheory.Automorphic.Iwasawa.mem_blockUpper]
    refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
    · rw [hg, Matrix.one_apply_ne (fun e => hab.ne (by rw [e])), Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      exact absurd hab hij.not_gt
    · rw [hg, Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      exact hij.ne hab
  rw [hbot, Subgroup.mem_bot] at hmem
  have h3 := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) hmem
  simp only [hg, Matrix.one_apply_ne hne, Matrix.single_apply_same, zero_add, Units.val_one] at h3
  exact one_ne_zero h3

theorem isSupercuspidal_of_isCuspidal {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (h : IsCuspidal π) :
    GroundTheory.Automorphic.Parabolic.IsSupercuspidal π := by
  intro γ hγ
  classical
  let s : ℕ := Finset.univ.sup γ + 1
  let r : Fin n → Fin s := fun i => ⟨γ i, Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))⟩
  let d : Fin s → ℕ := fun a => Fintype.card {i // r i = a}
  let e : (Σ a, Fin (d a)) ≃ Fin n :=
    (Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // r i = a}).symm).trans (Equiv.sigmaFiberEquiv r)
  have hblk : ∀ i, GlobalTheory.SmGL.blk e i = r i := fun i => by
    show (e.symm i).1 = r i
    rfl
  have hβ : ∀ i j, γ i < γ j ↔ GlobalTheory.SmGL.blk e i < GlobalTheory.SmGL.blk e j := fun i j => by
    rw [hblk, hblk]; exact Iff.rfl
  have hN : ∀ g, g ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k n γ ↔ g ∈ unipRad k e :=
    GlobalTheory.CompanionTheory.JacquetBridge.mem_unipotentRadical_iff e hβ
  have hne : unipRad k e ≠ ⊥ := fun hb => unipotentRadical_ne_bot (k := k) hγ
    (by rw [eq_bot_iff]; intro g hg; rw [← hb]; exact (hN g).1 hg)
  have htop := Submodule.Quotient.subsingleton_iff.1 (h.2 s d e hne)
  let ρ' := π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k n γ).subtype
  have hle : twKer π (unipRad k e) 1 ≤ LinearMap.ker (Representation.Coinvariants.mk ρ') := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    have : Representation.Coinvariants.mk ρ' (ρ' ⟨u, (hN _).2 u.2⟩ v) = Representation.Coinvariants.mk ρ' v :=
      Representation.Coinvariants.mk_self_apply _ _ _
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, MonoidHom.one_apply, Units.val_one, one_smul]
    exact sub_eq_zero.2 this
  have hz : ∀ y : Representation.Coinvariants ρ', y = 0 := fun y => by
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective ρ' y
    exact hle (htop ▸ Submodule.mem_top)
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

theorem isSubquotient_carry {r : ℕ} {d : Fin r → ℕ} {W V : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V]
    [Module ℂ V] {π : Representation ℂ (GL (Fin (∑ a, d a)) k) V}
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (e : (Σ a, Fin (d a)) ≃ Fin (∑ a, d a))
    (he : e = GlobalTheory.CompanionTheory.BZInd.stdE d) (h : IsSubquotient π (parInd e ρ)) :
    IsSubquotient π (parabolicInd k (∑ a, d a) (GlobalTheory.CompanionTheory.BZInd.pos d) (GlobalTheory.CompanionTheory.BZInd.carry ρ)) := by
  subst he
  exact h.trans (.of_injective _ (GlobalTheory.CompanionTheory.BZInd.toIndMap_injective ρ))

theorem isIrreducible_carry {r : ℕ} {d : Fin r → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (h : ρ.IsIrreducible) :
    (GlobalTheory.CompanionTheory.BZInd.carry ρ).IsIrreducible :=
  isIrreducible_twist (GlobalTheory.LocCompSplit.isIrreducible_comp_of_surjective ρ _ GlobalTheory.CompanionTheory.BZInd.leviTo_surjective h) _

theorem isSmooth_carry {r : ℕ} {d : Fin r → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (h : IsSmooth ρ) :
    IsSmooth (GlobalTheory.CompanionTheory.BZInd.carry ρ) :=
  isSmooth_twist (isSmooth_comp h _ GlobalTheory.CompanionTheory.BZInd.continuous_leviTo) GlobalTheory.CompanionTheory.BZInd.isSmoothChar_adj

theorem exists_pos_ne {r : ℕ} {d : Fin r → ℕ} (h2 : 2 ≤ r) (hd : ∀ a, 0 < d a) :
    ∃ i j, GlobalTheory.CompanionTheory.BZInd.pos d i ≠ GlobalTheory.CompanionTheory.BZInd.pos d j := by
  let a : Fin r := ⟨0, by omega⟩
  let b : Fin r := ⟨1, by omega⟩
  refine ⟨GlobalTheory.CompanionTheory.BZInd.stdE d ⟨a, ⟨0, hd a⟩⟩, GlobalTheory.CompanionTheory.BZInd.stdE d ⟨b, ⟨0, hd b⟩⟩, ?_⟩
  rw [GlobalTheory.CompanionTheory.BZInd.pos_stdE, GlobalTheory.CompanionTheory.BZInd.pos_stdE]
  simp [a, b]

theorem jhMult_eq_zero_of_isCusp : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (ρ : IrrGL (k := k)) {h : ℕ}
    (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = ρ.1), ρ.IsCusp → 2 ≤ h → (∀ a, 0 < (x a).1) →
    jhMult ρ.rep (prodIrr x hd) = 0 := by
  intro k _ _ _ _ hA ρ h x hd hc h2 hpos
  obtain ⟨N, c⟩ := ρ
  dsimp only at hd
  subst hd
  by_contra hne
  have hsub := jhMult_ne_zero_iff.1 hne
  let ρ₀ : IrrGL (k := k) := ⟨_, c⟩
  have hs2 := isSubquotient_carry (d := fun a => (x a).1) (piTensor fun a => (x a).rep) _
    (Equiv.ext fun y => by simp [stdBlocks, GlobalTheory.CompanionTheory.BZInd.stdE]) hsub
  obtain ⟨A, p, hp⟩ := hs2
  haveI : ρ₀.rep.IsIrreducible := ρ₀.2.rep.irr
  haveI := isIrreducible_carry (d := fun a => (x a).1) _ (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA x)
  exact GroundTheory.Automorphic.Parabolic.not_surjective_of_isIrreducible (π := ρ₀.rep) ρ₀.2.rep.smooth
    (isSupercuspidal_of_isCuspidal hc.2) (exists_pos_ne h2 hpos)
    (isSmooth_carry _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)) A p hp

end GlobalTheory.CompanionTheory.CuspNotInd

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMultiplicityProductZeroStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_multiplicity_product_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (ρ : IrrGL (k := k)) {h : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = ρ.1), ρ.IsCusp → 2 ≤ h → (∀ a, 0 < (x a).1) → jhMult ρ.rep (prodIrr x hd) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp | exact GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp | (intros; apply GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveIntertwinerQuotientEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveIntertwinerQuotientEquiv
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.KerQuot

theorem exists_subQuot_top_ker_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
    (R : ρ.IntertwiningMap τ) (hR : Function.Surjective R) :
    ∃ S : Subrepresentation ρ, S.toSubmodule = LinearMap.ker R.toLinearMap ∧
      Nonempty ((subQuot ⊤ S).Equiv τ) := by
  refine ⟨Representation.IntertwiningMap.ker ρ τ R, rfl, ?_⟩
  let T : Subrepresentation ρ := ⊤
  let f : T.toSubmodule →ₗ[ℂ] W := R.toLinearMap ∘ₗ T.toSubmodule.subtype
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨v, rfl⟩ := hR w
    exact ⟨⟨v, by first | exact Submodule.mem_top | trivial | simp [T]⟩, rfl⟩
  have hker : Submodule.comap T.toSubmodule.subtype
      (Representation.IntertwiningMap.ker ρ τ R).toSubmodule = LinearMap.ker f :=
    (LinearMap.ker_comp T.toSubmodule.subtype R.toLinearMap).symm
  let e := (Submodule.quotEquivOfEq _ _ hker).trans (f.quotKerEquivOfSurjective hf)
  refine ⟨⟨⟨e.toLinearMap, fun g => ?_⟩, e.symm, e.left_inv, e.right_inv⟩⟩
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro x
  first
    | exact Representation.IntertwiningMap.isIntertwining ρ τ R g x.1
    | exact R.isIntertwining g x.1
    | simp [e, f, T, GlobalTheory.SmGL.subQuot, Representation.quotient_apply,
        Subrepresentation.toRepresentation, Representation.IntertwiningMap.isIntertwining]

end GlobalTheory.CompanionTheory.BZRes.KerQuot
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveIntertwinerQuotientEquivStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_intertwiner_quotient_equiv : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (τ : Representation ℂ G W) (R : ρ.IntertwiningMap τ), Function.Surjective R → ∃ S : Subrepresentation ρ, S.toSubmodule = LinearMap.ker R.toLinearMap ∧ Nonempty ((subQuot ⊤ S).Equiv τ) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv | exact GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv | (intros; apply GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermHeckeFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermHeckeFormula
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have key : ∀ S : Subgroup H, S = ⊤ → ((S.index : ℂ))⁻¹ * ∑ᶠ _ : H ⧸ S, c = c := by
    rintro S rfl
    haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
    haveI : Unique (H ⧸ (⊤ : Subgroup H)) := Unique.mk' _
    rw [finsum_unique, Subgroup.index_top]
    simp
  exact key _ (by ext k; simp [rStab])

theorem ctT_split_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (ν : (w.adicCompletion E)ˣ →* ℂˣ) (ϖ : w.adicCompletion E), IsSplitAt w → IsUnifV E w ϖ → ∀ (k : ℕ) (m : GLw a w × GLw b w), ctT h w ν ϖ k m = (ν ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) * (absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * hint (intMat a b w) fun X => Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X))) := by
  intro E _ _ _ n a b h w ν ϖ hw hϖ k m
  have hT : UL n w = ⊤ := if_pos hw
  have hv : ∀ y : GLw n w, ((toSub (UL n w) y : UL n w) : GLw n w) = y := fun y => by
    have hy : y ∈ UL n w := hT ▸ Subgroup.mem_top y
    simp [toSub, hy]
  have hc : ∀ (x : GLw n w) (g : GlobalTheory.LFun.KGL w (n := n)),
      Tj ℂ n (Ov E w) ϖ k ((g : GLw n w)⁻¹ * x * g) = Tj ℂ n (Ov E w) ϖ k x := fun x g =>
    (Tj_mem_hecke (n := n) hϖ k).1 g⁻¹ g x
  unfold ctT ctMu ct
  congr 2
  congr 1
  funext X
  simp only [hv, hc]
  exact avg_const (H := GlobalTheory.LFun.KGL w (n := n)) _

end GlobalTheory.CompanionTheory.CtS

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermHeckeFormulaStatement
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_hecke_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (ν : (w.adicCompletion E)ˣ →* ℂˣ) (ϖ : w.adicCompletion E), IsSplitAt w → IsUnifV E w ϖ → ∀ (k : ℕ) (m : GLw a w × GLw b w), ctT h w ν ϖ k m = (ν ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) * (absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * hint (intMat a b w) fun X => Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X))) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.ctT_split_eq | exact GlobalTheory.CompanionTheory.CtS.ctT_split_eq | (intros; apply GlobalTheory.CompanionTheory.CtS.ctT_split_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionContinuousCompactSupport
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionContinuousCompactSupport
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem isCompact_setOf_toL_mem {K : Set (Lie E a)} (hK : IsCompact K) (hs : K ⊆ invSet E a) :
    IsCompact {y : GL (Fin a) (Cinf E) | toL y.val ∈ K} := by
  rw [(GlobalTheory.CuspQuot.isOpenEmbedding_val (E := E) (a := a)).isInducing.isCompact_iff]
  have himg : (Units.val '' {y : GL (Fin a) (Cinf E) | toL y.val ∈ K}) = Matrix.of '' K := by
    ext m
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨toL y.val, hy, by ext i j; rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨u, hu⟩ := hs hx
      refine ⟨u, ?_, hu⟩
      change toL u.val ∈ K
      rw [hu]
      simpa [toL] using hx
  rw [himg]
  exact hK.image (continuous_id : Continuous (fun x : Lie E a => x))

theorem continuous_ker {U : Subgroup (GL (Fin a) (Af E))} (hU : IsOpen (U : Set (GL (Fin a) (Af E))))
    {β : Lie E a → ℂ} (hβ : IsTest β) : Continuous (ker U β) := by
  have hpf := GlobalTheory.CuspRep.ContAut.continuous_map_pFin E a
  have hpi := GlobalTheory.CuspRep.ContAut.continuous_map_pInf E a
  have hclopen : IsClopen {v : GA E a | GeneralLinearGroup.map (pFin E) v ∈ U} :=
    (IsClopen.preimage ⟨U.isClosed_of_isOpen hU, hU⟩ hpf)
  have hval : Continuous fun v : GA E a => β (toL (GeneralLinearGroup.map (pInf E) v).val) :=
    hβ.contDiff.continuous.comp ((Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp hpi)
  classical
  unfold ker
  refine Continuous.if (fun v hv => ?_) hval continuous_const
  rw [hclopen.frontier_eq] at hv
  exact absurd hv (Set.notMem_empty _)

theorem hasCompactSupport_ker {U : Subgroup (GL (Fin a) (Af E))}
    (hUc : IsCompact (U : Set (GL (Fin a) (Af E)))) {β : Lie E a → ℂ} (hβ : IsTest β) :
    HasCompactSupport (ker U β) := by
  have hT := isCompact_setOf_toL_mem (E := E) (a := a) hβ.compact hβ.support
  haveI : R1Space (GA E a) := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact inferInstance
  refine HasCompactSupport.intro (K := (fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) =>
      infGL E a p.1 * finGL E a p.2) '' ({y : GL (Fin a) (Cinf E) | toL y.val ∈ tsupport β} ×ˢ
        (U : Set (GL (Fin a) (Af E)))))
    ((hT.prod hUc).image ((GlobalTheory.CuspQuot.continuous_infGL.comp continuous_fst).mul
      ((GlobalTheory.BlockLevel.continuous_finGL a).comp continuous_snd))) fun g hg => ?_
  by_contra h0
  unfold ker at h0
  split_ifs at h0 with hu
  · exact hg ⟨(_, _), ⟨subset_tsupport _ h0, hu⟩, infGL_mul_finGL g⟩
  · exact h0 rfl

theorem continuous_hasCompactSupport_tst : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ β : Lie E a → ℂ, IsTest β →
    Continuous (tst U β) ∧ HasCompactSupport (tst U β) := by
  intro E _ _ _ a U hU hUc β hβ
  exact ⟨(continuous_ker hU hβ).comp continuous_inv,
    (hasCompactSupport_ker hUc hβ).comp_homeomorph (Homeomorph.inv (GA E a))⟩

end GlobalTheory.CompanionTheory.SmoothRep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionContinuousCompactSupportStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_function_continuous_compact_support : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ β : Lie E a → ℂ, IsTest β → Continuous (tst U β) ∧ HasCompactSupport (tst U β) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.continuous_hasCompactSupport_tst | exact GlobalTheory.CompanionTheory.SmoothRep.continuous_hasCompactSupport_tst | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.continuous_hasCompactSupport_tst <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueRingStructure
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueRingStructure
noncomputable section

namespace GlobalTheory.CompanionTheory.RvRingPf

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem repr_one_tmul {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) bs).repr ((1 : Fv F v) ⊗ₜ[F] e) k =
      algebraMap F (Fv F v) (bs.repr e k) := by
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem struct_int {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (i j k : Fin d) :
    algebraMap F (Fv F v) (bs.repr (bs i * bs j) k) ∈ v.adicCompletionIntegers F := by
  refine h _ ?_
  classical
  unfold basisSet
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
  exact Finset.mem_image.2 ⟨(i, j, k), Finset.mem_univ _, rfl⟩

theorem one_int {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (k : Fin d) :
    algebraMap F (Fv F v) (bs.repr 1 k) ∈ v.adicCompletionIntegers F := by
  refine h _ ?_
  classical
  unfold basisSet
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
  exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩

theorem sig_int {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (i k : Fin d) :
    algebraMap F (Fv F v) (bs.repr (σ (bs i)) k) ∈ v.adicCompletionIntegers F := by
  refine h _ ?_
  classical
  unfold basisSet
  refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
  exact Finset.mem_image.2 ⟨(i, k), Finset.mem_univ _, rfl⟩

theorem repr_mul {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (x y : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) bs).repr (x * y) k =
      ∑ i, ∑ j, ((Algebra.TensorProduct.basis (Fv F v) bs).repr x i *
        (Algebra.TensorProduct.basis (Fv F v) bs).repr y j) *
          algebraMap F (Fv F v) (bs.repr (bs i * bs j) k) := by
  set bK := Algebra.TensorProduct.basis (Fv F v) bs with hbK
  have e : x * y = ∑ i, ∑ j, (bK.repr x i * bK.repr y j) • ((1 : Fv F v) ⊗ₜ[F] (bs i * bs j)) := by
    conv_lhs => rw [← bK.sum_repr x, ← bK.sum_repr y]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, hbK, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← bK.coord_apply, e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, bK.coord_apply, hbK, repr_one_tmul, smul_eq_mul]

theorem repr_sig (σ : E →ₐ[F] E) {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (x : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) bs).repr (sigR (Fv F v) σ x) k =
      ∑ i, (Algebra.TensorProduct.basis (Fv F v) bs).repr x i *
        algebraMap F (Fv F v) (bs.repr (σ (bs i)) k) := by
  set bK := Algebra.TensorProduct.basis (Fv F v) bs with hbK
  have e : sigR (Fv F v) σ x = ∑ i, bK.repr x i • ((1 : Fv F v) ⊗ₜ[F] σ (bs i)) := by
    conv_lhs => rw [← bK.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbK, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp [sigR]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← bK.coord_apply, e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, bK.coord_apply, hbK, repr_one_tmul, smul_eq_mul]

def ringOf {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) : Subring (Fv F v ⊗[F] E) where
  carrier := Rv bs v
  mul_mem' := by
    intro x y hx hy k
    rw [repr_mul]
    exact sum_mem fun i _ => sum_mem fun j _ => mul_mem (mul_mem (hx i) (hy j)) (struct_int h i j k)
  one_mem' := by
    intro k
    rw [Algebra.TensorProduct.one_def, repr_one_tmul]
    exact one_int h k
  add_mem' := by
    intro x y hx hy k
    rw [map_add (f := _), Finsupp.add_apply]
    exact add_mem (hx k) (hy k)
  zero_mem' := by
    intro k
    rw [map_zero, Finsupp.zero_apply]
    exact zero_mem _
  neg_mem' := by
    intro x hx k
    rw [map_neg, Finsupp.neg_apply]
    exact neg_mem (hx k)

theorem sigR_mem {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (x : Fv F v ⊗[F] E) (hx : x ∈ ringOf h) :
    sigR (Fv F v) σ x ∈ ringOf h := by
  intro k
  rw [repr_sig]
  exact sum_mem fun i _ => mul_mem (hx i) (sig_int h i k)

theorem rvRing : PositivityTheory.SiegelWeilFormula.Gunr.RvRing := by
  intro F E _ _ _ _ _ σ d bs v h
  exact ⟨ringOf h, (sigR (Fv F v) σ).restrict (ringOf h) (ringOf h) (sigR_mem h), rfl, fun x => rfl⟩

end GlobalTheory.CompanionTheory.RvRingPf

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueRingStructureStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_ring_structure : PositivityTheory.SiegelWeilFormula.Gunr.RvRing := by
  first | exact @GlobalTheory.CompanionTheory.RvRingPf.rvRing | exact GlobalTheory.CompanionTheory.RvRingPf.rvRing | (intros; apply GlobalTheory.CompanionTheory.RvRingPf.rvRing <;> assumption)
end
end
