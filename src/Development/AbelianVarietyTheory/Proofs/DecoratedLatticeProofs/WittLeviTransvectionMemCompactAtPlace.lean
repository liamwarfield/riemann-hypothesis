module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedZetaSumGLCosets
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsKActOfStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSmulIntegralMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarOfComm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinPartOneMulInvMemHeckeSplitCongruence
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemClosureHeckeSplitCongruenceOfFinPartOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlace
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RootKeep

open GlobalTheory.IwaPlace

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem conj_mem_idAt {v : Pl D} {r : AE D} (hr : r ∈ idAt D (· = v)) : cA D r ∈ idAt D (· = v) := by
  obtain ⟨ε, hc, hε, hact⟩ := LocSD.exists_idem v
  rw [← hact r hr, RingHom.map_mul, hc]
  exact Ideal.mul_mem_right _ _ hε.1

theorem colMul_add {m n : ℕ} (x : Mx D m n) (l : Fin n) (a b : AE D) :
    colMul x l (a + b) = colMul x l a + colMul x l b := by
  funext k; exact add_mul _ _ _

theorem colMul_neg {m n : ℕ} (x : Mx D m n) (l : Fin n) (a : AE D) : colMul x l (-a) = -colMul x l a := by
  funext k; exact neg_mul _ _

theorem hermAt_colMul_jY (d : HypDec S S₀ ρ) (l : Fin ρ) (b : AE D) (x : Fin S.rank → AE D) :
    hermAt S (colMul d.jY l b) x = b * cA D ((d.pX *ᵥ x) l) := by
  have hg : ∀ k m, cA D (gA S k m) = gA S m k := fun k m => congrFun (congrFun (adj_gA S) m) k
  have hp : ∀ m, cA D (d.pX l m) = ∑ k, gA S m k * d.jY k l := fun m => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [d.pX_eq, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RingHom.map_mul, hg, mul_comm]
    exact congrArg _ (congrFun (congrFun (adj_adj d.jY) k) l)
  unfold hermAt colMul
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mulVec, dotProduct, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [RingHom.map_mul, hp, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem pX_colMul_jX (d : HypDec S S₀ ρ) (l : Fin ρ) (a : AE D) : (d.pX *ᵥ colMul d.jX l a) l = a := by
  have h : (d.pX * d.jX) l l = 1 := by rw [d.pX_jX, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h
  refine Eq.trans ?_ (mul_one a)
  rw [Matrix.mulVec, dotProduct, ← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold colMul
  ring

theorem transv_mulVec (i j : Fin ρ) (r : AE D) (u : Fin ρ → AE D) (l : Fin ρ) :
    (transvection i j r *ᵥ u) l = u l + if l = i then r * u j else 0 := by
  rw [transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, Pi.add_apply, Function.update_apply]
  rfl

theorem adj_transv (i j : Fin ρ) (r : AE D) : adj (transvection i j r : Mx D ρ ρ) = transvection j i (cA D r) := by
  rw [transvection, transvection, adj_add, adj_one]
  congr 1
  funext a b
  change cA D (Matrix.single i j r b a) = _
  simp only [Matrix.single_apply]
  by_cases h : i = b ∧ j = a
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm), RingHom.map_zero]

theorem levi_maps (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {v : Pl D} (hL : IsSelfDualC S L)
    (hM : MonoAt d L L₀ v) {i j : Fin ρ} (hij : i ≠ j) {r : AE D}
    (h : ∀ a ∈ idAt D (· = v), colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * a) ∈ latV S L (· = v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) :
    mt S (d.levi (GlobalTheory.GLGen.transvGL hij r)) *ᵥ y ∈ latV S L (· = v) := by
  obtain ⟨hs, -, hd⟩ := LocSD.isSDAt_latV D S L v hL
  have hX : ∀ x ∈ latV S L (· = v), colMul d.jX i (r * (d.pX *ᵥ x) j) ∈ latV S L (· = v) := fun x hx =>
    h _ (mulVec_mem_idAt _ (hs x hx) j) (((hM x).1 hx).1 j)
  obtain ⟨h1, h2, h3⟩ := (hM y).1 hy
  refine (hM _).2 ⟨fun l => ?_, fun l => ?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, d.pX_levi, ← Matrix.mulVec_mulVec]
    change colMul d.jX l ((transvection i j r *ᵥ _) l) ∈ _
    rw [transv_mulVec, colMul_add]
    refine add_mem (h1 l) ?_
    split_ifs with hl
    · rw [hl]; exact hX y hy
    · have : colMul d.jX l 0 = 0 := funext fun k => zero_mul _
      rw [this]; exact zero_mem _
  · rw [Matrix.mulVec_mulVec, d.pY_levi, ← Matrix.mulVec_mulVec]
    change colMul d.jY l ((adj (transvection i j (-r) : Mx D ρ ρ) *ᵥ _) l) ∈ _
    rw [adj_transv, transv_mulVec, colMul_add]
    refine add_mem (h2 l) ?_
    split_ifs with hl
    · rw [hl, RingHom.map_neg, neg_mul, colMul_neg]
      refine neg_mem ((hd _ fun k => ?_).2 fun x hx => ?_)
      · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (mulVec_mem_idAt _ (hs y hy) i))
      · have h4 := (hd _ (hs _ (h2 i))).1 (h2 i) _ (hX x hx)
        rw [hermAt_colMul_jY, pX_colMul_jX, RingHom.map_mul] at h4
        rw [hermAt_colMul_jY]
        convert h4 using 1
        ring
    · have : colMul d.jY l 0 = 0 := funext fun k => zero_mul _
      rw [this]; exact zero_mem _
  · rwa [Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_levi]

theorem levi_mem_grpAt (d : HypDec S S₀ ρ) {v : Pl D} {i j : Fin ρ} (hij : i ≠ j) {r : AE D}
    (hr : r ∈ idAt D (· = v)) : d.levi (GlobalTheory.GLGen.transvGL hij r) ∈ grpAt S (· = v) := by
  refine (mem_congGrp_iff S _ _).2 fun a b => ?_
  have e : mt S (d.levi (GlobalTheory.GLGen.transvGL hij r)) - 1 =
      d.jX * (Matrix.single i j r : Mx D ρ ρ) * d.pX + d.jY * (Matrix.single j i (cA D (-r)) : Mx D ρ ρ) * d.pY := by
    rw [d.mt_levi, ← d.sum_eq_one]
    change d.jX * (transvection i j r : Mx D ρ ρ) * d.pX + _ + d.jY * adj (transvection i j (-r) : Mx D ρ ρ) * d.pY - _ = _
    rw [adj_transv, transvection, transvection]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
    abel
  have k : ∀ (A : Mx D S.rank ρ) (B : Mx D ρ S.rank) (p q : Fin ρ) (s : AE D), s ∈ idAt D (· = v) →
      (A * (Matrix.single p q s : Mx D ρ ρ) * B) a b ∈ idAt D (· = v) := fun A B p q s hs => by
    rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ ?_
    rw [Matrix.single_apply]
    split_ifs
    · exact hs
    · exact zero_mem _
  rw [← Matrix.sub_apply, e, Matrix.add_apply]
  exact add_mem (k _ _ _ _ _ hr) (k _ _ _ _ _ (conj_mem_idAt (neg_mem hr)))

theorem inK_levi_transv : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), IsSelfDualC S L → MonoAt d L L₀ v → ∀ (i j : Fin ρ) (hij : i ≠ j) (r : AE D), r ∈ idAt D (· = v) → (∀ a ∈ idAt D (· = v), colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * a) ∈ latV S L (· = v)) → InK S L (· = v) (d.levi (GlobalTheory.GLGen.transvGL hij r)) := by
  intro D S S₀ ρ d L L₀ v hL hM i j hij r hr h
  refine ⟨levi_mem_grpAt d hij hr, fun y _ => ⟨fun hy => levi_maps d hL hM hij h hy, fun hy => ?_⟩⟩
  have h' := levi_maps d hL hM hij (r := -r) (fun a ha hb => by
    rw [neg_mul, colMul_neg]; exact neg_mem (h a ha hb)) hy
  have e : GlobalTheory.GLGen.transvGL hij (-r) = (GlobalTheory.GLGen.transvGL hij r)⁻¹ := Units.ext rfl
  rwa [Matrix.mulVec_mulVec, ← mt_mul, ← map_mul, e, inv_mul_cancel, map_one, mt_one, Matrix.one_mulVec] at h'

end GlobalTheory.FinPl.RootKeep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlaceStatement
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittLeviTransvection_mem_compactAtPlace : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), IsSelfDualC S L → MonoAt d L L₀ v → ∀ (i j : Fin ρ) (hij : i ≠ j) (r : AE D), r ∈ idAt D (· = v) → (∀ a ∈ idAt D (· = v), colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * a) ∈ latV S L (· = v)) → InK S L (· = v) (d.levi (GlobalTheory.GLGen.transvGL hij r)) := by
  first | exact @GlobalTheory.FinPl.RootKeep.inK_levi_transv | exact GlobalTheory.FinPl.RootKeep.inK_levi_transv | (intros; apply GlobalTheory.FinPl.RootKeep.inK_levi_transv <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZetaSumGLComplex
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.ZetaGL

theorem zeta_sum_GL_complex : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (s : ℂ), (r : ℝ) / 2 < s.re → ∀ (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), ‖(z : ℂ)‖ = 1 → (∀ ϖ, IsUnifV E w ϖ → ∀ (d : Fin r → ℤ) (t : GL (Fin r) (w.adicCompletion E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := r), ∀ k₂ ∈ KGL w (n := r), φ (k₁ * t * k₂) = (z : ℂ) ^ (∑ i, d i) * (qV E w : ℂ) ^ (-((r : ℂ) / 2 + s) * ((∑ i, |d i| : ℤ) : ℂ))) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), IsSatVecGL w ρ x B → ∀ ℓ : V →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) → (ℓ x ≠ 0 → ∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ ((r : ℝ) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ ((r : ℝ) / 2)) → HasSum (fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) => φ a.out * ℓ (ρ a.out x)) (eulerFac (B.map (z * ·)) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) * eulerFac (B.map fun β => (z * β)⁻¹) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) * (∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ (-(2 * s + r - i)))) * ℓ x) := by
  intro H E _ _ w r s hs z φ hz hφ V _ _ ρ x B hx ℓ hℓ hB
  obtain ⟨Cℓ, hC⟩ := hℓ
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  have h0 : ϖ ≠ 0 := GlobalTheory.LFun.SatCompare.ne_zero_of_isUnifV hϖ
  let T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E) := fun d => GlobalTheory.WeylGL.tor h0 d
  have hTv : ∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i := fun d => rfl
  have hK : Formalism.UG.IsCommensurated (KGL w (n := r)) := Formalism.UG.Final.GLintComm E w r
  have hmem : ∀ g, Formalism.UG.dosetInd ℂ (KGL w (n := r)) g ∈ Hecke ℂ (KGL w (n := r)) := fun g => Formalism.UG.Final.DosetIndMem _ _ ℂ g
  choose c hc using fun d => GlobalTheory.LFun.SatCompare.exists_eigenvalue_GL hx hx _ (hmem (T d))
  let S : (Fin r → ℤ) → Set (GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r)) := fun d =>
    {a | a.out ∈ DoubleCoset.doubleCoset (T d) (KGL w (n := r) : Set (GL (Fin r) (w.adicCompletion E))) (KGL w (n := r))}
  have hSfin : ∀ d, (S d).Finite := fun d =>
    (Formalism.UG.P.finite_support_cosets hK (hmem (T d)).2).subset fun a ha => by
      simp only [Set.mem_setOf_eq, Formalism.UG.dosetInd]; rw [Set.indicator_of_mem (s := DoubleCoset.doubleCoset _ _ _) ha]; exact one_ne_zero
  have hsumS : ∀ d, ∑ᶠ a ∈ S d, ρ a.out x = c d • x := fun d => by
    rw [← (hc d).1, GlobalTheory.LFun.heckeVec, finsum_mem_def]
    refine finsum_congr fun a => ?_
    by_cases ha : a ∈ S d
    · rw [Set.indicator_of_mem ha, Formalism.UG.dosetInd, Set.indicator_of_mem (s := DoubleCoset.doubleCoset _ _ _) ha]; simp
    · rw [Set.indicator_of_notMem ha, Formalism.UG.dosetInd, Set.indicator_of_notMem (s := DoubleCoset.doubleCoset _ _ _) ha]; simp
  have hU := fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) => GlobalTheory.ZetaGL.cartan_existsUnique E w r hϖ T hTv a.out
  choose D hD using fun a => (hU a).exists
  have hDu : ∀ (d : {d : Fin r → ℤ // Antitone d}) (a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r)), a ∈ S d.1 → D a = d :=
    fun d a ha => (hU a).unique (hD a) ha
  let e : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) ≃ Σ d : {d : Fin r → ℤ // Antitone d}, S d.1 :=
    { toFun := fun a => ⟨D a, a, hD a⟩
      invFun := fun p => p.2.1
      left_inv := fun a => rfl
      right_inv := fun ⟨d, a, ha⟩ => by
        have h1 : D a = d := hDu d a ha
        subst h1
        rfl }
  haveI : ∀ d, Fintype (S d) := fun d => (hSfin d).fintype
  have hsumF : ∀ d, ∑ a : S d, ρ (a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r)).out x = c d • x := fun d => by
    rw [← hsumS d, ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  set q : ℝ := (qV E w : ℝ) with hqdef
  have hq1 : (1 : ℝ) < q := by
    show (1 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ); exact_mod_cast GlobalTheory.LFun.one_lt_absNorm w
  have hq0 : (0 : ℝ) < q := by linarith
  have hqC : (qV E w : ℂ) ≠ 0 := by exact_mod_cast GlobalTheory.LFun.qV_ne_zero w
  set M : ℝ := q ^ ((r : ℝ) / 2) with hM
  set M₁ : ℝ := q ^ (((r : ℝ) - 1) / 2) with hM₁
  set ρ₀ : ℝ := q ^ (-((r : ℝ) - 1 / 2)) with hρ₀
  have hM0 : 0 < M := Real.rpow_pos_of_pos hq0 _
  have hM₁0 : 0 < M₁ := Real.rpow_pos_of_pos hq0 _
  have hM₁M : M₁ ≤ M := Real.rpow_le_rpow_of_exponent_le hq1.le (by linarith)
  have hMM : M * M₁ * ρ₀ = 1 := by
    rw [hM, hM₁, hρ₀, ← Real.rpow_add hq0, ← Real.rpow_add hq0,
      show (r : ℝ) / 2 + ((r : ℝ) - 1) / 2 + -((r : ℝ) - 1 / 2) = 0 by ring, Real.rpow_zero]
  set cq : ℂ := (qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) with hcq
  have hcqn : ‖cq‖ = M₁ := by
    rw [hcq, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero w))]
    congr 1; simp
  have hsmall : ∀ β : ℂ, ‖β‖ ≤ M → ∀ X : ℂ, ‖X‖ < ρ₀ → ‖β * (cq * X)‖ < 1 := fun β hβ X hX => by
    rw [norm_mul, norm_mul, hcqn]
    calc ‖β‖ * (M₁ * ‖X‖) ≤ M * (M₁ * ‖X‖) := mul_le_mul_of_nonneg_right hβ (by positivity)
      _ < M * (M₁ * ρ₀) := by gcongr
      _ = 1 := by rw [← mul_assoc, hMM]
  set X₀ : ℂ := (qV E w : ℂ) ^ (-((r : ℂ) / 2 + s)) with hX₀
  have hX₀n : ‖X₀‖ = q ^ (-((r : ℝ) / 2 + s.re)) := by
    rw [hX₀, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero w))]
    congr 1; simp
  have hX₀ρ : ‖X₀‖ < ρ₀ := by
    rw [hX₀n]; exact Real.rpow_lt_rpow_of_exponent_lt hq1 (by linarith)
  let deg : {d : Fin r → ℤ // Antitone d} → ℕ := fun d => (∑ i, |d.1 i|).toNat
  have hdeg : ∀ k, {d | deg d = k}.Finite := fun k => by
    have hfin : (Set.pi Set.univ fun _ : Fin r => Set.Icc (-(k : ℤ)) k).Finite :=
      Set.Finite.pi fun _ => Set.finite_Icc _ _
    refine (hfin.preimage Subtype.val_injective.injOn).subset fun d hd => ?_
    simp only [Set.mem_setOf_eq, deg] at hd
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
    intro i
    have h1 : |d.1 i| ≤ ∑ j, |d.1 j| := Finset.single_le_sum (fun j _ => abs_nonneg (d.1 j)) (Finset.mem_univ i)
    have h2 : ∑ j, |d.1 j| = k := by rw [← hd, Int.toNat_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)]
    constructor
    · linarith [neg_abs_le (d.1 i)]
    · linarith [le_abs_self (d.1 i)]
  obtain ⟨δ₁, hδ₁, hs₁⟩ := GlobalTheory.T.satake_vector_hecke_eigenvalue H E w r V ρ x B hx z ϖ hϖ T hTv c (fun d => (hc d).1)
  obtain ⟨B₀, hB₀, δ₂, hδ₂, hs₂⟩ := GlobalTheory.T.hasSum_card_cosets_diagonalDoubleCoset_GL H E w r ϖ hϖ T hTv
  let a : {d : Fin r → ℤ // Antitone d} → ℂ := fun d => (z : ℂ) ^ (∑ i, d.1 i) * c d.1 * ℓ x
  let b : {d : Fin r → ℤ // Antitone d} → ℝ := fun d => (Nat.card (S d.1) : ℝ)
  let P : ℂ → ℂ := fun X => eulerFac (B.map (z * ·)) (cq * X) * eulerFac (B.map fun β => (z * β)⁻¹) (cq * X) *
    (∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * X ^ 2)) * ℓ x
  let P' : ℂ → ℂ := fun X => eulerFac B₀ (cq * X) * eulerFac (B₀.map (·⁻¹)) (cq * X) *
    ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * X ^ 2)
  have hC0 : 0 ≤ Cℓ := (norm_nonneg _).trans (hC 1)
  have hab : ∀ d, ‖a d‖ ≤ Cℓ * b d := fun d => by
    have e1 : c d.1 * ℓ x = ∑ y : S d.1, ℓ (ρ (y : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r)).out x) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, hsumF, map_smul, smul_eq_mul]
    have hz' : ‖(z : ℂ) ^ (∑ i, d.1 i)‖ = 1 := by rw [norm_zpow, hz, _root_.one_zpow]
    simp only [a, b]
    rw [mul_assoc, norm_mul, hz', one_mul, e1]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun y _ => hC _).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card, mul_comm]
  have hbnd₀ : ∀ β ∈ B₀, ‖(β : ℂ)‖ ≤ M := fun β hβ => (hB₀ β hβ).1.trans hM₁M
  have hbnd₀' : ∀ β ∈ B₀.map (·⁻¹), ‖(β : ℂ)‖ ≤ M := by
    intro β hβ
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hβ
    exact (hB₀ b hb).2.trans hM₁M
  have hpoly : Differentiable ℂ fun X : ℂ => ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * X ^ 2) := by fun_prop
  have hE3 := GlobalTheory.ZetaGL.differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd₀ β hβ) X hX
  have hE4 := GlobalTheory.ZetaGL.differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd₀' β hβ) X hX
  have hP : DifferentiableOn ℂ P (Metric.ball 0 ρ₀) := by
    by_cases hl : ℓ x = 0
    · have hP0 : P = fun _ => 0 := funext fun X => by simp only [P, hl, mul_zero]
      rw [hP0]; exact differentiableOn_const 0
    · have hbnd : ∀ β ∈ B.map (z * ·), ‖(β : ℂ)‖ ≤ M := by
        intro β hβ
        obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hβ
        simpa [norm_mul, hz] using (hB hl b hb).1
      have hbnd' : ∀ β ∈ B.map fun β => (z * β)⁻¹, ‖(β : ℂ)‖ ≤ M := by
        intro β hβ
        obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hβ
        simpa [norm_mul, hz, Units.val_inv_eq_inv_val] using (hB hl b hb).2
      have hE1 := GlobalTheory.ZetaGL.differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd β hβ) X hX
      have hE2 := GlobalTheory.ZetaGL.differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd' β hβ) X hX
      exact (((hE1.mul hE2).mul hpoly.differentiableOn).mul_const (ℓ x)).congr fun X _ => by simp only [P, Pi.mul_apply]
  have hP' : DifferentiableOn ℂ P' (Metric.ball 0 ρ₀) :=
    ((hE3.mul hE4).mul hpoly.differentiableOn).congr fun X _ => rfl
  have hser : ∀ X : ℝ, 0 < X → X < min δ₁ δ₂ → HasSum (fun d => a d * (X : ℂ) ^ deg d) (P X) ∧
      HasSum (fun d => (b d : ℂ) * (X : ℂ) ^ deg d) (P' X) := fun X hX h =>
    ⟨by
      have h1 := (hs₁ X hX (lt_of_lt_of_le h (min_le_left _ _))).mul_right (ℓ x)
      rw [show (fun d => a d * (X : ℂ) ^ deg d) = fun d : {d : Fin r → ℤ // Antitone d} =>
        (z : ℂ) ^ (∑ i, d.1 i) * c d.1 * (X : ℂ) ^ (∑ i, |d.1 i|).toNat * ℓ x from funext fun d => by
          simp only [a, deg]; ring]
      exact h1,
    hs₂ X hX (lt_of_lt_of_le h (min_le_right _ _))⟩
  obtain ⟨hA, hBs⟩ := GlobalTheory.T.hasSum_and_summable_on_ball_of_hasSum_on_interval deg hdeg a b Cℓ (min δ₁ δ₂) ρ₀ P P' (lt_min hδ₁ hδ₂) (fun d => Nat.cast_nonneg _)
    hab hP hP' hser X₀ hX₀ρ
  have hφv : ∀ a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r),
      φ a.out = (z : ℂ) ^ (∑ i, (D a).1 i) * X₀ ^ deg (D a) := fun a => by
    obtain ⟨k₁, hk₁, k₂, hk₂, e1⟩ := DoubleCoset.mem_doubleCoset.1 (hD a)
    rw [e1, hφ ϖ hϖ (D a).1 (T (D a).1) (hTv _) k₁ hk₁ k₂ hk₂]
    congr 1
    have hn : ((∑ i, |(D a).1 i| : ℤ) : ℂ) = ((deg (D a) : ℕ) : ℂ) := by
      simp only [deg]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)]
    rw [hn, hX₀, ← Complex.cpow_nat_mul, mul_comm]
  let f : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) → ℂ := fun a => φ a.out * ℓ (ρ a.out x)
  let u : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) → ℝ := fun a => Cℓ * ‖X₀‖ ^ deg (D a)
  have hfu : ∀ a, ‖f a‖ ≤ u a := fun a => by
    simp only [f, u]
    rw [hφv, norm_mul, norm_mul, norm_zpow, hz, _root_.one_zpow, one_mul, norm_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (pow_nonneg (norm_nonneg _) _)
  have hu : Summable u := by
    rw [← e.symm.summable_iff]
    refine (summable_sigma_of_nonneg fun p => mul_nonneg hC0 (pow_nonneg (norm_nonneg _) _)).2
      ⟨fun d => Summable.of_finite, ?_⟩
    have h1 : ∀ d : {d : Fin r → ℤ // Antitone d},
        Cℓ * (b d * ‖X₀‖ ^ deg d) = ∑' y : S d.1, (u ∘ e.symm) ⟨d, y⟩ := fun d => by
      have h2 : ∀ y : S d.1, (u ∘ e.symm) ⟨d, y⟩ = Cℓ * ‖X₀‖ ^ deg d := fun y => by
        show Cℓ * ‖X₀‖ ^ deg (D y.1) = _
        rw [hDu d y.1 y.2]
      simp_rw [h2]
      rw [tsum_const, nsmul_eq_mul]
      simp only [b]
      ring
    exact (hBs.mul_left Cℓ).congr h1
  have hf : Summable f := Summable.of_norm_bounded hu hfu
  have hfib : ∀ d : {d : Fin r → ℤ // Antitone d},
      HasSum (fun y : S d.1 => (f ∘ e.symm) ⟨d, y⟩) (a d * X₀ ^ deg d) := fun d => by
    have h2 : ∀ y : S d.1, (f ∘ e.symm) ⟨d, y⟩ =
        (z : ℂ) ^ (∑ i, d.1 i) * X₀ ^ deg d * ℓ (ρ (y : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r)).out x) :=
      fun y => by
        show φ (y : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r)).out * _ = _
        rw [hφv, hDu d y.1 y.2]
        rfl
    have h3 : ∑ y : S d.1, (f ∘ e.symm) ⟨d, y⟩ = a d * X₀ ^ deg d := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_congr rfl fun y _ => h2 y, ← Finset.mul_sum, ← map_sum, hsumF, map_smul, smul_eq_mul]
      simp only [a]
      ring
    exact h3 ▸ hasSum_fintype _
  have heq : ∑' a, f a = P X₀ := (((e.symm.hasSum_iff).2 hf.hasSum).sigma hfib).unique hA
  have hfin := hf.hasSum
  rw [heq] at hfin
  have hcX : cq * X₀ = GlobalTheory.LFun.npow w (-(s + 1 / 2)) := by
    rw [hcq, hX₀, ← Complex.cpow_add _ _ hqC]
    show ((qV E w : ℕ) : ℂ) ^ _ = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ _
    congr 1
    ring
  have hprod : ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * X₀ ^ 2) =
      ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ (-(2 * s + r - i))) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hX₀, ← Complex.cpow_nat_mul, ← Complex.cpow_natCast (qV E w : ℂ) i, ← Complex.cpow_add _ _ hqC]
    congr 2
    push_cast
    ring
  have hval : P X₀ = eulerFac (B.map (z * ·)) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) *
      eulerFac (B.map fun β => (z * β)⁻¹) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) *
      (∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ (-(2 * s + r - i)))) * ℓ x := by
    simp only [P]
    rw [hcX, hprod]
  rw [hval] at hfin
  exact hfin

end GlobalTheory.ZetaGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteVectorsDiscreteSeriesSmoothAbsolutelyIrre
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteVectorsDiscreteSeriesSmoothAbsolutelyIrre
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFinLoc

open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension

theorem kFin_rank_zero {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (h0 : V.rank = 0) :
    kFin M τ ≤ M.sm τ ∧ ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ),
      GlobalTheory.Chain.IoLift.IsKAct M τ a ∧ GlobalTheory.Chain.IoLift.AbsIrr (fun X : lieAt V τ => a X) := by
  have hsub : ∀ g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ, g = g' := fun g g' =>
    Matrix.ext fun i _ => absurd i.2 (by omega)
  have hσ1 : M.σ τ 1 = 1 := (M.ds τ).2.2.1.1.1
  have hσ : ∀ g, M.σ τ g = 1 := fun g => by rw [hsub g 1, hσ1]
  have hrep : ∀ g, M.rep τ g = 1 := fun g => hσ _
  refine ⟨fun x _ => Submodule.subset_span ?_, fun _ => 0, ⟨fun X _ v => ?_, fun X _ v w => by simp⟩, ?_⟩
  · intro k Xs _
    simp only [hrep, ContinuousLinearMap.one_apply]
    exact contDiff_const
  · simp only [hrep, ContinuousLinearMap.one_apply, LinearMap.zero_apply, Submodule.coe_zero]
    exact hasDerivAt_const _ _
  · haveI : CompleteSpace (M.H τ) := (M.ds τ).1

    have hline : ∀ x y : M.H τ, x ≠ 0 → ∃ c : ℂ, c • x = y := fun x y hx => by
      have hcl : IsClosed ((ℂ ∙ x : Submodule ℂ (M.H τ)) : Set (M.H τ)) := Submodule.closed_of_finiteDimensional _
      rcases (M.ds τ).2.2.2.1 _ hcl (fun g _ v hv => by rwa [hσ, ContinuousLinearMap.one_apply]) with hb | ht
      · exact absurd ((Submodule.span_singleton_eq_bot).1 hb) hx
      · exact Submodule.mem_span_singleton.1 (ht ▸ Submodule.mem_top)
    have hK : ∀ x y : kFin M τ, x ≠ 0 → ∃ c : ℂ, c • x = y := fun x y hx => by
      obtain ⟨c, hc⟩ := hline x y (fun e => hx (Subtype.ext e))
      exact ⟨c, Subtype.ext hc⟩
    refine ⟨fun N _ => ?_, fun T _ => ?_⟩
    · by_cases hN : N = ⊥
      · exact Or.inl hN
      · right
        obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
        refine eq_top_iff.2 fun y _ => ?_
        obtain ⟨c, rfl⟩ := hK x y hx0
        exact N.smul_mem c hxN
    · by_cases hz : ∀ x : kFin M τ, x = 0
      · exact ⟨0, LinearMap.ext fun x => by rw [hz x]; simp⟩
      · push_neg at hz
        obtain ⟨x, hx0⟩ := hz
        obtain ⟨c, hc⟩ := hK x (T x) hx0
        refine ⟨c, LinearMap.ext fun y => ?_⟩
        obtain ⟨d, rfl⟩ := hK x y hx0
        rw [map_smul, ← hc, LinearMap.smul_apply, LinearMap.id_apply, smul_comm]

theorem kFin_smooth_absIrr (hH : GlobalTheory.Published.HarishChandraModules) (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : DSModel V S) (τ : D.what₂.Tau) :
    kFin M τ ≤ M.sm τ ∧ ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ),
      GlobalTheory.Chain.IoLift.IsKAct M τ a ∧ GlobalTheory.Chain.IoLift.AbsIrr (fun X : lieAt V τ => a X) := by
  rcases Nat.eq_zero_or_pos V.rank with h0 | hpos
  · exact kFin_rank_zero M τ h0
  obtain ⟨p, q, e, he⟩ : ∃ p q : ℕ, ∃ e : Ix p q ≃ Fin V.rank, GlobalTheory.RealPar.BlockOrd e (M.ε τ) :=
    ⟨_, _, GlobalTheory.RealPar.exists_blockOrd (M.ε τ) rfl rfl⟩
  have hcard := Fintype.card_congr e
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  have hn : 1 ≤ p + q := hcard ▸ hpos
  let T : GrpData p q := Classical.choice (GlobalTheory.DetSqrtCover.nonempty_grpData p q)
  let P : GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters.SignedPar V.rank :=
    ⟨M.lam τ, M.ε τ, GlobalTheory.DSParam.isHCParam_of_isDS _ _ _ _ _ (M.enum τ).1 (M.ds τ)⟩
  have hsc : SignCompat (M.ε τ) e := by
    rintro (a | a)
    · exact he.1 a
    · exact he.2.1 a
  obtain ⟨R, U, -, hU⟩ := GlobalTheory.CoverModel.exists_pull T (fun U hU => ((hH.1 p q hn T).1 U hU).2.1) P
    (e := e) he (σ := M.σ τ) (M.ds τ)
  have hM : Matches R M τ (plainMat e) 0 U :=
    GlobalTheory.CoverModel.matches_of_grp hH (s := RingHom.id ℂ) (fun _ => rfl) R M τ
      (GlobalTheory.CoverModel.isFormIso_plainMat hsc) 0 U (fun g x => by simp [hU, plainMat])
  obtain ⟨hs, a, ha⟩ := GlobalTheory.Chain.IoLift.kFin_smooth_isKAct D V S M τ _ _ T R _ 0 _ hM
  have hAI := ((hH.1 p q hn T).1 R.U ⟨R.nontriv, R.irred⟩).2.2 R.HK R.ι ⟨R.ι_inj, R.ι_range, R.der⟩
  exact ⟨hs, a, ha, GlobalTheory.KFinIrr.absIrr_kFin D V S M τ _ _ T R _ 0 U.toLinearEquiv a hM hAI.2 hAI.1 ha⟩

end GlobalTheory.KFinLoc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteVectorsDiscreteSeriesSmoothAbsolutelyIrreStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_vectors_discrete_series_smooth_absolutely_irreducible : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ M.sm τ ∧ ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), GlobalTheory.Chain.IoLift.IsKAct M τ a ∧ GlobalTheory.Chain.IoLift.AbsIrr (fun X : lieAt V τ => a X) := by
  first | exact @GlobalTheory.KFinLoc.kFin_smooth_absIrr | exact GlobalTheory.KFinLoc.kFin_smooth_absIrr | (intros; apply GlobalTheory.KFinLoc.kFin_smooth_absIrr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmIntegralComm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.CommInt

theorem om_integral_comm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (U : Type) [TopologicalSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U] (m : Measure U) [SFinite m] (F : U → WO S T → ℂ) (p : GA D S × GA D T) (β : U → ℝ), (∀ u, IsThetaFunO ψ S T (F u)) → Continuous (Function.uncurry F) → Continuous (fun q : U × WO S T => om p (F q.1) q.2) → Integrable β m → (∀ u w, ‖F u w‖ ≤ β u ∧ ‖om p (F u) w‖ ≤ β u) → IsThetaFunO ψ S T (fun w => ∫ u, F u w ∂m) → ∀ w, om p (fun w' => ∫ u, F u w' ∂m) w = ∫ u, om p (F u) w ∂m := by
  intro D ψ S T χS χT om hom U _ _ _ _ m _ F p β hF hFc hOc hβ hdom hG w
  have hψ := hom.std
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : FirstCountableTopology (WO S T) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.Size.exists_isCovolOne S T
  haveI hfin : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  haveI : SFinite (μ.restrict 𝓕) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfin)
  set G : WO S T → ℂ := fun w => ∫ u, F u w ∂m with hGdef
  set H : WO S T → ℂ := fun w => ∫ u, om p (F u) w ∂m with hHdef
  have hHc : Continuous H := by
    refine continuous_of_dominated (bound := β) (fun x => ?_) (fun x => ?_) hβ ?_
    · exact (hOc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun u => (hdom u x).2
    · exact Filter.Eventually.of_forall fun u => hOc.comp (continuous_const.prodMk continuous_id)
  have hHb : ∀ x, ‖H x‖ ≤ ∫ u, β u ∂m := fun x =>
    norm_integral_le_of_norm_le hβ (Filter.Eventually.of_forall fun u => (hdom u x).2)
  have hOG := hom.om_pres p _ hG
  set q : WO S T → ℂ := fun x => om p G x - H x with hqdef
  have hq : q = 0 := by
    refine GlobalTheory.T.eq_zero_of_orthogonal_all_thetaFunctions D ψ hψ S T μ 𝓕 hμ h𝓕 q (hOG.cont.sub hHc) ?_ ?_
    · intro γ x
      have e1 := hOG.quasi γ x
      have e2 : H (ratW T S γ + x) = ψ (-(symplOH S T (ratW T S γ) x)) * H x := by
        simp only [hHdef]
        rw [← integral_const_mul]
        congr 1
        funext u
        exact (hom.om_pres p _ (hF u)).quasi γ x
      simp only [hqdef]
      rw [e1, e2]
      ring
    · intro f hf

      haveI : SecondCountableTopology (WO S T) := i3
      obtain ⟨CG, hCG⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hOG
      have hf0 := hom.om_pres p⁻¹ f hf
      have hff0 : om p (om p⁻¹ f) = f := by
        change (om p * om p⁻¹) f = f
        rw [← map_mul, mul_inv_cancel, map_one]; rfl
      set f0 := om p⁻¹ f with hf0def
      obtain ⟨C0, hC0⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hf0
      obtain ⟨Cf, hCf⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hf
      have hint : ∀ (g h : WO S T → ℂ) (a b : ℝ), Continuous g → Continuous h → (∀ x, ‖g x‖ ≤ a) →
          (∀ x, ‖h x‖ ≤ b) → Integrable (fun x => g x * star (h x)) (μ.restrict 𝓕) := by
        intro g h a b hg hh ha hb
        refine Integrable.mono' (integrable_const (a * b)) (hg.mul hh.star).aestronglyMeasurable
          (ae_of_all _ fun x => ?_)
        rw [norm_mul, norm_star]
        exact mul_le_mul (ha x) (hb x) (norm_nonneg _) ((norm_nonneg _).trans (ha x))
      have hprod : ∀ (K : U → WO S T → ℂ) (h : WO S T → ℂ) (b : ℝ), Continuous (fun z : U × WO S T => K z.1 z.2) →
          (∀ u x, ‖K u x‖ ≤ β u) → Continuous h → (∀ x, ‖h x‖ ≤ b) →
          Integrable (Function.uncurry fun x u => K u x * star (h x)) ((μ.restrict 𝓕).prod m) := by
        intro K h b hK hKb hh hb
        refine Integrable.mono' (((integrable_const b).mul_prod hβ)) ?_ (ae_of_all _ fun z => ?_)
        · exact ((hK.comp (continuous_snd.prodMk continuous_fst)).mul (hh.comp continuous_fst).star).aestronglyMeasurable
        · show ‖K z.2 z.1 * star (h z.1)‖ ≤ b * β z.2
          rw [norm_mul, norm_star, mul_comm b]
          exact mul_le_mul (hKb z.2 z.1) (hb z.1) (norm_nonneg _) ((norm_nonneg _).trans (hKb z.2 z.1))
      have hsc := fun g g' (hg : IsThetaFunO ψ S T g) (hg' : IsThetaFunO ψ S T g') =>
        GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S T μ 𝓕 hμ h𝓕 (om p) (hom.om_pres p) (hom.om_unit μ 𝓕 hμ h𝓕 p) g g' hg hg'
      have A : ∫ x in 𝓕, om p G x * star (f x) ∂μ = ∫ x in 𝓕, G x * star (f0 x) ∂μ := by
        rw [← hff0]; exact hsc G f0 hG hf0
      have B : ∫ x in 𝓕, G x * star (f0 x) ∂μ = ∫ x in 𝓕, H x * star (f x) ∂μ := by
        calc ∫ x in 𝓕, G x * star (f0 x) ∂μ = ∫ x in 𝓕, ∫ u, F u x * star (f0 x) ∂m ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun x => ?_)
              show (∫ u, F u x ∂m) * star (f0 x) = ∫ u, F u x * star (f0 x) ∂m
              rw [integral_mul_const]
          _ = ∫ u, ∫ x in 𝓕, F u x * star (f0 x) ∂μ ∂m :=
              integral_integral_swap (hprod F f0 C0 hFc (fun u x => (hdom u x).1) hf0.cont hC0)
          _ = ∫ u, ∫ x in 𝓕, om p (F u) x * star (f x) ∂μ ∂m := by
              refine integral_congr_ae (ae_of_all _ fun u => ?_)
              rw [← hff0]; exact (hsc (F u) f0 (hF u) hf0).symm
          _ = ∫ x in 𝓕, ∫ u, om p (F u) x * star (f x) ∂m ∂μ :=
              (integral_integral_swap (hprod (fun u => om p (F u)) f Cf hOc (fun u x => (hdom u x).2) hf.cont hCf)).symm
          _ = ∫ x in 𝓕, H x * star (f x) ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun x => ?_)
              show ∫ u, om p (F u) x * star (f x) ∂m = (∫ u, om p (F u) x ∂m) * star (f x)
              rw [integral_mul_const]
      have i1 := hint (om p G) f CG Cf hOG.cont hf.cont hCG hCf
      have i2 := hint H f (∫ u, β u ∂m) Cf hHc hf.cont hHb hCf
      simp only [hqdef, sub_mul]
      rw [integral_sub i1 i2, A, B, sub_self]
  have := congrFun hq w
  simp only [hqdef, Pi.zero_apply, sub_eq_zero] at this
  exact this

end GlobalTheory.CommInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PiTensorSubmoduleEqTopOfAbsolutelyIrreducibleSta
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PiTensorSubmoduleEqTopOfAbsolutelyIrreducibleSta
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.TensorIrr

open GlobalTheory.Chain.IoLift

variable {ι : Type} [Fintype ι] {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]

theorem position_add (i : ι) (f g : Module.End ℂ (K i)) : intersection_update_fsHerm_neg_one i (f + g) = intersection_update_fsHerm_neg_one i f + intersection_update_fsHerm_neg_one i g := by
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.add_apply, position_tprod, LinearMap.add_apply]
  rw [← MultilinearMap.map_update_add]

theorem position_mul (i : ι) (f g : Module.End ℂ (K i)) : intersection_update_fsHerm_neg_one i (f * g) = intersection_update_fsHerm_neg_one i f ∘ₗ intersection_update_fsHerm_neg_one i g := by
  ext v
  simp [position_tprod]

theorem position_algebraMap (i : ι) (c : ℂ) :
    intersection_update_fsHerm_neg_one i (algebraMap ℂ (Module.End ℂ (K i)) c) = c • LinearMap.id := by
  ext v
  simp only [LinearMap.compMultilinearMap_apply, position_tprod, LinearMap.smul_apply, LinearMap.id_apply]
  rw [Module.algebraMap_end_apply, MultilinearMap.map_update_smul, Function.update_eq_self]
  rfl

theorem stable_adjoin_position (i : ι) {G : Type} (a : G → Module.End ℂ (K i))
    (N : Submodule ℂ (⨂[ℂ] j, K j)) (hN : ∀ g, ∀ x ∈ N, intersection_update_fsHerm_neg_one i (a g) x ∈ N)
    {r : Module.End ℂ (K i)} (hr : r ∈ Algebra.adjoin ℂ (Set.range a)) :
    ∀ y ∈ N, intersection_update_fsHerm_neg_one i r y ∈ N := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hN g
  | algebraMap c =>
    intro y hy
    rw [position_algebraMap]
    exact N.smul_mem c hy
  | add x y _ _ hx hy =>
    intro z hz
    rw [position_add]
    exact N.add_mem (hx z hz) (hy z hz)
  | mul x y _ _ hx hy =>
    intro z hz
    rw [position_mul]
    exact hx _ (hy z hz)

theorem exists_finset_position (i : ι) (t : ⨂[ℂ] j, K j) :
    ∃ s : Finset (K i), ∀ f g : Module.End ℂ (K i), (∀ m ∈ s, f m = g m) → intersection_update_fsHerm_neg_one i f t = intersection_update_fsHerm_neg_one i g t := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r u =>
    refine ⟨{u i}, fun f g h => ?_⟩
    rw [map_smul, map_smul, position_tprod, position_tprod, h (u i) (Finset.mem_singleton_self _)]
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hy
    refine ⟨s ∪ s', fun f g h => ?_⟩
    rw [map_add (f := _), map_add (f := _), hs f g fun m hm => h m (Finset.mem_union_left _ hm),
      hs' f g fun m hm => h m (Finset.mem_union_right _ hm)]

theorem eq_zero_of_subsingleton (i : ι) [Subsingleton (K i)] (t : ⨂[ℂ] j, K j) : t = 0 := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r u =>
    rw [MultilinearMap.map_coord_zero _ i (Subsingleton.elim _ _), smul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

end GlobalTheory.TensorIrr

namespace GlobalTheory.TensorIrr

open GlobalTheory.Chain.IoLift

variable {ι : Type} [Fintype ι] {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]

theorem stable_all_position (i : ι) {G : Type} (a : G → Module.End ℂ (K i)) (ha : AbsIrr a) [Nontrivial (K i)]
    (N : Submodule ℂ (⨂[ℂ] j, K j)) (hN : ∀ g, ∀ x ∈ N, intersection_update_fsHerm_neg_one i (a g) x ∈ N)
    (f : Module.End ℂ (K i)) : ∀ y ∈ N, intersection_update_fsHerm_neg_one i f y ∈ N := by
  intro y hy
  obtain ⟨s, hs⟩ := exists_finset_position i y
  obtain ⟨r, hr, hfr⟩ := GlobalTheory.IrrTensor.density a ha.1 ha.2 f s
  rw [hs f r hfr]
  exact stable_adjoin_position i a N hN hr y hy

theorem stable_map (N : Submodule ℂ (⨂[ℂ] j, K j))
    (hN : ∀ i (f : Module.End ℂ (K i)), ∀ y ∈ N, intersection_update_fsHerm_neg_one i f y ∈ N) (f : ∀ i, Module.End ℂ (K i)) :
    ∀ y ∈ N, PiTensorProduct.map f y ∈ N := by
  have key : ∀ s : Finset ι, ∀ y ∈ N,
      PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) y ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro y hy; simpa using hy
    | insert i s hi ih =>
      have : PiTensorProduct.map (fun j => if j ∈ insert i s then f j else LinearMap.id) =
          intersection_update_fsHerm_neg_one i (f i) ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) := by
        ext v
        simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
          position_tprod]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj]
      intro y hy
      rw [this, LinearMap.comp_apply]
      exact hN i (f i) _ (ih y hy)
  intro y hy
  simpa using key Finset.univ y hy

theorem eq_top_of_stable : ∀ (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (G : ι → Type) (a : ∀ i, G i → Module.End ℂ (K i)), (∀ i, GlobalTheory.Chain.IoLift.AbsIrr (a i)) → ∀ N : Submodule ℂ (PiTensorProduct ℂ K), (∀ i g, ∀ x ∈ N, GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one i (a i g) x ∈ N) → N ≠ ⊥ → N = ⊤ := by
  intro ι _ K _ _ G a ha N hN hne
  obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hnt : ∀ i, Nontrivial (K i) := by
    intro i
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hx0 (eq_zero_of_subsingleton i x)
  have hall : ∀ i (f : Module.End ℂ (K i)), ∀ y ∈ N, intersection_update_fsHerm_neg_one i f y ∈ N := fun i f =>
    stable_all_position i (a i) (ha i) N (hN i) f
  obtain ⟨w, hw⟩ : ∃ w, Scal.tform w x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (Scal.eq_of_tform fun w => by rw [h w, map_zero])
  have htp : ∀ v : ∀ i, K i, PiTensorProduct.tprod ℂ v ∈ N := by
    intro v
    have hm : PiTensorProduct.map (fun i => (w i).smulRight (v i)) =
        (Scal.tform w).smulRight (PiTensorProduct.tprod ℂ v) := by
      ext u
      simp [Scal.tform_tprod, MultilinearMap.map_smul_univ]
    have h1 := stable_map N hall (fun i => (w i).smulRight (v i)) x hxN
    rw [hm, LinearMap.smulRight_apply] at h1
    have h2 := N.smul_mem (Scal.tform w x)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hw, one_smul] at h2
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  exact htp v

end GlobalTheory.TensorIrr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PiTensorSubmoduleEqTopOfAbsolutelyIrreducibleStaStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piTensor_submodule_eq_top_of_absolutely_irreducible_stable : ∀ (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (G : ι → Type) (a : ∀ i, G i → Module.End ℂ (K i)), (∀ i, GlobalTheory.Chain.IoLift.AbsIrr (a i)) → ∀ N : Submodule ℂ (PiTensorProduct ℂ K), (∀ i g, ∀ x ∈ N, GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one i (a i g) x ∈ N) → N ≠ ⊥ → N = ⊤ := by
  first | exact @GlobalTheory.TensorIrr.eq_top_of_stable | exact GlobalTheory.TensorIrr.eq_top_of_stable | (intros; apply GlobalTheory.TensorIrr.eq_top_of_stable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharacterEqOneOfTrivialSplitPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCongruenceModulusIdelicCharacterTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCongruenceModulusIdelicCharacterTrivial
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HeckeSplitAll

theorem char_trivial_modSet : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), Continuous ν →
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ GlobalTheory.HeckeSplitAll.modSet D N, ν x = 1 := by
  intro D ν hν
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν
  refine ⟨N, hN, fun x hx => ?_⟩
  obtain ⟨h1, ⟨r, hr, hxr⟩, h3⟩ := hx
  have hNr : (N : Af D.host.F ⊗[D.host.F] D.host.E) * r = N • r := (nsmul_eq_mul _ _).symm
  have hfin : finPart D (x : AE D) ∈ intAE D := by
    have : finPart D (x : AE D) = 1 + N • r := by rw [← hNr, ← hxr]; ring
    rw [this]
    exact add_mem (AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩) (nsmul_mem hr N)
  exact hker x ⟨h1, hfin, h3⟩ ⟨r, hr, by rw [hxr, hNr]⟩

end GlobalTheory.HeckeSplitAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCongruenceModulusIdelicCharacterTrivialStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_congruenceModulus_idelicCharacter_trivial : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), Continuous ν → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ GlobalTheory.HeckeSplitAll.modSet D N, ν x = 1 := by
  first | exact @GlobalTheory.HeckeSplitAll.char_trivial_modSet | exact GlobalTheory.HeckeSplitAll.char_trivial_modSet | (intros; apply GlobalTheory.HeckeSplitAll.char_trivial_modSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharacterEqOneOfTrivialSplitPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HeckeSplitAll

theorem heckeChar_eq_one_of_split : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → (∀ e, IsSplitIdem D e → ∀ x : (AE D)ˣ, (e + cA D e) * ((x : AE D) - 1) = (x : AE D) - 1 → ν x = 1) → ∀ x, ν x = 1 := by
  intro D ν hν hs
  obtain ⟨N, hN, hA⟩ := GlobalTheory.T.exists_congruenceModulus_idelicCharacter_trivial D ν hν.1
  have hH : grpH D N ≤ ν.ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ((⟨k, rfl⟩ | ⟨e, he, hx⟩) | hx)
    · exact hν.2 k
    · exact hs e he x hx
    · exact hA x hx
  have hcl : closure (grpH D N : Set (AE D)ˣ) ⊆ ν.ker := by
    refine closure_minimal hH ?_
    have : (ν.ker : Set (AE D)ˣ) = ν ⁻¹' {1} := rfl
    rw [this]
    exact isClosed_singleton.preimage hν.1
  intro x
  obtain ⟨z, hz, hxz⟩ := GlobalTheory.T.exists_finPartOne_mul_inv_mem_heckeSplitCongruence D N hN x
  have h1 : ν (x * z⁻¹) = 1 := hH hxz
  have h2 : ν z = 1 := hcl (GlobalTheory.T.mem_closure_heckeSplitCongruence_of_finPart_one D N hN z hz)
  have : x = x * z⁻¹ * z := by group
  rw [this, map_mul, h1, h2, one_mul]

end GlobalTheory.HeckeSplitAll
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharacterEqOneOfTrivialSplitPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_eq_one_of_trivial_splitPlaces : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → (∀ e, IsSplitIdem D e → ∀ x : (AE D)ˣ, (e + cA D e) * ((x : AE D) - 1) = (x : AE D) - 1 → ν x = 1) → ∀ x, ν x = 1 := by
  first | exact @GlobalTheory.HeckeSplitAll.heckeChar_eq_one_of_split | exact GlobalTheory.HeckeSplitAll.heckeChar_eq_one_of_split | (intros; apply GlobalTheory.HeckeSplitAll.heckeChar_eq_one_of_split <;> assumption)
end
end
