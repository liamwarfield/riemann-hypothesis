module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasCompactSupportTj
open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtHecke

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isUnifV_of_ordL {w : Pl E} {x : w.adicCompletion E} (h0 : x ≠ 0) (h : ordL x = 1) : IsUnifV E w x := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  unfold ordL at h
  rw [dite_eq_right hv] at h
  have e : WithZero.unzero hv = Multiplicative.ofAdd (-1 : ℤ) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    omega
  unfold IsUnifV
  rw [← e, WithZero.coe_unzero]

theorem ordL_eq_zero {w : Pl E} {x : w.adicCompletion E} (h : Valued.v x = 1) : ordL x = 0 := by
  have hv : Valued.v x ≠ 0 := by rw [h]; exact one_ne_zero
  unfold ordL
  rw [dite_eq_right hv]
  have e : WithZero.unzero hv = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h]
    rfl
  rw [e]
  simp

theorem det_mem {w : Pl E} {n : ℕ} {M : Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    (hM : ∀ i j, M i j ∈ Ov E w) : M.det ∈ Ov E w := by
  rw [Matrix.det_apply']
  exact Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _)
    (Subring.prod_mem _ fun i _ => hM _ _)

theorem v_det {w : Pl E} {n : ℕ} {g : GLw n w} (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) : Valued.v g.val.det = 1 := by
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hg
  have d1 : Valued.v g.val.det ≤ 1 := det_mem h1
  have d2 : Valued.v (g⁻¹).val.det ≤ 1 := det_mem h2
  have e : g.val.det * (g⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, show g.val * (g⁻¹).val = 1 from g.mul_inv, Matrix.det_one]
  have e' : Valued.v g.val.det * Valued.v (g⁻¹).val.det = 1 := by
    rw [← map_mul, e, map_one]
  refine le_antisymm d1 ?_
  calc (1 : _) = Valued.v g.val.det * Valued.v (g⁻¹).val.det := e'.symm
    _ ≤ Valued.v g.val.det * 1 := mul_le_mul_right d2 _
    _ = _ := mul_one _

def cMu {a b : ℕ} {w : Pl E} (μ : (w.adicCompletion E)ˣ →* ℂˣ) (m : GLw a w × GLw b w) : ℂ :=
  (μ ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ)

theorem mu_unit {a b : ℕ} {w : Pl E} {μ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1)
    {κ : GLw a w × GLw b w} (hκ : κ ∈ K2 a b w) :
    μ (GeneralLinearGroup.det κ.1 ^ b * GeneralLinearGroup.det κ.2 ^ a) = 1 := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hκ
  refine hμ _ (ordL_eq_zero ?_)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, map_mul, map_pow,
    v_det h1, v_det h2, one_pow, one_mul]

theorem cMu_mul_left {a b : ℕ} {w : Pl E} {μ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1)
    {κ : GLw a w × GLw b w} (hκ : κ ∈ K2 a b w) (m : GLw a w × GLw b w) : cMu μ (κ * m) = cMu μ m := by
  unfold cMu
  have e : ((-1) ^ (a * b) * GeneralLinearGroup.det (κ * m).1 ^ b * GeneralLinearGroup.det (κ * m).2 ^ a :
      (w.adicCompletion E)ˣ) = ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) *
        (GeneralLinearGroup.det κ.1 ^ b * GeneralLinearGroup.det κ.2 ^ a) := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
    ac_rfl
  rw [e, map_mul, mu_unit hμ hκ, mul_one]

theorem cMu_mul_right {a b : ℕ} {w : Pl E} {μ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1)
    {κ : GLw a w × GLw b w} (hκ : κ ∈ K2 a b w) (m : GLw a w × GLw b w) : cMu μ (m * κ) = cMu μ m := by
  unfold cMu
  have e : ((-1) ^ (a * b) * GeneralLinearGroup.det (m * κ).1 ^ b * GeneralLinearGroup.det (m * κ).2 ^ a :
      (w.adicCompletion E)ˣ) = ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) *
        (GeneralLinearGroup.det κ.1 ^ b * GeneralLinearGroup.det κ.2 ^ a) := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow]
    ac_rfl
  rw [e, map_mul, mu_unit hμ hκ, mul_one]

theorem hasCompactSupport_Tj {w : Pl E} {n : ℕ} {ϖ : w.adicCompletion E} (h0 : ϖ ≠ 0) (k : ℕ) :
    HasCompactSupport (Tj ℂ n (Ov E w) ϖ k : GLw n w → ℂ) := by
  have hdet : (diagJ n ϖ k).det ≠ 0 := by
    rw [diagJ, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    split_ifs
    · exact h0
    · exact one_ne_zero
  set t : GLw n w := GeneralLinearGroup.mkOfDetNeZero (diagJ n ϖ k) hdet with ht
  have hI := GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w n
  have hS : IsCompact ((fun p : GLw n w × GLw n w => p.1 * t * p.2) ''
      ((GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ×ˢ (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)))) :=
    (hI.prod hI).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  refine HasCompactSupport.intro' hS hS.isClosed fun g hg => ?_
  unfold Tj
  refine Set.indicator_of_notMem ?_ _
  rintro ⟨x, hx, y, hy, e⟩
  exact hg ⟨(x, y), ⟨hx, hy⟩, Units.ext (by simpa [ht] using e.symm)⟩

theorem blk_zero_mem {a b n : ℕ} (h : a + b = n) (w : Pl E) {κ : GLw a w × GLw b w} (hκ : κ ∈ K2 a b w) :
    blk h w κ 0 ∈ GlobalTheory.LFun.KGL w (n := n) := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hκ
  obtain ⟨l1, l2⟩ := GlobalTheory.BCT.CtLevel.lev_KGL_of_unram E a b n h w 1 (fun _ _ => rfl)
  have d1 : GlobalTheory.BCT.CtLevel.dgM h w (κ.1, 1) ∈ GlobalTheory.LFun.KGL w (n := n) := by
    have : κ.1 ∈ GlobalTheory.BCT.CtLevel.lev₁ h w (GlobalTheory.LFun.KGL w (n := n)) 1 := by rw [l1]; exact h1
    exact this.1.2
  have d2 : GlobalTheory.BCT.CtLevel.dgM h w (1, κ.2) ∈ GlobalTheory.LFun.KGL w (n := n) := by
    have : κ.2 ∈ GlobalTheory.BCT.CtLevel.lev₂ h w (GlobalTheory.LFun.KGL w (n := n)) 1 := by rw [l2]; exact h2
    exact this.1.2
  rw [GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.blk_zero_eq]
  have e : κ = (κ.1, 1) * (1, κ.2) := by simp
  rw [e, map_mul]
  exact mul_mem d1 d2

theorem ctT_eq {n a b : ℕ} (h : a + b = n) {w : Pl E} (hw : IsSplitAt w) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (k : ℕ) :
    RS.ctT h w μ ϖ k = fun m => cMu μ m * phi3 h w (Tj ℂ n (Ov E w) ϖ k) 1 1 m := by
  funext m
  rw [GlobalTheory.CompanionTheory.CtS.ctT_split_eq E n a b h w μ ϖ hw hϖ k m]
  simp [phi3, cMu]

theorem isHecke_ctT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (ϖ : (w.adicCompletion E)ˣ), IsSplitAt w → ordL (ϖ : w.adicCompletion E) = 1 → (∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1) → ∀ k : ℕ, IsHecke (K2 a b w) (RS.ctT h w μ (ϖ : w.adicCompletion E) k) := by
  intro E _ _ _ n a b h w μ ϖ hw hord hμ k
  have h0 : (ϖ : w.adicCompletion E) ≠ 0 := ϖ.ne_zero
  have hϖ : IsUnifV E w (ϖ : w.adicCompletion E) := isUnifV_of_ordL h0 hord
  have hT := Tj_mem_hecke (n := n) hϖ k
  have hf : ∀ k₁ ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k₂ ∈ GlobalTheory.LFun.KGL w (n := n), ∀ g : GLw n w,
      Tj ℂ n (Ov E w) (ϖ : w.adicCompletion E) k (k₁ * g * k₂) = Tj ℂ n (Ov E w) (ϖ : w.adicCompletion E) k g :=
    fun k₁ h₁ k₂ h₂ g => hT.1 ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ g
  have hbi := GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_bi_invariant (a := a) (b := b) h w (GlobalTheory.LFun.KGL w (n := n)) le_rfl
    (fun k hk k' hk' => mul_mem (mul_mem hk hk') (inv_mem hk)) _ hf 1 1 (one_mem _) (one_mem _)
  have hone : (1 : GLw a w × GLw b w) ∈ leviOf h w (GlobalTheory.LFun.KGL w (n := n)) := blk_zero_mem h w (one_mem _)
  rw [ctT_eq h hw μ hϖ k]
  refine ⟨?_, fun κ hκ x => ⟨?_, ?_⟩⟩
  · exact (GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_compact_support h w _ (hasCompactSupport_Tj h0 k) 1 1).mul_left
  · have := hbi κ 1 (blk_zero_mem h w hκ) hone x
    rw [mul_one] at this
    simp only [cMu_mul_left hμ hκ, this]
  · have := hbi 1 κ hone (blk_zero_mem h w hκ) x
    rw [one_mul] at this
    simp only [cMu_mul_right hμ hκ, this]

end GlobalTheory.CompanionTheory.CtHecke
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingSplitOf
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingSplitOf
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
open PositivityTheory.Rg.BcB.F.Eig (lconv)
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace GlobalTheory.CompanionTheory.MatchPowers

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isLevel_KL (n : ℕ) (w : Pl E) : IsLevel (MonoidHom.id _) (KL n w) (KL n w) :=
  ⟨GlobalTheory.CompanionTheory.SphLine.isOpen_KL n w, le_rfl, fun _ h => h⟩

theorem isHecke_lpow_KL {n : ℕ} {w : Pl E} {f : UL n w → ℂ} (hf : IsHecke (KL n w) f) (j : ℕ) :
    IsHecke (KL n w) (lpow (KL n w) f j) :=
  GlobalTheory.CompanionTheory.UnitaryWord.isHecke_lpow GlobalTheory.CompanionTheory.LocHecke.locAlg (isLevel_KL n w) hf j

theorem matchSplitOf : MatchSplitOf := by
  intro hM3 hCt E _ _ _ n a ha w hw μ hμ f hf k hk
  have hc : ∀ j : ℕ, ctMu (Nat.add_sub_cancel' ha) w μ (lpow (KL n w) f j) =
      Nat.rec (ctMu (Nat.add_sub_cancel' ha) w μ (lone (KL n w)))
        (fun _ g => mconv (ctMu (Nat.add_sub_cancel' ha) w μ f) g) j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      have h := hCt E n a ha w hw μ hμ f _ hf (isHecke_lpow_KL hf j)
      rw [ih] at h
      exact h
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := hM3 E n a ha w hw μ (KL n w) (isLevel_KL n w) _ (isHecke_lpow_KL hf (j + 1))
  rw [hc (j + 1)] at h
  exact h

end GlobalTheory.CompanionTheory.MatchPowers

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingSplitOfStatement
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matching_split_of : MatchSplitOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchPowers.matchSplitOf | exact GlobalTheory.CompanionTheory.MatchPowers.matchSplitOf | (intros; apply GlobalTheory.CompanionTheory.MatchPowers.matchSplitOf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgEqZeroOfInfiniteRange
noncomputable section

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
open scoped Classical

namespace GlobalTheory.CompanionTheory.MatchLinear

theorem index_rStab_ne_zero {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    (u : H → ℂ) (hu : IsLocallyConstant u) : (rStab u).index ≠ 0 := by
  have hd : IsLocallyConstant fun p : H × H => u (p.1 * p.2) - u p.1 :=
    (hu.comp_continuous (continuous_fst.mul continuous_snd)).sub (hu.comp_continuous continuous_fst)
  obtain ⟨A, B, -, hB, hA, h1, hAB⟩ := generalized_tube_lemma (isCompact_univ (X := H)) (isCompact_singleton (x := (1 : H)))
    (hd.isOpen_fiber 0) (fun p hp => by
      obtain ⟨-, h⟩ := hp
      have : p.2 = 1 := h
      simp [this])
  have hsub : B ⊆ (rStab u : Set H) := fun k hk x =>
    sub_eq_zero.1 (hAB (show (x, k) ∈ A ×ˢ B from ⟨hA (Set.mem_univ x), hk⟩))
  have hopen : IsOpen (rStab u : Set H) :=
    Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hB.mem_nhds (h1 rfl)) hsub)
  haveI := Subgroup.quotient_finite_of_isOpen (rStab u) hopen
  exact Subgroup.index_ne_zero_of_finite

theorem avg_lin {H : Type} [Group H] (S : Subgroup H) (hS : S.index ≠ 0) {J : Type} [Fintype J] (a : J → ℂ)
    (u : J → H → ℂ) (hu : ∀ j, S ≤ rStab (u j)) :
    avg (fun h => ∑ j, a j * u j h) = ∑ j, a j * avg (u j) := by
  have hsum : S ≤ rStab (fun h => ∑ j, a j * u j h) := fun k hk => show ∀ x, _ from fun x =>
    Finset.sum_congr rfl fun j _ => by rw [(hu j hk : ∀ x, u j (x * k) = u j x) x]
  haveI : S.FiniteIndex := ⟨hS⟩
  haveI : Finite (H ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (H ⧸ S) := Fintype.ofFinite _
  rw [avg_eq_of_le_rStab _ _ S hsum hS, finsum_eq_sum_of_fintype, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [avg_eq_of_le_rStab _ _ S (hu j) hS, finsum_eq_sum_of_fintype, ← Finset.mul_sum]
  ring

theorem twOrb_lin {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (hθ : Continuous θ)
    (K : Subgroup G) (hK : IsCompact (K : Set G)) (y : G) {J : Type} [Fintype J] (a : J → ℂ) (g : J → G → ℂ)
    (hg : ∀ j, IsLocallyConstant (g j))
    (hfin : ∀ j, {q : DoubleCoset.Quotient (twCent θ y : Set G) (K : Set G) |
      ∃ k ∈ K, g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k)) ≠ 0}.Finite) :
    twOrb θ K y (fun z => ∑ j, a j * g j z) = ∑ j, a j * twOrb θ K y (g j) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hsupp : ∀ j, (Function.support fun q : DoubleCoset.Quotient (twCent θ y : Set G) (K : Set G) =>
      (((twCent θ y ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent θ y)) : ℕ) : ℂ) *
        avg fun k : K => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))).Finite := by
    intro j
    refine (hfin j).subset fun q hq => ?_
    by_contra hno
    simp only [Set.mem_setOf_eq, not_exists, not_and, ne_eq, not_not] at hno
    apply hq
    have h0 : (fun k : K => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))) = fun _ => 0 :=
      funext fun k => hno k k.2
    have ha : avg (fun k : K => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))) = 0 := by
      rw [h0]; simp [avg]
    simp only [ha, mul_zero]
  unfold twOrb
  have hterm : ∀ q : DoubleCoset.Quotient (twCent θ y : Set G) (K : Set G),
      (((twCent θ y ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent θ y)) : ℕ) : ℂ) *
        (avg fun k : K => ∑ j, a j * g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))) =
      ∑ j, a j * ((((twCent θ y ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex
        (cptPart (twCent θ y)) : ℕ) : ℂ) *
        avg fun k : K => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))) := by
    intro q
    have hc : Continuous fun k : K => (Quotient.out q * (k : G))⁻¹ * y * θ (Quotient.out q * (k : G)) := by
      have h1 : Continuous fun k : K => Quotient.out q * (k : G) := continuous_const.mul continuous_subtype_val
      exact (h1.inv.mul continuous_const).mul (hθ.comp h1)
    have hi : ∀ j, (rStab fun k : K => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))).index ≠ 0 :=
      fun j => index_rStab_ne_zero _ ((hg j).comp_continuous hc)
    rw [avg_lin (⨅ j, rStab fun k : K => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k)))
      (Subgroup.index_iInf_ne_zero hi) a
      (fun j (k : K) => g j ((Quotient.out q * k)⁻¹ * y * θ (Quotient.out q * k))) (fun j => iInf_le _ j),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [finsum_congr hterm, finsum_sum_comm _ _ fun j _ => ?_]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_finsum]
  · exact (hsupp j).subset (Function.support_const_smul_subset (a j) _ |>.trans subset_rfl)

theorem clSum_lin {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (S : Set G) (wt : G → ℂ)
    (hS : {c : TwCl θ | c.rep ∈ S}.Finite) {J : Type} [Fintype J] (a : J → ℂ) (g : J → G → ℂ)
    (h : ∀ y ∈ S, twOrb θ K y (fun z => ∑ j, a j * g j z) = ∑ j, a j * twOrb θ K y (g j)) :
    clSum θ K S wt (fun z => ∑ j, a j * g j z) = ∑ j, a j * clSum θ K S wt (g j) := by
  have hsupp : ∀ j, (Function.support fun c : TwCl θ => if c.rep ∈ S then wt c.rep * twOrb θ K c.rep (g j) else 0).Finite :=
    fun j => hS.subset fun c hc => by
      by_contra hn
      exact hc (if_neg hn)
  unfold clSum
  have hterm : ∀ c : TwCl θ, (if c.rep ∈ S then wt c.rep * twOrb θ K c.rep (fun z => ∑ j, a j * g j z) else 0) =
      ∑ j, a j * (if c.rep ∈ S then wt c.rep * twOrb θ K c.rep (g j) else 0) := by
    intro c
    by_cases hc : c.rep ∈ S
    · simp only [if_pos hc, h _ hc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · simp only [if_neg hc, mul_zero, Finset.sum_const_zero]
  rw [finsum_congr hterm, finsum_sum_comm _ _ fun j _ => ?_]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_finsum]
  · exact (hsupp j).subset (Function.support_const_smul_subset (a j) _ |>.trans subset_rfl)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem charpoly_nrmL_twConj (hU : Unr E) (n : ℕ) (w : Pl E) (x g : GLw n w) :
    (nrmL n w (g⁻¹ * x * thL n w g)).val.charpoly = (nrmL n w x).val.charpoly := by
  rw [GlobalTheory.CompanionTheory.TwistOrbit.nrmL_twConj' hU, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
    Matrix.charpoly_units_conj']

theorem finite_dc_unitary (hU : Unr E) (n : ℕ) (w : Pl E) (y : UL n w) (hy : y.1.val.charpoly.Separable)
    (f : UL n w → ℂ) (hf : HasCompactSupport f) :
    {q : DoubleCoset.Quotient (twCent (MonoidHom.id (UL n w)) y : Set (UL n w)) (KL n w : Set (UL n w)) |
      ∃ k ∈ KL n w, f ((Quotient.out q * k)⁻¹ * y * MonoidHom.id (UL n w) (Quotient.out q * k)) ≠ 0}.Finite := by
  obtain ⟨hKo, hKc⟩ := GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w
  obtain ⟨D, hD, hP⟩ := GlobalTheory.OrbitU.orbit_cpt_U E hU n w y hy _ hf.isCompact
  refine GlobalTheory.CompanionTheory.TwistOrbit.finite_of_subset_mul' _ _ hKo
    ((fun p : UL n w × UL n w => p.1 * p.2⁻¹) '' (D ×ˢ (KL n w : Set (UL n w))))
    ((hD.prod hKc).image (by fun_prop)) (fun x => ∃ k ∈ KL n w,
      f ((x * k)⁻¹ * y * MonoidHom.id (UL n w) (x * k)) ≠ 0) ?_
  rintro x ⟨k, hk, hne⟩
  obtain ⟨t, ht, d, hd, e⟩ := hP (x * k) (subset_tsupport f hne)
  exact ⟨t, ht, d * k⁻¹, ⟨(d, k), ⟨hd, hk⟩, rfl⟩, by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩

theorem finite_dc_pair (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (h₁ : (nrmL a w y.1).val.charpoly.Separable) (h₂ : (nrmL b w y.2).val.charpoly.Separable)
    (f : GLw a w × GLw b w → ℂ) (hf : HasCompactSupport f) :
    {q : DoubleCoset.Quotient (twCent ((thL a w).prodMap (thL b w)) y : Set (GLw a w × GLw b w))
        (((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) |
      ∃ k ∈ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)), f ((Quotient.out q * k)⁻¹ * y *
        (thL a w).prodMap (thL b w) (Quotient.out q * k)) ≠ 0}.Finite := by
  obtain ⟨D, hD, hP⟩ := GlobalTheory.CompanionTheory.TwistOrbit.proper_pair hU a b w y h₁ h₂ _ hf.isCompact
  obtain ⟨hKo, hKc⟩ := GlobalTheory.BCT.StTw2Add.isOpen_isCompact_KK (E := E) a b w
  refine GlobalTheory.CompanionTheory.TwistOrbit.finite_of_subset_mul' _ _ hKo
    ((fun p : (GLw a w × GLw b w) × (GLw a w × GLw b w) => p.1 * p.2⁻¹) '' (D ×ˢ _))
    ((hD.prod hKc).image (by fun_prop)) (fun x => ∃ k ∈ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)),
      f ((x * k)⁻¹ * y * (thL a w).prodMap (thL b w) (x * k)) ≠ 0) ?_
  rintro x ⟨k, hk, hne⟩
  obtain ⟨t, ht, d, hd, e⟩ := hP (x * k) (subset_tsupport f hne)
  exact ⟨t, ht, d * k⁻¹, ⟨(d, k), ⟨hd, hk⟩, rfl⟩, by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩

theorem matchLin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n a b : ℕ) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ) (J : Type) [Fintype J] (c : J → ℂ) (f : J → UL n w → ℂ)
    (φ : J → GLw a w × GLw b w → ℂ),
    (∀ j, IsLocallyConstant (f j) ∧ HasCompactSupport (f j) ∧ IsLocallyConstant (φ j) ∧ HasCompactSupport (φ j)) →
    (∀ j, Match n a b w μ (f j) (φ j)) → Match n a b w μ (fun γ => ∑ j, c j * f j γ) (fun y => ∑ j, c j * φ j y) := by
  intro E _ _ _ hU n a b w μ J _ c f φ hreg hM Q₁ Q₂ m₁ m₂ d₁ d₂ hsep c₁ c₂
  have hs₁ : Q₁.Separable := hsep.of_mul_left
  have hs₂ : Q₂.Separable := hsep.of_mul_right
  have e₁ : stTw2 a b w Q₁ Q₂ (fun y => ∑ j, c j * φ j y) = ∑ j, c j * stTw2 a b w Q₁ Q₂ (φ j) := by
    unfold stTw2
    refine clSum_lin _ _ _ _ ?_ c φ ?_
    · exact GlobalTheory.BCT.StTw2Add.finite_prod _ _ (fun x => (nrmL a w x).val.charpoly = Q₁)
        (fun x => (nrmL b w x).val.charpoly = Q₂)
        (fun x g => by simp only [charpoly_nrmL_twConj hU])
        (fun x g => by simp only [charpoly_nrmL_twConj hU])
        (GlobalTheory.BCT.ClsFin.classes_finite E hU a w Q₁ hs₁).1 (GlobalTheory.BCT.ClsFin.classes_finite E hU b w Q₂ hs₂).1
    · rintro y ⟨hy₁, hy₂⟩
      have hθ : Continuous ((thL a w).prodMap (thL b w)) :=
        ((GlobalTheory.BCT.thL_continuous_involutive E hU a w).1.comp continuous_fst).prodMk
          ((GlobalTheory.BCT.thL_continuous_involutive E hU b w).1.comp continuous_snd)
      exact twOrb_lin _ hθ _ (GlobalTheory.BCT.StTw2Add.isOpen_isCompact_KK a b w).2 y c φ (fun j => (hreg j).2.2.1)
        fun j => finite_dc_pair hU a b w y (hy₁ ▸ hs₁) (hy₂ ▸ hs₂) (φ j) (hreg j).2.2.2
  have e₂ : kapOrb n w Q₁ Q₂ (fun γ => ∑ j, c j * f j γ) = ∑ j, c j * kapOrb n w Q₁ Q₂ (f j) := by
    unfold kapOrb
    refine clSum_lin _ _ _ _ (GlobalTheory.BCT.ClsFin.classes_finite E hU n w (Q₁ * Q₂) hsep).2 c f ?_
    intro y hy
    exact twOrb_lin _ continuous_id _ (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2 y c f (fun j => (hreg j).1)
      fun j => finite_dc_unitary hU n w y (by rw [show y.1.val.charpoly = Q₁ * Q₂ from hy]; exact hsep) (f j) (hreg j).2.1
  rw [e₁, e₂, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hM j Q₁ Q₂ m₁ m₂ d₁ d₂ hsep c₁ c₂]
  ring

end GlobalTheory.CompanionTheory.MatchLinear
end
end
