module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularPowerTorus
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocComm
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.LeviMatchingBlocks.StabilizerDilationWeightsDualIsotropicVector

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparablePowerTorus
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharpolyConjDiagonal
open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw

namespace GlobalTheory.CompanionTheory.UnitarySide

theorem charpoly_conj_diagonal {K : Type} [Field K] {n : ℕ} (c D g : GL (Fin n) K) (d : Fin n → K)
    (hD : D.val = Matrix.diagonal d) (hg : g = c * D * c⁻¹) :
    g.val.charpoly = ∏ i, (X - C (d i)) := by
  subst hg
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj, hD,
    Matrix.charpoly_diagonal]

open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end GlobalTheory.CompanionTheory.UnitarySide
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparablePowerTorus
noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.MLM Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SepPow

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem zpow_mul_inj {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {a c : ℤ} {u v : w.adicCompletion E}
    (hu : Valued.v u = 1) (hv : Valued.v v = 1)
    (h : ((ϖ ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * u = ((ϖ ^ c : (w.adicCompletion E)ˣ) : w.adicCompletion E) * v) :
    a = c := by
  have e := congrArg Valued.v h
  rw [map_mul, map_mul, hu, hv, mul_one, mul_one] at e
  have h1 : Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
    rw [GlobalTheory.BorelUMod.v_eq_exp ϖ.ne_zero, hϖ.1]
  have h0 : Valued.v (ϖ : w.adicCompletion E) ≠ 0 := by
    rw [h1]; exact WithZero.exp_ne_zero
  have hne : Valued.v (ϖ : w.adicCompletion E) ≠ 1 := by
    rw [h1, ← WithZero.exp_zero]
    intro h2
    have := WithZero.exp_injective h2
    omega
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀] at e
  exact zpow_right_injective₀ (zero_lt_iff.2 h0) hne e

theorem separable_of_fU {w : Pl E} {b : GLw n w} {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {l : Fin (n / 2) → ℤ}
    (hl : Cone l) {γ : UL n w} (h : fU n w b ϖ l γ ≠ 0) : γ.1.val.charpoly.Separable := by
  have hy := (GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl).1
  have h' : ∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b, γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1 := by
    by_contra hc
    exact h (if_neg hc)
  obtain ⟨x, hx, z, hz, e⟩ := h'
  obtain ⟨x', hx', ex⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
  obtain ⟨z', hz', ez⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hz)
  have ex' : x.1 = b * x' * b⁻¹ := ex.symm
  have ez' : z.1 = b * z' * b⁻¹ := ez.symm
  have hδ : dcos n w (tdiag ϖ (wexp n l)) (b⁻¹ * γ.1 * b) ≠ 0 := by
    have : ∃ p ∈ iwGL n w, ∃ q ∈ iwGL n w, b⁻¹ * γ.1 * b = p * tdiag ϖ (wexp n l) * q :=
      ⟨x', hx', z', hz', by rw [e, ex', ez']; group⟩
    simp [dcos, this]
  obtain ⟨m, -, τ, hτ, em⟩ := GlobalTheory.CompanionTheory.IwahoriContraction.contr_id w ϖ hϖ n (wexp n l) hy _ hδ
  have hval : (tdiag ϖ (wexp n l) * τ).val = Matrix.diagonal fun i =>
      ((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ) : w.adicCompletion E) * τ.val i i := by
    have hτd : τ.val = Matrix.diagonal fun i => τ.val i i := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · rw [hτ.1 i j hij, Matrix.diagonal_apply_ne _ hij]
    rw [Units.val_mul, GlobalTheory.CompanionTheory.FUMulPf.tdiag_val, hτd, Matrix.diagonal_mul_diagonal]
    simp
  have hg : γ.1 = (b * m) * (tdiag ϖ (wexp n l) * τ) * (b * m)⁻¹ := by
    rw [← em]; group
  rw [GlobalTheory.CompanionTheory.UnitarySide.charpoly_conj_diagonal (b * m) _ γ.1 _ hval hg, Polynomial.separable_prod_X_sub_C_iff]
  intro i j hij
  exact hy.injective (zpow_mul_inj hϖ (hτ.2 i) (hτ.2 j) hij)

theorem sepPowT : SepPowT := by
  intro E _ _ _ hU n d hd hm m w hT y hy
  obtain ⟨hs, hb, hϖ, hx⟩ := hm.T w hT
  have hx' : ∀ j, StrictAnti (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w j) ∧ Cone (lOf (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w j)) :=
    fun j => hx j.1 j.2
  obtain ⟨J', _, c', x', hx'', e1, -⟩ := GlobalTheory.CompanionTheory.MatchPow.pow_claim GlobalTheory.CompanionTheory.FUMulPf.fuMul GlobalTheory.CompanionTheory.DcosProduct.dcosMul hU hs 0
    hb hϖ (GlobalTheory.CompanionTheory.MatchLMPlaces.cc d w) (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w) hx' m
  have hKU : d.KU w = iwU n w (d.b w) := by simp [LocData.KU, hT]
  have hG : d.gU (m + 1) w y = (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) ^ (m + 1) *
      (GlobalTheory.CompanionTheory.MatchPow.alpha n w (d.b w) ^ m * ∑ j, c' j * fU n w (d.b w) (d.ϖ w) (lOf (x' j)) y) := by
    unfold LocData.gU
    rw [hKU, GlobalTheory.CompanionTheory.MatchLMPlaces.unitary_function_at_T d hT, GlobalTheory.CompanionTheory.MatchLMPlaces.lpow_scale, e1]
  rw [hG] at hy
  have hsum : ∑ j, c' j * fU n w (d.b w) (d.ϖ w) (lOf (x' j)) y ≠ 0 := fun h0 => hy (by rw [h0]; simp)
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact separable_of_fU hϖ (hx'' j).2 (right_ne_zero_of_mul hj)

end GlobalTheory.CompanionTheory.SepPow

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparablePowerTorusStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separable_power_torus : PositivityTheory.Rg.BcB.F.MLM.SepPowT := by
  first | exact @GlobalTheory.CompanionTheory.SepPow.sepPowT | exact GlobalTheory.CompanionTheory.SepPow.sepPowT | (intros; apply GlobalTheory.CompanionTheory.SepPow.sepPowT <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermStar
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermStar
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical Kronecker
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtAdj

section Generic

variable {H : Type} [Group H]

theorem rStab_conj (u : H → ℂ) : rStab (fun x => starRingEnd ℂ (u x)) = rStab u := by
  ext k
  constructor
  · intro hk x
    exact (starRingEnd ℂ).injective (hk x)
  · intro hk x
    show starRingEnd ℂ (u (x * k)) = starRingEnd ℂ (u x)
    rw [hk x]

theorem finsum_conj {α : Type} (g : α → ℂ) : ∑ᶠ q, starRingEnd ℂ (g q) = starRingEnd ℂ (∑ᶠ q, g q) :=
  (AddMonoidHom.map_finsum_of_injective (starRingEnd ℂ).toAddMonoidHom (starRingEnd ℂ).injective g).symm

theorem hint_conj (K : Subgroup H) (u : H → ℂ) :
    hint K (fun x => starRingEnd ℂ (u x)) = starRingEnd ℂ (hint K u) := by
  unfold hint
  rw [rStab_conj, map_mul, map_inv₀, map_natCast, finsum_conj]

theorem avg_conj (u : H → ℂ) : avg (fun x => starRingEnd ℂ (u x)) = starRingEnd ℂ (avg u) := by
  unfold avg
  rw [rStab_conj, map_mul, map_inv₀, map_natCast, finsum_conj]

end Generic

theorem det_lr {k : Type} [Field k] {a b : ℕ} (A : Matrix (Fin a) (Fin a) k) (B : Matrix (Fin b) (Fin b) k)
    (L : Matrix (Fin a) (Fin b) k →ₗ[k] Matrix (Fin a) (Fin b) k) (hL : ∀ X, L X = A * X * B) :
    LinearMap.det L = A.det ^ b * B.det ^ a := by
  let e : Matrix (Fin a) (Fin b) k ≃ₗ[k] (Fin a × Fin b → k) := (LinearEquiv.curry k k (Fin a) (Fin b)).symm
  have h : (e.toLinearMap ∘ₗ L ∘ₗ e.symm.toLinearMap) = Matrix.toLin' (A ⊗ₖ Bᵀ) := by
    apply LinearMap.ext
    intro v
    funext ⟨i, j⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hL, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.transpose_apply]
    show (A * (Matrix.of fun l c => v (l, c)) * B) i j = _
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [← LinearMap.det_conj L e, h, LinearMap.det_toLin', Matrix.det_kronecker, Matrix.det_transpose,
    Fintype.card_fin, Fintype.card_fin]

variable {E : Type} [Field E] [NumberField E]

theorem absHalf_one (w : Pl E) : absHalf w (1 : w.adicCompletion E) = 1 := by
  have h := GlobalTheory.LeviDesc.absHalf_mul E w 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  have h0 := GlobalTheory.LeviDesc.absHalf_ne_zero' w (1 : w.adicCompletion E)
  exact (mul_right_cancel₀ h0 (by rw [one_mul]; exact h)).symm

theorem absHalf_inv_mul (w : Pl E) {x : w.adicCompletion E} (hx : x ≠ 0) :
    absHalf w x⁻¹ * absHalf w x = 1 := by
  rw [← GlobalTheory.LeviDesc.absHalf_mul E w _ _ (inv_ne_zero hx) hx, inv_mul_cancel₀ hx, absHalf_one]

theorem conj_absHalf (w : Pl E) (x : w.adicCompletion E) : starRingEnd ℂ (absHalf w x) = absHalf w x := by
  unfold absHalf
  exact Complex.conj_ofReal _

variable [IsCMField E]

def negL {a b : ℕ} {w : Pl E} (m : GLw a w × GLw b w) :
    Matrix (Fin a) (Fin b) (w.adicCompletion E) →ₗ[w.adicCompletion E] Matrix (Fin a) (Fin b) (w.adicCompletion E) where
  toFun X := -(m.1.val * X * (m.2⁻¹).val)
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul, neg_add]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]

theorem det_inv_val {k : ℕ} {w : Pl E} (g : GLw k w) : (g⁻¹).val.det = (g.val.det)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]

theorem det_ne_zero {k : ℕ} {w : Pl E} (g : GLw k w) : g.val.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero

theorem v_det_negL {a b : ℕ} {w : Pl E} (m : GLw a w × GLw b w) :
    Valued.v (LinearMap.det (negL m)) = Valued.v (m.1.val.det ^ b / m.2.val.det ^ a) := by
  have h : LinearMap.det (negL m) = (-m.1.val).det ^ b * (m.2⁻¹).val.det ^ a :=
    det_lr _ _ _ fun X => by simp [negL, Matrix.neg_mul]
  rw [h, det_inv_val, Matrix.det_neg, Fintype.card_fin, div_eq_mul_inv, map_mul, map_mul, map_pow, map_mul, map_pow,
    map_pow, map_pow, map_inv₀, map_inv₀, map_pow, Valuation.map_neg, map_one, one_pow, one_mul, inv_pow]

theorem det_negL_ne_zero {a b : ℕ} {w : Pl E} (m : GLw a w × GLw b w) : LinearMap.det (negL m) ≠ 0 := by
  intro h0
  have h := v_det_negL m
  rw [h0, map_zero] at h
  exact div_ne_zero (pow_ne_zero _ (det_ne_zero m.1)) (pow_ne_zero _ (det_ne_zero m.2))
    ((Valuation.zero_iff _).1 h.symm)

theorem ct_adj {n a b : ℕ} (h : a + b = n) (w : Pl E) (F : GLw n w → ℂ)
    (hF : ∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' F) (m : GLw a w × GLw b w) :
    ct h w (fun y => starRingEnd ℂ (F y⁻¹)) m = starRingEnd ℂ (ct h w F m⁻¹) := by
  obtain ⟨hU, hcs⟩ := GlobalTheory.T.conjAverage_unipotent_locallyConstant_compactSupport E n a b h w F hF m⁻¹
  have hJ := GlobalTheory.T.normalisedMatrixIntegral_comp_linearEquiv_det E w a b (negL m)
    (fun X => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) F (blk h w m⁻¹ X)) (det_negL_ne_zero m) hU hcs
  have hpt : ∀ X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)),
      avg (fun k : GlobalTheory.LFun.KGL w (n := n) => starRingEnd ℂ (F ((((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k))⁻¹))) =
      starRingEnd ℂ (GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) F (blk h w m⁻¹ (negL m (Multiplicative.toAdd X)))) := by
    intro X
    unfold GlobalTheory.LeviDesc.cavg
    rw [← avg_conj]
    congr 1
    funext k
    have e : ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)⁻¹ =
        (k : GLw n w)⁻¹ * blk h w m⁻¹ (negL m (Multiplicative.toAdd X)) * k := by
      have e2 : blk h w m⁻¹ (negL m (Multiplicative.toAdd X)) = (blk h w m (Multiplicative.toAdd X))⁻¹ :=
        (CtLevel.blk_inv h w m _).symm
      rw [e2]
      group
    rw [e]
  have hD0 : m.1.val.det ^ b / m.2.val.det ^ a ≠ 0 :=
    div_ne_zero (pow_ne_zero _ (det_ne_zero m.1)) (pow_ne_zero _ (det_ne_zero m.2))
  have hinv : (m⁻¹).1.val.det ^ b / (m⁻¹).2.val.det ^ a = (m.1.val.det ^ b / m.2.val.det ^ a)⁻¹ := by
    rw [Prod.fst_inv, Prod.snd_inv, det_inv_val, det_inv_val, inv_pow, inv_pow, inv_div, div_eq_mul_inv, inv_inv, mul_comm,
      div_eq_mul_inv]
  have hc : absHalf w (LinearMap.det (negL m)) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) :=
    GlobalTheory.BCT.AbsHalfInv.absHalf_congr (v_det_negL m)
  have h1 : hint (intMat a b w) (fun X => avg fun k : GlobalTheory.LFun.KGL w (n := n) =>
        starRingEnd ℂ (F (((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)⁻¹))) =
      starRingEnd ℂ (hint (intMat a b w) fun X =>
        GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) F (blk h w m⁻¹ (negL m (Multiplicative.toAdd X)))) := by
    rw [← hint_conj]
    congr 1
    funext X
    exact hpt X
  have hJ' : (hint (intMat a b w) fun X =>
      GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) F (blk h w m⁻¹ (negL m (Multiplicative.toAdd X)))) =
      (absHalf w (LinearMap.det (negL m)) ^ 2)⁻¹ * hint (intMat a b w) (fun X =>
        GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) F (blk h w m⁻¹ (Multiplicative.toAdd X))) := hJ
  show absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * hint (intMat a b w) (fun X => avg fun k : GlobalTheory.LFun.KGL w (n := n) =>
        starRingEnd ℂ (F (((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)⁻¹))) =
      starRingEnd ℂ (absHalf w ((m⁻¹).1.val.det ^ b / (m⁻¹).2.val.det ^ a) * hint (intMat a b w) (fun X =>
        GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) F (blk h w m⁻¹ (Multiplicative.toAdd X))))
  rw [h1, hJ', hc, hinv, map_mul, map_mul, map_inv₀, map_pow, conj_absHalf, conj_absHalf]
  have hA := GlobalTheory.LeviDesc.absHalf_ne_zero' w (m.1.val.det ^ b / m.2.val.det ^ a)
  rw [eq_inv_of_mul_eq_one_left (absHalf_inv_mul w hD0)]
  field_simp

theorem mu_conj {K : Type} [Group K] (μ : K →* ℂˣ) (hμ : ∀ u, ‖((μ u : ℂˣ) : ℂ)‖ = 1) (x : K) :
    ((μ x⁻¹ : ℂˣ) : ℂ) = starRingEnd ℂ ((μ x : ℂˣ) : ℂ) := by
  rw [map_inv, Units.val_inv_eq_inv_val]
  exact Complex.inv_eq_conj (hμ x)

theorem ctStar : PositivityTheory.Rg.BcB.F.MLM.CtStar := by
  intro E _ _ _ n a ha w hw μ hμ f hf
  have hU : UL n w = ⊤ := if_pos hw
  funext m
  have hH := GlobalTheory.CompanionTheory.CtMulSplit.isHk_of_isHecke hU hf
  have hF : ∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' (fun y => f (toSub (UL n w) y)) :=
    ⟨GlobalTheory.LFun.KGL w (n := n), (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, hH.2.2.1, fun k hk x =>
      ⟨by simpa using hH.2.2.2 k hk 1 (Subgroup.one_mem _) x, by simpa using hH.2.2.2 1 (Subgroup.one_mem _) k hk x⟩⟩
  have hstar : (fun y => PositivityTheory.Rg.BcB.F.Eig.lstar f (toSub (UL n w) y)) =
      fun y => starRingEnd ℂ (f (toSub (UL n w) y⁻¹)) := by
    funext y
    show starRingEnd ℂ (f (toSub (UL n w) y)⁻¹) = _
    have e : (toSub (UL n w) y)⁻¹ = toSub (UL n w) y⁻¹ :=
      Subtype.ext (by rw [Subgroup.coe_inv, GlobalTheory.CompanionTheory.CtMulSplit.val_toSub hU, GlobalTheory.CompanionTheory.CtMulSplit.val_toSub hU])
    rw [e]
  show ((μ _ : ℂˣ) : ℂ) * ct _ w (fun y => PositivityTheory.Rg.BcB.F.Eig.lstar f (toSub (UL n w) y)) m =
    starRingEnd ℂ (((μ _ : ℂˣ) : ℂ) * ct _ w (fun y => f (toSub (UL n w) y)) m⁻¹)
  rw [hstar, ct_adj _ w (fun y => f (toSub (UL n w) y)) hF m, map_mul (starRingEnd ℂ)]
  congr 1
  rw [← mu_conj μ hμ]
  congr 2
  have hs : (((-1 : (w.adicCompletion E)ˣ) ^ (a * (n - a)))⁻¹) = (-1) ^ (a * (n - a)) := by
    rw [← inv_pow]
    simp
  simp only [Prod.fst_inv, Prod.snd_inv, map_inv, inv_pow, mul_inv, inv_inv, hs]

end GlobalTheory.CompanionTheory.CtAdj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermStarStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_star : PositivityTheory.Rg.BcB.F.MLM.CtStar := by
  first | exact @GlobalTheory.CompanionTheory.CtAdj.ctStar | exact GlobalTheory.CompanionTheory.CtAdj.ctStar | (intros; apply GlobalTheory.CompanionTheory.CtAdj.ctStar <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchLeviWordsOf
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchLMWordSOf
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcB.F.MLM (wordLS wordUS CtStar)
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MatchWordS

open GlobalTheory.CompanionTheory.MatchWord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem isHecke_lstar {w : Pl E} {f : UL n w → ℂ} (hf : IsHecke (KL n w) f) : IsHecke (KL n w) (lstar f) := by
  refine ⟨(hf.1.comp_homeomorph (Homeomorph.inv _)).comp_left (map_zero (starRingEnd ℂ)), fun k hk x => ⟨?_, ?_⟩⟩
  · simp only [lstar, _root_.mul_inv_rev, (hf.2 _ (inv_mem hk) _).2]
  · simp only [lstar, _root_.mul_inv_rev, (hf.2 _ (inv_mem hk) _).1]

def letU (d : LocData E n) (w : Pl E) (x : ℕ × Bool × Bool) : UL n w → ℂ :=
  if x.2.2 then lstar (d.hU w x.1) else d.hU w x.1

def letL (d : LocData E n) (a : ℕ) (ha : a ≤ n) (w : Pl E) (x : ℕ × Bool × Bool) : LM d.kap a (n - a) :=
  if x.2.2 then (d.hL a ha w x.1 x.2.1).adj else d.hL a ha w x.1 x.2.1

theorem word_ct (d : LocData E n) (a : ℕ) (ha : a ≤ n) {w : Pl E} (hCt : MT.CtMul) (hSt : CtStar) (hSp : SphComm) (hE : Unr E)
    (hd : d.Ok) (hG : d.Good w) (hN : ∀ u, ‖((d.μ w u : ℂˣ) : ℂ)‖ = 1) (l : List (ℕ × Bool × Bool)) :
    IsHecke (KL n w) (wordUS d w l) ∧ ∃ A B : UL n w → ℂ, IsHecke (KL n w) A ∧ IsHecke (KL n w) B ∧
      (wordLS d a ha w l).s w = ctMu (Nat.add_sub_cancel' ha) w (d.μ w) A ∧
      (wordLS d a ha w l).t w = ctMu (Nat.add_sub_cancel' ha) w (d.μ w) B ∧
      mconv (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) A) (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) B) =
        ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (wordUS d w l) := by
  have hG' := hG
  obtain ⟨hw, hT, hS₀, hBad, hμ⟩ := hG
  have hU : UL n w = ⊤ := if_pos hw
  set C := ctMu (Nat.add_sub_cancel' ha) w (d.μ w) with hC
  have conv : ∀ {f g : UL n w → ℂ}, IsHecke (KL n w) f → IsHecke (KL n w) g → IsHecke (KL n w) (lconv f g) :=
    fun hf hg => GlobalTheory.CompanionTheory.UnitaryWord.isHecke_lconv GlobalTheory.CompanionTheory.LocHecke.locAlg (GlobalTheory.CompanionTheory.MatchPowers.isLevel_KL n w) hf hg
  have mul : ∀ {f g : UL n w → ℂ}, IsHecke (KL n w) f → IsHecke (KL n w) g → C (lconv f g) = mconv (C f) (C g) :=
    fun hf hg => hCt E n a ha w hw (d.μ w) hμ _ _ hf hg
  have star : ∀ {f : UL n w → ℂ}, IsHecke (KL n w) f → lfStar (C f) = C (lstar f) :=
    fun hf => (hSt E n a ha w hw (d.μ w) hN _ hf).symm
  have hone : IsHecke (KL n w) (lone (KL n w)) := GlobalTheory.CompanionTheory.MatchUnit.isHecke_lone_KL hE
  have hunit : C (lone (KL n w)) = PositivityTheory.Rg.BcB.F.idem (K2 a (n - a) w) := GlobalTheory.CompanionTheory.MatchUnit.ctMu_lone _ hU _ hμ
  have hlev : d.lev a w = K2 a (n - a) w := by
    unfold LocData.lev
    rw [if_neg hT, if_neg (by simp [hS₀, hBad])]
  have hlev₂ : d.lev₂ a w = K2 a (n - a) w := by
    unfold LocData.lev₂
    rw [if_neg (by simp [hS₀, hBad])]
  have hes : (d.eL a).s w = C (lone (KL n w)) := by
    rw [hunit]
    show PositivityTheory.Rg.BcB.F.idem (d.lev a w) = _
    rw [hlev]
  have het : (d.eL a).t w = C (lone (KL n w)) := by
    rw [hunit]
    show PositivityTheory.Rg.BcB.F.idem (d.lev₂ a w) = _
    rw [hlev₂]
  have hstar1 : lfStar (C (lone (KL n w))) = C (lone (KL n w)) := by
    rw [hunit, PositivityTheory.Rg.BcB.F.LocComm.lfStar_idem]
  have hH : ∀ x, IsHecke (KL n w) (letU d w x) := by
    rintro ⟨k, intersection_update_fsHerm_neg_one, st⟩
    have hTk := isHecke_hU d hd hU k
    cases st
    · exact hTk
    · exact isHecke_lstar hTk
  have hck : ∀ k, d.hc a ha w k = C (d.hU w k) := fun k => hc_eq d a ha hμ k
  have hl0 : ∀ k st, (letL d a ha w (k, false, st)).s w = C (letU d w (k, false, st)) ∧
      (letL d a ha w (k, false, st)).t w = C (lone (KL n w)) := by
    intro k st
    have e : (d.hL a ha w k false).s w = d.hc a ha w k := by simp [LocData.hL]
    cases st
    · exact ⟨by simpa [letL, letU] using e.trans (hck k), het⟩
    · refine ⟨?_, ?_⟩
      · show lfStar ((d.hL a ha w k false).s w) = C (lstar (d.hU w k))
        rw [e, hck, star (isHecke_hU d hd hU k)]
      · show lfStar ((d.eL a).t w) = _
        rw [het, hstar1]
  have hl1 : ∀ k st, (letL d a ha w (k, true, st)).s w = C (lone (KL n w)) ∧
      (letL d a ha w (k, true, st)).t w = C (letU d w (k, true, st)) := by
    intro k st
    have e : (d.hL a ha w k true).t w = d.hc a ha w k := by simp [LocData.hL]
    cases st
    · exact ⟨hes, by simpa [letL, letU] using e.trans (hck k)⟩
    · refine ⟨?_, ?_⟩
      · show lfStar ((d.eL a).s w) = _
        rw [hes, hstar1]
      · show lfStar ((d.hL a ha w k true).t w) = C (lstar (d.hU w k))
        rw [e, hck, star (isHecke_hU d hd hU k)]
  induction l with
  | nil =>
    refine ⟨?_, lone (KL n w), lone (KL n w), hone, hone, hes, het, ?_⟩
    · show IsHecke (KL n w) ((KL n w : Set (UL n w)).indicator 1)
      rw [GlobalTheory.CompanionTheory.UnitaryWord.lone_KL] at hone
      exact hone
    · rw [← mul hone hone, lconv_lone_left hone, GlobalTheory.CompanionTheory.UnitaryWord.lone_KL]
      rfl
  | cons x l ih =>
    obtain ⟨hW, A, B, hA, hB, hs, ht, hm⟩ := ih
    obtain ⟨k, intersection_update_fsHerm_neg_one, st⟩ := x
    have hg := hH (k, intersection_update_fsHerm_neg_one, st)
    have hWc : wordUS d w ((k, intersection_update_fsHerm_neg_one, st) :: l) = lconv (letU d w (k, intersection_update_fsHerm_neg_one, st)) (wordUS d w l) := rfl
    have hLc : wordLS d a ha w ((k, intersection_update_fsHerm_neg_one, st) :: l) = (letL d a ha w (k, intersection_update_fsHerm_neg_one, st)).mul (wordLS d a ha w l) := rfl
    have key : mconv (C (lconv (letU d w (k, intersection_update_fsHerm_neg_one, st)) A)) (C B) = C (lconv (letU d w (k, intersection_update_fsHerm_neg_one, st)) (wordUS d w l)) := by
      rw [← mul (conv hg hA) hB, lconv_assoc hE hg hA hB, mul hg (conv hA hB), mul hA hB, hm, ← mul hg hW]
    refine ⟨hWc ▸ conv hg hW, ?_⟩
    rw [hWc, hLc]
    cases intersection_update_fsHerm_neg_one with
    | false =>
      obtain ⟨e₁, e₂⟩ := hl0 k st
      refine ⟨lconv (letU d w (k, false, st)) A, B, conv hg hA, hB, ?_, ?_, key⟩
      · show mconv ((letL d a ha w (k, false, st)).s w) ((wordLS d a ha w l).s w) = _
        rw [e₁, hs, ← mul hg hA]
      · show mconv ((letL d a ha w (k, false, st)).t w) ((wordLS d a ha w l).t w) = _
        rw [e₂, ht, ← mul hone hB, lconv_lone_left hB]
    | true =>
      obtain ⟨e₁, e₂⟩ := hl1 k st
      refine ⟨A, lconv (letU d w (k, true, st)) B, hA, conv hg hB, ?_, ?_, ?_⟩
      · show mconv ((letL d a ha w (k, true, st)).s w) ((wordLS d a ha w l).s w) = _
        rw [e₁, hs, ← mul hone hA, lconv_lone_left hA]
      · show mconv ((letL d a ha w (k, true, st)).t w) ((wordLS d a ha w l).t w) = _
        rw [e₂, ht, ← mul hg hB]
      · rw [← mul hA (conv hg hB), ← lconv_assoc hE hA hg hB, mul (conv hA hg) hB, mul hA hg,
          hSp E a (n - a) w (C A) (C (letU d w (k, true, st))) (isHecke_ctMu _ hU _ hμ hA) (isHecke_ctMu _ hU _ hμ hg),
          ← mul hg hA]
        exact key

theorem matchLMWordSOf : PositivityTheory.Rg.BcB.F.MLM.MatchLMWordSOf := by
  intro hS hCt hSt hSp _ E _ _ _ hE n d hd a ha w hG hN l
  have hP : w ∉ d.P := by simp [LocData.P, hG.2.1, hG.2.2.1]
  have htr : (wordLS d a ha w l).tr d.P d.one w = (wordLS d a ha w l).s w := if_neg hP
  obtain ⟨hW, A, B, -, -, hs, ht, hm⟩ := word_ct d a ha hCt hSt hSp hE hd hG hN l
  rw [htr, hs, ht, hm]
  have hμ := hG.2.2.2.2
  have hw := hG.1
  have h1 := hS E n a ha w hw (d.μ w) hμ _ hW 1 le_rfl
  have hone : IsHecke (KL n w) (lone (KL n w)) := GlobalTheory.CompanionTheory.MatchUnit.isHecke_lone_KL hE
  have e1 : lpow (KL n w) (wordUS d w l) 1 = wordUS d w l := lconv_lone_right hW
  have e2 : mconv (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (wordUS d w l))
      (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (lone (KL n w))) =
      ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (wordUS d w l) := by
    rw [← hCt E n a ha w hw (d.μ w) hμ _ _ hW hone, lconv_lone_right hW]
  rw [e1] at h1
  exact e2 ▸ h1

end GlobalTheory.CompanionTheory.MatchWordS

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchLeviWordsOf
namespace GlobalTheory.CompanionTheory.LeviMatchingWords

theorem matchLMWordSOf : PositivityTheory.Rg.BcB.F.MLM.MatchLMWordSOf := GlobalTheory.CompanionTheory.MatchWordS.matchLMWordSOf

end GlobalTheory.CompanionTheory.LeviMatchingWords
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchLeviWordsOfStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.match_levi_words_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMWordSOf := by
  first | exact @GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf | exact GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf | (intros; apply GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityInert
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityInert
noncomputable section

open NumberField IsDedekindDomain Polynomial
open GlobalTheory.BCT GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.MuInertPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem delta_indep {w : Pl E} (hw : ¬ IsSplitAt w) (μ μ' : (w.adicCompletion E)ˣ →* ℂˣ)
    (Q₁ Q₂ : (w.adicCompletion E)[X]) : delta w μ Q₁ Q₂ = delta w μ' Q₁ Q₂ := by
  simp only [delta, hw, if_false]

theorem match_indep {n a b : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w) (μ μ' : (w.adicCompletion E)ˣ →* ℂˣ)
    (f : UL n w → ℂ) (φ : GLw a w × GLw b w → ℂ) : Match n a b w μ f φ ↔ Match n a b w μ' f φ := by
  unfold Match
  simp only [delta_indep hw μ μ']

theorem muInert : PositivityTheory.Rg.BcB.F.MLM.MuInert := by
  intro E _ _ _ n a b w hw μ μ' f φ
  exact match_indep hw μ μ' f φ

end GlobalTheory.CompanionTheory.MuInertPlace
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityInertStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_inert : PositivityTheory.Rg.BcB.F.MLM.MuInert := by
  first | exact @GlobalTheory.CompanionTheory.MuInertPlace.muInert | exact GlobalTheory.CompanionTheory.MuInertPlace.muInert | (intros; apply GlobalTheory.CompanionTheory.MuInertPlace.muInert <;> assumption)
end
end

namespace PositivityTheory.Rg.BcB.F.MLM

theorem matchLMIdOf : MatchLMIdOf := GlobalTheory.T.matching_identity_of
theorem matchLMUnitOf : MatchLMUnitOf := GlobalTheory.T.matching_unit_of

theorem muInert : MuInert := GlobalTheory.T.multiplicity_inert
theorem regPowT : RegPowT := GlobalTheory.T.regular_power_torus
theorem sepPowT : SepPowT := GlobalTheory.T.separable_power_torus
theorem ctStar : CtStar := GlobalTheory.T.constant_term_star
theorem matchLMWordSOf : MatchLMWordSOf := GlobalTheory.T.match_levi_words_of

end PositivityTheory.Rg.BcB.F.MLM
