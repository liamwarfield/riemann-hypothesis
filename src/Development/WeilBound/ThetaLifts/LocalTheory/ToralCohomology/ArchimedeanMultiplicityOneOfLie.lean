module

public import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ParZero
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreLM
public import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ExistsTorus
public import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.EvIHalfTrace
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLFock
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLines
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.PolRange

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ArchimedeanMultiplicityOneOf
section -- merged from Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.EmbeddingTransposeVectorZero
section -- merged from Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.PiInfUnitNe
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open FockH1Action (Mat Ix fockAct1 fockAct2 cPair)
open Formalism.BasicNotions.TH (upq Jm)
open PositivityTheory.KReal ReciprocityTheory.ChartRestriction.G.ThK.Real

namespace PositivityTheory.ThKG.CayleyTransformDarboux

structure Dic : Prop where
  laws : ActsLaws
  fock : FockEx
  range : PolRange
  fst : LieFirst
  snd : LieSecond
  line : LineEx
  frame : FrameEx
  even_im_hermitian_sub : Parity

theorem Jm_eq (r s : ℕ) : Jm r s = Matrix.diagonal (Sum.elim (fun _ => 1) fun _ => -1) := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> simp [Jm, Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply, neg_ite]

theorem Jm_sq (r s : ℕ) : Jm r s * Jm r s = 1 := by
  rw [Jm_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; cases a <;> simp

theorem Jm_star (r s : ℕ) : (Jm r s)ᴴ = Jm r s := by
  rw [Jm_eq, Matrix.diagonal_conjTranspose]
  congr 1; funext a; cases a <;> simp

theorem upq_split {r s : ℕ} (Y : Mat r s) : ∃ Y₁ ∈ upq r s, ∃ Y₂ ∈ upq r s, Y = Y₁ + Complex.I • Y₂ := by
  have e1 : ∀ Z : Mat r s, Z * Jm r s * Jm r s = Z := fun Z => by rw [Matrix.mul_assoc, Jm_sq, Matrix.mul_one]
  have e2 : ∀ Z : Mat r s, Jm r s * (Jm r s * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, Jm_sq, Matrix.one_mul]
  refine ⟨(1 / 2 : ℂ) • (Y - Jm r s * Yᴴ * Jm r s), ?_, (-Complex.I / 2) • (Y + Jm r s * Yᴴ * Jm r s), ?_, ?_⟩
  · simp only [upq, Set.mem_ofPred_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Jm_star,
      Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_assoc, Jm_sq, Matrix.mul_one, e2]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp]
    module
  · simp only [upq, Set.mem_ofPred_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Jm_star,
      Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_assoc, Jm_sq, Matrix.mul_one, e2]
    rw [show star (-Complex.I / 2 : ℂ) = Complex.I / 2 by simp]
    module
  · rw [smul_smul, show Complex.I * (-Complex.I / 2) = 1 / 2 by linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I]
    module

theorem zero_upq (r s : ℕ) : (0 : Mat r s) ∈ upq r s := by simp [upq]

theorem single_upq {ι : Type} [DecidableEq ι] {r s : ℕ} (w : ι) {Y : Mat r s} (h : Y ∈ upq r s) (i : ι) :
    (Pi.single w Y : ι → Mat r s) i ∈ upq r s := by
  by_cases e : i = w
  · subst e; simpa using h
  · simpa [Pi.single_eq_of_ne e] using zero_upq r s

def sumL {ι P : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup P] [Module ℂ P] {r s : ℕ}
    (aP : ι → Mat r s →ₗ[ℂ] Module.End ℂ P) : (ι → Mat r s) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] _ : ι, P) :=
  ∑ w, (PiTensorProduct.mapMultilinear ℂ (fun _ : ι => P) (fun _ => P)).toLinearMap (fun _ => LinearMap.id) w ∘ₗ aP w ∘ₗ
    LinearMap.proj w

theorem sumL_eq {ι P : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup P] [Module ℂ P] {r s : ℕ}
    (aP : ι → Mat r s →ₗ[ℂ] Module.End ℂ P) (Y : ι → Mat r s) :
    sumL aP Y = sumPl (V := fun _ => P) fun i => aP i (Y i) := by
  rw [sumL, LinearMap.sum_apply]; rfl

theorem ker_stable {ι V : Type} [AddCommGroup V] [Module ℂ V] {r s : ℕ} (L : (ι → Mat r s) →ₗ[ℂ] Module.End ℂ V)
    (N N' : Submodule ℂ V) (h : ∀ Y, (∀ w, Y w ∈ upq r s) → ∀ x ∈ N, L Y x ∈ N') (Y) : ∀ x ∈ N, L Y x ∈ N' := by
  choose Y₁ h₁ Y₂ h₂ e using fun w => upq_split (Y w)
  intro x hx
  rw [show Y = Y₁ + Complex.I • Y₂ from funext e, map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  exact add_mem (h _ h₁ x hx) (N'.smul_mem _ (h _ h₂ x hx))

theorem exists_act {A V M : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    (L : A →ₗ[ℂ] Module.End ℂ V) (q : V →ₗ[ℂ] M) (hq : Function.Surjective q)
    (h : ∀ Y, ∀ x ∈ LinearMap.ker q, L Y x ∈ LinearMap.ker q) :
    ∃ act : A →ₗ[ℂ] Module.End ℂ M, ∀ Y t, act Y (q t) = q (L Y t) := by
  choose a ha using fun Y => exists_factor q hq (q ∘ₗ L Y) (h Y)
  refine ⟨⟨⟨a, fun X Y => LinearMap.ext fun m => ?_⟩, fun c X => LinearMap.ext fun m => ?_⟩, ha⟩
  · obtain ⟨t, rfl⟩ := hq m
    simp [ha]
  · obtain ⟨t, rfl⟩ := hq m
    simp [ha]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_map {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem piInf_unit_ne {w : InfinitePlace F} (τ : EmbOver E w) (z : (AE F E)ˣ) : piInf τ (z : AE F E) ≠ 0 := fun e => by
  have := congrArg (piInf τ) z.mul_inv
  rw [map_mul, e, zero_mul, map_one] at this
  exact zero_ne_one this

theorem hasExp_div (τ : ∀ w : InfinitePlace F, EmbOver E w) {χ χ' : Chr F E} {m m' : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (h' : HasExp τ χ' m') : HasExp τ (χ / χ') (fun w => m w - m' w) := by
  intro z hz
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h0 := piInf_unit_ne (τ w) z
  rw [zpow_sub₀ (div_ne_zero h0 (by exact_mod_cast norm_ne_zero_iff.2 h0))]

theorem actsD_zero {κ κ' : Type} [Fintype κ] {G : Type} [Monoid G] (om : G →* Module.End ℂ ((κ → AF F) → ℂ)) (g : ℝ → G) :
    ActsD (evI F) (fun t => om (g t)) (0 : SInf F κ) (0 : SInf F κ) := by
  intro r _ x
  have : tens (evI F) (0 : SInf F κ) r = 0 := by funext y; simp [tens]
  simp only [this, map_zero, Pi.zero_apply]
  exact hasDerivAt_const _ _

def lamW (B : Base F E) (P Q R S : ℕ) (w : InfinitePlace F) : Ix R S → ℚ
  | .inl k => (if (k : ℕ) < P then ((B.mα w - B.mβ w : ℤ) : ℚ) / 2 - cPair R S else 0) + cPair P Q + (B.mβ w : ℚ) / 2
  | .inr l => (if (l : ℕ) < Q then ((B.mα w - B.mβ w : ℤ) : ℚ) / 2 + cPair R S else 0) - cPair P Q + (B.mβ w : ℚ) / 2

theorem exists_mod (hD : Dic) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om om'} {Rm : RealMaps F a a'}
    (hT : IsTriple B G X om om') (hR : IsRealMaps B G om om' Rm) {R S : ℕ} (eR : R + G.p + G.q = a + a') (eS : S = G.p + G.q)
    (C : InfinitePlace F → Matrix (Fin (a + a')) (Ix R S) ℂ)
    (hC : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w)) (hCθ : ∀ w, G.W.θ w * C w = C w * Jm R S) :
    ∃ (act : (InfinitePlace F → Mat R S) →ₗ[ℂ] Module.End ℂ Rm.Pi) (f₀ : Rm.Pi),
      HWMod act (fun w c => (lamW B (a - G.p) G.p R S w c : ℂ)) f₀ ∧
      ∀ γ ∈ Lines σ G.W, ∀ Y, IsGen B.emb C γ Y → ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ : SInf F _,
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ Rm.p f₁ = act Y (Rm.p f) := by
  have par := hD.even_im_hermitian_sub F E σ B a a' G X om om' hT
  obtain ⟨hb, hg, hc, hw, -⟩ := hT
  have e1 := hg.eBig
  have e2 := hg.aBig
  obtain ⟨d2, hd2⟩ := hg.even
  choose A hA hAθ using fun w => hD.frame _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map, one_smul]; exact hA w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC⟩
  obtain ⟨Φ, hΦ⟩ := hD.fock F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hD.range F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  have hW2 := hD.snd F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1 hc.expβ
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hW1 := hD.fst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
    (hasExp_div B.emb hc.expβ hc.expα)
  have mem : ∀ T, Φ T ∈ G.M.Pol B.ψ B.emb := fun T => hr ▸ LinearMap.mem_range_self Φ T
  let q := Rm.p ∘ₗ Φ
  have hq : Function.Surjective q := by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, hr]; exact hR.quot.onto
  let aP := fun w : InfinitePlace F => twAct (a - G.p) G.p R S ((B.mβ w : ℂ) / 2)
  let a1 : InfinitePlace F → Mat (a - G.p) G.p →ₗ[ℂ] Module.End ℂ (FockH1Action.Pol (a - G.p) G.p R S) := fun w =>
    fockAct1 _ _ _ _ + ((((B.mβ w - B.mα w : ℤ) : ℂ) / 2) • Matrix.traceLinearMap _ ℂ ℂ).smulRight 1
  have s2 : ∀ γ ∈ Lines σ G.W, ∀ Y, IsGen B.emb C γ Y → ∀ T,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ T) (Φ (sumL aP Y T)) := fun γ hγ Y hY T => by
    rw [sumL_eq]
    exact (hD.laws F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) (hW2 γ hγ Y hY T)
  have s1 : ∀ Y T, q (sumL a1 Y T) = 0 := fun Y T => by
    refine ker_stable (sumL a1) ⊤ (LinearMap.ker q) (fun Y hY T _ => ?_) Y T trivial
    obtain ⟨γ, hγ, hgen⟩ := hD.line F E σ _ _ _ B.emb _ 1 A hb.cm hA1 Y hY
    rw [sumL_eq]
    exact hR.quot.lie γ hγ _ (mem T) _ ((hD.laws F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) (hW1 γ hγ Y hgen T))
  obtain ⟨act, ha⟩ := exists_act (sumL aP) q hq (ker_stable _ _ _ fun Y hY T hT => by
    obtain ⟨γ, hγ, hgen⟩ := hD.line F E σ _ _ _ B.emb _ Complex.I C hb.cm hC Y hY
    exact (hR.lie γ hγ _ (mem T) 0 (zero_mem _) _ 0 (s2 γ hγ Y hgen T) (actsD_zero (κ' := Unit) om' _)
      (hT.trans (map_zero _).symm)).trans (map_zero _))
  have side : ∀ w, Side (lamW B (a - G.p) G.p R S w) (ThC (a - G.p) G.p R S ((((B.mα w - B.mβ w : ℤ) : ℚ) / 2 : ℚ) : ℂ))
      (thAct _ _ _ _ _ ((B.mβ w : ℂ) / 2)) := fun w => by
    obtain ⟨k, hk⟩ := par w
    have hκ := hg.kappa w
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k - d2 + S by omega)
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k + d2 - S by omega)
    have hRq : (R : ℚ) + S = d2 + d2 := by exact_mod_cast (show R + S = d2 + d2 by omega)
    have hkq : ((B.mα w - B.mβ w : ℤ) : ℚ) / 2 = k := by rw [hk]; push_cast; ring
    have hn' : (k : ℚ) - d2 + S = n := by exact_mod_cast hn
    have hm' : (k : ℚ) + d2 - S = m := by exact_mod_cast hm
    have h1 : ((B.mα w - B.mβ w : ℤ) : ℚ) / 2 = n + cPair R S := by rw [hkq, cPair]; linarith
    have h2 : ((B.mα w - B.mβ w : ℤ) : ℚ) / 2 = m - cPair R S := by rw [hkq, cPair]; linarith
    have b1 : (G.p : ℚ) < ((a - G.p : ℕ) : ℚ) := by exact_mod_cast (show G.p < a - G.p by omega)
    have b2 : (((a - G.p : ℕ) : ℚ)) < m + G.p := by exact_mod_cast (show a - G.p < m + G.p by omega)
    have n0 : 0 < n := by omega
    have m0 : 0 < m := by omega
    have := side_of _ ((B.mβ w : ℂ) / 2) _ ((B.mβ w : ℚ) / 2) rfl (by push_cast; rfl) _
      (comb_pos (p := a - G.p) (q := G.p) (r := R) (s := S) (by omega) (by omega) n0 m0 _ _ h1 h2
        (by rw [cPair]; have : (0 : ℚ) ≤ n := by positivity
            linarith) (by rw [cPair]; linarith))
      (nontrivial_of_pair _ _ rfl (pair_pos (by omega) (by omega) n0 m0 _ h1 h2))
    convert this using 1
    funext c
    rcases c with c | c <;> simp only [lamW, laPos] <;> split_ifs <;> linarith
  obtain ⟨f₀, hf₀⟩ := tens_hw _ _ side aP (fun w => lie_tw _ _ _ _ _) (fun w => thMkC _ _ _ _ _)
    (fun w => Submodule.mkQ_surjective _) (fun w Y y => (thAct_mk _ _ _ _ _ _ Y y).symm) q hq
    (fun w y x hx => by
      have hx' := (Submodule.Quotient.mk_eq_zero _).1 hx
      refine (iSup_le ?_ : _ ≤ LinearMap.ker (q ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap y w)) hx'
      rintro Z _ ⟨x, rfl⟩
      have := s1 (Pi.single w Z) (PiTensorProduct.tprod ℂ (Function.update y w x))
      rw [sumL_eq, sumPl_single, Function.update_idem, Function.update_self] at this
      refine Eq.trans ?_ this
      simp only [LinearMap.comp_apply, MultilinearMap.toLinearMap_apply]
      congr 3
      simp only [a1, act1, chiTr, LinearMap.add_apply, LinearMap.smul_apply, one_apply_eq_self,
        LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, smul_eq_mul, sub_eq_add_neg, ← neg_smul]
      congr 2
      push_cast; ring)
    act (fun Y t => by rw [ha, sumL_eq])
  refine ⟨act, f₀, hf₀, fun γ hγ Y hY f hf => ?_⟩
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  exact ⟨_, s2 γ hγ Y hY T, (ha Y T).symm⟩

end PositivityTheory.ThKG.CayleyTransformDarboux

end
end

noncomputable section

open scoped Matrix Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open FockH1Action (Mat Ix sameBlock posC)
open Formalism.BasicNotions.TH (upq Jm)

namespace PositivityTheory.ThKG.CayleyTransformDarboux

section Exp

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem hasSum_exp (A : Matrix I I ℂ) (v : I → ℂ) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • (A ^ n *ᵥ v)) (NormedSpace.exp A *ᵥ v) := by
  letI := Matrix.linftyOpNormedRing (n := I) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := I) (R := ℂ) (α := ℂ)
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  let L : Matrix I I ℂ →ₗ[ℂ] (I → ℂ) := (Matrix.mulVecBilin ℂ ℂ).flip v
  have := h.map L L.continuous_of_finiteDimensional
  convert (preTransparency := .reducible) this using 1
  · funext n
    exact (Matrix.smul_mulVec _ _ _).symm
  · rfl

theorem exp_int {A : Matrix I I ℂ} {B : Matrix J J ℂ} {P : Matrix I J ℂ} (h : A * P = P * B) (u : J → ℂ) :
    NormedSpace.exp A *ᵥ (P *ᵥ u) = P *ᵥ (NormedSpace.exp B *ᵥ u) := by
  have hn : ∀ n : ℕ, A ^ n * P = P * B ^ n := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, pow_succ, Matrix.mul_assoc]
  have h2 := (hasSum_exp B u).map P.mulVecLin P.mulVecLin.continuous_of_finiteDimensional
  refine (hasSum_exp A _).unique ?_
  simpa [Function.comp_def, hn, Matrix.mulVec_smul] using h2

theorem exp_eig {A : Matrix I I ℂ} {v : I → ℂ} {c : ℂ} (h : A *ᵥ v = c • v) : NormedSpace.exp A *ᵥ v = Complex.exp c • v := by
  have hn : ∀ n : ℕ, A ^ n *ᵥ v = c ^ n • v := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
  refine (hasSum_exp A v).unique ?_
  have := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).smul_const v
  rw [← Complex.exp_eq_exp_ℂ] at this
  simpa [hn, smul_smul] using this

theorem exp_nil {A : Matrix I I ℂ} {v : I → ℂ} (h : A *ᵥ (A *ᵥ v) = 0) : NormedSpace.exp A *ᵥ v = v + A *ᵥ v := by
  refine (hasSum_exp A v).unique ?_
  have := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (f := fun n : ℕ => ((n.factorial : ℂ))⁻¹ • (A ^ n *ᵥ v)) (s := Finset.range 2) (fun n hn => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show 2 ≤ n from not_lt.1 (mt Finset.mem_range.2 hn))
      rw [pow_succ, pow_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero, smul_zero])
  simpa [Finset.sum_range_succ] using this

end Exp

variable {R S R₁ S₁ : ℕ}

def sg : Ix R S → ℂ := Sum.elim (fun _ => 1) fun _ => -1

theorem Jm_sg (r s : ℕ) : Jm r s = Matrix.diagonal sg := Jm_eq r s

theorem star_sg (a : Ix R S) : star (sg a) = sg a := by cases a <;> simp [sg]

theorem sg_sq (a : Ix R S) : sg a * sg a = 1 := by cases a <;> simp [sg]

def Emb.P (m : Emb R S R₁ S₁) : Matrix (Ix R S) (Ix R₁ S₁) ℂ := fun a b => if a = m.e b then 1 else 0

def Emb.x (m : Emb R S R₁ S₁) : Ix R S → ℂ := Pi.single (.inl m.i) 1 + Pi.single (.inr m.j) 1

def Emb.y (m : Emb R S R₁ S₁) : Ix R S → ℂ := Pi.single (.inl m.i) 1 - Pi.single (.inr m.j) 1

def embA (R S : ℕ) : Emb (R + 1) (S + 1) R S where
  e := Sum.map Fin.succ Fin.succ
  i := 0
  j := 0
  ε := 1
  ε_ne := one_ne_zero
  inj := (Fin.succ_injective _).sumMap (Fin.succ_injective _)
  cover := by
    rintro (a | a) <;> refine Fin.cases ?_ (fun b => ?_) a
    exacts [.inl rfl, .inr (.inr ⟨.inl b, rfl⟩), .inr (.inl rfl), .inr (.inr ⟨.inr b, rfl⟩)]
  ne_i := by rintro (b | b) <;> simp [Fin.succ_ne_zero]
  ne_j := by rintro (b | b) <;> simp [Fin.succ_ne_zero]
  sb := by rintro (a | a) (b | b) <;> simp [sameBlock]
  pos := by rintro (a | a) (b | b) <;> simp [posC]
  ext := by rintro a (b | b) (rfl | rfl) <;> simp [posC, sameBlock] <;> norm_num

def embB (R S : ℕ) : Emb (R + 1) (S + 1) R S where
  e := Sum.map Fin.castSucc Fin.castSucc
  i := Fin.last R
  j := Fin.last S
  ε := -1
  ε_ne := by norm_num
  inj := (Fin.castSucc_injective _).sumMap (Fin.castSucc_injective _)
  cover := by
    rintro (a | a) <;> refine Fin.lastCases ?_ (fun b => ?_) a
    exacts [.inl rfl, .inr (.inr ⟨.inl b, rfl⟩), .inr (.inl rfl), .inr (.inr ⟨.inr b, rfl⟩)]
  ne_i := by rintro (b | b) <;> simp [Fin.castSucc_ne_last]
  ne_j := by rintro (b | b) <;> simp [Fin.castSucc_ne_last]
  sb := by rintro (a | a) (b | b) <;> simp [sameBlock]
  pos := by rintro (a | a) (b | b) <;> simp [posC]
  ext := by rintro a (b | b) (rfl | rfl) <;> simp [posC, sameBlock, Fin.castSucc_lt_last] <;> norm_num

theorem sg_embA (R S : ℕ) (b) : sg ((embA R S).e b) = sg b := by cases b <;> rfl

theorem sg_embB (R S : ℕ) (b) : sg ((embB R S).e b) = sg b := by cases b <;> rfl

theorem Emb.embeddingMatrix_mulVec (m : Emb R S R₁ S₁) (u : Ix R₁ S₁ → ℂ) :
    (m.P *ᵥ u) (.inl m.i) = 0 ∧ (m.P *ᵥ u) (.inr m.j) = 0 ∧ ∀ b, (m.P *ᵥ u) (m.e b) = u b := by
  refine ⟨?_, ?_, fun b => ?_⟩ <;> simp [Emb.P, Matrix.mulVec, dotProduct, (m.ne_i _).symm, (m.ne_j _).symm, m.inj.eq_iff]

theorem Emb.tP (m : Emb R S R₁ S₁) (v : Ix R S → ℂ) (b) : (m.Pᵀ *ᵥ v) b = v (m.e b) := by
  simp [Emb.P, Matrix.mulVec, dotProduct]

theorem Emb.embedding_transpose_vector_zero (m : Emb R S R₁ S₁) : m.Pᵀ *ᵥ m.x = 0 := by
  funext b; simp [m.tP, Emb.x, Pi.single_eq_of_ne (m.ne_i b), Pi.single_eq_of_ne (m.ne_j b)]

theorem Emb.transpose_mulVec_y_eq_zero (m : Emb R S R₁ S₁) : m.Pᵀ *ᵥ m.y = 0 := by
  funext b; simp [m.tP, Emb.y, Pi.single_eq_of_ne (m.ne_i b), Pi.single_eq_of_ne (m.ne_j b)]

theorem Emb.tPP (m : Emb R S R₁ S₁) : m.Pᵀ * m.P = 1 := by
  ext a b; simp [Emb.P, Matrix.mul_apply, m.inj.eq_iff, Matrix.one_apply, eq_comm]

theorem Emb.conj_single (m : Emb R S R₁ S₁) (a b) : m.P * Matrix.single a b (1 : ℂ) * m.Pᵀ = Matrix.single (m.e a) (m.e b) 1 := by
  ext c d
  simp only [Matrix.mul_apply, Matrix.single_apply, Emb.P, Matrix.transpose_apply]
  rw [Finset.sum_eq_single b, Finset.sum_eq_single a] <;> simp +contextual [eq_comm, ite_and]
  split_ifs <;> rfl

theorem Emb.JP (m : Emb R S R₁ S₁) (hs : ∀ b, sg (m.e b) = sg b) : Jm R S * m.P = m.P * Jm R₁ S₁ := by
  ext a b
  rw [Jm_sg, Jm_sg, Matrix.diagonal_mul, Matrix.mul_diagonal, Emb.P]
  split_ifs with h
  · rw [h, hs, mul_comm]
  · simp

theorem Emb.conj_upq (m : Emb R S R₁ S₁) (hs : ∀ b, sg (m.e b) = sg b) {Y : Mat R₁ S₁} (h : Y ∈ upq R₁ S₁) :
    m.P * Y * m.Pᵀ ∈ upq R S := by
  have h1 : m.Pᴴ = m.Pᵀ := by ext a b; simp [Emb.P]
  have h2 : m.Pᵀᴴ = m.P := by ext a b; simp [Emb.P]
  have h3 : m.Pᵀ * Jm R S = Jm R₁ S₁ * m.Pᵀ := by
    have := congrArg Matrix.conjTranspose (m.JP hs)
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_star, Jm_star, h1] at this
  have h4 : Yᴴ * Jm R₁ S₁ + Jm R₁ S₁ * Y = 0 := h
  change (m.P * Y * m.Pᵀ)ᴴ * _ + _ = 0
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, h1, h2]
  calc _ = m.P * (Yᴴ * Jm R₁ S₁ + Jm R₁ S₁ * Y) * m.Pᵀ := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h3]
        rw [← Matrix.mul_assoc (Jm R S), m.JP hs, Matrix.mul_assoc]
    _ = 0 := by rw [h4]; simp

theorem single_mulVec' (a b : Ix R S) (v : Ix R S → ℂ) : Matrix.single a b (1 : ℂ) *ᵥ v = v b • Pi.single a 1 := by
  funext c
  by_cases e : c = a
  · subst e; simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, Ne.symm e, Pi.single_eq_of_ne e]

theorem J_single (a b : Ix R S) : Jm R S * Matrix.single a b (1 : ℂ) = sg a • Matrix.single a b 1 := by
  ext c d; rw [Jm_sg, Matrix.diagonal_mul]; simp only [Matrix.smul_apply, Matrix.single_apply]; split_ifs with h <;> simp [h]

theorem single_J (a b : Ix R S) : Matrix.single a b (1 : ℂ) * Jm R S = sg b • Matrix.single a b 1 := by
  ext c d; rw [Jm_sg, Matrix.mul_diagonal]; simp only [Matrix.smul_apply, Matrix.single_apply]; split_ifs with h <;> simp [h]

theorem sg_l (i : Fin R) : sg (.inl i : Ix R S) = 1 := rfl

theorem sg_r (i : Fin S) : sg (.inr i : Ix R S) = -1 := rfl

def hf {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (u v : Fin d → ℂ) : ℂ := u ⬝ᵥ M *ᵥ star v

theorem gram_apply {d : ℕ} {I : Type} (M : Matrix (Fin d) (Fin d) ℂ) (C : Matrix (Fin d) I ℂ) (a b : I) :
    (Cᵀ * M * C.map star) a b = hf M (fun r => C r a) (fun r => C r b) := by
  rw [Matrix.mul_assoc]; rfl

theorem exists_frame (m : Emb R S R₁ S₁) (hs : ∀ b, sg (m.e b) = sg b) {d d₁ : ℕ} (hd : d = R + S)
    {M θ : Matrix (Fin d) (Fin d) ℂ} {M₁ θ₁ : Matrix (Fin d₁) (Fin d₁) ℂ} (hM : ∀ i j, M j i = star (M i j)) (hθ : IsCartan M θ)
    {x y : Fin d → ℂ} {ι : Matrix (Fin d) (Fin d₁) ℂ} (x0 : x ≠ 0) (xx : hf M x x = 0) {c : ℂ} (c0 : c ≠ 0) (hy : y = c • θ *ᵥ x)
    (ox : ∀ k, hf M (fun r => ι r k) x = 0) (oy : ∀ k, hf M (fun r => ι r k) y = 0) (hg : ιᵀ * M * ι.map star = M₁)
    (hθι : θ * ι = ι * θ₁) {C₁ : Matrix (Fin d₁) (Ix R₁ S₁) ℂ} (hC₁ : IsFrame M₁ C₁) (hθ₁ : θ₁ * C₁ = C₁ * Jm R₁ S₁) :
    ∃ (C : Matrix (Fin d) (Ix R S) ℂ) (n n' : ℂ), IsFrame M C ∧ θ * C = C * Jm R S ∧ n ≠ 0 ∧ x = n • C *ᵥ m.x ∧
      y = n' • C *ᵥ m.y ∧ C * m.P = ι * C₁ := by
  have herm : ∀ u v, hf M v u = star (hf M u v) := fun u v => by
    simp only [hf, dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum, ← hM]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have iso : ∀ u v, hf M (θ *ᵥ u) (θ *ᵥ v) = hf M u v := fun u v => by
    conv_rhs => rw [← hθ.2.1]
    rw [hf, hf, show star (θ *ᵥ v) = θ.map star *ᵥ star v by
      funext i; simp [Matrix.mulVec, dotProduct, star_sum], Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec u, Matrix.vecMul_transpose]
  have θθ : ∀ u, θ *ᵥ (θ *ᵥ u) = u := fun u => by rw [Matrix.mulVec_mulVec, hθ.1, Matrix.one_mulVec]
  have addl : ∀ u u' v (s : ℂ), hf M (u + s • u') v = hf M u v + s * hf M u' v := fun u u' v s => by simp [hf]
  have addr : ∀ u v v' (s : ℂ), hf M u (v + s • v') = hf M u v + star s * hf M u v' := fun u v v' s => by
    simp [hf, Matrix.mulVec_add, Matrix.mulVec_smul]
  have sml : ∀ u v (s : ℂ), hf M (s • u) v = s * hf M u v := fun u v s => by simp [hf]
  have smr : ∀ u v (s : ℂ), hf M u (s • v) = star s * hf M u v := fun u v s => by simp [hf, Matrix.mulVec_smul]
  set z := θ *ᵥ x with hz
  have zz : hf M z z = 0 := (iso x x).trans xx
  have zx : hf M x z = hf M z x := by rw [← iso x z, hz, θθ]
  set k := (hf M z x).re with hk
  have k0 : 0 < k := hθ.2.2 x x0
  have zk : hf M z x = k := by
    have := herm z x
    rw [zx] at this
    exact (Complex.conj_eq_iff_re.1 this.symm).symm
  set N : ℂ := (((Real.sqrt (2 * k))⁻¹ : ℝ) : ℂ) with hN
  have sN : star N = N := Complex.conj_ofReal _
  have NN : N * N * (2 * k) = 1 := by
    rw [hN]; norm_cast
    rw [← mul_inv, Real.mul_self_sqrt (by positivity), inv_mul_cancel₀ (by positivity)]
  have N0 : N ≠ 0 := fun e => by rw [e] at NN; simp at NN
  have oz : ∀ k, hf M (fun r => ι r k) z = 0 := fun k => by
    have := oy k
    rw [hy, smr, mul_eq_zero] at this
    exact this.resolve_left (star_ne_zero.2 c0)
  have col : ∀ (v) (b), (∀ k, hf M (fun r => ι r k) v = 0) → hf M (fun r => (ι * C₁) r b) v = 0 := fun v b h => by
    have : hf M (fun r => (ι * C₁) r b) v = ∑ k, C₁ k b * hf M (fun r => ι r k) v := by
      simp only [hf, dotProduct, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    simp [this, h]
  let cl : Ix R S → Fin d → ℂ := fun a => if a = .inl m.i then N • (x + (1 : ℂ) • z) else if a = .inr m.j then
    N • (x + (-1 : ℂ) • z) else Function.extend m.e (fun b r => (ι * C₁) r b) 0 a
  have ci : cl (.inl m.i) = N • (x + (1 : ℂ) • z) := if_pos rfl
  have cj : cl (.inr m.j) = N • (x + (-1 : ℂ) • z) := by simp [cl]
  have ce : ∀ b, cl (m.e b) = fun r => (ι * C₁) r b := fun b => by
    simp only [cl, if_neg (m.ne_i b), if_neg (m.ne_j b), m.inj.extend_apply]
  have o1 : ∀ b (s : ℂ), hf M (fun r => (ι * C₁) r b) (N • (x + s • z)) = 0 := fun b s => by
    rw [smr, addr, col _ b ox, col _ b oz]; simp
  have gram : (Matrix.of fun r a => cl a r)ᵀ * M * (Matrix.of fun r a => cl a r).map star = Jm R S := by
    ext a b
    rw [gram_apply, Jm_sg]
    change hf M (cl a) (cl b) = _
    rcases m.cover a with rfl | rfl | ⟨a, rfl⟩ <;> rcases m.cover b with rfl | rfl | ⟨b, rfl⟩ <;>
      simp only [ci, cj, ce]
    · simp only [sml, smr, addl, addr, xx, zz, zx, zk, sN, Matrix.diagonal_apply_eq, sg_l, star_one]
      linear_combination NN
    · simp only [sml, smr, addl, addr, xx, zz, zx, zk, sN, star_neg, star_one]
      rw [Matrix.diagonal_apply_ne _ (by simp)]; ring
    · rw [herm, o1, Matrix.diagonal_apply_ne _ (m.ne_i b).symm, star_zero]
    · simp only [sml, smr, addl, addr, xx, zz, zx, zk, sN, star_neg, star_one]
      rw [Matrix.diagonal_apply_ne _ (by simp)]; ring
    · simp only [sml, smr, addl, addr, xx, zz, zx, zk, sN, Matrix.diagonal_apply_eq, sg_r, star_neg, star_one]
      linear_combination -NN
    · rw [herm, o1, Matrix.diagonal_apply_ne _ (m.ne_j b).symm, star_zero]
    · rw [o1, Matrix.diagonal_apply_ne _ (m.ne_i a)]
    · rw [o1, Matrix.diagonal_apply_ne _ (m.ne_j a)]
    · rw [← gram_apply, Matrix.transpose_mul, show (ι * C₁).map star = ι.map star * C₁.map star from
        Matrix.map_mul (f := starRingEnd ℂ), show C₁ᵀ * ιᵀ * M * (ι.map star * C₁.map star) =
          C₁ᵀ * (ιᵀ * M * ι.map star) * C₁.map star by simp only [Matrix.mul_assoc], hg, hC₁.1, Jm_sg]
      by_cases e : a = b
      · subst e; simp [hs]
      · rw [Matrix.diagonal_apply_ne _ e, Matrix.diagonal_apply_ne _ (m.inj.ne e)]
  refine ⟨Matrix.of fun r a => cl a r, (2 * N)⁻¹, c * (2 * N)⁻¹, ⟨gram, ?_⟩, ?_, by simp [N0], ?_, ?_, ?_⟩
  · set C : Matrix (Fin d) (Ix R S) ℂ := Matrix.of fun r a => cl a r
    have h1 : (Jm R S * (Cᵀ * M)) * C.map star = 1 := by rw [Matrix.mul_assoc, gram, Jm_sq]
    have h2 := (Matrix.mul_eq_one_comm_of_card_eq _ _ ℂ (by simp [hd])).1 h1
    refine ⟨(Jm R S * (Cᵀ * M)).map star, ?_⟩
    have h3 := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => A.map (starRingEnd ℂ)) h2
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h3
    rw [← h3, ← Matrix.map_mul, ← Matrix.map_mul]
    congr 1
    ext; simp
  · ext r a
    rw [Jm_sg, Matrix.mul_diagonal]
    change (θ *ᵥ cl a) r = cl a r * sg a
    rcases m.cover a with rfl | rfl | ⟨a, rfl⟩
    · rw [ci, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, θθ]; simp only [sg_l, hz, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
    · rw [cj, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, θθ]; simp [sg_r, hz]; ring
    · rw [ce, hs]
      change (θ * (ι * C₁)) r a = _
      rw [← Matrix.mul_assoc, hθι, Matrix.mul_assoc, hθ₁, ← Matrix.mul_assoc, Jm_sg, Matrix.mul_diagonal]
  · funext r
    simp only [Emb.x, Matrix.mulVec_add, Matrix.mulVec_single_one, Pi.smul_apply, Pi.add_apply, Matrix.col_apply,
      Matrix.of_apply, ci, cj, smul_eq_mul]
    field_simp; ring
  · funext r
    simp only [hy, Emb.y, Matrix.mulVec_sub, Matrix.mulVec_single_one, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
      Matrix.col_apply, Matrix.of_apply, ci, cj, smul_eq_mul]
    field_simp; ring
  · ext r b
    simp [Matrix.mul_apply (M := Matrix.of _), Emb.P, ce]

end PositivityTheory.ThKG.CayleyTransformDarboux

end
end

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.RealLift PositivityTheory.ThKG.Loc
open FockH1Action (Mat Ix cPair)
open Formalism.BasicNotions.TH (upq Jm)
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.ThKG.CayleyTransformDarboux

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {R S R₁ S₁ d d₁ : ℕ}

theorem piInf_incV {w : InfinitePlace F} (τ : EmbOver E w) {n : ℕ} (x : Fin n → E) :
    (piInf τ ∘ incV F x) = fun i => τ.1 (x i) := by
  funext i
  simp [incV, piInf, compInf, inclR, infEmb_tmul]

theorem map_mulVec' {w : InfinitePlace F} (τ : EmbOver E w) {n k : ℕ} (M : Matrix (Fin n) (Fin k) (AE F E)) (v : Fin k → AE F E) :
    piInf τ ∘ (M *ᵥ v) = M.map (piInf τ) *ᵥ (piInf τ ∘ v) := funext fun i => RingHom.map_mulVec _ M v i

theorem at_mulVec {n : ℕ} {M : Matrix (Fin n) (Fin n) (AE F E)} (h : At (evI F) (M - 1)) (z : Fin n → AE F E) (i : Fin n) :
    (M *ᵥ z) i - z i ∈ atI F E := by
  have : (M *ᵥ z) i - z i = ((M - 1) *ᵥ z) i := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; rfl
  rw [this]
  change ∑ j, (M - 1) i j * z j ∈ _
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (at_entry h i j)

structure FD (B : Base F E) (H' : Plane E d d₁) (m : Emb R S R₁ S₁) (C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ)
    (C₁ : InfinitePlace F → Matrix (Fin d₁) (Ix R₁ S₁) ℂ) (n n' : InfinitePlace F → ℂ) : Prop where
  cm : IsCMExt F E σ
  n0 : ∀ w, n w ≠ 0
  hx : ∀ w, (fun i => (B.emb w).1 (H'.x i)) = n w • C w *ᵥ m.x
  hy : ∀ w, (fun i => (B.emb w).1 (H'.y i)) = n' w • C w *ᵥ m.y
  hι : ∀ w, C w * m.P = H'.ι.map (B.emb w).1 * C₁ w
  inv : ∀ w, ∃ A : Matrix (Ix R₁ S₁) (Fin d₁) ℂ, C₁ w * A = 1

variable {B : Base F E} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {m : Emb R S R₁ S₁}
  {C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ} {C₁ : InfinitePlace F → Matrix (Fin d₁) (Ix R₁ S₁) ℂ}
  {n n' : InfinitePlace F → ℂ}

theorem gen_vec {γ : Multiplicative ℝ →* UA σ W.J} {Y} (h : IsGen B.emb C γ Y) (s : ℝ) (w) (v : Ix R S → ℂ) :
    (mat (γ (Multiplicative.ofAdd s))).map (piInf (B.emb w)) *ᵥ (C w *ᵥ v) = C w *ᵥ (NormedSpace.exp (s • Y w) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (· *ᵥ v) (h s w)

theorem real_mulVec (s : ℝ) (Y : Mat R S) (v : Ix R S → ℂ) : (s • Y) *ᵥ v = (s : ℂ) • (Y *ᵥ v) := by
  rw [Matrix.smul_mulVec]; rfl

theorem eig_vec (hc : IsCMExt F E σ) {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) {Y} (h : IsGen B.emb C γ Y) (s : ℝ)
    (x : Fin d → E) (k l : InfinitePlace F → ℂ) (v : Ix R S → ℂ) (hx : ∀ w, (fun i => (B.emb w).1 (x i)) = k w • C w *ᵥ v)
    (hY : ∀ w, Y w *ᵥ v = l w • v) (t : AE F E) (ht : t - 1 ∈ atI F E) (ht' : ∀ w, piInf (B.emb w) t = Complex.exp (s * l w)) :
    mat (γ (Multiplicative.ofAdd s)) *ᵥ incV F x = t • incV F x := by
  funext i
  refine eq_of_inf hc B.emb ?_ fun w => ?_
  · have := sub_mem (at_mulVec (hγ.2 (Multiplicative.ofAdd s)) (incV F x) i) (Ideal.mul_mem_right (incV F x i) _ ht)
    rwa [sub_mul, one_mul, sub_sub_sub_cancel_right] at this
  · have e := map_mulVec' (B.emb w) (mat (γ (Multiplicative.ofAdd s))) (incV F x)
    rw [piInf_incV, hx, Matrix.mulVec_smul, gen_vec h,
      exp_eig (c := s * l w) (by rw [real_mulVec, hY, smul_smul]), Matrix.mulVec_smul, smul_comm, ← hx] at e
    refine (congrFun e i).trans ?_
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, ht']
    exact congrArg _ (congrFun (piInf_incV (B.emb w) x) i).symm

theorem FD.iota (h : FD (σ := σ) B H' m C C₁ n n') (w) (z : Fin d₁ → ℂ) :
    ∃ u, z = C₁ w *ᵥ u ∧ H'.ι.map (B.emb w).1 *ᵥ z = C w *ᵥ (m.P *ᵥ u) := by
  obtain ⟨A, hA⟩ := h.inv w
  refine ⟨A *ᵥ z, by rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec], ?_⟩
  rw [Matrix.mulVec_mulVec, h.hι, Matrix.mulVec_mulVec, Matrix.mul_assoc, hA, Matrix.mul_one]

theorem FD.levi (h : FD (σ := σ) B H' m C C₁ n n') {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) {Y}
    (hg : IsGen B.emb C γ Y) {γ₁ : Multiplicative ℝ →* UA σ W₁.J} (hγ₁ : γ₁ ∈ Lines σ W₁) {Y₁} (hg₁ : IsGen B.emb C₁ γ₁ Y₁)
    {l : InfinitePlace F → ℂ} (h1 : ∀ w, Y w *ᵥ m.x = l w • m.x) (h2 : ∀ w, Y w *ᵥ m.y = (-star (l w)) • m.y)
    (h3 : ∀ w, Y w * m.P = m.P * Y₁ w) (s : ℝ) (t : (AE F E)ˣ) (ht : (t : AE F E) - 1 ∈ atI F E)
    (ht' : ∀ w, piInf (B.emb w) t = Complex.exp (s * l w)) :
    IsLevi H' t (γ₁ (Multiplicative.ofAdd s)) (γ (Multiplicative.ofAdd s)) := by
  refine ⟨eig_vec h.cm hγ hg s _ _ _ _ h.hx h1 _ ht ht', eig_vec h.cm hγ hg s _ _ _ _ h.hy h2 _ ?_ fun w => ?_, ?_⟩
  · have := at_cA (σ := σ) (inv_at ht)
    rwa [map_sub, map_one] at this
  · have h3 := congrArg (piInf (B.emb w)) t.mul_inv
    rw [map_mul, ht', map_one] at h3
    rw [piInf_cA h.cm, eq_inv_of_mul_eq_one_right h3, ← Complex.exp_neg]
    refine (Complex.exp_conj _).symm.trans ?_
    simp
  · refine Matrix.ext_iff_mulVec.2 fun z => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    funext i
    refine eq_of_inf h.cm B.emb ?_ fun w => ?_
    · have a1 := at_mulVec (hγ.2 (Multiplicative.ofAdd s)) (incM F H'.ι *ᵥ z) i
      have a2 : (incM F H'.ι *ᵥ (mat (γ₁ (Multiplicative.ofAdd s)) *ᵥ z - z)) i ∈ atI F E := by
        change ∑ j, incM F H'.ι i j * (mat (γ₁ (Multiplicative.ofAdd s)) *ᵥ z - z) j ∈ _
        exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (at_mulVec (hγ₁.2 (Multiplicative.ofAdd s)) z j)
      have := sub_mem a1 a2
      rwa [Matrix.mulVec_sub, Pi.sub_apply, sub_sub_sub_cancel_right] at this
    · refine congrFun (?_ : piInf (B.emb w) ∘ _ = piInf (B.emb w) ∘ _) i
      obtain ⟨u, e1, e2⟩ := h.iota w (piInf (B.emb w) ∘ z)
      rw [map_mulVec', map_mulVec', map_mulVec', map_mulVec', incM_map, e2, gen_vec hg, e1, gen_vec hg₁,
        exp_int (B := s • Y₁ w) (by rw [Matrix.smul_mul, h3, Matrix.mul_smul]), Matrix.mulVec_mulVec _ (C w), h.hι,
        ← Matrix.mulVec_mulVec]

theorem FD.unip (h : FD (σ := σ) B H' m C C₁ n n') {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) {Y}
    (hg : IsGen B.emb C γ Y) (h1 : ∀ w, Y w *ᵥ m.x = 0) (h2 : ∀ w u, ∃ a : ℂ, Y w *ᵥ (m.P *ᵥ u) = a • m.x) (s) :
    γ s ∈ unip σ W H' := by
  obtain ⟨s, rfl⟩ := Multiplicative.ofAdd.surjective s
  refine Subgroup.subset_closure ⟨?_, fun z => ?_⟩
  · have := eig_vec h.cm hγ hg s _ _ 0 m.x h.hx (fun w => by simp [h1]) 1 (by simp) fun w => by simp
    rwa [one_smul] at this
  · choose u e1 e2 using fun w => h.iota w (piInf (B.emb w) ∘ z)
    choose a ha using fun w => h2 w (u w)
    obtain ⟨b, hb, hb'⟩ := exists_inf h.cm B.emb fun w => s * a w / n w
    refine ⟨b, funext fun i => eq_of_inf h.cm B.emb ?_ fun w => ?_⟩
    · have := sub_mem (at_mulVec (hγ.2 (Multiplicative.ofAdd s)) (incM F H'.ι *ᵥ z) i)
        (Ideal.mul_mem_right (incV F H'.x i) (atI F E) hb)
      rwa [sub_sub] at this
    · have e3 := map_mulVec' (B.emb w) (mat (γ (Multiplicative.ofAdd s))) (incM F H'.ι *ᵥ z)
      have e4 := map_mulVec' (B.emb w) (incM F H'.ι) z
      rw [incM_map, e2] at e4
      rw [e4, gen_vec hg, exp_nil (by rw [real_mulVec, real_mulVec, ha, smul_smul, Matrix.mulVec_smul, h1]; simp), real_mulVec,
        ha, Matrix.mulVec_add, ← e4] at e3
      refine (congrFun e3 i).trans ?_
      have e5 := congrFun ((piInf_incV (B.emb w) H'.x).trans (h.hx w)) i
      have := h.n0 w
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at e5
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul, hb', e5, Matrix.mulVec_smul, Function.comp_apply]
      field_simp

theorem single_prop {ι A A' : Type} [DecidableEq ι] [Zero A] [Zero A'] (P : A → A' → Prop) (w : ι) {a : A} {a' : A'} (h : P a a')
    (h0 : P 0 0) (i : ι) : P ((Pi.single w a : ι → A) i) ((Pi.single w a' : ι → A') i) := by
  by_cases e : i = w
  · subst e; simpa using h
  · simpa [Pi.single_eq_of_ne e] using h0

theorem core (hD : Dic) {a a' a₁ a₁' : ℕ} {G : Geo σ a a'} {G₁ : Geo σ a₁ a₁'} {X : Chars F E} {om om' om₁ om₁'}
    {Rm : RealMaps F a a'} {Rm₁ : RealMaps F a₁ a₁'} (hT : IsTriple B G X om om') (hR : IsRealMaps B G om om' Rm)
    (hT₁ : IsTriple B G₁ X om₁ om₁') (hR₁ : IsRealMaps B G₁ om₁ om₁' Rm₁) {H' : Plane E (a + a') (a₁ + a₁')} {i₀ i₁ : ℕ}
    (hH : H'.IsAdapted σ B G.W G₁.W i₀ i₁) (m : Emb (a₁ + a₁' - (G₁.p + G₁.q) + 1) (G₁.p + G₁.q + 1)
      (a₁ + a₁' - (G₁.p + G₁.q)) (G₁.p + G₁.q)) (hs : ∀ b, sg (m.e b) = sg b) (hy : G₁.p + G₁.q + 1 = G.p + G.q)
    (hΛ : ∀ w b, lamW B (a - G.p) G.p _ _ w (m.e b) = lamW B (a₁ - G₁.p) G₁.p _ _ w b) {χ : Chr F E} {k} (hχ : HasExp B.emb χ k)
    (r : ℝ) {lam lam' : Rm.Pi →ₗ[ℂ] Rm₁.Pi} (h : IsArchimedeanLocalEquivariantMap B G.M G₁.M om om₁ H' χ r Rm.p Rm₁.p lam)
    (h' : IsArchimedeanLocalEquivariantMap B G.M G₁.M om om₁ H' χ r Rm.p Rm₁.p lam') (h0 : lam ≠ 0) : ∃ c : ℂ, lam' = c • lam := by
  have hc := hT.base.cm
  have rk := hH.rank
  have b1 := hT₁.geo.aBig
  choose C₁ hC₁ hθ₁ using fun w => hD.frame _ _ _ _ _ (hT₁.geo.hW.sig w) (hT₁.geo.hW.cartan w)
  have fm : ∀ (w) (x y : Fin (a + a') → E), hf (Complex.I • G.W.J.map (B.emb w).1) (fun i => (B.emb w).1 (x i))
      (fun i => (B.emb w).1 (y i)) = Complex.I * (B.emb w).1 (form σ G.W.J x y) := fun w x y => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hf, form, dotProduct, Matrix.mulVec, map_sum, map_mul, hc.2.2.2, Finset.mul_sum, Matrix.smul_apply,
      Matrix.map_apply, Pi.star_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [Complex.star_def]; ring
  have col : ∀ j, H'.ι *ᵥ Pi.single j 1 = fun r => H'.ι r j := fun j => Matrix.mulVec_single_one _ _
  choose c' c0' hcy using fun w => (hH.cartan w).2
  have ex := fun w => exists_frame m hs (d := a + a') (by omega) (M := Complex.I • G.W.J.map (B.emb w).1)
      (fun i j => by
        simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul']
        rw [← hc.2.2.2, hT.geo.hW.skew, Complex.star_def, Complex.conj_I, map_neg, neg_mul_neg])
      (hT.geo.hW.cartan w) (x := fun i => (B.emb w).1 (H'.x i)) (y := fun i => (B.emb w).1 (H'.y i))
      (ι := H'.ι.map (B.emb w).1)
      (fun e => by
        have := fm w H'.x H'.y
        rw [e, hH.xy] at this
        rw [map_one, mul_one, hf, zero_dotProduct] at this
        exact Complex.I_ne_zero this.symm)
      (by rw [fm, hH.xx]; simp) (c0' w) (hcy w)
      (fun j => by
        have := fm w (H'.ι *ᵥ Pi.single j 1) H'.x
        rw [(hH.orth _).1, col] at this
        simpa using this)
      (fun j => by
        have := fm w (H'.ι *ᵥ Pi.single j 1) H'.y
        rw [(hH.orth _).2, col] at this
        simpa using this)
      (by
        rw [← hH.gram, Matrix.map_mul, Matrix.map_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_map]
        congr 2
        ext i j
        exact (hc.2.2.2 _ _).symm)
      (hH.cartan w).1 (hC₁ w) (hθ₁ w)
  choose C n n' hC hθ n0 hx hy' hι using ex
  have fd : FD (σ := σ) B H' m C C₁ n n' := ⟨hc, n0, hx, hy', hι, fun w => (hC₁ w).2⟩
  have hC' : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by rw [incM_map]; exact hC w
  have hC₁' : ∀ w, IsFrame (Complex.I • (incM F G₁.W.J).map (piInf (B.emb w))) (C₁ w) := fun w => by
    rw [incM_map]; exact hC₁ w
  obtain ⟨act, f, hM, ha⟩ := exists_mod hD hT hR (by omega) hy C hC' hθ
  obtain ⟨act₁, f₁, hM₁, ha₁⟩ := exists_mod hD hT₁ hR₁ (by omega) rfl C₁ hC₁' hθ₁
  have tor := fun l => exists_torus hc B.emb l χ hχ r
  choose t c ht hd using tor
  have onto : ∀ v : Rm.Pi, ∃ f ∈ G.M.Pol B.ψ B.emb, Rm.p f = v := fun v => (hR.quot.onto ▸ Submodule.mem_top : v ∈ _)
  have onto₁ : ∀ v : Rm₁.Pi, ∃ f ∈ G₁.M.Pol B.ψ B.emb, Rm₁.p f = v := fun v => (hR₁.quot.onto ▸ Submodule.mem_top : v ∈ _)
  have c0 : c 0 = 0 := by
    refine (hd 0).unique ?_
    have : ∀ s, t 0 s = 1 := fun s => Units.ext (eq_of_inf hc B.emb (ht 0 s).1 fun w => by simp [(ht 0 s).2])
    simp only [this]
    exact hasDerivAt_const _ _
  have ij : (Sum.inl m.i : Ix _ _) ≠ Sum.inr m.j := Sum.inl_ne_inr
  have par : ∀ D : Rm.Pi →ₗ[ℂ] Rm₁.Pi, IsArchimedeanLocalEquivariantMap B G.M G₁.M om om₁ H' χ r Rm.p Rm₁.p D →
      IsPar m act act₁ (fun w => -Complex.I * c (Pi.single w Complex.I)) (fun w => c (Pi.single w 1)) D := by
    intro D hP
    have L : ∀ Y Y₁ l, (∀ w, Y w ∈ upq _ _) → (∀ w, Y₁ w ∈ upq _ _) → (∀ w, Y w *ᵥ m.x = l w • m.x) →
        (∀ w, Y w *ᵥ m.y = (-star (l w)) • m.y) → (∀ w, Y w * m.P = m.P * Y₁ w) →
        ∀ v, D (act Y v) = c l • D v + act₁ Y₁ (D v) := by
      intro Y Y₁ l u1 u2 h1 h2 h3 v
      obtain ⟨γ, hγ, hg⟩ := hD.line F E σ _ _ _ B.emb _ Complex.I C hc hC' Y u1
      obtain ⟨γ₁, hγ₁, hg₁⟩ := hD.line F E σ _ _ _ B.emb _ Complex.I C₁ hc hC₁' Y₁ u2
      obtain ⟨g, hg0, rfl⟩ := onto v
      obtain ⟨g₁, hg₁0, e⟩ := onto₁ (D (Rm.p g))
      obtain ⟨g', q1, q2⟩ := ha γ hγ Y hg g hg0
      obtain ⟨g₁', q3, q4⟩ := ha₁ γ₁ hγ₁ Y₁ hg₁ g₁ hg₁0
      rw [← q2, ← e, ← q4]
      exact hP.levi γ hγ γ₁ hγ₁ (t l) (fun s => fd.levi hγ hg hγ₁ hg₁ h1 h2 h3 s _ (ht l s).1 (ht l s).2) _ (hd l) g hg0 g₁ hg₁0
        g' g₁' q1 q3 e.symm
    have U : ∀ w Y, Y ∈ upq _ _ → Y *ᵥ m.x = 0 → (∀ u, ∃ a : ℂ, Y *ᵥ (m.P *ᵥ u) = a • m.x) →
        ∀ v, D (act (Pi.single w Y) v) = 0 := by
      intro w Y u1 h1 h2 v
      obtain ⟨γ, hγ, hg⟩ := hD.line F E σ _ _ _ B.emb _ Complex.I C hc hC' _ (single_upq w u1)
      obtain ⟨g, hg0, rfl⟩ := onto v
      obtain ⟨g', q1, q2⟩ := ha γ hγ _ hg g hg0
      rw [← q2]
      exact hP.unip γ hγ (fd.unip hγ hg (single_prop (fun Z (_ : ℂ) => Z *ᵥ m.x = 0) w (a' := 0) h1 (by simp))
        (single_prop (fun Z (_ : ℂ) => ∀ u, ∃ a : ℂ, Z *ᵥ (m.P *ᵥ u) = a • m.x) w (a' := 0) h2 fun u => ⟨0, by simp⟩)) g hg0 g' q1
    have T : ∀ w Y (l : ℂ), Y ∈ upq _ _ → Y *ᵥ m.x = l • m.x → Y *ᵥ m.y = (-star l) • m.y → (∀ u, Y *ᵥ (m.P *ᵥ u) = 0) →
        ∀ v, D (act (Pi.single w Y) v) = c (Pi.single w l) • D v := by
      intro w Y l u1 h1 h2 h3 v
      have := L (Pi.single w Y) 0 (Pi.single w l) (single_upq w u1) (fun _ => zero_upq _ _)
        (single_prop (fun Z (l : ℂ) => Z *ᵥ m.x = l • m.x) w h1 (by simp))
        (single_prop (fun Z (l : ℂ) => Z *ᵥ m.y = (-star l) • m.y) w h2 (by simp))
        (fun i => Matrix.ext_iff_mulVec.2 fun u => by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Pi.zero_apply, Matrix.zero_mulVec, Matrix.mulVec_zero]
          exact single_prop (fun Z (_ : ℂ) => Z *ᵥ (m.P *ᵥ u) = 0) w (a' := 0) (h3 u) (Matrix.zero_mulVec _) i) v
      simpa using this
    have xi : m.x (.inl m.i) = 1 ∧ m.x (.inr m.j) = 1 ∧ m.y (.inl m.i) = 1 ∧ m.y (.inr m.j) = -1 ∧ ∀ b, m.x (m.e b) = 0 := by
      simp [Emb.x, Emb.y, Pi.single_eq_of_ne (m.ne_i _), Pi.single_eq_of_ne (m.ne_j _)]
    have N : ∀ w b (s : ℂ) v, s • D (act (un w (m.e b) (.inl m.i) - un w (m.e b) (.inr m.j)) v) -
        (star s * sg (m.e b)) • D (act (un w (.inl m.i) (m.e b) + un w (.inr m.j) (m.e b)) v) = 0 := fun w b s v => by
      have := U w (s • (Matrix.single (m.e b) (.inl m.i) 1 - Matrix.single (m.e b) (.inr m.j) 1) -
          (star s * sg (m.e b)) • (Matrix.single (.inl m.i) (m.e b) 1 + Matrix.single (.inr m.j) (m.e b) 1))
        (by
          simp only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
            Matrix.conjTranspose_single, star_one, star_mul', star_star, star_sg, Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul,
            Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, J_single, single_J, sg_l, sg_r]
          module)
        (by simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, single_mulVec', xi]; simp)
        (fun u => ⟨-(star s * sg (m.e b) * u b), by
          simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, single_mulVec', m.embeddingMatrix_mulVec, Emb.x]
          module⟩) v
      simpa only [Pi.single_sub, Pi.single_smul, Pi.single_add, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        un, map_add, LinearMap.add_apply] using this
    have sg0 : ∀ b, sg (m.e b) ≠ 0 := fun b e => by simpa [e] using sg_sq (m.e b)
    refine ⟨fun w a b v => ?_, fun w v => ?_, fun w v => ?_, fun w v => ?_, fun w b v => ?_, fun w b v => ?_⟩
    · have key : ∀ Y : Mat _ _, D (act (Pi.single w (m.P * Y * m.Pᵀ)) v) = act₁ (Pi.single w Y) (D v) := by
        have k1 : ∀ Y ∈ upq _ _, D (act (Pi.single w (m.P * Y * m.Pᵀ)) v) = act₁ (Pi.single w Y) (D v) := fun Y hY => by
          have := L (Pi.single w (m.P * Y * m.Pᵀ)) (Pi.single w Y) 0 (single_upq w (m.conj_upq hs hY)) (single_upq w hY)
            (single_prop (fun Z (_ : ℂ) => Z *ᵥ m.x = (0 : ℂ) • m.x) w (a' := 0)
              (by rw [← Matrix.mulVec_mulVec, m.embedding_transpose_vector_zero]; simp) (by simp))
            (single_prop (fun Z (_ : ℂ) => Z *ᵥ m.y = (-star (0 : ℂ)) • m.y) w (a' := 0)
              (by rw [← Matrix.mulVec_mulVec, m.transpose_mulVec_y_eq_zero]; simp) (by simp))
            (single_prop (fun Z Z₁ => Z * m.P = m.P * Z₁) w (by rw [Matrix.mul_assoc, m.tPP, Matrix.mul_one]) (by simp)) v
          rwa [c0, zero_smul, zero_add] at this
        intro Y
        obtain ⟨Y₁, h₁, Y₂, h₂, rfl⟩ := upq_split Y
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Pi.single_add, Pi.single_smul, map_add (f := _),
          map_smul, LinearMap.add_apply, LinearMap.smul_apply, k1 _ h₁, k1 _ h₂]
      have := key (Matrix.single a b 1)
      rwa [m.conj_single] at this
    · have := T w (Complex.I • (Matrix.single (.inl m.i) (.inl m.i) 1 + Matrix.single (.inr m.j) (.inr m.j) 1)) Complex.I
        (by
          simp only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
            Matrix.conjTranspose_single, star_one, Complex.star_def, Complex.conj_I, Matrix.add_mul, Matrix.smul_mul,
            Matrix.mul_add, Matrix.mul_smul, J_single, single_J, sg_l, sg_r, map_one]
          module)
        (by simp only [Matrix.add_mulVec, Matrix.smul_mulVec, single_mulVec', xi]; simp [Emb.x])
        (by simp only [Matrix.add_mulVec, Matrix.smul_mulVec, single_mulVec', xi]; simp [Emb.y, sub_eq_add_neg])
        (fun u => by simp only [Matrix.add_mulVec, Matrix.smul_mulVec, single_mulVec', m.embeddingMatrix_mulVec]; simp) v
      rw [Pi.single_smul, map_smul, LinearMap.smul_apply, map_smul, Pi.single_add] at this
      rw [mul_smul, ← this, smul_smul]
      simp [un]
    · have := T w (Matrix.single (.inl m.i) (.inr m.j) 1 + Matrix.single (.inr m.j) (.inl m.i) 1) 1
        (by
          simp only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_add, Matrix.conjTranspose_single, star_one, Matrix.add_mul,
            Matrix.mul_add, J_single, single_J, sg_l, sg_r]
          module)
        (by simp only [Matrix.add_mulVec, single_mulVec', xi]; simp [Emb.x])
        (by simp only [Matrix.add_mulVec, single_mulVec', xi]; simp [Emb.y, neg_add_eq_sub])
        (fun u => by simp only [Matrix.add_mulVec, single_mulVec', m.embeddingMatrix_mulVec]; simp) v
      rwa [Pi.single_add] at this
    · have := U w (Complex.I • (Matrix.single (.inl m.i) (.inl m.i) 1 - Matrix.single (.inl m.i) (.inr m.j) 1 +
          Matrix.single (.inr m.j) (.inl m.i) 1 - Matrix.single (.inr m.j) (.inr m.j) 1))
        (by
          simp only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
            Matrix.conjTranspose_single, star_one, Complex.star_def, Complex.conj_I, Matrix.add_mul, Matrix.smul_mul,
            Matrix.mul_add, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, J_single, single_J, sg_l, sg_r, map_one]
          module)
        (by simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, single_mulVec', xi]; simp)
        (fun u => ⟨0, by simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, single_mulVec', m.embeddingMatrix_mulVec]; simp⟩) v
      rw [Pi.single_smul, map_smul, LinearMap.smul_apply, map_smul, Pi.single_sub, Pi.single_add, Pi.single_sub,
        smul_eq_zero] at this
      exact this.resolve_left Complex.I_ne_zero
    · have a1 := N w b 1 v
      have a2 := N w b Complex.I v
      rw [Complex.star_def, Complex.conj_I] at a2
      rw [star_one] at a1
      have : (2 * Complex.I) • D (act (un w (m.e b) (.inl m.i) - un w (m.e b) (.inr m.j)) v) = 0 := by
        linear_combination (norm := module) Complex.I • a1 + a2
      exact (smul_eq_zero.1 this).resolve_left (by simp)
    · have a1 := N w b 1 v
      have a2 := N w b Complex.I v
      rw [Complex.star_def, Complex.conj_I] at a2
      rw [star_one] at a1
      have : (2 * Complex.I * sg (m.e b)) • D (act (un w (.inl m.i) (m.e b) + un w (.inr m.j) (m.e b)) v) = 0 := by
        linear_combination (norm := module) a2 - Complex.I • a1
      exact (smul_eq_zero.1 this).resolve_left (by simp [sg0])
  exact par_line hM hM₁ (fun w b => congrArg _ (hΛ w b)) (par _ h) (par _ h') h0

theorem archimedean_multiplicity_one_of (hD : Dic) : ArchimedeanMultiplicityOne := by
  intro F E _ _ _ _ _ σ B a a' a₁ a₁' G G₁ X om om' om₁ om₁' R Rf R₁ Rf₁ H' i₀ i₁ χ r hM hM₁ hS hH lam lam' h h' h0
  have b1 := hM₁.triple.geo.aBig
  have b2 := hM₁.triple.geo.eBig
  rcases hS with ⟨rfl, e1, e2, e3, rfl, rfl⟩ | ⟨e0, rfl, e2, e3, rfl, rfl⟩
  · refine core hD hM.triple hM.real hM₁.triple hM₁.real hH (embB _ _) (sg_embB _ _) (by omega) ?_ hM.triple.chars.expβ _ h h' h0
    rintro w (b | b) <;> simp [lamW, embB, e2, FockH1Action.cPair]
  · refine core hD hM.triple hM.real hM₁.triple hM₁.real hH (embA _ _) (sg_embA _ _) (by omega) ?_ hM.triple.chars.expα _ h h' h0
    have e4 : a - G.p = a₁ - G₁.p + 1 := by omega
    rw [e4, ← e2]
    rintro w (b | b) <;> simp [lamW, embA, FockH1Action.cPair]

end PositivityTheory.ThKG.CayleyTransformDarboux

end
end

namespace PositivityTheory.ThKG.CayleyTransformDarboux

theorem archimedean_multiplicity_one_of_lie (h1 : GlobalTheory.RealLift.LieFirst) (h2 : GlobalTheory.RealLift.LieSecond) : Loc.ArchimedeanMultiplicityOne :=
  archimedean_multiplicity_one_of ⟨PositivityTheory.RL.actsLaws, PositivityTheory.RL.fockEx PositivityTheory.RL.derEx,
    PositivityTheory.ThKEnd.Comp.PR.polRange_of PositivityTheory.RL.actsLaws PositivityTheory.RL.derEx (PositivityTheory.RL.vacLine PositivityTheory.RL.derEx), h1, h2,
    PositivityTheory.RL.lineEx, PositivityTheory.RL.frameEx, PositivityTheory.RL.even_im_hermitian_sub⟩

end PositivityTheory.ThKG.CayleyTransformDarboux
