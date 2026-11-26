module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensSpanOfKilled
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneAddLeLminorSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartAlgebraMapLiftV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugacyClassClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootsOfUnityMapBijectiveOfHenselian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RouteBigVertexKernelProductEqConstMulThetaKernel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionIsLocallyBlockUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionIsLocallyBlockUnitary
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR MvPolynomial

namespace GlobalTheory.HoweR

theorem adjZ_Eab_of_isLeft {p q : ℕ} {a b : Ix p q} (h : a.isLeft = b.isLeft) :
    adjZ (Eab a b) = Eab b a := by
  have hs : sameBlock a b := by
    rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]
  ext i j
  rw [GlobalTheory.FockAdj.adjZ_apply]
  simp only [Eab, Matrix.single_apply]
  by_cases e : a = j ∧ b = i
  · obtain ⟨rfl, rfl⟩ := e
    simp [hs]
  · have e' : ¬ (b = i ∧ a = j) := fun ⟨h1, h2⟩ => e ⟨h2, h1⟩
    simp [e, e']

theorem isKC_Eab_of_isLeft {p q : ℕ} {a b : Ix p q} (h : a.isLeft = b.isLeft) : IsKC (Eab a b) := by
  intro i j hij
  simp only [Eab, Matrix.single_apply]
  rw [if_neg]
  rintro ⟨rfl, rfl⟩
  apply hij
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

theorem fock_locU : ∀ P Q R S : ℕ, LocU (fun a : Ix R S => a.isLeft) (units (fockAct2 P Q R S)) := by
  intro P Q R S t
  classical
  obtain ⟨ι, hι, hinj⟩ := GlobalTheory.FischerParts.exists_fockIP (Ln P Q R S)
  refine ⟨restrictTotalDegree (Ln P Q R S) ℂ (t.sup totalDegree), fun x hx => ?_, ?_⟩
  · rw [mem_restrictTotalDegree]
    exact Finset.le_sup hx
  refine ⟨inferInstance, fun a b hab u hu => ?_, ((innerₛₗ ℂ).comp ι).compl₂ ι, fun x _ y _ => ?_,
    fun x _ hx => ?_, fun a b hab x _ y _ => ?_⟩
  · exact GlobalTheory.DegKeep.stable_restrict _ (Eab a b) (isKC_Eab_of_isLeft hab) u hu
  · simp [inner_conj_symm]
  · have hx' : ι x ≠ 0 := fun h0 => hx (hinj (h0.trans (map_zero ι).symm))
    have := (re_inner_self_pos (𝕜 := ℂ)).2 hx'
    simpa using this
  · have := (GlobalTheory.FockAdj.fock_adjoints P Q R S _ ι hι).2.2 (Eab a b) x y
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, innerₛₗ_apply_apply, units]
    rw [this, adjZ_Eab_of_isLeft hab]

end GlobalTheory.HoweR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionIsLocallyBlockUnitaryStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockAction_isLocallyBlockUnitary : ∀ P Q R S : ℕ, LocU (fun a : Ix R S => a.isLeft) (units (fockAct2 P Q R S)) := by
  first | exact @GlobalTheory.HoweR.fock_locU | exact GlobalTheory.HoweR.fock_locU | (intros; apply GlobalTheory.HoweR.fock_locU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemDomOfIsom
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open scoped Matrix

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

theorem hermC_of_isom (G : Matrix (Fin r) (Fin r) E) {γ : GL (Fin r) E}
    (hγ : ∀ v w, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) = herm G v w)
    (τ : E →+* ℂ) (v w : Fin r → ℂ) :
    hermC τ G ((γ : Matrix (Fin r) (Fin r) E).map τ *ᵥ v) ((γ : Matrix (Fin r) (Fin r) E).map τ *ᵥ w) = hermC τ G v w := by
  rw [GlobalTheory.LevelCusp.hermC_of_herm (ε := 1) (fun v w => by rw [hγ, one_mul]), map_one, one_mul]

theorem lact_mem_dom_of_isom (M : TwoLevels E r U C) {γ : GL (Fin r) E}
    (hγ : ∀ v w, herm M.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) = herm M.Gm v w)
    {x : Frame M.Ψ r} (hx : x ∈ M.dom) : lact γ x ∈ M.dom := fun τ => by
  have hd : ∀ i, dmin M.Gm (lact γ x) τ i = dmin M.Gm x τ i := fun i => by
    unfold dmin
    congr 1
    ext p q
    exact hermC_of_isom M.Gm hγ τ.1 (col (mat x τ) p) (col (mat x τ) q)
  refine ⟨?_, fun i => by rw [hd]; exact (hx τ).2 i⟩
  have e : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  rw [e, Matrix.det_mul]
  refine mul_ne_zero ?_ (hx τ).1
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, map_ne_zero]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero

theorem lact_tr_mem (M : TwoLevels E r U C) (u : U) (c : C) {x : Frame M.Ψ r} (hx : x ∈ M.dom) :
    lact (M.tr u c) x ∈ M.dom :=
  lact_mem_dom_of_isom M (M.tr_herm u c) hx

def Lmap (M : TwoLevels E r U C) (u : U) (c : C) (x : M.dom) : M.dom :=
  ⟨lact (M.tr u c) x.1, lact_tr_mem M u c x.2⟩

def pb (M : TwoLevels E r U C) (u : U) : (C → M.dom → ℂ) →ₐ[ℂ] (C → M.dom → ℂ) where
  toFun f := fun c x => f (u • c) (Lmap M u c x)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem pb_apply (M : TwoLevels E r U C) (u : U) (f : C → M.dom → ℂ) (c : C) (x : M.dom) :
    pb M u f c x = f (u • c) (Lmap M u c x) := rfl

def IsHol (M : TwoLevels E r U C) (f : C → M.dom → ℂ) : Prop :=
  ∀ c, ∃ G : Frame M.Ψ r → ℂ, DifferentiableOn ℂ G M.dom ∧ ∀ x : M.dom, f c x = G x.1

def IsInv (M : TwoLevels E r U C) (f : C → M.dom → ℂ) : Prop :=
  ∀ c, ∀ γ ∈ (M.comp c).Γ, ∀ (x : M.dom) (hx : lact γ x.1 ∈ M.dom), f c ⟨lact γ x.1, hx⟩ = f c x

def HA (M : TwoLevels E r U C) : Subalgebra ℂ (C → M.dom → ℂ) where
  carrier := {f | IsHol M f ∧ IsInv M f}
  mul_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨fun c => ?_, fun c γ hγ x hx => ?_⟩
    · obtain ⟨F, hF, hF'⟩ := hf c
      obtain ⟨G, hG, hG'⟩ := hg c
      exact ⟨F * G, hF.mul hG, fun x => by simp [hF', hG']⟩
    · simp only [Pi.mul_apply]
      rw [hf' c γ hγ x hx, hg' c γ hγ x hx]
  add_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨fun c => ?_, fun c γ hγ x hx => ?_⟩
    · obtain ⟨F, hF, hF'⟩ := hf c
      obtain ⟨G, hG, hG'⟩ := hg c
      exact ⟨F + G, hF.add hG, fun x => by simp [hF', hG']⟩
    · simp only [Pi.add_apply]
      rw [hf' c γ hγ x hx, hg' c γ hγ x hx]
  algebraMap_mem' := by
    intro z
    refine ⟨fun c => ⟨fun _ => z, differentiableOn_const z, fun x => rfl⟩, fun c γ hγ x hx => rfl⟩

theorem pb_mem (M : TwoLevels E r U C) (u : U) {f : C → M.dom → ℂ} (hf : f ∈ HA M) : pb M u f ∈ HA M := by
  obtain ⟨hf, hf'⟩ := hf
  refine ⟨fun c => ?_, fun c γ hγ x hx => ?_⟩
  · obtain ⟨G, hG, hG'⟩ := hf (u • c)
    refine ⟨fun y => G (lact (M.tr u c) y),
      hG.comp (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.differentiable_lact _).differentiableOn (fun y hy => lact_tr_mem M u c hy),
      fun x => ?_⟩
    rw [pb_apply, hG']
    rfl
  · have hδ : M.tr u c * γ * (M.tr u c)⁻¹ ∈ (M.comp (u • c)).Γ := (M.tr_conj u c γ).1 hγ
    have e : lact (M.tr u c) (lact γ x.1) = lact (M.tr u c * γ * (M.tr u c)⁻¹) (lact (M.tr u c) x.1) := by
      simp only [ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul, ← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul (M.tr u c)⁻¹ (M.tr u c),
        inv_mul_cancel, ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_one]
    have hy : lact (M.tr u c * γ * (M.tr u c)⁻¹) (Lmap M u c x).1 ∈ M.dom := by
      show lact (M.tr u c * γ * (M.tr u c)⁻¹) (lact (M.tr u c) x.1) ∈ M.dom
      rw [← e]; exact lact_tr_mem M u c hx
    rw [pb_apply, pb_apply, ← hf' (u • c) _ hδ (Lmap M u c x) hy]
    congr 1
    exact Subtype.ext e

def pbA (M : TwoLevels E r U C) (u : U) : HA M →ₐ[ℂ] HA M where
  toFun f := ⟨pb M u f, pb_mem M u f.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def cst (M : TwoLevels E r U C) (a : C → ℂ) : HA M :=
  ⟨fun c _ => a c, fun c => ⟨fun _ => a c, differentiableOn_const _, fun _ => rfl⟩, fun _ _ _ _ _ => rfl⟩

def tw (M : TwoLevels E r U C) (a : C → ℂ) (u : U) : Polynomial (HA M) →ₐ[ℂ] Polynomial (HA M) :=
  { Polynomial.eval₂RingHom (Polynomial.C.comp (pbA M u).toRingHom) (Polynomial.C (cst M a) * Polynomial.X) with
    commutes' := fun z => by
      show Polynomial.eval₂ _ _ (algebraMap ℂ (Polynomial (HA M)) z) = _
      rw [Polynomial.algebraMap_apply, Polynomial.eval₂_C]
      simp }

theorem tw_C (M : TwoLevels E r U C) (a : C → ℂ) (u : U) (f : HA M) :
    tw M a u (Polynomial.C f) = Polynomial.C (pbA M u f) := by
  show Polynomial.eval₂ _ _ _ = _
  rw [Polynomial.eval₂_C]
  rfl

theorem tw_X (M : TwoLevels E r U C) (a : C → ℂ) (u : U) :
    tw M a u Polynomial.X = Polynomial.C (cst M a) * Polynomial.X := by
  show Polynomial.eval₂ _ _ _ = _
  rw [Polynomial.eval₂_X]

theorem tw_monomial_one (M : TwoLevels E r U C) (a : C → ℂ) (u : U) (f : HA M) :
    tw M a u (Polynomial.monomial 1 f) = Polynomial.monomial 1 (cst M a * pbA M u f) := by
  rw [← Polynomial.C_mul_X_eq_monomial, map_mul, tw_C, tw_X, ← mul_assoc, ← Polynomial.C_mul, mul_comm (pbA M u f),
    Polynomial.C_mul_X_eq_monomial]

end GlobalTheory.CuspEmb

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedFrameCMUnitaryProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedFrameCMUnitaryProof
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.BalancedPointPf

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem conj_mem_iff (X : Data E r) (σ : E →+* ℂ) :
    ComplexEmbedding.conjugate σ ∈ X.Ψ ↔ σ ∉ X.Ψ := by
  rw [X.cmType (ComplexEmbedding.conjugate σ)]
  simp [ComplexEmbedding.conjugate, star_star]

theorem sum_eq_two_mul (X : Data E r) (f : (E →+* ℂ) → ℝ)
    (hf : ∀ σ, f (ComplexEmbedding.conjugate σ) = f σ) :
    ∑ σ, f σ = 2 * ∑ τ : X.Ψ, f τ.1 := by
  classical
  rw [← Finset.sum_add_sum_compl X.Ψ, Finset.sum_coe_sort X.Ψ f]
  have h : ∑ σ ∈ X.Ψᶜ, f σ = ∑ σ ∈ X.Ψ, f σ := by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      rw [Finset.mem_compl] at hσ
      exact (conj_mem_iff X σ).2 hσ
    · intro σ hσ
      rw [Finset.mem_compl]
      exact (X.cmType σ).1 hσ
    · intro σ _; simp [ComplexEmbedding.conjugate, star_star]
    · intro σ _; simp [ComplexEmbedding.conjugate, star_star]
    · intro σ _; exact (hf σ).symm
  rw [h]; ring

theorem card_Ψ (X : Data E r) : (Fintype.card X.Ψ : ℝ) = fdeg E := by
  have h := sum_eq_two_mul X (fun _ => (1 : ℝ)) (fun _ => rfl)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [Embeddings.card E ℂ] at h
  have h2 : Module.finrank ℚ E = 2 * Fintype.card X.Ψ := by exact_mod_cast h
  rw [fdeg, h2, Nat.mul_div_cancel_left _ two_pos]

end

end GlobalTheory.BalancedPointPf

namespace GlobalTheory.BalancedPointPf

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem embVec_conj (σ : E →+* ℂ) (v : Fin r → E) :
    ReciprocityTheory.MultiplicativeHeights.embVec (ComplexEmbedding.conjugate σ) v = star (ReciprocityTheory.MultiplicativeHeights.embVec σ v) := by
  funext k
  simp [ReciprocityTheory.MultiplicativeHeights.embVec, ComplexEmbedding.conjugate_coe_eq]

theorem maj_eq_hq (X : Data E r) (H : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (x : Frame X.Ψ r)
    (ho : IsOrth X x) (hH : ∀ τ : X.Ψ, (mat x τ)ᴴ * H τ.1 * mat x τ = 1) (τ : X.Ψ) (u : Fin r → ℂ) :
    X.maj x τ u = ReciprocityTheory.MultiplicativeHeights.hq (H τ.1) u := by
  have hmo := GlobalTheory.MajorantOrthFrame.maj_eq_sum_norm_sq_of_isOrth r X x ho
  have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr (hmo.1 τ)
  have e : H τ.1 = ((mat x τ)⁻¹)ᴴ * (mat x τ)⁻¹ := by
    calc H τ.1 = (mat x τ * (mat x τ)⁻¹)ᴴ * H τ.1 * (mat x τ * (mat x τ)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hu]; simp
      _ = ((mat x τ)⁻¹)ᴴ * ((mat x τ)ᴴ * H τ.1 * mat x τ) * (mat x τ)⁻¹ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hH τ, Matrix.mul_one]
  rw [hmo.2 τ u, e, GlobalTheory.Up.BallExPf.hq_ct_mul]
  rfl

theorem balancedPoint :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.BalancedPointStatement E := by
  intro E _ _ _ r X
  obtain ⟨M, hss, hNC⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.semistable E r (MajorantOrthogonality.pform X.toData) X.L'
    (MajorantOrthogonality.isLattice X) (MajorantOrthogonality.selfDual X)
  have hex : ∀ τ : X.Ψ, ∃ x : Matrix (Fin r) (Fin r) ℂ,
      xᴴ * (MajorantOrthogonality.pform X.toData).G.map τ.1 * x = ReciprocityTheory.MultiplicativeHeights.signMat X.p0 r ∧
        xᴴ * M.H τ.1 * x = 1 := fun τ => by
    obtain ⟨P, hP, hPg⟩ := X.signature τ
    exact GlobalTheory.Up.BallExPf.exists_frame (M.posDef τ.1) (M.major τ.1) hP
      ((GlobalTheory.Up.BallExPf.gram_iff X.toData τ.1 P).1 hPg)
  choose y hy1 hy2 using hex
  let x0 : Frame X.Ψ r := fun τ => y τ
  have h0 : IsOrth X.toData x0 := fun τ => (GlobalTheory.Up.BallExPf.gram_iff X.toData τ.1 _).2 (hy1 τ)
  have hmaj : ∀ (τ : X.Ψ) (u : Fin r → ℂ), X.maj x0 τ u = ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) u :=
    maj_eq_hq X.toData M.H x0 h0 hy2
  refine ⟨x0, IW.orth_mem_dom X.toData x0 h0, ?_, ?_⟩
  · intro N hN hlt
    have key : ∀ (τ : X.Ψ) (w : Fin r → ℂ), w ≠ 0 →
        ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) (N.map τ.1 *ᵥ w) < ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) w := by
      intro τ w hw
      obtain ⟨c, hc0, hc1, hc⟩ := hlt τ
      have h1 := hc w
      rw [hmaj, hmaj] at h1
      have hpos : 0 < ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) w := (M.posDef τ.1).re_dotProduct_pos hw
      have hc2 : c ^ 2 < 1 := by nlinarith
      nlinarith
    refine hNC N hN fun σ u hu => ?_
    by_cases hσ : σ ∈ X.Ψ
    · exact key ⟨σ, hσ⟩ u hu
    · have hσ' : ComplexEmbedding.conjugate σ ∈ X.Ψ := (conj_mem_iff X.toData σ).2 hσ
      have hsu : star u ≠ 0 := fun h => hu (by simpa using congrArg star h)
      have h := key ⟨_, hσ'⟩ (star u) hsu
      have e1 : M.H (ComplexEmbedding.conjugate σ) = (M.H σ).map (starRingEnd ℂ) := M.conj_compat σ
      have e2 : N.map (ComplexEmbedding.conjugate σ) *ᵥ star u = star (N.map σ *ᵥ u) := by
        funext k
        simp [Matrix.mulVec, dotProduct, ComplexEmbedding.conjugate_coe_eq]
      simp only at h
      rwa [e1, e2, GlobalTheory.Up.BallExPf.hq_conj, GlobalTheory.Up.BallExPf.hq_conj] at h
  · intro v hv hv0
    classical
    set h : (E →+* ℂ) → ℝ := fun σ => ReciprocityTheory.MultiplicativeHeights.hq (M.H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ v) with hhdef
    have hpos : ∀ σ, 0 < h σ := by
      intro σ
      refine (M.posDef σ).re_dotProduct_pos fun h0 => hv0 ?_
      funext k
      have := congrFun h0 k
      simp only [ReciprocityTheory.MultiplicativeHeights.embVec, Pi.zero_apply, map_eq_zero] at this
      exact this
    have hconj : ∀ σ, h (ComplexEmbedding.conjugate σ) = h σ := by
      intro σ
      simp only [hhdef]
      rw [embVec_conj, show M.H (ComplexEmbedding.conjugate σ) = (M.H σ).map (starRingEnd ℂ) from
        M.conj_compat σ, GlobalTheory.Up.BallExPf.hq_conj]

    set B : Submodule (𝓞 E) (Fin r → E) := Submodule.span (𝓞 E) {v} with hB
    have hrange : Set.range ![v] = {v} := by simp
    have hBL : B ≤ X.L' := by rw [hB, Submodule.span_le]; simpa using hv
    have hbasis : ReciprocityTheory.MultiplicativeHeights.IsKBasisIn B ![v] := by
      refine ⟨fun i => ?_, ?_, fun y hy => ?_⟩
      · rw [Fin.eq_zero i]; exact Submodule.subset_span rfl
      · exact linearIndependent_unique_iff.2 (by simpa using hv0)
      · rw [hB, Submodule.mem_span_singleton] at hy
        obtain ⟨a, rfl⟩ := hy
        rw [hrange]
        have : (algebraMap (𝓞 E) E a) • v ∈ Submodule.span E ({v} : Set (Fin r → E)) :=
          Submodule.smul_mem _ _ (Submodule.subset_span rfl)
        rwa [algebraMap_smul] at this
    have hdeg := hss.2 B hBL 1 ![v] hbasis
    have hidx : (Submodule.span (𝓞 E) (Set.range ![v])).toAddSubgroup.relIndex B.toAddSubgroup = 1 := by
      rw [hrange, ← hB]; exact AddSubgroup.relIndex_self _
    have hdet : ∀ σ, (ReciprocityTheory.MultiplicativeHeights.gramC (M.H σ) σ ![v]).det.re = h σ := by
      intro σ
      rw [Matrix.det_unique]
      rfl
    simp only [ReciprocityTheory.MultiplicativeHeights.latDeg, hidx, Nat.cast_one, Real.log_one, zero_sub, hdet] at hdeg
    have hsum : 0 ≤ ∑ σ, Real.log (h σ) := by linarith
    rw [sum_eq_two_mul X.toData (fun σ => Real.log (h σ)) (fun σ => by simp only [hconj])] at hsum
    have hlog : ∀ τ : X.Ψ, Real.log (h τ.1) ≤ h τ.1 - 1 := fun τ => Real.log_le_sub_one_of_pos (hpos τ.1)
    have hsum2 : 0 ≤ ∑ τ : X.Ψ, (h τ.1 - 1) :=
      (by linarith : 0 ≤ ∑ τ : X.Ψ, Real.log (h τ.1)).trans (Finset.sum_le_sum fun τ _ => hlog τ)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      card_Ψ X.toData] at hsum2
    have e : ∀ τ : X.Ψ, X.maj x0 τ (Data.emb τ.1 v) = h τ.1 := fun τ => hmaj τ _
    simp only [e]
    linarith

end GlobalTheory.BalancedPointPf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedFrameCMUnitaryProofStatement
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsBalancedFrameCMUnitary_proof : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.BalancedPointStatement E := by
  first | exact @GlobalTheory.BalancedPointPf.balancedPoint | exact GlobalTheory.BalancedPointPf.balancedPoint | (intros; apply GlobalTheory.BalancedPointPf.balancedPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetAwayP
section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ShiftTw
noncomputable section

namespace GlobalTheory.LKRes

variable {H : Type} [Group H]

def conv (K : Subgroup H) (f f' : H → ℂ) (x : H) : ℂ :=
  ∑ᶠ q : H ⧸ K, f (Quotient.out q) * f' ((Quotient.out q)⁻¹ * x)

end GlobalTheory.LKRes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFiniteAdelesSplitAwayFromPrimePadic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFiniteAdelesSplitAwayFromPrimePadic
open IsDedekindDomain

noncomputable section

namespace GlobalTheory.AdeleSplitP

open GlobalTheory.LKTrip Rat.HeightOneSpectrum

local instance (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

def placeP (p : ℕ) [hp : Fact p.Prime] : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(p : ℤ)}
  isPrime := (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).2
    (Nat.prime_iff_prime_int.mp hp.out)
  ne_bot := by simpa using hp.out.ne_zero

theorem primesEquiv_placeP (p : ℕ) [hp : Fact p.Prime] :
    primesEquiv (placeP p) = (⟨p, hp.out⟩ : Nat.Primes) := by
  apply Subtype.ext
  change natGenerator (placeP p) = p
  have h1 := span_natGenerator (placeP p)
  have he : Rat.IsIntegralClosure.intEquiv ℤ = RingEquiv.refl ℤ :=
    RingEquiv.ext fun x ↦ by simpa using eq_intCast (Rat.IsIntegralClosure.intEquiv ℤ) x
  have h2 : (placeP p).asIdeal.map (Rat.IsIntegralClosure.intEquiv ℤ) = (placeP p).asIdeal := by
    rw [he]
    exact Ideal.map_id _
  rw [h2] at h1
  change Ideal.span {((natGenerator (placeP p) : ℕ) : ℤ)} = Ideal.span {(p : ℤ)} at h1
  rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at h1
  simpa using h1

def compP (p : ℕ) [hp : Fact p.Prime] : FiniteAdeleRing ℤ ℚ →+* ℚ_[p] :=
  ((ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)).toRingEquiv.toRingHom.comp
    (adicCompletion.padicEquiv (placeP p)).toRingEquiv.toRingHom).comp
    (RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ) (placeP p))

theorem compP_apply (p : ℕ) [Fact p.Prime] (a : FiniteAdeleRing ℤ ℚ) :
    compP p a = ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)
      (adicCompletion.padicEquiv (placeP p) (a (placeP p))) := rfl

theorem continuous_compP (p : ℕ) [Fact p.Prime] : Continuous (compP p) :=
  show Continuous (fun a ↦ compP p a) from (ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)).continuous.comp
    ((adicCompletion.padicEquiv (placeP p)).continuous.comp (RestrictedProduct.continuous_eval _))

theorem restr_eval (p : ℕ) (a : FiniteAdeleRing ℤ ℚ) (w : AwayP p) :
    AfP.eval w (AfP.restr p a) = a w.1 := rfl

theorem finiteAdeleRingAway_ext {p : ℕ} {b c : AfP p} (h : ∀ w, AfP.eval w b = AfP.eval w c) : b = c :=
  Subtype.ext (funext fun w ↦ h w)

theorem eq_placeP {p : ℕ} [Fact p.Prime] {v : HeightOneSpectrum ℤ}
    (hv : v.asIdeal = Ideal.span {(p : ℤ)}) : v = placeP p :=
  HeightOneSpectrum.ext hv

theorem finiteAdele_split (p : ℕ) [Fact p.Prime] :
    ∃ π : FiniteAdeleRing ℤ ℚ →ₐ[ℚ] ℚ_[p], Continuous π ∧
      Function.Bijective (fun a ↦ (GlobalTheory.LKTrip.AfP.restr p a, π a)) := by
  refine ⟨(compP p).toRatAlgHom, continuous_compP p, ?_, ?_⟩
  · intro a b hab
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    refine FiniteAdeleRing.ext _ fun v ↦ ?_
    by_cases hv : v.asIdeal = Ideal.span {(p : ℤ)}
    · obtain rfl := eq_placeP hv
      have h2' : compP p a = compP p b := h2
      rw [compP_apply, compP_apply] at h2'
      exact (adicCompletion.padicEquiv (placeP p)).injective
        ((ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)).injective h2')
    · exact congrArg (AfP.eval ⟨v, hv⟩) h1
  · rintro ⟨b, y⟩
    classical
    let x0 : (placeP p).adicCompletion ℚ := (adicCompletion.padicEquiv (placeP p)).symm
      ((ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)).symm y)
    let g0 : ∀ v : HeightOneSpectrum ℤ, v.adicCompletion ℚ := fun v ↦
      if h : v.asIdeal = Ideal.span {(p : ℤ)} then 0 else AfP.eval ⟨v, h⟩ b
    let g : ∀ v : HeightOneSpectrum ℤ, v.adicCompletion ℚ := Function.update g0 (placeP p) x0
    have hg : ∀ v (hv : v.asIdeal ≠ Ideal.span {(p : ℤ)}), g v = AfP.eval ⟨v, hv⟩ b := by
      intro v hv
      have hv0 : v ≠ placeP p := fun h ↦ hv (h ▸ rfl)
      simp only [g, g0, Function.update_of_ne hv0, dif_neg hv]
    have hS : {w : AwayP p | ¬ AfP.eval w b ∈ w.1.adicCompletionIntegers ℚ}.Finite :=
      Filter.eventually_cofinite.1 b.2
    have hfin : {v : HeightOneSpectrum ℤ | ¬ g v ∈ v.adicCompletionIntegers ℚ}.Finite := by
      refine ((hS.image Subtype.val).insert (placeP p)).subset fun v hv ↦ ?_
      by_cases hv0 : v = placeP p
      · exact Or.inl hv0
      · have hv' : v.asIdeal ≠ Ideal.span {(p : ℤ)} := fun h ↦ hv0 (eq_placeP h)
        refine Or.inr ⟨⟨v, hv'⟩, ?_, rfl⟩
        have hv2 : ¬ g v ∈ v.adicCompletionIntegers ℚ := hv
        rw [hg v hv'] at hv2
        exact hv2
    let A : FiniteAdeleRing ℤ ℚ := ⟨g, Filter.eventually_cofinite.2 hfin⟩
    refine ⟨A, Prod.ext ?_ ?_⟩
    · show AfP.restr p A = b
      refine finiteAdeleRingAway_ext fun w ↦ ?_
      rw [restr_eval]
      exact hg w.1 w.2
    · show compP p A = y
      change ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)
        (adicCompletion.padicEquiv (placeP p) (g (placeP p))) = y
      simp only [g, Function.update_self, x0, ContinuousAlgEquiv.apply_symm_apply]

end GlobalTheory.AdeleSplitP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFiniteAdelesSplitAwayFromPrimePadicStatement
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratFiniteAdeles_split_awayFromPrime_padic : ∀ (p : ℕ) [Fact p.Prime], ∃ π : FiniteAdeleRing ℤ ℚ →ₐ[ℚ] ℚ_[p], Continuous π ∧ Function.Bijective (fun a => (GlobalTheory.LKTrip.AfP.restr p a, π a)) := by
  first | (exact @GlobalTheory.AdeleSplitP.finiteAdele_split) | (exact GlobalTheory.AdeleSplitP.finiteAdele_split) | (intros; apply GlobalTheory.AdeleSplitP.finiteAdele_split  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousRestr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousRestr
open IsDedekindDomain

namespace GlobalTheory.LKTrip

theorem AfP.continuous_restr (p : ℕ) : Continuous (AfP.restr p) :=
  RestrictedProduct.mapAlong_continuous (fun v : HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ)
    (fun v : AwayP p ↦ v.1.adicCompletion ℚ) Subtype.val Subtype.val_injective.tendsto_cofinite
    (fun _ ↦ RingHom.id _) (Filter.Eventually.of_forall fun _ ↦ Set.mapsTo_id _)
    (fun _ ↦ continuous_id)

end GlobalTheory.LKTrip
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousRestrStatement
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_afP_restr : ∀ (p : ℕ), Continuous (GlobalTheory.LKTrip.AfP.restr p) := by
  first | (exact @GlobalTheory.LKTrip.AfP.continuous_restr) | (exact GlobalTheory.LKTrip.AfP.continuous_restr) | (intros; apply GlobalTheory.LKTrip.AfP.continuous_restr  <;> assumption)
end
end

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.CentTorus.AdelicSplit

section Tmap

variable {A B L : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B] [CommRing L] [Algebra ℚ L]

end Tmap

end GlobalTheory.CentTorus.AdelicSplit

namespace GlobalTheory.CentTorus.AdelicSplit

end GlobalTheory.CentTorus.AdelicSplit

namespace GlobalTheory.CentTorus.AdelicSplit

theorem adele_split (p : ℕ) [Fact p.Prime] :
    ∃ (π₁ : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] AfP p) (π₂ : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] ℚ_[p]),
      Continuous π₁ ∧ Continuous π₂ ∧ Function.Bijective (fun a => (π₁ a, π₂ a)) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_continuous_finiteAdele_equiv_rat_int
  obtain ⟨π, hπc, hπb⟩ := GlobalTheory.T.ratFiniteAdeles_split_awayFromPrime_padic p
  let r : FiniteAdeleRing ℤ ℚ →ₐ[ℚ] AfP p := { AfP.restr p with commutes' := fun _ => rfl }
  exact ⟨r.comp e.toAlgHom, π.comp e.toAlgHom, (GlobalTheory.T.continuous_afP_restr p).comp he, hπc.comp he, hπb.comp e.bijective⟩

end GlobalTheory.CentTorus.AdelicSplit

section Final

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.CentTorus
open scoped TensorProduct Classical

end Final
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteSeesawArrowKernelsProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteSeesawArrowKernelsProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigSeesaw

open GlobalTheory.RouteSeesaw

theorem swap_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (hT' : T'.gramᵀ = -(S.gram.submatrix e₁ e₁))
    (hS' : S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂)) {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT ω)
    {ω₀ : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ)} (hω₀ : IsWeilDatumO ψ S' T' χT χS ω₀)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (g : GA D S) (h : GA D T) (g' : GA D S') (h' : GA D T')
    (hh : Formalism.L2.Theta.mt T' h' = ((Formalism.L2.Theta.mt S g).map (cA D)).submatrix e₁ e₁)
    (hg : Formalism.L2.Theta.mt S' g' = ((Formalism.L2.Theta.mt T h⁻¹).submatrix e₂ e₂)ᵀ) :
    ω₀ (g', h') (fun u => f (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) :
      Matrix (Fin T.rank) (Fin S.rank) (AE D))) 0 = ω (g, h) f 0 := by
  obtain ⟨φ', c1, q1, m1, s1, d1⟩ := GlobalTheory.GrpConj.exists_conj_equiv D S T' e₁ hT'
  obtain ⟨φ, c2, q2, m2, s2, d2⟩ := GlobalTheory.InvTransposeIso.grp_contra D T S' e₂ hS'
  obtain ⟨L, hL, hLs, cL, cL', rL, iL, fL⟩ := GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec D S T S' T' e₁ e₂
  have m1' : ∀ h, Formalism.L2.Theta.mt T' h = ((Formalism.L2.Theta.mt S (φ' h)).map (cA D)).submatrix e₁ e₁ := fun h => by
    ext i j
    have t3 := congrArg (cA D) (congrFun (congrFun (m1 h) i) j)
    simp only [Matrix.map_apply, Formalism.L2.Theta.cA_cA] at t3
    exact t3.symm
  have hact : ∀ g h x, L (actO S' T' g h x) = actO S T (φ' h) (φ g) (L x) := by
    intro g h x
    have u1 : ((Formalism.L2.Theta.mt S (φ' h)).map (cA D))ᵀ * S.gram.map (incA D) =
        S.gram.map (incA D) * Formalism.L2.Theta.mt S (φ' h)⁻¹ := by
      have k := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram S (φ' h)
      have k2 : Formalism.L2.Theta.mt S (φ' h) * Formalism.L2.Theta.mt S (φ' h)⁻¹ = 1 := by
        simp only [Formalism.L2.Theta.mt, map_inv, Units.mul_inv]
      have k3 := congrArg (· * Formalism.L2.Theta.mt S (φ' h)⁻¹) k
      simp only [Matrix.mul_assoc, k2, Matrix.mul_one] at k3
      exact k3
    have u2 : Formalism.L2.Theta.mt T (φ g) = (Formalism.L2.Theta.mt S' g⁻¹)ᵀ.submatrix e₂.symm e₂.symm := by
      rw [← m2]; simp
    have u3 : (Formalism.L2.Theta.mt T' h)ᵀ.submatrix e₁.symm e₁.symm = ((Formalism.L2.Theta.mt S (φ' h)).map (cA D))ᵀ := by
      rw [m1']; simp
    rw [hL]
    unfold actO
    rw [hL, u2, Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.submatrix_mul_equiv _ _ _ e₂.symm,
      ← Matrix.submatrix_mul_equiv _ _ _ e₁.symm, u3]
    simp only [Matrix.mul_assoc, u1]
  have hs : ∀ x y, symplO S T (L x) (L y) = symplO S' T' x y := fun x y => by
    rw [hL, hL]; exact GlobalTheory.DarbouxSymp.symplO_darboux D S T S' T' e₁ e₂ hT' hS' x y
  obtain ⟨ω', hw, hω'⟩ := GlobalTheory.SwapWeil.isWeilDatumO_swap D ψ S T S' T' (by simpa using Fintype.card_congr e₂)
    (by simpa using Fintype.card_congr e₁) L φ.toMonoidHom
    φ'.toMonoidHom cL cL' rL hs iL fL c2 c1 q2 q1 hact s2 s1 d2 d1 χS χT ω hω
  have th : IsThetaFunO ψ S' T' (fun w => f (L w)) :=
    GlobalTheory.SwapWeil.theta_pull L cL (fun x hx => (rL x).2 hx) hs (fun x hx => (iL x).2 hx) (fun x hx => (fL x).2 hx) hf
  have a1 : φ' h' = g := by
    have k : h' = φ'.symm g := GlobalTheory.MixModel.mt_injective T' (by rw [hh, m1', MulEquiv.apply_symm_apply])
    rw [k, MulEquiv.apply_symm_apply]
  have a2 : φ g' = h := by
    have k : g' = φ.symm h := GlobalTheory.MixModel.mt_injective S' (by
      have := m2 (φ.symm h)⁻¹
      rw [inv_inv, map_inv, MulEquiv.apply_symm_apply] at this
      rw [hg, this, Matrix.transpose_transpose])
    rw [k, MulEquiv.apply_symm_apply]
  have k9 := congrFun (hω' g' h' f) 0
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, a1, a2, map_zero] at k9
  simp only [← hL]
  rw [GlobalTheory.WeilUniq.weilDatum_unique D ψ hω.std S' T' χT χS ω₀ ω' hω₀ hw (g', h') _ th]
  exact k9

theorem adjM_mul_neg {D : D7} (S B : HSp D) (y : Matrix (Fin S.rank) (Fin B.rank) (AE D)) :
    adjM S B (HMul.hMul yᵀ ((negSp S).gram.map (incA D)) : Matrix (Fin B.rank) (Fin S.rank) (AE D)) =
      -GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG B (y.map (cA D)) := by
  have h2 := GlobalTheory.RouteCoords.inv_mul_gram S
  have h3 : (((negSp S).gram.map (incA D)).map (cA D))ᵀ = -(S.gram.map (incA D)) := by
    rw [GlobalTheory.RouteCoords.gram_conj_transpose, negSp_gram, Matrix.map_neg _ (map_neg _)]
  unfold adjM
  rw [Matrix.map_mul, transpose_mul, h3, transpose_map, transpose_transpose, ← Matrix.mul_assoc, Matrix.mul_neg, h2,
    Matrix.neg_mul, Matrix.one_mul, Matrix.neg_mul]
  rfl


set_option maxHeartbeats 1000000 in
theorem seesaw_big : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T)
    (i j : Fin D.R.m) (M : Vol G) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : IsTripleOf W M t i j e Bs Γ X) (hTr : IsTriple Bs Γ X om om')
    (hT₁ : (GlobalTheory.WeilSchrodinger.sesq D Γ.V.Jᵀ).IsSymm) (hT₂ : (GlobalTheory.WeilSchrodinger.sesq D Γ.V.Jᵀ).Nondegenerate)
    (LT : Submodule (𝓞 D.host.E) (Fin (spW G i j).rank → D.host.E)) (hLT : LT.IsLattice D.host.E)
    (hUT : Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D Γ.V.Jᵀ) LT) (sgT : (D.host.E →+* ℂ) → ℕ × ℕ)
    (hS₁ : (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Γ.W.J⁻¹)).IsSymm)
    (hS₂ : (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Γ.W.J⁻¹)).Nondegenerate)
    (LS : Submodule (𝓞 D.host.E) (Fin ((spW G i j).rank + (spW₁ G i j).rank) → D.host.E)) (hLS : LS.IsLattice D.host.E)
    (hUS : Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Γ.W.J⁻¹)) LS) (sgS : (D.host.E →+* ℂ) → ℕ × ℕ)
    (ω : GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS) × GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT) →*
      Module.End ℂ (WO (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS) (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT) → ℂ))
    (hω : IsWeilDatumO W.ψ (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS)
      (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT) (X.β / X.α) X.β ω)
    (g : GA D (spV G i j)) (g₁ : GA D (spV₁ G i j)), ∃ ξ : ℂ, ξ ≠ 0 ∧ ∀ (f₁ : WO (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) → ℂ)
      (f₂ : WO (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) → ℂ),
      IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) f₁ →
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) f₂ →
      ∀ (u : GA D (spW G i j)) (g' : GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS))
        (h' : GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT)),
      Formalism.L2.Theta.mt _ h' = (conjU (spW G i j) 1 h.JW u).1.1 → Formalism.L2.Theta.mt _ g' = ((blkU (spV G i j) (spV₁ G i j) e h.JWW (g, g₁))⁻¹).1.1ᵀ →
      W.kerA (.right i (j + 1)) f₁ g u * W.kerA (.down t (i + 1) j) f₂ u g₁ =
        ξ * ω (g', h') (fun x => f₁ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e x)ᵀ) *
          f₂ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e x)) 0 := by
  intro D T L sc G W t i j M e Bs Γ X om om' h hTr hT₁ hT₂ LT hLT hUT sgT hS₁ hS₂ LS hLS hUS sgS ω hω g g₁
  have hi := i.2
  have hj := j.2
  have h1 := W.om_is (.chi i (j + 1)) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  have h2 := W.om_is (.mu t (i + 1) j) (show (↑i + 1 ≤ D.R.m ∧ ↑j + 1 ≤ D.R.m) by omega)
  obtain ⟨ω₂, hω₂, hadj⟩ := GlobalTheory.SquareDict.ExactBig.adjoint_exact h2
  have hcard : (spV G i j).rank + (spV₁ G i j).rank = (spW G i j).rank + (spW₁ G i j).rank := by
    simpa using Fintype.card_congr e
  have pV : (G.V (.grid i (j + 1))).rank % 2 = (G.V (.grid (i + 1) j)).rank % 2 := by
    have hev := hTr.geo.even
    rw [← hcard, Nat.even_iff] at hev
    simp only [spV, spV₁] at hev
    omega
  have cT : X.β / X.α = G.chrT (.chi i (j + 1)) * (G.chrS (.mu t (i + 1) j))⁻¹ := by
    rw [h.α, h.β]
    simp only [GridData.chrT, GridData.chrS, GridData.chr, GlobalTheory.SquareDict.ExactBig.attChr_eq, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta,
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha]
    rw [pV, mul_div_mul_right_eq_div, ← div_eq_mul_inv, div_div_div_cancel_right]
  obtain ⟨ωA, hA⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D W.ψ W.ψ_std (negSp (spW G i j))
    (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) X.β (G.chrT (.chi i (j + 1)) * (G.chrS (.mu t (i + 1) j))⁻¹)
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hω.hecT (hecke_mul' h1.hecT hω₂.hecT) hω.resT
    (resEta_mul h1.resT hω₂.resT)
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D _ g
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D _ g₁
  refine ⟨(((G.chrS (.chi i (j + 1)) / X.β) x : Circle) : ℂ) * ((((G.chrT (.mu t (i + 1) j))⁻¹ / X.β) y : Circle) : ℂ),
    mul_ne_zero (Circle.coe_ne_zero _) (Circle.coe_ne_zero _), fun f₁ f₂ hf₁ hf₂ u g' h' hh hg => ?_⟩
  have k := GlobalTheory.SquareDict.ExactBig.seesaw_exact h1 hω₂ hA hf₁ (hadj _ hf₂).1 (negGA _ u) g g₁ hx hy
  rw [(hadj _ hf₂).2] at k
  refine k.trans ?_
  congr 1
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let e₂ : Fin ((spW G i j).rank + (spW₁ G i j).rank) ≃ Fin ((spV G i j).rank + (spV₁ G i j).rank) :=
    e.symm.trans finSumFinEquiv
  have hb : ∀ {R : Type} [CommRing R] (A : Matrix (Fin (spV G i j).rank) (Fin (spV G i j).rank) R)
      (B : Matrix (Fin (spV₁ G i j).rank) (Fin (spV₁ G i j).rank) R),
      (GlobalTheory.Doubling.blkMat finSumFinEquiv A B).submatrix e₂ e₂ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e A B := fun A B => by
    ext a b
    simp [GlobalTheory.Doubling.blkMat, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, e₂]
  have hJ : Γ.W.J = D.host.xi0 • ((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂ := by
    refine h.JWW.trans (congrArg (D.host.xi0 • ·) ?_)
    rw [GlobalTheory.Doubling.gram_hsum, ← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose, ← hb]
    rfl
  have hJu : IsUnit Γ.W.J.det := by
    rw [hJ, det_smul, det_submatrix_equiv_self, det_transpose]
    exact (IsUnit.mk0 _ (pow_ne_zero _ hξ)).mul (GlobalTheory.MixModel.gram_isUnit_det _)
  have e0 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJu,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
  have hT' : (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT).gramᵀ =
      -((negSp (spW G i j)).gram.submatrix (Equiv.refl _) (Equiv.refl _)) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf, negSp_gram]
    show Γ.V.J = - -(spW G i j).gram
    rw [h.JW, one_smul, neg_neg]
  have hS' : (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS).gram⁻¹ =
      -(((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    refine e0.trans ?_
    rw [hJ, smul_smul, inv_neg, neg_mul, inv_mul_cancel₀ hξ, neg_one_smul]
  have hbox : IsThetaFunO W.ψ (negSp (spW G i j)) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j))
      (box2 (S := negSp (spW G i j)) (A := spV G i j) (B := spV₁ G i j) f₁
        (fun y => f₂ (adjM (spW G i j) (spV₁ G i j) y))) := by
    rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec]
    exact (GlobalTheory.BiTransfer.sumDec _ _).isThetaFunO_boxT hf₁ (hadj _ hf₂).1
  have hω' := hω
  rw [cT] at hω'
  have key := swap_eq (negSp (spW G i j)) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j))
    (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS) (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT)
    (Equiv.refl (Fin (spW G i j).rank)) e₂ hT' hS' hA hω'
    hbox (negGA _ u) (GlobalTheory.SquareComm.blk _ _ (g, g₁)) g' h' hh (by
      rw [hg, ← map_inv, Prod.inv_mk, GlobalTheory.SquareComm.mt_blk]
      exact congrArg transpose (hb (Formalism.L2.Theta.mt _ g⁻¹) (Formalism.L2.Theta.mt _ g₁⁻¹)).symm)
  refine key.symm.trans (congrArg (fun F => ω (g', h') F 0) ?_)
  funext z
  have k1 : ∀ a, e₂.symm (Fin.castAdd _ a) = e (.inl a) := fun a =>
    congrArg e (finSumFinEquiv_symm_apply_castAdd a)
  have k2 : ∀ a, e₂.symm (Fin.natAdd _ a) = e (.inr a) := fun a =>
    congrArg e (finSumFinEquiv_symm_apply_natAdd a)
  refine congrArg₂ (· * ·) (congrArg f₁ ?_) (congrArg f₂ ?_)
  · ext a b
    exact Finset.sum_congr (s₁ := Finset.univ) rfl fun c _ =>
      congrArg (fun s => z c s * incA D ((negSp (spW G i j)).gram c b)) (k1 a)
  · refine Eq.trans (congrArg (adjM (spW G i j) (spV₁ G i j)) ?_)
      (adjM_mul_neg (spW G i j) (spV₁ G i j) (z.submatrix id fun k => e (.inr k)))
    ext a b
    exact Finset.sum_congr (s₁ := Finset.univ) rfl fun c _ =>
      congrArg (fun s => z c s * incA D ((negSp (spW G i j)).gram c b)) (k2 a)

end GlobalTheory.BigSeesaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteSeesawArrowKernelsProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigRoute_seesaw_arrow_kernels_product : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T)
    (i j : Fin D.R.m) (M : Vol G) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : IsTripleOf W M t i j e Bs Γ X) (hTr : IsTriple Bs Γ X om om')
    (hT₁ : (GlobalTheory.WeilSchrodinger.sesq D Γ.V.Jᵀ).IsSymm) (hT₂ : (GlobalTheory.WeilSchrodinger.sesq D Γ.V.Jᵀ).Nondegenerate)
    (LT : Submodule (𝓞 D.host.E) (Fin (spW G i j).rank → D.host.E)) (hLT : LT.IsLattice D.host.E)
    (hUT : Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D Γ.V.Jᵀ) LT) (sgT : (D.host.E →+* ℂ) → ℕ × ℕ)
    (hS₁ : (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Γ.W.J⁻¹)).IsSymm)
    (hS₂ : (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Γ.W.J⁻¹)).Nondegenerate)
    (LS : Submodule (𝓞 D.host.E) (Fin ((spW G i j).rank + (spW₁ G i j).rank) → D.host.E)) (hLS : LS.IsLattice D.host.E)
    (hUS : Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D (-D.host.xi0 • Γ.W.J⁻¹)) LS) (sgS : (D.host.E →+* ℂ) → ℕ × ℕ)
    (ω : GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS) × GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT) →*
      Module.End ℂ (WO (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS) (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT) → ℂ))
    (hω : IsWeilDatumO W.ψ (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS)
      (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT) (X.β / X.α) X.β ω)
    (g : GA D (spV G i j)) (g₁ : GA D (spV₁ G i j)), ∃ ξ : ℂ, ξ ≠ 0 ∧ ∀ (f₁ : WO (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) → ℂ)
      (f₂ : WO (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) → ℂ),
      IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) f₁ →
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) f₂ →
      ∀ (u : GA D (spW G i j)) (g' : GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hS₁ hS₂ LS hLS hUS sgS))
        (h' : GA D (GlobalTheory.WeilSchrodinger.hspOf D _ hT₁ hT₂ LT hLT hUT sgT)),
      Formalism.L2.Theta.mt _ h' = (conjU (spW G i j) 1 h.JW u).1.1 → Formalism.L2.Theta.mt _ g' = ((blkU (spV G i j) (spV₁ G i j) e h.JWW (g, g₁))⁻¹).1.1ᵀ →
      W.kerA (.right i (j + 1)) f₁ g u * W.kerA (.down t (i + 1) j) f₂ u g₁ =
        ξ * ω (g', h') (fun x => f₁ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e x)ᵀ) *
          f₂ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e x)) 0 := by
  first | exact @GlobalTheory.BigSeesaw.seesaw_big | exact GlobalTheory.BigSeesaw.seesaw_big | (intros; apply GlobalTheory.BigSeesaw.seesaw_big <;> assumption)
end
end
