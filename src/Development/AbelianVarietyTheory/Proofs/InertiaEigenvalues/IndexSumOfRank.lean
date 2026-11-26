module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLatticePairsIndexRpowLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertPlaceLatticeIndexSumBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlaceSplitIdempotentOrInert
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlaceSplitIdempotentOrInert
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.PlaceDichotomy

theorem split_or_inert_idem : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D),
    IsFinIdem D v f → (∃ e, Formalism.L2.Theta.IsSplitIdem D e ∧ e + Formalism.L2.Theta.cA D e = f) ∨
      (∃ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E v w) := by
  intro D v f hf
  obtain ⟨ε, ⟨α, hεα, hα1, hα0⟩, rfl⟩ := hf
  haveI := v.isMaximal
  obtain ⟨⟨P, hPp, hPo⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 D.host.E)
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨P, hPp, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
  have hw : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hPo.over.symm
  rcases GlobalTheory.LPositivity.split_or_inert D w with hs | hi
  · left
    rw [hw] at hs
    obtain ⟨τ, -⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq (GlobalTheory.AdelicU.isCMExt_host D) hs hw
    refine ⟨GlobalTheory.EmbChart.idem τ, GlobalTheory.EmbChart.isSplitIdem_idem τ, ?_⟩
    have hα : α = GlobalTheory.AdelicU.singleFin v 1 := by
      refine FiniteAdeleRing.ext _ fun u => ?_
      change evalV D.host.F u α = evalV D.host.F u (GlobalTheory.AdelicU.singleFin v 1)
      by_cases e : u = v
      · subst e; rw [hα1, GlobalTheory.AdelicU.evalV_singleFin_self]
      · rw [hα0 u e, GlobalTheory.AdelicU.evalV_singleFin_ne e]
    rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add (f := _), add_sub_cancel, hεα, hα]
    rfl
  · right
    exact ⟨w, hw ▸ hi⟩

end GlobalTheory.PlaceDichotomy
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlaceSplitIdempotentOrInertStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_place_split_idempotent_or_inert : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D), IsFinIdem D v f → (∃ e, Formalism.L2.Theta.IsSplitIdem D e ∧ e + Formalism.L2.Theta.cA D e = f) ∨ (∃ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E v w) := by
  first | exact @GlobalTheory.PlaceDichotomy.split_or_inert_idem | exact GlobalTheory.PlaceDichotomy.split_or_inert_idem | (intros; apply GlobalTheory.PlaceDichotomy.split_or_inert_idem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceLatticeIndexSumLeZetaSqSubOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeIndexSplitPlaceEqProductLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeIndexSplitPlaceEqProductLocal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke GlobalTheory.RawLift
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SplitIndexLocal

theorem relIndex_eq_mul_of {G Q₁ Q₂ : Type} [AddCommGroup G] [AddCommGroup Q₁] [AddCommGroup Q₂]
    (H K : AddSubgroup G) (S₁ T₁ : AddSubgroup Q₁) (S₂ T₂ : AddSubgroup Q₂) (φ₁ : G →+ Q₁) (φ₂ : G →+ Q₂)
    (hT : ∀ y ∈ K, φ₁ y ∈ T₁ ∧ φ₂ y ∈ T₂) (hs : ∀ a ∈ T₁, ∀ b ∈ T₂, ∃ y ∈ K, φ₁ y = a ∧ φ₂ y = b)
    (hH : ∀ y ∈ K, y ∈ H ↔ φ₁ y ∈ S₁ ∧ φ₂ y ∈ S₂) :
    H.relIndex K = S₁.relIndex T₁ * S₂.relIndex T₂ := by
  let ψ : K →+ T₁ × T₂ :=
    { toFun := fun y => (⟨φ₁ y, (hT y y.2).1⟩, ⟨φ₂ y, (hT y y.2).2⟩)
      map_zero' := by ext <;> simp
      map_add' := by intros; ext <;> simp }
  have hψ : Function.Surjective ψ := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    obtain ⟨y, hy, h1, h2⟩ := hs a ha b hb
    exact ⟨⟨y, hy⟩, by ext <;> simp [ψ, h1, h2]⟩
  have e : H.addSubgroupOf K = ((S₁.addSubgroupOf T₁).prod (S₂.addSubgroupOf T₂)).comap ψ := by
    ext ⟨y, hy⟩
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, hH y hy]
    exact Iff.rfl
  unfold AddSubgroup.relIndex
  rw [e, AddSubgroup.index_comap_of_surjective _ hψ, AddSubgroup.index_prod]

section Pure
variable {O K : Type} [CommRing O] [Field K] [Algebra O K]

theorem mem_std {r : ℕ} (x : Fin r → K) :
    x ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))) ↔ ∀ i, IsInt O (x i) := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ i
    refine ⟨c i, ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  · intro h
    choose c hc using h
    refine ⟨c, funext fun i => ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hc]

theorem mem_map_iff {r : ℕ} (A B : Matrix (Fin r) (Fin r) K) (hAB : A * B = 1) (x : Fin r → K) :
    x ∈ (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (A.mulVecLin.restrictScalars O) ↔
      B *ᵥ x ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))) := by
  have hBA : B * A = 1 := (mul_eq_one_comm_of_card_eq (Fin r) (Fin r) K rfl).mp hAB
  constructor
  · rintro ⟨u, hu, rfl⟩
    change B *ᵥ (A *ᵥ u) ∈ _
    rwa [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  · intro h
    refine ⟨_, h, ?_⟩
    change A *ᵥ (B *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]

theorem final_iff {r : ℕ} (R R' : GL (Fin r) K) (hR : R.1 * R'.1 = 1) (a b a' b' : Fin r → K)
    (ha : a' = R'.1 *ᵥ a) (hb : b' = b ᵥ* R.1) :
    ((∀ i, IsInt O (a' i)) ∧ ∀ i, IsInt O (b' i)) ↔
      a ∈ ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        ((R.1.mulVecLin).restrictScalars O)).toAddSubgroup ∧
      b ∈ ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        (((R'.1)ᵀ.mulVecLin).restrictScalars O)).toAddSubgroup := by
  have hT : (R'.1)ᵀ * (R.1)ᵀ = 1 := by rw [← Matrix.transpose_mul, hR, Matrix.transpose_one]
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup, mem_map_iff _ _ hR, mem_map_iff _ _ hT,
    Matrix.mulVec_transpose, mem_std, mem_std, ha, hb]

end Pure
end GlobalTheory.SplitIndexLocal

noncomputable section
namespace GlobalTheory.SplitIndexLocal
open GlobalTheory.SplitHecke.Stab
open GlobalTheory.AdelicLatMove (mt_mul mt_one gram_mul_inv)

variable {D : D7}

def finV (D : D7) (r : ℕ) : (Fin r → AE D) →+ (Fin r → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddMonoidHom.compLeft (finPart D).toAddMonoidHom (Fin r)

theorem finV_apply (r : ℕ) (y : Fin r → AE D) : finV D r y = fun i => finPart D (y i) := rfl

theorem finV_surj (r : ℕ) : Function.Surjective (finV D r) := fun z =>
  ⟨fun k => (finPart_surj (z k)).choose, funext fun k => (finPart_surj (z k)).choose_spec⟩

def coordA {v : HeightOneSpectrum (𝓞 D.host.F)} (π : AE D →+* Fv D.host.F v) {r : ℕ}
    (β : GL (Fin r) (Fv D.host.F v)) : (Fin r → AE D) →+ (Fin r → Fv D.host.F v) where
  toFun y := (β⁻¹).1 *ᵥ fun k => π (y k)
  map_zero' := by simp only [Pi.zero_apply, map_zero]; exact Matrix.mulVec_zero _
  map_add' x y := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp only [Pi.add_apply, map_add]

def coordB (W : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (π : AE D →+* Fv D.host.F v)
    (β : GL (Fin W.rank) (Fv D.host.F v)) : (Fin W.rank → AE D) →+ (Fin W.rank → Fv D.host.F v) where
  toFun y := (fun i => π (cA D (y i))) ᵥ* ((W.gram.map fun a => π (incA D a)) * β.1)
  map_zero' := by simp only [Pi.zero_apply, map_zero]; exact Matrix.zero_vecMul _
  map_add' x y := by
    rw [← Matrix.add_vecMul]
    congr 1
    funext i
    simp only [Pi.add_apply, map_add]

variable {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v} {W : HSp D}
  {β : GL (Fin W.rank) (Fv D.host.F v)}

theorem chart_e (he : IsSplitIdem D e) (hπ : Chart e v π) : π e = 1 ∧ π (cA D e) = 0 := by
  refine ⟨?_, (hπ.2.1 _).2 he.2.1⟩
  have : π (1 - e) = 0 := (hπ.2.1 _).2 (by rw [mul_sub, mul_one, he.1, sub_self])
  rw [map_sub, map_one, sub_eq_zero] at this
  exact this.symm

theorem coords_int (he : IsSplitIdem D e) (hβ : Frame W e π β)
    (hd : ∀ y : Fin W.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ LamHat W ↔ ∀ j, IsInt (Ov D v)
      (((fun i => π (cA D (y i))) ᵥ* ((W.gram.map fun a => π (incA D a)) * β.1)) j))
    {y : Fin W.rank → AE D} (hy : finV D W.rank y ∈ LamHat W) :
    (∀ i, IsInt (Ov D v) (coordA π β y i)) ∧ (∀ i, IsInt (Ov D v) (coordB W π β y i)) :=
  ⟨(hβ y).1 (idem_mul_mem W he.1 hy), (hd y).1 (idem_mul_mem W (GlobalTheory.SplitScalar.isSplitIdem_conj he).1 hy)⟩

end GlobalTheory.SplitIndexLocal

noncomputable section
namespace GlobalTheory.SplitIndexLocal
open GlobalTheory.SplitHecke.Stab

variable {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v} {W : HSp D}
  {β : GL (Fin W.rank) (Fv D.host.F v)}

theorem coords_surj (he : IsSplitIdem D e) (hπ : Chart e v π) (hβ : Frame W e π β)
    (hd : ∀ y : Fin W.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ LamHat W ↔ ∀ j, IsInt (Ov D v)
      (((fun i => π (cA D (y i))) ᵥ* ((W.gram.map fun a => π (incA D a)) * β.1)) j))
    (a b : Fin W.rank → Fv D.host.F v) (ha : ∀ i, IsInt (Ov D v) (a i)) (hb : ∀ i, IsInt (Ov D v) (b i)) :
    ∃ y, finV D W.rank y ∈ LamHat W ∧ coordA π β y = a ∧ coordB W π β y = b := by
  obtain ⟨h1, h0⟩ := chart_e he hπ
  have hcc : cA D (cA D e) = e := cA_cA e
  set G := W.gram.map fun a => π (incA D a) with hG
  set N := W.gram⁻¹.map fun a => π (incA D a) with hN
  have hGN : G * N = 1 := by
    have := congrArg (Matrix.map · π) (GlobalTheory.OrientedAdjoint.gram_mul_inv W)
    simp only [Matrix.map_mul, Matrix.map_map] at this
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this
  have hNG : N * G = 1 := mul_eq_one_comm.1 hGN
  choose y₁ hy₁ using fun k => hπ.1 ((β.1 *ᵥ a) k)
  set x := b ᵥ* ((β⁻¹).1 * N) with hx
  choose z hz using fun k => hπ.1 (x k)
  let y₂ : Fin W.rank → AE D := fun k => cA D (z k)
  have hy₂ : (fun k => π (cA D (y₂ k))) = x := funext fun k => by simp [y₂, cA_cA, hz]
  have hxb : x ᵥ* (G * β.1) = b := by
    rw [hx, Matrix.vecMul_vecMul, Matrix.mul_assoc, ← Matrix.mul_assoc N, hNG, Matrix.one_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  have hA1 : (fun k => π (y₁ k)) = β.1 *ᵥ a := funext hy₁
  have hAa : (β⁻¹).1 *ᵥ (fun k => π (y₁ k)) = a := by
    rw [hA1, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  refine ⟨fun k => e * y₁ k + cA D e * y₂ k, ?_, ?_, ?_⟩
  · have hsplit : finV D W.rank (fun k => e * y₁ k + cA D e * y₂ k) =
        (fun i => finPart D (e * y₁ i)) + (fun i => finPart D (cA D e * y₂ i)) := by
      funext i
      show finPart D (e * y₁ i + cA D e * y₂ i) = finPart D (e * y₁ i) + finPart D (cA D e * y₂ i)
      exact RingHom.map_add _ _ _
    rw [hsplit]
    refine add_mem ((hβ y₁).2 fun i => ?_) ((hd y₂).2 fun j => ?_)
    · rw [hAa]; exact ha i
    · rw [hy₂, hxb]; exact hb j
  · change (β⁻¹).1 *ᵥ (fun k => π (e * y₁ k + cA D e * y₂ k)) = a
    have : (fun k => π (e * y₁ k + cA D e * y₂ k)) = fun k => π (y₁ k) := funext fun k => by
      simp [map_add (f := _), map_mul, h1, h0]
    rw [this, hAa]
  · change (fun i => π (cA D (e * y₁ i + cA D e * y₂ i))) ᵥ* (G * β.1) = b
    have : (fun i => π (cA D (e * y₁ i + cA D e * y₂ i))) = fun k => π (cA D (y₂ k)) := funext fun k => by
      simp [map_add (f := _), map_mul, h1, h0, hcc]
    rw [this, hy₂, hxb]

end GlobalTheory.SplitIndexLocal

noncomputable section
namespace GlobalTheory.SplitIndexLocal
open GlobalTheory.SplitHecke.Stab
open GlobalTheory.AdelicLatMove (mt_mul mt_one gram_mul_inv)

variable {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v} {W : HSp D}
  {β : GL (Fin W.rank) (Fv D.host.F v)}

theorem coordA_move (g' : GA D W) (y : Fin W.rank → AE D) :
    coordA π β (mt W g' *ᵥ y) = (rho W π β g').1 *ᵥ coordA π β y := by
  show (β⁻¹).1 *ᵥ (fun k => π ((mt W g' *ᵥ y) k)) = (rho W π β g').1 *ᵥ ((β⁻¹).1 *ᵥ fun k => π (y k))
  rw [map_mulVec', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, rho_val, Matrix.mul_assoc _ β.1,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem coordB_move (g' : GA D W) (y : Fin W.rank → AE D) :
    coordB W π β (mt W g' *ᵥ y) = coordB W π β y ᵥ* (rho W π β g'⁻¹).1 := by
  have h := dual_move (cA D) π (W.gram.map (incA D)) (mt W g') (mt W g'⁻¹) β (gram_mul_inv W g') y
  rw [rho_val]
  exact h

theorem mem_iff_coords (he : IsSplitIdem D e) (hβ : Frame W e π β)
    (hd : ∀ y : Fin W.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ LamHat W ↔ ∀ j, IsInt (Ov D v)
      (((fun i => π (cA D (y i))) ᵥ* ((W.gram.map fun a => π (incA D a)) * β.1)) j))
    {g' : GA D W} (hg' : SuppAt e W g') {y : Fin W.rank → AE D} (hy : finV D W.rank y ∈ LamHat W) :
    finV D W.rank (mt W g' *ᵥ y) ∈ LamHat W ↔
      (∀ i, IsInt (Ov D v) (coordA π β (mt W g' *ᵥ y) i)) ∧ (∀ i, IsInt (Ov D v) (coordB W π β (mt W g' *ᵥ y) i)) := by
  refine ⟨coords_int he hβ hd, fun ⟨hA, hB⟩ => ?_⟩
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have hs := split_move (finPart D) e (cA D e) (mt W g') hg' y
  rw [← map_mulVec'] at hs
  rw [finV_apply, hs]
  exact add_mem (add_mem ((hβ _).2 hA) ((hd _).2 hB))
    (sub_mem (sub_mem hy (idem_mul_mem W he.1 hy)) (idem_mul_mem W he'.1 hy))

theorem latIndex_split_local : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (W : HSp D) (β : GL (Fin W.rank) (Fv D.host.F v)), Frame W e π β → ∀ g : GA D W, SuppAt e W g → latIndex W g = ((Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).map ((((rho W π β g : GL (Fin W.rank) (Fv D.host.F v)) : Matrix (Fin W.rank) (Fin W.rank) (Fv D.host.F v)).mulVecLin).restrictScalars (Ov D v))).toAddSubgroup.relIndex (Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).toAddSubgroup * ((Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).map ((((rho W π β g⁻¹ : GL (Fin W.rank) (Fv D.host.F v)) : Matrix (Fin W.rank) (Fin W.rank) (Fv D.host.F v))ᵀ.mulVecLin).restrictScalars (Ov D v))).toAddSubgroup.relIndex (Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).toAddSubgroup := by
  intro D e v π he hπ W β hβ g hg
  have hd := GlobalTheory.T.conj_mem_completedLattice_iff_dual_splitPlace e v π he hπ W β hβ
  have h0 : latIndex W g = (((LamHat W).map (finMat D.sp.cm.sig W.gram g).mulVecLin.toAddMonoidHom).comap
      (finV D W.rank)).relIndex ((LamHat W).comap (finV D W.rank)) := by
    unfold latIndex
    rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective (finV_surj (D := D) W.rank)]
  have hgg : (rho W π β g).1 * (rho W π β g⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  rw [h0]
  refine relIndex_eq_mul_of _ _ _ _ _ _ (coordA π β) (coordB W π β) ?_ ?_ ?_
  · intro y hy
    obtain ⟨h1, h2⟩ := coords_int he hβ hd hy
    exact ⟨(mem_std _).2 h1, (mem_std _).2 h2⟩
  · intro a ha b hb
    obtain ⟨y, hy, h1, h2⟩ := coords_surj he hπ hβ hd a b ((mem_std _).1 ha) ((mem_std _).1 hb)
    exact ⟨y, hy, h1, h2⟩
  · intro y hy
    have hy' : finV D W.rank y ∈ LamHat W := hy
    have hstep : finV D W.rank y ∈ (LamHat W).map (finMat D.sp.cm.sig W.gram g).mulVecLin.toAddMonoidHom ↔
        finV D W.rank (mt W g⁻¹ *ᵥ y) ∈ LamHat W := by
      have hfv : finV D W.rank (mt W g⁻¹ *ᵥ y) = finMat D.sp.cm.sig W.gram g⁻¹ *ᵥ finV D W.rank y := by
        rw [finV_apply, finV_apply, finMat_eq, map_mulVec']
      rw [hfv]
      constructor
      · rintro ⟨z, hz, hzy⟩
        change finMat D.sp.cm.sig W.gram g *ᵥ z = _ at hzy
        rw [← hzy]
        have := finMat_mul_inv g⁻¹ z
        rw [inv_inv] at this
        rw [this]
        exact hz
      · intro h
        exact ⟨_, h, finMat_mul_inv g _⟩
    refine AddSubgroup.mem_comap.trans (hstep.trans ((mem_iff_coords he hβ hd (SplitHecke.suppAt_inv hg) hy').trans ?_))
    have hA : coordA π β (mt W g⁻¹ *ᵥ y) = (rho W π β g⁻¹).1 *ᵥ coordA π β y := coordA_move g⁻¹ y
    have hB : coordB W π β (mt W g⁻¹ *ᵥ y) = coordB W π β y ᵥ* (rho W π β g).1 := by rw [coordB_move, inv_inv]
    exact final_iff _ _ hgg _ _ _ _ hA hB

end GlobalTheory.SplitIndexLocal
end
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeIndexSplitPlaceEqProductLocalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke GlobalTheory.RawLift
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_index_split_place_eq_product_local : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (W : HSp D) (β : GL (Fin W.rank) (Fv D.host.F v)), Frame W e π β → ∀ g : GA D W, SuppAt e W g → latIndex W g = ((Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).map ((((rho W π β g : GL (Fin W.rank) (Fv D.host.F v)) : Matrix (Fin W.rank) (Fin W.rank) (Fv D.host.F v)).mulVecLin).restrictScalars (Ov D v))).toAddSubgroup.relIndex (Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).toAddSubgroup * ((Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).map ((((rho W π β g⁻¹ : GL (Fin W.rank) (Fv D.host.F v)) : Matrix (Fin W.rank) (Fin W.rank) (Fv D.host.F v))ᵀ.mulVecLin).restrictScalars (Ov D v))).toAddSubgroup.relIndex (Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).toAddSubgroup := by
  first | exact @GlobalTheory.SplitIndexLocal.latIndex_split_local | exact GlobalTheory.SplitIndexLocal.latIndex_split_local | (intros; apply GlobalTheory.SplitIndexLocal.latIndex_split_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlIntegralInvMulOfLatticeMapEq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlIntegralInvMulOfLatticeMapEq
namespace GlobalTheory.SplitHecke

open Matrix

section

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ}

theorem isInt_of_mem_span_basisFun {w : Fin r → K}
    (hw : w ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r)))) (i : Fin r) :
    IsInt O (w i) := by
  show ∃ o : O, algebraMap O K o = w i
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases hij : i = j
    · subst hij
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Pi.basisFun_apply, Pi.single_apply, hij]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp [ha, hb]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by simp [ha, Algebra.smul_def]⟩

theorem intM_inv_mul_of_map_le {a b : GL (Fin r) K}
    (hle : (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        (((a : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) ≤
      (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        (((b : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)) :
    IntM O (b⁻¹ * a).1 := by
  intro i j
  have hmem := Submodule.mem_map_of_mem
    (f := ((a : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)
    (Submodule.subset_span ⟨j, rfl⟩ :
      Pi.basisFun K (Fin r) j ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))))
  obtain ⟨w, hw, hwe⟩ := hle hmem
  simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply] at hwe
  have hcol : ((b⁻¹ * a : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ Pi.basisFun K (Fin r) j = w := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hwe, Matrix.mulVec_mulVec, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hentry : (b⁻¹ * a).1 i j = w i := by
    rw [← hcol]
    simp [Pi.basisFun_apply]
  rw [hentry]
  exact isInt_of_mem_span_basisFun hw i

end

theorem gInt_inv_mul_of_map_eq : ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (r : ℕ)
    (h h' : GL (Fin r) K),
    (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        (((h : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) =
      (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        (((h' : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) →
    GInt O (h⁻¹ * h') := by
  intro O K _ _ _ r h h' heq
  show IntM O (h⁻¹ * h').1 ∧ IntM O ((h⁻¹ * h')⁻¹).1
  refine ⟨intM_inv_mul_of_map_le heq.ge, ?_⟩
  rw [_root_.mul_inv_rev, inv_inv]
  exact intM_inv_mul_of_map_le heq.le

end GlobalTheory.SplitHecke
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlIntegralInvMulOfLatticeMapEqStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glIntegral_inv_mul_of_lattice_map_eq : ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (r : ℕ) (h h' : GL (Fin r) K), (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((h : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) = (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((h' : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) → GlobalTheory.SplitHecke.GInt O (h⁻¹ * h') := by
  first | exact @GlobalTheory.SplitHecke.gInt_inv_mul_of_map_eq | exact GlobalTheory.SplitHecke.gInt_inv_mul_of_map_eq | (intros; apply GlobalTheory.SplitHecke.gInt_inv_mul_of_map_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexStandardLatticeTransposeInvDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexStandardLatticeTransposeInvDvr
noncomputable section

open Matrix

namespace GlobalTheory.IndexTranspose

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ}

abbrev stdLat (O K : Type) [CommRing O] [Field K] [Algebra O K] (r : ℕ) : Submodule O (Fin r → K) :=
  Submodule.span O (Set.range (Pi.basisFun K (Fin r)))

theorem mem_stdLat {v : Fin r → K} :
    v ∈ stdLat O K r ↔ ∃ w : Fin r → O, v = fun i => algebraMap O K (w i) := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, funext fun i => ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  · rintro ⟨w, rfl⟩
    refine ⟨w, funext fun i => ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]

def latOf (O : Type) [CommRing O] [Algebra O K] (A : Matrix (Fin r) (Fin r) K) : Submodule O (Fin r → K) :=
  (stdLat O K r).map ((A.mulVecLin).restrictScalars O)

theorem mem_latOf {A : Matrix (Fin r) (Fin r) K} {v : Fin r → K} :
    v ∈ latOf O A ↔ ∃ w ∈ stdLat O K r, A *ᵥ w = v := by
  simp [latOf, Submodule.mem_map]

theorem latOf_mul (A B : Matrix (Fin r) (Fin r) K) :
    latOf O (A * B) = (latOf O B).map ((A.mulVecLin).restrictScalars O) := by
  ext v
  rw [Submodule.mem_map, mem_latOf]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨B *ᵥ w, mem_latOf.2 ⟨w, hw, rfl⟩, by simp [Matrix.mulVec_mulVec]⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨w, hw, rfl⟩ := mem_latOf.1 hu
    exact ⟨w, hw, by simp [Matrix.mulVec_mulVec]⟩

theorem latOf_one : latOf O (1 : Matrix (Fin r) (Fin r) K) = stdLat O K r := by
  ext v
  rw [mem_latOf]
  simp

theorem map_mulVec_mem (N : Matrix (Fin r) (Fin r) O) {v : Fin r → K} (hv : v ∈ stdLat O K r) :
    (N.map (algebraMap O K)) *ᵥ v ∈ stdLat O K r := by
  obtain ⟨w, rfl⟩ := mem_stdLat.1 hv
  refine mem_stdLat.2 ⟨N *ᵥ w, funext fun i => ?_⟩
  exact (RingHom.map_mulVec (algebraMap O K) N w i).symm

theorem latOf_unimod (N : Matrix (Fin r) (Fin r) O) (hN : IsUnit N.det) :
    latOf O (N.map (algebraMap O K)) = stdLat O K r := by
  apply le_antisymm
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_latOf.1 hv
    exact map_mulVec_mem N hw
  · intro v hv
    refine mem_latOf.2 ⟨(N⁻¹).map (algebraMap O K) *ᵥ v, map_mulVec_mem _ hv, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hN,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

theorem det_map_ne_zero (N : Matrix (Fin r) (Fin r) O) (hN : IsUnit N.det) :
    (N.map (algebraMap O K)).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (hN.map _).ne_zero

theorem toAddSubgroup_map (A : Matrix (Fin r) (Fin r) K) (p : Submodule O (Fin r → K)) :
    (p.map ((A.mulVecLin).restrictScalars O)).toAddSubgroup =
      p.toAddSubgroup.map A.mulVecLin.toAddMonoidHom := by
  ext v
  simp [Submodule.mem_map, AddSubgroup.mem_map]

def idx (O : Type) [CommRing O] [Algebra O K] (A : Matrix (Fin r) (Fin r) K) : ℕ :=
  (latOf O A).toAddSubgroup.relIndex (stdLat O K r).toAddSubgroup

theorem idx_mul_right (A U : Matrix (Fin r) (Fin r) K) (hU : latOf O U = stdLat O K r) :
    idx O (A * U) = idx O A := by
  unfold idx
  rw [latOf_mul, hU]
  rfl

theorem idx_mul_left (U A : Matrix (Fin r) (Fin r) K) (hU : latOf O U = stdLat O K r) (hd : U.det ≠ 0) :
    idx O (U * A) = idx O A := by
  have hinj : Function.Injective U.mulVecLin.toAddMonoidHom :=
    fun a b hab => Matrix.mulVec_injective_of_det_ne_zero hd hab
  have e : (stdLat O K r).toAddSubgroup = (stdLat O K r).toAddSubgroup.map U.mulVecLin.toAddMonoidHom := by
    rw [← toAddSubgroup_map]
    exact congrArg Submodule.toAddSubgroup hU.symm
  unfold idx
  rw [latOf_mul, toAddSubgroup_map]
  conv_lhs => rw [e]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj

theorem idx_transpose [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K]
    (g : Matrix (Fin r) (Fin r) K) (hg : g.det ≠ 0) : idx O gᵀ = idx O g := by
  classical
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset (Fin r × Fin r)) (fun ij => g ij.1 ij.2)
  have hc' := fun ij : Fin r × Fin r => RingHom.mem_rangeS.1 (hc ij (Finset.mem_univ ij))
  choose N0 hN0 using hc'
  set a : K := algebraMap O K (c : O) with ha_def
  have ha : a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors c.2
  let N : Matrix (Fin r) (Fin r) O := Matrix.of fun i j => N0 (i, j)
  have hNmap : N.map (algebraMap O K) = a • g := by
    ext i j
    simp only [N, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, hN0 (i, j), ha_def, smul_eq_mul, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
  have hNdet : N.det ≠ 0 := by
    intro h0
    have e := RingHom.map_det (algebraMap O K) N
    rw [h0, map_zero, RingHom.mapMatrix_apply, hNmap, Matrix.det_smul] at e
    exact mul_ne_zero (pow_ne_zero _ ha) hg e.symm
  obtain ⟨P, Q, hP, hQ, d, hPQ⟩ := GlobalTheory.SmithBetween.exists_mul_eq_mul_diagonal N hNdet
  set D : Matrix (Fin r) (Fin r) K := a⁻¹ • Matrix.diagonal (fun i => algebraMap O K (d i)) with hD
  have hmap := congrArg (fun M : Matrix (Fin r) (Fin r) O => M.map (algebraMap O K)) hPQ
  simp only [Matrix.map_mul, hNmap, Matrix.diagonal_map (map_zero _)] at hmap
  have key : g * Q.map (algebraMap O K) = P.map (algebraMap O K) * D := by
    rw [hD, Matrix.mul_smul, ← hmap, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hDT : Dᵀ = D := by
    rw [hD, Matrix.transpose_smul, Matrix.diagonal_transpose]
  have hQT : IsUnit Qᵀ.det := by rwa [Matrix.det_transpose]
  have hPT : IsUnit Pᵀ.det := by rwa [Matrix.det_transpose]
  have e1 : idx O g = idx O D := by
    rw [← idx_mul_right g _ (latOf_unimod Q hQ), key,
      idx_mul_left _ _ (latOf_unimod P hP) (det_map_ne_zero P hP)]
  have e2 : idx O gᵀ = idx O D := by
    have hQ' := latOf_unimod (K := K) Qᵀ hQT
    rw [Matrix.transpose_map] at hQ'
    have hP' := latOf_unimod (K := K) Pᵀ hPT
    rw [Matrix.transpose_map] at hP'
    have hQd := det_map_ne_zero (K := K) Qᵀ hQT
    rw [Matrix.transpose_map] at hQd
    rw [← idx_mul_left _ gᵀ hQ' hQd, ← Matrix.transpose_mul, key, Matrix.transpose_mul, hDT,
      idx_mul_right _ _ hP']
  rw [e1, e2]

theorem relIndex_transpose_inv : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (h : GL (Fin r) K), ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map ((((h⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ.mulVecLin).restrictScalars O)).toAddSubgroup.relIndex (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup = (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup.relIndex ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((h : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup := by
  intro O K _ _ _ _ _ _ _ r h
  set g : Matrix (Fin r) (Fin r) K := ((h⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) with hg_def
  set hM : Matrix (Fin r) (Fin r) K := (h : Matrix (Fin r) (Fin r) K) with hM_def
  have hgh : g * hM = 1 := Units.inv_mul h
  have hg : g.det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det hgh
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at e
    exact zero_ne_one e
  have hginj : Function.Injective g.mulVecLin.toAddMonoidHom :=
    fun a b hab => Matrix.mulVec_injective_of_det_ne_zero hg hab
  change idx O gᵀ = (stdLat O K r).toAddSubgroup.relIndex (latOf O hM).toAddSubgroup
  have e1 : (latOf O g).toAddSubgroup = (stdLat O K r).toAddSubgroup.map g.mulVecLin.toAddMonoidHom :=
    toAddSubgroup_map g _
  have e2 : (stdLat O K r).toAddSubgroup = (latOf O hM).toAddSubgroup.map g.mulVecLin.toAddMonoidHom := by
    rw [← toAddSubgroup_map, ← latOf_mul, hgh, latOf_one]
  rw [idx_transpose g hg, ← AddSubgroup.relIndex_map_map_of_injective _ _ hginj, ← e1, ← e2]
  rfl

end GlobalTheory.IndexTranspose
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexStandardLatticeTransposeInvDvrStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_standardLattice_transpose_inv_dvr : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (h : GL (Fin r) K), ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map ((((h⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ.mulVecLin).restrictScalars O)).toAddSubgroup.relIndex (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup = (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup.relIndex ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((h : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup := by
  first | exact @GlobalTheory.IndexTranspose.relIndex_transpose_inv | exact GlobalTheory.IndexTranspose.relIndex_transpose_inv | (intros; apply GlobalTheory.IndexTranspose.relIndex_transpose_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceLatticeIndexSumLeZetaSqSubOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.SplitHecke

noncomputable section

namespace GlobalTheory.SplitIndexSum
open GlobalTheory.AdelicLatMove (mt_mul mt_one)

abbrev stdLat (O K : Type) [CommRing O] [Field K] [Algebra O K] (r : ℕ) : Submodule O (Fin r → K) :=
  Submodule.span O (Set.range (Pi.basisFun K (Fin r)))

abbrev movLat (O K : Type) [CommRing O] [Field K] [Algebra O K] {r : ℕ} (h : GL (Fin r) K) : Submodule O (Fin r → K) :=
  (stdLat O K r).map (((h : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)

theorem suppAt_mul {D : D7} {e : AE D} {V : HSp D} {g g' : GA D V} (hg : SuppAt e V g) (hg' : SuppAt e V g') :
    SuppAt e V (g * g') := by
  have h : (e + cA D e) • (mt V g - 1) = mt V g - 1 := Matrix.ext fun i j => hg i j
  have h' : (e + cA D e) • (mt V g' - 1) = mt V g' - 1 := Matrix.ext fun i j => hg' i j
  have h1 : mt V (g * g') - 1 = (mt V g - 1) * mt V g' + (mt V g' - 1) := by
    rw [mt_mul, Matrix.sub_mul, Matrix.one_mul]; abel
  have h2 : (e + cA D e) • (mt V (g * g') - 1) = mt V (g * g') - 1 := by
    rw [h1, smul_add, ← Matrix.smul_mul, h, h']
  exact fun i j => congrFun (congrFun h2 i) j

theorem chart_of_finIdem {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D}
    (hv : IsFinIdem D v (e + cA D e)) (he : IsSplitIdem D e) : ∃ π : AE D →+* Fv D.host.F v, Chart e v π := by
  obtain ⟨v', π, hπ⟩ := GlobalTheory.T.exists_place_chart_of_splitIdempotent e he
  obtain ⟨ε, ⟨α, rfl, hα1, hα0⟩, hf⟩ := hv
  have hπe : π e = 1 := by
    have : π (1 - e) = 0 := (hπ.2.1 _).2 (by rw [mul_sub, mul_one, he.1, sub_self])
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  have hπc : π (cA D e) = 0 := (hπ.2.1 _).2 he.2.1
  have h1 : π (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 1 := by
    rw [← hf, map_add (f := _), hπe, hπc, add_zero]
  rw [hπ.2.2.1] at h1
  by_cases hvv : v' = v
  · subst hvv; exact ⟨π, hπ⟩
  · exfalso
    have h2 := hα0 v' hvv
    have h3 : sndA D.host.F (pairA D.host.F 0 α) = α := rfl
    rw [h3, h2] at h1
    exact zero_ne_one h1
theorem gInt_of_movLat_eq (O K : Type) [CommRing O] [Field K] [Algebra O K] {r : ℕ}
    (h h' : GL (Fin r) K) (hh : movLat O K h = movLat O K h') : GInt O (h⁻¹ * h') :=
  GlobalTheory.T.glIntegral_inv_mul_of_lattice_map_eq O K r h h' hh

theorem latIndex_eq_split : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v),
    IsSplitIdem D e → Chart e v π → ∀ (W : HSp D) (β : GL (Fin W.rank) (Fv D.host.F v)), Frame W e π β →
    ∀ g : GA D W, SuppAt e W g →
      latIndex W g = (movLat (Ov D v) (Fv D.host.F v) (rho W π β g)).toAddSubgroup.relIndex
          (stdLat (Ov D v) (Fv D.host.F v) W.rank).toAddSubgroup *
        (stdLat (Ov D v) (Fv D.host.F v) W.rank).toAddSubgroup.relIndex
          (movLat (Ov D v) (Fv D.host.F v) (rho W π β g)).toAddSubgroup := by
  intro D e v π he hπ W β hβ g hg
  haveI := Formalism.UG.P.glint_finite_residueField (F := D.host.F) v
  rw [GlobalTheory.T.lattice_index_split_place_eq_product_local e v π he hπ W β hβ g hg, map_inv, GlobalTheory.T.relIndex_standardLattice_transpose_inv_dvr]

theorem indexSum_split : ∀ (D : D7) (W : HSp D) (n : ℕ), 2 * W.rank + 5 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D), IsFinIdem D v f → (∃ e, Formalism.L2.Theta.IsSplitIdem D e ∧ e + Formalism.L2.Theta.cA D e = f) → ∀ C : Finset (GA D W), (∀ g ∈ C, SuppF W f g ∧ g ∉ KsphC W ∅) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ KsphC W ∅ → g = g') → ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) ≤ (∏ i ∈ Finset.range W.rank, (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ ((i : ℝ) - (n : ℝ) / 2))⁻¹) ^ 2 - 1 := by
  classical
  intro D W n hn v f hf ⟨e, he, hef⟩ C hC hdist
  subst hef
  obtain ⟨π, hπ⟩ := chart_of_finIdem hf he
  obtain ⟨β, hβ⟩ := GlobalTheory.SplitFrame.exists_frame e v π he hπ W
  haveI := Formalism.UG.P.glint_finite_residueField (F := D.host.F) v
  set O := Ov D v
  set K := Fv D.host.F v
  set σ : ℝ := (n : ℝ) / 2 with hσ
  have hsupp : ∀ g ∈ C, SuppAt e W g := fun g hg => (hC g hg).1
  let Φ : GL (Fin W.rank) K → ℝ := fun h =>
    ((((movLat O K h).toAddSubgroup.relIndex (stdLat O K W.rank).toAddSubgroup : ℕ) : ℝ) *
      (((stdLat O K W.rank).toAddSubgroup.relIndex (movLat O K h).toAddSubgroup : ℕ) : ℝ)) ^ (-σ)
  have hK : ∀ g, SuppAt e W g → (g ∈ KsphC W ∅ ↔ GInt O (rho W π β g)) :=
    GlobalTheory.SplitHecke.Stab.mem_KsphC_iff_gInt e v π he hπ W β hβ
  have hterm : ∀ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) = Φ (rho W π β g) := by
    intro g hg
    rw [latIndex_eq_split e v π he hπ W β hβ g (hsupp g hg), Nat.cast_mul, neg_div]
  have hinj : ∀ g ∈ C, ∀ g' ∈ C, movLat O K (rho W π β g) = movLat O K (rho W π β g') → g = g' := by
    intro g hg g' hg' hm
    have h1 := gInt_of_movLat_eq O K _ _ hm
    rw [← map_inv, ← map_mul] at h1
    exact hdist g hg g' hg' ((hK _ (suppAt_mul (GlobalTheory.SplitHecke.Stab.suppAt_inv (hsupp g hg)) (hsupp g' hg'))).2 h1)
  have hone : ∀ g ∈ C, movLat O K (1 : GL (Fin W.rank) K) ≠ movLat O K (rho W π β g) := by
    intro g hg hm
    have h1 := gInt_of_movLat_eq O K _ _ hm
    rw [inv_one, one_mul] at h1
    exact (hC g hg).2 ((hK g (hsupp g hg)).2 h1)
  have hnot : (1 : GL (Fin W.rank) K) ∉ C.image (rho W π β) := by
    intro h1
    obtain ⟨g, hg, hg1⟩ := Finset.mem_image.1 h1
    exact hone g hg (by rw [hg1])
  have hsum : ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) = ∑ h ∈ C.image (rho W π β), Φ h := by
    rw [Finset.sum_image (fun g hg g' hg' he' => hinj g hg g' hg' (congrArg (movLat O K) he'))]
    exact Finset.sum_congr rfl hterm
  have hΦ1 : Φ 1 = 1 := by
    have : movLat O K (1 : GL (Fin W.rank) K) = stdLat O K W.rank := by
      simp [movLat]
    simp only [Φ, this, AddSubgroup.relIndex_self, Nat.cast_one, mul_one, Real.one_rpow]
  have hσr : (W.rank : ℝ) - 1 < σ := by
    rw [hσ]; have : (2 * W.rank + 5 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hbig := GlobalTheory.T.sum_lattice_pairs_index_rpow_le O K W.rank σ hσr (insert 1 (C.image (rho W π β))) (by
    intro h hh h' hh' hm
    rcases Finset.mem_insert.1 hh with rfl | hh <;> rcases Finset.mem_insert.1 hh' with rfl | hh'
    · rfl
    · obtain ⟨g', hg', rfl⟩ := Finset.mem_image.1 hh'
      exact absurd hm (hone g' hg')
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hh
      exact absurd hm.symm (hone g hg)
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hh
      obtain ⟨g', hg', rfl⟩ := Finset.mem_image.1 hh'
      rw [hinj g hg g' hg' hm])
  rw [Finset.sum_insert hnot] at hbig
  have hq : (Nat.card (IsLocalRing.ResidueField O) : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by
    rw [Formalism.UG.P.tjcosets_card_residue]; rfl
  rw [hq] at hbig
  rw [hsum]
  change Φ 1 + ∑ h ∈ C.image (rho W π β), Φ h ≤ _ at hbig
  rw [hΦ1] at hbig
  rw [hσ] at hbig
  linarith

end GlobalTheory.SplitIndexSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceLatticeIndexSumLeZetaSqSubOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_lattice_index_sum_le_zeta_sq_sub_one : ∀ (D : D7) (W : HSp D) (n : ℕ), 2 * W.rank + 5 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D), IsFinIdem D v f → (∃ e, Formalism.L2.Theta.IsSplitIdem D e ∧ e + Formalism.L2.Theta.cA D e = f) → ∀ C : Finset (GA D W), (∀ g ∈ C, SuppF W f g ∧ g ∉ KsphC W ∅) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ KsphC W ∅ → g = g') → ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) ≤ (∏ i ∈ Finset.range W.rank, (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ ((i : ℝ) - (n : ℝ) / 2))⁻¹) ^ 2 - 1 := by
  first | exact @GlobalTheory.SplitIndexSum.indexSum_split | exact GlobalTheory.SplitIndexSum.indexSum_split | (intros; apply GlobalTheory.SplitIndexSum.indexSum_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneSubSumLeProdOneSubRange
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem one_sub_sum_le_prod_one_sub_range (x : ℕ → ℝ) (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1)
    (r : ℕ) : 1 - ∑ i ∈ Finset.range r, x i ≤ ∏ i ∈ Finset.range r, (1 - x i) := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have hS : 0 ≤ ∑ i ∈ Finset.range n, x i := Finset.sum_nonneg (fun i _ => h0 i)
    have hx1 : 0 ≤ 1 - x n := by linarith [h1 n]
    have := mul_le_mul_of_nonneg_right ih hx1
    nlinarith [h0 n]

theorem sum_rpow_sub_le (q : ℝ) (r : ℕ) (σ : ℝ) (hq : 2 ≤ q) (hσ : (r : ℝ) + 5 / 2 ≤ σ) :
    ∑ i ∈ Finset.range r, q ^ ((i : ℝ) - σ) ≤ 2 / q ^ 3 := by
  have hq0 : 0 < q := by linarith
  have hterm : ∀ i : ℕ, q ^ ((i : ℝ) - σ) = q ^ i / q ^ σ := by
    intro i; rw [Real.rpow_sub hq0, Real.rpow_natCast]
  simp_rw [hterm]
  rw [← Finset.sum_div, geom_sum_eq (by linarith : q ≠ 1)]
  have hqs : 0 < q ^ σ := Real.rpow_pos_of_pos hq0 σ
  have hrs : q ^ r / q ^ σ ≤ 1 / q ^ 2 := by
    have h1 : q ^ r / q ^ σ = q ^ ((r : ℝ) - σ) := by rw [Real.rpow_sub hq0, Real.rpow_natCast]
    have h2 : q ^ ((r : ℝ) - σ) ≤ q ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h3 : q ^ (-2 : ℝ) = 1 / q ^ 2 := by
      rw [Real.rpow_neg hq0.le]; norm_num
    rw [h1]; linarith
  have hq1 : 0 < q - 1 := by linarith
  have hpr : 0 < q ^ r := pow_pos hq0 r
  calc (q ^ r - 1) / (q - 1) / q ^ σ ≤ q ^ r / (q - 1) / q ^ σ := by
        gcongr; linarith
    _ = (q ^ r / q ^ σ) / (q - 1) := by ring
    _ ≤ (1 / q ^ 2) / (q - 1) := by gcongr
    _ ≤ 2 / q ^ 3 := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [pow_pos hq0 2, pow_pos hq0 3]

theorem lattice_zeta_sq_bound : ∀ (q : ℝ) (r : ℕ) (σ : ℝ), 2 ≤ q → (r : ℝ) + 5 / 2 ≤ σ →
    (∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - σ))⁻¹) ^ 2 - 1 < 1 ∧
    (∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - σ))⁻¹) ^ 2 - 1 ≤ 16 * q ^ (-(3 : ℝ)) := by
  intro q r σ hq hσ
  have hq0 : 0 < q := by linarith
  set x : ℕ → ℝ := fun i => q ^ ((i : ℝ) - σ) with hx
  have hS := sum_rpow_sub_le q r σ hq hσ
  have hq3 : 8 ≤ q ^ 3 := by nlinarith [sq_nonneg q, mul_le_mul hq hq (by norm_num) hq0.le]
  set w : ℝ := 1 / q ^ 3 with hw
  have hw0 : 0 < w := by positivity
  have hw8 : w ≤ 1 / 8 := by
    rw [hw]; exact one_div_le_one_div_of_le (by norm_num) hq3
  have h0 : ∀ i, 0 ≤ x i := fun i => (Real.rpow_pos_of_pos hq0 _).le

  have hD := one_sub_sum_le_prod_one_sub_range (fun i => min (x i) 1)
    (fun i => le_min (h0 i) zero_le_one) (fun i => min_le_right _ _) r
  have hmin : ∀ i ∈ Finset.range r, min (x i) 1 = x i := by
    intro i hi
    apply min_eq_left
    have : x i ≤ ∑ j ∈ Finset.range r, x j :=
      Finset.single_le_sum (fun j _ => h0 j) hi
    have : 2 / q ^ 3 ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  rw [Finset.sum_congr rfl hmin, Finset.prod_congr rfl (fun i hi => by rw [hmin i hi])] at hD
  set D := ∏ i ∈ Finset.range r, (1 - x i) with hDdef
  have h2w : 2 / q ^ 3 = 2 * w := by rw [hw]; ring
  have hDlow : 1 - 2 * w ≤ D := by linarith
  have hDpos : 0 < D := by linarith
  have hP : ∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - σ))⁻¹ = D⁻¹ := by
    rw [Finset.prod_inv_distrib]
  have hrhs : 16 * q ^ (-(3 : ℝ)) = 16 * w := by
    rw [Real.rpow_neg hq0.le, hw]; norm_num
  rw [hP, hrhs]
  have ha : 0 < 1 - 2 * w := by linarith
  have hPle : D⁻¹ ≤ (1 - 2 * w)⁻¹ := inv_anti₀ ha hDlow
  have hP0 : 0 ≤ D⁻¹ := inv_nonneg.mpr hDpos.le
  have hsq : D⁻¹ ^ 2 ≤ ((1 - 2 * w)⁻¹) ^ 2 := pow_le_pow_left₀ hP0 hPle 2
  have hkey : ((1 - 2 * w)⁻¹) ^ 2 ≤ 1 + 16 * w := by
    rw [inv_pow, inv_le_iff_one_le_mul₀ (by positivity)]
    nlinarith [mul_pos hw0 hw0]
  have hkey2 : ((1 - 2 * w)⁻¹) ^ 2 < 2 := by
    rw [inv_pow, inv_lt_iff_one_lt_mul₀ (by positivity)]
    nlinarith [mul_pos hw0 hw0]
  constructor <;> linarith

end GlobalTheory
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.IndexCount

theorem rank_le (D : D7) (i : Fin D.R.m) : 2 * (Wc D i).rank + 5 ≤ (Vc D i).rank := by
  have hV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have := D.R.rank_add_five_le
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  omega

theorem two_le_absNorm {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  have : 2 ≤ Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast this

theorem indexSum_of_rank {D : D7} (W : HSp D) (n : ℕ) (hn : 2 * W.rank + 5 ≤ n) : IndexSum W n := by
  let q : HeightOneSpectrum (𝓞 D.host.F) → ℝ := fun v => (Ideal.absNorm v.asIdeal : ℝ)
  let z : HeightOneSpectrum (𝓞 D.host.F) → ℝ := fun v =>
    (∏ i ∈ Finset.range W.rank, (1 - q v ^ ((i : ℝ) - (n : ℝ) / 2))⁻¹) ^ 2 - 1
  have hq : ∀ v, 2 ≤ q v := fun v => two_le_absNorm v
  have hσ : (W.rank : ℝ) + 5 / 2 ≤ (n : ℝ) / 2 := by
    have : ((2 * W.rank + 5 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at this; linarith
  have hz : ∀ v, z v < 1 ∧ z v ≤ 16 * q v ^ (-(3 : ℝ)) := fun v => GlobalTheory.lattice_zeta_sq_bound (q v) W.rank ((n : ℝ) / 2) (hq v) hσ
  have h8 : ∀ v, 8 * q v ^ (-(4 : ℝ)) ≤ 8 * q v ^ (-(3 : ℝ)) ∧ 8 * q v ^ (-(4 : ℝ)) ≤ 1 / 2 := by
    intro v
    have h1 : (1 : ℝ) ≤ q v := le_trans (by norm_num) (hq v)
    have hle : q v ^ (-(4 : ℝ)) ≤ q v ^ (-(3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    refine ⟨by linarith, ?_⟩
    have : q v ^ (-(4 : ℝ)) ≤ (2 : ℝ) ^ (-(4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (hq v) (by norm_num)
    have h2 : (2 : ℝ) ^ (-(4 : ℝ)) = 1 / 16 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    rw [h2] at this; linarith
  refine ⟨fun v => max (z v) (8 * q v ^ (-(4 : ℝ))), ?_, ?_, ?_⟩
  · have hs : Summable fun v : HeightOneSpectrum (𝓞 D.host.F) => 16 * q v ^ (-(3 : ℝ)) :=
      (GlobalTheory.summable_absNorm_rpow_heightOneSpectrum D.host.F 3 (by norm_num)).mul_left 16
    refine Summable.of_nonneg_of_le (fun v => ?_) (fun v => ?_) hs
    · exact le_trans (by positivity) (le_max_right _ _)
    · refine max_le (hz v).2 ?_
      have h3 : 0 ≤ q v ^ (-(3 : ℝ)) := by positivity
      linarith [(h8 v).1]
  · intro v
    exact max_lt (hz v).1 (by linarith [(h8 v).2])
  · intro v f hf C hC hd
    rcases GlobalTheory.T.finite_place_split_idempotent_or_inert D v f hf with hs | hi
    · exact le_trans (GlobalTheory.T.split_place_lattice_index_sum_le_zeta_sq_sub_one D W n hn v f hf hs C hC hd) (le_max_left _ _)
    · exact le_trans (GlobalTheory.T.inertPlace_latticeIndex_sum_bound D W n hn v f hf hi C hC hd) (le_max_right _ _)

theorem indexSum_holds : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i, IndexSum (Wc D i) (Vc D i).rank := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ _ i
  exact indexSum_of_rank (Wc D i) (Vc D i).rank (rank_le D i)

end GlobalTheory.IndexCount

end
