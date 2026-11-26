module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntegralIntegrable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitMpOmjExtIff
set_option autoImplicit false

noncomputable section

open CategoryTheory KaehlerDifferential

namespace GlobalTheory.CechDR.FormExtJ

open GlobalTheory.CatCoh

section Inst

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (j : ℕ)

@[reducible] def opModJ : Module Bᵐᵒᵖ (Om R B j) :=
  Module.compHom _ ((RingHom.id B).fromOpposite mul_comm)

attribute [local instance] opModJ

theorem isCentralScalarJ : IsCentralScalar B (Om R B j) := ⟨fun _ _ ↦ rfl⟩

theorem isScalarTowerJ : IsScalarTower R Bᵐᵒᵖ (Om R B j) := ⟨fun r b m ↦ smul_assoc r b.unop m⟩

end Inst

attribute [local instance] opModJ isCentralScalarJ isScalarTowerJ

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ)

def extMapJ {T T' : C} (φ : T ⟶ T') :
    TrivSqZeroExt (F.obj T) (Om R (F.obj T) j) →ₐ[R] TrivSqZeroExt (F.obj T') (Om R (F.obj T') j) where
  toFun c := TrivSqZeroExt.inl (mp F φ c.fst) + TrivSqZeroExt.inr (pOm F j φ c.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [pOm_smul]
  commutes' r := by
    ext
    · simp [TrivSqZeroExt.algebraMap_eq_inl']
    · simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_extMapJ {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j)) :
    (extMapJ F j φ c).fst = mp F φ c.fst := by
  simp [extMapJ]

theorem snd_extMapJ {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j)) :
    (extMapJ F j φ c).snd = pOm F j φ c.snd := by
  simp [extMapJ]

def omjExt : C ⥤ CommAlgCat.{0} R where
  obj T := CommAlgCat.of R (TrivSqZeroExt (F.obj T) (Om R (F.obj T) j))
  map φ := CommAlgCat.ofHom (extMapJ F j φ)
  map_id T := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext
    ((fst_extMapJ F j _ c).trans (mp_id F T _)) ((snd_extMapJ F j _ c).trans (pOm_id F _)))
  map_comp φ ψ := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext
    ((fst_extMapJ F j _ c).trans ((mp_comp F φ ψ _).trans (by
      change _ = ((extMapJ F j ψ) (extMapJ F j φ c)).fst
      rw [fst_extMapJ, fst_extMapJ])))
    ((snd_extMapJ F j _ c).trans ((pOm_comp F φ ψ _).trans (by
      change _ = ((extMapJ F j ψ) (extMapJ F j φ c)).snd
      rw [snd_extMapJ, snd_extMapJ]))))

theorem mp_omjExt_inr {T T' : C} (φ : T ⟶ T') (x : Om R (F.obj T) j) :
    mp (omjExt F j) φ (TrivSqZeroExt.inr x : (omjExt F j).obj T) =
      (TrivSqZeroExt.inr (pOm F j φ x) : (omjExt F j).obj T') := by
  change extMapJ F j φ (TrivSqZeroExt.inr x) = _
  exact TrivSqZeroExt.ext ((fst_extMapJ F j φ _).trans (by simp)) ((snd_extMapJ F j φ _).trans (by simp))

theorem snd_mp_omjExt {T T' : C} (φ : T ⟶ T') (c : (omjExt F j).obj T) :
    (mp (omjExt F j) φ c).snd = pOm F j φ c.snd := snd_extMapJ F j φ c

theorem isUnit_mp_omjExt_iff {T S : C} (u : T ⟶ S) (c : (omjExt F j).obj T) :
    IsUnit (mp (omjExt F j) u c) ↔ IsUnit (mp F u c.fst) :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.trans (iff_of_eq (congrArg IsUnit (fst_extMapJ F j u c)))

theorem span_inlJ_eq_top {S : C} {n : ℕ} {b : Fin n → F.obj S} (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun i ↦ (TrivSqZeroExt.inl (b i) : (omjExt F j).obj S)) = ⊤ := by
  have := congrArg (Ideal.map (TrivSqZeroExt.inlHom (F.obj S) (Om R (F.obj S) j))) hb
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  exact this

end GlobalTheory.CechDR.FormExtJ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarAction
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv.Intertwine

variable {A : Type} [CommRing A] [IsDomain A] {h : ℕ}

end GlobalTheory.DetInv.Intertwine

namespace GlobalTheory.DetInv

open Matrix TensorProduct in
private theorem matrix_eq_zero_of_mul_right_cancel_lemma {R : Type} [CommRing R] [IsDomain R] {n : ℕ}
    {A B X : Matrix (Fin n) (Fin n) R} {c : R} (hAB : A * B = c • (1 : Matrix (Fin n) (Fin n) R))
    (hc : c ≠ 0) (hX : X * B = 0) : X = 0 := by
  have hdet : A.det * B.det = c ^ n := by
    rw [← Matrix.det_mul, hAB, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hB : B.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdet
    exact pow_ne_zero n hc hdet.symm
  have h1 : X * B * B.adjugate = B.det • X := by
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
  rw [hX, Matrix.zero_mul] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left hB

open Matrix TensorProduct in
private theorem matrix_eq_zero_of_mul_left_cancel_lemma_2 {R : Type} [CommRing R] [IsDomain R] {n : ℕ}
    {A B Y : Matrix (Fin n) (Fin n) R} {c : R} (hAB : A * B = c • (1 : Matrix (Fin n) (Fin n) R))
    (hc : c ≠ 0) (hY : A * Y = 0) : Y = 0 := by
  have hdet : A.det * B.det = c ^ n := by
    rw [← Matrix.det_mul, hAB, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hA : A.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact pow_ne_zero n hc hdet.symm
  have h1 : A.adjugate * (A * Y) = A.det • Y := by
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [hY, Matrix.mul_zero] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left hA


open Matrix TensorProduct in
theorem _root_.GlobalTheory.DetInv.datum_scalar_intertwine : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (h : ℕ) (D : _root_.GlobalTheory.Sandwich.Datum ε h Λ), (∀ c : ℤ_[p], D.ρM (algebraMap ℤ_[p] Λ c) = _root_.GlobalTheory.Sandwich.ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O))) ∧ D.F * D.G = _root_.GlobalTheory.Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O)) ∧ (∀ l, D.G * D.ρM l = _root_.GlobalTheory.DetInv.rhoTA D l * D.G) ∧ (∀ l, D.Ψ * (D.ρM l).map (_root_.GlobalTheory.Sandwich.phiInv p O) = D.ρM l * D.Ψ) ∧ ∀ l, D.Ψ' * D.ρM l = (D.ρM l).map (_root_.GlobalTheory.Sandwich.phiInv p O) * D.Ψ' := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ h D
  haveI : IsDomain (_root_.GlobalTheory.Sandwich.Ainf p O) := _root_.GlobalTheory.AinfXi.isDomain_ainf hv
  set F := D.F with hF
  set G := D.G with hG
  set Ψ := D.Ψ with hΨ
  set Ψ' := D.Ψ' with hΨ'
  set M := D.ρM with hM
  set φ := _root_.GlobalTheory.Sandwich.phiInv p O with hφ
  have hμ : _root_.GlobalTheory.Sandwich.mu ε ≠ 0 :=
    (_root_.GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε).2.1
  have hμ' : φ (_root_.GlobalTheory.Sandwich.mu ε) ≠ 0 := by
    rw [hφ, _root_.GlobalTheory.Sandwich.phiInv_mu]
    exact (_root_.GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε).2.2
  have hξ : _root_.GlobalTheory.Sandwich.xi ε ≠ 0 := by
    intro h0
    have h1 := _root_.GlobalTheory.AinfXi.xi_nzd hv ε hε 1 (by rw [h0, mul_zero])
    exact one_ne_zero h1
  have hGF : G * F = _root_.GlobalTheory.Sandwich.mu ε • 1 := D.G_mul_F
  have hFΨ : F = Ψ * F.map φ := D.F_eq
  have hΨΨ' : Ψ * Ψ' = _root_.GlobalTheory.Sandwich.xi ε • 1 := D.Ψ_mul
  have hFT : ∀ l, F * _root_.GlobalTheory.DetInv.rhoTA D l = M l * F := fun l =>
    D.F_act l

  have hFG : F * G = _root_.GlobalTheory.Sandwich.mu ε • 1 := by
    have h0 : (F * G - _root_.GlobalTheory.Sandwich.mu ε • 1) * F = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hGF, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.one_mul, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGF hμ h0)

  have hTφ : ∀ l, (_root_.GlobalTheory.DetInv.rhoTA D l).map φ = _root_.GlobalTheory.DetInv.rhoTA D l := by
    intro l
    unfold _root_.GlobalTheory.DetInv.rhoTA
    rw [Matrix.map_map]
    congr 1
    funext x
    exact _root_.GlobalTheory.DetInv.PsiPhi.phiInv_ofPadic x

  have hFTφ : ∀ l, F.map φ * _root_.GlobalTheory.DetInv.rhoTA D l = (M l).map φ * F.map φ := by
    intro l
    have := congrArg (fun X => X.map φ) (hFT l)
    simp only [Matrix.map_mul] at this
    rwa [hTφ] at this
  have hGFφ : G.map φ * F.map φ = φ (_root_.GlobalTheory.Sandwich.mu ε) • 1 := by
    rw [← Matrix.map_mul, hGF]
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp

  have hΨM : ∀ l, Ψ * (M l).map φ = M l * Ψ := by
    intro l
    have h0 : (Ψ * (M l).map φ - M l * Ψ) * F.map φ = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, ← hFTφ, ← Matrix.mul_assoc, ← hFΨ, hFT,
        Matrix.mul_assoc, ← hFΨ, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGFφ hμ' h0)
  refine ⟨?_, hFG, ?_, hΨM, ?_⟩
  · intro c
    have hT : _root_.GlobalTheory.DetInv.rhoTA D (algebraMap ℤ_[p] Λ c) =
        _root_.GlobalTheory.Sandwich.ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O)) := by
      unfold _root_.GlobalTheory.DetInv.rhoTA
      rw [AlgHom.commutes]
      ext i j
      simp [Matrix.algebraMap_matrix_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h1 := hFT (algebraMap ℤ_[p] Λ c)
    rw [hT] at h1
    have h0 : (M (algebraMap ℤ_[p] Λ c) - _root_.GlobalTheory.Sandwich.ofPadic p O c • 1) * F = 0 := by
      rw [Matrix.sub_mul, ← h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.one_mul, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGF hμ h0)
  · intro l
    have h0 : (G * M l - _root_.GlobalTheory.DetInv.rhoTA D l * G) * F = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, ← hFT, ← Matrix.mul_assoc, hGF, Matrix.mul_assoc,
        hGF, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGF hμ h0)
  · intro l
    have h0 : Ψ * (Ψ' * M l - (M l).map φ * Ψ') = 0 := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hΨΨ', ← Matrix.mul_assoc, hΨM, Matrix.mul_assoc,
        hΨΨ', Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_left_cancel_lemma_2 hΨΨ' hξ h0)

end GlobalTheory.DetInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPEqOfTranslInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPEqOfTranslInvariant
set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv in
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) in
private theorem exists_mulBy_pow_eq_comp_resOne' {p : ℕ} {R : Type} [CommRing R]
    (G : _root_.GlobalTheory.PDivGroup p R) (n : ℕ) :
    ∃ M : G.A 1 →ₐc[R] G.A (n + 1),
      ∀ a : G.A (n + 1),
        _root_.GlobalTheory.PDiv.mulBy R (G.A (n + 1)) (p ^ n) a = M (G.resOne n a) := by
  induction n with
  | zero =>
    refine ⟨BialgHom.id R (G.A 1), fun a => ?_⟩
    have h := _root_.GlobalTheory.PDiv.mulBy_comp (BialgHom.id R (G.A 1)) 1
    rw [pow_one, toConv_ofConv] at h
    rw [_root_.GlobalTheory.PDivGroup.resOne_zero]
    simpa using congrArg (fun f : G.A 1 →ₐc[R] G.A 1 => f a) h
  | succ n ih =>
    obtain ⟨M, hM⟩ := ih
    refine ⟨(G.mulP (n + 1)).comp M, fun a => ?_⟩
    rw [pow_succ, ← _root_.GlobalTheory.PDiv.mulBy_mulBy, ← _root_.GlobalTheory.PDivGroup.mulP_res,
      ← _root_.GlobalTheory.PDiv.map_mulBy, hM, _root_.GlobalTheory.PDivGroup.resOne_succ, BialgHom.comp_apply]


set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv in
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) in
theorem _root_.GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R)
    (n : ℕ) (a : G.A (n + 1))
    (ha : G.transl n a = a ⊗ₜ[R] 1) :
    ∃ e : G.A n, G.mulP n e = a := by
  obtain ⟨M, hM⟩ := exists_mulBy_pow_eq_comp_resOne' G n
  have key : ∀ χ φ : _root_.GlobalTheory.CartierDual R (G.A (n + 1)),
      (χ * _root_.GlobalTheory.CartierDual.map
        (_root_.GlobalTheory.PDiv.mulBy R (G.A (n + 1)) (p ^ n)) φ).ofConv a =
        χ.ofConv a * φ.ofConv 1 := by
    intro χ φ
    have h1 : (_root_.GlobalTheory.CartierDual.map
        (_root_.GlobalTheory.PDiv.mulBy R (G.A (n + 1)) (p ^ n)) φ).ofConv =
        (φ.ofConv ∘ₗ (M : G.A 1 →ₗ[R] G.A (n + 1))) ∘ₗ
          (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1) := by
      ext x
      simp [_root_.GlobalTheory.CartierDual.map_apply, hM]
    rw [_root_.GlobalTheory.CartierDual.mul_apply, _root_.GlobalTheory.CartierDual.pair_tmul, h1]
    have h2 : ∀ t, TensorProduct.map χ.ofConv
        ((φ.ofConv ∘ₗ (M : G.A 1 →ₗ[R] G.A (n + 1))) ∘ₗ
          (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1)) t =
        TensorProduct.map χ.ofConv
          (φ.ofConv ∘ₗ (M : G.A 1 →ₗ[R] G.A (n + 1)))
          (LinearMap.lTensor _
            (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1) t) := by
      intro t
      rw [LinearMap.lTensor, ← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.comp_id]
    rw [h2, ← _root_.GlobalTheory.PDivGroup.transl_apply, ha]
    simp
  let K : Ideal (_root_.GlobalTheory.CartierDual R (G.A (n + 1))) :=
    { carrier := {ψ | ∀ χ : _root_.GlobalTheory.CartierDual R (G.A (n + 1)), (χ * ψ).ofConv a = 0}
      add_mem' := by
        intro x y hx hy χ
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [mul_add, ofConv_add, LinearMap.add_apply, hx, hy, add_zero]
      zero_mem' := by
        intro χ
        simp
      smul_mem' := by
        intro c x hx χ
        simp only [Set.mem_setOf_eq, smul_eq_mul] at hx ⊢
        rw [← mul_assoc]
        exact hx _ }
  have hK : _root_.GlobalTheory.PDiv.torsionIdeal (R := R) (A := _root_.GlobalTheory.CartierDual R (G.A (n + 1))) (p ^ n) ≤
      RingHom.ker (Ideal.Quotient.mkₐ R K) := by
    change _root_.GlobalTheory.PDiv.kerIdeal (_root_.GlobalTheory.PDiv.mulBy R _ (p ^ n)) ≤ _
    rw [Ideal.map_le_iff_le_comap]
    intro φ hφ
    have hφ₀ : CoalgebraStruct.counit (R := R) φ = 0 := hφ
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change Ideal.Quotient.mkₐ R K (_root_.GlobalTheory.PDiv.mulBy R _ (p ^ n) φ) = 0
    rw [← _root_.GlobalTheory.PDiv.dual_mulBy, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    intro χ
    rw [key, ← _root_.GlobalTheory.CartierDual.counit_apply, hφ₀, mul_zero]
  have hker : ∀ ψ, _root_.GlobalTheory.CartierDual.map (G.mulP n) ψ = 0 →
      ψ.ofConv a = 0 := by
    intro ψ hψ
    have h3 : ψ ∈ RingHom.ker (Ideal.Quotient.mkₐ R K) := by
      apply hK
      rw [← _root_.GlobalTheory.PDivGroup.ker_dual_mulP]
      exact hψ
    rw [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h3
    simpa using h3 1
  set πL : _root_.GlobalTheory.CartierDual R (G.A (n + 1)) →ₗ[R] _root_.GlobalTheory.CartierDual R (G.A n) :=
    (_root_.GlobalTheory.CartierDual.map (G.mulP n) :
      _root_.GlobalTheory.CartierDual R (G.A (n + 1)) →ₗ[R] _root_.GlobalTheory.CartierDual R (G.A n))
    with hπL
  have hs : Function.Surjective πL := _root_.GlobalTheory.PDivGroup.dual_mulP_surjective G n
  set evL : _root_.GlobalTheory.CartierDual R (G.A (n + 1)) →ₗ[R] R :=
    (_root_.GlobalTheory.CartierDual.cartierDualToBidual R (G.A (n + 1)) a).ofConv with hevL
  have hle : LinearMap.ker πL ≤ LinearMap.ker evL := by
    intro ψ hψ
    exact hker ψ hψ
  let L : _root_.GlobalTheory.CartierDual R (G.A n) →ₗ[R] R :=
    ((LinearMap.ker πL).liftQ evL hle).comp (πL.quotKerEquivOfSurjective hs).symm.toLinearMap
  have hL : ∀ ψ, L (πL ψ) = ψ.ofConv a := by
    intro ψ
    have h4 : (πL.quotKerEquivOfSurjective hs).symm (πL ψ) = Submodule.Quotient.mk ψ := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, h4, Submodule.liftQ_apply]
    rfl
  obtain ⟨e, he⟩ :=
    (_root_.GlobalTheory.CartierDual.toBidual_bijective (R := R) (M := G.A n)).2 (toConv L)
  refine ⟨e, (_root_.GlobalTheory.CartierDual.toBidual_bijective (R := R) (M := G.A (n + 1))).1 ?_⟩
  apply WithConv.ext
  ext ψ
  show ψ.ofConv (G.mulP n e) = ψ.ofConv a
  rw [← _root_.GlobalTheory.CartierDual.map_apply]
  have h5 := congrArg
    (fun x => x.ofConv (_root_.GlobalTheory.CartierDual.map (G.mulP n) ψ)) he
  simp only [ofConv_toConv] at h5
  rw [← hL ψ]
  exact h5

end GlobalTheory.PDivGroup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPEqOfTranslInvariantStatement
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mulP_eq_of_transl_invariant : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ) (a : G.A (n + 1)), G.transl n a = a ⊗ₜ[R] 1 → ∃ e : G.A n, G.mulP n e = a := by
  first | exact @GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq | exact GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq | (intros; apply GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIndependentBasisCoprime
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLocDIffSpan
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.Mass.SemiBasis

variable {K : Type} [Field K] [NumberField K]

open NumberField IsDedekindDomain in
private theorem natCast_not_isUnit_lemma_3 {F : Type} [Field F] [NumberField F] {N : ℕ} (hN : 2 ≤ N) :
    ¬ IsUnit (N : 𝓞 F) := by
  intro h
  have h1 : IsUnit (Algebra.norm ℤ (algebraMap ℤ (𝓞 F) (N : ℤ))) := by
    have : algebraMap ℤ (𝓞 F) (N : ℤ) = (N : 𝓞 F) := by simp
    rw [this]; exact h.map _
  rw [Algebra.norm_algebraMap, Int.isUnit_iff] at h1
  have hk : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
  have h2 : (2 : ℤ) ≤ (N : ℤ) ^ Module.finrank ℤ (𝓞 F) := by
    calc (2 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
      _ = (N : ℤ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by omega) hk
  omega

open NumberField IsDedekindDomain in
private theorem mem_primeTo_ne_zero_lemma_2 {F : Type} [Field F] [NumberField F] {N : ℕ} (hN : 2 ≤ N)
    {x : 𝓞 F} (hx : x ∈ _root_.GlobalTheory.Mass.primeTo (N : 𝓞 F)) : x ≠ 0 := by
  rintro rfl
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(N : 𝓞 F)})
    (by rw [Ne, Ideal.span_singleton_eq_top]; exact natCast_not_isUnit_lemma_3 hN)
  exact hx Q hQ (hle (Ideal.mem_span_singleton_self _)) Q.zero_mem

open NumberField IsDedekindDomain in
private theorem primeTo_le_nonZeroDivisors__lemma {F : Type} [Field F] [NumberField F] {N : ℕ}
    (hN : 2 ≤ N) : _root_.GlobalTheory.Mass.primeTo (N : 𝓞 F) ≤ nonZeroDivisors (𝓞 F) :=
  fun _ hx => mem_nonZeroDivisors_of_ne_zero (mem_primeTo_ne_zero_lemma_2 hN hx)

open NumberField Matrix in
open scoped ENNReal Classical in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Mass.SemiBasis.primeTo_le {d : ℕ} (hd : 2 ≤ d) :
    _root_.GlobalTheory.Mass.primeTo (d : 𝓞 K) ≤ nonZeroDivisors (𝓞 K) :=
  primeTo_le_nonZeroDivisors__lemma hd

abbrev A (K : Type) [Field K] [NumberField K] {d : ℕ} (hd : 2 ≤ d) : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (primeTo (d : 𝓞 K)) (primeTo_le hd)

theorem primes_finite {d : ℕ} (hd : 2 ≤ d) : {P : Ideal (A K hd) | P.IsPrime}.Finite := by
  have hd0 : (d : 𝓞 K) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hfin : {P : Ideal (𝓞 K) | P.IsMaximal ∧ (d : 𝓞 K) ∈ P}.Finite := by
    have h0 : Ideal.span {(d : 𝓞 K)} ≠ 0 := by
      simpa [Ideal.span_singleton_eq_bot] using hd0
    refine ((Ideal.finite_factors h0).image (fun v => v.asIdeal)).subset ?_
    rintro P ⟨hP, hdP⟩
    have hb : P ≠ ⊥ := by
      rintro rfl
      exact hd0 (by simpa using hdP)
    exact ⟨⟨P, hP.isPrime, hb⟩, Ideal.dvd_span_singleton.2 hdP, rfl⟩
  apply ((hfin.insert ⊥).image (Ideal.map (algebraMap (𝓞 K) (A K hd)))).subset
  intro P hP
  have hP' : P.IsPrime := hP
  obtain ⟨hQ, hdisj⟩ :=
    (IsLocalization.isPrime_iff_isPrime_disjoint (primeTo (d : 𝓞 K)) (A K hd) P).mp hP'
  refine ⟨P.comap (algebraMap (𝓞 K) (A K hd)), ?_,
    IsLocalization.map_under (primeTo (d : 𝓞 K)) (A K hd) P⟩
  set Q := P.comap (algebraMap (𝓞 K) (A K hd))
  have hsub : (Q : Set (𝓞 K)) ⊆ ⋃ i ∈ (hfin.toFinset : Set (Ideal (𝓞 K))), ((id i : Ideal (𝓞 K)) : Set (𝓞 K)) := by
    intro x hx
    by_contra hn
    refine Set.disjoint_left.mp hdisj (?_ : x ∈ primeTo (d : 𝓞 K)) hx
    intro I hI hdI hxI
    apply hn
    simp only [Set.mem_iUnion]
    exact ⟨I, by simpa using ⟨hI, hdI⟩, hxI⟩
  by_cases hb : Q = ⊥
  · exact Or.inl hb
  have hmax : Q.IsMaximal := hQ.isMaximal hb
  obtain ⟨I, hI, hle⟩ := (Ideal.subset_union_prime ⊥ ⊥ (fun i hi _ _ => by
    have : i.IsMaximal ∧ (d : 𝓞 K) ∈ i := by simpa using hi
    exact this.1.isPrime)).1 hsub
  have hI' : I.IsMaximal ∧ (d : 𝓞 K) ∈ I := by simpa using hI
  have : Q = I := hmax.eq_of_le hI'.1.ne_top hle
  right
  rw [this]
  exact hI'

theorem isPID {d : ℕ} (hd : 2 ≤ d) : IsPrincipalIdealRing (A K hd) := by
  have : IsDedekindDomain (A K hd) :=
    IsLocalization.isDedekindDomain (𝓞 K) (primeTo_le hd) (A K hd)
  exact IsPrincipalIdealRing.of_finite_primes (primes_finite hd)

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

end GlobalTheory.Mass.SemiBasis
end
end

open NumberField

namespace GlobalTheory.CoprimeBasis

theorem isTorsionFree_of_addTorsionFree {F : Type} [Field F] [NumberField F]
    (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [IsAddTorsionFree M] :
    Module.IsTorsionFree (𝓞 F) M where
  isSMulRegular r hr x y hxy := by
    have hxy' : r • x = r • y := hxy
    have hr0 : r ≠ 0 := hr.ne_zero
    have hn : Ideal.absNorm (Ideal.span {r}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hr0
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {r}))
    have h1 : (Ideal.absNorm (Ideal.span {r})) • (x - y) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (𝓞 F), ← hb, mul_smul, smul_sub, hxy', sub_self, smul_zero]
    haveI : HasUniqueDiv M := by
      refine ⟨fun {n} hn => ?_⟩
      intro x y h
      have h' : (n : ℤ) • x = (n : ℤ) • y := by exact_mod_cast h
      have hz : (n : ℤ) • (x - y) = 0 := by rw [zsmul_sub, h', sub_self]
      have hdiff : x - y = 0 := by simpa [hn] using hz
      exact sub_eq_zero.mp hdiff
    exact sub_eq_zero.1 (nsmul_right_injective hn (h1.trans (nsmul_zero _).symm))

theorem isCoprime_of_mem_primeTo {R : Type} [CommRing R] {s d : R}
    (hs : s ∈ GlobalTheory.Mass.primeTo d) : IsCoprime s d := by
  by_cases hI : Ideal.span {s, d} = ⊤
  · obtain ⟨a, b, h⟩ := Ideal.mem_span_pair.1 ((Ideal.eq_top_iff_one _).1 hI)
    exact ⟨a, b, h⟩
  · obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hI
    exact absurd (hle (Ideal.subset_span (by simp))) (hs P hP (hle (Ideal.subset_span (by simp))))

theorem exists_coprime_basis : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M] (N : ℕ), 2 ≤ N → ∃ (r : ℕ) (x : Fin r → M), LinearIndependent (𝓞 F) x ∧ ∃ c : 𝓞 F, c ≠ 0 ∧ IsCoprime c (N : 𝓞 F) ∧ ∀ m : M, c • m ∈ Submodule.span (𝓞 F) (Set.range x) := by
  intro F _ _ M _ _ _ _ N hN
  classical
  let S : Submonoid (𝓞 F) := GlobalTheory.Mass.primeTo (N : 𝓞 F)
  have hSle : S ≤ nonZeroDivisors (𝓞 F) := GlobalTheory.Mass.SemiBasis.primeTo_le hN
  haveI : Module.IsTorsionFree (𝓞 F) M := isTorsionFree_of_addTorsionFree M
  haveI : Module.Finite (𝓞 F) M := Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) M
  haveI : IsDomain (Localization S) := IsLocalization.isDomain_localization hSle
  haveI : IsPrincipalIdealRing (Localization S) := by
    haveI := GlobalTheory.Mass.SemiBasis.isPID (K := F) hN
    have hA : GlobalTheory.Mass.SemiBasis.A F hN =
        Localization.subalgebra.ofField F (GlobalTheory.Mass.primeTo (N : 𝓞 F))
          (GlobalTheory.Mass.SemiBasis.primeTo_le hN) := by
      apply Subalgebra.ext
      intro x
      rfl
    haveI : IsLocalization S (GlobalTheory.Mass.SemiBasis.A F hN) := by
      rw [hA]
      exact Localization.subalgebra.isLocalization_ofField (A := 𝓞 F) (K := F)
        (S := GlobalTheory.Mass.primeTo (N : 𝓞 F))
        (hS := GlobalTheory.Mass.SemiBasis.primeTo_le hN)
    exact IsPrincipalIdealRing.of_surjective
      (IsLocalization.algEquiv S (GlobalTheory.Mass.SemiBasis.A F hN) (Localization S)).toRingHom
      (IsLocalization.algEquiv S (GlobalTheory.Mass.SemiBasis.A F hN) (Localization S)).surjective
  haveI : Module.Finite (Localization S) (LocalizedModule S M) :=
    Module.Finite.of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)
  obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := Localization S) (M := LocalizedModule S M)
  have hb : ∀ i, ∃ (m : M) (s : S), b i = LocalizedModule.mk m s := fun i => by
    exact LocalizedModule.induction_on (β := fun y => ∃ (m : M) (s : S), y = LocalizedModule.mk m s)
      (fun m s => ⟨m, s, rfl⟩) (b i)
  choose x s hxs using hb
  have key : ∀ i, (s i : 𝓞 F) • b i = LocalizedModule.mk (x i) 1 := by
    intro i
    rw [hxs i, LocalizedModule.smul'_mk, ← Submonoid.smul_def, LocalizedModule.mk_cancel]
  refine ⟨r, x, ?_, ?_⟩
  · let u : Fin r → (Localization S)ˣ := fun i => (IsLocalization.map_units (Localization S) (s i)).unit
    have hu : LinearIndependent (Localization S) (u • ⇑b) := b.linearIndependent.units_smul u
    have hfx : (u • ⇑b) = LocalizedModule.mkLinearMap S M ∘ x := by
      funext i
      simp only [Pi.smul_apply', Function.comp_apply, LocalizedModule.mkLinearMap_apply, ← key i]
      rw [Units.smul_def, IsUnit.unit_spec, algebraMap_smul]
    rw [hfx] at hu
    have hinj : Function.Injective fun a : 𝓞 F => a • (1 : Localization S) := by
      intro a a' h
      simp only [Algebra.smul_def, mul_one] at h
      exact IsLocalization.injective (Localization S) hSle h
    exact (hu.restrict_scalars hinj).of_comp _
  · set P : Submodule (𝓞 F) M := Submodule.span (𝓞 F) (Set.range x) with hP
    have hloc : ∀ y : LocalizedModule S M, ∃ t : S, ∃ m' ∈ P, (t : 𝓞 F) • y = LocalizedModule.mk m' 1 := by
      intro y
      have hy : y ∈ Submodule.span (Localization S) (Set.range b) := by rw [b.span_eq]; trivial
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact ⟨s i, x i, Submodule.subset_span ⟨i, rfl⟩, key i⟩
      | zero => exact ⟨1, 0, P.zero_mem, by simp [LocalizedModule.zero_mk]⟩
      | add y z _ _ hy hz =>
        obtain ⟨t, m, hm, h⟩ := hy
        obtain ⟨t', m', hm', h'⟩ := hz
        refine ⟨t * t', (t' : 𝓞 F) • m + (t : 𝓞 F) • m', P.add_mem (P.smul_mem _ hm) (P.smul_mem _ hm'), ?_⟩
        calc ((t * t' : S) : 𝓞 F) • (y + z) = (t' : 𝓞 F) • ((t : 𝓞 F) • y) + (t : 𝓞 F) • ((t' : 𝓞 F) • z) := by
              rw [Submonoid.coe_mul, smul_add, smul_smul, smul_smul, mul_comm (t' : 𝓞 F)]
          _ = _ := by
              rw [h, h', LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, LocalizedModule.mk_add_mk]
              simp
      | smul a y _ hy =>
        obtain ⟨t, m, hm, h⟩ := hy
        obtain ⟨⟨r0, u⟩, hr⟩ := IsLocalization.surj S a
        have hua : (u : 𝓞 F) • a = algebraMap (𝓞 F) (Localization S) r0 := by
          rw [Algebra.smul_def, mul_comm]; exact hr
        refine ⟨u * t, r0 • m, P.smul_mem r0 hm, ?_⟩
        calc ((u * t : S) : 𝓞 F) • (a • y) = ((u : 𝓞 F) • a) • ((t : 𝓞 F) • y) := by
              rw [Submonoid.coe_mul, mul_smul, smul_comm (t : 𝓞 F) a y, smul_assoc]
          _ = LocalizedModule.mk (r0 • m) 1 := by
              rw [hua, h, algebraMap_smul, LocalizedModule.smul'_mk]
    have hgen : ∀ m : M, ∃ t : S, (t : 𝓞 F) • m ∈ P := by
      intro m
      obtain ⟨t, m', hm', h⟩ := hloc (LocalizedModule.mk m 1)
      rw [LocalizedModule.smul'_mk, LocalizedModule.mk_eq] at h
      obtain ⟨u, hu⟩ := h
      simp only [one_smul, Submonoid.smul_def] at hu
      refine ⟨u * t, ?_⟩
      rw [Submonoid.coe_mul, mul_smul, hu]
      exact P.smul_mem _ hm'
    obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := 𝓞 F) (M := M)
    choose t ht using fun j => hgen (g j)
    refine ⟨((∏ j, t j : S) : 𝓞 F), ?_, ?_, ?_⟩
    · exact nonZeroDivisors.ne_zero (hSle (∏ j, t j).2)
    · exact isCoprime_of_mem_primeTo (∏ j, t j).2
    · intro m
      have hle : Submodule.span (𝓞 F) (Set.range g) ≤
          P.comap (LinearMap.lsmul (𝓞 F) M ((∏ j, t j : S) : 𝓞 F)) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        show ((∏ j, t j : S) : 𝓞 F) • g j ∈ P
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), Submonoid.coe_mul, mul_smul]
        exact P.smul_mem _ (ht j)
      rw [hg] at hle
      exact hle Submodule.mem_top

end GlobalTheory.CoprimeBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictPull1InjectiveOfSepGlue
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.CoefMap

theorem restrict_pull1_injective_of_sep_glue {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (hsep : ∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0)
    (hglue : ∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)),
      (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) →
      ∃ x : F.obj T, ∀ t u, mp F u x = s t u) :
    Function.Injective (CoefMap.restrict F G).pull1 := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
  obtain ⟨g₀, hg⟩ := hc
  let g : ∀ t, F.obj (G.obj t) := fun t ↦ g₀ t
  have hg' : ∀ t t' (a : t ⟶ t'), g t' - mp F (G.map a) (g t) = f.1 _ _ (G.map a) := fun t t' a ↦
    congrFun (congrFun (congrFun hg t) t') a
  have h1 : ∀ T : C, ∃ x : F.obj T, ∀ t (u : T ⟶ G.obj t), mp F u x = g t - f.1 T _ u := by
    intro T
    refine hglue T (fun t u ↦ g t - f.1 T _ u) fun t t' u a ↦ ?_
    have k1 := Z1.comp f u (G.map a)
    have k2 := hg' t t' a
    simp only [map_sub]
    linear_combination k2 - k1
  choose x hx using h1
  refine H1.mk_eq_zero.2 ⟨x, ?_⟩
  funext T T' φ
  rw [amitsur_d0_apply]
  refine (sub_eq_zero.1 (hsep T' _ fun t u ↦ ?_)).symm
  have k1 := Z1.comp f φ u
  have k2 := hx T' t u
  have k3 := hx T t (φ ≫ u)
  rw [mp_comp] at k3
  simp only [map_sub]
  linear_combination k3 - k2 - k1

end GlobalTheory.CatCoh.CoefMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableFullRankFibreStatement
open MeasureTheory Matrix Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_full_rank_fibre :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν : kˣ →* ℂˣ),
      GlobalTheory.SmGL.IsSmoothChar ν → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB (k := k) a (a + b),
      MeasureTheory.Integrable (fun g : GL (Fin a) k =>
        Φ (g.val * GlobalTheory.SplitFlip.X0 (k := k) finSumFinEquiv) *
          (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
          GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2))
        (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) := by
  intro k _ _ _ _ _ _ a b ν hν Φ hΦ
  obtain ⟨⟨hLocal, hCompact⟩, hRank⟩ := hΦ
  let σ := finSumFinEquiv (m := a) (n := b)
  let X₀ := GlobalTheory.SplitFlip.X0 (k := k) σ
  have hLocalΦ : IsLocallyConstant fun g : GL (Fin a) k => Φ (g.val * X₀) :=
    hLocal.comp_continuous (Units.continuous_val.matrix_mul continuous_const)
  have hLocalν := GlobalTheory.GodementJacquet.isLocallyConstant_char_det (k := k) (n := Fin a) hν
  have hLocalPow : IsLocallyConstant fun g : GL (Fin a) k =>
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2) :=
    ((GlobalTheory.SplitWeil.isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det).comp
      fun x => ((x : ℝ) : ℂ) ^ (((a + b : ℕ) : ℂ) / 2)
  have hContinuous := ((hLocalΦ.mul hLocalν).mul hLocalPow).continuous

  let D : Set (Matrix (Fin a) (Fin a) k) := {A | Φ (A * X₀) ≠ 0}
  have hClosed : IsClosed D :=
    (hLocal.isOpen_fiber 0).isClosed_compl.preimage
      (show Continuous fun A : Matrix (Fin a) (Fin a) k => A * X₀ from
        continuous_id.matrix_mul continuous_const)
  have hSubset : D ⊆ (fun M : Matrix (Fin a) (Fin (a + b)) k => M * X₀ᵀ) '' tsupport Φ := by
    intro A hA
    refine ⟨A * X₀, subset_tsupport _ hA, ?_⟩
    have hTranspose : X₀ * X₀ᵀ = 1 := by
      ext i j
      change (GlobalTheory.SplitFlip.X0 (k := k) σ * X₀ᵀ) i j = _
      rw [GlobalTheory.SplitFlip.frameMatrixFirstColumnBlock_mul_apply]
      simp [X₀, GlobalTheory.SplitFlip.X0, Matrix.one_apply, eq_comm]
    show A * X₀ * X₀ᵀ = A
    rw [Matrix.mul_assoc, hTranspose, Matrix.mul_one]
  have hCompactD : IsCompact D :=
    (hCompact.image (show Continuous fun M : Matrix (Fin a) (Fin (a + b)) k => M * X₀ᵀ from
      continuous_id.matrix_mul continuous_const)).of_isClosed_subset hClosed hSubset
  have hRange : D ⊆ Set.range fun g : GL (Fin a) k => g.val := by
    intro A hA
    have hFullRank : (A * X₀).rank = a := by
      by_contra hne
      exact hA (hRank _ hne)
    have hRankA : A.rank = Fintype.card (Fin a) := by
      refine le_antisymm (by simpa using A.rank_le_width) ?_
      simpa [hFullRank] using Matrix.rank_mul_le_left A X₀
    have hIndependent : LinearIndependent k A.row := by
      rw [rank_eq_finrank_span_row] at hRankA
      rw [linearIndependent_iff_card_eq_finrank_span]
      exact hRankA.symm
    exact ⟨(Matrix.linearIndependent_row_iff_isUnit.1 hIndependent).unit, rfl⟩
  have hPreimage : IsCompact ((fun g : GL (Fin a) k => g.val) ⁻¹' D) :=
    GlobalTheory.SplitFlip.isEmbedding_val_GL.isInducing.isCompact_preimage' hCompactD hRange
  have hSupport : HasCompactSupport fun g : GL (Fin a) k =>
      Φ (g.val * X₀) * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2) := by
    refine HasCompactSupport.intro hPreimage fun g hg => ?_
    have hZero : Φ (g.val * X₀) = 0 := not_not.1 hg
    simp [hZero]
  exact hContinuous.integrable_of_hasCompactSupport hSupport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAlgebraStrictlyHenselianInduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAlgebraStrictlyHenselianInduction
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep.FinSH

open IsLocalRing

theorem sh_of_finite_local (A T : Type) [CommRing A] [CommRing T] [Algebra A T] (hA : SH A)
    [Module.Finite A T] [IsLocalRing T] : SH T := by
  obtain ⟨hH, hk⟩ := hA
  refine ⟨GlobalTheory.henselianLocalRing_of_finite A T, ?_⟩
  have hc : (maximalIdeal T).comap (algebraMap A T) = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal T))
  haveI : IsLocalHom (algebraMap A T) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : a ∈ (maximalIdeal T).comap (algebraMap A T) := by rw [hc]; exact hna
    exact (maximalIdeal T).ne_top_iff_one.1 (maximalIdeal.isMaximal T).ne_top
      (by simpa using Ideal.mul_mem_left _ (↑ha.unit⁻¹ : T) (show algebraMap A T a ∈ maximalIdeal T from this))
  haveI : Algebra.IsIntegral (ResidueField A) (ResidueField T) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨t', rfl⟩ := residue_surjective x
    have h1 : IsIntegral A (residue T t') :=
      (Algebra.IsIntegral.isIntegral (R := A) t').map (IsScalarTower.toAlgHom A T (ResidueField T))
    exact h1.tower_top
  exact Algebra.IsAlgebraic.isSepClosed (F := ResidueField A)

def optionProdEquiv (A : Type) [CommRing A] {α : Type} (T : Option α → Type) [∀ i, CommRing (T i)]
    [∀ i, Algebra A (T i)] : (∀ o, T o) ≃ₐ[A] T none × ∀ a, T (some a) :=
  { Equiv.piOptionEquivProd with
    map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl, commutes' := fun _ => rfl }

theorem induction_principle : ∀ (A : Type) [CommRing A], SH A → ∀ (P : ∀ (T : Type) [CommRing T] [Algebra A T], Prop),
  (∀ (T T' : Type) [CommRing T] [CommRing T'] [Algebra A T] [Algebra A T'], (T ≃ₐ[A] T') → P T → P T') →
  (∀ (T : Type) [CommRing T] [Algebra A T], Subsingleton T → P T) →
  (∀ (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] [Algebra A T₁] [Algebra A T₂], Module.Finite A T₁ → Module.Finite A T₂ →
    P T₁ → P T₂ → P (T₁ × T₂)) →
  (∀ (T : Type) [CommRing T] [Algebra A T], Module.Finite A T → SH T → P T) →
  ∀ (T : Type) [CommRing T] [Algebra A T], Module.Finite A T → P T := by
  intro A _ hA P hiso hsub hprod hsh T _ _ hT
  obtain ⟨hH, hk⟩ := hA
  obtain ⟨ι, hι, S, _, _, e, hS⟩ := GlobalTheory.exists_algEquiv_pi_henselianLocalRing A T
  have key : ∀ (α : Type) [Finite α] (S : α → Type) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)],
      (∀ i, Module.Finite A (S i) ∧ SH (S i)) → P (∀ i, S i) := by
    intro α _
    induction α using Finite.induction_empty_option with
    | of_equiv e' ih =>
      intro S _ _ hS'
      exact hiso _ _ (AlgEquiv.piCongrLeft A S e') (ih (fun a => S (e' a)) (fun a => hS' (e' a)))
    | h_empty =>
      intro S _ _ _
      exact hsub _ inferInstance
    | h_option ih =>
      intro S _ _ hS'
      refine hiso _ _ (optionProdEquiv A S).symm ?_
      haveI : ∀ a, Module.Finite A (S (some a)) := fun a => (hS' (some a)).1
      exact hprod _ _ (hS' none).1 inferInstance (hsh _ (hS' none).1 (hS' none).2)
        (ih (fun a => S (some a)) (fun a => hS' (some a)))
  refine hiso _ _ e.symm (key ι S fun i => ⟨(hS i).2, ?_⟩)
  haveI := (hS i).1
  haveI := (hS i).2
  exact sh_of_finite_local A (S i) ⟨hH, hk⟩

end GlobalTheory.EtC.GmStep.FinSH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAlgebraStrictlyHenselianInductionStatement
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAlgebra_strictlyHenselian_induction : ∀ (A : Type) [CommRing A], SH A → ∀ (P : ∀ (T : Type) [CommRing T] [Algebra A T], Prop),
  (∀ (T T' : Type) [CommRing T] [CommRing T'] [Algebra A T] [Algebra A T'], (T ≃ₐ[A] T') → P T → P T') →
  (∀ (T : Type) [CommRing T] [Algebra A T], Subsingleton T → P T) →
  (∀ (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] [Algebra A T₁] [Algebra A T₂], Module.Finite A T₁ → Module.Finite A T₂ →
    P T₁ → P T₂ → P (T₁ × T₂)) →
  (∀ (T : Type) [CommRing T] [Algebra A T], Module.Finite A T → SH T → P T) →
  ∀ (T : Type) [CommRing T] [Algebra A T], Module.Finite A T → P T := by
  first | (exact @GlobalTheory.EtC.GmStep.FinSH.induction_principle) | (exact GlobalTheory.EtC.GmStep.FinSH.induction_principle) | (intros; apply GlobalTheory.EtC.GmStep.FinSH.induction_principle  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAWExistsUniqueBiadditiveEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAWExistsUniqueBiadditiveEtale
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isAW_existsUnique_biadditive (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc}
    {n m k : ℤ} (hk : n + m = k) :
    (∀ (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m), ∃! γ, μ.IsAW hk α β γ) ∧
    (∀ α α' β γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α' β γ' → μ.IsAW hk (α + α') β (γ + γ')) ∧
    (∀ α β β' γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α β' γ' → μ.IsAW hk α (β + β') (γ + γ')) := by
  refine ⟨fun α β => ?_, fun α α' β γ γ' h h' => CupSpec.isAW_add_left μ hk h h',
    fun α β β' γ γ' h h' => CupSpec.isAW_add_right μ hk h h'⟩
  obtain ⟨γ, hγ⟩ := CupSpec.isAW_exists μ hk α β
  exact ⟨γ, hγ, fun γ' h' => CupSpec.isAW_unique μ hk h' hγ⟩

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAWExistsUniqueBiadditiveEtaleStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
theorem _root_.GlobalTheory.T.isAW_existsUnique_biadditive_etale : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k), (∀ (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m), ∃! γ, μ.IsAW hk α β γ) ∧ (∀ α α' β γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α' β γ' → μ.IsAW hk (α + α') β (γ + γ')) ∧ (∀ α β β' γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α β' γ' → μ.IsAW hk α (β + β') (γ + γ')) := by
  first | exact @GlobalTheory.EtC.isAW_existsUnique_biadditive | exact GlobalTheory.EtC.isAW_existsUnique_biadditive | (intros; apply GlobalTheory.EtC.isAW_existsUnique_biadditive <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftOfReducedOfSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftOfReducedOfSupport
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem GlobalTheory.lift_of_reduced_of_support {X Y T : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i]
    [IsReduced T] (g : T ⟶ Y) (hg : ∀ t, g t ∈ i.ker.support) : ∃ h : T ⟶ X, h ≫ i = g := by
  have hle : i.ker ≤ g.ker := by
    refine (Scheme.IdealSheafData.le_ofIdeals_iff (I := i.ker)).mpr ?_
    intro U a ha
    rw [RingHom.mem_ker]
    apply eq_zero_of_basicOpen_eq_bot
    rw [← Scheme.preimage_basicOpen]
    ext t
    simp only [Scheme.Hom.mem_preimage, Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    intro ht
    have h1 := (Scheme.IdealSheafData.mem_support_iff.mp (hg t)) U
    exact (Y.mem_zeroLocus_iff _ _).mp h1 a ha ht
  exact ⟨IsClosedImmersion.lift i g hle, IsClosedImmersion.lift_fac _ _ _⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftOfReducedOfSupportStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_of_isReduced_of_mem_ker_support : ∀ {X Y T : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i] [IsReduced T] (g : T ⟶ Y), (∀ t, g t ∈ i.ker.support) → ∃ h : T ⟶ X, h ≫ i = g := by
  first | exact @GlobalTheory.lift_of_reduced_of_support | exact GlobalTheory.lift_of_reduced_of_support | (intros; apply GlobalTheory.lift_of_reduced_of_support <;> assumption)
end
end
