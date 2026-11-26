module

public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypInvLe

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.ChartRank.HypFormsCl
noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PFormsCl

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms MvPolynomial NumberField IsDedekindDomain

section Tr

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem foNat_anti (lam : DomWeight n) : Antitone lam.natW := by
  intro a b hab
  have := lam.anti hab
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (by omega)

theorem foRow_delSq (lam : DomWeight n) (g : Matrix (Fin n) (Fin n) ℂ) {q : MvPolynomial (Fin n × Fin n) ℂ}
    (hq : q ∈ delSq ℂ n lam) : Formalism.GradedWeylDivisibility.rowAct ℂ g q ∈ delSq ℂ n lam := by
  unfold delSq at hq ⊢
  rw [Formalism.L2.G.Model.sw_weyl_eq ℂ n n le_rfl _ (foNat_anti lam)] at hq ⊢
  exact Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ g q hq

def foTr {Gm : ι → Matrix (Fin n) (Fin n) ℂ} (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, IsUnit (g τ).det)
    (y : Formalism.L2.Forms.Frames Gm) : Formalism.L2.Forms.Frames Gm :=
  (⟨fun τ => g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (hg τ).mul (y.2 τ)⟩ :
    {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det})

def blockRowSubstitutionAlgHom (g : ι → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (ι × Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ :=
  aeval fun x => ∑ c : Fin n, C (g x.1 x.2.1 c) * X (x.1, c, x.2.2)

theorem blockRowSubstitution_X (g : ι → Matrix (Fin n) (Fin n) ℂ) (x : ι × Fin n × Fin n) :
    blockRowSubstitutionAlgHom g (X x) = ∑ c : Fin n, C (g x.1 x.2.1 c) * X (x.1, c, x.2.2) := by
  simp only [blockRowSubstitutionAlgHom, aeval_X]

theorem eval_blockRowSubstitution (g : ι → Matrix (Fin n) (Fin n) ℂ) (z : ι × Fin n × Fin n → ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    eval z (blockRowSubstitutionAlgHom g P) = eval (fun x => ∑ c, g x.1 x.2.1 c * z (x.1, c, x.2.2)) P := by
  induction P using MvPolynomial.induction_on
  next a => simp [blockRowSubstitutionAlgHom]
  next p q hp hq => simp only [map_add (f := _), hp, hq]
  next p x hp => simp only [map_mul, hp, blockRowSubstitution_X, eval_X, map_sum, eval_C]

theorem blockRowSubstitution_rename (g : ι → Matrix (Fin n) (Fin n) ℂ) (τ : ι) (q : MvPolynomial (Fin n × Fin n) ℂ) :
    blockRowSubstitutionAlgHom g (rename (Prod.mk τ) q) = rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) q) := by
  have h : (blockRowSubstitutionAlgHom g).comp (rename (Prod.mk τ)) = (rename (Prod.mk τ)).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (r := n) (n := n) (g τ)) := by
    apply MvPolynomial.algHom_ext
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      simp [blockRowSubstitutionAlgHom, Formalism.GradedWeylDivisibility.rowAct, rename_X, map_sum]
  exact congrArg (fun φ => φ q) h

theorem blockRowSubstitution_tensor (g : ι → Matrix (Fin n) (Fin n) ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    blockRowSubstitutionAlgHom g (ten f) = ten fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) (f τ) := by
  simp only [ten, map_prod, blockRowSubstitution_rename]

theorem blockRowSubstitution_preserves_complexSpan (lam : ι → DomWeight n) (g : ι → Matrix (Fin n) (Fin n) ℂ) {P : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hP : P ∈ CSpan lam) : blockRowSubstitutionAlgHom g P ∈ CSpan lam := by
  have h : CSpan lam ≤ (CSpan lam).comap (blockRowSubstitutionAlgHom g).toLinearMap := by
    unfold CSpan
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact Submodule.subset_span ⟨fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) (f τ), fun τ => foRow_delSq _ _ (hf τ), blockRowSubstitution_tensor g f⟩
  exact h hP

theorem foValC_tr {Gm : ι → Matrix (Fin n) (Fin n) ℂ} (lam : ι → DomWeight n) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (hg : ∀ τ, IsUnit (g τ).det) {v : Formalism.L2.Forms.Frames Gm → ℂ} (hv : v ∈ ValC Gm lam) :
    (fun y => v (foTr g hg y)) ∈ ValC Gm lam := by
  obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.1 hv
  have h : (fun y => fnOf Gm (shiftOf lam) 1 P (foTr g hg y)) =
      (∏ τ, (g τ).det ^ shiftOf lam τ) • fnOf Gm (shiftOf lam) 1 (blockRowSubstitutionAlgHom g P) := by
    funext y
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul, foTr, Pi.one_apply, Matrix.one_mul, eval_blockRowSubstitution,
      Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
    simp only [Matrix.mul_apply]
    ring
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (blockRowSubstitution_preserves_complexSpan lam g hP))

end Tr

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T fT : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem foInf_unit (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) : IsUnit (atInf emb γ.1 τ).det := by
  have h := ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).map (emb τ)
  rwa [RingHom.map_det] at h

theorem foInf_mul (emb : ι → E →+* ℂ) (a b : Matrix (Fin n) (Fin n) E) (τ : ι) :
    atInf emb (a * b) τ = atInf emb a τ * atInf emb b τ := by
  simp [atInf, Matrix.map_mul]

theorem foInf_one (emb : ι → E →+* ℂ) (τ : ι) : atInf emb (1 : Matrix (Fin n) (Fin n) E) τ = 1 := by
  simp [atInf]

def foTrR (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (y : Formalism.L2.Forms.Frames (gramC J emb)) : Formalism.L2.Forms.Frames (gramC J emb) :=
  foTr (atInf emb γ.1) (foInf_unit emb γ) y

theorem foTrR_val (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (y : Formalism.L2.Forms.Frames (gramC J emb)) (τ : ι) :
    (foTrR emb γ y).1 τ = atInf emb γ.1 τ * y.1 τ := rfl

theorem foTrR_mul (emb : ι → E →+* ℂ) (γ δ : GL (Fin n) E) (y : Formalism.L2.Forms.Frames (gramC J emb)) :
    foTrR emb (γ * δ) y = foTrR emb γ (foTrR emb δ y) := by
  apply Subtype.ext
  funext τ
  show (foTrR emb (γ * δ) y).1 τ = (foTrR emb γ (foTrR emb δ y)).1 τ
  rw [foTrR_val, foTrR_val, foTrR_val, Units.val_mul, foInf_mul, Matrix.mul_assoc]

theorem foTrR_one (emb : ι → E →+* ℂ) (y : Formalism.L2.Forms.Frames (gramC J emb)) : foTrR emb 1 y = y := by
  apply Subtype.ext
  funext τ
  show (foTrR emb 1 y).1 τ = y.1 τ
  rw [foTrR_val, Units.val_one, foInf_one, Matrix.one_mul]

theorem foIsTr_iff (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (y' y : Formalism.L2.Forms.Frames (gramC J emb)) :
    IsTr (atInf emb γ) y' y ↔ y = foTrR emb γ y' := by
  constructor
  · intro h
    apply Subtype.ext
    funext τ
    exact h τ
  · intro h τ
    rw [h]
    rfl

def FoInv (S : StepLevel F E σ J T fT bad) (emb : ι → E →+* ℂ) (y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ) : Prop :=
  ∀ γ : GL (Fin n) E, γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
    y0.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1 →
    ∀ y y' : Formalism.L2.Forms.Frames (gramC J emb), IsTr (atInf emb γ) y' y → v y = (S.chi κ : ℂ) * v y'

variable (S : StepLevel F E σ J T fT bad) (emb : ι → E →+* ℂ)


variable {S emb}

end Adelic

section Rec

open Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

end Rec

section Card

open Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

end Card

end Formalism.MainNotions.G.CmpJ.PFormsCl
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLiftInv
section -- merged from Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLiftTw
section -- merged from Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLiftDesc
section -- merged from Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLift
noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PCmpLift

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Module Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe Formalism.MainNotions.G.CmpJ.PFormsCl

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

def trN (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (γ0 : GL (Fin (D.R.N i)) D.host.E) :
    (Formalism.L2.Forms.Frames (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) → ℂ) →ₗ[ℂ]
      (Formalism.L2.Forms.Frames (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) → ℂ) where
  toFun h := fun z => (detF (cTw D i) z)⁻¹ * h (foTrR (embT D) γ0 z)
  map_add' h h' := by funext z; simp only [Pi.add_apply]; ring
  map_smul' a h := by funext z; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem trN_inj (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (γ0 : GL (Fin (D.R.N i)) D.host.E) :
    LinearMap.ker (trN D i hi γ0) = ⊥ := by
  refine LinearMap.ker_eq_bot'.2 fun h hh => ?_
  funext z
  have h1 := congrFun hh (foTrR (embT D) γ0⁻¹ z)
  have h2 : foTrR (embT D) γ0 (foTrR (embT D) γ0⁻¹ z) = z := by
    rw [← foTrR_mul, mul_inv_cancel, foTrR_one]
  change (detF (cTw D i) _)⁻¹ * h (foTrR (embT D) γ0 (foTrR (embT D) γ0⁻¹ z)) = 0 at h1
  rw [h2] at h1
  exact (mul_eq_zero.1 h1).resolve_left (inv_ne_zero (detF_ne _ _))

def phiC (S : StepIn M i hi G) (β : S.Ch) (γ0 : GL (Fin (D.R.N i)) D.host.E) :
    XR (Hc S β).P ℂ →ₗ[ℂ] (Formalism.L2.Forms.Frames (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) → ℂ) :=
  (trN D i hi γ0).comp
    (evC (Hc S β).P (S.loc β).rk S.pos (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (crdB (embT D) (S.loc β).B))

theorem ker_phiC (S : StepIn M i hi G) (β : S.Ch) (γ0 : GL (Fin (D.R.N i)) D.host.E) : LinearMap.ker (phiC S β γ0) = ⊥ := by
  refine LinearMap.ker_eq_bot'.2 fun Q hQ => ?_
  have h1 : evC (Hc S β).P (S.loc β).rk S.pos (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (crdB (embT D) (S.loc β).B) Q = 0 :=
    LinearMap.ker_eq_bot'.1 (trN_inj D i hi γ0) _ hQ
  exact evInj_pf (J := gramN D i hi) (embT D) (Hc S β) (S.loc β) S.pos Q h1

def VtupDesc (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  ∀ β (Q : YR (Hc S β) D.what₂.LL), MvPolynomial.map e Q ∈ (Hc S β).P.Vtup → MvPolynomial.map D.what₂.embLL Q ∈ VtupR (Hc S β).P ℂ

def EvValLe (S : StepIn M i hi G) (β : S.Ch) : Prop :=
  ∀ Q ∈ VtupR (Hc S β).P ℂ,
    evC (Hc S β).P (S.loc β).rk S.pos (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (crdB (embT D) (S.loc β).B) Q ∈
      Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (M.lam i)

def CmpInvOf (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  BlockRationalityField → (∀ β, S.Core e β) → KAat.ChX S → ∀ β rep, RepOk S β rep → ∀ c
    (g : ∀ v, GL (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v)) (γ0 : GL (Fin (D.R.N i)) D.host.E) (κ0 : (S.K β).lev.U),
    γ0 ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) →
    (∀ v, (rep c).2 v = colSpan ((Hc S β).P.W v) (g v : Matrix (Fin ((Hc S β).P.m + 1)) (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v))) →
    (S.loc β).IsPt (rep c).1 g (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0 * ((S.K β).y c).1 * κ0.1) →
    ∀ Q ∈ YInv (Hc S β) e (rep c).1 (rep c).2,
      FoInv (S.K β).lev (embT D) ((S.K β).y c) (phiC S β γ0 (MvPolynomial.map D.what₂.embLL Q))

theorem phiC_mem_ValC (S : StepIn M i hi G) (β : S.Ch) (hV : EvValLe S β) (γ0 : GL (Fin (D.R.N i)) D.host.E)
    {Q : XR (Hc S β).P ℂ} (hQ : Q ∈ VtupR (Hc S β).P ℂ) :
    phiC S β γ0 Q ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (lamTG M i) := by
  have h1 := foValC_tr (M.lam i) (Formalism.L2.Forms.atInf (embT D) γ0.1) (foInf_unit (embT D) γ0) (hV Q hQ)
  have h2 := (mem_ValC_shW (D.R.N_pos i) (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (M.lam i) (cTw D i) 1 one_ne_zero
    (phiC S β γ0 Q)).2
  refine h2 ?_
  convert h1 using 1
  funext z
  change 1 * detF (cTw D i) z * ((detF (cTw D i) z)⁻¹ * _) = _
  rw [one_mul, ← mul_assoc, mul_inv_cancel₀ (detF_ne _ _), one_mul]
  rfl

theorem cmpLiftOf_of (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hD : VtupDesc S e) (hV : ∀ β, EvValLe S β)
    (hI : CmpInvOf S e) : CmpLiftOf S e := by
  intro hS H X β rep hok c
  obtain ⟨g, γ0, κ0, hγ0, hL, hpt⟩ := hok c
  let Y := YInv (Hc S β) e (rep c).1 (rep c).2
  let Φ : Y →+ (Formalism.L2.Forms.Frames (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) → ℂ) :=
    (phiC S β γ0).toAddMonoidHom.comp ((MvPolynomial.map D.what₂.embLL).toAddMonoidHom.comp Y.subtype.toAddMonoidHom)
  refine ⟨Φ, fun Q => ⟨?_, ?_⟩, fun k Q hQ => ?_⟩
  · exact phiC_mem_ValC S β (hV β) γ0 (hD β Q.1 Q.2.1)
  · exact hI hS H X β rep hok c g γ0 κ0 hγ0 hL hpt Q.1 Q.2
  · have a : LinearIndependent D.what₂.LL (fun j => (Q j : YR (Hc S β) D.what₂.LL)) :=
      hQ.map' Y.subtype (Submodule.ker_subtype _)
    have b := Formalism.MainNotions.G.SymmetricFormBlocks.li_map D.what₂.embLL _ a
    exact b.map' (phiC S β γ0) (ker_phiC S β γ0)

end Rec

section Card

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

end Card

end Formalism.MainNotions.G.CmpJ.PCmpLift
end
end

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PCmpLiftDesc

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Module Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe Formalism.MainNotions.G.CmpJ.PFormsCl Formalism.MainNotions.G.CmpJ.PCmpLift

section Desc

variable {LL K : Type} [Field LL] [Field K] (e : LL →+* K)

theorem lin_ext_map {σ : Type} (φ : MvPolynomial σ LL →ₗ[LL] LL) (P : MvPolynomial σ LL) :
    (MvPolynomial.basisMonomials σ K).constr K (fun m : σ →₀ ℕ => e (φ (MvPolynomial.monomial m 1)))
      (MvPolynomial.map e P) = e (φ P) := by
  induction P using MvPolynomial.induction_on'
  next u a =>
    have h1 : MvPolynomial.map e (MvPolynomial.monomial u a) = e a • MvPolynomial.basisMonomials σ K u := by
      simp only [MvPolynomial.map_monomial, MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have h2 : MvPolynomial.monomial u a = a • MvPolynomial.monomial u (1 : LL) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [h1, map_smul, Basis.constr_basis, h2, map_smul, smul_eq_mul, smul_eq_mul, map_mul]
  next p q hp hq =>
    simp only [map_add (f := _), hp, hq]

theorem desc_span {σ : Type} (V : Submodule LL (MvPolynomial σ LL)) {Q : MvPolynomial σ LL}
    (hQ : MvPolynomial.map e Q ∈ Submodule.span K (MvPolynomial.map e '' (V : Set (MvPolynomial σ LL)))) : Q ∈ V := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  let φK : MvPolynomial σ K →ₗ[K] K :=
    (MvPolynomial.basisMonomials σ K).constr K (fun m : σ →₀ ℕ => e (φ (MvPolynomial.monomial m 1)))
  have h1 : Submodule.span K (MvPolynomial.map e '' (V : Set (MvPolynomial σ LL))) ≤ LinearMap.ker φK := by
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    change φK (MvPolynomial.map e v) = 0
    rw [lin_ext_map e φ v, (Submodule.mem_dualAnnihilator φ).1 hφ v hv, map_zero]
  have h2 : φK (MvPolynomial.map e Q) = 0 := h1 hQ
  rw [lin_ext_map e φ Q] at h2
  exact (map_eq_zero_iff e e.injective).1 h2

theorem dw_desc {r n : ℕ} (ν : Fin n → ℕ) {f : MvPolynomial (Fin r × Fin n) LL}
    (h : MvPolynomial.map e f ∈ Formalism.GradedWeylDivisibility.dualWeyl K r n ν) : f ∈ Formalism.GradedWeylDivisibility.dualWeyl LL r n ν := by
  rw [Formalism.GradedWeylDivisibility.mem_dualWeyl_iff, isWH_iff] at h ⊢
  refine ⟨MvPolynomial.map_injective e e.injective ?_, fun l j hlj => MvPolynomial.map_injective e e.injective ?_⟩
  · rw [whc_map, h.1]
  · rw [colAddGen_map, MvPolynomial.map_rename, h.2 l j hlj]

theorem dw_span {r n : ℕ} (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.dualWeyl K r n ν ≤
      Submodule.span K (MvPolynomial.map e '' (Formalism.GradedWeylDivisibility.dualWeyl LL r n ν : Set (MvPolynomial (Fin r × Fin n) LL))) := by
  refine (dualWeyl_desc e ν).trans (Submodule.span_mono ?_)
  rintro _ ⟨Q, hQ, rfl⟩
  exact ⟨Q, dw_desc e ν hQ, rfl⟩

theorem span_prod_le {S : Type} [Fintype S] {σ : S → Type} {τ : Type} (f : ∀ s, σ s → τ)
    (Ms : ∀ s, Submodule K (MvPolynomial (σ s) K)) (Ns : ∀ s, Submodule LL (MvPolynomial (σ s) LL))
    (hM : ∀ s, Ms s ≤ Submodule.span K (MvPolynomial.map e '' (Ns s : Set (MvPolynomial (σ s) LL)))) :
    Submodule.span K {Z | ∃ F : ∀ s, MvPolynomial (σ s) K, (∀ s, F s ∈ Ms s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)} ≤
      Submodule.span K (MvPolynomial.map e '' (Submodule.span LL
        {Z | ∃ F : ∀ s, MvPolynomial (σ s) LL, (∀ s, F s ∈ Ns s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)} :
          Set (MvPolynomial τ LL))) := by
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  let A : S → Set (MvPolynomial τ K) := fun s =>
    {y | ∃ Q : MvPolynomial (σ s) LL, Q ∈ Ns s ∧ y = MvPolynomial.rename (f s) (MvPolynomial.map e Q)}
  have hx : ∀ s ∈ Finset.univ, MvPolynomial.rename (f s) (F s) ∈ Submodule.span K (A s) := by
    intro s _
    have h1 := Submodule.mem_map_of_mem (f := (MvPolynomial.rename (R := K) (f s)).toLinearMap) (hM s (hF s))
    rw [Submodule.map_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨_, ⟨Q, hQ, rfl⟩, rfl⟩
    exact ⟨Q, hQ, rfl⟩
  have h := prod_mem_span Finset.univ A _ hx
  refine Submodule.span_mono ?_ h
  rintro _ ⟨a, ha, rfl⟩
  choose Q hQ hQe using fun s => ha s (Finset.mem_univ s)
  refine ⟨∏ s, MvPolynomial.rename (f s) (Q s), Submodule.subset_span ⟨Q, hQ, rfl⟩, ?_⟩
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [hQe s, MvPolynomial.map_rename]

theorem vsp_span {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) :
    Vsp K lam0 ≤ Submodule.span K (MvPolynomial.map e '' (Vsp LL lam0 : Set (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) LL))) := by
  have hM : ∀ s : Fin n', (if Antitone (lamAt lam0 s) then Formalism.GradedWeylDivisibility.dualWeyl K (m + 1) (m + 1) (nuOf (lamAt lam0 s)) else ⊥) ≤
      Submodule.span K (MvPolynomial.map e '' (((if Antitone (lamAt lam0 s) then
        Formalism.GradedWeylDivisibility.dualWeyl LL (m + 1) (m + 1) (nuOf (lamAt lam0 s)) else ⊥ : Submodule LL _)) : Set (MvPolynomial (Fin (m + 1) × Fin (m + 1)) LL))) := by
    intro s
    split_ifs
    · exact dw_span e _
    · exact bot_le
  exact span_prod_le e (σ := fun _ => Fin (m + 1) × Fin (m + 1)) (fun s v => (s, v)) _ _ hM

theorem vtup_span {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) : VtupR P K ≤ Submodule.span K (MvPolynomial.map e '' (VtupR P LL : Set (XR P LL))) :=
  span_prod_le e (σ := fun v => Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) (fun v x => (⟨v, x⟩ : Var P)) _ _
    fun v => vsp_span e (P.lam0 v)

theorem span_prod_map {S : Type} [Fintype S] {σ : S → Type} {τ : Type} (f : ∀ s, σ s → τ)
    (Ns : ∀ s, Submodule LL (MvPolynomial (σ s) LL)) (Ms : ∀ s, Submodule K (MvPolynomial (σ s) K))
    (h : ∀ s, ∀ x ∈ Ns s, MvPolynomial.map e x ∈ Ms s) {Z : MvPolynomial τ LL}
    (hZ : Z ∈ Submodule.span LL {Z | ∃ F : ∀ s, MvPolynomial (σ s) LL, (∀ s, F s ∈ Ns s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)}) :
    MvPolynomial.map e Z ∈
      Submodule.span K {Z | ∃ F : ∀ s, MvPolynomial (σ s) K, (∀ s, F s ∈ Ms s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)} := by
  induction hZ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun s => MvPolynomial.map e (F s), fun s => h s _ (hF s), ?_⟩
    simp only [map_prod, MvPolynomial.map_rename]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [mapE_smul]; exact Submodule.smul_mem _ _ hx

theorem vsp_map {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) {x : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) LL}
    (hx : x ∈ Vsp LL lam0) : MvPolynomial.map e x ∈ Vsp K lam0 := by
  refine span_prod_map e (σ := fun _ => Fin (m + 1) × Fin (m + 1)) (fun s v => (s, v)) _ _ (fun s y hy => ?_) hx
  split_ifs at hy ⊢
  · exact Formalism.GradedWeylDivisibility.dualWeylMap LL K e _ _ _ y hy
  · rw [(Submodule.mem_bot _).1 hy, map_zero]
    exact Submodule.zero_mem _

theorem vtup_map {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) {Q : XR P LL} (hQ : Q ∈ VtupR P LL) : MvPolynomial.map e Q ∈ VtupR P K :=
  span_prod_map e (σ := fun v => Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) (fun v x => (⟨v, x⟩ : Var P)) _ _
    (fun v _ hy => vsp_map e (P.lam0 v) hy) hQ

end Desc

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

theorem vtupDesc_holds (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : VtupDesc S e := by
  intro β Q hQ
  exact vtup_map D.what₂.embLL _ (desc_span e (VtupR (Hc S β).P D.what₂.LL) (vtup_span e (Hc S β).P hQ))

theorem cmpLiftOf_of_two (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hV : ∀ β, EvValLe S β) (hI : CmpInvOf S e) :
    CmpLiftOf S e :=
  cmpLiftOf_of S e (vtupDesc_holds S e) hV hI

end Rec

end Formalism.MainNotions.G.CmpJ.PCmpLiftDesc
end
end

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PCmpLiftTw

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Module Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe Formalism.MainNotions.G.CmpJ.PFormsCl Formalism.MainNotions.G.CmpJ.PCmpLift
  Formalism.MainNotions.G.CmpJ.PCmpLiftDesc

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T fT : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {S : StepLevel F E σ J T fT bad} {emb : Tau → E →+* ℂ} {c : ℤ}

theorem tw_triv (X : DetTw S emb c) {y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)} {γ : GL (Fin n) E}
    (hγ : γ ∈ UJ (σ : E →+* E) J) {κ : S.U}
    (h : y0.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1) :
    ∏ τ, (emb τ (γ : Matrix (Fin n) (Fin n) E).det) ^ c = 1 := by
  let xg : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ, ratInU γ hγ⟩
  let xk : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩
  have e1 : xg * y0 * xk = y0 := Subtype.ext h.symm
  have e2 : X.ch xg = 1 := by
    have h3 := congrArg X.ch e1
    rw [map_mul, map_mul, X.ch_U xk κ.2, mul_one] at h3
    exact mul_right_cancel (h3.trans (one_mul _).symm)
  have h4 := X.ch_rat γ hγ xg rfl
  rwa [e2, Units.val_one, one_mul] at h4

theorem detF_tr (γ : GL (Fin n) E) {y y' : Formalism.L2.Forms.Frames (gramC J emb)} (hy : IsTr (atInf emb γ) y' y) :
    detF c y = (∏ τ, (emb τ (γ : Matrix (Fin n) (Fin n) E).det) ^ c) * detF c y' := by
  unfold detF
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [hy τ, Matrix.det_mul, mul_zpow]
  congr 2
  simp [atInf, RingHom.map_det]

theorem foInv_twist (X : DetTw S emb c) {y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)} {h : Formalism.L2.Forms.Frames (gramC J emb) → ℂ}
    (hh : FoInv S emb y0 h) : FoInv S emb y0 (fun z => (detF c z)⁻¹ * h z) := by
  intro γ hγ κ hy0 y y' hy
  simp only
  rw [hh γ hγ κ hy0 y y' hy, detF_tr γ hy, tw_triv X hγ hy0, one_mul]
  ring

end Gen

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

def CmpInvRawOf (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  BlockRationalityField → (∀ β, S.Core e β) → KAat.ChX S → ∀ β rep, RepOk S β rep → ∀ c
    (g : ∀ v, GL (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v)) (γ0 : GL (Fin (D.R.N i)) D.host.E) (κ0 : (S.K β).lev.U),
    γ0 ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) →
    (∀ v, (rep c).2 v = colSpan ((Hc S β).P.W v) (g v : Matrix (Fin ((Hc S β).P.m + 1)) (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v))) →
    (S.loc β).IsPt (rep c).1 g (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0 * ((S.K β).y c).1 * κ0.1) →
    ∀ Q ∈ YInv (Hc S β) e (rep c).1 (rep c).2,
      FoInv (S.K β).lev (embT D) ((S.K β).y c) (fun z =>
        evC (Hc S β).P (S.loc β).rk S.pos (gramC (gramN D i hi) (embT D)) (crdB (embT D) (S.loc β).B)
          (MvPolynomial.map D.what₂.embLL Q) (foTrR (embT D) γ0 z))

theorem cmpInvOf_of_raw (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hR : CmpInvRawOf S e) : CmpInvOf S e := by
  intro hS H X β rep hok c g γ0 κ0 hγ0 hL hpt Q hQ
  exact foInv_twist (S.tw β) (hR hS H X β rep hok c g γ0 κ0 hγ0 hL hpt Q hQ)

theorem cmpLiftOf_of_raw (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hV : ∀ β, EvValLe S β) (hR : CmpInvRawOf S e) :
    CmpLiftOf S e :=
  cmpLiftOf_of_two S e hV (cmpInvOf_of_raw S e hR)

end Rec

section Card

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

end Card

end Formalism.MainNotions.G.CmpJ.PCmpLiftTw
end
end

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PCmpLiftInv

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Module Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe Formalism.MainNotions.G.CmpJ.PFormsCl Formalism.MainNotions.G.CmpJ.PCmpLift
  Formalism.MainNotions.G.CmpJ.PCmpLiftDesc Formalism.MainNotions.G.CmpJ.PCmpLiftTw

theorem grp2 {Γ : Type} [Group Γ] (b y k : Γ) (h : y = b * y * k) : b = y * k⁻¹ * y⁻¹ := by
  rw [show y * k⁻¹ * y⁻¹ = (b * y * k) * k⁻¹ * y⁻¹ by rw [← h]]
  group

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}


set_option maxHeartbeats 4000000 in
theorem cmpInvRaw_holds (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : CmpInvRawOf S e := by
  intro hS H X β rep hok c g γ0 κ0 hγ0 hL hpt Q hQ γ hγ κ hyc y y' hy
  have Hb := H β
  obtain ⟨x, hx⟩ : ∃ x, x = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0 * ((S.K β).y c).1 * κ0.1 :=
    ⟨_, rfl⟩
  rw [← hx] at hpt
  have hxU : x ∈ UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    rw [hx]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (PStabEq.bc_mem hγ0) ((S.K β).y c).2) (PStabEq.U_le κ0.2)
  have hb : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ =
      ((S.K β).y c).1 * κ.1⁻¹ * ((S.K β).y c).1⁻¹ := grp2 _ _ _ hyc
  have hyU : ((S.K β).y c).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * ((S.K β).y c).1 ∈
      (S.K β).lev.U := by
    rw [hb, show ((S.K β).y c).1⁻¹ * (((S.K β).y c).1 * κ.1⁻¹ * ((S.K β).y c).1⁻¹) * ((S.K β).y c).1 = κ.1⁻¹ by group]
    exact (S.K β).lev.U.inv_mem κ.2
  have hδU : γ0 * γ * γ0⁻¹ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hγ0 hγ) (Subgroup.inv_mem _ hγ0)
  have hδx : x⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ0 * γ * γ0⁻¹) * x ∈ (S.K β).lev.U :=
    PStabEq.conj_mem' x ((S.K β).y c).1 γ0 γ κ0 hx hyU
  obtain ⟨⟨γ', hfix⟩, hγ'⟩ := (PStabEq.stab_bij Hb.good Hb.int Hb.hypP (X.hypC β) Hb.bad_p Hb.actB Hb.gam Hb.gamU (rep c).1
    (X.inj β _) (X.onto β _) (rep c).2 g hL ⟨x, hxU⟩ hpt).2 ⟨γ0 * γ * γ0⁻¹, hδU, hδx⟩
  have hgam : (S.loc β).gamI (rep c).1 γ' = γ0 * γ * γ0⁻¹ := congrArg Subtype.val hγ'
  obtain ⟨κa, hκa⟩ := awayEx_of Hb.good (S.K β).lev Hb.gam (rep c).1 γ'
  obtain ⟨r, hr, hr1⟩ := Hb.chi (rep c).1 γ' κa hκa

  have hN : natActR (Hc S β).P D.what₂.LL (blkLL (S.loc β) (sigD D) (tEL D) S.pos ((S.loc β).gamI (rep c).1 γ')) Q = r • Q := by
    apply MvPolynomial.map_injective e e.injective
    have h1 := hQ.2 γ' hfix
    rw [actX_map (S.loc β) (tEL D) S.pos e Hb.actB Hb.pos_emb (rep c).1 γ' Q] at h1
    have hr1' : algebraMap G.O G.Kf (((Hc S β).lev (rep c).1).χ γ' : G.O) * e r = 1 := hr1
    rw [mapE_smul e r Q, ← h1, ← algebraMap_smul G.Kf (((Hc S β).lev (rep c).1).χ γ' : G.O), smul_smul, mul_comm (e r), hr1',
      one_smul]

  have e1 : x⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ0 * γ * γ0⁻¹) * x =
      κ0.1⁻¹ * κ.1⁻¹ * κ0.1 := by
    rw [hx, map_mul, map_mul, map_inv, hb]
    group
  have ht : ∀ v ∈ S.bad, bc (prV (E := D.host.E) v) (κa * (κ0⁻¹ * κ * κ0)).1 = 1 := by
    intro v hv
    have hvp := Hb.bad_p v hv
    have a1 := hκa.2 v hvp
    have a2 : bc (prV (E := D.host.E) v) ((S.loc β).yG (rep c).1) = bc (prV (E := D.host.E) v) x := (hpt.1 v hvp).symm
    have key : bc (prV (E := D.host.E) v) κa.1 =
        bc (prV (E := D.host.E) v) (x⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ0 * γ * γ0⁻¹) * x) := by
      rw [a1, hgam]
      simp only [map_mul, map_inv, a2]
    have e2 : (κa * (κ0⁻¹ * κ * κ0)).1 = κa.1 * (κ0.1⁻¹ * κ.1 * κ0.1) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e2, map_mul, key, ← map_mul, e1,
      show κ0.1⁻¹ * κ.1⁻¹ * κ0.1 * (κ0.1⁻¹ * κ.1 * κ0.1) = 1 by group, map_one]
  have hc : ((S.K β).lev.chi κa : ℂ) * ((S.K β).lev.chi κ : ℂ) = 1 := by
    have h0 := congrArg (fun w : ℂˣ => (w : ℂ)) ((S.K β).lev.chi_triv _ ht)
    simp only [map_mul, map_inv, Units.val_mul, Units.val_one, Units.val_inv_eq_inv_val] at h0
    have hne : ((S.K β).lev.chi κ0 : ℂ) ≠ 0 := Units.ne_zero _
    field_simp at h0
    linear_combination h0

  have hz : IsTr (atInf (embT D) ((S.loc β).gamI (rep c).1 γ').1) (foTrR (embT D) γ0 y') (foTrR (embT D) γ0 y) := by
    rw [foIsTr_iff, hgam, (foIsTr_iff (embT D) γ y' y).1 hy, ← foTrR_mul, ← foTrR_mul]
    congr 1
    group
  have hE := evC_blk (S.loc β) (tEL D) S.pos (embT D) D.what₂.embLL (tEL_emb D) ((S.loc β).gamI (rep c).1 γ')
    (unit_of_std (S.loc β).B _ Hb.std (Hb.gamU _ γ')) (gramC (gramN D i hi) (embT D)) _ _ hz Q
  rw [hN, Formalism.L2.G.Cmp.map_smul', map_smul, Pi.smul_apply, smul_eq_mul, hr] at hE
  show _ = ((S.K β).lev.chi κ : ℂ) * _
  linear_combination (((S.K β).lev.chi κ : ℂ)) * hE - (evC (Hc S β).P (S.loc β).rk S.pos (gramC (gramN D i hi) (embT D))
    (crdB (embT D) (S.loc β).B) (MvPolynomial.map D.what₂.embLL Q) (foTrR (embT D) γ0 y)) * hc

theorem cmpLiftOf_of_evVal (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hV : ∀ β, EvValLe S β) : CmpLiftOf S e :=
  cmpLiftOf_of_raw S e hV (cmpInvRaw_holds S e)

end Rec

section Card

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

end Card

end Formalism.MainNotions.G.CmpJ.PCmpLiftInv
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ChartRank.NuOfAntiEv
open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms

noncomputable section

namespace Formalism.L2.G.EvLe

open Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags Formalism.L2.G.RelativeIndexFlags.Core

theorem nuOf_anti_ev {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone (nuOf lam) := by
  intro i j hij
  unfold nuOf
  exact Int.toNat_le_toNat (by have := h hij; omega)

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem vsp_le (v : Fin P.nV) :
    Vsp ℂ (P.lam0 v) ≤ Submodule.span ℂ {Y | ∃ f : Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ,
      (∀ s, f s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) ∧
        Y = ∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f s))} := by
  let T : Fin (P.n' v) → Set (MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℂ) := fun s =>
    (fun f => map (Int.castRingHom ℂ) f) '' (weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s)) :
      Set (MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ))
  have hM : ∀ s F, F ∈ (if Antitone (lamAt (P.lam0 v) s) then
      dualWeyl ℂ (P.m + 1) (P.m + 1) (nuOf (lamAt (P.lam0 v) s)) else ⊥) → F ∈ Submodule.span ℂ (T s) := by
    intro s F hF
    have ha := lamAt_anti (P.lam0 v) (P.dom v) s
    rw [if_pos ha, ← Formalism.L2.G.Model.sw_weyl_eq ℂ (P.m + 1) (P.m + 1) le_rfl _ (nuOf_anti_ev ha),
      weyl_eq_span_int] at hF
    exact hF
  have hP := prodSpan (O := ℂ) (I := Fin (P.n' v)) (B := fun _ => MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℂ)
    (fun s => (blockEmb ℂ (S := Fin (P.n' v)) (k := P.m + 1) (n := P.m + 1) s).toLinearMap) T
  unfold Vsp tensorLat
  refine (Submodule.span_mono ?_).trans (hP.le.trans (Submodule.span_mono ?_))
  · rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, fun s => hM s _ (hF s), rfl⟩
  · rintro _ ⟨F, hF, rfl⟩
    choose f hf hfe using fun s => (Set.mem_image _ _ _).1 (hF s)
    exact ⟨f, hf, Finset.prod_congr rfl fun s _ => by rw [← hfe s]; rfl⟩

theorem vtup_le : VtupR P ℂ ≤ Submodule.span ℂ {X | ∃ f : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ,
    (∀ v s, f v s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) ∧
      X = ∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f v s)))} := by
  let T : ∀ v : Fin P.nV, Set (MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) ℂ) := fun v =>
    {Y | ∃ f : Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ,
      (∀ s, f s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) ∧
        Y = ∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f s))}
  have hP := prodSpan (O := ℂ) (I := Fin P.nV)
    (B := fun v => MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) ℂ)
    (fun v => (rename (R := ℂ) (fun x : Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1)) => (⟨v, x⟩ : Var P))).toLinearMap) T
  unfold VtupR
  refine (Submodule.span_mono ?_).trans (hP.le.trans (Submodule.span_mono ?_))
  · rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, fun v => vsp_le P v (hF v), rfl⟩
  · rintro _ ⟨F, hF, rfl⟩
    have hF' : ∀ v, ∃ f : Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ,
        (∀ s, f s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) ∧
          F v = ∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f s)) := hF
    choose f hf hfe using hF'
    exact ⟨f, hf, Finset.prod_congr rfl fun v _ => by rw [hfe v]; rfl⟩

variable {Tau : Type} [Fintype Tau] (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau)

theorem blockRowSubstitution_one (v : Fin P.nV) (s : Fin (P.n' v)) (f : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ) :
    map (RingHom.id ℂ) (bl P rfl pos (fun _ => (1 : GL (Fin (P.m + 1)) ℂ)) v s f) = map (Int.castRingHom ℂ) f := by
  have hn : nAt P rfl pos (fun _ => (1 : GL (Fin (P.m + 1)) ℂ)) v s = 1 := by
    unfold nAt; split_ifs <;> simp
  have hi : niAt P rfl pos (fun _ => (1 : GL (Fin (P.m + 1)) ℂ)) v s = 1 := by
    unfold niAt; split_ifs <;> simp
  unfold bl
  rw [hn, hi, Matrix.det_one, _root_.one_zpow, one_smul, rowAct_one, MvPolynomial.map_id]

theorem gen_mem (G : Tau → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (M : Tau → GL (Fin (P.m + 1)) ℂ)
    (lam : Tau → DomWeight (P.m + 1)) (hw : WtTie P rfl pos lam)
    (f : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ)
    (hf : ∀ v s, f v s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) :
    evC P rfl pos G (fun τ => (M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ))
      (∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f v s)))) ∈ ValC G lam := by
  choose ft hft hev using fun x : Σ v : Fin P.nV, Fin (P.n' v) =>
    (blk_ev P pos lam M (fun _ => 1) (RingHom.id ℂ) (fun m l _ => oddFact_pf ℤ m l) hw x).1 (f x.1 x.2) (hf x.1 x.2)
  have hX : (∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f v s)))) =
      map (RingHom.id ℂ) (gen P rfl pos (fun _ => (1 : GL (Fin (P.m + 1)) ℂ)) f) := by
    rw [map_gen]
    simp only [blockRowSubstitution_one]
  have hM : (fun τ => (M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)) = mcOf M (RingHom.id ℂ) := by
    funext τ; ext a b; rfl
  have key : evC P rfl pos G (mcOf M (RingHom.id ℂ)) (map (RingHom.id ℂ) (gen P rfl pos (fun _ => 1) f)) =
      fnOf G (shiftOf lam) (kcOf M (fun _ => 1) (RingHom.id ℂ))
        (ten fun τ => map (Int.castRingHom ℂ) (ft (pos.symm τ))) := by
    funext z
    refine evC_gen P pos lam M (fun _ => 1) (RingHom.id ℂ) G f (fun τ => ft (pos.symm τ)) (fun x => ?_) z
    show BlockRealisation P pos lam M (fun _ => 1) (RingHom.id ℂ) x (f x.1 x.2) (ft (pos.symm (pos x)))
    rw [pos.symm_apply_apply]
    exact hev x
  have hK : kcOf M (fun _ => 1) (RingHom.id ℂ) = fun τ => (M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) := by
    funext τ; ext a b; simp [kcOf]
  have hP : ten (fun τ => map (Int.castRingHom ℂ) (ft (pos.symm τ))) ∈ CSpan lam := by
    refine Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩
    have h1 := hft (pos.symm τ)
    rw [pos.apply_symm_apply] at h1
    unfold delSq at h1 ⊢
    exact map_mem_weyl le_rfl _ _ h1
  have h0 : fnOf G (shiftOf lam) 1 (ten fun τ => map (Int.castRingHom ℂ) (ft (pos.symm τ))) ∈ ValC G lam :=
    Submodule.mem_map_of_mem hP
  have hu : ∀ τ, IsUnit ((M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)).det := fun τ =>
    (Matrix.isUnit_iff_isUnit_det _).1 (M τ).isUnit
  have h1 := Formalism.MainNotions.G.CmpJ.PFormsCl.foValC_tr lam (fun τ => (M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)) hu h0
  rw [hX, hM, key, hK]
  convert h1 using 1
  funext y
  simp [fnOf, Formalism.MainNotions.G.CmpJ.PFormsCl.foTr]

end Gen

section Main

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ}

theorem evC_le (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G : Tau → Matrix (Fin n) (Fin n) ℂ)
    (M : Tau → GL (Fin n) ℂ) (lam : Tau → DomWeight n) (hw : WtTie P h pos lam) :
    ∀ Q ∈ VtupR P ℂ, evC P h pos G (fun τ => (M τ : Matrix (Fin n) (Fin n) ℂ)) Q ∈ ValC G lam := by
  subst h
  intro Q hQ
  have hS := vtup_le P hQ
  clear hQ
  induction hS using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨f, hf, rfl⟩ := hX
    exact gen_mem P pos G M lam hw f hf
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

end Main

end Formalism.L2.G.EvLe
end
end

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PEvValChain

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Module Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe Formalism.MainNotions.G.CmpJ.PFormsCl Formalism.MainNotions.G.CmpJ.PCmpLift
  Formalism.MainNotions.G.CmpJ.PCmpLiftDesc Formalism.MainNotions.G.CmpJ.PCmpLiftTw Formalism.MainNotions.G.CmpJ.PCmpLiftInv

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

theorem evValLe_of_wt (S : StepIn M i hi G) (β : S.Ch) (hw : WtTie (Hc S β).P (S.loc β).rk S.pos (M.lam i)) :
    EvValLe S β := by
  intro Q hQ
  exact Formalism.L2.G.EvLe.evC_le (Hc S β).P (S.loc β).rk S.pos (gramC (gramN D i hi) (embT D))
    (atInfGL (embT D) (S.loc β).B⁻¹) (M.lam i) hw Q hQ

theorem cmpLiftOf_holds (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : CmpLiftOf S e := by
  intro hS H X
  exact cmpLiftOf_of_evVal S e (fun β => evValLe_of_wt S β (H β).wt) hS H X

end Rec

section Card

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

end Card

end Formalism.MainNotions.G.CmpJ.PEvValChain
