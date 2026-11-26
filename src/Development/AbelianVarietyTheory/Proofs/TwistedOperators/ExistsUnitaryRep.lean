module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActEqTranslate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointThLeSpanGood
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGramSchmidtIndefiniteHermitianFrames

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHeckeOpFullOfLevel
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.RowsNonzero

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {K G X H E : Type} [Field K] [Group G] [Fintype G] [AddCommGroup X] [Module K X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]


omit [Fintype G] in
theorem mem_range_adjoint (ρ : Representation ℂ G H) (π : Representation ℂ G E) (Θ : H →ₗ[ℂ] E)
    (hρ : ∀ g y, ‖ρ g y‖ = ‖y‖) (hΘ : ∀ g y, Θ (ρ g y) = π g (Θ y)) (g : G) {y : H}
    (hy : y ∈ LinearMap.range (LinearMap.adjoint Θ)) : ρ g y ∈ LinearMap.range (LinearMap.adjoint Θ) := by
  rw [← LinearMap.orthogonal_ker, Submodule.mem_orthogonal] at hy ⊢
  intro u hu
  have h1 : ρ g (ρ g⁻¹ u) = u := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have h2 : inner ℂ (ρ g (ρ g⁻¹ u)) (ρ g y) = inner ℂ (ρ g⁻¹ u) y := LinearIsometry.inner_map_map ⟨ρ g, hρ g⟩ _ _
  rw [← h1, h2]
  refine hy _ ?_
  rw [LinearMap.mem_ker] at hu ⊢
  rw [hΘ, hu, map_zero]

theorem exists_rational {σ : K →+* ℂ} (j : X →ₛₗ[σ] H) (r : Representation K G X) (ρ : Representation ℂ G H)
    (π : Representation ℂ G E) (Θ : H →ₗ[ℂ] E) (hj : ∀ g z, j (r g z) = ρ g (j z)) (hρ : ∀ g y, ‖ρ g y‖ = ‖y‖)
    (hΘ : ∀ g y, Θ (ρ g y) = π g (Θ y))
    (hrat : LinearMap.range (LinearMap.adjoint Θ) ≤
      Submodule.span ℂ (j '' {z | j z ∈ LinearMap.range (LinearMap.adjoint Θ)}))
    (a b : G → K) {x u : E} (hx : x ≠ 0) (hu : Θ (LinearMap.adjoint Θ u) = x)
    (ha : ∑ g, σ (a g) • π g x = x) (hb : ∑ g, σ (b g) • π g x = x) :
    ∃ z, (∑ g, a g • r g) ((∑ g, b g • r g) z) ≠ 0 ∧
      j ((∑ g, a g • r g) ((∑ g, b g • r g) z)) ∈ LinearMap.range (LinearMap.adjoint Θ) := by
  have hop : ∀ (c : G → K) z, j ((∑ g, c g • r g) z) = ∑ g, σ (c g) • ρ g (j z) := fun c z => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, hj]
  have hst : ∀ (c : G → K) z, j z ∈ LinearMap.range (LinearMap.adjoint Θ) →
      j ((∑ g, c g • r g) z) ∈ LinearMap.range (LinearMap.adjoint Θ) := fun c z hz => by
    rw [hop]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (mem_range_adjoint ρ π Θ hρ hΘ g hz)
  have hth : ∀ (c : G → K) z, Θ (j ((∑ g, c g • r g) z)) = (∑ g, σ (c g) • π g) (Θ (j z)) := fun c z => by
    rw [hop]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hΘ, LinearMap.sum_apply, LinearMap.smul_apply]
  by_contra hn
  push Not at hn
  have hker : Submodule.span ℂ (j '' {z | j z ∈ LinearMap.range (LinearMap.adjoint Θ)}) ≤
      LinearMap.ker ((∑ g, σ (a g) • π g) ∘ₗ (∑ g, σ (b g) • π g) ∘ₗ Θ) := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    have h0 : (∑ g, a g • r g) ((∑ g, b g • r g) z) = 0 := by
      by_contra h0
      exact hn z h0 (hst a _ (hst b z hz))
    show (∑ g, σ (a g) • π g) ((∑ g, σ (b g) • π g) (Θ (j z))) = 0
    rw [← hth, ← hth, h0, map_zero, map_zero]
  have h1 : (∑ g, σ (a g) • π g) ((∑ g, σ (b g) • π g) (Θ (LinearMap.adjoint Θ u))) = 0 := hker (hrat ⟨u, rfl⟩)
  simp only [hu, LinearMap.sum_apply, LinearMap.smul_apply, hb, ha] at h1
  exact hx h1


omit [FiniteDimensional ℂ E] in
theorem sum_lvlIdem {σ : K →+* ℂ} (π : Representation ℂ G E) (P : Subgroup G) (ψ : P →* Kˣ) {x : E}
    (hx : ∀ g : P, π (g : G) x = σ ((ψ g : Kˣ) : K) • x) : ∑ g, σ ((lvlIdem P ψ).coeff g) • π g x = x := by
  classical
  have hc : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h1 : ∀ (h : G) (c : K), ∑ g, σ ((MonoidAlgebra.single h c).coeff g) • π g x = σ c • π h x := fun h c => by
    rw [Finset.sum_eq_single h]
    · simp
    · intro g _ hg
      simp [Finsupp.single_eq_of_ne hg]
    · simp
  have h2 : ∀ h : P, σ ((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) • π (h : G) x = (Nat.card P : ℂ)⁻¹ • x := fun h => by
    rw [hx h, smul_smul, ← map_mul, mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, mul_one,
      map_inv₀, map_natCast]
  unfold lvlIdem
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, map_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [h1, h2, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← Nat.card_eq_fintype_card, mul_inv_cancel₀ hc, one_smul]

end Abstract

section Hecke

open GlobalTheory.HeckeModel GlobalTheory.SphericalOps

variable {D : D7}

variable {V : HSp D} {S : D.what₂.Tau → SPar} {β : GL (Fin V.rank) (Lev.EAf D)}

end Hecke

section Rows

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem dZ_pos {K : Type} [Field K] [NumberField K] [StarRing K] (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)
    {z : B.S.Forms} (h0 : B.S.gaOp B.r (idemOf ℓ.X) (B.S.gaOp B.r (lvlIdem ℓ.P ℓ.ψ) z) ≠ 0)
    (hZ : B.S.gaOp B.r (idemOf ℓ.X) (B.S.gaOp B.r (lvlIdem ℓ.P ℓ.ψ) z) ∈ Z) : 0 < B.dZ ℓ Z := by
  rw [← B.gaOp_mul, ← goodAt] at h0 hZ
  have hV : LinearMap.range (B.vE ℓ).mulVecLin = LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin :=
    (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ))).2
  obtain ⟨u, hu⟩ : B.S.basis.equivFun (B.S.gaOp B.r (goodAt ℓ.X ℓ.P ℓ.ψ) z) ∈ LinearMap.range (B.vE ℓ).mulVecLin := by
    rw [hV]
    exact ⟨B.S.basis.equivFun z, by rw [Matrix.mulVecLin_apply, CSD.gaMat_mulVec_equivFun]⟩
  rw [Matrix.mulVecLin_apply] at hu
  refine Nat.pos_of_ne_zero fun h => h0 ?_
  have h1 : u ∈ B.Z0 ℓ Z := by
    rw [BlockDat.Z0, B.mem_goodPart_iff, hu, LinearEquiv.symm_apply_apply]
    exact hZ
  rw [Submodule.finrank_eq_zero.1 h, Submodule.mem_bot] at h1
  rw [h1, Matrix.mulVec_zero] at hu
  exact B.S.basis.equivFun.map_eq_zero_iff.1 hu.symm

end Rows

end GlobalTheory.RowsNonzero

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.RowsPosRed

theorem exists_unitary_rep {K G V H E : Type} [Field K] [StarRing K] [Group G] [AddCommGroup V] [Module K V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [AddCommGroup E] [Module ℂ E] {σ : K →+* ℂ} (j : V →ₛₗ[σ] H)
    {ι : Type} (b : Module.Basis ι K V) (hli : LinearIndependent ℂ fun k => j (b k))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hiso : ∀ x y, ⟪j x, j y⟫_ℂ = σ (h x y)) (r : Representation K G V) (hr : ∀ g x y, h (r g x) (r g y) = h x y)
    (Θ : H →ₗ[ℂ] E) (π : Representation ℂ G E) (hΘ : ∀ g z, Θ (j (r g z)) = π g (Θ (j z))) :
    ∃ ρ : Representation ℂ G H, (∀ g z, j (r g z) = ρ g (j z)) ∧ (∀ g y, ‖ρ g y‖ = ‖y‖) ∧
      ∀ g y, Θ (ρ g y) = π g (Θ y) := by
  let B : Module.Basis ι ℂ H := Module.Basis.mk hli hsp.ge
  have hB : ∀ k, B k = j (b k) := fun k => Module.Basis.mk_apply hli hsp.ge k
  let f : G → Module.End ℂ H := fun g => B.constr ℂ fun k => j (r g (b k))
  have hf : ∀ g z, f g (j z) = j (r g z) := by
    intro g z
    have : (f g).comp j = j.comp (r g) := b.ext fun k => by
      show f g (j (b k)) = j (r g (b k))
      rw [← hB]
      exact B.constr_basis ℂ _ k
    exact LinearMap.congr_fun this z
  let ρ : Representation ℂ G H :=
    { toFun := f
      map_one' := B.ext fun k => by
        show f 1 (B k) = B k
        rw [hB, hf, map_one, Module.End.one_apply]
      map_mul' := fun g g' => B.ext fun k => by
        show f (g * g') (B k) = f g (f g' (B k))
        rw [hB, hf, hf, hf, map_mul, Module.End.mul_apply] }
  have hρ : ∀ g z, ρ g (j z) = j (r g z) := hf
  have hin : ∀ g y y', ⟪ρ g y, ρ g y'⟫_ℂ = ⟪y, y'⟫_ℂ := by
    intro g
    have h1 : ∀ k y', ⟪ρ g (B k), ρ g y'⟫_ℂ = ⟪B k, y'⟫_ℂ := by
      intro k
      have : (innerₛₗ ℂ (ρ g (B k))).comp (ρ g) = innerₛₗ ℂ (B k) := B.ext fun l => by
        show ⟪ρ g (B k), ρ g (B l)⟫_ℂ = ⟪B k, B l⟫_ℂ
        rw [hB, hB, hρ, hρ, hiso, hiso, hr]
      exact fun y' => LinearMap.congr_fun this y'
    intro y y'
    have : (innerₛₗ ℂ (ρ g y)).comp (ρ g) = innerₛₗ ℂ y := B.ext fun l => by
      show ⟪ρ g y, ρ g (B l)⟫_ℂ = ⟪y, B l⟫_ℂ
      rw [← inner_conj_symm, h1, inner_conj_symm]
    exact LinearMap.congr_fun this y'
  refine ⟨ρ, fun g z => (hρ g z).symm, fun g y => ?_, fun g => ?_⟩
  · rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hin]
  · have : Θ.comp (ρ g) = (π g).comp Θ := B.ext fun k => by
      show Θ (ρ g (B k)) = π g (Θ (B k))
      rw [hB, hρ, hΘ]
    exact fun y => LinearMap.congr_fun this y

end GlobalTheory.RowsPosRed

namespace GlobalTheory.RowsPosRed

open Formalism.IndefR.Cx.CxData

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem sum_idem_gEx (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : GlobalTheory.Hk3.Core R.toRealDat F.lv2) (x : (R.toCx3 F).EE) :
    ∑ g, A3.A.fam.v0.embedding ((idemOf A3.A.X).coeff g) • R.gEx F g x = x := by
  have h := GlobalTheory.AdjGood.proj_rows_core hC (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x)
  have e : ∀ g, Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)
      (A3.A.fam.v0.embedding ((idemOf A3.A.X).coeff g) • R.gEx F g x) =
      D.what₂.embLL ((idemOf A3.A.X).coeff g) • R.gE g (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x) := by
    intro g
    have hc : cj (twAt D.what₂.embLL A3.A.v0) (A3.A.v0.embedding ((idemOf A3.A.X).coeff g)) =
        D.what₂.embLL ((idemOf A3.A.X).coeff g) := by
      rw [R.emb0, cj_cj]
    exact congrArg (fun z : ℂ => z • R.gE g (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x)) hc
  exact (Finset.sum_congr rfl fun g _ => e g).trans h

theorem range_le_span_rat {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
    (X : CxData A) (cv : CrdV A) (hK : X.KFormR) (hJ : X.JIsoR cv) (hT : Formalism.IndefR.Rat.RowTest X) (t : Bs.Tup) :
    LinearMap.range (LinearMap.adjoint (X.Θ t)) ≤
      Submodule.span ℂ (X.jR t '' {z | X.jR t z ∈ LinearMap.range (LinearMap.adjoint (X.Θ t))}) := by
  obtain ⟨N, ψ, hψ, hr⟩ := hT
  exact (Formalism.IndefR.Rat.range_adjoint_rat _ (X.jR t) (cv.hR t) (bR t) (hK t).1 (hK t).2 (hJ t) (X.Θ t) ψ hψ
    (fun i x => hr t i x)).ge

theorem exists_rho (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (hOk : A3.fam3.Ok3 s) (hM : R.toRealDat.IsModels)
    (hGE : R.PGEquiv F) :
    ∃ ρ : Representation ℂ G ((R.toCx3 F).FC A3.A.fam.μ0),
      (∀ g z, (R.toCx3 F).jR A3.A.fam.μ0 ((A3.A.fam.R A3.A.fam.μ0).r g z) = ρ g ((R.toCx3 F).jR A3.A.fam.μ0 z)) ∧
      (∀ g y, ‖ρ g y‖ = ‖y‖) ∧
      ∀ g y, (R.toCx3 F).Θ A3.A.fam.μ0 (ρ g y) = R.gEx F g ((R.toCx3 F).Θ A3.A.fam.μ0 y) := by
  have hKR : (R.toCx3 F).KFormR := RealDat3.kFormR_of hM
  have hJR : (R.toCx3 F).JIsoR F.cv := RealDat3.jIsoR_of hM
  exact exists_unitary_rep (V := (A3.A.fam.R A3.A.fam.μ0).S.Forms) (H := (R.toCx3 F).FC A3.A.fam.μ0)
    ((R.toCx3 F).jR A3.A.fam.μ0) (Formalism.IndefR.Cx.CxData.bR (A := A3.fam3.amb3) A3.A.fam.μ0) (hKR A3.A.fam.μ0).1
    (hKR A3.A.fam.μ0).2 (F.cv.hR A3.A.fam.μ0) (hJR A3.A.fam.μ0) (A3.A.fam.R A3.A.fam.μ0).r
    (fun g x y => (hOk.ok2.what₂ A3.A.fam.μ0).act.unitary g x y) ((R.toCx3 F).Θ A3.A.fam.μ0) (R.gEx F)
    (fun g z => hGE.1 A3.A.fam.μ0 g z)

theorem exists_row (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hM : R.toRealDat.IsModels) (hN : RowsNe R.toRealDat F.lv2)
    (b : Bool) : ∃ u : (R.toCx3 F).EE, u ≠ 0 ∧ u ∈ (R.toCx3 F).EEl b := by
  obtain ⟨U, hU, hU0⟩ := (Submodule.ne_bot_iff _).1 (hN b)
  have hT : U ∈ R.EEat R.triv := GlobalTheory.GoodRowsLevel.eeat_le_triv R.toRealDat _ hU
  obtain ⟨y, rfl⟩ : U ∈ LinearMap.range R.HE.e := hM.HE.2.1 ▸ hT
  refine ⟨Tw.mk (twAt D.what₂.embLL A3.A.v0) y, fun h0 => hU0 ?_, hU⟩
  have : y = 0 := h0
  rw [this, map_zero]


omit [Fintype G] in
theorem tw_eq_zero {s : Bool} {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E'] (f : E →ₗ[ℂ] E')
    (hf : Function.Injective (LinearMap.adjoint f)) (v : Tw s E') (h1 : ∀ y : Tw s E, ⟪Tw.map s f y, v⟫_ℂ = 0) : v = 0 := by
  have h5 : LinearMap.adjoint f (Tw.out v) = 0 := by
    refine ext_inner_left ℂ fun y => ?_
    rw [LinearMap.adjoint_inner_right, inner_zero_right]
    have h3 : cj s ⟪f y, Tw.out v⟫_ℂ = 0 := h1 (Tw.mk s y)
    have h4 := congrArg (cj s) h3
    rwa [cj_cj, map_zero] at h4
  exact hf (h5.trans (map_zero _).symm)

theorem surj_of_upInj (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hUp : UpInj R.toRealDat) (x : (R.toCx3 F).EE) :
    ∃ u, (R.toCx3 F).Θ A3.A.fam.μ0 (LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) u) = x := by
  have hinj : ∀ v, LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) v = 0 → v = 0 := by
    intro v hv
    have h1 : ∀ y : (R.toCx3 F).FC A3.A.fam.μ0, ⟪(R.toCx3 F).Θ A3.A.fam.μ0 y, v⟫_ℂ = 0 := fun y => by
      rw [← LinearMap.adjoint_inner_right, hv, inner_zero_right]
    exact tw_eq_zero (s := twAt D.what₂.embLL A3.A.v0) (R.Th A3.A.fam.μ0) (hUp A3.A.fam.μ0) v h1
  have h2 : Function.Injective ((R.toCx3 F).Θ A3.A.fam.μ0 ∘ₗ LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h3 : ⟪LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) v, LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) v⟫_ℂ = 0 := by
      rw [LinearMap.adjoint_inner_left]
      rw [LinearMap.comp_apply] at hv
      rw [hv, inner_zero_right]
    exact hinj v (inner_self_eq_zero.1 h3)
  exact LinearMap.injective_iff_surjective.1 h2 x

theorem dZ_pos_of_row (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (hOk : A3.fam3.Ok3 s) (hC : R.WeakCharacterisation F)
    (hEx : R.toRealDat.ExAt) (hUp : UpInj R.toRealDat) (hGE : R.PGEquiv F) (hRT : Formalism.IndefR.Rat.RowTest (R.toCx3 F))
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (u : (R.toCx3 F).EE) (hu0 : u ≠ 0)
    (hu : u ∈ typeSp3 A3 (R.toCx3 F) (R.gEx F) P ψ) :
    0 < (A3.A.fam.R A3.A.fam.μ0).dZ (A3.A.fam.lvl P ψ) ((R.toCx3 F).Z A3.A.fam.μ0) := by
  have hM : R.toRealDat.IsModels := hC.base.models
  have hrat := range_le_span_rat (R.toCx3 F) F.cv (RealDat3.kFormR_of hM) (RealDat3.jIsoR_of hM) hRT A3.A.fam.μ0
  obtain ⟨ρ, hj, hρ, hΘ⟩ := exists_rho R F hOk hM hGE
  have hCore := (GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx).1
  have htype : ∀ h : P, R.gEx F (h : G) u = A3.A.fam.v0.embedding ((ψ h : D.what₂.LLˣ) : D.what₂.LL) • u := by
    intro h
    have := (Submodule.mem_iInf _).1 hu h
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  obtain ⟨w, hw⟩ := surj_of_upInj R F hUp u
  obtain ⟨z, hz0, hz⟩ := GlobalTheory.RowsNonzero.exists_rational ((R.toCx3 F).jR A3.A.fam.μ0) (A3.A.fam.R A3.A.fam.μ0).r ρ
    (R.gEx F) ((R.toCx3 F).Θ A3.A.fam.μ0) hj hρ hΘ hrat (fun g => (idemOf A3.A.X).coeff g)
    (fun g => (lvlIdem P ψ).coeff g) hu0 hw (sum_idem_gEx R F hCore u)
    (GlobalTheory.RowsNonzero.sum_lvlIdem (R.gEx F) P ψ htype)
  exact GlobalTheory.RowsNonzero.dZ_pos (A3.A.fam.R A3.A.fam.μ0) (A3.A.fam.lvl P ψ) ((R.toCx3 F).Z A3.A.fam.μ0) hz0 hz

end GlobalTheory.RowsPosRed

theorem GlobalTheory.RowsPosRed.pos_of_rows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → UpInj R.toRealDat → RowsNe R.toRealDat F.lv2 → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hUp hNe hGE _ hRT b
  have hel := GlobalTheory.LevelRows3.eel_eq_typeSp3 R F hC
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.RowsPosRed.exists_row R F hC.base.models hNe b
  cases b
  · rw [hel.1] at hu
    exact GlobalTheory.RowsPosRed.dZ_pos_of_row R F hOk hC hEx hUp hGE hRT F.P0 F.ψ0 u hu0 hu
  · rw [hel.2] at hu
    exact GlobalTheory.RowsPosRed.dZ_pos_of_row R F hOk hC hEx hUp hGE hRT F.P1 F.ψ1 u hu0 hu
