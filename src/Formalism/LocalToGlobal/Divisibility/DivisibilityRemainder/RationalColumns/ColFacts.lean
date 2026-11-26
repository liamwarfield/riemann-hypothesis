module

public import Formalism.LocalToGlobal.IndefiniteRealisationChoice

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.RationalColumns.Descent
noncomputable section

namespace Formalism.L2.DIV.PerDescent

open Formalism.BasicNotions

theorem perCol_smul (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) (c : ℂ) (F : D.what₂.Amb D.what₂.mu0) :
    D.what₂.perCol u D.what₂.mu0 φ (c • F) = c * D.what₂.perCol u D.what₂.mu0 φ F := by
  simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, smul_eq_mul]

def perLin (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) : D.what₂.Amb D.what₂.mu0 →ₗ[ℂ] ℂ where
  toFun F := D.what₂.perCol u D.what₂.mu0 φ F
  map_add' F G := D.perCol_add u φ F G
  map_smul' c F := by simpa using perCol_smul D u φ c F

theorem exists_ext (D : D7) (γ : D.div.RR.V →ₗ[D.what₂.LL] D.what₂.LL) :
    ∃ Λ : D.what₂.EE →ₗ[ℂ] ℂ, ∀ v, Λ (D.jEE v) = D.what₂.embLL (γ v) := by
  let B : Module.Basis D.div.RR.ι ℂ D.what₂.EE := Module.Basis.mk D.jEE_basis.1 (le_of_eq D.jEE_basis.2.symm)
  refine ⟨B.constr ℂ fun i => D.what₂.embLL (γ (D.div.RR.b i)), fun v => ?_⟩
  have hB : ∀ i, B i = D.jEE (D.div.RR.b i) := fun i => Module.Basis.mk_apply _ _ i
  conv_lhs => rw [← D.div.RR.b.linearCombination_repr v]
  conv_rhs => rw [← D.div.RR.b.linearCombination_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smulₛₗ, map_smul, ← hB, Module.Basis.constr_basis, map_smul, smul_eq_mul, smul_eq_mul, map_mul]

theorem per_sec (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) {n d : ℕ} (μ : D.what₂.Tup) (hμ : μ = D.what₂.mu0)
    (a : (Fin n → D.what₂.LL) → D.what₂.Amb μ)
    (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V) (p : (Fin n → D.what₂.LL) → (Fin d → D.what₂.LL))
    (β : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] D.what₂.LL)
    (hp : Function.Surjective p)
    (hV : D.what₂.V0 μ = Submodule.span ℂ (Set.range a))
    (hι : ∀ F, D.what₂.iota μ (a F) = D.jEE (e (p F)))
    (hper : ∀ F, D.what₂.perCol u μ φ (a F) = D.what₂.embLL (β (p F))) (y : Fin d → D.what₂.LL) :
    D.what₂.perCol u D.what₂.mu0 φ (D.what₂.sec D.what₂.mu0 (D.jEE (e y))) = D.what₂.embLL (β y) := by
  subst hμ
  obtain ⟨Λ, hΛ⟩ := exists_ext D (β ∘ₗ e.symm.toLinearMap)

  have hEq : ∀ F ∈ D.what₂.V0 D.what₂.mu0, perLin D u φ F = (Λ ∘ₗ D.what₂.iota D.what₂.mu0) F := by
    intro F hF
    rw [hV] at hF
    refine LinearMap.eqOn_span (f := perLin D u φ) (g := Λ ∘ₗ D.what₂.iota D.what₂.mu0) ?_ hF
    rintro _ ⟨G, rfl⟩
    show D.what₂.perCol u D.what₂.mu0 φ (a G) = Λ (D.what₂.iota D.what₂.mu0 (a G))
    rw [hper, hι, hΛ]
    simp
  obtain ⟨F, rfl⟩ := hp y
  have hF : a F ∈ D.what₂.V0 D.what₂.mu0 := by
    rw [hV]; exact Submodule.subset_span ⟨F, rfl⟩
  set nn : D.what₂.Amb D.what₂.mu0 := (D.what₂.Usp D.what₂.mu0).starProjection (a F) with hn
  have hnU : nn ∈ D.what₂.Usp D.what₂.mu0 := Submodule.starProjection_apply_mem _ _
  have hq : a F - nn ∈ D.what₂.Qsp D.what₂.mu0 :=
    ⟨Submodule.sub_mem _ hF hnU.1, Submodule.sub_starProjection_mem_orthogonal (a F)⟩
  have hιq : D.what₂.iota D.what₂.mu0 (a F - nn) = D.jEE (e (p F)) := by
    have : D.what₂.iota D.what₂.mu0 nn = 0 := hnU.2
    rw [map_sub, this, sub_zero, hι]
  rw [← hιq, D.what₂.sec_iota _ _ hq]
  have := hEq _ hq.1
  show perLin D u φ (a F - nn) = _
  rw [this, LinearMap.comp_apply, hιq, hΛ]
  simp

end Formalism.L2.DIV.PerDescent

end
end

noncomputable section

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace Formalism.L2.DIV.RatFullPt

section CSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G] [Fintype G]
  (r : Representation K G S.Forms) (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ)

theorem lvlOp_range (x : Fin (S.lvlDim r P ψ) → K) :
    ∃ F : Fin (S.BaseDimension r X P ψ) → K,
      (S.lvlOp r P ψ (idemOf X)).mulVec x = (S.lvlPr r P ψ * S.V0E r X P ψ).mulVec F := by
  have h1 : (S.lvlE r P ψ).mulVec x ∈ LinearMap.range (S.gaMat r (lvlIdem P ψ)).mulVecLin := by
    rw [← (image_idempotent_spec K S.dim (S.gaMat r (lvlIdem P ψ))).2]
    exact ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := h1
  have h2 : (S.gaMat r (goodAt X P ψ)).mulVec z ∈ LinearMap.range (S.V0E r X P ψ).mulVecLin := by
    have := (image_idempotent_spec K S.dim (S.gaMat r (goodAt X P ψ))).2
    show _ ∈ LinearMap.range (imE (S.gaMat r (goodAt X P ψ))).mulVecLin
    rw [this]
    exact ⟨z, rfl⟩
  obtain ⟨F, hF⟩ := h2
  refine ⟨F, ?_⟩
  rw [Matrix.mulVecLin_apply] at hz hF
  unfold CSD.lvlOp
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hF, ← hz]
  congr 1
  rw [Matrix.mulVec_mulVec, ← (group_action_matrix_hom K S G r).2]
  rfl

end CSD

section Forms

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem range_op_eq_span {n k : ℕ} {σ : K →+* ℂ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {j : (Fin n → K) →ₛₗ[σ] W} {H E : Matrix (Fin n) (Fin n) K} {op : W →ₗ[ℂ] W} (h : FormsTie σ j H E op)
    (V : Matrix (Fin n) (Fin k) K) (h1 : ∀ x, ∃ F, E.mulVec x = V.mulVec F) (h2 : ∀ F, E.mulVec (V.mulVec F) = V.mulVec F) :
    LinearMap.range op = Submodule.span ℂ (Set.range fun F : Fin k → K => j (V.mulVec F)) := by
  apply le_antisymm
  · rw [LinearMap.range_eq_map, ← h.span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    obtain ⟨F, hF⟩ := h1 (Pi.single i 1)
    apply Submodule.subset_span
    exact ⟨F, by rw [h.op_eq, hF]⟩
  · rw [Submodule.span_le]
    rintro _ ⟨F, rfl⟩
    exact LinearMap.mem_range.mpr ⟨j (V.mulVec F), by rw [h.op_eq, h2]⟩

end Forms

structure ColFacts {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc}
    (S : IndefData Df) (C : ColData Dc Sp S) : Prop where
  wf : Df.WF
  h0 : S.H0
  bij : ∀ t, Function.Bijective (S.ι t).mulVec
  l1b : C.PairingFactorsThroughPeriods

theorem ColFacts.rr_lattice {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df}
    {Sp : SPer Dc} {S : IndefData Df} {C : ColData Dc Sp S} (h : ColFacts S C) : Submodule.IsLattice K S.RR := by
  let localLat (t : Bs.Tup) := matLat (S.ι t) (Df.abelian₂ t)
  let M := localLat Bs.μ0 ⊔ ⨆ w : S.Tw, localLat (S.μ w)
  have hfg (t : Bs.Tup) : (localLat t).FG := (h.wf.Lam_lat t).fg.map _
  have hM : M.FG := (hfg Bs.μ0).sup (Submodule.fg_iSup _ fun w => hfg (S.μ w))
  refine Submodule.IsLattice.of_fg K (hM.of_le ?_)
  intro x hx
  refine GluingInclusion.lg (RingOfIntegers.not_isField K) M x fun w => ?_
  change x ∈ glueLat (fun w => localLat (S.μ w)) at hx
  rw [glueLat, Submodule.mem_iInf] at hx
  have hle : localLat (S.μ w) ≤ M := by
    by_cases hw : w ∈ S.Tw
    · exact (le_iSup (fun u : S.Tw => localLat (S.μ u)) ⟨w, hw⟩).trans le_sup_right
    · rw [show S.μ w = Bs.μ0 from not_ne_iff.mp (fun hn => hw ((h.h0.2 w).mpr hn))]
      exact le_sup_left
  exact Formalism.HermitianLatticesTheory.locBasic_locS_mono _ hle (hx w)

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

theorem colFacts_transport {P : RowSideFamily ex} {Z : DefSub P.A3.fam3.amb3} (hZ : Z = P.Zs) {Dc' : DefCols (P.A3.side3 P.Ps P.ψs Z)}
    {Sp' : SPer Dc'} {S' : IndefData (P.A3.side3 P.Ps P.ψs Z)} {C' : ColData Dc' Sp' S'} (hDc : HEq Dc' P.Dc) (hSp : HEq Sp' P.Sp)
    (hS : HEq S' P.S1) (hC : HEq C' P.C) (h : ColFacts S' C') : ColFacts P.S1 P.C := by
  subst hZ
  obtain rfl := eq_of_heq hDc
  obtain rfl := eq_of_heq hSp
  obtain rfl := eq_of_heq hS
  obtain rfl := eq_of_heq hC
  exact h

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Formalism.L2.DIV.RatFullPt

end
