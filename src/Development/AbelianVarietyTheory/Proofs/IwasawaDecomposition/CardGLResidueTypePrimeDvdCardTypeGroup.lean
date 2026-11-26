module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalFunctionMatrixRelation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionEstimateOffCentreCell
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricFrameEqRiemannFormAtInteriorPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardGLResidueTypePrimeDvdCardTypeGroup
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.ZetaSer

theorem coeffRings_contain_rootsOfUnity_of_groupOrder (D : D7) (h : RootsLL D) : GlobalTheory.PendOf.CoeffRingsHaveRootsOfUnity D := by
  obtain ⟨ζ, hζ⟩ := h
  intro i
  have hpos := D.what₂.restRowsFiniteGroupCard_pos
  have hz : IsPrimitiveRoot (D.nd.embK i ζ) D.what₂.restRowsFiniteGroupCard := hζ.map_of_injective (D.nd.embK i).injective
  have hint : IsIntegral (D.nd.O i) (D.nd.embK i ζ) := ⟨Polynomial.X ^ D.what₂.restRowsFiniteGroupCard - Polynomial.C 1,
    Polynomial.monic_X_pow_sub_C 1 hpos.ne', by simp [hz.pow_eq_one]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, ?_⟩
  rw [← hy] at hz
  exact hz.of_map_of_injective (IsFractionRing.injective _ _)

theorem trace_mem_fieldRange {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {L : Type} [Field L] (e : L →+* ℂ) {n : ℕ} (hn : 0 < n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (f : Module.End ℂ V) (hf : f ^ n = 1) : LinearMap.trace ℂ V f ∈ e.fieldRange := by
  classical
  let b := Module.finBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace_eq_sum_roots_charpoly]
  refine multiset_sum_mem _ fun μ hμ => ?_
  have hroot : (LinearMap.charpoly f).IsRoot μ := by
    rw [← LinearMap.charpoly_toMatrix f b]
    exact (Polynomial.mem_roots'.mp hμ).2
  obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).2 hroot).exists_hasEigenvector
  have hpow : μ ^ n = 1 := by
    have h1 := hv.pow_apply n
    rw [hf, Module.End.one_apply] at h1
    have h2 : (μ ^ n - 1) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv.2)
  have hζc := hζ.map_of_injective e.injective
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨j, -, hj⟩ := hζc.eq_pow_of_pow_eq_one hpow
  exact ⟨ζ ^ j, by rw [map_pow, hj]⟩

end GlobalTheory.ZetaSer

namespace GlobalTheory.ZetaSer

theorem card_GL_residue_typePrime_dvd_card_typeGroup (D : D7) (k : Fin 2) :
    Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) ∣ D.what₂.restRowsFiniteGroupCard := by
  rw [D.nd.restN_card_levelGroup_eq]
  have hf : D.R.f ≠ 0 := by
    unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n
    have := Nat.one_le_two_pow (n := D.R.e)
    have := D.R.ord_pos
    omega
  exact (dvd_pow_self _ hf).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))

theorem coeff_zIdem_mem {Γ : Type} [Group Γ] [Fintype Γ] {L : Type} [Field L] (e : L →+* ℂ) {n : ℕ} (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (hΓ : Nat.card Γ ∣ n) (τ : FDRep ℂ Γ) (γ : Γ) :
    (Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ).coeff γ ∈ e.fieldRange := by
  rw [Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff]
  refine mul_mem (div_mem (natCast_mem _ _) (natCast_mem _ _)) (trace_mem_fieldRange e hn hζ _ ?_)
  obtain ⟨c, hc⟩ := hΓ
  rw [← map_pow, hc, pow_mul, pow_card_eq_one', one_pow, map_one]

theorem serLL_of_rootsLL (D : D7) (h : RootsLL D) (G : GrpSide D) : GlobalTheory.PendOf.SerLL D := by
  obtain ⟨ζ, hζ⟩ := h
  intro k f γ
  apply RingHom.mem_fieldRange.mp
  rw [G.eSer_def k f]
  unfold eSerO
  refine finsum_induction (fun x : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) => x.coeff γ ∈ D.what₂.embLL.fieldRange) ?_ ?_ fun z => ?_
  · simp
  · intro x y hx hy
    simpa using add_mem hx hy
  · refine finsum_induction (fun x : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) => x.coeff γ ∈ D.what₂.embLL.fieldRange) ?_ ?_ fun hz => ?_
    · simp
    · intro x y hx hy
      simpa using add_mem hx hy
    · obtain ⟨τ, -, rfl, -⟩ := hz
      exact coeff_zIdem_mem _ D.what₂.restRowsFiniteGroupCard_pos hζ (card_GL_residue_typePrime_dvd_card_typeGroup D k) τ γ

theorem rootsOfUnity_and_seriesIdempotent_rational : ∀ D : D7, RootsLL D → GlobalTheory.PendOf.CoeffRingsHaveRootsOfUnity D ∧ (GrpSide D → GlobalTheory.PendOf.SerLL D) :=
  fun D h => ⟨coeffRings_contain_rootsOfUnity_of_groupOrder D h, serLL_of_rootsLL D h⟩

end GlobalTheory.ZetaSer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatSectionIsFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodsChangeOfEigenFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodsChangeOfEigenFrame
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.Chg

open GlobalTheory.ShFam.OpenReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {i : Fin Fu.n}
  {P : (Fu.Di i).La →+ (Fin g → ℂ)} {y : Sp ℂ ⟶ Xo.XF c}


variable (Z P y) in
def Lifts (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ Z.t.G.left) : Prop :=
  ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
    v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = v ∧
    IsDerivAt0 (fun w => (Fu.ex i P w).left) w (v₀ ≫ Z.m0.toSABMap.φ)

variable (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
  (hy : y ≫ pullback.fst _ _ = Fu.u i P) {x : Sp ℂ ⟶ Z.X} (hx : y ≫ Z.jQ ≫ pullback.fst _ _ = x)

include hP hy hx

theorem exists_dir {v : Sp (DualNumber ℂ) ⟶ Z.t.G.left} (hv : IsTanAtG Z.t x v) : ∃ w, Lifts Z P y w v := by
  obtain ⟨v₀, h1, rfl⟩ := exists_lift Z.m (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [hv.1, ← hx, Category.assoc])
  obtain ⟨w, hw, -⟩ := (isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP).2.2 _
    ((tan_iff Z.m0.toSABMap hy h1).2 ((tan_iff Z.m hx h1).1 hv))
  exact ⟨w, v₀, h1, rfl, hw⟩

theorem eq_sum_of_comb {n : ℕ} {v : Fin n → (Sp (DualNumber ℂ) ⟶ Z.t.G.left)} {W : Fin n → Fin g → ℂ}
    (hW : ∀ k, Lifts Z P y (W k) (v k)) {v' : Sp (DualNumber ℂ) ⟶ Z.t.G.left} {w : Fin g → ℂ} (hw : Lifts Z P y w v')
    {a : Fin n → ℂ} (h : IsCombAtG Z.t x v a v') : w = ∑ k, a k • W k := by
  choose u h1 h2 h3 using hW
  obtain ⟨u', h1', rfl, h3'⟩ := hw
  obtain rfl : v = fun k => u k ≫ Z.m.φ := funext fun k => (h2 k).symm
  have h4 := (comb_iff Z.m0.toSABMap hy h1 a h1').2 ((comb_iff Z.m hx h1 a h1').1 h)
  have h5 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ Fu i P hP n _ W h3 a _).1 h4
  have ht := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  exact (ht.2.2 _ (ht.1 _ _ h3')).unique h3' h5

theorem span_eq_top (f : EigFrame Z σ x) {W : Letter Dw → Fin g → ℂ} (hW : ∀ z, Lifts Z P y (W z) (f.v z.1 z.2)) :
    ⊤ ≤ Submodule.span ℂ (Set.range W) := by
  rw [← (Pi.basisFun ℂ (Fin g)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have ht := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  obtain ⟨v, hv, -⟩ := ht.2.1 (Pi.basisFun ℂ (Fin g) j)
  have he := (isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP _ v (e j).1 hv).2 (fun k hk => by
    obtain rfl : k = j := by
      by_contra hne
      exact hk (by simp [hne])
    rfl)
  have htan := ht.1 _ _ hv
  obtain ⟨v₀, h1, rfl⟩ := exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [htan.1, ← hy, Category.assoc])
  obtain ⟨a, ha, -⟩ := f.basis (e j).1 (v₀ ≫ Z.m.φ) ((tan_iff Z.m hx h1).2 ((tan_iff Z.m0.toSABMap hy h1).1 htan))
    fun a => (eig_iff Z.m h1 a _).2 ((eig_iff Z.m0.toSABMap h1 a _).1 (he a))
  rw [eq_sum_of_comb hP hy hx (W := fun k => W ⟨(e j).1, k⟩) (fun k => hW ⟨_, k⟩) ⟨v₀, h1, rfl, hv⟩ ha]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem linearIndependent (f : EigFrame Z σ x) {W : Letter Dw → Fin g → ℂ}
    (hW : ∀ z, Lifts Z P y (W z) (f.v z.1 z.2)) : LinearIndependent ℂ W :=
  linearIndependent_of_top_le_span_of_card_eq_finrank (span_eq_top hP hy hx f hW)
    (by rw [← Fintype.card_congr e]; simp)

end GlobalTheory.ShFam.Hor.Chg

namespace GlobalTheory.ShFam.Hor

theorem per_chg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a a' : CxFr Z σ) (i : Fin Fu.n) (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)), Per Fu a i Q → a.1 = a'.1 → ∃ Q', Per Fu a' i Q' ∧ ∀ ρ M, Chg a a' ρ M → ∀ v k, Q v ⟨ρ, k⟩ = ∑ j, Q' v ⟨ρ, j⟩ * M j k := by
  rintro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu ⟨x, f⟩ ⟨x', f'⟩ i Q ⟨P, W, y, hP, hy, hyx, hW, hQ⟩ hxx
  obtain rfl : x = x' := hxx
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = x.1 ≫ genι Z := by rw [← Category.assoc, hyx]
  choose W' hW' using fun z : Letter Dw => Chg.exists_dir hP hy hx (f'.tan z.1 z.2)
  let b := Module.Basis.mk (Chg.linearIndependent hP hy hx f' hW') (Chg.span_eq_top hP hy hx f' hW')
  let Q' : (Fu.Di i).La →+ (Letter Dw → ℂ) := b.equivFun.toLinearMap.toAddMonoidHom.comp P
  have hQ' : ∀ v, P v = ∑ z, Q' v z • W' z := fun v => by
    have := b.sum_equivFun (P v)
    simp only [b, Module.Basis.coe_mk] at this
    exact this.symm
  refine ⟨Q', ⟨P, W', y, hP, hy, hyx, hW', hQ'⟩, fun ρ M hM v k => ?_⟩
  choose N hN using fun (τ : E →+* ℂ) j => (f.basis τ _ (f'.tan τ j) (f'.eig τ j)).exists
  have hNM : ∀ j, N ρ j = M j := fun j => (f.basis ρ _ (f'.tan ρ j) (f'.eig ρ j)).unique (hN ρ j) (hM.2 j)
  have hc : ∀ τ j, W' ⟨τ, j⟩ = ∑ k, N τ j k • W ⟨τ, k⟩ := fun τ j =>
    Chg.eq_sum_of_comb hP hy hx (W := fun k => W ⟨τ, k⟩) (fun k => hW ⟨τ, k⟩) (hW' ⟨τ, j⟩) (hN τ j)
  have h1 : ∑ z, Q v z • W z = ∑ z : Letter Dw, (∑ j, Q' v ⟨z.1, j⟩ * N z.1 j z.2) • W z := by
    rw [← hQ, hQ', Fintype.sum_sigma, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [hc, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  have h2 := Fintype.linearIndependent_iffₛ.1 (Chg.linearIndependent hP hy hx f hW) _ _ h1 ⟨ρ, k⟩
  simp only [hNM] at h2
  exact h2

end GlobalTheory.ShFam.Hor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodsChangeOfEigenFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periods_change_of_eigenFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a a' : CxFr Z σ) (i : Fin Fu.n) (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)), Per Fu a i Q → a.1 = a'.1 → ∃ Q', Per Fu a' i Q' ∧ ∀ ρ M, Chg a a' ρ M → ∀ v k, Q v ⟨ρ, k⟩ = ∑ j, Q' v ⟨ρ, j⟩ * M j k := by
  first | exact @GlobalTheory.ShFam.Hor.per_chg | exact GlobalTheory.ShFam.Hor.per_chg | (intros; apply GlobalTheory.ShFam.Hor.per_chg <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

section Lin

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem det_fromRows_mul (A : Matrix m m ℂ) (B : Matrix n n ℂ) (R : Matrix m (m ⊕ n) ℂ) (C : Matrix n (m ⊕ n) ℂ) :
    (Matrix.fromRows (A * R) (B * C)).det = A.det * B.det * (Matrix.fromRows R C).det := by
  rw [← Matrix.det_fromBlocks_zero₂₁ A 0 B, ← Matrix.det_mul, Matrix.fromBlocks_mul_fromRows]
  simp

theorem horVal_change {K : Matrix (m ⊕ n) m ℂ} {C : Matrix n (m ⊕ n) ℂ} {R : Matrix m (m ⊕ n) ℂ}
    {S S' : Matrix (m ⊕ n) n ℂ} (N : Matrix m m ℂ) (M : Matrix n n ℂ) (h : C * K = 0) (hS : C * S = 1)
    (hR : R * (K * N) = 1) (hS' : Mᵀ * C * S' = 1) :
    horVal K C * M.det = horVal (K * N) (Mᵀ * C) * N.det := by
  have h1 : N * R * K = 1 := by
    rw [Matrix.mul_assoc, mul_eq_one_comm, Matrix.mul_assoc]; exact hR
  have h2 : Mᵀ * C * (K * N) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, h]; simp
  have e1 := det_fromRows_mul N 1 R C
  have e2 := det_fromRows_mul 1 Mᵀ R C
  rw [Matrix.one_mul] at e1 e2
  rw [horVal_eq h h1 hS, horVal_eq h2 hR hS', e1, e2]
  simp only [Matrix.det_one, Matrix.det_transpose]
  ring

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem differentiableAt_det {A : V → Matrix m m ℂ} {b : V} (h : ∀ i j, DifferentiableAt ℂ (fun b => A b i j) b) :
    DifferentiableAt ℂ (fun b => (A b).det) b := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun s _ => (differentiableAt_const _).mul ?_
  exact (HasFDerivAt.finsetProd fun i _ => (h _ _).hasFDerivAt).differentiableAt

theorem differentiableAt_horVal {K : V → Matrix (m ⊕ n) m ℂ} {C : V → Matrix n (m ⊕ n) ℂ} {b₀ : V}
    (hK : ∀ i j, DifferentiableAt ℂ (fun b => K b i j) b₀) (hC : ∀ i j, DifferentiableAt ℂ (fun b => C b i j) b₀)
    {R : Matrix m (m ⊕ n) ℂ} (hR : R * K b₀ = 1)
    (h : ∀ᶠ b in 𝓝 b₀, C b * K b = 0 ∧ ∃ S : Matrix (m ⊕ n) n ℂ, C b * S = 1) :
    DifferentiableAt ℂ (fun b => horVal (K b) (C b)) b₀ := by
  have d1 : DifferentiableAt ℂ (fun b => (R * K b).det) b₀ := differentiableAt_det fun i j => by
    simp only [Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun k _ => (differentiableAt_const _).mul (hK _ _)
  have d2 : DifferentiableAt ℂ (fun b => (Matrix.fromRows R (C b)).det) b₀ := differentiableAt_det fun i j => by
    rcases i with i | i
    · exact differentiableAt_const _
    · exact hC i j
  have n1 : (R * K b₀).det ≠ 0 := by rw [hR]; simp
  have d3 : DifferentiableAt ℂ (fun b => (Matrix.fromRows R (C b)).det * ((R * K b).det)⁻¹) b₀ :=
    d2.fun_mul (d1.fun_inv n1)
  refine d3.congr_of_eventuallyEq ?_
  filter_upwards [h, d1.continuousAt.eventually_ne n1] with b ⟨h0, S, hS⟩ hb
  have hu : IsUnit (R * K b).det := hb.isUnit
  have e := det_fromRows_mul (R * K b)⁻¹ 1 R (C b)
  rw [Matrix.one_mul] at e
  rw [horVal_eq h0 (R := (R * K b)⁻¹ * R) (by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu]) hS, e,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Matrix.det_one]
  ring

end Lin

theorem exists_generates {F : Type} [Field F] (Y : GlobalTheory.ProjVar.Var F) (D : Y.Dv) (h : Y.H0 D ≠ ⊥)
    (h' : Y.H0 (-D) ≠ ⊥) : ∃ s, ∀ y, D.GeneratesAt y s := by
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h'
  have hst : s * t ∈ Y.H0 0 := add_neg_cancel D ▸ Y.mul_mem_riemannRochSpace_add _ _ _ _ hs ht
  let L : Y.H0 0 →ₗ[F] Y.H0 0 := (LinearMap.mulLeft F (s * t)).restrict fun g hg =>
    add_zero (0 : Y.Dv) ▸ Y.mul_mem_riemannRochSpace_add _ _ _ _ hst hg
  have hinj : Function.Injective L := fun a b e =>
    Subtype.ext (mul_left_cancel₀ (mul_ne_zero hs0 ht0) (congrArg Subtype.val e))
  letI : FiniteDimensional F (Y.H0 0) := by
    have := finite_coh_of_isProjOver Y.algebraMap_Γ (structureModule Y.X) Y.isProjOver 0
    haveI : Module.Finite F Γ(Y.X, ⊤) := .equiv ((coh.zeroUnitEquiv Y.X).restrictScalars F)
    let f : Γ(Y.X, ⊤) →ₗ[F] Y.Fn := (IsScalarTower.toAlgHom F Γ(Y.X, ⊤) Y.Fn).toLinearMap
    have hf : ∀ a, f a ∈ Y.H0 0 := fun a =>
      GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.2 fun x =>
        CartierDiv.regularAt_zero_iff.2 (regAt_fnOf trivial trivial a)
    apply Module.Finite.of_surjective (f.codRestrict _ hf)
    intro a
    obtain ⟨b, hb⟩ := exists_fnOf_eq (X := Y.X) (U := ⊤) trivial fun x _ =>
      CartierDiv.regularAt_zero_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 a.2 x)
    exact ⟨b, Subtype.ext hb⟩
  obtain ⟨u, hu⟩ := LinearMap.injective_iff_surjective.1 hinj ⟨1, GlobalTheory.ProjVar.Var.eff_iff_one_mem.1 Y.eff_zero⟩
  have hu' : s * t * u = 1 := congrArg Subtype.val hu
  refine ⟨s, fun y => ?_⟩
  obtain ⟨g, hg⟩ := D.exists_isEqn y
  have r1 := hg.regularAt_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 hs y)
  have r2 := hg.neg.regularAt_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 ht y)
  have r3 := CartierDiv.regularAt_zero_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 u.2 y)
  refine hg.generatesAt_iff.2 ((unitAt_iff (mul_ne_zero hs0 g.ne_zero)).2 ⟨r1, ?_⟩)
  have e : (s * (g : Y.Fn))⁻¹ = t * ((g⁻¹ : Y.Fnˣ) : Y.Fn) * u := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← hu', Units.val_inv_eq_inv_val]
    have := g.ne_zero
    field_simp
  exact e ▸ r2.mul r3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {σ : c.F →+* ℂ}
  {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {τ : E →+* ℂ} {x : ∀ i, Idx Dw τ → (Fu.Di i).La}
  {hm : Fin Fu.n → Matrix (Idx Dw τ) (Idx Dw τ) E}

end GlobalTheory.ShFam.Hor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImIntCombinationEqConjMul
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImIntCombinationEqConjMul
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh.Core

theorem hermForm_im_intComb : ∀ (g r r' : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ) (w : Fin r' → Fin g → ℂ) (c : Matrix (Fin r') (Fin r) ℤ) (M : Matrix (Fin r) (Fin r) ℤ), (∀ i, w i = ∑ j, c i j • l j) → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ∀ i j, (hermForm Hm (w i) (w j)).im = ((c * M * cᵀ) i j : ℝ) := by
  intro g r r' Hm l w c M hw hM i j
  rw [hw i, hw j, hermForm_im_sum]
  simp only [hM]
  push_cast [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end GlobalTheory.ShFam.Hor.LogCh.Core
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImIntCombinationEqConjMulStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermForm_im_intCombination_eq_conj_mul : ∀ (g r r' : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ) (w : Fin r' → Fin g → ℂ) (c : Matrix (Fin r') (Fin r) ℤ) (M : Matrix (Fin r) (Fin r) ℤ), (∀ i, w i = ∑ j, c i j • l j) → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ∀ i j, (hermForm Hm (w i) (w j)).im = ((c * M * cᵀ) i j : ℝ) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.Core.hermForm_im_intComb | exact GlobalTheory.ShFam.Hor.LogCh.Core.hermForm_im_intComb | (intros; apply GlobalTheory.ShFam.Hor.LogCh.Core.hermForm_im_intComb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffMatrixMulEqOfSameIntCombinations
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffMatrixMulEqOfSameIntCombinations
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrameFix

theorem coeff_mul_eq_of_same_combinations :
    ∀ (g r r₀ : ℕ) (l l' : Fin r → Fin g → ℂ) (w : Fin r₀ → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ)
      (T : Matrix (Fin r) (Fin r) ℤ), LinearIndependent ℤ l → (∀ i, l' i = ∑ j, T i j • l j) →
      (∀ i, w i = ∑ j, c i j • l j) → (∀ i, w i = ∑ j, c i j • l' j) → c * T = c := by
  intro g r r₀ l l' w c T hl hl' h1 h2
  ext i m
  have key : ∑ j, c i j • l' j = ∑ m, (c * T) i m • l m := by
    simp only [hl', Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    exact Finset.sum_comm
  have hsum : ∑ m, ((c * T) i m - c i m) • l m = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← key, ← h2, h1, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hl (fun m => (c * T) i m - c i m) hsum m)

end GlobalTheory.FrameFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffMatrixMulEqOfSameIntCombinationsStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffMatrix_mul_eq_of_same_intCombinations : ∀ (g r r₀ : ℕ) (l l' : Fin r → Fin g → ℂ) (w : Fin r₀ → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ) (T : Matrix (Fin r) (Fin r) ℤ), LinearIndependent ℤ l → (∀ i, l' i = ∑ j, T i j • l j) → (∀ i, w i = ∑ j, c i j • l j) → (∀ i, w i = ∑ j, c i j • l' j) → c * T = c := by
  first | exact @GlobalTheory.FrameFix.coeff_mul_eq_of_same_combinations | exact GlobalTheory.FrameFix.coeff_mul_eq_of_same_combinations | (intros; apply GlobalTheory.FrameFix.coeff_mul_eq_of_same_combinations <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImIntCombinationDotProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImIntCombinationDotProduct
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ShFam.Hor.LogCh.Core

theorem hermForm_im_intComb_dotProduct : ∀ (g r r₀ : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ) (w : Fin r₀ → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ) (M : Matrix (Fin r) (Fin r) ℤ), (∀ i, w i = ∑ j, c i j • l j) → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ∀ u u' : Fin r₀ → ℤ, (hermForm Hm (∑ i, u i • w i) (∑ j, u' j • w j)).im = (((∑ i, u i • c i) ⬝ᵥ M *ᵥ (∑ i, u' i • c i) : ℤ) : ℝ) := by
  intro g r r₀ Hm l w c M hw hM u u'
  have hre : ∀ v : Fin r₀ → ℤ, ∑ i, v i • w i = ∑ j, (∑ i, v i • c i) j • l j := by
    intro v
    simp only [hw, Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [hre u, hre u', hermForm_im_sum]
  simp only [hM, dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.ShFam.Hor.LogCh.Core
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImIntCombinationDotProductStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermForm_im_intCombination_dotProduct : ∀ (g r r₀ : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ) (w : Fin r₀ → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ) (M : Matrix (Fin r) (Fin r) ℤ), (∀ i, w i = ∑ j, c i j • l j) → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ∀ u u' : Fin r₀ → ℤ, (hermForm Hm (∑ i, u i • w i) (∑ j, u' j • w j)).im = (((∑ i, u i • c i) ⬝ᵥ M *ᵥ (∑ i, u' i • c i) : ℤ) : ℝ) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.Core.hermForm_im_intComb_dotProduct | exact GlobalTheory.ShFam.Hor.LogCh.Core.hermForm_im_intComb_dotProduct | (intros; apply GlobalTheory.ShFam.Hor.LogCh.Core.hermForm_im_intComb_dotProduct <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorRatMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorRatMatrices
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem rat_matrix_common_denom : ∀ (a g : ℕ) (b : Fin a → Matrix (Fin g) (Fin g) ℚ), ∃ (D : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < D ∧ ∀ k i j, (B k i j : ℚ) = D * b k i j := by
  intro a g b
  classical
  let D : ℕ := ∏ k, ∏ i, ∏ j, (b k i j).den
  have hdvd : ∀ k i j, (b k i j).den ∣ D := fun k i j =>
    dvd_trans (Finset.dvd_prod_of_mem (fun j => (b k i j).den) (Finset.mem_univ j))
      (dvd_trans (Finset.dvd_prod_of_mem (fun i => ∏ j, (b k i j).den) (Finset.mem_univ i))
        (Finset.dvd_prod_of_mem (fun k => ∏ i, ∏ j, (b k i j).den) (Finset.mem_univ k)))
  refine ⟨D, fun k i j => ((D / (b k i j).den : ℕ) : ℤ) * (b k i j).num, ?_, ?_⟩
  · exact Finset.prod_pos fun k _ => Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => (b k i j).den_pos
  · intro k i j
    obtain ⟨m, hm⟩ := hdvd k i j
    have hD : D = (b k i j).den * m := hm
    simp only
    rw [hD, Nat.mul_div_cancel_left _ (b k i j).den_pos]
    push_cast
    rw [mul_comm ((b k i j).den : ℚ) (m : ℚ), _root_.mul_assoc, Rat.den_mul_eq_num]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorRatMatricesStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_rat_matrices : ∀ (a g : ℕ) (b : Fin a → Matrix (Fin g) (Fin g) ℚ), ∃ (D : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < D ∧ ∀ k i j, (B k i j : ℚ) = D * b k i j := by
  first | exact @GlobalTheory.rat_matrix_common_denom | exact GlobalTheory.rat_matrix_common_denom | (intros; apply GlobalTheory.rat_matrix_common_denom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongrFunHeq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D)

def Mv.lam (x : GlobalTheory.LamTie.LamDat D) : GlobalTheory.LamTie.LamDat m.D := @_root_.GlobalTheory.LamTie.LamDat.mk (_)
    (C := @_root_.Formalism.L2.Host.CharFrame.mk (_)
      (P := (by with_unfolding_all exact (x.C.P :)))
      (W := (by with_unfolding_all exact (x.C.W :)))
      (mu0 := (by with_unfolding_all exact (x.C.mu0 :)))
      (eta := (by with_unfolding_all exact (x.C.eta :)))
      (chiPsi := (by with_unfolding_all exact (x.C.chiPsi :)))
      (del := (by with_unfolding_all exact (x.C.del :)))
      (del' := (by with_unfolding_all exact (x.C.del' :)))
      (isMu0 := (by with_unfolding_all exact (x.C.isMu0 :)))
      (isEta := (by with_unfolding_all exact (x.C.isEta :)))
      (isChi := (by with_unfolding_all exact (x.C.isChi :)))
      (isDel := (by with_unfolding_all exact (x.C.isDel :)))
      (isDel' := (by with_unfolding_all exact (x.C.isDel' :))))
    (q0 := (by with_unfolding_all exact (x.q0 :)))
    (w0 := (by with_unfolding_all exact (x.w0 :)))
    (c := (by with_unfolding_all exact (x.c :)))
    (chi := (by with_unfolding_all exact (x.chi :)))
theorem Mv.lam_ok {l : GlobalTheory.LamTie.LamDat D} (x : l.Ok) : (m.lam l).Ok := @_root_.GlobalTheory.LamTie.LamDat.Ok.mk (_) (_)
    (places := (by with_unfolding_all exact (x.places :)))
    (aux := (by with_unfolding_all exact (x.aux :)))
    (big := (by with_unfolding_all exact (x.big :)))
theorem Mv.lam_teich {l : GlobalTheory.LamTie.LamDat D} (x : l.Teich) : (m.lam l).Teich := (by with_unfolding_all exact (x :))
theorem Mv.lam_tie {l : GlobalTheory.LamTie.LamDat D} (x : GlobalTheory.LamTie.IsLamTieFull D.ntw l) : GlobalTheory.LamTie.IsLamTieFull m.D.ntw (m.lam l) := (by with_unfolding_all exact (x :))

theorem Mv.rowLoc {D : D7} (m : Mv D) {C : NChoice D} (a : NAllC D C) (F : Formalism.L2.RowFrame D) (F' : Formalism.L2.RowFrame m.D)
    (hF : HEq F'.rep F.rep) (x : Formalism.L2.RowLocTied D a.gal.lp F) : Formalism.L2.RowLocTied m.D (m.all a).gal.lp F' := by
  obtain ⟨rep, inj⟩ := F
  obtain ⟨rep', inj'⟩ := F'
  have e : rep' = (by with_unfolding_all exact (rep :)) := eq_of_heq ((by with_unfolding_all exact (hF :)))
  subst e
  exact (@_root_.Formalism.L2.RowLocTied.mk (_) (_) (_)
    (sat := (by with_unfolding_all exact (x.sat :)))
    )

theorem congrFun_heq {α β : Type} {f g : α → β} (h : HEq f g) (x : α) : f x = g x := by rw [eq_of_heq h]

end GlobalTheory.LayerMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImIntMatrixTransposeNeg
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImIntMatrixTransposeNeg
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem hermForm_swap_of_isHermitian {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (z w : Fin g → ℂ) : hermForm Hm w z = star (hermForm Hm z w) := by
  unfold hermForm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, star_sum, star_mul', Pi.star_apply, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (congrFun hH i) j
  simp only [Matrix.conjTranspose_apply] at h
  rw [← h, star_star]
  ring

theorem hermForm_im_antisymm : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ)
    (M : Matrix (Fin r) (Fin r) ℤ), Hm.IsHermitian →
    (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → Mᵀ = -M := by
  intro g r Hm l M hH hM
  ext i j
  have h1 := hM j i
  rw [hermForm_swap_of_isHermitian Hm hH] at h1
  have h2 := hM i j
  simp only [Complex.star_def, Complex.conj_im] at h1
  have : ((M j i : ℤ) : ℝ) = ((-M i j : ℤ) : ℝ) := by push_cast; linarith
  simpa [Matrix.transpose_apply] using Int.cast_injective this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImIntMatrixTransposeNegStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermForm_im_intMatrix_transpose_neg : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), Hm.IsHermitian → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → Mᵀ = -M := by
  first | exact @GlobalTheory.hermForm_im_antisymm | exact GlobalTheory.hermForm_im_antisymm | (intros; apply GlobalTheory.hermForm_im_antisymm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMarkedFormPiecesRaysOfSimplicialCells
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMarkedFormPiecesRaysOfSimplicialCells
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark

namespace GlobalTheory.PolFan.OrbMark

theorem exists_pieces_match : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)), IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell H.bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, h₀.mem i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (β : LinearMap.BilinForm ℤ X), (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β = 1 →
  ∃ p : Fin m₀ → LinearMap.BilinForm ℤ X, toReal β = ∑ i, t i • toReal (p i) ∧
    (∀ i, 0 < t i → p i ∈ balForms H.bar X ∧ (∀ y, 0 ≤ p i y y) ∧
      (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = p i → k = 1) ∧
      ∀ lab : InvFun (𝓞 E), IsTwInv H lab → lab.evalZ (p i) = lab.evalZ (δ₀ i)) ∧
    ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ δ → LinearIndependent ℤ δ →
      ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
        (∀ i, 0 < t i → ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
        (∀ j, 0 < c j → ∃ i, 0 < t i ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) := by
  intro E _ _ _ H φ hφ X₀ _ _ _ m₀ δ₀ h₀ hind hprim v t hv ht hvt X _ _ _ β hβ
  obtain ⟨τ, f, hτ, hf, hsemi, hrel⟩ := GlobalTheory.T.exists_semilinear_pullback_of_markedOrbitIndicator H.w0 v β hβ
  obtain ⟨u, hsum, hli, hu⟩ := GlobalTheory.T.exists_descended_rays_marked_form_pieces E H δ₀ h₀.mem h₀.nonneg hind hprim v t ht hvt β τ f hτ hf hsemi hrel
  refine ⟨fun i => pullAdd f (u i), hsum, fun i hi => (hu i hi).2, ?_⟩
  intro m δ hδ hδi c hc hβc
  have hA := GlobalTheory.T.marked_form_pieces_in_every_cell_cone E H φ hφ δ₀ h₀ t ht (CarDim.orad v : Submodule (𝓞 E) X₀).mkQ (Submodule.mkQ_surjective _) τ f hτ
    hf hsemi u (fun i hi => ⟨(hu i hi).1, (hu i hi).2.1, (hu i hi).2.2.1⟩) β hsum m δ hδ c hc hβc
  have hB := GlobalTheory.T.cell_ray_in_cone_of_marked_form_pieces E H φ hφ δ₀ h₀ hind v t ht hvt (CarDim.orad v : Submodule (𝓞 E) X₀).mkQ
    (Submodule.mkQ_surjective _) τ f hτ hf hsemi u (fun i hi => (hu i hi).1) β
    (fun x y x₀ y₀ hx hy => hrel x y x₀ y₀ hx hy) m δ hδ c hc hβc
  exact GlobalTheory.T.cone_match_rays_after_dropping_zero_coords (fun i => pullAdd f (u i)) t ht hli β hsum m δ hδi c hc hβc hA hB

end GlobalTheory.PolFan.OrbMark
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMarkedFormPiecesRaysOfSimplicialCellsStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_markedForm_pieces_rays_of_simplicialCells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)), IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell H.bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, h₀.mem i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (β : LinearMap.BilinForm ℤ X), (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β = 1 →
  ∃ p : Fin m₀ → LinearMap.BilinForm ℤ X, toReal β = ∑ i, t i • toReal (p i) ∧
    (∀ i, 0 < t i → p i ∈ balForms H.bar X ∧ (∀ y, 0 ≤ p i y y) ∧
      (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = p i → k = 1) ∧
      ∀ lab : InvFun (𝓞 E), IsTwInv H lab → lab.evalZ (p i) = lab.evalZ (δ₀ i)) ∧
    ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ δ → LinearIndependent ℤ δ →
      ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
        (∀ i, 0 < t i → ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
        (∀ j, 0 < c j → ∃ i, 0 < t i ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) := by
  first | exact @GlobalTheory.PolFan.OrbMark.exists_pieces_match | exact GlobalTheory.PolFan.OrbMark.exists_pieces_match | (intros; apply GlobalTheory.PolFan.OrbMark.exists_pieces_match <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexMatrixEqOfHermFormImEqRealSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexMatrixEqOfHermFormImEqRealSpan
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem hermForm_eq_of_im_eq_on_span : ∀ (g r : ℕ) (Hm Hm' : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ), Submodule.span ℝ (Set.range l) = ⊤ → (∀ i j, (hermForm Hm (l i) (l j)).im = (hermForm Hm' (l i) (l j)).im) → Hm = Hm' := by
  intro g r Hm Hm' l hspan h
  have h1 : ∀ z, ∀ j, (hermForm Hm z (l j)).im = (hermForm Hm' z (l j)).im := by
    intro z j
    have hz : z ∈ Submodule.span ℝ (Set.range l) := hspan ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact h i j
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, add_dotProduct, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul a x _ hx =>
      simp only [hermForm, smul_dotProduct, Complex.smul_im] at hx ⊢
      rw [hx]
  have h2 : ∀ z w, (hermForm Hm z w).im = (hermForm Hm' z w).im := by
    intro z w
    have hw : w ∈ Submodule.span ℝ (Set.range l) := hspan ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact h1 z j
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul a x _ hx =>
      simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im] at hx ⊢
      rw [hx]
  ext i j
  have e1 := h2 (Pi.single i 1) (Pi.single j 1)
  have e2 := h2 (Pi.single i Complex.I) (Pi.single j 1)
  simp [hermForm] at e1 e2
  exact Complex.ext e2 e1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexMatrixEqOfHermFormImEqRealSpanStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexMatrix_eq_of_hermForm_im_eq_real_span : ∀ (g r : ℕ) (Hm Hm' : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ), Submodule.span ℝ (Set.range l) = ⊤ → (∀ i j, (hermForm Hm (l i) (l j)).im = (hermForm Hm' (l i) (l j)).im) → Hm = Hm' := by
  first | exact @GlobalTheory.hermForm_eq_of_im_eq_on_span | exact GlobalTheory.hermForm_eq_of_im_eq_on_span | (intros; apply GlobalTheory.hermForm_eq_of_im_eq_on_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelLatticeOfIsUnf
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open Limits

namespace GlobalTheory.ShFam.Hor.LogCh

theorem kernel_lattice_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (g : ℕ) (x : GlobalTheory.CxPts (genStr Z) σ) (ex : (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)), Inner x → IsExpAt Z.t (x.1 ≫ genι Z) ex → IsHolTo Set.univ (fun w => (ex w).left) → Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) = g ∧ ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ Submodule.span ℝ {w | ex w = 1} = ⊤ ∧ (∀ v w, ex v = 1 → ex w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex v = 1 → ex w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (ex ((k : ℂ)⁻¹ • v)) (ex ((k : ℂ)⁻¹ • w)) (unitOn ζ) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ U _hσ hU g x ex hx hex hhol
  obtain ⟨y, hy⟩ := hx.exists_lift
  obtain ⟨W₀⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c σ _ U hU
  have hs : y ≫ pullback.snd _ _ = spMap σ := by
    rw [← Z.jQ_over, ← Category.assoc, hy]
    exact x.2
  obtain ⟨i, P, hP, hu⟩ := W₀.F.onto (y ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, OpenReg.spMap_comp])
  obtain ⟨e', he', hhol', hker, hweil⟩ := exists_pushed_exp E H Dw l Xo c O β Z _ _ _ W₀.F y i P (x.1 ≫ genι Z) hP hu
    (by rw [← hy, Category.assoc])
  obtain ⟨L, hL⟩ := exp_eq_comp_linearEquiv E H Z.X Z.t (x.1 ≫ genι Z) g _ ex e' hex hhol he' hhol'
  have hg : W₀.g = g := by
    have := L.finrank_eq
    simpa using this
  obtain ⟨Hm₀, hH₀, hpos₀, hEF⟩ := hP.2.2.2.2
  obtain ⟨Hm, hH, hpos, hform⟩ := exists_hermForm_transport _ _ L Hm₀ hH₀ hpos₀
  have hkerex : ∀ w, ex w = 1 ↔ ∃ a, w = L (P a) := by
    intro w
    constructor
    · intro h
      have h' : e' (L.symm w) = 1 := by rw [hL, L.apply_symm_apply, h]
      obtain ⟨a, ha⟩ := (hker _).1 h'
      exact ⟨a, by rw [ha, L.apply_symm_apply]⟩
    · rintro ⟨a, rfl⟩
      rw [← hL]
      exact (hker _).2 ⟨a, rfl⟩
  refine ⟨?_, Hm, hH, hpos, ?_, ?_, ?_⟩
  · rw [← hg, ← Fintype.card_congr W₀.e, Fintype.card_fin]
  · have hset : {w | ex w = 1} = (L.toLinearMap.restrictScalars ℝ) '' Set.range P := by
      ext w
      simp only [Set.mem_setOf_eq, hkerex, Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨P a, ⟨a, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, rfl⟩
    rw [hset, Submodule.span_image, hP.2.2.2.1, Submodule.map_top, LinearMap.range_eq_top]
    exact L.surjective
  · intro v w hv hw
    obtain ⟨a, rfl⟩ := (hkerex v).1 hv
    obtain ⟨b, rfl⟩ := (hkerex w).1 hw
    exact ⟨(W₀.F.Di i).EF a b, by rw [hform, hEF]⟩
  · intro k v w ζ hk hv hw hζ
    obtain ⟨a, rfl⟩ := (hkerex v).1 hv
    obtain ⟨b, rfl⟩ := (hkerex w).1 hw
    rw [← L.map_smul, ← L.map_smul, ← hL, ← hL]
    refine hweil k a b ζ hk ?_
    rw [hζ, hform, hEF, Complex.ofReal_intCast]

end GlobalTheory.ShFam.Hor.LogCh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenSpanInclusionInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EigSpanDesc

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem iotaR_injective_of (R : RealDat3 D A3 Ks) (hM : R.toRealDat.IsModels) (hU : R.toRealDat.LUnif) (i : Fin D.R.m) :
    Function.Injective (iotaR R i) := by
  have hj : Function.Injective ((R.FW i).j (sg0 D A3.A)) := by
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    by_contra hne
    exact ((hU i _).1 1 (fun _ => v) (linearIndependent_unique_iff.2 hne)).ne_zero 0 hv
  exact (hM.HW i _).1.comp hj

end Gen

end GlobalTheory.EigSpanDesc
end
end
