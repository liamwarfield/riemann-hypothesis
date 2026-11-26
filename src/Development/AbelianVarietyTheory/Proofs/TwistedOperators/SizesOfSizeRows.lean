module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumLatticeSameLatticedSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualFullLatticeShared

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowSizes

theorem sizes_of_sizeRows : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D := by
  intro D large₂ h
  obtain ⟨⟨Pm, _, _⟩, _, hmf, hm44, _⟩ := h
  refine ⟨?_, ?_⟩
  · have h1 := D.R.f_le_k
    have h2 : D.R.f = 2 * D.R.ord := rfl
    have h3 : D.R.r = D.R.k + D.R.m - 1 := rfl
    have h4 : 44 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm44 4
    omega
  · intro τ j hj
    have hg := (Pm.nodes_gap τ j hj).1
    have hf := Pm.heightBound_ge_rank_cubic
    have hN : ((GlobalTheory.Grid.bigN D : ℕ) : ℝ) = (D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1) := by
      unfold GlobalTheory.Grid.bigN GlobalTheory.Grid.sLen; push_cast; ring
    have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    have key : ((2 * (GlobalTheory.Grid.bigN D : ℚ) ^ 3 : ℚ) : ℝ) <
        (((D.hc τ).b ⟨j + 1, hj⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) := by
      push_cast at hg ⊢
      rw [hN]
      linarith
    exact_mod_cast key

end GlobalTheory.RowSizes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchActOne
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord
open scoped Matrix Classical

namespace GlobalTheory.ArchLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}


open Classical in
def archOp (om : Rep σ X W) (h : UA σ W.J) (f : SInf F (Fin n × Fin d)) : SInf F (Fin n × Fin d) :=
  if hx : ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) ⇑f ⇑f₁ then hx.choose else 0

def archAct (M : Model σ X W) (h : UA σ W.J)
    (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  coordI M (actAB (cA σ) ((1 : UA σ X.J), h) (M.co.e.symm (liftV v.1, liftV v.2)))

theorem acts_archOp (om : Rep σ X W) (h : UA σ W.J) (f : SInf F (Fin n × Fin d))
    (hx : ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) ⇑f ⇑f₁) :
    Acts (evI F) (om (1, h)) ⇑f ⇑(archOp om h f) := by
  classical
  unfold archOp
  rw [dite_eq_left hx]
  exact hx.choose_spec

theorem archAct_one (M : Model σ X W)
    (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    archAct M 1 v = v := by
  unfold archAct
  simp [actAB, coordI_lift]

end GlobalTheory.ArchLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunTransportS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLift

open GlobalTheory.GridJoin

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

structure RowMatchS (ch : Choice R) (G' : GlobalTheory.Grid.GridPre R) : Prop where

  V : ∀ i, i ≤ D.R.m → SameSp (ch.G.V (.grid i 0)) (G'.V i 0).V

  ν : ∀ i, i ≤ D.R.m → HEq (G'.measCol i).ν (ch.M.ν (.grid i 0))

  fd : ∀ i, i ≤ D.R.m → HEq (G'.measCol i).fd (ch.M.fd (.grid i 0))

  ker : ∀ (ρ : ch.G.RealVec) (Φ : ch.G.Datum) (i : Fin D.R.m), ∃ f,
    GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G'.V ((i : ℕ) + 1) 0) (G'.V i 0) f ∧ ∃ p,
      HEq (fun h g => thetaKO (G'.X i 0).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G'.V ((i : ℕ) + 1) 0) (G'.V i 0) f p))
        (fun h g => ch.W.kerA (.right (i : ℕ) 0) (ch.W.datum ρ Φ i) g h)

theorem transport_stepS {A A' B B' : HSp D} (eA : SameSp A' A) (eB : SameSp B' B)
    {ν : Measure (GA D A)} {fd : Set (GA D A)} {ν' : Measure (GA D A')} {fd' : Set (GA D A')}
    (hν : HEq ν ν') (hfd : HEq fd fd') {K : GA D B → GA D A → ℂ} {K' : GA D A' → GA D B' → ℂ}
    (hK : HEq K (fun h g => K' g h)) {φ : GA D A → ℂ} {φ' : GA D A' → ℂ} (hφ : HEq φ φ') {ψ : GA D B → ℂ}
    (hI : ∀ h, IntegrableOn (fun g => K h g * φ g) fd ν) (hE : ∀ h, ∫ g in fd, K h g * φ g ∂ν = ψ h) :
    (∀ h, IntegrableOn (fun g => K' g h * φ' g) fd' ν') ∧ HEq ψ (fun h => ∫ g in fd', K' g h * φ' g ∂ν') := by
  obtain ⟨L, h1, h2, rfl⟩ := eA
  obtain ⟨L', h1', h2', rfl⟩ := eB
  obtain rfl := eq_of_heq hν
  obtain rfl := eq_of_heq hfd
  obtain rfl := eq_of_heq hφ
  obtain rfl := eq_of_heq hK
  exact ⟨hI, heq_of_eq (funext hE).symm⟩

theorem isAutFun_transportS {V V' : HSp D} (e : SameSp V' V) {φ : GA D V → ℂ} {φ' : GA D V' → ℂ} (h : HEq φ φ')
    (hφ : IsAutFun V φ) : IsAutFun V' φ' := by
  obtain ⟨L, h1, h2, rfl⟩ := e
  obtain rfl := eq_of_heq h
  exact ⟨hφ.left, hφ.level, hφ.cont⟩

end GlobalTheory.RowLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalf
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceCoord

theorem isOpen_isCompact_of_comm {K : Type} [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K]
    {m n : ℕ} (O : AddSubgroup K) (ho : IsOpen (O : Set K)) (hc : IsCompact (O : Set K))
    (A : AddSubgroup (Matrix (Fin m) (Fin n) K)) {k M : ℕ} (hk : 0 < k) (hM : 0 < M)
    (h1 : ∀ y : Matrix (Fin m) (Fin n) K, (∀ i j, y i j ∈ O) → k • y ∈ A)
    (h2 : ∀ y ∈ A, ∀ i j, (M : K) * y i j ∈ O) :
    IsOpen (A : Set (Matrix (Fin m) (Fin n) K)) ∧ IsCompact (A : Set (Matrix (Fin m) (Fin n) K)) := by
  have hk' : (k : K) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hM' : (M : K) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hU : IsOpen {y : Matrix (Fin m) (Fin n) K | ∀ i j, (k : K)⁻¹ * y i j ∈ O} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      ho.preimage (f := fun y : Matrix (Fin m) (Fin n) K => (k : K)⁻¹ * y i j) (by fun_prop)
  have hA : IsOpen (A : Set (Matrix (Fin m) (Fin n) K)) := by
    refine A.isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset (hU.mem_nhds fun i j => by simp) fun y hy => ?_)
    have := h1 ((k : K)⁻¹ • y) hy
    rwa [← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ hk', one_smul] at this
  refine ⟨hA, ?_⟩
  have hC : IsCompact (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin n => (fun x => (M : K)⁻¹ * x) '' O) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc.image (by fun_prop)
  refine IsCompact.of_isClosed_subset (s := Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin n => (fun x => (M : K)⁻¹ * x) '' O) hC (A.isClosed_of_isOpen hA) fun y hy i _ j _ => ⟨_, h2 y hy i j, ?_⟩
  simp only [inv_mul_cancel_left₀ hM']

def mulHomeo {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {m n : ℕ} (P : GL (Fin m) K)
    (Q : GL (Fin n) K) : Matrix (Fin m) (Fin n) K ≃ₜ Matrix (Fin m) (Fin n) K where
  toFun x := P.val * x * Q.val
  invFun x := (P⁻¹).val * x * (Q⁻¹).val
  left_inv x := by
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv x := by
    simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

variable {D : D7}

theorem toEAf_mem {w : AE D} (hw : finPart D w ∈ intAE D) : toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have key : ∀ z ∈ intAE D, Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E z ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, rfl⟩ := hz
      exact GlobalTheory.PlaceDatum.tmul_mem_int ⟨x, rfl⟩ ha
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  exact key _ hw

variable {v : FinPl D} {S T : HSp D} {e : AE D} {π : AE D →+* Fv D.host.F v}

theorem exists_half (hπ : GlobalTheory.SplitHecke.Chart e v π) (he : e * e = e) (h1 : π e = 1)
    (y : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) : ∃ t : WO S T, IsHalf e t ∧ t.map π = y := by
  choose s hs using hπ.1
  refine ⟨Matrix.of fun i j => e * s (y i j), fun i j => ?_, Matrix.ext fun i j => ?_⟩
  · rw [Matrix.of_apply, ← mul_assoc, he]
  · rw [Matrix.map_apply, Matrix.of_apply, RingHom.map_mul, h1, one_mul, hs]

theorem bijOn_map (hπ : GlobalTheory.SplitHecke.Chart e v π) (he : e * e = e) (h1 : π e = 1) :
    Set.BijOn (fun t : WO S T => t.map π) {t | IsHalf e t} Set.univ := by
  refine ⟨Set.mapsTo_univ _ _, fun x hx y hy h => Matrix.ext fun i j => ?_, fun y _ => exists_half hπ he h1 y⟩
  have h0 : π (x i j - y i j) = 0 := by
    rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun h i) j
  rw [hπ.2.1, mul_sub, hx i j, hy i j, sub_eq_zero] at h0
  exact h0

private theorem selfDual_full {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : Submodule.IsFullLattice D.host.E Λ := _root_.DedupShared.selfDual_isFullLattice V Λ hΛ

theorem isOpen_isCompact_map {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) (hπ : GlobalTheory.SplitHecke.Chart e v π) (he : e * e = e) (h1 : π e = 1)
    (hinf : infPart D e = 0) :
    IsOpen ((fun t : WO S T => t.map π) '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf e t}) ∧
    IsCompact ((fun t : WO S T => t.map π) '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf e t}) := by
  have : CharZero (Fv D.host.F v) := charZero_of_injective_algebraMap (algebraMap D.host.F _).injective
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.1.fg hT.1.fg
  obtain ⟨k, hk, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) (selfDual_full S ΛS hS) (selfDual_full T ΛT hT)
  have hset : ((fun t : WO S T => t.map π) '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf e t}) =
      (((latO S T ΛS ΛT fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T e).map π.toAddMonoidHom.mapMatrix :
        AddSubgroup (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v))) := by
    rw [AddSubgroup.coe_map]
    congr 1
    ext t
    exact and_congr_right fun _ => GlobalTheory.PlaceModel.isHalf_iff S T
  rw [hset]
  refine isOpen_isCompact_of_comm (v.adicCompletionIntegers D.host.F).toSubring.toAddSubgroup
    (Valued.isOpen_valuationSubring _) (isCompact_iff_compactSpace.2 (Formalism.L2.Col.rlt_compact_int v)) _ hk hM
    (fun y hy => ?_) ?_
  · obtain ⟨t, ht, rfl⟩ := exists_half hπ he h1 y
    refine ⟨k • t, ⟨hmul t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht) fun i j => toEAf_mem ?_,
      nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 ht) k⟩, map_nsmul _ _ _⟩
    rw [← ht i j]
    exact (hπ.2.2.2 _).2 (GlobalTheory.SplitHecke.isInt_Ov.2 (hy i j))
  · rintro _ ⟨t, ⟨ht, ht'⟩, rfl⟩ i j
    have h2 : toEAf D ((M : AE D) * t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [RingHom.map_mul, map_natCast]; exact hden t ht i j
    have h3 : finPart D (e * ((M : AE D) * t i j)) ∈ intAE D := by
      rw [mul_left_comm, (GlobalTheory.PlaceModel.isHalf_iff S T).2 ht' i j]
      exact GlobalTheory.PlaceDatum.finPart_mem_of_toEAf h2
    have h4 := GlobalTheory.SplitHecke.isInt_Ov.1 ((hπ.2.2.2 _).1 h3)
    rw [RingHom.map_mul, map_natCast] at h4
    exact h4

theorem infPart_split (he : IsSplitIdem D e) : infPart D e = 0 := by
  obtain ⟨a1, a2, v, ε, ⟨β, rfl, -⟩, a3⟩ := he
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) = 0 := TensorProduct.zero_tmul _ _
  have hi' : e * (e + cA D e) = e := by rw [mul_add, a1, a2, add_zero]
  rw [← hi', a3, RingHom.map_mul, h0, mul_zero]

theorem isCoord_mapCo : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)), IsCoord e (latO S T ΛS ΛT fun _ => True) (mapCo φ S T BS BT) ∧ ∀ (g : GA D S) (h : GA D T) (t : WO S T), mapCo φ S T BS BT (actO S T g⁻¹ h⁻¹ t) = ((grpCo φ T BT h)⁻¹).val * mapCo φ S T BS BT t * (grpCo φ S BS g).val := by
  intro D S T ΛS ΛT hS hT v φ e he BS BT
  have hπ := (GlobalTheory.T.splitProjAdeleComponent_chart_properties D v φ e he).1
  have hcomp : mapCo φ S T BS BT = mulHomeo BT⁻¹ BS ∘ fun t : WO S T => t.map (rdA φ) := rfl
  have hoc := isOpen_isCompact_map (S := S) (T := T) hS hT hπ he.1.1 he.2.2 (infPart_split he.1)
  refine ⟨⟨fun x y => ?_, ?_, ?_, ?_⟩, fun g h t => ?_⟩
  · unfold mapCo
    rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]
  · rw [hcomp]
    exact (Set.bijOn_univ.2 (mulHomeo BT⁻¹ BS).bijective).comp (bijOn_map hπ he.1.1 he.2.2)
  · rw [hcomp, Set.image_comp]
    exact (mulHomeo BT⁻¹ BS).isOpenMap _ hoc.1
  · rw [hcomp, Set.image_comp]
    exact hoc.2.image (mulHomeo BT⁻¹ BS).continuous
  · have e1 : ((grpCo φ T BT h)⁻¹).val = (BT⁻¹).val * (mt T h⁻¹).map (rdA φ) * BT.val := by
      have : (grpCo φ T BT h)⁻¹ = grpCo φ T BT h⁻¹ := by
        unfold grpCo
        rw [map_inv, map_inv, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, mul_assoc]
      rw [this]; rfl
    have e2 : (grpCo φ S BS g).val = (BS⁻¹).val * (mt S g).map (rdA φ) * BS.val := rfl
    rw [e1, e2]
    unfold mapCo actO
    rw [inv_inv, Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
    rw [← Matrix.mul_assoc BT.val, Units.mul_inv, Matrix.one_mul]

end GlobalTheory.PlaceCoord

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalfStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_matrix_coordinate_on_half : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)), IsCoord e (latO S T ΛS ΛT fun _ => True) (mapCo φ S T BS BT) ∧ ∀ (g : GA D S) (h : GA D T) (t : WO S T), mapCo φ S T BS BT (actO S T g⁻¹ h⁻¹ t) = ((grpCo φ T BT h)⁻¹).val * mapCo φ S T BS BT t * (grpCo φ S BS g).val := by
  first | exact @GlobalTheory.PlaceCoord.isCoord_mapCo | exact GlobalTheory.PlaceCoord.isCoord_mapCo | (intros; apply GlobalTheory.PlaceCoord.isCoord_mapCo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRational
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRational
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitaryEmbeddingProperties

def ex {R : Type} [CommRing R] {n r : ℕ} (P : Matrix (Fin n) (Fin r) R) (Q : Matrix (Fin r) (Fin n) R)
    (h : Matrix (Fin r) (Fin r) R) : Matrix (Fin n) (Fin n) R :=
  1 + P * (h - 1) * Q

section Gen

variable {R : Type} [CommRing R] {n r : ℕ} (P : Matrix (Fin n) (Fin r) R) (Q : Matrix (Fin r) (Fin n) R)

theorem ex_mul_P (hQP : Q * P = 1) (h : Matrix (Fin r) (Fin r) R) : ex P Q h * P = P * h := by
  rw [ex, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hQP, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one,
    add_sub_cancel]

theorem ex_mul_N (hQP : Q * P = 1) (h : Matrix (Fin r) (Fin r) R) : ex P Q h * (1 - P * Q) = 1 - P * Q := by
  have e : Q * (1 - P * Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hQP, Matrix.one_mul, sub_self]
  rw [ex, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc (P * (h - 1)), e, Matrix.mul_zero, add_zero]

theorem ex_mul (hQP : Q * P = 1) (a b : Matrix (Fin r) (Fin r) R) : ex P Q (a * b) = ex P Q a * ex P Q b := by
  have e3 : P * (a - 1) * Q * (P * (b - 1) * Q) = P * ((a - 1) * (b - 1)) * Q := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
  have e4 : a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) := by noncomm_ring
  rw [ex, ex, ex, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, e3, e4]
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel

theorem ex_one : ex P Q 1 = 1 := by simp [ex]

theorem ex_map {R' : Type} [CommRing R'] (φ : R →+* R') (h : Matrix (Fin r) (Fin r) R) :
    (ex P Q h).map φ = ex (P.map φ) (Q.map φ) (h.map φ) := by
  simp only [ex, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_sub _ (map_sub φ),
    Matrix.map_one _ (map_zero φ) (map_one φ)]

end Gen

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}

def qM (d : HermitianOrthogonalExtensionData A B c ε) : Matrix (Fin A.rank) (Fin B.rank) D.host.E :=
  A.gram⁻¹ * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι) * B.gram)

theorem qM_mul (d : HermitianOrthogonalExtensionData A B c ε) : qM d * frameMat B A d.ι = 1 := by
  rw [qM, Matrix.mul_assoc, GlobalTheory.AutFunCounterexample.gram_pull B A d.ι d.isom,
    Matrix.nonsing_inv_mul _ (GlobalTheory.AutFunCounterexample.gram_det_ne A).isUnit]

theorem qM_mul_map {R : Type} [CommRing R] (φ : D.host.E →+* R) (d : HermitianOrthogonalExtensionData A B c ε) :
    (qM d).map φ * (frameMat B A d.ι).map φ = 1 := by
  rw [← Matrix.map_mul, qM_mul, Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem unitaryEmbedding_matrix_formula (d : HermitianOrthogonalExtensionData A B c ε) (h : GA D A) :
    (matHom B (stabilizerEmbedding d h)).1 = ex ((frameMat B A d.ι).map (incA D)) ((qM d).map (incA D)) (matHom A h).1 := by
  have hr := (embRel_iff d h _).2 rfl
  set P := frameMat B A d.ι
  set C := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P * B.gram
  have hG : C * P = A.gram := GlobalTheory.AutFunCounterexample.gram_pull B A d.ι d.isom
  set N : Matrix (Fin B.rank) (Fin B.rank) D.host.E := 1 - P * qM d with hN
  have hC : C * N = 0 := by
    rw [hN, qM, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hG,
      Matrix.mul_nonsing_inv _ (GlobalTheory.AutFunCounterexample.gram_det_ne A).isUnit, Matrix.one_mul, sub_self]
  have h1 : (matHom B (stabilizerEmbedding d h)).1 * N.map (incA D) = N.map (incA D) := by
    ext i j
    exact congr_fun (hr.2 (fun k => N k j) (by funext k; exact congr_fun (congr_fun hC k) j)) i
  have hNm : N.map (incA D) = (1 : Matrix (Fin B.rank) (Fin B.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) -
      HMul.hMul (P.map (incA D)) ((qM d).map (incA D)) := by
    rw [hN, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  refine GlobalTheory.AutFunCounterexample.split_gen (incA D) P (qM d) _ _ ?_ ?_
  · rw [h1, hNm, ex_mul_N _ _ (qM_mul_map _ d)]
  · rw [hr.1, ex_mul_P _ _ (qM_mul_map _ d)]

theorem unitaryEmbedding_mul (d : HermitianOrthogonalExtensionData A B c ε) (g h : GA D A) : stabilizerEmbedding d (g * h) = stabilizerEmbedding d g * stabilizerEmbedding d h := by
  apply GlobalTheory.AutFunCounterexample.GA_ext
  rw [map_mul, Units.val_mul, unitaryEmbedding_matrix_formula, unitaryEmbedding_matrix_formula, unitaryEmbedding_matrix_formula, map_mul, Units.val_mul,
    ex_mul _ _ (qM_mul_map _ d)]

theorem unitaryEmbedding_rational (d : HermitianOrthogonalExtensionData A B c ε) (γ : GA D A) (hγ : γ ∈ GQ A) : stabilizerEmbedding d γ ∈ GQ B := by
  obtain ⟨γE, hγE, e⟩ := Subgroup.mem_subgroupOf.1 hγ
  have q2 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι) * B.gram = A.gram * qM d := by
    rw [qM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.AutFunCounterexample.gram_det_ne A).isUnit, Matrix.one_mul]
  set P := frameMat B A d.ι
  set Q := qM d
  have q3 : Q * P = 1 := qM_mul d
  have q1 : B.gram * P = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Q * A.gram := by
    have := congrArg (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)) q2
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, GlobalTheory.AutFunCounterexample.gram_herm, GlobalTheory.AutFunCounterexample.cT_cT,
      GlobalTheory.AutFunCounterexample.gram_herm] at this
  let γ' : GL (Fin B.rank) D.host.E := ⟨ex P Q γE, ex P Q (γE⁻¹ : GL (Fin A.rank) D.host.E),
    by rw [← ex_mul _ _ q3, Units.mul_inv, ex_one], by rw [← ex_mul _ _ q3, Units.inv_mul, ex_one]⟩
  have hu : γ' ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) B.gram :=
    GlobalTheory.AutFunCounterexample.ext_unitary _ B.gram A.gram P Q q1 q2 q3 _ hγE
  refine Subgroup.mem_subgroupOf.2 ⟨γ', hu, Units.ext ?_⟩
  have hA : (matHom A γ).1 = (γE : Matrix (Fin A.rank) (Fin A.rank) D.host.E).map (incA D) := by
    exact (congrArg Units.val e).symm
  show (ex P Q γE).map (incA D) = (matHom B (stabilizerEmbedding d γ)).1
  rw [unitaryEmbedding_matrix_formula, hA, ex_map]


set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_unitaryEmbedding (d : HermitianOrthogonalExtensionData A B c ε) : Continuous (stabilizerEmbedding d) := by
  haveI : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have hf : ∀ {f : GA D A → Matrix (Fin A.rank) (Fin A.rank) (AF D.host.F ⊗[D.host.F] D.host.E)}, Continuous f →
      Continuous fun h => ex ((frameMat B A d.ι).map (incA D)) ((qM d).map (incA D)) (f h) := fun hc =>
    continuous_const.add ((continuous_const.matrix_mul (hc.sub continuous_const)).matrix_mul continuous_const)
  have hv : Continuous fun h : GA D A => (matHom A h).1 :=
    Units.continuous_val.comp continuous_subtype_val
  have hi : Continuous fun h : GA D A => (matHom A h⁻¹).1 :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  let φ : GA D A →* GA D B := MonoidHom.mk' (stabilizerEmbedding d) (unitaryEmbedding_mul d)
  have hc : Continuous fun h => matHom B (stabilizerEmbedding d h) := by
    refine Units.continuous_iff.2 ⟨(hf hv).congr fun h => (unitaryEmbedding_matrix_formula d h).symm, (hf hi).congr fun h => ?_⟩
    have e : (stabilizerEmbedding d h)⁻¹ = stabilizerEmbedding d h⁻¹ := (map_inv φ h).symm
    rw [← map_inv (matHom B), e, unitaryEmbedding_matrix_formula]
  exact Continuous.subtype_mk (p := fun g => g ∈ HR (AF D.host.F) D.sp.cm.sig B.gram) hc fun h => (stabilizerEmbedding d h).2

theorem unitaryEmbedding_continuous_hom_rational : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε), Continuous (stabilizerEmbedding d) ∧
    (∀ g h, stabilizerEmbedding d (g * h) = stabilizerEmbedding d g * stabilizerEmbedding d h) ∧ ∀ γ ∈ GQ A, stabilizerEmbedding d γ ∈ GQ B :=
  fun d => ⟨continuous_unitaryEmbedding d, unitaryEmbedding_mul d, unitaryEmbedding_rational d⟩

end GlobalTheory.UnitaryEmbeddingProperties
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRationalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryEmbedding_continuous_mul_rational : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε), Continuous (stabilizerEmbedding d) ∧
    (∀ g h, stabilizerEmbedding d (g * h) = stabilizerEmbedding d g * stabilizerEmbedding d h) ∧ ∀ γ ∈ GQ A, stabilizerEmbedding d γ ∈ GQ B := by
  first | exact @GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_continuous_hom_rational | exact GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_continuous_hom_rational | (intros; apply GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_continuous_hom_rational <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskyGrothendieckPolynomialRingOfSegments
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskyGrothendieckPolynomialRingOfSegments
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory

theorem zelevinskyPolynomialRing_of_parts :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.SegmentRepresentation →
      GlobalTheory.Published.GrothendieckRingPolynomial → GlobalTheory.Published.ZelevinskyPolynomialRing := by
  intro hBZ hSeg hRing k _ _ _ _
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.zelevinskySegmentClass_exists_for_every_placing hSeg k
  obtain ⟨Ψ, h1, hmul, hX⟩ := hRing k Z hZ
  refine ⟨Z, Ψ, hZ, ⟨h1, fun r t V W _ _ _ _ π₁ π₂ h₁ h₂ s₁ s₂ => ?_⟩, hX⟩
  have h := GlobalTheory.T.parabolicProduct_hasFiniteLength_GL hBZ k r t V W π₁ π₂ h₁ h₂ s₁ s₂
  exact ⟨h, hmul r t V W π₁ π₂ h₁ h₂ s₁ s₂ h⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskyGrothendieckPolynomialRingOfSegmentsStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
theorem _root_.GlobalTheory.T.zelevinskyGrothendieckPolynomialRing_of_segments : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.SegmentRepresentation → GlobalTheory.Published.GrothendieckRingPolynomial → GlobalTheory.Published.ZelevinskyPolynomialRing := by
  first | exact @GlobalTheory.zelevinskyPolynomialRing_of_parts | exact GlobalTheory.zelevinskyPolynomialRing_of_parts | (intros; apply GlobalTheory.zelevinskyPolynomialRing_of_parts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjIdempotentConjFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjIdempotentConjFixed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemConjSum

theorem idemSum_add_conj_idem : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z →
    (e + cA D e) * (e + cA D e) = e + cA D e ∧ cA D (e + cA D e) = e + cA D e := by
  intro D Z e he
  have h1 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have h2 : e * cA D e = 0 := he.2
  have h3 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  refine ⟨?_, ?_⟩
  · have h4 : cA D e * e = 0 := by rw [mul_comm]; exact h2
    calc (e + cA D e) * (e + cA D e) = e * e + e * cA D e + cA D e * e + cA D e * cA D e := by ring
      _ = e + cA D e := by rw [h1, h2, h4, h3]; ring
  · rw [map_add (f := _), cA_cA, add_comm]

end GlobalTheory.IdemConjSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjIdempotentConjFixedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentSum_add_conj_idempotent_conj_fixed : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → (e + cA D e) * (e + cA D e) = e + cA D e ∧ cA D (e + cA D e) = e + cA D e := by
  first | exact @GlobalTheory.IdemConjSum.idemSum_add_conj_idem | exact GlobalTheory.IdemConjSum.idemSum_add_conj_idem | (intros; apply GlobalTheory.IdemConjSum.idemSum_add_conj_idem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersRealPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersRealPlaces
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

namespace GlobalTheory.VacuumCharacter

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem signBlockDeterminant_diagonalPhases_zpow {n : ℕ} (ε : Fin n → Bool) (t : Fin n → ℝ) (x : Bool → ℤ) :
    signBlockDeterminant ε true (diagonal fun j => Complex.exp (Complex.I * t j)) ^ x true *
      signBlockDeterminant ε false (diagonal fun j => Complex.exp (Complex.I * t j)) ^ x false =
      Complex.exp (Complex.I * ∑ j, (x (ε j) : ℂ) * t j) := by
  have key : ∀ e : Bool, signBlockDeterminant ε e (diagonal fun j => Complex.exp (Complex.I * t j)) ^ x e =
      Complex.exp (Complex.I * ∑ j ∈ Finset.univ.filter (fun j => ε j = e), (x e : ℂ) * t j) := by
    intro e
    rw [signBlockDeterminant, submatrix_diagonal _ _ Subtype.val_injective, det_diagonal]
    simp only [Function.comp_apply]
    rw [← Complex.exp_sum,
      ← Complex.exp_int_mul,
      Finset.sum_subtype (Finset.univ.filter fun j => ε j = e) (p := fun j => ε j = e) (by simp)]
    congr 1
    try simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [key, key, ← Complex.exp_add, ← mul_add,
    ← Finset.sum_fiberwise (M := ℂ) (s := (Finset.univ : Finset (Fin n))) (g := ε)
      (f := fun j : Fin n => (x (ε j) : ℂ) * (t j : ℂ)), Fintype.sum_bool]
  congr 3 <;> refine Finset.sum_congr rfl fun j hj => ?_ <;> rw [(Finset.mem_filter.1 hj).2]

theorem diag_mem_Kset {n : ℕ} (ε : Fin n → Bool) (t : Fin n → ℝ) :
    (diagonal fun j => Complex.exp (Complex.I * t j)) ∈ Formalism.REAL.Kset ε := by
  have hu : ∀ j, star (Complex.exp (Complex.I * t j)) * Complex.exp (Complex.I * t j) = 1 := by
    intro j
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  simp only [Formalism.REAL.Kset, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext j
    exact hu j
  · rw [Formalism.REAL.Jm, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext j
    ring

theorem torusVac_of_compactFock {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ)
    (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S') (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ) (h : CompactFock ψ θ M M' ω f τ aS aT) :
    TorusVac θ M M' ω f τ aS aT := by
  obtain ⟨x, y, hx, hy, hK⟩ := h
  intro t t'
  have hact := hK _ (diag_mem_Kset (M.ε τ) t) _ (diag_mem_Kset (M'.ε τ) t') 1
  rw [map_one, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.ptOf_one] at hact
  rw [hact, signBlockDeterminant_diagonalPhases_zpow, signBlockDeterminant_diagonalPhases_zpow, ← Complex.exp_add, ← mul_add]
  have hx' : ∀ j, ((x (M.ε τ j) : ℤ) : ℂ) = ((wtS (M'.ε τ) aT (M.ε τ j) : ℚ) : ℂ) := fun j => by
    rw [← hx j]; push_cast; rfl
  have hy' : ∀ i, ((y (M'.ε τ i) : ℤ) : ℂ) = ((wtT (M.ε τ) aS (M'.ε τ i) : ℚ) : ℂ) := fun i => by
    rw [← hy i]; push_cast; rfl
  simp only [hx', hy']

theorem vacChar : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D := by
  intro D V W S S' M M' θ ψ χS χT ω f τ aS aT hθ hW hS hT hV
  have hF := GlobalTheory.ChainFr.isVacF_of_isVacVec hV
  have hK := GlobalTheory.T.compact_subgroups_act_on_fock_vectors_all_signatures D V W (GlobalTheory.ChainFr.Fr.ofModel M) (GlobalTheory.ChainFr.Fr.ofModel M') θ ψ χS χT ω f τ aS aT
    hθ hW hS hT hF hV.ne
  have hL := GlobalTheory.T.lieAction_fockOperators_scalars_trace D V W (GlobalTheory.ChainFr.Fr.ofModel M) (GlobalTheory.ChainFr.Fr.ofModel M') θ ψ χS χT ω f τ aS aT
    hθ hW hS hT hF
  have hC : CompactFock ψ θ M M' ω f τ aS aT := by
    obtain ⟨x, y, hx, hy, hk⟩ := hK
    refine ⟨x, y, hx, hy, fun g hg k hk' P => ?_⟩
    have e := hk g hg k hk' P
    rwa [GlobalTheory.ChainFr.ptF_ofModel] at e
  refine ⟨torusVac_of_compactFock ψ θ M M' ω f τ aS aT hC, hC, ?_, ?_⟩
  · intro X hX P z
    have e := hL.1 X hX P z
    rw [GlobalTheory.ChainFr.ptF_ofModel] at e
    rw [sub_eq_add_neg, ← neg_smul]
    exact e
  · intro Y hY P z
    have e := hL.2 Y hY P z
    rw [GlobalTheory.ChainFr.ptF_ofModel] at e
    exact e

end GlobalTheory.VacuumCharacter

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersRealPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaVacuumCharacters_realPlaces : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D := by
  first | exact @GlobalTheory.VacuumCharacter.vacChar | exact GlobalTheory.VacuumCharacter.vacChar | (intros; apply GlobalTheory.VacuumCharacter.vacChar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFiniteDatumVectorThetaFockVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFiniteDatumVectorThetaFockVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockRealVec

theorem compAt_central {D : D7} {θ : InfFam D} (τ : D.what₂.Tau) {n : ℕ} (c : AE D) :
    ∃ s : ℂ, compAt θ τ (c • (1 : Matrix (Fin n) (Fin n) (AE D))) = s • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  refine ⟨θ τ (infPart D c), ?_⟩
  ext i j
  by_cases h : i = j
  · subst h; simp [compAt]
  · simp [compAt, h]

theorem vec_theta_fock : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} {N : GlobalTheory.FunObj.Std G U} (Z : GlobalTheory.FunObj.Normal W N) {t : T} {p : GlobalTheory.ChiGrid.Pair T}, GlobalTheory.FunObj.DefPair D.R.m p → ∀ d : GlobalTheory.FunObj.FinDatum G t p, Z.HasVec d → IsThetaFunO W.ψ (G.pS p) (G.pT p) (Z.vec d) ∧ ∀ τ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ τ (cplxO (G.cartS W.cart p τ) (G.onT W.cart p τ)) (Z.vec d) := by
  intro D T L sc G W U N Z t p hp d hv
  obtain ⟨f, hf⟩ := hv
  have hvac := Z.vac_is p hp
  have hψ := hvac.1
  have hV := hvac.2
  have hθ : IsInfFam W.θ := hV.inf
  have hf0 := hV.theta
  have hft : IsThetaFunO W.ψ (G.pS p) (G.pT p) f := GlobalTheory.GalLift.Vec.theta_of_thetaAt hψ hθ hf hf0
  have he : infPart D d.e = 0 := GlobalTheory.PlaceVec.idemSum_infPart d.e_is
  have hfock : ∀ τ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ τ
      (cplxO (G.cartS W.cart p τ) (G.onT W.cart p τ)) f := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ he (GlobalTheory.PlaceVec.infPart_cA he) hf hf0 hft (hV.fock τ)
  have hr : Pair.InRange D.R.m p := by
    have := (DefPair.nodes hp).2
    unfold Pair.InRange
    revert this
    cases p.big <;> simp [DefNode, Node.InRange] <;> omega
  have hW := W.om_is p hr
  have hvec : Z.vec d = W.om p (d.z, 1) f := FinDatum.vec_eq W hf
  rw [hvec]
  refine ⟨hW.om_pres _ _ hft, fun τ z => ?_⟩
  obtain ⟨c, hc⟩ := d.z_cen
  obtain ⟨s, hs⟩ := compAt_central (θ := W.θ) τ (n := (G.pS p).rank) c
  have hS : G.cartS W.cart p τ * compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) d.z) =
      compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) d.z) * G.cartS W.cart p τ := by
    rw [hc, hs, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  have hc1 : Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p)) = (1 : AE D) • (1 : Matrix _ _ (AE D)) := by
    simp [Formalism.L2.Theta.mt]
  obtain ⟨s', hs'⟩ := compAt_central (θ := W.θ) τ (n := (G.pT p).rank) (1 : AE D)
  have hT : G.onT W.cart p τ * compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p))) =
      compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p))) * G.onT W.cart p τ := by
    rw [hc1, hs', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  obtain ⟨z₀, rfl⟩ : ∃ z₀ : Matrix (Fin (G.pT p).rank) (Fin (G.pS p).rank) ℂ,
      z = compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p))) * z₀ *
        compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) d.z⁻¹) := by
    refine ⟨compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p))⁻¹) * z *
      compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) d.z), ?_⟩
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.OrientedHeis.compAt_mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      GlobalTheory.OrientedHeis.compAt_mt_mul_inv, Matrix.mul_one]
  have h0 := congrArg (W.om p (d.z, 1)) (hfock τ z₀)
  rw [GlobalTheory.FockMove.om_annih hW hθ d.z 1 τ hS hT z₀ hft, map_zero] at h0
  exact h0

end GlobalTheory.FockRealVec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFiniteDatumVectorThetaFockVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridFiniteDatumVector_theta_fockVacuum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} {N : GlobalTheory.FunObj.Std G U} (Z : GlobalTheory.FunObj.Normal W N) {t : T} {p : GlobalTheory.ChiGrid.Pair T}, GlobalTheory.FunObj.DefPair D.R.m p → ∀ d : GlobalTheory.FunObj.FinDatum G t p, Z.HasVec d → IsThetaFunO W.ψ (G.pS p) (G.pT p) (Z.vec d) ∧ ∀ τ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ τ (cplxO (G.cartS W.cart p τ) (G.onT W.cart p τ)) (Z.vec d) := by
  first | exact @GlobalTheory.FockRealVec.vec_theta_fock | exact GlobalTheory.FockRealVec.vec_theta_fock | (intros; apply GlobalTheory.FockRealVec.vec_theta_fock <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DefStep

variable {D : D7}

def finOf (V : HSp D) (g : GA D V) : GfC V := ((GlobalTheory.AdelicSplit.splitEquiv V).symm g).2

def infOf (V : HSp D) (g : GA D V) : GinfC V := ((GlobalTheory.AdelicSplit.splitEquiv V).symm g).1

theorem infOf_mul_finOf (V : HSp D) (g : GA D V) : ((infOf V g : GinfC V) : GA D V) * (finOf V g : GA D V) = g :=
  (GlobalTheory.AdelicSplit.splitEquiv V).apply_symm_apply g

def IsFinReal {V : HSp D} {Wsp : Type} [AddCommGroup Wsp] [Module ℂ Wsp] (ρ : GA D V →* Module.End ℂ Wsp)
    (F : GA D V → ℂ) (Λ : Module.Dual ℂ Wsp) (v : GfC V → Wsp) : Prop :=
  ∀ g, F g = Λ (ρ g⁻¹ (v (finOf V g)))

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def frGL (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) (τ : D.what₂.Tau) : GL (Fin (G.V X).rank) ℂ :=
  Formalism.UG.bc (tauE D τ) (fr X)

def realIn (θ : InfFam D) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) :
    GA D (G.V X) →* (D.what₂.Tau → GL (Fin (G.V X).rank) ℂ) :=
  MonoidHom.pi fun τ ↦ (MulAut.conj (frGL fr X τ)⁻¹).toMonoidHom.comp
    ((Pi.evalMonoidHom (fun _ : D.what₂.Tau ↦ GL (Fin (G.V X).rank) ℂ) τ).comp (GlobalTheory.CoefModel.realGL θ (G.V X)))

def realAct (θ : InfFam D) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) :
    GA D (G.V X) →* Module.End ℂ (VV ℂ (wt G X)) :=
  (rhoK (wt G X)).comp (invTrK.comp (realIn θ fr X))

theorem realAct_fin (θ : InfFam D) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) {g : GA D (G.V X)}
    (hg : g ∈ GfC (G.V X)) : realAct θ fr X g = 1 := by
  have h : GlobalTheory.CoefModel.realGL θ (G.V X) g = 1 := by
    funext τ
    show Formalism.UG.bc (θ τ) (infHom (G.V X) g) = 1
    rw [show infHom (G.V X) g = 1 from hg, map_one]
  have h2 : realIn θ fr X g = 1 := by
    funext τ
    simp [realIn, h]
  rw [realAct, MonoidHom.comp_apply, MonoidHom.comp_apply, h2, map_one, map_one]

end GlobalTheory.DefStep

namespace GlobalTheory.DefStep
variable {D : D7}

theorem split_symm_eq (V : HSp D) {g : GA D V} (a : GinfC V) (b : GfC V) (h : (a : GA D V) * b = g) :
    (GlobalTheory.AdelicSplit.splitEquiv V).symm g = (a, b) :=
  (GlobalTheory.AdelicSplit.splitEquiv V).symm_apply_eq.2 h.symm

theorem finOf_fin (V : HSp D) (b : GfC V) : finOf V b = b := by
  rw [finOf, split_symm_eq V 1 b (one_mul _)]

theorem finOf_mul_inf (V : HSp D) (g : GA D V) (k : GinfC V) : finOf V (g * k) = finOf V g := by
  have h : ((infOf V g * k : GinfC V) : GA D V) * (finOf V g : GA D V) = g * k := by
    have hc := GlobalTheory.AdelicSplit.commute_GinfC_GfC V k.2 (finOf V g).2
    conv_rhs => rw [← infOf_mul_finOf V g]
    rw [Subgroup.coe_mul, mul_assoc, hc, ← mul_assoc]
  rw [finOf, split_symm_eq V _ _ h]

theorem finOf_mul_fin (V : HSp D) (g : GA D V) (k : GfC V) : finOf V (g * k) = finOf V g * k := by
  have h : ((infOf V g : GinfC V) : GA D V) * ((finOf V g * k : GfC V) : GA D V) = g * k := by
    rw [Subgroup.coe_mul, ← mul_assoc, infOf_mul_finOf]
  rw [finOf, split_symm_eq V _ _ h]

end GlobalTheory.DefStep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselColumnScalarFunctionContinuousLeftInvariant
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

namespace GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem colFn_cont_left : Big fun ch => ∀ a, Continuous (colFn ch a) ∧
    ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g, colFn ch a (γ * g) = colFn ch a g := by
  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ a
  exact ⟨GlobalTheory.RowBplus.pairVec_cont ch.G ch.W.θ ch.W.θ_is ch.ξ (col_mem ch a),
    fun γ hγ g => GlobalTheory.RowBplus.pairVec_left ch.G ch.W.θ ch.ξ (col_mem ch a) hγ g⟩

end GlobalTheory.RowClaim

end
end
