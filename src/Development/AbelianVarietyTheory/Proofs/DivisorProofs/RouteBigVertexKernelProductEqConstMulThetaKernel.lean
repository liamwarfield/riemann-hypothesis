module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFinitePartMemHomLatticeCompletionIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPair
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAbelianGaloisHost

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RouteBigVertexKernelProductEqConstMulThetaKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RouteBigVertexKernelProductEqConstMulThetaKernel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grid
noncomputable section

namespace GlobalTheory.RouteSeesaw

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.MixModel

theorem data_theta {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)}
    (hΘ : IsMatched B t ρ i j Θ Θ') : ∀ d ∈ Θ.support,
      IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) d.2 := by
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, -, φ₁, φ₂, hloc, -⟩, rfl, -⟩ := hΘ
  intro d hd
  have hsupp := Finsupp.support_sum hd
  simp only [Finset.mem_biUnion] at hsupp
  obtain ⟨P, -, hP⟩ := hsupp
  have hsupp2 := Finsupp.support_sum hP
  simp only [Finset.mem_biUnion] at hsupp2
  obtain ⟨d', hd', hd'2⟩ := hsupp2
  have hdd := Finset.mem_singleton.1 (Finsupp.support_single_subset hd'2)
  subst hdd
  obtain ⟨h1, h2⟩ := hloc d' hd'
  have v1 := (ρ.vX_is (i : ℕ) ((j : ℕ) + 1) i.2 j.2).2.theta
  have v2 := (ρ.vT_is t ((i : ℕ) + 1) (j : ℕ) i.2 j.2).2.theta
  have t1 := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h1.2 v1
  have t2 := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h2.2 v2
  exact ⟨GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _,
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _⟩

theorem dagger_zero {D : D7} (S T : HSp D) : dagger S T 0 = 0 := by
  simp [dagger]

theorem hecke_mul' {D : D7} {χ ν : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hν : IsHeckeChar D ν) :
    IsHeckeChar D (χ * ν) :=
  ⟨hχ.1.mul hν.1, fun x => by rw [MonoidHom.mul_apply, hχ.2, hν.2, mul_one]⟩

theorem splitFac_ratio {D : D7} (a b c : (AE D)ˣ →* Circle) (x y : (AE D)ˣ) :
    (splitFacO a c⁻¹ x y : ℂ) * (splitFacO b⁻¹ c⁻¹ x y : ℂ)⁻¹ = ((a y * b y : Circle) : ℂ) := by
  simp only [splitFacO, MonoidHom.inv_apply, inv_inv, Circle.coe_mul, Circle.coe_inv]
  have h1 : ((c x : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have h2 : ((b y : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  field_simp

theorem seesaw_product {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {Wo V V₁ : HSp D}
    {c1S c1T c2S c2T : (AE D)ˣ →* Circle}
    {ω₁ : GA D (negSp Wo) × GA D V →* Module.End ℂ (WO (negSp Wo) V → ℂ)}
    {ω₂ : GA D V₁ × GA D Wo →* Module.End ℂ (WO V₁ Wo → ℂ)}
    (H1 : IsWeilDatumO ψ (negSp Wo) V c1S c1T ω₁) (H2 : IsWeilDatumO ψ V₁ Wo c2S c2T ω₂)
    {f₁ : WO (negSp Wo) V → ℂ} {f₂ : WO V₁ Wo → ℂ} (hf₁ : IsThetaFunO ψ (negSp Wo) V f₁)
    (hf₂ : IsThetaFunO ψ V₁ Wo f₂) (g : GA D V) (g₁ : GA D V₁) :
    ∃ (X : HSp D) (χ χ' : (AE D)ˣ →* Circle) (ω : WRep Wo X), IsWeil ψ true Wo X χ χ' ω ∧
      X.rank = V.rank + V₁.rank ∧ ∃ Φ : WO (sgn true Wo) X → ℂ, IsThetaFunO ψ (sgn true Wo) X Φ ∧
        ∃ (h : GA D X) (c : ℂ), ∀ u, ω₁ (negGA Wo u, g) f₁ 0 * ω₂ (g₁, u) f₂ 0 = c * thetaKO ω u h Φ := by
  have hη : ∃ η, GlobalTheory.WeilParts.IsEtaTilde D η :=
    (GlobalTheory.Mem.EtaTilde.exists_etaTilde D).imp fun _ h => ⟨h.1, h.2.2.2, h.2.2.1, h.2.1⟩

  have H2b : IsWeilDatumO ψ (negSp Wo) V₁ c2T⁻¹ c2S⁻¹ (conjSource (conjAdjoint ω₂)) :=
    GlobalTheory.ConjWeil.weil_conjSource D ψ Wo V₁ _ _ _ (GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ V₁ Wo _ _ ω₂ H2)

  obtain ⟨ω₂c, H2c⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ (negSp Wo) V₁ c1S c2S⁻¹ hη H1.hecS
    (GlobalTheory.ConjWeil.hecke_inv H2.hecS) H1.resS (resEta_inv H2.resS)

  obtain ⟨⟨X, o⟩⟩ := GlobalTheory.OrthSumExists.exists_orthDec D V V₁
  obtain ⟨ω', H'⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ (negSp Wo) X c1S (c1T * c2S⁻¹) hη
    H1.hecS (hecke_mul' H1.hecT (GlobalTheory.ConjWeil.hecke_inv H2.hecS)) H1.resS (o.rank_add ▸ resEta_mul H1.resT (resEta_inv H2.resS))
  have TT := GlobalTheory.TensorTargetRule.tensorTarget D ψ hψ (X) V V₁ o (negSp Wo)

  have hF₂ : IsThetaFunO ψ (negSp Wo) V₁ (cj id (cj (dagger Wo V₁) f₂)) := by
    have h1 : IsThetaFunO ψ Wo V₁ (cj (dagger Wo V₁) f₂) := ((GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ V₁ Wo).2.2.1 f₂).2 hf₂
    have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hψ Wo V₁
    exact ((I.1 _).2).2 h1
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D V₁ g₁
  let ω : WRep Wo (X) := ω'.comp ((negGA Wo).toMonoidHom.prodMap (MonoidHom.id _))
  have hω : ω.toSgn true = ω' := MonoidHom.ext fun p => rfl
  refine ⟨X, c1S, c1T * c2S⁻¹, ω, ?_, o.rank_add.symm, o.boxT (negSp Wo) f₁ (cj id (cj (dagger Wo V₁) f₂)),
    TT.box_theta _ _ hf₁ hF₂, o.emb (g, g₁), ((c1S y * c2T y : Circle) : ℂ)⁻¹, fun u => ?_⟩
  · show IsWeilDatumO ψ (sgn true Wo) _ _ _ (ω.toSgn true)
    rw [hω]; exact H'
  · obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D (negSp Wo) (negGA Wo u)
    have k1 := TT.om_box c1S c1T c2S⁻¹ ω' ω₁ ω₂c H' H1 H2c (negGA Wo u) g g₁ f₁ _ hf₁ hF₂
    have k2 := GlobalTheory.WeilChange.weilData_differ_by_splitFac D ψ (negSp Wo) V₁ c2T⁻¹ c2S⁻¹ c1S c2S⁻¹ _ ω₂c H2b H2c
      (negGA Wo u) g₁ x y hx hy _ hF₂
    have k3 : conjSource (conjAdjoint ω₂) (negGA Wo u, g₁) (cj id (cj (dagger Wo V₁) f₂)) 0 = ω₂ (g₁, u) f₂ 0 := by
      rw [GlobalTheory.ConjWeil.conjSource_apply]
      simp only [MulEquiv.symm_apply_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
      rw [GlobalTheory.TensorTargetRule.conjAdjoint_cj]
      simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_zero]
    show _ = _ * ω' (negGA Wo u, o.emb (g, g₁)) (o.boxT (negSp Wo) f₁ (cj id (cj (dagger Wo V₁) f₂))) 0
    rw [k1, OrthDec.boxT_zero, k2, Pi.smul_apply, smul_eq_mul, k3, splitFac_ratio]
    have h0 : ((c1S y * c2T y : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    field_simp

end GlobalTheory.RouteSeesaw


open GlobalTheory.RouteSeesaw in
theorem GlobalTheory.FunObj.routeBig_kernel_product_eq_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ'),
    ∀ d ∈ Θ.support, ∀ (g : GA D (G.V (.grid i (j + 1)))) (g₁ : GA D (G.V (.grid (i + 1) j))),
      ∃ (ε : Bool) (X : HSp D) (χ χ' : (AE D)ˣ →* Circle) (ω : WRep (G.V (.grid (i + 1) (j + 1))) X),
        IsWeil W.ψ ε _ X χ χ' ω ∧ X.rank = (G.V (.grid i (j + 1))).rank + (G.V (.grid (i + 1) j)).rank ∧
        ∃ Φ : WO (sgn ε (G.V (.grid (i + 1) (j + 1)))) X → ℂ, IsThetaFunO W.ψ (sgn ε _) X Φ ∧
          ∃ (h : GA D X) (c : ℂ), ∀ u, W.kerA (.right i (j + 1)) d.1.2 g u * W.kerA (.down t (i + 1) j) d.2 u g₁ =
            c * thetaKO ω u h Φ := by
  intro D T L sc G μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ d hd g g₁
  obtain ⟨hf₁, hf₂⟩ := data_theta W B ρ t i j hΘ d hd
  have hp1 : (Pair.chi (i : ℕ) ((j : ℕ) + 1) : Pair T).InRange D.R.m := ⟨by omega, by omega⟩
  have hp2 : (Pair.mu t ((i : ℕ) + 1) (j : ℕ)).InRange D.R.m := ⟨by omega, by omega⟩
  obtain ⟨X, χ, χ', ω, hω, hX, Φ, hΦ, h, c, hc⟩ :=
    seesaw_product W.ψ_std (W.om_is _ hp1) (W.om_is _ hp2) hf₁ hf₂ g g₁
  exact ⟨true, X, χ, χ', ω, hω, hX, Φ, hΦ, h, c, hc⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RouteBigVertexKernelProductEqConstMulThetaKernelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.routeBigVertex_kernelProduct_eq_const_mul_thetaKernel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ'),
    ∀ d ∈ Θ.support, ∀ (g : GA D (G.V (.grid i (j + 1)))) (g₁ : GA D (G.V (.grid (i + 1) j))),
      ∃ (ε : Bool) (X : HSp D) (χ χ' : (AE D)ˣ →* Circle) (ω : WRep (G.V (.grid (i + 1) (j + 1))) X),
        IsWeil W.ψ ε _ X χ χ' ω ∧ X.rank = (G.V (.grid i (j + 1))).rank + (G.V (.grid (i + 1) j)).rank ∧
        ∃ Φ : WO (sgn ε (G.V (.grid (i + 1) (j + 1)))) X → ℂ, IsThetaFunO W.ψ (sgn ε _) X Φ ∧
          ∃ (h : GA D X) (c : ℂ), ∀ u, W.kerA (.right i (j + 1)) d.1.2 g u * W.kerA (.down t (i + 1) j) d.2 u g₁ =
            c * thetaKO ω u h Φ := by
  first | exact @GlobalTheory.FunObj.routeBig_kernel_product_eq_theta | exact GlobalTheory.FunObj.routeBig_kernel_product_eq_theta | (intros; apply GlobalTheory.FunObj.routeBig_kernel_product_eq_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemScLatOfMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.BigDat

theorem smul_mem_scLat_of_mem {E : Type} [Field E] [NumberField E] {n : ℕ} {𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E}
    {Λ : Submodule (𝓞 E) (Fin n → E)} {a : E} (ha : a ∈ 𝔞) {y : Fin n → E} (hy : y ∈ Λ) :
    a • y ∈ GlobalTheory.SkewLat.scLat 𝔞 Λ := by
  intro c hc
  have h : a * c ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
    FractionalIdeal.mul_one_div_le_one (FractionalIdeal.mul_mem_mul ha hc)
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h
  rw [smul_smul, mul_comm, ← hr, algebraMap_smul]
  exact Λ.smul_mem r hy

theorem divG_gen {D : D7} (S : HSp D) {n : ℕ} (β : AF D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin n → D.host.E) (p : Fin n) (q : Fin S.rank) :
    divG S (Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) p q =
      β ⊗ₜ[D.host.F] (a * t p * star (s q)) := by
  have h : (Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : Matrix _ _ (AE D)) =
      mulG S (Matrix.of fun i k => β ⊗ₜ[D.host.F] (a * t i * star (s k))) := by
    ext i j
    rw [mulG_eq, Matrix.mul_apply]
    simp only [of_apply, map_apply, Finset.mul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change _ = (β ⊗ₜ[D.host.F] (a * t i * star (s k))) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram k j)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_assoc (a * t i)]
  rw [h, divG_mulG, of_apply]

theorem divG_zero {D : D7} (S : HSp D) {n : ℕ} : divG S (0 : Matrix (Fin n) (Fin S.rank) (AE D)) = 0 :=
  Matrix.zero_mul _

theorem divG_neg {D : D7} (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) (AE D)) : divG S (-x) = -divG S x :=
  Matrix.neg_mul _ _

theorem smul_incM_apply {D : D7} {m n : Type} (β : AF D.host.F) (M : Matrix m n D.host.E) (p : m) (q : n) :
    (β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F M) p q = β ⊗ₜ[D.host.F] M p q := by
  change β • ((1 : AF D.host.F) ⊗ₜ[D.host.F] M p q) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem one_smul_gen_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {α : Af F} (hα : α ∈ intAf F) {x : Fin n → E} (hx : x ∈ X.L)
    {y : Fin d → E} (hy : y ∈ Y.L) :
    GlobalTheory.LatVac.liftV v 1 • pairA F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (vecMulVec x y) ∈ latAtV X Y v := by
  rw [smul_smul]
  refine AddSubgroup.subset_closure ⟨_, ?_, ?_, x, hx, y, hy, rfl⟩
  · intro u hu
    rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u, GlobalTheory.LatVac.at_liftV v 1 u hu, zero_mul]
  · rw [map_mul, GlobalTheory.LatVac.evFin_liftV, one_mul]
    exact hα v

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem ofMaps_inl (e : Num G i j) (x : HomV G i j × HomW G i j) (p : Fin (spW G i j).rank) (k : Fin (spV G i j).rank) :
    ofMaps e x p (e (.inl k)) = divG (negSp (spW G i j)) x.1 k p := by
  simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, transpose_apply]

theorem ofMaps_inr (e : Num G i j) (x : HomV G i j × HomW G i j) (p : Fin (spW G i j).rank) (k : Fin (spV₁ G i j).rank) :
    ofMaps e x p (e (.inr k)) = cA D (divG (spV₁ G i j) (-x.2) p k) := by
  simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply]

theorem ofMaps_genV (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spW G i j).rank → D.host.E)
    (t : Fin (spV G i j).rank → D.host.E) :
    ofMaps e (Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * t i' * ∑ k, star (s k) * (negSp (spW G i j)).gram k j'), 0) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star s) (Sum.elim (a • t) 0 ∘ e.symm)) := by
  ext p q
  obtain ⟨k | k, rfl⟩ := e.surjective q
  · refine (ofMaps_inl e _ p k).trans ((divG_gen (negSp (spW G i j)) β a s t k p).trans ?_)
    rw [smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, mul_comm]
    rfl
  · refine (ofMaps_inr e _ p k).trans ?_
    rw [smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, neg_zero, divG_zero,
      Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
    exact map_zero _

theorem ofMaps_genW (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spV₁ G i j).rank → D.host.E)
    (t : Fin (spW G i j).rank → D.host.E) :
    ofMaps e (0, Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * t i' * ∑ k, star (s k) * (spV₁ G i j).gram k j')) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star (-t)) (Sum.elim 0 (star (a • star s)) ∘ e.symm)) := by
  ext p q
  obtain ⟨k | k, rfl⟩ := e.surjective q
  · refine (ofMaps_inl e _ p k).trans ((congrFun (congrFun (divG_zero (negSp (spW G i j))) k) p).trans ?_)
    rw [smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl,
      Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
    rfl
  · refine (ofMaps_inr e _ p k).trans ?_
    rw [smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, divG_neg, Matrix.neg_apply,
      divG_gen, ← TensorProduct.tmul_neg]
    change β ⊗ₜ[D.host.F] star (-(a * t p * star (s k))) = β ⊗ₜ[D.host.F] (star (-t p) * star (a * star (s k)))
    rw [← star_mul']
    congr 2
    ring

theorem map_mem_of_closure {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) {s : Set A} {H : AddSubgroup B}
    (h : ∀ x ∈ s, f x ∈ H) {x : A} (hx : x ∈ AddSubgroup.closure s) : f x ∈ H :=
  (AddSubgroup.closure_le (H.comap f)).2 h hx

theorem pair_mem {E : Type} [Field E] [NumberField E] {a b d : ℕ} {ΛA : Submodule (𝓞 E) (Fin a → E)}
    {ΛB : Submodule (𝓞 E) (Fin b → E)} (e : Fin a ⊕ Fin b ≃ Fin d) {x : Fin a → E} {y : Fin b → E} (hx : x ∈ ΛA) (hy : y ∈ ΛB) :
    Sum.elim x y ∘ e.symm ∈ GlobalTheory.SkewLat.pairLat ΛA ΛB e := by
  rw [GlobalTheory.SkewLat.mem_pairLat]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
  exact ⟨hx, hy⟩

theorem star_mem_conjSub {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)}
    {y : Fin n → E} (hy : y ∈ Λ) : star y ∈ GlobalTheory.TripleSpaceW.conjSub Λ := by
  rw [GlobalTheory.TripleSpaceW.mem_conjSub, star_star]; exact hy

theorem smul_ofMaps_inl_mem {t : T} {e : Num G i j} {Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} (h : IsTied t i j e Bs Γ X) (v : Pl D.host.F) {x : HomV G i j} (hx : x ∈ latV G i j) :
    GlobalTheory.LatVac.liftV v 1 • ofMaps e (x, 0) ∈ latAtV Γ.V Γ.W v := by
  refine map_mem_of_closure ((DistribSMul.toAddMonoidHom (Pt G i j) (GlobalTheory.LatVac.liftV v 1)).comp
    ((maps e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inl _ _))) ?_ hx
  rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
  exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V Γ.W v) (ofMaps_genV e (pairA _ 0 α) a s t)).mpr
    (one_smul_gen_mem _ _ v hα (h.1.ge (star_mem_conjSub hs))
      (h.2.1.ge (pair_mem e (smul_mem_scLat_of_mem ha ht) (zero_mem _))))

theorem smul_ofMaps_inr_mem {t : T} {e : Num G i j} {Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} (h : IsTied t i j e Bs Γ X) (v : Pl D.host.F) {x : HomW G i j} (hx : x ∈ latW G i j) :
    GlobalTheory.LatVac.liftV v 1 • ofMaps e (0, x) ∈ latAtV Γ.V Γ.W v := by
  refine map_mem_of_closure ((DistribSMul.toAddMonoidHom (Pt G i j) (GlobalTheory.LatVac.liftV v 1)).comp
    ((maps e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inr _ _))) ?_ hx
  rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
  exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V Γ.W v) (ofMaps_genW e (pairA _ 0 α) a s t)).mpr
    (one_smul_gen_mem _ _ v hα (h.1.ge (star_mem_conjSub (neg_mem ht)))
      (h.2.1.ge (pair_mem e (zero_mem _) (star_mem_conjSub (smul_mem_scLat_of_mem ha (star_mem_conjSub hs))))))

theorem latPt_le_latAtV : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (i j : ℕ) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E), IsTied t i j e Bs Γ X →
    ∀ v : Pl D.host.F, ∀ u ∈ latPt e v, u ∈ latAtV Γ.V Γ.W v := by
  intro D T L sc G t i j e Bs Γ X h v u hu
  obtain ⟨hat, h1, h2⟩ := hu
  have e1 : GlobalTheory.LatVac.liftV v 1 • u = u := by
    have := hat (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  have e2 : u = ofMaps e (mapV e u, 0) + ofMaps e (0, mapW e u) :=
    ((ofMaps_maps e u).symm.trans (congrArg (ofMaps e) (Prod.ext (add_zero _).symm (zero_add _).symm))).trans
      (map_add (maps e).symm (mapV e u, 0) (0, mapW e u))
  have e3 := add_mem (smul_ofMaps_inl_mem h v h1) (smul_ofMaps_inr_mem h v h2)
  rwa [← smul_add, ← e2, e1] at e3

end GlobalTheory.BigDat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzEqPureTensorOfFiniteSlices
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzEqPureTensorOfFiniteSlices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

open Filter Topology

noncomputable section

namespace GlobalTheory.PureGlue

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_slice (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) (z : κ → Af F) :
    ∃ f : SInf F κ, ∀ a : κ → AF F, (∀ i, (a i).2 = z i) → Φ a = f (fun i => evI F (a i)) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, -, rfl⟩ := hΦ
    refine ⟨g z • f, fun a ha => ?_⟩
    have h : (fun i => (a i).2) = z := funext ha
    show f _ * g (fun i => (a i).2) = _
    rw [h, SchwartzMap.smul_apply, smul_eq_mul, mul_comm]
    rfl
  | zero => exact ⟨0, fun a _ => by simp⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨f1, hf1⟩ := h1
    obtain ⟨f2, hf2⟩ := h2
    exact ⟨f1 + f2, fun a ha => by simp [hf1 a ha, hf2 a ha]⟩
  | smul c Φ _ h =>
    obtain ⟨f1, hf1⟩ := h
    exact ⟨c • f1, fun a ha => by simp [hf1 a ha]⟩

theorem isLocallyConstant_fin (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) (b : κ → Ainf F) :
    IsLocallyConstant (fun z : κ → Af F => Φ (fun i => (b i, z i))) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    exact (IsLocallyConstant.const (f fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (b i))).mul hg.1
  | zero => exact IsLocallyConstant.const 0
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul c Φ _ h => exact h.comp (fun t => c • t)

def hyb (S : Finset (HeightOneSpectrum (𝓞 F))) (y g : Af F) : Af F :=
  g + ∑ v ∈ S, singleFin v (evalV F v y - evalV F v g)

theorem evalV_hyb (S : Finset (HeightOneSpectrum (𝓞 F))) (y g : Af F) (u : HeightOneSpectrum (𝓞 F)) :
    evalV F u (hyb S y g) = if u ∈ S then evalV F u y else evalV F u g := by
  unfold hyb
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum]
  split_ifs with hu
  · rw [Finset.sum_eq_single u (fun v _ hv => evalV_singleFin_ne (Ne.symm hv) _) (fun h => absurd hu h),
      evalV_singleFin_self]
    abel
  · rw [Finset.sum_eq_zero (fun v hv => evalV_singleFin_ne (by rintro rfl; exact hu hv) _), add_zero]

theorem hyb_insert {S : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) (y g : Af F) :
    hyb (insert v S) y g = hyb S y g + singleFin v (evalV F v y - evalV F v g) := by
  unfold hyb
  rw [Finset.sum_insert hv]
  abel

theorem hyb_empty (y g : Af F) : hyb ∅ y g = g := by simp [hyb]

theorem tendsto_hyb (y g : Af F) : Tendsto (fun S => hyb S y g) atTop (𝓝 y) :=
  GlobalTheory.AdelicLimit.tendsto_finAdele _ y g
    (fun T v hv => by have h := evalV_hyb T y g v; rw [if_pos hv] at h; exact h)
    (fun T v hv => by have h := evalV_hyb T y g v; rw [if_neg hv] at h; exact h)

end GlobalTheory.PureGlue

namespace GlobalTheory.PureGlue
variable {F : Type} [Field F] [NumberField F]
theorem liftV_fst (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) : (GlobalTheory.LatVac.liftV v a).1 = 0 := rfl
theorem liftV_snd (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) : (GlobalTheory.LatVac.liftV v a).2 = singleFin v a := rfl
theorem fst_sub_add (p : AF F) (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) :
    (p - GlobalTheory.LatVac.liftV v a + GlobalTheory.LatVac.liftV v b).1 = p.1 := by
  change p.1 - (GlobalTheory.LatVac.liftV v a).1 + (GlobalTheory.LatVac.liftV v b).1 = p.1
  rw [liftV_fst, liftV_fst, sub_zero, add_zero]
theorem snd_sub_add (p : AF F) (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) :
    (p - GlobalTheory.LatVac.liftV v a + GlobalTheory.LatVac.liftV v b).2 = p.2 - singleFin v a + singleFin v b := by
  change p.2 - (GlobalTheory.LatVac.liftV v a).2 + (GlobalTheory.LatVac.liftV v b).2 = _
  rw [liftV_snd, liftV_snd]
end GlobalTheory.PureGlue

namespace GlobalTheory.PureGlue

open scoped Classical

theorem eq_pure_of_slices : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ), (∀ v, vac v ≠ 0) →
    (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ Φ ∈ schA F κ, (∀ (v : HeightOneSpectrum (𝓞 F)) (y : κ → AF F), (∀ k, evFin F v (y k) = 0) →
      ∃ a : ℂ, ∀ ξ : κ → Fv F v, Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)) = a * vac v ξ) →
    ∃ f : SInf F κ, Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f vac := by
  intro F _ _ κ _ vac hvac hcof Φ hΦ hsl
  set T0 : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | ¬ vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1} with hT0
  have hT0f : T0.Finite := hcof
  have hex : ∀ v, ∃ ζ : κ → Fv F v, vac v ζ ≠ 0 := fun v => by
    by_contra h
    push_neg at h
    exact hvac v (funext h)
  let ζ : ∀ v, κ → Fv F v := fun v => if v ∈ T0 then (hex v).choose else 0
  have hζ1 : ∀ v, v ∉ T0 → vac v (ζ v) = 1 := by
    intro v hv
    have h : vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := not_not.1 hv
    simp only [ζ, if_neg hv]
    rw [h, Set.indicator_of_mem (show (0 : κ → Fv F v) ∈ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from
      fun i => zero_mem _)]
    rfl
  have hζ : ∀ v, vac v (ζ v) ≠ 0 := by
    intro v
    by_cases hv : v ∈ T0
    · simp only [ζ, if_pos hv]
      exact (hex v).choose_spec
    · rw [hζ1 v hv]
      exact one_ne_zero
  let ξ0 : κ → Af F := fun i => ∑ v ∈ hT0f.toFinset, singleFin v (ζ v i)
  have hξ0 : ∀ v i, evalV F v (ξ0 i) = ζ v i := by
    intro v i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ξ0, map_sum]
    by_cases hv : v ∈ T0
    · rw [Finset.sum_eq_single v (fun u _ hu => evalV_singleFin_ne (Ne.symm hu) _)
        (fun h => absurd (hT0f.mem_toFinset.2 hv) h), evalV_singleFin_self]
    · rw [Finset.sum_eq_zero (fun u hu => evalV_singleFin_ne
        (by rintro rfl; exact hv (hT0f.mem_toFinset.1 hu)) _)]
      simp [ζ, hv]
  set c : ℂ := ∏ v ∈ hT0f.toFinset, vac v (ζ v) with hcdef
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hζ v
  obtain ⟨f0, hf0⟩ := exists_slice Φ hΦ ξ0
  refine ⟨c⁻¹ • f0, ?_⟩
  funext x
  have hev : ∀ (v : HeightOneSpectrum (𝓞 F)) (a : AF F), evFin F v a = evalV F v a.2 := fun _ _ => rfl
  let P : Finset (HeightOneSpectrum (𝓞 F)) → κ → AF F := fun S i => ((x i).1, hyb S (x i).2 (ξ0 i))
  have key : ∀ S, Φ (P S) * ∏ v ∈ S, vac v (ζ v) =
      Φ (P ∅) * ∏ v ∈ S, vac v (fun i => evFin F v (x i)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert v S hv ih =>
      let y : κ → AF F := fun k => P S k - GlobalTheory.LatVac.liftV v (ζ v k)
      have hy : ∀ k, evFin F v (y k) = 0 := by
        intro k
        simp only [y, map_sub, GlobalTheory.LatVac.evFin_liftV]
        rw [hev]
        change evalV F v (hyb S (x k).2 (ξ0 k)) - ζ v k = 0
        rw [evalV_hyb, if_neg hv, hξ0, sub_self]
      obtain ⟨a, ha⟩ := hsl v y hy
      have e1 : P S = y + fun k => GlobalTheory.LatVac.liftV v (ζ v k) := by
        funext k
        simp [y]
      have e2 : P (insert v S) = y + fun k => GlobalTheory.LatVac.liftV v (evFin F v (x k)) := by
        funext k
        have hk : (y + fun k => GlobalTheory.LatVac.liftV v (evFin F v (x k))) k =
            P S k - GlobalTheory.LatVac.liftV v (ζ v k) + GlobalTheory.LatVac.liftV v (evFin F v (x k)) := rfl
        rw [hk]
        refine Prod.ext ?_ ?_
        · rw [fst_sub_add]
        · rw [snd_sub_add]
          show hyb (insert v S) (x k).2 (ξ0 k) =
            hyb S (x k).2 (ξ0 k) - singleFin v (ζ v k) + singleFin v (evFin F v (x k))
          rw [hyb_insert hv, hξ0, map_sub, hev]
          abel
      have h1 := ha (ζ v)
      have h2 := ha (fun i => evFin F v (x i))
      rw [← e1] at h1
      rw [← e2] at h2
      rw [Finset.prod_insert hv, Finset.prod_insert hv]
      linear_combination (vac v (ζ v) * ∏ u ∈ S, vac u (ζ u)) * h2 -
        (vac v (fun i => evFin F v (x i)) * ∏ u ∈ S, vac u (ζ u)) * h1 + vac v (fun i => evFin F v (x i)) * ih
  have hlc := isLocallyConstant_fin Φ hΦ (fun i => (x i).1)
  have ht : Tendsto (fun S => fun i => hyb S (x i).2 (ξ0 i)) atTop (𝓝 (fun i => (x i).2)) :=
    tendsto_pi_nhds.2 fun i => tendsto_hyb (x i).2 (ξ0 i)
  have hev1 : ∀ᶠ S in atTop, Φ (P S) = Φ x :=
    ht ((hlc.isOpen_fiber (Φ x)).mem_nhds rfl)
  have hxi : ∀ᶠ v in Filter.cofinite, ∀ i, evalV F v (x i).2 ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (x i).2.2.mono fun v hv => hv
  set S0 : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | ¬ (vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      ∀ i, evalV F v (x i).2 ∈ v.adicCompletionIntegers F)} with hS0
  have hS0f : S0.Finite := hcof.and hxi
  have hev2 : ∀ᶠ S in atTop, hS0f.toFinset ∪ hT0f.toFinset ≤ S := Filter.eventually_ge_atTop _
  obtain ⟨S, hS1, hS2⟩ := (hev1.and hev2).exists
  have k := key S
  rw [hS1] at k
  have hcS : ∏ v ∈ S, vac v (ζ v) = c := by
    symm
    refine Finset.prod_subset (fun v hv => hS2 (Finset.mem_union_right _ hv)) ?_
    intro v _ hv
    exact hζ1 v (fun h => hv (hT0f.mem_toFinset.2 h))
  have hfp : ∏ᶠ v, vac v (fun i => evFin F v (x i)) = ∏ v ∈ S, vac v (fun i => evFin F v (x i)) := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    by_contra hvS
    apply hv
    show vac v (fun i => evFin F v (x i)) = 1
    have hn : v ∉ S0 := fun h => hvS (hS2 (Finset.mem_union_left _ (hS0f.mem_toFinset.2 h)))
    have h' := not_not.1 hn
    rw [h'.1, Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈
      {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from h'.2)]
    rfl
  have hP0 : Φ (P ∅) = f0 (fun i => evI F (x i)) :=
    hf0 (P ∅) (fun i => by simp [P, hyb_empty])
  rw [hcS] at k
  show Φ x = (c⁻¹ • f0) (fun i => evI F (x i)) * ∏ᶠ v, vac v fun i => evFin F v (x i)
  rw [SchwartzMap.smul_apply, smul_eq_mul, hfp, ← hP0, mul_assoc, ← k, mul_comm (Φ x), ← mul_assoc,
    inv_mul_cancel₀ hc, one_mul]

end GlobalTheory.PureGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzEqPureTensorOfFiniteSlicesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartz_eq_pureTensor_of_finite_slices : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ), (∀ v, vac v ≠ 0) →
    (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ Φ ∈ schA F κ, (∀ (v : HeightOneSpectrum (𝓞 F)) (y : κ → AF F), (∀ k, evFin F v (y k) = 0) →
      ∃ a : ℂ, ∀ ξ : κ → Fv F v, Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)) = a * vac v ξ) →
    ∃ f : SInf F κ, Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f vac := by
  first | exact @GlobalTheory.PureGlue.eq_pure_of_slices | exact GlobalTheory.PureGlue.eq_pure_of_slices | (intros; apply GlobalTheory.PureGlue.eq_pure_of_slices <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsOfPrincipalLevelFieldOfDefinition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsOfPrincipalLevelFieldOfDefinition
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Matrix

namespace GlobalTheory.LevLaws

open GlobalTheory.PrincCore

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eq_one_of_norm_one {E : Type} [Field E] [NumberField E] [IsCMField E] {M : ℕ} (hM : 3 ≤ M) (u : E)
    (hint : IsIntegral ℤ ((u - 1) / M)) (hc : u * IsCMField.complexConj E u = 1) : u = 1 := by
  have hM0 : M ≠ 0 := by omega
  by_contra hne
  have hx : (⟨(u - 1) / M, hint⟩ : 𝓞 E) ≠ 0 := by
    intro h
    have : (u - 1) / (M : E) = 0 := congrArg Subtype.val h
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · exact hne (sub_eq_zero.mp h)
    · exact hM0 (Nat.cast_eq_zero.mp h)
  obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hx
  have hσ' : 1 ≤ ‖σ ((u - 1) / M)‖ := hσ
  have h1 : ‖σ u‖ = 1 := by
    have := congrArg (fun z => ‖σ z‖) hc
    simp only [map_mul, IsCMField.complexEmbedding_complexConj, norm_mul, map_one, norm_one,
      Complex.norm_conj] at this
    nlinarith [norm_nonneg (σ u)]
  rw [map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast] at hσ'
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h2 : ‖σ u - 1‖ ≤ 2 := by
    have := norm_sub_le (σ u) 1
    rw [h1, norm_one] at this
    linarith
  rw [le_div_iff₀ (by linarith)] at hσ'
  linarith


set_option maxHeartbeats 800000 in
theorem det_eq_one {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (hr0 : 0 < r) {Comp : Type}
    (X : Comp → Data D.host.E r) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (Kf : Subgroup (GA D V)) (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hD : DictIsUnif V dict Kf th hr)
    (hmu : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1)
    (M : ℕ) (hM : 3 ≤ M) (hK : IsLevelK V M Kf) (k : Comp) (γ' : GL (Fin r) D.host.E) (hγ' : γ' ∈ (X k).Γ) :
    (γ' : Matrix (Fin r) (Fin r) D.host.E).det = 1 := by
  classical
  subst hr
  obtain ⟨-, -, ⟨x0, hx0, heq⟩, -, -, hfib⟩ := hD
  obtain ⟨hdom, g, hg⟩ := hx0 k
  obtain ⟨-, hrat, -, hsur⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).2 (X k).Ψ (th k) (X k).cmType (hth k)
  have hact : ∀ h, ∀ τ, mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ = archM V (th k τ) h * mat (x0 k) τ := by
    intro h τ
    show mat (x0 k) τ * ((mat (x0 k) τ)⁻¹ * Matrix.reindex (finCongr rfl) (finCongr rfl) (archM V (th k τ) h) *
      mat (x0 k) τ) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdom τ).1),
      Matrix.one_mul]
    rfl
  have key : ∀ h ∈ GinfC V, ∃ γ'' ∈ (X k).Γ,
      dict (g * h) = ⟨k, lact γ'' (rmul (x0 k) (archMat V th rfl x0 h k))⟩ := by
    have := heq g
    rw [hg] at this
    exact this
  have hun : ∀ τ : (X k).Ψ, ((γ'.1.map τ.1).map (starRingEnd ℂ))ᵀ * V.gram.map τ.1 *
      γ'.1.map τ.1 = V.gram.map τ.1 := by
    intro τ
    refine unitary_of_first_minor hr0 τ.1 (X k).Gm (X k).Gm_herm _ (mat (x0 k) τ) ?_ ?_ ?_ _ ?_
    · ext a b
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply, HSpace.gram]
      rw [← V.herm.eq (V.frame b) (V.frame a)]
      exact (IsCMField.complexEmbedding_complexConj D.host.E τ.1 _).symm
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero_iff _ τ.1.injective).2 (gram_det_ne V)
    · intro w hw
      obtain ⟨h, hh, hw'⟩ := hsur (Function.update (fun _ => 1) τ w) (by
        intro τ'
        by_cases e : τ' = τ
        · subst e
          simpa using hw
        · simp [Function.update_of_ne e])
      obtain ⟨γ'', h1, h2⟩ := key h hh
      have h3 := hmu (g * h)
      rw [h2] at h3
      have h4 := h3 τ ⟨1, by omega⟩
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.dmin_lact (X k) h1] at h4
      unfold dmin at h4
      rw [hact, hw', Function.update_self] at h4
      exact h4
    · have hcc : (γ'.1.map τ.1).map (starRingEnd ℂ) =
          (γ'.1.map cc).map τ.1 := by
        ext a b
        exact (IsCMField.complexEmbedding_complexConj D.host.E τ.1 _).symm
      rw [hcc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
        ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.gramE (X k) hγ']
  obtain ⟨h, hh, hw⟩ := hsur _ hun
  obtain ⟨γ'', h1, h2⟩ := key h hh
  obtain ⟨γ₀, hγ₀, κ, hκ, hdc⟩ := hfib g (g * h) (by
    rw [hg]
    refine ⟨γ'' * γ', mul_mem h1 hγ', ?_⟩
    rw [h2]
    congr 1
    funext τ
    show γ''.1.map τ.1 * mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ =
      (γ'' * γ').1.map τ.1 * mat (x0 k) τ
    rw [hact, hw, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc])
  obtain ⟨δ, hδ1, hδ2⟩ := hrat γ₀ hγ₀
  obtain ⟨hκ1, hκ2⟩ := (hK κ⁻¹).1 (inv_mem hκ)
  have hfin : finHom V γ₀ * finHom V g = finHom V g * finHom V κ⁻¹ := by
    have h0 : finHom V h = 1 := hh
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, h0, mul_one]
  have hinf : infHom V γ₀ * infHom V g = infHom V g * infHom V h := by
    have h0 : infHom V κ⁻¹ = 1 := hκ1
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, h0, mul_one]
  let f : V.V →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := V.frame.equivFun.toLinearMap.restrictScalars _
  have hhat : latHat V = GlobalTheory.AdLat.hat D.host.F (V.L0.map f : Set (Fin V.rank → D.host.E)) := by
    unfold latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, f x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have hspan : Submodule.span D.host.E (V.L0.map f : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have : (V.L0.map f : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
          Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨z, hz, hz₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e z ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        have hzy : V.hT (e z) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hz)
        have hyz : V.hT y (e z) = 0 := by
          have hh := V.herm.eq (e z) y
          simpa [hzy] using hh.symm
        simp [hyz]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    rw [this, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  rw [hhat] at hκ2
  obtain ⟨Λ', g1, g2, g3⟩ := exists_lattice_congr D.host.F D.host.E V.rank M (by omega) (V.L0.map f)
    (V.standardTuple_isLattice.fg.map f) hspan (finHom V g) (finHom V κ⁻¹).1 δ.1 hκ2 (by
      rw [← hδ2, ← Units.val_mul, hfin, Units.val_mul])
  obtain ⟨τ⟩ : Nonempty (X k).Ψ := by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    by_cases e : τ ∈ (X k).Ψ
    · exact ⟨⟨τ, e⟩⟩
    · exact ⟨⟨_, not_not.1 (fun e' => e (((X k).cmType τ).2 e'))⟩⟩
  have hm : ∀ a b, archM V (th k τ) (a * b) = archM V (th k τ) a * archM V (th k τ) b := by
    intro a b
    unfold archM
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  have h1' : archM V (th k τ) 1 = 1 := by
    unfold archM
    rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hg0 : (archM V (th k τ) g).det ≠ 0 := by
    have := congrArg Matrix.det (hm g⁻¹ g)
    rw [inv_mul_cancel, h1', Matrix.det_one, Matrix.det_mul] at this
    exact right_ne_zero_of_mul_eq_one this.symm
  have hconj : δ.1.map τ.1 * archM V (th k τ) g = archM V (th k τ) g * γ'.1.map τ.1 := by
    rw [← hw τ, ← hδ1 τ, ← hm, ← hm]
    unfold archM
    rw [map_mul, map_mul, hinf]
  have hdd : γ'.1.det = δ.1.det := by
    have := congrArg Matrix.det hconj
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det, ← RingHom.map_det] at this
    exact τ.1.injective (mul_left_cancel₀ hg0 this).symm
  refine eq_one_of_norm_one hM _ ?_
    (GlobalTheory.CongruenceDet.det_mul_conj (X k).Gm _ (X k).Gm_det ((X k).Γ_stab γ' hγ').1)
  rw [hdd]
  refine isIntegral_trans (A := 𝓞 D.host.E) _
    (GlobalTheory.CongruenceDet.isIntegral_det_sub_one (by omega) Λ' _ g1 g2 fun v hv => ?_)
  obtain ⟨y, hy, e⟩ := g3 v hv
  exact ⟨y, hy, by rw [← Nat.cast_smul_eq_nsmul D.host.E, ← e, add_sub_cancel]⟩


open Module GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore in
set_option maxHeartbeats 1000000 in
theorem laws_of_level : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, Formalism.L2.Theta.GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → FnAlgClosed (Xo := Xo) (c := c) → (∀ p : ℕ, p.Prime → l.GoodAt p) → GlobalTheory.FlatCore.Laws U (xiR D) ∧ GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H := by
  intro D j H Dw l Xo c U dict h hF hg
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  refine ⟨⟨?_, h.levA, hg, h.unf, hF, h.xiAbs, h.chiTriv, fun σ hσ k γ hγ => ?_, fun σ hσ a n ha hp hn => ?_,
    GlobalTheory.RankOneDatum.exists_datum_of_rt D H h.host.2.1 h.host.2.2.1⟩, GlobalTheory.FlatRow.isHostField D H h.host.1⟩
  · have e : D.R.r = Dw.p + Dw.q := (h.unf c.F.val.toRingHom rfl).1
    omega
  · obtain ⟨Kf, th, hrk, hK, hth, hD, hu⟩ := h.dictU σ hσ
    exact det_eq_one _ hrk hr (U σ).X (dict σ) Kf th hth hD hu l.M l.three_le hK k γ hγ
  · obtain ⟨hrk, hM⟩ := h.modelW σ hσ
    obtain ⟨Kf, th, hrk', hK, hth, hD, hu⟩ := h.dictU σ hσ
    have key := GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional D.host.E H Dw l
      Xo c D.R.r (fun s => Formalism.L2.PjFree.Unf.ofPj (U s)) hr h.levA
      (fun s hs => (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf s hs)) σ hσ
      (fun k k' => ⟨(hM k).1.trans (hM k').1.symm, (hM k).2.trans (hM k').2.symm⟩)
      (fun k γ hγ hc0 => by
        have hc : ∀ x ∈ ((U σ).X k).Λ, ∃ y ∈ ((U σ).X k).Λ,
            Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x = (l.M : D.host.E) • y := by
          intro x hx
          obtain ⟨y, hy, e⟩ := hc0 x hx
          exact ⟨y, hy, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩
        obtain ⟨γ', hγ', u, m, hm, hum, he⟩ := GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _
          (Formalism.L2.PjFree.Unf.ofPj (U σ)) (h.unf σ hσ) h.levA hr k γ hγ hc
        have h1 := root_eq_one _ hrk' hr (U σ).X (dict σ) (fun _ => 1) Kf th hth hD
          ⟨fun _ _ => (one_mul _).symm, fun _ => norm_one, fun _ _ => rfl, hu⟩ _ l.three_le hK k γ γ' hγ' hc u m hm hum he
        rw [h1, one_smul] at he
        exact Units.ext he ▸ hγ')
      a n ha (fun τ _ h0 => hp τ _ (by omega)) hn (fun k => h.chiTriv σ hσ a n ha k)
    intro P hP
    exact key ⟨hP.1, hP.2⟩

end GlobalTheory.LevLaws
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsOfPrincipalLevelFieldOfDefinitionStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduliLaws_of_principalLevel_fieldOfDefinition : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, Formalism.L2.Theta.GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → FnAlgClosed (Xo := Xo) (c := c) → (∀ p : ℕ, p.Prime → l.GoodAt p) → Laws U (xiR D) ∧ GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H := by
  first | exact @GlobalTheory.LevLaws.laws_of_level | exact GlobalTheory.LevLaws.laws_of_level | (intros; apply GlobalTheory.LevLaws.laws_of_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaVanishing
noncomputable section

namespace GlobalTheory.ThetaFacInf.Fib

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F]

theorem rest_finPart {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hSB : ∀ v, φ v ∈ SB (κ → Fv F v))
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    Rest (evI F) (⇑f) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) := by
  refine ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
  have hz0 : ∀ v i, evFin F v (z i) = 0 := fun v i => by
    have h := congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i
    have h2 : (1 : Af F) * (z i).2 = 0 := congrArg Prod.snd h
    rw [one_mul] at h2
    rw [evFin, AlgHom.comp_apply]
    convert map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)
    exact h2
  simp only [Pi.add_apply, map_add (f := _), hz0, add_zero]

theorem hasDerivAt_pure {κ : Type} [Fintype κ] {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ}
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB (κ → Fv F v))
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (h : ActsD (evI F) T f f₁) :
    ∀ x, HasDerivAt (fun t => T t (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ x) 0 :=
  h _ (rest_finPart f φ hSB hstd)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

end GlobalTheory.ThetaFacInf.Fib

end

namespace GlobalTheory.ThetaFacInf.Fib

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

end GlobalTheory.ThetaFacInf.Fib
end
