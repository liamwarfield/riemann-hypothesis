module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightOfSizeBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSquareProductRouteBEqExternalProduct

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteKernelEqUnitNormMulTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteKernelEqUnitNormMulTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallKernel

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumB skewGram blkU conjU xiV xiV₁ boxB alpha beta)
open GlobalTheory.RouteSeesaw
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem end_finsupp_sum_apply {α β : Type} (A : Module.End ℂ (β → ℂ)) (Θ : α →₀ ℂ) (f : α → β → ℂ) (w : β) :
    A (fun x => Θ.sum fun d c => c * f d x) w = Θ.sum fun d c => c * A (f d) w := by
  have e : (fun x => Θ.sum fun d c => c * f d x) = ∑ d ∈ Θ.support, Θ d • f d := by
    funext x
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {χ χ' : (AF F ⊗[F] E)ˣ →* Circle} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') := by
  refine ⟨h.1.div' h'.1, fun x => ?_⟩
  simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem resEtaPow_div {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ χ' : Eˣ →* Circle} {n m : ℕ} (h : GlobalTheory.WeilM.ResEtaPow K χ n) (h' : GlobalTheory.WeilM.ResEtaPow K χ' m) :
    GlobalTheory.WeilM.ResEtaPow K (χ / χ') (m + n) := by
  intro a
  have e1 := h a
  have e2 := h' a
  simp only [MonoidHom.div_apply, Circle.coe_div] at *
  rw [e1, e2]
  split_ifs
  · simp
  · have hm : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    rw [div_eq_iff (by simp), add_comm, pow_add, mul_assoc, hm, mul_one]

theorem data_theta_small {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)}
    (hΘ : IsMatched B t ρ i j Θ Θ') : ∀ d ∈ Θ'.support,
      IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) d.2 := by
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, ⟨φ₁, φ₂, hloc, -⟩, -⟩, -, rfl⟩ := hΘ
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
  have v1 := (ρ.vT_is t (i : ℕ) (j : ℕ) i.2.le j.2).2.theta
  have v2 := (ρ.vX_is (i : ℕ) (j : ℕ) i.2 j.2.le).2.theta
  have t1 := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h1.2 v1
  have t2 := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h2.2 v2
  exact ⟨GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _,
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _⟩


set_option maxHeartbeats 1000000 in
theorem seesaw_swapped {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (t : T) (i j : Fin D.R.m) (S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin (spW₁ G i j).rank)
    (e₂ : Fin S'.rank ≃ Fin (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).rank)
    (hT' : T'.gramᵀ = -((spW₁ G i j).gram.submatrix e₁ e₁))
    (hS' : S'.gram⁻¹ = -((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ.submatrix e₂ e₂))
    (ω : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ))
    (hω : IsWeilDatumO W.ψ S' T' (alpha G t i j / beta G i j) (alpha G t i j) ω)
    (f₁ : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ) (f₂ : WO (G.pS (.chi i j)) (G.pT (.chi i j)) → ℂ)
    (hf₁ : IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) f₁)
    (hf₂ : IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) f₂)
    (g : GA D (spV G i j)) (u : GA D (spW₁ G i j)) (g₁ : GA D (spV₁ G i j)) (g' : GA D S') (h' : GA D T')
    (hh : Formalism.L2.Theta.mt T' h' = ((Formalism.L2.Theta.mt _ u).map (cA D)).submatrix e₁ e₁)
    (hg : Formalism.L2.Theta.mt S' g' = ((Formalism.L2.Theta.mt _ (GlobalTheory.SquareComm.blk _ _ (g, g₁))⁻¹).submatrix e₂ e₂)ᵀ) :
    W.kerA (.down t i j) f₁ g u * W.kerA (.right i j) f₂ u g₁ =
      xiV G i j g * xiV₁ G t i j g₁ * ω (g', h') (fun x => box2 f₁ (GlobalTheory.SeesawSmall.adjFn (spW₁ G i j) (spV₁ G i j) f₂)
        (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) ((spW₁ G i j).gram.map (incA D)) :
          Matrix (Fin (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).rank) (Fin (spW₁ G i j).rank) (AE D))) 0 := by
  have r₁ : T'.rank = (spW₁ G i j).rank := by simpa using Fintype.card_congr e₁
  have r₂ : S'.rank = (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).rank := by simpa using Fintype.card_congr e₂
  obtain ⟨ωA, hA⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D W.ψ W.ψ_std (spW₁ G i j)
    (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) (alpha G t i j) (alpha G t i j / beta G i j)
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hω.hecT hω.hecS (r₁ ▸ hω.resT) (r₂ ▸ hω.resS)
  obtain ⟨hbox, hker⟩ := GlobalTheory.SeesawSmall.seesaw_small hL W t i.2 j.2 ωA hA f₁ f₂ hf₁ hf₂
  rw [hker g u g₁, GlobalTheory.BigSeesaw.swap_eq _ _ S' T' e₁ e₂ hT' hS' hA hω hbox u _ g' h' hh hg]
  rfl


set_option maxHeartbeats 1000000 in
theorem kerSmall_eq_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∀ ΦB, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsDatumB W e Γ Θ' ΦB →
    ∃ ξ : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) j)) → ℂ, (∀ x, ‖ξ x‖ = 1) ∧
      ∀ g u, kerSmall W Θ' g g₁ u =
        ξ (g, g₁) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' ΦB (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (g, g₁)) := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv Φ hΦ
  refine ⟨fun x => xiV G i j x.1 * xiV₁ G t i j x.2, fun x => ?_, fun g u => ?_⟩
  · simp only [xiV, xiV₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.flatDet, norm_mul, Circle.norm_coe, mul_one]
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.WeilSchrodingerHerm.main D Bs hTr.base _ Γ.V' _ _ hTr.geo.hV'
  obtain ⟨hJ, LS, hLS, h4, h5, h6⟩ := GlobalTheory.WeilSchrodingerSkew.main D Bs hTr.base _ Γ.W _ _ hTr.geo.hW
  have hξ0 : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have eA : Γ.V'.J = (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat.toIsLattice h3 (fun _ => (0, 0))).gramᵀ := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]; exact (Matrix.transpose_transpose _).symm
  have e1 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
      inv_mul_cancel₀ (neg_ne_zero.2 hξ0), one_smul])
  have eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 •
      (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0))).gram⁻¹) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Γ.W.J = -Γ.W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ0, neg_one_smul]
    show (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (-D.host.xi0 • Γ.W.J⁻¹)⁻¹)
    rw [e1, e2]
    funext a b
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  obtain ⟨ω, hω, -, hth⟩ := GlobalTheory.WeilBridge.exists_theta_eq D Bs hTr.base
    (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0)))
    (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat.toIsLattice h3 (fun _ => (0, 0))) Γ.V' Γ.W _ _ _ _
    hTr.geo.hV' hTr.geo.hW eA eB
    Γ.M' hTr.geo.hM' X.α (X.α / X.β) hTr.chars.heckeα (isHecke_div hTr.chars.heckeα hTr.chars.heckeβ) hTr.chars.resα
    (resEtaPow_div hTr.chars.resα hTr.chars.resβ) om' hTr.weil'
  rw [h.ψ, h.α, h.β] at hω
  obtain ⟨g', h', hh', hg'⟩ := GlobalTheory.WeilSchrodinger.match_pair D
    (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0)))
    (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat.toIsLattice h3 (fun _ => (0, 0))) Γ.V'.J Γ.W.J (-1) eA eB
    (conjU (spW₁ G i j) (-1) h.JW₁ u) (blkU (spV G i j) (spV₁ G i j) e h.JWW (g, g₁))
  have key := hth _ _ g' h' hh' hg' Φ hΦ.1
  refine Eq.trans ?_ (congrArg (fun z => xiV G i j g * xiV₁ G t i j g₁ * z) key.symm)
  have htr : GlobalTheory.WeilSchrodinger.thetaTr D.host.F Γ.M'.co Bs.ψ Φ =
      fun w => Θ'.sum fun d c => c * boxB e d w := by
    funext w
    show GlobalTheory.WeilM.thetaSum D.host.F (Γ.M'.co.rho Bs.ψ w Φ) = _
    rw [h.ψ, hΦ.2 w]
    rfl
  refine Eq.trans ?_ (congrArg (fun f => xiV G i j g * xiV₁ G t i j g₁ * ω (g', h') f 0) htr.symm)
  refine Eq.trans ?_ (congrArg (fun z => xiV G i j g * xiV₁ G t i j g₁ * z)
    (end_finsupp_sum_apply (ω (g', h')) Θ' (boxB e) 0).symm)
  rw [kerSmall, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨t1, t2⟩ := data_theta_small W B ρ t i j hΘ d hd
  let e₂ : Fin ((spW G i j).rank + (spW₁ G i j).rank) ≃ Fin ((spV G i j).rank + (spV₁ G i j).rank) :=
    e.symm.trans finSumFinEquiv
  have hb : ∀ {R : Type} [CommRing R] (A : Matrix (Fin (spV G i j).rank) (Fin (spV G i j).rank) R)
      (B : Matrix (Fin (spV₁ G i j).rank) (Fin (spV₁ G i j).rank) R),
      (GlobalTheory.Doubling.blkMat finSumFinEquiv A B).submatrix e₂ e₂ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e A B := fun A B => by
    ext a b
    simp [GlobalTheory.Doubling.blkMat, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, e₂]
  have hJ' : Γ.W.J = D.host.xi0 • ((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂ := by
    refine h.JWW.trans (congrArg (D.host.xi0 • ·) ?_)
    rw [GlobalTheory.Doubling.gram_hsum, ← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose, ← hb]
    rfl
  have hT' : (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat.toIsLattice h3 (fun _ => (0, 0))).gramᵀ =
      -((spW₁ G i j).gram.submatrix (Equiv.refl _) (Equiv.refl _)) := by
    rw [← eA]
    show Γ.V'.J = -(spW₁ G i j).gram
    rw [h.JW₁, neg_one_smul]
  have hS' : (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0))).gram⁻¹ =
      -(((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    refine e1.trans ?_
    rw [hJ', smul_smul, inv_neg, neg_mul, inv_mul_cancel₀ hξ0, neg_one_smul]
  have k := seesaw_swapped hL W t i j
    (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0)))
    (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat.toIsLattice h3 (fun _ => (0, 0)))
    (Equiv.refl (Fin (spW₁ G i j).rank)) e₂ hT' hS' ω hω d.1.2 d.2 t1 t2 g u g₁
    g' h' hh' (by
      rw [hg', ← map_inv, Prod.inv_mk, GlobalTheory.SquareComm.mt_blk]
      exact congrArg transpose (hb (Formalism.L2.Theta.mt _ g⁻¹) (Formalism.L2.Theta.mt _ g₁⁻¹)).symm)
  refine (congrArg (fun z => Θ' d * z) k).trans ?_
  rw [mul_left_comm]
  refine congrArg (fun f => xiV G i j g * xiV₁ G t i j g₁ * (Θ' d * ω (g', h') f 0)) ?_
  funext x
  exact (GlobalTheory.SeesawSmall.thetaSquareProductRouteB_eq_externalProduct e d x).symm

end GlobalTheory.SmallKernel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteKernelEqUnitNormMulThetaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_route_kernel_eq_unit_norm_mul_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∀ ΦB, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsDatumB W e Γ Θ' ΦB →
    ∃ ξ : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) j)) → ℂ, (∀ x, ‖ξ x‖ = 1) ∧
      ∀ g u, kerSmall W Θ' g g₁ u =
        ξ (g, g₁) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' ΦB (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (g, g₁)) := by
  first | exact @GlobalTheory.SmallKernel.kerSmall_eq_theta | exact GlobalTheory.SmallKernel.kerSmall_eq_theta | (intros; apply GlobalTheory.SmallKernel.kerSmall_eq_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldBasisOfSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPowMulMemHermPairSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPowMulMemHermPairSections
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.ExtPow

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem compactSpace_of_projOver {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace Y := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem unitAt_zpow {z : X} {u : X.functionField} (h : UnitAt z u) (n : ℤ) : UnitAt z (u ^ n) := by
  have hu : u ≠ 0 := h.ne_zero
  induction n using Int.induction_on with
  | zero => rw [zpow_zero]; exact unitAt_one z
  | succ n ih => rw [zpow_add_one₀ hu]; exact ih.mul h
  | pred n ih => rw [zpow_sub_one₀ hu]; exact ih.mul h.inv

theorem loc_change (P : Pair p) (a b : ℤ) (f : X.functionField) (i i' : P.L.B.ι) (j j' : P.A.B.ι) :
    P.loc a b f i' j' = P.loc a b f i j *
      (((P.r i' : X.functionField) / P.r i) ^ a * ((P.r' j' : X.functionField) / P.r' j) ^ b) := by
  have h1 : (P.r i : X.functionField) ^ a ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  have h2 : (P.r' j : X.functionField) ^ b ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  simp only [Pair.loc, div_zpow]
  field_simp

theorem unitAt_quot (P : Pair p) (a b : ℤ) {z : X} {i i' : P.L.B.ι} {j j' : P.A.B.ι}
    (hi : z ∈ P.L.B.U i) (hi' : z ∈ P.L.B.U i') (hj : z ∈ P.A.B.U j) (hj' : z ∈ P.A.B.U j') :
    UnitAt z (((P.r i' : X.functionField) / P.r i) ^ a * ((P.r' j' : X.functionField) / P.r' j) ^ b) :=
  (unitAt_zpow (germOf_eq_iff.1 (P.hr.germOf_eq hi' hi)) a).mul
    (unitAt_zpow (germOf_eq_iff.1 (P.hr'.germOf_eq hj' hj)) b)

theorem loc_pow_mul (P : Pair p) (e a b : ℤ) (c : ℕ) (x f : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc (e * c + a) b (x ^ c * f) i j = P.loc e 0 x i j ^ c * P.loc a b f i j := by
  have h0 : (P.r i : X.functionField) ≠ 0 := Units.ne_zero _
  simp only [Pair.loc, zpow_zero, mul_one, zpow_add₀ h0, zpow_mul, zpow_natCast, mul_pow]
  ring

theorem exists_pow_mul_regAt {W : X.Opens} (hW : IsAffineOpen W) (s : Γ(X, W)) (hg : genericPoint X ∈ X.basicOpen s)
    {g : X.functionField} (h : ∀ z ∈ X.basicOpen s, RegAt z g) :
    ∃ N : ℕ, ∀ z ∈ W, RegAt z (fnOf W (X.basicOpen_le s hg) s ^ N * g) := by
  obtain ⟨a, ha⟩ := exists_fnOf_eq hg h
  have := hW.isLocalization_basicOpen s
  obtain ⟨⟨b, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) a
  obtain ⟨N, hN⟩ := m.2
  refine ⟨N, fun z hz => ?_⟩
  have e := congrArg (fnOf _ hg) hm
  simp only [map_mul] at e
  change fnOf _ hg a * fnOf _ hg (resG X (X.basicOpen_le s) (m : Γ(X, W))) =
    fnOf _ hg (resG X (X.basicOpen_le s) b) at e
  rw [fnOf_resG, fnOf_resG, ha, ← hN, map_pow] at e
  rw [mul_comm, e]
  exact regAt_fnOf hz _ b

end GlobalTheory.HSAmp.ExtPow


open GlobalTheory.HSAmp.ExtPow in
theorem GlobalTheory.HSAmp.eventually_pow_mul_mem_H : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e a b : ℤ) (x f : X.functionField), x ∈ P.H e 0 → x ≠ 0 → (∀ z ∈ NV P e 0 x, ∀ i j, z ∈ P.L.B.U i → z ∈ P.A.B.U j → RegAt z (P.loc a b f i j)) → ∀ᶠ c : ℕ in atTop, x ^ c * f ∈ P.H (e * c + a) b := by
  intro k _ X _ p D hD P e a b x f hx hx0 hf
  haveI : CompactSpace X := compactSpace_of_projOver hD.isProjOver
  have loc_ok : ∀ z : X, ∃ W : X.Opens, z ∈ W ∧ ∃ N : ℕ, ∀ c : ℕ, N ≤ c → ∀ w ∈ W, ∀ i j, w ∈ P.L.B.U i →
      w ∈ P.A.B.U j → RegAt w (P.loc (e * c + a) b (x ^ c * f) i j) := by
    intro z
    obtain ⟨i, hi⟩ := exists_chart P.L.isLB z
    obtain ⟨j, hj⟩ := exists_chart P.A.isLB z
    obtain ⟨W, hW, hzW, hWle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show z ∈ P.L.B.U i ⊓ P.A.B.U j from ⟨hi, hj⟩)
    have hgW : genericPoint X ∈ W := gen_mem hzW
    have hsW : ∀ w ∈ W, RegAt w (P.loc e 0 x i j) := fun w hw => hx w i j (hWle hw).1 (hWle hw).2
    obtain ⟨s, hs⟩ := exists_fnOf_eq hgW hsW
    have hbas : ∀ w ∈ X.basicOpen s, w ∈ NV P e 0 x := by
      intro w hw i' j' hi' hj'
      have hwW := X.basicOpen_le s hw
      have hu : UnitAt w (P.loc e 0 x i j) := hs ▸ (unitAt_fnOf_iff hwW hgW s).2 hw
      rw [loc_change P e 0 x i i' j j']
      exact hu.mul (unitAt_quot P e 0 (hWle hwW).1 hi' (hWle hwW).2 hj')
    have hne : P.loc e 0 x i j ≠ 0 :=
      mul_ne_zero (mul_ne_zero hx0 (zpow_ne_zero _ (Units.ne_zero _))) (zpow_ne_zero _ (Units.ne_zero _))
    have hg0 : genericPoint X ∈ X.basicOpen s := by
      have hu : UnitAt (genericPoint X) (fnOf W hgW s) := by rw [hs]; exact unitAt_genericPoint hne
      exact (unitAt_fnOf_iff hgW hgW s).1 hu
    obtain ⟨N, hN⟩ := exists_pow_mul_regAt hW s hg0 (g := P.loc a b f i j) fun w hw =>
      hf w (hbas w hw) i j (hWle (X.basicOpen_le s hw)).1 (hWle (X.basicOpen_le s hw)).2
    refine ⟨W, hzW, N, fun c hc w hw i' j' hi' hj' => ?_⟩
    rw [loc_change P (e * c + a) b (x ^ c * f) i i' j j', loc_pow_mul, ← hs]
    refine RegAt.mul ?_ (unitAt_quot P _ b (hWle hw).1 hi' (hWle hw).2 hj').regAt
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
    have hd := regAt_fnOf hw hgW (s ^ d)
    rw [map_pow] at hd
    rw [pow_add, mul_comm (_ ^ N) (_ ^ d), mul_assoc]
    exact hd.mul (hN w hw)
  choose W hzW N hN using loc_ok
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun z => (W z : Set X)) (fun z => (W z).isOpen)
    (fun z _ => Set.mem_iUnion.2 ⟨z, hzW z⟩)
  refine eventually_atTop.2 ⟨t.sup N, fun c hc w i j hi hj => ?_⟩
  obtain ⟨z, hz, hwz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ w))
  exact hN z c ((Finset.le_sup hz).trans hc) w hwz i j hi hj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPowMulMemHermPairSectionsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_pow_mul_mem_hermPairSections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e a b : ℤ) (x f : X.functionField), x ∈ P.H e 0 → x ≠ 0 → (∀ z ∈ NV P e 0 x, ∀ i j, z ∈ P.L.B.U i → z ∈ P.A.B.U j → RegAt z (P.loc a b f i j)) → ∀ᶠ c : ℕ in atTop, x ^ c * f ∈ P.H (e * c + a) b := by
  first | exact @GlobalTheory.HSAmp.eventually_pow_mul_mem_H | exact GlobalTheory.HSAmp.eventually_pow_mul_mem_H | (intros; apply GlobalTheory.HSAmp.eventually_pow_mul_mem_H <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldBasisOfSections
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.FBasis

theorem exists_ne_zero_mem_H (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsArithVar p D) (P : Pair p) (hL : IsAmpleLB P.L.B) (e : ℕ) (he : 0 < e) (a b : ℤ) :
    ∃ (c : ℕ) (γ : X.functionField), γ ≠ 0 ∧ γ ∈ P.H ((e : ℤ) * c + a) b := by
  obtain ⟨M, hM⟩ := Pair.exists_rep k X p P a b
  have hLe : IsAmpleLB (P.L.pow e).B := (isAmpleLB_pow_iff hL.isLB he).2 hL
  obtain ⟨c, -, u, hu⟩ := exists_sec_finite_subset_nonzeroLocus k X p D hX M (P.L.pow e) hLe {genericPoint X}
    (Set.finite_singleton _)
  have h1 := (Pair.rep_base k X p P).1
  have h2 := Pair.rep_pow k X p P 1 0 P.L e h1
  have h3 := Pair.rep_pow k X p P _ _ _ c h2
  have hN := Pair.rep_tens k X p P a b _ _ M _ hM h3
  have e1 : a + (c : ℤ) * ((e : ℤ) * 1) = (e : ℤ) * c + a := by ring
  have e2 : b + (c : ℤ) * ((e : ℤ) * 0) = b := by ring
  rw [e1, e2] at hN
  obtain ⟨f, -, hrange, -, hloc⟩ := RepDict.rep_dict k X p P _ _ _ hN
  have hmem : f u ∈ P.H ((e : ℤ) * c + a) b := by
    have : f u ∈ Set.range f := Set.mem_range_self u
    rw [hrange] at this
    exact this
  obtain ⟨i, hi⟩ : ∃ i, genericPoint X ∈ P.L.B.U i :=
    Opens.mem_iSup.1 (P.L.isLB.cover.ge (Opens.mem_top _))
  obtain ⟨j, hj⟩ : ∃ j, genericPoint X ∈ P.A.B.U j :=
    Opens.mem_iSup.1 (P.A.isLB.cover.ge (Opens.mem_top _))
  have hU := (hloc u (genericPoint X) i j hi hj).1 (hu rfl)
  refine ⟨c, f u, fun h0 => ?_, hmem⟩
  rw [h0] at hU
  have z : P.loc ((e : ℤ) * c + a) b 0 i j = 0 := by simp [Pair.loc]
  rw [z] at hU
  have hz : ∀ x : X, ¬ UnitAt x (0 : X.functionField) := by
    rintro x ⟨w, hw, h⟩
    exact (hw.map (algebraMap _ X.functionField)).ne_zero h
  exact hz _ hU

theorem exists_linearIndependent_of_frac {K : Type} [Field K] (F : Subfield K) [FiniteDimensional F K] (R : Subring K)
    (hR : ∀ w : K, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ w = a / b) :
    ∃ β : Fin (Module.finrank F K) → K, (∀ i, β i ∈ R) ∧ LinearIndependent F β := by
  have hS : Algebra.adjoin F (R : Set K) = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨a, ha, b, hb, hb0, rfl⟩ := hR w
    have hbS : b ∈ Algebra.adjoin F (R : Set K) := Algebra.subset_adjoin hb
    have hinv : b⁻¹ ∈ Algebra.adjoin F (R : Set K) :=
      (Algebra.adjoin F (R : Set K)).inv_mem_of_algebraic (x := ⟨b, hbS⟩) (Algebra.IsAlgebraic.isAlgebraic (b : K))
    rw [div_eq_mul_inv]
    exact mul_mem (Algebra.subset_adjoin ha) hinv
  have hspan : Submodule.span F (R : Set K) = ⊤ := by
    have := congrArg Subalgebra.toSubmodule hS
    rw [Algebra.adjoin_eq_span, Algebra.top_toSubmodule] at this
    have hc : (Submonoid.closure (R : Set K) : Set K) = (R : Set K) := by
      exact congrArg (fun s : Submonoid K => (s : Set K)) (Submonoid.closure_eq R.toSubmonoid)
    rw [hc] at this
    exact this
  obtain ⟨s, hsR, hsspan, hli⟩ := exists_linearIndependent F (R : Set K)
  rw [hspan] at hsspan
  let B : Module.Basis s F K := Module.Basis.mk hli (by rw [Subtype.range_coe, hsspan])
  let E : s ≃ Fin (Module.finrank F K) := B.indexEquiv (Module.finBasis F K)
  refine ⟨fun i => (E.symm i : K), fun i => hsR (E.symm i).2, ?_⟩
  exact hli.comp _ E.symm.injective

end GlobalTheory.HSAmp.FBasis

namespace GlobalTheory.HSAmp

theorem exists_linearIndependent_mem_H : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField),
    Gens P D e x → ∀ a b : ℤ, ∃ (c : ℕ) (g : Fin (Module.finrank (ratF x) X.functionField) → X.functionField),
    (∀ i, g i ∈ P.H (e * c + a) b) ∧ LinearIndependent (ratF x) g := by
  intro k _ X _ p D hX P hL e x hx a b
  obtain ⟨hne, -, hfin⟩ := GlobalTheory.T.sectionQuotients_transcendenceBasis_basepointFree k X p D hX P hL e x hx
  obtain ⟨U, hU, hUe, -, hreg, -, hfrac, -⟩ :=
    GlobalTheory.T.nonvanishingLocus_ample_section_isAffine_model k X p D hX P hL e (x 0) hx.pos (hx.mem 0) (hne 0)
  obtain ⟨β, hβR, hβ⟩ := FBasis.exists_linearIndependent_of_frac (ratF x) (fnOf U hU).range hfrac
  obtain ⟨c₁, γ, hγ0, hγ⟩ := FBasis.exists_ne_zero_mem_H k X p D hX P hL e hx.pos a b
  have hext : ∀ i, ∀ᶠ c : ℕ in atTop, x 0 ^ c * β i ∈ P.H ((e : ℤ) * c + 0) 0 := by
    intro i
    refine GlobalTheory.T.eventually_pow_mul_mem_hermPairSections k X p D hX P e 0 0 (x 0) (β i) (hx.mem 0) (hne 0) fun z hz i' j _ _ => ?_
    have e0 : P.loc 0 0 (β i) i' j = β i := by simp [Pair.loc]
    rw [e0]
    refine (hreg (β i)).2 (hβR i) z ?_
    rw [← SetLike.mem_coe, hUe]
    exact hz
  obtain ⟨c₂, hc₂⟩ := (Filter.eventually_all.2 hext).exists
  refine ⟨c₁ + c₂, fun i => γ * x 0 ^ c₂ * β i, fun i => ?_, ?_⟩
  · have h := (NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ γ (x 0 ^ c₂ * β i) hγ (hc₂ i)).1
    have e1 : (e : ℤ) * c₁ + a + ((e : ℤ) * c₂ + 0) = (e : ℤ) * ((c₁ + c₂ : ℕ) : ℤ) + a := by
      push_cast; ring
    rw [e1, add_zero, ← mul_assoc] at h
    exact h
  · have ht : γ * x 0 ^ c₂ ≠ 0 := mul_ne_zero hγ0 (pow_ne_zero _ (hne 0))
    exact hβ.map' (LinearMap.mulLeft (ratF x) (γ * x 0 ^ c₂))
      (LinearMap.ker_eq_bot.2 (mul_right_injective₀ ht))

end GlobalTheory.HSAmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldBasisOfSectionsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_functionField_basis_of_sections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ a b : ℤ, ∃ (c : ℕ) (g : Fin (Module.finrank (ratF x) X.functionField) → X.functionField), (∀ i, g i ∈ P.H (e * c + a) b) ∧ LinearIndependent (ratF x) g := by
  first | exact @GlobalTheory.HSAmp.exists_linearIndependent_mem_H | exact GlobalTheory.HSAmp.exists_linearIndependent_mem_H | (intros; apply GlobalTheory.HSAmp.exists_linearIndependent_mem_H <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFieldDataAbelian
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ThmAUpper.Read

theorem exists_pow_of_two_emb {L K : Type} [Field L] [Field K] (f g : L →+* K) {l : ℕ} (hl : l.Prime) (n : ℕ) :
    ∃ c : ℤ, IsCoprime c (l : ℤ) ∧ ∀ y : L, y ^ (l ^ n) = 1 → g y = f y ^ c := by
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := rootsOfUnity (l ^ n) L)
  have key : ∀ c : ℤ, g ((z : Lˣ) : L) = f ((z : Lˣ) : L) ^ c → ∀ y : L, y ^ (l ^ n) = 1 → g y = f y ^ c := by
    intro c hc y hy
    obtain ⟨k, hk⟩ := hz (rootsOfUnity.mkOfPowEq y hy)
    have e : y = ((z : Lˣ) : L) ^ k := by
      have := congrArg (fun t : rootsOfUnity (l ^ n) L => ((t : Lˣ) : L)) hk
      simpa using this.symm
    rw [e, map_zpow₀, map_zpow₀, hc, ← zpow_mul, ← zpow_mul, mul_comm]
  have h1 : ((z : Lˣ) : L) ^ (l ^ n) = 1 := by
    have := z.2
    rw [mem_rootsOfUnity'] at this
    exact this
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hl).1 (orderOf_dvd_of_pow_eq_one h1)
  have hp : IsPrimitiveRoot ((z : Lˣ) : L) (l ^ m) := hm ▸ IsPrimitiveRoot.orderOf _
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have e : ((z : Lˣ) : L) = 1 := by simpa using hp
    exact ⟨1, isCoprime_one_left, key 1 (by simp [e])⟩
  · have : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
    obtain ⟨i, -, hi, e⟩ := ((hp.map_of_injective f.injective).isPrimitiveRoot_iff).1 (hp.map_of_injective g.injective)
    refine ⟨i, Nat.isCoprime_iff_coprime.2 ((Nat.coprime_pow_right_iff hm0 _ _).1 hi), key i ?_⟩
    rw [zpow_natCast, e]

theorem exists_extend {A B K : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    [Field K] [IsAlgClosed K] (hi : Function.Injective (algebraMap A B)) (f : A →+* K) (hf : Function.Injective f) :
    ∃ g : FractionRing B →+* K, ∀ a, g (algebraMap B _ (algebraMap A B a)) = f a := by
  letI := f.toAlgebra
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
  let J0 : B →ₐ[A] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hJ : Function.Injective J0.toRingHom := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := A) ?_
    rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    intro a b hab
    exact hf ((J0.commutes a).symm.trans (Eq.trans hab (J0.commutes b)))
  exact ⟨IsFractionRing.lift hJ, fun a => by rw [IsFractionRing.lift_algebraMap]; exact J0.commutes a⟩

theorem isClassTerm_reindex {E : Type} [Field E] [NumberField E] {I I' : Type} [Fintype I] [Fintype I'] (e : I' ≃ I)
    {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {c : Ideal (OF E)} {χ : HChar E} {y : (Af E)ˣ} {T : ℂ}
    (h : GlobalTheory.ToricDenom.IsClassTerm φ s κ c χ y T) : GlobalTheory.ToricDenom.IsClassTerm (φ ∘ e) s (κ ∘ e) c χ y T := by
  obtain ⟨S, hS, hT⟩ := h
  refine ⟨S, ⟨hS.1, fun σ hσ => ?_⟩, hT⟩
  have : ∀ x, term (φ ∘ e) (2 * s) (κ ∘ e) σ x = term φ (2 * s) κ σ x := fun x =>
    Fintype.prod_equiv e _ _ fun _ => rfl
  simp only [this]
  exact hS.2 σ hσ


open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum GlobalTheory.ToricDenom in
theorem cond0_eq {D : D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc)
    (hb : IsBaseCond (condF G.pl)) : GlobalTheory.LamTie.cond0 D.host (G.pl.w G.pl.v0) = condF G.pl := by
  classical
  have hw0 : below (G.pl.w G.pl.v0) = G.pl.v0 := G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  have hv0 := G.ch.basePlace_not_mem_chiGridBadPlaces
  rw [S1_mem_OmF] at hv0
  simp only [not_or] at hv0
  have hdvd : ∀ v ∈ G.pl.S0, v.asIdeal ∣ condF G.pl := fun v hv =>
    (dvd_pow_self _ (by unfold condExp; split_ifs <;> omega)).trans (Finset.dvd_prod_of_mem _ hv)
  have good : ∀ p : ℕ, p.Prime → ∀ v ∈ G.pl.S0, (p : 𝓞 D.host.F) ∈ v.asIdeal → p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr D.host.E ∧
      ∀ P : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = p := by
    intro p hp v hv hpv
    obtain ⟨-, -, l, hl, h2, h3, h4, h5⟩ := hb.2.2 v (hdvd v hv)
    obtain rfl : l = p := prime_unique (K := D.host.F) hl hp h3 hpv
    exact ⟨hl, h2, h4, h5⟩
  have ex : ∀ p : ℕ, p.Prime → ∃ v : HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal := by
    intro p hp
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    obtain ⟨Q, hQ, hv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.F) (Ideal.span {(p : ℤ)})
    have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p : ℤ)}) (by simpa using hp.ne_zero) Q
    refine ⟨⟨Q, hQ.isPrime, hne⟩, ?_⟩
    have h1 : (p : ℤ) ∈ Q.under ℤ := hv.over ▸ Ideal.mem_span_singleton_self _
    rw [Ideal.under_def, Ideal.mem_comap] at h1
    simpa using h1
  have hP : GlobalTheory.LamTie.PlacesOk D.host (q0 D) (G.pl.w G.pl.v0) := by
    refine ⟨?_, ?_, fun p hp => ?_⟩
    · refine (FieldDatPf.natCast_mem_below _ _).1 ?_
      rw [hw0]; exact G.pl.basePlace_over_qZero
    · have a1 := D.host.g_ne
      have a2 := D.host.pde_ne
      have a3 := D.host.pde_ne_g 0
      have a4 := D.host.pde_ne_g 1
      have a5 : q0 D ≠ D.host.g 0 := fun e => hv0.1 (e ▸ G.pl.basePlace_over_qZero)
      have a6 : q0 D ≠ D.host.g 1 := fun e => hv0.2.1 (e ▸ G.pl.basePlace_over_qZero)
      have a7 := leastSplitAuxiliaryPrime_ne_typePrimes D
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, not_false_eq_true,
        and_true]
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · obtain ⟨v, hv⟩ := ex _ (D.host.g_prime 0)
        exact good _ (D.host.g_prime 0) v (G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 (Or.inl hv)))) hv
      · obtain ⟨v, hv⟩ := ex _ (D.host.g_prime 1)
        exact good _ (D.host.g_prime 1) v (G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 (Or.inr (Or.inl hv))))) hv
      · obtain ⟨v, hv⟩ := ex _ D.host.pde_prime
        exact good _ D.host.pde_prime v (G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 (Or.inr (Or.inr (Or.inl hv)))))) hv
      · obtain ⟨v, hv⟩ := ex _ D.host.pde'_prime
        exact good _ D.host.pde'_prime v (G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 (Or.inr (Or.inr (Or.inr hv)))))) hv
      · exact good _ (leastSplitAuxiliaryPrimeThetaChain_spec D).1 _ (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)) G.pl.basePlace_over_qZero
  have hexp : ∀ v : HeightOneSpectrum (OF D.host.E),
      expIn (GlobalTheory.LamTie.cond0 D.host (G.pl.w G.pl.v0)) v = expIn (condF G.pl) v := by
    intro v
    obtain ⟨w, rfl⟩ := FieldDatPf.exists_above v
    obtain ⟨h2, h1, h0⟩ := GlobalTheory.LamTie.expIn_cond0 D.R D.host _ _ hP w
    have h4 : GlobalTheory.LamTie.Over4 D.host w ↔ below w ∈ S1 D := by
      rw [S1_mem_OmF, GlobalTheory.LamTie.Over4, Fin.exists_fin_two, or_assoc]
      exact or_congr (FieldDatPf.natCast_mem_below w _).symm (or_congr (FieldDatPf.natCast_mem_below w _).symm
        (or_congr (FieldDatPf.natCast_mem_below w _).symm (FieldDatPf.natCast_mem_below w _).symm))
    rw [hw0] at h1 h0
    refine Eq.trans ?_ (FieldDatPf.expIn_condF' G.pl (below w)).symm
    by_cases e : below w = G.pl.v0
    · rw [(h1 e).2, if_pos (G.pl.mem_S0_of_sum_eq.2 (Or.inl e)), condExp, if_pos e]
    · by_cases e' : below w ∈ S1 D
      · rw [h2 (h4.2 e'), if_pos (G.pl.mem_S0_of_sum_eq.2 (Or.inr e')), condExp, if_neg e]
      · rw [h0 (fun h => e' (h4.1 h)) e, if_neg fun h => (G.pl.mem_S0_of_sum_eq.1 h).elim e e']
  have hne : GlobalTheory.LamTie.cond0 D.host (G.pl.w G.pl.v0) ≠ ⊥ := by
    refine mul_ne_zero (pow_ne_zero _ ?_) (below _).ne_bot
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    have := (D.host.g_prime 0).pos
    have := (D.host.g_prime 1).pos
    have := D.host.pde_prime.pos
    have := D.host.pde'_prime.pos
    positivity
  rw [← Ideal.finprod_heightOneSpectrum_pow_multiplicity hne, ← Ideal.finprod_heightOneSpectrum_pow_multiplicity hb.1]
  exact finprod_congr fun v => congrArg _ (hexp v)

section Record

open GlobalTheory.ToricDenom GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {i : X.Tw}
  {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))}

theorem thEval_eq_twisted {k : ℕ} {ψ : X.RCG i Q →* (X.Ok i k)ˣ} {ι : ℂ →+* Kbar X i}
    {J : FractionRing (X.Ok i k) →+* Kbar X i}
    (hJ : ∀ x, J (BlochKatoReduction.Gen.kMap X i k x) = algebraMap (FractionRing (X.O i)) (Kbar X i) x)
    {I : Type} [Fintype I] {φ : I → D.host.E →+* ℂ} {s : ℕ} {κ : I → ℕ} {c : Ideal (OF D.host.E)}
    {χ : HChar D.host.E} {lam : X.abelian₂ i} {u : Kbar X i} [Finite (PicO c)] {π : PicO c →* X.RCG i Q} {T : PicO c → ℂ}
    {θ : PicO c →* ℂˣ} (hθ : ∀ q, ι (θ q) = J (algebraMap (X.Ok i k) _ (ψ (π q) : X.Ok i k)))
    (hT : ∀ q, IsClassTerm φ s κ c χ q.out (T q))
    (hδ : ∀ δ, algebraMap (FractionRing (X.O i)) (Kbar X i) (X.th i Q lam δ) = u * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q))
    {t : ℂ} (ht : IsTwistedSum φ s κ c χ θ t) : J (BlochKatoReduction.Gen.thEval X i Q lam k ψ) = u * ι t := by
  classical
  have := Fintype.ofFinite (PicO c)
  have e : t = ∑ q, T q * (θ q⁻¹ : ℂ) := by
    choose S hS hTq using hT
    refine ht.unique ⟨inferInstance, S, hS, ?_⟩
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hTq, map_inv, Units.val_inv_eq_inv_val, lamF]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, ← Finset.sum_fiberwise Finset.univ (fun q => π q⁻¹), map_sum, Finset.mul_sum, BlochKatoReduction.Gen.thEval, map_sum]
  refine Finset.sum_congr rfl fun δ _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, hJ, hδ, show {q | π q⁻¹ = δ} = ↑(Finset.univ.filter fun q => π q⁻¹ = δ) by ext; simp,
    finsum_mem_coe_finset, map_sum, map_sum, mul_assoc, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun q hq => by rw [map_mul, hθ, (Finset.mem_filter.1 hq).2]

theorem sum_th_eq {ι : ℂ →+* Kbar X i}
    {I : Type} [Fintype I] {φ : I → D.host.E →+* ℂ} {s : ℕ} {κ : I → ℕ} {c : Ideal (OF D.host.E)}
    {χ : HChar D.host.E} {lam : X.abelian₂ i} {u : Kbar X i} [Finite (PicO c)] {π : PicO c →* X.RCG i Q} {T : PicO c → ℂ}
    (hT : ∀ q, IsClassTerm φ s κ c χ q.out (T q))
    (hδ : ∀ δ, algebraMap (FractionRing (X.O i)) (Kbar X i) (X.th i Q lam δ) = u * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q))
    {t : ℂ} (ht : IsToricSum φ s κ c χ t) :
    algebraMap (FractionRing (X.O i)) (Kbar X i) (∑ δ, X.th i Q lam δ) = u * ι t := by
  obtain ⟨J, hJ⟩ := GlobalTheory.ToricDistribution.exists_emb X i 0
  have h := thEval_eq_twisted (ψ := 1) (θ := 1) hJ (fun q => by simp) hT hδ (t := t)
    (by simpa [IsTwistedSum, IsToricSum, lamF] using ht)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h, ← hJ, BlochKatoReduction.Gen.thEval, map_sum]
  simp

end Record


open GlobalTheory.ToricDenom in
theorem exists_pow_char {D : D7} {C : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {Tp : Formalism.L2.Host.TupTied D C nch}
    (hψ : Formalism.L2.Host.PsiChoiceCompatible D C nch Tp) {w : D.what₂.places.Pl} (hw : TwistedAt D w)
    (hval : (Tp.psi w).ValuesIn 0 D.what₂.embLL) (ι : ℂ →+* Kbar D.ntw (nch.twI w))
    (J : FractionRing (D.ntw.Ok (nch.twI w) (nch.k' w)) →+* Kbar D.ntw (nch.twI w)) :
    ∃ e : ℤ, IsCoprime e (D.ntw.l (nch.twI w) : ℤ) ∧ ∀ {c : Ideal (OF D.host.E)}, c ≠ ⊥ →
      ∀ π : PicO c →* D.ntw.RCG (nch.twI w) (nch.Q w), IsRecMap D.ntw (nch.twI w) (nch.Q w) π → ∀ y : (Af D.host.E)ˣ,
        ι ((finPart (Tp.psi w) y ^ e : ℂˣ) : ℂ) = J (algebraMap (D.ntw.Ok (nch.twI w) (nch.k' w)) _
          (nch.psi' w (π (QuotientGroup.mk y)) : D.ntw.Ok (nch.twI w) (nch.k' w))) := by
  classical
  have hl := (D.ntw.lPrime (nch.twI w)).out
  have := nch.Oe_fin w
  obtain ⟨g, hg⟩ := exists_extend (nch.Oe_inj w) (J.comp (algebraMap (D.ntw.Ok (nch.twI w) (nch.k' w)) _))
    (J.injective.comp (IsFractionRing.injective _ _))
  obtain ⟨n, hn⟩ := GlobalTheory.ToricDistribution.exists_exponent D.ntw (nch.twI w) (nch.Q w)
  obtain ⟨e, he, hpow⟩ := exists_pow_of_two_emb (ι.comp D.what₂.embLL) (g.comp (nch.embW w)) hl n
  obtain ⟨r, hr⟩ := GlobalTheory.ToricDistribution.exists_complex_char ι
    ((Units.map (J.comp (algebraMap (D.ntw.Ok (nch.twI w) (nch.k' w)) _)).toMonoidHom).comp (nch.psi' w))
    (pow_ne_zero n hl.ne_zero) fun x => by rw [← map_pow, hn, map_one]
  refine ⟨e, he, fun {c} hc π hπ y => ?_⟩
  have key := GlobalTheory.ToricDistribution.pic_char_eq_finPart hc (r.comp π) (Tp.psi w ^ e) (D.ntw.S0 (nch.twI w) ∪ nch.Q w)
    (fun P hP => ?_) y
  · have e1 : finPart (Tp.psi w ^ e) y = finPart (Tp.psi w) y ^ e := rfl
    rw [← e1, ← key]
    exact hr _
  rw [Finset.mem_union, not_or] at hP
  have hu : (Tp.psi w).UnrAt P := ((Tp.psi_is w hw).ram P).2 hP.2
  refine ⟨fun x hx => ?_, ?_⟩
  · show (Tp.psi w).loc P x ^ e = 1
    rw [hu x hx, one_zpow]
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob (D.nd.plOm.2 P)
  obtain ⟨y0, hy0⟩ := hval P hu
  have hy1 : D.what₂.embLL y0⁻¹ = (((Tp.psi w).val P)⁻¹ : ℂˣ).1 := by
    rw [map_inv₀, hy0, Units.val_inv_eq_inv_val]
    simp [Formalism.L2.Host.HChar.valTw]
  have h1 := hψ w hw P hP.2 (fun h => hP.1 (D.ntw.twistExcludedPlaces_contains_residueChar _ (by rw [nch.twI_l]; exact h))) _ σ (D.nd.plOm.2 P) hσ _ hy1
  have h2 : g (nch.embW w y0⁻¹) = ι (r (D.ntw.art (nch.twI w) (nch.Q w) σ)) := by
    rw [h1, hg, hr]; rfl
  have h3 : y0⁻¹ ^ (D.ntw.l (nch.twI w) ^ n) = 1 := by
    apply (g.comp (nch.embW w)).injective
    rw [map_pow, map_one, RingHom.comp_apply, h2, ← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, hn, map_one,
      Units.val_one, map_one]
  have h4 := hpow _ h3
  rw [RingHom.comp_apply, RingHom.comp_apply, h2, hy1, ← map_zpow₀, ← Units.val_zpow_eq_zpow_val] at h4
  have h5 := Units.ext (ι.injective h4)
  rw [MonoidHom.comp_apply, hπ P hP.1 hP.2 σ hσ, map_inv, h5, inv_zpow, inv_inv]
  rfl

end GlobalTheory.ThmAUpper.Read

namespace GlobalTheory.ThmAUpper


end GlobalTheory.ThmAUpper
end
end
