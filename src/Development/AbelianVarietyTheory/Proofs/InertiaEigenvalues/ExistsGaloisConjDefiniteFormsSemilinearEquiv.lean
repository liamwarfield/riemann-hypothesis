module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatricesIntegralOfMemCompletedLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeOfFrameMatrixIntegral
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.ConjTwist

open GlobalTheory.CoefModel

theorem bc_invTr {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {N : ℕ} (g : GL (Fin N) A) :
    Formalism.UG.bc φ (inside₂ A N g) = inside₂ B N (Formalism.UG.bc φ g) := by
  apply Units.ext
  ext a b
  show φ (((g⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) b a) = (((Formalism.UG.bc φ g)⁻¹ : GL (Fin N) B) : Matrix (Fin N) (Fin N) B) b a
  rw [← map_inv]
  rfl

theorem mapVV_rhoVr {E K : Type} [Field E] [Field K] {ι : Type} [Fintype ι] {n : ℕ} (φ : K →+* ℂ)
    (emb : ι → E →+* K) (lam : ι → DomWeight n) (γ : GL (Fin n) E) (x : VV K lam) :
    mapVV φ lam (rhoVr emb lam γ x) = rhoVr (fun τ => φ.comp (emb τ)) lam γ (mapVV φ lam x) := by
  have h := mapVV_rhoK φ lam (invTrK (embGL emb γ)) x
  refine h.trans (congrArg (fun g : ι → GL (Fin n) ℂ => rhoK lam g (mapVV φ lam x)) ?_)
  funext τ
  show Formalism.UG.bc φ (inside₂ K n (Formalism.UG.bc (emb τ) γ)) = inside₂ ℂ n (Formalism.UG.bc (φ.comp (emb τ)) γ)
  rw [bc_invTr]
  congr 1

end GlobalTheory.ConjTwist

namespace GlobalTheory.ConjTwist

open GlobalTheory.CoefModel

def conjVV {ι : Type} [Fintype ι] {n : ℕ} (τ : ℂ ≃+* ℂ) (lam : ι → DomWeight n) : VV ℂ lam ≃+ VV ℂ lam where
  toFun := mapVV (τ : ℂ →+* ℂ) lam
  invFun := mapVV (τ.symm : ℂ →+* ℂ) lam
  left_inv x := Subtype.ext (by
    have e : (τ.symm : ℂ →+* ℂ).comp (τ : ℂ →+* ℂ) = RingHom.id ℂ := by ext z; simp
    rw [mapVV_coe, mapVV_coe, MvPolynomial.map_map, e, MvPolynomial.map_id])
  right_inv x := Subtype.ext (by
    have e : (τ : ℂ →+* ℂ).comp (τ.symm : ℂ →+* ℂ) = RingHom.id ℂ := by ext z; simp
    rw [mapVV_coe, mapVV_coe, MvPolynomial.map_map, e, MvPolynomial.map_id])
  map_add' x y := map_add _ x y

theorem post_mem {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* G)
    (ρ : Γ →* Module.End ℂ W) {J J' : Subgroup G} (hJ : J' = J) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (τ : ℂ ≃+* ℂ) (T : W →+ W)
    (hs : ∀ (a : ℂ) w, T (a • w) = τ a • T w) (hρ : ∀ γ w, T (ρ γ w) = ρ γ (T w))
    (hχ : ∀ k (hk : k ∈ J) (hk' : k ∈ J'), ((χ' ⟨k, hk'⟩ : ℂˣ) : ℂ) = τ ((χ ⟨k, hk⟩ : ℂˣ) : ℂ))
    {F : G → W} (hF : F ∈ Bridge.AdForms ι ρ J χ) : (fun g => T (F g)) ∈ Bridge.AdForms ι ρ J' χ' := by
  intro γ h k
  have hk : (k : G) ∈ J := hJ ▸ k.2
  have e := hF γ h ⟨k, hk⟩
  show T (F (ι γ * h * (k : G))) = ((χ' k : ℂˣ) : ℂ) • ρ γ (T (F h))
  have e' : F (ι γ * h * (k : G)) = ((χ ⟨k, hk⟩ : ℂˣ) : ℂ) • ρ γ (F h) := e
  rw [e', hs, hρ, ← hχ k hk k.2]

end GlobalTheory.ConjTwist

namespace GlobalTheory.ConjTwist

open GlobalTheory.CoefModel

theorem c_rhoVr {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
    (M : OMDat T.toCore R i Tp tup) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v : (R.MW i (sg0 D A)).Vec}
    {ι : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
    (hP : M.Pins κ v ι x₀) (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) (hc : ExtC R i (inC M.c') M.c0' c)
    (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E) (hγ : Bridge.IsRatMat (Vc D i) γ γE) (x : VsV D i ℂ) :
    c (rhoVr (fun τ => D.what₂.embLL.comp (labLL D τ)) (lamV D i) γE x) = (R.cV i).coef.ρ γ (c x) := by
  obtain ⟨gramR, c0R, c0L, hT, hbc⟩ := hP.lift.c0
  have hf : (inC M.c').comp M.jL = D.what₂.embLL := hP.lift.field
  have key : ∀ w : VsV D i D.what₂.LL, c (mapVV D.what₂.embLL (lamV D i) w) = c0L i w := by
    intro w
    obtain ⟨w', hw', hw''⟩ := hbc w
    refine (hc w' _ ?_).trans hw''
    rw [mapVV_coe, hw', MvPolynomial.map_map, hf]
  have hL : c ∘ₗ rhoVr (fun τ => D.what₂.embLL.comp (labLL D τ)) (lamV D i) γE = (R.cV i).coef.ρ γ ∘ₗ c := by
    apply LinearMap.ext_on_range (span_mapVV D.what₂.embLL (lamV D i))
    intro k
    show c (rhoVr (fun τ => D.what₂.embLL.comp (labLL D τ)) (lamV D i) γE (mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) k))) =
      (R.cV i).coef.ρ γ (c (mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) k)))
    rw [← mapVV_rhoVr]
    refine (key _).trans (((hT.mapL i).1 γ γE hγ _).trans ?_)
    exact congrArg _ (key _).symm
  exact LinearMap.congr_fun hL x

end GlobalTheory.ConjTwist

namespace GlobalTheory.ConjTwist

open GlobalTheory.CoefModel

theorem mapVV_tau_rhoVr (D : D7) (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (hτ : ∀ (φ : D.host.E →+* ℂ) x, τ (φ x) = φ x)
    (γE : GL (Fin (Vc D i).rank) D.host.E) (x : VsV D i ℂ) :
    mapVV (τ : ℂ →+* ℂ) (lamV D i) (rhoVr (fun τ' => D.what₂.embLL.comp (labLL D τ')) (lamV D i) γE x) =
      rhoVr (fun τ' => D.what₂.embLL.comp (labLL D τ')) (lamV D i) γE (mapVV (τ : ℂ →+* ℂ) (lamV D i) x) := by
  rw [mapVV_rhoVr]
  have e : (fun τ' => (τ : ℂ →+* ℂ).comp (D.what₂.embLL.comp (labLL D τ'))) = fun τ' => D.what₂.embLL.comp (labLL D τ') := by
    funext τ'
    ext a
    exact hτ _ a
  rw [e]

theorem exists_conjW {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
    (M : OMDat T.toCore R i Tp tup) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v : (R.MW i (sg0 D A)).Vec}
    {ι : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
    (hP : M.Pins κ v ι x₀) (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) (hc : ExtC R i (inC M.c') M.c0' c)
    (hb : Function.Bijective c) (τ : ℂ ≃+* ℂ) (hτ : ∀ (φ : D.host.E →+* ℂ) x, τ (φ x) = φ x) :
    ∃ TW : (R.cV i).W ≃+ (R.cV i).W, (∀ (a : ℂ) w, TW (a • w) = τ a • TW w) ∧
      (∀ x, TW (c x) = c (mapVV (τ : ℂ →+* ℂ) (lamV D i) x)) ∧
      ∀ γ w, TW ((R.cV i).coef.ρ γ w) = (R.cV i).coef.ρ γ (TW w) := by
  let cb := LinearEquiv.ofBijective c hb
  have hcb : ∀ x, cb.symm (c x) = x := fun x => cb.symm_apply_apply x
  let TW : (R.cV i).W ≃+ (R.cV i).W := cb.symm.toAddEquiv.trans ((conjVV τ (lamV D i)).trans cb.toAddEquiv)
  have hTW : ∀ w, TW w = c (mapVV (τ : ℂ →+* ℂ) (lamV D i) (cb.symm w)) := fun w => rfl
  have hTc : ∀ x, TW (c x) = c (mapVV (τ : ℂ →+* ℂ) (lamV D i) x) := fun x => by rw [hTW, hcb]
  refine ⟨TW, fun a w => ?_, hTc, fun γ w => ?_⟩
  · rw [hTW, hTW, map_smul, map_smulₛₗ, map_smul]
    rfl
  · obtain ⟨x, rfl⟩ := hb.2 w
    obtain ⟨γE, hγ⟩ := GlobalTheory.ConjForms.exists_ratMat (Vc D i) γ
    rw [← c_rhoVr M hP c hc γ γE hγ x, hTc, hTc, mapVV_tau_rhoVr D i τ hτ, c_rhoVr M hP c hc γ γE hγ]

end GlobalTheory.ConjTwist

namespace GlobalTheory.ConjTwist


set_option maxHeartbeats 8000000 in
theorem exists_conjForm_equiv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → ∀ (τ : ℂ ≃+* ℂ) (t t' : T0), FixBase T R i τ → ConjTup R τ t t' → ∃ φ : (R.HV i t).H ≃+ (R.HV i t').H, (∀ (a : ℂ) y, φ (a • y) = τ a • φ y) ∧ ∀ y y', ConjForm R i τ c t t' y y' ↔ y' = φ y := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hCore hFW i Tp tup M hPins c hc τ t t' hFix hConj
  have hX := GlobalTheory.T.coefficientMap_unique_bijective_complex_extension D G Pl0 T0 A T R F κ v₀ hCore hFW i Tp tup M hPins
  obtain ⟨c₁, -, hb₁, hu⟩ := hX
  have hb : Function.Bijective c :=
    (congrArg (fun f : VsV D i ℂ →ₗ[ℂ] (R.cV i).W => Function.Bijective f) (hu c hc)).mpr hb₁
  have hY := exists_conjW M hPins c hc hb τ hFix.host
  obtain ⟨TW, hs, hTc, hρ⟩ := hY
  have hZ := (GlobalTheory.T.conjugate_tuples_conjugate_residue_levels D G Pl0 T0 A T R F κ v₀ hCore τ t t' hConj).2.2.2 i hFix
  obtain ⟨hJ, hχ⟩ := hZ
  have hV := hCore.models.HV i t
  have hV' := hCore.models.HV i t'
  have hs' : ∀ (a : ℂ) w, TW.symm (a • w) = τ.symm a • TW.symm w := by
    intro a w
    apply TW.injective
    rw [hs, TW.apply_symm_apply, TW.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hρ' : ∀ γ w, TW.symm ((R.cV i).coef.ρ γ w) = (R.cV i).coef.ρ γ (TW.symm w) := by
    intro γ w
    apply TW.injective
    refine (TW.apply_symm_apply _).trans ?_
    refine Eq.trans ?_ (hρ γ (TW.symm w)).symm
    exact congrArg _ (TW.apply_symm_apply w).symm
  have hχ' : ∀ k (hk : k ∈ levJ R i t') (hk' : k ∈ levJ R i t),
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨k, hk'⟩ : ℂˣ) : ℂ) =
        τ.symm (((levEnv (Vc D i) (R.βV i) (R.datVt i t')).χ ⟨k, hk⟩ : ℂˣ) : ℂ) := by
    intro k hk hk'
    exact (τ.symm_apply_apply _).symm.trans (congrArg τ.symm (hχ k hk' hk).symm)
  have hmem := fun y => hV.2.1.le (LinearMap.mem_range_self (R.HV i t).e y)
  have hmem' := fun y => hV'.2.1.le (LinearMap.mem_range_self (R.HV i t').e y)
  have hfwd : ∀ y, ∃ y', (R.HV i t').e y' = fun g => TW ((R.HV i t).e y g) := fun y =>
    LinearMap.mem_range.1 (hV'.2.1.ge
      (post_mem (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ hJ _ _ τ TW.toAddMonoidHom hs hρ hχ (hmem y)))
  have hbwd : ∀ y', ∃ y, (R.HV i t).e y = fun g => TW.symm ((R.HV i t').e y' g) := fun y' =>
    LinearMap.mem_range.1 (hV.2.1.ge
      (post_mem (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ hJ.symm _ _ τ.symm TW.symm.toAddMonoidHom hs' hρ' hχ' (hmem' y')))
  choose φ hφ using hfwd
  have hφadd : ∀ y z, φ (y + z) = φ y + φ z := by
    intro y z
    apply hV'.1
    funext g
    have e1 := congrFun (hφ (y + z)) g
    have e2 := congrFun (hφ y) g
    have e3 := congrFun (hφ z) g
    beta_reduce at e1 e2 e3
    refine e1.trans ?_
    exact (congrArg TW (congrFun (map_add (R.HV i t).e y z) g)).trans ((map_add TW _ _).trans
      ((congrArg₂ (· + ·) e2 e3).symm.trans (congrFun (map_add (R.HV i t').e (φ y) (φ z)) g).symm))
  have hφsmul : ∀ (a : ℂ) y, φ (a • y) = τ a • φ y := by
    intro a y
    apply hV'.1
    funext g
    have e1 := congrFun (hφ (a • y)) g
    have e2 := congrFun (hφ y) g
    beta_reduce at e1 e2
    refine e1.trans ?_
    exact (congrArg TW (congrFun (map_smul (R.HV i t).e a y) g)).trans ((hs _ _).trans
      ((congrArg (τ a • ·) e2).symm.trans (congrFun (map_smul (R.HV i t').e (τ a) (φ y)) g).symm))
  have hbij : Function.Bijective φ := by
    constructor
    · intro y z h
      apply hV.1
      funext g
      have := congrFun ((hφ y).symm.trans ((congrArg (R.HV i t').e h).trans (hφ z))) g
      exact TW.injective this
    · intro y'
      obtain ⟨y, hy⟩ := hbwd y'
      refine ⟨y, hV'.1 ?_⟩
      funext g
      exact (congrFun (hφ y) g).trans ((congrArg TW (congrFun hy g)).trans (TW.apply_symm_apply _))
  refine ⟨AddEquiv.ofBijective (AddMonoidHom.mk' φ hφadd) hbij, fun a y => hφsmul a y, fun y y' => ?_⟩
  show ConjForm R i τ c t t' y y' ↔ y' = φ y
  constructor
  · intro hC
    have key : ∀ h, (R.HV i t').e y' (Formalism.IndefR.FWT.fin (Vc D i) h) = TW ((R.HV i t).e y (Formalism.IndefR.FWT.fin (Vc D i) h)) := by
      intro h
      have h0 := hC h
      obtain ⟨x, x', hx, h1, h2⟩ := h0
      have hx' : x' = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x := Subtype.ext (hx.trans (GlobalTheory.CoefModel.mapVV_coe _ _ _).symm)
      exact h2.trans ((congrArg c hx').trans ((hTc x).symm.trans (congrArg TW h1.symm)))
    apply hV'.1
    refine Eq.trans ?_ (hφ y).symm
    funext g
    have hs0 := (finHom (Vc D i)).rangeRestrict_surjective g
    obtain ⟨h, hh⟩ := hs0
    exact Eq.subst (motive := fun g => (R.HV i t').e y' g = TW ((R.HV i t).e y g)) hh (key h)
  · rintro rfl h
    have hs1 := hb.2 ((R.HV i t).e y (Formalism.IndefR.FWT.fin (Vc D i) h))
    obtain ⟨x, hx⟩ := hs1
    refine ⟨x, GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x, GlobalTheory.CoefModel.mapVV_coe _ _ _, hx.symm, ?_⟩
    refine (congrFun (hφ y) (Formalism.IndefR.FWT.fin (Vc D i) h)).trans ?_
    exact (congrArg TW hx.symm).trans (hTc x)

end GlobalTheory.ConjTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquivStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisConj_definiteForms_semilinearEquiv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → ∀ (τ : ℂ ≃+* ℂ) (t t' : T0), FixBase T R i τ → ConjTup R τ t t' → ∃ φ : (R.HV i t).H ≃+ (R.HV i t').H, (∀ (a : ℂ) y, φ (a • y) = τ a • φ y) ∧ ∀ y y', ConjForm R i τ c t t' y y' ↔ y' = φ y := by
  first | exact @GlobalTheory.ConjTwist.exists_conjForm_equiv | exact GlobalTheory.ConjTwist.exists_conjForm_equiv | (intros; apply GlobalTheory.ConjTwist.exists_conjForm_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyAlgHomOfIsIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeRealRdIff
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EvKEqSum
open scoped TensorProduct

namespace GlobalTheory.EvaluationSum

open GlobalTheory.SeriesTie

theorem evK_eq_sum {D : Formalism.BasicNotions.D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D)) Γ Pl0 I0 (List Nat) T (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D))]
    {Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks}
    {cG : MulEquiv (Formalism.L2.DIV.G0 (Formalism.IndefR.Links.LevCh.Pg (Formalism.IndefR.Links.RealDat.toLevCh (Formalism.IndefR.Links.RealDat3.toRealDat Rl))) (Formalism.BasicNotions.Ranks.r (Formalism.BasicNotions.D7.R D))) (Formalism.BasicNotions.G0g (Formalism.BasicNotions.D7.nd D))}
    {S : Formalism.IndefR.NX.RatDat (Formalism.BasicNotions.D7.ntw D)} (YS : Formalism.IndefR.NX.NExpRealS Rl cG S)
    (v₀ : (j : Fin (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))) → (σ : RingHom (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D)) Complex) → Formalism.IndefR.Mult.DSModel.Vec (Formalism.IndefR.Links.RealDat.MW (Formalism.IndefR.Links.RealDat3.toRealDat Rl) j σ))
    {ρ : GlobalTheory.SeriesTie.Setup (Formalism.BasicNotions.D7.ntw D)} (hρ : GlobalTheory.SeriesTie.Setup.Good ρ)
    (i : Formalism.BasicNotions.NTw.Tw (Formalism.BasicNotions.D7.ntw D)) (j : Fin (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))) (b : Bool)
    (t : TensorProduct (Formalism.IndefR.NX.RatDat.Ks S) (Formalism.IndefR.NX.KB S i b) (Formalism.IndefR.NX.FmK S ((j : ℕ) + 1))) :
    ∃ (n : ℕ) (a : Fin n → Formalism.IndefR.NX.KB S i b) (x : Fin n → Formalism.IndefR.NX.FmK S ((j : ℕ) + 1)),
      GlobalTheory.SeriesTie.evK YS v₀ hρ i j b t =
        ∑ k : Fin n, GlobalTheory.SeriesTie.Setup.e ρ i b (a k) • GlobalTheory.SeriesTie.evW YS v₀ j (x k).val := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a f => exact ⟨1, fun _ => a, fun _ => f, by simp [evK_tmul]⟩
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨n₁, a₁, x₁, e₁⟩ := h₁
    obtain ⟨n₂, a₂, x₂, e₂⟩ := h₂
    refine ⟨n₁ + n₂, Fin.append a₁ a₂, Fin.append x₁ x₂, ?_⟩
    rw [map_add (f := _), e₁, e₂, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

end GlobalTheory.EvaluationSum
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

theorem evK_eq_sum (t : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    ∃ (n : ℕ) (a : Fin n → NX.KB S i b) (x : Fin n → NX.FmK S ((j : ℕ) + 1)),
      evK YS v₀ hρ i j b t = ∑ k, ρ.e i b (a k) • evW YS v₀ j (Subtype.val (x k)) := by
  first
  | exact @_root_.GlobalTheory.EvaluationSum.evK_eq_sum
  | exact _root_.GlobalTheory.EvaluationSum.evK_eq_sum
  | (apply _root_.GlobalTheory.EvaluationSum.evK_eq_sum <;> assumption)
  | (intros; apply _root_.GlobalTheory.EvaluationSum.evK_eq_sum <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EvaluationSum.evK_eq_sum <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EvaluationSum.evK_eq_sum ..)

theorem mem_range_realRd_iff {ν : ℂ} (hν : ν ≠ 0) (g : GA D (Wc D j) → ℂ) :
    g ∈ Set.range (realRd YS v₀ hρ i j b ν) ↔
      ∃ (n : ℕ) (a : Fin n → NX.KB S i b) (x : Fin n → NX.FmK S ((j : ℕ) + 1)),
        ν • g = ∑ k, ρ.e i b (a k) • evW YS v₀ j (Subtype.val (x k)) := by
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨n, a, x, e⟩ := evK_eq_sum YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)
    refine ⟨n, a, x, ?_⟩
    change ν • (ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)) = _
    rw [smul_inv_smul₀ hν, e]
  · rintro ⟨n, a, x, e⟩
    refine ⟨∑ k, (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (a k ⊗ₜ[S.Ks] x k), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [realRd_tmul, mul_smul]
    rw [← Finset.smul_sum, ← e, inv_smul_smul₀ hν]

end GlobalTheory.SeriesTie
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Export

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)


variable {YS v₀ i j b} in
theorem mem_range_realRd_of_sum {ν : ℂ} (hν : ν ≠ 0) {g : GA D (Wc D j) → ℂ} {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ k, ∃ y, ρ.e i b y = z k) (x : Fin n → NX.FmK S ((j : ℕ) + 1))
    (h : ν • g = ∑ k, z k • evW YS v₀ j (Subtype.val (x k))) : g ∈ Set.range (realRd YS v₀ hρ i j b ν) := by
  choose y hy using hz
  exact (mem_range_realRd_iff YS v₀ hρ i j b hν g).2 ⟨n, y, x, h.trans (Finset.sum_congr rfl fun k _ => by rw [← hy k])⟩


variable (ρ) in
def UnrComb (Φ : GA D (Wc D j) → ℂ) : Prop :=
  ∃ (k L : Type) (_ : Field k) (_ : NumberField k) (_ : Field L) (_ : NumberField L) (_ : Algebra k L)
    (ι : k →+* FractionRing (D.ntw.O i)) (σ : L →+* ℂ), Normal k L ∧
    (∀ (P : Ideal (𝓞 L)) [P.IsPrime], ((D.ntw.l i : ℕ) : 𝓞 L) ∈ P → Algebra.IsUnramifiedAt (𝓞 k) P) ∧
    (∀ a, σ (algebraMap k L a) = ρ.e i b (ι a)) ∧
    ∃ (n : ℕ) (a : Fin n → L) (x : Fin n → NX.FmK S ((j : ℕ) + 1)), Φ = ∑ c, σ (a c) • evW YS v₀ j (Subtype.val (x c))


variable {YS v₀ i j b}

end Export

section Any

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw} {j : Fin D.R.m} {b : Bool}


variable (ρ Y i j b) in
def xiLin (Q : Finset (Pl D.host.E)) (M : ℕ) (h : GA D (Vc D j)) (a : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) :
    PolF D (Wc D j).rank (Vc D j).rank →ₗ[ℂ] (GA D (Wc D j) → ℂ) where
  toFun P := ρ.xi i j b Y Q M h P a
  map_add' P P' := by funext g; simp only [Base.xiCoef_apply, map_add (f := _), Pi.add_apply]
  map_smul' c P := by funext g; simp only [Base.xiCoef_apply, map_smul, Pi.smul_apply, RingHom.id_apply]

theorem Faithful.mem_range_of_smul {rd : Rd ρ Y i j b} (hF : Faithful rd) {g : GA D (Wc D j) → ℂ} (hg : g ≠ 0) {u : ℂ}
    (h1 : g ∈ Set.range rd) (h2 : u • g ∈ Set.range rd) : ∃ y, ρ.e i b y = u := by
  obtain ⟨f, rfl⟩ := h1
  obtain ⟨f', h2⟩ := h2
  have hf : f ≠ 0 := fun h => hg (by rw [h, map_zero])
  have hdep : ¬ LinearIndependent (FractionRing (X.O i)) ![f, f'] := fun h => by
    have h3 : LinearIndependent ℂ ![rd f, rd f'] := by
      convert hF 2 _ h using 1
      funext c
      fin_cases c <;> rfl
    have := (LinearIndependent.pair_iff.1 h3 u (-1) (by rw [h2]; simp)).2
    simp at this
  rw [LinearIndependent.pair_iff' hf] at hdep
  push Not at hdep
  obtain ⟨y, rfl⟩ := hdep
  rw [map_smulₛₗ] at h2
  exact ⟨y, smul_left_injective ℂ hg h2⟩

theorem mem_range_of_small (rd : Rd ρ Y i j b) (Φ : PolF D (Wc D j).rank (Vc D j).rank →ₗ[ℂ] (GA D (Wc D j) → ℂ))
    (hinj : ∀ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P = 0 → P = 0)
    (honto : ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam, ∃ P ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
      coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank))
    (hΦ : ∀ P ∈ (ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
      coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → Φ P ∈ Set.range rd)
    {h : GA D (Vc D j)} {P : PolF D (Wc D j).rank (Vc D j).rank} (hP : P ∈ ρ.lat i j b (ρ.eO i b).range h) :
    Φ P ∈ Set.range rd := by
  have key : ∀ φ ∈ coefLatFn (embLL0 D) (labLL0 D) (ρ.eO i b).range (ρ.B i j b).w.lam ((ρ.B i j b).latAt (finPt _ h)),
      ∃ P' ∈ (ρ.B i j b).valSpace, harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P' = φ ∧ Φ P' ∈ Set.range rd := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h1 =>
      obtain ⟨F, -, rfl⟩ := h1
      obtain ⟨P', h2, h3⟩ := honto F
      exact ⟨P', h2, h3, hΦ P' h2 F h3⟩
    | zero => exact ⟨0, zero_mem _, map_zero _, 0, by rw [map_zero, map_zero]⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨P₁, a1, rfl, f₁, e1⟩ := h1
      obtain ⟨P₂, a2, rfl, f₂, e2⟩ := h2
      exact ⟨P₁ + P₂, add_mem a1 a2, map_add _ _ _, f₁ + f₂, by rw [map_add (f := _), map_add (f := _), e1, e2]⟩
    | smul c _ _ h1 =>
      obtain ⟨P₁, a1, rfl, f₁, e1⟩ := h1
      obtain ⟨_, o, rfl⟩ := c
      exact ⟨ρ.eO i b o • P₁, Submodule.smul_mem _ _ a1, map_smul _ _ _, o • f₁, by rw [rd_smul, map_smul, e1]⟩
  obtain ⟨P', h1, h2, h3⟩ := key _ hP.2
  rwa [sub_eq_zero.1 (hinj (P - P') (sub_mem hP.1 h1) (by rw [map_sub, h2]; exact sub_self _))]

end Any

section Main

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

variable {YS v₀ i j b}

end Main

section Core
open Formalism.IndefR.FWT Formalism.L2.Pj

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ i : Fin D.R.m, Formalism.MainNotions.WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem exists_evW_eq_phiC (t : FWTie T Rl.toRealDat κ v₀) (ht : t.Evaluates) (j : Fin D.R.m)
    (hσ : GoodEmb T.Q.c (res T (sg0 D A3.A))) (hV : T.V ((j : ℕ) + 1) (res T (sg0 D A3.A)) = Wc D j) (f : Cu T κ j) :
    ∃ x : NX.FmK S ((j : ℕ) + 1), evW YS v₀ j (Subtype.val x) = phiC T hV (wtA (κ j)) (f : T.R ((j : ℕ) + 1)) := by
  have hx : (YS.fi j).e.symm ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL) ∈ (S.A ((j : ℕ) + 1)).WK := by
    refine ((YS.fi j).wk _).2 ?_
    have e1 : (YS.fi j).e ((YS.fi j).e.symm ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL)) =
        ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL) := LinearEquiv.apply_symm_apply _ _
    rw [e1]
    exact (t.e j f).2
  refine ⟨⟨_, hx⟩, Eq.trans ?_ (ht j (sg0 D A3.A) hσ hV f)⟩
  have e2 := LinearEquiv.apply_symm_apply (YS.fi j).e ((t.e j f : (Rl.FW j).WK) : Fin (Rl.nW j) → D.what₂.LL)
  simp only [evW, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [e2]
  rfl

end Core
end GlobalTheory.SeriesTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharValuesMemCoeffFieldRange
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharValuesMemCoeffFieldRange
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DeltaRange

theorem delta_value_mem_range : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X}, ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ), ∃ a : FractionRing (X.O i), ρ.e i b a = (((ρ.B i j b).de.chi z : Circle) : ℂ) := by
  intro D N X ρ hρ i j b z
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i)).ker : Set (G D.host.E N.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i)).ker = (X.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact X.delta_open i
  have : Finite (G D.host.E N.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (X.O i) (FractionRing (X.O i))
    (algebraMap (X.O0 i) (X.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i) σ : (X.O0 i)ˣ) : X.O0 i)), ?_⟩
  rw [hρ.delta i j b]
  exact (charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (X.O0 i) (X.O i))) hopen hσ hn hpow).symm

end GlobalTheory.DeltaRange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharValuesMemCoeffFieldRangeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisting_char_values_mem_coeff_field_range : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X}, ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ), ∃ a : FractionRing (X.O i), ρ.e i b a = (((ρ.B i j b).de.chi z : Circle) : ℂ) := by
  first | exact @GlobalTheory.DeltaRange.delta_value_mem_range | exact GlobalTheory.DeltaRange.delta_value_mem_range | (intros; apply GlobalTheory.DeltaRange.delta_value_mem_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSelfDualLatticeIffIntegralFrameMatricesHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSelfDualLatticeIffIntegralFrameMatricesHalf
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries.LatHalf

open GlobalTheory.ExportSeries
open Formalism.L2.DIV (Pl)

variable {D : D7}

theorem levConj_conjPl (P : Formalism.L2.DIV.Pl D.host.E) : Formalism.IndefR.Lev.IsConjPl P (Formalism.L2.DIV.conjPl P) := by
  intro c hc
  refine ⟨Formalism.L2.DIV.starO c, ?_, Formalism.L2.DIV.starO_coe c⟩
  show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO c) ∈ P.asIdeal
  rw [Formalism.L2.DIV.starO_starO]
  exact hc

theorem eq_conjPl_of_levConj {A B : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.IndefR.Lev.IsConjPl A B) :
    B = Formalism.L2.DIV.conjPl A := by
  refine (HeightOneSpectrum.ext ?_).symm
  refine Ideal.IsMaximal.eq_of_le (Formalism.L2.DIV.conjPl A).isMaximal B.isPrime.ne_top fun b hb => ?_
  obtain ⟨c', hc', e⟩ := h (Formalism.L2.DIV.starO b) hb
  have : c' = b := RingOfIntegers.ext (by rw [e, Formalism.L2.DIV.starO_coe, star_star])
  exact this ▸ hc'

theorem isIdemAt_conjPl {e : AE D} {P : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt e P) :
    Formalism.L2.NTheta.IsIdemAt (cA D e) (Formalism.L2.DIV.conjPl P) :=
  GlobalTheory.MovedIdem.isIdemAt_conj h fun x => by
    rw [show Formalism.L2.Col.cO D.host.E x = Formalism.L2.DIV.starO x from RingOfIntegers.ext (by rw [Formalism.L2.DIV.starO_coe]; rfl)]
    rfl

theorem conj_placesOK {Pg Q : Finset (Pl D.host.E)} (h : PlacesOK Pg Q) :
    idem (Pg.image Formalism.L2.DIV.conjPl) = cA D (idem Pg) ∧ PlacesOK ∅ (Pg.image Formalism.L2.DIV.conjPl) := by
  obtain ⟨P, h1, -, hP⟩ := h.split
  have hS := hP.mono h1
  have hinj : Set.InjOn Formalism.L2.DIV.conjPl (Pg : Set (Pl D.host.E)) := fun a _ b _ hab => by
    rw [← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl]
  have hc : ∀ PP ∈ Pg, idemAt (Formalism.L2.DIV.conjPl PP) = cA D (idemAt PP) := fun PP hPP =>
    idemAt_eq (isIdemAt_conjPl (hS.isIdemAt hPP))
  have he : idem (Pg.image Formalism.L2.DIV.conjPl) = cA D (idem Pg) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [idem, Finset.sum_image hinj, idem, map_sum]
    exact Finset.sum_congr rfl hc
  refine ⟨he, ⟨⟨Pg.image Formalism.L2.DIV.conjPl, Finset.empty_subset _, le_rfl,
    ⟨idem (Pg.image Formalism.L2.DIV.conjPl), ⟨idemAt, ?_, rfl⟩, ?_⟩⟩, Finset.disjoint_empty_left _, ?_⟩⟩
  · intro PP hPP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 hPP
    rw [hc P0 hP0]
    exact isIdemAt_conjPl (hS.isIdemAt hP0)
  · rw [he, GlobalTheory.DualPairCheck.cA_cA, mul_comm]
    exact hS.isIdemSum.2
  · intro PP hPP PP' hPP'
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 (hPP.resolve_left (Finset.notMem_empty PP))
    rcases hPP' with rfl | hc'
    · exact h.prime P0 (Or.inl hP0) _ (Or.inr (levConj_conjPl P0))
    · rw [eq_conjPl_of_levConj hc', Formalism.L2.DIV.conjPl_conjPl]
      exact h.prime P0 (Or.inl hP0) P0 (Or.inl rfl)

theorem goodPosition_auxiliaryPlaces_alone {Pg Q : Finset (Pl D.host.E)} (h : PlacesOK Pg Q) : PlacesOK ∅ Q :=
  ⟨h.split.imp fun _ hP => ⟨Finset.empty_subset _, hP.2.1, hP.2.2⟩, Finset.disjoint_empty_left _,
    fun PP hPP => h.prime PP (Or.inr (hPP.resolve_left (Finset.notMem_empty PP)))⟩

theorem idem_sq {R : Finset (Pl D.host.E)} (h : PlacesOK ∅ R) : idem R * idem R = idem R := by
  have := h.isOrthSum.1.idem
  rwa [halfIdem, idem_empty, map_zero, zero_add] at this

theorem toEAf_idem_int {R : Finset (Pl D.host.E)} (h : PlacesOK ∅ R) :
    toEAf D (idem R) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨P, -, h2, hP⟩ := h.split
  have := GlobalTheory.DatumFourier.idem_div_int (hP.mono h2).isIdemSum one_ne_zero fun PP _ hPP =>
    PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using hPP))
  simpa using this

theorem frMapO_add {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x y : WO S T) :
    frMapO S T βS βT (x + y) = frMapO S T βS βT x + frMapO S T βS βT y := by
  unfold frMapO
  rw [Matrix.map_add _ (map_add (toEAf D)), Matrix.mul_add, Matrix.add_mul]

theorem frMapO_smul {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (x : WO S T) :
    frMapO S T βS βT (e • x) = toEAf D e • frMapO S T βS βT x := by
  unfold frMapO
  have : (e • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D e • x.map (toEAf D) :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem isHalf_smul {m n : ℕ} {e : AE D} (he : e * e = e) (x : Mx D m n) : IsHalf e (e • x) := fun i j => by
  show e * (e * x i j) = e * x i j
  rw [← mul_assoc, he]

theorem mem_lat_piece {S T : HSp D} {F : Frame S T} (hF : F.Good) {R : Finset (Pl D.host.E)} (hR : PlacesOK ∅ R)
    (x : WO S T) (hi : IsIntM (frMapO S T F.βS F.βT x)) : idem R • x ∈ F.lat := by
  refine GlobalTheory.T.mem_completedLattice_of_frameMatrix_integral hF hR (isHalf_smul (idem_sq hR) x) ?_
  rw [frMapO_smul]
  exact fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (toEAf_idem_int hR) (hi i j)

theorem mem_lat_iff_isIntM_halfIdem : ∀ {D : D7} {S T : HSp D} {F : GlobalTheory.ExportSeries.Frame S T}, F.Good →
    ∀ {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)}, GlobalTheory.ExportSeries.PlacesOK Pg Q →
    (∀ PP, PP ∈ Pg ∨ PP ∈ Q → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) →
    ∀ {x : WO S T}, IsHalf (GlobalTheory.ExportSeries.halfIdem Pg Q) x →
      (x ∈ F.lat ↔ IsIntM (frMapAdj S T F.βS F.βT x) ∧ IsIntM (frMapO S T F.βS F.βT x)) := by
  intro D S T F hF Pg Q h _ x hx
  obtain ⟨hR1, hR⟩ := conj_placesOK h
  have hQ := goodPosition_auxiliaryPlaces_alone h
  have hxe : x = idem (Pg.image Formalism.L2.DIV.conjPl) • x + idem Q • x := by
    rw [← add_smul, hR1]
    exact (Matrix.ext fun i j => hx i j).symm
  constructor
  · intro hl
    obtain ⟨o1, a1⟩ := GlobalTheory.T.frameMatrices_integral_of_mem_completedLattice hF hR (isHalf_smul (idem_sq hR) x)
      (GlobalTheory.PlaceModelSum.idem_smul_latO (idem_sq hR) hl)
    obtain ⟨o2, a2⟩ := GlobalTheory.T.frameMatrices_integral_of_mem_completedLattice hF hQ (isHalf_smul (idem_sq hQ) x)
      (GlobalTheory.PlaceModelSum.idem_smul_latO (idem_sq hQ) hl)
    rw [hxe, GlobalTheory.PlaceVec.frMapAdj_add, frMapO_add]
    exact ⟨fun i j => add_mem (a1 i j) (a2 i j), fun i j => add_mem (o1 i j) (o2 i j)⟩
  · rintro ⟨-, hi⟩
    rw [hxe]
    exact add_mem (mem_lat_piece hF hR x hi) (mem_lat_piece hF hQ x hi)

end GlobalTheory.ExportSeries.LatHalf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSelfDualLatticeIffIntegralFrameMatricesHalfStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_selfDualLattice_iff_integral_frameMatrices_half : ∀ {D : D7} {S T : HSp D} {F : GlobalTheory.ExportSeries.Frame S T}, F.Good → ∀ {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)},
    GlobalTheory.ExportSeries.PlacesOK Pg Q → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ {x : WO S T}, IsHalf (GlobalTheory.ExportSeries.halfIdem Pg Q) x →
      (x ∈ F.lat ↔ IsIntM (frMapAdj S T F.βS F.βT x) ∧ IsIntM (frMapO S T F.βS F.βT x)) := by
  first | exact @GlobalTheory.ExportSeries.LatHalf.mem_lat_iff_isIntM_halfIdem | exact GlobalTheory.ExportSeries.LatHalf.mem_lat_iff_isIntM_halfIdem | (intros; apply GlobalTheory.ExportSeries.LatHalf.mem_lat_iff_isIntM_halfIdem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOffOutsideS0
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOffOutsideS0
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.SplitOffS0

theorem main : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X}, ρ.Good → ∀ (i : X.Tw) (Q : Finset (Pl D.host.E)), (∀ P' ∈ Q, P' ∈ X.S0 i) → ∀ (P : Pl D.host.E), IsSplitPl D.host P → P ∉ X.S0 i → Bridge.SplitOff P (Q : Set (Pl D.host.E)) := by
  intro D N X ρ hρ i Q hQ P hsplit hP
  have hinv : ∀ z : D.host.E, D.host.conj (D.host.conj z) = z := fun z => Formalism.L2.Host.conj_conj (D := D) D.host z
  let c : 𝓞 D.host.E → 𝓞 D.host.E := fun x => RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) x
  have hc : ∀ x : 𝓞 D.host.E, ((c x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := fun x => rfl
  have key : ∀ x y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) →
      (x ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ↔ y ∈ P.asIdeal) :=
    fun x y h => GlobalTheory.Mem.Col2.HAt.mem_conjIdeal_Pv P.asIdeal x y h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx, hy⟩ := hsplit
    intro heq
    have h1 : c x ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal :=
      (key (c x) x (by rw [hc, hinv])).2 hx
    exact hy (c x) (hc x) (heq ▸ h1)
  · intro hPQ
    exact hP (hQ P (by simpa using hPQ))
  · intro Q' hQ' heq
    apply hP
    refine hρ.goodSetup_badPlaces_conj i Q' (hQ Q' (by simpa using hQ')) P ?_
    intro x y hxy
    rw [heq]
    exact key x y hxy

end GlobalTheory.SplitOffS0
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOffOutsideS0Statement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_off_outside_S0 : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X}, ρ.Good → ∀ (i : X.Tw) (Q : Finset (Pl D.host.E)), (∀ P' ∈ Q, P' ∈ X.S0 i) → ∀ (P : Pl D.host.E), IsSplitPl D.host P → P ∉ X.S0 i → Bridge.SplitOff P (Q : Set (Pl D.host.E)) := by
  first | exact @GlobalTheory.SplitOffS0.main | exact GlobalTheory.SplitOffS0.main | (intros; apply GlobalTheory.SplitOffS0.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperLeftBlockEqOneIffOfMemBlockTri
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrincipalLevel

theorem upperLeftBlock_eq_one_iff_of_mem_blockTri {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (h : r = n) (g : GL (Fin n) κ) :
    upperLeftBlock hr g = 1 ↔ g = 1 := by
  subst h
  have hg : g ∈ blockTri (κ := κ) (blk2 r) := fun i j hij => by
    simp [blk2, i.2, j.2] at hij
  constructor
  · intro h1
    apply Units.ext
    ext i j
    have := congrArg (fun u : GL (Fin r) κ => (u : Matrix (Fin r) (Fin r) κ) i j) h1
    simp only [upper_block_val_submatrix hr hg, Matrix.submatrix_apply] at this
    have ei : Fin.castLE hr i = i := Fin.ext rfl
    have ej : Fin.castLE hr j = j := Fin.ext rfl
    rw [ei, ej] at this
    simpa using this
  · rintro rfl
    exact blockDiagonalExtendByOnePrimeField_one _ _

theorem mem_lev_whole {D : D7} {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (β : GL (Fin n) (Lev.EAf D))
    (L : LevDat D.host.E ℂ n) (hr : L.r = n) (hQ : L.Q = ∅) (hP : L.P.H = ⊥) (x : GL (Fin n) (Lev.EAf D)) :
    x ∈ lev D.sp.cm J β L ↔ x ∈ UA D.sp.cm J ∧ x ∈ St β ∧ ∀ PP ∈ L.Pg, redFn β PP x = 1 := by
  have h0 : ∀ a : Fin n, blkOf L.r L.t a = 0 := fun a => by
    unfold blkOf
    rw [if_pos (by rw [hr]; exact a.2)]
  rw [mem_lev, mem_parLev, hP, Subgroup.mem_bot]
  constructor
  · rintro ⟨⟨h1, h2, -, -⟩, h3⟩
    exact ⟨h1, h2, fun PP hPP => (upperLeftBlock_eq_one_iff_of_mem_blockTri L.hr hr _).1 (congrFun h3 ⟨PP, hPP⟩)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2, fun PP _ i j hij => ?_, fun PP hPP => ?_⟩, funext fun PP => (upperLeftBlock_eq_one_iff_of_mem_blockTri L.hr hr _).2 (h3 PP.1 PP.2)⟩
    · rw [h0, h0] at hij
      exact absurd hij (lt_irrefl 0)
    · rw [hQ] at hPP
      exact absurd hPP (Finset.notMem_empty _)

theorem levK_eq_levG : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : GlobalTheory.SeriesTie.Setup D.ntw}, GlobalTheory.SeriesTie.RealPin Rl cG ρ → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ρ.levK i j b = Formalism.IndefR.Lev.levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG ρ hpin i j b
  show Lev.levG (Wc D j) (ρ.B i j b).F.βT (Lev.flag1L (ρ.B i j b).G.levT) = _
  rw [hpin.frT i j b]
  unfold Lev.levG
  congr 1
  ext x
  rw [mem_lev_whole _ _ _ rfl rfl rfl, mem_lev_whole _ _ _ (FWT.rank_Wc j).symm rfl rfl]
  have hg : (Lev.flag1L (ρ.B i j b).G.levT).Pg = (Rl.datWp j Rl.triv).Pg := hpin.Pg i j b
  rw [hg]

end GlobalTheory.PrincipalLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsHeckeDatum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeDatumExists

variable {D : D7}

theorem conj_ne_of_split {P : Pl D.host.E} (h : IsSplitPl D.host P) : Formalism.DivisionValues.conjPl P ≠ P := by
  intro hP
  obtain ⟨x, hx, hy⟩ := h
  refine hy (Formalism.DivisionValues.cO D.host.E x) ?_ ?_
  · show starRingAut (x : D.host.E) = D.host.conj (x : D.host.E)
    rw [starRingAut_apply]
    exact Formalism.BasicNotions.bridge_star_holds D.R D.host _
  · have : Formalism.DivisionValues.cO _ x ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hx
    rwa [hP] at this

theorem exists_isDC_levG (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {α : GA D V}
    (hα : α ∈ GfC V) : ∃ R : Finset (GA D V), Bridge.IsDC (Lev.levG V β L) α R := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hle : Lev.levG V β L ≤ GfC V := fun k hk => hk.1
  have hi := GlobalTheory.HeckeLabels.relIndex_conj_ne_zero (L := GfC V) (GlobalTheory.ParahoricCompact.isCompact_levG V β L)
    (GlobalTheory.ParahoricCompact.isOpen_comap_lev V β L) (fun k hk hk' => ⟨hk, hk'⟩) hα
  rw [inf_eq_left.2 hle] at hi
  obtain ⟨R, r1, r2⟩ := GlobalTheory.HeckeLabels.exists_reps hi
  refine ⟨R, fun a ha => ?_, fun g ⟨k₁, k₂, hg⟩ => ?_⟩
  · obtain ⟨k₁, h₁, k₂, h₂, e⟩ := r1 a ha
    exact ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩, e⟩
  · exact r2 g ⟨k₁, k₁.2, k₂, k₂.2, hg⟩

theorem exists_isHeckeDatum : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X),
    ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool), ∀ (k : ℕ) (P : Pl D.host.E), Formalism.MainNotions.IntegralHeckeForms.HkIdx i k P →
      ∃ α R z, ρ.IsHeckeDatum i j b k P α R z := by
  intro D N X ρ _ i j b k P hk
  obtain ⟨-, hkr, hsp, -⟩ := hk
  obtain ⟨e, he⟩ := GlobalTheory.Hk3.SplitMatch.exists_isIdemAt (conj_ne_of_split hsp)
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
  obtain ⟨α, R₀, R₀', hα, -⟩ := GlobalTheory.Hk3.SplitMatch.exists_data he h1 h2 (Wc D j)
  have hA := (hα k (hkr.trans (r_le_rank_Wc j))).1
  obtain ⟨R, hR⟩ := exists_isDC_levG (Wc D j) _ _ hA.1
  have hee : e * e = e := he.1.1
  set u : (AE D)ˣ := Matrix.GeneralLinearGroup.det (matHom (Wc D j) (α k)) with hu
  have huv : (u : AE D) * ((u⁻¹ : (AE D)ˣ) : AE D) = 1 := Units.mul_inv u
  let z : (AE D)ˣ := Units.mkOfMulEqOne (e * u + (1 - e)) (e * ((u⁻¹ : (AE D)ˣ) : AE D) + (1 - e)) (by
    linear_combination ((u : AE D) * ((u⁻¹ : (AE D)ˣ) : AE D) - u - ((u⁻¹ : (AE D)ˣ) : AE D) + 1) * hee + e * huv)
  refine ⟨α k, R, z, ⟨e, ϖ, he, h1, h2, hA⟩, hR, ?_⟩
  show (z : AE D) = idemAt P * (mt (Wc D j) (α k)).det + (1 - idemAt P)
  rw [idemAt_eq he]
  rfl

end GlobalTheory.HeckeDatumExists
end
end
