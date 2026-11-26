module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetRdMulInvPow
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff

namespace GlobalTheory.AnVal.JetAlg

def AnO {n g : ℕ} (f : (Fin n → Fin g → ℂ) → ℂ) : Prop := ContDiffAt ℂ ω (fun v => f (colsOf n g v)) 0

private lemma jetN_eq_renN_psJet_tay {n g : ℕ} (m : ℕ) (f : (Fin n → Fin g → ℂ) → ℂ) :
    jetN m f = renN n g m (psJet m (tay (fun v => f (colsOf n g v)) 0)) := by
  rfl

theorem jetN_mul {n g : ℕ} (m : ℕ) {f h : (Fin n → Fin g → ℂ) → ℂ} (hf : AnO f) (hh : AnO h) :
    jetN m (fun w => f w * h w) = jetN m f * jetN m h := by
  rw [jetN_eq_renN_psJet_tay, jetN_eq_renN_psJet_tay, jetN_eq_renN_psJet_tay, ← map_mul, ← FBIdJet.psJet_mul]
  congr 2
  exact (TM.taylor_multiplication.1 _ _ _ hf hh).1

theorem jetN_one {n g : ℕ} (m : ℕ) : jetN m (fun _ : Fin n → Fin g → ℂ => (1 : ℂ)) = 1 := by
  have hc := TM.taylor_multiplication.2.1 (n * g) 1
  simp only [jetN, jetOf]
  rw [hc, map_one, FBIdJet.psJet_one, map_one]

theorem jetN_pow {n g : ℕ} (m : ℕ) {f : (Fin n → Fin g → ℂ) → ℂ} (hf : AnO f) (p : ℕ) :
    jetN m (fun w => f w ^ p) = jetN m f ^ p := by
  induction p with
  | zero =>
    simp only [pow_zero]
    exact jetN_one m
  | succ p ih =>
    have hp : AnO fun w => f w ^ p := by
      unfold AnO at hf ⊢
      exact hf.pow p
    rw [show (fun w => f w ^ (p + 1)) = fun w => f w ^ p * f w from funext fun w => pow_succ (f w) p,
      jetN_mul m hp hf, ih]
    exact (pow_succ _ _).symm

theorem jetN_inv_mul {n g : ℕ} (m : ℕ) {f : (Fin n → Fin g → ℂ) → ℂ} (hf : AnO f) (h0 : f (colsOf n g 0) ≠ 0) :
    jetN m (fun w => (f w)⁻¹) * jetN m f = 1 := by
  have hf' : ContDiffAt ℂ ω (fun v => f (colsOf n g v)) 0 := hf
  have hinv : AnO fun w => (f w)⁻¹ := hf'.inv h0
  rw [← jetN_mul m hinv hf]
  have hev : (fun v => (f (colsOf n g v))⁻¹ * f (colsOf n g v)) =ᶠ[nhds 0] fun _ => (1 : ℂ) := by
    filter_upwards [hf'.continuousAt.eventually_ne h0] with v hv
    exact inv_mul_cancel₀ hv
  have h1 := jetN_one (n := n) (g := g) m
  simp only [jetN, jetOf] at h1 ⊢
  rw [TM.taylor_multiplication.2.2 _ _ _ hev]
  exact h1

theorem AnO.zpow {n g : ℕ} {f : (Fin n → Fin g → ℂ) → ℂ} (hf : AnO f) (h0 : f (colsOf n g 0) ≠ 0) (k : ℤ) :
    AnO fun w => f w ^ k := by
  have hf' : ContDiffAt ℂ ω (fun v => f (colsOf n g v)) 0 := hf
  show ContDiffAt ℂ ω (fun v => f (colsOf n g v) ^ k) 0
  obtain ⟨p, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simp only [zpow_natCast]
    exact hf'.pow p
  · simp only [zpow_neg, zpow_natCast]
    exact (hf'.pow p).inv (pow_ne_zero _ h0)

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
  {n m : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem origin_mem {ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left} {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (hψ : Φ.JetMap m ψ Λ) {U : A.left.Opens} (hU : ⊤ ≤ ψ ⁻¹ᵁ U) :
    ⊤ ≤ (Φ.e (Λ (colsOf n g 0))).left ⁻¹ᵁ U := by
  obtain ⟨hol, rfl⟩ := hψ
  have hz : IsLocalHom (jetZero (g := n * g) m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) := by
    unfold jetZero
    exact isLocalHom_jetMap _ _
  have hr : IsLocalHom (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) := by
    unfold renN
    exact isLocalHom_jetMap _ _
  have hc : ∀ F : (Fin (n * g) → ℂ) → ℂ, jetAug (jetOf m F) = F 0 := by
    intro F
    unfold jetOf psJet
    rw [jetAug_mk, FBIdJet.psTrunc_eq]
    show AddMonoidAlgebra.coeff _ 0 = _
    rw [MvPowerSeries.coeff_truncTotal _ (by simp), coeff_tay]
    simp [dirs, fct, TM.mD_zero]
  have hk : ∀ c : ℂ, jetOf m (fun _ : Fin (n * g) → ℂ => c) = algebraMap ℂ _ c := by
    intro c
    unfold jetOf psJet
    rw [TM.taylor_multiplication.2.1, ← MvPolynomial.coe_C, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]
    rfl
  have key := jetPt_precomp _ (fun _ => (Φ.e (Λ (colsOf n g 0))).left) hol (isHolFam_const _) rfl m
    (jetZero (g := n * g) m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) (fun U _ f => by
      rw [AlgHom.coe_toRingHom, jetZero_eq, hc, hk])
  rw [← jetPt_const] at key
  intro p _
  have h1 := hU (show IsLocalRing.closedPoint (Jet ℂ (Fin n × Fin g) m) ∈ (⊤ : (Sp (Jet ℂ (Fin n × Fin g) m)).Opens) from trivial)
  have h2 := congrArg (fun φ => φ (IsLocalRing.closedPoint (Jet ℂ (Fin 1 × Fin (n * g)) m))) key
  unfold spMap at h1 h2
  simp only [Scheme.Hom.comp_apply] at h1 h2
  have hz' : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom
      (jetZero (g := n * g) m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m))) := hz
  have hr' : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom
      (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m))) := hr
  have q1 : (Spec.map (CommRingCat.ofHom (jetZero (g := n * g) m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m)))
      (IsLocalRing.closedPoint (Jet ℂ (Fin 1 × Fin (n * g)) m)) = IsLocalRing.closedPoint _ :=
    AlgebraicGeometry.Spec_closedPoint
  have q2 : (Spec.map (CommRingCat.ofHom (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m)))
      (IsLocalRing.closedPoint (Jet ℂ (Fin n × Fin g) m)) = IsLocalRing.closedPoint _ :=
    AlgebraicGeometry.Spec_closedPoint
  have hp : ∀ q r : PrimeSpectrum ℂ, q = r := fun q r =>
    PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm)
  show (Over.Hom.left (Φ.e (Λ (colsOf n g 0)))) p ∈ U
  rw [hp p ((Spec.map (CommRingCat.ofHom (algebraMap ℂ (Jet ℂ (Fin 1 × Fin (n * g)) m))))
    (IsLocalRing.closedPoint (Jet ℂ (Fin 1 × Fin (n * g)) m)))]
  refine (congrArg (fun z => z ∈ U) h2).mp ?_
  exact (congrArg (fun z => (jetPt (fun v => Over.Hom.left (Φ.e (Λ (colsOf n g v)))) hol m) z ∈ U)
    (q1.trans q2.symm)).mpr h1

theorem anO_fr {ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left} {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (hψ : Φ.JetMap m ψ Λ) {j : L.L.ι} (hU : ⊤ ≤ ψ ⁻¹ᵁ L.L.U j) : AnO fun w => Φ.fr j (Λ w) := by
  have h0 := origin_mem Φ hψ hU
  have hopen := (Φ.hol (L.L.U j) 0).1
  have han : AnalyticAt ℂ (Φ.fr j) (Λ (colsOf n g 0)) :=
    ReciprocityTheory.AnForm.Osgood.osgood g _ _ hopen (Φ.fr_hol j) _ h0
  have hc : ContDiff ℂ ω (fun v : Fin (n * g) → ℂ => colsOf n g v) := by
    unfold colsOf
    fun_prop
  have hΛ : ContDiff ℂ ω (fun x : Fin n → Fin g → ℂ => Λ x) := (LinearMap.toContinuousLinearMap Λ).contDiff
  show ContDiffAt ℂ ω (fun v => Φ.fr j (Λ (colsOf n g v))) 0
  exact han.contDiffAt.comp (x := 0) (hΛ.comp hc).contDiffAt

variable {K : Type} [Fintype K] {φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)}
  {Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}

theorem anO_prod (hφ : ∀ k, Φ.JetMap m (φ k) (Λ k)) (ε : K → ℤ) {j : K → L.L.ι} (h : ⊤ ≤ LB.wchart L.L φ j) :
    AnO fun w => ∏ k, Φ.fr (j k) (Λ k w) ^ ε k := by
  classical
  have hk : ∀ k, ⊤ ≤ φ k ⁻¹ᵁ L.L.U (j k) := fun k x _ => by
    have hx := h (show x ∈ (⊤ : (Sp (Jet ℂ (Fin n × Fin g) m)).Opens) from trivial)
    unfold LB.wchart at hx
    exact Set.mem_iInter.1 hx k
  have hne : ∀ k, Φ.fr (j k) (Λ k (colsOf n g 0)) ≠ 0 := fun k => Φ.fr_ne _ _ (origin_mem Φ (hφ k) (hk k))
  have hfr : ∀ k, AnO fun w => Φ.fr (j k) (Λ k w) := fun k => anO_fr Φ (hφ k) (hk k)
  have key : ∀ s : Finset K,
      ContDiffAt ℂ ω (fun v => ∏ k ∈ s, Φ.fr (j k) (Λ k (colsOf n g v)) ^ ε k) 0 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp only [Finset.prod_empty]
      exact contDiffAt_const
    · intro a s ha ih
      simp only [Finset.prod_insert ha]
      exact (show ContDiffAt ℂ ω (fun v => Φ.fr (j a) (Λ a (colsOf n g v)) ^ ε a) 0 from
        AnO.zpow (hfr a) (hne a) (ε a)).mul ih
  exact key Finset.univ

theorem prod_ne (hφ : ∀ k, Φ.JetMap m (φ k) (Λ k)) (ε : K → ℤ) {j : K → L.L.ι} (h : ⊤ ≤ LB.wchart L.L φ j) :
    ∏ k, Φ.fr (j k) (Λ k (colsOf n g 0)) ^ ε k ≠ 0 := by
  have hk : ∀ k, ⊤ ≤ φ k ⁻¹ᵁ L.L.U (j k) := fun k x _ => by
    have hx := h (show x ∈ (⊤ : (Sp (Jet ℂ (Fin n × Fin g) m)).Opens) from trivial)
    unfold LB.wchart at hx
    exact Set.mem_iInter.1 hx k
  have hne : ∀ k, Φ.fr (j k) (Λ k (colsOf n g 0)) ≠ 0 := fun k => Φ.fr_ne _ _ (origin_mem Φ (hφ k) (hk k))
  exact Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne k)

end

theorem map_res_val {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (h' : ⊤ ≤ V) (u : Γ(X, U)ˣ) :
    (X.presheaf.map (homOfLE h').op).hom (Semi.res h u).val =
      (X.presheaf.map (homOfLE (h'.trans h)).op).hom u.val := by
  unfold Semi.res
  show (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE h').op).hom u.val = _
  rw [← Functor.map_comp]
  rfl

end GlobalTheory.AnVal.JetAlg


open GlobalTheory.AnVal.JetAlg in
set_option backward.isDefEq.respectTransparency false in
theorem GlobalTheory.AnVal.jetRd_mul_inv_pow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n m : ℕ) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (φ' : K' → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε' : K' → ℤ) (τ' : LB.Gen (LB.LinComb L.L φ' ε')) (Λ' : K' → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.JetRd m φ ε τ Λ → Φ.JetRd m φ' ε' τ' Λ' → Φ.JetRd m (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L.L φ ε φ' ε' τ τ') (Sum.elim Λ Λ') ∧ Φ.JetRd m φ (fun k => -ε k) (LB.invGen L.L φ ε τ) Λ ∧ ∀ p : ℕ, Φ.JetRd m φ (fun k => (p : ℤ) * ε k) ⟨fun j => τ.s j ^ p⟩ Λ := by
  intro S A _ _ L x0 g Φ n m K K' _ _ φ ε τ Λ φ' ε' τ' Λ' h1 h2
  refine ⟨⟨fun k => ?_, fun j h => ?_⟩, ⟨h1.1, fun j h => ?_⟩, fun p => ⟨h1.1, fun j h => ?_⟩⟩
  · cases k with
    | inl k => exact h1.1 k
    | inr k => exact h2.1 k
  · have hL : ⊤ ≤ LB.wchart L.L φ (j ∘ Sum.inl) := fun x _ => by
      have hx := h (show x ∈ (⊤ : (Sp (Jet ℂ (Fin n × Fin g) m)).Opens) from trivial)
      unfold LB.wchart at hx ⊢
      exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inl k)
    have hR : ⊤ ≤ LB.wchart L.L φ' (j ∘ Sum.inr) := fun x _ => by
      have hx := h (show x ∈ (⊤ : (Sp (Jet ℂ (Fin n × Fin g) m)).Opens) from trivial)
      unfold LB.wchart at hx ⊢
      exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inr k)
    unfold LB.mulGen
    rw [Units.val_mul, map_mul, map_res_val, map_res_val]
    refine (congrArg₂ (· * ·) (h1.2 (j ∘ Sum.inl) hL) (h2.2 (j ∘ Sum.inr) hR)).trans ?_
    rw [← map_mul, ← jetN_mul m (anO_prod Φ h1.1 ε hL) (anO_prod Φ h2.1 ε' hR)]
    refine congrArg (toΓ _) (congrArg (jetN m) (funext fun w => ?_))
    rw [Fintype.prod_sum_type]
    rfl
  · have e1 : ((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map (homOfLE h).op).hom ((τ.s j)⁻¹).val *
        ((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map (homOfLE h).op).hom (τ.s j).val = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [h1.2 j h] at e1
    have e2 := jetN_inv_mul m (anO_prod Φ h1.1 ε h) (prod_ne Φ h1.1 ε h)
    have hG : (fun w => ∏ k, Φ.fr (j k) (Λ k w) ^ (-ε k)) = fun w => (∏ k, Φ.fr (j k) (Λ k w) ^ ε k)⁻¹ := by
      funext w
      simp only [zpow_neg, Finset.prod_inv_distrib]
    refine left_inv_eq_right_inv e1 ?_
    rw [mul_comm, ← map_mul]
    beta_reduce
    rw [hG, e2, map_one]
  · have hP : (fun w => ∏ k, Φ.fr (j k) (Λ k w) ^ ((p : ℤ) * ε k)) = fun w => (∏ k, Φ.fr (j k) (Λ k w) ^ ε k) ^ p := by
      funext w
      simp only [mul_comm (p : ℤ), zpow_mul, zpow_natCast, Finset.prod_pow]
    beta_reduce
    rw [hP, jetN_pow m (anO_prod Φ h1.1 ε h) p, map_pow, ← h1.2 j h, ← map_pow, ← Units.val_pow_eq_pow_val]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SectionReadingExistsUniqueIsTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SectionReadingExistsUniqueIsTheta
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem isHolFam_vtfQ {x0 : Sp ℂ ⟶ S} {g : ℕ} (e : (Fin g → ℂ) → (Over.mk x0 ⟶ A))
    (hol : IsHolFam (fun z => (e z).left)) : IsHolFam (fun z => (vtfQ A (e z)).left) := by
  have he : ∀ z, (e z).left ≫ A.hom = x0 := fun z => Over.w (e z)
  have h := isHolFam_vtfLift A.hom x0 (fun z => (e z).left) he hol
  let σ : pullback A.hom x0 ⟶ (Over.mk x0 ⊗ A).left := (pullbackSymmetry A.hom x0).hom
  have key : ∀ z, (vtfQ A (e z)).left = vtfLift A.hom x0 (fun z => (e z).left) he z ≫ σ := by
    intro z
    symm
    apply vtf_pt_uniq
    · have : σ ≫ (snd (Over.mk x0) A).left = pullback.fst A.hom x0 :=
        pullbackSymmetry_hom_comp_snd A.hom x0
      rw [Category.assoc, this]
      exact pullback.lift_fst _ _ _
    · have : σ ≫ (fst (Over.mk x0) A).left = pullback.snd A.hom x0 :=
        pullbackSymmetry_hom_comp_fst A.hom x0
      rw [Category.assoc, this]
      exact pullback.lift_snd _ _ _
  intro V φ
  have h1 := h (σ ⁻¹ᵁ V) ((σ.app V).hom φ)
  have h2 : (fun z => valAt' (vtfQ A (e z)).left V φ) = fun z =>
      valAt' (vtfLift A.hom x0 (fun z => (e z).left) he z) (σ ⁻¹ᵁ V) ((σ.app V).hom φ) := by
    funext z
    rw [key]
    exact (valAt'_comp _ σ V φ).symm
  have h3 : {z | ⊤ ≤ (vtfQ A (e z)).left ⁻¹ᵁ V} =
      {z | ⊤ ≤ vtfLift A.hom x0 (fun z => (e z).left) he z ⁻¹ᵁ (σ ⁻¹ᵁ V)} := by
    ext z
    rw [Set.mem_ofPred_eq, key]
    rfl
  exact ⟨h3 ▸ h1.1, h3 ▸ h2 ▸ h1.2⟩

variable {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem AnFr.exists_chart_e (z : Fin g → ℂ) : ∃ j, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j := by
  have h : (Φ.e z).left cpt ∈ ⨆ i, L.L.U i := by rw [L.isLB.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨j, top_le_of_mem hj⟩

theorem AnFr.rd_val {k : ℤ} {F : LB.Sec (LPow A L.L k (Over.mk x0))} {θ : (Fin g → ℂ) → ℂ} (h : Φ.Rd k F θ)
    (j : L.L.ι) (z : Fin g → ℂ) (hj : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j) :
    valAt' (vtfQ A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) =
      θ z * Φ.fr j z ^ k :=
  h j z _ (vtfQ_snd A _) (vtfQ_fst A _) hj

theorem AnFr.rd_iff (k : ℤ) (F : LB.Sec (LPow A L.L k (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ) :
    Φ.Rd k F θ ↔ ∀ z, ∃ j, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j ∧
      valAt' (vtfQ A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) =
        θ z * Φ.fr j z ^ k := by
  constructor
  · intro h z
    obtain ⟨j, hj⟩ := Φ.exists_chart_e z
    exact ⟨j, hj, Φ.rd_val h j z hj⟩
  · intro h j' z pt h1 h2 hj'
    obtain ⟨j, hj, hv⟩ := h z
    rw [vtf_pt_uniq A (Φ.e z) pt h1 h2]
    exact vtf_read A L.L F (Φ.e z) (fun j => Φ.fr j z) (fun a b hab => Φ.fr_g a b z hab) j j' hj hj' _ hv

theorem AnFr.rd_eq_div {k : ℤ} {F : LB.Sec (LPow A L.L k (Over.mk x0))} {θ : (Fin g → ℂ) → ℂ} (h : Φ.Rd k F θ)
    (j : L.L.ι) (z : Fin g → ℂ) (hj : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j) :
    θ z = valAt' (vtfQ A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) /
      Φ.fr j z ^ k := by
  rw [Φ.rd_val h j z hj, mul_div_cancel_right₀ _ (zpow_ne_zero _ (Φ.fr_ne j z hj))]

theorem AnFr.existsUnique_rd (k : ℤ) (F : LB.Sec (LPow A L.L k (Over.mk x0))) : ∃! θ, Φ.Rd k F θ := by
  choose c hc using Φ.exists_chart_e
  refine ⟨fun z => valAt' (vtfQ A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => c z))
    (F.f (fun _ => c z)) / Φ.fr (c z) z ^ k, ?_, fun θ hθ => ?_⟩
  · refine (Φ.rd_iff k F _).2 fun z => ⟨c z, hc z, ?_⟩
    rw [div_mul_cancel₀ _ (zpow_ne_zero _ (Φ.fr_ne _ z (hc z)))]
  · funext z
    exact Φ.rd_eq_div hθ (c z) z (hc z)

theorem AnFr.e_add_lat {a : Fin g → ℂ} (ha : a ∈ Φ.lat) (z : Fin g → ℂ) : Φ.e (z + a) = Φ.e z := by
  rw [Φ.e_add, (Φ.e_ker a).2 ha, _root_.mul_one]

theorem AnFr.isTh_of_rd {k : ℤ} {F : LB.Sec (LPow A L.L k (Over.mk x0))} {θ : (Fin g → ℂ) → ℂ}
    (h : Φ.Rd k F θ) : Φ.IsTh k θ := by
  constructor
  · intro z0
    obtain ⟨j, hj⟩ := Φ.exists_chart_e z0
    have hO : IsOpen {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j} := (Φ.hol (L.L.U j) 0).1
    have hv := (isHolFam_vtfQ Φ.e Φ.hol ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j))).2
    have hv' := hv.mono (s := {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j})
      (fun z hz => vtf_chart A L.L k (Φ.e z) (fun _ => j) hz)
    have hd : DifferentiableOn ℂ θ {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j} :=
      (hv'.mul ((Φ.fr_hol j).zpow (m := -k) (Or.inl fun z hz => Φ.fr_ne j z hz))).congr fun z hz => by
        rw [Φ.rd_eq_div h j z hz, div_eq_mul_inv, ← zpow_neg]
        rfl
    exact hd.differentiableAt (hO.mem_nhds hj)
  · intro a ha z
    obtain ⟨j, hj⟩ := Φ.exists_chart_e z
    have hj' : ⊤ ≤ (Φ.e (z + a)).left ⁻¹ᵁ L.L.U j := by rw [Φ.e_add_lat ha]; exact hj
    have h1 := Φ.rd_val h j z hj
    have h2 := Φ.rd_val h j (z + a) hj'
    rw [Φ.e_add_lat ha, h1, Φ.fr_per a ha j z hj, mul_zpow] at h2
    apply mul_right_cancel₀ (zpow_ne_zero k (Φ.fr_ne j (z + a) hj'))
    rw [← h2, AnFr.fac]
    ring

theorem reading_existsUnique_isTh : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (F : LB.Sec (LPow A L.L k (Over.mk x0))), (∃! θ, Φ.Rd k F θ) ∧ (∀ θ, Φ.Rd k F θ → Φ.IsTh k θ) ∧ ∀ θ, Φ.Rd k F θ ↔ ∀ z, ∃ j, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j ∧ valAt' (ptSecT A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) = θ z * Φ.fr j z ^ k := by
  intro S A _ _ L x0 g Φ k F
  exact ⟨Φ.existsUnique_rd k F, fun θ h => Φ.isTh_of_rd h, fun θ => Φ.rd_iff k F θ⟩

end GlobalTheory.AnVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SectionReadingExistsUniqueIsThetaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_reading_existsUnique_isTheta : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (F : LB.Sec (LPow A L.L k (Over.mk x0))), (∃! θ, Φ.Rd k F θ) ∧ (∀ θ, Φ.Rd k F θ → Φ.IsTh k θ) ∧ ∀ θ, Φ.Rd k F θ ↔ ∀ z, ∃ j, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j ∧ valAt' (ptSecT A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) = θ z * Φ.fr j z ^ k := by
  first | exact @GlobalTheory.AnVal.reading_existsUnique_isTh | exact GlobalTheory.AnVal.reading_existsUnique_isTh | (intros; apply GlobalTheory.AnVal.reading_existsUnique_isTh <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsHolomorphicGeneratorReadingAutomorphy
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsHolomorphicGeneratorReadingAutomorphy
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnValGenRd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt

attribute [local instance] Over.cartesianMonoidalCategory

theorem differentiableAt_prod {E K : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : Finset K)
    (f : K → E → ℂ) (z : E) (h : ∀ k, DifferentiableAt ℂ (f k) z) :
    DifferentiableAt ℂ (fun w => ∏ k ∈ s, f k w) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

private theorem preimage_eq_univ_iff_forall_mem {W : Scheme.{0}} (x : Sp ℂ ⟶ W) (U : W.Opens) :
    ⊤ ≤ x ⁻¹ᵁ U ↔ ∀ p, x p ∈ U := by
  constructor
  · intro h p
    exact h (show p ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  · intro h p _
    exact h p

section LC

variable {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

theorem top_le_wchart_iff (φ : K → (Y ⟶ X)) (j : K → L.ι) (x : Sp ℂ ⟶ Y) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  simp only [preimage_eq_univ_iff_forall_mem]
  unfold LB.wchart
  constructor
  · intro h k p
    exact Set.mem_iInter.1 (h p) k
  · intro h p
    exact Set.mem_iInter.2 fun k => h k p

theorem top_le_inf {x : Sp ℂ ⟶ Y} {U V : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ V) :
    ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) := by
  rw [preimage_eq_univ_iff_forall_mem] at h h' ⊢
  intro p
  exact TopologicalSpace.Opens.mem_inf.2 ⟨h p, h' p⟩

theorem val_prod (x : Sp ℂ ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (u : K → Γ(Y, U)ˣ) :
    valAt' x U (∏ k, u k).val = ∏ k, valAt' x U (u k).val := by
  rw [Units.coe_prod]
  exact map_prod (valHom x U h) _ _

private theorem valAt'_app_hom_eq_valAt'_comp {W V : Scheme.{0}} (x : Sp ℂ ⟶ V) (ψ : V ⟶ W) (U : W.Opens) (f : Γ(W, U)) :
    valAt' x (ψ ⁻¹ᵁ U) ((ψ.app U).hom f) = valAt' (x ≫ ψ) U f := by
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (ψ ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U := h
    rw [dite_eq_left h, dite_eq_left h']
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U := h
    rw [dite_eq_right h, dite_eq_right h']

private theorem valAt'_pullU_eq_valAt'_comp {W V : Scheme.{0}} (x : Sp ℂ ⟶ V) (ψ : V ⟶ W) (U : W.Opens) (u : Γ(W, U)ˣ) :
    valAt' x (ψ ⁻¹ᵁ U) (pullU ψ U u).val = valAt' (x ≫ ψ) U u.val := by
  unfold pullU
  rw [Units.coe_map]
  exact valAt'_app_hom_eq_valAt'_comp x ψ U u.val

private theorem valAt'_res_unit_eq {W : Scheme.{0}} (x : Sp ℂ ⟶ W) {U V : W.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V)
    (u : Γ(W, U)ˣ) : valAt' x V (res hVU u).val = valAt' x U u.val := by
  unfold res
  rw [Units.coe_map]
  exact valAt'_res x hVU h u.val

private theorem valAt'_unit_zpow' {W : Scheme.{0}} (x : Sp ℂ ⟶ W) (U : W.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(W, U)ˣ)
    (n : ℤ) : valAt' x U (u ^ n).val = valAt' x U u.val ^ n := by
  have e := congrArg Units.val (map_zpow (Units.map (valHom x U h).toMonoidHom) u n)
  rw [Units.coe_map, Units.val_zpow_eq_zpow_val, Units.coe_map] at e
  exact e

theorem val_linComb_g (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Sp ℂ ⟶ Y) (j j' : K → L.ι)
    (h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    valAt' p (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j').val =
      ∏ k, valAt' (p ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k := by
  unfold LB.LinComb
  dsimp only
  rw [val_prod p _ h]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [valAt'_unit_zpow' p _ h]
  congr 1
  exact (valAt'_res_unit_eq p _ h _).trans (valAt'_pullU_eq_valAt'_comp p (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)))

theorem val_isGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (p : Sp ℂ ⟶ Y) (j j' : K → L.ι) (h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    valAt' p (LB.wchart L φ j) (t.s j).val =
      (∏ k, valAt' (p ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k) *
        valAt' p (LB.wchart L φ j') (t.s j').val := by
  have e := congrArg (fun u => valAt' p (LB.wchart L φ j ⊓ LB.wchart L φ j') (Units.val u)) (ht j j')
  simp only [Units.val_mul] at e
  have e1 := valAt'_res_unit_eq p (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j) h (t.s j)
  have e2 := valAt'_res_unit_eq p (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j') h (t.s j')
  have e3 := val_linComb_g L φ ε p j j' h
  exact e1.symm.trans (e.trans ((valAt'_mul _ _ _ _).trans (congrArg₂ (· * ·) e3 e2)))

theorem exists_chart (hL : L.IsLB) (φ : K → (Y ⟶ X)) (x : Sp ℂ ⟶ Y) :
    ∃ j : K → L.ι, ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j := by
  have hp : ∀ k, ∃ i, (x ≫ φ k) (default : PrimeSpectrum ℂ) ∈ L.U i := fun k => by
    have h0 : (x ≫ φ k) (default : PrimeSpectrum ℂ) ∈ (⨆ i, L.U i) := by
      rw [hL.cover]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.1 h0
  choose j hj using hp
  refine ⟨j, (top_le_wchart_iff L φ j x).2 fun k => (preimage_eq_univ_iff_forall_mem _ _).2 fun p => ?_⟩
  rw [Subsingleton.elim (α := PrimeSpectrum ℂ) p default]
  exact hj k

end LC

section Rd

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
  {Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε))

theorem top_le_chart {q : Sp ℂ ⟶ Z} {p : K → Fin g → ℂ} (hq : ∀ k, q ≫ φ k = (Φ.e (p k)).left) {j : K → L.L.ι}
    (hj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L.L φ j) (k : K) : ⊤ ≤ (Φ.e (p k)).left ⁻¹ᵁ L.L.U (j k) := by
  have h := (top_le_wchart_iff L.L φ j q).1 hj k
  rwa [hq k] at h

theorem prod_fr_ne {q : Sp ℂ ⟶ Z} {p : K → Fin g → ℂ} (hq : ∀ k, q ≫ φ k = (Φ.e (p k)).left) {j : K → L.L.ι}
    (hj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L.L φ j) : ∏ k, Φ.fr (j k) (p k) ^ ε k ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ ?_
  exact Φ.fr_ne _ _ (top_le_chart Φ φ hq hj k)

theorem genRd_of_chart (ht : t.IsGen) {q : Sp ℂ ⟶ Z} {p : K → Fin g → ℂ} (hq : ∀ k, q ≫ φ k = (Φ.e (p k)).left)
    {j' : K → L.L.ι} (hj' : ⊤ ≤ q ⁻¹ᵁ LB.wchart L.L φ j') :
    Φ.GenRd φ ε t q p (valAt' q (LB.wchart L.L φ j') (t.s j').val / ∏ k, Φ.fr (j' k) (p k) ^ ε k) := by
  refine ⟨hq, fun j hj => ?_⟩
  have hg : ∀ k, valAt' (q ≫ φ k) (L.L.U (j k) ⊓ L.L.U (j' k)) (L.L.g (j k) (j' k)).val =
      Φ.fr (j k) (p k) / Φ.fr (j' k) (p k) := fun k => by
    rw [hq k, eq_div_iff (Φ.fr_ne _ _ (top_le_chart Φ φ hq hj' k))]
    exact (Φ.fr_g _ _ _ (top_le_inf (top_le_chart Φ φ hq hj k) (top_le_chart Φ φ hq hj' k))).symm
  have hA := prod_fr_ne Φ φ ε hq hj
  have hB := prod_fr_ne Φ φ ε hq hj'
  rw [val_isGen L.L φ ε t ht q j j' (top_le_inf hj hj')]
  simp only [hg, div_zpow, Finset.prod_div_distrib]
  field_simp

theorem genRd_eq {q : Sp ℂ ⟶ Z} {p : K → Fin g → ℂ} {u : ℂ} (hu : Φ.GenRd φ ε t q p u)
    {j : K → L.L.ι} (hj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L.L φ j) :
    u = valAt' q (LB.wchart L.L φ j) (t.s j).val / ∏ k, Φ.fr (j k) (p k) ^ ε k := by
  rw [eq_div_iff (prod_fr_ne Φ φ ε hu.1 hj)]
  exact (hu.2 j hj).symm

private theorem valAt'_unit_val_ne_zero {W : Scheme.{0}} (x : Sp ℂ ⟶ W) (U : W.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (u : Γ(W, U)ˣ) : valAt' x U u.val ≠ 0 :=
  (u.isUnit.map (valHom x U h)).ne_zero

end Rd

theorem exists_reading : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)), t.IsGen → ∀ (N : ℕ) (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z)) (p : K → (Fin N → ℂ) → Fin g → ℂ), IsHolFam q → (∀ k, Differentiable ℂ (p k)) → (∀ z k, q z ≫ φ k = (Φ.e (p k z)).left) → ∃ v : (Fin N → ℂ) → ℂ, Differentiable ℂ v ∧ (∀ z, v z ≠ 0) ∧ (∀ z, Φ.GenRd φ ε t (q z) (fun k => p k z) (v z)) ∧ (∀ z u, Φ.GenRd φ ε t (q z) (fun k => p k z) u → u = v z) ∧ ∀ z z' (a : K → Fin g → ℂ), q z' = q z → (∀ k, a k ∈ Φ.lat ∧ p k z' = p k z + a k) → v z' = v z * ∏ k, Φ.fac (a k) (p k z) ^ ε k := by
  intro S A _ _ L x0 g Φ Z K _ φ ε t ht N q p hq hp hqp
  have hL : L.L.IsLB := L.isLB
  have hJ : ∀ z, ∃ j : K → L.L.ι, ⊤ ≤ q z ⁻¹ᵁ LB.wchart L.L φ j := fun z => exists_chart L.L hL φ (q z)
  choose J hJ using hJ
  have hgen : ∀ z, Φ.GenRd φ ε t (q z) (fun k => p k z)
      (valAt' (q z) (LB.wchart L.L φ (J z)) (t.s (J z)).val / ∏ k, Φ.fr (J z k) (p k z) ^ ε k) :=
    fun z => genRd_of_chart Φ φ ε t ht (fun k => hqp z k) (hJ z)
  refine ⟨fun z => valAt' (q z) (LB.wchart L.L φ (J z)) (t.s (J z)).val / ∏ k, Φ.fr (J z k) (p k z) ^ ε k,
    ?_, ?_, hgen, fun z u hu => genRd_eq Φ φ ε t hu (hJ z), ?_⟩
  · intro z0
    have hO := (hq (LB.wchart L.L φ (J z0)) (t.s (J z0)).val).1
    have hz0 : z0 ∈ {z | ⊤ ≤ q z ⁻¹ᵁ LB.wchart L.L φ (J z0)} := hJ z0
    have hnum : DifferentiableAt ℂ (fun z => valAt' (q z) (LB.wchart L.L φ (J z0)) (t.s (J z0)).val) z0 :=
      ((hq (LB.wchart L.L φ (J z0)) (t.s (J z0)).val).2 z0 hz0).differentiableAt (hO.mem_nhds hz0)
    have hfac : ∀ k, DifferentiableAt ℂ (fun z => Φ.fr (J z0 k) (p k z) ^ ε k) z0 := fun k => by
      have hc := top_le_chart Φ φ (fun k => hqp z0 k) (hJ z0) k
      have hO' := (Φ.hol (L.L.U (J z0 k)) 1).1
      have hfr : DifferentiableAt ℂ (Φ.fr (J z0 k)) (p k z0) :=
        (Φ.fr_hol (J z0 k) (p k z0) hc).differentiableAt (hO'.mem_nhds hc)
      exact (hfr.comp z0 ((hp k) z0)).zpow (Or.inl (Φ.fr_ne _ _ hc))
    have hden := differentiableAt_prod (Finset.univ : Finset K) (fun k z => Φ.fr (J z0 k) (p k z) ^ ε k) z0 hfac
    have hne := prod_fr_ne Φ φ ε (fun k => hqp z0 k) (hJ z0)
    have hinv : DifferentiableAt ℂ (fun z => (∏ k, Φ.fr (J z0 k) (p k z) ^ ε k)⁻¹) z0 := hden.inv hne
    have hw : DifferentiableAt ℂ (fun z => valAt' (q z) (LB.wchart L.L φ (J z0)) (t.s (J z0)).val /
        ∏ k, Φ.fr (J z0 k) (p k z) ^ ε k) z0 := by
      simpa only [div_eq_mul_inv, Pi.mul_def] using hnum.mul hinv
    refine hw.congr_of_eventuallyEq (Filter.eventually_of_mem (hO.mem_nhds hz0) fun z hz => ?_)
    exact genRd_eq Φ φ ε t (hgen z) hz
  · intro z
    exact div_ne_zero (valAt'_unit_val_ne_zero _ _ (hJ z) _) (prod_fr_ne Φ φ ε (fun k => hqp z k) (hJ z))
  · intro z z' a hzz ha
    have hz' : ⊤ ≤ q z' ⁻¹ᵁ LB.wchart L.L φ (J z) := by
      rw [hzz]
      exact hJ z
    have hA := prod_fr_ne Φ φ ε (fun k => hqp z' k) hz'
    have hper : ∀ k, Φ.fr (J z k) (p k z) = Φ.fac (a k) (p k z) * Φ.fr (J z k) (p k z + a k) := fun k =>
      Φ.fr_per (a k) (ha k).1 (J z k) (p k z) (top_le_chart Φ φ (fun k => hqp z k) (hJ z) k)
    have hC := prod_fr_ne Φ φ ε (fun k => hqp z k) (hJ z)
    have hB : ∏ k, Φ.fac (a k) (p k z) ^ ε k ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ ?_
      intro h0
      have h1 := Φ.fr_ne _ _ (top_le_chart Φ φ (fun k => hqp z k) (hJ z) k)
      rw [hper k, h0, zero_mul] at h1
      exact h1 rfl
    show valAt' (q z') (LB.wchart L.L φ (J z')) (t.s (J z')).val / ∏ k, Φ.fr (J z' k) (p k z') ^ ε k = _
    rw [genRd_eq Φ φ ε t (hgen z') hz', hzz]
    simp only [(ha _).2] at hA ⊢
    simp only [hper, mul_zpow, Finset.prod_mul_distrib]
    field_simp

end GlobalTheory.AnValGenRd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsHolomorphicGeneratorReadingAutomorphyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_generator_reading_automorphy : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)), t.IsGen → ∀ (N : ℕ) (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z)) (p : K → (Fin N → ℂ) → Fin g → ℂ), IsHolFam q → (∀ k, Differentiable ℂ (p k)) → (∀ z k, q z ≫ φ k = (Φ.e (p k z)).left) → ∃ v : (Fin N → ℂ) → ℂ, Differentiable ℂ v ∧ (∀ z, v z ≠ 0) ∧ (∀ z, Φ.GenRd φ ε t (q z) (fun k => p k z) (v z)) ∧ (∀ z u, Φ.GenRd φ ε t (q z) (fun k => p k z) u → u = v z) ∧ ∀ z z' (a : K → Fin g → ℂ), q z' = q z → (∀ k, a k ∈ Φ.lat ∧ p k z' = p k z + a k) → v z' = v z * ∏ k, Φ.fac (a k) (p k z) ^ ε k := by
  first | exact @GlobalTheory.AnValGenRd.exists_reading | exact GlobalTheory.AnValGenRd.exists_reading | (intros; apply GlobalTheory.AnValGenRd.exists_reading <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsGeneratorJetReading
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsGeneratorJetReading
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnValJetEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

theorem jet_point_eq {K : Type} [Field K] {I : Type} {m : ℕ} (p : PrimeSpectrum (Jet K I m)) :
    p = IsLocalRing.closedPoint (Jet K I m) := by
  apply PrimeSpectrum.ext
  refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun a ha => ?_
  have hn : IsNilpotent a := by
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h0 : MvPolynomial.constantCoeff q = 0 := by
      by_contra hne
      exact (IsLocalRing.mem_maximalIdeal _).mp ha (isUnit_of_jetAug _ (by rwa [jetAug_mk]))
    have := jet_nilpotent_of_orig K I m (sub_const_mem_orig (R := K) q)
    rwa [h0, map_zero, sub_zero] at this
  obtain ⟨n, hn⟩ := hn
  exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a := by
  apply Units.ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_id' {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)ˣ) : res h a = a := by
  apply Units.ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  have : (homOfLE h).op = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

theorem res_pullU {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U)
    (h' : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(X, U)ˣ) (b : Γ(Y, ⊤)ˣ) (hb : (f.appLE U ⊤ h').hom a.val = b.val) :
    res h (pullU f U a) = res (le_top : W ≤ ⊤) b := by
  have : b = res h' (pullU f U a) := Units.ext hb.symm
  rw [this, res_res']

theorem exists_gen_of_units {X Y : Scheme.{0}} (L : LB X) (hY : ∀ p q : Y, p = q) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (u : K → L.ι → Γ(Y, ⊤)ˣ)
    (hu : ∀ k j j' (h : ⊤ ≤ φ k ⁻¹ᵁ (L.U j ⊓ L.U j')),
      (u k j).val = ((φ k).appLE _ ⊤ h).hom (L.g j j').val * (u k j').val) :
    ∃ τ : LB.Gen (LB.LinComb L φ ε), τ.IsGen ∧ ∀ (j : K → L.ι) (h : ⊤ ≤ LB.wchart L φ j),
      (Y.presheaf.map (homOfLE h).op).hom (τ.s j).val = (∏ k, u k (j k) ^ ε k).val := by
  refine ⟨⟨fun j => res le_top (∏ k, u k (j k) ^ ε k)⟩, fun (i : K → L.ι) (j : K → L.ι) => ?_, fun j h => ?_⟩
  · by_cases hne : ∃ p, p ∈ LB.wchart L φ i ⊓ LB.wchart L φ j
    · obtain ⟨p, hp⟩ := hne
      have hk : ∀ k, ⊤ ≤ φ k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)) := fun k q _ => by
        rw [hY q p]
        exact ⟨LB.wchart_le L φ i k hp.1, LB.wchart_le L φ j k hp.2⟩
      have hle : ∀ k, LB.wchart L φ i ⊓ LB.wchart L φ j ≤ φ k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)) := fun k =>
        le_top.trans (hk k)
      show res (inf_le_left : LB.wchart L φ i ⊓ LB.wchart L φ j ≤ LB.wchart L φ i) (res le_top (∏ k, u k (i k) ^ ε k)) =
        (∏ k, (res (hle k) (pullU (φ k) _ (L.g (i k) (j k)))) ^ (ε k)) *
          res (inf_le_right : LB.wchart L φ i ⊓ LB.wchart L φ j ≤ LB.wchart L φ j) (res le_top (∏ k, u k (j k) ^ ε k))
      rw [res_res', res_res', map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [res_pullU (φ k) _ _ (hk k) (L.g (i k) (j k)) (u k (i k) * (u k (j k))⁻¹)
        (by rw [Units.val_mul, hu k _ _ (hk k), Units.mul_inv_cancel_right]), map_zpow, map_zpow, ← mul_zpow,
        ← map_mul, inv_mul_cancel_right]
    · have hb : LB.wchart L φ i ⊓ LB.wchart L φ j = ⊥ :=
        le_bot_iff.1 fun p hp => (hne ⟨p, hp⟩).elim
      have : Subsingleton Γ(Y, LB.wchart L φ i ⊓ LB.wchart L φ j) := by
        rw [hb]; infer_instance
      exact Units.ext (this.elim _ _)
  · exact congrArg Units.val ((res_res' le_top h _).trans (res_id' _ _))

theorem jetOf_one {d : ℕ} (m : ℕ) : jetOf m (fun _ : Fin d → ℂ => (1 : ℂ)) = 1 := by
  rw [jetOf_const, map_one]

theorem jetOf_pow {d : ℕ} (m : ℕ) {f : (Fin d → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (k : ℕ) :
    jetOf m (fun z => f z ^ k) = jetOf m f ^ k := by
  induction k with
  | zero => simpa using jetOf_one m
  | succ k ih =>
    rw [pow_succ, ← ih, ← jetOf_mul m (hf.pow k) hf]
    congr 1

theorem contDiffAt_zpow' {d : ℕ} {f : (Fin d → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (h0 : f 0 ≠ 0) (k : ℤ) :
    ContDiffAt ℂ ω (fun z => f z ^ k) 0 := by
  cases k with
  | ofNat k => simpa using hf.pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)

theorem jetOf_zpow {d : ℕ} (m : ℕ) {f : (Fin d → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (h0 : f 0 ≠ 0)
    (u : (Jet ℂ (Fin 1 × Fin d) m)ˣ) (hu : u.val = jetOf m f) (k : ℤ) :
    jetOf m (fun z => f z ^ k) = (u ^ k).val := by
  cases k with
  | ofNat k => simpa [hu] using jetOf_pow m hf k
  | negSucc k =>
    rw [zpow_negSucc]
    refine Units.eq_inv_of_mul_eq_one_left ?_
    rw [Units.val_pow_eq_pow_val, hu, ← jetOf_pow m hf,
      ← jetOf_mul m (hf.pow (k + 1)) (contDiffAt_zpow' hf h0 _), ← jetOf_one m]
    refine jetOf_congr m ((hf.continuousAt.eventually_ne h0).mono fun z hz => ?_)
    show f z ^ (k + 1) * f z ^ (Int.negSucc k) = 1
    rw [zpow_negSucc, mul_inv_cancel₀ (pow_ne_zero _ hz)]

theorem jetOf_prod {d : ℕ} (m : ℕ) {K : Type} (s : Finset K) {f : K → (Fin d → ℂ) → ℂ}
    (hf : ∀ k, ContDiffAt ℂ ω (f k) 0) :
    jetOf m (fun z => ∏ k ∈ s, f k z) = ∏ k ∈ s, jetOf m (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jetOf_one m
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← ih, ← jetOf_mul m (hf a) (contDiffAt_prod fun k _ => hf k)]
    congr 1
    funext z
    simp [Finset.prod_insert ha]

theorem appLE_spMap_jetPt {d : ℕ} {Y : Scheme.{0}} (e : (Fin d → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (m : ℕ)
    {R : Type} [CommRing R] (r : Jet ℂ (Fin 1 × Fin d) m →+* R) (U : Y.Opens) (hU : e 0 cpt ∈ U)
    (h : ⊤ ≤ (spMap r ≫ jetPt e hol m) ⁻¹ᵁ U) (a : Γ(Y, U)) :
    ((spMap r ≫ jetPt e hol m).appLE U ⊤ h).hom a = toΓ R (r (jetOf m fun z => valAt' (e z) U a)) := by
  have h1 : ⊤ ≤ jetPt e hol m ⁻¹ᵁ U := fun p _ => by
    rw [jet_point_eq (K := ℂ) (I := Fin 1 × Fin d) (m := m) p]
    show jetPt e hol m (IsLocalRing.closedPoint _) ∈ U
    rwa [jetPt_closedPoint]
  have e1 : (spMap r ≫ jetPt e hol m).appLE U ⊤ h = (jetPt e hol m).appLE U ⊤ h1 ≫ (spMap r).appTop :=
    (Scheme.Hom.appLE_comp_appLE (spMap r) (jetPt e hol m) U ⊤ ⊤ h1 le_rfl).symm
  rw [e1, jetPt_appLE e hol m U hU h1, Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem mem_of_spMap_jetPt {d : ℕ} {Y : Scheme.{0}} (e : (Fin d → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (m : ℕ)
    {I : Type} (r : Jet ℂ (Fin 1 × Fin d) m →+* Jet ℂ I m) (U : Y.Opens)
    (h : ⊤ ≤ (spMap r ≫ jetPt e hol m) ⁻¹ᵁ U) : e 0 cpt ∈ U := by
  let p : Sp (Jet ℂ I m) := IsLocalRing.closedPoint (Jet ℂ I m)
  have h2 : (spMap r ≫ jetPt e hol m) p ∈ U := h (show p ∈ (⊤ : (Sp (Jet ℂ I m)).Opens) from trivial)
  rw [Scheme.Hom.comp_apply] at h2
  rw [← jetPt_closedPoint e hol m, ← jet_point_eq (K := ℂ) (I := Fin 1 × Fin d) (m := m) (spMap r p)]
  exact h2

theorem contDiffAt_fr {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) {n : ℕ} (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (j : L.L.ι)
    (h : (Φ.e (Λ (colsOf n g 0))).left cpt ∈ L.L.U j) :
    ContDiffAt ℂ ω (fun v => Φ.fr j (Λ (colsOf n g v))) 0 := by
  have h1 : ContDiffAt ℂ ω (Φ.fr j) (Λ (colsOf n g 0)) :=
    (ReciprocityTheory.AnForm.Osgood.osgood g {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j} (Φ.fr j) (Φ.hol (L.L.U j) 0).1 (Φ.fr_hol j) _
      (top_le_of_mem h)).contDiffAt
  have h2 : ContDiff ℂ ω (colsOf n g) :=
    contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_apply ℂ (fun _ => ℂ) (finProdFinEquiv (i, j))
  have h3 : ContDiff ℂ ω (fun v => Λ (colsOf n g v)) :=
    (LinearMap.toContinuousLinearMap Λ).contDiff.comp h2
  exact h1.comp 0 h3.contDiffAt

theorem exists_gen_jetRd : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n m : ℕ) (K : Type) [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ k, Φ.JetMap m (φ k) (Λ k)) → ∃ τ : LB.Gen (LB.LinComb L.L φ ε), τ.IsGen ∧ Φ.JetRd m φ ε τ Λ := by
  intro S A _ _ L x0 g Φ n m K _ φ ε Λ hφ
  classical
  have hφ' := hφ
  choose hol hφe using hφ'
  let r : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m := renN n g m
  let F : K → L.L.ι → (Fin (n * g) → ℂ) → ℂ := fun k j v => Φ.fr j (Λ k (colsOf n g v))
  let u0 : K → L.L.ι → (Jet ℂ (Fin 1 × Fin (n * g)) m)ˣ := fun k j =>
    if h : IsUnit (jetOf m (F k j)) then h.unit else 1
  have hmem : ∀ k (U : A.left.Opens), ⊤ ≤ φ k ⁻¹ᵁ U → (Φ.e (Λ k (colsOf n g 0))).left cpt ∈ U := fun k U h =>
    mem_of_spMap_jetPt _ (hol k) m r U (by rw [hφe k] at h; exact h)
  have hF0 : ∀ k j, (Φ.e (Λ k (colsOf n g 0))).left cpt ∈ L.L.U j → F k j 0 ≠ 0 := fun k j h =>
    Φ.fr_ne j _ (top_le_of_mem h)
  have hu0 : ∀ k j, (Φ.e (Λ k (colsOf n g 0))).left cpt ∈ L.L.U j → (u0 k j).val = jetOf m (F k j) := fun k j h => by
    have hu : IsUnit (jetOf m (F k j)) := isUnit_of_jetAug _ (by rw [jetAug_jetOf]; exact hF0 k j h)
    simp only [u0, dif_pos hu, IsUnit.unit_spec]
  let ρ : (Jet ℂ (Fin 1 × Fin (n * g)) m)ˣ →* Γ(Sp (Jet ℂ (Fin n × Fin g) m), ⊤)ˣ :=
    Units.map ((toΓ (Jet ℂ (Fin n × Fin g) m)).comp r).toMonoidHom
  have hρ : ∀ a, (ρ a).val = toΓ _ (r a.val) := fun _ => rfl
  obtain ⟨τ, h1, h2⟩ := exists_gen_of_units L.L (Y := Sp (Jet ℂ (Fin n × Fin g) m))
    (fun p q => (jet_point_eq (K := ℂ) (I := Fin n × Fin g) (m := m) p).trans
      (jet_point_eq (K := ℂ) (I := Fin n × Fin g) (m := m) q).symm) φ ε (fun k j => ρ (u0 k j)) (fun k j j' h => by
      have hm := hmem k _ h
      have key : ∀ (ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left) (h : ⊤ ≤ ψ ⁻¹ᵁ (L.L.U j ⊓ L.L.U j')),
          ψ = spMap r ≫ jetPt _ (hol k) m → (ψ.appLE _ ⊤ h).hom (L.L.g j j').val = toΓ _ (r (jetOf m fun z =>
            valAt' (Φ.e (Λ k (colsOf n g z))).left (L.L.U j ⊓ L.L.U j') (L.L.g j j').val)) := by
        rintro _ h rfl
        exact appLE_spMap_jetPt _ (hol k) m r _ hm h _
      rw [key _ h (hφe k), hρ, hρ, ← map_mul, ← map_mul, hu0 k j hm.1, hu0 k j' hm.2,
        ← jetOf_mul m (contDiffAt_val _ (hol k) hm _) (contDiffAt_fr Φ (Λ k) j' hm.2)]
      exact congrArg (fun x => toΓ _ (r x))
        (jetOf_congr m ((eventually_mem _ (hol k) hm).mono fun z hz => Φ.fr_g j j' _ hz)))
  refine ⟨τ, h1, hφ, fun j h => ?_⟩
  have hm : ∀ k, (Φ.e (Λ k (colsOf n g 0))).left cpt ∈ L.L.U (j k) := fun k =>
    hmem k _ (h.trans (LB.wchart_le L.L φ j k))
  rw [h2 j h]
  have e1 : (∏ k, ρ (u0 k (j k)) ^ ε k) = ρ (∏ k, u0 k (j k) ^ ε k) := by
    simp only [map_prod, map_zpow]
  rw [e1, hρ]
  show toΓ _ (r _) = toΓ _ (r (jetOf m fun v => ∏ k, F k (j k) v ^ ε k))
  refine congrArg (fun x => toΓ _ (r x)) ?_
  rw [jetOf_prod m Finset.univ (f := fun k v => F k (j k) v ^ ε k)
    (fun k => contDiffAt_zpow' (contDiffAt_fr Φ (Λ k) _ (hm k)) (hF0 k _ (hm k)) _), Units.coe_prod]
  exact Finset.prod_congr rfl fun k _ =>
    (jetOf_zpow m (contDiffAt_fr Φ (Λ k) _ (hm k)) (hF0 k _ (hm k)) _ (hu0 k _ (hm k)) _).symm

end GlobalTheory.AnValJetEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsGeneratorJetReadingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_jet_reading : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n m : ℕ) (K : Type) [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ k, Φ.JetMap m (φ k) (Λ k)) → ∃ τ : LB.Gen (LB.LinComb L.L φ ε), τ.IsGen ∧ Φ.JetRd m φ ε τ Λ := by
  first | exact @GlobalTheory.AnValJetEx.exists_gen_jetRd | exact GlobalTheory.AnValJetEx.exists_gen_jetRd | (intros; apply GlobalTheory.AnValJetEx.exists_gen_jetRd <;> assumption)
end
end
