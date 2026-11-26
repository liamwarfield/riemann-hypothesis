module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerElementFixedFieldClosedSubgroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedH1CardInvariants

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlanePairingEquivariantTwistCartierDual
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlanePairingEquivariantTwistCartierDual
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

namespace GlobalTheory.Ord2.SelPerp

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem tbA_eps_mul (c : Coef l) (n : ℕ) (s : G ℚ Ω) (u : Qn c n) :
    tbA c n (red c n ⟨eps l s, CupCob.eps_mem c s⟩ * u) =
      ((cycMod ℚ Ω l n s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * tbA c n u := by
  obtain ⟨x, rfl⟩ := red_surjective c n u
  have h : eps l s = algebraMap ℤ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]; rfl
  have e : (⟨eps l s, CupCob.eps_mem c s⟩ : c.O) * x = ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) • x := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_smul, Algebra.smul_def, ← h]
  rw [← map_mul, e, tbA_red, tbA_red, map_smul, smul_eq_mul, map_mul]
  rfl

theorem matQ_dual1_apply (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O)
    (hdet : dt W ^ 2 = 1) (s : G ℚ Ω) (i j : Fin 2) :
    matQ c n (dual1 W) (CupCob.dual_representation_integral c W hdet hint) s i j =
      red c n ⟨eps l s, CupCob.eps_mem c s⟩ *
        (matQ c n W hint s 0 0 * matQ c n W hint s 1 1 - matQ c n W hint s 0 1 * matQ c n W hint s 1 0) *
        matQ c n W hint s i j := by
  simp only [matQ_apply, ← map_mul, ← map_sub]
  congr 1
  apply Subtype.ext
  show mat (dual1 W) s i j = eps l s * (mat W s 0 0 * mat W s 1 1 - mat W s 0 1 * mat W s 1 0) * mat W s i j
  rw [CupCob.mat_dual1 W hdet, Matrix.smul_apply, smul_eq_mul, Matrix.det_fin_two]

theorem matQ_det_sq (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O)
    (hdet : dt W ^ 2 = 1) (s : G ℚ Ω) :
    (matQ c n W hint s 0 0 * matQ c n W hint s 1 1 - matQ c n W hint s 0 1 * matQ c n W hint s 1 0) ^ 2 = 1 := by
  simp only [matQ_apply, ← map_mul, ← map_sub, ← map_pow]
  rw [← map_one (red c n)]
  congr 1
  apply Subtype.ext
  show (mat W s 0 0 * mat W s 1 1 - mat W s 0 1 * mat W s 1 0) ^ 2 = 1
  rw [← Matrix.det_fin_two]
  exact CupCob.det_sq W hdet s

end GlobalTheory.Ord2.SelPerp

theorem GlobalTheory.Ord2.SelPerp.Phi_equivariant : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hdet : dt W ^ 2 = 1) (S : Finset Pl) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (s : G ℚ Ω) (y : Mn c n), GlobalTheory.Ord2.SelPerp.Phi c n (matQ c n (dual1 W) (CupCob.dual_representation_integral c W hdet hint) s *ᵥ y) = twDual μ (rhoS c n W hint S hN) (toGS Ω (S : Set Pl) s) (GlobalTheory.Ord2.SelPerp.Phi c n y) := by
  intro l _ Ω _ _ c n W hint hdet S hN μ hμ s y
  apply DFunLike.ext
  intro x
  have hμs : μ (toGS Ω (S : Set Pl) s) = cycMod ℚ Ω l n s := by rw [← hμ]; rfl
  obtain ⟨p, rfl⟩ : ∃ p : Mn c n, x = matQ c n W hint s *ᵥ p :=
    ⟨matQ c n W hint s⁻¹ *ᵥ x, by
      rw [Matrix.mulVec_mulVec, ← matQ_mul, mul_inv_cancel, matQ_one, Matrix.one_mulVec]⟩
  rw [twDual_apply, ← map_inv, rhoS_toGS, Matrix.mulVec_mulVec, ← matQ_mul, inv_mul_cancel, matQ_one,
    Matrix.one_mulVec, hμs, SelPerp.Phi_apply, SelPerp.Phi_apply, ← SelPerp.tbA_eps_mul]
  congr 1
  have hd := SelPerp.matQ_det_sq c n W hint hdet s
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, SelPerp.matQ_dual1_apply c n W hint hdet]
  linear_combination (red c n ⟨eps l s, CupCob.eps_mem c s⟩ * (p 0 * y 1 - p 1 * y 0)) * hd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlanePairingEquivariantTwistCartierDualStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.planePairing_equivariant_twist_cartierDual : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hdet : dt W ^ 2 = 1) (S : Finset Pl) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (s : G ℚ Ω) (y : Mn c n), GlobalTheory.Ord2.SelPerp.Phi c n (matQ c n (dual1 W) (CupCob.dual_representation_integral c W hdet hint) s *ᵥ y) = twDual μ (rhoS c n W hint S hN) (toGS Ω (S : Set Pl) s) (GlobalTheory.Ord2.SelPerp.Phi c n y) := by
  first | exact @GlobalTheory.Ord2.SelPerp.Phi_equivariant | exact GlobalTheory.Ord2.SelPerp.Phi_equivariant | (intros; apply GlobalTheory.Ord2.SelPerp.Phi_equivariant <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.matQ_det_sq | exact GlobalTheory.Ord2.SelPerp.matQ_det_sq | (intros; apply GlobalTheory.Ord2.SelPerp.matQ_det_sq <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.matQ_dual1_apply | exact GlobalTheory.Ord2.SelPerp.matQ_dual1_apply | (intros; apply GlobalTheory.Ord2.SelPerp.matQ_dual1_apply <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualCocycleCoboundaryOnInertiaOfOrthogonal
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductFixedSubmoduleRestrictDual
noncomputable section

namespace GlobalTheory.InertiaFixed

open ReciprocityTheory.Gal

section Gen

variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {D : Type} [Group D] [TopologicalSpace D]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation R D M) (J : Subgroup D)

def fix : Submodule R M where
  carrier := {m | ∀ σ ∈ J, ρ σ m = m}
  zero_mem' := fun σ _ => map_zero _
  add_mem' := fun {a b} ha hb σ hσ => by
    show ρ σ (a + b) = a + b
    rw [map_add (f := _), ha σ hσ, hb σ hσ]
  smul_mem' := fun c m hm σ hσ => by
    show ρ σ (c • m) = c • m
    rw [map_smul, hm σ hσ]

variable [hJ : J.Normal]

theorem fix_stable (g : D) : ∀ m ∈ fix ρ J, ρ g m ∈ fix ρ J := by
  intro m hm σ hσ
  have h1 : g⁻¹ * σ * g ∈ J := by simpa using hJ.conj_mem σ hσ g⁻¹
  have e : σ * g = g * (g⁻¹ * σ * g) := by group
  calc ρ σ (ρ g m) = ρ (σ * g) m := by rw [map_mul]; rfl
    _ = ρ (g * (g⁻¹ * σ * g)) m := by rw [e]
    _ = ρ g (ρ (g⁻¹ * σ * g) m) := by rw [map_mul]; rfl
    _ = ρ g m := by rw [hm _ h1]

def fixRep : Representation R D (fix ρ J) where
  toFun g := (ρ g).restrict (p := fix ρ J) (q := fix ρ J) (fix_stable ρ J g)
  map_one' := by
    refine LinearMap.ext fun m => Subtype.ext ?_
    show ρ 1 m = m
    rw [map_one]; rfl
  map_mul' g h := by
    refine LinearMap.ext fun m => Subtype.ext ?_
    show ρ (g * h) m = ρ g (ρ h m)
    rw [map_mul]; rfl

theorem contAction_fixRep (h : ContAction ρ) : ContAction (fixRep ρ J) :=
  continuous_induced_rng.2 (h.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))

def resD : TDual R M →ₗ[R] TDual R (fix ρ J) where
  toFun φ := TDual.mk ((φ : M →ₗ[R] R) ∘ₗ (fix ρ J).subtype)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem resD_equiv (χ : D →* Rˣ) (g : D) (φ : TDual R M) :
    resD ρ J (twDual χ ρ g φ) = twDual χ (fixRep ρ J) g (resD ρ J φ) := rfl

theorem map_h1_mem_unramified {M' : Type} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
    [DiscreteTopology M'] (ρ' : Representation R D M') (u : M →ₗ[R] M')
    (he : ∀ g m, u (ρ g m) = ρ' g (u m)) (x : H1 ρ) (hx : x ∈ H1ur ρ J) :
    mapH1 ρ ρ' u continuous_of_discreteTopology he x ∈ H1ur ρ' J := by
  induction x using Submodule.Quotient.induction_on with | H f =>
  rw [H1ur, LinearMap.mem_ker] at hx ⊢
  change Submodule.Quotient.mk (restrictCocycles1 ρ J.subtype continuous_subtype_val f) = 0 at hx
  change Submodule.Quotient.mk (restrictCocycles1 ρ' J.subtype continuous_subtype_val
    (cocycles1MapOfEquivariant ρ ρ' u continuous_of_discreteTopology he f)) = 0
  rw [Submodule.Quotient.mk_eq_zero] at hx ⊢
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hx
  refine (mem_coboundaries1 _ _).2 ⟨u m, fun σ => ?_⟩
  have e := hm σ
  change f.1 σ = ρ σ m - m at e
  change u (f.1 σ) = ρ' σ (u m) - u m
  rw [e, map_sub, he]

theorem exists_fix_of_mem_H1ur (h : ContAction ρ) (x : H1 ρ) (hx : x ∈ H1ur ρ J) :
    ∃ x' : H1 (fixRep ρ J), x' ∈ H1ur (fixRep ρ J) J ∧
      mapH1 (fixRep ρ J) ρ (fix ρ J).subtype continuous_of_discreteTopology (fun _ _ => rfl) x' = x := by
  induction x using Submodule.Quotient.induction_on with | H f =>
  rw [H1ur, LinearMap.mem_ker] at hx
  change Submodule.Quotient.mk (restrictCocycles1 ρ J.subtype continuous_subtype_val f) = 0 at hx
  rw [Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hx
  let f' : D → M := fun g => f.1 g - (ρ g m - m)
  have hf'J : ∀ σ ∈ J, f' σ = 0 := fun σ hσ => by
    have e := hm ⟨σ, hσ⟩
    change f.1 σ = ρ σ m - m at e
    show f.1 σ - (ρ σ m - m) = 0
    rw [e, sub_self]
  have hcoc : ∀ g k, f' (g * k) = f' g + ρ g (f' k) := fun g k => by
    show f.1 (g * k) - (ρ (g * k) m - m) = f.1 g - (ρ g m - m) + ρ g (f.1 k - (ρ k m - m))
    rw [f.2.2 g k, map_mul, Module.End.mul_apply, map_sub, map_sub]
    abel
  have hfix : ∀ g, f' g ∈ fix ρ J := fun g σ hσ => by
    have h1 : g⁻¹ * σ * g ∈ J := by simpa using hJ.conj_mem σ hσ g⁻¹
    have e1 := hcoc σ g
    have e2 := hcoc g (g⁻¹ * σ * g)
    rw [hf'J σ hσ, zero_add] at e1
    rw [hf'J _ h1, map_zero, add_zero] at e2
    have : σ * g = g * (g⁻¹ * σ * g) := by group
    rw [← e1, this, e2]
  have hcont : Continuous f' :=
    f.2.1.sub ((h.comp (continuous_id.prodMk continuous_const)).sub continuous_const)
  let F : Z1 (fixRep ρ J) := ⟨fun g => ⟨f' g, hfix g⟩, continuous_induced_rng.2 hcont,
    fun g k => Subtype.ext (hcoc g k)⟩
  refine ⟨Submodule.Quotient.mk F, ?_, ?_⟩
  · rw [H1ur, LinearMap.mem_ker]
    change Submodule.Quotient.mk (restrictCocycles1 _ J.subtype continuous_subtype_val F) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine (mem_coboundaries1 _ _).2 ⟨0, fun σ => Subtype.ext ?_⟩
    show f' σ = ρ σ 0 - 0
    rw [hf'J σ.1 σ.2, map_zero, sub_zero]
  · change Submodule.Quotient.mk (cocycles1MapOfEquivariant _ _ _ continuous_of_discreteTopology (fun _ _ => rfl) F) =
      Submodule.Quotient.mk f
    rw [Submodule.Quotient.eq]
    refine (mem_coboundaries1 _ _).2 ⟨-m, fun g => ?_⟩
    show f' g - f.1 g = ρ g (-m) - -m
    show f.1 g - (ρ g m - m) - f.1 g = ρ g (-m) - -m
    rw [map_neg]
    abel

theorem cupProduct_fixedSubmodule_restrictDual (χ : D →* Rˣ) (h : ContAction ρ) (hN : ContAction (fixRep ρ J))
    (y : H1 (twDual χ ρ)) (x : H1 (fixRep ρ J)) :
    cupH1H1TwistedDual χ ρ (MonoidHom.id D) (h.comp' continuous_id) y
        (mapH1 (fixRep ρ J) ρ (fix ρ J).subtype continuous_of_discreteTopology (fun _ _ => rfl) x) =
      cupH1H1TwistedDual χ (fixRep ρ J) (MonoidHom.id D) (hN.comp' continuous_id)
        (mapH1 (twDual χ ρ) (twDual χ (fixRep ρ J)) (resD ρ J) continuous_of_discreteTopology
          (resD_equiv ρ J χ) y) x := by
  induction y using Submodule.Quotient.induction_on with | H y =>
  induction x using Submodule.Quotient.induction_on with | H x =>
  rfl

end Gen

theorem bijective_compr₂_iff {R A B C : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] (b : A →ₗ[R] B →ₗ[R] C)
    (j : C ≃ₗ[R] R) : Function.Bijective (b.compr₂ j.toLinearMap) ↔ Function.Bijective b :=
  (LinearEquiv.congrRight (M := B) j).bijective.of_comp_iff' b

theorem mem_H1ur_of_perp {n : ℕ} [NeZero n] {D : Type} [Group D] [TopologicalSpace D]
    {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (χ : D →* (ZMod n)ˣ) (ρ : Representation (ZMod n) D M) (h : ContAction ρ) (J : Subgroup D)
    (inv : H2 ((charRep χ).comp (MonoidHom.id D)) ≃ₗ[ZMod n] ZMod n)
    [Finite (H1 (ρ.comp (MonoidHom.id D)))] [Finite (H1 ((twDual χ ρ).comp (MonoidHom.id D)))]
    [Finite (H0 ((twDual χ ρ).comp (MonoidHom.id D)))]
    (hb : Function.Bijective (cupH1H1TwistedDual χ ρ (MonoidHom.id D) (h.comp' continuous_id)))
    (hbf : Function.Bijective (cupH1H1TwistedDual χ ρ (MonoidHom.id D) (h.comp' continuous_id)).flip)
    (h20 : Function.Bijective (cup20 χ ρ (MonoidHom.id D)))
    (hE : Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ))
    (hLc : Nat.card (H1ur ρ J) = Nat.card (H0 ρ))
    (hU : Nat.card (H1ur (twDual χ ρ) J) = Nat.card (H0 (twDual χ ρ)))
    (orth : ∀ y ∈ H1ur (twDual χ ρ) J, ∀ x ∈ H1ur ρ J,
      cupH1H1TwistedDual χ ρ (MonoidHom.id D) (h.comp' continuous_id) y x = 0)
    (y : H1 (twDual χ ρ))
    (hy : ∀ x ∈ H1ur ρ J, cupH1H1TwistedDual χ ρ (MonoidHom.id D) (h.comp' continuous_id) y x = 0) :
    y ∈ H1ur (twDual χ ρ) J := by
  classical
  let cup := cupH1H1TwistedDual χ ρ (MonoidHom.id D) (h.comp' continuous_id)
  let L := H1ur ρ J
  let P : Submodule (ZMod n) (H1 ((twDual χ ρ).comp (MonoidHom.id D))) :=
    ⨅ x ∈ L, LinearMap.ker (cup.flip x)
  have memP : ∀ z, z ∈ P ↔ ∀ x ∈ L, cup z x = 0 := fun z => by
    simp only [P, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
  let b := cup.compr₂ inv.toLinearMap
  have hbb : Function.Bijective b := (bijective_compr₂_iff cup inv).2 hb
  let bL := b.compl₂ (L.subtype : L →ₗ[ZMod n] H1 (ρ.comp (MonoidHom.id D)))
  have hk := GlobalTheory.ZModDual.card_ker_mul_card_eq n _ L bL
  have hkP : LinearMap.ker bL = P := by
    ext z
    rw [LinearMap.mem_ker, memP]
    constructor
    · intro hz x hx
      have := LinearMap.congr_fun hz ⟨x, hx⟩
      exact inv.map_eq_zero_iff.1 this
    · intro hz
      refine LinearMap.ext fun x => ?_
      show inv (cup z x.1) = 0
      rw [hz x.1 x.2, map_zero]
  have hk1 : Nat.card (LinearMap.ker bL.flip) = 1 := by
    have hz : ∀ a : LinearMap.ker bL.flip, a = 0 := fun a => by
      have ha := LinearMap.mem_ker.1 a.2
      have h0 : cup.flip a.1.1 = 0 := LinearMap.ext fun z => by
        have := LinearMap.congr_fun ha z
        exact inv.map_eq_zero_iff.1 this
      have h1 : a.1.1 = 0 := hbf.1 (h0.trans (map_zero _).symm)
      exact Subtype.ext (Subtype.ext h1)
    refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun a c => by rw [hz a, hz c]⟩, ⟨0⟩⟩
  rw [hkP, hk1, one_mul] at hk
  have hY : Nat.card (H1 ((twDual χ ρ).comp (MonoidHom.id D))) =
      Nat.card (H1 (ρ.comp (MonoidHom.id D))) :=
    (Nat.card_eq_of_bijective b hbb).trans (GlobalTheory.ZModDual.card_dual_eq n _)
  have h2 : Nat.card (H2 (ρ.comp (MonoidHom.id D))) =
      Nat.card (H0 ((twDual χ ρ).comp (MonoidHom.id D))) :=
    (Nat.card_eq_of_bijective _ ((bijective_compr₂_iff _ inv).2 h20)).trans
      (GlobalTheory.ZModDual.card_dual_eq n _)
  have hpos : 0 < Nat.card (H0 ρ) := Nat.card_pos
  have hcard : Nat.card P = Nat.card (H1ur (twDual χ ρ) J) := by
    rw [hU]
    have e : Nat.card P * Nat.card (H0 ρ) = Nat.card (H0 (twDual χ ρ)) * Nat.card (H0 ρ) :=
      calc Nat.card P * Nat.card (H0 ρ) = Nat.card P * Nat.card L := by rw [hLc]
        _ = Nat.card (H1 ((twDual χ ρ).comp (MonoidHom.id D))) := hk
        _ = Nat.card (H1 (ρ.comp (MonoidHom.id D))) := hY
        _ = Nat.card (H0 ρ) * Nat.card (H2 ρ) := hE
        _ = Nat.card (H0 (twDual χ ρ)) * Nat.card (H0 ρ) := by
          rw [mul_comm]; exact congrArg (· * Nat.card (H0 ρ)) h2
    exact Nat.eq_of_mul_eq_mul_right hpos e
  have hUP : H1ur (twDual χ ρ) J ≤ P := fun z hz => (memP z).2 (fun x hx => orth z hz x hx)
  haveI : Finite P := Subtype.finite
  obtain ⟨u, hu⟩ := (Function.Injective.bijective_of_nat_card_le
    (Submodule.inclusion_injective hUP) hcard.le).2 ⟨y, (memP y).2 hy⟩
  have e := congrArg Subtype.val hu
  change (u : H1 ((twDual χ ρ).comp (MonoidHom.id D))) = y at e
  rw [← e]
  exact u.2

end GlobalTheory.InertiaFixed

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem unramified_h1_dual_iff_perp : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (ρ : Representation (ZMod (l ^ r)) (Dec (F := F) A) M) (hρ : ContAction ρ), IsPlaceOver A v → 0 < r → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∀ y : H1 (twDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) ρ), y ∈ H1ur (twDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) ρ) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) ↔ ∀ x ∈ H1ur ρ ((Ine (F := F) A).subgroupOf (Dec (F := F) A)), cupH1H1TwistedDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) ρ (MonoidHom.id _) (hρ.comp' continuous_id) y x = 0 := by
  intro hL F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A v ρ hρ hA hr hl y
  classical
  set χ := (cycMod F Ω l r).comp (Dec (F := F) A).subtype with hχdef
  set J := (Ine (F := F) A).subgroupOf (Dec (F := F) A) with hJdef
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : Finite (TDual (ZMod (l ^ r)) M) := GlobalTheory.DualSide.finite_TDual
  have hχ : ContAction (charRep χ) :=
    (((Units.continuous_val.comp GlobalTheory.Published.PoitouTate.continuous_cycMod).comp
      continuous_subtype_val).comp continuous_fst).mul continuous_snd
  have hρ' : ContAction (twDual χ ρ) := GlobalTheory.DualSide.contAction_twDual hχ hρ
  have orth : ∀ y ∈ H1ur (twDual χ ρ) J, ∀ x ∈ H1ur ρ J,
      cupH1H1TwistedDual χ ρ (MonoidHom.id _) (hρ.comp' continuous_id) y x = 0 := by
    intro y hy x hx
    obtain ⟨x', hx', rfl⟩ := GlobalTheory.InertiaFixed.exists_fix_of_mem_H1ur ρ J hρ x hx
    have hN := GlobalTheory.InertiaFixed.contAction_fixRep ρ J hρ
    rw [GlobalTheory.InertiaFixed.cupProduct_fixedSubmodule_restrictDual ρ J χ hρ hN]
    have uo := hL.uo F Ω l r (GlobalTheory.InertiaFixed.fix ρ J) A (GlobalTheory.InertiaFixed.fixRep ρ J) v hr hA hl
      (fun σ hσ => LinearMap.ext fun m => Subtype.ext (m.2 σ (Subgroup.mem_subgroupOf.2 hσ))) hN
    exact (uo.2 _).1 (GlobalTheory.InertiaFixed.map_h1_mem_unramified _ J _ _ _ y hy) x' hx'
  refine ⟨fun hy x hx => orth _ hy x hx, fun hy => ?_⟩
  obtain ⟨-, hfin1, -, -⟩ := hL.lf F Ω l r M A ρ v hr hA hρ
  have hfin0' := (hL.lf F Ω l r _ A (twDual χ ρ) v hr hA hρ').1
  have hfin1' := (hL.lf F Ω l r _ A (twDual χ ρ) v hr hA hρ').2.1
  obtain ⟨⟨inv⟩, -, hb, hbf, h20⟩ := hL.lt F Ω l r M A ρ v hr hA hρ
  haveI : Finite (H1 (ρ.comp (MonoidHom.id _))) := hfin1
  haveI : Finite (H1 ((twDual χ ρ).comp (MonoidHom.id _))) := hfin1'
  haveI : Finite (H0 ((twDual χ ρ).comp (MonoidHom.id _))) := hfin0'
  exact GlobalTheory.InertiaFixed.mem_H1ur_of_perp χ ρ hρ J inv hb hbf h20
    ((hL.le F Ω l r M A ρ v hr hA hρ).2 hl) (GlobalTheory.T.unramified_h1_card_invariants F Ω l r M A v ρ hρ hA)
    (GlobalTheory.T.unramified_h1_card_invariants F Ω l r (TDual (ZMod (l ^ r)) M) A v (twDual χ ρ) hρ' hA) orth _ hy

end GlobalTheory.Ord2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualCocycleCoboundaryOnInertiaOfOrthogonal
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

namespace GlobalTheory.Ord2.GwIneq

theorem cob_of_perp_transport {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    {Γ D : Type} [Group Γ] [Group D] [TopologicalSpace D]
    {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (μ : Γ →* Rˣ) (rho : Representation R Γ M) (φ : D →* Γ) (J : Subgroup D)
    (h : ContAction (rho.comp φ)) (h' : ContAction ((rho.comp φ).comp (MonoidHom.id D)))
    (key : ∀ y : H1 (twDual (μ.comp φ) (rho.comp φ)),
      (∀ x ∈ H1ur (rho.comp φ) J, cupH1H1TwistedDual (μ.comp φ) (rho.comp φ) (MonoidHom.id D) h' y x = 0) →
        y ∈ H1ur (twDual (μ.comp φ) (rho.comp φ)) J)
    (f : Z1 ((twDual μ rho).comp φ))
    (hf : ∀ a ∈ H1ur (rho.comp φ) J, cupH1H1TwistedDual μ rho φ h (Submodule.mkQ _ f) a = 0) :
    ∃ m : TDual R M, ∀ s ∈ J, f.1 s = twDual μ rho (φ s) m - m := by
  have heq : twDual (μ.comp φ) (rho.comp φ) = (twDual μ rho).comp φ := by
    refine MonoidHom.ext fun s => LinearMap.ext fun ψ => LinearMap.ext fun x => ?_
    change ((μ (φ s) : Rˣ) : R) * ψ (rho (φ s⁻¹) x) =
      ((μ (φ s) : Rˣ) : R) * ψ (rho (φ s)⁻¹ x)
    rw [map_inv]
  have hf' : f.1 ∈ Z1 (twDual (μ.comp φ) (rho.comp φ)) := by rw [heq]; exact f.2
  have hy := key (Submodule.Quotient.mk ⟨f.1, hf'⟩) (by
    intro x hx
    induction x using Submodule.Quotient.induction_on with | H a =>
    have e := hf _ hx
    have e' := (Submodule.Quotient.mk_eq_zero _).1 e
    exact (Submodule.Quotient.mk_eq_zero _).2 e')
  rw [H1ur, LinearMap.mem_ker] at hy
  change Submodule.Quotient.mk (restrictCocycles1 _ J.subtype continuous_subtype_val ⟨f.1, hf'⟩) = 0 at hy
  rw [Submodule.Quotient.mk_eq_zero] at hy
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hy
  refine ⟨m, fun s hs => ?_⟩
  have e := hm ⟨s, hs⟩
  change f.1 s = twDual (μ.comp φ) (rho.comp φ) s m - m at e
  rw [e, heq]
  rfl

theorem dual_cocycle_cob_on_inertia : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ), 1 ≤ n → ∀ (S : Finset Pl) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ n)) (GS Ω (S : Set Pl)) M) (hrho : ContAction rho) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (B : ValuationSubring Ω) (q : Pl), IsPlaceOver B q → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ f : Z1 ((twDual μ rho).comp (locHom (S : Set Pl) B)), (∀ a ∈ H1ur (rho.comp (locHom (S : Set Pl) B)) ((Ine (F := ℚ) B).subgroupOf (Dec (F := ℚ) B)), cupH1H1TwistedDual μ rho (locHom (S : Set Pl) B) (hrho.comp' (continuous_locHom _ B)) (Submodule.mkQ _ f) a = 0) → ∃ m : TDual (ZMod (l ^ n)) M, ∀ s : Dec (F := ℚ) B, (s : G ℚ Ω) ∈ Ine (F := ℚ) B → f.1 s = twDual μ rho (locHom (S : Set Pl) B s) m - m := by
  intro hL l _ Ω _ _ _ n hn S M _ _ _ _ _ rho hrho μ hμ B q hq hl f hf
  have hχ : (cycMod ℚ Ω l n).comp (Dec (F := ℚ) B).subtype = μ.comp (locHom (S : Set Pl) B) := by
    rw [← hμ]; rfl
  have hc := hrho.comp' (continuous_locHom (S : Set Pl) B)
  have key := GlobalTheory.Ord2.unramified_h1_dual_iff_perp hL ℚ Ω l n M B q (rho.comp (locHom (S : Set Pl) B)) hc
    hq hn hl
  rw [hχ] at key
  obtain ⟨m, hm⟩ := cob_of_perp_transport μ rho (locHom (S : Set Pl) B) _ hc _
    (fun y hy => (key y).2 hy) f hf
  exact ⟨m, fun s hs => hm s (Subgroup.mem_subgroupOf.2 hs)⟩

end GlobalTheory.Ord2.GwIneq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualCocycleCoboundaryOnInertiaOfOrthogonalStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.dualCocycle_coboundary_on_inertia_of_orthogonal : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ), 1 ≤ n → ∀ (S : Finset Pl) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ n)) (GS Ω (S : Set Pl)) M) (hrho : ContAction rho) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (B : ValuationSubring Ω) (q : Pl), IsPlaceOver B q → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ f : Z1 ((twDual μ rho).comp (locHom (S : Set Pl) B)), (∀ a ∈ H1ur (rho.comp (locHom (S : Set Pl) B)) ((Ine (F := ℚ) B).subgroupOf (Dec (F := ℚ) B)), cupH1H1TwistedDual μ rho (locHom (S : Set Pl) B) (hrho.comp' (continuous_locHom _ B)) (Submodule.mkQ _ f) a = 0) → ∃ m : TDual (ZMod (l ^ n)) M, ∀ s : Dec (F := ℚ) B, (s : G ℚ Ω) ∈ Ine (F := ℚ) B → f.1 s = twDual μ rho (locHom (S : Set Pl) B s) m - m := by
  first | exact @GlobalTheory.Ord2.GwIneq.dual_cocycle_cob_on_inertia | exact GlobalTheory.Ord2.GwIneq.dual_cocycle_cob_on_inertia | (intros; apply GlobalTheory.Ord2.GwIneq.dual_cocycle_cob_on_inertia <;> assumption) | exact @GlobalTheory.Ord2.GwIneq.cob_of_perp_transport | exact GlobalTheory.Ord2.GwIneq.cob_of_perp_transport | (intros; apply GlobalTheory.Ord2.GwIneq.cob_of_perp_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdDualGeneratorPairingModPowNondegenerate
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdDualGeneratorPairingModPowNondegenerate
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.SelPerp

variable {l : ℕ} [Fact l.Prime]

theorem tau_mul_dvd (c : Coef l) (n : ℕ) (b' : c.O)
    (h : ∀ a : Qn c n, tbA c n (a * red c n b') = 0) (x : c.O) :
    ∃ q : ℤ_[l], tau c (b' * x) = (l : ℤ_[l]) ^ n * q := by
  have h1 := h (red c n x)
  rw [← map_mul, tbA_red, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
  rw [mul_comm]
  exact h1

theorem pair_nondeg (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (b : Qn c n)
    (h : ∀ a : Qn c n, GlobalTheory.Ord2.SelPerp.tbA c n (a * b) = 0) : b = 0 := by
  obtain ⟨b', rfl⟩ := red_surjective c n b
  have hd := tau_mul_dvd c n b' h
  have hl : ((l : ℤ_[l]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  let q : c.O → ℤ_[l] := fun x => Classical.choose (hd x)
  have hq : ∀ x, tau c (b' * x) = (l : ℤ_[l]) ^ n * q x := fun x => Classical.choose_spec (hd x)
  let g : c.O →ₗ[ℤ_[l]] ℤ_[l] :=
    { toFun := q
      map_add' := fun x y => by
        apply mul_left_cancel₀ hl
        rw [← hq, mul_add, map_add (f := _), hq, hq, mul_add]
      map_smul' := fun r x => by
        apply mul_left_cancel₀ hl
        rw [← hq, mul_smul_comm, map_smul, hq, RingHom.id_apply, smul_eq_mul, smul_eq_mul]
        ring }
  obtain ⟨a0, ha0⟩ := (tau_spec c g).exists
  let f : c.O →ₗ[ℤ_[l]] ℤ_[l] := (tau c).comp (LinearMap.mulLeft ℤ_[l] b')
  have e1 : ∀ x, f x = tau c (b' * x) := fun x => rfl
  have e2 : ∀ x, f x = tau c ((((l : ℤ_[l]) ^ n) • a0) * x) := fun x => by
    rw [e1, hq, smul_mul_assoc, map_smul, smul_eq_mul]
    congr 1
    exact ha0 x
  have heq : b' = ((l : ℤ_[l]) ^ n) • a0 := (tau_spec c f).unique e1 e2
  rw [heq, red_eq_zero_iff_mem]
  exact smul_mem_Ik c n (Ideal.mem_span_singleton_self _) a0

end GlobalTheory.Ord2.SelPerp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdDualGeneratorPairingModPowNondegenerateStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.ordDualGeneratorPairing_modPow_nondegenerate : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (b : Qn c n), (∀ a : Qn c n, GlobalTheory.Ord2.SelPerp.tbA c n (a * b) = 0) → b = 0 := by
  first | exact @GlobalTheory.Ord2.SelPerp.pair_nondeg | exact GlobalTheory.Ord2.SelPerp.pair_nondeg | (intros; apply GlobalTheory.Ord2.SelPerp.pair_nondeg <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.tau_mul_dvd | exact GlobalTheory.Ord2.SelPerp.tau_mul_dvd | (intros; apply GlobalTheory.Ord2.SelPerp.tau_mul_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualCocycleCoboundaryOnStableLineOfOrthogonal
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualCocycleCoboundaryOnStableLineOfOrthogonal
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.OrdCob

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem matQ_one_zero (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O)
    (B : ValuationSubring Ω) (hB : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) (s : Dec (F := ℚ) B) :
    matQ c n W hint s 1 0 = 0 := by
  have h : (⟨mat W s 1 0, hint s 1 0⟩ : c.O) = 0 := Subtype.ext (hB s s.2)
  rw [matQ_apply, h, map_zero]

def rhoL (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O)
    (B : ValuationSubring Ω) (hB : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) :
    Representation (ZMod (l ^ n)) (Dec (F := ℚ) B) (Qn c n) where
  toFun s := (AddMonoidHom.mulLeft (matQ c n W hint s 0 0)).toZModLinearMap (l ^ n)
  map_one' := by
    apply LinearMap.ext
    intro x
    show matQ c n W hint 1 0 0 * x = x
    rw [matQ_one, Matrix.one_apply_eq, one_mul]
  map_mul' s t := by
    apply LinearMap.ext
    intro x
    show matQ c n W hint ((s : G ℚ Ω) * (t : G ℚ Ω)) 0 0 * x =
      matQ c n W hint s 0 0 * (matQ c n W hint t 0 0 * x)
    rw [matQ_mul, Matrix.mul_apply, Fin.sum_univ_two, matQ_one_zero c n W hint B hB t, mul_zero, add_zero,
      mul_assoc]

theorem contAction_rhoL (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O)
    (B : ValuationSubring Ω) (hB : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) (hcont : Continuous W) :
    ReciprocityTheory.Gal.ContAction (rhoL c n W hint B hB) := by
  unfold ReciprocityTheory.Gal.ContAction
  rw [continuous_prod_of_discrete_right]
  intro x
  show Continuous fun s : Dec (F := ℚ) B => matQ c n W hint s 0 0 * x
  exact ((continuous_matQ_apply c n W hint hcont 0 0).comp continuous_subtype_val).mul continuous_const

theorem rhoS_single (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1)
    (B : ValuationSubring Ω) (hB : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) (s : Dec (F := ℚ) B) (u : Qn c n) :
    rhoS c n W hint S hN (locHom (S : Set Pl) B s) (Pi.single 0 u) =
      Pi.single 0 (rhoL c n W hint B hB s u) := by
  show matQ c n W hint s *ᵥ Pi.single 0 u = Pi.single 0 (matQ c n W hint s 0 0 * u)
  have h := matQ_one_zero c n W hint B hB s
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h]

theorem dual_cob_on_line : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ), 1 ≤ n → ∀ (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hcont : Continuous W) (S : Finset Pl) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (B : ValuationSubring Ω) (v : Pl), IsPlaceOver B v → (∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) → ∀ f : Z1 ((twDual μ (rhoS c n W hint S hN)).comp (locHom (S : Set Pl) B)), (∀ a ∈ ordCond c n W hint S hN B, cupH1H1TwistedDual μ (rhoS c n W hint S hN) (locHom (S : Set Pl) B) ((contAction_rhoS c n W hint S hN hcont).comp' (continuous_locHom _ B)) (Submodule.mkQ _ f) a = 0) → ∃ m : TDual (ZMod (l ^ n)) (Mn c n), ∀ (s : Dec (F := ℚ) B) (u : Qn c n), f.1 s (Pi.single 0 u) = twDual μ (rhoS c n W hint S hN) (locHom (S : Set Pl) B s) m (Pi.single 0 u) - m (Pi.single 0 u) := by
  intro hL l _ Ω _ _ _ c n hn W hint hcont S hN μ hμ B v hBv hB f hf
  have hμχ : ∀ s : Dec (F := ℚ) B,
      μ (locHom (S : Set Pl) B s) = ((cycMod ℚ Ω l n).comp (Dec (F := ℚ) B).subtype) s := fun s =>
    DFunLike.congr_fun hμ (s : G ℚ Ω)
  have hinj := (hL.lt ℚ Ω l n (Qn c n) B (rhoL c n W hint B hB) v hn hBv
    (contAction_rhoL c n W hint B hB hcont)).2.2.1.1
  set χ : Dec (F := ℚ) B →* (ZMod (l ^ n))ˣ := (cycMod ℚ Ω l n).comp (Dec (F := ℚ) B).subtype with hχ
  have hs := rhoS_single c n W hint S hN B hB
  have hs' : ∀ (s : Dec (F := ℚ) B) (u : Qn c n),
      rhoS c n W hint S hN (locHom (S : Set Pl) B s)⁻¹ (Pi.single 0 u) =
        Pi.single 0 (rhoL c n W hint B hB s⁻¹ u) := fun s u => by rw [← map_inv, hs]
  let ι : Qn c n →ₗ[ZMod (l ^ n)] Mn c n := LinearMap.single (ZMod (l ^ n)) (fun _ : Fin 2 => Qn c n) 0
  let r : TDual (ZMod (l ^ n)) (Mn c n) → TDual (ZMod (l ^ n)) (Qn c n) := fun φ =>
    TDual.mk (LinearMap.comp (show Mn c n →ₗ[ZMod (l ^ n)] ZMod (l ^ n) from φ) ι)
  have hψ : (fun s => r (f.1 s)) ∈ Z1 ((twDual χ (rhoL c n W hint B hB)).comp (MonoidHom.id _)) := by
    refine ⟨(continuous_of_discreteTopology (f := r)).comp f.2.1, fun g h => ?_⟩
    refine DFunLike.ext _ _ fun u => ?_
    have e : f.1 (g * h) (Pi.single 0 u) = f.1 g (Pi.single 0 u) +
        ((μ (locHom (S : Set Pl) B g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) *
          f.1 h (rhoS c n W hint S hN (locHom (S : Set Pl) B g)⁻¹ (Pi.single 0 u)) := by
      rw [f.2.2 g h]; rfl
    rw [hμχ, hs'] at e
    exact e
  have hcup : cupH1H1TwistedDual χ (rhoL c n W hint B hB) (MonoidHom.id _)
      ((contAction_rhoL c n W hint B hB hcont).comp' continuous_id) (Submodule.mkQ _ ⟨_, hψ⟩) = 0 := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a0, rfl⟩ := Submodule.mkQ_surjective _ x
    have ha : (fun s => ι (a0.1 s)) ∈ Z1 ((rhoS c n W hint S hN).comp (locHom (S : Set Pl) B)) := by
      refine ⟨(continuous_of_discreteTopology (f := ι)).comp a0.2.1, fun g h => ?_⟩
      show ι (a0.1 (g * h)) = ι (a0.1 g) +
        rhoS c n W hint S hN (locHom (S : Set Pl) B g) (Pi.single 0 (a0.1 h))
      rw [a0.2.2 g h, map_add (f := _), hs]
      rfl
    have hmem : Submodule.mkQ _ (⟨_, ha⟩ : Z1 _) ∈ ordCond c n W hint S hN B := by
      refine Submodule.mem_map.2 ⟨⟨_, ha⟩, (mem_ordZ _).2 ⟨0, fun s => ?_⟩, rfl⟩
      show (Pi.single 0 (a0.1 s) : Mn c n) 1 = _
      simp
    obtain ⟨cc, hcc, hd⟩ := (separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 (hf _ hmem))
    refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨cc, hcc, ?_⟩)
    funext p
    obtain ⟨g, h⟩ := p
    have e : ((μ (locHom (S : Set Pl) B g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * cc h - cc (g * h) + cc g =
        f.1 g (rhoS c n W hint S hN (locHom (S : Set Pl) B g) (Pi.single 0 (a0.1 h))) := congrFun hd (g, h)
    rw [hμχ, hs] at e
    exact e
  have h0 := hinj (hcup.trans (map_zero _).symm)
  obtain ⟨m0, hm0⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
  refine ⟨TDual.mk (LinearMap.comp (show Qn c n →ₗ[ZMod (l ^ n)] ZMod (l ^ n) from m0) (LinearMap.proj 0)),
    fun s u => ?_⟩
  have e : f.1 s (Pi.single 0 u) =
      ((χ s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * m0 (rhoL c n W hint B hB s⁻¹ u) - m0 u :=
    congrArg (fun φ : TDual (ZMod (l ^ n)) (Qn c n) => φ u) (hm0 s)
  rw [e, twDual_apply, hμχ, hs']
  rfl

end GlobalTheory.Ord2.OrdCob
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualCocycleCoboundaryOnStableLineOfOrthogonalStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.dualCocycle_coboundary_on_stableLine_of_orthogonal : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ), 1 ≤ n → ∀ (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hcont : Continuous W) (S : Finset Pl) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (B : ValuationSubring Ω) (v : Pl), IsPlaceOver B v → (∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) → ∀ f : Z1 ((twDual μ (rhoS c n W hint S hN)).comp (locHom (S : Set Pl) B)), (∀ a ∈ ordCond c n W hint S hN B, cupH1H1TwistedDual μ (rhoS c n W hint S hN) (locHom (S : Set Pl) B) ((contAction_rhoS c n W hint S hN hcont).comp' (continuous_locHom _ B)) (Submodule.mkQ _ f) a = 0) → ∃ m : TDual (ZMod (l ^ n)) (Mn c n), ∀ (s : Dec (F := ℚ) B) (u : Qn c n), f.1 s (Pi.single 0 u) = twDual μ (rhoS c n W hint S hN) (locHom (S : Set Pl) B s) m (Pi.single 0 u) - m (Pi.single 0 u) := by
  first | exact @GlobalTheory.Ord2.OrdCob.dual_cob_on_line | exact GlobalTheory.Ord2.OrdCob.dual_cob_on_line | (intros; apply GlobalTheory.Ord2.OrdCob.dual_cob_on_line <;> assumption) | exact @GlobalTheory.Ord2.OrdCob.rhoS_single | exact GlobalTheory.Ord2.OrdCob.rhoS_single | (intros; apply GlobalTheory.Ord2.OrdCob.rhoS_single <;> assumption) | exact @GlobalTheory.Ord2.OrdCob.contAction_rhoL | exact GlobalTheory.Ord2.OrdCob.contAction_rhoL | (intros; apply GlobalTheory.Ord2.OrdCob.contAction_rhoL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqOrdDualGeneratorPairingOfAdditiveMap
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqOrdDualGeneratorPairingOfAdditiveMap
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

namespace GlobalTheory.Ord2.SelPerp

theorem coef_free_pairSurj (l : ℕ) [Fact l.Prime] (c : Coef l) : Module.Free ℤ_[l] c.O := by
  haveI : Module.IsTorsionFree ℤ_[l] c.O := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun a x h => ?_
    have h' : a • (x : Qbar l) = 0 := by rw [← Subalgebra.coe_smul, h]; rfl
    rw [Algebra.smul_def, mul_eq_zero] at h'
    rcases h' with h' | h'
    · left
      have := congrArg norm h'
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap', norm_zero] at this
      have h2 : ((a : ℤ_[l]) : ℚ_[l]) = 0 := norm_eq_zero.1 this
      exact PadicInt.coe_eq_zero.1 h2
    · right
      exact Subtype.ext h'
  infer_instance

theorem exists_eq_tbA_mul (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (φ : Qn c n →+ ZMod (l ^ n)) :
    ∃ b : Qn c n, ∀ a : Qn c n, φ a = GlobalTheory.Ord2.SelPerp.tbA c n (a * b) := by
  classical
  haveI := coef_free_pairSurj l c
  let e := Module.Free.chooseBasis ℤ_[l] c.O
  let f : c.O →ₗ[ℤ_[l]] ℤ_[l] := e.constr ℤ_[l] fun i => (((φ (red c n (e i))).val : ℕ) : ℤ_[l])
  have hf : ∀ x : c.O, PadicInt.toZModPow n (f x) = φ (red c n x) := by
    intro x
    have hx : x ∈ Submodule.span ℤ_[l] (Set.range e) := by rw [e.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      simp only [f, Module.Basis.constr_basis]
      rw [map_natCast, ZMod.natCast_zmod_val]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
    | smul a x _ hx =>
      rw [map_smul, smul_eq_mul, map_mul, hx, red_smul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  obtain ⟨b, hb, -⟩ := tau_spec c f
  refine ⟨red c n b, fun a => ?_⟩
  obtain ⟨x, rfl⟩ := red_surjective c n a
  rw [← hf, hb, ← map_mul, tbA_red, mul_comm]

end GlobalTheory.Ord2.SelPerp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqOrdDualGeneratorPairingOfAdditiveMapStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_eq_ordDualGeneratorPairing_of_additiveMap : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (φ : Qn c n →+ ZMod (l ^ n)), ∃ b : Qn c n, ∀ a : Qn c n, φ a = GlobalTheory.Ord2.SelPerp.tbA c n (a * b) := by
  first | exact @GlobalTheory.Ord2.SelPerp.exists_eq_tbA_mul | exact GlobalTheory.Ord2.SelPerp.exists_eq_tbA_mul | (intros; apply GlobalTheory.Ord2.SelPerp.exists_eq_tbA_mul <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.coef_free_pairSurj | exact GlobalTheory.Ord2.SelPerp.coef_free_pairSurj | (intros; apply GlobalTheory.Ord2.SelPerp.coef_free_pairSurj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualSelmerClassesGiveNoncohomologousCochains
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section
namespace GlobalTheory.Ord2.SelPerp

theorem phi_bijective : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ), Function.Bijective (GlobalTheory.Ord2.SelPerp.Phi c n) := by
  intro l _ c n
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    have h : ∀ x : Mn c n, tbA c n (x 0 * y 1 - x 1 * y 0) = 0 := fun x : Mn c n => by
      rw [← Phi_apply, hy]; rfl
    have h1 : y 1 = 0 := GlobalTheory.T.ordDualGeneratorPairing_modPow_nondegenerate l c n _ fun a => by simpa using h (Pi.single 0 a)
    have h0 : y 0 = 0 := GlobalTheory.T.ordDualGeneratorPairing_modPow_nondegenerate l c n _ fun a => by simpa using h (Pi.single 1 (-a))
    funext i
    fin_cases i
    · exact h0
    · exact h1
  · intro φ
    let φ' : Mn c n →ₗ[ZMod (l ^ n)] ZMod (l ^ n) := φ
    obtain ⟨b0, h0⟩ := GlobalTheory.T.exists_eq_ordDualGeneratorPairing_of_additiveMap l c n (φ'.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin 2 => Qn c n) 0))
    obtain ⟨b1, h1⟩ := GlobalTheory.T.exists_eq_ordDualGeneratorPairing_of_additiveMap l c n (φ'.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin 2 => Qn c n) 1))
    refine ⟨![-b1, b0], ?_⟩
    apply LinearMap.ext
    intro x
    change Phi c n ![-b1, b0] x = φ x
    have e : x = Pi.single 0 (x 0) + Pi.single 1 (x 1) := by
      funext i; fin_cases i <;> simp
    have e2 : φ x = φ' (Pi.single 0 (x 0)) + φ' (Pi.single 1 (x 1)) := by
      rw [← map_add (f := _), ← e]; rfl
    have h0' : φ' (Pi.single 0 (x 0)) = tbA c n (x 0 * b0) := h0 (x 0)
    have h1' : φ' (Pi.single 1 (x 1)) = tbA c n (x 1 * b1) := h1 (x 1)
    rw [Phi_apply, e2, h0', h1', ← map_add (f := _)]
    congr 1
    simp

theorem ord_perp : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ), 1 ≤ n → ∀ (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hdet : dt W ^ 2 = 1) (hcont : Continuous W) (S : Finset Pl) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (B : ValuationSubring Ω) (v : Pl), IsPlaceOver B v → (∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) → ∀ f : Z1 ((twDual μ (rhoS c n W hint S hN)).comp (locHom (S : Set Pl) B)), (∀ a ∈ ordCond c n W hint S hN B, cupH1H1TwistedDual μ (rhoS c n W hint S hN) (locHom (S : Set Pl) B) ((contAction_rhoS c n W hint S hN hcont).comp' (continuous_locHom _ B)) (Submodule.mkQ _ f) a = 0) → ∀ y : G ℚ Ω → Mn c n, (∀ (s : G ℚ Ω) (hs : s ∈ Dec (F := ℚ) B), GlobalTheory.Ord2.SelPerp.Phi c n (y s) = f.1 ⟨s, hs⟩) → ∃ m : Qn c n, ∀ s ∈ Dec (F := ℚ) B, y s 1 = matQ c n (dual1 W) (CupCob.dual_representation_integral c W hdet hint) s 1 1 * m - m := by
  intro hL l _ Ω _ _ _ c n hn W hint hdet hcont S hN μ hμ B v hB hup f hf y hy
  obtain ⟨m, hm⟩ := GlobalTheory.T.dualCocycle_coboundary_on_stableLine_of_orthogonal hL l Ω c n hn W hint hcont S hN μ hμ B v hB hup f hf
  obtain ⟨w, rfl⟩ := (phi_bijective l c n).2 m
  refine ⟨w 1, fun s hs => ?_⟩
  have h10 : matQ c n (dual1 W) (CupCob.dual_representation_integral c W hdet hint) s 1 0 = 0 := by
    rw [matQ_apply, ← map_zero (red c n)]
    congr 1
    apply Subtype.ext
    show mat (dual1 W) s 1 0 = 0
    rw [CupCob.mat_dual1 W hdet, Matrix.smul_apply, hup s hs, smul_zero]
  rw [← sub_eq_zero]
  refine GlobalTheory.T.ordDualGeneratorPairing_modPow_nondegenerate l c n _ fun u => ?_
  have h := hm ⟨s, hs⟩ u
  have e := GlobalTheory.T.planePairing_equivariant_twist_cartierDual l Ω c n W hint hdet S hN μ hμ s w
  have e' : twDual μ (rhoS c n W hint S hN) (locHom (S : Set Pl) B ⟨s, hs⟩) (Phi c n w) =
      Phi c n (matQ c n (dual1 W) (CupCob.dual_representation_integral c W hdet hint) s *ᵥ w) := e.symm
  rw [← hy s hs, e', Phi_apply, Phi_apply, Phi_apply, ← map_sub, ← sub_eq_zero, ← map_sub] at h
  rw [← h]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h10, Pi.single_eq_same, ne_eq, one_ne_zero,
    not_false_eq_true, Pi.single_eq_of_ne]
  ring


set_option maxHeartbeats 1000000 in
theorem sel_perp : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (hW : Nf e S A W) (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (n : ℕ), 1 ≤ n → ∀ μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ, μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∃ z : SelD c n W hint S hN A hW.cont μ → (G ℚ Ω → Fin 2 → Qbar l), (∀ x, GwCount.SelN c n S A (dual1 W) (z x)) ∧ ∀ x x', x ≠ x' → ¬ Cob1 c n (dual1 W) ⊤ (z x - z x') := by
  intro hL l _ Ω _ _ _ e S A W hW c hint hN n hn μ hμ
  have hdet := hW.det2
  have hint' := CupCob.dual_representation_integral c W hdet hint
  have hbij : Function.Bijective (Phi c n) := phi_bijective l c n
  set E := LinearEquiv.ofBijective (Phi c n) hbij with hE
  have hΦΨ : ∀ φ, Phi c n (E.symm φ) = φ := fun φ => E.apply_symm_apply φ
  have heq := GlobalTheory.T.planePairing_equivariant_twist_cartierDual l Ω c n W hint hdet S hN μ hμ
  have hΨeq : ∀ s φ, E.symm (twDual μ (rhoS c n W hint S hN) (toGS Ω (S : Set Pl) s) φ) =
      matQ c n (dual1 W) hint' s *ᵥ E.symm φ := by
    intro s φ
    apply hbij.1
    rw [hΦΨ, heq, hΦΨ]
  set rho := rhoS c n W hint S hN with hrho_def
  have hcA : ContAction rho := contAction_rhoS c n W hint S hN hW.cont
  let rep : SelD c n W hint S hN A hW.cont μ → Z1 (twDual μ rho) :=
    fun x => Function.surjInv (Submodule.mkQ_surjective _) x.1
  have hrep : ∀ x, Submodule.mkQ _ (rep x) = x.1 := fun x => Function.surjInv_eq (Submodule.mkQ_surjective _) x.1
  let Y : SelD c n W hint S hN A hW.cont μ → G ℚ Ω → Mn c n := fun x s => E.symm ((rep x).1 (toGS Ω (S : Set Pl) s))
  have hY : ∀ x s, Phi c n (Y x s) = (rep x).1 (toGS Ω (S : Set Pl) s) := fun x s => hΦΨ _
  have hYc : ∀ x s t, Y x (s * t) = Y x s + matQ c n (dual1 W) hint' s *ᵥ Y x t := by
    intro x s t
    simp only [Y, map_mul, (rep x).2.2, map_add (f := _), hΨeq]
  refine ⟨fun x s => lftV c n (Y x s), fun x => ?_, fun x x' hne hcob => ?_⟩
  · have hsel0 := (mem_Sel _ _ _ _ _).1 x.2
    refine ⟨⟨?_, fun s i => lftV_mem c n _ i, fun s _ t _ => ?_⟩, fun a ha => ?_, fun q hq hlq => ?_, ?_⟩
    · have h1 : Continuous fun s => (rep x).1 (toGS Ω (S : Set Pl) s) := (rep x).2.1.comp (continuous_toGS Ω _)
      have h2 : Continuous fun s => lftV c n (E.symm ((rep x).1 (toGS Ω (S : Set Pl) s))) :=
        (continuous_of_discreteTopology (f := fun φ => lftV c n (E.symm φ))).comp h1
      exact h2.continuousOn
    · intro i
      dsimp only
      have hb : ∀ i, (lftV c n (Y x s) + mat (dual1 W) s *ᵥ lftV c n (Y x t)) i ∈ c.O := fun i =>
        add_mem (lftV_mem c n _ i) (CupCob.mulVec_mem c _ _ (hint' s) (lftV_mem c n _) i)
      refine cg_of_red (lftV_mem c n _ i) (hb i) ?_
      have e1 : (⟨(lftV c n (Y x s) + mat (dual1 W) s *ᵥ lftV c n (Y x t)) i, hb i⟩ : c.O) =
          ⟨lftV c n (Y x s) i, lftV_mem c n _ i⟩ +
            ⟨(mat (dual1 W) s *ᵥ lftV c n (Y x t)) i, CupCob.mulVec_mem c _ _ (hint' s) (lftV_mem c n _) i⟩ := rfl
      rw [e1, map_add (f := _), red_lftV, red_mulVec c n _ (hint' s) _ (lftV_mem c n _), red_lftV, hYc]
      simp only [red_lftV, Pi.add_apply]
      rfl
    · intro i
      have h1 : toGS Ω (S : Set Pl) a = 1 := MonoidHom.mem_ker.1 ha
      have h0 : (rep x).1 1 = 0 := by
        have := (rep x).2.2 1 1
        rw [mul_one, map_one, Module.End.one_apply] at this
        exact add_left_cancel (this.symm.trans (add_zero _).symm)
      show Cg n (lftV c n (Y x a) i) 0
      refine cg_of_red (lftV_mem c n _ i) (zero_mem _) ?_
      rw [red_lftV]
      simp only [Y, h1, h0, map_zero, Pi.zero_apply]
      exact (map_zero (red c n)).symm
    · obtain ⟨v0, hA0, hl0⟩ := hW.atL
      have hnot : ¬ IsPlaceOver A q := fun h => hlq ((eq_of_isPlaceOver hA0 h) ▸ hl0)
      have hBq : IsPlaceOver (Av A S ⟨q, hq⟩) q := isPlaceOver_Av A S ⟨q, hq⟩
      have hsel := hsel0 ⟨q, hq⟩
      have hLc : Lc c n W hint S hN A ⟨q, hq⟩ = H1ur ((rhoS c n W hint S hN).comp (locFam S (Av A S) ⟨q, hq⟩))
          ((Ine (F := ℚ) (Av A S ⟨q, hq⟩)).subgroupOf (Dec (F := ℚ) (Av A S ⟨q, hq⟩))) := if_neg hnot
      rw [mem_perpCond, hLc, ← hrep x] at hsel
      obtain ⟨m, hm⟩ := GlobalTheory.T.dualCocycle_coboundary_on_inertia_of_orthogonal hL l Ω n hn S (Mn c n) rho hcA μ hμ (Av A S ⟨q, hq⟩) q hBq hlq
        (restrictCocycles1 _ (locFam S (Av A S) ⟨q, hq⟩) (continuous_locFam S (Av A S) ⟨q, hq⟩) (rep x)) hsel
      refine ⟨Av A S ⟨q, hq⟩, hBq, lftV c n (E.symm m), lftV_mem c n _, fun s hs i => ?_⟩
      have hsD : s ∈ Dec (F := ℚ) (Av A S ⟨q, hq⟩) := hs.1
      have hms : (rep x).1 (toGS Ω (S : Set Pl) s) = twDual μ rho (toGS Ω (S : Set Pl) s) m - m := hm ⟨s, hsD⟩ hs
      have hb : (mat (dual1 W) s *ᵥ lftV c n (E.symm m) - lftV c n (E.symm m)) i ∈ c.O :=
        sub_mem (CupCob.mulVec_mem c _ _ (hint' s) (lftV_mem c n _) i) (lftV_mem c n _ i)
      refine cg_of_red (lftV_mem c n _ i) hb ?_
      have e1 : (⟨(mat (dual1 W) s *ᵥ lftV c n (E.symm m) - lftV c n (E.symm m)) i, hb⟩ : c.O) =
          ⟨(mat (dual1 W) s *ᵥ lftV c n (E.symm m)) i, CupCob.mulVec_mem c _ _ (hint' s) (lftV_mem c n _) i⟩ -
            ⟨lftV c n (E.symm m) i, lftV_mem c n _ i⟩ := rfl
      rw [e1, map_sub, red_mulVec c n _ (hint' s) _ (lftV_mem c n _), red_lftV, red_lftV]
      simp only [red_lftV, Y, hms, map_sub, hΨeq, Pi.sub_apply]
      rfl
    · obtain ⟨v0, hA0, hl0⟩ := hW.atL
      have hv0 : v0 ∈ S := hW.above v0 hl0
      have hAv : Av A S ⟨v0, hv0⟩ = A := if_pos hA0
      have hsel := hsel0 ⟨v0, hv0⟩
      have hLc : Lc c n W hint S hN A ⟨v0, hv0⟩ = ordCond c n W hint S hN (Av A S ⟨v0, hv0⟩) := if_pos hA0
      rw [mem_perpCond, hLc, ← hrep x] at hsel
      have hup : ∀ s ∈ Dec (F := ℚ) (Av A S ⟨v0, hv0⟩), mat W s 1 0 = 0 := by
        rw [hAv]; exact hW.upper
      obtain ⟨m, hm⟩ := ord_perp hL l Ω c n hn W hint hdet hW.cont S hN μ hμ (Av A S ⟨v0, hv0⟩) v0
        (isPlaceOver_Av A S ⟨v0, hv0⟩) hup (restrictCocycles1 _ _ (continuous_locFam S (Av A S) ⟨v0, hv0⟩) (rep x)) hsel
        (Y x) (fun s hs => hY x s)
      rw [hAv] at hm
      refine ⟨lft c n m, (lft c n m).2, fun s hs => ?_⟩
      refine cg_of_red (lftV_mem c n _ 1) (sub_mem (mul_mem (hint' s 1 1) (lft c n m).2) (lft c n m).2) ?_
      rw [red_lftV, hm s hs]
      show _ = red c n (⟨mat (dual1 W) s 1 1, hint' s 1 1⟩ * lft c n m - lft c n m)
      rw [map_sub, map_mul, red_lft]
      rfl
  · apply hne
    obtain ⟨v, hv, hcv⟩ := hcob
    apply Subtype.ext
    rw [← hrep x, ← hrep x', ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap]
    refine (mem_coboundaries1 _ _).2 ⟨Phi c n (fun i => red c n ⟨v i, hv i⟩), fun g => ?_⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective g
    have hs : ∀ i, Cg n (lftV c n (Y x s) i - lftV c n (Y x' s) i) ((mat (dual1 W) s *ᵥ v - v) i) :=
      hcv s (Subgroup.mem_top s)
    have key : Y x s - Y x' s = matQ c n (dual1 W) hint' s *ᵥ (fun i => red c n ⟨v i, hv i⟩) -
        (fun i => red c n ⟨v i, hv i⟩) := by
      funext i
      have h := red_of_cg (sub_mem (lftV_mem c n (Y x s) i) (lftV_mem c n (Y x' s) i))
        (sub_mem (CupCob.mulVec_mem c _ _ (hint' s) hv i) (hv i)) (hs i)
      rw [show (⟨lftV c n (Y x s) i - lftV c n (Y x' s) i, sub_mem (lftV_mem c n (Y x s) i) (lftV_mem c n (Y x' s) i)⟩ : c.O) =
          ⟨lftV c n (Y x s) i, lftV_mem c n _ i⟩ - ⟨lftV c n (Y x' s) i, lftV_mem c n _ i⟩ from rfl,
        show (⟨(mat (dual1 W) s *ᵥ v) i - v i, sub_mem (CupCob.mulVec_mem c _ _ (hint' s) hv i) (hv i)⟩ : c.O) =
          ⟨(mat (dual1 W) s *ᵥ v) i, CupCob.mulVec_mem c _ _ (hint' s) hv i⟩ - ⟨v i, hv i⟩ from rfl,
        map_sub, map_sub, red_lftV, red_lftV, red_mulVec c n _ (hint' s) _ hv] at h
      rw [Pi.sub_apply, Pi.sub_apply, h]
      rfl
    have h2 := congrArg (Phi c n) key
    rw [map_sub, map_sub, hY x s, hY x' s, heq s] at h2
    exact h2

end GlobalTheory.Ord2.SelPerp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualSelmerClassesGiveNoncohomologousCochainsStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.dualSelmer_classes_give_noncohomologous_cochains : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (hW : Nf e S A W) (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (n : ℕ), 1 ≤ n → ∀ μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ, μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∃ z : SelD c n W hint S hN A hW.cont μ → (G ℚ Ω → Fin 2 → Qbar l), (∀ x, GwCount.SelN c n S A (dual1 W) (z x)) ∧ ∀ x x', x ≠ x' → ¬ Cob1 c n (dual1 W) ⊤ (z x - z x') := by
  first | exact @GlobalTheory.Ord2.SelPerp.sel_perp | exact GlobalTheory.Ord2.SelPerp.sel_perp | (intros; apply GlobalTheory.Ord2.SelPerp.sel_perp <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.ord_perp | exact GlobalTheory.Ord2.SelPerp.ord_perp | (intros; apply GlobalTheory.Ord2.SelPerp.ord_perp <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.phi_bijective | exact GlobalTheory.Ord2.SelPerp.phi_bijective | (intros; apply GlobalTheory.Ord2.SelPerp.phi_bijective <;> assumption)
end
