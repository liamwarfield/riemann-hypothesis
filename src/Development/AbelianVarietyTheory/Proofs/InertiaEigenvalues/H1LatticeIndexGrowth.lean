module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentWittTiltEqZeroOfResidueZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeModPowActionIsLocallyConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeModPowActionIsLocallyConstant
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open scoped Pointwise

namespace GlobalTheory.InertiaEigenvalues

theorem actQ_pow_isLocallyConstant : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep G ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), IsLocallyConstant fun g : G => actQ LA _ hI g x := by
  intro l _ G _ _ LL _ _ _ O _ _ hG A LA r hI x
  obtain ⟨_, _, _, hTR, hO⟩ := hG
  haveI := hTR
  haveI : CharZero LL := charZero_of_injective_algebraMap (algebraMap ℚ_[l] LL).injective
  haveI := IsModuleTopology.topologicalAddGroup LL A.V
  set c : LL := ((l : ℕ) : LL) ^ r with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hT : IsOpen (LA.T : Set A.V) :=
    GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hO LA.T LA.fg LA.span
  have hcT : IsOpen (c • (LA.T : Set A.V)) := hT.smul₀ hc0
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [IsLocallyConstant.iff_exists_open]
  intro g0
  refine ⟨(fun g => A.ρ g t - A.ρ g0 t) ⁻¹' (c • (LA.T : Set A.V)),
    hcT.preimage ((A.cont _).sub continuous_const), ?_, ?_⟩
  · show A.ρ g0 t - A.ρ g0 t ∈ c • (LA.T : Set A.V)
    rw [sub_self]
    exact ⟨0, LA.T.zero_mem, smul_zero c⟩
  · intro g hg
    obtain ⟨w, hw, hwe⟩ := hg
    simp only [actQ, Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨⟨w, hw⟩, Submodule.mem_top, ?_⟩
    apply Subtype.ext
    simp only [Submodule.coe_smul, Submodule.coe_sub, actT, LinearMap.restrict_coe_apply,
      LinearMap.coe_restrictScalars]
    rw [← algebraMap_smul LL ((l : O) ^ r) w, map_pow, map_natCast]
    exact hwe

end GlobalTheory.InertiaEigenvalues
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeModPowActionIsLocallyConstantStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_modPow_action_isLocallyConstant : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep G ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), IsLocallyConstant fun g : G => actQ LA _ hI g x := by
  first | exact @GlobalTheory.InertiaEigenvalues.actQ_pow_isLocallyConstant | exact GlobalTheory.InertiaEigenvalues.actQ_pow_isLocallyConstant | (intros; apply GlobalTheory.InertiaEigenvalues.actQ_pow_isLocallyConstant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1H0TransportLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1H0TransportLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.GaloisTransport

section Generic

variable {R G' G Q M : Type} [CommRing R] [Group G'] [TopologicalSpace G'] [Group G]
  [TopologicalSpace G] [AddCommGroup Q] [Module R Q] {N : ℕ} [AddCommGroup M] [Module (ZMod N) M]
  [TopologicalSpace M] [DiscreteTopology M]

theorem card_H1_transport (φ : G' ≃* G) (hφ : Continuous φ ∧ Continuous φ.symm)
    (act : G' → Q → Q) (Z B : Submodule R (G' → Q))
    (hZ : ∀ c, c ∈ Z ↔ IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + act g (c h))
    (hB : ∀ c, c ∈ B ↔ ∃ t, ∀ g, c g = act g t - t)
    (e : Q ≃+ M) (rho : Representation (ZMod N) G M)
    (hr : ∀ g x, rho g (e x) = e (act (φ.symm g) x)) :
    Nat.card (↥Z ⧸ B.comap Z.subtype) = Nat.card (ReciprocityTheory.Gal.H1 rho) := by
  have hr' : ∀ g x, rho (φ g) (e x) = e (act g x) := fun g x => by
    rw [hr, MulEquiv.symm_apply_apply]
  let F : (G' → Q) → (G → M) := fun c g => e (c (φ.symm g))
  have hF : ∀ c g, F c (φ g) = e (c g) := fun c g => by simp only [F, MulEquiv.symm_apply_apply]
  have hFB : ∀ c, c ∈ B ↔ F c ∈ ReciprocityTheory.Gal.B1 rho := by
    intro c
    rw [hB, ReciprocityTheory.Gal.mem_coboundaries1]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨e t, fun g => ?_⟩
      simp only [F, ht, map_sub, hr]
    · rintro ⟨m, hm⟩
      refine ⟨e.symm m, fun g => ?_⟩
      have h1 := hm (φ g)
      rw [hF] at h1
      apply e.injective
      rw [h1, map_sub, ← hr', e.apply_symm_apply]
  have hZf : ∀ c : ↥Z, F c.1 ∈ ReciprocityTheory.Gal.Z1 rho := fun c => by
    obtain ⟨hc1, hc2⟩ := (hZ c.1).1 c.2
    refine ⟨((hc1.comp_continuous hφ.2).comp e).continuous, fun g h => ?_⟩
    simp only [F, map_mul, hc2, map_add (f := _), hr]
  have hZb : ∀ f : ↥(ReciprocityTheory.Gal.Z1 rho), (fun g => e.symm (f.1 (φ g))) ∈ Z := fun f => by
    obtain ⟨hf1, hf2⟩ := (ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ _).1 f.2
    refine (hZ _).2 ⟨((IsLocallyConstant.iff_continuous _).2 (hf1.comp hφ.1)).comp e.symm,
      fun g h => ?_⟩
    apply e.injective
    have h2 := hr' g (e.symm (f.1 (φ h)))
    rw [e.apply_symm_apply] at h2
    simp only [map_mul, hf2, map_add (f := _), AddEquiv.apply_symm_apply, h2]
  let E : ↥Z ≃ ↥(ReciprocityTheory.Gal.Z1 rho) :=
    { toFun := fun c => ⟨F c.1, hZf c⟩
      invFun := fun f => ⟨fun g => e.symm (f.1 (φ g)), hZb f⟩
      left_inv := fun c => Subtype.ext (funext fun g => by
        show e.symm (F c.1 (φ g)) = c.1 g
        rw [hF, e.symm_apply_apply])
      right_inv := fun f => Subtype.ext (funext fun g => by
        show e (e.symm (f.1 (φ (φ.symm g)))) = f.1 g
        rw [e.apply_symm_apply, MulEquiv.apply_symm_apply]) }
  have hEsub : ∀ a b : ↥Z, ((E a - E b : ↥(ReciprocityTheory.Gal.Z1 rho)) : G → M) = F ((a - b : ↥Z) : G' → Q) :=
    fun a b => funext fun g => by
      show e (a.1 (φ.symm g)) - e (b.1 (φ.symm g)) = e (a.1 (φ.symm g) - b.1 (φ.symm g))
      rw [map_sub]
  refine Nat.card_congr (Quotient.congr E fun a b => ?_)
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap,
    Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_subtype, hEsub, hFB]

theorem card_H0_transport (φ : G' ≃* G) (act : G' → Q → Q)
    (e : Q ≃+ M) (rho : Representation (ZMod N) G M)
    (hr : ∀ g x, rho g (e x) = e (act (φ.symm g) x)) :
    Nat.card {x : Q // ∀ g, act g x = x} = Nat.card (ReciprocityTheory.Gal.H0 rho) := by
  have hr' : ∀ g x, rho (φ g) (e x) = e (act g x) := fun g x => by
    rw [hr, MulEquiv.symm_apply_apply]
  refine Nat.card_congr
    { toFun := fun x => ⟨e x.1, (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun g => by rw [hr, x.2]⟩
      invFun := fun m => ⟨e.symm m.1, fun g => by
        apply e.injective
        rw [← hr', e.apply_symm_apply]
        exact (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 m.2 (φ g)⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun m => Subtype.ext (e.apply_symm_apply m.1) }

end Generic

theorem card_H1_H0_transport : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (I : Submodule O ↥LA.T) (hI : StableSub LA I) (N : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod N) M] [TopologicalSpace M] [DiscreteTopology M] (e : (↥LA.T ⧸ I) ≃+ M) (rho : Representation (ZMod N) (Formalism.GaloisCohomology.GK l K.1) M), (∀ g x, rho g (e x) = e (actQ LA I hI ((IntermediateField.fixingSubgroupEquiv K.1).symm g) x)) → Nat.card (QuotientCohomology LA I hI) = Nat.card (ReciprocityTheory.Gal.H1 rho) ∧ Nat.card {x : ↥LA.T ⧸ I // ∀ g, actQ LA I hI g x = x} = Nat.card (ReciprocityTheory.Gal.H0 rho) := by
  intro l _ K LL _ _ _ O _ _ A LA I hI N M _ _ _ _ e rho hrho
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hφ := GlobalTheory.fixingSubgroupEquiv_bicontinuous _ _ K.1
  refine ⟨card_H1_transport _ hφ (fun g x => actQ LA I hI g x) (quotientCocycles LA I hI) (BQ LA I hI)
    (fun c => Iff.rfl) (fun c => ?_) e rho hrho,
    card_H0_transport _ (fun g x => actQ LA I hI g x) e rho hrho⟩
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, fun g => (congrFun ht g).symm⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, funext fun g => (ht g).symm⟩

end GlobalTheory.GaloisTransport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1H0TransportLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_H1_H0_transport_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (I : Submodule O ↥LA.T) (hI : StableSub LA I) (N : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod N) M] [TopologicalSpace M] [DiscreteTopology M] (e : (↥LA.T ⧸ I) ≃+ M) (rho : Representation (ZMod N) (Formalism.GaloisCohomology.GK l K.1) M), (∀ g x, rho g (e x) = e (actQ LA I hI ((IntermediateField.fixingSubgroupEquiv K.1).symm g) x)) → Nat.card (QuotientCohomology LA I hI) = Nat.card (ReciprocityTheory.Gal.H1 rho) ∧ Nat.card {x : ↥LA.T ⧸ I // ∀ g, actQ LA I hI g x = x} = Nat.card (ReciprocityTheory.Gal.H0 rho) := by
  first | exact @GlobalTheory.GaloisTransport.card_H1_H0_transport | exact GlobalTheory.GaloisTransport.card_H1_H0_transport | (intros; apply GlobalTheory.GaloisTransport.card_H1_H0_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TracePairingInjectiveEquivariantLevelMap
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TracePairingInjectiveEquivariantLevelMap
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.TraceLevel

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL]
  {A A' : GRep ↥(GK K) ℚ_[l] LL O} {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
  {m : A.V →ₗ[LL] A'.V →ₗ[LL] LL} {lam : LL →ₗ[ℚ_[l]] ℚ_[l]}
  (h2 : ∀ y, y ∈ LA'.T ↔ ∀ x ∈ LA.T, ∃ a : O, m x y = algebraMap O LL a)
  (hlam : ∀ a : LL, (∀ b : O, ∃ u : ℤ_[l], lam (a * algebraMap O LL b) = (u : ℚ_[l])) ↔
      ∃ b : O, algebraMap O LL b = a)


include h2 hlam in
theorem norm_le_one (x : ↥LA.T) (y : ↥LA'.T) : ‖lam (m x y)‖ ≤ 1 := by
  obtain ⟨a, ha⟩ := (h2 y).1 y.2 x x.2
  obtain ⟨u, hu⟩ := (hlam (m x y)).2 ⟨a, ha.symm⟩ 1
  rw [map_one, mul_one] at hu
  rw [hu]
  exact u.norm_le_one

def uv (x : ↥LA.T) (y : ↥LA'.T) : ℤ_[l] :=
  ⟨lam (m x y), norm_le_one h2 hlam x y⟩

theorem coe_uv (x : ↥LA.T) (y : ↥LA'.T) :
    ((uv h2 hlam x y : ℤ_[l]) : ℚ_[l]) = lam (m x y) := rfl

theorem lam_natPow_mul (z : LL) (r : ℕ) :
    lam ((l : LL) ^ r * z) = (l : ℚ_[l]) ^ r * lam z := by
  have : (l : LL) ^ r * z = ((l : ℚ_[l]) ^ r) • z := by
    rw [Algebra.smul_def]; simp
  rw [this, map_smul, smul_eq_mul]

theorem uv_add_left (x x' : ↥LA.T) (y : ↥LA'.T) :
    uv h2 hlam (x + x') y = uv h2 hlam x y + uv h2 hlam x' y := by
  apply Subtype.ext; simp [coe_uv]

theorem uv_add_right (x : ↥LA.T) (y y' : ↥LA'.T) :
    uv h2 hlam x (y + y') = uv h2 hlam x y + uv h2 hlam x y' := by
  apply Subtype.ext; simp [coe_uv]

theorem uv_zero_left (y : ↥LA'.T) : uv h2 hlam 0 y = 0 := by
  apply Subtype.ext; simp [coe_uv]

theorem uv_zero_right (x : ↥LA.T) : uv h2 hlam x 0 = 0 := by
  apply Subtype.ext; simp [coe_uv]

theorem uv_smul_left (r : ℕ) (x : ↥LA.T) (y : ↥LA'.T) :
    uv h2 hlam ((((l : ℕ) : O) ^ r) • x) y = (l : ℤ_[l]) ^ r * uv h2 hlam x y := by
  apply Subtype.ext
  rw [coe_uv, PadicInt.coe_mul, coe_uv]
  have : (((((l : ℕ) : O) ^ r) • x : ↥LA.T) : A.V) = ((l : LL) ^ r) • (x : A.V) := by
    rw [Submodule.coe_smul, ← algebraMap_smul LL]; simp
  rw [this, map_smul, LinearMap.smul_apply, smul_eq_mul, lam_natPow_mul]
  simp

theorem uv_smul_right (r : ℕ) (x : ↥LA.T) (y : ↥LA'.T) :
    uv h2 hlam x ((((l : ℕ) : O) ^ r) • y) = (l : ℤ_[l]) ^ r * uv h2 hlam x y := by
  apply Subtype.ext
  rw [coe_uv, PadicInt.coe_mul, coe_uv]
  have : (((((l : ℕ) : O) ^ r) • y : ↥LA'.T) : A'.V) = ((l : LL) ^ r) • (y : A'.V) := by
    rw [Submodule.coe_smul, ← algebraMap_smul LL]; simp
  rw [this, map_smul, smul_eq_mul, lam_natPow_mul]
  simp

theorem toZModPow_natPow_mul (r : ℕ) (u : ℤ_[l]) :
    PadicInt.toZModPow r ((l : ℤ_[l]) ^ r * u) = 0 := by
  rw [map_mul, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

theorem mem_lr {r : ℕ} {V : Type} [AddCommGroup V] [Module O V] {T : Submodule O V} {x : ↥T}
    (hx : x ∈ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥T)) :
    ∃ x' : ↥T, (((l : ℕ) : O) ^ r) • x' = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
  obtain ⟨x', -, hx'⟩ := hx
  exact ⟨x', hx'⟩

def pr (r : ℕ) (y : ↥LA'.T) : ↥LA.T →+ ZMod (l ^ r) where
  toFun x := PadicInt.toZModPow r (uv h2 hlam x y)
  map_zero' := by rw [uv_zero_left, map_zero]
  map_add' a b := by rw [uv_add_left, map_add (f := _)]

def psi0 (r : ℕ) (y : ↥LA'.T) :
    (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) →+ ZMod (l ^ r) :=
  ((((Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)).restrictScalars ℤ).liftQ
      (pr h2 hlam r y).toIntLinearMap (by
        intro x hx
        obtain ⟨x', rfl⟩ := mem_lr ((Submodule.restrictScalars_mem ℤ _ _).1 hx)
        rw [LinearMap.mem_ker]
        show PadicInt.toZModPow r (uv h2 hlam _ y) = 0
        rw [uv_smul_left, toZModPow_natPow_mul])).toAddMonoidHom.comp
    (Submodule.Quotient.restrictScalarsEquiv ℤ
      (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)).symm.toLinearMap.toAddMonoidHom

theorem tracePairingLevelMap_mk (r : ℕ) (y : ↥LA'.T) (x : ↥LA.T) :
    psi0 h2 hlam r y (Submodule.Quotient.mk x) = PadicInt.toZModPow r (uv h2 hlam x y) := by
  simp [psi0, pr]

variable {r : ℕ} {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M]
  (e : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) ≃+ M)

def psi1 (y : ↥LA'.T) : TDual (ZMod (l ^ r)) M :=
  TDual.mk (((psi0 h2 hlam r y).comp e.symm.toAddMonoidHom).toZModLinearMap (l ^ r))

theorem tracePairingLevelDual_apply (y : ↥LA'.T) (x : ↥LA.T) :
    psi1 h2 hlam e y (e (Submodule.Quotient.mk x)) = PadicInt.toZModPow r (uv h2 hlam x y) := by
  simp [psi1, tracePairingLevelMap_mk]

theorem tracePairingLevelDual_ext {φ φ' : TDual (ZMod (l ^ r)) M}
    (h : ∀ x : ↥LA.T, φ (e (Submodule.Quotient.mk x)) = φ' (e (Submodule.Quotient.mk x))) :
    φ = φ' := by
  apply LinearMap.ext
  intro z
  obtain ⟨q, rfl⟩ := e.surjective z
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact h x

theorem tracePairingLevelDual_zero : psi1 h2 hlam e 0 = 0 :=
  tracePairingLevelDual_ext e fun x => by
    rw [tracePairingLevelDual_apply h2 hlam e, uv_zero_right, map_zero]; exact (LinearMap.zero_apply _).symm

theorem tracePairingLevelDual_add (y y' : ↥LA'.T) :
    psi1 h2 hlam e (y + y') = psi1 h2 hlam e y + psi1 h2 hlam e y' :=
  tracePairingLevelDual_ext e fun x => by
    rw [TDual.add_apply, tracePairingLevelDual_apply h2 hlam e, tracePairingLevelDual_apply h2 hlam e, tracePairingLevelDual_apply h2 hlam e,
      uv_add_right, map_add]

def psi1Hom : ↥LA'.T →+ TDual (ZMod (l ^ r)) M where
  toFun := psi1 h2 hlam e
  map_zero' := tracePairingLevelDual_zero h2 hlam e
  map_add' := tracePairingLevelDual_add h2 hlam e

def psiQ : (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) →+
    TDual (ZMod (l ^ r)) M :=
  ((((Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)).restrictScalars ℤ).liftQ
      (psi1Hom h2 hlam e).toIntLinearMap (by
        intro y hy
        obtain ⟨y', rfl⟩ := mem_lr ((Submodule.restrictScalars_mem ℤ _ _).1 hy)
        rw [LinearMap.mem_ker]
        show psi1 h2 hlam e _ = 0
        refine tracePairingLevelDual_ext e fun x => ?_
        rw [tracePairingLevelDual_apply h2 hlam e, uv_smul_right, toZModPow_natPow_mul]; exact (LinearMap.zero_apply _).symm)).toAddMonoidHom.comp
    (Submodule.Quotient.restrictScalarsEquiv ℤ
      (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)).symm.toLinearMap.toAddMonoidHom

theorem psiQ_mk (y : ↥LA'.T) (x : ↥LA.T) :
    psiQ h2 hlam e (Submodule.Quotient.mk y) (e (Submodule.Quotient.mk x)) =
      PadicInt.toZModPow r (uv h2 hlam x y) := by
  rw [← tracePairingLevelDual_apply h2 hlam e y x]
  rfl

include e in
theorem psiQ_injective : Function.Injective (psiQ h2 hlam e) := by
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl : (l : LL) ≠ 0 := by
    intro h
    apply hl0
    have h' : algebraMap ℚ_[l] LL (l : ℚ_[l]) = 0 := by rw [map_natCast]; exact h
    exact (map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective).1 h'
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨y, hyq⟩ := Submodule.Quotient.mk_surjective
    (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T) q
  subst hyq
  have hx : ∀ x : ↥LA.T, ∃ c : ℤ_[l], (l : ℤ_[l]) ^ r * c = uv h2 hlam x y := by
    intro x
    have h0 : PadicInt.toZModPow r (uv h2 hlam x y) = 0 := by
      rw [← psiQ_mk h2 hlam e y x, hq]
      exact LinearMap.zero_apply _
    have h1 : uv h2 hlam x y ∈ RingHom.ker (PadicInt.toZModPow (p := l) r) := h0
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, by rw [← hc, mul_comm]⟩
  obtain ⟨z, hz⟩ : ∃ z : A'.V, z = ((l : LL) ^ r)⁻¹ • (y : A'.V) := ⟨_, rfl⟩
  have hzT : z ∈ LA'.T := by
    rw [h2]
    intro x hxT
    suffices hs : ∀ b : O, ∃ u : ℤ_[l], lam (m x z * algebraMap O LL b) = (u : ℚ_[l]) by
      obtain ⟨a, ha⟩ := (hlam (m x z)).1 hs
      exact ⟨a, ha.symm⟩
    intro b
    obtain ⟨c', hc'⟩ := hx (b • ⟨x, hxT⟩)
    refine ⟨c', ?_⟩
    have hb : ((b • (⟨x, hxT⟩ : ↥LA.T) : ↥LA.T) : A.V) = algebraMap O LL b • x := by
      rw [Submodule.coe_smul, algebraMap_smul]
    have e1 : m x z * algebraMap O LL b =
        ((l : LL) ^ r)⁻¹ * m ((b • (⟨x, hxT⟩ : ↥LA.T) : ↥LA.T) : A.V) y := by
      rw [hb, hz]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    have e2 : ((l : LL) ^ r)⁻¹ = algebraMap ℚ_[l] LL (((l : ℚ_[l]) ^ r)⁻¹) := by
      rw [map_inv₀, map_pow, map_natCast]
    rw [e1, e2, ← Algebra.smul_def, map_smul, smul_eq_mul, ← coe_uv h2 hlam, ← hc',
      PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hl0), one_mul]
  have hy : (((l : ℕ) : O) ^ r) • (⟨z, hzT⟩ : ↥LA'.T) = y := by
    apply Subtype.ext
    rw [Submodule.coe_smul, ← algebraMap_smul LL, map_pow, map_natCast]
    show ((l : LL) ^ r) • z = (y : A'.V)
    rw [hz, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hl), one_smul]
  rw [Submodule.Quotient.mk_eq_zero, ← hy]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

omit [TopologicalSpace LL] in
theorem rho_inv {G V : Type} [Group G] [AddCommGroup V] [Module LL V] (ρ : Representation LL G V)
    (h : G) (v : V) : ρ h (ρ h⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem uv_act (c : ↥(GK K) → LL)
    (h1 : ∀ g x y, m (A.ρ g x) (A'.ρ g y) = c g * m x y)
    (hc : ∀ g : ↥(GK K), ∃ w : ℤ_[l], c g = algebraMap ℚ_[l] LL (w : ℚ_[l]) ∧
      (PadicInt.toZModPow r w : ZMod (l ^ r)) =
        ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) :
          ZMod (l ^ r)))
    (g : Formalism.GaloisCohomology.GK l K.1) (x : ↥LA.T) (y : ↥LA'.T) :
    PadicInt.toZModPow r
        (uv h2 hlam x (actT LA' ((IntermediateField.fixingSubgroupEquiv K.1).symm g) y)) =
      ((Formalism.GaloisCohomology.cycK l K.1 r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) *
        PadicInt.toZModPow r
          (uv h2 hlam (actT LA ((IntermediateField.fixingSubgroupEquiv K.1).symm g)⁻¹ x) y) := by
  obtain ⟨w, hw1, hw2⟩ := hc ((IntermediateField.fixingSubgroupEquiv K.1).symm g)
  rw [MulEquiv.apply_symm_apply] at hw2
  rw [← hw2, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [PadicInt.coe_mul, coe_uv, coe_uv]
  generalize (IntermediateField.fixingSubgroupEquiv K.1).symm g = h at hw1
  show lam (m (x : A.V) (A'.ρ h y)) = (w : ℚ_[l]) * lam (m (A.ρ h⁻¹ x) y)
  have key := h1 h (A.ρ h⁻¹ x) y
  rw [show A.ρ h (A.ρ h⁻¹ (x : A.V)) = x from rho_inv A.ρ h x] at key
  rw [key, hw1, ← Algebra.smul_def, map_smul, smul_eq_mul]

omit [TopologicalSpace LL] in
theorem actQ_mk' {G V : Type} [Group G] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (h : G) (x : ↥L.T) :
    actQ L I hI h (Submodule.Quotient.mk x) = Submodule.Quotient.mk (actT L h x) := rfl

include e in
theorem psiQ_equivariant (c : ↥(GK K) → LL)
    (h1 : ∀ g x y, m (A.ρ g x) (A'.ρ g y) = c g * m x y)
    (hc : ∀ g : ↥(GK K), ∃ w : ℤ_[l], c g = algebraMap ℚ_[l] LL (w : ℚ_[l]) ∧
      (PadicInt.toZModPow r w : ZMod (l ^ r)) =
        ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) :
          ZMod (l ^ r)))
    (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T))
    (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T))
    (rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K.1) M)
    (hrho : ∀ g x, rho g (e x) = e (actQ LA _ hI ((IntermediateField.fixingSubgroupEquiv K.1).symm g) x))
    (g : Formalism.GaloisCohomology.GK l K.1) (q : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) :
    psiQ h2 hlam e (actQ LA' _ hI' ((IntermediateField.fixingSubgroupEquiv K.1).symm g) q) =
      ReciprocityTheory.Gal.twDual (Formalism.GaloisCohomology.cycK l K.1 r) rho g (psiQ h2 hlam e q) := by
  induction q using Submodule.Quotient.induction_on with
  | H y =>
  apply tracePairingLevelDual_ext e
  intro x
  have key : psiQ h2 hlam e (Submodule.Quotient.mk
        (actT LA' ((IntermediateField.fixingSubgroupEquiv K.1).symm g) y))
        (e (Submodule.Quotient.mk x)) =
      ((Formalism.GaloisCohomology.cycK l K.1 r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) *
        psiQ h2 hlam e (Submodule.Quotient.mk y) (e (Submodule.Quotient.mk
          (actT LA ((IntermediateField.fixingSubgroupEquiv K.1).symm g)⁻¹ x))) := by
    rw [psiQ_mk h2 hlam e, psiQ_mk h2 hlam e]
    exact uv_act h2 hlam c h1 hc g x y
  have hinv : (IntermediateField.fixingSubgroupEquiv K.1).symm g⁻¹ =
      ((IntermediateField.fixingSubgroupEquiv K.1).symm g)⁻¹ := map_inv _ g
  have hr : rho g⁻¹ (e (Submodule.Quotient.mk x)) = e (Submodule.Quotient.mk
      (actT LA ((IntermediateField.fixingSubgroupEquiv K.1).symm g)⁻¹ x)) := by
    have h0 := hrho g⁻¹ (Submodule.Quotient.mk x)
    rw [hinv] at h0
    exact h0.trans (congrArg e (actQ_mk' LA _ hI _ x))
  have hA' := actQ_mk' LA' _ hI' ((IntermediateField.fixingSubgroupEquiv K.1).symm g) y
  have s1 := congrArg (fun q => psiQ h2 hlam e q (e (Submodule.Quotient.mk x))) hA'
  have s2 := congrArg (fun t => ((Formalism.GaloisCohomology.cycK l K.1 r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) *
    psiQ h2 hlam e (Submodule.Quotient.mk y) t) hr
  have s3 := ReciprocityTheory.Gal.twDual_apply (Formalism.GaloisCohomology.cycK l K.1 r) rho g
    (psiQ h2 hlam e (Submodule.Quotient.mk y)) (e (Submodule.Quotient.mk x))
  beta_reduce at s1 s2
  exact s1.trans (key.trans (s2.symm.trans s3.symm))

end GlobalTheory.TraceLevel

namespace GlobalTheory


open TraceLevel in
theorem tracePairing_levelMap : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (lam : LL →ₗ[ℚ_[l]] ℚ_[l]), (∀ a : LL, (∀ b : O, ∃ u : ℤ_[l], lam (a * algebraMap O LL b) = (u : ℚ_[l])) ↔ ∃ b : O, algebraMap O LL b = a) → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), (∀ g : ↥(GK K), ∃ u : ℤ_[l], (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = (u : ℚ_[l]) ∧ (PadicInt.toZModPow r u : ZMod (l ^ r)) = ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r))) → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] (e : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) ≃+ M) (rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K.1) M), (∀ g x, rho g (e x) = e (actQ LA _ hI ((IntermediateField.fixingSubgroupEquiv K.1).symm g) x)) → ∃ Ψ : (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) →+ ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M, Function.Injective Ψ ∧ ∀ g y, Ψ (actQ LA' _ hI' ((IntermediateField.fixingSubgroupEquiv K.1).symm g) y) = ReciprocityTheory.Gal.twDual (Formalism.GaloisCohomology.cycK l K.1 r) rho g (Ψ y) := by
  intro l _ P K LL _ _ _ O _ _ A A' LA LA' m hm lam hlam r hI hI' hchi M _ _ e rho hrho
  have hc : ∀ g : ↥(GK K), ∃ w : ℤ_[l],
      ((Formalism.MainNotions.N.cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap ℚ_[l] LL (w : ℚ_[l]) ∧
      (PadicInt.toZModPow r w : ZMod (l ^ r)) =
        ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) :
          ZMod (l ^ r)) := by
    intro g
    obtain ⟨w, hw1, hw2⟩ := hchi g
    exact ⟨w, by rw [← hw1]; rfl, hw2⟩
  exact ⟨psiQ hm.2 hlam e, psiQ_injective hm.2 hlam e,
    psiQ_equivariant hm.2 hlam e (fun h => ((Formalism.MainNotions.N.cycLL (P.PD K) LL h : LLˣ) : LL)) hm.1.1 hc
      hI hI' rho hrho⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TracePairingInjectiveEquivariantLevelMapStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tracePairing_injective_equivariant_levelMap : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (lam : LL →ₗ[ℚ_[l]] ℚ_[l]), (∀ a : LL, (∀ b : O, ∃ u : ℤ_[l], lam (a * algebraMap O LL b) = (u : ℚ_[l])) ↔ ∃ b : O, algebraMap O LL b = a) → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), (∀ g : ↥(GK K), ∃ u : ℤ_[l], (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = (u : ℚ_[l]) ∧ (PadicInt.toZModPow r u : ZMod (l ^ r)) = ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r))) → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] (e : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) ≃+ M) (rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K.1) M), (∀ g x, rho g (e x) = e (actQ LA _ hI ((IntermediateField.fixingSubgroupEquiv K.1).symm g) x)) → ∃ Ψ : (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) →+ ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M, Function.Injective Ψ ∧ ∀ g y, Ψ (actQ LA' _ hI' ((IntermediateField.fixingSubgroupEquiv K.1).symm g) y) = ReciprocityTheory.Gal.twDual (Formalism.GaloisCohomology.cycK l K.1 r) rho g (Ψ y) := by
  first | exact @GlobalTheory.tracePairing_levelMap | exact GlobalTheory.tracePairing_levelMap | (intros; apply GlobalTheory.tracePairing_levelMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodCyclotomicCharReducesModPrimePow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodCyclotomicCharReducesModPrimePow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CycLevel

theorem toZModPow_eq_of_norm_sub_le {l : ℕ} [Fact l.Prime] (u : ℤ_[l]) (a : ℕ) (r : ℕ)
    (h : ‖(u : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(r : ℤ))) :
    (PadicInt.toZModPow r u : ZMod (l ^ r)) = (a : ZMod (l ^ r)) := by
  have h1 : ‖u - (a : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by
    rw [PadicInt.norm_def]; push_cast; exact h
  have h2 := (PadicInt.norm_le_pow_iff_mem_span_pow (u - (a : ℤ_[l])) r).mp h1
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h2
  exact h2

theorem chi_reduces (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (r : ℕ) (g : ↥(GK K)) :
    ∃ u : ℤ_[l], (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = (u : ℚ_[l]) ∧
      (PadicInt.toZModPow r u : ZMod (l ^ r)) =
        ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) := by
  obtain ⟨ζ, hζ1, hζ⟩ := GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr K.1
    (IntermediateField.fixingSubgroupEquiv K.1 g) r
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc (g : GQ l) r ζ hζ1
  have key := hζ a hga
  have hr : (l : ℝ) ^ (-(r : ℤ)) ≤ 1 := by
    apply zpow_le_one_of_nonpos₀
    · exact_mod_cast (Fact.out : l.Prime).one_lt.le
    · simp
  have hnorm : ‖((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
    have e : ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) =
        (((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) + (a : ℚ_[l]) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha.trans hr) ?_)
    have := PadicInt.norm_le_one (a : ℤ_[l])
    rwa [PadicInt.norm_def, PadicInt.coe_natCast] at this
  let u : ℤ_[l] := ⟨_, hnorm⟩
  have hu : (u : ℚ_[l]) = ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) := rfl
  have ha' : ‖(u : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by rw [hu]; exact ha
  refine ⟨u, (P.PD_χ K g).trans hu.symm, ?_⟩
  rw [toZModPow_eq_of_norm_sub_le u a r ha', key]
  rfl

end GlobalTheory.CycLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodCyclotomicCharReducesModPrimePowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodCyclotomicChar_reduces_mod_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (r : ℕ) (g : ↥(GK K)), ∃ u : ℤ_[l], (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = (u : ℚ_[l]) ∧ (PadicInt.toZModPow r u : ZMod (l ^ r)) = ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) := by
  first | exact @GlobalTheory.CycLevel.chi_reduces | exact GlobalTheory.CycLevel.chi_reduces | (intros; apply GlobalTheory.CycLevel.chi_reduces <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLatticeQuotPrimePow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLatticeQuotPrimePow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.LatticeCard

theorem mem_span_singleton_smul_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : R) (x : M) : x ∈ (Ideal.span {b} • ⊤ : Submodule R M) ↔ ∃ y : M, b • y = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

theorem card_quot_pow_succ {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (ha : IsSMulRegular M a) (k : ℕ) :
    Nat.card (M ⧸ (Ideal.span {a ^ (k + 1)} • ⊤ : Submodule R M)) =
      Nat.card (M ⧸ (Ideal.span {a} • ⊤ : Submodule R M)) *
      Nat.card (M ⧸ (Ideal.span {a ^ k} • ⊤ : Submodule R M)) := by
  set S : Submodule R M := Ideal.span {a ^ (k + 1)} • ⊤ with hS
  set T : Submodule R M := Ideal.span {a ^ k} • ⊤ with hT
  have hST : S ≤ T := by
    intro x hx
    rw [hS, mem_span_singleton_smul_top] at hx
    rw [hT, mem_span_singleton_smul_top]
    obtain ⟨y, rfl⟩ := hx
    exact ⟨a • y, by rw [smul_smul, ← pow_succ]⟩
  have h1 := Submodule.card_eq_card_quotient_mul_card (T.map S.mkQ)
  rw [Nat.card_congr (Submodule.quotientQuotientEquivQuotient S T hST).toEquiv] at h1
  rw [h1]
  congr 1
  have hmem : ∀ x : M, S.mkQ (a ^ k • x) ∈ T.map S.mkQ := fun x =>
    ⟨a ^ k • x, SetLike.mem_coe.2 ((mem_span_singleton_smul_top _ _).2 ⟨x, rfl⟩), rfl⟩
  let φ : M →ₗ[R] ↥(T.map S.mkQ) :=
    LinearMap.codRestrict (T.map S.mkQ) (S.mkQ ∘ₗ (a ^ k • LinearMap.id)) (fun x => hmem x)
  have hsurj : Function.Surjective φ := by
    rintro ⟨z, w, hw, rfl⟩
    rw [SetLike.mem_coe, mem_span_singleton_smul_top] at hw
    obtain ⟨x, rfl⟩ := hw
    exact ⟨x, rfl⟩
  have hker : LinearMap.ker φ = (Ideal.span {a} • ⊤ : Submodule R M) := by
    ext x
    rw [LinearMap.mem_ker, mem_span_singleton_smul_top]
    have hφ : φ x = 0 ↔ a ^ k • x ∈ S := by
      rw [← Subtype.coe_inj]
      change S.mkQ (a ^ k • x) = 0 ↔ _
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [hφ, hS, mem_span_singleton_smul_top]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, (ha.pow k) ?_⟩
      change a ^ k • (a • y) = a ^ k • x
      rw [smul_smul, ← pow_succ]; exact hy
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [smul_smul, ← pow_succ]⟩
  rw [← Nat.card_congr (LinearMap.quotKerEquivOfSurjective φ hsurj).toEquiv,
    Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv]

theorem card_quot_pow {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (ha : IsSMulRegular M a) (r : ℕ) :
    Nat.card (M ⧸ (Ideal.span {a ^ r} • ⊤ : Submodule R M)) =
      Nat.card (M ⧸ (Ideal.span {a} • ⊤ : Submodule R M)) ^ r := by
  induction r with
  | zero =>
    rw [pow_zero, pow_zero, Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨0⟩⟩
    induction x using Submodule.Quotient.induction_on with | _ x => ?_
    induction y using Submodule.Quotient.induction_on with | _ y => ?_
    rw [Submodule.Quotient.eq, mem_span_singleton_smul_top]
    exact ⟨x - y, one_smul _ _⟩
  | succ k ih => rw [card_quot_pow_succ a ha k, ih, pow_succ, mul_comm]

theorem card_quot_equiv {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (b : R) :
    Nat.card (M ⧸ (Ideal.span {b} • ⊤ : Submodule R M)) =
      Nat.card (N ⧸ (Ideal.span {b} • ⊤ : Submodule R N)) := by
  refine Nat.card_congr (Submodule.Quotient.equiv _ _ e ?_).toEquiv
  ext y
  rw [Submodule.mem_map_equiv, mem_span_singleton_smul_top, mem_span_singleton_smul_top]
  constructor
  · rintro ⟨x, hx⟩; exact ⟨e x, by rw [← map_smul, hx, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨x, rfl⟩; exact ⟨e.symm x, by rw [map_smul]⟩

theorem card_quot_fun {ι O : Type*} [Fintype ι] [CommRing O] (b : O) :
    Nat.card ((ι → O) ⧸ (Ideal.span {b} • ⊤ : Submodule O (ι → O))) =
      Nat.card (O ⧸ Ideal.span {b}) ^ Fintype.card ι := by
  let π : (ι → O) →ₗ[O] (ι → O ⧸ Ideal.span {b}) :=
    LinearMap.pi (fun i => (Ideal.Quotient.mkₐ O (Ideal.span {b})).toLinearMap ∘ₗ LinearMap.proj i)
  have hπ : ∀ x i, π x i = Ideal.Quotient.mk _ (x i) := fun x i => rfl
  have hsurj : Function.Surjective π := by
    intro y
    refine ⟨fun i => (y i).out, funext fun i => ?_⟩
    rw [hπ, Ideal.Quotient.mk_out]
  have hker : LinearMap.ker π = (Ideal.span {b} • ⊤ : Submodule O (ι → O)) := by
    ext x
    rw [LinearMap.mem_ker, mem_span_singleton_smul_top]
    constructor
    · intro hx
      have : ∀ i, ∃ c, b * c = x i := fun i => by
        have h := congrFun hx i
        rw [hπ, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
        obtain ⟨c, hc⟩ := h
        exact ⟨c, hc.symm⟩
      choose c hc using this
      exact ⟨c, funext fun i => by simp [hc]⟩
    · rintro ⟨y, rfl⟩
      funext i
      rw [hπ, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact ⟨y i, by simp⟩
  rw [← Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv,
    Nat.card_congr (LinearMap.quotKerEquivOfSurjective π hsurj).toEquiv, Nat.card_fun,
    Nat.card_eq_fintype_card (α := ι)]

end GlobalTheory.LatticeCard

namespace GlobalTheory.LatticeCard

theorem card_lattice_quot_pow : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep G ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ), Nat.card (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) = Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL A.V) := by
  intro l _ G _ _ LL _ _ _ O _ _ hG A LA r
  obtain ⟨⟨hD, -, hFr⟩, -, -, -, -⟩ := hG
  haveI := hD
  haveI := hFr
  haveI : Module.Free O LA.T := LA.free
  haveI : Module.Finite O LA.T := Module.Finite.iff_fg.2 LA.fg
  let b := Module.Free.chooseBasis O LA.T
  have hli : LinearIndependent LL (fun i => (b i : A.V)) := by
    rw [← LinearIndependent.iff_fractionRing O LL]
    exact b.linearIndependent.map' LA.T.subtype (Submodule.ker_subtype _)
  have hT : (LA.T : Set A.V) ⊆ Submodule.span LL (Set.range fun i => (b i : A.V)) := by
    intro x hx
    have hx' : (⟨x, hx⟩ : LA.T) ∈ Submodule.span O (Set.range b) := by
      rw [b.span_eq]; trivial
    have h2 := Submodule.apply_mem_span_image_of_mem_span LA.T.subtype hx'
    rw [← Set.range_comp] at h2
    exact Submodule.span_le_restrictScalars O LL _ h2
  have hsp : ⊤ ≤ Submodule.span LL (Set.range fun i => (b i : A.V)) :=
    calc ⊤ = Submodule.span LL (LA.T : Set A.V) := LA.span.symm
      _ ≤ _ := Submodule.span_le.2 hT
  have hn : finrank LL A.V = Fintype.card (Module.Free.ChooseBasisIndex O LA.T) :=
    finrank_eq_card_basis (Basis.mk hli hsp)
  have hl : ((l : ℕ) : LL) ≠ 0 := by
    have h := (algebraMap ℚ_[l] LL).injective.ne
      (show ((l : ℕ) : ℚ_[l]) ≠ 0 from Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
    simpa using h
  have hreg : IsSMulRegular LA.T ((l : ℕ) : O) := by
    intro x y hxy
    have h1 : ((l : ℕ) : O) • (x : A.V) = ((l : ℕ) : O) • (y : A.V) := by
      have := congrArg (fun z : LA.T => (z : A.V)) hxy
      simpa only [Submodule.coe_smul] using this
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul LL,
      ← Nat.cast_smul_eq_nsmul LL l (y : A.V)] at h1
    exact Subtype.ext (smul_right_injective A.V hl h1)
  rw [card_quot_pow _ hreg, card_quot_equiv b.equivFun, card_quot_fun, hn, ← pow_mul, mul_comm]

end GlobalTheory.LatticeCard
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLatticeQuotPrimePowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_lattice_quot_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep G ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ), Nat.card (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) = Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL A.V) := by
  first | exact @GlobalTheory.LatticeCard.card_lattice_quot_pow | exact GlobalTheory.LatticeCard.card_lattice_quot_pow | (intros; apply GlobalTheory.LatticeCard.card_lattice_quot_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1LatticeIndexGrowth
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.EulerLevel

theorem card_H2_eq (N : ℕ) [NeZero N] (G : Type) [Group G] [TopologicalSpace G]
    (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : G →* (ZMod N)ˣ) (rho : Representation (ZMod N) G M)
    (e : ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod N] ZMod N)
    (hb : Function.Bijective (ReciprocityTheory.Gal.cup20 χ rho (MonoidHom.id _))) :
    Nat.card (ReciprocityTheory.Gal.H2 rho) = Nat.card (ReciprocityTheory.Gal.H0 (ReciprocityTheory.Gal.twDual χ rho)) := by
  have hT := GlobalTheory.CocycleCount.card_linear_le N M
  have hTf : Finite (ReciprocityTheory.Gal.TDual (ZMod N) M) := hT.1
  let A : Type := ReciprocityTheory.Gal.H0 ((ReciprocityTheory.Gal.twDual χ rho).comp (MonoidHom.id G))
  let E : ReciprocityTheory.Gal.H2 rho ≃ (A →ₗ[ZMod N] ZMod N) :=
    (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight e).toEquiv
  have hA : Finite A := Subtype.finite
  rw [Nat.card_congr E]
  exact GlobalTheory.ZModDual.card_dual_eq N A


set_option maxHeartbeats 1600000 in
theorem core_pos (hT : Formalism.GaloisCohomology.LocalTateDualityK) (hE : Formalism.GaloisCohomology.LocalEulerCharK) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (hG : GoodO (Qp := ℚ_[l]) LL O) (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (hm : IsDualLat1 (P.PD K) LA LA' m) (r : ℕ) (hr : 0 < r) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T))
    (M : Type) [AddCommGroup M] (tM : TopologicalSpace M) (dM : @DiscreteTopology M tM) (e : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) ≃+ M) :
    Nat.card (QuotientCohomology LA _ hI) = Nat.card {x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) // ∀ g, actQ LA _ hI g x = x} * Nat.card {x : (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) // ∀ g, actQ LA' _ hI' g x = x} * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * (finrank ℚ_[l] ↥K.1 * finrank LL A.V)) := by
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hp : l.Prime := Fact.out
  obtain ⟨-, -, hfinO, -⟩ := GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG
  have hcO : Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ≠ 0 := by
    have := hfinO 1
    rw [pow_one] at this
    exact Nat.card_pos.ne'
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcM : Nat.card M = Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL A.V) := by
    rw [← Nat.card_congr e.toEquiv]
    exact GlobalTheory.T.card_lattice_quot_prime_pow l _ LL O hG A LA r
  have hcM' : Nat.card (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) =
      Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL A.V) := by
    rw [GlobalTheory.T.card_lattice_quot_prime_pow l _ LL O hG A' LA' r, ← hm.1.2.2.2]
  haveI : Finite M := Nat.finite_of_card_ne_zero (by rw [hcM]; exact pow_ne_zero _ hcO)
  have htor : ∀ x : M, l ^ r • x = 0 := by
    intro x
    rw [← e.apply_symm_apply x, ← map_nsmul]
    generalize e.symm x = y
    induction y using Submodule.Quotient.induction_on with
    | H t =>
      rw [← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _).2, map_zero]
      rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  haveI instM : Module (ZMod (l ^ r)) M := AddCommGroup.zmodModule htor
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  have hφ1 : φ.symm 1 = 1 := map_one _
  have hφm : ∀ g h, φ.symm (g * h) = φ.symm g * φ.symm h := map_mul _
  have hact1 : ∀ x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), actQ LA _ hI 1 x = x := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H t =>
      exact congrArg Submodule.Quotient.mk (Subtype.ext (by
        show A.ρ 1 (t : A.V) = t
        rw [map_one]
        rfl))
  have hactm : ∀ (g h : ↥(GK K)) (x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T))),
      actQ LA _ hI (g * h) x = actQ LA _ hI g (actQ LA _ hI h x) := by
    intro g h x
    induction x using Submodule.Quotient.induction_on with
    | H t =>
      exact congrArg Submodule.Quotient.mk (Subtype.ext (by
        show A.ρ (g * h) (t : A.V) = A.ρ g (A.ρ h t)
        rw [map_mul]
        rfl))
  have hex : ∃ rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K.1) M,
      ∀ (g : Formalism.GaloisCohomology.GK l K.1) (x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T))), rho g (e x) = e (actQ LA _ hI (φ.symm g) x) :=
    ⟨GlobalTheory.CocycleCount.repOfAction _
      (fun g => e.toAddMonoidHom.comp ((actQ LA _ hI (φ.symm g)).toAddMonoidHom.comp e.symm.toAddMonoidHom))
      (fun x => by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
          AddEquiv.coe_toAddMonoidHom, hφ1, hact1, AddEquiv.apply_symm_apply])
      (fun g h x => by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
          AddEquiv.coe_toAddMonoidHom, hφm, hactm, AddEquiv.symm_apply_apply]),
      fun g x => congrArg (fun y => e (actQ LA _ hI (φ.symm g) y)) (e.symm_apply_apply x)⟩
  obtain ⟨rho, hcomp⟩ := hex
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun x => ?_
    have hx : (fun g => rho g x) = fun g => e (actQ LA _ hI (φ.symm g) (e.symm x)) := by
      funext g
      rw [← hcomp, e.apply_symm_apply]
    rw [hx]
    exact ((GlobalTheory.T.lattice_modPow_action_isLocallyConstant l ↥(GK K) LL O hG A LA r hI (e.symm x)).comp e).continuous.comp hφ.2
  have hT1 := hT l K.1 hK r M rho hr hrho
  obtain ⟨⟨eH⟩, -, -, -, hb⟩ := hT1
  have hEu := hE l K.1 hK r M rho hr hrho
  have hTr := GlobalTheory.T.card_H1_H0_transport_lattice l K LL O A LA _ hI (l ^ r) M e rho hcomp
  obtain ⟨h1Q, h0Q⟩ := hTr
  have hTDfin : Finite (ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M) :=
    (GlobalTheory.CocycleCount.card_linear_le (l ^ r) M).1
  have hH2 := card_H2_eq (l ^ r) _ M _ rho eH hb
  have hD := GlobalTheory.T.exists_trace_form_integral_iff_goodCoeff l LL O hG
  obtain ⟨lam, hlam⟩ := hD
  have hMp := GlobalTheory.T.tracePairing_injective_equivariant_levelMap l P K LL O A A' LA LA' m hm lam hlam r hI hI' (GlobalTheory.T.periodCyclotomicChar_reduces_mod_prime_pow l P K r) M e rho hcomp
  obtain ⟨Ψ, hΨi, hΨe⟩ := hMp
  have hcD : Nat.card (ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M) = Nat.card M :=
    GlobalTheory.ZModDual.card_dual_eq (l ^ r) M
  have hΨb : Function.Bijective Ψ :=
    hΨi.bijective_of_nat_card_le (by rw [hcD, hcM, hcM'])
  have hfix' : Nat.card {y : (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) // ∀ g, actQ LA' _ hI' g y = y} =
      Nat.card (ReciprocityTheory.Gal.H0 (ReciprocityTheory.Gal.twDual (Formalism.GaloisCohomology.cycK l K.1 r) rho)) := by
    refine Nat.card_congr ((Equiv.ofBijective _ hΨb).subtypeEquiv fun y => ?_)
    rw [Equiv.ofBijective_apply, ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere]
    constructor
    · intro hy g
      exact (hΨe g y).symm.trans (congrArg Ψ (hy _))
    · intro hy g
      have h := hΨe (φ g) y
      have h2 : (IntermediateField.fixingSubgroupEquiv K.1).symm (φ g) = g := φ.symm_apply_apply g
      rw [h2, hy (φ g)] at h
      exact hΨb.1 h
  rw [h1Q, hEu, ← h0Q, hH2, ← hfix', hcM, ← pow_mul]
  rw [show r * finrank LL A.V * finrank ℚ_[l] ↥K.1 = r * (finrank ℚ_[l] ↥K.1 * finrank LL A.V) by ring]

theorem card_H1Q_eq : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), Nat.card (QuotientCohomology LA _ hI) = Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} * Nat.card {x : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * (finrank ℚ_[l] ↥K.1 * finrank LL A.V)) := by
  intro hT hE l _ P K LL _ _ _ O _ _ hG A A' LA LA' m hm r hI hI'
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hp : l.Prime := Fact.out
  obtain ⟨-, -, hfinO, -⟩ := GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG
  have hcO : Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ≠ 0 := by
    have := hfinO 1
    rw [pow_one] at this
    exact Nat.card_pos.ne'
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hs : ∀ (X : Type) [AddCommGroup X] [Module O X],
        Subsingleton (X ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O X)) := by
      intro X _ _
      rw [Submodule.Quotient.subsingleton_iff, pow_zero, Ideal.span_singleton_one, Submodule.top_smul]
    haveI := hs ↥LA.T
    haveI := hs ↥LA'.T
    have e1 : Nat.card (QuotientCohomology LA _ hI) = 1 := by
      haveI : Subsingleton (QuotientCohomology LA _ hI) := (Submodule.Quotient.mk_surjective _).subsingleton
      exact Nat.card_unique
    have e2 : Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} = 1 := by
      haveI : Unique {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} :=
        { default := ⟨0, fun g => map_zero _⟩, uniq := fun _ => Subsingleton.elim _ _ }
      exact Nat.card_unique
    have e3 : Nat.card {x : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} = 1 := by
      haveI : Unique {x : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} :=
        { default := ⟨0, fun g => map_zero _⟩, uniq := fun _ => Subsingleton.elim _ _ }
      exact Nat.card_unique
    simp only [e1, e2, e3]
    simp
  · exact core_pos hT hE l P K LL O hG A A' LA LA' m hm r hr hI hI' _ ⊥ (@DiscreteTopology.mk _ ⊥ rfl) (AddEquiv.refl _)

end GlobalTheory.EulerLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1LatticeIndexGrowthStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H1_lattice_index_growth_of_tateDuality_eulerChar : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), Nat.card (QuotientCohomology LA _ hI) = Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} * Nat.card {x : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * (finrank ℚ_[l] ↥K.1 * finrank LL A.V)) := by
  first | exact @GlobalTheory.EulerLevel.card_H1Q_eq | exact GlobalTheory.EulerLevel.card_H1Q_eq | (intros; apply GlobalTheory.EulerLevel.card_H1Q_eq <;> assumption)
end
