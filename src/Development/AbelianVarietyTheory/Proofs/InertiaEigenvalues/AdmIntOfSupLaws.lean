module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrrHarishChandraInductionThetaInvDet

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmIntOfSupLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanInfOfSpanTop
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.IntRestBall

open GlobalTheory.TwAll

theorem span_inf_of_span_top {O V : Type} [CommRing O] [IsDomain O] [AddCommGroup V] [Module O V]
    [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] (B : Submodule O V)
    (hB : Submodule.span (FractionRing O) (B : Set V) = ⊤) (W : Submodule (FractionRing O) V)
    (M : Submodule O V) (hM : ∀ f, f ∈ M ↔ f ∈ B ∧ f ∈ W) :
    Submodule.span (FractionRing O) (M : Set V) = W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    exact fun f hf => ((hM f).1 hf).2
  · intro f hf
    have h1 : f ∈ Submodule.span (FractionRing O) (B : Set V) := hB ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) (FractionRing O) (B : Set V) f h1
    rw [Submodule.span_eq] at ht
    have e : t • f = (algebraMap O (FractionRing O) t) • f := by
      rw [algebraMap_smul]; rfl
    have hne : algebraMap O (FractionRing O) t ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors t.2
    have h2 : t • f ∈ M := (hM _).2 ⟨ht, e ▸ W.smul_mem _ hf⟩
    have h3 := (Submodule.span (FractionRing O) (M : Set V)).smul_mem
      (algebraMap O (FractionRing O) t)⁻¹ (Submodule.subset_span h2)
    rwa [e, smul_smul, inv_mul_cancel₀ hne, one_smul] at h3

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} (T : NTh D.R D.host D.what₂ D.LL0 N X Y)

end GlobalTheory.IntRestBall
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmIntOfSupLaws
noncomputable section

namespace GlobalTheory.IntSup

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
open scoped TensorProduct

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem mall_map_le (i : X.Tw) (j : ℕ) (b : Bool) (φ : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (hφ : ∀ f ∈ Y.Bsup i j b, φ f ∈ Y.Bsup i j b)
    (hc : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ φ = φ ∘ₗ (Y.actG i j b g).toLinearMap) :
    (IntegralHeckeForms.Mall Y i j b).map (φ.restrictScalars (X.O i)) ≤ IntegralHeckeForms.Mall Y i j b := by
  rintro _ ⟨f, ⟨hf, hf0⟩, rfl⟩
  refine ⟨hφ f hf, ?_⟩
  change φ f ∈ IntegralHeckeForms.Fm0 Y i j b
  replace hf0 : f ∈ IntegralHeckeForms.Fm0 Y i j b := hf0
  simp only [IntegralHeckeForms.Fm0, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hf0 ⊢
  intro u
  have h := LinearMap.congr_fun (hc u) f
  simp only [LinearMap.comp_apply] at h
  rw [h, hf0 u, map_smul]

theorem admInt_of_sup : ∀ (D : D7) (E : IntegralHeckeForms.XD D), SupG D → SupFull D → SupHk D → UnivSup D E → TypeKept E → CommG D →
    IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E := by
  intro D E hG hF hH hU hT hC i hi j hj b
  obtain ⟨hfg, hsp⟩ := hF i hi j hj b
  refine ⟨fun g => ?_, ?_,
    GlobalTheory.IntRestBall.span_inf_of_span_top _ hsp _ _ (fun _ => Iff.rfl),
    fun k P hk => mall_map_le D.nexp i j b _ (hH i hi j hj b k P hk) (fun g => hC i hi b j hj g k P hk),
    ?_, hT i hi j hj b⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact hG i hi j hj b g f hf
  · exact hfg.of_le (fun f hf => hf.1)
  · intro a ha
    obtain ⟨c, hc⟩ := hU i hi j hj b a ha
    refine ⟨c, fun Q M h1 h2 h3 h4 => ?_⟩
    obtain ⟨Xi, hXi, hδ⟩ := hc Q M h1 h2 h3 h4
    rw [hXi, Finsupp.sum, Finset.smul_sum]
    refine Submodule.sum_mem _ fun δ _ => ?_
    have hm : ((D.ntw.l i : D.ntw.O i) ^ c) • Xi δ ∈ IntegralHeckeForms.Mall D.nexp i j b :=
      ⟨(hδ δ).2, ((IntegralHeckeForms.Fm0 D.nexp i j b).restrictScalars (D.ntw.O i)).smul_mem _ (hδ δ).1⟩
    exact ⟨(⟨_, hm⟩ : IntegralHeckeForms.Mall D.nexp i j b) ⊗ₜ AddMonoidAlgebra.single δ (1 : D.ntw.O i), by
      simp [TensorProduct.smul_tmul']⟩

end GlobalTheory.IntSup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmIntOfSupLawsStatement
open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admInt_of_sup_laws : ∀ (D : D7) (E : IntegralHeckeForms.XD D), SupG D → SupFull D → SupHk D → UnivSup D E → TypeKept E → CommG D → IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E := by
  first | exact @GlobalTheory.IntSup.admInt_of_sup | exact GlobalTheory.IntSup.admInt_of_sup | (intros; apply GlobalTheory.IntSup.admInt_of_sup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNormalSubgroupTwoCocycles
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNormalSubgroupTwoCocycles
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CocycleKernel

section General

variable {R : Type} [CommRing R] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {rho : Representation R Γ M} (x : Z1 rho) {L : Subgroup Γ}

theorem cocycle_one : x.1 1 = 0 := by
  have h := x.2.2 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  exact left_eq_add.1 h

theorem cocycle_conj (hL : ∀ g ∈ L, ∀ m, rho g m = m) (k : Γ) {g : Γ} (hg : g ∈ L) :
    x.1 (k * g * k⁻¹) = rho k (x.1 g) := by
  have h := x.2.2 k k⁻¹
  rw [mul_inv_cancel, cocycle_one] at h
  rw [x.2.2, x.2.2, map_mul, Module.End.mul_apply, hL g hg, add_right_comm, ← h, zero_add]

def zeros (L : Subgroup Γ) : Subgroup Γ where
  carrier := {g | g ∈ L ∧ x.1 g = 0}
  one_mem' := ⟨L.one_mem, cocycle_one x⟩
  mul_mem' := fun {a b} ha hb => ⟨L.mul_mem ha.1 hb.1, by rw [x.2.2, ha.2, hb.2, map_zero, add_zero]⟩
  inv_mem' := fun {a} ha => ⟨L.inv_mem ha.1, by
    have h := x.2.2 a⁻¹ a
    rwa [inv_mul_cancel, cocycle_one, ha.2, map_zero, add_zero, eq_comm] at h⟩

theorem zeros_normal (hN : L.Normal) (hL : ∀ g ∈ L, ∀ m, rho g m = m) : (zeros x L).Normal :=
  ⟨fun g hg k => ⟨hN.conj_mem g hg.1 k, by rw [cocycle_conj x hL k hg.1, hg.2, map_zero]⟩⟩

theorem isOpen_zeros [DiscreteTopology M] (hO : IsOpen (L : Set Γ)) : IsOpen (zeros x L : Set Γ) :=
  hO.inter ((isOpen_discrete ({0} : Set M)).preimage x.2.1)

theorem cocycle_eq (hL : ∀ g ∈ L, ∀ m, rho g m = m) {h σ g : Γ} (hh : h ∈ L)
    (hu : g * σ * g⁻¹ * h⁻¹ ∈ zeros x L) : x.1 σ = rho g⁻¹ (x.1 h) := by
  have e : σ = g⁻¹ * (g * σ * g⁻¹ * h⁻¹ * h) * g⁻¹⁻¹ := by group
  rw [e, cocycle_conj x hL _ (L.mul_mem hu.1 hh), x.2.2, hu.2, hL _ hu.1, zero_add]

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (i : X.Tw) (s : X.Sig i)

theorem dot_repOn {A : Type} [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ)
    {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (hρ : IsDual i s ρ) (k : GE N) (a b : Fin D.R.r → A) :
    repOn (Tgl i s) κ A k a ⬝ᵥ repOn ρ κ⁻¹ A k b =
      algebraMap (X.O0 i) A ((eps0 X i k : (X.O0 i)ˣ) : X.O0 i) * a ⬝ᵥ b := by
  have e : (Tmat i s k).transpose * Tdual i s k = ((eps0 X i k : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix _ _ (X.O0 i)) := by
    rw [Tdual, Matrix.mul_smul, ← Matrix.transpose_mul, ← Tgl_coe, ← Matrix.coe_units_inv, Units.inv_mul,
      Matrix.transpose_one]
  have e2 : ((Tmat i s k).map (algebraMap (X.O0 i) A)).transpose * (Tdual i s k).map (algebraMap (X.O0 i) A) =
      algebraMap (X.O0 i) A ((eps0 X i k : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix _ _ A) := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, e]
    ext a b
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  change ((κ k : A) • ((Tgl i s k : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) A)).mulVec a) ⬝ᵥ
    ((((κ k)⁻¹ : Aˣ) : A) • ((ρ k : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) A)).mulVec b) = _
  rw [hρ k, Tgl_coe, smul_dotProduct, dotProduct_smul, smul_smul, Units.mul_inv, one_smul, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, e2, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    smul_eq_mul]

theorem exists_open_normal : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → Small2 i s M L z → ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → IsDual i s ρ → (∀ g ∈ L, κ g = 1) → ∀ (x : Z1 (repOn (Tgl i s) κ A)) (y : Z1 (repOn ρ κ⁻¹ A)), ∀ h ∈ L, bform (X := X) x.1 y.1 h ≠ 0 → ∃ U : Subgroup (GE N), IsOpen (U : Set (GE N)) ∧ U.Normal ∧ U ≤ L ∧ (∀ g ∈ L, x.1 g = 0 → x.1 (cConj X g) = 0 → y.1 g = 0 → y.1 (cConj X g) = 0 → g ∈ U) ∧ ∀ σ g : GE N, g * σ * g⁻¹ * h⁻¹ ∈ U → bform (X := X) x.1 y.1 σ ≠ 0 := by
  intro D N X i s hl M L z hM hS A _ _ _ _ κ ρ hK hρ hκ x y h hh hb
  have h1 : ∀ g ∈ L, ∀ m, repOn (Tgl i s) κ A g m = m := fun g hg m => by
    rw [(GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl M L z hM hS A κ ρ hK hρ A g hg).1, hκ g hg, Units.val_one, one_smul]
  have h2 : ∀ g ∈ L, ∀ m, repOn ρ κ⁻¹ A g m = m := fun g hg m => by
    rw [(GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl M L z hM hS A κ⁻¹ ρ hK hρ A g hg).2.1, MonoidHom.inv_apply, hκ g hg, inv_one,
      Units.val_one, one_smul]
  obtain ⟨⟨hO, hN, hc, -⟩, -⟩ := hS
  have hc' : ∀ g ∈ L, cConj X g ∈ L := fun g hg => (hc g _ (cConj_apply X g)).1 hg
  haveI := zeros_normal x hN h1
  haveI := zeros_normal y hN h2
  refine ⟨(zeros x L ⊓ (zeros x L).comap (cConj X)) ⊓ (zeros y L ⊓ (zeros y L).comap (cConj X)),
    ((isOpen_zeros x hO).inter (isOpen_comap_cConj X (isOpen_zeros x hO))).inter
      ((isOpen_zeros y hO).inter (isOpen_comap_cConj X (isOpen_zeros y hO))), inferInstance,
    fun g hg => hg.1.1.1, fun g hg a b c d => ⟨⟨⟨hg, a⟩, hc' g hg, b⟩, ⟨hg, c⟩, hc' g hg, d⟩, ?_⟩
  rintro σ g ⟨⟨a, b⟩, c, d⟩ h0
  have e : cConj X (g * σ * g⁻¹ * h⁻¹) = cConj X g * cConj X σ * (cConj X g)⁻¹ * (cConj X h)⁻¹ := by
    simp only [map_mul, map_inv]
  have b' : cConj X (g * σ * g⁻¹ * h⁻¹) ∈ zeros x L := b
  have d' : cConj X (g * σ * g⁻¹ * h⁻¹) ∈ zeros y L := d
  rw [e] at b' d'
  rw [bform, cocycle_eq x h1 hh a, cocycle_eq y h2 hh c, cocycle_eq x h1 (hc' h hh) b', cocycle_eq y h2 (hc' h hh) d',
    dot_repOn i s κ hρ, dot_repOn i s κ hρ, ← map_inv (cConj X), GlobalTheory.ResConjTriv.auxiliaryCharacter_complexConj_invariant, ← mul_sub] at h0
  exact hb (((Units.isUnit _).map (algebraMap (X.O0 i) A)).mul_right_eq_zero.1 h0)

end GlobalTheory.CocycleKernel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNormalSubgroupTwoCocyclesStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_normal_subgroup_two_cocycles : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → Small2 i s M L z → ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → IsDual i s ρ → (∀ g ∈ L, κ g = 1) → ∀ (x : Z1 (repOn (Tgl i s) κ A)) (y : Z1 (repOn ρ κ⁻¹ A)), ∀ h ∈ L, bform (X := X) x.1 y.1 h ≠ 0 → ∃ U : Subgroup (GE N), IsOpen (U : Set (GE N)) ∧ U.Normal ∧ U ≤ L ∧ (∀ g ∈ L, x.1 g = 0 → x.1 (cConj X g) = 0 → y.1 g = 0 → y.1 (cConj X g) = 0 → g ∈ U) ∧ ∀ σ g : GE N, g * σ * g⁻¹ * h⁻¹ ∈ U → bform (X := X) x.1 y.1 σ ≠ 0 := by
  first | exact @GlobalTheory.CocycleKernel.exists_open_normal | exact GlobalTheory.CocycleKernel.exists_open_normal | (intros; apply GlobalTheory.CocycleKernel.exists_open_normal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniversalSelmerCocycleBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniversalSelmerCocycleBaseChange
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.UnivCocycle

theorem matAct_map {Λ B Y : Type} [CommRing Λ] [CommRing B] [AddCommGroup Y] [Module Λ Y] [Module B Y] (φ : Λ → B)
    (h : ∀ (c : Λ) (y : Y), c • y = φ c • y) {a : ℕ} (Φ : Matrix (Fin a) (Fin a) Λ) (x : Fin a → Y) :
    matAct Φ x = matAct (Φ.map φ) x := by
  funext c
  simp [matAct, h]

def ev {B Y : Type} [CommRing B] [AddCommGroup Y] [Module B Y] {a : ℕ} (Ψ : Matrix (Fin a) (Fin a) B) (x : Fin a → Y)
    (hx : matAct Ψ x = 0) : ((Fin a → B) ⧸ what₂ Ψ) →ₗ[B] Y :=
  (what₂ Ψ).liftQ (Fintype.linearCombination B x) (by
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    have := congrFun hx c
    simpa [matAct, Fintype.linearCombination_apply] using this)

theorem ev_mk {B Y : Type} [CommRing B] [AddCommGroup Y] [Module B Y] {a : ℕ} (Ψ : Matrix (Fin a) (Fin a) B) (x : Fin a → Y)
    (hx : matAct Ψ x = 0) (v : Fin a → B) : ev Ψ x hx (Submodule.Quotient.mk v) = ∑ j, v j • x j := by
  simp [ev, Fintype.linearCombination_apply]

theorem univ_ker {B : Type} [CommRing B] {a : ℕ} (Ψ : Matrix (Fin a) (Fin a) B) :
    matAct Ψ (fun j => (Submodule.Quotient.mk (Pi.single j 1) : (Fin a → B) ⧸ what₂ Ψ)) = 0 := by
  funext c
  have h : (∑ j, Ψ c j • (Pi.single j 1 : Fin a → B)) = Ψ c := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have h2 : (Submodule.Quotient.mk (Ψ c) : (Fin a → B) ⧸ what₂ Ψ) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span ⟨c, rfl⟩)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h, ← Submodule.mkQ_apply, map_sum] at h2
  simpa [matAct] using h2

theorem tors {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (i : X.Tw)
    {B : Type} [CommRing B] [Algebra (X.O0 i) B] (hK : Kills i B) (Y : Type) [AddCommGroup Y] [Module B Y] (b : Y) :
    ∃ n : ℕ, (X.l i ^ n) • b = 0 := by
  refine ⟨nu X i + 1, ?_⟩
  have h := hK ((X.l i : X.O0 i) ^ nu X i * (X.l i : X.O0 i))
    (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (GlobalTheory.ResSel.SmallSub.l_mem X i))
  rw [map_mul, map_pow, map_natCast] at h
  rw [← Nat.cast_smul_eq_nsmul B, Nat.cast_pow, pow_succ, h, zero_smul]

theorem main : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (M : ℕ) (ι : Type) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), Computes bkP i s M d Q Φ → ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (φ : abelian₂ X i M ι →ₐ[X.O0 i] B) (κ : GE N →* Bˣ), (∀ g, ((κ g : Bˣ) : B) = φ (delInv i M d g : (abelian₂ X i M ι)ˣ)) → Kills i B → ∃ Z, Univ bkP i s κ Q (Φ.map φ) Z := by
  intro D N X bkP i s M ι d Q a Φ hC B _ _ φ κ hκ hK
  obtain ⟨e, he⟩ := hC
  letI : TopologicalSpace ((Fin a → B) ⧸ what₂ (Φ.map φ)) := ⊥
  haveI : DiscreteTopology ((Fin a → B) ⧸ what₂ (Φ.map φ)) := ⟨rfl⟩
  letI : Module (abelian₂ X i M ι) ((Fin a → B) ⧸ what₂ (Φ.map φ)) := Module.compHom _ (φ : abelian₂ X i M ι →+* B)
  have hW : ∀ (c : abelian₂ X i M ι) (y : (Fin a → B) ⧸ what₂ (Φ.map φ)), c • y = φ c • y := fun _ _ => rfl
  let xu : LinearMap.ker (matAct (M := (Fin a → B) ⧸ what₂ (Φ.map φ)) Φ) :=
    ⟨fun j => Submodule.Quotient.mk (Pi.single j 1), by
      rw [LinearMap.mem_ker, matAct_map φ hW]; exact univ_ker _⟩
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (e _ (tors i hK _) xu).1
  choose Z hZ using fun g c => Submodule.Quotient.mk_surjective (what₂ (Φ.map φ)) (z.1 g c)
  refine ⟨fun g => Matrix.of (Z g), ?_⟩
  intro Y _ _ _ _
  letI : Module (abelian₂ X i M ι) Y := Module.compHom _ (φ : abelian₂ X i M ι →+* B)
  have hY : ∀ (c : abelian₂ X i M ι) (y : Y), c • y = φ c • y := fun _ _ => rfl
  obtain ⟨hrep, hsel⟩ := GlobalTheory.T.selmerCocycles_scalarChange_transfer D N X bkP i s _ B φ (delInv i M d) κ hκ Y hY
  have key : ∀ x : LinearMap.ker (matAct (M := Y) Φ), ∃ z' : Z1 (repOn (Tgl i s) (delInv i M d) Y),
      z'.1 = (fun g => rect (Matrix.of (Z g)) x.1) ∧ (e Y (tors i hK Y) x).1 = Submodule.Quotient.mk z' := by
    intro x
    have hx : matAct (Φ.map φ) x.1 = 0 := by rw [← matAct_map φ hY]; exact x.2
    let f : ((Fin a → B) ⧸ what₂ (Φ.map φ)) →ₗ[abelian₂ X i M ι] Y :=
      { toFun := ev _ x.1 hx
        map_add' := map_add _
        map_smul' := fun c y => by rw [hW, map_smul, RingHom.id_apply, hY] }
    have hf : ∀ v, f (Submodule.Quotient.mk v) = ∑ j, v j • x.1 j := ev_mk _ _ hx
    refine ⟨cocycles1MapOfEquivariant _ _ (f.compLeft (Fin D.R.r)) continuous_of_discreteTopology (repOn_map _ _ f) z, ?_, ?_⟩
    · funext g c
      change f (z.1 g c) = _
      rw [← hZ, hf]
      rfl
    · refine he _ Y _ _ f xu x z _ (fun c => ?_) (fun g c => rfl) hz.symm
      change _ = f (Submodule.Quotient.mk _)
      rw [hf]
      simp [Pi.single_apply]
  have hker : ∀ x : Fin a → Y, matAct (Φ.map φ) x = 0 → x ∈ LinearMap.ker (matAct (M := Y) Φ) := fun x hx => by
    rw [LinearMap.mem_ker, matAct_map φ hY]; exact hx
  refine ⟨fun x hx => ?_, fun x hx hc => ?_, fun f hf => ?_⟩
  · obtain ⟨z', h1, h2⟩ := key ⟨x, hker x hx⟩
    exact (hsel Q _).1 ⟨z', h1, h2 ▸ (e Y (tors i hK Y) ⟨x, hker x hx⟩).2⟩
  · obtain ⟨z', h1, h2⟩ := key ⟨x, hker x hx⟩
    obtain ⟨m, hm⟩ := hc
    have h0 : (Submodule.Quotient.mk z' : H1 (repOn (Tgl i s) (delInv i M d) Y)) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1]
      refine ⟨m, fun g => ?_⟩
      rw [hrep, ← hm]
      exact congrFun h1 g
    have h3 : e Y (tors i hK Y) ⟨x, hker x hx⟩ = 0 := Subtype.ext (h2.trans h0)
    exact congrArg Subtype.val ((e Y (tors i hK Y)).map_eq_zero_iff.1 h3)
  · obtain ⟨w, rfl, hw⟩ := (hsel Q f).2 hf
    obtain ⟨x, hx⟩ := (e Y (tors i hK Y)).surjective ⟨_, hw⟩
    obtain ⟨z', h1, h2⟩ := key x
    refine ⟨x.1, by rw [← matAct_map φ hY]; exact x.2, ?_⟩
    have h3 : (Submodule.Quotient.mk w : H1 (repOn (Tgl i s) (delInv i M d) Y)) = Submodule.Quotient.mk z' := by
      rw [← h2, hx]
    rw [Submodule.Quotient.eq, Submodule.mem_comap, mem_coboundaries1] at h3
    obtain ⟨m, hm⟩ := h3
    refine ⟨m, fun g => ?_⟩
    rw [← hrep, ← hm]
    change _ = w.1 g - z'.1 g
    rw [h1]

end GlobalTheory.NewPrime.UnivCocycle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniversalSelmerCocycleBaseChangeStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universalSelmerCocycle_baseChange : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (M : ℕ) (ι : Type) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), Computes bkP i s M d Q Φ → ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (φ : abelian₂ X i M ι →ₐ[X.O0 i] B) (κ : GE N →* Bˣ), (∀ g, ((κ g : Bˣ) : B) = φ (delInv i M d g : (abelian₂ X i M ι)ˣ)) → Kills i B → ∃ Z, Univ bkP i s κ Q (Φ.map φ) Z := by
  first | exact @GlobalTheory.NewPrime.UnivCocycle.main | exact GlobalTheory.NewPrime.UnivCocycle.main | (intros; apply GlobalTheory.NewPrime.UnivCocycle.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT3OfHeckeSemisimple
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentImageStableOfEquivariant
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.EigRed

theorem mem_smul_of_sum_eigenvectors {O V ι α : Type*} [CommRing O] [AddCommGroup V] [Module O V]
    (I : Ideal O) (B : Submodule O V) (T : ι → Module.End O V) (hT : ∀ i, ∀ x ∈ B, T i x ∈ B) (ev : ι → O)
    (s : Finset α) :
    ∀ (y : α → V) (x : V), (∀ a ∈ s, y a = 0 ∨ ∃ e : ι → O, (∀ i, T i (y a) = e i • y a) ∧ ∃ i, IsUnit (ev i - e i)) →
      x = ∑ a ∈ s, y a → x ∈ B → (∀ i, T i x - ev i • x ∈ I • B) → x ∈ I • B := by
  classical
  have hTI : ∀ i, ∀ m ∈ I • B, T i m ∈ I • B := by
    intro i m hm
    refine Submodule.smul_induction_on hm (fun r hr n hn => ?_) (fun a b ha hb => ?_)
    · rw [map_smul]; exact Submodule.smul_mem_smul hr (hT i n hn)
    · rw [map_add]; exact add_mem ha hb
  induction s using Finset.induction_on with
  | empty => intro y x _ hx _ _; simp [hx]
  | insert a s ha ih =>
    intro y x hy hx hxB hev
    rw [Finset.sum_insert ha] at hx
    rcases hy a (Finset.mem_insert_self _ _) with h0 | ⟨e, he, i, hu⟩
    · exact ih y x (fun b hb => hy b (Finset.mem_insert_of_mem hb)) (by simpa [h0] using hx) hxB hev
    · have h1 : T i x - e i • x ∈ I • B := by
        refine ih (fun b => T i (y b) - e i • y b) _ (fun b hb => ?_) ?_ (sub_mem (hT i x hxB) (B.smul_mem _ hxB))
          (fun j => ?_)
        · rcases hy b (Finset.mem_insert_of_mem hb) with h0 | ⟨e', he', hu'⟩
          · left; simp [h0]
          · right
            refine ⟨e', fun j => ?_, hu'⟩
            rw [he' i, ← sub_smul, map_smul, he' j, smul_comm]
        set_option synthInstance.maxHeartbeats 100000 in
          · rw [hx, map_add (f := _), smul_add, he i, map_sum, Finset.smul_sum, Finset.sum_sub_distrib]; abel
        · have h2 : T j (T i x - e i • x) - ev j • (T i x - e i • x) =
              (ev i - e i) • (T j x - ev j • x) + (T j (T i x - ev i • x) - ev j • (T i x - ev i • x)) := by
            simp only [map_sub, map_smul]
            module
          rw [h2]
          exact add_mem (Submodule.smul_mem _ _ (hev j))
            (sub_mem (hTI j _ (hev i)) (Submodule.smul_mem _ _ (hev i)))
      have h3 : (ev i - e i) • x ∈ I • B := by
        have : (ev i - e i) • x = (T i x - e i • x) - (T i x - ev i • x) := by module
        rw [this]; exact sub_mem h1 (hev i)
      obtain ⟨u, hu⟩ := hu
      have h4 := Submodule.smul_mem _ ((u⁻¹ : Oˣ) : O) h3
      rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h4

open Formalism.MainNotions.IntegralHeckeForms

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem eG_idem (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) : eG Y i j b (eG Y i j b x) = eG Y i j b x := by
  rw [← mul_apply_eq_comp]
  unfold eG
  rw [← map_mul, Y.eAlg_idem]

theorem eG_comm (i : X.Tw) (j : ℕ) (b : Bool) (T : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (h : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ T = T ∘ₗ (Y.actG i j b g).toLinearMap) (x : Y.Fm i j b) :
    eG Y i j b (T x) = T (eG Y i j b x) := by
  unfold eG
  induction Y.eAlg i b using MonoidAlgebra.induction_on with
  | of g =>
    simp only [MonoidAlgebra.lift_of]
    exact LinearMap.congr_fun (h g) x
  | add f g hf hg => simp only [map_add (f := _), LinearMap.add_apply, hf, hg]
  | smul r f hf => simp only [map_smul, LinearMap.smul_apply, hf]

theorem idempotentImage_stable_of_equivariant (i : X.Tw) (j : ℕ) (b : Bool) (T : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (h : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ T = T ∘ₗ (Y.actG i j b g).toLinearMap) (x : Y.Fm i j b)
    (hx : x ∈ V0 Y i j b) : T x ∈ V0 Y i j b := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨T y, ?_, eG_comm Y i j b T h y⟩
  simp only [Fm0, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hy ⊢
  intro u
  have := LinearMap.congr_fun (h u) y
  simp only [LinearMap.comp_apply] at this
  rw [this, hy u, map_smul]

end GlobalTheory.EigRed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT3OfHeckeSemisimple
open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.EigRed

open Formalism.MainNotions.IntegralHeckeForms

theorem admT3_of_semisimple_good : ∀ (D : D7) (E : IntegralHeckeForms.XD D), IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp → D.nexp.sig_all → HkSS D → IntegralHeckeForms.GoodLatticePoints D.nexp := by
  intro D E hI hA hS hss i hi j hj b x hxB hxm ev hev
  by_contra hno
  apply hxm
  have hcomm := ((hA i hi b).2 j hj).1
  have hM := (hI i hi j hj b).2.2.2.1
  have hx := hss i hi j hj b hxB.2
  obtain ⟨f, hf, hfx⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx
  refine mem_smul_of_sum_eigenvectors (ι := {p : ℕ × PlE D.host // HkIdx i p.1 p.2}) _ _
    (fun p => hkO D.nexp i j b p.1.1 p.1.2) (fun p z hz => ?_) (fun p => ev p.1.1 p.1.2) f.support
    (fun a => f a) x (fun a _ => ?_) ?_ hxB (fun p => hev _ _ p.2)
  · exact ⟨hM _ _ p.2 ⟨z, hz.1, rfl⟩, idempotentImage_stable_of_equivariant D.nexp i j b _ (fun g => hcomm g _ _ p.2) z hz.2⟩
  · by_cases h0 : f a = 0
    · exact Or.inl h0
    right
    have hex : eG D.nexp i j b (f a) = f a := by
      obtain ⟨y, -, hy⟩ := (hf a).2
      rw [← hy, eG_idem]
    have heig : ∀ k P, HkIdx i k P → D.nexp.hkF i j b k P (f a) = a k P • f a := by
      intro k P hk
      have h1 := (hf a).1
      simp only [Eigsp, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h1
      exact h1 k P hk
    obtain ⟨s, hs1, hs2, hs3⟩ := hS i j b _ a h0 hex
      (fun k P h1 h2 h3 h4 => heig k P ⟨h1, h2, h3, h4⟩)
    refine ⟨fun p => D.ntw.hEig i s p.1.1 p.1.2, fun p => ?_, ?_⟩
    · change D.nexp.hkF i j b _ _ _ = _
      rw [heig _ _ p.2, ← hs3 _ _ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2, algebraMap_smul]
    · by_contra hu
      refine hno ⟨s, hs1, hs2, fun k P hk => ?_⟩
      exact fun h => hu ⟨⟨(k, P), hk⟩, h⟩
  · exact hfx.symm

end GlobalTheory.EigRed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT3OfHeckeSemisimpleStatement
open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admT3_of_hecke_semisimple : ∀ (D : D7) (E : IntegralHeckeForms.XD D), IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp → D.nexp.sig_all → HkSS D → IntegralHeckeForms.GoodLatticePoints D.nexp := by
  first | exact @GlobalTheory.EigRed.admT3_of_semisimple_good | exact GlobalTheory.EigRed.admT3_of_semisimple_good | (intros; apply GlobalTheory.EigRed.admT3_of_semisimple_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaVanishingNoInvariantsFirstHalfPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaVanishingNoInvariantsFirstHalfPlaces
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.StageFirst

open IsLocalRing GlobalTheory.ScalarFrob GlobalTheory.PrimeToInertia GlobalTheory.AntiRamConj
open scoped Pointwise

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (i : X.Tw) (s : X.Sig i)

theorem isLocalHom_of_kills {A : Type} [CommRing A] [Nontrivial A] [Algebra (X.O0 i) A] (h : Kills i A) :
    IsLocalHom (algebraMap (X.O0 i) A) := by
  refine ⟨fun x hx => ?_⟩
  by_contra hn
  have hm : x ∈ maximalIdeal (X.O0 i) := hn
  have : CharZero (FractionRing (X.O0 i)) := (X.emb0 i).charZero_iff (X.emb0 i).injective |>.1 inferInstance
  have : CharZero (X.O0 i) := (algebraMap (X.O0 i) (FractionRing (X.O0 i))).charZero
  have hl : ((X.l i : ℕ) : X.O0 i) ^ nu X i ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : (X.l i).Prime).ne_zero)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.O0 i)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ
  have h1 : ϖ ∣ x := by
    rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  have h2 : ((X.l i : ℕ) : X.O0 i) ^ nu X i ∣ x ^ n := by
    rw [hu, Units.mul_left_dvd]
    exact pow_dvd_pow_of_dvd h1 n
  have h3 := h (x ^ n * x) (Ideal.mul_mem_mul (Ideal.mem_span_singleton.2 h2) hm)
  rw [← pow_succ, map_pow] at h3
  exact (hx.pow _).ne_zero h3

theorem frob_scalar (bkP : BKPh X) (h : GalHyp bkP i s) {z : GE N} {L : Subgroup (GE N)} (hz : IsTameInertiaElementAtTwistPrime X i z)
    (hL : Small i s L z) {P : PlE D.host}
    (hA : ∀ v, Over P v → v ∉ X.S0 i ∧ (normV v : ResidueField (X.O0 i)) = 1)
    (hS : ∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ L)
    {v : PlE D.host} (hv : Over P v) {σ : GE N}
    (hσ : IsFrob (N.plOm.1 v) (normV v) σ) : ∃ c : ResidueField (X.O0 i), c ≠ 0 ∧ c ≠ 1 ∧ resT i s σ = c • 1 := by
  obtain ⟨e, he, -, hu, -⟩ := GlobalTheory.T.tameInertiaElement_acts_by_scalar D N X bkP i s z h.1 hz
  have c0 : residue (X.O0 i) e ≠ 0 := (residue_ne_zero_iff_isUnit _).2 e.isUnit
  have c1 : residue (X.O0 i) e ≠ 1 := by
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_one, sub_ne_zero] at hu
    exact hu
  have key : ∀ τ : GE N, IsFrob (N.plOm.1 P) (normV P) τ → resT i s τ = residue (X.O0 i) e • 1 := by
    intro τ hτ
    obtain ⟨g, hg⟩ := hS τ hτ
    have e1 : resT i s (g * τ * g⁻¹ * z⁻¹ * z) = residue (X.O0 i) e • 1 := by
      rw [map_mul, resT_apply, (hL.2.2.2.2 _ hg).1, one_mul, resT_apply, he]
      ext a b
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    have e2 := conj_scalar _ e1 g⁻¹
    rwa [show g⁻¹ * (g * τ * g⁻¹ * z⁻¹ * z) * g⁻¹⁻¹ = τ by group] at e2
  have hp := hA v hv
  have hp0 := hA _ (over_refl P)
  rcases hv with rfl | hv
  · exact ⟨_, c0, c1, key σ hσ⟩
  · have ε := eps_frob i hp.1 hp.2 hσ
    obtain ⟨τ, g, hτ, rfl⟩ := exists_frob_of_conj X hv hσ
    have ε0 := eps_frob i hp0.1 hp0.2 hτ
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at ε
    refine ⟨_, inv_ne_zero c0, inv_ne_one.2 c1, conj_scalar _ (scalar_of_dual i s ε c0 ?_) g⟩
    obtain ⟨A, hA⟩ := h.2.2.1
    have e3 : ((((eps0 X i τ : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s τ).map (residue (X.O0 i)) =
        residue (X.O0 i) e • 1 := by
      rw [← key τ hτ, resT_apply]
      ext a b
      simp [ε0]
    rw [hA τ _ (cConj_apply X τ), Matrix.map_mul, Matrix.map_mul, e3, mul_smul_comm, mul_one, smul_mul_assoc,
      ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem firstHalf : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → 0 < nu X i → ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → (∀ g, ∃ k : ℕ, κ g ^ (X.l i ^ k) = 1) → (ρ = Tgl i s ∨ IsDual i s ρ) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (b : Fin R), (∀ v, Over (P (.inl b)) v → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ Y g m = m) → m = 0) ∧ (AntiHom X.cc κ → (∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inl b))), κ τ = 1) → ∀ f : Z1 (repOn ρ κ Y), ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inl b))), f.1 τ = 0 ∧ f.1 (cConj X τ) = 0) := by
  intro hT D N X bkP i s h hl2 M R n d A₀ L z P hM hz hL hP A _ _ _ _ κ ρ hK hκ hρ Y _ _ _ _ b
  have := isLocalHom_of_kills i hK
  have hA : ∀ v, Over (P (.inl b)) v → v ∉ X.S0 i ∧ (normV v : ResidueField (X.O0 i)) = 1 := fun v hv =>
    ⟨(hP.1.1 _ v hv).2.2.2.1, natCast_eq_one i (show 1 ≤ M by omega) (hP.1.1 _ v hv).2.2.2.2.2⟩
  have fix0 : ∀ v, Over (P (.inl b)) v → ∀ σ : GE N, IsFrob (N.plOm.1 v) (normV v) σ →
      ∀ m, repOn ρ κ Y σ m = m → m = 0 := by
    intro v hv σ hσ m hm
    obtain ⟨c, c0, c1, hc⟩ := frob_scalar i s bkP h hz hL.1 hA (hP.2.1 b).2 hv hσ
    obtain ⟨c', c1', hc'⟩ : ∃ c' : ResidueField (X.O0 i), c' ≠ 1 ∧
        ((ρ σ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (residue _) = c' • 1 := by
      rcases hρ with rfl | hρ
      · exact ⟨c, c1, by rw [Tgl_coe, ← resT_apply, hc]⟩
      · exact ⟨c⁻¹, inv_ne_one.2 c1, by rw [hρ, dual_of_scalar i s (eps_frob i (hA v hv).1 (hA v hv).2 hσ) c0 hc]⟩
    exact eq_zero_of_scalar Fact.out (l_mem i) ρ κ (hκ σ) c1' hc' (q := 1) Nat.cast_one m (by rw [one_smul]; exact hm)
  have fix : ∀ v, Over (P (.inl b)) v → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ : GE N, IsFrob B (normV v) σ →
      ∀ m, repOn ρ κ Y σ m = m → m = 0 := by
    intro v hv B hB σ hσ m hm
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) hB (N.plOm.2 v)
    have h3 := isFrob_smul hσ g
    rw [hg] at h3
    have h4 := fix0 v hv _ h3 (repOn ρ κ Y g m) (by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, hm])
    have h5 := congrArg (repOn ρ κ Y g⁻¹) h4
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero] at h5
  have van : ∀ v, Over (P (.inl b)) v → ∀ B : ValuationSubring N.Om, IsPlaceOver B v →
      (∀ τ ∈ Ine (F := D.host.E) B, κ τ = 1) → ∀ f : Z1 (repOn ρ κ Y), ∀ τ ∈ Ine (F := D.host.E) B, f.1 τ = 0 := by
    intro v hv B hB hκB f
    obtain ⟨γ, -, hγ⟩ := GlobalTheory.TameRead.exists_gen_read hT.1 D.host.E N.Om (X.l i) B v hB
      (fun h => (hA v hv).1 (X.twistExcludedPlaces_contains_residueChar i h))
    have h1 : ∀ m : Fin D.R.r → Y, (X.l i ^ (nu X i + 1)) • m = 0 := fun m => by
      have := hK ((X.l i : X.O0 i) ^ nu X i * (X.l i : X.O0 i))
        (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (l_mem i))
      rw [map_mul, map_pow, map_natCast] at this
      rw [← Nat.cast_smul_eq_nsmul A, Nat.cast_pow, pow_succ, this, zero_smul]
    have h2 : normV v ≡ 1 [MOD X.l i ^ (nu X i + 1)] := by
      have hq := (hP.1.1 _ v hv).2.2.2.2.2
      have hd : X.l i ^ (nu X i + 1) ∣ 2 * X.l i ^ M := Dvd.dvd.mul_left (pow_dvd_pow _ hM) 2
      have h6 : normV v ≡ 1 [MOD 2 * X.l i ^ M] := by
        rw [← hq]
        exact (Nat.mod_modEq _ _).symm
      exact h6.of_dvd hd
    have h3 : ∀ σ ∈ Ine (F := D.host.E) B, ∀ m, repOn ρ κ Y σ m = m := by
      intro σ hσ m
      have hσL := (hP.2.1 b).1 v hv B hB hσ
      rcases hρ with rfl | hρ
      · rw [(GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl2 M L z hM hL A κ _ hK (isDual_dualRep i s) Y σ hσL).1, hκB σ hσ, Units.val_one,
          one_smul]
      · rw [(GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl2 M L z hM hL A κ _ hK hρ Y σ hσL).2.1, hκB σ hσ, Units.val_one, one_smul]
    obtain ⟨h4, h5⟩ := hγ A _ (repOn ρ κ Y) (nu X i + 1) h1 h2 h3 f
    obtain ⟨φ, hφ⟩ := exists_isFrob (F := D.host.E) hB
    exact h4 (fix v hv B hB φ hφ _ (h5 φ hφ))
  refine ⟨fun v hv m hm => ?_, fun hanti hκI f τ hτ => ⟨van _ (over_refl _) _ (N.plOm.2 _) hκI f τ hτ, ?_⟩⟩
  · obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 v)
    exact fix0 v hv σ hσ m (hm σ hσ.1)
  · obtain ⟨v, hv⟩ := exists_isConjPl (P (.inl b))
    refine van v (Or.inr hv) _ (isPlaceOver_moveVal_cc X hv (N.plOm.2 _)) (fun σ hσ => ?_) f _ (cConj_mem_ine X hτ)
    have h1 := cConj_mem_ine X hσ
    have e : moveVal X.cc (moveVal X.cc (N.plOm.1 (P (.inl b)))) = N.plOm.1 (P (.inl b)) := by
      ext y
      rw [mem_moveVal, mem_moveVal, cc_symm, cc_symm, cc_cc]
    rw [e] at h1
    have h2 := hκI _ h1
    rwa [antiHom_cConj X hanti, inv_eq_one] at h2

end GlobalTheory.StageFirst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaVanishingNoInvariantsFirstHalfPlacesStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaVanishing_noInvariants_firstHalfPlaces : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → 0 < nu X i → ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → (∀ g, ∃ k : ℕ, κ g ^ (X.l i ^ k) = 1) → (ρ = Tgl i s ∨ IsDual i s ρ) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (b : Fin R), (∀ v, Over (P (.inl b)) v → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ Y g m = m) → m = 0) ∧ (AntiHom X.cc κ → (∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inl b))), κ τ = 1) → ∀ f : Z1 (repOn ρ κ Y), ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inl b))), f.1 τ = 0 ∧ f.1 (cConj X τ) = 0) := by
  first | exact @GlobalTheory.StageFirst.firstHalf | exact GlobalTheory.StageFirst.firstHalf | (intros; apply GlobalTheory.StageFirst.firstHalf <;> assumption)
end
end
