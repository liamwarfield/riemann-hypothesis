module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterTwistProps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModel
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntryUnramifiedUnit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAway

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthInertiaRestrictionCocyclesLe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthInertiaRestrictionCocyclesLe
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.Quad

theorem length_torsionBy_le {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (a : O) :
    Module.length O (Submodule.torsionBy O (KOG O 1) a) ≤ Module.length O (O ⧸ Ideal.span {a}) := by
  rcases eq_or_ne a 0 with rfl | ha
  · have e : (O ⧸ Ideal.span {(0 : O)}) ≃ₗ[O] O := Submodule.quotEquivOfEqBot _ (by simp)
    rw [e.length_eq]
    have : Module.length O O = ⊤ := by
      by_contra h
      have h2 := (isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 h)).2
      have : IsArtinianRing O := h2
      exact IsDiscreteValuationRing.not_isField O (IsArtinianRing.isField_of_isDomain O)
    rw [this]; exact le_top
  · have ha' : algebraMap O (FractionRing O) a ≠ 0 := by
      simpa using ha
    let x : KOG O 1 := Submodule.Quotient.mk fun _ => (algebraMap O (FractionRing O) a)⁻¹
    have hx : a • x = 0 := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      refine ⟨fun _ => 1, ?_⟩
      funext j
      simp [Algebra.smul_def, mul_inv_cancel₀ ha']
    let x' : Submodule.torsionBy O (KOG O 1) a := ⟨x, hx⟩
    let f : O →ₗ[O] Submodule.torsionBy O (KOG O 1) a := LinearMap.toSpanSingleton O _ x'
    have hf : Ideal.span {a} ≤ LinearMap.ker f := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Subtype.ext hx
    refine Module.length_le_of_surjective (Submodule.liftQ _ f hf) ?_
    rintro ⟨y, hy⟩
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      rw [Submodule.mem_torsionBy_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨b, hb⟩ := hy
      refine ⟨Submodule.Quotient.mk (b 0), Subtype.ext ?_⟩
      change b 0 • x = Submodule.Quotient.mk y
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      have h0 : algebraMap O (FractionRing O) (b 0) = algebraMap O (FractionRing O) a * y 0 := by
        simpa [Algebra.smul_def] using congrFun hb 0
      simp only [Pi.smul_apply, Algebra.smul_def, h0]
      field_simp

theorem eq_zero_of_tameGen {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {γ : G E Ω} (hγ : TameGenAt A γ) {M : Type} [AddCommGroup M] (f : G E Ω → M)
    (hf : IsLocallyConstant f) (hadd : ∀ a ∈ Ine (F := E) A, ∀ b ∈ Ine (F := E) A, f (a * b) = f a + f b)
    (hw : ∀ σ : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) → f σ = 0) (h0 : f γ = 0)
    (σ : G E Ω) (hσ : σ ∈ Ine (F := E) A) : f σ = 0 := by
  have h1 : f 1 = 0 := by simpa using hadd 1 (one_mem _) 1 (one_mem _)
  let K : Subgroup (G E Ω) :=
    { carrier := {g | g ∈ Ine (F := E) A ∧ f g = 0}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [hadd a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      one_mem' := ⟨one_mem _, h1⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        have := hadd a ha.1 a⁻¹ (inv_mem ha.1)
        rw [mul_inv_cancel, h1, ha.2, zero_add] at this
        exact this.symm⟩ }
  refine closure_minimal (t := {g | f g = 0}) ?_ (hf.isClosed_fiber 0) (hγ.2 hσ)
  intro g hg
  refine ((Subgroup.closure_le K).2 ?_ hg).2
  rintro g (rfl | hg)
  · exact ⟨hγ.1, h0⟩
  · exact ⟨GlobalTheory.TameCharUnique.mem_Ine_of_wild hg, hw g hg⟩

theorem psiChi_group {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i} {S : IdempotentChoiceData D.nd i}
    (hS : GoodCongruenceObjects D.nd r ρ π S) (c : Fin D.R.t) (g : GE D.nd) :
    S.ψχ c (fun x' => rO D.nd i r (S.p x') g) = ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  obtain ⟨-, h1, h2, -, -, -, -, -, -, ⟨hp, -⟩, -⟩ := hS
  have hg : InR' D.nd r S fun x' => rO D.nd i r (S.p x') g :=
    ⟨1, fun _ => 1, fun _ => g, fun _ => one_mem _, by funext x; simp⟩
  have a1 := h1 g (S.e.symm (0, fun _ => 1))
  have a2 := h2 _ hg (S.e.symm (0, fun _ => 1))
  simp only [hp] at a2
  have a3 := congrFun (congrArg Prod.snd (a2.symm.trans a1)) c
  simp only [LinearEquiv.apply_symm_apply, mul_one] at a3
  exact IsFractionRing.injective _ _ a3

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ v, v ∈ D.nd.S i ∨ v ∈ D.nd.Q i → QuadAt i r Xs v → ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(resIne i (cocChi i r S Xs c) v) ≤ lenQ i (D.nd.zeta i v - 1) := by
  intro D i r ρ π Xs S hr hS hπ v hv hq c
  have hl := D.nd.SQ_l i v hv
  have hchi : ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), chiU D.nd i ((c : ℕ) + 1) γ = chiU D.nd i 1 γ :=
    fun γ hγ => (GlobalTheory.T.cyclotomicChar_unramified_away_from_ell D i v hl γ hγ).2 _ (by omega) c.2
  have hγ0 := D.nd.locNd_chebotarevPlace_mem i v
  have htor : ∀ f ∈ cocChi i r S Xs c, (D.nd.zeta i v - 1) • f (D.nd.gam0 i v) = 0 := by
    intro f hf
    have := Check.cocW_quad i r S Xs _ hq hf _ hγ0
    rw [Check.matKO_smul_one, psiChi_group hS, hchi _ hγ0] at this
    rw [sub_smul, one_smul, sub_eq_zero]
    exact this
  have hdet : ∀ f ∈ cocChi i r S Xs c, f (D.nd.gam0 i v) = 0 →
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), f σ = 0 := by
    intro f hf h0
    obtain ⟨hc, hz⟩ := (GlobalTheory.T.finiteQuotientCocycleSpan_rho_char_le_cocycles D i r ρ π Xs S hr hS hπ).2 c hf
    have : DiscreteTopology (KOG (D.nd.O i) 1) := ⟨rfl⟩
    have hlc : IsLocallyConstant f := (IsLocallyConstant.iff_continuous f).2 hc
    have hadd : ∀ a ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), ∀ b ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
        f (a * b) = f a + f b := by
      intro a ha b _
      have e : chiRatO D.nd i ((c : ℕ) + 1) a = (1 : D.nd.O i) • 1 := by
        change (((chiU D.nd i ((c : ℕ) + 1) a * (chiU D.nd i 1 a)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) •
          (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) = _
        rw [hchi a ha, mul_inv_cancel, Units.val_one]
      rw [hz, Check.WKG_eq_matKO, e, Check.matKO_smul_one, one_smul]
    exact eq_zero_of_tameGen (D.nd.restN_tameGenerator_generates i v hv) f hlc hadd (GlobalTheory.T.wildInertia_killed_by_additive_locallyConstant D i v hl f hlc hadd) h0
  refine le_trans ?_ (length_torsionBy_le (D.nd.zeta i v - 1))
  refine Module.length_le_of_injective
    (LinearMap.restrict (LinearMap.proj (⟨D.nd.gam0 i v, hγ0⟩ : Ine (F := D.host.E) (D.nd.plOm.1 v))) ?_) ?_
  · rintro _ ⟨f, hf, rfl⟩
    exact htor f hf
  · rw [injective_iff_map_eq_zero]
    rintro ⟨_, f, hf, rfl⟩ h0
    refine Subtype.ext (funext fun σ => ?_)
    exact hdet f hf (congrArg Subtype.val h0) σ.1 σ.2

end GlobalTheory.Cut.Quad
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthInertiaRestrictionCocyclesLeStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_inertia_restriction_cocycles_le : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ v, v ∈ D.nd.S i ∨ v ∈ D.nd.Q i → QuadAt i r Xs v → ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(resIne i (cocChi i r S Xs c) v) ≤ lenQ i (D.nd.zeta i v - 1) := by
  first | exact @GlobalTheory.Cut.Quad.main | exact GlobalTheory.Cut.Quad.main | (intros; apply GlobalTheory.Cut.Quad.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableLatticeInMatrixAlgebraLayer
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableLatticeInMatrixAlgebraLayer
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.LayerSst

open Module

section Sum

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ_[l] (V i)]
  {V' : Type} [AddCommGroup V'] [Module ℚ_[l] V']
  {ρ : ∀ i, Representation ℚ_[l] ↥(GK K) (V i)} {ρ' : Representation ℚ_[l] ↥(GK K) V'}
  {E : V' ≃ₗ[ℚ_[l]] (∀ i, V i)}
  (hE : ∀ g x i, E (ρ' g x) i = ρ i g (E x i))
include hE

theorem mem_Dst_iff (x : V' ⊗[ℚ_[l]] Bst P) :
    x ∈ Dst P ρ' ↔ ∀ i, GlobalTheory.BlockSum.tensComp E (Bst P) x i ∈ Dst P (ρ i) := by
  simp only [mem_Dst]
  rw [forall_comm]
  refine forall_congr' fun g => ?_
  rw [← (GlobalTheory.BlockSum.tensComp E (Bst P)).injective.eq_iff, funext_iff]
  refine forall_congr' fun i => ?_
  have key : GlobalTheory.BlockSum.tensComp E (Bst P) (stRep P ρ' g x) i =
      stRep P (ρ i) g (GlobalTheory.BlockSum.tensComp E (Bst P) x i) :=
    GlobalTheory.BlockSum.tensComp_map E (ρ' g) (fun i => ρ i g) (hE g) (actSt P (g : GQ l)).toLinearMap x i
  rw [key]

theorem isSst_sum [∀ i, FiniteDimensional ℚ_[l] (V i)] (h : ∀ i, IsSst P (ρ i)) : IsSst P ρ' := by
  have := fun i => finiteDimensional_Dst_of_isSst l P K (V i) (ρ i) (h i)
  unfold IsSst at h ⊢
  rw [GlobalTheory.BlockSum.finrank_eq_sum (GlobalTheory.BlockSum.tensComp E (Bst P)) _ _ (mem_Dst_iff P hE), E.finrank_eq,
    Module.finrank_pi_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => h i

end Sum

theorem isSst_resQ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (ρ : Representation LL ↥(GK K) V) (h : IsSst P ρ) : IsSst P (GlobalTheory.PstCoeff.resQ ρ) := by
  have hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l] := by
    ext x
    simp [mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]
  have e : finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) = finrank ℚ_[l] LL * finrank LL ↥(Dst P ρ) := by
    rw [hD, finrank_mul_finrank]
    rfl
  rw [IsSst, e, h, ← finrank_mul_finrank ℚ_[l] LL V]
  ring

section Layer

variable {l : ℕ} [Fact l.Prime] {K L₀ : FinExt l} {a d : ℕ} {Cl : Set (↥(GK K) →* GL (Fin a) (Om l))}
  {ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]} (Ly : Layer L₀ Cl ρ)

def matL (k : Fin Ly.m) (g : ↥(GK K)) : Matrix (Fin a) (Fin a) ↥(Ly.L k).1 :=
  fun i j => ⟨(Ly.rep k g).val i j, Ly.rep_mem k g i j⟩

def repL (k : Fin Ly.m) : ↥(GK K) →* GL (Fin a) ↥(Ly.L k).1 :=
  MonoidHom.toHomUnits
    { toFun := matL Ly k
      map_one' := by
        ext i j
        simp only [matL, map_one, Units.val_one, Matrix.one_apply]
        split_ifs <;> rfl
      map_mul' := fun g h => by
        ext i j
        simp [matL, Matrix.mul_apply] }

theorem repL_val (k : Fin Ly.m) (g : ↥(GK K)) (i j : Fin a) :
    (((repL Ly k g).val i j : ↥(Ly.L k).1) : Om l) = (Ly.rep k g).val i j := rfl

def RL (k : Fin Ly.m) : Representation ↥(Ly.L k).1 ↥(GK K) (Fin a → ↥(Ly.L k).1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥(Ly.L k).1 ≃ₐ[↥(Ly.L k).1] _) : _ →* _).comp
    ((Units.coeHom _).comp (repL Ly k))

theorem RL_apply (k : Fin Ly.m) (g : ↥(GK K)) (v : Fin a → ↥(Ly.L k).1) : RL Ly k g v = (repL Ly k g).val *ᵥ v := by
  simp [RL, Matrix.toLinAlgEquiv'_apply]

def coordM (v : Fin d → ℚ_[l]) (k : Fin Ly.m) : Matrix (Fin a) (Fin a) (Om l) :=
  ∑ s, algebraMap ℚ_[l] (Om l) (v s) • Ly.b s k

theorem coordM_mem (v : Fin d → ℚ_[l]) (k : Fin Ly.m) (i j : Fin a) : coordM Ly v k i j ∈ (Ly.L k).1 := by
  simp only [coordM, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact sum_mem fun s _ => mul_mem (IntermediateField.algebraMap_mem _ _) (Ly.b_mem s k i j)

theorem sum_b (v : Fin d → ℚ_[l]) : ∑ s, v s • Ly.b s = fun k => coordM Ly v k := by
  funext k
  simp [coordM, Finset.sum_apply, algebraMap_smul]

end Layer

section Layer2

variable {l : ℕ} [Fact l.Prime] {K L₀ : FinExt l} {a d : ℕ} {Cl : Set (↥(GK K) →* GL (Fin a) (Om l))}
  {ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]} (Ly : Layer L₀ Cl ρ)

def coordLin : (Fin d → ℚ_[l]) →ₗ[ℚ_[l]] ((p : Fin Ly.m × Fin a) → Fin a → ↥(Ly.L p.1).1) where
  toFun v p i := ⟨coordM Ly v p.1 i p.2, coordM_mem Ly v p.1 i p.2⟩
  map_add' v w := by
    funext p i
    apply Subtype.ext
    simp [coordM, Finset.sum_add_distrib, add_smul, Matrix.sum_apply]
  map_smul' c v := by
    funext p i
    apply Subtype.ext
    show coordM Ly (c • v) p.1 i p.2 = c • coordM Ly v p.1 i p.2
    simp only [coordM, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, map_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Algebra.smul_def, mul_assoc]

theorem coordLin_apply (v : Fin d → ℚ_[l]) (p : Fin Ly.m × Fin a) (i : Fin a) :
    ((coordLin Ly v p i : ↥(Ly.L p.1).1) : Om l) = coordM Ly v p.1 i p.2 := rfl

theorem coordLin_bijective : Function.Bijective (coordLin Ly) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h0 : ∑ s, v s • Ly.b s = 0 := by
      rw [sum_b]
      funext k i j
      have := congrArg Subtype.val (congrFun (congrFun hv (k, j)) i)
      exact this
    exact funext (Fintype.linearIndependent_iff.1 Ly.indep v h0)
  · intro y
    let x : Fin Ly.m → Matrix (Fin a) (Fin a) (Om l) := fun k i j => ((y (k, j) i : ↥(Ly.L k).1) : Om l)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ_[l]).1 (Ly.span x fun k i j => (y (k, j) i).2)
    refine ⟨c, ?_⟩
    funext p i
    apply Subtype.ext
    rw [coordLin_apply]
    rw [sum_b] at hc
    exact congrFun (congrFun (congrFun hc p.1) i) p.2

def coordEquiv : (Fin d → ℚ_[l]) ≃ₗ[ℚ_[l]] ((p : Fin Ly.m × Fin a) → Fin a → ↥(Ly.L p.1).1) :=
  LinearEquiv.ofBijective (coordLin Ly) (coordLin_bijective Ly)

theorem coordM_mulVec (g : ↥(GK K)) (v : Fin d → ℚ_[l]) (k : Fin Ly.m) :
    coordM Ly (((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v) k = (Ly.rep k g).val * coordM Ly v k := by
  have hr : ∀ t, (Ly.rep k g).val * Ly.b t k = ∑ s, zOm l ((ρ g).val s t) • Ly.b s k :=
    fun t => (Ly.reads k).equi g t
  calc coordM Ly (((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v) k
      = ∑ s, ∑ t, (algebraMap ℚ_[l] (Om l) (v t) * zOm l ((ρ g).val s t)) • Ly.b s k := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [coordM, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_smul, Matrix.map_apply]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
        rw [mul_comm]
        rfl
    _ = ∑ t, ∑ s, (algebraMap ℚ_[l] (Om l) (v t) * zOm l ((ρ g).val s t)) • Ly.b s k := Finset.sum_comm
    _ = (Ly.rep k g).val * coordM Ly v k := by
        simp only [coordM, Finset.mul_sum, Matrix.mul_smul, hr, Finset.smul_sum, smul_smul]

theorem coordEquiv_equi (g : ↥(GK K)) (v : Fin d → ℚ_[l]) (p : Fin Ly.m × Fin a) :
    coordEquiv Ly (qRep ρ g v) p = GlobalTheory.PstCoeff.resQ (RL Ly p.1) g (coordEquiv Ly v p) := by
  funext i
  apply Subtype.ext
  have hq : qRep ρ g v = ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v := by
    simp [qRep, Matrix.toLinAlgEquiv'_apply]
  rw [GlobalTheory.PstCoeff.resQ_apply, RL_apply]
  change coordM Ly (qRep ρ g v) p.1 i p.2 = _
  rw [hq, coordM_mulVec, Matrix.mul_apply]
  simp [Matrix.mulVec, dotProduct, repL_val, coordEquiv, coordLin_apply]

end Layer2

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ) (Cl : Set (↥(GK K) →* GL (Fin a) (Om l))) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (Ly : Layer L₀ Cl ρ), ((∀ ρ₁ ∈ Cl, ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R) → IsSst P (qRep ρ)) ∧ ((∀ ρ₁ ∈ Cl, (∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsCrys (P.PD K) R)) → IsCrys (P.PD K) (qRep ρ)) := by
  intro l _ K L₀ P AI T a Cl d ρ Ly
  have hfin : ∀ p : Fin Ly.m × Fin a, FiniteDimensional ℚ_[l] (Fin a → ↥(Ly.L p.1).1) := fun p => by
    have := (Ly.L p.1).2
    infer_instance
  have hE := coordEquiv_equi Ly
  refine ⟨fun hS => ?_, fun hC => ?_⟩
  · refine isSst_sum P (E := coordEquiv Ly) (fun g x p => hE g x p) fun p => ?_
    have := (Ly.L p.1).2
    exact isSst_resQ P _ (hS (Ly.rep p.1) (Ly.mem p.1) (Ly.L p.1) (repL Ly p.1) (RL Ly p.1) (Ly.le p.1)
      (fun g v => RL_apply Ly p.1 g v) (fun g i j => repL_val Ly p.1 g i j))
  · refine GlobalTheory.BlockSum.isCrys_sum (P.PD K) (E := coordEquiv Ly) (fun g x p => hE g x p) fun p => ?_
    have := (Ly.L p.1).2
    exact (GlobalTheory.BSCoeff.isCrys_resQ_iff P (RL Ly p.1)).2 (hC (Ly.rep p.1) (Ly.mem p.1) (Ly.L p.1) (repL Ly p.1)
      (RL Ly p.1) (Ly.le p.1) (fun g v => RL_apply Ly p.1 g v) (fun g i j => repL_val Ly p.1 g i j))

end GlobalTheory.LayerSst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableLatticeInMatrixAlgebraLayerStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemistable_latticeInMatrixAlgebraLayer : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ) (Cl : Set (↥(GK K) →* GL (Fin a) (Om l))) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (Ly : Layer L₀ Cl ρ), ((∀ ρ₁ ∈ Cl, ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R) → IsSst P (qRep ρ)) ∧ ((∀ ρ₁ ∈ Cl, (∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsCrys (P.PD K) R)) → IsCrys (P.PD K) (qRep ρ)) := by
  first | exact @GlobalTheory.LayerSst.main | exact GlobalTheory.LayerSst.main | (intros; apply GlobalTheory.LayerSst.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistHeckeCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNeZeroMulConjEqOfUnitary
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Host Formalism.L2.Col Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.NormOneHilbert90Units

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_ne_zero_mul_conj_eq_of_unitary (D : D7) (z : unitary D.host.E) :
    ∃ w : D.host.E, w ≠ 0 ∧ (z : D.host.E) * D.host.conj w = w := by
  have hz : (z : D.host.E) * star (z : D.host.E) = 1 := z.2.2
  have key : ∀ a : D.host.E, (z : D.host.E) * star (a + (z : D.host.E) * star a) = a + (z : D.host.E) * star a := by
    intro a
    rw [star_add, star_mul, star_star]
    linear_combination a * hz
  obtain ⟨x, hx⟩ : ∃ x : D.host.E, star x ≠ x := by
    by_contra h
    push_neg at h
    apply NumberField.IsCMField.complexConj_ne_one D.host.E
    refine AlgEquiv.ext fun x => ?_
    rw [← Formalism.BasicNotions.Examples₂.cmStar_apply]
    exact h x
  by_cases h1 : (1 : D.host.E) + (z : D.host.E) * star (1 : D.host.E) = 0
  · refine ⟨x + (z : D.host.E) * star x, ?_, ?_⟩
    · intro h2
      have hz1 : (z : D.host.E) = -1 := by rw [star_one] at h1; linear_combination h1
      rw [hz1] at h2
      exact hx (by linear_combination -h2)
    · rw [← Formalism.BasicNotions.Examples₂.star_eq_conj]; exact key x
  · exact ⟨_, h1, by rw [← Formalism.BasicNotions.Examples₂.star_eq_conj]; exact key 1⟩

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

end Comparison₂

end GlobalTheory.NormOneHilbert90Units
end
end

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AntiCycRead

variable (D : D7)

def quo : (AE D)ˣ →* (Af D.host.F ⊗[D.host.F] D.host.E)ˣ :=
  MonoidHom.mk' (fun x => Units.map (finPart D).toMonoidHom x *
      (Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x)⁻¹)
    (fun x y => by simp only [map_mul, mul_inv]; exact mul_mul_mul_comm _ _ _ _)

theorem quo_mul (x : (AE D)ˣ) :
    ((quo D x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) *
        sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) = finPart D (x : AE D) := by
  have hsv : ((Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x :
      (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) := GlobalTheory.DetRootChar.finPart_sigR D x
  rw [← hsv]
  show ((Units.map (finPart D).toMonoidHom x * (Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x)⁻¹ :
      (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) * _ = _
  rw [← Units.val_mul, inv_mul_cancel_right]
  rfl

theorem quo_eq_of (x : (AE D)ˣ) (u : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ)
    (hu : (u : Af D.host.F ⊗[D.host.F] D.host.E) * sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) =
      finPart D (x : AE D)) : quo D x = u := by
  set s : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ :=
    Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x with hs
  have hsv : (s : Af D.host.F ⊗[D.host.F] D.host.E) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) := by
    rw [hs]; exact GlobalTheory.DetRootChar.finPart_sigR D x
  have h1 := quo_mul D x
  rw [← hsv] at h1 hu
  have : ((quo D x * s : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ)) = u * s := Units.ext (by simp [h1, hu])
  exact mul_right_cancel this

theorem ker_trivial (δ : (AE D)ˣ →* Circle) (hF : ∀ a, δ (idF D a) = 1) (hfin : ∃ m : ℕ, 0 < m ∧ ∀ x, δ x ^ m = 1)
    (x : (AE D)ˣ) (hx : quo D x = 1) : δ x = 1 := by
  have h1 := quo_mul D x
  rw [hx, Units.val_one, one_mul] at h1
  obtain ⟨a, y, hy, hxy⟩ := GlobalTheory.DetRootChar.exists_idF_mul D x h1
  obtain ⟨m, hm, hδ⟩ := hfin
  obtain ⟨z, hz⟩ := GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D m hm y hy
  rw [hxy, map_mul, hF, mul_one, ← hz, map_pow, hδ]

theorem quo_of_isDetRoot (W : HSp D) (g : GA D W) (x : (AE D)ˣ) (hx : IsDetRoot W g x) :
    quo D x = Matrix.GeneralLinearGroup.det (finHom W g) := by
  apply quo_eq_of
  have hdet : ((Matrix.GeneralLinearGroup.det (finHom W g) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
      Af D.host.F ⊗[D.host.F] D.host.E) = finPart D (matHom W g).1.det :=
    (GlobalTheory.DetRootChar.finPart_det D W g).symm
  rw [hdet, ← GlobalTheory.DetRootChar.finPart_sigR, ← RingHom.map_mul]
  exact (congrArg _ hx).symm

end GlobalTheory.AntiCycRead

end

noncomputable section

namespace GlobalTheory.AntiCycRead

variable (D : D7)

theorem val_of_quo (χ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* Circle) (Y : (AE D)ˣ) :
    (((Circle.toUnits.comp χ) (quo D Y) : ℂˣ) : ℂ) = ((χ (quo D Y) : Circle) : ℂ) := by
  simp

theorem exists_rat (x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) (a : D.host.E)
    (hxa : (x : Af D.host.F ⊗[D.host.F] D.host.E) = 1 ⊗ₜ a) (hx : GlobalTheory.FinalJoin.NormOne x)
    [Nontrivial (Af D.host.F)] : ∃ w : D.host.Eˣ, quo D (Units.map (incA D).toMonoidHom w) = x := by
  have hN : (x : Af D.host.F ⊗[D.host.F] D.host.E) *
      sigR (Af D.host.F) D.sp.cm.sig (x : Af D.host.F ⊗[D.host.F] D.host.E) = 1 := hx
  rw [hxa] at hN
  have ha : a * D.sp.cm.sig a = 1 := by
    apply Algebra.TensorProduct.includeRight_injective (A := Af D.host.F) (R := D.host.F)
      (algebraMap D.host.F (Af D.host.F)).injective
    show (1 : Af D.host.F) ⊗ₜ[D.host.F] (a * D.sp.cm.sig a) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)
    rw [← Algebra.TensorProduct.one_def]
    simpa [sigR] using hN
  have hu : a ∈ unitary D.host.E := ⟨by rw [mul_comm]; exact ha, ha⟩
  obtain ⟨w, hw0, hw⟩ := GlobalTheory.NormOneHilbert90Units.exists_ne_zero_mul_conj_eq_of_unitary D ⟨a, hu⟩
  refine ⟨Units.mk0 w hw0, ?_⟩
  apply quo_eq_of
  have hfY : finPart D ((Units.map (incA D).toMonoidHom (Units.mk0 w hw0) : (AE D)ˣ) : AE D) =
      (1 : Af D.host.F) ⊗ₜ[D.host.F] w := rfl
  rw [hfY, hxa]
  simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [← Formalism.BasicNotions.Examples₂.star_eq_conj] at hw
  exact congrArg _ hw

theorem exists_cong (N : ℕ) (hN : Odd N) (x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) (hx : GlobalTheory.FinalJoin.NormOne x)
    (w : Af D.host.F ⊗[D.host.F] D.host.E) (hw : w ∈ intAE D)
    (hwe : (x : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = N • w) :
    ∃ Y : (AE D)ˣ, FinUnit Y ∧ (∃ y ∈ intAE D, finPart D (Y : AE D) - 1 = N • y) ∧ quo D Y = x := by
  have hn : (x : Af D.host.F ⊗[D.host.F] D.host.E) *
      sigR (Af D.host.F) D.sp.cm.sig (x : Af D.host.F ⊗[D.host.F] D.host.E) = 1 := hx
  obtain ⟨y, y', hy, hy', hyy, hroot, q, hq, hqe⟩ :=
    GlobalTheory.T.exists_normOne_root_congruent_odd_hostField D N hN (x : Af D.host.F ⊗[D.host.F] D.host.E) w hw hwe hn
  obtain ⟨Y, h1, h2, h3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  refine ⟨Y, ⟨h1, h2 ▸ hy, h3 ▸ hy'⟩, ⟨q, hq, h2 ▸ hqe⟩, ?_⟩
  apply quo_eq_of
  rw [h2]
  exact hroot.symm

theorem exists_normOne (x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) (hx : GlobalTheory.FinalJoin.NormOne x) :
    ∃ Y : (AE D)ˣ, quo D Y = x := by
  obtain ⟨y, hy⟩ := (GlobalTheory.IdeleNinety.finiteIdeles_normOne_eq_div_conj_with_congruence D).1 x hx
  obtain ⟨Y, -, h1, -⟩ := GlobalTheory.DetRootCong.exists_idele D (y : Af D.host.F ⊗[D.host.F] D.host.E)
    ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _) y.mul_inv
  have hc : ((Formalism.L2.Pj.cjFin D y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E) :=
    GlobalTheory.IdeleNinety.coe_cjFin D y
  refine ⟨Y, ?_⟩
  apply quo_eq_of
  rw [h1, ← hc, hy, ← Units.val_mul, div_mul_cancel]

end GlobalTheory.AntiCycRead

end

noncomputable section

namespace GlobalTheory.AntiCycRead

theorem read_anticyc : ∀ (D : D7) (W : HSp D) (L : Type) [Field L] (σ : L →+* ℂ) (p : ℕ), Odd p → ∀ δ : (AE D)ˣ →* Circle, IsHeckeChar D δ → (∀ a, δ (Formalism.L2.Theta.idF D a) = 1) → (∃ m : ℕ, 0 < m ∧ ∀ x, δ x ^ m = 1) → (∀ x, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = p • y) → δ x = 1) → (∀ x, ∃ y : L, σ y = ((δ x : Circle) : ℂ)) → ∃ xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTwist σ p xi ∧ ∀ (g : GA D W) (x : (AE D)ˣ), IsDetRoot W g x → ((xi (Matrix.GeneralLinearGroup.det (finHom W g)) : ℂˣ) : ℂ) = ((δ x : Circle) : ℂ) := by
  intro D W L _ σ p hp δ hH hF hfin hcong hval
  obtain ⟨χ, hχ⟩ := GlobalTheory.DetRootChar.circle_hom_factor (quo D) δ (ker_trivial D δ hF hfin)
  have hxi : ∀ Y : (AE D)ˣ, (((Circle.toUnits.comp χ) (quo D Y) : ℂˣ) : ℂ) = ((δ Y : Circle) : ℂ) := by
    intro Y
    rw [val_of_quo, hχ]
  refine ⟨Circle.toUnits.comp χ, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x a hxa hx
    rcases subsingleton_or_nontrivial (Af D.host.F) with hs | hs
    · have h0 : ∀ z : Af D.host.F ⊗[D.host.F] D.host.E, z = 0 := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul b e => rw [Subsingleton.elim b 0, TensorProduct.zero_tmul]
        | add u v hu hv => rw [hu, hv, add_zero]
      have hx1 : x = 1 := Units.ext ((h0 _).trans (h0 _).symm)
      rw [hx1, map_one]
    obtain ⟨w, hw⟩ := exists_rat D x a hxa hx
    apply Units.ext
    rw [← hw, hxi, hH.2 w]
    rfl
  · rintro x hx ⟨w, hw, hwe⟩
    obtain ⟨Y, hY, hYc, hQ⟩ := exists_cong D p hp x hx w hw hwe
    apply Units.ext
    rw [← hQ, hxi, hcong Y hY hYc]
    rfl
  · intro x hx
    obtain ⟨Y, hQ⟩ := exists_normOne D x hx
    obtain ⟨a, ha⟩ := hval Y
    refine ⟨a, ?_⟩
    rw [← hQ, hxi]
    exact ha
  · intro g x hx
    rw [← quo_of_isDetRoot D W g x hx, hxi]

end GlobalTheory.AntiCycRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRankinSelbergPlaceSetSupersetTotallyCo
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRankinSelbergPlaceSetSupersetTotallyCo
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

noncomputable section

namespace GlobalTheory.RSNonvan.GoodSet

variable {E : Type} [Field E] [NumberField E]

theorem psiLoc_cond (w : HeightOneSpectrum (𝓞 E))
    (hw : FractionalIdeal.count E w ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 0) (x : w.adicCompletion E) :
    (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w := by
  have key : (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔
      ∀ a ∈ w.adicCompletionIntegers E, GroundTheory.Global.localAdelicChar E w (a * x) = 1 := by
    refine forall_congr' fun y => imp_congr Iff.rfl ?_
    change GlobalTheory.StdCharConductor.psi E (sFin E (sLoc E w (x * y))) = 1 ↔ _
    rw [GlobalTheory.StdCharConductor.psi_loc_eq_one_iff, mul_comm]
  rw [key, GroundTheory.Global.forall_localAdelicChar_mul_eq_one_iff, GroundTheory.Global.mem_localInvDifferent_iff_valued, hw]
  change _ ↔ x ∈ w.adicCompletionIntegers E
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  rfl

theorem finite_sameBelow (u : HeightOneSpectrum (𝓞 E)) :
    {w' : HeightOneSpectrum (𝓞 E) | Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal}.Finite := by
  set N : ℕ := Ideal.absNorm u.asIdeal
  have hN : N ≠ 0 := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm u
    omega
  have hI : Ideal.span {(N : 𝓞 E)} ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine (Ideal.finite_factors hI).subset fun w' hw' => ?_
  simp only [Set.mem_setOf_eq] at hw' ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  have h1 : ((N : ℤ)) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal := by
    rw [Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem u.asIdeal
  rw [← hw', Ideal.mem_comap, map_natCast] at h1
  exact h1

variable [_root_.NumberField.IsTotallyComplex E]

theorem exists_isGood_superset (T : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ T' : Finset (HeightOneSpectrum (𝓞 E)), T ⊆ T' ∧ IsGood T' := by
  classical
  have hD : {w : HeightOneSpectrum (𝓞 E) | FractionalIdeal.count E w ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0}.Finite :=
    FractionalIdeal.finite_factors (K := E) ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
  set T₁ : Finset (HeightOneSpectrum (𝓞 E)) := T ∪ hD.toFinset
  set S : Set (HeightOneSpectrum (𝓞 E)) := {w' | ∃ u ∈ T₁, Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal}
  have hS : S.Finite := by
    have : S = ⋃ u ∈ T₁, {w' : HeightOneSpectrum (𝓞 E) | Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
        Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal} := by
      ext w'
      simp [S]
    rw [this]
    exact T₁.finite_toSet.biUnion fun u _ => finite_sameBelow u
  have hT₁ : ∀ w ∈ T₁, w ∈ hS.toFinset := fun w hw => by
    rw [Set.Finite.mem_toFinset]
    exact ⟨w, hw, rfl⟩
  refine ⟨hS.toFinset, fun w hw => hT₁ w (Finset.mem_union_left _ hw), ?_, ?_⟩
  · intro w hw w' hw'
    rw [Set.Finite.mem_toFinset] at hw ⊢
    obtain ⟨u, hu, hwu⟩ := hw
    exact ⟨u, hu, hw'.trans hwu⟩
  · intro w hw x
    refine psiLoc_cond w ?_ x
    by_contra h
    exact hw (hT₁ w (Finset.mem_union_right _ (by simpa using h)))

end GlobalTheory.RSNonvan.GoodSet

theorem GlobalTheory.RSNonvan.exists_isGood_superset_all : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (T : Finset (HeightOneSpectrum (𝓞 E))), ∃ T' : Finset (HeightOneSpectrum (𝓞 E)), T ⊆ T' ∧ IsGood T' :=
  fun _ _ _ _ T => GlobalTheory.RSNonvan.GoodSet.exists_isGood_superset T

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRankinSelbergPlaceSetSupersetTotallyCoStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodRankinSelbergPlaceSet_superset_totallyComplex : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (T : Finset (HeightOneSpectrum (𝓞 E))), ∃ T' : Finset (HeightOneSpectrum (𝓞 E)), T ⊆ T' ∧ IsGood T' := by
  first | (exact @GlobalTheory.RSNonvan.exists_isGood_superset_all) | (exact GlobalTheory.RSNonvan.exists_isGood_superset_all) | (intros; apply GlobalTheory.RSNonvan.exists_isGood_superset_all  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionWhittakerEquivariant
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurEquiv

open Matrix

section Alg

variable {R : Type} [CommRing R]

def IsUT {n : ℕ} (U : Matrix (Fin n) (Fin n) R) : Prop := (∀ i j : Fin n, j < i → U i j = 0) ∧ ∀ i, U i i = 1

def sd {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : R := ∑ i : Fin n, ∑ j : Fin n, if j.val = i.val + 1 then M i j else 0

theorem superDiag_eq_sd {n : ℕ} (g : GL (Fin n) R) : GlobalTheory.Whittaker.superDiag g = sd (g : Matrix (Fin n) (Fin n) R) := by
  simp [GlobalTheory.Whittaker.superDiag, sd, Finset.sum_filter]

theorem det_of_isUT {n : ℕ} {U : Matrix (Fin n) (Fin n) R} (hU : IsUT U) : U.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j h => hU.1 i j h)]
  simp [hU.2]

variable {m r : ℕ}

theorem eqv_symm_inl (i : Fin (m + 1)) : ((eqv m r).symm (Sum.inl i)).val = i.val := by simp [eqv]
theorem eqv_symm_inr (j : Fin (r + 1)) : ((eqv m r).symm (Sum.inr j)).val = m + 1 + j.val := by simp [eqv]

theorem blk_mul (M N : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : blk (M * N) = blk M * blk N :=
  (Matrix.submatrix_mul_equiv M N _ (eqv m r).symm _).symm

theorem blk_eq (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    blk M = fromBlocks (Aof M) (Bof M) (Cof M) (Dof M) := (fromBlocks_toBlocks _).symm

variable {U : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R}

theorem Cof_of_isUT (hU : IsUT U) : Cof U = 0 := by
  ext i j
  apply hU.1
  rw [Fin.lt_def, eqv_symm_inl, eqv_symm_inr]
  omega

theorem Aof_isUT (hU : IsUT U) : IsUT (Aof U) :=
  ⟨fun i j h => hU.1 _ _ (by rw [Fin.lt_def, eqv_symm_inl, eqv_symm_inl]; exact h), fun i => hU.2 _⟩

theorem Dof_isUT (hU : IsUT U) : IsUT (Dof U) :=
  ⟨fun i j h => hU.1 _ _ (by rw [Fin.lt_def, eqv_symm_inr, eqv_symm_inr]; rw [Fin.lt_def] at h; omega), fun i => hU.2 _⟩

variable (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R)

theorem blk_UM (hU : IsUT U) : blk (U * M) = fromBlocks (Aof U * Aof M + Bof U * Cof M) (Aof U * Bof M + Bof U * Dof M)
    (Dof U * Cof M) (Dof U * Dof M) := by
  rw [blk_mul, blk_eq U, blk_eq M, Cof_of_isUT hU, fromBlocks_multiply]
  simp

theorem Aof_mul (hU : IsUT U) : Aof (U * M) = Aof U * Aof M + Bof U * Cof M := by
  rw [Aof, blk_UM M hU, toBlocks_fromBlocks₁₁]
theorem Bof_mul (hU : IsUT U) : Bof (U * M) = Aof U * Bof M + Bof U * Dof M := by
  rw [Bof, blk_UM M hU, toBlocks_fromBlocks₁₂]
theorem Cof_mul (hU : IsUT U) : Cof (U * M) = Dof U * Cof M := by
  rw [Cof, blk_UM M hU, toBlocks_fromBlocks₂₁]
theorem Dof_mul (hU : IsUT U) : Dof (U * M) = Dof U * Dof M := by
  rw [Dof, blk_UM M hU, toBlocks_fromBlocks₂₂]

theorem isUnit_Dof_mul_iff (hU : IsUT U) : IsUnit (Dof (U * M)).det ↔ IsUnit (Dof M).det := by
  rw [Dof_mul M hU, det_mul, det_of_isUT (Dof_isUT hU), one_mul]

theorem Yof_mul (hU : IsUT U) : Yof (U * M) = Yof M := by
  have hu : IsUnit (Dof U).det := by rw [det_of_isUT (Dof_isUT hU)]; exact isUnit_one
  rw [Yof, Yof, Dof_mul M hU, Cof_mul M hU, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (Dof U)⁻¹,
    nonsing_inv_mul _ hu, Matrix.one_mul]

theorem Scof_mul (hU : IsUT U) (hD : IsUnit (Dof M).det) : Scof (U * M) = Aof U * Scof M := by
  have hu : IsUnit (Dof U).det := by rw [det_of_isUT (Dof_isUT hU)]; exact isUnit_one
  have h1 : (Dof M)⁻¹ * (Dof U)⁻¹ * (Dof U * Cof M) = (Dof M)⁻¹ * Cof M := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Dof U)⁻¹, nonsing_inv_mul _ hu, Matrix.one_mul]
  rw [Scof, Scof, Aof_mul M hU, Bof_mul M hU, Dof_mul M hU, Cof_mul M hU, Matrix.mul_inv_rev, Matrix.mul_assoc _ _ (Dof U * Cof M), h1]
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Dof M) (Dof M)⁻¹ (Cof M), mul_nonsing_inv _ hD, Matrix.one_mul]
  abel

theorem Xof_mul (hU : IsUT U) (hD : IsUnit (Dof M).det) :
    Xof (U * M) = Aof U * Xof M * (Dof U)⁻¹ + Bof U * (Dof U)⁻¹ := by
  rw [Xof, Xof, Bof_mul M hU, Dof_mul M hU, Matrix.mul_inv_rev]
  simp only [Matrix.add_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Dof M) (Dof M)⁻¹ (Dof U)⁻¹, mul_nonsing_inv _ hD, Matrix.one_mul]

theorem inv_first_column_of_upper_triangular {n : ℕ} {V : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (hV : IsUT V) (l : Fin (n + 1)) :
    V⁻¹ l 0 = if l = 0 then 1 else 0 := by
  have hu : IsUnit V.det := by rw [det_of_isUT hV]; exact isUnit_one
  have h := congrFun (congrFun (nonsing_inv_mul V hu) l) 0
  rw [Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (n + 1)), hV.2, mul_one, Matrix.one_apply] at h
  · exact h
  · intro k _ hk; rw [hV.1 k 0 (Fin.pos_iff_ne_zero.2 hk), mul_zero]
  · simp

theorem mul_first_column_of_unit_column {n k : ℕ} (N : Matrix (Fin k) (Fin (n + 1)) R) {P : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hP : ∀ l, P l 0 = if l = 0 then 1 else 0) (i : Fin k) : (N * P) i 0 = N i 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp [hP]
  · intro l _ hl; simp [hP, hl]
  · simp

theorem lastRow_mul {n k : ℕ} {Q : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (hQ : IsUT Q) (N : Matrix (Fin (n + 1)) (Fin k) R)
    (j : Fin k) : (Q * N) (Fin.last n) j = N (Fin.last n) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n), hQ.2, one_mul]
  · intro l _ hl; rw [hQ.1 _ _ (Fin.lt_last_iff_ne_last.2 hl), zero_mul]
  · simp

theorem Xof_mul_entry (hU : IsUT U) (hD : IsUnit (Dof M).det) :
    Xof (U * M) (Fin.last m) 0 = Xof M (Fin.last m) 0 + Bof U (Fin.last m) 0 := by
  rw [Xof_mul M hU hD, Matrix.add_apply, mul_first_column_of_unit_column _ (inv_first_column_of_upper_triangular (Dof_isUT hU)), mul_first_column_of_unit_column _ (inv_first_column_of_upper_triangular (Dof_isUT hU)),
    lastRow_mul (Aof_isUT hU)]

theorem sd_blocks (U : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    sd U = sd (Aof U) + Bof U (Fin.last m) 0 + sd (Dof U) := by
  have e : ∀ f : Fin (m + r + 1 + 1) → R, ∑ i, f i = ∑ a, f ((eqv m r).symm a) := fun f =>
    (Equiv.sum_comp (eqv m r).symm f).symm
  rw [sd, e]
  simp only [Fintype.sum_sum_type]
  simp_rw [e, Fintype.sum_sum_type, eqv_symm_inl, eqv_symm_inr]
  have h2 : ∑ i : Fin (m + 1), ∑ j : Fin (r + 1),
      (if m + 1 + j.val = i.val + 1 then U ((eqv m r).symm (Sum.inl i)) ((eqv m r).symm (Sum.inr j)) else 0) =
      Bof U (Fin.last m) 0 := by
    rw [Finset.sum_eq_single (Fin.last m), Finset.sum_eq_single (0 : Fin (r + 1))]
    · rw [if_pos (by simp)]; rfl
    · intro j _ hj; rw [if_neg]; intro h; apply hj; ext; simp at h ⊢; omega
    · simp
    · intro i _ hi; refine Finset.sum_eq_zero fun j _ => ?_; rw [if_neg]; intro h; apply hi; ext; simp; omega
    · simp
  have h3 : ∑ i : Fin (r + 1), ∑ j : Fin (m + 1),
      (if j.val = m + 1 + i.val + 1 then U ((eqv m r).symm (Sum.inr i)) ((eqv m r).symm (Sum.inl j)) else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]; omega
  have h4 : ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
      (if m + 1 + j.val = m + 1 + i.val + 1 then U ((eqv m r).symm (Sum.inr i)) ((eqv m r).symm (Sum.inr j)) else 0) =
      sd (Dof U) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j.val = i.val + 1
    · rw [if_pos (by omega), if_pos h]; rfl
    · rw [if_neg (by omega), if_neg h]
  simp only [Finset.sum_add_distrib]
  rw [h2, h3, h4, zero_add]
  rfl

end Alg

end GlobalTheory.SchurEquiv

namespace GlobalTheory.SchurEquiv

open Matrix

section Adelic

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem mkGL_mem_NA {V : Matrix (Fin k) (Fin k) (Ad E)} (hV : IsUT V) : mkGL V ∈ GlobalTheory.JSW.NA (E := E) (a := k) := by
  have hu : IsUnit V.det := by rw [det_of_isUT hV]; exact isUnit_one
  refine ⟨fun i j h => ?_, fun i => ?_⟩ <;> rw [coe_mkGL hu]
  · exact hV.1 i j h
  · exact hV.2 i

theorem mkGL_mul {V S : Matrix (Fin k) (Fin k) (Ad E)} (hV : IsUT V) (hS : IsUnit S.det) :
    mkGL (V * S) = mkGL V * mkGL S := by
  have hu : IsUnit V.det := by rw [det_of_isUT hV]; exact isUnit_one
  have hVS : IsUnit (V * S).det := by rw [det_mul]; exact hu.mul hS
  apply Units.ext
  rw [Units.val_mul, coe_mkGL hVS, coe_mkGL hu, coe_mkGL hS]

theorem psi_add (a b : Ad E) : psi (a + b) = psi a * psi b := by
  simp [psi, AddChar.map_add_eq_mul]

theorem psiN_mkGL {V : Matrix (Fin k) (Fin k) (Ad E)} (hV : IsUT V) : GlobalTheory.JSW.psiN (mkGL V) = psi (sd V) := by
  have hu : IsUnit V.det := by rw [det_of_isUT hV]; exact isUnit_one
  rw [GlobalTheory.JSW.psiN, superDiag_eq_sd, coe_mkGL hu]; rfl

theorem isUnit_Scof {m r : ℕ} (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (hM : IsUnit M.det)
    (hD : IsUnit (Dof M).det) : IsUnit (Scof M).det := by
  letI := (Dof M).invertibleOfIsUnitDet hD
  have h1 : M.det = (Dof M).det * (Scof M).det := by
    have e : (blk M).det = M.det := Matrix.det_submatrix_equiv_self _ _
    rw [← e, blk_eq, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]; rfl
  rw [h1] at hM
  exact isUnit_of_mul_isUnit_right hM

end Adelic

theorem schurF_equivariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), ∀ g, b₁ (u * g) = GlobalTheory.JSW.psiN u * b₁ g) → ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, schurF β b₁ χ (u * g) = GlobalTheory.JSW.psiN u * schurF β b₁ χ g := by
  intro E _ _ _ m r β b₁ χ hβ hb u hu g
  have hU : IsUT (u : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) := hu
  have hM : IsUnit (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  set M := (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) with hMdef
  set U := (u : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) with hUdef
  unfold schurF
  rw [Units.val_mul]
  by_cases hD : IsUnit (Dof M).det
  · rw [if_pos ((isUnit_Dof_mul_iff M hU).2 hD), if_pos hD, Xof_mul_entry M hU hD, Scof_mul M hU hD, Dof_mul M hU,
      Yof_mul M hU, mkGL_mul (Aof_isUT hU) (isUnit_Scof M hM hD), mkGL_mul (Dof_isUT hU) hD,
      hβ _ (mkGL_mem_NA (Aof_isUT hU)), hb _ (mkGL_mem_NA (Dof_isUT hU)), psiN_mkGL (Aof_isUT hU),
      psiN_mkGL (Dof_isUT hU)]
    have h : GlobalTheory.JSW.psiN u = psi (sd (Aof U)) * psi (Bof U (Fin.last m) 0) * psi (sd (Dof U)) := by
      rw [GlobalTheory.JSW.psiN, superDiag_eq_sd, sd_blocks, ← psi_add, ← psi_add]; rfl
    rw [h, psi_add]; ring
  · rw [if_neg (mt (isUnit_Dof_mul_iff M hU).1 hD), if_neg hD, mul_zero]

end GlobalTheory.SchurEquiv
end
end
