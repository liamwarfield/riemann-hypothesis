module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryArchimedean
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitMulClauseOfGeneratesIffNonzero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionSubgroupCocompactHaarFundamentalDoma
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdArgRealUnitEqOneStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JKInvOfTriv
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial

namespace GlobalTheory.ExpFrame.HeckeMod

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)
  (jK : F.K →* alg F.O N lam) (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W]
  [IsScalarTower F.O (alg F.O N lam) W]

theorem mem_forms {f : F.G → W} : f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W ↔
    ∀ (γ : F.Γ) (g : F.G) (κ : F.K), f ((γ : F.G) * g * κ) = jK κ⁻¹ • f g := Iff.rfl


variable {F lam jK} in
theorem jK_eq (hJ : F.IsJ lam jK) {κ κ' : F.K} (h1 : F.kap κ' = F.kap κ) (h2 : F.chi κ' = F.chi κ) : jK κ' = jK κ := by
  rw [hJ κ', hJ κ, h1, h2]

variable {F lam jK} in
theorem jK_inv_congr {κ κ' : F.K} (h : jK κ' = jK κ) : jK κ'⁻¹ = jK κ⁻¹ := by
  have e1 : jK κ'⁻¹ * jK κ' = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have e2 : jK κ * jK κ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc jK κ'⁻¹ = jK κ'⁻¹ * (jK κ * jK κ⁻¹) := by rw [e2, mul_one]
    _ = (jK κ'⁻¹ * jK κ') * jK κ⁻¹ := by rw [h, mul_assoc]
    _ = jK κ⁻¹ := by rw [e1, one_mul]

theorem grpA_one : grpA F.O N lam 1 = 1 := Subtype.ext (by simp [grpA, grp])


variable {F lam jK} in
theorem jK_inv_of_triv (hJ : F.IsJ lam jK) {κ : F.K} (h1 : F.kap κ = 1) (h2 : F.chi κ = 1) : jK κ⁻¹ = 1 := by
  have : jK κ = jK 1 := by rw [hJ κ, h1, h2, map_one, grpA_one]; simp
  rw [jK_inv_congr this, inv_one, map_one]

def heckeFn (i : F.I) (f : F.G → W) : F.G → W := fun g => F.cst i • ∑ s ∈ F.tr i, f (g * s)

variable {F lam jK W}

theorem heckeFn_mem (hOk : F.Ok) (hJ : F.IsJ lam jK) (i : F.I) {f : F.G → W}
    (hf : f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W) : heckeFn F W i f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W := by
  rw [mem_forms] at hf ⊢
  intro γ g κ
  obtain ⟨σ, hσ⟩ := hOk.perm i κ
  have key : ∀ s : F.tr i, f ((γ : F.G) * g * κ * s) = jK κ⁻¹ • f (g * (σ s : F.G)) := by
    intro s
    obtain ⟨κ', h1, h2, h3⟩ := hσ s
    have e : (γ : F.G) * g * κ * s = γ * (g * σ s) * κ' := by
      rw [mul_assoc ((γ : F.G) * g) (κ : F.G) (s : F.G), h1]; simp only [mul_assoc]
    rw [e, hf γ (g * σ s) κ', jK_inv_congr (jK_eq hJ h2 h3)]
  simp only [heckeFn]
  rw [← Finset.sum_coe_sort (F.tr i), ← Finset.sum_coe_sort (F.tr i)]
  simp_rw [key]
  rw [← Finset.smul_sum, Equiv.sum_comp σ (fun s : F.tr i => f (g * (s : F.G))), smul_comm]

theorem heckeFn_comm (hOk : F.Ok) (hJ : F.IsJ lam jK) (i j : F.I) {f : F.G → W}
    (hf : f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W) :
    heckeFn F W i (heckeFn F W j f) = heckeFn F W j (heckeFn F W i f) := by
  rw [mem_forms] at hf
  funext g
  obtain ⟨σ, hσ⟩ := hOk.comm i j
  have key : ∀ x : F.tr i × F.tr j, f (g * x.1 * x.2) = f (g * (σ x).1 * (σ x).2) := by
    intro x
    obtain ⟨hK, h1, h2⟩ := hσ x
    have e : g * x.1 * x.2 = ((1 : F.Γ) : F.G) * (g * (σ x).1 * (σ x).2) * (⟨_, hK⟩ : F.K) := by
      simp only [OneMemClass.coe_one, one_mul, mul_assoc, mul_inv_cancel_left]
    rw [e, hf, jK_inv_of_triv hJ h1 h2, one_smul]
  have hsum : ∀ (a b : F.I), heckeFn F W a (heckeFn F W b f) g =
      F.cst a • F.cst b • ∑ x : F.tr a × F.tr b, f (g * x.1 * x.2) := by
    intro a b
    simp only [heckeFn, Fintype.sum_prod_type, Finset.smul_sum]
    rw [← Finset.sum_coe_sort (F.tr a)]
    refine Fintype.sum_congr _ _ fun s => ?_
    rw [← Finset.sum_coe_sort (F.tr b)]
  rw [hsum, hsum, smul_comm (F.cst i) (F.cst j)]
  congr 2
  rw [Fintype.sum_congr _ _ key, Equiv.sum_comp σ (fun y : F.tr j × F.tr i => f (g * y.1 * y.2))]

end GlobalTheory.ExpFrame.HeckeMod

namespace GlobalTheory.ExpFrame.HeckeMod

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} {F : Frame l ι N} {lam : ι → ℕ → ℕ}
  {jK : F.K →* alg F.O N lam} {W : Type} [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W]
  [IsScalarTower F.O (alg F.O N lam) W]

def op (hOk : F.Ok) (hJ : F.IsJ lam jK) (i : F.I) :
    Module.End F.O (Forms F.O (A := alg F.O N lam) F.Γ jK W) where
  toFun f := ⟨heckeFn F W i f, heckeFn_mem hOk hJ i f.2⟩
  map_add' f f' := by
    ext g
    simp [heckeFn, Finset.sum_add_distrib, smul_add]
  map_smul' c f := by
    ext g
    simp [heckeFn, Finset.smul_sum, smul_comm (F.cst i) c]

theorem op_comm (hOk : F.Ok) (hJ : F.IsJ lam jK) (i j : F.I) :
    (op (W := W) hOk hJ i) * op hOk hJ j = op hOk hJ j * op hOk hJ i := by
  ext f : 1
  exact Subtype.ext (heckeFn_comm hOk hJ i j f.2)

end GlobalTheory.ExpFrame.HeckeMod

namespace GlobalTheory.ExpFrame.HeckeMod

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} {F : Frame l ι N} {lam : ι → ℕ → ℕ}
  {jK : F.K →* alg F.O N lam} {W : Type} [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W]
  [IsScalarTower F.O (alg F.O N lam) W]

open scoped IsMulCommutative in
def heckeAlg (hOk : F.Ok) (hJ : F.IsJ lam jK) : F.T →ₐ[F.O] Module.End F.O (Forms F.O (A := alg F.O N lam) F.Γ jK W) :=
  letI : IsMulCommutative (Algebra.adjoin F.O (Set.range (op (W := W) hOk hJ))) :=
    Algebra.isMulCommutative_adjoin F.O (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact op_comm hOk hJ i j)
  (Algebra.adjoin F.O (Set.range (op (W := W) hOk hJ))).val.comp
    (MvPolynomial.aeval fun i => ⟨op hOk hJ i, Algebra.subset_adjoin ⟨i, rfl⟩⟩)

theorem heckeAlg_X (hOk : F.Ok) (hJ : F.IsJ lam jK) (i : F.I) : heckeAlg (W := W) hOk hJ (X i) = op hOk hJ i := by
  simp [heckeAlg]

theorem hecke_module : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam), F.Ok → F.IsJ lam jK → ∀ (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W] [IsScalarTower F.O (alg F.O N lam) W], ∃ (_ : Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)) (_ : IsScalarTower F.O F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)), F.IsHecke lam jK W := by
  intro l _ ι _ _ N F lam jK hOk hJ W _ _ _ _
  letI inst : Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W) := Module.compHom _ (heckeAlg (W := W) hOk hJ).toRingHom
  refine ⟨inst, ⟨fun c t f => ?_⟩, fun c f => ?_, fun i f g => ?_⟩
  · change heckeAlg hOk hJ (c • t) f = c • heckeAlg hOk hJ t f
    rw [map_smul, LinearMap.smul_apply]
  · change heckeAlg hOk hJ (C c) f = c • f
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply]
  · change ((heckeAlg hOk hJ (X i) f : Forms F.O (A := alg F.O N lam) F.Γ jK W) : F.G → W) g = _
    rw [heckeAlg_X]
    rfl

end GlobalTheory.ExpFrame.HeckeMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDdREqOfEquiv
open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

open Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.ConjCrys

section DdR

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem ddR_map (f : V →ₗ[LL] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    ∀ x ∈ DdR PD ρ, GlobalTheory.HTW.SumJumps.ext1 Qp BdR f x ∈ DdR PD ρ' := by
  intro x hx
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  have := hx g
  unfold actVdR at this ⊢
  rw [GlobalTheory.HTW.SumJumps.ext1_comm f (ρ g) (ρ' g) (hf g), this]

theorem finrank_ddR_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    finrank LL (DdR PD ρ) = finrank LL (DdR PD ρ') :=
  GlobalTheory.HTW.Rec.finrank_eq_of_equiv_tensor e _ _ (ddR_map PD e.toLinearMap he)
    (ddR_map PD e.symm.toLinearMap (GlobalTheory.HTW.Rec.symm_equivariant e he))

end DdR

section Matrix

theorem mapRep_conj {Γ : Type} [Group Γ] {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (f : R →+* S)
    (M : GL (Fin a) R) (ρ : Γ →* GL (Fin a) R) :
    mapRep f ((MulAut.conj M).toMonoidHom.comp ρ) =
      (MulAut.conj (Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) R →+* Matrix (Fin a) (Fin a) S).toMonoidHom M)).toMonoidHom.comp
        (mapRep f ρ) := by
  ext g : 1
  simp [mapRep, MulAut.conj_apply, map_mul, map_inv]

variable {l : ℕ} [Fact l.Prime]

def glOf {n : ℕ} (L : FinExt l) (A : GL (Fin n) (Om l))
    (hA : ∀ i j, (A : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1 ∧
      ((A⁻¹ : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1) : GL (Fin n) ↥L.1 where
  val := Matrix.of fun i j => ⟨_, (hA i j).1⟩
  inv := Matrix.of fun i j => ⟨_, (hA i j).2⟩
  val_inv := by
    apply Matrix.map_injective (f := (algebraMap ↥L.1 (Om l))) (algebraMap ↥L.1 (Om l)).injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact A.mul_inv
  inv_val := by
    apply Matrix.map_injective (f := (algebraMap ↥L.1 (Om l))) (algebraMap ↥L.1 (Om l)).injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact A.inv_mul

theorem map_glOf {n : ℕ} (L : FinExt l) (A : GL (Fin n) (Om l))
    (hA : ∀ i j, (A : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1 ∧
      ((A⁻¹ : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1) :
    Units.map ((algebraMap ↥L.1 (Om l)).mapMatrix :
      Matrix (Fin n) (Fin n) ↥L.1 →+* Matrix (Fin n) (Fin n) (Om l)).toMonoidHom (glOf L A hA) = A := by
  ext i j
  rfl

end Matrix

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  (Bw : LocBridge l E Ω Gw O) {m : ℕ}

def linOf {L : Type} [Field L] (M : GL (Fin m) L) : (Fin m → L) ≃ₗ[L] (Fin m → L) :=
  LinearEquiv.ofLinear (Matrix.toLin' (M : Matrix (Fin m) (Fin m) L))
    (Matrix.toLin' ((M⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L))
    (by rw [← Matrix.toLin'_mul, M.mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, M.inv_mul, Matrix.toLin'_one])

theorem linOf_repE (L : FinExt l) (M : GL (Fin m) ↥L.1) (r : ↥Gw →* GL (Fin m) ↥L.1) (g) (v : Fin m → ↥L.1) :
    linOf M (Bw.repE L ((MulAut.conj M⁻¹).toMonoidHom.comp r) g v) = Bw.repE L r g (linOf M v) := by
  simp only [linOf, LocBridge.repE, LinearEquiv.ofLinear_apply, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.coeHom_apply, Matrix.toLin'_apply, inv_inv, Units.val_mul]
  erw [Matrix.toLinAlgEquiv'_apply, Matrix.toLinAlgEquiv'_apply]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, M.mul_inv, Matrix.one_mul]

theorem local_conj (L : FinExt l) (M : GL (Fin m) ↥L.1) (r : ↥Gw →* GL (Fin m) ↥L.1) :
    (Bw.IsCrysE P L r → Bw.IsCrysE P L ((MulAut.conj M⁻¹).toMonoidHom.comp r)) ∧
    (Bw.IsdRE P L r → Bw.IsdRE P L ((MulAut.conj M⁻¹).toMonoidHom.comp r)) ∧
    ∀ τ a, Bw.multE P L ((MulAut.conj M⁻¹).toMonoidHom.comp r) τ a = Bw.multE P L r τ a := by
  have he := linOf_repE Bw L M r
  refine ⟨fun h => GlobalTheory.HTW.Rec.isCrys_of_equiv _ (linOf M) he h, fun h => ?_, fun τ a =>
    GlobalTheory.HTW.Rec.multV_eq_of_equiv _ (linOf M) he τ a⟩
  unfold LocBridge.IsdRE at h ⊢
  rw [finrank_ddR_eq_of_equiv _ (linOf M) he, h]

variable {P Bw}

theorem exists_conj_model {r : ↥Gw →* GL (Fin m) (Om l)} (A : GL (Fin m) (Om l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1)
    {LL' : FinExt l} {r' : ↥Gw →* GL (Fin m) ↥LL'.1} (hm : GlobalTheory.Pst.IsModel Bw r LL' r') :
    ∃ (h : LL'.1 ≤ (GlobalTheory.Pst.supExt LL' K).1) (M : GL (Fin m) ↥(GlobalTheory.Pst.supExt LL' K).1),
      GlobalTheory.Pst.IsModel Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) (GlobalTheory.Pst.supExt LL' K)
        ((MulAut.conj M⁻¹).toMonoidHom.comp (mapRep (IntermediateField.inclusion h).toRingHom r')) := by
  have h1 : LL'.1 ≤ (GlobalTheory.Pst.supExt LL' K).1 := le_sup_left
  have h2 : K.1 ≤ (GlobalTheory.Pst.supExt LL' K).1 := le_sup_right
  have hA' : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ (GlobalTheory.Pst.supExt LL' K).1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ (GlobalTheory.Pst.supExt LL' K).1 :=
    fun i j => ⟨h2 (hA i j).1, h2 (hA i j).2⟩
  have hm2 := hm.enlarge h1
  refine ⟨h1, glOf _ A hA', hm2.1, ?_⟩
  rw [mapRep_conj, hm2.2, map_inv, map_glOf]

theorem isCrysAt_conj {r : ↥Gw →* GL (Fin m) (Om l)} (A : GL (Fin m) (Om l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1)
    (hr : GlobalTheory.Pst.IsCrysAt P Bw r) : GlobalTheory.Pst.IsCrysAt P Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) := by
  obtain ⟨LL', r', hm, hc⟩ := hr
  obtain ⟨h, M, hM⟩ := exists_conj_model A K hA hm
  exact ⟨_, _, hM, (local_conj P Bw _ M _).1 ((GlobalTheory.Pst.local_ext P Bw h r').1.2 hc)⟩

theorem isJumpsAt_conj {r : ↥Gw →* GL (Fin m) (Om l)} (A : GL (Fin m) (Om l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1)
    {τ : E →+* Om l} {J : Multiset ℤ}
    (hr : GlobalTheory.Pst.IsJumpsAt P Bw r τ J) : GlobalTheory.Pst.IsJumpsAt P Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) τ J := by
  obtain ⟨LL', r', hm, hdR, τ', hI, hc⟩ := hr
  obtain ⟨h, M, hM⟩ := exists_conj_model A K hA hm
  obtain ⟨-, hdR2, -, hmult⟩ := GlobalTheory.Pst.local_ext P Bw h r'
  obtain ⟨-, hdR3, hmult3⟩ := local_conj P Bw _ M (mapRep (IntermediateField.inclusion h).toRingHom r')
  refine ⟨_, _, hM, hdR3 (hdR2.2 hdR), (IntermediateField.inclusion h).comp τ', fun x => hI x, fun n => ?_⟩
  rw [hc n, hmult3, hmult]

end Local

end GlobalTheory.ConjCrys


open GlobalTheory.ConjCrys in
theorem GlobalTheory.crysWith_conj : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) (A : GL (Fin n) (PadicAlgCl l)) (K : FinExt l) (Jm : (E →+* PadicAlgCl l) → Multiset ℤ), (∀ i j, (A : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ K.1 ∧ ((A⁻¹ : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ K.1) → CrysWith r Jm → CrysWith ((MulAut.conj A⁻¹).toMonoidHom.comp r) Jm := by
  intro E Ω _ _ _ _ _ l _ n r A K Jm hA hr
  obtain ⟨hcont, hloc⟩ := hr
  refine ⟨?_, fun P AI hT w B hB O _ _ _ Bw hInd => ?_⟩
  · change Continuous fun g => A⁻¹ * r g * A⁻¹⁻¹
    exact (continuous_const.mul hcont).mul continuous_const
  · obtain ⟨h1, h2⟩ := hloc P AI hT w B hB O Bw hInd
    have e : ((MulAut.conj A⁻¹).toMonoidHom.comp r).comp (Dec (F := E) B).subtype =
        (MulAut.conj A⁻¹).toMonoidHom.comp (r.comp (Dec (F := E) B).subtype) := MonoidHom.comp_assoc _ _ _
    rw [e]
    refine ⟨isCrysAt_conj (r := r.comp (Dec (F := E) B).subtype) A K hA h1, fun τ LL' τ' hI => ?_⟩
    exact isJumpsAt_conj (r := r.comp (Dec (F := E) B).subtype) A K hA (h2 τ LL' τ' hI)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOddPrimeGtTwoBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAlgCharEqArgMulAbs
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAlgCharEqArgMulAbs
open NumberField

namespace GlobalTheory.Div.CMAlgChar

theorem place_factor (z : ℂ) (hz : z ≠ 0) (a b w0 : ℤ) (hab : a + b = w0) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 * a - w0) *
      (((‖z‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ) *
        ((‖(starRingEnd ℂ) z‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ)) =
      z ^ a * (starRingEnd ℂ z) ^ b := by
  rw [Complex.norm_conj]
  set r : ℂ := ((‖z‖ : ℝ) : ℂ) with hr
  have hr0 : r ≠ 0 := by simp [hr, hz]
  rw [← Complex.cpow_add _ _ hr0]
  have hsum : ((((w0 : ℝ) / 2 : ℝ)) : ℂ) + ((((w0 : ℝ) / 2 : ℝ)) : ℂ) = ((w0 : ℤ) : ℂ) := by
    push_cast; ring
  rw [hsum, Complex.cpow_intCast]
  have hc : starRingEnd ℂ z = r ^ 2 / z := by
    rw [eq_div_iff hz, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hr]
    push_cast; rfl
  rw [hc]
  subst hab
  have he : 2 * a - (a + b) = a - b := by ring
  rw [he, div_zpow, div_zpow, zpow_sub₀ hz, zpow_sub₀ hr0, zpow_add₀ hr0, pow_two, mul_zpow]
  field_simp

theorem fiber_eq {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] [DecidableEq (E →+* ℂ)]
    [DecidableEq (InfinitePlace E)]
    (w : InfinitePlace E) :
    (Finset.univ.filter fun φ : E →+* ℂ => InfinitePlace.mk φ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  have h1 : InfinitePlace.mk φ = w ↔ InfinitePlace.mk φ = InfinitePlace.mk w.embedding := by
    rw [w.mk_embedding]
  rw [h1, InfinitePlace.mk_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right; rw [← h, ComplexEmbedding.involutive_conjugate E]
  · rintro (h | h)
    · exact Or.inl h
    · right; rw [h, ComplexEmbedding.involutive_conjugate E]

theorem embedding_ne_conjugate {E : Type} [Field E] [IsTotallyComplex E] (w : InfinitePlace E) :
    w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
  intro h
  have hc := IsTotallyComplex.isComplex w
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff,
    ComplexEmbedding.isReal_iff] at hc
  exact hc h.symm

theorem algChar_eq_arg_mul_abs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (n : (E →+* ℂ) → ℤ) (w0 : ℤ),
    (∀ φ, n φ + n (NumberField.ComplexEmbedding.conjugate φ) = w0) → ∀ k : E, k ≠ 0 →
    (∏ w : InfinitePlace E, (w.embedding k / ((‖w.embedding k‖ : ℝ) : ℂ)) ^ (2 * n w.embedding - w0)) *
      ∏ φ : E →+* ℂ, ((‖φ k‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ) = ∏ φ : E →+* ℂ, φ k ^ n φ := by
  intro E _ _ _ n w0 hn k hk
  classical
  have hfib : ∀ f : (E →+* ℂ) → ℂ, ∏ φ, f φ =
      ∏ w : InfinitePlace E, (f w.embedding * f (ComplexEmbedding.conjugate w.embedding)) := by
    intro f
    rw [← Finset.prod_fiberwise Finset.univ (fun φ => InfinitePlace.mk φ) f]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [fiber_eq w, Finset.prod_pair (embedding_ne_conjugate w)]
  rw [hfib (fun φ => ((‖φ k‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ)),
    hfib (fun φ => φ k ^ n φ), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hz : w.embedding k ≠ 0 := (map_ne_zero _).2 hk
  simp only [ComplexEmbedding.conjugate_coe_eq]
  exact place_factor _ hz _ _ _ (hn _)

end GlobalTheory.Div.CMAlgChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAlgCharEqArgMulAbsStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_algChar_eq_arg_mul_abs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : (E →+* ℂ) → ℤ) (w0 : ℤ),
    (∀ φ, n φ + n (NumberField.ComplexEmbedding.conjugate φ) = w0) → ∀ k : E, k ≠ 0 →
    (∏ w : InfinitePlace E, (w.embedding k / ((‖w.embedding k‖ : ℝ) : ℂ)) ^ (2 * n w.embedding - w0)) *
      ∏ φ : E →+* ℂ, ((‖φ k‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ) = ∏ φ : E →+* ℂ, φ k ^ n φ := by
  first | exact @GlobalTheory.Div.CMAlgChar.algChar_eq_arg_mul_abs | exact GlobalTheory.Div.CMAlgChar.algChar_eq_arg_mul_abs | (intros; apply GlobalTheory.Div.CMAlgChar.algChar_eq_arg_mul_abs <;> assumption)
end
end

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.AlgCharUnr

theorem phase_prod_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] {q : ℕ} (hq : q.Prime) (hq2 : 2 < q)
    (ht : ¬ q ∣ Nat.card (Units.torsion E)) (u : (𝓞 E)ˣ) (hu : (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)})
    (m : InfinitePlace E → ℤ) (w0 : ℤ) (hm : ∀ w, ∃ a, m w = 2 * a - w0) :
    ∏ w : InfinitePlace E, (w.embedding ((u : 𝓞 E) : E) / ((‖w.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) ^ m w = 1 := by
  have hr := GlobalTheory.T.unit_real_of_sub_one_mem_span_prime E q hq ht u hu
  have hs := GlobalTheory.T.prod_arg_real_unit_eq_one' E q hq hq2 u hu hr
  have hsq : ∀ w : InfinitePlace E,
      (w.embedding ((u : 𝓞 E) : E) / ((‖w.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) ^ m w =
      ((w.embedding ((u : 𝓞 E) : E) / ((‖w.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) ^ w0)⁻¹ := fun w => by
    set z := w.embedding ((u : 𝓞 E) : E) with hz
    have h0 : z ≠ 0 := by rw [hz, map_ne_zero]; exact Units.coe_ne_zero u
    have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
    have hzr : starRingEnd ℂ z = z := hr _
    have h2 : (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 : ℤ) = 1 := by
      rw [zpow_two, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hn hn)]
      have e : ((‖z‖ : ℝ) : ℂ) * ((‖z‖ : ℝ) : ℂ) = z * starRingEnd ℂ z := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
      rw [e, hzr]
    obtain ⟨a, ha⟩ := hm w
    have hne : z / ((‖z‖ : ℝ) : ℂ) ≠ 0 := div_ne_zero h0 hn
    rw [ha, sub_eq_add_neg, zpow_add₀ hne, zpow_mul, h2, one_zpow, one_mul, zpow_neg]
  rw [Finset.prod_congr rfl fun w _ => hsq w, Finset.prod_inv_distrib, Finset.prod_zpow, hs, one_zpow, inv_one]

theorem exists_odd_prime_gt_two_bounds (l t : ℕ) : ∃ q : ℕ, q.Prime ∧ 2 < q ∧ l < q ∧ t < q := by
  obtain ⟨q, hq, hp⟩ := Nat.exists_infinite_primes (max (max 3 (l + 1)) (t + 1))
  exact ⟨q, hp, by omega, by omega, by omega⟩

theorem exists_algChar_unr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime → ∀ (n : (E →+* ℂ) → ℤ) (w0 : ℤ), (∀ φ, n φ + n (NumberField.ComplexEmbedding.conjugate φ) = w0) → ∃ χ : HChar E, IsAlgPos χ n ∧ ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → χ.UnrAt w := by
  intro E _ _ _ l hl n w0 hn
  classical
  obtain ⟨q, hq, hq2, hlq, htq⟩ := exists_odd_prime_gt_two_bounds l (Nat.card (Units.torsion E))
  have ht : ¬ q ∣ Nat.card (Units.torsion E) := fun h =>
    absurd (Nat.le_of_dvd Nat.card_pos h) (by omega)
  set 𝔪 : Ideal (𝓞 E) := Ideal.span {((q : ℕ) : 𝓞 E)} with h𝔪
  have hq0 : ((q : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have hm : 𝔪 ≠ ⊥ := by rw [h𝔪, Ne, Ideal.span_singleton_eq_bot]; exact hq0
  let m : InfinitePlace E → ℤ := fun w => 2 * n w.embedding - w0
  have hbij : Function.Bijective fun w : InfinitePlace E => InfinitePlace.mk w.embedding := by
    simp only [InfinitePlace.mk_embedding]
    exact Function.bijective_id
  obtain ⟨ψ, hψ, hψu, hψi, -, hψS, hψd⟩ := GlobalTheory.ModelChar.exists_modelChar E (InfinitePlace E) (fun w => w.embedding)
    hbij m ∅ (fun _ => 1) (by simp)
  have hinf := (GlobalTheory.InfTypeLocal.infType_iff_local E (InfinitePlace E) (fun w => w.embedding) hbij ψ hψ _).2 hψi
  let U : Subgroup (Neutral.B1.Ideles E) := GlobalTheory.Mem.Chr.unitIdl E ⊓ GlobalTheory.RayChar.congrIdl 𝔪
  have hU : IsOpen (U : Set (Neutral.B1.Ideles E)) :=
    GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.inter (GlobalTheory.RayChar.isOpen_congrIdl hm)
  have hmem : ∀ k : Eˣ, infDiag k ∈ U := fun k => by
    refine ⟨?_, (GlobalTheory.RayChar.mem_congrIdl hm).2 fun v _ => ?_⟩
    · unfold infDiag
      rw [MonoidHom.finsetProd_apply]
      exact Subgroup.prod_mem _ fun w _ => GlobalTheory.Mem.Chr.AntiExist.inf_mem w _
    · have h1 : GlobalTheory.RayChar.cmp (infDiag k) v = 1 :=
        congrArg Units.val (GlobalTheory.ModelChar.finEv_infDiag v k)
      rw [h1, sub_self, map_zero]
      exact zero_le
  obtain ⟨χ1, hχc, -, hχU, hχd⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (Neutral.B1.Ideles E) Eˣ U hU
    (GlobalTheory.Mem.Chr.diagUnits E) 1 ψ hψ hψu (fun _ => by simp) (fun k hk => by
      obtain ⟨u, hu⟩ := GlobalTheory.DefU.NonTriv.exists_unit k hk.1
      have hu1 : (u : 𝓞 E) - 1 ∈ 𝔪 := (GlobalTheory.RayChar.mem_iff_at hm _).2 fun v hv => by
        rw [GlobalTheory.RayChar.at'_sub_one]
        have h2 := (GlobalTheory.RayChar.mem_congrIdl hm).1 hk.2 v hv
        rw [GlobalTheory.RayChar.cmp_diag, ← hu] at h2
        exact h2
      show (1 : ℂˣ) = ψ (GlobalTheory.Mem.Chr.diagUnits E k)
      rw [hψd, Finset.prod_empty, mul_one]
      refine (Units.ext ?_).symm
      change ((ψ (infDiag k) : ℂˣ) : ℂ) = ((1 : ℂˣ) : ℂ)
      rw [hinf k, Units.val_one, ← hu]
      exact phase_prod_eq_one hq hq2 ht u hu1 m w0 fun w => ⟨n w.embedding, rfl⟩)
  let χ0 : HChar E := ⟨χ1, hχc, fun k => by change χ1 (GlobalTheory.Mem.Chr.diagUnits E k) = 1; rw [hχd]; rfl⟩
  let s : ℝ := (w0 : ℝ) / 2
  let ν : HChar E := GlobalTheory.Mem.Chr.CharModel.absChar E (s : ℂ)
  have hν : ν.IsAbsPow s := GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow s
  refine ⟨χ0 * ν, fun k _ => ?_, fun w hw x hx => ?_⟩
  · have h1 : ((χ0.inf k : ℂˣ) : ℂ) = ∏ w : InfinitePlace E, (w.embedding (k : E) / ((‖w.embedding (k : E)‖ : ℝ) : ℂ)) ^ m w := by
      show ((χ1 (infDiag k) : ℂˣ) : ℂ) = _
      rw [hχU _ (hmem k)]
      exact hinf k
    rw [HChar.inf_mul, Units.val_mul, h1, hν.2.2 k]
    exact GlobalTheory.T.cm_algChar_eq_arg_mul_abs E n w0 hn (k : E) k.ne_zero
  · have hwq : ¬ w.asIdeal ∣ 𝔪 := by
      rw [h𝔪, Ideal.dvd_span_singleton]
      intro hqw
      have hc : IsCoprime ((l : ℕ) : 𝓞 E) ((q : ℕ) : 𝓞 E) :=
        Nat.Coprime.cast ((Nat.coprime_primes hl hq).2 hlq.ne)
      obtain ⟨a, b, hab⟩ := hc
      apply w.isPrime.ne_top
      rw [Ideal.eq_top_iff_one, ← hab]
      exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw) (w.asIdeal.mul_mem_left _ hqw)
    change χ0.loc w x * ν.loc w x = 1
    rw [hν.1 w x hx, mul_one]
    show χ1 (GlobalTheory.Mem.Chr.localIdele E w x) = 1
    rw [hχU _ ⟨GlobalTheory.RayChar.local_mem_unitIdl hx, GlobalTheory.RayChar.local_mem_congrIdl hwq x⟩]
    exact hψS w (Finset.notMem_empty w) x

end GlobalTheory.AlgCharUnr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGaussianRealIsometryNoFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGaussianRealIsometryNoFixed
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatAut.RealInt

open GlobalTheory.RealWeil

section Mat

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def expM (H s g : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • ((g - 1)ᴴ * (H * s) * (g - 1) - H * g + (H * g)ᴴ)

theorem expM_herm {H s g : Matrix ι ι ℂ} (hQ : (H * s).PosDef) (hd : (g - 1).det ≠ 0) :
    (expM H s g + (expM H s g)ᴴ).PosDef := by
  have e : expM H s g + (expM H s g)ᴴ = (g - 1)ᴴ * (H * s) * (g - 1) := by
    have h1 : ((g - 1)ᴴ * (H * s) * (g - 1))ᴴ = (g - 1)ᴴ * (H * s) * (g - 1) := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hQ.1.eq]
      simp only [Matrix.mul_assoc]
    unfold expM
    rw [conjTranspose_smul, conjTranspose_add, conjTranspose_sub _ (H * g), h1, conjTranspose_conjTranspose]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this]
    module
  rw [e]
  exact hQ.conjTranspose_mul_mul_same
    (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd)))

theorem expM_mul {H s g g' : Matrix ι ι ℂ} (hH : Hᴴ = H) (hs : s * s = 1) (hg : gᴴ * H * g = H)
    (hc : s * g = g * s) (hi : g * g' = 1) :
    expM H s g * (g * ((1 / 2 : ℂ) • ((1 + s) * g') + (1 / 2 : ℂ) • (1 - s))) = -H * (g - 1) := by
  have hi' : g' * g = 1 := mul_eq_one_comm.1 hi
  have h1 : gᴴ * H = H * g' := by
    calc gᴴ * H = gᴴ * H * g * g' := by rw [Matrix.mul_assoc _ g, hi, Matrix.mul_one]
      _ = _ := by rw [hg]
  have hc' : g' * s = s * g' := by
    calc g' * s = g' * (s * g) * g' := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hi, Matrix.mul_one]
      _ = _ := by rw [hc, ← Matrix.mul_assoc, hi', Matrix.one_mul]
  have a1 : ∀ x : Matrix ι ι ℂ, gᴴ * (H * x) = H * (g' * x) := fun x => by rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have a2 : ∀ x : Matrix ι ι ℂ, g * (s * x) = s * (g * x) := fun x => by rw [← Matrix.mul_assoc, ← hc, Matrix.mul_assoc]
  have a3 : ∀ x : Matrix ι ι ℂ, g' * (s * x) = s * (g' * x) := fun x => by rw [← Matrix.mul_assoc, hc', Matrix.mul_assoc]
  have a4 : ∀ x : Matrix ι ι ℂ, s * (s * x) = x := fun x => by rw [← Matrix.mul_assoc, hs, Matrix.one_mul]
  have a5 : ∀ x : Matrix ι ι ℂ, g' * (g * x) = x := fun x => by rw [← Matrix.mul_assoc, hi', Matrix.one_mul]
  unfold expM
  simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hH, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
    a1, h1, a2, a3, a4, a5, hi, hi', ← hc, hc', hs, Matrix.neg_mul]
  module

theorem dot_expM {H s g : Matrix ι ι ℂ} (hH : Hᴴ = H) (hQ : (H * s).PosDef) (z : ι → ℂ) :
    star z ⬝ᵥ expM H s g *ᵥ z = Complex.I * ((-(star z ⬝ᵥ H *ᵥ (g *ᵥ z)).im : ℝ) : ℂ) +
      (1 / 2 : ℂ) * ((-(star (Complex.I • s *ᵥ (g *ᵥ z - z)) ⬝ᵥ H *ᵥ (g *ᵥ z - z)).im : ℝ) : ℂ) := by
  have e1 : (g - 1) *ᵥ z = g *ᵥ z - z := by rw [sub_mulVec, one_mulVec]
  have e2 : star z ⬝ᵥ ((g - 1)ᴴ * (H * s) * (g - 1)) *ᵥ z = star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z) := by
    rw [← e1, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  have e3 : star z ⬝ᵥ (H * g)ᴴ *ᵥ z = star (star z ⬝ᵥ H *ᵥ (g *ᵥ z)) := by
    rw [mulVec_mulVec, ← star_dotProduct_star, star_star, star_mulVec, ← dotProduct_mulVec]
  have e4 : ∀ w : ι → ℂ, star (Complex.I • s *ᵥ w) ⬝ᵥ H *ᵥ w = -Complex.I * (star w ⬝ᵥ (H * s) *ᵥ w) := fun w => by
    rw [star_smul, smul_dotProduct, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← hQ.1.eq, conjTranspose_mul, hH]
    simp
  have e5 : (star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z)).im = 0 :=
    (Complex.nonneg_iff.1 (hQ.posSemidef.dotProduct_mulVec_nonneg _)).2.symm
  unfold expM
  rw [smul_mulVec, add_mulVec, sub_mulVec, dotProduct_smul, dotProduct_add, dotProduct_sub, e2, e3, e4, ← mulVec_mulVec z H g]
  generalize star (g *ᵥ z - z) ⬝ᵥ (H * s) *ᵥ (g *ᵥ z - z) = u at e5
  generalize star z ⬝ᵥ H *ᵥ (g *ᵥ z) = w
  apply Complex.ext <;> simp [e5] <;> ring

theorem gauss_det {H s g g' : Matrix ι ι ℂ} (hH : Hᴴ = H) (hs : s * s = 1) (hQ : (H * s).PosDef) (hg : gᴴ * H * g = H)
    (hc : s * g = g * s) (hi : g * g' = 1) (hd : (g - 1).det ≠ 0) :
    (expM H s g).det⁻¹ * (g - 1).det = ((H * s).det.re⁻¹ : ℝ) * (-s).det * (g.det * dP s g') := by
  have h0 := (GlobalTheory.MatrixGaussian.integral_gaussian ι _ (expM_herm hQ hd)).1
  have h1 := congrArg det (expM_mul hH hs hg hc hi)
  rw [det_mul, det_mul, det_mul] at h1
  have h2 : (-H).det * (-s).det = (H * s).det := by rw [← det_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  have h3 := hQ.det_pos
  have h4 : ((H * s).det.re : ℂ) = (H * s).det := Complex.ext rfl (Complex.pos_iff.1 h3).2
  rw [Complex.ofReal_inv, h4]
  have h5 := h3.ne'
  unfold dP
  field_simp
  rw [← h2]
  linear_combination (-(-s).det) * h1

end Mat

section Coord

variable {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ}

def unvE (O : Type) (m n : ℕ) : ((Fin m × Fin n) × O → ℂ) ≃L[ℝ] (O → Fin m → Fin n → ℂ) :=
  ContinuousLinearEquiv.equivOfInverse unvecL vecL vecL_unv unv_vecL


omit [DecidableEq O] in
theorem integral_unv (f : (O → Fin m → Fin n → ℂ) → ℂ) (hf : Integrable fun z : (Fin m × Fin n) × O → ℂ => f (unvecL z)) :
    Integrable f ∧ ∃ c : ℝ, 0 < c ∧ ∫ v, f v = c * ∫ z : (Fin m × Fin n) × O → ℂ, f (unvecL z) := by
  haveI i1 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := inferInstance
  haveI i2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i3 : (volume : Measure (O → Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e := unvE O m n
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hm := Measure.isAddLeftInvariant_eq_smul (volume : Measure (O → Fin m → Fin n → ℂ)) (Measure.map e volume)
  have hp := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (volume : Measure (O → Fin m → Fin n → ℂ))
    (Measure.map e volume)
  generalize Measure.addHaarScalarFactor (volume : Measure (O → Fin m → Fin n → ℂ)) (Measure.map e volume) = c at hm hp
  refine ⟨?_, c, hp, ?_⟩
  · rw [hm]
    exact (he.integrable_map_iff.2 hf).smul_measure_nnreal
  · conv_lhs => rw [hm]
    rw [integral_smul_nnreal_measure, he.integral_map]
    rfl

theorem det_blk (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) :
    (blk b a).det = ∏ τ, (b τ ⊗ₖ (a τ)ᵀ).det := det_blockDiagonal _

theorem det_blk_sub_one (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) :
    (blk b a - 1).det = ∏ τ, (b τ ⊗ₖ (a τ)ᵀ - 1).det := by
  unfold RealWeil.blk
  rw [← blockDiagonal_one, ← blockDiagonal_sub, det_blockDiagonal]
  rfl

theorem inv_unitary {G a a' : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hi : a * a' = 1) (ha : aᴴ * G * a = G) :
    a * (G⁻¹ * aᴴ) = G⁻¹ := by
  have h1 : a'ᴴ * aᴴ = 1 := by rw [← conjTranspose_mul, hi, conjTranspose_one]
  have h2 : G * a = a'ᴴ * G := by
    conv_rhs => rw [← ha, Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine (inv_eq_right_inv ?_).symm
  rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc, ← Matrix.mul_assoc G, mul_nonsing_inv _ hG, Matrix.one_mul, h1]

end Coord

open Classical in
theorem gaussR_unv {D : D7} {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (hQ : (HM S T * blk sT sS).PosDef)
    (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (z : Ix S T → ℂ) : gaussR S T sS sT a b (unvecL z) =
      Complex.exp (-(Real.pi : ℂ) * (star z ⬝ᵥ expM (HM S T) (blk sT sS) (blk b a) *ᵥ z)) := by
  have e1 : actR S T a b (unvecL z) = unvecL (blk b a *ᵥ z) := funext fun τ => (cpt_blk b a z τ).symm
  have e2 : ∀ w : Ix S T → ℂ, jO S T sS sT (unvecL w) = unvecL (Complex.I • blk sT sS *ᵥ w) := fun w => funext fun τ => by
    show Complex.I • (sT τ * cpt w τ * sS τ) = _
    rw [← cpt_blk]
    rfl
  unfold gaussR
  rw [dot_expM HM_herm hQ, im_HM, im_HM, e1, ← map_sub, e2, ← Complex.exp_add, neg_neg, neg_neg]
  congr 1
  ring


open Classical in
theorem integral_gaussR : ∀ (D : D7) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∃ ε : ℂ, ∀ (a a' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (b b' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, a τ * a' τ = 1 ∧ b τ * b' τ = 1 ∧ (a τ)ᴴ * gramAt D S τ * a τ = gramAt D S τ ∧ (b τ)ᴴ * gramAt D T τ * b τ = gramAt D T τ ∧ sS τ * a τ = a τ * sS τ ∧ sT τ * b τ = b τ * sT τ ∧ (b τ ⊗ₖ (a τ)ᵀ - 1).det ≠ 0) → Integrable (gaussR S T sS sT a b) volume ∧ ∃ r : ℝ, 0 < r ∧ (∫ v, gaussR S T sS sT a b v) * ∏ τ, (b τ ⊗ₖ (a τ)ᵀ - 1).det = r * ε * ∏ τ, ((b τ ⊗ₖ (a τ)ᵀ).det * detPlus (sS τ) (sT τ) (a' τ) (b' τ)) := by
  intro D S T sS sT hS hT
  refine ⟨(-blk sT sS).det, fun a a' b b' h => ?_⟩
  obtain ⟨hs, hQ⟩ := HM_cartan hS hT
  have hd : (blk b a - 1).det ≠ 0 := by
    rw [det_blk_sub_one]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => (h τ).2.2.2.2.2.2
  have hi : blk b a * blk b' a' = 1 := by
    rw [blk_mul, ← blk_one]
    congr 1 <;> funext τ
    · exact (h τ).2.1
    · exact mul_eq_one_comm.1 (h τ).1
  have hc : blk sT sS * blk b a = blk b a * blk sT sS := by
    rw [blk_mul, blk_mul]
    congr 1 <;> funext τ
    · exact (h τ).2.2.2.2.2.1
    · exact (h τ).2.2.2.2.1.symm
  have hg : (blk b a)ᴴ * HM S T * blk b a = HM S T := by
    unfold HM
    rw [blk_conjTranspose, blk_mul, blk_mul]
    congr 1 <;> funext τ
    · rw [Matrix.mul_smul, Matrix.smul_mul, (h τ).2.2.2.1]
    · exact inv_unitary (GlobalTheory.SmoothForms.RealPts.gramAt_unit S τ) (h τ).1 (h τ).2.2.1
  obtain ⟨-, h1, h2⟩ := GlobalTheory.MatrixGaussian.integral_gaussian _ _ (expM_herm hQ hd)
  simp only [← gaussR_unv hQ] at h1 h2
  obtain ⟨h3, c, hc0, h4⟩ := integral_unv _ h1
  refine ⟨h3, c * (HM S T * blk sT sS).det.re⁻¹, mul_pos hc0 (inv_pos.2 (Complex.pos_iff.1 hQ.det_pos).1), ?_⟩
  rw [h4, h2, ← det_blk_sub_one, mul_assoc, gauss_det HM_herm hs hQ hg hc hi hd, Finset.prod_mul_distrib, ← det_blk,
    ← detPlus_blockDiagonal, Complex.ofReal_mul]
  ring

end GlobalTheory.RatAut.RealInt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGaussianRealIsometryNoFixedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_gaussian_real_isometry_no_fixed : ∀ (D : D7) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∃ ε : ℂ, ∀ (a a' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (b b' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, a τ * a' τ = 1 ∧ b τ * b' τ = 1 ∧ (a τ)ᴴ * gramAt D S τ * a τ = gramAt D S τ ∧ (b τ)ᴴ * gramAt D T τ * b τ = gramAt D T τ ∧ sS τ * a τ = a τ * sS τ ∧ sT τ * b τ = b τ * sT τ ∧ (b τ ⊗ₖ (a τ)ᵀ - 1).det ≠ 0) → Integrable (gaussR S T sS sT a b) volume ∧ ∃ r : ℝ, 0 < r ∧ (∫ v, gaussR S T sS sT a b v) * ∏ τ, (b τ ⊗ₖ (a τ)ᵀ - 1).det = r * ε * ∏ τ, ((b τ ⊗ₖ (a τ)ᵀ).det * detPlus (sS τ) (sT τ) (a' τ) (b' τ)) := by
  first | exact @GlobalTheory.RatAut.RealInt.integral_gaussR | exact GlobalTheory.RatAut.RealInt.integral_gaussR | (intros; apply GlobalTheory.RatAut.RealInt.integral_gaussR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentMemUpperUnipotent
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.UnipPlaced

variable {R : Type} [CommRing R]

theorem mul_apply_succ {n : ℕ} {X Y : GL (Fin n) R} (hX : X ∈ unipB R (Fin n)) (hY : Y ∈ unipB R (Fin n))
    {a a' : Fin n} (h : a'.val = a.val + 1) :
    ((X * Y : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a a' =
      (X : Matrix (Fin n) (Fin n) R) a a' + (Y : Matrix (Fin n) (Fin n) R) a a' := by
  rw [mem_unipB] at hX hY
  have hne : a ≠ a' := fun e => by have := congrArg Fin.val e; omega
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add_of_mem a a' (Finset.mem_univ _) (Finset.mem_univ _) hne]
  · rw [hX.2 a, hY.2 a', one_mul, mul_one, add_comm]
  · intro c _ hc
    have h1 := Fin.val_injective.ne hc.1
    have h2 := Fin.val_injective.ne hc.2
    by_cases hca : c < a
    · rw [hX.1 a c hca, zero_mul]
    · have : a' < c := by rw [Fin.lt_iff_val_lt_val] at hca ⊢; omega
      rw [hY.1 c a' this, mul_zero]

end GlobalTheory.GamMul.UnipPlaced

namespace GlobalTheory.GamMul.UnipPlaced

variable {R : Type} [CommRing R]

theorem superDiag_mul_unip {n : ℕ} {u v : GL (Fin n) R} (hu : u ∈ unipB R (Fin n)) (hv : v ∈ unipB R (Fin n)) :
    superDiag (u * v) = superDiag u + superDiag v := by
  simp only [superDiag, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
    mul_apply_succ hu hv (Finset.mem_filter.1 hj).2

end GlobalTheory.GamMul.UnipPlaced
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroOnClosedFibreCompleteLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroOnClosedFibreCompleteLocal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN

namespace GlobalTheory.ThetaClosed

theorem nonzeroLocus_firstPower_section_subset {X : Scheme.{0}} {L : LB X} (σ : H0 L 1) {x : X} (hx : x ∈ nonzeroLocus σ) :
    x ∈ nonzeroLocus (DVR.secOfH0 σ) := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨i, rfl⟩ : ∃ i : L.ι, j = fun _ => i := ⟨j 0, funext fun a => congrArg j (Subsingleton.elim a 0)⟩
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  have e := X.basicOpen_res (σ.f fun _ => i) (homOfLE (DVR.chart_le_weighted_chart_single (L := L) i)).op
  exact e.ge ⟨DVR.h0_le (fun _ => i) (X.basicOpen_le _ hj), hj⟩

theorem exists_section_nonzero_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → CharZero R → ∀ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal R) D A G), ∃ θ : LB.Sec U.LG.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R := by
  intro R _ _ _ hN _ _ _ D A G _ _ hG U
  have : GeometricallyConnected G.hom := hG.geomConnected
  have hL := GlobalTheory.allSixLaws.1
  obtain ⟨th, hth⟩ := GlobalTheory.ThetaCompare.exists_nonzero_closed hL.secBaseChange D.toPre
  obtain ⟨σ, fam, h0, hE, hm, -⟩ := GlobalTheory.ThetaUnit.exists_theta hL.globalFns hL.secBaseChange le_rfl U th hth
  obtain ⟨g, hg, hn⟩ := GlobalTheory.ThetaUnit.exists_mem_nonzeroLocus le_rfl U.toUnifPre (hE 0) (h0 ▸ hth) hm
  exact ⟨DVR.secOfH0 σ, g, nonzeroLocus_firstPower_section_subset σ hn, hg⟩

end GlobalTheory.ThetaClosed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroOnClosedFibreCompleteLocalStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_nonzero_on_closed_fibre_complete_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → CharZero R → ∀ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal R) D A G), ∃ θ : LB.Sec U.LG.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R := by
  first | exact @GlobalTheory.ThetaClosed.exists_section_nonzero_closed | exact GlobalTheory.ThetaClosed.exists_section_nonzero_closed | (intros; apply GlobalTheory.ThetaClosed.exists_section_nonzero_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsEvaluateFirst
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.GalLift.BaseEquiv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem phiC_congr {D : D7} (T : CoreJ D) {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ') {W : HSp D} (hV : T.V j σ = W)
    (hV' : T.V j σ' = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : phiC T hV a f = phiC T hV' a f := by
  subst e
  rfl

theorem alg_step {l c a a' x y : ℂ} (h1 : x = l * a) (h2 : a = c * a') (h3 : y = l * a') : x = c * y := by
  rw [h1, h2, h3]; ring

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

theorem baseEmbedding_restriction_eq_coefficientInclusion (fw : FWTie T R κw v₀) : res T (sg0 D A) = T.σ₀ :=
  (congrArg (res T) (show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0)).trans (res_embLL T fw.alg_eq fw.laws.pins.2.2.1)

theorem ev_base (fw : FWTie T R κw v₀) (i : Fin D.R.m) (hev : fw.Evaluates)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (f : Cu T κw i) (h : GA D (Wc D i)) :
    (R.HW i (sg0 D A)).e (fw.jK i (sg0 D A) f) (v₀ i (sg0 D A)) h =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κw i)) : ℂ) *
        (O i).phi (T.cE ((i : ℕ) + 1) (O i).s0) (f : T.R ((i : ℕ) + 1)) h := by
  have e : res T (sg0 D A) = (O i).s0 := (baseEmbedding_restriction_eq_coefficientInclusion T R κw v₀ fw).trans (sOv_eq T.toCore (O i).c' (O i).hle).symm
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := (congrArg (T.V ((i : ℕ) + 1)) e).trans (O i).hV
  have h1 := hev i (sg0 D A) (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) hV f
  have h2 := phiC_congr T e hV (O i).hV (wtA (κw i)) (f : T.R ((i : ℕ) + 1))
  have h3 := phi_cE T R O i (wtA (κw i)) (f : T.R ((i : ℕ) + 1)) h
  exact (congrFun (h1.trans h2) h).trans h3.symm

end GlobalTheory.GalLift.BaseEquiv

end
end
