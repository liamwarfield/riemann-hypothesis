module

public import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
public import Formalism.AdmissibleDesigns.LengthSemilinear

@[expose] public section

section -- merged from Formalism.AdmissibleDesigns.FinDimOfLat
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KRow

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Formalism.NG Module

section Gen

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Ow : Type} [CommRing Ow] [Algebra Ow LL] (eO : O ≃+* Ow)

scoped instance (priority := low) modOw (V : Type) [AddCommGroup V] [Module (FractionRing O) V] : Module Ow (TrV e V) :=
  Module.compHom (TrV e V) (algebraMap Ow LL)

variable {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]

instance towOw : IsScalarTower Ow LL (TrV e V) :=
  ⟨fun a b v => by
    show (a • b) • v = (algebraMap Ow LL a) • (b • v)
    rw [Algebra.smul_def, mul_smul]⟩

variable {e eO}

def tr (e : FractionRing O ≃+* LL) (v : V) : TrV e V := v

def untr (e : FractionRing O ≃+* LL) (v : TrV e V) : V := v

theorem smul_eO (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    (a : O) (v : V) : (eO a • tr e v : TrV e V) = tr e (a • v) := by
  show (algebraMap Ow LL (eO a)) • tr e v = tr e (a • v)
  rw [smulLL_def, heO, RingEquiv.symm_apply_apply]
  exact algebraMap_smul (FractionRing O) a v

theorem smul_Ow (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    (c : Ow) (v : V) : (c • tr e v : TrV e V) = tr e (eO.symm c • v) := by
  have h := smul_eO heO (eO.symm c) v
  rwa [RingEquiv.apply_symm_apply] at h

variable {M : Type} [AddCommGroup M] [Module O M] (j : M →ₗ[O] V)


variable (e eO) in
def latT (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a)) :
    Submodule Ow (TrV e V) where
  carrier := Set.range fun m => tr e (j m)
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add j a b⟩
  zero_mem' := ⟨0, map_zero j⟩
  smul_mem' := by
    rintro c _ ⟨a, rfl⟩
    refine ⟨eO.symm c • a, ?_⟩
    show tr e (j (eO.symm c • a)) = c • tr e (j a)
    rw [smul_Ow heO, map_smul]

theorem mem_latT (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    (v : TrV e V) : v ∈ latT e eO j heO ↔ ∃ m, tr e (j m) = v := by
  exact Iff.rfl

def MO (_eO : O ≃+* Ow) (M : Type) : Type := M

instance : AddCommGroup (MO eO M) := ‹AddCommGroup M›
instance : Module O (MO eO M) := ‹Module O M›
instance instModMO : Module Ow (MO eO M) := Module.compHom M eO.symm.toRingHom

def latMap (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a)) :
    MO eO M →ₗ[Ow] ↥(latT e eO j heO) where
  toFun m := ⟨tr e (j m), m, rfl⟩
  map_add' a b := Subtype.ext (map_add j a b)
  map_smul' c a := Subtype.ext (by
    show tr e (j (eO.symm c • (show M from a))) = c • tr e (j a)
    rw [smul_Ow heO, map_smul])

def latEquiv (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    (hj : Function.Injective j) : MO eO M ≃ₗ[Ow] ↥(latT e eO j heO) :=
  LinearEquiv.ofBijective (latMap j heO)
    ⟨fun a b h => hj (congrArg Subtype.val h : tr e (j a) = tr e (j b)),
      fun ⟨_, m, hm⟩ => ⟨m, Subtype.ext hm⟩⟩

def basMO [Module.Free O M] : Basis (Module.Free.ChooseBasisIndex O M) O (MO eO M) := Module.Free.chooseBasis O M

theorem free_MO [Module.Free O M] : Module.Free Ow (MO eO M) := by
  exact Module.Free.of_basis ((basMO (eO := eO) (M := M)).mapCoeffs eO (fun c x => by
    show eO.symm (eO c) • x = c • x
    rw [RingEquiv.symm_apply_apply]))

theorem finite_MO [Module.Finite O M] [Module.Free O M] : Module.Finite Ow (MO eO M) := by
  exact Module.Finite.of_basis ((basMO (eO := eO) (M := M)).mapCoeffs eO (fun c x => by
    show eO.symm (eO c) • x = c • x
    rw [RingEquiv.symm_apply_apply]))

variable {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) (ι : G →* Γ)


variable (e eO) in
def latOf (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    (ρV : Representation O Γ V) (ρM : Representation O Γ M) (hj : Function.Injective j)
    (hjeq : ∀ γ m, j (ρM γ m) = ρV γ (j m))
    (hsp : ∀ v : V, ∃ c : O, c ≠ 0 ∧ ∃ m, j m = c • v) [Module.Finite O M] [Module.Free O M] :
    Lattice (O := Ow) (repL e ρV ι) where
  T := latT e eO j heO
  stable g := by
    rintro _ ⟨m, rfl⟩
    exact ⟨ρM (ι g) m, hjeq _ _⟩
  fg := by
    haveI := finite_MO (eO := eO) (M := M)
    haveI : Module.Finite Ow ↥(latT e eO j heO) := Module.Finite.equiv (latEquiv j heO hj)
    exact (Module.Finite.iff_fg).1 inferInstance
  free := by
    haveI := free_MO (eO := eO) (M := M)
    exact Module.Free.of_equiv (latEquiv j heO hj)
  span := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨c, hc, m, hm⟩ := hsp (untr e v)
    have hk : algebraMap O (FractionRing O) c ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)
    have hv0 : untr e v = (algebraMap O (FractionRing O) c)⁻¹ • j m := by
      rw [hm, ← algebraMap_smul (FractionRing O) c (untr e v), smul_smul, inv_mul_cancel₀ hk, one_smul]
    have hv : v = e (algebraMap O (FractionRing O) c)⁻¹ • tr e (j m) := by
      show untr e v = e.symm (e (algebraMap O (FractionRing O) c)⁻¹) • j m
      rw [RingEquiv.symm_apply_apply, hv0]
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

end Gen

section Lift

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  {e : FractionRing O ≃+* LL} {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Ow : Type} [CommRing Ow] [Algebra Ow LL] {eO : O ≃+* Ow}
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) (ι : G →* Γ)
  {P Q VP VQ : Type} [AddCommGroup P] [Module O P] [AddCommGroup Q] [Module O Q]
  [AddCommGroup VP] [Module (FractionRing O) VP] [Module O VP] [IsScalarTower O (FractionRing O) VP]
  [AddCommGroup VQ] [Module (FractionRing O) VQ] [Module O VQ] [IsScalarTower O (FractionRing O) VQ]
  [Module.Finite O P] [Module.Free O P] [Module.Finite O Q] [Module.Free O Q]
  (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
  {ρP : Representation O Γ P} {ρQ : Representation O Γ Q} {ρVP : Representation O Γ VP}
  {ρVQ : Representation O Γ VQ} {jP : P →ₗ[O] VP} {jQ : Q →ₗ[O] VQ}
  (hjP : Function.Injective jP) (hjQ : Function.Injective jQ)
  (hjeqP : ∀ γ m, jP (ρP γ m) = ρVP γ (jP m)) (hjeqQ : ∀ γ m, jQ (ρQ γ m) = ρVQ γ (jQ m))
  (hspP : ∀ v : VP, ∃ c : O, c ≠ 0 ∧ ∃ m, jP m = c • v) (hspQ : ∀ v : VQ, ∃ c : O, c ≠ 0 ∧ ∃ m, jQ m = c • v)
  {ev : P →ₗ[O] Q} {f0 : VP →ₗ[O] VQ}
  (hf0 : ∀ γ v, f0 (ρVP γ v) = ρVQ γ (f0 v)) (hcomm : ∀ m, f0 (jP m) = jQ (ev m))

def latHom : LatHom (latOf e eO jP ι heO ρVP ρP hjP hjeqP hspP) (latOf e eO jQ ι heO ρVQ ρQ hjQ hjeqQ hspQ) where
  f := trL e f0
  equiv g x := hf0 (ι g) x
  cont := trL_cont e f0
  T_le := by
    rintro _ ⟨m, rfl⟩
    exact ⟨ev m, (hcomm m).symm⟩

theorem latHom_onto (hev : Function.Surjective ev) :
    (latHom ι heO hjP hjQ hjeqP hjeqQ hspP hspQ hf0 hcomm).Onto := by
  intro y hy
  obtain ⟨q, rfl⟩ := (mem_latT jQ heO y).mp hy
  obtain ⟨p, rfl⟩ := hev q
  refine ⟨tr e (jP p), (mem_latT jP heO _).mpr ⟨p, rfl⟩, ?_⟩
  show trL e f0 (tr e (jP p)) = tr e (jQ (ev p))
  rw [trL_apply]
  exact hcomm p

end Lift

section FromAt

theorem finDim_of_lat {LL Ow : Type} [Field LL] [CommRing Ow] [Algebra Ow LL] {G : Type} [Group G]
    {Qp : Type} [Field Qp] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module Ow V]
    [IsScalarTower Ow LL V] {ρ : Representation LL G V} (L : Lattice (O := Ow) ρ) : FiniteDimensional LL V := by
  obtain ⟨s, hs⟩ := L.fg
  have h1 : (L.T : Set V) ⊆ Submodule.span LL (s : Set V) := by
    rw [← hs]
    exact Submodule.span_subset_span Ow LL _
  refine ⟨⟨s, ?_⟩⟩
  rw [eq_top_iff, ← L.span]
  exact Submodule.span_le.mpr h1

end FromAt

section Lift2

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL]
  {e : FractionRing O ≃+* LL} {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Ow : Type} [CommRing Ow] [Algebra Ow LL] {eO : O ≃+* Ow}
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) (ι : G →* Γ)
  {P Q VP VQ : Type} [AddCommGroup P] [Module O P] [AddCommGroup Q] [Module O Q]
  [AddCommGroup VP] [Module (FractionRing O) VP] [Module O VP] [IsScalarTower O (FractionRing O) VP]
  [AddCommGroup VQ] [Module (FractionRing O) VQ] [Module O VQ] [IsScalarTower O (FractionRing O) VQ]
  [Module.Finite O P] [Module.Free O P] [Module.Finite O Q] [Module.Free O Q]
  (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
  {ρP : Representation O Γ P} {ρQ : Representation O Γ Q} {ρVP : Representation O Γ VP}
  {ρVQ : Representation O Γ VQ} {jP : P →ₗ[O] VP} {jQ : Q →ₗ[O] VQ}
  (hjP : Function.Injective jP) (hjQ : Function.Injective jQ)
  (hjeqP : ∀ γ m, jP (ρP γ m) = ρVP γ (jP m)) (hjeqQ : ∀ γ m, jQ (ρQ γ m) = ρVQ γ (jQ m))
  (hspP : ∀ v : VP, ∃ c : O, c ≠ 0 ∧ ∃ m, jP m = c • v) (hspQ : ∀ v : VQ, ∃ c : O, c ≠ 0 ∧ ∃ m, jQ m = c • v)
  {ev : P →ₗ[O] Q} {f0 : VP →ₗ[O] VQ}
  (hf0 : ∀ γ v, f0 (ρVP γ v) = ρVQ γ (f0 v)) (hcomm : ∀ m, f0 (jP m) = jQ (ev m))


include hspQ hcomm in
theorem trL_onto (hev : Function.Surjective ev) : Function.Surjective (trL e f0) := by
  intro w
  obtain ⟨c, hc, q, hq⟩ := hspQ (untr e w)
  obtain ⟨p, rfl⟩ := hev q
  have hk : algebraMap O (FractionRing O) c ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)
  refine ⟨tr e ((algebraMap O (FractionRing O) c)⁻¹ • jP p), ?_⟩
  rw [trL_apply]
  show f0 ((algebraMap O (FractionRing O) c)⁻¹ • jP p) = untr e w
  rw [smulK, hcomm, hq, ← algebraMap_smul (FractionRing O) c, smul_smul, inv_mul_cancel₀ hk, one_smul]

end Lift2

section Loc

variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module O M]

theorem mkK_inj [Module.Free O M] : Function.Injective (mkK (O := O) (M := M)) := by
  intro a b h
  simp only [LocalizedModule.mkLinearMap_apply] at h
  rw [LocalizedModule.mk_eq] at h
  obtain ⟨u, hu⟩ := h
  simp only [one_smul, Submonoid.smul_def] at hu
  exact smul_right_injective M (nonZeroDivisors.coe_ne_zero u) hu

theorem mkK_span (v : MK (O := O) M) : ∃ c : O, c ≠ 0 ∧ ∃ m, mkK m = c • v := by
  refine LocalizedModule.induction_on (fun m s => ?_) v
  refine ⟨s, nonZeroDivisors.coe_ne_zero s, m, ?_⟩
  rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  exact ⟨1, by simp [Submonoid.smul_def]⟩

end Loc

end Formalism.MainNotions.N.KRow

end
end

section -- merged from Formalism.AdmissibleDesigns.LiftMapEquivariant
section -- merged from Formalism.AdmissibleDesigns.LenComapSurj
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KRow

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Module

section Len

theorem len_comap_surj {O A B : Type} [CommRing O] [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B]
    (f : A →ₗ[O] B) (hf : Function.Surjective f) (Q P : Submodule O B) :
    Module.length O (↥(Q.comap f) ⧸ (P.comap f).comap (Q.comap f).subtype) =
      Module.length O (↥Q ⧸ P.comap Q.subtype) := by
  let q : ↥(Q.comap f) →ₗ[O] ↥Q ⧸ P.comap Q.subtype :=
    (P.comap Q.subtype).mkQ ∘ₗ LinearMap.codRestrict Q (f ∘ₗ (Q.comap f).subtype) (fun x => x.2)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨⟨a, hb⟩, rfl⟩
  have hk : LinearMap.ker q = (P.comap f).comap (Q.comap f).subtype := by
    ext x
    rw [LinearMap.mem_ker]
    exact Submodule.Quotient.mk_eq_zero _
  exact ((Submodule.quotEquivOfEq _ _ hk.symm).trans (q.quotKerEquivOfSurjective hq)).length_eq

variable {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  (e : R ≃+* S) [RingHomInvPair (e : R →+* S) (e.symm : S →+* R)] [RingHomInvPair (e.symm : S →+* R) (e : R →+* S)]
  (Ψ : M →ₛₗ[(e : R →+* S)] N) (hinj : Function.Injective Ψ)
  (Q P : Submodule R M) (Q' P' : Submodule S N)
  (hQ : ∀ y, y ∈ Q' ↔ ∃ x : M, x ∈ Q ∧ Ψ x = y) (hP : ∀ x ∈ Q, x ∈ P ↔ Ψ x ∈ P')

def resQ : ↥Q →ₛₗ[(e : R →+* S)] ↥Q' where
  toFun x := ⟨Ψ (x : M), (hQ _).2 ⟨x, x.2, rfl⟩⟩
  map_add' a b := Subtype.ext (map_add Ψ (a : M) (b : M))
  map_smul' c a := Subtype.ext (Ψ.map_smulₛₗ c (a : M))

include hinj in
theorem resQ_bij : Function.Bijective (resQ e Ψ Q Q' hQ) := by
  constructor
  · intro a b h
    have h' : Ψ (a : M) = Ψ (b : M) := congrArg Subtype.val h
    exact Subtype.ext (hinj h')
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := (hQ y).1 hy
    exact ⟨⟨x, hx⟩, rfl⟩


include hinj hQ in
def resQE : ↥Q ≃ₛₗ[(e : R →+* S)] ↥Q' :=
  LinearEquiv.ofBijective (resQ e Ψ Q Q' hQ) (resQ_bij e Ψ hinj Q Q' hQ)

include hinj hQ in
theorem resQE_apply (x : ↥Q) : ((resQE e Ψ hinj Q Q' hQ x : ↥Q') : N) = Ψ (x : M) := rfl


include hinj hQ hP in
theorem len_semi :
    Module.length R (↥Q ⧸ P.comap Q.subtype) = Module.length S (↥Q' ⧸ P'.comap Q'.subtype) := by
  obtain ⟨E, hE⟩ : ∃ E : ↥Q ≃ₛₗ[(e : R →+* S)] ↥Q', ∀ x, ((E x : ↥Q') : N) = Ψ (x : M) :=
    ⟨resQE e Ψ hinj Q Q' hQ, resQE_apply e Ψ hinj Q Q' hQ⟩
  have hmap : (P.comap Q.subtype).map (E : ↥Q →ₛₗ[(e : R →+* S)] ↥Q') = P'.comap Q'.subtype := by
    ext y
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hE]
      exact (hP x x.2).1 hx
    · intro hy
      obtain ⟨x, rfl⟩ := E.surjective y
      rw [hE] at hy
      exact ⟨x, (hP x x.2).2 hy, rfl⟩
  let F := Submodule.Quotient.equiv (P.comap Q.subtype) (P'.comap Q'.subtype) E hmap
  have h1 := Order.height_orderIso (Submodule.orderIsoMapComap F) ⊤
  rw [OrderIso.map_top] at h1
  rw [Module.length_eq_height, Module.length_eq_height]
  exact h1.symm

end Len

section Props

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.BasicNotions Formalism.RepresentationBoundsCohomology.FIN Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT w)] [∀ w, Module (D.nd.O i) (VT w)] [∀ w, TopologicalSpace (VT w)]
  [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul (D.nd.O i) (VT w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT w)]
  [∀ w, AddCommGroup (VT' w)] [∀ w, Module (D.nd.O i) (VT' w)] [∀ w, TopologicalSpace (VT' w)]
  [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul (D.nd.O i) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (VT w) (VT' w))
  {T₁ T₂ : Type} [AddCommGroup T₁] [Module (D.nd.O i) T₁] [TopologicalSpace T₁] [IsTopologicalAddGroup T₁]
  [ContinuousConstSMul (D.nd.O i) T₁] [AddCommGroup T₂] [Module (D.nd.O i) T₂]
  (ρ₁ : Representation (D.nd.O i) (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) T₁) (π : T₁ →ₗ[D.nd.O i] T₂)
  (vD : ∀ w, T₂ ≃ₗ[D.nd.O i] (Dat w).T') (hpD : ∀ w, Continuous fun t => vD w (π t))
  (heD : ∀ w g t, vD w (π (resRep ρ₁ (Γn i dc w) g t)) = (Dat w).ρTl' g (vD w (π t)))

def imRow (w : ℕ) : Submodule (D.nd.O i) (ReciprocityTheory.Gal.H1 (Dat w).ρTl') :=
  (Hf₁ i dc ρ₁ w).map (gRow (Dat w) (resRep ρ₁ (Γn i dc w)) π (vD w) (hpD w) (heD w))

variable [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]

def rowLenD (w : ℕ) : ℕ∞ :=
  Module.length (D.nd.O i) (↥(Fs i dc VT VT' Dat w) ⧸
    (imRow i dc VT VT' Dat ρ₁ π vD hpD heD w).comap (Fs i dc VT VT' Dat w).subtype)

theorem heO_br {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) (a : D.nd.O i) :
    algebraMap (Br.Ow (D.nbr i _ hn)) (Br.LLw (D.nbr i _ hn)) ((D.nbr i _ hn).eO a) =
      eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) a) := by
  change _ = Br.toLLK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) a)
  rw [Br.toLLK, IsFractionRing.lift_algebraMap]
  rfl

def RowSub (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    IsSubOfSums (repL (eK (D.nbr i _ hn)) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hn))
      (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (rDuO D.nd i r x)))

def RowOrb : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    ∀ x, Continuous fun g => repL (eK (D.nbr i _ hn)) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hn) g x

def RowMat (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (πx : D.nd.X i) : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    IsMatLat (ρ := repL (eK (D.nbr i _ hn)) (Dat n).ρT' (Br.iota D.nbr i _ hn))
      (latT (eK (D.nbr i _ hn)) (D.nbr i _ hn).eO (Dat n).T'.subtype (heO_br i dc hn))
      (⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (T2O D.nd i ρ πx)))

def RowTop : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    (∀ c : ↥(Γn i dc n) → VT' n,
      Continuous (fun g => tr (eK (D.nbr i _ hn)) (c (Br.iota D.nbr i _ hn g))) → Continuous c) ∧
    (∀ c : ↥(Γn i dc n) → T₁,
      Continuous (fun g => tr (eK (D.nbr i _ hn)) (mkK (O := D.nd.O i) (c (Br.iota D.nbr i _ hn g)))) →
        Continuous c)

def RowFin : Prop :=
  Module.Finite (D.nd.O i) T₁ ∧ Module.Free (D.nd.O i) T₁ ∧
  ∀ n ∈ K.rowsN i dc, Module.Finite (D.nd.O i) (Dat n).T' ∧ Module.Free (D.nd.O i) (Dat n).T' ∧
    ∀ v : VT' n, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ t : (Dat n).T', (t : VT' n) = c • v

end Props

end Formalism.MainNotions.N.KRow

end
end

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KRow

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Formalism.NG Module Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.FIN

section SpanK

variable {O : Type} [CommRing O] [IsDomain O] {H : Type} [AddCommGroup H] [Module O H]
  [Module (FractionRing O) H] [IsScalarTower O (FractionRing O) H]

theorem mem_spanK (S : Submodule O H) {x : H} (hx : x ∈ Submodule.span (FractionRing O) (S : Set H)) :
    ∃ t : O, t ≠ 0 ∧ t • x ∈ S := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact S.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨t, ht, hty⟩ := hy
    obtain ⟨s, hs, hsz⟩ := hz
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    rw [smul_add, mul_smul, mul_comm s t, mul_smul]
    exact S.add_mem (S.smul_mem s hty) (S.smul_mem t hsz)
  | smul a y _ hy =>
    obtain ⟨t, ht, hty⟩ := hy
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) a
    dsimp only at hnd
    have key : (d : O) • a = algebraMap O (FractionRing O) n := by
      rw [← hnd, Algebra.smul_def, mul_comm]
      exact IsLocalization.mk'_spec (FractionRing O) n d
    refine ⟨(d : O) * t, mul_ne_zero (nonZeroDivisors.coe_ne_zero d) ht, ?_⟩
    have e : ((d : O) * t) • (a • y) = n • (t • y) := by
      rw [mul_comm, ← smul_smul, ← smul_assoc (d : O) a y, key, algebraMap_smul, smul_comm]
    rw [e]
    exact S.smul_mem n hty

end SpanK

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {LL : Type} [Field LL] [TopologicalSpace LL] (e : FractionRing O ≃+* LL) {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Ow : Type} [CommRing Ow] [Algebra Ow LL] (eO : O ≃+* Ow)
  (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
  {Γ G : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) (ι : G →* Γ)
  {VT VT' : Type}
  [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
  [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  (Dt : LatData O Γ VT VT')

def psiR : (Γ → Dt.T') →ₛₗ[(eO : O →+* Ow)] (G → TrV e VT') where
  toFun c g := tr e ((c (ι g) : VT'))
  map_add' a b := by
    funext g
    rfl
  map_smul' a c := by
    funext g
    show tr e (a • ((c (ι g) : VT'))) = eO a • tr e ((c (ι g) : VT'))
    rw [smul_eO heO]

theorem psiR_inj (hι : Function.Bijective ι) : Function.Injective (psiR e eO heO ι Dt) := by
  intro a b h
  funext γ
  obtain ⟨g, rfl⟩ := hι.2 γ
  exact Subtype.ext (congrFun h g)

variable [Module (FractionRing O) (ReciprocityTheory.Gal.H1 Dt.ρT')] [IsScalarTower O (FractionRing O) (ReciprocityTheory.Gal.H1 Dt.ρT')]

def FsG : Submodule O (ReciprocityTheory.Gal.H1 Dt.ρTl') :=
  ((Submodule.span (FractionRing O) (finiteClassesContinuous e PD ι Dt.ρT' Dt.ρT' LinearMap.id :
    Set (ReciprocityTheory.Gal.H1 Dt.ρT'))).restrictScalars O).comap Dt.j'

theorem mem_FsG (hcob : ∀ v : VT', (fun γ => Dt.ρT' γ v - v) ∈ finZ e PD Dt.ρT' ι)
    (x : ReciprocityTheory.Gal.Z1 Dt.ρTl') :
    Submodule.mkQ _ x ∈ FsG e PD ι Dt ↔ (fun γ => ((x : Γ → Dt.T') γ : VT')) ∈ finZ e PD Dt.ρT' ι := by
  have hx' : (fun γ => ((x : Γ → Dt.T') γ : VT')) ∈ ReciprocityTheory.Gal.Z1 Dt.ρT' :=
    ⟨continuous_subtype_val.comp x.2.1, fun g h => by
      show (((x : Γ → Dt.T') (g * h) : Dt.T') : VT') = _
      rw [x.2.2 g h]
      rfl⟩
  have hj : Dt.j' (Submodule.mkQ _ x) = Submodule.mkQ _ ⟨_, hx'⟩ := rfl
  constructor
  · intro hF
    have hF' : Dt.j' (Submodule.mkQ _ x) ∈ Submodule.span (FractionRing O) (finiteClassesContinuous e PD ι Dt.ρT' Dt.ρT' LinearMap.id :
        Set (ReciprocityTheory.Gal.H1 Dt.ρT')) := hF
    obtain ⟨t, ht, hS⟩ := mem_spanK _ hF'
    rw [hj, ← map_smul] at hS
    obtain ⟨f, hf, hfe⟩ := hS
    have hfz : ((f : ReciprocityTheory.Gal.Z1 Dt.ρT') : Γ → VT') ∈ finZ e PD Dt.ρT' ι := hf
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hfe
    obtain ⟨v, hv⟩ := (ReciprocityTheory.Gal.mem_coboundaries1 _ _).1 hfe
    have htK : algebraMap O (FractionRing O) t ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ht)
    have heq : (fun γ => ((x : Γ → Dt.T') γ : VT')) =
        (algebraMap O (FractionRing O) t)⁻¹ • (((f : ReciprocityTheory.Gal.Z1 Dt.ρT') : Γ → VT') -
          fun γ => Dt.ρT' γ v - v) := by
      funext γ
      have e1 : ((f : ReciprocityTheory.Gal.Z1 Dt.ρT') : Γ → VT') γ - t • ((x : Γ → Dt.T') γ : VT') = Dt.ρT' γ v - v :=
        hv γ
      show ((x : Γ → Dt.T') γ : VT') = (algebraMap O (FractionRing O) t)⁻¹ •
        (((f : ReciprocityTheory.Gal.Z1 Dt.ρT') : Γ → VT') γ - (Dt.ρT' γ v - v))
      have e2 : ((f : ReciprocityTheory.Gal.Z1 Dt.ρT') : Γ → VT') γ - (Dt.ρT' γ v - v) =
          algebraMap O (FractionRing O) t • ((x : Γ → Dt.T') γ : VT') := by
        rw [algebraMap_smul]
        have e3 : ((f : ReciprocityTheory.Gal.Z1 Dt.ρT') : Γ → VT') γ = Dt.ρT' γ v - v + t • ((x : Γ → Dt.T') γ : VT') := by
          rw [← e1]
          abel
        rw [e3]
        abel
      rw [e2, smul_smul, inv_mul_cancel₀ htK, one_smul]
    rw [heq]
    exact (finZ e PD Dt.ρT' ι).smul_mem _ ((finZ e PD Dt.ρT' ι).sub_mem hfz (hcob v))
  · intro h
    show Dt.j' (Submodule.mkQ _ x) ∈ Submodule.span (FractionRing O) _
    rw [hj]
    exact Submodule.subset_span ⟨⟨_, hx'⟩, h, rfl⟩

variable {T₁ T₂ : Type} [AddCommGroup T₁] [Module O T₁] [TopologicalSpace T₁] [IsTopologicalAddGroup T₁]
  [ContinuousConstSMul O T₁] [AddCommGroup T₂] [Module O T₂] [Module.Finite O T₁] [Module.Free O T₁]
  [Module.Finite O Dt.T'] [Module.Free O Dt.T']
  (ρ₁ : Representation O Γ T₁) (π : T₁ →ₗ[O] T₂) (v : T₂ ≃ₗ[O] Dt.T')
  (hc : Continuous fun t => v (π t)) (he : ∀ g t, v (π (ρ₁ g t)) = Dt.ρTl' g (v (π t)))
  (hsp : ∀ x : VT', ∃ c : O, c ≠ 0 ∧ ∃ m : Dt.T', Dt.T'.subtype m = c • x)

def imG : Submodule O (ReciprocityTheory.Gal.H1 Dt.ρTl') :=
  (finiteClassesContinuousLattice e PD ι ρ₁).map (gRow Dt ρ₁ π v hc he)

abbrev L1 : Lattice (O := Ow) (repL e (locRep ρ₁) ι) :=
  latOf e eO (mkK (O := O) (M := T₁)) ι heO (locRep ρ₁) ρ₁ mkK_inj (fun γ m => (locRep_mkK ρ₁ γ m).symm) mkK_span

abbrev L2 : Lattice (O := Ow) (repL e Dt.ρT' ι) :=
  latOf e eO Dt.T'.subtype ι heO Dt.ρT' Dt.ρTl' Subtype.val_injective (fun _ _ => rfl) hsp

abbrev f0 : MK (O := O) T₁ →ₗ[O] VT' := liftK (Dt.T'.subtype ∘ₗ v.toLinearMap ∘ₗ π)

theorem lift_map_mk (m : T₁) : f0 Dt π v (mkK m) = Dt.T'.subtype ((v.toLinearMap ∘ₗ π) m) := liftK_mkK _ m

include he in
theorem lift_map_equivariant (γ : Γ) (x : MK (O := O) T₁) : f0 Dt π v (locRep ρ₁ γ x) = Dt.ρT' γ (f0 Dt π v x) :=
  liftK_equiv Dt.ρT' ρ₁ _ (fun g m => congrArg Subtype.val (he g m)) γ x

abbrev FR : LatHom (L1 e eO heO ι ρ₁) (L2 e eO heO ι Dt hsp) :=
  latHom ι heO mkK_inj Subtype.val_injective (fun γ m => (locRep_mkK ρ₁ γ m).symm) (fun _ _ => rfl) mkK_span hsp
    (lift_map_equivariant Dt ρ₁ π v he) (fun m => lift_map_mk Dt π v m)

theorem psi_mem_Z1fT (hcob : ∀ x : VT', (fun γ => Dt.ρT' γ x - x) ∈ finZ e PD Dt.ρT' ι)
    (x : ReciprocityTheory.Gal.Z1 Dt.ρTl') (hx : Submodule.mkQ _ x ∈ FsG e PD ι Dt) :
    psiR e eO heO ι Dt (x : Γ → Dt.T') ∈ latticeFiniteCocycles PD (L2 e eO heO ι Dt hsp) := by
  have h : psiR e eO heO ι Dt (x : Γ → Dt.T') ∈ finiteCocycles PD (repL e Dt.ρT' ι) := (mem_FsG e PD ι Dt hcob x).1 hx
  exact ⟨⟨h.1, fun g _ => ⟨(x : Γ → Dt.T') (ι g), rfl⟩⟩, h⟩

theorem exists_pre (hι : Function.Bijective ι)
    (hcob : ∀ x : VT', (fun γ => Dt.ρT' γ x - x) ∈ finZ e PD Dt.ρT' ι)
    (htopV : ∀ c : Γ → VT', Continuous (fun g => tr e (c (ι g))) → Continuous c)
    (y : G → TrV e VT') (hy : y ∈ latticeFiniteCocycles PD (L2 e eO heO ι Dt hsp)) :
    ∃ x : ReciprocityTheory.Gal.Z1 Dt.ρTl', Submodule.mkQ _ x ∈ FsG e PD ι Dt ∧ psiR e eO heO ι Dt (x : Γ → Dt.T') = y := by
  let σ : Γ ≃ G := (Equiv.ofBijective ι hι).symm
  have hισ : ∀ γ, ι (σ γ) = γ := fun γ => (Equiv.ofBijective ι hι).apply_symm_apply γ
  have hσι : ∀ g, σ (ι g) = g := fun g => (Equiv.ofBijective ι hι).symm_apply_apply g
  have hσmul : ∀ γ δ, σ (γ * δ) = σ γ * σ δ := fun γ δ => hι.1 (by rw [hισ, ι.map_mul, hισ, hισ])
  have hval : ∀ g, ∃ m : Dt.T', tr e (Dt.T'.subtype m) = y g := fun g => hy.1.2 g (Set.mem_univ g)
  let x0 : Γ → Dt.T' := fun γ => Classical.choose (hval (σ γ))
  have hx0 : ∀ γ, ((x0 γ : Dt.T') : VT') = untr e (y (σ γ)) := fun γ => Classical.choose_spec (hval (σ γ))
  have hpsi : psiR e eO heO ι Dt x0 = y := by
    funext g
    show ((x0 (ι g) : Dt.T') : VT') = untr e (y g)
    rw [hx0, hσι]
  have hcv : Continuous fun γ => ((x0 γ : Dt.T') : VT') := by
    apply htopV
    have : (fun g => tr e (((x0 (ι g) : Dt.T') : VT'))) = y := hpsi
    rw [this]
    exact hy.1.1.1
  have hcont : Continuous x0 := continuous_induced_rng.2 hcv
  have hcoc : ∀ γ δ, x0 (γ * δ) = x0 γ + Dt.ρTl' γ (x0 δ) := by
    intro γ δ
    apply Subtype.ext
    show ((x0 (γ * δ) : Dt.T') : VT') = ((x0 γ : Dt.T') : VT') + Dt.ρT' γ ((x0 δ : Dt.T') : VT')
    rw [hx0, hx0, hx0, hσmul]
    have h2 := hy.1.1.2 (σ γ) (σ δ)
    show untr e (y (σ γ * σ δ)) = untr e (y (σ γ)) + Dt.ρT' γ (untr e (y (σ δ)))
    rw [h2]
    show untr e (y (σ γ)) + Dt.ρT' (ι (σ γ)) (untr e (y (σ δ))) = _
    rw [hισ]
  let x : ReciprocityTheory.Gal.Z1 Dt.ρTl' := ⟨x0, hcont, hcoc⟩
  refine ⟨x, (mem_FsG e PD ι Dt hcob x).2 ?_, hpsi⟩
  show psiR e eO heO ι Dt x0 ∈ finiteCocycles PD (repL e Dt.ρT' ι)
  rw [hpsi]
  exact hy.2

theorem im_iff (hι : Function.Bijective ι)
    (htop1 : ∀ c : Γ → T₁, Continuous (fun g => tr e (mkK (O := O) (c (ι g)))) → Continuous c)
    (x : ReciprocityTheory.Gal.Z1 Dt.ρTl') :
    Submodule.mkQ _ x ∈ imG e PD ι Dt ρ₁ π v hc he ↔
      psiR e eO heO ι Dt (x : Γ → Dt.T') ∈ (FR e eO heO ι Dt ρ₁ π v he hsp).ImF PD := by
  let σ : Γ ≃ G := (Equiv.ofBijective ι hι).symm
  have hισ : ∀ γ, ι (σ γ) = γ := fun γ => (Equiv.ofBijective ι hι).apply_symm_apply γ
  have hσι : ∀ g, σ (ι g) = g := fun g => (Equiv.ofBijective ι hι).symm_apply_apply g
  have hσmul : ∀ γ δ, σ (γ * δ) = σ γ * σ δ := fun γ δ => hι.1 (by rw [hισ, ι.map_mul, hισ, hισ])
  constructor
  · rintro ⟨z, ⟨c₁, hc₁, rfl⟩, hzx⟩
    have hfin : (fun γ => mkK (O := O) ((c₁ : Γ → T₁) γ)) ∈ finZ e PD (locRep ρ₁) ι := hc₁
    have hzx' : Submodule.mkQ _ (ReciprocityTheory.Gal.cocycles1MapOfEquivariant ρ₁ Dt.ρTl' (v.toLinearMap ∘ₗ π) hc he c₁) =
        Submodule.mkQ _ x := hzx
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hzx'
    obtain ⟨t, ht⟩ := (ReciprocityTheory.Gal.mem_coboundaries1 _ _).1 hzx'
    let d₁ : G → TrV e (MK (O := O) T₁) := fun g => tr e (mkK (O := O) ((c₁ : Γ → T₁) (ι g)))
    have hd₁ : d₁ ∈ latticeFiniteCocycles PD (L1 e eO heO ι ρ₁) := ⟨⟨hfin.1, fun g _ => ⟨_, rfl⟩⟩, hfin⟩
    refine Submodule.mem_sup.2 ⟨_, ⟨d₁, hd₁, rfl⟩, _, ⟨tr e (((-t : Dt.T')) : VT'), ⟨-t, rfl⟩, rfl⟩, ?_⟩
    funext g
    have h1 : ((v (π ((c₁ : Γ → T₁) (ι g))) : Dt.T') : VT') - (((x : Γ → Dt.T') (ι g) : Dt.T') : VT') =
        Dt.ρT' (ι g) (t : VT') - (t : VT') := congrArg Subtype.val (ht (ι g))
    show f0 Dt π v (mkK ((c₁ : Γ → T₁) (ι g))) + (Dt.ρT' (ι g) (((-t : Dt.T')) : VT') - (((-t : Dt.T')) : VT')) =
      (((x : Γ → Dt.T') (ι g) : Dt.T') : VT')
    rw [lift_map_mk]
    have h2 : (((x : Γ → Dt.T') (ι g) : Dt.T') : VT') =
        ((v (π ((c₁ : Γ → T₁) (ι g))) : Dt.T') : VT') - (Dt.ρT' (ι g) (t : VT') - (t : VT')) := by
      rw [← h1]
      abel
    rw [h2]
    simp only [Submodule.coe_neg, map_neg]
    show ((v (π ((c₁ : Γ → T₁) (ι g))) : Dt.T') : VT') + (-(Dt.ρT' (ι g) (t : VT')) - -(t : VT')) = _
    abel
  · intro h
    obtain ⟨a, ⟨d₁, hd₁, rfl⟩, b, ⟨yv, ⟨t, rfl⟩, rfl⟩, hab⟩ := Submodule.mem_sup.1 h
    have hval : ∀ g, ∃ m : T₁, tr e (mkK (O := O) m) = d₁ g := fun g => hd₁.1.2 g (Set.mem_univ g)
    let c0 : Γ → T₁ := fun γ => Classical.choose (hval (σ γ))
    have hc0 : ∀ γ, mkK (O := O) (c0 γ) = untr e (d₁ (σ γ)) := fun γ => Classical.choose_spec (hval (σ γ))
    have hd : (fun g => tr e (mkK (O := O) (c0 (ι g)))) = d₁ := by
      funext g
      show mkK (O := O) (c0 (ι g)) = untr e (d₁ g)
      rw [hc0, hσι]
    have hcont : Continuous c0 := htop1 c0 (by rw [hd]; exact hd₁.1.1.1)
    have hcoc : ∀ γ δ, c0 (γ * δ) = c0 γ + ρ₁ γ (c0 δ) := by
      intro γ δ
      apply mkK_inj (O := O)
      rw [map_add (f := _), ← locRep_mkK, hc0, hc0, hc0, hσmul]
      have h2 := hd₁.1.1.2 (σ γ) (σ δ)
      show untr e (d₁ (σ γ * σ δ)) = untr e (d₁ (σ γ)) + locRep ρ₁ γ (untr e (d₁ (σ δ)))
      rw [h2]
      show untr e (d₁ (σ γ)) + locRep ρ₁ (ι (σ γ)) (untr e (d₁ (σ δ))) = _
      rw [hισ]
    let c₁ : ReciprocityTheory.Gal.Z1 ρ₁ := ⟨c0, hcont, hcoc⟩
    have hfin : (fun γ => mkK (O := O) (c0 γ)) ∈ finZ e PD (locRep ρ₁) ι := by
      show (fun g => tr e (mkK (O := O) (c0 (ι g)))) ∈ finiteCocycles PD (repL e (locRep ρ₁) ι)
      rw [hd]
      exact hd₁.2
    refine ⟨Submodule.mkQ _ c₁, ⟨c₁, hfin, rfl⟩, ?_⟩
    show Submodule.mkQ _ (ReciprocityTheory.Gal.cocycles1MapOfEquivariant ρ₁ Dt.ρTl' (v.toLinearMap ∘ₗ π) hc he c₁) = Submodule.mkQ _ x
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine (ReciprocityTheory.Gal.mem_coboundaries1 _ _).2 ⟨-t, fun γ => ?_⟩
    apply Subtype.ext
    have h3 := congrFun hab (σ γ)
    have h5 : f0 Dt π v (untr e (d₁ (σ γ))) + (Dt.ρT' (ι (σ γ)) (t : VT') - (t : VT')) =
        (((x : Γ → Dt.T') (ι (σ γ)) : Dt.T') : VT') := h3
    rw [← hc0, lift_map_mk, hισ] at h5
    have h4 : ((v (π (c0 γ)) : Dt.T') : VT') + (Dt.ρT' γ (t : VT') - (t : VT')) =
        (((x : Γ → Dt.T') γ : Dt.T') : VT') := h5
    show ((v (π (c0 γ)) : Dt.T') : VT') - (((x : Γ → Dt.T') γ : Dt.T') : VT') =
      Dt.ρT' γ ((-t : Dt.T') : VT') - ((-t : Dt.T') : VT')
    rw [← h4]
    simp only [Submodule.coe_neg, map_neg]
    abel

theorem len_eq_col (hι : Function.Bijective ι)
    (hcob : ∀ x : VT', (fun γ => Dt.ρT' γ x - x) ∈ finZ e PD Dt.ρT' ι)
    (htopV : ∀ c : Γ → VT', Continuous (fun g => tr e (c (ι g))) → Continuous c)
    (htop1 : ∀ c : Γ → T₁, Continuous (fun g => tr e (mkK (O := O) (c (ι g)))) → Continuous c) :
    Module.length O (↥(FsG e PD ι Dt) ⧸ (imG e PD ι Dt ρ₁ π v hc he).comap (FsG e PD ι Dt).subtype) =
      (FR e eO heO ι Dt ρ₁ π v he hsp).col PD := by
  haveI h1 := RingHomInvPair.of_ringEquiv eO
  haveI h2 := RingHomInvPair.symm (eO : O →+* Ow) (eO.symm : Ow →+* O)
  rw [← len_comap_surj (Submodule.mkQ _) (Submodule.mkQ_surjective _)]
  unfold LatHom.col
  refine len_semi eO ((psiR e eO heO ι Dt).comp (ReciprocityTheory.Gal.Z1 Dt.ρTl').subtype)
    ((psiR_inj e eO heO ι Dt hι).comp Subtype.val_injective) _ _ _ _ ?_ ?_
  · intro y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := exists_pre e eO heO PD ι Dt hsp hι hcob htopV y hy
      exact ⟨x, hx, hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact psi_mem_Z1fT e eO heO PD ι Dt hsp hcob x hx
  · intro x _
    exact im_iff e eO heO PD ι Dt ρ₁ π v hc he hsp hι htop1 x

end Gen

end Formalism.MainNotions.N.KRow

end
end

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KRow

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Module Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.BasicNotions Formalism.RepresentationBoundsCohomology.FIN Formalism.NG Formalism.BasicNotions.Loc

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT w)] [∀ w, Module (D.nd.O i) (VT w)] [∀ w, TopologicalSpace (VT w)]
  [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul (D.nd.O i) (VT w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT w)]
  [∀ w, AddCommGroup (VT' w)] [∀ w, Module (D.nd.O i) (VT' w)] [∀ w, TopologicalSpace (VT' w)]
  [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul (D.nd.O i) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (VT w) (VT' w))
  {T₁ T₂ : Type} [AddCommGroup T₁] [Module (D.nd.O i) T₁] [TopologicalSpace T₁] [IsTopologicalAddGroup T₁]
  [ContinuousConstSMul (D.nd.O i) T₁] [AddCommGroup T₂] [Module (D.nd.O i) T₂]
  (ρ₁ : Representation (D.nd.O i) (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) T₁) (π : T₁ →ₗ[D.nd.O i] T₂)
  (vD : ∀ w, T₂ ≃ₗ[D.nd.O i] (Dat w).T') (hpD : ∀ w, Continuous fun t => vD w (π t))
  (heD : ∀ w g t, vD w (π (resRep ρ₁ (Γn i dc w) g t)) = (Dat w).ρTl' g (vD w (π t)))
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]

theorem len_congr {O H : Type} [CommRing O] [AddCommGroup H] [Module O H] {A A' B B' : Submodule O H}
    (hA : A = A') (hB : B = B') :
    Module.length O (↥A ⧸ B.comap A.subtype) = Module.length O (↥A' ⧸ B'.comap A'.subtype) := by
  subst hA hB
  rfl

theorem fs_eq {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    Fs i dc VT VT' Dat n = FsG (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (Br.iota D.nbr i _ hn) (Dat n) := by
  have key : fZ i dc n (Dat n).ρT' = finZ (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (Dat n).ρT' (Br.iota D.nbr i _ hn) := by
    unfold fZ
    rw [dite_eq_left hn]
  unfold Fs FsG Hf₂ finiteClassesContinuousMap fPre finiteClassesContinuous finPre
  rw [key]

theorem finite_classes_row_eq_generic {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    Hf₁ i dc ρ₁ n = finiteClassesContinuousLattice (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (Br.iota D.nbr i _ hn)
      (resRep ρ₁ (Γn i dc n)) := by
  have key : fZ i dc n (locRep (resRep ρ₁ (Γn i dc n))) = finZ (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hn) := by
    unfold fZ
    rw [dite_eq_left hn]
  unfold Hf₁ finiteClassesContinuousLocal finiteClassesContinuousLattice finiteClassesContinuousMap fPre finiteClassesContinuous finPre
  rw [key]
  rfl

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (πx : D.nd.X i)


set_option maxHeartbeats 1000000 in
theorem rowLenD_eq_gen {n : ℕ} (hw : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    rowLenD i dc VT VT' Dat ρ₁ π vD hpD heD n =
      Module.length (D.nd.O i)
        (↥(FsG (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (Br.PD D.loc D.nbr i _ hw) (Br.iota D.nbr i _ hw) (Dat n)) ⧸
          (imG (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (Br.PD D.loc D.nbr i _ hw) (Br.iota D.nbr i _ hw) (Dat n)
            (resRep ρ₁ (Γn i dc n)) π (vD n) (hpD n) (heD n)).comap
            (FsG (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (Br.PD D.loc D.nbr i _ hw) (Br.iota D.nbr i _ hw)
              (Dat n)).subtype) := by
  unfold rowLenD
  exact len_congr (fs_eq i dc VT VT' Dat hw) (by unfold imRow; rw [finite_classes_row_eq_generic i dc ρ₁ hw]; rfl)


set_option maxHeartbeats 1000000 in
theorem rowLenD_eq {n : ℕ} (hw : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
    [Module.Finite (D.nd.O i) T₁] [Module.Free (D.nd.O i) T₁]
    [Module.Finite (D.nd.O i) (Dat n).T'] [Module.Free (D.nd.O i) (Dat n).T']
    (hsp : ∀ x : VT' n, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ m : (Dat n).T', (Dat n).T'.subtype m = c • x)
    (hcob : OrbC i dc (n := n) (Dat n).ρT')
    (htopV : ∀ c : ↥(Γn i dc n) → VT' n,
      Continuous (fun g => tr (eK (D.nbr i _ hw)) (c (Br.iota D.nbr i _ hw g))) → Continuous c)
    (htop1 : ∀ c : ↥(Γn i dc n) → T₁,
      Continuous (fun g => tr (eK (D.nbr i _ hw)) (mkK (O := D.nd.O i) (c (Br.iota D.nbr i _ hw g)))) →
        Continuous c) :
    rowLenD i dc VT VT' Dat ρ₁ π vD hpD heD n =
      (FR (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw) (Dat n)
        (resRep ρ₁ (Γn i dc n)) π (vD n) (heD n) hsp).col (Br.PD D.loc D.nbr i _ hw) := by
  have hbij : Function.Bijective (Br.iota D.nbr i _ hw) := (D.nbr i _ hw).e.symm.bijective
  have hcobn : ∀ x : VT' n, (fun γ => (Dat n).ρT' γ x - x) ∈
      finZ (eK (D.nbr i _ hw)) (Br.PD D.loc D.nbr i _ hw) (Dat n).ρT' (Br.iota D.nbr i _ hw) := by
    intro x
    have h := cob_mem_fZ i dc (Dat n).ρT' hcob x
    rwa [fZ_pos i dc _ hw] at h
  exact (rowLenD_eq_gen i dc VT VT' Dat ρ₁ π vD hpD heD hw).trans
    (len_eq_col (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw)
      (Br.PD D.loc D.nbr i _ hw) (Br.iota D.nbr i _ hw) (Dat n) (resRep ρ₁ (Γn i dc n)) π (vD n) (hpD n) (heD n) hsp
      hbij hcobn htopV htop1)


set_option maxHeartbeats 1000000 in
theorem rowTie_disp (hπ : Function.Surjective π)
    (hSub : RowSub (ρ₁ := ρ₁) i dc r) (hOrb : RowOrb (ρ₁ := ρ₁) i dc)
    (hMat : RowMat i dc VT VT' Dat ρ πx) (hTop : RowTop i dc VT' (T₁ := T₁))
    (hFin : RowFin i dc VT VT' Dat (T₁ := T₁))
    (hcob : ∀ n ∈ K.rowsN i dc, OrbC i dc (n := n) (Dat n).ρT') :
    K.Sel.RowTie i dc r ρ πx (rowLenD i dc VT VT' Dat ρ₁ π vD hpD heD) := by
  intro n hn hw b hR
  obtain ⟨hF1, hF2, hFn⟩ := hFin
  obtain ⟨hF3, hF4, hsp⟩ := hFn n hn
  haveI := hF1
  haveI := hF2
  haveI := hF3
  haveI := hF4
  have hev : Function.Surjective ((vD n).toLinearMap ∘ₗ π) := (vD n).surjective.comp hπ
  have hrow := rowLenD_eq i dc VT VT' Dat ρ₁ π vD hpD heD hw hsp (hcob n hn) (hTop n hn hw).1 (hTop n hn hw).2
  have hR' : RowAt (Br.PD D.loc D.nbr i _ hw) (LL := Br.LLw (D.nbr i _ hw)) (O := Br.Ow (D.nbr i _ hw))
      (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hw) (rDuO D.nd i r x)))
      ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hw) (T2O D.nd i ρ πx)) b := hR
  have hL1 := finDim_of_lat (Ow := Br.Ow (D.nbr i _ hw)) (Qp := ℚ_[D.nd.l i])
    (L1 (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw)
      (resRep ρ₁ (Γn i dc n)))
  have hL2 := finDim_of_lat (Ow := Br.Ow (D.nbr i _ hw)) (Qp := ℚ_[D.nd.l i])
    (L2 (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw) (Dat n) hsp)
  have hons : Function.Surjective (trL (eK (D.nbr i _ hw)) (f0 (Dat n) π (vD n))) :=
    trL_onto (hspQ := hsp) (hcomm := fun m => lift_map_mk (Dat n) π (vD n) m) hev
  have hc1 := hOrb n hn hw
  have hc2 : ∀ y, Continuous fun g => repL (eK (D.nbr i _ hw)) (Dat n).ρT' (Br.iota D.nbr i _ hw) g y := by
    intro y
    obtain ⟨x, rfl⟩ := hons y
    have h : (fun g => repL (eK (D.nbr i _ hw)) (Dat n).ρT' (Br.iota D.nbr i _ hw) g
        (trL (eK (D.nbr i _ hw)) (f0 (Dat n) π (vD n)) x)) =
        fun g => trL (eK (D.nbr i _ hw)) (f0 (Dat n) π (vD n))
          (repL (eK (D.nbr i _ hw)) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hw) g x) :=
      funext fun g => (lift_map_equivariant (Dat n) (resRep ρ₁ (Γn i dc n)) π (vD n) (heD n) (Br.iota D.nbr i _ hw g) x).symm
    rw [h]
    exact (trL_cont (eK (D.nbr i _ hw)) _).comp (hc1 x)
  have hOnto := latHom_onto (ρP := resRep ρ₁ (Γn i dc n)) (ρQ := (Dat n).ρTl') (Br.iota D.nbr i _ hw) (heO_br i dc hw) mkK_inj Subtype.val_injective
    (fun γ m => (locRep_mkK (resRep ρ₁ (Γn i dc n)) γ m).symm) (fun _ _ => rfl) mkK_span hsp
    (lift_map_equivariant (Dat n) (resRep ρ₁ (Γn i dc n)) π (vD n) (heD n)) (fun m => lift_map_mk (Dat n) π (vD n) m) hev
  obtain ⟨m, k, hm, hk, hmk⟩ := hR' (TrV (eK (D.nbr i _ hw)) (VT' n))
    (repL (eK (D.nbr i _ hw)) (Dat n).ρT' (Br.iota D.nbr i _ hw))
    (L2 (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw) (Dat n) hsp)
    hc2 (hMat n hn hw) (TrV (eK (D.nbr i _ hw)) (MK (O := D.nd.O i) T₁))
    (repL (eK (D.nbr i _ hw)) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hw))
    (L1 (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw)
      (resRep ρ₁ (Γn i dc n)))
    hc1 (hSub n hn hw)
    (FR (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw) (Dat n)
      (resRep ρ₁ (Γn i dc n)) π (vD n) (heD n) hsp) hOnto
  have hm' : rowLenD i dc VT VT' Dat ρ₁ π vD hpD heD n = m := hrow.trans hm
  have hk' : lenOl (Br.PD D.loc D.nbr i (K.plOf i dc n) hw)
      (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i (K.plOf i dc n) hw).LL)) = k := hk
  refine ⟨by rw [hm']; exact ENat.coe_ne_top m, ?_⟩
  rw [hm', hk']
  simp only [ENat.toNat_coe]
  exact hmk


end Rec

end Formalism.MainNotions.N.KRow

end
