module

public import GroundTheory.GlobalFields.HerbrandQuotients.CycTateNegOneOrbitEquivSymmMk
public import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Decomposition
public import GroundTheory.GlobalFields.IdeleGroups.LocalHerbrandInfinite
public import GroundTheory.GlobalFields.HerbrandQuotients.SUnits
public import GroundTheory.GlobalFields.IdeleGroups.LocalNormsEverywhere
public import GroundTheory.GlobalFields.FirstInequalityStatement

@[expose] public section

section -- merged from GroundTheory.GlobalFields.FirstInequality.HerbrandClass
section -- merged from GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand
section -- merged from GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand.Places
section -- merged from GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand.Product
namespace GroundTheory.Global

open GroundTheory.GroupCoh

noncomputable section

section KerModRangeProd

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

def kerModRangeProdEquiv (F G : A × B →+ A × B) (fA gA : A →+ A) (fB gB : B →+ B)
    (hF : ∀ x, F x = (fA x.1, fB x.2)) (hG : ∀ x, G x = (gA x.1, gB x.2)) :
    KerModRange F G ≃+ KerModRange fA gA × KerModRange fB gB :=
  kerModRangeEquivOfSurjective
    (AddMonoidHom.prod
      ((QuotientAddGroup.mk' _).comp
        (((AddMonoidHom.fst A B).comp F.ker.subtype).codRestrict fA.ker fun x ↦
          AddMonoidHom.mem_ker.2 (congrArg Prod.fst ((hF x).symm.trans (AddMonoidHom.mem_ker.1 x.2)))))
      ((QuotientAddGroup.mk' _).comp
        (((AddMonoidHom.snd A B).comp F.ker.subtype).codRestrict fB.ker fun x ↦
          AddMonoidHom.mem_ker.2 (congrArg Prod.snd ((hF x).symm.trans (AddMonoidHom.mem_ker.1 x.2))))))
    (by
      rintro ⟨y₁, y₂⟩
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y₁
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y₂
      refine ⟨⟨((a : A), (b : B)), AddMonoidHom.mem_ker.2 ?_⟩, rfl⟩
      rw [hF, AddMonoidHom.mem_ker.1 a.2, AddMonoidHom.mem_ker.1 b.2, Prod.mk_zero_zero])
    (by
      intro x
      constructor
      · intro h
        have h1 : (x : A × B).1 ∈ gA.range :=
          (KerModRange.mk_eq_zero_iff (g := gA) _).1 (congrArg Prod.fst h)
        have h2 : (x : A × B).2 ∈ gB.range :=
          (KerModRange.mk_eq_zero_iff (g := gB) _).1 (congrArg Prod.snd h)
        obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.1 h1
        obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.1 h2
        exact AddMonoidHom.mem_range.2 ⟨(a, b), by rw [hG, ha, hb]⟩
      · intro h
        obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.1 h
        rw [hG] at hy
        exact Prod.ext
          ((KerModRange.mk_eq_zero_iff (g := gA) _).2
            (AddMonoidHom.mem_range.2 ⟨y.1, congrArg Prod.fst hy⟩))
          ((KerModRange.mk_eq_zero_iff (g := gB) _).2
            (AddMonoidHom.mem_range.2 ⟨y.2, congrArg Prod.snd hy⟩)))

end KerModRangeProd

section Prod

variable {k G V W : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

theorem cycSubOne_prod_apply (ρ : Representation k G V) (ρ' : Representation k G W) (σ : G)
    (x : V × W) : cycSubOne (ρ.prod ρ') σ x = (cycSubOne ρ σ x.1, cycSubOne ρ' σ x.2) := by
  rw [cycSubOne_apply, cycSubOne_apply, cycSubOne_apply]
  rfl

variable [Fintype G]

theorem cycNorm_prod_apply (ρ : Representation k G V) (ρ' : Representation k G W)
    (x : V × W) : cycNorm (ρ.prod ρ') x = (cycNorm ρ x.1, cycNorm ρ' x.2) := by
  rw [cycNorm_apply, cycNorm_apply, cycNorm_apply]
  exact Prod.ext (by rw [Prod.fst_sum]; rfl) (by rw [Prod.snd_sum]; rfl)

def cycTateZeroProdEquiv (ρ : Representation k G V) (ρ' : Representation k G W) (σ : G) :
    CycTateZero (ρ.prod ρ') σ ≃+ CycTateZero ρ σ × CycTateZero ρ' σ :=
  kerModRangeProdEquiv _ _ _ _ _ _ (cycSubOne_prod_apply ρ ρ' σ) (cycNorm_prod_apply ρ ρ')

def cycTateNegOneProdEquiv (ρ : Representation k G V) (ρ' : Representation k G W) (σ : G) :
    CycTateNegOne (ρ.prod ρ') σ ≃+ CycTateNegOne ρ σ × CycTateNegOne ρ' σ :=
  kerModRangeProdEquiv _ _ _ _ _ _ (cycNorm_prod_apply ρ ρ') (cycSubOne_prod_apply ρ ρ' σ)

theorem cycHerbrand_prod_eq_mul (ρ : Representation k G V) (ρ' : Representation k G W) (σ : G) :
    cycHerbrand (ρ.prod ρ') σ = cycHerbrand ρ σ * cycHerbrand ρ' σ := by
  simp only [cycHerbrand_eq]
  rw [Nat.card_congr (cycTateZeroProdEquiv ρ ρ' σ).toEquiv,
    Nat.card_congr (cycTateNegOneProdEquiv ρ ρ' σ).toEquiv, Nat.card_prod, Nat.card_prod,
    Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm]

end Prod

section Mul

variable {G : Type*} [Group G]

def additiveProdEquiv (M N : Type*) [CommGroup M] [CommGroup N] :
    Additive (M × N) ≃+ Additive M × Additive N where
  toFun x := (Additive.ofMul x.toMul.1, Additive.ofMul x.toMul.2)
  invFun y := Additive.ofMul (y.1.toMul, y.2.toMul)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def additivePiEquiv {ι : Type*} (M : ι → Type*) [∀ i, CommGroup (M i)] :
    Additive (∀ i, M i) ≃+ ∀ i, Additive (M i) where
  toFun x i := Additive.ofMul (x.toMul i)
  invFun y := Additive.ofMul fun i ↦ (y i).toMul
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

section Prod

variable (M N : Type*) [CommGroup M] [CommGroup N] [MulDistribMulAction G M]
  [MulDistribMulAction G N] [Fintype G]

theorem cycHerbrand_mulProd (σ : G) :
    cycHerbrand (Representation.ofMulDistribMulAction G (M × N)) σ =
      cycHerbrand (Representation.ofMulDistribMulAction G M) σ *
        cycHerbrand (Representation.ofMulDistribMulAction G N) σ := by
  rw [cycHerbrand_congr (ρ' := (Representation.ofMulDistribMulAction G M).prod
      (Representation.ofMulDistribMulAction G N)) (additiveProdEquiv M N) (fun _ _ ↦ rfl) σ,
    cycHerbrand_prod_eq_mul]

end Prod

section Pi

variable {ι : Type*} (M : ι → Type*) [∀ i, CommGroup (M i)] [∀ i, MulDistribMulAction G (M i)]
  [Fintype G]

def cycTateZeroMulPiEquiv (σ : G) :
    CycTateZero (Representation.ofMulDistribMulAction G (∀ i, M i)) σ ≃+
      ∀ i, CycTateZero (Representation.ofMulDistribMulAction G (M i)) σ :=
  (cycTateZeroCongr (ρ' := piRep fun i ↦ Representation.ofMulDistribMulAction G (M i))
      (additivePiEquiv M) (fun _ _ ↦ rfl) σ).trans (cycTateZeroPiEquiv _ σ)

def cycTateNegOneMulPiEquiv (σ : G) :
    CycTateNegOne (Representation.ofMulDistribMulAction G (∀ i, M i)) σ ≃+
      ∀ i, CycTateNegOne (Representation.ofMulDistribMulAction G (M i)) σ :=
  (cycTateNegOneCongr (ρ' := piRep fun i ↦ Representation.ofMulDistribMulAction G (M i))
      (additivePiEquiv M) (fun _ _ ↦ rfl) σ).trans (cycTateNegOnePiEquiv _ σ)

theorem cycHerbrand_mulPi [Fintype ι] (σ : G) :
    cycHerbrand (Representation.ofMulDistribMulAction G (∀ i, M i)) σ =
      ∏ i, cycHerbrand (Representation.ofMulDistribMulAction G (M i)) σ := by
  rw [cycHerbrand_congr (ρ' := piRep fun i ↦ Representation.ofMulDistribMulAction G (M i))
      (additivePiEquiv M) (fun _ _ ↦ rfl) σ, cycHerbrand_pi]

end Pi

section Orbit

variable {X : Type*} {U : X → Type*} [∀ x, CommGroup (U x)] [MulDistribMulAction G (∀ x, U x)]


variable (G U) in
def mulPiRep : Representation ℤ G (∀ x, Additive (U x)) where
  toFun g := AddMonoidHom.toIntLinearMap ((additivePiEquiv U).toAddMonoidHom.comp
    ((Representation.ofMulDistribMulAction G (∀ x, U x) g).toAddMonoidHom.comp
      (additivePiEquiv U).symm.toAddMonoidHom))
  map_one' := LinearMap.ext fun y ↦ funext fun x ↦
    congrArg (fun f : ∀ x, U x ↦ Additive.ofMul (f x)) (one_smul G fun x ↦ (y x).toMul)
  map_mul' g h := LinearMap.ext fun y ↦ funext fun x ↦
    congrArg (fun f : ∀ x, U x ↦ Additive.ofMul (f x)) (mul_smul g h fun x ↦ (y x).toMul)

variable [MulAction G X]

theorem permutesFactors_mulPiRep
    (h : ∀ (g : G) (f : ∀ x, U x) (x : X), f x = 1 → (g • f) (g • x) = 1) :
    PermutesFactors (mulPiRep (G := G) (U := U)) := fun g f x hf ↦
  congrArg Additive.ofMul (h g (fun x ↦ (f x).toMul) x hf)

variable [Fintype G] [MulAction.IsPretransitive G X]

def cycTateZeroMulOrbitEquiv
    (hU : ∀ (g : G) (f : ∀ x, U x) (x : X), f x = 1 → (g • f) (g • x) = 1) (x₀ : X)
    (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) [MulDistribMulAction D (U x₀)]
    (hU₀ : ∀ (d : D) (f : ∀ x, U x), ((d : G) • f) x₀ = d • f x₀) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    CycTateZero (Representation.ofMulDistribMulAction G (∀ x, U x)) σ ≃+
      CycTateZero (Representation.ofMulDistribMulAction D (U x₀)) τ :=
  (cycTateZeroCongr (ρ' := mulPiRep (G := G) (U := U)) (additivePiEquiv U)
    (fun _ _ ↦ rfl) σ).trans
    (cycTateZeroOrbitEquiv (mulPiRep (G := G) (U := U)) (permutesFactors_mulPiRep hU) x₀ D hD
      (Representation.ofMulDistribMulAction D (U x₀))
      (fun d f ↦ congrArg Additive.ofMul (hU₀ d fun x ↦ (f x).toMul)) σ hσ τ hτ)

def cycTateNegOneMulOrbitEquiv
    (hU : ∀ (g : G) (f : ∀ x, U x) (x : X), f x = 1 → (g • f) (g • x) = 1) (x₀ : X)
    (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) [MulDistribMulAction D (U x₀)]
    (hU₀ : ∀ (d : D) (f : ∀ x, U x), ((d : G) • f) x₀ = d • f x₀) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    CycTateNegOne (Representation.ofMulDistribMulAction G (∀ x, U x)) σ ≃+
      CycTateNegOne (Representation.ofMulDistribMulAction D (U x₀)) τ :=
  (cycTateNegOneCongr (ρ' := mulPiRep (G := G) (U := U)) (additivePiEquiv U)
    (fun _ _ ↦ rfl) σ).trans
    (cycTateNegOneOrbitEquiv (mulPiRep (G := G) (U := U)) (permutesFactors_mulPiRep hU) x₀ D hD
      (Representation.ofMulDistribMulAction D (U x₀))
      (fun d f ↦ congrArg Additive.ofMul (hU₀ d fun x ↦ (f x).toMul)) σ hσ τ hτ)

theorem cycHerbrand_mulOrbit
    (hU : ∀ (g : G) (f : ∀ x, U x) (x : X), f x = 1 → (g • f) (g • x) = 1) (x₀ : X)
    (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) [MulDistribMulAction D (U x₀)]
    (hU₀ : ∀ (d : D) (f : ∀ x, U x), ((d : G) • f) x₀ = d • f x₀) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    cycHerbrand (Representation.ofMulDistribMulAction G (∀ x, U x)) σ =
      cycHerbrand (Representation.ofMulDistribMulAction D (U x₀)) τ := by
  rw [cycHerbrand_eq, cycHerbrand_eq,
    Nat.card_congr (cycTateZeroMulOrbitEquiv hU x₀ D hD hU₀ σ hσ τ hτ).toEquiv,
    Nat.card_congr (cycTateNegOneMulOrbitEquiv hU x₀ D hD hU₀ σ hσ τ hτ).toEquiv]

end Orbit

end Mul

end

end GroundTheory.Global
end

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum GroundTheory.GroupCoh
  AdeleBaseChange SemiLocal

open scoped Pointwise NumberField.LiesOver

noncomputable section

namespace IdeleGroup

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

section Finite

variable (v : HeightOneSpectrum (𝓞 K))


omit [NumberField K] [NumberField L] in
theorem mem_stabilizer_iff_smul_placesOver (w : PlacesOver L v) (σ : Gal(L/K)) :
    σ ∈ MulAction.stabilizer Gal(L/K) w.1.asIdeal ↔ σ • w = w := by
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, coe_smul_placesOver,
    HeightOneSpectrum.ext_iff, smul_asIdeal]

theorem finiteUnitsAbove_smul_apply_of_eq (σ : Gal(L/K))
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) (w w' : PlacesOver L v)
    (h : w' = σ • w) :
    (((σ • y) w' : (w'.1.adicCompletion L)ˣ) : w'.1.adicCompletion L) =
      galEquiv v σ w.1 w'.1 (by rw [h]; rfl) (y w) := by
  subst h
  exact finiteUnitsAbove_smul_apply v σ y w


omit [NumberField K] in
theorem galHom_eq_decomposition_smul (w : PlacesOver L v)
    (σ : MulAction.stabilizer Gal(L/K) w.1.asIdeal) (h : w.1 = (σ : Gal(L/K)) • w.1)
    (x : w.1.adicCompletion L) : galHom (σ : Gal(L/K)) w.1 w.1 h x = σ • x := by
  rw [decomposition_smul_def]
  exact congrFun (congrArg DFunLike.coe (ringHom_ext_adicCompletion w.1
    (continuous_galHom _ _ _ h) (continuous_adicCompletionRingHomOf _ _) fun y ↦ by
      rw [galHom_algebraMap, adicCompletionRingHomOf_algebraMap])) x

theorem finiteUnitsAbove_smul_apply_self (w : PlacesOver L v)
    (σ : MulAction.stabilizer Gal(L/K) w.1.asIdeal)
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) : ((σ : Gal(L/K)) • y) w = σ • y w := by
  have hw : w = (σ : Gal(L/K)) • w :=
    ((mem_stabilizer_iff_smul_placesOver v w σ).1 σ.2).symm
  apply Units.ext
  rw [finiteUnitsAbove_smul_apply_of_eq v _ y w w hw, galEquiv_apply,
    galHom_eq_decomposition_smul]
  rfl

theorem finiteUnitsAbove_smul_apply_eq_one (σ : Gal(L/K))
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) (w : PlacesOver L v) (hy : y w = 1) :
    (σ • y) (σ • w) = 1 :=
  Units.ext (by rw [finiteUnitsAbove_smul_apply, hy, Units.val_one, map_one, Units.val_one])

theorem integerUnitsAbove_smul_apply_self (w : PlacesOver L v)
    (σ : MulAction.stabilizer Gal(L/K) w.1.asIdeal)
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) :
    ((σ : Gal(L/K)) • z) w = σ • z w := by
  apply Units.ext
  apply Subtype.ext
  rw [coe_decomposition_smul_integerUnits, ← coe_integerUnitsAboveIncl_apply,
    integerUnitsAboveIncl_smul, finiteUnitsAbove_smul_apply_self, coe_decomposition_smul_units,
    coe_integerUnitsAboveIncl_apply]

theorem integerUnitsAbove_smul_apply_eq_one (σ : Gal(L/K))
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) (w : PlacesOver L v)
    (hz : z w = 1) : (σ • z) (σ • w) = 1 := by
  apply Units.ext
  apply Subtype.ext
  rw [integerUnitsAbove_smul_apply, hz, Units.val_one, OneMemClass.coe_one, map_one,
    Units.val_one, OneMemClass.coe_one]

variable [IsGalois K L] [Fintype Gal(L/K)]


open AdicLiesOver in
theorem cycHerbrand_finiteUnitsAbove (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (w : PlacesOver L v) :
    cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K)
        ((u : PlacesOver L v) → (u.1.adicCompletion L)ˣ)) σ =
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1.asIdeal)
  let _ : Fintype (MulAction.stabilizer Gal(L/K) w.1.asIdeal) := Fintype.ofFinite _
  rw [cycHerbrand_mulOrbit (U := fun u : PlacesOver L v ↦ (u.1.adicCompletion L)ˣ)
    (finiteUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver v w)
    (finiteUnitsAbove_smul_apply_self v w) σ hσ τ hτ]
  exact (cycHerbrand_adicCompletion_units v w.1 τ hτ).2

theorem subsingleton_cycTateZero_integerUnitsAbove (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (w : PlacesOver L v)
    (he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    Subsingleton (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K)
      ((u : PlacesOver L v) → (u.1.adicCompletionIntegers L)ˣ)) σ) := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1.asIdeal)
  let _ : Fintype (MulAction.stabilizer Gal(L/K) w.1.asIdeal) := Fintype.ofFinite _
  have := subsingleton_cycTateZero_adicCompletionIntegers_units v w.1 he τ hτ
  exact (cycTateZeroMulOrbitEquiv (U := fun u : PlacesOver L v ↦ (u.1.adicCompletionIntegers L)ˣ)
    (integerUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver v w)
    (integerUnitsAbove_smul_apply_self v w) σ hσ τ hτ).toEquiv.subsingleton

theorem subsingleton_cycTateNegOne_integerUnitsAbove (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (w : PlacesOver L v)
    (he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    Subsingleton (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K)
      ((u : PlacesOver L v) → (u.1.adicCompletionIntegers L)ˣ)) σ) := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1.asIdeal)
  let _ : Fintype (MulAction.stabilizer Gal(L/K) w.1.asIdeal) := Fintype.ofFinite _
  have := subsingleton_cycTateNegOne_adicCompletionIntegers_units v w.1 he τ hτ
  exact (cycTateNegOneMulOrbitEquiv
    (U := fun u : PlacesOver L v ↦ (u.1.adicCompletionIntegers L)ˣ)
    (integerUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver v w)
    (integerUnitsAbove_smul_apply_self v w) σ hσ τ hτ).toEquiv.subsingleton

end Finite

section Infinite

def infiniteCompletionCongr {u u' : InfinitePlace L} (h : u = u') :
    u.Completion ≃+* u'.Completion :=
  h ▸ RingEquiv.refl _

omit [NumberField L] in
theorem continuous_infiniteCompletionCongr {u u' : InfinitePlace L} (h : u = u') :
    Continuous (infiniteCompletionCongr h) := by
  subst h
  exact continuous_id

omit [NumberField L] in
theorem infiniteCompletionCongr_algebraMap {u u' : InfinitePlace L} (h : u = u') (x : L) :
    infiniteCompletionCongr h (algebraMap L u.Completion x) = algebraMap L u'.Completion x := by
  subst h
  rfl

theorem continuous_infiniteCompletionMap {M M' : Type*} [Field M] [NumberField M] [Field M']
    [NumberField M'] (τ : M ≃+* M') (w' : InfinitePlace M') :
    Continuous (infiniteCompletionMap τ w') := by
  let _ : Algebra M M' := (τ : M →+* M').toAlgebra
  change Continuous (algebraMap (w'.comap (algebraMap M M')).Completion w'.Completion)
  exact continuous_algebraMap _ _

variable (v : InfinitePlace K)

theorem infiniteUnitsAbove_smul_apply_of_eq (σ : Gal(L/K))
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) (u w : v.placesOver L)
    (h : u.1 = w.1.comap ((σ : L ≃+* L) : L →+* L)) :
    (((σ • y) w : (w.1.Completion)ˣ) : w.1.Completion) =
      infiniteCompletionMap (σ : L ≃+* L) w.1 (infiniteCompletionCongr h (y u)) := by
  obtain rfl : u = ⟨w.1.comap ((σ : L ≃+* L) : L →+* L), comap_mem_placesOver v σ w⟩ :=
    Subtype.ext h
  exact infiniteUnitsAbove_smul_apply v σ y w

omit [NumberField K] [NumberField L] in
theorem eq_comap_smul_placesOver (σ : Gal(L/K)) (w : v.placesOver L) :
    w.1 = (σ • w).1.comap ((σ : L ≃+* L) : L →+* L) := by
  rw [comap_eq_inv_smul, InfinitePlace.coe_smul_placesOver, inv_smul_smul]

theorem infiniteUnitsAbove_smul_apply_eq_one (σ : Gal(L/K))
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) (w : v.placesOver L) (hy : y w = 1) :
    (σ • y) (σ • w) = 1 := by
  apply Units.ext
  rw [infiniteUnitsAbove_smul_apply_of_eq v σ y w (σ • w) (eq_comap_smul_placesOver v σ w), hy,
    Units.val_one, map_one, map_one, Units.val_one]


omit [NumberField K] [NumberField L] in
theorem mem_stabilizer_iff_smul_placesOver_infinite (w : v.placesOver L) (σ : Gal(L/K)) :
    σ ∈ MulAction.stabilizer Gal(L/K) w.1 ↔ σ • w = w := by
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, InfinitePlace.coe_smul_placesOver]


omit [NumberField K] in
theorem infiniteCompletionMap_eq_decomposition_smul (w : v.placesOver L)
    (σ : MulAction.stabilizer Gal(L/K) w.1)
    (h : w.1 = w.1.comap (((σ : Gal(L/K)) : L ≃+* L) : L →+* L)) (x : w.1.Completion) :
    infiniteCompletionMap ((σ : Gal(L/K)) : L ≃+* L) w.1 (infiniteCompletionCongr h x) =
      σ • x := by
  rw [infiniteDecomposition_smul_def]
  have := ringHom_ext_completion w.1
    (f := (infiniteCompletionMap ((σ : Gal(L/K)) : L ≃+* L) w.1).comp
      (infiniteCompletionCongr h).toRingHom)
    ((continuous_infiniteCompletionMap _ _).comp (continuous_infiniteCompletionCongr h))
    (continuous_completionRingHomOf σ.2) fun y ↦ by
      rw [completionRingHomOf_coe]
      have hy : (y : w.1.Completion) = algebraMap L w.1.Completion y.ofAbs := by
        rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
        rfl
      have hy' : ((withAbsMapOf w.1 (σ : Gal(L/K)) y : WithAbs w.1.1) : w.1.Completion) =
          algebraMap L w.1.Completion (withAbsMapOf w.1 (σ : Gal(L/K)) y).ofAbs := by
        rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
        rfl
      rw [hy, hy']
      change infiniteCompletionMap _ w.1
          (infiniteCompletionCongr h (algebraMap L w.1.Completion y.ofAbs)) =
        algebraMap L w.1.Completion (withAbsMapOf w.1 (σ : Gal(L/K)) y).ofAbs
      rw [infiniteCompletionCongr_algebraMap, infiniteCompletionMap_algebraMap,
        ofAbs_withAbsMapOf]
      rfl
  exact congrFun (congrArg DFunLike.coe this) x

theorem infiniteUnitsAbove_smul_apply_self (w : v.placesOver L)
    (σ : MulAction.stabilizer Gal(L/K) w.1) (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    ((σ : Gal(L/K)) • y) w = σ • y w := by
  have hw : w = (σ : Gal(L/K)) • w :=
    ((mem_stabilizer_iff_smul_placesOver_infinite v w σ).1 σ.2).symm
  have h : w.1 = w.1.comap (((σ : Gal(L/K)) : L ≃+* L) : L →+* L) := by
    have h' := eq_comap_smul_placesOver v (σ : Gal(L/K)) w
    rwa [← hw] at h'
  apply Units.ext
  rw [infiniteUnitsAbove_smul_apply_of_eq v (σ : Gal(L/K)) y w w h,
    infiniteCompletionMap_eq_decomposition_smul]
  rfl

variable [IsGalois K L] [Fintype Gal(L/K)]

theorem cycHerbrand_infiniteUnitsAbove (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (w : v.placesOver L) :
    cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K)
        ((u : v.placesOver L) → (u.1.Completion)ˣ)) σ =
      Module.finrank v.Completion w.1.Completion := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1)
  let _ : Fintype (MulAction.stabilizer Gal(L/K) w.1) := Fintype.ofFinite _
  rw [cycHerbrand_mulOrbit (U := fun u : v.placesOver L ↦ (u.1.Completion)ˣ)
    (infiniteUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver_infinite v w)
    (infiniteUnitsAbove_smul_apply_self v w) σ hσ τ hτ]
  exact (cycHerbrand_infiniteCompletion_units v w.1 τ hτ).2

end Infinite

end IdeleGroup

end

end GroundTheory.Global
end

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum GroundTheory.GroupCoh

open scoped NumberField.LiesOver

open SemiLocal (PlacesOver)

noncomputable section

namespace IdeleGroup

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


open SemiLocal in
theorem nonempty_placesOver_of_finite (v : HeightOneSpectrum (𝓞 K)) :
    Nonempty (PlacesOver L v) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := sum_finrank_eq L v
  rw [Finset.univ_eq_empty, Finset.sum_empty] at this
  exact (Module.finrank_pos (R := K) (M := L)).ne this

variable [IsGalois K L] [Fintype Gal(L/K)]

theorem subsingleton_cycTateZero_integerUnitsOutside (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S, ∀ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Subsingleton (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K)
      ((v : ↥Sᶜ) → (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ) := by
  have h : ∀ v : ↥Sᶜ, Subsingleton (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K)
      ((w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ) := fun v ↦ by
    obtain ⟨w⟩ := nonempty_placesOver_of_finite (L := L) v.1
    exact subsingleton_cycTateZero_integerUnitsAbove v.1 σ hσ w (hS v.1 v.2 w)
  exact (cycTateZeroMulPiEquiv
    (fun v : ↥Sᶜ ↦ (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ) σ).toEquiv.subsingleton

theorem subsingleton_cycTateNegOne_integerUnitsOutside (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S, ∀ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Subsingleton (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K)
      ((v : ↥Sᶜ) → (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ) := by
  have h : ∀ v : ↥Sᶜ, Subsingleton (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K)
      ((w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ) := fun v ↦ by
    obtain ⟨w⟩ := nonempty_placesOver_of_finite (L := L) v.1
    exact subsingleton_cycTateNegOne_integerUnitsAbove v.1 σ hσ w (hS v.1 v.2 w)
  exact (cycTateNegOneMulPiEquiv
    (fun v : ↥Sᶜ ↦ (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ) σ).toEquiv.subsingleton

theorem cycHerbrand_integerUnitsOutside (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S, ∀ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K)
      ((v : ↥Sᶜ) → (w : PlacesOver L v.1) → (w.1.adicCompletionIntegers L)ˣ)) σ = 1 := by
  have h0 := subsingleton_cycTateZero_integerUnitsOutside S hS σ hσ
  have h1 := subsingleton_cycTateNegOne_integerUnitsOutside S hS σ hσ
  rw [cycHerbrand_eq, Nat.card_eq_one_iff_unique.2 ⟨h0, ⟨0⟩⟩,
    Nat.card_eq_one_iff_unique.2 ⟨h1, ⟨0⟩⟩]
  norm_num


open AdicLiesOver in
theorem cycHerbrand_sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) (hSf : S.Finite)
    (hS : ∀ v ∉ S, ∀ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (wInf : ∀ v : InfinitePlace K, v.placesOver L) (wFin : ∀ v : HeightOneSpectrum (𝓞 K), PlacesOver L v) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction Gal(L/K) (sIdeles (placesAbove L S))) σ)
        (cycNorm (Representation.ofMulDistribMulAction Gal(L/K) (sIdeles (placesAbove L S)))) ∧
      cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K) (sIdeles (placesAbove L S))) σ =
        (∏ v : InfinitePlace K, (Module.finrank v.Completion (wInf v).1.Completion : ℚ)) *
          ∏ v ∈ hSf.toFinset,
            (Module.finrank (v.adicCompletion K) ((wFin v).1.adicCompletion L) : ℚ) := by
  let _ : Fintype S := hSf.fintype
  have key : cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K)
      (sIdeles (placesAbove L S))) σ =
        (∏ v : InfinitePlace K, (Module.finrank v.Completion (wInf v).1.Completion : ℚ)) *
          ∏ v ∈ hSf.toFinset,
            (Module.finrank (v.adicCompletion K) ((wFin v).1.adicCompletion L) : ℚ) := by
    have hcompat : ∀ (g : Gal(L/K)) (x : Additive (sIdeles (placesAbove L S))),
        (sIdelesEquivProduct S hSf).toAdditive
            (Representation.ofMulDistribMulAction Gal(L/K) (sIdeles (placesAbove L S)) g x) =
          Representation.ofMulDistribMulAction Gal(L/K) (SIdelesProduct L S) g
            ((sIdelesEquivProduct S hSf).toAdditive x) := fun g x ↦ by
      apply Additive.toMul.injective
      exact sIdelesEquivProduct_smul S hSf g x.toMul
    rw [cycHerbrand_congr (sIdelesEquivProduct S hSf).toAdditive hcompat σ]
    rw [cycHerbrand_mulProd, cycHerbrand_mulProd, cycHerbrand_integerUnitsOutside S hS σ hσ,
      mul_one, cycHerbrand_mulPi, cycHerbrand_mulPi,
      Finset.prod_subtype hSf.toFinset (fun v ↦ hSf.mem_toFinset)]
    congr 1
    · exact Finset.prod_congr rfl fun v _ ↦ cycHerbrand_infiniteUnitsAbove v σ hσ (wInf v)
    · exact Finset.prod_congr rfl fun v _ ↦ cycHerbrand_finiteUnitsAbove v.1 σ hσ (wFin v.1)
  refine ⟨hasHerbrandQuotient_of_cycHerbrand_ne_zero ?_, key⟩
  rw [key]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun v _ ↦ ?_)
    (Finset.prod_ne_zero_iff.2 fun v _ ↦ ?_)
  · exact Nat.cast_ne_zero.2 (GroundTheory.Global.InfinitePlace.finrank_completion_pos
      (v := v) (wInf v).1).ne'
  · exact Nat.cast_ne_zero.2 Module.finrank_pos.ne'

end IdeleGroup

end

end GroundTheory.Global
end

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum GroundTheory.GroupCoh Module

open scoped NumberField.LiesOver

open SemiLocal (PlacesOver)

noncomputable section

section Equivariant

variable {G A B : Type*} [Group G] [AddCommGroup A] [AddCommGroup B]

theorem map_cycSubOne {ρA : Representation ℤ G A} {ρB : Representation ℤ G B} {f : A →+ B}
    (hf : ∀ g a, f (ρA g a) = ρB g (f a)) (σ : G) (a : A) :
    f (cycSubOne ρA σ a) = cycSubOne ρB σ (f a) := by
  rw [cycSubOne_apply, cycSubOne_apply, map_sub, hf]

theorem map_cycNorm [Fintype G] {ρA : Representation ℤ G A} {ρB : Representation ℤ G B}
    {f : A →+ B} (hf : ∀ g a, f (ρA g a) = ρB g (f a)) (a : A) :
    f (cycNorm ρA a) = cycNorm ρB (f a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cycNorm_apply, cycNorm_apply, map_sum]
  simp only [hf]

end Equivariant

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

namespace IdeleGroup


open scoped Classical in
theorem finrank_infiniteCompletion_eq_ite [IsGalois K L] (v : InfinitePlace K)
    (w : InfinitePlace L) [w.LiesOver v] :
    (finrank v.Completion w.Completion : ℚ) = if v.IsUnramifiedIn L then 1 else 2 := by
  have hv : w.comap (algebraMap K L) = v := NumberField.InfinitePlace.LiesOver.comap_eq w v
  have hiff : v.IsUnramifiedIn L ↔ w.IsUnramified K := by
    rw [← hv]
    exact NumberField.InfinitePlace.isUnramifiedIn_comap
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [if_pos (hiff.2 h), h.finrank_eq_one v, Nat.cast_one]
  · have hn : ¬ v.IsUnramifiedIn L := fun h' ↦ by
      have := hiff.1 h'
      rw [NumberField.InfinitePlace.IsRamified] at h
      exact h this
    rw [if_neg hn, h.finrank_eq_two v, Nat.cast_ofNat]


open AdicLiesOver in
theorem finrank_adicCompletion_eq_ramificationIdxIn_mul [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v) :
    finrank (v.adicCompletion K) (w.1.adicCompletion L) =
      v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) := by
  rw [finrank_adicCompletion v w.1,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.1.asIdeal Gal(L/K),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.1.asIdeal Gal(L/K)]

end IdeleGroup

namespace IdeleGroup


open AdeleBaseChange in
theorem exists_finset_unramified_sup_sIdeles_eq_top :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v ∉ (S : Set (HeightOneSpectrum (𝓞 K))), ∀ w : PlacesOver L v,
        w.1.asIdeal.ramificationIdx (𝓞 K) = 1) ∧
      (diagonal L).range ⊔ sIdeles (placesAbove L (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤ := by
  classical
  have hfin := Filter.eventually_cofinite.1 (IdeleNorm.eventually_ramificationIdx_eq_one K L)
  obtain ⟨S, hS₀, htop⟩ := exists_finset_superset_sup_sIdeles_placesAbove_eq_top (L := L)
    (hfin.toFinset.image (below K))
  refine ⟨S, fun v hv w ↦ ?_, htop⟩
  by_contra h
  apply hv
  apply hS₀
  rw [Finset.mem_image]
  exact ⟨w.1, hfin.mem_toFinset.2 h, (below_eq_iff w.1 v).2 inferInstance⟩

variable [IsGalois K L]


open AdeleBaseChange AdicLiesOver in
theorem cycHerbrand_ideleClassGroup (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
        (cycNorm (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L))) ∧
      cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ =
        finrank K L := by
  classical
  obtain ⟨S, hram, htop⟩ := exists_finset_unramified_sup_sIdeles_eq_top (K := K) (L := L)
  set T := placesAbove L (S : Set (HeightOneSpectrum (𝓞 K))) with hTdef
  have hT : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ T, g • w ∈ T := fun g w hw ↦
    (smul_mem_placesAbove_iff _ g w).2 hw
  have : Finite T := (placesAbove_finite S.finite_toSet).to_subtype
  set ρA := sUnitRep T hT
  set ρB := Representation.ofMulDistribMulAction Gal(L/K) (sIdeles T)
  set ρC := Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)
  obtain ⟨hinj, hrange, hsurj⟩ :=
    sUnits_sIdeles_placesAbove_exact (L := L) (S : Set (HeightOneSpectrum (𝓞 K))) htop
  let i : Additive (T.unit L) →+ Additive (sIdeles T) := (sUnitsToSIdeles T).toAdditive
  let p : Additive (sIdeles T) →+ Additive (IdeleClassGroup L) :=
    (sIdelesToIdeleClassGroup T).toAdditive
  have hi : Function.Injective i := fun a b h ↦ hinj h
  have hp : Function.Surjective p := hsurj
  have hex : Function.Exact i p := by
    intro b
    have := SetLike.ext_iff.1 hrange b.toMul
    rw [MonoidHom.mem_ker, MonoidHom.mem_range] at this
    exact this.symm
  have hiG : ∀ g a, i (ρA g a) = ρB g (i a) := fun g a ↦ by
    apply Additive.toMul.injective
    apply Subtype.ext
    change diagonal L ((sUnitMap T hT g a.toMul : T.unit L) : Lˣ) =
      g • diagonal L ((a.toMul : T.unit L) : Lˣ)
    rw [smul_diagonal]
    exact congrArg (diagonal L) (Units.ext rfl)
  have hpG : ∀ g b, p (ρB g b) = ρC g (p b) := fun g b ↦
    sIdelesToIdeleClassGroup_smul (S : Set (HeightOneSpectrum (𝓞 K))) g b.toMul
  have hA := hasHerbrandQuotient_sUnitRep (K := K) T hT hσ
  have hiS := map_cycSubOne hiG σ
  have hiN := map_cycNorm hiG
  have hpS : ∀ b, p (cycSubOne ρB σ b) = cycSubOne ρC σ (p b) := fun b ↦ by
    rw [cycSubOne_apply, cycSubOne_apply, map_sub, hpG]
  have hpN : ∀ b, p (cycNorm ρB b) = cycNorm ρC (p b) := fun b ↦ by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [cycNorm_apply, cycNorm_apply, map_sum]
    simp only [hpG]
  obtain ⟨wFin⟩ : Nonempty (∀ v : HeightOneSpectrum (𝓞 K), PlacesOver L v) :=
    ⟨fun v ↦ (nonempty_placesOver_of_finite (L := L) v).some⟩
  obtain ⟨wInf⟩ : Nonempty (∀ v : InfinitePlace K, v.placesOver L) :=
    ⟨fun v ↦ ⟨(InfinitePlace.comap_surjective (K := L) v).choose,
      (GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq v _).2
        (InfinitePlace.comap_surjective (K := L) v).choose_spec⟩⟩
  obtain ⟨hB, hBval⟩ :=
    cycHerbrand_sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet hram σ hσ wInf wFin
  have hC := HasHerbrandQuotient.of_shortExact_left_mid (C := Additive (IdeleClassGroup L)) (p := p) hi hp hex hiS hiN hpS hpN (cycSubOne_cycNorm ρB σ)
    (cycNorm_cycSubOne ρB σ) hA hB
  refine ⟨hC, ?_⟩
  have hmul : cycHerbrand ρB σ = cycHerbrand ρA σ * cycHerbrand ρC σ :=
    herbrandQuotient_eq_mul_of_shortExact (C := Additive (IdeleClassGroup L)) (p := p) hi hp hex hiS hiN hpS hpN (cycSubOne_cycNorm ρB σ)
      (cycNorm_cycSubOne ρB σ) hA hC
  have hInf : ∏ v : InfinitePlace K, (finrank v.Completion (wInf v).1.Completion : ℚ) =
      ∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ) :=
    Finset.prod_congr rfl fun v _ ↦ by
      exact finrank_infiniteCompletion_eq_ite v (wInf v).1
  have hFin : (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : ∃ w ∈ T, w.asIdeal.LiesOver v.asIdeal),
        ((v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) : ℕ) : ℚ)) =
      ∏ v ∈ S.finite_toSet.toFinset,
        (finrank (v.adicCompletion K) ((wFin v).1.adicCompletion L) : ℚ) := by
    rw [Finset.finite_toSet_toFinset]
    rw [finprod_cond_eq_prod_of_cond_iff _ (t := S) fun {v} _ ↦ ?_]
    · exact Finset.prod_congr rfl fun v _ ↦ by
        rw [finrank_adicCompletion_eq_ramificationIdxIn_mul v (wFin v)]
    · constructor
      · rintro ⟨w, hw, hlies⟩
        have := (below_eq_iff w v).2 hlies
        rw [← this]
        exact hw
      · intro hv
        refine ⟨(wFin v).1, ?_, inferInstance⟩
        rw [hTdef, mem_placesAbove, (below_eq_iff (wFin v).1 v).2 inferInstance]
        exact hv
  rw [hBval, cycHerbrand_sUnitRep T hT hσ, hFin, hInf] at hmul
  have hI : (∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ ↦ by split_ifs <;> norm_num
  have hP : (∏ v ∈ S.finite_toSet.toFinset,
      (finrank (v.adicCompletion K) ((wFin v).1.adicCompletion L) : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ ↦ Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hn : (finrank K L : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  field_simp at hmul
  exact hmul.symm

end IdeleGroup

end

end GroundTheory.Global
end

namespace GroundTheory.Global

open NumberField GroundTheory.GroupCoh Module

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


variable (K L) in
def ideleClassToCycTateZero (σ : Gal(L/K)) :
    Additive (IdeleClassGroup K) →+
      CycTateZero (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ :=
  (QuotientAddGroup.mk' _).comp ((ideleClassMap K L).toAdditive.codRestrict _ fun c ↦ by
    rw [AddMonoidHom.mem_ker, cycSubOne_apply, Representation.ofMulDistribMulAction_apply_apply,
      sub_eq_zero]
    exact congrArg Additive.ofMul (smul_ideleClassMap σ _))

theorem ideleClassToCycTateZero_apply (σ : Gal(L/K)) (c : Additive (IdeleClassGroup K)) :
    ideleClassToCycTateZero K L σ c = QuotientAddGroup.mk ⟨Additive.ofMul (ideleClassMap K L c.toMul),
      by
        rw [AddMonoidHom.mem_ker, cycSubOne_apply, Representation.ofMulDistribMulAction_apply_apply,
          sub_eq_zero]
        exact congrArg Additive.ofMul (smul_ideleClassMap σ _)⟩ :=
  rfl

section Galois

variable [IsGalois K L]

theorem cycNorm_ideleClassGroup (c : Additive (IdeleClassGroup L)) :
    cycNorm (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) c =
      Additive.ofMul (ideleClassMap K L (ideleClassNorm K L c.toMul)) := by
  rw [cycNorm_apply, ideleClassMap_ideleClassNorm]
  simp only [Representation.ofMulDistribMulAction_apply_apply]
  rfl

theorem ideleClassToCycTateZero_surjective (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) : Function.Surjective (ideleClassToCycTateZero K L σ) := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H y =>
  obtain ⟨y, hy⟩ := y
  have hfix := (mem_ker_cycSubOne_iff _ hσ y).1 hy
  obtain ⟨c, hc⟩ := (forall_smul_eq_iff_mem_range_ideleClassMap (K := K) y.toMul).1 fun g ↦
    congrArg Additive.toMul (hfix g)
  refine ⟨Additive.ofMul c, ?_⟩
  rw [ideleClassToCycTateZero_apply]
  congr 1
  exact Subtype.ext (by simp [hc])

theorem ker_ideleClassToCycTateZero (σ : Gal(L/K)) :
    (ideleClassToCycTateZero K L σ).ker = Subgroup.toAddSubgroup (ideleClassNorm K L).range := by
  ext c
  rw [AddMonoidHom.mem_ker, ideleClassToCycTateZero_apply, KerModRange.mk_eq_zero_iff]
  change _ ↔ c.toMul ∈ (ideleClassNorm K L).range
  rw [AddMonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨d, hd⟩
    rw [cycNorm_ideleClassGroup] at hd
    exact ⟨d.toMul, ideleClassMap_injective (congrArg Additive.toMul hd)⟩
  · rintro ⟨d, hd⟩
    refine ⟨Additive.ofMul d, ?_⟩
    rw [cycNorm_ideleClassGroup]
    simp [hd]

theorem natCard_cycTateZero_ideleClassGroup (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ) =
      (ideleClassNorm K L).range.index := by
  rw [← Subgroup.index_toAddSubgroup, ← ker_ideleClassToCycTateZero σ, AddSubgroup.index]
  exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _
    (ideleClassToCycTateZero_surjective σ hσ)).toEquiv).symm

theorem index_range_ideleClassNorm (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (ideleClassNorm K L).range.index = finrank K L *
      Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ) ∧
    Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
      ≠ 0 := by
  obtain ⟨hH, hval⟩ := IdeleGroup.cycHerbrand_ideleClassGroup (K := K) (L := L) σ hσ
  have := hH.2
  have hpos : Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K)
      (IdeleClassGroup L)) σ) ≠ 0 := Nat.card_pos.ne'
  refine ⟨?_, hpos⟩
  rw [cycHerbrand_eq, natCard_cycTateZero_ideleClassGroup σ hσ,
    div_eq_iff (Nat.cast_ne_zero.2 hpos)] at hval
  exact_mod_cast hval

theorem finrank_le_index_range_ideleClassNorm [IsCyclic Gal(L/K)] :
    finrank K L ≤ (ideleClassNorm K L).range.index ∧ (ideleClassNorm K L).range.index ≠ 0 := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  obtain ⟨h, hpos⟩ := index_range_ideleClassNorm σ hσ
  rw [h]
  exact ⟨Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hpos),
    mul_ne_zero Module.finrank_pos.ne' hpos⟩

end Galois

theorem firstInequality.{u} : FirstInequality.{u} := by
  intro K L _ _ _ _ _ _ _
  obtain ⟨hle, hne⟩ := finrank_le_index_range_ideleClassNorm (K := K) (L := L)
  have : (ideleClassNorm K L).range.FiniteIndex := ⟨hne⟩
  have : Finite (IdeleClassGroup K ⧸ (ideleClassNorm K L).range) :=
    Subgroup.finite_quotient_of_finiteIndex
  let := Fintype.ofFinite (IdeleClassGroup K ⧸ (ideleClassNorm K L).range)
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_eq_nat_card]
  exact_mod_cast hle

end

end GroundTheory.Global
