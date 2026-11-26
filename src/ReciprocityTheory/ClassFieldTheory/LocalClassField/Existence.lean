module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormLimit

@[expose] public section

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.Kummer
section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.KummerA
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer

open _root_.Neutral.B1

noncomputable section

def quotAddCongr {R R' A A' : Type} [Ring R] [Ring R'] [AddCommGroup A] [AddCommGroup A'] [Module R A] [Module R' A']
    (P : Submodule R A) (P' : Submodule R' A') (e : A ≃+ A') (h : ∀ x, x ∈ P ↔ e x ∈ P') : (A ⧸ P) ≃+ (A' ⧸ P') :=
  QuotientAddGroup.congr P.toAddSubgroup P'.toAddSubgroup e (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h x).1 hx
    · intro hy
      exact ⟨e.symm y, (h _).2 (by simpa using hy), by simp⟩)

section Scalars

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  (rho : Representation R G M) (rho' : Representation ℤ G M) (h : ∀ g m, rho g m = rho' g m)

def oneCocyclesScalarEquiv : Z1 rho ≃+ Z1 rho' where
  toFun f := ⟨f.1, f.2.1, fun g k => by rw [← h]; exact f.2.2 g k⟩
  invFun f := ⟨f.1, f.2.1, fun g k => by rw [h]; exact f.2.2 g k⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def h1ScalarEquiv : H1 rho ≃+ H1 rho' :=
  quotAddCongr _ _ (oneCocyclesScalarEquiv rho rho' h) fun f => by
    show f.1 ∈ Bd1 rho ↔ f.1 ∈ Bd1 rho'
    simp only [mem_contCoboundaries1, h]

end Scalars

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]

theorem kbarRep_apply (σ : GK p K) (x : (PadicAlgCl p)ˣ) :
    kbarRep p K σ (Additive.ofMul x : KbarMult p) =
      (Additive.ofMul (Units.map (σ : PadicAlgCl p →* PadicAlgCl p) x) : KbarMult p) := rfl

theorem contAction_kbarRep : ReciprocityTheory.Gal.ContAction (kbarRep p K) := by
  show Continuous fun q : GK p K × KbarMult p => kbarRep p K q.1 q.2
  rw [continuous_prod_of_discrete_right]
  intro x
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun σ₀ => ?_)
  have hx := stabilizer_isOpen_of_isIntegral (K := K) (L := PadicAlgCl p)
    ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)
  refine ⟨_, hx.preimage (continuous_const_mul σ₀⁻¹), ?_, ?_⟩
  · simp
  · intro σ hσ
    have h1 : (σ₀⁻¹ * σ) ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) = (Additive.toMul x : (PadicAlgCl p)ˣ) := hσ
    have h2 : σ ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) = σ₀ (Additive.toMul x : (PadicAlgCl p)ˣ) := by
      have := congrArg σ₀ h1
      simpa [AlgEquiv.mul_apply] using this
    exact Units.ext h2

def kT : ReciprocityTheory.Coh.TRep ℤ (GK p K) where
  V := KbarMult p
  rho := kbarRep p K
  cont := contAction_kbarRep p K

def muRep : Representation ℤ (GK p K) (ZMod n) where
  toFun g := (charRep (cycK p K n) g).toAddMonoidHom.toIntLinearMap
  map_one' := LinearMap.ext fun x => by
    show charRep (cycK p K n) 1 x = x
    rw [map_one]; rfl
  map_mul' g h := LinearMap.ext fun x => by
    show charRep (cycK p K n) (g * h) x = charRep (cycK p K n) g (charRep (cycK p K n) h x)
    rw [map_mul]; rfl

theorem muRep_apply (g : GK p K) (x : ZMod n) : muRep p K n g x = ((cycK p K n g : (ZMod n)ˣ) : ZMod n) * x := rfl

variable {p n}

def muMap (ζ : (PadicAlgCl p)ˣ) (hζ : ζ ^ n = 1) : ZMod n →ₗ[ℤ] KbarMult p :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun k => (Additive.ofMul (ζ ^ k.val) : KbarMult p)
      map_zero' := by simp; rfl
      map_add' := fun a b => by
        show ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val
        rw [ZMod.val_add, ← pow_eq_pow_mod _ hζ, pow_add] }

theorem muMap_apply (ζ : (PadicAlgCl p)ˣ) (hζ : ζ ^ n = 1) (k : ZMod n) :
    muMap ζ hζ k = (Additive.ofMul (ζ ^ k.val) : KbarMult p) := rfl

theorem muMap_equiv (ζ : (PadicAlgCl p)ˣ) (hζ : ζ ^ n = 1) (g : GK p K) (k : ZMod n) :
    muMap ζ hζ (muRep p K n g k) = kbarRep p K g (muMap ζ hζ k) := by
  rw [muMap_apply, muMap_apply, kbarRep_apply, muRep_apply]
  refine congrArg Additive.ofMul (Units.ext ?_)
  have h1 : ((ζ ^ k.val : (PadicAlgCl p)ˣ) : PadicAlgCl p) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, Units.val_one]
  have h2 := cycN_spec (K := K) (L := PadicAlgCl p) (n := n) g _ h1
  show _ = g ((ζ ^ k.val : (PadicAlgCl p)ˣ) : PadicAlgCl p)
  rw [h2, ← Units.val_pow_eq_pow_val, ZMod.val_mul, ← pow_eq_pow_mod _ hζ, ← pow_mul, mul_comm]

theorem muMap_injective {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) : Function.Injective (muMap ζ hζ.pow_eq_one) := by
  intro a b hab
  exact ZMod.val_injective n (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) hab)


variable (p n) in
def powMap : KbarMult p →ₗ[ℤ] KbarMult p := (n : ℤ) • LinearMap.id

theorem powMap_apply (x : (PadicAlgCl p)ˣ) :
    powMap p n (Additive.ofMul x : KbarMult p) = (Additive.ofMul (x ^ n) : KbarMult p) := by
  show (n : ℤ) • (Additive.ofMul x : Additive (PadicAlgCl p)ˣ) = _
  rw [natCast_zsmul]; rfl

theorem powMap_surjective : Function.Surjective (powMap p n) := by
  intro y
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p) (NeZero.pos n)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne n)] at hz
    exact (Additive.toMul y : (PadicAlgCl p)ˣ).ne_zero hz.symm
  refine ⟨(Additive.ofMul (Units.mk0 z hz0) : KbarMult p), ?_⟩
  rw [powMap_apply]
  exact congrArg Additive.ofMul (Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hz))

theorem exact_muMap_powMap {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) :
    Function.Exact (muMap ζ hζ.pow_eq_one) (powMap p n) := by
  intro y
  constructor
  · intro hy
    have h1 : (Additive.toMul y : (PadicAlgCl p)ˣ) ^ n = 1 := by
      have := powMap_apply (p := p) (n := n) (Additive.toMul y)
      exact (this.symm.trans hy : _)
    have h2 : ((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    obtain ⟨i, hi, hi'⟩ := (IsPrimitiveRoot.coe_units_iff.2 hζ).eq_pow_of_pow_eq_one h2
    have hi'' : ζ ^ i = (Additive.toMul y : (PadicAlgCl p)ˣ) := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hi')
    refine ⟨(i : ZMod n), ?_⟩
    rw [muMap_apply, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hi'']; rfl
  · rintro ⟨k, rfl⟩
    rw [muMap_apply, powMap_apply, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]; rfl

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

namespace Kummer

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]

theorem exists_primitive_unit : ∃ ζ : (PadicAlgCl p)ˣ, IsPrimitiveRoot ζ n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) n
  exact ⟨_, hζ.isUnit_unit (NeZero.ne n)⟩

theorem isEmbedding_muMap {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) :
    Topology.IsEmbedding (muMap ζ hζ.pow_eq_one) :=
  (Continuous.isClosedEmbedding continuous_of_discreteTopology (muMap_injective hζ)).isEmbedding

theorem contAction_muRep : ReciprocityTheory.Gal.ContAction (muRep p K n) := by
  obtain ⟨ζ, hζ⟩ := exists_primitive_unit p n
  show Continuous fun q : GK p K × ZMod n => muRep p K n q.1 q.2
  rw [(isEmbedding_muMap p n hζ).continuous_iff]
  have h : (muMap ζ hζ.pow_eq_one ∘ fun q : GK p K × ZMod n => muRep p K n q.1 q.2) =
      fun q => kbarRep p K q.1 (muMap ζ hζ.pow_eq_one q.2) := funext fun q => muMap_equiv K ζ _ q.1 q.2
  rw [h]
  exact (contAction_kbarRep p K).comp (f := fun q : GK p K × ZMod n => (q.1, muMap ζ hζ.pow_eq_one q.2))
    (continuous_fst.prodMk (continuous_of_discreteTopology.comp continuous_snd))

def muT : TRep ℤ (GK p K) where
  V := ZMod n
  rho := muRep p K n
  cont := contAction_muRep p K n


variable {p n} in
def iP {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) : Pair (muT p K n) (kT p K) :=
  Pair.ofMap (M := muT p K n) (M' := kT p K) (muMap ζ hζ.pow_eq_one)
    (continuous_of_discreteTopology : Continuous (muMap ζ hζ.pow_eq_one : ZMod n → KbarMult p))
    (muMap_equiv K ζ _)

def pP : Pair (kT p K) (kT p K) :=
  Pair.ofMap (M := kT p K) (M' := kT p K) (powMap p n)
    (continuous_of_discreteTopology : Continuous (powMap p n : KbarMult p → KbarMult p))
    fun g m => (map_zsmul (kbarRep p K g) (n : ℤ) m).symm

variable {p n} in
theorem adm {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) : admitted (iP K hζ) (pP p K n) :=
  ⟨rfl, rfl, isEmbedding_muMap p n hζ, exact_muMap_powMap hζ,
    ⟨Function.surjInv (powMap_surjective (p := p) (n := n)),
      (continuous_of_discreteTopology : Continuous (Function.surjInv (powMap_surjective (p := p) (n := n)))),
      Function.surjInv_eq _⟩⟩

def unitsToInvariants' : Additive Kˣ →+ ReciprocityTheory.Gal.H0 (kT p K).rho where
  toFun a := ⟨(Additive.ofMul (Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) a.toMul) : KbarMult p),
    fun σ => Units.ext (σ.commutes _)⟩
  map_zero' := Subtype.ext (by simp; rfl)
  map_add' a b := Subtype.ext (by simp; rfl)

theorem units_to_invariants_prime_injective : Function.Injective (unitsToInvariants' p K) := by
  intro a b hab
  have h1 : Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) a.toMul =
      Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) b.toMul := congrArg Subtype.val hab
  exact Units.map_injective (algebraMap K (PadicAlgCl p)).injective h1

theorem units_to_invariants_prime_surjective : Function.Surjective (unitsToInvariants' p K) := by
  rintro ⟨x, hx⟩
  have : IsGalois K (PadicAlgCl p) := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  have h1 : ∀ σ : GK p K, σ ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) = (Additive.toMul x : (PadicAlgCl p)ˣ) :=
    fun σ => congrArg (fun y : KbarMult p => ((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p)) (hx σ)
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 h1
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (Additive.toMul x : (PadicAlgCl p)ˣ).ne_zero ha.symm
  exact ⟨Additive.ofMul (Units.mk0 a ha0), Subtype.ext (Units.ext ha)⟩

theorem power_map_h0_unitsToInvariants (b : Kˣ) :
    (pP p K n).h0 (unitsToInvariants' p K (Additive.ofMul b)) = unitsToInvariants' p K (Additive.ofMul (b ^ n)) := by
  refine Subtype.ext ?_
  show powMap p n (Additive.ofMul (Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) b) : KbarMult p) = _
  rw [powMap_apply, ← map_pow]
  rfl

end

end Kummer

open Kummer

theorem h1_roots_of_unity_equiv_of_h1_subsingleton (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]
    (h90 : Subsingleton (H1 (kbarRep p K))) :
    Nonempty (H1 (charRep (cycK p K n)) ≃+ Additive (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)) := by
  obtain ⟨ζ, hζ⟩ := exists_primitive_unit p n
  obtain ⟨δ₀, δ₁, -, -, -, -, e2, e3, -⟩ :=
    low_degree_long_exact_sequence ℤ (GK p K) (muT p K n) (kT p K) (kT p K) (iP K hζ) (pP p K n) (adm K hζ)
  have h90' : Subsingleton (ReciprocityTheory.Gal.H1 (kT p K).rho) := h90
  have hs : Function.Surjective δ₀ := fun y => (e3 y).1 (Subsingleton.elim _ _)
  let ψ : Kˣ →* Multiplicative (ReciprocityTheory.Gal.H1 (muT p K n).rho) :=
    AddMonoidHom.toMultiplicativeRight (δ₀.toAddMonoidHom.comp (unitsToInvariants' p K))
  have hψ : ∀ a : Kˣ, ψ a = Multiplicative.ofAdd (δ₀ (unitsToInvariants' p K (Additive.ofMul a))) := fun a => rfl
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := hs y.toAdd
    obtain ⟨a, rfl⟩ := units_to_invariants_prime_surjective p K x
    exact ⟨a.toMul, hx⟩
  have hker : ψ.ker = (powMonoidHom n : Kˣ →* Kˣ).range := by
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    constructor
    · intro ha
      have ha' : δ₀ (unitsToInvariants' p K (Additive.ofMul a)) = 0 := ha
      obtain ⟨y, hy⟩ := (e2 _).1 ha'
      obtain ⟨b, rfl⟩ := units_to_invariants_prime_surjective p K y
      refine ⟨b.toMul, ?_⟩
      have := (power_map_h0_unitsToInvariants p K n b.toMul).symm.trans hy
      exact units_to_invariants_prime_injective p K this
    · rintro ⟨b, rfl⟩
      show δ₀ (unitsToInvariants' p K (Additive.ofMul (b ^ n))) = 0
      exact (e2 _).2 ⟨_, power_map_h0_unitsToInvariants p K n b⟩
  have E1 : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range ≃* Multiplicative (ReciprocityTheory.Gal.H1 (muT p K n).rho) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  exact ⟨(h1ScalarEquiv (charRep (cycK p K n)) (muRep p K n) fun _ _ => rfl).trans (MulEquiv.toAdditiveLeft E1).symm⟩

theorem h1_roots_of_unity_equiv_units_quot_pow (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n] :
    Nonempty (H1 (charRep (cycK p K n)) ≃+ Additive (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)) :=
  h1_roots_of_unity_equiv_of_h1_subsingleton p K n (h1_kbarRep_subsingleton p K)

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistenceB
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function
open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem exists_maximal_exponent_abelian_extension (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hfin : Finite {χ : charGrp (GK p K) // n • χ = 0}) :
    ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), IsAbLK p K L ∧ ∀ χ : charGrp (GK p K), TrivOn p K L χ ↔ n • χ = 0 := by
  let U : Subgroup (GK p K) :=
    { carrier := {g | ∀ χ : charGrp (GK p K), n • χ = 0 → χ.1 (Additive.ofMul g) = 0}
      one_mem' := fun χ _ => map_zero χ.1
      mul_mem' := fun {a b} ha hb χ h => by
        show χ.1 (Additive.ofMul a + Additive.ofMul b) = 0
        rw [map_add (f := _), ha χ h, hb χ h, add_zero]
      inv_mem' := fun {a} ha χ h => by
        show χ.1 (- Additive.ofMul a) = 0
        rw [map_neg, ha χ h, neg_zero] }
  have hU : IsOpen (U : Set (GK p K)) := by
    have h1 : (U : Set (GK p K)) = ⋂ χ : {χ : charGrp (GK p K) // n • χ = 0},
        {g : GK p K | χ.1.1 (Additive.ofMul g) = 0} := by
      ext g
      rw [Set.mem_iInter]
      exact ⟨fun h χ => h χ.1 χ.2, fun h χ hχ => h ⟨χ, hχ⟩⟩
    rw [h1]
    exact isOpen_iInter_of_finite fun χ => IsLocallyConstant.isOpen_fiber χ.1.2 0
  obtain ⟨L, hKL, hLfin, hLU⟩ := exists_subG_eq_of_isOpen hK U hU
  refine ⟨L, ⟨hKL, hLfin, ?_⟩, fun χ => ⟨fun hχ => ?_, fun hχ g hg => ?_⟩⟩
  · rw [hLU, commutator_def, Subgroup.commutator_le]
    intro a _ b _ χ _
    show χ.1 (Additive.ofMul a + Additive.ofMul b + - Additive.ofMul a + - Additive.ofMul b) = 0
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_neg, map_neg]
    abel
  · refine Subtype.ext (AddMonoidHom.ext fun x => ?_)
    show n • χ.1 x = 0
    rw [← map_nsmul]
    refine hχ (Additive.toMul x ^ n) ?_
    rw [hLU]
    intro ψ hψ
    show ψ.1 (n • x) = 0
    rw [map_nsmul]
    exact congrArg (fun f : charGrp (GK p K) => f.1 x) hψ
  · rw [hLU] at hg
    exact hg χ hχ

theorem exists_conj {K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)} (h₀ : K₀ ≤ K) (hK₀ : ∀ (σ : GK p K₀), ∀ x ∈ K, σ x ∈ K)
    (σ : GK p K₀) :
    ∃ c : GK p K →* GK p K, Continuous c ∧ ∀ g, resGK h₀ (c g) = σ * resGK h₀ g * σ⁻¹ := by
  have hn : (subG p K₀ K).Normal := subG_normal_of_stable hK₀
  obtain ⟨e, he, hc, hc'⟩ := exists_equiv_subG h₀
  refine ⟨(e.symm.toMonoidHom.comp (MulAut.conjNormal σ : MulAut (subG p K₀ K)).toMonoidHom).comp e.toMonoidHom, ?_, ?_⟩
  · refine hc'.comp (Continuous.comp ?_ hc)
    refine Continuous.subtype_mk (f := fun h : subG p K₀ K => σ * (h : GK p K₀) * σ⁻¹) ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  · intro g
    show resGK h₀ (e.symm (MulAut.conjNormal σ (e g))) = _
    rw [← he (e.symm _), e.apply_symm_apply, MulAut.conjNormal_apply, he]

theorem maximal_exponent_extension_stable {K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)} (h₀ : K₀ ≤ K) (hK₀ : ∀ (σ : GK p K₀), ∀ x ∈ K, σ x ∈ K) {n : ℕ}
    (hL : IsAbLK p K L) (hL' : ∀ χ : charGrp (GK p K), TrivOn p K L χ ↔ n • χ = 0) (σ : GK p K₀) (x : PadicAlgCl p)
    (hx : x ∈ L) : σ x ∈ L := by
  rw [mem_iff_fixed hL.le]
  intro g hg
  obtain ⟨c, hc, hcg⟩ := exists_conj h₀ hK₀ σ⁻¹
  suffices hmem : c g ∈ subG p K L by
    have h1 : resGK h₀ (c g) x = x := hmem x hx
    rw [hcg, inv_inv] at h1
    have h3 : σ ((σ⁻¹ * resGK h₀ g * σ) x) = g (σ x) := by
      show σ (σ⁻¹ (g (σ x))) = g (σ x)
      exact σ.apply_symm_apply _
    rw [h1] at h3
    exact h3.symm
  by_contra hcon
  obtain ⟨χ, hχ, hne⟩ := exists_char_ne_zero hL (c g) hcon
  let χ' : charGrp (GK p K) := ⟨χ.1.comp (MonoidHom.toAdditive c),
    (show IsLocallyConstant fun g : GK p K => χ.1 (Additive.ofMul g) from χ.2).comp_continuous hc⟩
  have hχ' : n • χ' = 0 := by
    refine Subtype.ext (AddMonoidHom.ext fun y => ?_)
    exact congrArg (fun f : charGrp (GK p K) => f.1 (MonoidHom.toAdditive c y)) ((hL' χ).1 hχ)
  exact hne ((hL' χ').2 hχ' g hg)

theorem mem_subG_adjoin (S : Set (PadicAlgCl p)) (g : GK p K) (h : ∀ x ∈ S, g x = x) :
    g ∈ subG p K (IntermediateField.adjoin ℚ_[p] S) := by
  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap x => exact (g.restrictScalars ℚ_[p]).commutes x
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

theorem isAbelian_cyclotomic_extension (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    IsAbLK p K (K ⊔ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ n = 1}) := by
  have : NeZero n := ⟨hn.ne'⟩
  have hfinS : {ζ : PadicAlgCl p | ζ ^ n = 1}.Finite := by
    have h1 : {ζ : PadicAlgCl p | ζ ^ n = 1} = ↑(Polynomial.nthRootsFinset n (1 : PadicAlgCl p)) := by
      ext ζ
      simp [Polynomial.mem_nthRootsFinset hn]
    rw [h1]
    exact Finset.finite_toSet _
  refine ⟨le_sup_left, ?_, ?_⟩
  · have := hK
    have := hfinS.to_subtype
    have : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ n = 1}) :=
      IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
    exact IntermediateField.finiteDimensional_sup _ _
  · rw [subG_sup, commutator_def, Subgroup.commutator_le]
    intro σ _ τ _
    refine mem_subG_adjoin _ _ fun ζ hζ => ?_
    have hζ' : ζ ^ n = 1 := hζ
    rw [cycN_spec ⁅σ, τ⁆ ζ hζ', map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _),
      Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ', pow_one]

theorem isSolvable_of_abelian_tower {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (hM : IsAbLK p K M) (hL : IsAbLK p M L) [(subG p K L).Normal] :
    Group.IsSolvable (GalLK p K L) := by
  have h2 : derivedSeries (GK p K) 2 ≤ subG p K L := by
    have h1 : derivedSeries (GK p K) 1 ≤ subG p K M := hM.comm
    change ⁅derivedSeries (GK p K) 1, derivedSeries (GK p K) 1⁆ ≤ subG p K L
    refine (Subgroup.commutator_mono h1 h1).trans ?_
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [← range_resGK hM.le] at hg₁ hg₂
    obtain ⟨a, rfl⟩ := hg₁
    obtain ⟨b, rfl⟩ := hg₂
    have h3 : ⁅a, b⁆ ∈ subG p M L :=
      hL.comm (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
    rw [← map_commutatorElement]
    intro x hx
    exact h3 x hx
  refine ⟨⟨2, ?_⟩⟩
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (subG p K L)), eq_bot_iff, Subgroup.map_le_iff_le_comap]
  intro g hg
  show QuotientGroup.mk' _ g ∈ (⊥ : Subgroup _)
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff g).2 (h2 hg)

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistenceA
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem nsmul_mk_one_div (n : ℕ) [NeZero n] (m : ℤ) :
    m • (QuotientAddGroup.mk (1 / (n : ℚ)) : QZ) = QuotientAddGroup.mk ((m : ℚ) / n) := by
  rw [← QuotientAddGroup.mk_zsmul]
  congr 1
  rw [zsmul_eq_mul, mul_one_div]

theorem mk_eq_zero_QZ (q : ℚ) : (QuotientAddGroup.mk q : QZ) = 0 ↔ ∃ k : ℤ, (k : ℚ) = q := by
  rw [QuotientAddGroup.eq_zero_iff]
  exact Iff.rfl

noncomputable def zmodToQZ (n : ℕ) [NeZero n] : ZMod n →+ QZ :=
  ZMod.lift n ⟨zmultiplesHom QZ (QuotientAddGroup.mk (1 / (n : ℚ))), by
    have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
    rw [zmultiplesHom_apply, nsmul_mk_one_div, mk_eq_zero_QZ]
    exact ⟨1, by rw [Int.cast_natCast, div_self hn, Int.cast_one]⟩⟩

theorem zmodToQZ_intCast (n : ℕ) [NeZero n] (m : ℤ) :
    zmodToQZ n (m : ZMod n) = QuotientAddGroup.mk ((m : ℚ) / n) := by
  rw [zmodToQZ, ZMod.lift_coe]
  show zmultiplesHom QZ (QuotientAddGroup.mk (1 / (n : ℚ))) m = _
  rw [zmultiplesHom_apply, nsmul_mk_one_div]

theorem zmodToQZ_injective (n : ℕ) [NeZero n] : Injective (zmodToQZ n) := by
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective a
  rw [zmodToQZ_intCast, mk_eq_zero_QZ] at ha
  obtain ⟨k, hk⟩ := ha
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨k, ?_⟩
  rw [eq_div_iff hn] at hk
  have : ((k * n : ℤ) : ℚ) = (m : ℚ) := by push_cast; exact hk
  rw [mul_comm]
  exact_mod_cast this.symm

theorem exists_zmodToQZ_eq (n : ℕ) [NeZero n] (x : QZ) (hx : n • x = 0) : ∃ a, zmodToQZ n a = x := by
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [← QuotientAddGroup.mk_nsmul, mk_eq_zero_QZ] at hx
  obtain ⟨k, hk⟩ := hx
  refine ⟨(k : ZMod n), ?_⟩
  rw [zmodToQZ_intCast, hk, nsmul_eq_mul, mul_div_cancel_left₀ _ hn]

theorem cycK_eq_one {n : ℕ} [NeZero n] (hμ : ∀ ζ : PadicAlgCl p, ζ ^ n = 1 → ζ ∈ K) (g : GK p K) :
    cycK p K n g = 1 := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) n
  have h1 : g ζ = ζ := g.commutes ⟨ζ, hμ ζ hζ.pow_eq_one⟩
  rw [cycN_spec (K := K) (L := PadicAlgCl p) (n := n) g ζ hζ.pow_eq_one] at h1
  have h2 : ζ ^ ((cycK p K n g : (ZMod n)ˣ) : ZMod n).val = ζ ^ (1 % n) := by
    rw [← pow_eq_pow_mod 1 hζ.pow_eq_one, pow_one]
    exact h1
  have h3 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt 1 (Nat.pos_of_ne_zero (NeZero.ne n))) h2
  rw [← ZMod.val_one_eq_one_mod] at h3
  exact Units.ext (ZMod.val_injective n h3)

theorem card_character_n_torsion {n : ℕ} (hn : 0 < n) (hμ : ∀ ζ : PadicAlgCl p, ζ ^ n = 1 → ζ ∈ K) :
    Nat.card {χ : charGrp (GK p K) // n • χ = 0} = (powMonoidHom n : Kˣ →* Kˣ).range.index := by
  have : NeZero n := ⟨hn.ne'⟩
  have hrho : ∀ g x, charRep (cycK p K n) g x = x := fun g x => by
    rw [charRep_apply, cycK_eq_one hμ, Units.val_one, one_mul]
  obtain ⟨e⟩ := h1_roots_of_unity_equiv_units_quot_pow p K n
  have hbot : (Bd1 (charRep (cycK p K n))).comap (Z1 (charRep (cycK p K n))).subtype = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    obtain ⟨m, hm⟩ := (mem_contCoboundaries1 _ _).1 (Submodule.mem_comap.1 hf)
    rw [Submodule.mem_bot]
    refine Subtype.ext (funext fun g => ?_)
    have := hm g
    rw [hrho, sub_self] at this
    exact this
  let Φ : Z1 (charRep (cycK p K n)) → {χ : charGrp (GK p K) // n • χ = 0} := fun f =>
    ⟨⟨AddMonoidHom.mk' (fun a : Additive (GK p K) => zmodToQZ n (f.1 a.toMul)) fun a b => by
        show zmodToQZ n (f.1 (a.toMul * b.toMul)) = _
        rw [f.2.2, hrho, map_add (f := _)],
      ((IsLocallyConstant.iff_continuous _).2 f.2.1).comp (zmodToQZ n)⟩,
     Subtype.ext (AddMonoidHom.ext fun a => by
        show n • zmodToQZ n (f.1 a.toMul) = 0
        rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero])⟩
  have hΦ : Bijective Φ := by
    constructor
    · intro f f' h
      refine Subtype.ext (funext fun g => zmodToQZ_injective n ?_)
      exact congrArg (fun χ : {χ : charGrp (GK p K) // n • χ = 0} => χ.1.1 (Additive.ofMul g)) h
    · rintro ⟨χ, hχ⟩
      have hex : ∀ g : GK p K, ∃ a, zmodToQZ n a = χ.1 (Additive.ofMul g) := fun g =>
        exists_zmodToQZ_eq n _ (congrArg (fun ψ : charGrp (GK p K) => ψ.1 (Additive.ofMul g)) hχ)
      choose f hf using hex
      have hlc : IsLocallyConstant f := by
        refine IsLocallyConstant.desc f (zmodToQZ n) ?_ (zmodToQZ_injective n)
        have : zmodToQZ n ∘ f = fun g : GK p K => χ.1 (Additive.ofMul g) := funext hf
        rw [this]
        exact χ.2
      refine ⟨⟨f, hlc.continuous, fun g h => zmodToQZ_injective n ?_⟩, ?_⟩
      · rw [hrho, map_add (f := _), hf, hf, hf]
        exact map_add χ.1 (Additive.ofMul g) (Additive.ofMul h)
      · exact Subtype.ext (Subtype.ext (AddMonoidHom.ext fun a => hf a.toMul))
  rw [← Nat.card_congr (Equiv.ofBijective Φ hΦ), ← Nat.card_congr (Submodule.quotEquivOfEqBot _ hbot).toEquiv,
    Nat.card_congr e.toEquiv]
  rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem card_char_torsion {n : ℕ} (hn : 0 < n) (hμ : ∀ ζ : PadicAlgCl p, ζ ^ n = 1 → ζ ∈ K) :
    Nat.card {χ : charGrp (GK p K) // n • χ = 0} = (powMonoidHom n : Kˣ →* Kˣ).range.index :=
  card_character_n_torsion hn hμ

theorem exists_maxExp (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (hfin : Finite {χ : charGrp (GK p K) // n • χ = 0}) :
    ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), IsAbLK p K L ∧ ∀ χ : charGrp (GK p K), TrivOn p K L χ ↔ n • χ = 0 :=
  exists_maximal_exponent_abelian_extension hK hfin

theorem maxExp_stable {K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)} (h₀ : K₀ ≤ K) (hK₀ : ∀ (σ : GK p K₀), ∀ x ∈ K, σ x ∈ K) {n : ℕ}
    (hL : IsAbLK p K L) (hL' : ∀ χ : charGrp (GK p K), TrivOn p K L χ ↔ n • χ = 0) (σ : GK p K₀) (x : PadicAlgCl p)
    (hx : x ∈ L) : σ x ∈ L := maximal_exponent_extension_stable h₀ hK₀ hL hL' σ x hx

theorem normGrp_maxExp (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (hμ : ∀ ζ : PadicAlgCl p, ζ ^ n = 1 → ζ ∈ K)
    (hL : IsAbLK p K L) (hL' : ∀ χ : charGrp (GK p K), TrivOn p K L χ ↔ n • χ = 0) :
    normGrp p K L = (powMonoidHom n : Kˣ →* Kˣ).range := by
  have hle : (powMonoidHom n : Kˣ →* Kˣ).range ≤ normGrp p K L := by
    rintro _ ⟨a, rfl⟩
    have h1 : IsRecip p K L (a ^ n) 1 := by
      intro χ hχ
      rw [pairK_pow, ← pairK_nsmul, (hL' χ).1 hχ, pairK_zero]
      exact map_zero χ.1
    exact (h1.mem_subG_iff hK hL).1 (subG p K L).one_mem
  have hidx : (normGrp p K L).index = (powMonoidHom n : Kˣ →* Kˣ).range.index := by
    rw [index_normGrp hK hL, ← card_trivOn hL, ← card_char_torsion hn hμ]
    exact Nat.card_congr (Equiv.subtypeEquivRight hL')
  have hfi := finiteIndex_range_pow hK hn
  have h2 := Subgroup.relIndex_mul_index hle
  rw [hidx] at h2
  have h3 : (powMonoidHom n : Kˣ →* Kˣ).range.relIndex (normGrp p K L) = 1 :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hfi.index_ne_zero) (by rw [h2, one_mul])
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h3) hle

theorem isAbLK_cyclotomic (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    IsAbLK p K (K ⊔ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ n = 1}) := isAbelian_cyclotomic_extension hK hn

theorem isSolvable_of_ab_of_ab {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (hM : IsAbLK p K M) (hL : IsAbLK p M L) [(subG p K L).Normal] :
    Group.IsSolvable (GalLK p K L) := isSolvable_of_abelian_tower hM hL

theorem exists_unit_ofK (x : KbarMult p) (hx : x ∈ multOf p K) : ∃ u : Kˣ, ofK p K (Additive.ofMul u) = x :=
  ⟨unitOf p K ⟨x, hx⟩, Units.ext rfl⟩

theorem ofK_injective' : Injective (ofK p K) := by
  intro a b hab
  have h1 : Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) a.toMul =
      Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) b.toMul := hab
  exact Units.map_injective (algebraMap K (PadicAlgCl p)).injective h1

theorem exists_normGrp_le_pow (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    ∃ E : IntermediateField ℚ_[p] (PadicAlgCl p), IsAbLK p K E ∧ normGrp p K E ≤ (powMonoidHom n : Kˣ →* Kˣ).range := by
  obtain ⟨M, hMdef⟩ : ∃ M, M = K ⊔ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ n = 1} := ⟨_, rfl⟩
  have hM : IsAbLK p K M := hMdef ▸ isAbLK_cyclotomic hK hn
  have hμ : ∀ ζ : PadicAlgCl p, ζ ^ n = 1 → ζ ∈ M := fun ζ hζ => by
    rw [hMdef]
    exact (le_sup_right : _ ≤ K ⊔ _) (IntermediateField.subset_adjoin _ _ hζ)
  have hfinM := hM.fin
  have hfin : Finite {χ : charGrp (GK p M) // n • χ = 0} := by
    apply Nat.finite_of_card_ne_zero
    rw [card_char_torsion hn hμ]
    exact (finiteIndex_range_pow hfinM hn).index_ne_zero
  obtain ⟨L, hL, hL'⟩ := exists_maxExp hfinM hn hfin
  have hMst : ∀ (σ : GK p K), ∀ x ∈ M, σ x ∈ M := (subG_normal_iff hM.le).1 hM.normal
  have hst : ∀ (σ : GK p K), ∀ x ∈ L, σ x ∈ L := fun σ x hx => maxExp_stable hM.le hMst hL hL' σ x hx
  have : (subG p K L).Normal := subG_normal_of_stable hst
  have hKL : K ≤ L := hM.le.trans hL.le
  have hsol := isSolvable_of_ab_of_ab hM hL
  obtain ⟨E, hE, hEL, hE'⟩ := exists_maxAb hL.fin hKL
  refine ⟨E, hE, ?_⟩
  rw [← normGrp_eq_of_soluble hK hL.fin hKL hsol hE hEL hE']
  intro x hx
  obtain ⟨y, hy, hxy⟩ := (mem_normGrp_iff p K L x).1 hx
  rw [← normHom_trans hL.fin hM.le hL.le y hy] at hxy
  obtain ⟨z, hz⟩ := exists_unit_ofK _ (normHom_mem hL.fin hL.le y hy)
  have hzN : z ∈ normGrp p M L := (mem_normGrp_iff p M L z).2 ⟨y, hy, hz.symm⟩
  rw [normGrp_maxExp hfinM hn hμ hL hL'] at hzN
  obtain ⟨w, rfl⟩ := hzN
  obtain ⟨u, hu⟩ := exists_unit_ofK (K := K) _ (normHom_mem hfinM hM.le _ (ofK_mem p M (Additive.ofMul w)))
  refine ⟨u, ?_⟩
  apply Additive.ofMul.injective
  apply ofK_injective' (K := K)
  rw [← hxy, ← hz]
  show ofK p K (n • Additive.ofMul u) = normHom p K M (ofK p M (n • Additive.ofMul w))
  rw [map_nsmul, map_nsmul, map_nsmul, hu]

theorem existence (hK : FiniteDimensional ℚ_[p] K) (H : Subgroup Kˣ) (hH : H.FiniteIndex) :
    ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), IsAbLK p K L ∧ normGrp p K L = H := by
  obtain ⟨E, hE, hEle⟩ := exists_normGrp_le_pow hK (n := H.index) (Nat.pos_of_ne_zero hH.index_ne_zero)
  obtain ⟨L₀, h1, -, h2⟩ := exists_normGrp_eq_of_le hK hE H (hEle.trans (by
    rintro _ ⟨a, rfl⟩; exact Subgroup.pow_index_mem H a))
  exact ⟨L₀, h1, h2⟩

theorem exists_not_mem_UKi (hK : FiniteDimensional ℚ_[p] K) (a : Kˣ) (ha : a ≠ 1) : ∃ i, a ∉ UKi p K i := by
  have hε : 0 < ‖((a : K) : PadicAlgCl p) - 1‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    intro h
    exact ha (Units.ext (Subtype.ext h))
  have he : (0 : ℝ) < eK p K := by exact_mod_cast eK_pos p K hK
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  have hq1 : (p : ℝ) ^ (- 1 / (eK p K : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (div_neg_of_neg_of_pos (by norm_num) he)
  obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one hε hq1
  refine ⟨i, fun hx => absurd (lt_of_le_of_lt ((mem_UKi_iff p K i a).1 hx).2 ?_) (lt_irrefl _)⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le] at hi
  convert hi using 2
  ring

theorem eq_one_of_forall_mem_normGrp (hK : FiniteDimensional ℚ_[p] K) (a : Kˣ) (h : ∀ L, IsAbLK p K L → a ∈ normGrp p K L) : a = 1 := by
  by_contra ha
  obtain ⟨π, hπ⟩ := exists_vK_eq_one p K hK
  obtain ⟨i, hi⟩ := exists_not_mem_UKi hK a ha
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = (vK p K a).natAbs + 1 := ⟨_, rfl⟩
  have hopen : IsOpen ((UKi p K i ⊔ Subgroup.zpowers (π ^ m) : Subgroup Kˣ) : Set Kˣ) :=
    Subgroup.isOpen_mono le_sup_left (isOpen_UKi i)
  have hfi : (UKi p K i ⊔ Subgroup.zpowers (π ^ m)).FiniteIndex :=
    finiteIndex_of_isOpen_of_vK hK _ hopen (x := π ^ m)
      ((le_sup_right : _ ≤ UKi p K i ⊔ _) (Subgroup.mem_zpowers _)) (by rw [vK_pow, hπ, hm]; positivity)
  obtain ⟨L, hL, hLH⟩ := existence hK _ hfi
  have haH : a ∈ UKi p K i ⊔ Subgroup.zpowers (π ^ m) := hLH ▸ h L hL
  obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.1 haH
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have hu0 : vK p K u = 0 := (mem_UK_iff p K hK u).1 ((mem_UKi_iff p K i u).1 hu).1
  have hv : vK p K (u * (π ^ m) ^ k) = k * m := by
    rw [vK_mul, hu0, vK_zpow, vK_pow, hπ]; ring
  rw [hv] at hm
  have hk : k = 0 := by
    by_contra hk
    have h1 : 1 ≤ k.natAbs := Int.natAbs_pos.2 hk
    rw [Int.natAbs_mul, Int.natAbs_natCast] at hm
    nlinarith
  rw [hk, zpow_zero, mul_one] at hi
  exact hi hu

end ReciprocityTheory.DiscreteGroups.LocalClassField
