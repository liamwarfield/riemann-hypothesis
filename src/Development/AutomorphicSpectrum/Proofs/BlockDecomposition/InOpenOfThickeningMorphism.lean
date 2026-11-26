module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmIndCoinvariants
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoOfIsClosedImmersionOfThickenings
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechDifferentialOneInclusion
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TerminalRes
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphism
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphism
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ThickPt

theorem inU_map {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (V : X.Opens)
    {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') : InU V T → InU V T' := by
  intro h
  unfold CrystallineSemistableComparison.Pb.InU at h ⊢
  obtain ⟨ψ, _, _, _, hle, hpt, _, _, _⟩ := φ
  have key : CrystallineSemistableComparison.Pb.pt T' =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J ψ hle)) ≫ CrystallineSemistableComparison.Pb.pt T := by
    unfold CrystallineSemistableComparison.Pb.pt
    rw [← hpt]
    rfl
  rw [key]
  intro x _
  exact @h ((Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J ψ hle))).base x) trivial

end GlobalTheory.CompanionTheory.ThickPt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphismStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inOpen_of_thickening_morphism : ∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (V : X.Opens) {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T'), InU V T → InU V T' := by
  first | exact @GlobalTheory.CompanionTheory.ThickPt.inU_map | exact GlobalTheory.CompanionTheory.ThickPt.inU_map | (intros; apply GlobalTheory.CompanionTheory.ThickPt.inU_map <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIff
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIff
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Thick

theorem inU_iInf_finset : ∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {ι : Type} (U : ι → X.Opens) (S : Finset ι) (T : Thick (nlFun γ p X q κ)), InU (⨅ α ∈ S, U α) T ↔ ∀ α ∈ S, InU (U α) T := by
  intro O _ R _ I γ p X q κ ι U S T
  classical
  have htop : InU (⊤ : X.Opens) T := fun x _ => trivial
  have hinf : ∀ V W : X.Opens, InU (V ⊓ W) T ↔ InU V T ∧ InU W T := by
    intro V W
    constructor
    · intro h
      exact ⟨fun x hx => (h hx).1, fun x hx => (h hx).2⟩
    · intro h x hx
      exact ⟨h.1 hx, h.2 hx⟩
  induction S using Finset.induction_on with
  | empty => simpa using htop
  | insert a s ha ih =>
    rw [Finset.iInf_insert]
    refine (hinf _ _).trans ?_
    constructor
    · rintro ⟨h1, h2⟩ α hα
      rcases Finset.mem_insert.1 hα with rfl | hα
      · exact h1
      · exact ih.1 h2 α hα
    · intro h
      exact ⟨h a (Finset.mem_insert_self a s), ih.2 fun α hα => h α (Finset.mem_insert_of_mem hα)⟩

end GlobalTheory.CompanionTheory.Thick
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIffStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inOpen_finite_inf_iff : ∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {ι : Type} (U : ι → X.Opens) (S : Finset ι) (T : Thick (nlFun γ p X q κ)), InU (⨅ α ∈ S, U α) T ↔ ∀ α ∈ S, InU (U α) T := by
  first | exact @GlobalTheory.CompanionTheory.Thick.inU_iInf_finset | exact GlobalTheory.CompanionTheory.Thick.inU_iInf_finset | (intros; apply GlobalTheory.CompanionTheory.Thick.inU_iInf_finset <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof Matrix Topology

namespace GlobalTheory.CompanionTheory.ThetaGLLen

section Abstract

variable {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V]

def twRel (ρ : Representation ℂ Γ V) (ψ : Γ →* ℂˣ) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ (γ : Γ) (v : V), w = ρ γ v - (ψ γ : ℂ) • v}

end Abstract

section Fibre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

def fibChar (μ : kˣ →* ℂˣ) : GL a k × (GL c k × GL d k) →* ℂˣ :=
  (detChar a (μ⁻¹ * absPow k (((Fintype.card c : ℂ) + Fintype.card d) / 2))).comp (MonoidHom.fst _ _) *
    (detChar c (μ * absPow k (-(Fintype.card a : ℂ) / 2) * absPow k (-(Fintype.card d : ℂ) / 2))).comp
      ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _)) *
    (detChar d (μ * absPow k (-(Fintype.card a : ℂ) / 2) * absPow k ((Fintype.card c : ℂ) / 2))).comp
      ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _))

def fibBase (κ : ℕ) :
    Representation ℂ (GL a k × GL c k) (SB (RankIn (k := k) (a := a) (b := c) {κ})) :=
  sbRep (fun x γ => ⟨act x.1 γ, by rw [rank_act]; exact x.2⟩)
    (fun x => Subtype.ext (act_one x.1)) (fun x γ δ => Subtype.ext (act_mul x.1 γ δ))
    (fun γ => ((continuous_act γ).comp continuous_subtype_val).subtype_mk _)

def fibRep (μ : kˣ →* ℂˣ) (κ : ℕ) :
    Representation ℂ (GL a k × (GL c k × GL d k)) (SB (RankIn (k := k) (a := a) (b := c) {κ})) :=
  twist ((fibBase a c κ).comp ((MonoidHom.id _).prodMap (MonoidHom.fst _ _))) (fibChar a c d μ)

theorem fibRep_apply (μ : kˣ →* ℂˣ) (κ : ℕ) (g : GL a k) (p₁ : GL c k) (p₂ : GL d k)
    (φ : SB (RankIn (k := k) (a := a) (b := c) {κ})) (y : RankIn (k := k) (a := a) (b := c) {κ}) :
    (fibRep a c d μ κ (g, p₁, p₂) φ).1 y = (fibChar a c d μ (g, p₁, p₂) : ℂ) *
      φ.1 ⟨act y.1 (g, p₁), by rw [rank_act]; exact y.2⟩ := rfl

def rightRep (κ : ℕ) :
    Representation ℂ (GL a k) (SB (RankIn (k := k) (a := a) (b := c) {κ})) :=
  (fibBase a c κ).comp (MonoidHom.inl _ _)

end Fibre

end GlobalTheory.CompanionTheory.ThetaGLLen
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMulPowEqIncl
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.Away

variable {K : Type} [Field K] {n d : ℕ}

theorem mon_pow {M : AddSubmonoid (Gam n d)} (c : Gam n d) (hc : c ∈ M) (N : ℕ) :
    mon K c hc ^ N = mon K (N • c) (M.nsmul_mem hc N) := by
  simp only [mon, AddMonoidAlgebra.single_pow, one_pow]
  rfl

theorem incl_injective {M M' : AddSubmonoid (Gam n d)} (h : M ≤ M') :
    Function.Injective (incl (K := K) h) := by
  intro x y hxy
  simp only [incl, AddMonoidAlgebra.mapDomainAlgHom_apply] at hxy
  exact AddMonoidAlgebra.mapDomain_injective (AddSubmonoid.inclusion_injective h) hxy

theorem exists_mul_pow_eq_incl {M M' : AddSubmonoid (Gam n d)} (h : M ≤ M') (c : Gam n d) (hc : c ∈ M)
    (hg : ∀ g ∈ M', ∃ N : ℕ, g + N • c ∈ M) (z : Rg K M') :
    ∃ (N : ℕ) (a : Rg K M), z * incl h (mon K c hc ^ N) = incl h a := by
  induction z using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, 0, by simp⟩
  | add f g hf hg' =>
    obtain ⟨N₁, a₁, h₁⟩ := hf
    obtain ⟨N₂, a₂, h₂⟩ := hg'
    refine ⟨N₁ + N₂, a₁ * mon K c hc ^ N₂ + a₂ * mon K c hc ^ N₁, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, ← h₁, ← h₂, pow_add, map_mul]
    ring
  | single m k =>
    obtain ⟨N, hN⟩ := hg m.1 m.2
    refine ⟨N, AddMonoidAlgebra.single ⟨m.1 + N • c, hN⟩ k, ?_⟩
    rw [mon_pow, incl_mon]
    simp only [mon, incl, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.single_mul_single, mul_one]
    simp
    rfl

theorem isLocalization_away : ∀ {K : Type} [Field K] {n d : ℕ} {M M' : AddSubmonoid (Gam n d)} (h : M ≤ M') (c : Gam n d) (hc : c ∈ M), -c ∈ M' → (∀ g ∈ M', ∃ N : ℕ, g + N • c ∈ M) → letI := (incl (K := K) h).toRingHom.toAlgebra; IsLocalization.Away (mon K c hc) (Rg K M') := by
  intro K _ n d M M' h c hc hneg hg
  letI := (incl (K := K) h).toRingHom.toAlgebra
  have hal : ∀ x, algebraMap (Rg K M) (Rg K M') x = incl h x := fun _ => rfl
  have hu : IsUnit (incl h (mon K c hc)) := by
    rw [incl_mon]
    refine IsUnit.of_mul_eq_one (mon K (-c) hneg) ?_
    rw [mon_mul]
    simp only [mon, add_neg_cancel]
    rfl
  refine (isLocalization_iff _ _).2 ⟨?_, fun z => ?_, fun {x y} hxy => ⟨1, ?_⟩⟩
  · rintro ⟨_, N, rfl⟩
    rw [hal, map_pow]
    exact hu.pow N
  · obtain ⟨N, a, ha⟩ := exists_mul_pow_eq_incl h c hc hg z
    exact ⟨(a, ⟨mon K c hc ^ N, N, rfl⟩), ha⟩
  · rw [incl_injective h hxy]

end GlobalTheory.CompanionTheory.SurjectionOntoH4.Away
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolyEqPolyEquiv
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.PolyBij
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {n d : ℕ}

theorem cone_empty_nonneg {g : Gam n d} (hg : g ∈ (cone ∅ : AddSubmonoid (Gam n d))) (e : E n d) : 0 ≤ g e := by
  have hg' : (∀ l : Fin n, 0 ≤ g (Sum.inl l)) ∧ (∀ j ∉ (∅ : Finset (Fin d)), 0 ≤ g (Sum.inr j)) ∧
      0 ≤ tdeg g := hg
  rcases e with l | j
  · exact hg'.1 l
  · exact hg'.2.1 j (Finset.notMem_empty j)

theorem coe_mem_cone (f : E n d →₀ ℕ) :
    (fun e => (f e : ℤ) : Gam n d) ∈ (cone ∅ : AddSubmonoid (Gam n d)) := by
  show (∀ l : Fin n, (0 : ℤ) ≤ (f (Sum.inl l) : ℤ)) ∧
    (∀ j ∉ (∅ : Finset (Fin d)), (0 : ℤ) ≤ (f (Sum.inr j) : ℤ)) ∧ 0 ≤ tdeg (fun e => (f e : ℤ) : Gam n d)
  refine ⟨fun l => Int.natCast_nonneg _, fun j _ => Int.natCast_nonneg _, ?_⟩
  exact Finset.sum_nonneg fun j _ => Int.natCast_nonneg _

def expEquiv : (E n d →₀ ℕ) ≃+ (cone ∅ : AddSubmonoid (Gam n d)) where
  toFun f := ⟨fun e => (f e : ℤ), coe_mem_cone f⟩
  invFun g := Finsupp.equivFunOnFinite.symm fun e => (g.1 e).toNat
  left_inv f := by
    ext e
    simp
  right_inv g := by
    refine Subtype.ext (funext fun e => ?_)
    simpa using cone_empty_nonneg g.2 e
  map_add' f f' := by
    refine Subtype.ext (funext fun e => ?_)
    simp

def polyEquiv (K : Type) [Field K] : Bp K n d ≃ₐ[K] R0 K n d (∅ : Finset (Fin d)) :=
  AddMonoidAlgebra.domCongr K K expEquiv

theorem expEquiv_single (e : E n d) :
    (expEquiv (Finsupp.single e 1) : (cone ∅ : AddSubmonoid (Gam n d))) = ⟨oneE e, oneE_mem ∅ e⟩ := by
  refine Subtype.ext (funext fun e' => ?_)
  change ((Finsupp.single e 1 : E n d →₀ ℕ) e' : ℤ) = (Pi.single e (1 : ℤ) : E n d → ℤ) e'
  by_cases h : e' = e
  · subst h
    simp
  · simp [Finsupp.single_apply, Pi.single_apply, h, Ne.symm h]

theorem poly_eq_polyEquiv (K : Type) [Field K] :
    poly n K (∅ : Finset (Fin d)) = (polyEquiv K).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro e
  rw [poly_X, polyEquiv,
    MvPolynomial.X, ← MvPolynomial.single_eq_monomial]
  erw [AddMonoidAlgebra.domCongr_single, expEquiv_single]
  rfl

theorem poly_bijective {K : Type} [Field K] {n d : ℕ} :
    Function.Bijective (poly n K (∅ : Finset (Fin d))) := by
  rw [poly_eq_polyEquiv]
  exact (polyEquiv K).bijective

end GlobalTheory.CompanionTheory.SurjectionOntoH4.PolyBij
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonLNegMul
set_option autoImplicit false
noncomputable section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.LaurentD

variable {K : Type} [Field K] {n d : ℕ}

theorem monL_zero' : monL K (0 : Gam n d) = 1 := rfl

theorem monL_add' (g g' : Gam n d) : monL K (g + g') = monL K g * monL K g' := by
  unfold monL
  rw [mon_mul]

theorem monL_neg_mul (g : Gam n d) : monL K (-g) * monL K g = 1 := by
  rw [← monL_add', neg_add_cancel, monL_zero']

def lam (K : Type) [Field K] {n d : ℕ} (g : Gam n d) : Ω[Lr K n d⁄K] :=
  monL K (-g) • KaehlerDifferential.D K (Lr K n d) (monL K g)

theorem lam_add (g g' : Gam n d) : lam K (g + g') = lam K g + lam K g' := by
  unfold lam
  have h1 : monL K (-(g + g')) = monL K (-g) * monL K (-g') := by
    rw [neg_add, monL_add']
  have e1 : monL K (-g) * monL K (-g') * monL K g = monL K (-g') := by
    rw [mul_comm (monL K (-g)), mul_assoc, monL_neg_mul, mul_one]
  have e2 : monL K (-g) * monL K (-g') * monL K g' = monL K (-g) := by
    rw [mul_assoc, monL_neg_mul, mul_one]
  rw [monL_add', Derivation.leibniz, smul_add, smul_smul, smul_smul, h1, e1, e2]
  exact add_comm _ _

def lamHom (K : Type) [Field K] (n d : ℕ) : Gam n d →+ Ω[Lr K n d⁄K] :=
  AddMonoidHom.mk' (lam K) lam_add

theorem exp_eq_sum (g : Gam n d) : g = ∑ e, g e • (oneE e : Gam n d) := by
  funext x
  simp [oneE, Finset.sum_apply, Pi.single_apply]

theorem lam_eq_sum (g : Gam n d) : lam K g = ∑ e, (g e) • (dl e : Ω[Lr K n d⁄K]) := by
  have h : lam K g = lamHom K n d g := rfl
  rw [h]
  conv_lhs => rw [exp_eq_sum g]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_zsmul]
  rfl

theorem D_monL (g : Gam n d) :
    KaehlerDifferential.D K (Lr K n d) (monL K g) = monL K g • ∑ e, (g e) • (dl e : Ω[Lr K n d⁄K]) := by
  rw [← lam_eq_sum]
  unfold lam
  rw [smul_smul, mul_comm, monL_neg_mul, one_smul]

end GlobalTheory.CompanionTheory.SurjectionOntoH4.LaurentD
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIsoOfIsClosedImmersionOfThickenings
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.FormalClosed

open GlobalTheory.ThickeningClosed

theorem mem_of_forall_mem_over_closedFibre {R : Type} [CommRing R] {I : Ideal R}
    (hI : I ≤ Ideal.jacobson ⊥) {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    [UniversallyClosed f] {W : Set X} (hW : IsOpen W)
    (h : ∀ x, I ≤ (f x).asIdeal → x ∈ W) (x : X) : x ∈ W := by
  by_contra hx
  have hZ : IsClosed (f '' Wᶜ) := f.isClosedMap _ hW.isClosed_compl
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (f x).asIdeal (f x).isPrime.ne_top
  let p : PrimeSpectrum (CommRingCat.of R) := ⟨m, hm.isPrime⟩
  have h1 : p ∈ closure ({f x} : Set (PrimeSpectrum (CommRingCat.of R))) :=
    (PrimeSpectrum.le_iff_mem_closure (f x) p).1 hle
  have hfx : f x ∈ f '' Wᶜ := ⟨x, hx, rfl⟩
  have hp : p ∈ f '' Wᶜ :=
    closure_minimal (Set.singleton_subset_iff.2 hfx) hZ h1
  obtain ⟨z, hz, hzp⟩ := hp
  apply hz
  apply h z
  rw [hzp]
  show I ≤ m
  refine hI.trans ?_
  unfold Ideal.jacobson
  exact sInf_le ⟨bot_le, hm⟩

theorem eq_bot_of_forall_mem_zeroLocusOpen {X : Scheme.{0}} (K : X.IdealSheafData)
    (h : ∀ x, x ∈ zeroLocusOpen K) : K = ⊥ := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_bot]
  apply le_antisymm _ bot_le
  intro a ha
  rw [Ideal.mem_bot]
  by_contra ha0
  let J : Ideal Γ(X, U) := LinearMap.ker (LinearMap.toSpanSingleton Γ(X, U) Γ(X, U) a)
  have hJ : J ≠ ⊤ := by
    intro hJ
    apply ha0
    have h1 : (1 : Γ(X, U)) ∈ J := by rw [hJ]; exact Submodule.mem_top
    simpa [J] using h1
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  obtain ⟨s, hs, hsa⟩ := exists_mul_eq_zero_of_mem K U ⟨m, hm.isPrime⟩ (h _) ha
  apply hs
  apply hJm
  simpa [J] using hsa

theorem isIso_of_isClosedImmersion_of_thickenings :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom →
    ∀ (E : Scheme.{0}) (j : E ⟶ X.left), IsClosedImmersion j →
      (∀ e, ∃ h : (thickObj R I e X).left ⟶ E, h ≫ j = pullback.fst X.hom (thick R I e)) →
        IsIso j := by
  intro R _ _ I hI X hX E j hj hth
  haveI := hX
  haveI := hj
  haveI := hI
  haveI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
  apply eq_bot_of_forall_mem_zeroLocusOpen
  intro x
  refine mem_of_forall_mem_over_closedFibre (IsAdicComplete.le_jacobson_bot I) X.hom
    (isOpen_zeroLocusOpen _) ?_ x
  intro y hy
  refine mem_of_thickenings I X.hom j ?_ y hy
  intro n
  obtain ⟨l, hl⟩ := hth n
  exact ⟨l, hl⟩

end GlobalTheory.CompanionTheory.FormalClosed
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompOfCechPt
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.CechPts

open CategoryTheory.Limits

variable {Y X : Scheme.{0}} (f : Y ⟶ X)

def baseOf {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) : U ⟶ X :=
  (WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)).app (op U) z

def compOf {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) (i : Fin (k + 1)) : U ⟶ Y :=
  (WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i).app (op U) z

theorem compOf_comp {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) (i : Fin (k + 1)) :
    compOf f z i ≫ f = baseOf f z := by
  have e := WidePullback.π_arrow (fun _ : Fin (k + 1) => yoneda.map f) i
  have := congrArg (fun t => t.app (op U) z) e
  exact this

theorem ext_comp {k : ℕ} {U : Scheme.{0}} (z z' : Sx (cech f) k U)
    (hb : baseOf f z = baseOf f z') (hc : ∀ i, compOf f z i = compOf f z' i) : z = z' := by
  apply yonedaEquiv.symm.injective
  apply WidePullback.hom_ext (fun _ : Fin (k + 1) => yoneda.map f)
  · intro i
    have : yonedaEquiv (yonedaEquiv.symm z ≫ WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i) =
        yonedaEquiv (yonedaEquiv.symm z' ≫ WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i) := by
      rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hc i
    exact yonedaEquiv.injective this
  · have : yonedaEquiv (yonedaEquiv.symm z ≫ WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)) =
        yonedaEquiv (yonedaEquiv.symm z' ≫ WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)) := by
      rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hb
    exact yonedaEquiv.injective this

theorem baseOf_cechPt {k : ℕ} {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ Y)) (h : ∀ i, y i ≫ f = x) :
    baseOf f (cechPt f k x y h) = x := by
  have e := WidePullback.lift_base (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map x)
    (fun i => yoneda.map (y i)) (fun i => by rw [← yoneda.map_comp, h i])
  exact (congrArg (fun t => t.app (op U) (𝟙 U)) e).trans (Category.id_comp x)

theorem compOf_cechPt {k : ℕ} {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ Y)) (h : ∀ i, y i ≫ f = x)
    (i : Fin (k + 1)) : compOf f (cechPt f k x y h) i = y i := by
  have e := WidePullback.lift_π (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map x)
    (fun i => yoneda.map (y i)) (fun i => by rw [← yoneda.map_comp, h i]) i
  exact (congrArg (fun t => t.app (op U) (𝟙 U)) e).trans (Category.id_comp (y i))

theorem baseOf_res {k : ℕ} {U V : Scheme.{0}} (g : V ⟶ U) (z : Sx (cech f) k U) :
    baseOf f (Sx.res g z) = g ≫ baseOf f z :=
  NatTrans.naturality_apply (WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)) g.op z

theorem compOf_res {k : ℕ} {U V : Scheme.{0}} (g : V ⟶ U) (z : Sx (cech f) k U) (i : Fin (k + 1)) :
    compOf f (Sx.res g z) i = g ≫ compOf f z i :=
  NatTrans.naturality_apply (WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i) g.op z

theorem baseOf_along {p k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk k) :
    baseOf f (Sx.along z θ) = baseOf f z := by
  have e := WidePullback.lift_base (arrows := fun _ : Fin (p + 1) => yoneda.map f)
    (WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f))
    (fun i => WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) (θ.toOrderHom i)) (by simp)
  exact congrArg (fun t => t.app (op U) z) e

theorem compOf_along {p k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk k) (i : Fin (p + 1)) :
    compOf f (Sx.along z θ) i = compOf f z (θ.toOrderHom i) := by
  have e := WidePullback.lift_π (arrows := fun _ : Fin (p + 1) => yoneda.map f)
    (WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f))
    (fun i => WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) (θ.toOrderHom i)) (by simp) i
  exact congrArg (fun t => t.app (op U) z) e

theorem map_aug {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) :
    Sx.map (GlobalTheory.EtC.cechAug f) z = baseOf f z := rfl

theorem cechPt_spec : CrystallineSemistableComparison.E.CechPt := by
  intro Y X f k U
  refine ⟨fun z => ⟨baseOf f z, compOf f z, compOf_comp f z, ?_⟩, ?_, ?_⟩
  · exact ext_comp f _ _ (baseOf_cechPt f _ _ _).symm fun i => (compOf_cechPt f _ _ _ i).symm
  · intro x y h x' y' h' e
    funext i
    rw [← compOf_cechPt f x y h i, e, compOf_cechPt]
  · intro x y h
    refine ⟨?_, ?_, ?_⟩
    · rw [map_aug, baseOf_cechPt]
    · intro V g
      apply ext_comp
      · rw [baseOf_res, baseOf_cechPt, baseOf_cechPt]
      · intro i
        rw [compOf_res, compOf_cechPt, compOf_cechPt]
    · intro p θ
      apply ext_comp
      · rw [baseOf_along, baseOf_cechPt, baseOf_cechPt]
      · intro i
        rw [compOf_along, compOf_cechPt, compOf_cechPt]

end GlobalTheory.CompanionTheory.CechPts
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseLimitCohomologyComparison
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LimLift

open CrystallineSemistableComparison.CechClassBoundaries

variable {R : Type} [CommRing R]

theorem cls_congr {K : Cx.{1} R} {j : ℕ} {a b : K.X j} (h : a = b) (ha : K.d j a = 0) (hb : K.d j b = 0) :
    K.cls a ha = K.cls b hb := by
  subst h
  rfl

theorem pow_tf {K : Cx.{1} R} {c : R} (ht : ∀ j (x : K.X j), c • x = 0 → x = 0) (n j : ℕ) (x : K.X j)
    (h : c ^ n • x = 0) : x = 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ', mul_smul] at h
    exact ih (ht _ _ h)

theorem ker_red {K L : Cx.{1} R} (c : R) (n : ℕ) (r : Cx.Hom K L (RingHom.id R))
    (hs : ∀ j, Function.Surjective (r.f j)) (hk : ∀ j x, r.f j x = 0 ↔ ∃ y, x = c ^ n • y)
    (ht : ∀ j (x : K.X j), c • x = 0 → x = 0) (j : ℕ) (z : K.H j) (hz : r.mapH j z = 0) :
    ∃ y, z = c ^ n • y := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K j).1 z
  rw [mapH_cls' r a ha (cyc r a ha), (CrystallineSemistableComparison.P.cls_surj L j).2.1] at hz
  have hv : ∃ v : K.X j, v ∈ K.B j ∧ K.d j v = 0 ∧ r.f j (a - v) = 0 := by
    cases j with
    | zero =>
      refine ⟨0, (mem_boundaries_zero_iff _).2 rfl, map_zero _, ?_⟩
      rw [sub_zero]
      exact (mem_boundaries_zero_iff _).1 hz
    | succ j =>
      obtain ⟨b, hb⟩ := (mem_Bs _).1 hz
      obtain ⟨v, rfl⟩ := hs j b
      refine ⟨K.d j v, (mem_Bs _).2 ⟨v, rfl⟩, K.dd j v, ?_⟩
      rw [map_sub, ← r.comm, hb, sub_self]
  obtain ⟨v, hvB, hvd, h0⟩ := hv
  obtain ⟨y, hy⟩ := (hk j _).1 h0
  have hdy : K.d j y = 0 := by
    refine pow_tf ht n _ _ ?_
    rw [← map_smul, ← hy, map_sub, ha, hvd, sub_zero]
  refine ⟨K.cls y hdy, ?_⟩
  have hcy : K.d j (c ^ n • y) = 0 := by rw [map_smul, hdy, smul_zero]
  rw [← cls_smul _ _ hdy hcy, (CrystallineSemistableComparison.P.cls_surj K j).2.2.1 _ _ ha hcy, ← hy]
  simpa using hvB

theorem kill_H {K L : Cx.{1} R} (c : R) (n : ℕ) (r : Cx.Hom K L (RingHom.id R))
    (hs : ∀ j, Function.Surjective (r.f j)) (hk : ∀ j x, r.f j x = 0 ↔ ∃ y, x = c ^ n • y)
    (j : ℕ) (h : L.H j) : c ^ n • h = 0 := by
  obtain ⟨w, hw, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L j).1 h
  obtain ⟨a, rfl⟩ := hs j w
  have h0 : c ^ n • r.f j a = 0 := by
    rw [← map_smul]
    exact (hk j _).2 ⟨a, rfl⟩
  have hd : L.d j (c ^ n • r.f j a) = 0 := by rw [h0, map_zero]
  rw [← cls_smul _ _ hw hd, (CrystallineSemistableComparison.P.cls_surj L j).2.1, h0]
  exact zero_mem _

theorem lift_level {K L : Cx.{1} R} (c : R) (n k j : ℕ) (r : Cx.Hom K L (RingHom.id R))
    (hs : ∀ j, Function.Surjective (r.f j)) (hk : ∀ j x, r.f j x = 0 ↔ ∃ y, x = c ^ n • y)
    (ht : ∀ j (x : K.X j), c • x = 0 → x = 0)
    (hA : ∀ (x : K.H (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0) (x : L.H j) :
    ∃ y : K.H j, r.mapH j y = c ^ k • x := by
  obtain ⟨w, hw, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L j).1 x
  obtain ⟨a, rfl⟩ := hs j w
  have h1 : r.f (j + 1) (K.d j a) = 0 := by rw [← r.comm]; exact hw
  obtain ⟨b, hb⟩ := (hk (j + 1) _).1 h1
  have hdb : K.d (j + 1) b = 0 := by
    refine pow_tf ht n _ _ ?_
    rw [← map_smul, ← hb, K.dd]
  have hcb : K.d (j + 1) (c ^ n • b) = 0 := by rw [map_smul, hdb, smul_zero]
  have h2 : c ^ n • K.cls b hdb = 0 := by
    rw [← cls_smul _ _ hdb hcb, (CrystallineSemistableComparison.P.cls_surj K (j + 1)).2.1]
    exact (mem_Bs _).2 ⟨a, hb⟩
  have h3 := hA _ n h2
  have hkb : K.d (j + 1) (c ^ k • b) = 0 := by rw [map_smul, hdb, smul_zero]
  rw [← cls_smul _ _ hdb hkb, (CrystallineSemistableComparison.P.cls_surj K (j + 1)).2.1] at h3
  obtain ⟨e, he⟩ := (mem_Bs _).1 h3
  have hy : K.d j (c ^ k • a - c ^ n • e) = 0 := by
    rw [map_sub, map_smul, map_smul, he, hb, smul_smul, smul_smul, mul_comm, sub_self]
  have hr : r.f j (c ^ k • a - c ^ n • e) = c ^ k • r.f j a := by
    rw [map_sub, (hk j _).2 ⟨e, rfl⟩, sub_zero, map_smul]
  have hd : L.d j (c ^ k • r.f j a) = 0 := by rw [map_smul, hw, smul_zero]
  refine ⟨K.cls _ hy, ?_⟩
  rw [mapH_cls' r _ hy (cyc r _ hy), ← cls_smul _ _ hw hd]
  exact cls_congr hr _ _

theorem mapH_tr {K L M : Cx.{1} R} (r : Cx.Hom K L (RingHom.id R)) (r' : Cx.Hom K M (RingHom.id R))
    (t : Cx.Hom L M (RingHom.id R)) (j : ℕ) (h : ∀ x, t.f j (r.f j x) = r'.f j x) (z : K.H j) :
    t.mapH j (r.mapH j z) = r'.mapH j z := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K j).1 z
  rw [mapH_cls' r a ha (cyc r a ha), mapH_cls' t _ _ (cyc t _ (cyc r a ha)), mapH_cls' r' a ha (cyc r' a ha)]
  exact cls_congr (h a) _ _

theorem lim_lift : ∀ {R : Type} [CommRing R] {K : Cx.{1} R} (Kn : ℕ → Cx.{1} R) (c : R) (red : ∀ n, Cx.Hom K (Kn n) (RingHom.id R))
    (tr : ∀ n, Cx.Hom (Kn (n + 1)) (Kn n) (RingHom.id R)), (∀ n j x, (tr n).f j ((red (n + 1)).f j x) = (red n).f j x) →
    (∀ n j, Function.Surjective ((red n).f j)) → (∀ n j x, (red n).f j x = 0 ↔ ∃ y, x = c ^ n • y) → (∀ j (x : K.X j), c • x = 0 → x = 0) →
    ∀ j k : ℕ, (∀ (x : K.H (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0) → (∀ x : K.H j, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0) →
    (∀ x : ℕ → K.H j, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) → ∃ z : K.H j, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y) →
    (∀ x : ∀ n, (Kn n).H j, (∀ n, (tr n).mapH j (x (n + 1)) = x n) → ∃ z : K.H j, ∀ n, (red n).mapH j z = c ^ (2 * k) • x n) ∧
    ∀ z : K.H j, (∀ n, (red n).mapH j z = 0) → c ^ k • z = 0 := by
  intro R _ K Kn c red tr hc hs hk ht j k hA hB hC
  refine ⟨fun x hx => ?_, fun z hz => hB z fun n => ker_red c n (red n) (hs n) (hk n) ht j z (hz n)⟩
  choose y hy using fun n => lift_level c n k j (red n) (hs n) (hk n) ht hA (x n)
  have hdiff : ∀ n, ∃ u, y (n + 1) - y n = c ^ n • u := by
    intro n
    refine ker_red c n (red n) (hs n) (hk n) ht j _ ?_
    rw [map_sub, ← mapH_tr (red (n + 1)) (red n) (tr n) j (hc n j), hy, hy, map_smul, hx, sub_self]
  obtain ⟨z, hz⟩ := hC y hdiff
  refine ⟨z, fun n => ?_⟩
  obtain ⟨u, hu⟩ := hz n
  have e : z = c ^ k • y n + c ^ n • u := by rw [← hu]; abel
  rw [e, map_add (f := _), map_smul, map_smul, hy, kill_H c n (red n) (hs n) (hk n), add_zero, smul_smul, ← pow_add, two_mul]

end GlobalTheory.CompanionTheory.LimLift
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ToConeSurjective
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ChartBij
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {n d : ℕ}

def coord (k : Fin d) (g : Gam n d) : E n d → ℤ
  | Sum.inl l => g (Sum.inl l)
  | Sum.inr j => if j = k then tdeg g else g (Sum.inr j)

theorem coord_add (k : Fin d) (g g' : Gam n d) : coord k (g + g') = coord k g + coord k g' := by
  funext e
  rcases e with l | j
  · rfl
  · by_cases h : j = k
    · simp [coord, h, tdeg_add]
    · simp [coord, h]

theorem coord_zero (k : Fin d) : coord k (0 : Gam n d) = 0 := by
  funext e
  rcases e with l | j
  · rfl
  · by_cases h : j = k
    · simp [coord, h, tdeg]
    · simp [coord, h]

theorem tdeg_ratE (k j : Fin d) : tdeg (ratE k j : Gam n d) = 0 := by
  have h1 := tdeg_add (ratE k j : Gam n d) (oneE (Sum.inr k))
  have h2 : (ratE k j : Gam n d) + oneE (Sum.inr k) = oneE (Sum.inr j) := by simp [ratE]
  rw [h2, tdeg_oneE_inr, tdeg_oneE_inr] at h1
  linarith

theorem coord_wv (k : Fin d) (e e' : E n d) : coord k (wv k e) e' = if e' = e then 1 else 0 := by
  rcases e with l | j <;> rcases e' with l' | j'
  · simp [coord, wv, oneE, Pi.single_apply]
  · by_cases h : j' = k
    · simp [coord, wv, oneE, h, tdeg, Pi.single_apply]
    · simp [coord, wv, oneE, h, Pi.single_apply]
  · by_cases h : j = k
    · simp [coord, wv, oneE, h, Pi.single_apply]
    · simp [coord, wv, ratE, oneE, h, Pi.single_apply]
  · by_cases h : j = k
    · subst h
      by_cases h' : j' = j
      · simp [coord, wv, h', tdeg_oneE_inr]
      · simp [coord, wv, oneE, h', Pi.single_apply]
    · by_cases h' : j' = k
      · subst h'
        have hne : ¬ j' = j := fun e => h e.symm
        simp [coord, wv, h, hne, tdeg_ratE]
      · by_cases h'' : j' = j
        · subst h''
          simp [coord, wv, ratE, oneE, h, h', Pi.single_apply]
        · simp [coord, wv, ratE, oneE, h, h', h'', Pi.single_apply]

theorem coord_inj (k : Fin d) {g g' : Gam n d} (h : coord k g = coord k g') : g = g' := by
  have hj : ∀ j, j ≠ k → g (Sum.inr j) = g' (Sum.inr j) := fun j hj => by
    have := congrFun h (Sum.inr j)
    simpa [coord, hj] using this
  have ht : tdeg g = tdeg g' := by
    have := congrFun h (Sum.inr k)
    simpa [coord] using this
  funext e
  rcases e with l | j
  · exact congrFun h (Sum.inl l)
  · by_cases hjk : j = k
    · subst hjk
      unfold tdeg at ht
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at ht
      have : ∑ x ∈ Finset.univ.erase j, g (Sum.inr x) = ∑ x ∈ Finset.univ.erase j, g' (Sum.inr x) :=
        Finset.sum_congr rfl fun x hx => hj x (Finset.ne_of_mem_erase hx)
      linarith
    · exact hj j hjk

def toCone (k : Fin d) : (E n d →₀ ℕ) →+ (cone {k} : AddSubmonoid (Gam n d)) :=
  Finsupp.liftAddHom fun e => multiplesHom _ ⟨wv k e, wv_mem (Finset.mem_singleton_self k) e⟩

theorem toCone_single (k : Fin d) (e : E n d) :
    toCone k (Finsupp.single e 1) = ⟨wv k e, wv_mem (Finset.mem_singleton_self k) e⟩ := by
  simp [toCone]

theorem coord_toCone (k : Fin d) (f : E n d →₀ ℕ) (e : E n d) :
    coord k (toCone k f : Gam n d) e = f e := by
  induction f using Finsupp.induction_linear with
  | zero => simp [coord_zero]
  | add f g hf hg =>
    rw [map_add (f := _), AddSubmonoid.coe_add, coord_add, Pi.add_apply, hf, hg]
    simp
  | single a b =>
    induction b with
    | zero => simp [coord_zero]
    | succ b ih =>
      rw [show Finsupp.single a (b + 1) = Finsupp.single a b + Finsupp.single a 1 by simp,
        map_add, AddSubmonoid.coe_add, coord_add, Pi.add_apply, ih, toCone_single]
      simp only [coord_wv, Finsupp.add_apply, Finsupp.single_apply]
      by_cases h : e = a
      · simp [h]
      · have : ¬ a = e := fun x => h x.symm
        simp [h, this]

theorem toCone_injective (k : Fin d) : Function.Injective (toCone k : (E n d →₀ ℕ) → _) := by
  intro f f' h
  ext e
  have h1 := coord_toCone k f e
  rw [h, coord_toCone] at h1
  exact_mod_cast h1.symm

theorem coord_nonneg (k : Fin d) {g : Gam n d} (hg : g ∈ (cone {k} : AddSubmonoid (Gam n d))) (e : E n d) :
    0 ≤ coord k g e := by
  rcases e with l | j
  · exact hg.1 l
  · by_cases h : j = k
    · simpa [coord, h] using hg.2.2
    · simpa [coord, h] using hg.2.1 j (by simpa using h)

theorem toCone_surjective (k : Fin d) : Function.Surjective (toCone k : (E n d →₀ ℕ) → _) := by
  rintro ⟨g, hg⟩
  refine ⟨Finsupp.equivFunOnFinite.symm fun e => (coord k g e).toNat, Subtype.ext (coord_inj k ?_)⟩
  funext e
  rw [coord_toCone]
  simpa using coord_nonneg k hg e

def coneEquiv (k : Fin d) : (E n d →₀ ℕ) ≃+ (cone {k} : AddSubmonoid (Gam n d)) :=
  AddEquiv.ofBijective (toCone k) ⟨toCone_injective k, toCone_surjective k⟩

theorem chart_bijective {K : Type} [Field K] {n d : ℕ} (k : Fin d) :
    Function.Bijective (MvPolynomial.aeval (R := K)
      (fun e : E n d => mon K (wv k e) (wv_mem (Finset.mem_singleton_self k) e)) : Bp K n d →ₐ[K] R0 K n d {k}) := by
  let Φ : Bp K n d ≃ₐ[K] R0 K n d {k} := AddMonoidAlgebra.domCongr K K (coneEquiv k)
  have h : (MvPolynomial.aeval (R := K)
      (fun e : E n d => mon K (wv k e) (wv_mem (Finset.mem_singleton_self k) e)) : Bp K n d →ₐ[K] R0 K n d {k}) = Φ.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro e
    rw [MvPolynomial.aeval_X]
    change _ = AddMonoidAlgebra.domCongr K K (coneEquiv k) (AddMonoidAlgebra.single (Finsupp.single e 1) 1)
    simp only [mon, coneEquiv]
    simp
    exact congrArg (fun m => AddMonoidAlgebra.single m (1 : K)) (toCone_single k e).symm
  rw [h]
  exact Φ.bijective

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ChartBij
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EdgeCupOfSteps
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem edgeCup_of_steps : CrystallineSemistableComparison.E.CupCls → CrystallineSemistableComparison.E.StTop → CrystallineSemistableComparison.E.StCupA → CrystallineSemistableComparison.E.StCupB → CrystallineSemistableComparison.E.EdgeCup := by
  intro hCls hTop hA hB
  unfold CrystallineSemistableComparison.E.EdgeCup
  intro R _ C _ F₁ F₂ F₃ T₁ T₂ T₃ P μ hT₁ hT₂ i j n hn x y a b hx hy
  obtain ⟨z, hz, hzx, rfl⟩ := hx
  obtain ⟨z', hz', hzy, rfl⟩ := hy
  obtain ⟨hu, hcls⟩ := hCls R C F₁ F₂ F₃ P i j n hn z z' hz hz'
  refine ⟨P.cupC hn z z', hu, ?_, hcls.symm⟩
  have hyy := hTop R C F₂ T₂ hT₂ j z' hz' j 0 y hzy
  have hb := hB R C F₁ F₂ F₃ T₁ T₂ T₃ P μ hT₁ hT₂ i j n hn z z' hz j 0 i (add_zero i) y hzy
  exact hA R C F₁ F₂ F₃ T₁ T₂ T₃ P μ hT₁ hT₂ i j n z y (P.cupC hn z z') hyy.1 hyy.2 hb i 0 n hn x hzx

end GlobalTheory.CompanionTheory.EdgeMap
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StAdd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.StairAdd

theorem stAdd : CrystallineSemistableComparison.E.StAdd := by
  intro R _ C _ F T j z z' s
  induction s with
  | zero =>
    intro k x x' hx hx'
    obtain ⟨h, rfl⟩ := hx
    obtain ⟨h', rfl⟩ := hx'
    subst h
    exact ⟨⟨rfl, by simp⟩, ⟨rfl, by simp⟩⟩
  | succ s ih =>
    intro k x x' hx hx'
    obtain ⟨a, rfl, ha⟩ := hx
    obtain ⟨a', rfl, ha'⟩ := hx'
    obtain ⟨h1, h2⟩ := ih (k + 1) _ _ ha ha'
    refine ⟨⟨a + a', by simp, ?_⟩, ⟨a - a', by simp, ?_⟩⟩
    · simpa [map_add (f := _), smul_add] using h1
    · simpa [map_sub, smul_sub] using h2

end GlobalTheory.CompanionTheory.StairAdd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EdgeUniqOf
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeClass

theorem edgeUniq_of : CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.StAdd → CrystallineSemistableComparison.E.StUniq → CrystallineSemistableComparison.E.EdgeUniq := by
  intro _ hadd huniq R _ C _ F T hG j x x' h h' hx hx'
  obtain ⟨z, hz, st, rfl⟩ := hx
  obtain ⟨z', hz', st', rfl⟩ := hx'
  refine ⟨⟨z + z', ?_, (hadd R C F T j z z' j 0 x x' st st').1, ?_⟩, ?_⟩
  · rw [map_add (f := _), hz, hz', add_zero]
  · rfl
  · intro hv
    have st2 : T.St (z - z') j 0 (x - x') := (hadd R C F T j z z' j 0 x x' st st').2
    have hB : z - z' ∈ (cx F).B j := by
      cases j with
      | zero => exact huniq R C F T hG 0 (z - z') 0 0 (x - x') st2 hv
      | succ s =>
        obtain ⟨b, hb, hbx⟩ := hv
        obtain ⟨a, hax, sta⟩ := st2
        refine huniq R C F T hG (s + 1) (z - z') s 1 _ sta ?_
        refine ⟨a - b, ?_, ?_⟩
        · rw [map_sub, hax, hbx, sub_self]
        · rw [map_sub, hb, sub_zero, pow_zero, one_smul]
    exact (Submodule.Quotient.eq _).2 hB

end GlobalTheory.CompanionTheory.EdgeClass
end
