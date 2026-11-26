module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHolds
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ExpToSat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpSat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefOverOfFiniteOrbit

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowD
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw

namespace GlobalTheory.CompanionTheory.ZUnf

section Rows

variable {K : Type} [Field K] {n ρ p : ℕ}

def zinc (hn : ρ + p = n) : (Fin ρ → K) →ₗ[K] (Fin n → K) where
  toFun u i := Sum.elim u (fun _ : Fin p => (0 : K)) ((finSumFinEquiv.trans (finCongr hn)).symm i)
  map_add' u v := by
    funext i
    simp only [Pi.add_apply]
    generalize (finSumFinEquiv.trans (finCongr hn)).symm i = j
    rcases j with j | j <;> simp
  map_smul' c u := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    generalize (finSumFinEquiv.trans (finCongr hn)).symm i = j
    rcases j with j | j <;> simp

def wM (hn : ρ + p = n) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 (bl hn 0 0 0 1) (bl hn 1 0 0 0) (bl hn (-1) 0 0 0) (bl hn 0 0 0 1)

def nM (hn : ρ + p = n) (ζ : Matrix (Fin ρ) (Fin ρ) K) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 1 (bl hn ζ 0 0 0) 0 1

def sM (hn : ρ + p = n) (σ : K →+* K) (η : Matrix (Fin ρ) (Fin p) K) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 (bl hn 1 η 0 1) 0 0 (bl hn 1 0 (-cT σ η) 1)

def eM (hn : ρ + p = n) (a b c d : Matrix (Fin p) (Fin p) K) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d)

def rowC (hn : ρ + p = n) (η : Matrix (Fin ρ) (Fin p) K) (a c : Matrix (Fin p) (Fin p) K) : Matrix (Fin n) (Fin n) K :=
  bl hn (-1) (-(η * a)) 0 c

def rowD (hn : ρ + p = n) (σ : K →+* K) (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K)
    (b d : Matrix (Fin p) (Fin p) K) : Matrix (Fin n) (Fin n) K :=
  bl hn (-ζ) (-(η * b)) (-cT σ η) d

end Rows

variable {D : D7} {n ρ p : ℕ}

def zKer (hn : ρ + p = n) (x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) : Submodule D.host.E (Fin ρ → D.host.E) :=
  (cellKer x).comap (zinc hn)

end GlobalTheory.CompanionTheory.ZUnf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfVB

abbrev Hc {S A B C : Type} [CommRing S] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module S A] [Module S B] [Module S C] (f : A →ₗ[S] B) (g : B →ₗ[S] C) : Type :=
  LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype

def Lift {A Q N : Type} [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q]
    [AddCommGroup N] [Module A N] (b : Q →ₗ[A] N) : Prop :=
  ∀ (J : Ideal A) (t : A), J ≠ ⊤ → (∀ x ∈ IsLocalRing.maximalIdeal A, x * t ∈ J) → ∀ z : Q,
    b z ∈ (J ⊔ Ideal.span {t}) • (⊤ : Submodule A N) →
    ∃ x : Q, b x ∈ J • (⊤ : Submodule A N) ∧
      x - z ∈ (J ⊔ Ideal.span {t}) • (⊤ : Submodule A Q)

def SmallLift {R P₀ P₁ P₂ : Type} [CommRing R] [AddCommGroup P₀] [AddCommGroup P₁]
    [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁)
    (a₁ : P₁ →ₗ[R] P₂) : Prop :=
  ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B] (t : B), (∀ x, ¬ IsUnit x → x * t = 0) →
    ∀ z : (B ⧸ Ideal.span {t}) ⊗[R] P₁, a₁.lTensor _ z = 0 →
    ∃ (x : B ⊗[R] P₁) (y : (B ⧸ Ideal.span {t}) ⊗[R] P₀), a₁.lTensor B x = 0 ∧
      (Ideal.Quotient.mkₐ R (Ideal.span {t})).toLinearMap.rTensor P₁ x - z = a₀.lTensor _ y

section Semi

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

def liftSemi {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : M →ₛₗ[algebraMap R S] N) : S ⊗[R] M →ₗ[S] N :=
  letI : Module R N := Module.compHom N (algebraMap R S)
  haveI : IsScalarTower R S N := ⟨fun r s n ↦ by
    change (r • s) • n = algebraMap R S r • s • n
    rw [Algebra.smul_def, mul_smul]⟩
  LinearMap.liftBaseChange S
    { toFun := f, map_add' := f.map_add, map_smul' := fun r x ↦ f.map_smulₛₗ r x }

theorem liftSemi_tmul {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : M →ₛₗ[algebraMap R S] N) (s : S) (x : M) : liftSemi f (s ⊗ₜ x) = s • f x := by
  simp [liftSemi]

end Semi

section Cochains

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {C : Type} [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} S}

def c0 (m : BC F F') : C0 F →ₛₗ[algebraMap R S] C0 F' where
  toFun f T := m.α T (f T)
  map_add' f g := funext fun T ↦ map_add (m.α T) _ _
  map_smul' r f := funext fun T ↦ m.smul T r (f T)

def c1 (m : BC F F') : C1 F →ₛₗ[algebraMap R S] C1 F' where
  toFun f T T' φ := m.α T' (f T T' φ)
  map_add' f g := funext fun T ↦ funext fun T' ↦ funext fun φ ↦ map_add (m.α T') _ _
  map_smul' r f := funext fun T ↦ funext fun T' ↦ funext fun φ ↦ m.smul T' r (f T T' φ)

def c2 (m : BC F F') : C2 F →ₛₗ[algebraMap R S] C2 F' where
  toFun f T T' T'' φ ψ := m.α T'' (f T T' T'' φ ψ)
  map_add' f g := funext fun T ↦ funext fun T' ↦ funext fun T'' ↦ funext fun φ ↦ funext fun ψ ↦
    map_add (m.α T'') _ _
  map_smul' r f := funext fun T ↦ funext fun T' ↦ funext fun T'' ↦ funext fun φ ↦ funext fun ψ ↦
    m.smul T'' r (f T T' T'' φ ψ)

def th0 (m : BC F F') : S ⊗[R] C0 F →ₗ[S] C0 F' := liftSemi (c0 m)

def th1 (m : BC F F') : S ⊗[R] C1 F →ₗ[S] C1 F' := liftSemi (c1 m)

def th2 (m : BC F F') : S ⊗[R] C2 F →ₗ[S] C2 F' := liftSemi (c2 m)

end Cochains

def IsModel {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    {P₀ P₁ P₂ : Type} [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀]
    [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F)
    (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F) : Prop :=
  a₁ ∘ₗ a₀ = 0 ∧ ψ₁ ∘ₗ a₀ = d0 F ∘ₗ ψ₀ ∧ ψ₂ ∘ₗ a₁ = d1 F ∘ₗ ψ₁ ∧
    ∀ M : ModuleCat.{0} R,
      QIsoAt (0 : R →ₗ[R] M ⊗[R] P₀) (a₀.lTensor M) (0 : R →ₗ[R] M ⊗[R] C0 F) ((d0 F).lTensor M)
        (ψ₀.lTensor M) ∧
      QIsoAt (a₀.lTensor M) (a₁.lTensor M) ((d0 F).lTensor M) ((d1 F).lTensor M) (ψ₁.lTensor M)

end GlobalTheory.CompanionTheory.PerfVB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

variable {R : Type} [CommRing R] {X : Scheme.{0}}

abbrev ext (s : X ⟶ Sp R) (J : Ideal R) (U : X.Opens) : Ideal Γ(X, U) :=
  J.map (GlobalTheory.SmallExtLift.cst s U)

def tr (M : LB X) {A : Type} (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (a b : A) :
    Γ(X, V a ⊓ V b) :=
  rs X (inf_le_inf (hj a) (hj b)) (M.g (j a) (j b)).val

def trInv (M : LB X) {A : Type} (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (a b : A) :
    Γ(X, V a ⊓ V b) :=
  rs X (inf_le_inf (hj a) (hj b)) (M.g (j a) (j b))⁻¹.val

theorem tr_mul_trInv (M : LB X) {A : Type} (V : A → X.Opens) (j : A → M.ι)
    (hj : ∀ a, V a ≤ M.U (j a)) (a b : A) : tr M V j hj a b * trInv M V j hj a b = 1 := by
  simp only [tr, trInv, ← map_mul, Units.mul_inv, map_one]

section Triple

variable {A : Type} (V : A → X.Opens) (a b d : A)

theorem le₁₂ : V a ⊓ V b ⊓ V d ≤ V a ⊓ V b := inf_le_left

theorem le₂₃ : V a ⊓ V b ⊓ V d ≤ V b ⊓ V d := le_inf (inf_le_left.trans inf_le_right) inf_le_right

theorem le₁₃ : V a ⊓ V b ⊓ V d ≤ V a ⊓ V d := le_inf (inf_le_left.trans inf_le_left) inf_le_right

end Triple

theorem tr_cocycle {M : LB X} (hM : M.IsLB) {A : Type} (V : A → X.Opens) (j : A → M.ι)
    (hj : ∀ a, V a ≤ M.U (j a)) (a b d : A) :
    rs X (le₁₂ V a b d) (tr M V j hj a b) * rs X (le₂₃ V a b d) (tr M V j hj b d) =
      rs X (le₁₃ V a b d) (tr M V j hj a d) := by
  have h := congrArg (fun u => rs X (le_inf (le_inf
    ((inf_le_left.trans inf_le_left).trans (hj a)) ((inf_le_left.trans inf_le_right).trans (hj b)))
    (inf_le_right.trans (hj d)) : V a ⊓ V b ⊓ V d ≤ M.U (j a) ⊓ M.U (j b) ⊓ M.U (j d)) u.val)
    (hM.cocycle (j a) (j b) (j d))
  have e : ∀ {U W : X.Opens} (h : W ≤ U) (u : Γ(X, U)ˣ), ((res h u : Γ(X, W)ˣ) : Γ(X, W)) = rs X h u :=
    fun _ _ => rfl
  simp only [Units.val_mul, map_mul, e, GlobalTheory.AbLaw.rs_rs] at h
  simp only [tr, GlobalTheory.AbLaw.rs_rs]
  exact h

def DepSt : Prop :=
  ∀ (k : Type) [Field k] (Y : Scheme.{0}) (s₀ : Y ⟶ Sp k), Y.IsSeparated → ∀ n r : ℕ,
    Module.Finite k (HO1 s₀) → Module.finrank k (HO1 s₀) ≤ n → n < r →
    ∀ (A : Type) (V : A → Y.Opens), ⨆ a, V a = ⊤ → (∀ a, IsAffineOpen (V a)) →
    ∀ α : Fin r → ∀ a b, Γ(Y, V a ⊓ V b),
      (∀ i a b d, rs Y (le₁₂ V a b d) (α i a b) + rs Y (le₂₃ V a b d) (α i b d) =
        rs Y (le₁₃ V a b d) (α i a d)) →
      ∃ (c : Fin r → k) (ψ : ∀ a, Γ(Y, V a)), c ≠ 0 ∧ ∀ a b,
        ∑ i, GlobalTheory.SmallExtLift.cst s₀ _ (c i) * α i a b =
          rs Y inf_le_left (ψ a) - rs Y inf_le_right (ψ b)

end GlobalTheory.CompanionTheory.FewEq
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAndFinrankLe
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.FirstCohomologyUpperBounds

theorem finite_and_finrank_le {k V : Type} [Field k] [AddCommGroup V] [Module k V] (g : ℕ)
    (h : ∀ x : Fin (g + 1) → V, ¬ LinearIndependent k x) :
    Module.Finite k V ∧ Module.finrank k V ≤ g := by
  classical
  let b := Module.Basis.ofVectorSpace k V
  have hemb : ∀ e : Fin (g + 1) ↪ Module.Basis.ofVectorSpaceIndex k V, False :=
    fun e => h _ (b.linearIndependent.comp e e.injective)
  haveI : Finite (Module.Basis.ofVectorSpaceIndex k V) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    exact hemb (Fin.valEmbedding.trans (Infinite.natEmbedding _))
  haveI hfin : Module.Finite k V := Module.Finite.of_basis b
  refine ⟨hfin, ?_⟩
  rw [Module.finrank_eq_nat_card_basis b]
  by_contra hlt
  rw [not_le] at hlt
  exact hemb ((Fin.castLEEmb (Nat.succ_le_of_lt hlt)).trans (Finite.equivFin _).symm.toEmbedding)

theorem h1Le : DescentSt → LowSt → SteinSt → VanSt → HopfSt → HopfLeSt → PositivityTheory.ObstructionTrivialLocus.H1StructureDimLe := by
  intro hD hL hS hV hH hHL k _ A _ g hA hsm
  haveI : AlgebraicGeometry.IsProper A.hom := ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme.proper (self := hA)
  haveI : CompactSpace A.left := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨P, _, _, ⟨S⟩⟩ := GlobalTheory.CompanionTheory.Hodge.WedgeField.exists_finite_sys A.hom
  have hfield : IsField k := Field.toIsField k
  have hq : MainStatements.Hodge.AllQIso (MainStatements.Hodge.resSys A.hom S) := hD k A.left A.hom inferInstance P S
  obtain ⟨hb1, -, hst⟩ := hL k _ _ _ _ (MainStatements.Hodge.resSys A.hom S) hq
  have hstein : MainStatements.Hodge.Stein (MainStatements.Hodge.OSys A.hom S) := hst.mp (hS k A g hA hsm)
  have hexact := hV k A g hA hsm hfield P S
  have hhopf : MainStatements.Hodge.Hopf (MainStatements.Hodge.OSys A.hom S) True := by
    have h := hH k A g hA hsm P S
    rwa [eq_true hfield] at h
  have hno := hHL k P (MainStatements.Hodge.OSys A.hom S) g hfield hstein hexact hhopf
  refine finite_and_finrank_le g (fun x hx => ?_)
  exact hno (⇑(MainStatements.Hodge.resSys A.hom S).pull1 ∘ x)
    (hx.map' (MainStatements.Hodge.resSys A.hom S).pull1 (LinearMap.ker_eq_bot.mpr hb1.1))

end GlobalTheory.CompanionTheory.Hodge.FirstCohomologyUpperBounds
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentToSaturation
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SatBridge
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LFun

namespace PositivityTheory.SphericalProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def SatBridge : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V), IsSmooth ρ → ρ.IsIrreducible →
    ∀ α : Fin n → ℂˣ, HasSatake ρ α ↔ HasSatGL w ρ (Finset.univ.val.map α)

end PositivityTheory.SphericalProduct

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatBridge
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LFun

namespace GlobalTheory.CompanionTheory.SatakeBridge

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem satBridge : PositivityTheory.SphericalProduct.SatBridge := by
  intro E _ _ w n V _ _ ρ hs hi α
  constructor
  · exact GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake E w n V ρ α
  · intro h
    obtain ⟨x, hx⟩ := h.exists_vec
    exact GlobalTheory.CompanionTheory.SatComp.hasSatake_of_isSatVecGL ⟨hs, hi⟩ α hx

end GlobalTheory.CompanionTheory.SatakeBridge

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentToSaturation
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ExpProd

theorem val_unifU (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    valuation k ((Zls.unifU k : kˣ) : k) = uniformizer k := by
  apply le_antisymm
  · rw [le_uniformizer_iff]
    exact GlobalTheory.CompanionTheory.UnifPow.valuation_unifU_lt_one k
  · obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
    have hy1 : valuation k y < 1 := hy ▸ uniformizer_lt_one
    have hyO : y ∈ 𝒪[k] := hy1.le
    have hm : (⟨y, hyO⟩ : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu
      exact hy1.ne (((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one).1 hu)
    rw [(Zls.irreducible_unif (k := k)).maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    rw [← hy]
    exact (Valuation.Integers.le_iff_dvd (Valuation.integer.integers (valuation k))).2 hm

theorem atUnif_unrChar (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (ξ : Fin n → ℂˣ) : PositivityTheory.SphericalProduct.atUnif k (fun i => unrChar k (ξ i)) = ξ :=
  funext fun i => unrChar_uniformizer k (ξ i) (val_unifU k)

theorem expToSat : PositivityTheory.Rg.BcB.F.Tail.PExp.ExpToSat := by
  intro E _ _ w c n N h σ P ξ hsub hmono ⟨y, hy0, hy⟩
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hd : ∑ _a : Fin n, 1 = n := by simp
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.CompanionTheory.StandardBlocks.stdBridge (w.adicCompletion E) n hd P.V P.ρ _ y hy0 hy
  have hadm : IsAdmissible P.ρ :=
    (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness (w.adicCompletion E)).1 _ P.V P.ρ P.smooth P.irred
  have hanti : PositivityTheory.SphericalProduct.AbsAnti (PositivityTheory.SphericalProduct.atUnif (w.adicCompletion E)
      (fun i => unrChar (w.adicCompletion E) (ξ i))) := by
    rw [atUnif_unrChar]
    exact fun i j hij => hmono i j hij
  have hsat := GlobalTheory.CompanionTheory.LocGL.expSat (w.adicCompletion E) n hd P.V P.ρ P.smooth hadm P.irred
    (fun i => unrChar (w.adicCompletion E) (ξ i)) (fun i => isUnram_unrChar _ _) hanti ⟨v, hv0, hv⟩
  rw [atUnif_unrChar] at hsat
  have hG := (GlobalTheory.CompanionTheory.SatakeBridge.satBridge E w n P.V P.ρ P.smooth P.irred ξ).1 hsat
  obtain ⟨x, hx⟩ := hG.exists_vec
  obtain ⟨S, f, hf⟩ := hsub
  have hsm : IsSmooth (locProd h w σ) := GlobalTheory.SmGL.isSmooth_parInd _ _
  have hSs : IsSmooth S.toRepresentation := GlobalTheory.CompanionTheory.JacExp.isSmooth_sub hsm S
  have hc := GlobalTheory.SatInd.isCompact_KGL (w := w) (n := n)
  obtain ⟨s, rfl⟩ := hf x
  obtain ⟨u, hu, hfu⟩ := GlobalTheory.LocGL.exists_mem_fixed_map_eq hSs hc f hx.2.1
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hx.1 (by rw [← hfu, map_zero])
  have hfix : u.1 ∈ fixed (locProd h w σ) (GlobalTheory.LFun.KGL w (n := n)) :=
    GlobalTheory.LGrp.mem_fixed.2 fun g hg => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hu g hg)
  have hne : u.1 ≠ 0 := fun e => hu0 (Subtype.ext e)
  obtain ⟨B, hB, hBv⟩ := GlobalTheory.SatInd.exists_sat_multiProd h (π := fun i => (σ i).ρ)
    (fun i => (σ i).smooth) (fun i => (σ i).irred) hfix hne
  have h1 : GlobalTheory.LFun.IsSatVecGL w S.toRepresentation u (∑ a, B a) :=
    GlobalTheory.LFun.IsSatVecGL.of_map S.toSubmodule.subtype (fun g y => rfl) Subtype.val_injective hBv
  have h2 := h1.map (ρ' := P.ρ) f.toLinearMap (fun g y => f.isIntertwining _ _ g y) (by
    change f u ≠ 0
    rw [hfu]
    exact hx.1)
  change GlobalTheory.LFun.IsSatVecGL w P.ρ (f u) _ at h2
  rw [hfu] at h2
  exact ⟨fun i => (hB i).1, B, hB, h2.unique hx⟩

end GlobalTheory.CompanionTheory.ExpProd

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentToSaturationStatement
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponent_to_saturation : PositivityTheory.Rg.BcB.F.Tail.PExp.ExpToSat := by
  first | exact @GlobalTheory.CompanionTheory.ExpProd.expToSat | exact GlobalTheory.CompanionTheory.ExpProd.expToSat | (intros; apply GlobalTheory.CompanionTheory.ExpProd.expToSat <;> assumption)
end PositivityTheory.Rg.BcB.F.Tail.PExp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeFieldOfField
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory.CompanionTheory.Hodge.WedgeField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.WedgeFieldGeo

theorem wedgeField_of_field :
    DescentSt → LowSt → SteinSt → H1StructureFieldDim → VanSt → HopfSt → HopfFieldSt → WedgeFieldSt := by
  intro hD hL hS hH1 hV hHopf hHF R _ A _ g hA hg hR
  haveI : IsAbelianScheme A := hA
  haveI : IsProper A.hom := IsAbelianScheme.proper
  haveI : CompactSpace (Sp R) := by
    unfold Sp
    infer_instance
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨P, iP, hfin, ⟨S⟩⟩ := exists_finite_sys A.hom
  letI := iP
  haveI := hfin
  have hQ : AllQIso (resSys A.hom S) := hD R A.left A.hom inferInstance P S
  obtain ⟨h1, h2, hSt⟩ := hL R _ _ _ _ (resSys A.hom S) hQ
  have hStein : Stein (OSys A.hom S) := hSt.mp (hS R A g hA hg)
  have hvb : VB R (H1 (OSys A.hom S)) g := vb_of_bijective (resSys A.hom S) h1 (hH1 R A g hA hg hR)
  have hvan : ∀ n : ℕ, g ≤ n → Function.Exact (dn (OSys A.hom S) n) (dn (OSys A.hom S) (n + 1)) :=
    fun n hn => hV R A g hA hg hR P S n hn
  have hh : Hopf (OSys A.hom S) (IsField R) := hHopf R A g hA hg P S
  rw [eq_true hR] at hh
  exact wedge_of_bijective (resSys A.hom S) h1 h2 (hHF R P (OSys A.hom S) g hR hStein hvb hvan hh)

end GlobalTheory.CompanionTheory.Hodge.WedgeFieldGeo
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfStOfSpreads
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfModels

theorem flat_sec {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [Flat s] (U : X.affineOpens) :
    Module.Flat R (Sec s U.1) := by
  have hfl : RingHom.Flat (s.appLE ⊤ U.1 le_top).hom := s.flat_appLE (isAffineOpen_top _) U.2 le_top
  have hi : RingHom.Flat (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)
  have h : RingHom.Flat (secMap s U.1).hom := RingHom.Flat.comp hi hfl
  exact (RingHom.flat_algebraMap_iff (R := R) (S := Sec s U.1)).1 h

theorem exists_sys {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsSeparated s] [QuasiCompact s] :
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P), Nonempty (Sys X P) := by
  obtain ⟨J, hf, hl, U, -, hm, hc⟩ := GlobalTheory.exists_finite_affine_cover_infClosed R X s inferInstance inferInstance
  exact ⟨J, hl, hf, ⟨⟨U, hm, hc⟩⟩⟩

theorem perf_noeth (hF : FinCohSt) (hN : PerfNoethSt) (R : Type) [CommRing R] [IsNoetherianRing R]
    (X : Scheme.{0}) (s : X ⟶ Sp R) [Smooth s] [IsProper s] :
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P) (S : Sys X P), Perf (OSys s S) := by
  obtain ⟨P, _, _, ⟨S⟩⟩ := exists_sys s
  obtain ⟨h₀, h₁⟩ := hF R X s inferInstance P S
  exact ⟨P, inferInstance, inferInstance, S,
    hN R P (OSys s S) inferInstance (fun T ↦ flat_sec s (S.u T.unop)) h₀ h₁⟩

theorem perf_base (hB : SysBCSt) (hP : PerfBaseSt) {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R)
    {Y X : Scheme.{0}} (f : Y ⟶ Sp R₀) (s : X ⟶ Sp R) (π : X ⟶ Y) [IsSeparated f]
    (h : IsPullback π s f (spMap φ))
    (hY : ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P) (S : Sys Y P), Perf (OSys f S)) :
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P) (S : Sys X P), Perf (OSys s S) := by
  obtain ⟨P, _, _, S, hS⟩ := hY
  letI := φ.toAlgebra
  obtain ⟨S', m, -⟩ := hB R₀ R Y X f s π h inferInstance P S
  exact ⟨P, inferInstance, inferInstance, S', hP R₀ P (OSys f S) hS R (OSys s S') m⟩

theorem perfSt_of_spreads : GlobalTheory.SpreadingModels.SchemeModels → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f) →
    GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) → DescentSt → LowSt → SysBCSt → FinCohSt → PerfNoethSt →
    PerfBaseSt → PerfSt := by
  intro hS hSm hPr _ _ hBC hF hN hP R _ X s hsm hpr
  obtain ⟨R₀, _, φ, Y₀, f₀, π, hm⟩ := hS R X s inferInstance inferInstance inferInstance
  obtain ⟨R₁, _, ψ₁, φ₁, e₁, ft₁, sm₁⟩ := hSm R R₀ φ X Y₀ s f₀ π hm hsm
  have m₁ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₁ ft₁ hm
  obtain ⟨R₂, _, ψ₂, φ₂, e₂, ft₂, pr₂⟩ := hPr R R₁ φ₁ X _ s _ _ m₁ hpr
  have m₂ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₂ ft₂ m₁
  have sm₁' : Smooth (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁))) := sm₁
  have pr₂' : IsProper (Limits.pullback.snd (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) := pr₂
  haveI : IsNoetherianRing R₂ := Algebra.FiniteType.isNoetherianRing ℤ R₂
  exact perf_base hBC hP φ₂ _ s _ m₂.2.2.2.2 (perf_noeth hF hN R₂ _ _)

end GlobalTheory.CompanionTheory.PerfModels
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeFirstCohomology
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.FlatBase

section Alg

variable (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']

def Bas {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] (f : M → M') : Prop :=
  ∃ e : R' ⊗[R] M ≃ₗ[R'] M', ∀ b, e (1 ⊗ₜ b) = f b

variable {R R'}

theorem Bas.pi {J : Type} [Finite J] {M M' : J → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M' i)] [∀ i, Module R' (M' i)] (f : ∀ i, M i → M' i) (h : ∀ i, Bas R R' (f i)) :
    Bas R R' (fun (x : ∀ i, M i) i ↦ f i (x i)) := by
  classical
  haveI := Fintype.ofFinite J
  choose e he using h
  refine ⟨(TensorProduct.piRight R R' R' M).trans (LinearEquiv.piCongrRight e), fun b ↦ ?_⟩
  funext i
  simp [he]

theorem flat_coh [Module.Flat R R'] {A₀ A₁ A₂ B₀ B₁ B₂ : Type} [AddCommGroup A₀] [AddCommGroup A₁]
    [AddCommGroup A₂] [Module R A₀] [Module R A₁] [Module R A₂] [AddCommGroup B₀] [AddCommGroup B₁]
    [AddCommGroup B₂] [Module R' B₀] [Module R' B₁] [Module R' B₂]
    (Z : Submodule R A₁) (Z' : Submodule R' B₁) (d₀ : A₀ →ₗ[R] Z) (d₁ : A₁ →ₗ[R] A₂)
    (d₀' : B₀ →ₗ[R'] Z') (d₁' : B₁ →ₗ[R'] B₂)
    (hZ : ∀ x, x ∈ Z ↔ d₁ x = 0) (hZ' : ∀ x, x ∈ Z' ↔ d₁' x = 0)
    (a₀ : A₀ → B₀) (a₁ : A₁ → B₁) (a₂ : A₂ → B₂)
    (h₀ : Bas R R' a₀) (h₁ : Bas R R' a₁) (h₂ : Bas R R' a₂)
    (c₀ : ∀ x, (d₀' (a₀ x)).1 = a₁ (d₀ x).1) (c₁ : ∀ x, d₁' (a₁ x) = a₂ (d₁ x))
    (p : (Z ⧸ LinearMap.range d₀) →ₛₗ[algebraMap R R'] (Z' ⧸ LinearMap.range d₀'))
    (hp : ∀ (z : Z) (z' : Z'), z'.1 = a₁ z.1 →
      p (Submodule.Quotient.mk z) = Submodule.Quotient.mk z') :
    ∃ e : R' ⊗[R] (Z ⧸ LinearMap.range d₀) ≃ₗ[R'] (Z' ⧸ LinearMap.range d₀'),
      ∀ c, e (1 ⊗ₜ c) = p c := by
  obtain ⟨e₀, he₀⟩ := h₀
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  letI : Module R (Z' ⧸ LinearMap.range d₀') := Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' (Z' ⧸ LinearMap.range d₀') :=
    ⟨fun r s x ↦ by
      change (r • s) • x = algebraMap R R' r • s • x
      rw [Algebra.smul_def, mul_smul]⟩
  let pl : (Z ⧸ LinearMap.range d₀) →ₗ[R] (Z' ⧸ LinearMap.range d₀') :=
    { toFun := p, map_add' := p.map_add, map_smul' := fun r x ↦ p.map_smulₛₗ r x }
  let L : R' ⊗[R] (Z ⧸ LinearMap.range d₀) →ₗ[R'] (Z' ⧸ LinearMap.range d₀') := pl.liftBaseChange R'
  have hL : ∀ c, L (1 ⊗ₜ c) = p c := fun c ↦ by
    simp only [L, LinearMap.liftBaseChange_tmul, one_smul]; rfl
  have ta : ∀ (r : R') (x : A₁), e₁ (r ⊗ₜ x) = r • a₁ x := fun r x ↦ by
    rw [← he₁, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have ta₀ : ∀ (r : R') (x : A₀), e₀ (r ⊗ₜ x) = r • a₀ x := fun r x ↦ by
    rw [← he₀, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have ta₂ : ∀ (r : R') (x : A₂), e₂ (r ⊗ₜ x) = r • a₂ x := fun r x ↦ by
    rw [← he₂, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have a₂0 : a₂ 0 = 0 := by rw [← he₂, TensorProduct.tmul_zero, map_zero]

  have comm₁ : ∀ t, e₂ (d₁.baseChange R' t) = d₁' (e₁ t) := fun t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => simp [ta, ta₂, c₁]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have comm₀ : ∀ t, (d₀' (e₀ t)).1 = e₁ (Z.subtype.baseChange R' (d₀.baseChange R' t)) := fun t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => simp [ta, ta₀, c₀]
    | add x y hx hy => simp only [map_add (f := _), Submodule.coe_add, hx, hy]
  have mem : ∀ t, e₁ (Z.subtype.baseChange R' t) ∈ Z' := fun t ↦ by
    rw [hZ', ← comm₁]
    have : ∀ t, d₁.baseChange R' (Z.subtype.baseChange R' t) = 0 := fun t ↦ by
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul r x => simp [(hZ _).1 x.2]
      | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
    rw [this, map_zero]
  let g : R' ⊗[R] Z →ₗ[R'] Z' :=
    LinearMap.codRestrict Z' (e₁.toLinearMap ∘ₗ Z.subtype.baseChange R') mem
  have hg : ∀ t, (g t).1 = e₁ (Z.subtype.baseChange R' t) := fun _ ↦ rfl
  have key : ∀ t, L ((LinearMap.range d₀).mkQ.baseChange R' t) = Submodule.Quotient.mk (g t) := fun t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      have hx : a₁ x.1 ∈ Z' := by
        rw [hZ', c₁, (hZ _).1 x.2, a₂0]
      rw [LinearMap.baseChange_tmul]
      simp only [L, LinearMap.liftBaseChange_tmul]
      have e1 : pl ((LinearMap.range d₀).mkQ x) = Submodule.Quotient.mk ⟨a₁ x.1, hx⟩ := hp x _ rfl
      rw [e1, ← Submodule.Quotient.mk_smul]
      congr 1
      apply Subtype.ext
      simp [hg, ta]
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]; rfl
  have hLs : Function.Surjective L := fun c' ↦ by
    obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ c'
    have hex : Function.Exact Z.subtype d₁ := fun x ↦ by
      rw [← hZ]; simp
    have hex' := Module.Flat.lTensor_exact R' hex
    have h0 : d₁.lTensor R' (e₁.symm z'.1) = 0 := by
      rw [← LinearMap.baseChange_eq_ltensor]
      apply e₂.injective
      rw [comm₁, e₁.apply_symm_apply, map_zero]
      exact (hZ' _).1 z'.2
    obtain ⟨t, ht⟩ := (hex' _).1 h0
    rw [← LinearMap.baseChange_eq_ltensor] at ht
    refine ⟨(LinearMap.range d₀).mkQ.baseChange R' t, ?_⟩
    rw [key]
    congr 1
    apply Subtype.ext
    rw [hg, ht, e₁.apply_symm_apply]
  have hLi : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨t₀, rfl⟩ : ∃ t₀, (LinearMap.range d₀).mkQ.baseChange R' t₀ = t := by
      have := LinearMap.lTensor_surjective R' (g := (LinearMap.range d₀).mkQ)
        (Submodule.mkQ_surjective _)
      rw [← LinearMap.baseChange_eq_ltensor] at this
      exact this t
    rw [key, Submodule.Quotient.mk_eq_zero] at ht
    obtain ⟨y', hy'⟩ := ht
    have e1 : Z.subtype.baseChange R' (d₀.baseChange R' (e₀.symm y')) = Z.subtype.baseChange R' t₀ := by
      apply e₁.injective
      rw [← comm₀, e₀.apply_symm_apply, hy', hg]
    have inj : Function.Injective (Z.subtype.baseChange R') := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ Z.injective_subtype
    rw [← inj e1]
    have : ∀ y, (LinearMap.range d₀).mkQ.baseChange R' (d₀.baseChange R' y) = 0 := fun y ↦ by
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r x =>
        have : (LinearMap.range d₀).mkQ (d₀ x) = 0 :=
          (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
        simp [this]
      | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
    exact this _
  exact ⟨LinearEquiv.ofBijective L ⟨hLi, hLs⟩, hL⟩

end Alg

section Sys

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {C : Type} [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} R'}

theorem flat_base_change_first_cohomology [Module.Flat R R'] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (m : BC F F') :
    ∃ e : R' ⊗[R] H1 F ≃ₗ[R'] H1 F', ∀ c, e (1 ⊗ₜ c) = m.coef.pull1 c := by
  have b : ∀ T, Bas R R' (m.α T) := m.bij
  have b₀ : Bas R R' (fun (x : C0 F) T ↦ m.α T (x T)) := Bas.pi _ b
  have b₁ : Bas R R' (fun (x : C1 F) T T' φ ↦ m.α T' (x T T' φ)) :=
    Bas.pi (M := fun T ↦ ∀ (T' : C) (_ : T ⟶ T'), F.obj T')
      (M' := fun T ↦ ∀ (T' : C) (_ : T ⟶ T'), F'.obj T') _ fun T ↦
    Bas.pi (M := fun T' ↦ ∀ _ : T ⟶ T', F.obj T') (M' := fun T' ↦ ∀ _ : T ⟶ T', F'.obj T') _ fun T' ↦
    Bas.pi (M := fun _ : T ⟶ T' ↦ F.obj T') (M' := fun _ : T ⟶ T' ↦ F'.obj T') _ fun _ ↦ b T'
  have b₂ : Bas R R' (fun (x : C2 F) T T' T'' φ ψ ↦ m.α T'' (x T T' T'' φ ψ)) :=
    Bas.pi (M := fun T ↦ ∀ (T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'')
      (M' := fun T ↦ ∀ (T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'') _ fun T ↦
    Bas.pi (M := fun T' ↦ ∀ (T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'')
      (M' := fun T' ↦ ∀ (T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'') _ fun T' ↦
    Bas.pi (M := fun T'' ↦ ∀ (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'')
      (M' := fun T'' ↦ ∀ (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'') _ fun T'' ↦
    Bas.pi (M := fun _ : T ⟶ T' ↦ ∀ _ : T' ⟶ T'', F.obj T'')
      (M' := fun _ : T ⟶ T' ↦ ∀ _ : T' ⟶ T'', F'.obj T'') _ fun _ ↦
    Bas.pi (M := fun _ : T' ⟶ T'' ↦ F.obj T'') (M' := fun _ : T' ⟶ T'' ↦ F'.obj T'') _ fun _ ↦ b T''
  refine flat_coh (Z1 F) (Z1 F') ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)) (d1 F)
    ((d0 F').codRestrict (Z1 F') (commAlgFunctorCoboundaryZero_mem_cocyclesOne F')) (d1 F')
    (fun x ↦ by rw [commAlgFunctorCocyclesOne_eq_ker]; rfl) (fun x ↦ by rw [commAlgFunctorCocyclesOne_eq_ker]; rfl) _ _ _ b₀ b₁ b₂ ?_ ?_
    m.coef.pull1 ?_
  · intro x
    funext T T' φ
    simp only [LinearMap.codRestrict_apply, amitsur_d0_apply, map_sub, m.naturality]
  · intro x
    funext T T' T'' φ ψ
    simp only [d1_apply, map_sub, map_add (f := _), m.naturality]
  · intro z z' h
    have : m.coef.pullbackOneCocycle z = z' := Subtype.ext h.symm
    rw [← this]
    rfl

end Sys

theorem flatBC : DescentSt → LowSt → SysBCSt → FlatBCSt := by
  intro hD hL hS R R' _ _ _ _ X X' s s' φ h hsep hqc
  haveI := hsep
  haveI := hqc
  haveI : CompactSpace X := by
    rw [← isCompact_univ_iff]
    simpa using QuasiCompact.isCompact_preimage (f := s) Set.univ isOpen_univ isCompact_univ
  obtain ⟨P, iP, fP, ⟨S⟩⟩ := GlobalTheory.CompanionTheory.Hodge.WedgeField.exists_finite_sys s
  obtain ⟨S', m, hm⟩ := hS R R' X X' s s' φ h hsep P S
  have hsep' : IsSeparated s' := MorphismProperty.of_isPullback (P := @IsSeparated) h hsep
  obtain ⟨b, -, -⟩ := hL R _ _ _ _ _ (hD R X s hsep P S)
  obtain ⟨b', -, -⟩ := hL R' _ _ _ _ _ (hD R' X' s' hsep' P S')
  let E : HO1 s ≃ₗ[R] H1 (OSys s S) := LinearEquiv.ofBijective (resSys s S).pull1 b
  let E' : HO1 s' ≃ₗ[R'] H1 (OSys s' S') := LinearEquiv.ofBijective (resSys s' S').pull1 b'
  haveI : Finite Pᵒᵖ := Finite.of_equiv P Opposite.equivToOpposite
  haveI : ∀ T T' : Pᵒᵖ, Finite (T ⟶ T') := fun _ _ ↦ Finite.of_subsingleton
  obtain ⟨e, he⟩ := flat_base_change_first_cohomology m
  refine ⟨(TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R') E).trans
    (e.trans E'.symm), fun c ↦ hm c _ ?_⟩
  have : E' ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R') E).trans
      (e.trans E'.symm) (1 ⊗ₜ c)) = e (1 ⊗ₜ E c) := by
    simp
  exact ((he _).symm.trans this.symm)

end GlobalTheory.CompanionTheory.Hodge.FlatBase
end
end
