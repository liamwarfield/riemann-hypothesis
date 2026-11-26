module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.PolFibreIsogAny
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroLocusRegularFunctionNull

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfFibresFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfFibresFinite
namespace GlobalTheory.CompanionTheory.FlatFib

theorem flatOfFibresFinite : PositivityTheory.Tls2.Zar3.Ch1.FlatOfFibresFinite := by
  intro R _ X Y f h1 h0 h2 h3 H
  exact GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres _ X Y f h1 h0 h2 h3 H

end GlobalTheory.CompanionTheory.FlatFib
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfFibresFiniteStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_fibres_finite : PositivityTheory.Tls2.Zar3.Ch1.FlatOfFibresFinite := by
  first | exact @GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite | exact GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite | (intros; apply GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpiOfFiniteFlat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpiOfFiniteFlat
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.Dblock

theorem epiOfFF : PositivityTheory.Tls2.Zar3.Ch1.EpiOfFF := by
  intro R _ A B A' l hf hs hq g₁ g₂ h
  have : EffectiveEpi l.left := inferInstance
  have : Epi l.left := inferInstance
  apply Over.OverMorphism.ext
  rw [← cancel_epi l.left]
  simpa using congrArg (fun k => k.left) h

end GlobalTheory.CompanionTheory.Dblock
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpiOfFiniteFlatStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epi_of_finite_flat : PositivityTheory.Tls2.Zar3.Ch1.EpiOfFF := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.epiOfFF | exact GlobalTheory.CompanionTheory.Dblock.epiOfFF | (intros; apply GlobalTheory.CompanionTheory.Dblock.epiOfFF <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorThroughFiniteFlat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorThroughFiniteFlat
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp)

namespace GlobalTheory.CompanionTheory.FlatFactor

theorem ext_of_affine_points {R : Type} [CommRing R] {W X : Over (Sp R)} (u v : W ⟶ X)
    (h : ∀ (S : Type) [CommRing S] [Algebra R S] (t : sp (R₀ := R) S ⟶ W), t ≫ u = t ≫ v) : u = v := by
  have key : ∀ (B : CommRingCat.{0}) (j₀ : Spec B ⟶ W.left), j₀ ≫ u.left = j₀ ≫ v.left := by
    intro B j₀
    letI : Algebra R B := (Spec.preimage (j₀ ≫ W.hom)).hom.toAlgebra
    let j : sp (R₀ := R) B ⟶ W := Over.homMk j₀ (Spec.map_preimage (j₀ ≫ W.hom)).symm
    exact congrArg CommaMorphism.left (h B j)
  apply Over.OverMorphism.ext
  exact Scheme.Cover.hom_ext W.left.affineCover _ _ fun i => key _ _

theorem comp_eq_of_comp_eq {R : Type} [CommRing R] {A B A' : Over (Sp R)} [GrpObj A] [GrpObj B] [GrpObj A']
    (l : A ⟶ B) (f : A ⟶ A') [IsMonHom l] [IsMonHom f]
    (hk : ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A), z ≫ l = 1 → z ≫ f = 1)
    {W : Over (Sp R)} (a b : W ⟶ A) (h : a ≫ l = b ≫ l) : a ≫ f = b ≫ f := by
  refine ext_of_affine_points _ _ fun S _ _ t => ?_
  have h1 : ((t ≫ a) / (t ≫ b)) ≫ l = 1 := by
    rw [GrpObj.div_comp, Category.assoc, Category.assoc, h, div_self']
  have h2 := hk S _ h1
  rw [GrpObj.div_comp, div_eq_one] at h2
  simpa using h2

theorem factorThroughFF : PositivityTheory.Tls2.Zar3.Ch1.FactorThroughFF := by
  intro R _ A B A' _ _ _ l f hl hf hfl hsl hql hk
  have hc : ∀ {Z : Scheme.{0}} (g g' : Z ⟶ A.left), g ≫ l.left = g' ≫ l.left →
      g ≫ f.left = g' ≫ f.left := by
    intro Z g g' h
    have hw : g' ≫ A.hom = g ≫ A.hom := by
      rw [← Over.w l, ← Category.assoc, ← h, Category.assoc]
    have := comp_eq_of_comp_eq l f hk (W := Over.mk (g ≫ A.hom))
      (Over.homMk g rfl) (Over.homMk g' hw) (Over.OverMorphism.ext h)
    exact congrArg CommaMorphism.left this
  have hfac := EffectiveEpi.fac l.left f.left hc
  let g : B ⟶ A' := Over.homMk (EffectiveEpi.desc l.left f.left hc) (by
    rw [← cancel_epi l.left, ← Category.assoc, hfac, Over.w, Over.w])
  have hg : l ≫ g = f := Over.OverMorphism.ext hfac
  refine ⟨g, ⟨?_, ?_⟩, hg⟩
  · rw [← IsMonHom.one_hom l, Category.assoc, hg, IsMonHom.one_hom]
  · have := GlobalTheory.FlatQuotient.epi_tensorHom l l
    rw [← cancel_epi (l ⊗ₘ l), ← IsMonHom.mul_hom_assoc, hg, tensorHom_comp_tensorHom_assoc, hg,
      IsMonHom.mul_hom]

end GlobalTheory.CompanionTheory.FlatFactor
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorThroughFiniteFlatStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factor_through_finite_flat : PositivityTheory.Tls2.Zar3.Ch1.FactorThroughFF := by
  first | exact @GlobalTheory.CompanionTheory.FlatFactor.factorThroughFF | exact GlobalTheory.CompanionTheory.FlatFactor.factorThroughFF | (intros; apply GlobalTheory.CompanionTheory.FlatFactor.factorThroughFF <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCoreDefs
set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

variable {K H : Type} [Field K] [CommRing H] [Algebra K H]

def pw (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) : ℕ → (H →ₐ[K] H)
  | 0 => (Algebra.ofId K H).comp ε
  | n + 1 => (Algebra.TensorProduct.lmul' K).comp ((Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H)).comp Δ)

def CounitL (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) : Prop :=
  (Algebra.TensorProduct.lmul' K).comp
    ((Algebra.TensorProduct.map ((Algebra.ofId K H).comp ε) (AlgHom.id K H)).comp Δ) = AlgHom.id K H

def CounitR (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) : Prop :=
  (Algebra.TensorProduct.lmul' K).comp
    ((Algebra.TensorProduct.map (AlgHom.id K H) ((Algebra.ofId K H).comp ε)).comp Δ) = AlgHom.id K H

def KilledCore : Prop :=
  ∀ (K H : Type) [Field K] [IsAlgClosed K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K), CounitL Δ ε → CounitR Δ ε →
    (∀ a b : ℕ, pw Δ ε (a * b) = (pw Δ ε a).comp (pw Δ ε b)) →
    (∃ m : ℕ, 0 < m ∧ ∀ x : H →ₐ[K] K, x.comp (pw Δ ε m) = ε) →
    ∃ N : ℕ, 0 < N ∧ pw Δ ε N = pw Δ ε 0

end PositivityTheory.PrwZar.Qi
end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.CompLmulMapId
set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

variable {K H : Type} [Field K] [CommRing H] [Algebra K H]

theorem comp_lmul_map_id (ε : H →ₐ[K] K) (f : H →ₐ[K] H) (t : H ⊗[K] H) :
    f (Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (AlgHom.id K H) ((Algebra.ofId K H).comp ε) t)) =
      Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map f ((Algebra.ofId K H).comp ε) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, AlgHom.id_apply,
      AlgHom.comp_apply, Algebra.ofId_apply, map_mul, AlgHom.commutes]
  | add s t hs ht => simp only [map_add (f := _), hs, ht]

theorem counit_pw (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) (hL : CounitL Δ ε) (hR : CounitR Δ ε) (n : ℕ) :
    ε.comp (pw Δ ε n) = ε := by
  induction n with
  | zero => ext x; simp [pw]
  | succ n ih =>
    ext x
    have key : ∀ t : H ⊗[K] H,
        ε (Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H) t)) =
          ε (Algebra.TensorProduct.lmul' K
            (Algebra.TensorProduct.map ((Algebra.ofId K H).comp ε) (AlgHom.id K H) t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_mul,
          AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.commutes, AlgHom.id_apply]
        rw [← AlgHom.comp_apply ε (pw Δ ε n), ih]
        simp
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
    have hx := DFunLike.congr_fun hL x
    simp only [CounitL, AlgHom.comp_apply, AlgHom.id_apply] at hx
    show ε (Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H) (Δ x))) = ε x
    rw [key, hx]

theorem pw_sub_mem (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) (hL : CounitL Δ ε) (hR : CounitR Δ ε) (n : ℕ)
    {x : H} (hx : x ∈ RingHom.ker ε) : pw Δ ε n x - (n : H) * x ∈ RingHom.ker ε ^ 2 := by
  have hx0 : ε x = 0 := hx
  set e : H →ₐ[K] H := (Algebra.ofId K H).comp ε with he
  have gen : ∀ f : H →ₐ[K] H, ε.comp f = ε → ∀ t : H ⊗[K] H,
      Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map f (AlgHom.id K H) t) -
        Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map e (AlgHom.id K H) t) -
        Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map f e t) +
        Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map e e t) ∈ RingHom.ker ε ^ 2 := by
    intro f hf t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, AlgHom.id_apply, he,
        AlgHom.comp_apply, Algebra.ofId_apply]
      have e1 : f a * b - algebraMap K H (ε a) * b - f a * algebraMap K H (ε b) +
          algebraMap K H (ε a) * algebraMap K H (ε b) =
          (f a - algebraMap K H (ε a)) * (b - algebraMap K H (ε b)) := by ring
      rw [e1, pow_two]
      refine Ideal.mul_mem_mul ?_ ?_
      · rw [RingHom.mem_ker, map_sub, ← AlgHom.comp_apply, hf, AlgHom.commutes]; simp
      · rw [RingHom.mem_ker, map_sub, AlgHom.commutes]; simp
    | add s t hs ht =>
      simp only [map_add (f := _)]
      convert Ideal.add_mem _ hs ht using 1
      ring
  induction n with
  | zero => simp [pw, hx0]
  | succ n ih =>
    have h1 := gen (pw Δ ε n) (counit_pw Δ ε hL hR n) (Δ x)
    have hLx := DFunLike.congr_fun hL x
    have hRx := DFunLike.congr_fun hR x
    simp only [CounitL, CounitR, AlgHom.comp_apply, AlgHom.id_apply] at hLx hRx
    rw [← comp_lmul_map_id ε (pw Δ ε n), ← comp_lmul_map_id ε e, hRx, hLx] at h1
    have hex : e x = 0 := by simp [he, hx0]
    rw [hex, add_zero] at h1
    have h2 := Ideal.add_mem _ h1 ih
    have hp : pw Δ ε (n + 1) x =
        Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H) (Δ x)) := rfl
    rw [hp]
    convert h2 using 1
    push_cast
    ring

end PositivityTheory.PrwZar.Qi
end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.KilledAnyOf
section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiPtsA
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open GlobalTheory.CompanionTheory.Ar.GR

namespace PositivityTheory.PrwZar.QiP

variable {R : Type} [CommRing R] {F : Type} [CommRing F] [Algebra R F]

theorem spMap_comp {S T : Type} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
    (φ : F →ₐ[R] S) (ψ : S →ₐ[R] T) : spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  simp [spMap, ← Spec.map_comp]
  rfl

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {h : sp (R₀ := R) F ⟶ G}

def mulPt (hs : IsFinFlatSub G F h) {S : Type} [CommRing S] [Algebra R S] (φ φ' : F →ₐ[R] S) : F →ₐ[R] S :=
  (hs.mul S φ φ').choose

theorem mulPt_spec (hs : IsFinFlatSub G F h) {S : Type} [CommRing S] [Algebra R S] (φ φ' : F →ₐ[R] S) :
    spMap (mulPt hs φ φ') ≫ h = (spMap φ ≫ h) * (spMap φ' ≫ h) :=
  (hs.mul S φ φ').choose_spec

def onePt (hs : IsFinFlatSub G F h) (S : Type) [CommRing S] [Algebra R S] : F →ₐ[R] S :=
  (hs.one S).choose

theorem onePt_spec (hs : IsFinFlatSub G F h) (S : Type) [CommRing S] [Algebra R S] :
    spMap (onePt hs S) ≫ h = 1 :=
  (hs.one S).choose_spec

theorem pt_ext (hs : IsFinFlatSub G F h) {S : Type} [CommRing S] [Algebra R S] {φ φ' : F →ₐ[R] S}
    (e : spMap φ ≫ h = spMap φ' ≫ h) : φ = φ' :=
  hs.mono S φ φ' e

def powPt (hs : IsFinFlatSub G F h) {S : Type} [CommRing S] [Algebra R S] (φ : F →ₐ[R] S) : ℕ → (F →ₐ[R] S)
  | 0 => onePt hs S
  | n + 1 => mulPt hs (powPt hs φ n) φ

theorem powPt_spec (hs : IsFinFlatSub G F h) {S : Type} [CommRing S] [Algebra R S] (φ : F →ₐ[R] S) (n : ℕ) :
    spMap (powPt hs φ n) ≫ h = (spMap φ ≫ h) ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact onePt_spec hs S
  | succ n ih => rw [pow_succ, ← ih]; exact mulPt_spec hs _ _

variable {S T : Type} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

theorem comp_mulPt (hs : IsFinFlatSub G F h) (ψ : S →ₐ[R] T) (φ φ' : F →ₐ[R] S) :
    ψ.comp (mulPt hs φ φ') = mulPt hs (ψ.comp φ) (ψ.comp φ') := by
  apply pt_ext hs
  rw [mulPt_spec, ← spMap_comp, ← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc, Category.assoc,
    mulPt_spec, MonObj.comp_mul]

theorem comp_onePt (hs : IsFinFlatSub G F h) (ψ : S →ₐ[R] T) : ψ.comp (onePt hs S) = onePt hs T := by
  apply pt_ext hs
  rw [onePt_spec, ← spMap_comp, Category.assoc, onePt_spec, MonObj.comp_one]

theorem comp_powPt (hs : IsFinFlatSub G F h) (ψ : S →ₐ[R] T) (φ : F →ₐ[R] S) (n : ℕ) :
    ψ.comp (powPt hs φ n) = powPt hs (ψ.comp φ) n := by
  apply pt_ext hs
  rw [powPt_spec, ← spMap_comp, Category.assoc, powPt_spec, MonObj.comp_pow, ← Category.assoc, spMap_comp]

theorem powPt_mul (hs : IsFinFlatSub G F h) (φ : F →ₐ[R] S) (a b : ℕ) :
    powPt hs φ (a * b) = powPt hs (powPt hs φ a) b := by
  apply pt_ext hs
  rw [powPt_spec, powPt_spec, powPt_spec, pow_mul]

theorem mulPt_onePt (hs : IsFinFlatSub G F h) (φ : F →ₐ[R] S) : mulPt hs (onePt hs S) φ = φ := by
  apply pt_ext hs
  rw [mulPt_spec, onePt_spec, _root_.one_mul]

theorem mulPt_onePt' (hs : IsFinFlatSub G F h) (φ : F →ₐ[R] S) : mulPt hs φ (onePt hs S) = φ := by
  apply pt_ext hs
  rw [mulPt_spec, onePt_spec, _root_.mul_one]

end PositivityTheory.PrwZar.QiP
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

open TensorProduct

namespace PositivityTheory.PrwZar.QiP

open GlobalTheory.CompanionTheory.Ar.GR

section BaseChange

variable {R : Type} [CommRing R] {C : Type} [Field C] [Algebra R C] {F : Type} [CommRing F] [Algebra R F]

def uu : F →ₐ[R] (C ⊗[R] F) := (Algebra.TensorProduct.includeRight : F →ₐ[R] C ⊗[R] F)

def lft {T : Type} [CommRing T] [Algebra C T] [Algebra R T] [IsScalarTower R C T] (g : F →ₐ[R] T) :
    (C ⊗[R] F) →ₐ[C] T :=
  Algebra.TensorProduct.lift (Algebra.ofId C T) g (fun _ _ => Commute.all _ _)

theorem lft_uu {T : Type} [CommRing T] [Algebra C T] [Algebra R T] [IsScalarTower R C T] (g : F →ₐ[R] T) :
    ((lft g).restrictScalars R).comp (uu (C := C)) = g := by
  ext x
  simp [lft, uu]

theorem ext_uu {T : Type} [CommRing T] [Algebra C T] [Algebra R T] [IsScalarTower R C T]
    (x y : (C ⊗[R] F) →ₐ[C] T)
    (e : (x.restrictScalars R).comp (uu (C := C)) = (y.restrictScalars R).comp (uu (C := C))) : x = y := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · exact e

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {h : sp (R₀ := R) F ⟶ G}

def u1 : F →ₐ[R] (C ⊗[R] F) ⊗[C] (C ⊗[R] F) :=
  (((Algebra.TensorProduct.includeLeft : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F) ⊗[C] (C ⊗[R] F))).restrictScalars R).comp (uu (R := R) (C := C) (F := F))

def u2 : F →ₐ[R] (C ⊗[R] F) ⊗[C] (C ⊗[R] F) :=
  (((Algebra.TensorProduct.includeRight : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F) ⊗[C] (C ⊗[R] F))).restrictScalars R).comp (uu (R := R) (C := C) (F := F))

def dlt (hs : IsFinFlatSub G F h) : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F) ⊗[C] (C ⊗[R] F) :=
  lft (mulPt hs (u1 (C := C)) u2)

def eps (hs : IsFinFlatSub G F h) : (C ⊗[R] F) →ₐ[C] C :=
  lft (onePt hs C)

theorem eps_uu (hs : IsFinFlatSub G F h) :
    ((((Algebra.ofId C (C ⊗[R] F)).comp (eps (C := C) hs)).restrictScalars R).comp (uu (C := C))) = onePt hs (C ⊗[R] F) := by
  rw [← comp_onePt hs ((Algebra.ofId C (C ⊗[R] F)).restrictScalars R), ← lft_uu (C := C) (onePt hs C)]
  rfl

theorem mul_dlt_uu (hs : IsFinFlatSub G F h) (f g : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F)) :
    ((((Algebra.TensorProduct.lmul' C).comp ((Algebra.TensorProduct.map f g).comp (dlt (C := C) hs))).restrictScalars R).comp
      (uu (C := C))) = mulPt hs ((f.restrictScalars R).comp uu) ((g.restrictScalars R).comp uu) := by
  have e : (((Algebra.TensorProduct.lmul' C).comp ((Algebra.TensorProduct.map f g).comp (dlt (C := C) hs))).restrictScalars R).comp
      (uu (C := C)) = ((((Algebra.TensorProduct.lmul' C).comp (Algebra.TensorProduct.map f g))).restrictScalars R).comp
        (((dlt (C := C) hs).restrictScalars R).comp uu) := rfl
  rw [e, dlt, lft_uu, comp_mulPt]
  congr 1
  · ext x
    simp [u1, uu]
  · ext x
    simp [u2, uu]

theorem counitL (hs : IsFinFlatSub G F h) : Qi.CounitL (dlt (C := C) hs) (eps (C := C) hs) := by
  apply ext_uu
  rw [mul_dlt_uu, eps_uu]
  exact mulPt_onePt hs _

theorem counitR (hs : IsFinFlatSub G F h) : Qi.CounitR (dlt (C := C) hs) (eps (C := C) hs) := by
  apply ext_uu
  rw [mul_dlt_uu, eps_uu]
  exact mulPt_onePt' hs _

theorem pw_uu (hs : IsFinFlatSub G F h) (n : ℕ) :
    ((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) n).restrictScalars R).comp uu = powPt hs uu n := by
  induction n with
  | zero => exact eps_uu hs
  | succ n ih =>
    change (((Algebra.TensorProduct.lmul' C).comp ((Algebra.TensorProduct.map (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) n)
      (AlgHom.id C (C ⊗[R] F))).comp (dlt (C := C) hs))).restrictScalars R).comp uu = _
    rw [mul_dlt_uu, ih]
    rfl

theorem pw_mul (hs : IsFinFlatSub G F h) (a b : ℕ) :
    Qi.pw (dlt (C := C) hs) (eps (C := C) hs) (a * b) = (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) a).comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) b) := by
  apply ext_uu
  rw [pw_uu, powPt_mul]
  have hc : (((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) a).comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) b)).restrictScalars R).comp
      (uu (C := C)) = ((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) a).restrictScalars R).comp
        (((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) b).restrictScalars R).comp uu) := rfl
  rw [hc, pw_uu, comp_powPt, pw_uu]

def ptGrp (hs : IsFinFlatSub G F h) (S : Type) [CommRing S] [Algebra R S] : Subgroup (sp (R₀ := R) S ⟶ G) where
  carrier := {g | ∃ φ : F →ₐ[R] S, spMap φ ≫ h = g}
  mul_mem' := by
    rintro _ _ ⟨φ, rfl⟩ ⟨φ', rfl⟩
    exact ⟨mulPt hs φ φ', mulPt_spec hs φ φ'⟩
  one_mem' := ⟨onePt hs S, onePt_spec hs S⟩
  inv_mem' := by
    rintro _ ⟨φ, rfl⟩
    obtain ⟨χ, hχ⟩ := hs.inv S φ
    exact ⟨χ, eq_inv_of_mul_eq_one_left hχ⟩

theorem pts_killed [Module.Finite R F] (hs : IsFinFlatSub G F h) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : (C ⊗[R] F) →ₐ[C] C, x.comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) m) = eps hs := by
  haveI : Finite (ptGrp hs C) :=
    Finite.of_surjective (fun φ : F →ₐ[R] C => (⟨_, φ, rfl⟩ : ptGrp hs C))
      (by rintro ⟨_, φ, rfl⟩; exact ⟨φ, rfl⟩)
  refine ⟨Nat.card (ptGrp hs C), Nat.card_pos, fun x => ?_⟩
  apply ext_uu
  have hx : ((x.comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) (Nat.card (ptGrp hs C)))).restrictScalars R).comp
      (uu (C := C)) = (x.restrictScalars R).comp
        (((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) (Nat.card (ptGrp hs C))).restrictScalars R).comp uu) := rfl
  have he : ((eps (C := C) hs).restrictScalars R).comp uu = onePt hs C := lft_uu _
  rw [hx, pw_uu, comp_powPt, he]
  apply pt_ext hs
  rw [powPt_spec, onePt_spec]
  have h1 := pow_card_eq_one' (G := ptGrp hs C) (x := ⟨_, (x.restrictScalars R).comp uu, rfl⟩)
  exact congrArg Subtype.val h1

theorem uu_injective [Module.Flat R F] (hR : Function.Injective (algebraMap R C)) :
    Function.Injective (uu (R := R) (C := C) (F := F)) := Algebra.TensorProduct.includeRight_injective hR

end BaseChange

end PositivityTheory.PrwZar.QiP

namespace PositivityTheory.PrwZar

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Ar.GR QiP

theorem killedAny_of (hc : Qi.KilledCore) : KilledAny := by
  intro C _ _ v R _ _ hv G _ _ F _ _ h hs
  haveI := hs.fin
  haveI := hs.proj
  obtain ⟨N, hN0, hN⟩ := hc C (C ⊗[R] F) (dlt (C := C) hs) (eps hs) (counitL hs) (counitR hs) (pw_mul hs)
    (pts_killed hs)
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have key : powPt hs (AlgHom.id R F) N = onePt hs F := by
    have e1 := pw_uu (C := C) hs N
    have e0 := pw_uu (C := C) hs 0
    rw [hN, e0] at e1
    have a1 : (uu (R := R) (C := C) (F := F)).comp (powPt hs (AlgHom.id R F) N) = powPt hs uu N := by
      rw [comp_powPt, AlgHom.comp_id]
    have a0 : (uu (R := R) (C := C) (F := F)).comp (onePt hs F) = powPt hs uu 0 := by
      rw [comp_onePt]
      rfl
    ext y
    apply uu_injective (C := C) hinj
    exact congrArg (fun f => f y) (a1.trans (e1.symm.trans a0.symm))
  refine ⟨N, hN0, fun S _ _ φ => ?_⟩
  rw [← powPt_spec hs, ← onePt_spec hs S]
  have e : φ.comp (powPt hs (AlgHom.id R F) N) = φ.comp (onePt hs F) := by rw [key]
  rw [comp_powPt, comp_onePt, AlgHom.comp_id] at e
  rw [e]

end PositivityTheory.PrwZar
end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCore
section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCharP
set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

variable {K H : Type} [Field K] [CommRing H] [Algebra K H]

theorem pw_charP (p : ℕ) [Fact p.Prime] [CharP K p] (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K)
    (hL : CounitL Δ ε) (hR : CounitR Δ ε) (hmul : ∀ a b : ℕ, pw Δ ε (a * b) = (pw Δ ε a).comp (pw Δ ε b))
    (r : ℕ) {x : H} (hx : x ∈ RingHom.ker ε) : pw Δ ε (p ^ r) x ∈ RingHom.ker ε ^ (2 ^ r) := by
  induction r generalizing x with
  | zero =>
    rw [pow_zero, pow_zero, pow_one, RingHom.mem_ker]
    have h := AlgHom.congr_fun (counit_pw Δ ε hL hR 1) x
    rw [AlgHom.comp_apply] at h
    rw [h]
    exact RingHom.mem_ker.1 hx
  | succ r ih =>
    have hp : (p : H) = 0 := by
      rw [← map_natCast (algebraMap K H), CharP.cast_eq_zero K p, map_zero]
    have h2 : pw Δ ε p x ∈ RingHom.ker ε ^ 2 := by
      have := pw_sub_mem Δ ε hL hR p hx
      rwa [hp, zero_mul, sub_zero] at this
    have hcomp : pw Δ ε (p ^ (r + 1)) = (pw Δ ε (p ^ r)).comp (pw Δ ε p) := by
      rw [pow_succ]
      exact hmul _ _
    rw [hcomp, AlgHom.comp_apply]
    have hmap : Ideal.map (pw Δ ε (p ^ r)) (RingHom.ker ε) ≤ RingHom.ker ε ^ (2 ^ r) :=
      Ideal.map_le_iff_le_comap.2 fun z hz => ih hz
    have hy : pw Δ ε (p ^ r) (pw Δ ε p x) ∈ Ideal.map (pw Δ ε (p ^ r)) (RingHom.ker ε ^ 2) :=
      Ideal.mem_map_of_mem _ h2
    rw [Ideal.map_pow] at hy
    have h3 := Ideal.pow_right_mono hmap 2 hy
    rwa [← pow_mul, ← pow_succ] at h3

end PositivityTheory.PrwZar.Qi
end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiStab
set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

theorem exists_stable_pow {K H : Type} [Field K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    (I : Ideal H) : ∃ (k : ℕ) (e : H), IsIdempotentElem e ∧ I ^ k = Ideal.span {e} ∧ ∀ j, k ≤ j → I ^ j = I ^ k := by
  haveI : IsArtinianRing H := isArtinian_of_tower K inferInstance
  haveI : IsNoetherianRing H := isNoetherian_of_tower K inferInstance
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := H) (M := H)
    ⟨fun n => OrderDual.toDual (I ^ n), fun a b h => Ideal.pow_le_pow_right h⟩
  have hst : ∀ j, n ≤ j → I ^ j = I ^ n := fun j hj => congrArg OrderDual.ofDual (hn j hj).symm
  have hidem : IsIdempotentElem (I ^ n) := by
    unfold IsIdempotentElem
    rw [← pow_add]
    exact hst (n + n) (by omega)
  obtain ⟨e, he, hI⟩ := (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian _)).1 hidem
  exact ⟨n, e, he, hI.trans Ideal.submodule_span_eq, hst⟩

end PositivityTheory.PrwZar.Qi
end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiIdem
set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

theorem idem_eq_zero {K H : Type} [Field K] [IsAlgClosed K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    {f : H} (hf : IsIdempotentElem f) (h : ∀ x : H →ₐ[K] K, x f = 0) : f = 0 := by
  by_contra hne
  have hne1 : Ideal.span {1 - f} ≠ ⊤ := by
    intro htop
    rw [Ideal.span_singleton_eq_top] at htop
    apply hne
    have h0 : f * (1 - f) = 0 := by rw [mul_sub, mul_one, hf.eq, sub_self]
    exact htop.mul_left_eq_zero.1 h0
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne1
  letI := Ideal.Quotient.field M
  haveI : Module.Finite K (H ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K M).toLinearMap (Ideal.Quotient.mkₐ_surjective K M)
  haveI : Algebra.IsIntegral K (H ⧸ M) := Algebra.IsIntegral.of_finite K (H ⧸ M)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := H ⧸ M)
  let e : K ≃ₐ[K] H ⧸ M := AlgEquiv.ofBijective (Algebra.ofId K (H ⧸ M)) hb
  let x : H →ₐ[K] K := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K M)
  have h1 : Ideal.Quotient.mk M f = 1 := by
    have hmem : 1 - f ∈ M := hle (Ideal.mem_span_singleton_self _)
    have h2 : Ideal.Quotient.mk M (1 - f) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hmem
    rw [map_sub, map_one, sub_eq_zero] at h2
    exact h2.symm
  have hx1 : x f = 1 := by
    change e.symm (Ideal.Quotient.mkₐ K M f) = 1
    rw [Ideal.Quotient.mkₐ_eq_mk, h1, map_one]
  have hx := h x
  rw [hx1] at hx
  exact one_ne_zero hx

end PositivityTheory.PrwZar.Qi
end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCartier
set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

variable {K H : Type} [Field K] [CommRing H] [Algebra K H]

theorem qc_stable [FiniteDimensional K H] (I : Ideal H) : ∃ k : ℕ, ∀ j, k ≤ j → I ^ j = I ^ k := by
  haveI : IsArtinianRing H := IsArtinianRing.of_finite K H
  let f : ℕ →o (Ideal H)ᵒᵈ := ⟨fun n => OrderDual.toDual (I ^ n), fun _ _ hab => Ideal.pow_le_pow_right hab⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes f
  exact ⟨n, fun j hj => congrArg OrderDual.ofDual (hn j hj).symm⟩

theorem qc_functional (ε : H →ₐ[K] K) {x : H} (hx : x ∈ RingHom.ker ε) (hx2 : x ∉ RingHom.ker ε ^ 2) :
    ∃ l : H →ₗ[K] K, l 1 = 0 ∧ (∀ y ∈ RingHom.ker ε ^ 2, l y = 0) ∧ l x = 1 := by
  let W : Submodule K H := Submodule.span K {(1 : H)} ⊔ (RingHom.ker ε ^ 2).restrictScalars K
  have hxW : x ∉ W := by
    intro h
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hz2 : z ∈ RingHom.ker ε ^ 2 := hz
    have hz' : z ∈ RingHom.ker ε := Ideal.pow_le_self two_ne_zero hz2
    have hc : c = 0 := by
      have h1 : ε x = 0 := hx
      have h2 : ε z = 0 := hz'
      rw [← hyz, map_add (f := _), map_smul, map_one, h2] at h1
      simpa using h1
    subst hc
    apply hx2
    rw [← hyz, zero_smul, zero_add]
    exact hz2
  obtain ⟨f, hf, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxW inferInstance
  have hW : ∀ w ∈ W, f w = 0 := fun w hw => by
    have : f w ∈ W.map f := Submodule.mem_map_of_mem hw
    rw [hfW] at this
    simpa using this
  refine ⟨(f x)⁻¹ • f, ?_, ?_, ?_⟩
  · simp [hW 1 (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))]
  · intro y hy
    simp [hW y (Submodule.mem_sup_right hy)]
  · simp [hf]

theorem qc_leib (ε : H →ₐ[K] K) (l : H →ₗ[K] K) (h1 : l 1 = 0) (h2 : ∀ y ∈ RingHom.ker ε ^ 2, l y = 0)
    (a b : H) : l (a * b) = ε a * l b + l a * ε b := by
  have ha : a - algebraMap K H (ε a) ∈ RingHom.ker ε := by simp [RingHom.mem_ker]
  have hb : b - algebraMap K H (ε b) ∈ RingHom.ker ε := by simp [RingHom.mem_ker]
  have hab : l ((a - algebraMap K H (ε a)) * (b - algebraMap K H (ε b))) = 0 :=
    h2 _ (by rw [pow_two]; exact Ideal.mul_mem_mul ha hb)
  have e : a * b = (a - algebraMap K H (ε a)) * (b - algebraMap K H (ε b)) + ε a • b + ε b • a -
      (ε a * ε b) • (1 : H) := by
    simp only [Algebra.smul_def, map_mul, mul_one]
    ring
  rw [e, map_sub, map_add (f := _), map_add (f := _), hab, map_smul, map_smul, map_smul, h1]
  simp only [smul_eq_mul, mul_zero, sub_zero, zero_add]
  ring

theorem aug_le_sq {K H : Type} [Field K] [CharZero K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) (hL : CounitL Δ ε) (hR : CounitR Δ ε) :
    RingHom.ker ε ≤ RingHom.ker ε ^ 2 := by
  classical
  intro x hx
  by_contra hx2
  obtain ⟨l, hl1, hl2, hlx⟩ := qc_functional ε hx hx2
  let Φ : H ⊗[K] H →ₗ[K] H := (TensorProduct.rid K H).toLinearMap ∘ₗ LinearMap.lTensor H l
  let mR : H ⊗[K] H →ₐ[K] H :=
    (Algebra.TensorProduct.lmul' K).comp (Algebra.TensorProduct.map (AlgHom.id K H) ((Algebra.ofId K H).comp ε))
  let mL : H ⊗[K] H →ₐ[K] H :=
    (Algebra.TensorProduct.lmul' K).comp (Algebra.TensorProduct.map ((Algebra.ofId K H).comp ε) (AlgHom.id K H))
  have hΦ : ∀ s t : H ⊗[K] H, Φ (s * t) = mR s * Φ t + Φ s * mR t := by
    intro s t
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a₁ a₂ =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b₁ b₂ =>
        simp only [Φ, mR, Algebra.TensorProduct.tmul_mul_tmul, LinearMap.comp_apply, LinearMap.lTensor_tmul,
          LinearEquiv.coe_coe, TensorProduct.rid_tmul, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
          AlgHom.coe_id, id_eq, Algebra.TensorProduct.lmul'_apply_tmul, Algebra.ofId_apply,
          qc_leib ε l hl1 hl2, Algebra.smul_def, map_add, map_mul]
        ring
      | add t₁ t₂ h₁ h₂ => simp only [mul_add, map_add (f := _), h₁, h₂]; ring
    | add s₁ s₂ h₁ h₂ => simp only [add_mul, map_add (f := _), h₁, h₂]; ring
  have hεΦ : ∀ t : H ⊗[K] H, ε (Φ t) = l (mL t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [Φ, mL, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
        AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        Algebra.TensorProduct.lmul'_apply_tmul, Algebra.ofId_apply, map_smul, smul_eq_mul]
      rw [← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    | add s t h₁ h₂ => simp only [map_add (f := _), h₁, h₂]
  have hRa : ∀ a, mR (Δ a) = a := fun a => DFunLike.congr_fun hR a
  have hLa : ∀ a, mL (Δ a) = a := fun a => DFunLike.congr_fun hL a
  let D : H →ₗ[K] H := Φ ∘ₗ Δ.toLinearMap
  have hD : ∀ a b, D (a * b) = a * D b + D a * b := by
    intro a b
    simp only [D, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, hΦ, hRa]
  have hεD : ∀ a, ε (D a) = l a := by
    intro a
    simp only [D, LinearMap.comp_apply, AlgHom.toLinearMap_apply, hεΦ, hLa]
  have hDpow : ∀ n : ℕ, D (x ^ (n + 1)) = ((n : H) + 1) * x ^ n * D x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, hD, ih]
      push_cast
      ring
  obtain ⟨k, hk⟩ := qc_stable (K := K) (RingHom.ker ε)
  have hJJ : RingHom.ker ε ^ (k + 2) * RingHom.ker ε ^ (k + 2) = RingHom.ker ε ^ (k + 2) := by
    rw [← pow_add, hk (k + 2 + (k + 2)) (by omega), hk (k + 2) (by omega)]
  have hDJ : ∀ y ∈ RingHom.ker ε ^ (k + 2), D y ∈ RingHom.ker ε ^ (k + 2) := by
    intro y hy
    rw [← hJJ] at hy
    refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [hD]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hb)
    · rw [map_add (f := _)]
      exact Ideal.add_mem _ ha hb
  have hJ2 : RingHom.ker ε ^ (k + 2) ≤ RingHom.ker ε ^ 2 := Ideal.pow_le_pow_right (by omega)
  have hJ1 : RingHom.ker ε ^ (k + 2) ≤ RingHom.ker ε := Ideal.pow_le_self (by omega)
  have hex : ∃ n, x ^ n ∈ RingHom.ker ε ^ (k + 2) := ⟨k + 2, Ideal.pow_mem_pow hx _⟩
  have hN : x ^ Nat.find hex ∈ RingHom.ker ε ^ (k + 2) := Nat.find_spec hex
  have hmin : ∀ m < Nat.find hex, x ^ m ∉ RingHom.ker ε ^ (k + 2) := fun m hm => Nat.find_min hex hm
  have hN0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hN
    have : ε 1 = 0 := hJ1 hN
    simp at this
  have hN1 : Nat.find hex ≠ 1 := by
    intro h1
    rw [h1, pow_one] at hN
    exact hx2 (hJ2 hN)
  obtain ⟨M, hM⟩ : ∃ M, Nat.find hex = M + 2 := ⟨Nat.find hex - 2, by omega⟩
  have h1 : D (x ^ (M + 2)) ∈ RingHom.ker ε ^ (k + 2) := hDJ _ (hM ▸ hN)
  rw [hDpow (M + 1)] at h1
  let π := Ideal.Quotient.mk (RingHom.ker ε ^ (k + 2))
  have hu1 : IsUnit (π ((((M + 1 : ℕ) : H)) + 1)) := by
    have e : π ((((M + 1 : ℕ) : H)) + 1) = algebraMap K (H ⧸ RingHom.ker ε ^ (k + 2)) ((M + 2 : ℕ) : K) := by
      simp only [map_add (f := _), map_natCast, map_one]
      push_cast
      ring
    rw [e]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (by omega))).map _
  have hu2 : IsUnit (π (D x)) := by
    have hm : D x - 1 ∈ RingHom.ker ε := by
      change ε (D x - 1) = 0
      rw [map_sub, hεD, hlx, map_one, sub_self]
    have hnil : IsNilpotent (π (D x - 1)) :=
      ⟨k + 2, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hm _⟩
    have := hnil.isUnit_one_add
    rwa [map_sub, map_one, add_sub_cancel] at this
  have h0 : π ((((M + 1 : ℕ) : H) + 1) * x ^ (M + 1) * D x) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h1
  rw [map_mul, map_mul, hu2.mul_left_eq_zero, hu1.mul_right_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at h0
  exact hmin (M + 1) (by omega) h0

end PositivityTheory.PrwZar.Qi
end
end

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

theorem killedCore : KilledCore := by
  intro K H _ _ _ _ _ Δ ε hL hR hmul hpts
  obtain ⟨m, hm, hpt⟩ := hpts
  set I : Ideal H := RingHom.ker ε with hI
  obtain ⟨k, e, he, hIk, hstab⟩ := exists_stable_pow (K := K) I

  have hk1 : I ^ (k + 1) = Ideal.span {e} := by rw [hstab (k + 1) (Nat.le_succ k), hIk]
  have heI : e ∈ I := by
    have : e ∈ I ^ (k + 1) := by rw [hk1]; exact Ideal.subset_span rfl
    exact Ideal.pow_le_self (Nat.succ_ne_zero k) this

  have hs : ∃ s : ℕ, 0 < s ∧ ∀ x ∈ I, pw Δ ε s x ∈ I ^ k := by
    obtain ⟨p, hp⟩ := CharP.exists K
    rcases CharP.char_is_prime_or_zero K p with hpp | hp0
    · have : Fact p.Prime := ⟨hpp⟩
      refine ⟨p ^ k, pow_pos hpp.pos k, fun x hx => ?_⟩
      exact Ideal.pow_le_pow_right (Nat.lt_two_pow_self).le (pw_charP p Δ ε hL hR hmul k hx)
    · subst hp0
      have : CharZero K := CharP.charP_to_charZero K
      have h1 : pw Δ ε 1 = AlgHom.id K H := hL
      have hle : ∀ j : ℕ, I ≤ I ^ (j + 1) := by
        intro j
        induction j with
        | zero => rw [zero_add, pow_one]
        | succ j ih =>
          calc I ≤ I ^ 2 := aug_le_sq Δ ε hL hR
            _ = I * I := pow_two I
            _ ≤ I * I ^ (j + 1) := Ideal.mul_mono_right ih
            _ = I ^ (j + 1 + 1) := (pow_succ' I (j + 1)).symm
      refine ⟨1, one_pos, fun x hx => ?_⟩
      rw [h1]
      exact Ideal.pow_le_pow_right (Nat.le_succ k) (hle k hx)
  obtain ⟨s, hs0, hsI⟩ := hs

  have hme : pw Δ ε m e = 0 := by
    refine idem_eq_zero (K := K) (he.map (pw Δ ε m)) fun x => ?_
    have := congrArg (fun f : H →ₐ[K] K => f e) (hpt x)
    simp only [AlgHom.comp_apply] at this
    rw [this]
    exact heI
  refine ⟨m * s, Nat.mul_pos hm hs0, AlgHom.ext fun x => ?_⟩
  have hy : x - algebraMap K H (ε x) ∈ I := by
    change ε (x - algebraMap K H (ε x)) = 0
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (hIk ▸ hsI _ hy)
  have key : pw Δ ε (m * s) (x - algebraMap K H (ε x)) = 0 := by
    rw [hmul, AlgHom.comp_apply, ← ha, map_mul, hme, mul_zero]
  have h0 : pw Δ ε 0 (x - algebraMap K H (ε x)) = 0 := by
    change algebraMap K H (ε (x - algebraMap K H (ε x))) = 0
    rw [show ε (x - algebraMap K H (ε x)) = 0 from hy, map_zero]
  have e1 := congrArg (· + algebraMap K H (ε x)) key
  have e2 := congrArg (· + algebraMap K H (ε x)) h0
  simp only [map_sub, AlgHom.commutes, sub_add_cancel, zero_add] at e1 e2
  rw [e1, e2]

end PositivityTheory.PrwZar.Qi
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Ar.GR

theorem qi_isMonHom_id_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom ((𝟙 A) ^ n : A ⟶ A) := by
  induction n with
  | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (1 : A ⟶ A))
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))

theorem quasiInverseR_of (h1 : PolFibreIsogAny) (h5 : KilledAny) : QuasiInverseR := by
  intro C _ _ v R _ _ hv A B _ _ P l g hA hB hgA hgB h₁ h₂ hp
  have hm : IsMonHom l := hp.1
  have fib := h1 C v R hv A B P l g hA hB hgA hgB h₁ h₂ hp
  obtain ⟨hf, hs⟩ := GlobalTheory.T.finite_of_finite_fibres R A B l hA hB hm fun Ω _ _ s => ⟨(fib Ω s).1, (fib Ω s).2.2⟩
  have := hA.comm
  have := hA.smooth
  have := hB.smooth
  have hfl : Flat l.left := GlobalTheory.T.flat_of_fibres_finite R A B l inferInstance inferInstance inferInstance hf
    fun Ω _ _ s => (fib Ω s).2.1
  obtain ⟨F, _, _, h, hsub, hker⟩ := GlobalTheory.T.kernel_finite_flat R A B l hA hB hm hf hfl
  obtain ⟨n, hn, hk⟩ := h5 C v R hv A F h hsub
  obtain ⟨g, hg, e⟩ := GlobalTheory.T.factor_through_finite_flat R A B A l (𝟙 A ^ n) hm (qi_isMonHom_id_pow A n) hfl hs inferInstance
    fun S _ _ z hz => by
      obtain ⟨φ, rfl⟩ := (hker S z).1 hz
      rw [MonObj.comp_pow, Category.comp_id]
      exact hk S φ
  refine ⟨n, g, hn, hg, e, GlobalTheory.T.epi_of_finite_flat R A B B l hfl hs inferInstance _ _ ?_⟩
  rw [← Category.assoc, e, MonObj.comp_pow, MonObj.pow_comp, Category.id_comp, Category.comp_id]

theorem polFibreIsogAny : PolFibreIsogAny := Z2.polFibreIsogAny

theorem killedAny : KilledAny := killedAny_of Qi.killedCore

theorem quasiInverseR : QuasiInverseR := quasiInverseR_of polFibreIsogAny killedAny

end PositivityTheory.PrwZar
