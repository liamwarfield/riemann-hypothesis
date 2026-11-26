module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyRestrictionBetweenStableFamilies
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineCocycleClosed
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntegrableOfContinuousCompact
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

variable {X : Scheme.{0}}

def secMulOn {N : LB X} {a b c : ℤ} (h : a + b = c) {V : X.Opens} (x : SecOn (pw N a) V)
    (y : SecOn (pw N b) V) : SecOn (pw N c) V :=
  GlobalTheory.LB.mkSec (L := pw N c) (fun i => @HMul.hMul (Γ(X, V ⊓ N.U i)) (Γ(X, V ⊓ N.U i)) _ _ (GlobalTheory.LB.coord x i) (GlobalTheory.LB.coord y i)) (fun i j => by
    have hx := GlobalTheory.LB.coord_rel x i j (W := V ⊓ N.U i ⊓ N.U j) inf_le_left
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    have hy := GlobalTheory.LB.coord_rel y i j (W := V ⊓ N.U i ⊓ N.U j) inf_le_left
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    subst h
    have e : ((N.g i j ^ (a + b) : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) =
        ((N.g i j ^ a : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) *
          ((N.g i j ^ b : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) := by
      rw [zpow_add, Units.val_mul]
    erw [map_mul, map_mul]
    erw [hx, hy, e, map_mul]
    rw [show (AbLaw.pw N a).g i j = N.g i j ^ a from rfl, show (AbLaw.pw N b).g i j = N.g i j ^ b from rfl]
    exact mul_mul_mul_comm _ _ _ _)

@[simp] theorem coord_secMulOn {N : LB X} {a b c : ℤ} (h : a + b = c) {V : X.Opens}
    (x : SecOn (pw N a) V) (y : SecOn (pw N b) V) (i : N.ι) :
    GlobalTheory.LB.coord (secMulOn h x y) i =
      @HMul.hMul (Γ(X, V ⊓ N.U i)) (Γ(X, V ⊓ N.U i)) _ _ (GlobalTheory.LB.coord x i) (GlobalTheory.LB.coord y i) := rfl

end GlobalTheory.CompanionTheory.FormalAlg.Lift

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

variable {X : Scheme.{0}} {R : Type} [CommRing R]

def mulRight (f : X ⟶ Spec (CommRingCat.of R)) {N : LB X} {a b c : ℤ} (h : a + b = c)
    {V : X.Opens} (y : SecOn (pw N b) V) : SecOnR f (pw N a) V →ₗ[R] SecOnR f (pw N c) V where
  toFun x := SecOnR.of f _ V (secMulOn h ((SecOnR.of f _ V).symm x) y)
  map_add' x x' := GlobalTheory.LB.sec_ext fun (i : N.ι) => add_mul (R := Γ(X, V ⊓ N.U i)) _ _ _
  map_smul' r x := GlobalTheory.LB.sec_ext fun (i : N.ι) => mul_assoc (G := Γ(X, V ⊓ N.U i)) _ _ _

theorem coord_mulRight (f : X ⟶ Spec (CommRingCat.of R)) {N : LB X} {a b c : ℤ} (h : a + b = c)
    {V : X.Opens} (y : SecOn (pw N b) V) (x : SecOnR f (pw N a) V) (i : N.ι) :
    SecOnR.coord (mulRight f h y x) i =
      @HMul.hMul (Γ(X, V ⊓ N.U i)) (Γ(X, V ⊓ N.U i)) _ _ (SecOnR.coord x i) (GlobalTheory.LB.coord y i) :=
  rfl

def oneOn (N : LB X) {a : ℤ} (h : a = 0) (V : X.Opens) : SecOn (pw N a) V :=
  GlobalTheory.LB.mkSec (L := pw N a) (fun _ => 1) (fun i j => by
    subst h
    rw [map_one, map_one, show (AbLaw.pw N 0).g i j = N.g i j ^ (0 : ℤ) from rfl, zpow_zero,
      Units.val_one]
    erw [map_one, one_mul])

section Tower

variable (I : Ideal R)

abbrev toR (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (e : ℕ) :
    (Y e).left ⟶ Spec (CommRingCat.of R) :=
  (Y e).hom ≫ thick R I e

theorem toR_w (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (e : ℕ) :
    β e ≫ toR I Y (e + 1) =
      toR I Y e ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, toR, toR, ← Category.assoc, (hβ e).w,
    Category.assoc, thickTrans_comp]

variable {ι : Type} (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
  (N : ∀ e, LB (Y e).left) (D : ∀ e, Finset ι → (Y e).left.Opens) (d : ℤ)

abbrev Tm (e : ℕ) (t : ℤ) (S : Finset ι) : Type :=
  SecOnR (toR I Y e) (pw (N e) (d * t)) (D e S)

def resT (hD : ∀ e (S S' : Finset ι), S ⊆ S' → D e S' ≤ D e S) (e : ℕ) (t : ℤ) {S S' : Finset ι}
    (h : S ⊆ S') : Tm I Y N D d e t S →ₗ[R] Tm I Y N D d e t S' :=
  SecOnR.restrict (toR I Y e) _ (hD e S S' h)

def mulT (e : ℕ) (t : ℤ) (S : Finset ι) (σ : SecOn (pw (N e) d) (D e S)) :
    Tm I Y N D d e t S →ₗ[R] Tm I Y N D d e (t + 1) S :=
  mulRight (toR I Y e) (by ring) σ

theorem mulT_comm (e : ℕ) (t : ℤ) (S : Finset ι) (σ τ : SecOn (pw (N e) d) (D e S))
    (x : Tm I Y N D d e t S) :
    mulT I Y N D d e (t + 1) S σ (mulT I Y N D d e t S τ x) =
      mulT I Y N D d e (t + 1) S τ (mulT I Y N D d e t S σ x) := by
  refine SecOnR.ext_iff.mpr fun i => ?_
  unfold mulT
  first
  | (erw [coord_mulRight, coord_mulRight, coord_mulRight, coord_mulRight]; exact mul_right_comm _ _ _)
  | (simp only [coord_mulRight]; exact mul_right_comm _ _ _)
  | (simp only [coord_mulRight]; ring)

def oneT (e : ℕ) (S : Finset ι) : Tm I Y N D d e 0 S :=
  SecOnR.of _ _ _ (oneOn (N e) (mul_zero d) (D e S))

def redL (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e)))
    (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V : (Y (e + 1)).left.Opens)
    (V' : (Y e).left.Opens) (h : V' ≤ β e ⁻¹ᵁ V) :
    SecOnR (toR I Y (e + 1)) (L (e + 1)) V →ₗ[R] SecOnR (toR I Y e) (L e) V' :=
  (SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
    (hL e).2 V')).symm.toLinearMap ∘ₗ SecOnR.pull (L (e + 1)) (toR_w I Y β hβ e) V V' h

def red (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e)))
    (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen)
    (hDβ : ∀ e (S : Finset ι), D e S ≤ β e ⁻¹ᵁ D (e + 1) S) (a : ℤ) (e : ℕ) (S : Finset ι) :
    SecOnR (toR I Y (e + 1)) (pw (N (e + 1)) a) (D (e + 1) S) →ₗ[R]
      SecOnR (toR I Y e) (pw (N e) a) (D e S) :=
  redL I Y β hβ (fun e => pw (N e) a) (fun e => pullPow (v e) a)
    (fun e => ⟨isLB_pw (hN e).1 a, pullPow_isGen (v e) a (hN e).2⟩) e (D (e + 1) S) (D e S) (hDβ e S)

end Tower

section Sub

variable {ι : Type} [DecidableEq ι]

theorem sub_pair_left (i j : ι) : ({i} : Finset ι) ⊆ {i, j} :=
  Finset.singleton_subset_iff.2 (Finset.mem_insert_self _ _)

theorem sub_pair_right (i j : ι) : ({j} : Finset ι) ⊆ {i, j} :=
  Finset.singleton_subset_iff.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

theorem sub_triple_ij (i j k : ι) : ({i, j} : Finset ι) ⊆ {i, j, k} := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

theorem sub_triple_jk (i j k : ι) : ({j, k} : Finset ι) ⊆ {i, j, k} := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

theorem sub_triple_ik (i j k : ι) : ({i, k} : Finset ι) ⊆ {i, j, k} := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

end Sub

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE

abbrev PO (R : Type) [CommRing R] (N : ℕ) : Over (Spec (CommRingCat.of R)) :=
  Over.mk (GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R N)

abbrev thickι (R : Type) [CommRing R] (I : Ideal R) (N e : ℕ) :
    (thickObj R I e (PO R N)).left ⟶ PSpace R N :=
  pullback.fst (PO R N).hom (thick R I e)

variable {R : Type} [CommRing R] {N : ℕ}

def HomogIdeal {B : Type} [CommRing B] {n : ℕ} (P : Ideal (MvPolynomial (Fin n) B)) : Prop :=
  ∀ (d : ℕ) (f : MvPolynomial (Fin n) B), f ∈ P → homogeneousComponent d f ∈ P

def KillsForm {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R)
    (hf : f.IsHomogeneous n) : Prop :=
  ∀ k, (φ.app (GlobalTheory.ProjSpace.chart R N k)).hom
    (GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n f hf) = 0

def vanIdeal {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) : Ideal (MvPolynomial (Fin (N + 1)) R) :=
  Ideal.span {f | ∃ n, ∃ hf : f.IsHomogeneous n, KillsForm φ n f hf}


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem vanIdeal_homog {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) : HomogIdeal (vanIdeal φ) := by
  intro d f hf
  have hI : (vanIdeal φ).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) R) := by
    apply Ideal.homogeneous_span
    rintro x ⟨n, hx, -⟩
    exact ⟨n, (mem_homogeneousSubmodule n x).mpr hx⟩
  exact homogeneousComponent_mem_of_mem hI hf d

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueChernClassNilpotentBase
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueChernClassNilpotentBase
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.CrystallineChernClass

theorem mapH_bijective {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K : Cx.{1} R} {M : Cx.{1} R'}
    (φ : Cx.Hom K M σ) (h : ∀ n, Function.Bijective (φ.f n)) (n : ℕ) : Function.Bijective (φ.mapH n) := by
  refine ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero (φ.mapH n)).2 fun x hx => ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : φ.f n z.1 ∈ M.B n := (Submodule.Quotient.mk_eq_zero ((M.B n).submoduleOf (M.Z n)) (x := φ.mapZ n z)).1 hx
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    change z.1 ∈ K.B n
    cases n with
    | zero =>
      have h2 : φ.f 0 z.1 = 0 := h1
      have h3 : z.1 = 0 := (h 0).1 (h2.trans (map_zero _).symm)
      rw [h3]
      exact Submodule.zero_mem _
    | succ n =>
      obtain ⟨y, hy⟩ := h1
      obtain ⟨y', rfl⟩ := (h n).2 y
      refine ⟨y', (h (n + 1)).1 ?_⟩
      rw [← φ.comm, hy]
  · intro y
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨x, hx⟩ := (h n).2 w.1
    have h0 : K.d n x = 0 := (h (n + 1)).1 (by
      rw [← φ.comm, hx, map_zero]
      exact w.2)
    exact ⟨Submodule.Quotient.mk ⟨x, h0⟩, congrArg _ (Subtype.ext hx)⟩

section Gen

variable {b : Base} {L : b.Fun} {Λ : Type} [CommRing Λ] (c : Λ →+* b.R)

def toO (Q : ObjectProperty (Thick L)) : CH.Mor (Q.ι ⋙ B.OM L c) (CH.modF (sP Q).A) c where
  G := 𝟭 _
  τ T := { toFun := fun x => x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  nat _ _ := rfl

theorem toO_bij (Q : ObjectProperty (Thick L)) (n : ℕ) : Function.Bijective ((toO c Q).pull n) :=
  mapH_bijective _ (fun _ => Function.bijective_id) n

def sub {P Q : ObjectProperty (Thick L)} (h : Q ≤ P) : CH.Mor (P.ι ⋙ B.OM L c) (Q.ι ⋙ B.OM L c) (RingHom.id Λ) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem sub_square {P Q : ObjectProperty (Thick L)} (h : Q ≤ P) (j : ℕ) (x : CH.H (P.ι ⋙ B.OM L c) j) :
    (toO c Q).pull j ((sub c h).pull j x) = (incl h).o.pull j ((toO c P).pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem sub_bij {P Q : ObjectProperty (Thick L)} (h : Q ≤ P) (j : ℕ) (hb : Function.Bijective ((incl h).o.pull j)) :
    Function.Bijective ((sub c h).pull j) := by
  have e : (toO c Q).pull j ∘ (sub c h).pull j = (incl h).o.pull j ∘ (toO c P).pull j :=
    funext (sub_square c h j)
  refine (Function.Bijective.of_comp_iff' (toO_bij c Q j) _).1 ?_
  rw [e]
  exact hb.comp (toO_bij c P j)

theorem sub_sub {P Q S : ObjectProperty (Thick L)} (h : Q ≤ P) (h' : S ≤ Q) (j : ℕ) (x : CH.H (P.ι ⋙ B.OM L c) j) :
    (sub c h').pull j ((sub c h).pull j x) = (sub c (h'.trans h)).pull j x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem res_sub {P Q : ObjectProperty (Thick L)} (h : Q ≤ P) (j : ℕ) (x : CH.H (B.OM L c) j) :
    (sub c h).pull j ((CH.Mor.restrict (B.OM L c) P.ι).pull j x) = (CH.Mor.restrict (B.OM L c) Q.ι).pull j x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem res_all (P : ObjectProperty (Thick L)) (hP : ∀ T, P T) (j : ℕ) :
    Function.Bijective ((CH.Mor.restrict (B.OM L c) P.ι).pull j) := by
  refine mapH_bijective _ (fun n => ⟨fun f g e => ?_, fun g => ?_⟩) j
  · funext t
    exact congrFun e (P.lift t fun i => hP _)
  · exact ⟨fun t => g (P.lift t fun i => hP _), rfl⟩

theorem bij_three {P Q S : ObjectProperty (Thick L)} (h : Q ≤ P) (h1 : S ≤ Q) (h2 : S ≤ P) (j : ℕ)
    (b1 : Function.Bijective ((incl h1).o.pull j)) (b2 : Function.Bijective ((incl h2).o.pull j)) (hP : ∀ T, P T) :
    Function.Bijective ((CH.Mor.restrict (B.OM L c) Q.ι).pull j) := by
  have s1 := sub_bij c h1 j b1
  have s2 := sub_bij c h2 j b2
  have s3 : Function.Bijective ((sub c h).pull j) := by
    have e : (sub c h1).pull j ∘ (sub c h).pull j = (sub c h2).pull j := funext (sub_sub c h h1 j)
    refine (Function.Bijective.of_comp_iff' s1 _).1 ?_
    rw [e]
    exact s2
  have e : (sub c h).pull j ∘ (CH.Mor.restrict (B.OM L c) P.ι).pull j =
      (CH.Mor.restrict (B.OM L c) Q.ι).pull j := funext (res_sub c h j)
  rw [← e]
  exact s3.comp (res_all c _ hP j)

end Gen

end GlobalTheory.CompanionTheory.CrystallineChernClass

namespace GlobalTheory.CompanionTheory.CrystallineChernClass

section Core

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
  {κ : O →+* b.R ⧸ b.I}

def precomp {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {g : C ⥤ Thick ((B.schFn q).cr b ht κ)} {D : E.LineData X}
    (Λ₀ : B.CLift g D) (h : C' ⥤ C) : B.CLift (h ⋙ g) D where
  p c := Λ₀.p (h.obj c)
  hp c := Λ₀.hp (h.obj c)
  w φ := Λ₀.w (h.map φ)
  hw φ hh := Λ₀.hw (h.map φ) hh

theorem exu_core (D : E.LineData X) (Q : ObjectProperty (Thick ((B.schFn q).cr b ht κ)))
    (hQ : ∀ T, Q T ↔ ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = B.thPt T)
    {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (N : ℕ)
    (hbij : Function.Bijective ((CH.Mor.restrict (B.OM ((B.schFn q).cr b ht κ) c) Q.ι).pull 2))
    (hN : ∀ (T : Thick ((B.schFn q).cr b ht κ)) (k : ℕ), N ≤ k → (k.factorial : T.B) = 0) :
    ∃! x, B.IsFirstChernClassOfLineBundle (q := q) (b := b) (ht := ht) (κ := κ) D c N x := by
  obtain ⟨Λ₀⟩ := GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift Q.ι D (fun T => (hQ _).1 T.property)
  have hz₀ := (GlobalTheory.T.crystalline_cocycle_closed Q.ι D c N (fun T k hk x _ => by
    change ((k.factorial : ℕ) : (T.obj).B) * _ = 0
    rw [hN _ k hk, zero_mul])).1 Λ₀
  obtain ⟨x, hx⟩ := hbij.2 ((CH.cx _).cls _ hz₀)
  refine ⟨x, ?_, ?_⟩
  · intro C _ G Λ₁
    have hG : ∀ T, Q (G.obj T) := fun T => (hQ _).2 ⟨Λ₁.p T, Λ₁.hp T⟩
    have hcl := GlobalTheory.T.crystalline_cocycle_closed G D c N (fun T k hk x _ => by rw [hN _ k hk, zero_mul])
    let Λ' : B.CLift G D := precomp Λ₀ (Q.lift G hG)
    refine ⟨hcl.1 Λ₁, ?_⟩
    rw [hcl.2 Λ₁ Λ' (hcl.1 Λ₁) (hcl.1 Λ')]
    have e1 : (CH.Mor.restrict (B.OM ((B.schFn q).cr b ht κ) c) G).pull 2 x =
        (CH.Mor.restrict (Q.ι ⋙ B.OM ((B.schFn q).cr b ht κ) c) (Q.lift G hG)).pull 2
          ((CH.Mor.restrict (B.OM ((B.schFn q).cr b ht κ) c) Q.ι).pull 2 x) := by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
    rw [e1, hx]
    rfl
  · intro y hy
    apply hbij.1
    obtain ⟨h1, h2⟩ := hy _ Q.ι Λ₀
    rw [hx, ← h2]

end Core

section Main

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

def Lifts (D : E.LineData X) : ObjectProperty (Thick (nlFun γ p X q κ)) :=
  fun T => ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = pt T

theorem st_le_lifts (D : E.LineData X) : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (𝒱D D) ≤ Lifts D := by
  rintro T ⟨-, V, ⟨σ, hσ⟩, hV⟩
  have hr : Set.range (pt T) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hV (show x ∈ (⊤ : Scheme.Opens _) from trivial)
  refine ⟨IsOpenImmersion.lift V.ι (pt T) hr ≫ σ, ?_⟩
  rw [Category.assoc, hσ, IsOpenImmersion.lift_fac]

theorem inU_top (T : Thick (nlFun γ p X q κ)) : InU ⊤ T := fun _ _ => trivial

theorem lifts_map (D : E.LineData X) {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (h : Lifts D T) : Lifts D T' := by
  obtain ⟨a, ha⟩ := h
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ a, ?_⟩
  rw [Category.assoc, ha]
  exact congrArg (fun y => y.1.2) φ.pt

theorem res_bij (hp : p ≠ 0) (D : E.LineData X) (hD : sSup (𝒱D D) = ⊤) {Λ : Type} [CommRing Λ] (c : Λ →+* R) (j : ℕ) :
    Function.Bijective ((CH.Mor.restrict (B.OM (nlFun γ p X q κ) c) (Lifts D).ι).pull j) := by
  have hU : Used (⊤ : ObjectProperty (Thick (nlFun γ p X q κ))) := Or.inr ⟨hp, Or.inl rfl⟩
  have h1 : St ⊤ (𝒱D D) ≤ Lifts (γ := γ) (p := p) (q := q) (κ := κ) D := st_le_lifts D
  have h1' : Lifts (γ := γ) (p := p) (q := q) (κ := κ) D ≤ St ⊤ {sSup (𝒱D D)} := fun T _ =>
  ⟨trivial, _, rfl, by rw [hD]; exact inU_top T⟩
  have b1 := (GlobalTheory.T.cohomology_restriction_between_stable_families ⊤ hU (𝒱D D) (Lifts D) h1 h1' (fun T T' φ h _ => lifts_map D φ h) j).2.2
  have h2 : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (𝒱D D) ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, inU_top T⟩
  have b2 := (GlobalTheory.T.cech_refinement_cohomology_bijective ⊤ hU (𝒱D D) {⊤} h2 (by rintro W rfl; rw [hD]) j).2.2
  have h3 : Lifts (γ := γ) (p := p) (q := q) (κ := κ) D ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, inU_top T⟩
  have hall : ∀ T, St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {⊤} T := fun T => ⟨trivial, ⊤, rfl, inU_top T⟩
  exact bij_three (b := nlBase R I γ p) (L := nlFun γ p X q κ) c h3 h1 h2 j b1 b2 hall

end Main

theorem existsUnique_crystalline_chern_class : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (D : E.LineData X) (hD : sSup (𝒱D D) = ⊤) {Λ : Type} [CommRing Λ]
    (c : Λ →+* R) (N : ℕ), (N.factorial : R) = 0 →
    ∃! x, B.IsFirstChernClassOfLineBundle (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) D c N x := by
  intro O R _ _ I γ p hp X q κ D hD Λ _ c N hN
  have hf : ∀ (T : Thick ((B.schFn q).cr (nlBase R I γ p) rfl κ)) (k : ℕ), N ≤ k → (k.factorial : T.B) = 0 := fun T k hk => by
    obtain ⟨m, hm⟩ := Nat.factorial_dvd_factorial hk
    have h0 : (k.factorial : R) = 0 := by rw [hm, Nat.cast_mul, hN, zero_mul]
    have := congrArg T.i h0
    rwa [map_natCast, map_zero] at this
  have hb := res_bij (γ := γ) (q := q) (κ := κ) hp D hD c 2
  let Q : ObjectProperty (Thick ((B.schFn q).cr (nlBase R I γ p) rfl κ)) := Lifts (γ := γ) (p := p) (q := q) (κ := κ) D
  have hQ : ∀ T, Q T ↔ ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = B.thPt T := fun T => Iff.rfl
  have hb' : Function.Bijective ((CH.Mor.restrict (B.OM ((B.schFn q).cr (nlBase R I γ p) rfl κ) c) Q.ι).pull 2) := hb
  exact exu_core (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) D Q hQ c N hb' hf

end GlobalTheory.CompanionTheory.CrystallineChernClass
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueChernClassNilpotentBaseStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_chern_class_nilpotent_base : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (D : E.LineData X) (hD : sSup (𝒱D D) = ⊤) {Λ : Type} [CommRing Λ]
    (c : Λ →+* R) (N : ℕ), (N.factorial : R) = 0 →
    ∃! x, B.IsFirstChernClassOfLineBundle (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) D c N x := by
  first | exact @GlobalTheory.CompanionTheory.CrystallineChernClass.existsUnique_crystalline_chern_class | exact GlobalTheory.CompanionTheory.CrystallineChernClass.existsUnique_crystalline_chern_class | (intros; apply GlobalTheory.CompanionTheory.CrystallineChernClass.existsUnique_crystalline_chern_class <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusRestrictionRepresentation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusRestrictionRepresentation
noncomputable section

open Finset Matrix

namespace GlobalTheory.CompanionTheory.RgTorus

open PositivityTheory.RgDs.K

variable {n : ℕ}

theorem tor_inv (θ : Fin n → ℝ) :
    (tor θ)⁻¹ = Matrix.diagonal fun a => Complex.exp (-((θ a : ℂ) * Complex.I)) := by
  apply Matrix.inv_eq_left_inv
  simp only [tor, Matrix.diagonal_mul_diagonal, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  exact Matrix.diagonal_one

theorem adC_tor_ne (θ : Fin n → ℝ) {p q : Fin n × Fin n} (h : p ≠ q) : adC (tor θ) p q = 0 := by
  unfold adC
  rw [tor_inv]
  by_cases h1 : q.1 = p.1
  · have h2 : p.2 ≠ q.2 := fun h2 => h (Prod.ext h1.symm h2)
    rw [Matrix.diagonal_apply_ne _ h2, mul_zero]
  · unfold tor
    rw [Matrix.diagonal_apply_ne _ h1, zero_mul]

theorem adC_tor_self (θ : Fin n → ℝ) (p : Fin n × Fin n) :
    adC (tor θ) p p = Complex.exp (((θ p.1 - θ p.2 : ℝ) : ℂ) * Complex.I) := by
  unfold adC
  rw [tor_inv]
  unfold tor
  rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem rhoTorus : RhoTorus := by
  intro n ε Λ T m θ k hk a x
  unfold rhoA
  rw [hk, Finset.sum_eq_single x.2]
  · congr 1
    simp only [adC_tor_self]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
  · intro w _ hw
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (adC_tor_ne θ hi), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end GlobalTheory.CompanionTheory.RgTorus
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusRestrictionRepresentationStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_restriction_representation : PositivityTheory.RgDs.K.RhoTorus := by
  first | exact @GlobalTheory.CompanionTheory.RgTorus.rhoTorus | exact GlobalTheory.CompanionTheory.RgTorus.rhoTorus | (intros; apply GlobalTheory.CompanionTheory.RgTorus.rhoTorus <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CKContinuous
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgFd

variable {n : ℕ}

theorem cont_triple {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [Group B]
    [IsTopologicalGroup B] (F : A × B → ℝ) (c : B → ℝ) (hF : Continuous F) (hc : Continuous c) :
    Continuous fun z : A × (B × B) => F (z.1, z.2.1) * F (z.1, z.2.2) * c (z.2.1⁻¹ * z.2.2) ^ 2 := by
  have h1 : Continuous fun z : A × (B × B) => F (z.1, z.2.1) :=
    hF.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have h2 : Continuous fun z : A × (B × B) => F (z.1, z.2.2) :=
    hF.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  have h3 : Continuous fun z : A × (B × B) => c (z.2.1⁻¹ * z.2.2) :=
    hc.comp (((continuous_fst.comp continuous_snd).inv).mul (continuous_snd.comp continuous_snd))
  exact (h1.mul h2).mul (h3.pow 2)

theorem cont_slice {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] (f : A × B → ℝ)
    (hf : Continuous f) (a : A) : Continuous fun b : B => f (a, b) :=
  hf.comp (continuous_const.prodMk continuous_id)

theorem cK_continuous {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Continuous (cK T) := by
  have h : Continuous fun k : KG ε => T.op k T.w :=
    (KType_continuous_op T).clm_apply continuous_const
  have h2 : Continuous fun k : KG ε => ‖⟪T.w, T.op k T.w⟫_ℂ‖ := (continuous_const.inner h).norm
  exact h2

theorem hI_continuous (hC : PhiCont) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) :
    Continuous fun z : UJ ε × (KG ε × KG ε) => hI T μ (pP (toM z.1)) z.2 :=
  cont_triple (fun z : UJ ε × KG ε => phiK μ (pP (toM z.1)) z.2) (cK T) (hC n ε μ) (cK_continuous T)

theorem hI_measurable (hC : PhiCont) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) :
    Measurable fun z : UJ ε × (KG ε × KG ε) => hI T μ (pP (toM z.1)) z.2 :=
  (hI_continuous hC T μ).measurable

theorem hI_nonneg (hMul : PhiMul) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (p : KG ε × KG ε) :
    0 ≤ hI T μ x p := by
  have a := (hMul n ε μ 0 x hx p.1).1
  have b := (hMul n ε μ 0 x hx p.2).1
  exact mul_nonneg (mul_pos a b).le (sq_nonneg _)

theorem hI_integrable (hC : PhiCont) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) (g : UJ ε) :
    Integrable (fun p : KG ε × KG ε => hI T μ (pP (toM g)) p) ((dk ε).prod (dk ε)) := by
  haveI : IsProbabilityMeasure (dk ε) := (dk_props ε).1
  have hc : Continuous fun p : KG ε × KG ε => hI T μ (pP (toM g)) p :=
    cont_slice (fun z : UJ ε × (KG ε × KG ε) => hI T μ (pP (toM z.1)) z.2)
      (hI_continuous hC T μ) g
  exact integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)

theorem hsInt : HsPs → HsPol → PhiMul → PhiCont → HsInt := by
  intro hPs hPol hMul hC n ε Λ T μ
  refine ⟨hI_measurable hC T μ, fun g => ?_⟩
  obtain ⟨⟨X, hX, hE⟩, hN⟩ := hPol n ε (toM g) g.2
  have hpd : (pP (toM g)).PosDef := by
    rw [hE]
    exact exp_noncompactPart_posDef hX
  rw [hN Λ T μ, hPs n ε Λ T μ _ hpd, ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal (hI_integrable hC T μ g)
      (Filter.Eventually.of_forall (hI_nonneg hMul T μ hpd))]

end GlobalTheory.CompanionTheory.RgFd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueIsFirstChernTorsionFree
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CrystallineFirstChernTorsionFree

section Core

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
  {κ : O →+* b.R ⧸ b.I}

def precomp {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {g : C ⥤ Thick ((B.schFn q).cr b ht κ)} {D : E.LineData X}
    (Λ₀ : B.CLift g D) (h : C' ⥤ C) : B.CLift (h ⋙ g) D where
  p c := Λ₀.p (h.obj c)
  hp c := Λ₀.hp (h.obj c)
  w φ := Λ₀.w (h.map φ)
  hw φ hh := Λ₀.hw (h.map φ) hh

end Core

section Main

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} {γ : DividedPowers I} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {l s : ℕ}

theorem dpow_vanish {T : Thick (nlFun γ 0 X q (κA O I))} (hT : TF l s T) (k : ℕ) (hk : s ≤ k) (x : T.B) (hx : x ∈ T.J) :
    (k.factorial : T.B) * T.δ.dpow (k + 1) x = 0 := by
  have h1 : T.δ.dpow (k + 1) x ∈ T.pdPow s := by
    rw [pdPow_eq]
    refine Ideal.subset_span ⟨[(k + 1, x)], ?_, ?_, ?_⟩
    · intro z hz
      rw [List.mem_singleton] at hz
      rw [hz]
      exact hx
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
    · simp
  rw [hT.1] at h1
  rw [(Ideal.mem_bot.1 h1), mul_zero]

theorem lifts_of_mem (D : E.LineData X) (T : Thick (nlFun γ 0 X q (κA O I))) (h : ∃ V ∈ 𝒱D D, InU V T) :
    ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = pt T := by
  obtain ⟨V, ⟨σ, hσ⟩, hV⟩ := h
  have hr : Set.range (pt T) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hV (show x ∈ (⊤ : Scheme.Opens _) from trivial)
  refine ⟨IsOpenImmersion.lift V.ι (pt T) hr ≫ σ, ?_⟩
  rw [Category.assoc, hσ, IsOpenImmersion.lift_fac]

end Main

theorem existsUnique_isFirstChernTorsionFree : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (D : E.LineData X), sSup (𝒱D D) = ⊤ → ∃! z, IsFirstChernThickening (TS γ q l s {⊤}) D s z := by
  intro O A _ _ _ I γ X q l s D hD
  have hle : St (TF l s) (𝒱D D) ≤ TS γ q l s {⊤} := fun T h => ⟨h.1, ⊤, rfl, fun _ _ => trivial⟩
  have hU : Used (TF l s : ObjectProperty (Thick (nlFun γ 0 X q (κA O I)))) := Or.inl ⟨rfl, l, s, rfl⟩
  have hb := (GlobalTheory.T.cech_refinement_cohomology_bijective (TF l s) hU (𝒱D D) {⊤} hle (by rintro W rfl; rw [hD]) 2).2.2
  let Q : ObjectProperty (Thick (nlFun γ 0 X q (κA O I))) := TS γ q l s {⊤}
  let Q' : ObjectProperty (Thick (nlFun γ 0 X q (κA O I))) := St (TF l s) (𝒱D D)
  let G₀ : Q'.FullSubcategory ⥤ Thick ((B.schFn q).cr (nlBase A I γ 0) rfl (κA O I)) := Q'.ι
  obtain ⟨Λ₀⟩ := GlobalTheory.T.exists_crystalline_lift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) G₀ D
    (fun T => lifts_of_mem D T.obj T.property.2)
  have hz₀ := (GlobalTheory.T.crystalline_cocycle_closed G₀ D (RingHom.id A) s (fun T k hk x hx => dpow_vanish T.property.1 k hk x hx)).1 Λ₀
  obtain ⟨x, hx⟩ := hb.2 ((CH.cx _).cls _ hz₀)
  refine ⟨x, ?_, ?_⟩
  · intro C _ G hG Λ₁
    let G₁ : C ⥤ Thick ((B.schFn q).cr (nlBase A I γ 0) rfl (κA O I)) := G ⋙ Q.ι
    have hcl := GlobalTheory.T.crystalline_cocycle_closed G₁ D (RingHom.id A) s
      (fun T k hk x hx => dpow_vanish (G.obj T).property.1 k hk x hx)
    let G' : C ⥤ Q'.FullSubcategory := Q'.lift (G ⋙ Q.ι) fun T => ⟨(G.obj T).property.1, hG T⟩
    let Λ' : B.CLift G₁ D := precomp Λ₀ G'
    refine ⟨hcl.1 Λ₁, ?_⟩
    refine (hcl.2 Λ₁ Λ' (hcl.1 Λ₁) (hcl.1 Λ')).trans ?_
    have e1 : (CH.Mor.restrict (CH.modF (sP Q).A) G).pull 2 x =
        (CH.Mor.restrict (CH.modF (sP Q').A) G').pull 2 ((incl hle).o.pull 2 x) := by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
    rw [e1, hx]
    rfl
  · intro y hy
    apply hb.1
    obtain ⟨h1, h2⟩ := hy _ (ObjectProperty.ιOfLE hle) (fun T => T.property.2) Λ₀
    have e : (incl hle).o.pull 2 y = (CH.Mor.restrict (CH.modF (sP Q).A) (ObjectProperty.ιOfLE hle)).pull 2 y := by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rfl
    rw [hx, e]
    exact h2.symm

end GlobalTheory.CompanionTheory.CrystallineFirstChernTorsionFree
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusWeightDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusWeightDecomposition
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.RgDsTor

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW PositivityTheory.RgDs.K

variable {n : ℕ}

theorem diagI_inK (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    inK ε (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := by
  unfold inK inG Jm
  refine ⟨?_, ?_⟩
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_add, ← Matrix.diagonal_zero]
    congr 1
    funext a
    simp [star_mul]
    split_ifs <;> ring
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

theorem tor_eq_exp (θ : Fin n → ℝ) :
    tor θ = NormedSpace.exp (((1 : ℝ) : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := by
  rw [Complex.ofReal_one, one_smul, Matrix.exp_diagonal, Pi.exp_def]
  unfold tor
  congr 1
  funext a
  rw [Complex.exp_eq_exp_ℂ]

private theorem pow_apply_eq_pow_smul_of_apply_eq_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A : V →L[ℂ] V) (c : ℂ) (w : V) (h : A w = c • w) (k : ℕ) : (A ^ k) w = c ^ k • w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply, h, map_smul, ih, smul_smul, ← pow_succ']

theorem exp_apply_of_eigen {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (A : V →L[ℂ] V) (c : ℂ) (w : V) (h : A w = c • w) :
    NormedSpace.exp A w = Complex.exp c • w := by
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL (ContinuousLinearMap.apply ℂ V w)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).smul_const w
  rw [← Complex.exp_eq_exp_ℂ] at h2
  have h3 : HasSum (fun k : ℕ => (ContinuousLinearMap.apply ℂ V w) (((k.factorial : ℂ))⁻¹ • A ^ k))
      (Complex.exp c • w) := by
    convert h2 using 1
    funext k
    rw [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
      pow_apply_eq_pow_smul_of_apply_eq_smul A c w h k, smul_smul, smul_eq_mul]
  have e := h1.unique h3
  rwa [ContinuousLinearMap.apply_apply] at e

private theorem diagonal_mul_I_eq_sum_single (θ : Fin n → ℝ) :
    (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) =
      ∑ a, ((θ a : ℂ) * Complex.I) • Matrix.single a a (1 : ℂ) := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [if_neg hij]
    symm
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact hij rfl

theorem dtau_diag_w {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (θ : Fin n → ℝ) :
    T.dτ (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) T.w =
      (((∑ a, Λ a * θ a : ℝ) : ℂ) * Complex.I) • T.w := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [diagonal_mul_I_eq_sum_single, map_sum, ContinuousLinearMap.sum_apply]
  simp_rw [map_smul, ContinuousLinearMap.smul_apply, T.13, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem torW : TorW := by
  intro n ε Λ T θ k hk
  have hX := diagI_inK ε θ
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  have h1 : γ 1 = k := onep_KG_ext (by rw [hγ 1, hk, tor_eq_exp])
  rw [← h1, KType.op_curve T hX γ hγ 1]
  apply exp_apply_of_eigen
  rw [ContinuousLinearMap.smul_apply, dtau_diag_w, smul_smul, Complex.ofReal_one, one_mul]

end GlobalTheory.CompanionTheory.RgDsTor
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusWeightDecompositionStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_weight_decomposition : PositivityTheory.RgDs.K.TorW := by
  first | exact @GlobalTheory.CompanionTheory.RgDsTor.torW | exact GlobalTheory.CompanionTheory.RgDsTor.torW | (intros; apply GlobalTheory.CompanionTheory.RgDsTor.torW <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisIsAdicComplete
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisIsAdicComplete
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ACrisAdic

theorem acris_isAdicComplete :
    ∀ {l : ℕ} [Fact l.Prime], IsAdicComplete (Ideal.span {(l : Acris l)}) (Acris l) := by
  intro l _
  exact ACris.isAdicComplete ℂ_[l] l

end GlobalTheory.CompanionTheory.ACrisAdic
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisIsAdicCompleteStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_isAdicComplete_span_prime : ∀ {l : ℕ} [Fact l.Prime], IsAdicComplete (Ideal.span {(l : Acris l)}) (Acris l) := by
  first | exact @GlobalTheory.CompanionTheory.ACrisAdic.acris_isAdicComplete | exact GlobalTheory.CompanionTheory.ACrisAdic.acris_isAdicComplete | (intros; apply GlobalTheory.CompanionTheory.ACrisAdic.acris_isAdicComplete <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIdealEqMap
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIdealEqMap
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem lev_IB_eq_map {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ) : (lev h k).IB = (lev h k).I.map (lev h k).ι := by
  have key : IB (fk l k) (xi0 l) = (I (fk l k) (xi0 l) l M).map (ι (fk l k) (xi0 l) l M) := by
    apply le_antisymm
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨⟩
      have hm : ofW (fk l k) (xi0 l) l M (xi0 l) ∈ I (fk l k) (xi0 l) l M := by
        show ι (fk l k) (xi0 l) l M (ofW (fk l k) (xi0 l) l M (xi0 l)) ∈ IB (fk l k) (xi0 l)
        rw [ι_ofW]
        exact Ideal.subset_span rfl
      have := Ideal.mem_map_of_mem (ι (fk l k) (xi0 l) l M) hm
      rwa [ι_ofW] at this
    · exact Ideal.map_comap_le
  exact key

end GlobalTheory.CompanionTheory.LatC
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIdealEqMapStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_ideal_eq_map : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), (lev h k).IB = (lev h k).I.map (lev h k).ι := by
  first | exact @GlobalTheory.CompanionTheory.LatC.lev_IB_eq_map | exact GlobalTheory.CompanionTheory.LatC.lev_IB_eq_map | (intros; apply GlobalTheory.CompanionTheory.LatC.lev_IB_eq_map <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuPullbackCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuPullbackCompat
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.NuPull

theorem nu_pull {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ}
    (hT : Mid.TeichmullerCongruence r N) {M M' : Model l K} (u : M.X ⟶ M'.X) (hu : u ≫ M'.p = M.p) (n j : ℕ)
    (x : B.Hc (B.schFn M'.p) (okToOC l K) true n j) :
    Mid.nu r M n j hT (B.pullHc (okToOC l K) (B.schMap u hu) true n j x) = pullM r u hu n j (Mid.nu r M' n j hT x) := by
  unfold Mid.nu pullM B.pullHc Mid.nuMor pullT' B.pullMorC
  exact (cr_square (Mid.mOut r M' n hT)
    (B.crMor (F := B.schFn M'.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (RingHom.id _) rfl (DPMorphism.id _).isDPMorphism ((B.schMap u hu).ptK _) fun _ _ _ => rfl)
    (B.crMor (F := B.schFn M'.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (RingHom.id _) rfl (DPMorphism.id _).isDPMorphism ((B.schMap u hu).ptK _) fun _ _ _ => rfl)
    (Mid.mOut r M n hT)
    (Mid.phiP_cris n N) (fun _ => rfl) (fun _ => rfl) (Mid.phiP_cris n N) (fun _ => rfl) (fun _ _ => rfl) j x).symm

end GlobalTheory.CompanionTheory.NuPull
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuPullbackCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_nu_pullback_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) {M M' : Model l K} (u : M.X ⟶ M'.X) (hu : u ≫ M'.p = M.p) (n j : ℕ) (x : B.Hc (B.schFn M'.p) (okToOC l K) true n j), Mid.nu r M n j hT (B.pullHc (okToOC l K) (B.schMap u hu) true n j x) = pullM r u hu n j (Mid.nu r M' n j hT x) := by
  first | exact @GlobalTheory.CompanionTheory.NuPull.nu_pull | exact GlobalTheory.CompanionTheory.NuPull.nu_pull | (intros; apply GlobalTheory.CompanionTheory.NuPull.nu_pull <;> assumption)
end
end
