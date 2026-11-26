module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovGlue
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitLogRepresentativeCompat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHBijOfRes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StdSomeZero

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmMapEqMOm
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace GlobalTheory.CompanionTheory.FormsGlue

section Alg

variable {K : Type} [CommRing K] {A B : Type} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

theorem omMap_eq_mOm (φ : A →ₐ[K] B) (h : SemiHom (RingHom.id K) (φ : A →+* B)) (a : ℕ) (ω : CrystallineSemistableComparison.Onto.Om K A a) :
    CrystallineSemistableComparison.Onto.omMap φ a ω = h.mOm a ω := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A B := IsScalarTower.of_algHom φ
  have hs : ∀ (c : A) (x : CrystallineSemistableComparison.Onto.Om K A a), CrystallineSemistableComparison.Onto.omMap φ a (c • x) = φ c • CrystallineSemistableComparison.Onto.omMap φ a x := by
    intro c x
    have h' := map_smul (exteriorPower.alternatingMapLinearEquiv
      { ((exteriorPower.ιMulti B a (M := Ω[B⁄K])).toMultilinearMap.restrictScalars A).compLinearMap
          fun _ => KaehlerDifferential.map K K A B with
        map_eq_zero_of_eq' := fun v i j h hij =>
          (exteriorPower.ιMulti B a (M := Ω[B⁄K])).map_eq_zero_of_eq (fun k => KaehlerDifferential.map K K A B (v k))
            (congrArg _ h) hij } : CrystallineSemistableComparison.Onto.Om K A a →ₗ[A] CrystallineSemistableComparison.Onto.Om K B a) c x
    exact h'.trans (algebraMap_smul B c _)
  have hι : ∀ g : Fin a → Ω[A⁄K], CrystallineSemistableComparison.Onto.omMap φ a (exteriorPower.ιMulti A a g) =
      h.mOm a (exteriorPower.ιMulti A a g) := by
    intro g
    have e1 : CrystallineSemistableComparison.Onto.omMap φ a (exteriorPower.ιMulti A a g) =
        exteriorPower.ιMulti B a fun k => KaehlerDifferential.map K K A B (g k) :=
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _
    rw [e1]
    refine Subtype.ext ?_
    rw [SemiHom.coe_mOm, exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
    congr 2
    funext k
    exact (congrArg ι1 (SemiHom.oneFormMap_eq_kaehlerDifferential_map h (fun _ => rfl) (g k))).symm.trans (SemiHom.mDR_ι h (g k)).symm
  have hmem : ω ∈ (⊤ : Submodule A (CrystallineSemistableComparison.Onto.Om K A a)) := Submodule.mem_top
  rw [← exteriorPower.ιMulti_span] at hmem
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact hι g
  | zero => rw [map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | smul c x _ hx => rw [hs, SemiHom.mOm_smul, hx]; rfl

end Alg

section Sch

variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

abbrev omSheaf (a : ℕ) : TopCat.Sheaf Ab X := ⟨(Omega q a).presheaf, (Omega q a).isSheaf⟩

theorem glue_core [IsAffine X] {ι : Type} (U : ι → X.Opens) (hcov : (⨆ α, U α) = ⊤) (a : ℕ) :
    (∀ ω ω' : OmU q ⊤ a, (∀ α, toOm q a (U α) (formRes q (le_top : U α ≤ ⊤) a ω) =
      toOm q a (U α) (formRes q (le_top : U α ≤ ⊤) a ω')) → ω = ω') ∧
    ∀ y : ∀ α, OmU q (U α) a,
      (∀ α β, formRes q (inf_le_left : U α ⊓ U β ≤ U α) a (y α) = formRes q (inf_le_right : U α ⊓ U β ≤ U β) a (y β)) →
      ∃ ω : OmU q ⊤ a, ∀ α, toOm q a (U α) (formRes q (le_top : U α ≤ ⊤) a ω) = toOm q a (U α) (y α) := by
  have hT : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  refine ⟨fun ω ω' h => toOm_injective hT ?_, fun y hy => ?_⟩
  · refine TopCat.Sheaf.eq_of_locally_eq' (omSheaf q a) U ⊤ (fun α => homOfLE le_top) hcov.ge _ _ fun α => ?_
    exact (res_toOm q a le_top ω).trans ((h α).trans (res_toOm q a le_top ω').symm)
  · have hc : TopCat.Presheaf.IsCompatible (omSheaf q a).1 U (fun α => toOm q a (U α) (y α)) := fun α β =>
      (res_toOm q a inf_le_left (y α)).trans ((congrArg _ (hy α β)).trans (res_toOm q a inf_le_right (y β)).symm)
    obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' (omSheaf q a) U ⊤ (fun α => homOfLE le_top) hcov.ge
      (fun α => toOm q a (U α) (y α)) hc
    obtain ⟨ω, rfl⟩ := toOm_surjective hT t
    exact ⟨ω, fun α => (res_toOm q a le_top ω).symm.trans (ht α)⟩

theorem omMap_res {V W : X.Opens} (h : W ≤ V) (φ : CrystallineSemistableComparison.Onto.Sec q V →ₐ[K] CrystallineSemistableComparison.Onto.Sec q W)
    (hφ : ∀ g, φ g = (X.presheaf.map (homOfLE h).op).hom g) (a : ℕ)
    (ω : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q V) a) : CrystallineSemistableComparison.Onto.omMap φ a ω = formRes q h a ω := by
  have e : φ = (Sec.res q h : GlobalTheory.CechDR.Sec q V →ₐ[K] GlobalTheory.CechDR.Sec q W) := AlgHom.ext hφ
  subst e
  exact omMap_eq_mOm _ (SemiHom.of_algHom (Sec.res q h)) a ω

end Sch

end GlobalTheory.CompanionTheory.FormsGlue

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace GlobalTheory.CompanionTheory.FormsGlue

theorem forms_glue : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] {ι : Type}
    (U : ι → X.Opens), (∀ α, IsAffineOpen (U α)) → (⨆ α, U α) = ⊤ →
    ∀ (φ : ∀ α, CrystallineSemistableComparison.Onto.Sec q ⊤ →ₐ[K] CrystallineSemistableComparison.Onto.Sec q (U α))
      (ψ₁ : ∀ α β, CrystallineSemistableComparison.Onto.Sec q (U α) →ₐ[K] CrystallineSemistableComparison.Onto.Sec q (U α ⊓ U β))
      (ψ₂ : ∀ α β, CrystallineSemistableComparison.Onto.Sec q (U β) →ₐ[K] CrystallineSemistableComparison.Onto.Sec q (U α ⊓ U β)),
    (∀ α g, φ α g = (X.presheaf.map (homOfLE (le_top : U α ≤ ⊤)).op).hom g) →
    (∀ α β g, ψ₁ α β g = (X.presheaf.map (homOfLE (inf_le_left : U α ⊓ U β ≤ U α)).op).hom g) →
    (∀ α β g, ψ₂ α β g = (X.presheaf.map (homOfLE (inf_le_right : U α ⊓ U β ≤ U β)).op).hom g) → ∀ a : ℕ,
    Function.Injective (fun (ω : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a) α => CrystallineSemistableComparison.Onto.omMap (φ α) a ω) ∧
    ∀ y : ∀ α, CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q (U α)) a,
      (∀ α β, CrystallineSemistableComparison.Onto.omMap (ψ₁ α β) a (y α) = CrystallineSemistableComparison.Onto.omMap (ψ₂ α β) a (y β)) →
      ∃ ω, ∀ α, CrystallineSemistableComparison.Onto.omMap (φ α) a ω = y α := by
  intro K _ X q _ ι U hU hcov φ ψ₁ ψ₂ hφ hψ₁ hψ₂ a
  have hc := glue_core q U hcov a
  refine ⟨fun ω ω' h => hc.1 ω ω' fun α => ?_, fun y hy => ?_⟩
  · have e := congrFun h α
    simp only [] at e
    rw [omMap_res q le_top (φ α) (hφ α), omMap_res q le_top (φ α) (hφ α)] at e
    exact congrArg _ e
  · obtain ⟨ω, hω⟩ := hc.2 y fun α β => by
      have e := hy α β
      rw [omMap_res q inf_le_left (ψ₁ α β) (hψ₁ α β), omMap_res q inf_le_right (ψ₂ α β) (hψ₂ α β)] at e
      exact e
    refine ⟨ω, fun α => ?_⟩
    rw [omMap_res q le_top (φ α) (hφ α)]
    exact toOm_injective (hU α) (hω α)

end GlobalTheory.CompanionTheory.FormsGlue
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupH0NormalCoboundary
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitOfBasicOpenTop
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
noncomputable section
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.B CrystallineSemistableComparison.Pb DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.KMVan

section Sc

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']

structure Sc (Φ : PDF R C) (Λ : Type) [CommRing Λ] where
  ρ : ∀ T : C, Λ →+* Φ.A.obj T
  nat : ∀ {T T' : C} (φ : T ⟶ T') (a : Λ), (Φ.A.map φ).hom (ρ T a) = ρ T' a

variable {Φ : PDF R C} {Λ : Type} [CommRing Λ]

end Sc

end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section Loc
open TensorProduct
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Λ : Type} [CommRing Λ]

end Loc
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
open TensorProduct

end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
open TensorProduct
section D
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Λ : Type} [CommRing Λ]

end D
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
open TensorProduct
section LT
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Λ : Type} [CommRing Λ]

end LT
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section FV
variable {R : Type} [CommRing R]

end FV
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section PS
open CrystallineSemistableComparison.Pb.Site GlobalTheory.PDA GlobalTheory.CompanionTheory.ChartLocBc
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

end PS

section Res
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

end Res

section Fr
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ}

end Fr
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section CL
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V V' : X.Opens} {d : ℕ}

end CL
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section TAU
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem inU_top (T : Thick (nlFun γ p X q κ)) : InU (⊤ : X.Opens) T := fun _ _ => trivial

def evT (T : Thick (nlFun γ p X q κ)) : Γ(X, ⊤) →+* T.B ⧸ T.J := ev T (inU_top T)

theorem evT_nat {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (f : Γ(X, ⊤)) :
    evT T' f = Ideal.quotientMap T'.J φ.φ φ.hle (evT T f) := by
  have key : ∀ (y : Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ X)
      (hy : y = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T)
      (hh : ⊤ ≤ y ⁻¹ᵁ ⊤), GlobalTheory.Cris.evalAt y ⊤ hh f = Ideal.quotientMap T'.J φ.φ φ.hle (evT T f) := by
    intro y hy hh
    subst hy
    exact evalAt_map (B := CommRingCat.of (T.B ⧸ T.J)) (B' := CommRingCat.of (T'.B ⧸ T'.J)) _ (pt T) (inU_top T) hh f
  exact key _ (pt_hom φ) (inU_top T')

end TAU
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section TAU2
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

end TAU2
end GlobalTheory.CompanionTheory.KMVan
end
end

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

noncomputable section

namespace GlobalTheory.CompanionTheory.OmCls

open CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)
open GlobalTheory.CompanionTheory.CupRep GlobalTheory.CompanionTheory.RepLifts GlobalTheory.CompanionTheory.ConeLocal

section Abs
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}

def vx {n : ℕ} (s : ComposableArrows C n) (w : ∀ T : C, Φ.A.obj T) (i : Fin (n + 1)) : Φ.A.obj (s.obj (Fin.last n)) :=
  (Φ.A.map (s.map (homOfLE (Fin.le_last i)))).hom (w (s.obj i))

theorem vx_res {p n : ℕ} (s : ComposableArrows C n) (w : ∀ T : C, Φ.A.obj T) (g : Fin (p + 1) → Fin (n + 1))
    (hg : Monotone g) (i : Fin (p + 1)) :
    (Φ.A.map (s.map (homOfLE (Fin.le_last (g (Fin.last p)))))).hom (vx (hg.functor ⋙ s) w i) = vx s w (g i) := by
  have e : (hg.functor ⋙ s).map (homOfLE (Fin.le_last i)) ≫ s.map (homOfLE (Fin.le_last (g (Fin.last p)))) =
      s.map (homOfLE (Fin.le_last (g i))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  unfold vx
  change (Φ.A.map ((hg.functor ⋙ s).map (homOfLE (Fin.le_last i))) ≫
    Φ.A.map (s.map (homOfLE (Fin.le_last (g (Fin.last p)))))).hom (w (s.obj (g i))) = _
  rw [← Φ.A.map_comp, e]
  rfl

theorem map_idem {n : ℕ} (s : ComposableArrows C n) (i : Fin (n + 1)) (h : i ⟶ i) (x : Φ.A.obj (s.obj i)) :
    (Φ.A.map (s.map h)).hom x = x := by
  rw [Subsingleton.elim h (𝟙 _), s.map_id, Φ.A.map_id]
  rfl

theorem vx_last {n : ℕ} (s : ComposableArrows C n) (w : ∀ T : C, Φ.A.obj T) :
    vx s w (Fin.last n) = w (s.obj (Fin.last n)) :=
  map_idem s _ _ _

theorem cech_d_h0_vertex_diff (w : ∀ T : C, Φ.A.obj T) (t : ComposableArrows C 1) :
    vl (CH.d (CH.modF Φ.A) 0 (h0 w)) t = vx t w (Fin.last 1) - vx t w 0 := by
  rw [cech_d_h0_eval, vx_last]
  rfl

theorem cupList_val : ∀ {a : ℕ} (u : Fin a → ∀ T : C, Φ.A.obj T) (s : ComposableArrows C a),
    vl (cupListC Φ.A fun k => CH.d (CH.modF Φ.A) 0 (h0 (u k))) s =
      ∏ k : Fin a, (vx s (u k) k.succ - vx s (u k) k.castSucc)
  | 0, _, _ => by simp; rfl
  | a + 1, u, s => by
    have ih := cupList_val (fun i : Fin a => u i.castSucc)
      ((CH.front_mono (rfl : a + 1 = a + 1)).functor ⋙ s)
    have h1 : (show Φ.A.obj (s.obj (Fin.last (a + 1))) from CH.term (CH.modF Φ.A) s
        (cupListC Φ.A fun k : Fin a => CH.d (CH.modF Φ.A) 0 (h0 (u k.castSucc)))
        (CH.front (rfl : a + 1 = a + 1)) (CH.front_mono _)) =
        ∏ k : Fin a, (vx s (u k.castSucc) k.castSucc.succ - vx s (u k.castSucc) k.castSucc.castSucc) := by
      change (Φ.A.map (s.map (homOfLE (Fin.le_last (CH.front (rfl : a + 1 = a + 1) (Fin.last a)))))).hom
        (vl (cupListC Φ.A fun k : Fin a => CH.d (CH.modF Φ.A) 0 (h0 (u k.castSucc)))
          ((CH.front_mono (rfl : a + 1 = a + 1)).functor ⋙ s)) = _
      rw [ih, map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [map_sub, vx_res, vx_res]
      rfl
    have h2 : (show Φ.A.obj (s.obj (Fin.last (a + 1))) from CH.term (CH.modF Φ.A) s
        (CH.d (CH.modF Φ.A) 0 (h0 (u (Fin.last a))))
        (CH.back (rfl : a + 1 = a + 1)) (CH.back_mono _)) =
        vx s (u (Fin.last a)) (Fin.last a).succ - vx s (u (Fin.last a)) (Fin.last a).castSucc := by
      change (Φ.A.map (s.map (homOfLE (Fin.le_last (CH.back (rfl : a + 1 = a + 1) (Fin.last 1)))))).hom
        (vl (CH.d (CH.modF Φ.A) 0 (h0 (u (Fin.last a))))
          ((CH.back_mono (rfl : a + 1 = a + 1)).functor ⋙ s)) = _
      rw [cech_d_h0_vertex_diff, map_sub, vx_res, vx_res]
      rfl
    rw [Fin.prod_univ_castSucc, ← h1, ← h2]
    rfl

def fm {a : ℕ} (u₀ : ∀ T : C, Φ.A.obj T) (u : Fin a → ∀ T : C, Φ.A.obj T) : CH.Cn (CH.modF Φ.A) a :=
  (CH.mulP Φ.A).cupC (add_zero a) (cupListC Φ.A fun k => CH.d (CH.modF Φ.A) 0 (h0 (u k))) (h0 u₀)

theorem cup_h0_eval {a : ℕ} (P : CH.Cn (CH.modF Φ.A) a) (w : ∀ T : C, Φ.A.obj T) (s : ComposableArrows C a) :
    vl ((CH.mulP Φ.A).cupC (add_zero a) P (h0 w)) s = vl P s * w (s.obj (Fin.last a)) := by
  have h1 : (show Φ.A.obj (s.obj (Fin.last a)) from CH.term (CH.modF Φ.A) s P
      (CH.front (add_zero a)) (CH.front_mono _)) = vl P s :=
    map_idem (Φ := Φ) s (Fin.last a) _ _
  have h2 : (show Φ.A.obj (s.obj (Fin.last a)) from CH.term (CH.modF Φ.A) s (h0 w)
      (CH.back (add_zero a)) (CH.back_mono _)) = w (s.obj (Fin.last a)) :=
    map_idem (Φ := Φ) s (Fin.last a) _ _
  rw [← h1, ← h2]
  rfl

theorem fm_val {a : ℕ} (u₀ : ∀ T : C, Φ.A.obj T) (u : Fin a → ∀ T : C, Φ.A.obj T) (s : ComposableArrows C a) :
    vl (fm u₀ u) s = (∏ k : Fin a, (vx s (u k) k.succ - vx s (u k) k.castSucc)) * u₀ (s.obj (Fin.last a)) := by
  unfold fm
  rw [cup_h0_eval, cupList_val]

end Abs

section Cls
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}

def Nr (Fil : ℤ → IdF Φ.A) (w : ∀ T : C, Φ.A.obj T) : Prop :=
  ∀ (T T' : C) (f : T ⟶ T'), w T' - (Φ.A.map f).hom (w T) ∈ (Fil ((1 : ℕ) : ℤ)).S T'

theorem d_h0_mem_filtration_one {w : ∀ T : C, Φ.A.obj T} (hw : Nr Fil w) :
    CH.d (CH.modF Φ.A) 0 (h0 w) ∈ FC (Fil ((1 : ℕ) : ℤ)) 1 :=
  mem_FC.2 fun t => by
    rw [cech_d_h0_eval]
    exact hw _ _ _

theorem h0_mem_filtration_zero (hF : IsFil Φ Fil) (w : ∀ T : C, Φ.A.obj T) : h0 w ∈ FC (Fil ((0 : ℕ) : ℤ)) 0 :=
  mem_FC.2 fun t => by
    have e : (Fil ((0 : ℕ) : ℤ)).S (t.obj (Fin.last 0)) = ⊤ := hF.top _ (by simp) _
    rw [e]
    trivial

theorem fm_mem (hF : IsFil Φ Fil) {a : ℕ} (u₀ : ∀ T : C, Φ.A.obj T) {u : Fin a → ∀ T : C, Φ.A.obj T}
    (hu : ∀ k, Nr Fil (u k)) : fm u₀ u ∈ FC (Fil (a : ℤ)) a :=
  cup_mem hF (add_zero a) (r := a) (r' := 0) (cupList_mem hF _ fun k => d_h0_mem_filtration_one (hu k)) (h0_mem_filtration_zero hF u₀)

theorem d_fm_mem (hF : IsFil Φ Fil) {a : ℕ} {u₀ : ∀ T : C, Φ.A.obj T} {u : Fin a → ∀ T : C, Φ.A.obj T}
    (h₀ : Nr Fil u₀) (hu : ∀ k, Nr Fil (u k)) :
    CH.d (CH.modF Φ.A) a (fm u₀ u) ∈ FC (Fil ((a + 1 : ℕ) : ℤ)) (a + 1) := by
  unfold fm
  rw [CrystallineSemistableComparison.P.leibniz, d_cupList Φ.A _ fun k => CH.d_d _ 0 _]
  simp only [map_zero, LinearMap.zero_apply, zero_add]
  exact zsmul_mem (cup_mem hF _ (r := a) (r' := 1) (cupList_mem hF _ fun k => d_h0_mem_filtration_one (hu k)) (d_h0_mem_filtration_one h₀)) _

theorem cup_h0_normal_coboundary (hF : IsFil Φ Fil) {m : ℕ} {g : CH.Cn (CH.modF Φ.A) m} (hg : IsBd Fil m g)
    {y : ∀ T : C, Φ.A.obj T} (hy : Nr Fil y) :
    ∃ W ∈ FC (Fil ((m + 1 : ℕ) : ℤ)) m, IsBd Fil m ((CH.mulP Φ.A).cupC (add_zero m) g (h0 y) - W) := by
  cases m with
  | zero =>
    have hg0 : g = 0 := hg
    subst hg0
    refine ⟨0, zero_mem _, ?_⟩
    change _ = _
    simp
  | succ n =>
    obtain ⟨H, hH, rfl⟩ := hg
    refine ⟨-((-1 : ℤ) ^ n • (CH.mulP Φ.A).cupC (p := n) (q := 0 + 1) (by omega) H (CH.d (CH.modF Φ.A) 0 (h0 y))),
      neg_mem (zsmul_mem (cup_mem hF _ (r := n + 1) (r' := 1) hH (d_h0_mem_filtration_one hy)) _),
      (CH.mulP Φ.A).cupC (add_zero n) H (h0 y), cup_mem hF (add_zero n) (r := n + 1) (r' := 0) hH (h0_mem_filtration_zero hF y), ?_⟩
    rw [CrystallineSemistableComparison.P.leibniz, sub_neg_eq_add]

theorem cupList_diff_local (hF : IsFil Φ Fil) : ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1)
    (α : Fin m → CH.Cn (CH.modF Φ.A) 0), (∀ k, ℓ k ∈ FC (Fil ((1 : ℕ) : ℤ)) 1) → (∀ k, CH.d _ 1 (ℓ k) = 0) →
    (∀ k, α k ∈ FC (Fil ((1 : ℕ) : ℤ)) 0) →
    IsBd Fil m (cupListC Φ.A (fun k => ℓ k + CH.d _ 0 (α k)) - cupListC Φ.A ℓ)
  | 0, _, _, _, _, _ => sub_self _
  | m + 1, ℓ, α, hℓ, hd, hα => by
    have ih := cupList_diff_local hF (fun i : Fin m => ℓ i.castSucc) (fun i => α i.castSucc) (fun i => hℓ _)
      (fun i => hd _) (fun i => hα _)
    have hl' : ℓ (Fin.last m) + CH.d _ 0 (α (Fin.last m)) ∈ FC (Fil ((1 : ℕ) : ℤ)) 1 :=
      add_mem (hℓ _) (d_mem (hα _))
    have hdl' : CH.d (CH.modF Φ.A) 1
        (ℓ (Fin.last m) + CH.d (CH.modF Φ.A) 0 (α (Fin.last m))) = 0 := by
      rw [map_add (f := _), hd, CH.d_d, add_zero]
    have h₁ := bd_cup (m := m) (Fil := Fil) hF ih hl' hdl'
    rcases h₁ with ⟨H₁, hH₁, e₁⟩
    let ℓ' : Fin m → CH.Cn (CH.modF Φ.A) 1 := fun i => ℓ i.castSucc
    have h₂ := cup_d (Φ := Φ) (Fil := Fil) (m := m) (B := cupListC Φ.A ℓ')
      (a := α (Fin.last m)) hF (cupList_mem hF ℓ' fun i => hℓ i.castSucc)
      (d_cupList Φ.A ℓ' fun i => hd i.castSucc) (hα (Fin.last m))
    rcases h₂ with ⟨H₂, hH₂, e₂⟩
    refine ⟨H₁ + H₂, add_mem hH₁ hH₂, ?_⟩
    rw [map_add (f := _), ← e₁, ← e₂]
    change (CH.mulP Φ.A).cupC rfl _ (ℓ (Fin.last m) + CH.d _ 0 (α (Fin.last m))) - (CH.mulP Φ.A).cupC rfl _ (ℓ (Fin.last m)) = _
    simp only [map_sub, map_add (f := _), LinearMap.sub_apply]
    abel


theorem fm_change (hF : IsFil Φ Fil) {a : ℕ} {u₀ u₀' : ∀ T : C, Φ.A.obj T} {u u' : Fin a → ∀ T : C, Φ.A.obj T}
    (h₀' : Nr Fil u₀') (hu : ∀ k, Nr Fil (u k))
    (hz₀ : ∀ T, u₀' T - u₀ T ∈ (Fil ((1 : ℕ) : ℤ)).S T) (hz : ∀ k T, u' k T - u k T ∈ (Fil ((1 : ℕ) : ℤ)).S T)
    {c : CH.H (sq (Fil (a : ℤ)) (Fil ((a : ℤ) + 1))) a}
    (h : CrystallineSemistableComparison.Pb.Rep (Fil (a : ℤ)) (Fil ((a : ℤ) + 1)) (fm u₀ u) c) :
    CrystallineSemistableComparison.Pb.Rep (Fil (a : ℤ)) (Fil ((a : ℤ) + 1)) (fm u₀' u') c := by
  set P := cupListC Φ.A fun k => CH.d (CH.modF Φ.A) 0 (h0 (u k)) with hP
  set P' := cupListC Φ.A fun k => CH.d (CH.modF Φ.A) 0 (h0 (u' k)) with hP'
  have hα : ∀ k, h0 (u' k) - h0 (u k) ∈ FC (Fil ((1 : ℕ) : ℤ)) 0 := fun k => mem_FC.2 fun t => hz k _
  have hbd : IsBd Fil a (P' - P) := by
    have := cupList_diff_local hF (fun k => CH.d (CH.modF Φ.A) 0 (h0 (u k))) (fun k => h0 (u' k) - h0 (u k))
      (fun k => d_h0_mem_filtration_one (hu k)) (fun k => CH.d_d _ 0 _) hα
    have e : (fun k => CH.d (CH.modF Φ.A) 0 (h0 (u k)) + CH.d (CH.modF Φ.A) 0 (h0 (u' k) - h0 (u k))) =
        fun k => CH.d (CH.modF Φ.A) 0 (h0 (u' k)) := by
      funext k
      rw [map_sub]
      abel
    rw [e] at this
    exact this
  obtain ⟨W, hW, hD⟩ := cup_h0_normal_coboundary hF hbd h₀'
  set D := (CH.mulP Φ.A).cupC (add_zero a) (P' - P) (h0 u₀') with hDdef
  set V := (CH.mulP Φ.A).cupC (add_zero a) P (h0 u₀' - h0 u₀) with hV
  have hVm : V ∈ FC (Fil ((a + 1 : ℕ) : ℤ)) a :=
    cup_mem hF (add_zero a) (r := a) (r' := 1)
      (cupList_mem hF _ fun k => d_h0_mem_filtration_one (hu k)) (mem_FC.2 fun t => hz₀ _)
  have e : fm u₀' u' = fm u₀ u + D + V := by
    change (CH.mulP Φ.A).cupC (add_zero a) P' (h0 u₀') = (CH.mulP Φ.A).cupC (add_zero a) P (h0 u₀) + D + V
    simp only [hDdef, hV, map_sub, LinearMap.sub_apply]
    abel
  have h1 : CrystallineSemistableComparison.Pb.Rep (Fil (a : ℤ)) (Fil ((a : ℤ) + 1)) (fm u₀ u + (D - W)) c :=
    rep_of_bd (z := fm u₀ u) (by rwa [add_sub_cancel_left]) h
  refine rep_congr h1 fun s => ?_
  have e2 : (fm u₀ u + (D - W)) - fm u₀' u' = -(W + V) := by
    rw [e]
    abel
  have h3 : -(W + V) ∈ FC (Fil ((a + 1 : ℕ) : ℤ)) a := neg_mem (add_mem hW hVm)
  have h4 := mem_FC.1 h3 s
  rw [← e2] at h4
  exact h4

theorem fm_exists (hF : IsFil Φ Fil) {a : ℕ} {u₀ : ∀ T : C, Φ.A.obj T} {u : Fin a → ∀ T : C, Φ.A.obj T}
    (h₀ : Nr Fil u₀) (hu : ∀ k, Nr Fil (u k)) :
    ∃ c : CH.H (sq (Fil (a : ℤ)) (Fil ((a : ℤ) + 1))) a, CrystallineSemistableComparison.Pb.Rep (Fil (a : ℤ)) (Fil ((a : ℤ) + 1)) (fm u₀ u) c :=
  rep_exists (fm u₀ u) (fun s => mem_FC.1 (fm_mem hF u₀ hu) s) (fun s => by
    have h := mem_FC.1 (d_fm_mem hF h₀ hu) s
    rw [Nat.cast_succ] at h
    exact h)

end Cls

section Conc
open CrystallineSemistableComparison.HT CrystallineSemistableComparison.Om.L2

theorem isFil_thFil {b : Base} (L : b.Fun) : IsFil (thP L) (thFil L) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr T
    change T.pdPow r.toNat = ⊤
    rw [Int.toNat_of_nonpos hr]
    exact T.pdPow_zero
  · intro T
    change T.pdPow (1 : ℤ).toNat = T.J
    exact le_antisymm (GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_one_le T.δ) T.J_le_pdPow_one
  · intro r r' h T
    exact T.pdPow_anti (Int.toNat_le_toNat h)
  · intro r r' T x y hx hy
    have hx' : (show T.B from x) ∈ pdP T.δ r := by
      have : (show T.B from x) ∈ T.pdPow ((r : ℤ).toNat) := hx
      rw [Int.toNat_natCast] at this
      exact this
    have hy' : (show T.B from y) ∈ pdP T.δ r' := by
      have : (show T.B from y) ∈ T.pdPow ((r' : ℤ).toNat) := hy
      rw [Int.toNat_natCast] at this
      exact this
    have h := GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.δ r r' (Ideal.mul_mem_mul hx' hy')
    change _ ∈ T.pdPow (((r + r' : ℕ) : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact h
  · intro k T x hx
    change _ ∈ T.pdPow ((k : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact GlobalTheory.CompanionTheory.DPFil.dpow_mem_pdP T.δ k hx

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem fil_one (T : Thick (smFun X q)) : (thFil (smFun X q) ((1 : ℕ) : ℤ)).S T = T.J :=
  (isFil_thFil (smFun X q)).one T

theorem lifts_nr (Λ : LiftsT q) (x : Γ(X, ⊤)) : Nr (Φ := thP (smFun X q)) (thFil (smFun X q)) fun T => Λ.v T x := by
  intro T T' f
  rw [fil_one]
  have h : Ideal.Quotient.mk T'.J (Λ.v T' x) = Ideal.Quotient.mk T'.J (f.φ (Λ.v T x)) := by
    rw [Λ.hv T' x]
    refine (GlobalTheory.CompanionTheory.KMVan.evT_nat f x).trans ?_
    change Ideal.quotientMap T'.J f.φ f.hle (ev T (inTop q T) x) = _
    rw [← Λ.hv T x]
    rfl
  exact Ideal.Quotient.eq.1 h

theorem lifts_sub (Λ Λ' : LiftsT q) (x : Γ(X, ⊤)) (T : Thick (smFun X q)) :
    Λ'.v T x - Λ.v T x ∈ (thFil (smFun X q) ((1 : ℕ) : ℤ)).S T := by
  rw [fil_one]
  exact Ideal.Quotient.eq.1 ((Λ'.hv T x).trans (Λ.hv T x).symm)


variable (q) in
def liftsTopBot : LiftsT q where
  v T g := Function.surjInv Ideal.Quotient.mk_surjective
    (ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T (inTop q T) g)
  hv T g := Function.surjInv_eq _ _

theorem form_eq (Λ : LiftsT q) {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) :
    Λ.form g₀ g = fm (Φ := thP (smFun X q)) (fun T => Λ.v T g₀) fun k T => Λ.v T (g k) := by
  funext s
  refine Eq.trans ?_ (fm_val (Φ := thP (smFun X q)) (fun T => Λ.v T g₀) (fun k T => Λ.v T (g k)) s).symm
  exact mul_comm _ _

end Conc


open CrystallineSemistableComparison.HT CrystallineSemistableComparison.Om.L2 in
theorem main : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)),
    ∃ c : CrystallineSemistableComparison.HT.Hdg q a a, CrystallineSemistableComparison.Om.L2.IsFormT q g₀ g c := by
  intro K _ X q a g₀ g
  have hF := isFil_thFil (smFun X q)
  obtain ⟨c, hc⟩ := fm_exists (Φ := thP (smFun X q)) hF (u₀ := fun T => (liftsTopBot q).v T g₀)
    (u := fun k T => (liftsTopBot q).v T (g k)) (lifts_nr _ _) fun k => lifts_nr _ _
  refine ⟨c, fun Λ => ?_⟩
  rw [form_eq]
  exact fm_change hF (lifts_nr Λ g₀) (fun k => lifts_nr _ _) (lifts_sub _ _ _) (fun k => lifts_sub _ _ _) hc

end GlobalTheory.CompanionTheory.OmCls
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineSmoothFormsBijective
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.OmGlue

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT

variable {K : Type} [CommRing K] {Z : Scheme.{0}}

theorem inU_mono (q : Z ⟶ Spec (CommRingCat.of K)) {V V' : Z.Opens} (k : V' ≤ V) : inU q V' ≤ inU q V :=
  fun T hT x hx => k (hT hx)

theorem ev_res (q : Z ⟶ Spec (CommRingCat.of K)) {V V' : Z.Opens} (k : V' ≤ V) (T : Thick (smFun Z q))
    (h : inU q V' T) (h' : inU q V T) (g : Γ(Z, V)) :
    ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T h ((Z.presheaf.map (homOfLE k).op).hom g) =
      ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T h' g := by
  simp only [ev, GlobalTheory.Cris.evalAt, RingHom.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem lifts_nonempty (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens) : Nonempty (Lifts q V) :=
  ⟨⟨fun T g => (Ideal.Quotient.mk_surjective
      (ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T.obj T.property g)).choose,
    fun T g => (Ideal.Quotient.mk_surjective
      (ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T.obj T.property g)).choose_spec⟩⟩

theorem rep_unique {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) {j : ℕ}
    {z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c c' : CH.H (sq a b) j}
    (h : Rep a b z c) (h' : Rep a b z c') : c = c' := by
  obtain ⟨f, hf, rfl, hz⟩ := h
  obtain ⟨f', hf', rfl, hz'⟩ := h'
  have e : f = f' := funext fun s => Subtype.ext ((hz s).trans (hz' s).symm)
  subst e
  rfl

theorem isForm_unique (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens) {a : ℕ} {g₀ : Sec q V} {g : Fin a → Sec q V}
    {c c' : HV q V a a} (h : IsForm q V g₀ g c) (h' : IsForm q V g₀ g c') : c = c' := by
  obtain ⟨Λ⟩ := lifts_nonempty q V
  exact rep_unique (A := (inU q V).ι ⋙ thA (smFun Z q)) ((thFil (smFun Z q) (a : ℤ)).res (inU q V).ι)
    ((thFil (smFun Z q) ((a : ℤ) + 1)).res (inU q V).ι) (h Λ) (h' Λ)

theorem isForm_res (q : Z ⟶ Spec (CommRingCat.of K)) {V V' : Z.Opens} (k : V' ≤ V) (φ : Sec q V →ₐ[K] Sec q V')
    (hφ : ∀ g, φ g = (Z.presheaf.map (homOfLE k).op).hom g) {a : ℕ} {g₀ : Sec q V} {g : Fin a → Sec q V}
    {c : HV q V a a} (hc : IsForm q V g₀ g c) :
    IsForm q V' (φ g₀) (fun j => φ (g j)) ((resU (G q a) (inU_mono q k)).pull a c) := by
  classical
  intro Λ'
  obtain ⟨Λ₀⟩ := lifts_nonempty q V
  let Λ : Lifts q V :=
    { v := fun T g => if h : inU q V' T.obj then Λ'.v ⟨T.obj, h⟩ (φ g) else Λ₀.v T g
      hv := fun T g => by
        by_cases h : inU q V' T.obj
        · simp only [dif_pos h]
          refine (Λ'.hv ⟨T.obj, h⟩ (φ g)).trans ?_
          rw [hφ]
          exact ev_res q k T.obj h T.property g
        · simp only [dif_neg h]
          exact Λ₀.hv T g }
  have hv : ∀ (T : (inU q V').FullSubcategory) (g : Sec q V),
      Λ.v ((ObjectProperty.ιOfLE (inU_mono q k)).obj T) g = Λ'.v T (φ g) := fun T g => dif_pos T.property
  have hz := GlobalTheory.CompanionTheory.ConeRep.rep_resB (thA (smFun Z q)) (thFil (smFun Z q) (a : ℤ)) (thFil (smFun Z q) ((a : ℤ) + 1))
    (inU_mono q k) (Λ.form g₀ g) c (hc Λ)
  have e : Λ'.form (φ g₀) (fun j => φ (g j)) = resB (thA (smFun Z q)) (inU_mono q k) (Λ.form g₀ g) := by
    funext s
    simp only [Lifts.form, resB]
    refine congrArg₂ (· * ·) (hv _ _).symm (Finset.prod_congr rfl fun k' _ => ?_)
    exact congrArg₂ (· - ·) (congrArg _ (hv _ _).symm) (congrArg _ (hv _ _).symm)
  exact e ▸ hz

theorem fs_hom_heq {C : Type 1} [Category.{0} C] {P : ObjectProperty C} {S₁ S₂ S₁' S₂' : P.FullSubcategory}
    (h : S₁ = S₂) (h' : S₁' = S₂') (f : S₁ ⟶ S₁') (g : S₂ ⟶ S₂') (hh : HEq f.hom g.hom) : HEq f g := by
  subst h h'
  exact heq_of_eq (ObjectProperty.hom_ext _ (eq_of_heq hh))

theorem morV_G (q : Z ⟶ Spec (CommRingCat.of K)) {P P' : ObjectProperty (Thick (smFun Z q))} (k : P' ≤ P) (a : ℕ)
    (h : ∀ T, P' T → P ((smS (𝟙 Z) (Category.id_comp q)).G.obj T)) :
    (morV (𝟙 Z) (Category.id_comp q) a h).G = (resU (G q a) k).G := by
  refine Functor.hext (fun T => ?_) (fun T T' f => ?_)
  · exact ObjectProperty.FullSubcategory.ext (GlobalTheory.CompanionTheory.HodgePull.obj_id T.obj)
  · refine fs_hom_heq (ObjectProperty.FullSubcategory.ext (GlobalTheory.CompanionTheory.HodgePull.obj_id T.obj))
      (ObjectProperty.FullSubcategory.ext (GlobalTheory.CompanionTheory.HodgePull.obj_id T'.obj)) _ _ ?_
    exact GlobalTheory.CompanionTheory.HodgePull.hom_heq (GlobalTheory.CompanionTheory.HodgePull.obj_id T.obj) (GlobalTheory.CompanionTheory.HodgePull.obj_id T'.obj) _ _ HEq.rfl

theorem morV_pullC (q : Z ⟶ Spec (CommRingCat.of K)) {P P' : ObjectProperty (Thick (smFun Z q))} (k : P' ≤ P) (a n : ℕ)
    (h : ∀ T, P' T → P ((smS (𝟙 Z) (Category.id_comp q)).G.obj T)) (z : CH.Cn (P.ι ⋙ G q a) n) :
    (morV (𝟙 Z) (Category.id_comp q) a h).pullC n z = (resU (G q a) k).pullC n z := by
  funext s
  have hs : s ⋙ (morV (𝟙 Z) (Category.id_comp q) a h).G = s ⋙ (resU (G q a) k).G := by
    rw [morV_G q k a h]
  exact (GlobalTheory.CompanionTheory.HodgePull.τ_id a _ _).trans (eq_of_heq (congr_arg_heq z hs))

theorem morV_pull (q : Z ⟶ Spec (CommRingCat.of K)) {P P' : ObjectProperty (Thick (smFun Z q))} (k : P' ≤ P) (a n : ℕ)
    (h : ∀ T, P' T → P ((smS (𝟙 Z) (Category.id_comp q)).G.obj T)) (x : HU (G q a) P n) :
    (morV (𝟙 Z) (Category.id_comp q) a h).pull n x = (resU (G q a) k).pull n x := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg (Submodule.Quotient.mk (p := _)) (Subtype.ext (morV_pullC q k a n h z))

theorem isForm_top (q : Z ⟶ Spec (CommRingCat.of K)) {a : ℕ} (g₀ : Γ(Z, ⊤)) (g : Fin a → Γ(Z, ⊤)) (c : Hdg q a a)
    (hc : Om.L2.IsFormT q g₀ g c) :
    IsForm q ⊤ (a := a) g₀ g ((CH.Mor.restrict (G q a) (inU q ⊤).ι).pull a c) := by
  intro Λ
  let Λ' : Om.L2.LiftsT q := ⟨fun T g => Λ.v ⟨T, Om.L2.inTop q T⟩ g, fun T g => Λ.hv ⟨T, Om.L2.inTop q T⟩ g⟩
  obtain ⟨f, hf, hcf, hz⟩ := hc Λ'
  have hf' : CH.d (G q a) a f = 0 := hf
  have hb : CH.d ((inU q ⊤).ι ⋙ G q a) a ((CH.Mor.restrict (G q a) (inU q ⊤).ι).pullC a f) = 0 := by
    rw [(CH.Mor.restrict (G q a) (inU q ⊤).ι).d_pullC, hf', map_zero]
  have hcl : (CH.Mor.restrict (G q a) (inU q ⊤).ι).pull a c =
      (CH.cx ((inU q ⊤).ι ⋙ G q a)).cls ((CH.Mor.restrict (G q a) (inU q ⊤).ι).pullC a f) hb := by
    have hc' : c = (CH.cx (G q a)).cls f hf' := hcf
    rw [hc']
    rfl
  exact ⟨(CH.Mor.restrict (G q a) (inU q ⊤).ι).pullC a f, hb, hcl, fun s => hz (s ⋙ (inU q ⊤).ι)⟩

theorem omMap_cross {K A B₁ B₂ C : Type} [CommRing K] [CommRing A] [CommRing B₁] [CommRing B₂] [CommRing C] [Algebra K A]
    [Algebra K B₁] [Algebra K B₂] [Algebra K C] (φ₁ : A →ₐ[K] B₁) (φ₂ : A →ₐ[K] B₂) (ψ₁ : B₁ →ₐ[K] C) (ψ₂ : B₂ →ₐ[K] C)
    (h : ∀ g, ψ₁ (φ₁ g) = ψ₂ (φ₂ g)) (a : ℕ) (ω : Om K A a) :
    omMap ψ₁ a (omMap φ₁ a ω) = omMap ψ₂ a (omMap φ₂ a ω) := by
  have hs := (GlobalTheory.CompanionTheory.OntoForms.formLaws K A A a).1
  have e : (omMap ψ₁ a).comp (omMap φ₁ a) = (omMap ψ₂ a).comp (omMap φ₂ a) := by
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨g₀, g, rfl⟩
    simp only [LinearMap.comp_apply]
    rw [((GlobalTheory.CompanionTheory.OntoForms.formLaws K A B₁ a).2 φ₁).1, ((GlobalTheory.CompanionTheory.OntoForms.formLaws K A B₂ a).2 φ₂).1,
      ((GlobalTheory.CompanionTheory.OntoForms.formLaws K B₁ C a).2 ψ₁).1, ((GlobalTheory.CompanionTheory.OntoForms.formLaws K B₂ C a).2 ψ₂).1]
    simp only [h]
  exact LinearMap.congr_fun e ω

theorem res_key (hN : OmNat) (K : Type) [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a : ℕ)
    {V V' : X.Opens} (k : V' ≤ V) :
    ∃ φ : Sec q V →ₐ[K] Sec q V', (∀ g, φ g = (X.presheaf.map (homOfLE k).op).hom g) ∧
      ∀ e e', IsOm q V a e → IsOm q V' a e' → ∀ ω,
        (resU (G q a) (inU_mono q k)).pull a (e ω) = e' (omMap φ a ω) := by
  have h : ∀ T, inU q V' T → inU q V ((smS (𝟙 X) (Category.id_comp q)).G.obj T) := fun T hT => by
    have e : (smS (𝟙 X) (Category.id_comp q)).G.obj T = T := GlobalTheory.CompanionTheory.HodgePull.obj_id T
    rw [e]
    exact inU_mono q k T hT
  obtain ⟨φ, h1, h2⟩ := hN K X X q q (𝟙 X) (Category.id_comp q) V V' k h
  refine ⟨φ, fun g => ?_, fun e e' he he' ω => ?_⟩
  · rw [h1]
    simp [Scheme.Hom.appLE]
  · rw [← morV_pull q (inU_mono q k) a a h]
    exact h2 a e e' he he' ω

theorem om_top : AffOm → OmNat → ∀ (K : Type) [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [IsAffine X] [Smooth q] (a : ℕ),
    ∃ e : Om K (Sec q ⊤) a →ₗ[K] HV q ⊤ a a, IsOm q ⊤ a e ∧ Function.Bijective e := by
  intro hA hN K _ _ X q _ _ a
  classical
  obtain ⟨U⟩ := (Pb.cov_ex q).1 inferInstance
  have hAff2 : ∀ α β, IsAffineOpen (U.U α ⊓ U.U β) := fun α β => by
    have h := U.inter {α, β} ⟨α, by simp⟩
    rwa [Finset.iInf_insert, Finset.iInf_singleton] at h
  have hc1 : ∀ α, Nonempty (Coord q (U.U α) (U.d α)) := fun α => ⟨U.c α⟩
  have hc2 : ∀ α β, Nonempty (Coord q (U.U α ⊓ U.U β) (U.d α)) := fun α β =>
    ⟨(Pb.coord_res (U.c α) inf_le_left (hAff2 α β)).choose⟩
  have van : ∀ S : Finset U.ι, S.Nonempty → ∀ j < a, Subsingleton (HV q (⨅ α ∈ S, U.U α) a j) := by
    rintro S hS j hj
    obtain ⟨α₀, h₀⟩ := id hS
    exact (hA K X q _ (U.d α₀) ⟨(Pb.coord_res (U.c α₀) (iInf₂_le α₀ h₀) (U.inter S hS)).choose⟩ a).1 j (by omega)
  choose E hE hEb using fun α => (hA K X q _ _ (hc1 α) a).2
  choose E₂ hE₂ hE₂b using fun α β => (hA K X q _ _ (hc2 α β) a).2
  choose φ hφ hφn using fun α => res_key hN K q a (le_top : U.U α ≤ ⊤)
  choose ψ₁ hψ₁ hψ₁n using fun α β => res_key hN K q a (inf_le_left : U.U α ⊓ U.U β ≤ U.U α)
  choose ψ₂ hψ₂ hψ₂n using fun α β => res_key hN K q a (inf_le_right : U.U α ⊓ U.U β ≤ U.U β)
  have hk : ∀ α, inU q (U.U α) ≤ inU q ⊤ := fun α => inU_mono q le_top
  have hk₁ : ∀ α β, inU q (U.U α ⊓ U.U β) ≤ inU q (U.U α) := fun α β => inU_mono q inf_le_left
  have hk₂ : ∀ α β, inU q (U.U α ⊓ U.U β) ≤ inU q (U.U β) := fun α β => inU_mono q inf_le_right
  obtain ⟨hinj, hglue⟩ := GlobalTheory.CompanionTheory.CechDeg.om_cech q U.U U.cover a van hk hk₁ hk₂
  obtain ⟨finj, fglue⟩ := GlobalTheory.CompanionTheory.FormsGlue.forms_glue q U.U (fun α => (U.c α).affine) U.cover φ ψ₁ ψ₂ hφ hψ₁ hψ₂ a
  let R : HV q ⊤ a a →ₗ[K] ∀ α, HV q (U.U α) a a := LinearMap.pi fun α => (resU (G q a) (hk α)).pull a
  let Eo : Om K (Sec q ⊤) a →ₗ[K] ∀ α, HV q (U.U α) a a := LinearMap.pi fun α => (E α).comp (omMap (φ α) a)
  have hRinj : Function.Injective R := hinj
  have hcompat : ∀ ω α β, (resU (G q a) (hk₁ α β)).pull a (Eo ω α) = (resU (G q a) (hk₂ α β)).pull a (Eo ω β) := by
    intro ω α β
    have e₁ := hψ₁n α β _ _ (hE α) (hE₂ α β) (omMap (φ α) a ω)
    have e₂ := hψ₂n α β _ _ (hE β) (hE₂ α β) (omMap (φ β) a ω)
    refine e₁.trans (Eq.trans ?_ e₂.symm)
    refine congrArg _ (omMap_cross _ _ _ _ (fun g => ?_) a ω)
    rw [hψ₁, hψ₂, hφ, hφ]
    change ((X.presheaf.map (homOfLE le_top).op ≫ X.presheaf.map (homOfLE inf_le_left).op).hom g) =
      ((X.presheaf.map (homOfLE le_top).op ≫ X.presheaf.map (homOfLE inf_le_right).op).hom g)
    rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    rfl
  have hmem : ∀ ω, Eo ω ∈ LinearMap.range R := fun ω => by
    obtain ⟨x, hx⟩ := hglue (Eo ω) (hcompat ω)
    exact ⟨x, funext hx⟩
  let e : Om K (Sec q ⊤) a →ₗ[K] HV q ⊤ a a :=
    ((LinearEquiv.ofInjective R hRinj).symm : LinearMap.range R →ₗ[K] HV q ⊤ a a).comp (Eo.codRestrict _ hmem)
  have hRe : ∀ ω, R (e ω) = Eo ω := fun ω =>
    congrArg Subtype.val ((LinearEquiv.ofInjective R hRinj).apply_symm_apply (Eo.codRestrict _ hmem ω))
  refine ⟨e, fun g₀ g => ?_, fun ω ω' h => ?_, fun x => ?_⟩
  · obtain ⟨c, hc⟩ := GlobalTheory.CompanionTheory.OmCls.main q (a := a) g₀ g
    have hc' := isForm_top q g₀ g c hc
    have key : e (form K g₀ g) = (CH.Mor.restrict (G q a) (inU q ⊤).ι).pull a c := by
      refine hRinj (funext fun α => ?_)
      rw [hRe]
      have h1 := isForm_res q le_top (φ α) (hφ α) hc'
      have h2 := hE α (φ α g₀) fun j => φ α (g j)
      refine Eq.trans ?_ (isForm_unique q _ h2 h1)
      exact congrArg (E α) (((GlobalTheory.CompanionTheory.OntoForms.formLaws K _ _ a).2 (φ α)).1 g₀ g)
    rw [key]
    exact hc'
  · refine finj (funext fun α => (hEb α).1 ?_)
    have := congrFun ((hRe ω).symm.trans ((congrArg R h).trans (hRe ω'))) α
    exact this
  · choose y hy using fun α => (hEb α).2 (R x α)
    obtain ⟨ω, hω⟩ := fglue y fun α β => (hE₂b α β).1 (by
      rw [← hψ₁n α β _ _ (hE α) (hE₂ α β), ← hψ₂n α β _ _ (hE β) (hE₂ α β), hy, hy]
      change (resU (G q a) (hk₁ α β)).pull a ((resU (G q a) (hk α)).pull a x) =
        (resU (G q a) (hk₂ α β)).pull a ((resU (G q a) (hk β)).pull a x)
      rw [← CrystallineSemistableComparison.Onto.resU_pull_trans (G q a) (hk α) (hk₁ α β) (inU_mono q le_top),
        ← CrystallineSemistableComparison.Onto.resU_pull_trans (G q a) (hk β) (hk₂ α β) (inU_mono q le_top)])
    refine ⟨ω, hRinj (funext fun α => ?_)⟩
    rw [hRe]
    change E α (omMap (φ α) a ω) = R x α
    rw [hω, hy]

end GlobalTheory.CompanionTheory.OmGlue
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineSmoothFormsBijectiveStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_smooth_forms_bijective : CrystallineSemistableComparison.Onto.AffOm → CrystallineSemistableComparison.Onto.OmNat → ∀ (K : Type) [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [IsAffine X] [Smooth q] (a : ℕ),
    ∃ e : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a →ₗ[K] CrystallineSemistableComparison.Onto.HV q ⊤ a a, CrystallineSemistableComparison.Onto.IsOm q ⊤ a e ∧ Function.Bijective e := by
  first | exact @GlobalTheory.CompanionTheory.OmGlue.om_top | exact GlobalTheory.CompanionTheory.OmGlue.om_top | (intros; apply GlobalTheory.CompanionTheory.OmGlue.om_top <;> assumption)
end
