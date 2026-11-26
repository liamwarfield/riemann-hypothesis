module

public import Development.EtaleCohomology.EtaleTrace.FrobTraceOf
public import Development.EtaleCohomology.TateTwists.EtalePrimitiveRootsExistLocally
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleTrace.TorsionH0PointOfLocalTwist
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.EtaleTrace

def PtCover : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] (T : Sieve (S k)), T ∈ Scheme.etaleTopology (S k) → T.arrows (𝟙 _)

def TwZero : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)),
  GlobalTheory.EtC.twGen (U := U) 0 ζ = GlobalTheory.EtC.twGen (U := U) 0 ξ

def EvNat : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X U : Scheme.{0}) (α : CochainComplex.HomComplex.Cochain ((chains R).obj (sch.obj X)) (res R F) 0)
  (x : U ⟶ X), ev (R := R) α 0 0 (by simp) U x = Sec.res x (ev (R := R) α 0 0 (by simp) X (𝟙 X))

def CocEq : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})
  (α β : CochainComplex.HomComplex.Cocycle ((chains R).obj (sch.obj X)) (res R F) 0),
  (∀ (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U),
    ev (R := R) α.1 0 0 (by simp) U x = ev (R := R) β.1 0 0 (by simp) U x) → α = β

theorem exists_prim (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k] (hl : (l : k) ≠ 0) (j : ℕ) :
    Nonempty (Prim (l ^ j) Γ(S k, ⊤)) := by
  have hq : 0 < l ^ j := pow_pos (Fact.out : l.Prime).pos j
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l ^ j) k)
    (Polynomial.degree_cyclotomic_pos (l ^ j) k hq).ne'
  have hu : IsUnit ((l ^ j : ℕ) : k) := by
    rw [Nat.cast_pow]; exact (isUnit_iff_ne_zero.2 hl).pow j
  have hr' : Polynomial.aeval r (Polynomial.cyclotomic (l ^ j) ℤ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hr
  exact ⟨Prim.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom ⟨r, hu, hr'⟩⟩

end LateralTheory.EtaleTrace
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.GenOutPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def GenOn {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) {N : ℕ}
    (w : Fin (N + 1) → X.functionField) (U : X.Opens) (πU : U.toScheme ⟶ PN k N) : Prop :=
  ∀ (hη : genericPoint X ∈ U) (n : ℕ), 0 < n → ∀ (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f ∈ homogeneousSubmodule (Fin (N + 1)) k n),
    ((⟨genericPoint X, hη⟩ : U) ∈ πU ⁻¹ᵁ Proj.basicOpen _ f ↔ eval₂ (kHom p) w f ≠ 0) ∧
    ∀ (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • n))
      (h : (⟨genericPoint X, hη⟩ : U) ∈ πU ⁻¹ᵁ Proj.basicOpen _ f),
      U.toScheme.presheaf.germ _ ⟨genericPoint X, hη⟩ h (πU.app _
          (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ hf m g hg))) *
        (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom (show X.presheaf.stalk (U.ι ⟨genericPoint X, hη⟩) from
          eval₂ (kHom p) w f) ^ m =
        (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom (show X.presheaf.stalk (U.ι ⟨genericPoint X, hη⟩) from eval₂ (kHom p) w g)

def GenOutChart : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField), (∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, w j / w i ∈ loc X x) →
  ∀ x : X, ∃ (U : X.Opens) (πU : U.toScheme ⟶ PN k N), x ∈ U ∧ πU ≫ PNto k N = U.ι ≫ p ∧ GenOn p w U πU

def GenOutGlue : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField),
  (∀ x : X, ∃ (U : X.Opens) (πU : U.toScheme ⟶ PN k N), x ∈ U ∧ πU ≫ PNto k N = U.ι ≫ p ∧ GenOn p w U πU) →
  ∃ π : X ⟶ PN k N, π ≫ PNto k N = p ∧ Gen p π w

theorem GenOut_of (h1 : GenOutChart) (h2 : GenOutGlue) : GenOut := by
  intro k _ X _ p N w hw
  exact h2 k p N w (h1 k p N w hw)

end LateralTheory.EtaleTrace.Cov
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.GenInPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov.GenInPf

abbrev A (k : Type) [Field k] (N : ℕ) := homogeneousSubmodule (Fin (N + 1)) k

theorem X_mem (k : Type) [Field k] (N : ℕ) (j : Fin (N + 1)) : (X j : MvPolynomial (Fin (N + 1)) k) ∈ A k N 1 :=
  (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k j)

theorem X_mem' (k : Type) [Field k] (N : ℕ) (j : Fin (N + 1)) :
    (X j : MvPolynomial (Fin (N + 1)) k) ∈ A k N (1 • 1) := by
  simpa using X_mem k N j

theorem genCover {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {N : ℕ} (ι : X ⟶ PN k N) :
    ∃ i : Fin (N + 1), genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i) := by
  have htop : ⨆ i, Proj.basicOpen (A k N) (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) = ⊤ := by
    apply Proj.iSup_basicOpen_eq_top'
    · exact fun i => ⟨1, X_mem k N i⟩
    · rw [eq_top_iff]
      intro x hxt; clear hxt
      have hx : x ∈ Algebra.adjoin k (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) k)) := by
        rw [MvPolynomial.adjoin_range_X]; trivial
      induction hx using Algebra.adjoin_induction with
      | mem y hy => exact Algebra.subset_adjoin hy
      | algebraMap c =>
        have h0 : (C c : MvPolynomial (Fin (N + 1)) k) ∈ A k N 0 :=
          (mem_homogeneousSubmodule _ _).2 (isHomogeneous_C _ c)
        have := (Algebra.adjoin (A k N 0) (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) k))).algebraMap_mem
          (⟨C c, h0⟩ : A k N 0)
        simpa using this
      | add a b _ _ ha hb => exact add_mem ha hb
      | mul a b _ _ ha hb => exact mul_mem ha hb
  have hm : ι.base (genericPoint X) ∈ (⨆ i, Proj.basicOpen (A k N) (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)) := by
    rw [htop]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hm
  exact ⟨i, hi⟩

def away {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {N : ℕ} (ι : X ⟶ PN k N) {n : ℕ}
    (f : MvPolynomial (Fin (N + 1)) k) (hf : f ∈ A k N n) (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) f)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • n)) : X.functionField :=
  X.presheaf.germ _ (genericPoint X) h (ι.app _
    (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ hf m g hg)))

def coordAt {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {N : ℕ} (ι : X ⟶ PN k N) (i : Fin (N + 1))
    (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) : Fin (N + 1) → X.functionField :=
  fun j => away ι (MvPolynomial.X i) (X_mem k N i) h 1 (MvPolynomial.X j) (X_mem' k N j)

def GenAwayEval : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N),
  ι ≫ PNto k N = p → ∀ (i : Fin (N + 1)) (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i))
  (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • 1)),
  away ι (MvPolynomial.X i) (X_mem k N i) h m g hg = eval₂ (kHom p) (coordAt ι i h) g

def GenOfAway : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N),
  ι ≫ PNto k N = p → ∀ (i : Fin (N + 1)) (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)),
  (∀ (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • 1)),
    away ι (MvPolynomial.X i) (X_mem k N i) h m g hg = eval₂ (kHom p) (coordAt ι i h) g) →
  Gen p ι (coordAt ι i h)

end LateralTheory.EtaleTrace.Cov.GenInPf

namespace LateralTheory.EtaleTrace.Cov
open GenInPf in
theorem GenIn_of (hE : GenAwayEval) (hG : GenOfAway) : GenIn := by
  intro k _ X _ p N ι hp
  obtain ⟨i, h⟩ := genCover ι
  have hgen := hG k p N ι hp i h (hE k p N ι hp i h)
  refine ⟨coordAt ι i h, i, ?_, hgen⟩
  have h1 := (hgen 1 one_pos (MvPolynomial.X i) (X_mem k N i)).1.mp h
  have h2 := (hgen 1 one_pos (MvPolynomial.X i) (X_mem k N i)).2 1 (MvPolynomial.X i) (X_mem' k N i) h
  simp only [eval₂_X, pow_one] at h1 h2
  change coordAt ι i h i * coordAt ι i h i = coordAt ι i h i at h2
  exact mul_left_cancel₀ h1 (h2.trans (mul_one _).symm)

end LateralTheory.EtaleTrace.Cov
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.FibrePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

def GenEtale : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P] (p : X ⟶ S k)
  (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p → LocallyOfFiniteType r → IsFinite π → Surjective π →
  (π.stalkMap (genericPoint X)).hom.FormallyUnramified → ∃ V : P.Opens, (V : Set P).Nonempty ∧ Etale (π ∣_ V)

def RatPtIn : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {P : Scheme.{0}} (r : P ⟶ S k), LocallyOfFiniteType r →
  ∀ V : P.Opens, (V : Set P).Nonempty → ∃ t : Pt r, ∀ x, t.1.base x ∈ V

def FibreOfEtale : Prop := ∀ (k : Type) [Field k] {X P : Scheme.{0}} (p : X ⟶ S k) (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p →
  ∀ V : P.Opens, Etale (π ∣_ V) → ∀ t : Pt r, (∀ x, t.1.base x ∈ V) → Etale (equalizer.ι π (p ≫ t.1) ≫ p)

theorem Fibre_of (h1 : GenEtale) (h2 : RatPtIn) (h3 : FibreOfEtale) : Fibre := by
  intro k _ _ X P _ _ p r π hπ hr hfin hsurj hun
  obtain ⟨V, hV, hE⟩ := h1 k p r π hπ hr hfin hsurj hun
  obtain ⟨t, ht⟩ := h2 k r hr V hV
  exact ⟨t, h3 k p r π hπ V hE t ht⟩

end LateralTheory.EtaleTrace.Cov
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.PNBasicPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

theorem pn_sep (k : Type) [Field k] (d : ℕ) : IsSeparated (PNto k d) := by
  unfold PNto; infer_instance

theorem algebraMap_field_homogeneousDegreeZero_surjective (k : Type) [Field k] (d : ℕ) :
    Function.Surjective (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 0)) := by
  rintro ⟨x, hx⟩
  refine ⟨AddMonoidAlgebra.coeff x 0, ?_⟩
  apply Subtype.ext
  have h0 := (MvPolynomial.mem_homogeneousSubmodule 0 x).1 hx
  have h : x = C (AddMonoidAlgebra.coeff x 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 ((MvPolynomial.totalDegree_zero_iff_isHomogeneous _).2 h0)
  show (algebraMap k (MvPolynomial (Fin (d + 1)) k)) (AddMonoidAlgebra.coeff x 0) = x
  conv_rhs => rw [h]
  rfl

instance ft0 (k : Type) [Field k] (d : ℕ) :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 0) (MvPolynomial (Fin (d+1)) k) := by
  have : IsScalarTower k (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 0) (MvPolynomial (Fin (d+1)) k) := by
    exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType k _ _

theorem pn_lft (k : Type) [Field k] (d : ℕ) : LocallyOfFiniteType (PNto k d) := by
  unfold PNto
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 0)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.FiniteType.of_surjective _ (algebraMap_field_homogeneousDegreeZero_surjective k d)
  infer_instance

def PNIntegral : Prop := ∀ (k : Type) [Field k] (d : ℕ), IsIntegral (PN k d)

theorem PNBasic_of (h : PNIntegral) : PNBasic := fun k _ d => ⟨h k d, pn_sep k d, pn_lft k d⟩

end LateralTheory.EtaleTrace.Cov
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.LCompIntPf
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.EtaleTrace

theorem LCompInt_of : LCompInt := by
  intro k _ _ d X p hp hc
  have := hp.2
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  exact GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace p

end LateralTheory.EtaleTrace
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.GenUsePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

lemma genUse_generic_mem {X : Scheme.{0}} [IsIntegral X] (U : X.Opens) (x : X) (hx : x ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩

lemma genUse_ne {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) {N : ℕ} (ι : X ⟶ PN k N)
    (v : Fin (N + 1) → X.functionField) (hG : Gen p ι v) (n : ℕ) (hn : 0 < n) (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f.IsHomogeneous n) (x : X) (hx : x ∈ ι ⁻¹ᵁ Proj.basicOpen _ f) : eval₂ (kHom p) v f ≠ 0 :=
  ((hG n hn f ((mem_homogeneousSubmodule _ _).mpr hf)).1).mp (genUse_generic_mem _ x hx)

def GenUseLoc : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
  (v : Fin (N + 1) → X.functionField), Gen p ι v → ∀ (n : ℕ), 0 < n → ∀ f : MvPolynomial (Fin (N + 1)) k,
  f.IsHomogeneous n → ∀ x : X, x ∈ ι ⁻¹ᵁ Proj.basicOpen _ f →
  ∀ g : MvPolynomial (Fin (N + 1)) k, g.IsHomogeneous n → eval₂ (kHom p) v g / eval₂ (kHom p) v f ∈ loc X x

def GenUseBack : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
  (v : Fin (N + 1) → X.functionField), Gen p ι v → ∀ (n : ℕ), 0 < n → ∀ f : MvPolynomial (Fin (N + 1)) k,
  f.IsHomogeneous n → ∀ x : X, eval₂ (kHom p) v f ≠ 0 →
  (∀ g : MvPolynomial (Fin (N + 1)) k, g.IsHomogeneous n → eval₂ (kHom p) v g / eval₂ (kHom p) v f ∈ loc X x) →
  x ∈ ι ⁻¹ᵁ Proj.basicOpen _ f

def GenUseRangeTo : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
  (v : Fin (N + 1) → X.functionField), Gen p ι v → ∀ z : X.functionField, z ∈ (ι.stalkMap (genericPoint X)).hom.range →
  ∃ (n : ℕ) (f g : MvPolynomial (Fin (N + 1)) k), f.IsHomogeneous n ∧ g.IsHomogeneous n ∧
    eval₂ (kHom p) v f ≠ 0 ∧ z = eval₂ (kHom p) v g / eval₂ (kHom p) v f

def GenUseRangeOf : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
  (v : Fin (N + 1) → X.functionField), Gen p ι v → ∀ (n : ℕ) (f g : MvPolynomial (Fin (N + 1)) k), f.IsHomogeneous n →
  g.IsHomogeneous n → eval₂ (kHom p) v f ≠ 0 →
  eval₂ (kHom p) v g / eval₂ (kHom p) v f ∈ (ι.stalkMap (genericPoint X)).hom.range

theorem genUseLoc : GenUseLoc := by
  intro k _ X _ p N ι v hG n hn f hf x hx g hg
  have hne := genUse_ne p ι v hG n hn f hf x hx
  have hη := genUse_generic_mem _ x hx
  have hg' : g ∈ homogeneousSubmodule (Fin (N + 1)) k (1 • n) := by
    rw [one_smul]; exact (mem_homogeneousSubmodule _ _).mpr hg
  have key := (hG n hn f ((mem_homogeneousSubmodule _ _).mpr hf)).2 1 g hg' hη
  have : Nonempty (ι ⁻¹ᵁ Proj.basicOpen _ f) := ⟨⟨x, hx⟩⟩
  refine ⟨X.presheaf.germ _ x hx (ι.app _ (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ ((mem_homogeneousSubmodule _ _).mpr hf) 1 g hg'))), ?_⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField, eq_div_iff hne]
  rw [pow_one] at key
  exact key

theorem genUseRangeOf_pos {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
    (v : Fin (N + 1) → X.functionField) (hG : Gen p ι v) (n : ℕ) (hn : 0 < n) (f g : MvPolynomial (Fin (N + 1)) k)
    (hf : f.IsHomogeneous n) (hg : g.IsHomogeneous n) (hne : eval₂ (kHom p) v f ≠ 0) :
    eval₂ (kHom p) v g / eval₂ (kHom p) v f ∈ (ι.stalkMap (genericPoint X)).hom.range := by
  have hη := ((hG n hn f ((mem_homogeneousSubmodule _ _).mpr hf)).1).mpr hne
  have hg' : g ∈ homogeneousSubmodule (Fin (N + 1)) k (1 • n) := by
    rw [one_smul]; exact (mem_homogeneousSubmodule _ _).mpr hg
  have key := (hG n hn f ((mem_homogeneousSubmodule _ _).mpr hf)).2 1 g hg' hη
  rw [pow_one] at key
  refine ⟨(PN k N).presheaf.germ _ (ι (genericPoint X)) hη (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ ((mem_homogeneousSubmodule _ _).mpr hf) 1 g hg')), ?_⟩
  rw [eq_div_iff hne, ← key]
  erw [Scheme.Hom.germ_stalkMap_apply]

def GenUseNZ : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
  (v : Fin (N + 1) → X.functionField), Gen p ι v → ∃ i, v i ≠ 0

theorem genUseNZ : GenUseNZ := by
  intro k _ X _ p N ι v hG
  have hcov : ⨆ i, Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) = ⊤ := by
    apply Proj.iSup_basicOpen_eq_top'
    · exact fun i => ⟨1, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i)⟩
    · rw [eq_top_iff]
      rintro a -
      induction a using MvPolynomial.induction_on with
      | C c =>
        have : (C c : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 0 :=
          (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ c)
        exact Subalgebra.algebraMap_mem _ (⟨_, this⟩ : homogeneousSubmodule (Fin (N + 1)) k 0)
      | add a b ha hb => exact Subalgebra.add_mem _ ha hb
      | mul_X a i ha => exact Subalgebra.mul_mem _ ha (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hm : ι (genericPoint X) ∈ (⊤ : (PN k N).Opens) := trivial
  rw [← hcov, TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, hi⟩ := hm
  refine ⟨i, ?_⟩
  have := ((hG 1 one_pos (MvPolynomial.X i) ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i))).1).mp hi
  simpa using this

theorem genUseRangeOf_of (hZ : GenUseNZ) : GenUseRangeOf := by
  intro k _ X _ p N ι v hG n f g hf hg hne
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨i, hi⟩ := hZ k p N ι v hG
    have h1 : (MvPolynomial.X i * f).IsHomogeneous 1 := by simpa using (isHomogeneous_X k i).mul hf
    have h2 : (MvPolynomial.X i * g).IsHomogeneous 1 := by simpa using (isHomogeneous_X k i).mul hg
    have hne' : eval₂ (kHom p) v (MvPolynomial.X i * f) ≠ 0 := by simp [hi, hne]
    have := genUseRangeOf_pos p N ι v hG 1 one_pos _ _ h1 h2 hne'
    simpa [eval₂_mul, eval₂_X, mul_div_mul_left _ _ hi] using this
  · exact genUseRangeOf_pos p N ι v hG n hn f g hf hg hne

theorem genUseRangeTo : GenUseRangeTo := by
  intro k _ X _ p N ι v hG z hz
  obtain ⟨t, rfl⟩ := hz
  obtain ⟨U, hU, s, rfl⟩ := (PN k N).presheaf.exists_germ_eq t
  obtain ⟨_, ⟨h, rfl⟩, hhη, hhU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Proj.isBasis_basicOpen _)) hU
  have hle : ∀ j, Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (GradedRing.proj _ j h) ≤
      Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) h := fun j => by
    rw [Proj.basicOpen_eq_iSup_proj _ h]; exact le_iSup (fun i => Proj.basicOpen _ (GradedRing.proj _ i h)) j
  rw [Proj.basicOpen_eq_iSup_proj, TopologicalSpace.Opens.mem_iSup] at hhη
  obtain ⟨j, hj⟩ := hhη
  obtain ⟨i, hi⟩ := genUseNZ k p N ι v hG
  have hXi : ι (genericPoint X) ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) :=
    ((hG 1 one_pos _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i))).1).mpr (by simpa using hi)
  have hpj : GradedRing.proj (homogeneousSubmodule (Fin (N + 1)) k) j h ∈ homogeneousSubmodule (Fin (N + 1)) k j := by
    rw [GradedRing.proj_apply]; exact SetLike.coe_mem _
  have hfm : MvPolynomial.X i * GradedRing.proj (homogeneousSubmodule (Fin (N + 1)) k) j h ∈
      homogeneousSubmodule (Fin (N + 1)) k (j + 1) := by
    have := (isHomogeneous_X k i).mul ((mem_homogeneousSubmodule _ _).mp hpj)
    exact (mem_homogeneousSubmodule _ _).mpr (by rwa [Nat.add_comm 1 j] at this)
  set f := MvPolynomial.X i * GradedRing.proj (homogeneousSubmodule (Fin (N + 1)) k) j h with hfdef
  have hfη : ι (genericPoint X) ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) f := by
    rw [hfdef, Proj.basicOpen_mul]; exact ⟨hXi, hj⟩
  have hfU : Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) f ≤ U := by
    rw [hfdef, Proj.basicOpen_mul]; exact inf_le_right.trans ((hle j).trans hhU)
  have hfne := ((hG (j + 1) (Nat.succ_pos j) f hfm).1).mp hfη
  rw [← (PN k N).presheaf.germ_res_apply (homOfLE hfU) _ hfη s]
  obtain ⟨a, ha⟩ : ∃ a, Proj.awayToSection _ f a = (PN k N).presheaf.map (homOfLE hfU).op s :=
    ⟨(Proj.basicOpenIsoAway _ f hfm (Nat.succ_pos j)).inv ((PN k N).presheaf.map (homOfLE hfU).op s), by
      rw [← Proj.basicOpenIsoAway_hom _ f hfm (Nat.succ_pos j)]; simp⟩
  obtain ⟨m, g, hg, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ hfm a
  have key := (hG (j + 1) (Nat.succ_pos j) f hfm).2 m g hg hfη
  refine ⟨m • (j + 1), f ^ m, g, ?_, (mem_homogeneousSubmodule _ _).mp hg, by rw [eval₂_pow]; exact pow_ne_zero _ hfne, ?_⟩
  · rw [smul_eq_mul, mul_comm]; exact ((mem_homogeneousSubmodule _ _).mp hfm).pow m
  rw [← ha]
  erw [Scheme.Hom.germ_stalkMap_apply]
  rw [eval₂_pow, eq_div_iff (pow_ne_zero _ hfne)]
  exact key

theorem GenUse_of (hB : GenUseBack) : GenUse := by
  have hT := genUseRangeTo
  have hL := genUseLoc
  have hO := genUseRangeOf_of genUseNZ
  intro k _ X _ p N ι v hG
  refine ⟨fun n hn f hf x => ⟨fun hx => ⟨genUse_ne p ι v hG n hn f hf x hx, hL k p N ι v hG n hn f hf x hx⟩,
    fun h => hB k p N ι v hG n hn f hf x h.1 h.2⟩, fun z => ⟨hT k p N ι v hG z, ?_⟩⟩
  rintro ⟨n, f, g, hf, hg, hne, rfl⟩
  exact hO k p N ι v hG n f g hf hg hne

end LateralTheory.EtaleTrace.Cov
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.FinSurjPfAll
section -- merged from Development.EtaleCohomology.EtaleTrace.FinSurjPfDense
section -- merged from Development.EtaleCohomology.EtaleTrace.FinSurjPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def FSAffine : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k),
  ∀ (N d : ℕ) (ι : X ⟶ PN k N) (π : X ⟶ PN k d) (v : Fin (N + 1) → X.functionField) (w : Fin (d + 1) → X.functionField),
  IsClosedImmersion ι → Coord p ι v → Coord p π w →
  (∀ i, ∃ c : Fin (N + 1) → k, w i = ∑ j, kHom p (c j) * v j) →
  (∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, v j / w i ∈ loc X x) →
  IsAffineHom π

def FSDense : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k),
  ∀ (d : ℕ) (π : X ⟶ PN k d) (w : Fin (d + 1) → X.functionField), Coord p π w →
  (∀ (m : ℕ) (F : MvPolynomial (Fin (d + 1)) k), F.IsHomogeneous m → eval₂ (kHom p) w F = 0 → F = 0) →
  IsDominant π

theorem FinSurj_of (h1 : PNBasic) (hA : FSAffine) (hD : FSDense) : FinSurj := by
  intro k _ X _ p hp N d ι π v w hι hπ cv cw hlin hx hind
  have hsep : IsSeparated (PNto k d) := (h1 k d).2.1
  have : IsProper (π ≫ PNto k d) := by rw [hπ]; exact hp
  have : IsProper π := IsProper.of_comp π (PNto k d)
  have : IsAffineHom π := hA k p N d ι π v w hι cv cw hlin hx
  have : IsDominant π := hD k p d π w cw hind
  refine ⟨IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩, ?_⟩
  exact surjective_of_isDominant_of_isClosed_range π (π.isClosedMap.isClosed_range)
end LateralTheory.EtaleTrace.Cov
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

theorem loc_generic_top (X : Scheme.{0}) [IsIntegral X] (z : X.functionField) : z ∈ loc X (genericPoint X) := by
  refine ⟨z, ?_⟩
  simp [RingHom.algebraMap_toAlgebra, TopCat.Presheaf.stalkSpecializes_refl]

theorem FSDense_pf : FSDense := by
  intro k _ X _ p d π w cw hind

  have hz : ∀ (n : ℕ) (g : MvPolynomial (Fin (d + 1)) k), g.IsHomogeneous n →
      g ∈ (π (genericPoint X)).asHomogeneousIdeal → g = 0 := by
    intro n g hg hmem
    have hgX : (g * MvPolynomial.X 0).IsHomogeneous (n + 1) := hg.mul (isHomogeneous_X k (0 : Fin (d + 1)))
    have h1 := (cw.opens (n + 1) (Nat.succ_pos n) (g * MvPolynomial.X 0) hgX (genericPoint X))
    have hnot : genericPoint X ∉ π ⁻¹ᵁ Proj.basicOpen _ (g * MvPolynomial.X 0) := by
      intro h
      have h' : π (genericPoint X) ∈ Proj.basicOpen _ (g * MvPolynomial.X 0) := h
      rw [Proj.mem_basicOpen] at h'
      exact h' (Ideal.mul_mem_right _ _ hmem)
    have he : eval₂ (kHom p) w (g * MvPolynomial.X 0) = 0 := by
      by_contra hne
      exact hnot (h1.2 ⟨hne, fun _ _ => loc_generic_top X _⟩)
    have := hind (n + 1) _ hgX he
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h (X_ne_zero 0)
  have hbot : ∀ a ∈ (π (genericPoint X)).asHomogeneousIdeal, a = 0 := by
    intro a ha
    classical
    rw [← DirectSum.sum_support_decompose (homogeneousSubmodule (Fin (d + 1)) k) a]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine hz i _ ?_ ((π (genericPoint X)).asHomogeneousIdeal.isHomogeneous i ha)
    exact (mem_homogeneousSubmodule i _).mp (SetLike.coe_mem _)
  constructor
  intro y
  have hle : (show ProjectiveSpectrum (homogeneousSubmodule (Fin (d + 1)) k) from π (genericPoint X)) ≤
      (show ProjectiveSpectrum (homogeneousSubmodule (Fin (d + 1)) k) from y) := by
    rw [← ProjectiveSpectrum.as_ideal_le_as_ideal]
    intro a ha
    rw [hbot a ha]
    exact zero_mem _
  have hc := (ProjectiveSpectrum.le_iff_mem_closure _ _ _).mp hle
  exact closure_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self _)) hc
end LateralTheory.EtaleTrace.Cov
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

theorem eval₂_scale_one {k K : Type} [Field k] [Field K] {n : ℕ} (f : k →+* K) (u : Fin n → K) (t : K)
    (g : MvPolynomial (Fin n) k) (hg : g.IsHomogeneous 1) :
    eval₂ f (fun j => u j * t) g = eval₂ f u g * t := by
  rw [eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ j, d j = 1 := by
    have := hg (mem_support_iff.mp hd)
    rw [← this]; simp [Finsupp.weight_apply, Finsupp.sum_fintype]
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, pow_one, mul_assoc]

theorem eval₂_mem_subring {k K : Type} [Field k] [Field K] {n : ℕ} (f : k →+* K) (S : Subring K)
    (hf : ∀ c, f c ∈ S) (u : Fin n → K) (hu : ∀ j, u j ∈ S) (g : MvPolynomial (Fin n) k) : eval₂ f u g ∈ S := by
  induction g using MvPolynomial.induction_on with
  | C a => simpa using hf a
  | add a b ha hb => rw [eval₂_add]; exact S.add_mem ha hb
  | mul_X a j ha => rw [eval₂_mul, eval₂_X]; exact S.mul_mem ha (hu j)

theorem eval_linear_form_div_mem_local_ring_of_coordinates_div_mem {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (x : X) {n : ℕ}
    (u : Fin n → X.functionField) (t : X.functionField) (hu : ∀ j, u j / t ∈ loc X x)
    (g : MvPolynomial (Fin n) k) (hg : g.IsHomogeneous 1) : eval₂ (kHom p) u g / t ∈ loc X x := by
  rw [div_eq_mul_inv, ← eval₂_scale_one _ _ _ _ hg]
  exact eval₂_mem_subring _ _ (kHom_mem_loc p x) _ (fun j => by simpa [div_eq_mul_inv] using hu j) g

theorem linForm {k : Type} [Field k] {K : Type} [Field K] (f : k →+* K) {N : ℕ} (v : Fin (N + 1) → K) (z : K)
    (h : ∃ c : Fin (N + 1) → k, z = ∑ j, f (c j) * v j) :
    ∃ L : MvPolynomial (Fin (N + 1)) k, L.IsHomogeneous 1 ∧ eval₂ f v L = z := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨∑ j, C (c j) * X j, ?_, by simp [eval₂_sum]⟩
  exact IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _

theorem PN_cover (k : Type) [Field k] (d : ℕ) (y : PN (k := k) d) :
    ∃ i : Fin (d + 1), y ∈ Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) k) (X i) := by
  have htop := Proj.iSup_basicOpen_eq_top (homogeneousSubmodule (Fin (d + 1)) k)
    (fun i : Fin (d + 1) => (X i : MvPolynomial (Fin (d + 1)) k)) ?_
  · have : y ∈ (⊤ : (PN (k := k) d).Opens) := trivial
    rw [← htop] at this
    exact TopologicalSpace.Opens.mem_iSup.mp this
  intro q hq
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra! hne
  have hm0 : m = 0 := Finsupp.ext fun i => hne i (Set.mem_univ i)
  subst hm0
  have h0 : GradedRing.proj (homogeneousSubmodule (Fin (d + 1)) k) 0 q = 0 := hq
  rw [GradedRing.proj_apply] at h0
  change ((MvPolynomial.decomposition.decompose' q 0 : homogeneousSubmodule (Fin (d + 1)) k 0) :
    MvPolynomial (Fin (d + 1)) k) = 0 at h0
  rw [MvPolynomial.decomposition.decompose'_apply, homogeneousComponent_zero, C_eq_zero] at h0
  exact (mem_support_iff.mp hm) h0

theorem FSAffine_pf : FSAffine := by
  intro k _ X _ p N d ι π v w hι cv cw hlin hx
  have : IsAffineHom ι := inferInstance
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro y
  obtain ⟨i, hi⟩ := PN_cover k d y
  obtain ⟨L, hL, evL⟩ := linForm (kHom p) v (w i) (hlin i)
  have hXi : (MvPolynomial.X i : MvPolynomial (Fin (d + 1)) k).IsHomogeneous 1 := isHomogeneous_X _ _
  have heq : π ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) k) (MvPolynomial.X i) =
      ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) L := by
    ext x
    change x ∈ π ⁻¹ᵁ _ ↔ x ∈ ι ⁻¹ᵁ _
    rw [cw.opens 1 one_pos _ hXi x, cv.opens 1 one_pos L hL x, eval₂_X, evL]
    constructor
    · rintro ⟨hne, H⟩
      refine ⟨hne, fun g hg => eval_linear_form_div_mem_local_ring_of_coordinates_div_mem p x v (w i) (fun j => ?_) g hg⟩
      obtain ⟨i', hi', hv'⟩ := hx x
      have h1 : w i' / w i ∈ loc X x := by simpa using H (MvPolynomial.X i') (isHomogeneous_X _ _)
      have : v j / w i = v j / w i' * (w i' / w i) := by field_simp
      rw [this]; exact (loc X x).mul_mem (hv' j) h1
    · rintro ⟨hne, H⟩
      refine ⟨hne, fun g hg => eval_linear_form_div_mem_local_ring_of_coordinates_div_mem p x w (w i) (fun l => ?_) g hg⟩
      obtain ⟨L', hL', evL'⟩ := linForm (kHom p) v (w l) (hlin l)
      rw [← evL']; exact H L' hL'
  refine ⟨_, hi, Proj.isAffineOpen_basicOpen _ _ ((mem_homogeneousSubmodule 1 _).mpr hXi) one_pos, ?_⟩
  rw [heq]
  exact (Proj.isAffineOpen_basicOpen _ _ ((mem_homogeneousSubmodule 1 _).mpr hL) one_pos).preimage ι

theorem FinSurj_of_full (h1 : PNBasic) : FinSurj := FinSurj_of h1 FSAffine_pf FSDense_pf
end LateralTheory.EtaleTrace.Cov
end
end
