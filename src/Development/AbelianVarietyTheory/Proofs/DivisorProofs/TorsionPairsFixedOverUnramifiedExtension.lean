module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLiftSemiSecPull

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteKTorsionAbelianPartAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteKTorsionAbelianPartAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.AbTorsionFiniteF

theorem finite_torsion_TF : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → Finite {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} := by
  intro R _ _ D F _ _ _ k hk
  let g := jFK (R := R) F ≫ jK R
  let B' := (Over.pullback g).obj D.P.A
  have hB : IsAbelianScheme B' := GlobalTheory.isAbelianScheme_pullback_obj g D.P.A D.P.isAb
  have hfin := GlobalTheory.AbTorsionFinite.finite_torsion F B' hB k hk
  let φ : (TF (R := R) F ⟶ D.P.A) → (𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ B') := fun x =>
    Over.homMk (pullback.lift x.left (𝟙_ (Over (Spec (CommRingCat.of F)))).hom
      ((Over.w x).trans (by simp [g]))) (pullback.lift_snd _ _ _)
  have hφ : ∀ x, (φ x).left ≫ pullback.fst D.P.A.hom g = x.left := fun x => pullback.lift_fst _ _ _
  have hpow : ∀ x : TF (R := R) F ⟶ D.P.A, (φ x) ^ k = 1 ↔ x ^ k = 1 := fun x =>
    GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull (by simp [g]) (isGrpPullback_pullback D.P.A g) (hφ x)
  refine Finite.of_injective (fun x : {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} =>
    (⟨φ x.1, (hpow x.1).2 x.2⟩ : {y : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ B' // y ^ k = 1})) ?_
  intro a b hab
  have e := congrArg (fun y => y.1.left ≫ pullback.fst D.P.A.hom g) hab
  simp only [hφ] at e
  exact Subtype.ext (Over.OverMorphism.ext e)

end GlobalTheory.AbTorsionFiniteF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteKTorsionAbelianPartAlgClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_kTorsion_abelianPart_algClosed : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → Finite {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} := by
  first | exact @GlobalTheory.AbTorsionFiniteF.finite_torsion_TF | exact GlobalTheory.AbTorsionFiniteF.finite_torsion_TF | (intros; apply GlobalTheory.AbTorsionFiniteF.finite_torsion_TF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPointCharacterValuePowIsUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPointCharacterValuePowIsUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UnramCharPow

open GlobalTheory.TorusExt GlobalTheory.BXOf GlobalTheory.UnramTorsion

attribute [local instance] gtGroup

theorem charVal_pow_unit : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → (∀ χ, ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (val (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J) : F) = ((u : T) : F)) → ∀ (k : ℕ) (p : QkPt D F k) (b : Sp T ⟶ D.P.A.left), spMap T.subtype ≫ b = p.g.b.left → b ≫ D.P.A.hom = spMap φ₁ → ∀ χ, ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal p.g χ (closedPoint F) J) : F) ^ k = ((u : T) : F) := by
  intro R _ _ D hB F _ _ T _ φ₁ hφ J₀ h₀ J hJ eJ hψ k p b hb hbA χ
  let H : Subgroup Fˣ := (Units.map T.subtype.toMonoidHom).range
  let w : ((TF (R := R) F).left.presheaf.stalk (closedPoint F))ˣ →* Fˣ ⧸ H :=
    (QuotientGroup.mk' H).comp (sig F)
  let ρ : TF (R := R) F ⟶ Over.mk (spMap φ₁) := Over.homMk (spMap T.subtype) (by
    show spMap T.subtype ≫ spMap φ₁ = jFK (R := R) F ≫ jK R
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ)
  let b' : Over.mk (spMap φ₁) ⟶ D.P.A := Over.homMk b hbA
  have hb' : ρ ≫ b' = p.g.b := Over.OverMorphism.ext hb
  have mem : ∀ s : ((TF (R := R) F).left.presheaf.stalk (closedPoint F))ˣ,
      (∃ u : Tˣ, (sig F s : F) = ((u : T) : F)) → w s = 1 := fun s ⟨u, hu⟩ => by
    show (QuotientGroup.mk' H) (sig F s) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨u, Units.ext hu.symm⟩
  have hw : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ D.P.A.left)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : (Over.mk (spMap φ₁)).left ⟶ Y),
      w (val t (ρ.left ≫ r) (closedPoint F) J) = 1 := by
    intro Y K _ φ ε t r
    exact mem _ (val_integral T.subtype h₀ eJ t r)
  have e₁ := w_nsmul ρ hJ w hw p.g b' hb' χ k
  obtain ⟨g, hg, hi⟩ := p.eq
  have hp : k • p.g = g := ((isNsmul_iff_eq _ _ _).1 hg).symm
  have hv : charVal g χ (closedPoint F) J = tauVal D F p.y χ (closedPoint F) J :=
    ((isIota_iff _ _).1 hi).2 χ (closedPoint F) J hJ
  rw [hp, hv, w_tau ρ hJ w hw, mem _ (hψ _), mem _ (hψ _), mem _ (hψ _)] at e₁
  simp only [inv_one, _root_.mul_one] at e₁
  have e₂ : (QuotientGroup.mk' H) (sig F (charVal p.g χ (closedPoint F) J) ^ k) = 1 := by
    rw [map_pow]; exact e₁.symm
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at e₂
  obtain ⟨u, hu⟩ := e₂
  exact ⟨u, by rw [← Units.val_pow_eq_pow_val, ← hu]; rfl⟩

end GlobalTheory.UnramCharPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPointCharacterValuePowIsUnitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientPoint_characterValue_pow_isUnit : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → (∀ χ, ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (val (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J) : F) = ((u : T) : F)) → ∀ (k : ℕ) (p : QkPt D F k) (b : Sp T ⟶ D.P.A.left), spMap T.subtype ≫ b = p.g.b.left → b ≫ D.P.A.hom = spMap φ₁ → ∀ χ, ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal p.g χ (closedPoint F) J) : F) ^ k = ((u : T) : F) := by
  first | exact @GlobalTheory.UnramCharPow.charVal_pow_unit | exact GlobalTheory.UnramCharPow.charVal_pow_unit | (intros; apply GlobalTheory.UnramCharPow.charVal_pow_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiValueIsUnitOfPsiUnitOnLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiValueIsUnitOfPsiUnitOnLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.PsiValUnit
open GlobalTheory.BXOf

theorem psi_val_unit_of_psiUnitOn : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens) (χ : D.X), PsiUnitOn D χ W → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → spMap φ₁ (closedPoint T) ∈ W → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (val (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J) : F) = ((u : T) : F) := by
  intro R _ _ D W χ hW F _ _ T _ φ₁ hφ hP J₀ h₀ J hJ
  have hmem : spMap φ₁ (closedPoint T) ∈ W ⊓ (D.c χ).left ⁻¹ᵁ D.P.L.U (J₀ ((D.c χ).left (spMap φ₁ (closedPoint T)))) :=
    ⟨hP, h₀ _⟩
  obtain ⟨V, hVa, hPV, hVle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Sp R).isBasis_affineOpens) hmem
  set j₀ := J₀ ((D.c χ).left (spMap φ₁ (closedPoint T))) with hj₀
  have hxK : D.xK χ = jK R ≫ (D.c χ).left := by
    show (toUnit (TK R) ≫ D.c χ).left = _
    rw [Over.comp_left]
    congr 1
  have hwch : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U (fun _ => j₀) :=
    fun x hx => Set.mem_iInter.2 fun _ => by
      show D.xK χ x ∈ D.P.L.U j₀
      rw [hxK]
      exact (hVle hx).2
  obtain ⟨r, hr, hre⟩ := hW (fun _ => j₀) V hVa (fun x hx => (hVle hx).1) (fun x hx => (hVle hx).2) hwch
  have hcomp : ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ jK R = spMap T.subtype ≫ spMap φ₁ := by
    rw [Over.id_left, Category.id_comp]
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext hφ).symm
  have hch : J (((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ D.xK χ) = j₀ := by
    have e : ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ D.xK χ = spMap T.subtype ≫ (spMap φ₁ ≫ (D.c χ).left) := by
      rw [hxK, ← Category.assoc, hcomp, Category.assoc]
    rw [e, hJ]
    rfl
  have e1 := val_of (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J (fun _ => j₀) (fun _ => hch)
  have hin : jK R (((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F)) ∈ V := by
    show (((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ jK R) (closedPoint F) ∈ V
    rw [hcomp]
    exact top_le_of_mem (spMap φ₁) hPV trivial
  have e2 : res hwch ((D.psi χ).s fun _ => j₀) = pullU (jK R) V hr.unit := Units.ext hre.symm
  have e3 := gm_res ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) hwch hin ((D.psi χ).s fun _ => j₀)
  rw [e2, gm_pull ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (jK R) (closedPoint F) V hin hr.unit, hcomp] at e3
  have e4 := sig_nat T.subtype (spMap φ₁) hPV hr.unit
  refine ⟨sig T (gm (spMap φ₁) (closedPoint T) V hr.unit), ?_⟩
  exact (congrArg (fun u => (sig F u : F)) (e1.trans e3.symm)).trans (congrArg Units.val e4).symm

end GlobalTheory.PsiValUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiValueIsUnitOfPsiUnitOnLocalRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiValue_isUnit_of_psiUnitOn_localRing : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens) (χ : D.X), PsiUnitOn D χ W → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → spMap φ₁ (closedPoint T) ∈ W → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (val (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J) : F) = ((u : T) : F) := by
  first | exact @GlobalTheory.PsiValUnit.psi_val_unit_of_psiUnitOn | exact GlobalTheory.PsiValUnit.psi_val_unit_of_psiUnitOn | (intros; apply GlobalTheory.PsiValUnit.psi_val_unit_of_psiUnitOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPointsFiniteRepresentatives
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPointsFiniteRepresentatives
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum

theorem qkPt_finite_reps : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), k ≠ 0 → Finite {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} → ∃ Rep : Set (QkPt D F k), Rep.Finite ∧ ∀ p : QkPt D F k, ∃ p' ∈ Rep, ∃ (z : D.X) (t : GtPtF D F), t.b = 1 ∧ (letI := GlobalTheory.TorusExt.gtGroup D F; k • t = 0 ∧ p.g = p'.g + GlobalTheory.TorusExt.iota hB F z + t) := by
  intro R _ _ D hB F _ _ k hk hfin
  letI := GlobalTheory.TorusExt.gtGroup D F
  classical
  by_cases hne : Nonempty (QkPt D F k)
  swap
  · exact ⟨∅, Set.finite_empty, fun p => (hne ⟨p⟩).elim⟩
  let K : AddSubgroup D.X := (nsmulAddMonoidHom (α := D.X) k).range
  haveI : K.FiniteIndex := ⟨by
    simp only [K, AddSubgroup.index_range_nsmul]; exact pow_ne_zero _ hk⟩
  haveI : Finite (D.X ⧸ K) := AddSubgroup.finite_quotient_of_finiteIndex
  let Q : QkPt D F k → D.X ⧸ K := fun p => (p.y : D.X ⧸ K)
  let bp : D.X ⧸ K → QkPt D F k := Function.invFun Q
  have hbp : ∀ p, Q (bp (Q p)) = Q p := fun p => Function.invFun_eq ⟨p, rfl⟩
  have hz : ∀ p, ∃ z : D.X, k • z = -(bp (Q p)).y + p.y := by
    intro p
    have h := QuotientAddGroup.eq.mp (hbp p)
    obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.mp h
    exact ⟨z, by simpa using hz⟩
  let zOf : QkPt D F k → D.X := fun p => (hz p).choose
  have hzOf : ∀ p, k • zOf p = -(bp (Q p)).y + p.y := fun p => (hz p).choose_spec
  let δ : QkPt D F k → GtPtF D F := fun p =>
    p.g - (bp (Q p)).g - GlobalTheory.TorusExt.iota hB F (zOf p)
  have hδk : ∀ p, k • δ p = 0 := by
    intro p
    simp only [δ, smul_sub, GlobalTheory.TorusExt.qk_nsmul hB, ← map_nsmul, hzOf]
    rw [map_add (f := _), map_neg]; abel
  have hδb : ∀ p, (δ p).b ^ k = 1 := by
    intro p
    rw [← GlobalTheory.TorusExt.nsmul_b, hδk p, GlobalTheory.TorusExt.zero_b]
  let Φ : QkPt D F k → (D.X ⧸ K) × {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} :=
    fun p => (Q p, ⟨(δ p).b, hδb p⟩)
  let rep : (D.X ⧸ K) × {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} → QkPt D F k :=
    Function.invFun Φ
  have hrep : ∀ p, Φ (rep (Φ p)) = Φ p := fun p => Function.invFun_eq ⟨p, rfl⟩
  refine ⟨Set.range (rep ∘ Φ), ?_, ?_⟩
  · rw [Set.range_comp]; exact (Set.toFinite _).image _
  intro p
  set p' := rep (Φ p) with hp'
  have h1 : Q p' = Q p := congrArg Prod.fst (hrep p)
  have h2 : (δ p').b = (δ p).b := congrArg (fun x => x.2.1) (hrep p)
  refine ⟨p', ⟨p, rfl⟩, zOf p - zOf p', δ p - δ p', ?_, ?_, ?_⟩
  · rw [sub_eq_add_neg, GlobalTheory.TorusExt.add_b, GlobalTheory.TorusExt.neg_b, h2, mul_inv_cancel]
  · rw [smul_sub, hδk, hδk, sub_zero]
  · have hb : bp (Q p') = bp (Q p) := by rw [h1]
    simp only [δ, hb, map_sub]
    abel

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPointsFiniteRepresentativesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientPoints_finite_representatives : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), k ≠ 0 → Finite {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} → ∃ Rep : Set (QkPt D F k), Rep.Finite ∧ ∀ p : QkPt D F k, ∃ p' ∈ Rep, ∃ (z : D.X) (t : GtPtF D F), t.b = 1 ∧ (letI := GlobalTheory.TorusExt.gtGroup D F; k • t = 0 ∧ p.g = p'.g + GlobalTheory.TorusExt.iota hB F z + t) := by
  first | exact @GlobalTheory.Mum.qkPt_finite_reps | exact GlobalTheory.Mum.qkPt_finite_reps | (intros; apply GlobalTheory.Mum.qkPt_finite_reps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointCharacterValuesFixedLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointCharacterValuesFixedLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.CharValsFixed

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt GlobalTheory.BXOf GlobalTheory.UnramTorsion

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → ∀ (σ : F →+* F), (∀ t ∈ T, σ t = t) → ∀ (g : GtPtF D F) (b : Sp T ⟶ D.P.A.left), spMap T.subtype ≫ b = g.b.left → b ≫ D.P.A.hom = spMap φ₁ → ∀ (S : Set D.X), AddSubgroup.closure S = ⊤ → (∀ χ ∈ S, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F)) → ∀ χ, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) := by
  intro R _ _ D F _ _ T _ φ₁ hφ₁ J₀ h₀ J hJ eJ σ hσ g b hb hbA S hS hSfix
  let ρ : TF (R := R) F ⟶ Over.mk (spMap φ₁) := Over.homMk (spMap T.subtype) (by
    show spMap T.subtype ≫ spMap φ₁ = jFK (R := R) F ≫ jK R
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ₁)
  let w : ((TF (R := R) F).left.presheaf.stalk (closedPoint F))ˣ →* Fˣ :=
    (Units.map σ.toMonoidHom).comp (sig F) * (sig F)⁻¹
  have hwv : ∀ u, ((w u : Fˣ) : F) = σ (sig F u : F) * ((sig F u)⁻¹ : Fˣ) := fun u => rfl
  have hw1 : ∀ u, w u = 1 ↔ σ (sig F u : F) = (sig F u : F) := fun u => by
    constructor
    · intro h
      have e := congrArg Units.val h
      rw [hwv, Units.val_one] at e
      calc σ (sig F u : F) = σ (sig F u : F) * ((sig F u)⁻¹ : Fˣ) * (sig F u : F) := by
            rw [_root_.mul_assoc, Units.inv_mul, _root_.mul_one]
        _ = (sig F u : F) := by rw [e, _root_.one_mul]
    · intro h
      apply Units.ext
      rw [hwv, h, Units.mul_inv, Units.val_one]
  have hw : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ D.P.A.left)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : (Over.mk (spMap φ₁)).left ⟶ Y),
      w (val t (ρ.left ≫ r) (closedPoint F) J) = 1 := by
    intro Y K _ φ ε t r
    obtain ⟨u, hu⟩ := val_integral T.subtype h₀ eJ t r
    refine (hw1 _).2 ?_
    have hu' : (sig F (val t (ρ.left ≫ r) (closedPoint F) J) : F) = T.subtype u := hu
    rw [hu']
    exact hσ _ (u : T).2
  let b' : Over.mk (spMap φ₁) ⟶ D.P.A := Over.homMk b hbA
  have hgb : g.b = ρ ≫ b' := by
    ext1
    exact hb.symm
  have hth : ∀ χ χ', w (th D (closedPoint F) J (cP D _ χ) (cP D _ χ') g.b) = 1 := fun χ χ' => by
    rw [hgb, ← comp_cP D ρ χ, ← comp_cP D ρ χ']
    exact w_th ρ w hw _ _ _
  let H : AddSubgroup D.X :=
    { carrier := {χ | w (charVal g χ (closedPoint F) J) = 1}
      zero_mem' := by
        show w _ = 1
        rw [charVal_zero g hJ, map_one]
      add_mem' := fun {χ χ'} (h : w _ = 1) (h' : w _ = 1) => by
        show w _ = 1
        have e := congrArg w (charVal_add g hJ χ χ')
        rw [map_mul, map_mul, hth, h, h', _root_.mul_one, _root_.mul_one] at e
        exact e
      neg_mem' := fun {χ} (h : w _ = 1) => by
        show w _ = 1
        have e := congrArg w (charVal_add g hJ χ (-χ))
        rw [map_mul, map_mul, hth, h, _root_.mul_one, _root_.one_mul, add_neg_cancel, charVal_zero g hJ,
          map_one] at e
        exact e.symm }
  have hSH : S ⊆ H := fun χ hχ => (hw1 _).2 (hSfix χ hχ)
  have hH : H = ⊤ := eq_top_iff.2 (hS ▸ (AddSubgroup.closure_le H).2 hSH)
  intro χ
  exact (hw1 _).1 (show χ ∈ H by rw [hH]; trivial)

end GlobalTheory.CharValsFixed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointCharacterValuesFixedLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtensionPoint_characterValues_fixed_local : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → ∀ (σ : F →+* F), (∀ t ∈ T, σ t = t) → ∀ (g : GtPtF D F) (b : Sp T ⟶ D.P.A.left), spMap T.subtype ≫ b = g.b.left → b ≫ D.P.A.hom = spMap φ₁ → ∀ (S : Set D.X), AddSubgroup.closure S = ⊤ → (∀ χ ∈ S, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F)) → ∀ χ, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) := by
  first | exact @GlobalTheory.CharValsFixed.main | exact GlobalTheory.CharValsFixed.main | (intros; apply GlobalTheory.CharValsFixed.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedDvrAdjoiningUnitRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedDvrAdjoiningUnitRoots
open IsLocalRing Polynomial

namespace GlobalTheory.KummerUnram

theorem etale_adjoinRoot_pow_sub {R : Type} [CommRing R] [Nontrivial R] {k : ℕ} (hk : IsUnit (k : R)) (u : Rˣ) :
    Algebra.Etale R (AdjoinRoot (X ^ k - C (u : R))) := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (M₀ := R) (by simpa using hk)
  have hm : (X ^ k - C (u : R)).Monic := monic_X_pow_sub_C _ hk0
  have h1 : AdjoinRoot.root (X ^ k - C (u : R)) ^ k = algebraMap R _ (u : R) := by
    have := AdjoinRoot.eval₂_root (X ^ k - C (u : R))
    simpa [sub_eq_zero] using this
  have hr : IsUnit (AdjoinRoot.root (X ^ k - C (u : R))) :=
    (isUnit_pow_iff hk0).1 (h1 ▸ (u.isUnit.map _))
  let P : StandardEtalePair R := ⟨X ^ k - C (u : R), hm, derivative (X ^ k - C (u : R)), 1, 0, 1, by simp⟩
  have h : IsUnit (AdjoinRoot.mk (X ^ k - C (u : R)) (derivative (X ^ k - C (u : R)))) := by
    have e : AdjoinRoot.mk (X ^ k - C (u : R)) (derivative (X ^ k - C (u : R))) =
        algebraMap R _ (k : R) * AdjoinRoot.root _ ^ (k - 1) := by
      simp [derivative_X_pow, AdjoinRoot.algebraMap_eq]
    rw [e]
    exact (hk.map _).mul (hr.pow _)
  exact .of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit _ (Localization.Away (AdjoinRoot.mk _ (derivative (X ^ k - C (u : R))))) _
      h).symm.restrictScalars R))

end GlobalTheory.KummerUnram

namespace GlobalTheory.KummerUnram

theorem exists_root_step {F : Type} [Field F] [IsAlgClosed F] (T : Subring F)
    [IsDiscreteValuationRing T] {k : ℕ} (hk : IsUnit (k : T)) (u : Tˣ)
    (ub : AlgebraicClosure (ResidueField T)) (hub : ub ^ k = algebraMap _ _ (residue T u)) :
    ∃ T' : Subring F, UnramSub T.subtype T' ∧ ∃ y ∈ T', y ^ k = ((u : T) : F) ∧
      ∀ n : ℕ, ub ^ n ≠ 1 → y ^ n ≠ 1 := by
  have := etale_adjoinRoot_pow_sub hk u
  let ρ : T →+* AlgebraicClosure (ResidueField T) :=
    (algebraMap (ResidueField T) _).comp (residue T)
  let ε : AdjoinRoot (X ^ k - C (u : T)) →+* AlgebraicClosure (ResidueField T) :=
    AdjoinRoot.lift ρ ub (by simp [ρ, hub])
  have hερ : ε.comp (algebraMap T _) = ρ := by
    ext t
    simp [ε, AdjoinRoot.algebraMap_eq]
  have hε : IsLocalHom (ε.comp (algebraMap T (AdjoinRoot (X ^ k - C (u : T))))) := by
    rw [hερ]
    refine ⟨fun x hx => (IsLocalRing.residue_ne_zero_iff_isUnit x).1 fun h0 => ?_⟩
    simp [ρ, h0] at hx
  obtain ⟨B, _, _, _, ψ, ρ', j', -, h2, h3, h4, h5⟩ :=
    TorsionUnram.exists_local_of_etale ε hε T.subtype Subtype.val_injective
  obtain ⟨hD, f, hf, hirr⟩ := UnramSub.range (i := j') h3
  refine ⟨j'.range, ⟨hD, f.comp (ψ.comp (algebraMap T _)), fun v => ?_,
    fun π hπ => hirr _ (h5 π hπ)⟩, j' (ψ (AdjoinRoot.root _)), ⟨_, rfl⟩, ?_, fun n hn hy => hn ?_⟩
  · rw [RingHom.comp_apply, hf]
    exact congr($h4 v)
  · have h1 : AdjoinRoot.root (X ^ k - C (u : T)) ^ k = algebraMap T _ (u : T) := by
      have := AdjoinRoot.eval₂_root (X ^ k - C (u : T))
      simpa [sub_eq_zero] using this
    rw [← map_pow, ← map_pow, h1]
    exact congr($h4 (u : T))
  · have e1 : ψ (AdjoinRoot.root (X ^ k - C (u : T))) ^ n = 1 :=
      h3 (by rw [map_pow, hy, map_one])
    have e2 : ρ' (ψ (AdjoinRoot.root (X ^ k - C (u : T)))) = ub := by
      rw [← RingHom.comp_apply, h2]
      simp [ε]
    rw [← e2, ← map_pow, e1, map_one]

end GlobalTheory.KummerUnram

namespace GlobalTheory.KummerUnram

theorem exists_rootsOfUnity {F : Type} [Field F] [IsAlgClosed F] (T : Subring F)
    [IsDiscreteValuationRing T] {k : ℕ} (hk : IsUnit (k : T)) :
    ∃ T' : Subring F, UnramSub T.subtype T' ∧ ∀ z : F, z ^ k = 1 → z ∈ T' := by
  let ρ : T →+* AlgebraicClosure (ResidueField T) :=
    (algebraMap (ResidueField T) _).comp (residue T)
  have hkΩ : ((k : ℕ) : AlgebraicClosure (ResidueField T)) ≠ 0 := by
    simpa [ρ] using (hk.map ρ).ne_zero
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hkΩ)
  haveI : NeZero ((k : ℕ) : AlgebraicClosure (ResidueField T)) := ⟨hkΩ⟩
  obtain ⟨ub, hub⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ResidueField T)) k
  obtain ⟨T', hT', y, hyT, hy, hyn⟩ := exists_root_step T hk 1 ub (by simp [hub.pow_eq_one])
  have hy1 : y ^ k = 1 := by simpa using hy
  have hprim : IsPrimitiveRoot y k := IsPrimitiveRoot.mk_of_lt y hk0 hy1
    fun l hl hlk => hyn l (hub.pow_ne_one_of_pos_of_lt hl.ne' hlk)
  refine ⟨T', hT', fun z hz => ?_⟩
  haveI : NeZero k := ⟨hk0.ne'⟩
  obtain ⟨i, -, rfl⟩ := hprim.eq_pow_of_pow_eq_one hz
  exact pow_mem hyT i

end GlobalTheory.KummerUnram

namespace GlobalTheory


open KummerUnram in
theorem exists_unramSub_of_pow_eq_units : ∀ (F : Type) [Field F] [IsAlgClosed F] (T : Subring F) [IsDiscreteValuationRing T] (k : ℕ), IsUnit (k : T) → ∀ U : Set Tˣ, U.Finite → ∃ T' : Subring F, GlobalTheory.UnramSub T.subtype T' ∧ ∀ x : F, (∃ u ∈ U, x ^ k = ((u : T) : F)) → x ∈ T' := by
  intro F _ _ T _ k hk U hU
  obtain ⟨T₁, h₁, hroots⟩ := exists_rootsOfUnity T hk
  suffices key : ∃ T' : Subring F, UnramSub T.subtype T' ∧ T₁ ≤ T' ∧
      ∀ x : F, (∃ u ∈ U, x ^ k = ((u : T) : F)) → x ∈ T' by
    obtain ⟨T', h, -, h'⟩ := key
    exact ⟨T', h, h'⟩
  induction U, hU using Set.Finite.induction_on with
  | empty => exact ⟨T₁, h₁, le_rfl, by simp⟩
  | @insert a s _ _ ih =>
    obtain ⟨T', hT', hle, hmem⟩ := ih
    haveI := hT'.isDVR
    have hTT' : T ≤ T' := fun z hz => hT'.mem ⟨z, hz⟩
    let ι : T →+* T' := Subring.inclusion hTT'
    have hk' : IsUnit (k : T') := by simpa [ι] using hk.map ι
    let a' : T'ˣ := Units.map ι.toMonoidHom a
    have hk0 : k ≠ 0 := by rintro rfl; exact not_isUnit_zero (M₀ := T) (by simpa using hk)
    obtain ⟨ub, hub⟩ := IsAlgClosed.exists_pow_nat_eq
      (algebraMap (ResidueField T') (AlgebraicClosure (ResidueField T')) (residue T' a'))
      (Nat.pos_of_ne_zero hk0)
    obtain ⟨T'', hT'', y, hyT, hy, -⟩ := exists_root_step T' hk' a' ub hub
    have hy' : y ^ k = ((a : T) : F) := by simpa [a', ι] using hy
    have ha0 : ((a : T) : F) ≠ 0 := fun h => a.ne_zero (Subtype.ext h)
    have hy0 : y ≠ 0 := by rintro rfl; exact ha0 (by rw [← hy', zero_pow hk0])
    have hle' : T' ≤ T'' := UnramSub.le hT''
    refine ⟨T'', hT'.trans hT'', hle.trans hle', fun x ⟨u, hu, hx⟩ => ?_⟩
    rcases Set.mem_insert_iff.1 hu with rfl | hu
    · have hz : (x / y) ^ k = 1 := by rw [div_pow, hx, hy', div_self ha0]
      have : x = (x / y) * y := by field_simp
      rw [this]
      exact mul_mem (hle' (hle (hroots _ hz))) hyT
    · exact hle' (hmem x ⟨u, hu, hx⟩)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedDvrAdjoiningUnitRootsStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_dvr_adjoining_unit_roots : ∀ (F : Type) [Field F] [IsAlgClosed F] (T : Subring F) [IsDiscreteValuationRing T] (k : ℕ), IsUnit (k : T) → ∀ U : Set Tˣ, U.Finite → ∃ T' : Subring F, GlobalTheory.UnramSub T.subtype T' ∧ ∀ x : F, (∃ u ∈ U, x ^ k = ((u : T) : F)) → x ∈ T' := by
  first | exact @GlobalTheory.exists_unramSub_of_pow_eq_units | exact GlobalTheory.exists_unramSub_of_pow_eq_units | (intros; apply GlobalTheory.exists_unramSub_of_pow_eq_units <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairsFixedOverUnramifiedExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.UnramCharVals

attribute [local instance] GlobalTheory.TorusExt.gtGroup


open ReciprocityTheory.ChartRestriction.G.DVR in
theorem tor_charVal_pow : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (t : GtPtF D F) (k : ℕ), t.b = 1 → (letI := GlobalTheory.TorusExt.gtGroup D F; k • t = 0) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → ∀ χ, (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal t χ (closedPoint F) J) : F) ^ k = 1 := by
  intro R _ _ D F _ _ t k h1 hk J hJ χ
  letI := GlobalTheory.TorusExt.gtGroup D F
  have C : IsCub (th D (T := TF (R := R) F) (closedPoint F) J) := isCub_cubV D.cub hJ
  have key : ∀ i : ℕ, GlobalTheory.TorusExt.charVal (i • t) χ (closedPoint F) J = GlobalTheory.TorusExt.charVal t χ (closedPoint F) J ^ i := by
    intro i
    induction i with
    | zero => rw [zero_nsmul, GlobalTheory.TorusExt.zero_val χ hJ, pow_zero]
    | succ i ih =>
      have e := GlobalTheory.TorusExt.add_val (i • t) t χ hJ
      rw [h1, C.face₃, _root_.mul_one, ih] at e
      rw [succ_nsmul, e, pow_succ]
  have e := key k
  rw [hk, GlobalTheory.TorusExt.zero_val χ hJ] at e
  rw [← Units.val_pow_eq_pow_val, ← map_pow, ← e, map_one, Units.val_one]

theorem qk_fixed_of_unram : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (W : (Sp R).Opens), (∀ y, PsiUnitOn D.toPre y W) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → spMap φ (closedPoint V) ∈ W → ∀ [Algebra (FractionRing R) (AlgebraicClosure (FractionRing V))], (∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r))) → ∀ k : ℕ, IsUnit (k : V) → ∀ T₁ : Subring (AlgebraicClosure (FractionRing V)), GlobalTheory.UnramSub ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp (algebraMap V (FractionRing V))) T₁ → (∀ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, ∃ b : Sp T₁ ⟶ D.toPre.P.A.left, spMap T₁.subtype ≫ b = p.g.b.left) → ∃ T' : Subring (AlgebraicClosure (FractionRing V)), GlobalTheory.UnramSub T₁.subtype T' ∧ ∀ σ : (AlgebraicClosure (FractionRing V)) ≃+* (AlgebraicClosure (FractionRing V)), (∀ z ∈ T', σ z = z) → ∀ p q : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, QkExt σ.toRingHom p q → QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing V)) p q := by
  intro R _ _ _ _ D W hW V _ _ _ φ hV _ hcl _ hc k hk T₁ hT₁ hbs
  have hB := D.tau_bimult
  haveI : IsDiscreteValuationRing V := hV.1
  obtain ⟨hdvr, f, hf, hirr⟩ := id hT₁
  haveI := hdvr
  let φ₁ : R →+* T₁ := f.comp φ
  have hφ₁ : ∀ r, (φ₁ r : AlgebraicClosure (FractionRing V)) =
      algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) := fun r =>
    (hf _).trans (hc r).symm
  have hloc : IsLocalHom f := ⟨fun v hv => by
    by_contra h
    have hv0 : v ≠ 0 := by rintro rfl; rw [map_zero] at hv; exact not_isUnit_zero hv
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv0 hπ
    cases n with
    | zero => exact h (by simp)
    | succ n =>
      rw [map_mul, map_pow, pow_succ] at hv
      exact (hirr π hπ).not_isUnit (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hv))⟩
  have hcl' : spMap φ₁ (closedPoint T₁) ∈ W := by
    have e : spMap φ₁ = spMap f ≫ spMap φ := by
      show Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]; rfl
    have e' : spMap f (closedPoint T₁) = closedPoint V := PrimeSpectrum.ext (Ideal.ext fun r =>
      ⟨fun h e => h (e.map f), fun h e => h (isUnit_of_map_unit f r e)⟩)
    rw [e]
    show (spMap φ) ((spMap f) (closedPoint T₁)) ∈ W
    rw [e']
    exact hcl
  choose J₀ h₀ using fun x : D.toPre.P.A.left => exists_chart D.toPre.P.isLB x
  have := D.toPre.P.isAb.proper
  have : D.toPre.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.toPre.P.A.hom]; infer_instance⟩
  obtain ⟨J, hJ, eJ⟩ := GlobalTheory.UnramTorsion.exists_good_ext D.toPre.P.isLB T₁.subtype Subtype.val_injective J₀ h₀
  have hψ := fun χ => GlobalTheory.T.psiValue_isUnit_of_psiUnitOn_localRing R D.toPre W χ (hW χ) _ T₁ φ₁ hφ₁ hcl' J₀ h₀ J eJ
  have hbw : ∀ (x : TF (R := R) (AlgebraicClosure (FractionRing V)) ⟶ D.toPre.P.A) (b : Sp T₁ ⟶ D.toPre.P.A.left),
      spMap T₁.subtype ≫ b = x.left → b ≫ D.toPre.P.A.hom = spMap φ₁ := by
    intro x b hb
    have hd : IsDominant (spMap T₁.subtype) := by
      constructor
      exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
        (by rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]; exact bot_le)
    refine ext_of_isDominant (spMap T₁.subtype) ?_
    rw [← Category.assoc, hb, Over.w x]
    show jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R = spMap T₁.subtype ≫ spMap φ₁
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext hφ₁).symm
  choose bb hbb using hbs
  have hk0 : k ≠ 0 := by rintro rfl; exact not_isUnit_zero (M₀ := V) (by simpa using hk)
  have fin := GlobalTheory.T.finite_kTorsion_abelianPart_algClosed R D.toPre (AlgebraicClosure (FractionRing V)) k (Nat.one_le_iff_ne_zero.2 hk0)
  obtain ⟨Rep, hRepf, hRep⟩ := GlobalTheory.T.quotientPoints_finite_representatives R D.toPre hB (AlgebraicClosure (FractionRing V)) k hk0 fin
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := D.toPre.X)
  have hS : AddSubgroup.closure (s : Set D.toPre.X) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, hs]; rfl
  choose uu huu using fun (p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k) χ =>
    GlobalTheory.T.quotientPoint_characterValue_pow_isUnit R D.toPre hB _ T₁ φ₁ hφ₁ J₀ h₀ J hJ eJ hψ k p (bb p) (hbb p) (hbw _ _ (hbb p)) χ
  let U : Set T₁ˣ := insert 1 ((fun pc : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k × D.toPre.X => uu pc.1 pc.2) '' (Rep ×ˢ (s : Set D.toPre.X)))
  have hU : U.Finite := ((hRepf.prod s.finite_toSet).image _).insert 1
  have hkT : IsUnit (k : T₁) := by simpa using hk.map f
  obtain ⟨T', hT', hroot⟩ := GlobalTheory.T.exists_unramified_dvr_adjoining_unit_roots _ T₁ k hkT U hU
  refine ⟨T', hT', fun σ hσT' p q hq => ?_⟩
  have hσT : ∀ t ∈ T₁, σ t = t := fun t ht => hσT' t (hT'.le ht)
  have hσ : σ.toRingHom.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))) =
      algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => by
      show σ (algebraMap (FractionRing R) _ (algebraMap R _ r)) = algebraMap (FractionRing R) _ (algebraMap R _ r)
      rw [← hφ₁]; exact hσT _ (φ₁ r).2)
  have hsub : spMap σ.toRingHom ≫ spMap T₁.subtype = spMap T₁.subtype := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext t
    exact hσT t t.2
  have hfix : ∀ p' ∈ Rep, GlobalTheory.TorusExt.gtExt D.toPre σ.toRingHom hσ p'.g = p'.g := by
    intro p' hp'
    refine GlobalTheory.T.torusExtensionPoint_fixed_of_chartValues_fixed R D.toPre _ σ.toRingHom hσ p'.g ?_ J hJ ?_
    · rw [← hbb p', ← Category.assoc, hsub]
    · exact GlobalTheory.T.torusExtensionPoint_characterValues_fixed_local R D.toPre _ T₁ φ₁ hφ₁ J₀ h₀ J hJ eJ σ.toRingHom hσT p'.g (bb p') (hbb p') (hbw _ _ (hbb p')) _ hS
        (fun χ hχ => hσT' _ (hroot _ ⟨uu p' χ, Set.mem_insert_of_mem _ ⟨(p', χ), ⟨hp', hχ⟩, rfl⟩, huu p' χ⟩))
  have hfixt : ∀ t : GtPtF D.toPre (AlgebraicClosure (FractionRing V)), t.b = 1 → k • t = 0 →
      GlobalTheory.TorusExt.gtExt D.toPre σ.toRingHom hσ t = t := by
    intro t h1 hkt
    refine GlobalTheory.T.torusExtensionPoint_fixed_of_chartValues_fixed R D.toPre _ σ.toRingHom hσ t ?_ J hJ (fun χ => hσT' _ (hroot _ ⟨1, Set.mem_insert _ _, ?_⟩))
    · rw [h1]
      exact congrArg (fun q => q.left) (MonObj.comp_one (GlobalTheory.TorusExt.extMap (R := R) σ.toRingHom hσ) :
        GlobalTheory.TorusExt.extMap (R := R) σ.toRingHom hσ ≫ (1 : TF (R := R) _ ⟶ D.toPre.P.A) = 1)
    · rw [tor_charVal_pow R D.toPre _ t k h1 hkt J hJ χ]; simp
  obtain ⟨p', hp', z, t, h1, hkt, hpg⟩ := hRep p
  have hg : GlobalTheory.TorusExt.gtExt D.toPre σ.toRingHom hσ p.g = p.g := by
    rw [hpg, map_add (f := _), map_add (f := _), hfix p' hp', GlobalTheory.TorusExt.gtExt_iota, hfixt t h1 hkt]
  have hq' := (GlobalTheory.TorusExt.qkExt_iff hB σ.toRingHom hσ p q).1 hq
  refine (GlobalTheory.TorusExt.equiv_iff hB p q).2 ⟨0, ?_, ?_⟩
  · rw [hq', smul_zero, add_zero]; rfl
  · rw [hq', map_zero, add_zero]; exact hg

end GlobalTheory.UnramCharVals
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairsFixedOverUnramifiedExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPairs_fixed_over_unramified_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (W : (Sp R).Opens), (∀ y, PsiUnitOn D.toPre y W) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → spMap φ (closedPoint V) ∈ W → ∀ [Algebra (FractionRing R) (AlgebraicClosure (FractionRing V))], (∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r))) → ∀ k : ℕ, IsUnit (k : V) → ∀ T₁ : Subring (AlgebraicClosure (FractionRing V)), GlobalTheory.UnramSub ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp (algebraMap V (FractionRing V))) T₁ → (∀ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, ∃ b : Sp T₁ ⟶ D.toPre.P.A.left, spMap T₁.subtype ≫ b = p.g.b.left) → ∃ T' : Subring (AlgebraicClosure (FractionRing V)), GlobalTheory.UnramSub T₁.subtype T' ∧ ∀ σ : (AlgebraicClosure (FractionRing V)) ≃+* (AlgebraicClosure (FractionRing V)), (∀ z ∈ T', σ z = z) → ∀ p q : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, QkExt σ.toRingHom p q → QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing V)) p q := by
  first | exact @GlobalTheory.UnramCharVals.qk_fixed_of_unram | exact GlobalTheory.UnramCharVals.qk_fixed_of_unram | (intros; apply GlobalTheory.UnramCharVals.qk_fixed_of_unram <;> assumption)
end
