module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerFixesVacuumLeft
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefOverOfFiniteOrbit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightPowerCm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionPullbackNaturality
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionPullbackNaturality
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem isObU_pull : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (u' : ∀ (T T' : C') (_ : T ⟶ T'), (F'.obj T')ˣ) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsLift L' n l → L.IsNat L' n l → (∀ T T' a, (u' T T' a : F'.obj T') = n.α T' (u _ _ (n.G.map a) : F.obj (n.G.obj T'))) → IsObU L α u c → IsObU L' α u' ((extMap R₁ n).pull2 c) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L C' _ F' L' n l u u' c hL hN hu hob
  obtain ⟨v, σ, z, hv, hσ, hc, hz⟩ := hob
  have hex : ∀ T, ∃ s : R₁ ⊗[R₀] F'.obj T →+ L'.B T, α.IsSig (L'.p T) s := fun T =>
    GlobalTheory.Obs.exists_isSig R R₀ I hI π hπ hk R₁ α (L'.B T) (F'.obj T) (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T)
  choose σ' hσ' using hex
  have hnat : ∀ T : C', (∀ y, l T (σ (n.G.obj T) y) = σ' T (extHom R₁ (coefHom n T) y)) ∧
      ∀ y, α.KerQ y → α.KerQ (extHom R₁ (coefHom n T) y) := fun T =>
    GlobalTheory.Obs.sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _)
      _ _ (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T) (l T) (coefHom n T) (fun b => hL T b) _ _ (hσ _) (hσ' T)
  refine ⟨fun T T' a => Units.map (l T').toRingHom.toMonoidHom (v _ _ (n.G.map a)), σ', (extMap R₁ n).pullbackTwoCocycle z,
    ?_, hσ', ?_, ?_⟩
  · intro T T' a
    change L'.p T' (l T' _) = _
    rw [hL, hv, hu]
  · rw [hc]; rfl
  · intro T T' T'' a b
    obtain ⟨hk1, hk2⟩ := hz _ _ _ (n.G.map a) (n.G.map b)
    refine ⟨(hnat T'').2 _ hk1, ?_⟩
    change L'.ρ b (l T' _) * l T'' _ = (1 + σ' T'' (extHom R₁ (coefHom n T'') _)) * l T'' _
    rw [hN, ← map_mul, hk2, map_mul, map_add (f := _), map_one, (hnat T'').1, Functor.map_comp]
    rfl

end GlobalTheory.LBObs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionPullbackNaturalityStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitCocycleLiftObstruction_pullback_naturality : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (u' : ∀ (T T' : C') (_ : T ⟶ T'), (F'.obj T')ˣ) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsLift L' n l → L.IsNat L' n l → (∀ T T' a, (u' T T' a : F'.obj T') = n.α T' (u _ _ (n.G.map a) : F.obj (n.G.obj T'))) → IsObU L α u c → IsObU L' α u' ((extMap R₁ n).pull2 c) := by
  first | exact @GlobalTheory.LBObs.isObU_pull | exact GlobalTheory.LBObs.isObU_pull | (intros; apply GlobalTheory.LBObs.isObU_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodLabRankOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Recog

variable {R : Type} [CommRing R] [IsDomain R]

structure GoodLab (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (f : ∀ k : ℕ, QkPt D F k → (TFK (R := R) F ⟶ A.A)) : Prop where
  pow : ∀ k, 1 ≤ k → ∀ p, f k p ^ k = 1
  onto : ∀ k, 1 ≤ k → ∀ x : TFK (R := R) F ⟶ A.A, x ^ k = 1 → ∃ p, f k p = x
  eqv : ∀ k, 1 ≤ k → ∀ p p', f k p = f k p' ↔ QkPt.Equiv D F p p'
  add : ∀ k, 1 ≤ k → ∀ p p' p'', QkAdd p p' p'' → f k p'' = f k p * f k p'
  weil : ∀ k, 1 ≤ k → ∀ p p' (z : Fˣ), WeilQkIs D F k p p' z → WeilIs A.A A.L k (f k p) (f k p') (unitOn z)
  level : ∀ k m N, 1 ≤ k → 1 ≤ m → N = k * m → ∀ (p : QkPt D F k) (q : QkPt D F N), q.y = m • p.y → q.g = p.g →
    f N q = f k p

def Lies {W : Type} [CommRing W] [IsDomain W] (φ : R →+* W) {D : DegPre R} {D' : DegPre W} (hD : IsPullDeg φ D D')
    {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F']
    [Algebra (FractionRing W) F'] (em : F →+* F') {k : ℕ} (p : QkPt D F k) (p' : QkPt D' F' k) : Prop :=
  ∃ p₁ : QkPt D F' k, QkExt em p p₁ ∧ p'.y = hD.xe.symm p₁.y ∧ IsPullGtF φ hD F' p₁.g p'.g

theorem exists_goodLab [CharZero R] {I : Ideal R} (hR : AdmBase R I) {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) (F : Type) [Field F]
    [IsAlgClosed F] [Algebra (FractionRing R) F] :
    ∃ f, GoodLab D.toPre A F f ∧ ∀ k, 1 ≤ k → ∀ p x, QkToAkU U.toUnifPre F k p x ↔ x = f k p := by
  have H : ∀ k : ℕ, ∃ f : QkPt D.toPre F k → (TFK (R := R) F ⟶ A.A), 1 ≤ k →
      GlobalTheory.UT.Tors U.toUnifPre F k f ∧ ∀ p, f p ^ k = 1 := fun k => by
    by_cases hk : 1 ≤ k
    · obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_clause R _ hR D A G hG U F k hk
      exact ⟨f, fun _ => hf⟩
    · exact ⟨fun _ => 1, fun h => absurd h hk⟩
  choose f hf using H
  refine ⟨f, ⟨fun k hk => (hf k hk).2, fun k hk => (hf k hk).1.2.1, fun k hk => (hf k hk).1.2.2.1,
    fun k hk => (hf k hk).1.2.2.2.1, fun k hk p p' z => ((hf k hk).1.2.2.2.2 p p' z).1, ?_⟩, fun k hk => (hf k hk).1.1⟩
  intro k m N hk hm hN p q hy hg
  have hN1 : 1 ≤ N := hN ▸ Nat.mul_pos hk hm
  exact (((hf N hN1).1.1 q _).1 (((GlobalTheory.LevelCompat.qkToAkU_level GlobalTheory.firstFiveLaws R _ hR D A G hG U F k m N hk hm hN p q
    (f k p)).1 hy hg).1 (((hf k hk).1.1 p _).2 rfl))).symm

end GlobalTheory.Mum.Recog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaTermsOfMulIndexZeroTermEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaTermsOfMulIndexZeroTermEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem isThetaTerms_of_mul_eq_one : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (N₁ : ℕ) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (T : X → C → V₁) (v : V₁) (c₀ : C), IsThetaTerms₀ D N₁ e T → T 0 c₀ * v = 1 → IsThetaTerms D N₁ e (fun mu c => T mu c * v) := by
  intro V₁ _ _ D N₁ X C _ e T v c₀ h hv
  obtain ⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨(algebraMap V₁ (FractionRing V₁) v) • th, g, b, w, h₁, h₂, h₃, h₄, ?_, ⟨c₀, hv⟩⟩
  intro mu c z J hJ
  have H := h₅ mu c z J hJ
  rw [ReciprocityTheory.ChartRestriction.G.DVR.sval_smul _ _ _ _ z hJ]
  have e₁ : (lift (𝟙 (TF (R := V₁) (FractionRing V₁))) (g c).b).left ≫
      (fst (TF (R := V₁) (FractionRing V₁)) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst, Over.id_left]
  rw [e₁]
  have e₂ : GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) (T mu c * v)) =
      GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) v) *
        GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) (T mu c)) := by
    simp only [GlobalTheory.UT.cst, map_mul]
    rw [gs_mul _ z ⊤ trivial, mul_comm]
  rw [e₂, _root_.mul_assoc, H]
  simp only [GlobalTheory.UT.cst, _root_.mul_assoc]

end GlobalTheory.Poinc.Sep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaTermsOfMulIndexZeroTermEqOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaTerms_of_mul_index_zero_term_eq_one : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (N₁ : ℕ) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (T : X → C → V₁) (v : V₁) (c₀ : C), IsThetaTerms₀ D N₁ e T → T 0 c₀ * v = 1 → IsThetaTerms D N₁ e (fun mu c => T mu c * v) := by
  first | exact @GlobalTheory.Poinc.Sep.isThetaTerms_of_mul_eq_one | exact GlobalTheory.Poinc.Sep.isThetaTerms_of_mul_eq_one | (intros; apply GlobalTheory.Poinc.Sep.isThetaTerms_of_mul_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeAutomorphismCongrOneModDetEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeAutomorphismCongrOneModDetEqOne
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem det_eq_one_of_congMod (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : X ≃+ X) (m : ℕ)
    (hm : 3 ≤ m) (hk : ∀ x, CongMod m (k x) x) :
    LinearMap.det (k.toIntLinearEquiv : X →ₗ[ℤ] X) = 1 := by
  set f : X ≃ₗ[ℤ] X := k.toIntLinearEquiv
  have hu : IsUnit (LinearMap.det (f : X →ₗ[ℤ] X)) := LinearEquiv.isUnit_det' f
  let b := Module.Free.chooseBasis ℤ X
  set M := LinearMap.toMatrix b b (f : X →ₗ[ℤ] X) with hM
  have hdet : M.det = LinearMap.det (f : X →ₗ[ℤ] X) := LinearMap.det_toMatrix b _
  have hmap : (Int.castRingHom (ZMod m)).mapMatrix M = 1 := by
    ext i j
    obtain ⟨w, hw⟩ := hk (b j)
    have hfb : (f : X →ₗ[ℤ] X) (b j) = k (b j) := rfl
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hM, LinearMap.toMatrix_apply, hfb, hw, map_add (f := _), map_nsmul,
      Finsupp.add_apply, Finsupp.smul_apply, b.repr_self, Finsupp.single_apply, Matrix.one_apply]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]
  have hz : ((LinearMap.det (f : X →ₗ[ℤ] X) : ℤ) : ZMod m) = 1 := by
    rw [← hdet]
    have := RingHom.map_det (Int.castRingHom (ZMod m)) M
    rw [hmap, Matrix.det_one] at this
    simpa using this
  rcases Int.isUnit_iff.mp hu with h | h
  · exact h
  · exfalso
    rw [h] at hz
    have h2 : ((2 : ℕ) : ZMod m) = 0 := by
      have e : ((2 : ℕ) : ZMod m) = 1 - ((-1 : ℤ) : ZMod m) := by push_cast; ring
      rw [e, hz, sub_self]
    have hd := (ZMod.natCast_eq_zero_iff 2 m).mp h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeAutomorphismCongrOneModDetEqOneStatement
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_automorphism_congr_one_mod_det_eq_one : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : X ≃+ X) (m : ℕ), 3 ≤ m → (∀ x, CongMod m (k x) x) → LinearMap.det (k.toIntLinearEquiv : X →ₗ[ℤ] X) = 1 := by
  first | exact @GlobalTheory.Poinc.det_eq_one_of_congMod | exact GlobalTheory.Poinc.det_eq_one_of_congMod | (intros; apply GlobalTheory.Poinc.det_eq_one_of_congMod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricOfLineBundleIsoPullGroupHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricOfLineBundleIsoPullGroupHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem sym_of_lbIso_pull_hom : ∀ (S : Scheme.{0}) (H H' : Over S) [GrpObj H] [GrpObj H'] (f : H ⟶ H'), IsMonHom f →
    ∀ (N : LB H'.left) (M : LB H.left), N.IsLB → M.IsLB → Out.Sym H' N → LBIso (N.pull f.left) M → Out.Sym H M := by
  intro S H H' _ _ f hf N M hN hM hs hiso s
  obtain ⟨U, hU, t, ht⟩ := hs s
  refine ⟨U, hU, ?_⟩
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  have hw' := (isGen_iff w).1 hw
  obtain ⟨n, hn⟩ : ∃ n : (H.hom ⁻¹ᵁ U).toScheme ⟶ (H'.hom ⁻¹ᵁ U).toScheme,
      n ≫ (H'.hom ⁻¹ᵁ U).ι = (H.hom ⁻¹ᵁ U).ι ≫ f.left :=
    ⟨IsOpenImmersion.lift _ ((H.hom ⁻¹ᵁ U).ι ≫ f.left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y.1 ∈ U) (Over.w f)).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
  have hi : (GrpObj.inv : H ⟶ H).left ≫ f.left = f.left ≫ (GrpObj.inv : H' ⟶ H').left :=
    congrArg (fun q => q.left) (GrpObj.inv_hom f)
  let ψ : Fin 2 → ((H.hom ⁻¹ᵁ U).toScheme ⟶ H.left) :=
    ![(H.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : H ⟶ H).left, (H.hom ⁻¹ᵁ U).ι]
  obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame N (fun k => ψ k ≫ f.left) _ ![1, -1] n (fun k => by
    fin_cases k
    · show ((H.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : H ⟶ H).left) ≫ f.left =
        n ≫ (H'.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : H' ⟶ H').left
      rw [← Category.assoc n, hn, Category.assoc, Category.assoc, hi]
    · show (H.hom ⁻¹ᵁ U).ι ≫ f.left = n ≫ (H'.hom ⁻¹ᵁ U).ι
      rw [hn])) t ht
  exact exists_down hw' hN hM (φ' := ψ) c₂ h₂

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricOfLineBundleIsoPullGroupHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_of_lineBundleIso_pull_groupHom : ∀ (S : Scheme.{0}) (H H' : Over S) [GrpObj H] [GrpObj H'] (f : H ⟶ H'), IsMonHom f → ∀ (N : LB H'.left) (M : LB H.left), N.IsLB → M.IsLB → Out.Sym H' N → LBIso (N.pull f.left) M → Out.Sym H M := by
  first | exact @GlobalTheory.sym_of_lbIso_pull_hom | exact GlobalTheory.sym_of_lbIso_pull_hom | (intros; apply GlobalTheory.sym_of_lbIso_pull_hom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumCompatibleOfLineBundleIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumCompatibleOfLineBundleIso
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBDescent

theorem descCompat_of_lbIso : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X), L.IsLB →
    LBIso (L.pull (pullback.fst f f)) (L.pull (pullback.snd f f)) →
    ∃ φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ, DescCompat f L φ := by
  intro X Y f L hL hI
  obtain ⟨w, hw⟩ := hI
  have hP := (isGen_iff w).1 hw
  have hle : ∀ i j, chart f L i j ≤ (L.pull (pullback.snd f f)).U (fun _ => j) ⊓ (L.pull (pullback.fst f f)).U (fun _ => i) :=
    fun i j z hz => ⟨mem_pull.2 hz.2, mem_pull.2 hz.1⟩
  refine ⟨fun i j => res (hle i j) (w.s (fun _ => j, fun _ => i)), ?_⟩
  intro z i i' j j' hi hi' hj hj'
  have hc : ∀ a b, pullback.fst f f z ∈ L.U a → pullback.snd f f z ∈ L.U b →
      gm (𝟙 _) z (chart f L a b) (res (hle a b) (w.s (fun _ => b, fun _ => a))) =
        gw w (𝟙 _) z b (fun _ => a) := fun a b ha hb =>
    gm_res (𝟙 _) z (hle a b) ⟨ha, hb⟩ _
  have key := hP _ (𝟙 _) z j' j (fun _ => i') (fun _ => i) hj' hj (mem_pull.2 hi') (mem_pull.2 hi)
  have e1 : gm (𝟙 _) z _ ((L.pull (pullback.fst f f)).g (fun _ => i') (fun _ => i)) =
      gm (pullback.fst f f) z _ (L.g i' i) := by
    have := gm_pull_g L (pullback.fst f f) (𝟙 _) z (fun _ => i') (fun _ => i) (mem_pull.2 hi') (mem_pull.2 hi)
    rw [Category.id_comp] at this
    exact this
  have e2 : (gm (pullback.fst f f) z _ (L.g i' i))⁻¹ = gm (pullback.fst f f) z _ (L.g i i') := by
    rw [inv_eq_iff_mul_eq_one, gm_cocycle hL _ z hi' hi hi', gm_self hL _ z hi']
  rw [Category.id_comp, e1, e2] at key
  rw [hc i' j' hi' hj', hc i j hi hj, key]
  ac_rfl

end GlobalTheory.LBDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumCompatibleOfLineBundleIsoStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descentDatumCompatible_of_lineBundle_iso : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X), L.IsLB → LBIso (L.pull (pullback.fst f f)) (L.pull (pullback.snd f f)) → ∃ φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ, DescCompat f L φ := by
  first | exact @GlobalTheory.LBDescent.descCompat_of_lbIso | exact GlobalTheory.LBDescent.descCompat_of_lbIso | (intros; apply GlobalTheory.LBDescent.descCompat_of_lbIso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatLocalBaseChangeOfProperProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatLocalBaseChangeOfProperProperties
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem finiteFlat_proper_baseChange_facts : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] (ρ : R →+* R'), Function.Injective ρ → ρ.Finite → ρ.Flat → ∀ (Z Y Z' Y' : Scheme.{0}) (p : Z ⟶ Y) (p' : Z' ⟶ Y') (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (k : Y' ⟶ Y) (k' : Z' ⟶ Z), IsPullback k y' y (spMap ρ) → IsPullback k' p' p k → IsProper p → IsFinite k ∧ QuasiCompact p' ∧ QuasiSeparated p' ∧ Function.Surjective k'.base ∧ IsClosedMap (p' ≫ k).base ∧ IsClosedMap p.base ∧ (∀ V : Y.Opens, IsAffineOpen V → IsCompact (p ⁻¹ᵁ V : Set Z) ∧ IsQuasiSeparated (p ⁻¹ᵁ V : Set Z)) ∧ ∃ (d : ℕ) (b : Fin d → R'), ∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, ρ (c l) * b l := by
  intro R R' _ _ _ _ ρ hinj hfin hflat Z Y Z' Y' p p' y y' k k' hk hk' hp
  have h1 : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).mpr hfin
  have h2 : IsFinite k := MorphismProperty.of_isPullback (P := @IsFinite) hk.flip h1
  have h3 : IsProper p' := MorphismProperty.of_isPullback (P := @IsProper) hk' hp
  have h4 : Surjective (spMap ρ) :=
    ⟨RingHom.IsIntegral.comap_surjective hfin.to_isIntegral hinj⟩
  have h5 : Surjective k := MorphismProperty.of_isPullback (P := @Surjective) hk.flip h4
  have h6 : Surjective k' := MorphismProperty.of_isPullback (P := @Surjective) hk'.flip h5
  refine ⟨h2, inferInstance, inferInstance, h6.surj, (p' ≫ k).isClosedMap, p.isClosedMap, ?_, ?_⟩
  · intro V hV
    refine ⟨QuasiCompact.isCompact_preimage (f := p) _ V.isOpen hV.isCompact, ?_⟩
    haveI : IsAffine V := hV
    haveI : QuasiSeparatedSpace (p ⁻¹ᵁ V : Z.Opens).toScheme :=
      quasiSeparatedSpace_of_quasiSeparated (p ∣_ V)
    exact (isQuasiSeparated_iff_quasiSeparatedSpace _ (p ⁻¹ᵁ V).isOpen).mpr this
  · letI := ρ.toAlgebra
    haveI : Module.Finite R R' := hfin
    haveI : Module.Flat R R' := hflat
    haveI : Module.Free R R' := Module.free_of_flat_of_isLocalRing
    let b := Module.finBasis R R'
    refine ⟨_, b, fun r' => ⟨b.repr r', ?_, ?_⟩⟩
    · exact (b.sum_repr r').symm
    · intro c hc
      have : r' = ∑ l, c l • b l := hc
      rw [this, b.repr_sum_self]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatLocalBaseChangeOfProperPropertiesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_flat_local_baseChange_of_proper_properties : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] (ρ : R →+* R'), Function.Injective ρ → ρ.Finite → ρ.Flat → ∀ (Z Y Z' Y' : Scheme.{0}) (p : Z ⟶ Y) (p' : Z' ⟶ Y') (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (k : Y' ⟶ Y) (k' : Z' ⟶ Z), IsPullback k y' y (spMap ρ) → IsPullback k' p' p k → IsProper p → IsFinite k ∧ QuasiCompact p' ∧ QuasiSeparated p' ∧ Function.Surjective k'.base ∧ IsClosedMap (p' ≫ k).base ∧ IsClosedMap p.base ∧ (∀ V : Y.Opens, IsAffineOpen V → IsCompact (p ⁻¹ᵁ V : Set Z) ∧ IsQuasiSeparated (p ⁻¹ᵁ V : Set Z)) ∧ ∃ (d : ℕ) (b : Fin d → R'), ∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, ρ (c l) * b l := by
  first | exact @GlobalTheory.finiteFlat_proper_baseChange_facts | exact GlobalTheory.finiteFlat_proper_baseChange_facts | (intros; apply GlobalTheory.finiteFlat_proper_baseChange_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatWFgPow
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.ShiftFG

theorem exists_good_cmPt_frame_ne_zero {D : D7} {T : Core D} {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (hG : Y.Good e o)
    [StarRing (𝓞 D.host.E)] (hstar : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) (G : WTZ D.host.E)
    (F : Rul Y.d.Xo₂ Y.d.c₂) (hF : F ∈ Y.V G) (hF0 : F ≠ 0) :
    ∃ (z : CMPt Y.d.Xo₂ Y.d.c₂) (La : ℝ) (y : FrPt Y.d.Xo₂ Y.d.c₂ z.K),
      z.Good (Module.finrank ℚ D.host.E / 2) La ∧ y.x = z.x ∧ evR Y.d.Xo₂ Y.d.c₂ F y ≠ 0 := by
  classical
  have hσ : GoodEmb Y.d.c₂ Y.d.c₂.F.val.toRingHom := rfl
  have hU := hG.unf _ hσ
  have hFm := GlobalTheory.AllWt.mem_cuspW.1 hF
  obtain ⟨k, x₁, hx₁, hne₁⟩ := GlobalTheory.T.exists_uniformisationFrame_reading_ne_zero _ _ _ _ _ _ _ _ _ hU _ F hFm.1 hF0
  obtain ⟨Xx, 𝔄, hX, h𝔄, hΛ⟩ := GlobalTheory.T.goodCover_component_extends_to_rankOne_cusp_data D T j Y e o hG _ hσ k
  have hbdd := (Formalism.L2.Pj.abelian₂.holSub_SS ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds _ _ (hFm.2 _ hσ) k).1
  have hr : 0 < D.R.r := by
    have hn : 0 < D.R.ord := D.R.ord_pos
    have hk := D.R.f_le_k
    have ht := D.R.rank_add_five_le
    unfold Ranks.r; omega
  obtain ⟨La, x, lam, hx, hB, hne⟩ := GlobalTheory.CMDetect.exists_cm_frame Xx _ hX hr _ _ hbdd hx₁ hne₁
  obtain ⟨z, σ₁, hz, hzx⟩ := GlobalTheory.LamT.exists_good_cmPt_at_frame _ _ _ _ _ _ hstar _ _ hU hr k ⟨x, hx⟩ Xx hX 𝔄 h𝔄 hΛ
    La lam hB
  have hev : evR Y.d.Xo₂ Y.d.c₂ F ((Y.U _).un k ⟨x, hx⟩) ≠ 0 := by
    intro h0
    apply hne
    change (if h : x ∈ ((Y.U _).X k).dom then toC (evR Y.d.Xo₂ Y.d.c₂ F ((Y.U _).un k ⟨x, h⟩)) else 0) = 0
    rw [dite_eq_left hx]
    exact h0
  obtain ⟨y, hy, hyne⟩ := GlobalTheory.T.exists_numberFieldFrame_value_ne_zero_of_complex _ _ _ _ _ _ z.K z.y _ F hFm.1 _ σ₁ _ hzx hev
  exact ⟨z, La, y, hz, hy.trans hz.2.2.2.1, hyne⟩


end GlobalTheory.CovTop.ShiftFG

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureRationalThetaPointSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureRationalThetaPointSubfield
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ThetaDescentLevel

theorem isThetaPt_reindex {S : Scheme.{0}} {P : PolAV S} {k : ℕ} {T : Over S} {I I' : Type}
    {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P k x v) (f : I' → I) :
    IsThetaPt P k (fun i => x (f i)) fun i => v (f i) := by
  refine ⟨H.1, H.2.1, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := H.2.2 p
  exact ⟨V, hV, th, s1, α, τ, fun i => U (f i), fun i => s2 (f i), fun i => w (f i), u, a1, a2, a3, a4,
    fun i => a5 _, fun i => a6 _, fun i => a7 _, fun i => a8 _⟩

theorem exists_level : ∀ (F Ω : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] (em : F →+* Ω) (A : PolAV (Sp Ω)) (n J : ℕ), n.Prime → 1 ≤ J → ∀ (Ix : Type) (x : Ix → (baseOver (Sp Ω) ⟶ A.A)) (v : Ix → F), (∀ z : baseOver (Sp Ω) ⟶ A.A, z ^ ((n ^ J) ^ 2) = 1 → ∃ i, x i = z) → IsThetaPt A (n ^ J) x (fun i => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v i))) → ∃ (ζ : Fˣ) (lev : Level A ((n ^ J) ^ 2) (unitOn (Units.map em.toMonoidHom ζ))) (v' : (Fin (2 * A.g) → ZMod ((n ^ J) ^ 2)) → F), IsPrimitiveRoot ζ ((n ^ J) ^ 2) ∧ IsThetaPt A (n ^ J) (GlobalTheory.levelPoint lev rfl) (fun a => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v' a))) := by
  intro F Ω _ _ _ _ _ em A n J hn _ Ix x v hx hv
  have hF : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn.ne_zero
  have hΩ : (n : Ω) ≠ 0 := by
    rw [← map_natCast em]
    exact (map_ne_zero _).2 hF
  have hlev := nonempty_level_prime_pow GlobalTheory.abelianSchemeLaws_all.1 Ω A n (J * 2) hn hΩ
  rw [pow_mul] at hlev
  have hM : (n ^ J) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)
  generalize n ^ J = m at *
  have : NeZero (m ^ 2) := ⟨hM⟩
  have : NeZero ((m ^ 2 : ℕ) : F) := ⟨Nat.cast_ne_zero.2 hM⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (m ^ 2)
  have hζ := hz.isUnit_unit (NeZero.ne _)
  generalize (hz.isUnit (NeZero.ne _)).unit = ζ at hζ
  have inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of Ω)).symm.commRingCatIsoToRingEquiv.injective
  have hζ' : IsPrimitiveRoot (Units.map em.toMonoidHom ζ) (m ^ 2) :=
    hζ.map_of_injective (Units.map_injective em.injective)
  obtain ⟨lev⟩ := hlev (unitOn (Units.map em.toMonoidHom ζ)) (hζ'.map_of_injective (Units.map_injective inj))
  choose i hi using fun a => hx _ (ThetaPtDet.levelPoint_pow lev rfl a)
  refine ⟨ζ, lev, fun a => v (i a), hζ, ?_⟩
  have h := isThetaPt_reindex hv i
  rwa [show (fun a => x (i a)) = GlobalTheory.levelPoint lev rfl from funext hi] at h

end GlobalTheory.ThetaDescentLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureRationalThetaPointSubfieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_structure_rational_thetaPoint_subfield : ∀ (F Ω : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] (em : F →+* Ω) (A : PolAV (Sp Ω)) (n J : ℕ), n.Prime → 1 ≤ J → ∀ (Ix : Type) (x : Ix → (baseOver (Sp Ω) ⟶ A.A)) (v : Ix → F), (∀ z : baseOver (Sp Ω) ⟶ A.A, z ^ ((n ^ J) ^ 2) = 1 → ∃ i, x i = z) → IsThetaPt A (n ^ J) x (fun i => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v i))) → ∃ (ζ : Fˣ) (lev : Level A ((n ^ J) ^ 2) (unitOn (Units.map em.toMonoidHom ζ))) (v' : (Fin (2 * A.g) → ZMod ((n ^ J) ^ 2)) → F), IsPrimitiveRoot ζ ((n ^ J) ^ 2) ∧ IsThetaPt A (n ^ J) (GlobalTheory.levelPoint lev rfl) (fun a => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v' a))) := by
  first | exact @GlobalTheory.ThetaDescentLevel.exists_level | exact GlobalTheory.ThetaDescentLevel.exists_level | (intros; apply GlobalTheory.ThetaDescentLevel.exists_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastRatCastAndExpRat
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

noncomputable section

namespace GlobalTheory.SizeRat

theorem norm_ratCast (l : ℕ) [Fact l.Prime] (q : ℚ) : ‖(q : ℂ_[l])‖ = (padicNorm l q : ℝ) := by
  have e : ((q : ℚ_[l]) : ℂ_[l]) = (q : ℂ_[l]) := by simp only [PadicComplex.coe_eq, map_ratCast]
  rw [← e, PadicComplex.norm_extends', Padic.eq_padicNorm]

theorem sz_ratCast (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (q : ℚ) (r : ℝ)
    (hr : -(padicValRat l q : ℝ) ≤ r) : Sz l lam r (q : ℂ) := by
  have hmem : (q : ℂ) ∈ algebraicClosure ℚ ℂ := SubfieldClass.ratCast_mem _ q
  refine ⟨hmem, ?_⟩
  have e : (⟨(q : ℂ), hmem⟩ : algebraicClosure ℚ ℂ) = (q : algebraicClosure ℚ ℂ) := by
    apply Subtype.ext; simp
  have hl : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
  rw [e, map_ratCast, norm_ratCast]
  by_cases hq : q = 0
  · subst hq; simp only [padicNorm.zero, Rat.cast_zero]; exact Real.rpow_nonneg (by linarith) r
  · rw [padicNorm.eq_zpow_of_nonzero hq, Rat.cast_zpow, Rat.cast_natCast, ← Real.rpow_intCast]
    exact Real.rpow_le_rpow_of_exponent_le hl (by push_cast; exact hr)

theorem sz_exp (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (q : ℚ) :
    Sz l lam 0 (Complex.exp ((2 * Real.pi * Complex.I) * (q : ℂ))) := by
  set ζ := Complex.exp ((2 * Real.pi * Complex.I) * (q : ℂ)) with hζ
  have hpow : ζ ^ q.den = 1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    have : (q.den : ℂ) * ((2 * Real.pi * Complex.I) * (q : ℂ)) = (q.num : ℂ) * (2 * Real.pi * Complex.I) := by
      have hq : (q : ℂ) = (q.num : ℂ) / (q.den : ℂ) := by exact_mod_cast (Rat.num_div_den q).symm
      have hd : (q.den : ℂ) ≠ 0 := by exact_mod_cast q.den_nz
      rw [hq]; field_simp
    rw [this]; exact Complex.exp_int_mul_two_pi_mul_I q.num
  have hmem : ζ ∈ algebraicClosure ℚ ℂ := by
    rw [mem_algebraicClosure_iff]
    exact (IsIntegral.of_pow q.den_pos (by rw [hpow]; exact isIntegral_one)).isAlgebraic
  refine ⟨hmem, ?_⟩
  have h1 : (⟨ζ, hmem⟩ : algebraicClosure ℚ ℂ) ^ q.den = 1 := by
    apply Subtype.ext; simp [hpow]
  have h2 : ‖lam ⟨ζ, hmem⟩‖ ^ q.den = 1 := by
    rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  have h3 : ‖lam ⟨ζ, hmem⟩‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) q.den_nz).mp h2
  rw [h3, Real.rpow_zero]

theorem sz_rat_exp : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]),
    (∀ (q : ℚ) (r : ℝ), (-(padicValRat l q : ℝ) ≤ r) → Sz l lam r (q : ℂ)) ∧
      ∀ q : ℚ, Sz l lam 0 (Complex.exp ((2 * Real.pi * Complex.I) * (q : ℂ))) :=
  fun l _ lam => ⟨sz_ratCast l lam, sz_exp l lam⟩

end GlobalTheory.SizeRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartKltCriterion
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem IsSncChart.neg_one_lt_formOrd_sub_sum : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ (E : DivOver q), E.Through y → ∀ a : Fin n → ℚ, ((∀ j ∈ J, a j < 1) → -1 < ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j)) ∧ ((∀ j ∈ J, a j ≤ 1) → -1 ≤ ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j)) := by
  intro k _ _ Y _ _ q n _ B y U hy z J w u hc E hE a
  classical
  haveI := SmoothOfRelativeDimension.smooth n q
  have hn : topologicalKrullDim Y = n := by
    have hd (V : Y.Opens) (hV : IsAffineOpen V) (hne : (V : Set Y).Nonempty) :
        topologicalKrullDim (V : Set Y) = n := by
      rw [topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
        hV.range_fromSpec]
      exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, V))).trans
        (SmoothDim.ringKrullDim_affineOpen k _ q _ inferInstance V hV hne)
    refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top x)
      exact ⟨V, V.isOpen, hx, (hd V hV ⟨x, hx⟩).le⟩
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top y)
      exact (hd V hV ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)
  have h0 : formOf U (gen_mem hy) (dOn q z) ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_formOf (gen_mem hy) hc.frame).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  have hnn : ∀ j ∈ J, 0 ≤ E.ord (u j) := fun j hj =>
    (E.ord_nonneg_iff _).2 (by rw [hc.val j hj]; exact hE _ (regAt_fnOf hy _ (z j)))
  have hA := DivOver.sum_ord_sub_one_le_formOrd_dOn hn E hy hE z h0 (J := {j // j ∈ J})
    Subtype.val Subtype.val_injective (fun j => u j.1) fun j => hc.val j.1 j.2
  rw [Finset.sum_coe_sort J (fun j => E.ord (u j))] at hA
  have hF := DivOver.formOrd_formOf_nonneg hn hy hE (dOn q z) h0
  set F := E.formOrd (formOf U (gen_mem hy) (dOn q z))
  have hAq : ∑ j ∈ J, (E.ord (u j) : ℚ) - 1 ≤ F := by exact_mod_cast hA
  have hFq : (0 : ℚ) ≤ F := by exact_mod_cast hF
  have hnq : ∀ j ∈ J, (0 : ℚ) ≤ E.ord (u j) := fun j hj => by exact_mod_cast hnn j hj
  have hle : (∀ j ∈ J, a j ≤ 1) → ∀ j ∈ J, a j * (E.ord (u j) : ℚ) ≤ E.ord (u j) :=
    fun ha j hj => by nlinarith [ha j hj, hnq j hj]
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · change -1 < (F : ℚ) - ∑ j ∈ J, a j * E.ord (u j)
    by_cases hz : ∀ j ∈ J, (E.ord (u j) : ℚ) = 0
    · rw [Finset.sum_eq_zero fun j hj => by rw [hz j hj, mul_zero]]
      linarith
    · push Not at hz
      obtain ⟨j, hj, hj0⟩ := hz
      have hpos : (0 : ℚ) < E.ord (u j) := lt_of_le_of_ne (hnq j hj) hj0.symm
      have := Finset.sum_lt_sum (hle fun j hj => (ha j hj).le)
        ⟨j, hj, by nlinarith [ha j hj]⟩
      linarith
  · change -1 ≤ (F : ℚ) - ∑ j ∈ J, a j * E.ord (u j)
    have := Finset.sum_le_sum (hle ha)
    linarith

end GlobalTheory.Discrepancy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantGeometricGenericPointSpecDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantGeometricGenericPointSpecDomain
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory

theorem exists_geomGeneric_dominant : ∀ (A : CommRingCat.{0}) [IsDomain A], ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (y : Sp Ω ⟶ Spec A), (∀ x, (y x).asIdeal = ⊥) ∧ IsDominant y := by
  intro A _
  let Ω := AlgebraicClosure (FractionRing A)
  let φ : A →+* Ω := algebraMap A Ω
  have hφ : Function.Injective φ := by
    have h1 : Function.Injective (algebraMap A (FractionRing A)) := IsFractionRing.injective A _
    have h2 : Function.Injective (algebraMap (FractionRing A) Ω) := (algebraMap (FractionRing A) Ω).injective
    have : φ = (algebraMap (FractionRing A) Ω).comp (algebraMap A (FractionRing A)) :=
      IsScalarTower.algebraMap_eq A (FractionRing A) Ω
    rw [this]; exact h2.comp h1
  refine ⟨Ω, inferInstance, inferInstance, Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · intro x
    show Ideal.comap φ x.asIdeal = ⊥
    rw [show x.asIdeal = ⊥ from @Ideal.eq_bot_of_prime _ _ _ (PrimeSpectrum.isPrime x)]
    exact Ideal.comap_bot_of_injective _ hφ
  · rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantGeometricGenericPointSpecDomainStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominant_geometricGenericPoint_spec_domain : ∀ (A : CommRingCat.{0}) [IsDomain A], ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (y : Sp Ω ⟶ Spec A), (∀ x, (y x).asIdeal = ⊥) ∧ IsDominant y := by
  first | exact @GlobalTheory.exists_geomGeneric_dominant | exact GlobalTheory.exists_geomGeneric_dominant | (intros; apply GlobalTheory.exists_geomGeneric_dominant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeastVectorUniqueInClassMod
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeastVectorUniqueInClassMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.LeastVec

def cross {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (x y : Fin s → X) : ℤ :=
  ∑ u, ∑ v, W u v * (β (x u) (y v) + β (y u) (x v))

theorem qW_add_zsmul {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (x y : Fin s → X) (n : ℤ) :
    qW W β (x + n • y) = qW W β x + n * cross W β x y + n ^ 2 * qW W β y := by
  unfold qW cross
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, map_add (f := _), LinearMap.add_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem least_lt_add_smul : ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∀ (X : Type) [AddCommGroup X] (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → ∀ (H : AddSubgroup (Fin s → X)), (∀ mu ∈ H, mu ≠ 0 → 0 < qW W β mu) → ∀ mu₀ ∈ H, mu₀ ≠ 0 → (∀ mu ∈ H, mu ≠ 0 → qW W β mu₀ ≤ qW W β mu) → ∀ N₁ : ℕ, 3 ≤ N₁ → ∀ nu ∈ H, nu ≠ 0 → qW W β mu₀ < qW W β (mu₀ + N₁ • nu) := by
  intro s W hW X _ β hs hβ H hpos mu₀ hmu₀ _ hmin N₁ hN nu hnu hnu0
  have hq := qW_add_zsmul W β mu₀ nu
  have h1 : 0 ≤ qW W β (mu₀ + nu) := qW_nonneg hW hs hβ _
  rw [← one_zsmul nu, hq 1] at h1
  simp only [one_mul, one_pow] at h1
  have hN' : qW W β (mu₀ + N₁ • nu) = qW W β mu₀ + (N₁ : ℤ) * cross W β mu₀ nu + (N₁ : ℤ) ^ 2 * qW W β nu := by
    rw [← hq, natCast_zsmul]
  rw [hN']
  have hle := hmin nu hnu hnu0
  have hp := hpos nu hnu hnu0
  have hN3 : (3 : ℤ) ≤ N₁ := by exact_mod_cast hN
  set B := cross W β mu₀ nu
  set q0 := qW W β mu₀
  set qn := qW W β nu
  have hNn : (0 : ℤ) ≤ N₁ := by omega
  have e1 : (N₁ : ℤ) * (-q0 - qn) ≤ (N₁ : ℤ) * B := mul_le_mul_of_nonneg_left (by linarith) hNn
  have e2 : (N₁ : ℤ) * q0 ≤ (N₁ : ℤ) * qn := mul_le_mul_of_nonneg_left hle hNn
  have e3 : 0 < (N₁ : ℤ) * ((N₁ : ℤ) - 2) * qn := by
    apply mul_pos (mul_pos (by omega) (by omega)) hp
  nlinarith

end GlobalTheory.Poinc.LeastVec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeastVectorUniqueInClassModStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.least_vector_unique_in_class_mod : ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∀ (X : Type) [AddCommGroup X] (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → ∀ (H : AddSubgroup (Fin s → X)), (∀ mu ∈ H, mu ≠ 0 → 0 < qW W β mu) → ∀ mu₀ ∈ H, mu₀ ≠ 0 → (∀ mu ∈ H, mu ≠ 0 → qW W β mu₀ ≤ qW W β mu) → ∀ N₁ : ℕ, 3 ≤ N₁ → ∀ nu ∈ H, nu ≠ 0 → qW W β mu₀ < qW W β (mu₀ + N₁ • nu) := by
  first | exact @GlobalTheory.Poinc.LeastVec.least_lt_add_smul | exact GlobalTheory.Poinc.LeastVec.least_lt_add_smul | (intros; apply GlobalTheory.Poinc.LeastVec.least_lt_add_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackCompositionCompatible
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

variable {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

theorem functionFieldMap_comp_dominant (s : Y ⟶ X) [IsDominant s] (t : Z ⟶ Y) [IsDominant t] :
    functionFieldMap (t ≫ s) = (functionFieldMap t).comp (functionFieldMap s) := by
  ext f
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective
    (A := X.presheaf.stalk ((t ≫ s) (genericPoint Z))) f
  have key : ∀ c : X.presheaf.stalk ((t ≫ s) (genericPoint Z)),
      functionFieldMap (t ≫ s) (algebraMap _ X.functionField c) =
        functionFieldMap t (functionFieldMap s (algebraMap _ X.functionField c)) := by
    intro c
    have h1 := functionFieldMap_algebraMap (t ≫ s) (genericPoint Z) c
    have h2 := functionFieldMap_algebraMap s (t (genericPoint Z)) c
    have h3 := functionFieldMap_algebraMap t (genericPoint Z) (s.stalkMap (t (genericPoint Z)) c)
    refine h1.trans (Eq.trans ?_ ((congrArg (functionFieldMap t) h2).trans h3).symm)
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  simp only [map_div₀, RingHom.comp_apply, key]

theorem pullCart_comp (s : Y ⟶ X) [IsDominant s] (t : Z ⟶ Y) [IsDominant t] (D : CartierDiv X) :
    pullCart (t ≫ s) D = pullCart t (pullCart s D) :=
  CartierDiv.ext_of_isEqn fun z => by
    obtain ⟨g, hg⟩ := D.exists_isEqn ((t ≫ s) z)
    refine ⟨_, isEqn_pullCart (t ≫ s) hg, ?_⟩
    have e : fnPull (t ≫ s) g = fnPull t (fnPull s g) :=
      Units.ext (RingHom.congr_fun (functionFieldMap_comp_dominant s t) g)
    rw [e]
    exact isEqn_pullCart t (isEqn_pullCart s hg)

theorem isDivOfForm_ratPull_comp {k : Type} [Field k] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s]
    (t : Z ⟶ Y) [IsDominant t] (n : ℕ) (η : RatForms p n) (K : CartierDiv Z) :
    IsDivOfForm K (EtaleKlt.ratPull p (t ≫ s) n η) ↔
      IsDivOfForm K (EtaleKlt.ratPull (s ≫ p) t n (EtaleKlt.ratPull p s n η)) := by
  have key : ∀ (q q' : Z ⟶ Sp k) (_ : q = q') (φ : X.functionField →+* Z.functionField)
      (h : φ.comp (Cartier.constFn p) = Cartier.constFn q) (h' : φ.comp (Cartier.constFn p) = Cartier.constFn q'),
      IsDivOfForm (p := q) K (TopForm.formMap n φ h η) ↔
        IsDivOfForm (p := q') K (TopForm.formMap n φ h' η) := by
    intro q q' e φ h h'
    subst e
    rfl
  have h' : (functionFieldMap (t ≫ s)).comp (Cartier.constFn p) = Cartier.constFn (t ≫ s ≫ p) := by
    rw [EtaleKlt.functionFieldMap_comp_constFn, Category.assoc]
  have e : EtaleKlt.ratPull (s ≫ p) t n (EtaleKlt.ratPull p s n η) =
      TopForm.formMap n (functionFieldMap (t ≫ s)) h' η :=
    formMap_formMap _ _ _ (functionFieldMap_comp_dominant s t).symm _ _ _ η
  rw [e]
  exact key _ _ (Category.assoc t s p) _ _ h'

theorem pull_comp : ∀ (k : Type) [Field k] (X Y Z : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s] (t : Z ⟶ Y) [IsDominant t], functionFieldMap (t ≫ s) = (functionFieldMap t).comp (functionFieldMap s) ∧ (∀ D : CartierDiv X, pullCart (t ≫ s) D = pullCart t (pullCart s D)) ∧ ∀ (n : ℕ) (η : RatForms p n) (K : CartierDiv Z), IsDivOfForm K (EtaleKlt.ratPull p (t ≫ s) n η) ↔ IsDivOfForm K (EtaleKlt.ratPull (s ≫ p) t n (EtaleKlt.ratPull p s n η)) :=
  fun _ _ _ _ _ _ _ _ p s _ t _ =>
    ⟨functionFieldMap_comp_dominant s t, pullCart_comp s t, isDivOfForm_ratPull_comp p s t⟩

end GlobalTheory.Discrepancy
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicValIntDiscrDivLeDeltaVp
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal UpperHalfPlane ReciprocityTheory.ChartRestriction.L1
open scoped UpperHalfPlane

namespace GlobalTheory.DiscrTower

theorem finrank_mul_padicValInt_discr_le (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (l : ℕ) (hl : l.Prime) :
    Module.finrank K L * padicValInt l (discr K) ≤ padicValInt l (discr L) := by
  haveI : Fact l.Prime := ⟨hl⟩
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have hL : (discr L).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero L)
  rw [h] at hL
  unfold padicValInt
  rw [h, Nat.multiplicity_mul (left_ne_zero_of_mul hL) (right_ne_zero_of_mul hL),
    Nat.multiplicity_pow]
  omega

theorem padicValInt_discr_div_le_delta_vp :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime →
      (padicValInt l (discr (maximalRealSubfield E)) : ℝ) / Module.finrank ℚ (maximalRealSubfield E) ≤
        GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp E l := by
  intro E _ _ _ l hl
  have h := finrank_mul_padicValInt_discr_le (maximalRealSubfield E) E l hl
  have h2 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
  have hF : (0 : ℝ) < Module.finrank ℚ (maximalRealSubfield E) := by exact_mod_cast Module.finrank_pos
  have hE : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp
  rw [div_le_div_iff₀ hF hE, ← h2]
  have h' : (Module.finrank (maximalRealSubfield E) E : ℝ) * padicValInt l (discr (maximalRealSubfield E)) ≤
      padicValInt l (discr E) := by exact_mod_cast h
  push_cast
  nlinarith

end GlobalTheory.DiscrTower
end
