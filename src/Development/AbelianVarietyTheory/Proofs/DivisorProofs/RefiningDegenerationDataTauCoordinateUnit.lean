module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTrivialOfSamePolarization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOneTrivialOnAxis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalTau
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsFramePolynomialAtPrime
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSncCoordinatesComplexPointSmoothVariety
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.WMultA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefiningDegenerationDataTauCoordinateUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefiningDegenerationDataTauCoordinateUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.RefTauCoord

open GlobalTheory.PeriodBalance GlobalTheory.PsiTauCoordRel

theorem gm_stalk {X Y Z : Scheme.{0}} (κ : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (κ z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (κ ≫ r) z U a = Units.map (κ.stalkMap z).hom.toMonoidHom (gm r (κ z) U a) := by
  apply Units.ext
  refine (gm_val (κ ≫ r) z U h a).trans (Eq.trans ?_ (congrArg (κ.stalkMap z).hom (gm_val r (κ z) U h a)).symm)
  exact (Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ U) z h _).symm

theorem val_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y' ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (κ : Z ⟶ Y) (r : Y ⟶ Y') (z : Z) {J} (hJ : Good L z J) :
    val t (κ ≫ r) z J = Units.map (κ.stalkMap z).hom.toMonoidHom (val t r (κ z) fun ψ => J (κ ≫ ψ)) := by
  rw [val_of t (κ ≫ r) z J (fun k => J (κ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_stalk κ r z _ (Set.mem_iInter.2 fun k => hJ (κ ≫ r ≫ φ k)) _

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem exists_good_over (ξ : Spec (CommRingCat.of (FractionRing R))) {X S : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (s : X ⟶ S) [IsSeparated s] (f : Spec (CommRingCat.of R) ⟶ S) :
    ∃ J, Good L ξ J ∧ ∀ p : Spec (CommRingCat.of R) ⟶ X, p ≫ s = f →
      p (closedPoint R) ∈ L.U (J (jK R ≫ p)) := by
  haveI : IsDominant (jK R) := DVR.isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of R) ⟶ X => exists_chart hL (p (closedPoint R))
  obtain ⟨J, hJ, e⟩ := exists_good L hL ξ (K := {p : Spec (CommRingCat.of R) ⟶ X // p ≫ s = f})
    (fun p => jK R ≫ p.1) (fun p => pick p.1)
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated s (a.2.trans b.2.symm) (jK R) h))
    (fun p => by
      have := DVR.eq_top_of_closedPoint_mem (p.1 ⁻¹ᵁ L.U (pick p.1)) (hpk p.1)
      have h2 : jK R ξ ∈ p.1 ⁻¹ᵁ L.U (pick p.1) := by rw [this]; trivial
      exact h2)
  exact ⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩

theorem gm_unitOn {A : Type} [CommRing A] (σ : A →+* FractionRing R) (ξ : Spec (CommRingCat.of (FractionRing R)))
    (k : Aˣ) : (gm (spMap σ) ξ ⊤ (unitOn k)).val = kst ξ (σ k) := by
  rw [gm_val _ ξ ⊤ trivial]
  have hnat := congrArg (fun f => (CommRingCat.Hom.hom f) k.val)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
  exact (congrArg ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom hnat).symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (hρ : Function.Injective ρ),
    Refines Q ρ D e → ∀ (a b : D.X) (k : (FractionRing R)ˣ), Q.TauCoord (e a) (e b) k →
      ∀ x : (FractionRing R')ˣ, IsTauCoord D a b x → ∃ u : R'ˣ, (x : FractionRing R') =
        algebraMap R' (FractionRing R') u * IsFractionRing.lift (A := R) (K := FractionRing R)
          (g := (algebraMap R' (FractionRing R')).comp ρ) ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (k : FractionRing R) := by
  intro R _ _ R' _ _ _ Q ρ D e hρ href a b k hk x hx
  letI := D.P.isAb.comm
  obtain ⟨β, β₂, w, h₁, h₂, -, -, h₅⟩ := href
  have hσ : ∀ r, IsFractionRing.lift (A := R) (K := FractionRing R) (g := (algebraMap R' (FractionRing R')).comp ρ)
      ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (algebraMap R (FractionRing R) r) =
      algebraMap R' (FractionRing R') (ρ r) := fun r => IsFractionRing.lift_algebraMap _ r
  generalize IsFractionRing.lift (A := R) (K := FractionRing R) (g := (algebraMap R' (FractionRing R')).comp ρ)
      ((IsFractionRing.injective R' (FractionRing R')).comp hρ) = σ at hσ ⊢
  have hκ : spMap σ ≫ jK R = jK R' ≫ spMap ρ := by
    have : σ.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp ρ := RingHom.ext hσ
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, this]
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  haveI : IsProper Q.B.hom := Q.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R'))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J', hJ', hc'⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  obtain ⟨J, hJ, hc⟩ := exists_good_over ξ Q.M.isLB Q.B.hom (spMap ρ)
  have E := h₅ (spMap σ) hκ a b ξ J J' hJ hJ'
  obtain ⟨u₁, e₁⟩ := GlobalTheory.TauShift.coord_val D ξ hJ' hc' hx
  obtain ⟨u₂, e₂⟩ : ∃ u : R'ˣ, (lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left ξ J J').val =
      cst ξ u := by
    have hp : (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left = jK R' ≫ (lift (D.c a) (D.c b)).left := by
      simp [← CartesianMonoidalCategory.comp_lift]
    rw [hp]
    refine unit_gm' ξ (lift (D.c a) (D.c b)).left _ ?_ _
    refine And.intro (mem_pull.2 (Set.mem_iInter.2 fun I => ?_)) (Set.mem_iInter.2 fun I => ?_)
    · have := hc ((lift (D.c a) (D.c b)).left ≫ β₂ ≫ (psum Q.B (x2 Q.B) I.down).left) (by
        rw [Category.assoc, Category.assoc, Over.w, ← Over.w (fst Q.B Q.B), reassoc_of% h₂.1, h₁.1.w,
          Over.w_assoc, Over.w_assoc]
        exact Category.id_comp _)
      exact this
    · have := hc' ((lift (D.c a) (D.c b)).left ≫ (psum D.P.A (x2 D.P.A) I.down).left) (by
        rw [Category.assoc, Over.w, Over.w]; rfl)
      exact this
  obtain ⟨u, -, hu⟩ := hk
  obtain ⟨u₃, e₃⟩ : ∃ v : R'ˣ, (val u (jK R' ≫ spMap ρ) ξ J).val = cst ξ v := by
    refine unit_gm' ξ _ _ (Set.mem_iInter.2 fun i => ?_) _
    obtain ⟨q, hq⟩ : ∃ q : 𝟙_ (Over (Sp R)) ⟶ Q.B, lamPts (Q.c (e a)) (Q.c (e b)) i = q.left := by
      fin_cases i <;> exact ⟨_, rfl⟩
    have := hc (spMap ρ ≫ lamPts (Q.c (e a)) (Q.c (e b)) i) (by
      rw [hq, Category.assoc, Over.w q]; exact Category.comp_id _)
    exact this
  have hT := congrArg (Units.map ((spMap σ).stalkMap ξ).hom.toMonoidHom)
    (hu (spMap σ ξ) (fun ψ => J (spMap σ ≫ ψ)) fun ψ => hJ (spMap σ ≫ ψ))
  have v₁ := val_stalk (Q.tau (e a) (e b)) (spMap σ) (𝟙 (TK R).left) ξ hJ
  have v₂ := val_stalk u (spMap σ) (toUnit (TK R)).left ξ hJ
  have v₃ := gm_stalk (spMap σ) (𝟙 (TK R).left) ξ ⊤ trivial (unitOn k)
  have hh : spMap σ ≫ (toUnit (TK R)).left = jK R' ≫ spMap ρ := by
    rw [show (toUnit (TK R)).left = jK R by simpa using Over.w (toUnit (TK R))]; exact hκ
  have hT' := v₁.trans (hT.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) v₃.symm v₂.symm)))
  rw [hh] at hT'
  rw [show spMap σ ≫ 𝟙 (TK R).left = spMap σ from Category.comp_id _] at hT'
  have F : (val (Q.tau (e a) (e b)) (spMap σ) ξ J).val = kst ξ (σ k) * cst ξ u₃ :=
    (congrArg Units.val hT').trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) (gm_unitOn σ ξ k) e₃))
  have G : kst ξ x.val = cst ξ u₁ * (cst ξ u₂ * (kst ξ (σ k) * cst ξ u₃)) :=
    (congrArg Units.val e₁).trans ((Units.val_mul _ _).trans (congrArg (cst ξ u₁ * ·)
      ((congrArg Units.val E).trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) e₂ F)))))
  refine ⟨u₁ * u₂ * u₃, kst_injective ξ ?_⟩
  rw [G, map_mul, kst_algebraMap, Units.val_mul, Units.val_mul, map_mul, map_mul]
  ring

end GlobalTheory.RefTauCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefiningDegenerationDataTauCoordinateUnitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refining_degenerationData_tauCoordinate_unit : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (hρ : Function.Injective ρ),
    Refines Q ρ D e → ∀ (a b : D.X) (k : (FractionRing R)ˣ), Q.TauCoord (e a) (e b) k →
      ∀ x : (FractionRing R')ˣ, IsTauCoord D a b x → ∃ u : R'ˣ, (x : FractionRing R') =
        algebraMap R' (FractionRing R') u * IsFractionRing.lift (A := R) (K := FractionRing R)
          (g := (algebraMap R' (FractionRing R')).comp ρ) ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (k : FractionRing R) := by
  first | exact @GlobalTheory.RefTauCoord.main | exact GlobalTheory.RefTauCoord.main | (intros; apply GlobalTheory.RefTauCoord.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSiegelObjectPolarisationKernelKilled
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSiegelObjectPolarisationKernelKilled
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.UPel.HT.KerBy

theorem ev_nsmul {La Q : Type} [AddCommGroup La] [Group Q] (f : La → Q) (hadd : ∀ x y, f (x + y) = f x * f y)
    (e : ℕ) (y : La) : f (e • y) = f y ^ e := by
  induction e with
  | zero =>
    have h := hadd 0 0
    rw [add_zero] at h
    simpa using (mul_eq_left.1 h.symm)
  | succ e ih => rw [succ_nsmul, hadd, ih, pow_succ]

theorem pow_eq_one_at_geom (hC : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (m : ℕ), (m : k) ≠ 0 → ∀ (a b : Over.mk x₀ ⟶ A), a ^ m = 1 → b ^ m = 1 → (∃ t : (P.pull (lift (snd A (Over.mk x₀) ≫ a ^ 2) (fst A (Over.mk x₀))).left).Gen, t.IsGen) → ∀ c : Γ((Over.mk x₀).left, ⊤)ˣ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) (m : ℤ) a b c → c = 1) {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    {N : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp R} (o : Obj b N t) (e : ℕ) (hEF : ∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f)
    (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (g : Over.mk x₀ ⟶ o.A)
    (hg : ∃ t : (o.P.pull (lift (snd o.A (Over.mk x₀) ≫ g) (fst o.A (Over.mk x₀))).left).Gen, t.IsGen) :
    g ^ e = 1 := by
  have hpr : p.Prime := Fact.out
  obtain ⟨e', he', hk⟩ := o.kerP
  have hn : g ^ e' = 1 := hk _ g hg
  have hpos : 0 < e' := by
    rcases Nat.eq_zero_or_pos e' with h | h
    · subst h
      have := (Nat.coprime_zero_left p).1 he'
      exact absurd this hpr.one_lt.ne'
    · exact h
  let φ := Spec.preimage (x₀ ≫ t)
  have hβ : x₀ ≫ t = spMap φ.hom := by
    simp [spMap, φ]
  obtain ⟨I, -⟩ := o.geom k x₀ φ.hom hβ
  have hunit : ∀ m : ℕ, m.Coprime p → ((m : ℕ) : k) ≠ 0 := fun m hm => by
    have := (b.unit m hm).map φ.hom
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨y, hy⟩ := (I.onto e' hpos he' g).1 hn
  have hadd : ∀ m, ∀ u v, I.ev m (u + v) = I.ev m u * I.ev m v := fun m u v => I.add m u v

  have vanish : ∀ (m : ℕ), 0 < m → m.Coprime p → ∀ y' z : D.La, I.ev m y' ^ 2 = g →
      I.ζ m ^ (2 * D.EF y' z) = 1 := by
    intro m hm hmp y' z ha
    have ha1 : I.ev m y' ^ m = 1 := (I.onto m hm hmp _).2 ⟨y', rfl⟩
    have hb1 : I.ev m z ^ m = 1 := (I.onto m hm hmp _).2 ⟨z, rfl⟩
    have hgen : ∃ t : (o.P.pull (lift (snd o.A (Over.mk x₀) ≫ I.ev m y' ^ 2) (fst o.A (Over.mk x₀))).left).Gen,
        t.IsGen := ha ▸ hg
    have hc := hC S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm o.ample k x₀ m (hunit m hmp) _ _ ha1 hb1 hgen _
      (I.isom m hm hmp y' z)
    exact ReciprocityTheory.ChartRestriction.G.H1.unitOn_injective (hc.trans (map_one _).symm)
  have key : ∀ z, (e' : ℤ) ∣ D.EF y z := by
    intro z
    by_cases hp2 : p = 2
    · subst hp2
      have hodd : Odd e' := Nat.odd_iff.2 (by
        rcases Nat.even_or_odd e' with h | h
        · exact absurd (Nat.Coprime.coprime_dvd_left (even_iff_two_dvd.1 h) he') (by norm_num)
        · exact Nat.odd_iff.1 h)
      obtain ⟨r, hr⟩ := hodd
      have h2 : 2 • ((r + 1) • y) = y + e' • y := by
        rw [smul_smul, hr]
        rw [show (2 * (r + 1)) = 1 + (2 * r + 1) by ring, add_smul, one_smul]
      have ha : I.ev e' ((r + 1) • y) ^ 2 = g := by
        rw [← ev_nsmul _ (hadd e'), h2, hadd, ev_nsmul _ (hadd e'), hy, hn, _root_.mul_one]
      have h1 := vanish e' hpos he' _ z ha
      have h3 := ((I.ζ_prim e' hpos he').zpow_eq_one_iff_dvd _).1 h1
      rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h3
      have h4 : (e' : ℤ) ∣ (((r + 1) * 2 : ℕ) : ℤ) * D.EF y z := by
        have : (2 : ℤ) * (((r + 1 : ℕ) : ℤ) * D.EF y z) = (((r + 1) * 2 : ℕ) : ℤ) * D.EF y z := by push_cast; ring
        rw [← this]; exact_mod_cast h3
      have hcop : IsCoprime (e' : ℤ) (((r + 1) * 2 : ℕ) : ℤ) := by
        rw [Nat.isCoprime_iff_coprime]
        have : (r + 1) * 2 = e' + 1 := by omega
        rw [this]
        exact (Nat.coprime_self_add_right.2 (Nat.coprime_one_right e'))
      exact hcop.dvd_of_dvd_mul_left h4
    · have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hpr).2 (Ne.symm hp2)
      have hmp : (e' * 2).Coprime p := Nat.Coprime.mul_left he' h2p
      have ha : I.ev (e' * 2) y ^ 2 = g := by
        rw [I.tower e' 2 hpos two_pos hmp y, hy]
      have h1 := vanish (e' * 2) (by omega) hmp y z ha
      have h3 := ((I.ζ_prim (e' * 2) (by omega) hmp).zpow_eq_one_iff_dvd _).1 h1
      have h4 : (e' : ℤ) * 2 ∣ D.EF y z * 2 := by
        have : (2 : ℤ) * D.EF y z = D.EF y z * 2 := by ring
        rw [← this]; exact_mod_cast h3
      exact (mul_dvd_mul_iff_right (by norm_num : (2 : ℤ) ≠ 0)).1 h4
  let f : D.La →ₗ[ℤ] ℤ :=
    { toFun := fun z => D.EF y z / e'
      map_add' := fun u v => by
        rw [map_add (f := _), Int.add_ediv_of_dvd_left (key u)]
      map_smul' := fun r u => by
        rw [map_smul, smul_eq_mul, smul_eq_mul, RingHom.id_apply, Int.mul_ediv_assoc _ (key u)] }
  have hf : ∀ z, (e' : ℤ) * f z = D.EF y z := fun z => Int.mul_ediv_cancel' (key z)
  obtain ⟨w, hw⟩ := hEF f
  have hyw : e • y = e' • w := by
    apply D.nondeg
    ext z
    have hwz : D.EF w z = e • f z := by rw [hw]; rfl
    simp only [map_nsmul, LinearMap.smul_apply, hwz, nsmul_eq_mul]
    rw [← hf z]; ring
  calc g ^ e = I.ev e' y ^ e := by rw [hy]
    _ = I.ev e' (e • y) := (ev_nsmul _ (hadd e') e y).symm
    _ = 1 := by rw [hyw]; exact (I.ker e' hpos he' _).2 ⟨w, rfl⟩

end GlobalTheory.UPel.HT.KerBy

namespace GlobalTheory.UPel.HT.KerBy

theorem gen_comp : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (G2 A).left) (T T' : Over S) (a : T' ⟶ T) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → ∃ t : (P.pull (lift (snd A T' ≫ a ≫ x) (fst A T')).left).Gen, t.IsGen := by
  intro S A _ P T T' a x hx
  obtain ⟨t, ht⟩ := hx
  have e : (A ◁ a) ≫ lift (snd A T ≫ x) (fst A T) = lift (snd A T' ≫ a ≫ x) (fst A T') := by
    rw [comp_lift, whiskerLeft_snd_assoc, whiskerLeft_fst]
  rw [← e, Over.comp_left]
  exact ⟨_, LB.isGen_pullGen P _ _ t ht (A ◁ a).left⟩

end GlobalTheory.UPel.HT.KerBy

namespace GlobalTheory.UPel.HT.KerBy

theorem siegKerBy_toSieg_of (hA : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (n : ℕ), IsUnit (n : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ A), x ^ n = 1 → ∀ d : ℕ, (∀ (k : Type) [Field k] [IsAlgClosed k] (ξ : Sp k ⟶ T.left), ((Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) ≫ x) ^ d = 1) → x ^ d = 1) (hB : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (G2 A).left) (T T' : Over S) (a : T' ⟶ T) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → ∃ t : (P.pull (lift (snd A T' ≫ a ≫ x) (fst A T')).left).Gen, t.IsGen) (hC : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (m : ℕ), (m : k) ≠ 0 → ∀ (a b : Over.mk x₀ ⟶ A), a ^ m = 1 → b ^ m = 1 → (∃ t : (P.pull (lift (snd A (Over.mk x₀) ≫ a ^ 2) (fst A (Over.mk x₀))).left).Gen, t.IsGen) → ∀ c : Γ((Over.mk x₀).left, ⊤)ˣ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) (m : ℤ) a b c → c = 1) : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (h M : ℕ) (t₁ : S ⟶ Sp (cycAway M)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ lev) (e : ℕ), e.Coprime p → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SiegKerBy (o.toSieg hl) e := by
  intro p _ D R _ b N S t o h M t₁ lev hl e _ hEF
  refine ⟨Obj.toSieg_ample o hl, ?_⟩
  intro T x hx
  obtain ⟨e', he', hk⟩ := o.kerP
  have hx' : x ^ e' = 1 := hk T x hx
  have hu : IsUnit ((e' : ℕ) : Γ(S, ⊤)) := by
    have h1 := (b.unit e' he').map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    have h2 := h1.map t.appTop.hom
    simpa using h2
  refine hA S o.A o.ab e' hu T x hx' e (fun k _ _ ξ => ?_)
  have hx2 := hB S o.A o.P T (Over.mk (ξ ≫ T.hom)) (Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) x hx
  exact pow_eq_one_at_geom hC o e hEF k (ξ ≫ T.hom) _ hx2

end GlobalTheory.UPel.HT.KerBy

namespace GlobalTheory.UPel.HT.KerBy

theorem siegKerBy_toSieg : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (h M : ℕ) (t₁ : S ⟶ Sp (cycAway M)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ lev) (e : ℕ), e.Coprime p → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SiegKerBy (o.toSieg hl) e :=
  siegKerBy_toSieg_of GlobalTheory.T.pow_eq_one_of_geometric_points_torsion gen_comp GlobalTheory.T.commutatorPairing_eq_one_trivial_on_axis

end GlobalTheory.UPel.HT.KerBy
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSiegelObjectPolarisationKernelKilledStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_siegelObject_polarisationKernel_killed : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (h M : ℕ) (t₁ : S ⟶ Sp (cycAway M)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ lev) (e : ℕ), e.Coprime p → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SiegKerBy (o.toSieg hl) e := by
  first | (exact @GlobalTheory.UPel.HT.KerBy.siegKerBy_toSieg) | (exact GlobalTheory.UPel.HT.KerBy.siegKerBy_toSieg) | (intros; apply GlobalTheory.UPel.HT.KerBy.siegKerBy_toSieg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsIsoOfMonoSameDimension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsIsoOfMonoSameDimension
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbMonoIsoAny

open GlobalTheory.NearFibreIso GlobalTheory.DenseFibreIso

theorem exists_away_bijective_of_fg {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (R K : Type) [CommRing R] [CommRing K]
    [Algebra R K] [Algebra R A] [Algebra R B] [IsScalarTower R A B] [Module.Flat R B]
    (hs : Function.Surjective (algebraMap A B))
    (hfg : (RingHom.ker (algebraMap A B)).FG)
    (h : Function.Injective
      (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B))
    (m : PrimeSpectrum (A ⊗[R] K)) :
    ∃ a : A, algebraMap A (A ⊗[R] K) a ∉ m.asIdeal ∧ Function.Bijective
      (Algebra.TensorProduct.includeLeftRingHom :
        Localization.Away a →+* Localization.Away a ⊗[A] B) := by
  let I : Submodule A A := LinearMap.ker (Algebra.linearMap A B)
  have : Module.Finite A I := Module.Finite.iff_fg.2 hfg
  have hex : Function.Exact I.subtype (Algebra.linearMap A B) := LinearMap.exact_subtype_ker_map _
  have hinj : Function.Injective ((I.subtype.restrictScalars R).rTensor K) :=
    (LinearMap.lTensor_inj_iff_rTensor_inj K _).1
      (LinearMap.lTensor_injective_of_exact_of_flat ((Algebra.linearMap A B).restrictScalars R) hs
        (I.subtype.restrictScalars R) Subtype.val_injective hex K)
  have h1 : Subsingleton (I ⊗[R] K) := by
    refine subsingleton_of_forall_eq 0 fun z => hinj (h ?_)
    rw [map_zero, map_zero]
    induction z with
    | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz, add_zero]
    | tmul x c =>
      have e : (x : A) ⊗ₜ[R] c = (x : A) • ((1 : A) ⊗ₜ[R] c) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      have hx : (x : A) • (1 : B) = 0 := by
        rw [← Algebra.algebraMap_eq_smul_one]; exact x.2
      change ((x : A) ⊗ₜ[R] c) ⊗ₜ[A] (1 : B) = 0
      rw [e, TensorProduct.smul_tmul, hx, TensorProduct.tmul_zero]
  have h2 : Subsingleton ((A ⊗[R] K) ⊗[A] I) :=
    ((TensorProduct.comm A _ _).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A I K)).toEquiv.subsingleton
  obtain ⟨a, ha, ha'⟩ := exists_smul_eq_zero (A := A) (N := I) (A ⊗[R] K) m
  refine ⟨a, ha, ?_⟩
  have h3 := subsingleton_of_isUnit ha' (Localization.Away a)
    (IsLocalization.Away.algebraMap_isUnit a)
  rw [includeLeft_eq, EquivLike.bijective_comp]
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz => ?_, LinearMap.lTensor_surjective _ hs⟩
  obtain ⟨y, rfl⟩ := (lTensor_exact (Localization.Away a) hex hs z).1 hz
  rw [Subsingleton.elim y 0, map_zero]


set_option backward.isDefEq.respectTransparency.types false in
theorem near_isIso_of_finitePresentation {R : Type} [CommRing R] {Y X : Scheme.{0}} (s : X ⟶ Sp R)
    (f : Y ⟶ X) (K : Type) [Field K] [Algebra R K] [hcl : IsClosedImmersion f]
    [LocallyOfFinitePresentation s] [LocallyOfFinitePresentation (f ≫ s)] [Flat (f ≫ s)]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f (MorphismProperty.isomorphisms _) x := by
  refine local_of_ring (K := K) s f _ (fun A B _ _ _ _ _ _ j j' _ H hj hb m => ?_) x hx
  have h1 : IsClosedImmersion (spMap (algebraMap A B)) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) H.flip hcl
  have hs : Function.Surjective (algebraMap A B) := by
    have h2 := (IsClosedImmersion.isAffine_surjective_of_isAffine (spMap (algebraMap A B))).2
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))
    have h3 := (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom).2.comp h2
    rw [← ConcreteCategory.coe_comp, e, ConcreteCategory.coe_comp] at h3
    exact h3.of_comp
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback (P := @IsOpenImmersion) H ‹_›
  have e : spMap (algebraMap R B) = j' ≫ f ≫ s := by
    rw [← H.w_assoc, hj, ← Spec.map_comp, IsScalarTower.algebraMap_eq R A B]; rfl
  have h2 : Flat (spMap (algebraMap R B)) := by
    rw [e]; infer_instance
  have : Module.Flat R B := RingHom.flat_algebraMap_iff.1 (Flat.SpecMap_iff.1 h2)
  have h3 : LocallyOfFinitePresentation (spMap (algebraMap R B)) := by
    rw [e]; infer_instance
  have h4 : LocallyOfFinitePresentation (spMap (algebraMap R A)) := by
    rw [← hj]; infer_instance
  have : Algebra.FinitePresentation R B := RingHom.finitePresentation_algebraMap.1
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 h3)
  have : Algebra.FinitePresentation R A := RingHom.finitePresentation_algebraMap.1
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 h4)
  have hfg : (RingHom.ker (algebraMap A B)).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective (IsScalarTower.toAlgHom R A B) hs
  obtain ⟨a, ha, ha'⟩ := exists_away_bijective_of_fg R K hs hfg hb.1 m
  exact ⟨a, ha, isIso_SpecMap_iff.2 ha'⟩

theorem isIso_of_isClosedImmersion {S X Y : Scheme.{0}} (p : X ⟶ S)
    (f : Y ⟶ X) [IsClosedImmersion f] [GeometricallyConnected p] [Surjective (f ≫ p)]
    {g g' : ℕ} (hg' : SmoothOfRelativeDimension g' p)
    (hg : SmoothOfRelativeDimension g (f ≫ p)) (hle : g' ≤ g) : IsIso f := by
  have hn : ∀ y : X, Near f (MorphismProperty.isomorphisms _) y := by
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p y)) isOpen_univ
    replace hU : IsAffineOpen U := hU
    let j : Sp Γ(S, U) ⟶ S := hU.fromSpec
    obtain ⟨z, hz⟩ : p y ∈ Set.range j := by rw [hU.range_fromSpec]; exact hyU
    let gX := pullback.fst p j
    let s := pullback.snd p j
    let f' := pullback.snd f gX
    have HX := IsPullback.of_hasPullback p j
    have HY := IsPullback.of_hasPullback f gX
    have HYS := HY.paste_vert HX
    obtain ⟨y', hy', hy's⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := j) y z hz.symm
    have : Surjective (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have h₁ : SmoothOfRelativeDimension g' s :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback HX hg'
    have h₂ : SmoothOfRelativeDimension g (f' ≫ s) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback HYS hg
    have : Smooth s := h₁.smooth
    have : Smooth (f' ≫ s) := h₂.smooth
    have : (s y').asIdeal.IsPrime := (s y').isPrime
    have := GlobalTheory.AbMonoIso.fibre_isIso s f' h₁ h₂ hle (s y').asIdeal.ResidueField
    have h := near_isIso_of_finitePresentation s f' (s y').asIdeal.ResidueField y'
      (Ideal.ker_algebraMap_residueField (s y').asIdeal)
    have h' := Near.of_pullback f HY.flip h
    rwa [hy'] at h'
  have h := isIso_of_near f (𝟙 _) (fun y => by simpa using hn y)
  have e : f = inv (pullback.fst f (𝟙 X)) ≫ pullback.snd f (𝟙 X) := by
    rw [IsIso.eq_inv_comp, pullback.condition, Category.comp_id]
  rw [e]
  infer_instance

theorem isIso_of_mono : ∀ (S : Scheme.{0}) (B B' : Over S) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → ∀ g : ℕ, SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension g B'.hom → ∀ x : B ⟶ B', IsMonHom x → Mono x → IsIso x := by
  intro S B B' _ _ hB hB' g hg hg' x _ _
  have := hB.proper
  have := hB'.proper
  have := hB'.geomConnected
  have : Mono x.left := inferInstanceAs (Mono ((Over.forget S).map x))
  have : IsProper (x.left ≫ B'.hom) := by rw [Over.w]; infer_instance
  have : IsProper x.left := IsProper.of_comp x.left B'.hom
  have : IsClosedImmersion x.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have hs : Surjective B.hom := ⟨fun t => ⟨(η[B] : 𝟙_ (Over S) ⟶ B).left t, by
    rw [← Scheme.Hom.comp_apply, Over.w]; rfl⟩⟩
  have : Surjective (x.left ≫ B'.hom) := by rw [Over.w]; exact hs
  have : IsIso x.left :=
    isIso_of_isClosedImmersion B'.hom x.left hg' (by rw [Over.w]; exact hg) le_rfl
  have : IsIso ((Over.forget _).map x) := ‹_›
  exact isIso_of_reflects_iso x (Over.forget _)

end GlobalTheory.AbMonoIsoAny
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsIsoOfMonoSameDimensionStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_isIso_of_mono_same_dimension : ∀ (S : Scheme.{0}) (B B' : Over S) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → ∀ g : ℕ, SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension g B'.hom → ∀ x : B ⟶ B', IsMonHom x → Mono x → IsIso x := by
  first | exact @GlobalTheory.AbMonoIsoAny.isIso_of_mono | exact GlobalTheory.AbMonoIsoAny.isIso_of_mono | (intros; apply GlobalTheory.AbMonoIsoAny.isIso_of_mono <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopFormFrameBaseCoordinatesAddVariablesEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMvPolynomialEval2HomRestrictSmallerAffines
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMvPolynomialEval2HomRestrictSmallerAffines
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.EtaleRestrict

theorem etale_eval₂_res : ∀ (X Y : Scheme.{0}) (q : Y ⟶ X) (ι : Type) (U U' : X.Opens) (hU' : U' ≤ U), IsAffineOpen U → IsAffineOpen U' → ∀ (W W' : Y.Opens) (hW' : W' ≤ W), IsAffineOpen W → IsAffineOpen W' → ∀ (hWU : W ≤ q ⁻¹ᵁ U) (hW'U' : W' ≤ q ⁻¹ᵁ U') (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N).Etale → (MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a))).Etale := by
  intro X Y q ι U U' hU' hU hU'a W W' hW' hW hW'a hWU hW'U' N hN
  have h1 : (resG Y hW').Etale := GlobalTheory.TopForm.etale_resG hW hW'a hW'
  have h2 : ((resG Y hW').comp (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N)).Etale :=
    RingHom.Etale.stableUnderComposition _ _ hN h1
  have h3 : (resG X hU').Etale := GlobalTheory.TopForm.etale_resG hU hU'a hU'
  have h4 : (MvPolynomial.map (σ := ι) (resG X hU')).Etale := by
    algebraize [resG X hU']
    letI := MvPolynomial.algebraMvPolynomial (σ := ι) (R := Γ(X, U)) (S := Γ(X, U'))
    exact RingHom.Etale.isStableUnderBaseChange Γ(X, U) Γ(X, U') (MvPolynomial ι Γ(X, U)) (MvPolynomial ι Γ(X, U')) h3
  have h5 : (MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a))).comp
      (MvPolynomial.map (resG X hU')) = (resG Y hW').comp (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C]
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE,
        ← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
    · intro i
      simp
  rw [← h5] at h2
  algebraize [MvPolynomial.map (σ := ι) (resG X hU'),
    MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a)),
    (MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a))).comp
      (MvPolynomial.map (resG X hU'))]
  exact Algebra.Etale.of_restrictScalars (R := MvPolynomial ι Γ(X, U)) _ _

end GlobalTheory.EtaleRestrict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMvPolynomialEval2HomRestrictSmallerAffinesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_mvPolynomial_eval2Hom_restrict_smaller_affines : ∀ (X Y : Scheme.{0}) (q : Y ⟶ X) (ι : Type) (U U' : X.Opens) (hU' : U' ≤ U), IsAffineOpen U → IsAffineOpen U' → ∀ (W W' : Y.Opens) (hW' : W' ≤ W), IsAffineOpen W → IsAffineOpen W' → ∀ (hWU : W ≤ q ⁻¹ᵁ U) (hW'U' : W' ≤ q ⁻¹ᵁ U') (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N).Etale → (MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a))).Etale := by
  first | exact @GlobalTheory.EtaleRestrict.etale_eval₂_res | exact GlobalTheory.EtaleRestrict.etale_eval₂_res | (intros; apply GlobalTheory.EtaleRestrict.etale_eval₂_res <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopFormFrameBaseCoordinatesAddVariablesEtale
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TopFrameEt

open GlobalTheory.TopForm

theorem appLE_comp_algX' {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (q : Y ⟶ X)
    {U : X.Opens} {W : Y.Opens} (h : W ≤ q ⁻¹ᵁ U) :
    (q.appLE U W h).hom.comp (algX p U) = algX (q ≫ p) W := by
  have e := Scheme.Hom.appLE_comp_appLE q p ⊤ U W le_top h
  exact congrArg (fun f ↦ (CommRingCat.Hom.hom f).comp
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) e

theorem exists_basis_of_exact {R M₁ M₂ M₃ ι ι' : Type} [CommRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (hf : Function.Injective f) (hex : Function.Exact f g)
    (v : Module.Basis ι R M₁) (w : Module.Basis ι' R M₃) (u : ι' → M₂) (hu : ∀ a, g (u a) = w a) :
    ∃ b : Module.Basis (ι ⊕ ι') R M₂, ∀ j, b j = Sum.elim (fun i ↦ f (v i)) u j := by
  let S : ShortComplex (ModuleCat R) := ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
    (by ext x; exact hex.apply_apply_eq_zero x)
  have hS : S.Exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 hex
  have hm : Mono S.f := (ModuleCat.mono_iff_injective _).2 hf
  let u' : ι ⊕ ι' → M₂ := Sum.elim (fun i ↦ f (v i)) u
  have hw : (S.g ∘ u' ∘ Sum.inr) = w := funext fun a ↦ hu a
  have hli : LinearIndependent R u' := by
    refine ModuleCat.linearIndependent_leftExact (S := S) (v := v) hS v.linearIndependent ?_ hm ?_
    · rw [hw]; exact w.linearIndependent
    · rfl
  have hsp : ⊤ ≤ Submodule.span R (Set.range u') := by
    refine ModuleCat.span_exact (S := S) (v := v) hS rfl (by rw [v.span_eq]) ?_
    rw [hw, w.span_eq]
  exact ⟨Module.Basis.mk hli hsp, fun j ↦ by simp [u']⟩

theorem isFrame_etale : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ X) (p' : Y ⟶ Sp k), q ≫ p = p' → ∀ (m D : ℕ), SmoothOfRelativeDimension m p → ∀ (ι : Type) (o : Fin D ≃ Fin m ⊕ ι) (U U' : X.Opens) (hU' : U' ≤ U), IsAffineOpen U → ∀ (W W' : Y.Opens) (hW' : W' ≤ W), IsAffineOpen W → IsAffineOpen W' → ∀ (hWU : W ≤ q ⁻¹ᵁ U), W' ≤ q ⁻¹ᵁ U' → ∀ (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N).Etale → ∀ (x : Fin m → Γ(X, U)), TopForm.IsFrame (TopForm.dOn p fun i => resG X hU' (x i)) → TopForm.IsFrame (TopForm.dOn p' fun a => resG Y hW' (Sum.elim (fun i => (q.appLE U W hWU).hom (x i)) N (o a))) := by
  intro k _ X Y p q p' hp m D _ ι o U U' hU' hU W W' hW' hW hW'a hWU hW'U' N hN x hx
  subst hp
  have hU'a : IsAffineOpen U' := hx.affine
  have hC := GlobalTheory.T.etale_mvPolynomial_eval2Hom_restrict_smaller_affines X Y q ι U U' hU' hU hU'a W W' hW' hW hW'a hWU hW'U' N hN
  obtain ⟨bR, hbR⟩ := GlobalTheory.T.exists_kaehlerBasis_differentials_of_topFormFrame k X p m ‹_› U' _ hx
  haveI : Finite ι := Finite.of_injective (fun a ↦ o.symm (Sum.inr a))
    (fun a b h ↦ Sum.inr_injective (o.symm.injective h))
  letI : Algebra k Γ(X, U') := (algX p U').toAlgebra
  letI : Algebra k Γ(Y, W') := (algX (q ≫ p) W').toAlgebra
  letI : Algebra Γ(X, U') Γ(Y, W') := (q.appLE U' W' hW'U').hom.toAlgebra
  haveI : IsScalarTower k Γ(X, U') Γ(Y, W') :=
    IsScalarTower.of_algebraMap_eq' (appLE_comp_algX' p q hW'U').symm
  let φ := MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a))
  letI : Algebra (MvPolynomial ι Γ(X, U')) Γ(Y, W') := φ.toAlgebra
  haveI : IsScalarTower Γ(X, U') (MvPolynomial ι Γ(X, U')) Γ(Y, W') :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change _ = φ (MvPolynomial.C r)
      simp [φ]; rfl
  haveI : Algebra.Etale (MvPolynomial ι Γ(X, U')) Γ(Y, W') := hC
  obtain ⟨⟨bT, hbT⟩, hsm⟩ := GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale Γ(X, U') Γ(Y, W') ι
  haveI := hsm
  haveI : Subsingleton (Algebra.H1Cotangent Γ(X, U') Γ(Y, W')) :=
    Algebra.FormallySmooth.subsingleton_h1Cotangent
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange k Γ(X, U') Γ(Y, W')) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k Γ(X, U') Γ(Y, W') y).1 hy
    rw [Subsingleton.elim z 0, map_zero]
  obtain ⟨b, hb⟩ := exists_basis_of_exact
    (KaehlerDifferential.mapBaseChange k Γ(X, U') Γ(Y, W'))
    (KaehlerDifferential.map k Γ(X, U') Γ(Y, W') Γ(Y, W')) hinj
    (KaehlerDifferential.exact_mapBaseChange_map k Γ(X, U') Γ(Y, W'))
    (bR.baseChange Γ(Y, W')) bT (fun a ↦ KaehlerDifferential.D k Γ(Y, W') (resG Y hW' (N a)))
    (fun a ↦ by rw [hbT, KaehlerDifferential.map_D]; simp [φ, RingHom.algebraMap_toAlgebra])
  refine ⟨hW'a, isFreeGen_dForm _ (b.reindex o.symm) fun a ↦ ?_⟩
  rw [Module.Basis.reindex_apply, Equiv.symm_symm, hb]
  rcases o a with i | i
  · simp only [Sum.elim_inl, Module.Basis.baseChange_apply, KaehlerDifferential.mapBaseChange_tmul,
      one_smul, hbR, dFun, KaehlerDifferential.map_D]
    refine congrArg (KaehlerDifferential.D k Γ(Y, W')) ?_
    rw [RingHom.algebraMap_toAlgebra, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.resG_appLE]
  · rfl

end GlobalTheory.TopFrameEt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopFormFrameBaseCoordinatesAddVariablesEtaleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTopFormFrame_base_coordinates_add_variables_etale : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ X) (p' : Y ⟶ Sp k), q ≫ p = p' → ∀ (m D : ℕ), SmoothOfRelativeDimension m p → ∀ (ι : Type) (o : Fin D ≃ Fin m ⊕ ι) (U U' : X.Opens) (hU' : U' ≤ U), IsAffineOpen U → ∀ (W W' : Y.Opens) (hW' : W' ≤ W), IsAffineOpen W → IsAffineOpen W' → ∀ (hWU : W ≤ q ⁻¹ᵁ U), W' ≤ q ⁻¹ᵁ U' → ∀ (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N).Etale → ∀ (x : Fin m → Γ(X, U)), TopForm.IsFrame (TopForm.dOn p fun i => resG X hU' (x i)) → TopForm.IsFrame (TopForm.dOn p' fun a => resG Y hW' (Sum.elim (fun i => (q.appLE U W hWU).hom (x i)) N (o a))) := by
  first | exact @GlobalTheory.TopFrameEt.isFrame_etale | exact GlobalTheory.TopFrameEt.isFrame_etale | (intros; apply GlobalTheory.TopFrameEt.isFrame_etale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsE8WeightedBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration

def e8 (W : Matrix (Fin 8) (Fin 8) ℤ) : Matrix (Fin 8) (Fin 8) ℤ := W + W.transpose

def actMat (W : Matrix (Fin 8) (Fin 8) ℤ) : Fin 2 → Matrix (Fin 8) (Fin 8) ℤ :=
  ![(e8 W).adjugate * W, (e8 W).adjugate * W.transpose]

variable {S : Scheme.{0}}

def IsProd {A B : Over S} [GrpObj A] [GrpObj B] (pr : Fin 8 → (A ⟶ B)) : Prop :=
  (∀ a, IsMonHom (pr a)) ∧ ∀ (T : Over S) (y : Fin 8 → (T ⟶ B)), ∃! x : T ⟶ A, ∀ a, x ≫ pr a = y a

def IsE8WeightedBundle (W : Matrix (Fin 8) (Fin 8) ℤ) {A B : Over S} [GrpObj A] [GrpObj B] (pr : Fin 8 → (A ⟶ B))
    (L : LB A.left) (M : LB B.left) : Prop :=
  LBIso L (LB.LinComb M (K := (Fin 8 × Fin 8) × Fin 4) (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2)
    (fun k => -(W k.1.1 k.1.2 * negε k.2)))

def IsPPFib (B : Over S) [GrpObj B] (g : ℕ) (M : RigLB B) : Prop :=
  IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ Nonempty (CubicalStr B M) ∧ RelAmple B M.L ∧ KTriv B M.L

def ActsBy {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)) (f : A ⟶ A)
    (m : Matrix (Fin 8) (Fin 8) ℤ) : Prop :=
  ∀ a, f ≫ pr a = ∏ b, pr b ^ m a b

end GlobalTheory.Poinc.Sep.E8Fibration

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtChar
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GSum

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}


open Classical in
def base (X₁ : Setup F W i) (z₁ : X₁.M.Z) : X₁.S.Gam :=
  if h : (X₁.S.supI X₁.M z₁).Nonempty then h.some else 0

def wtChar (D : Deep X₁ ε₁) (T : AddSubgroup D.X.S.Gam) (a : D.X.S.Gam) : T →+ ZMod D.X.S.N where
  toFun t := ZMod.castHom (dvd_mul_left D.X.S.N D.X.S.r) (ZMod D.X.S.N) (eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a))
  map_zero' := by simp [eStd]
  map_add' := by
    intro s t
    rw [← map_add (f := _)]
    congr 1
    simp only [eStd, AddSubgroup.coe_add, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring


open Classical in
def lift (D : Deep X₁ ε₁) (z₂ : D.X.M.Z) (κ : X₁.S.Gam) : D.X.S.Gam :=
  if h : ∃ h' ∈ D.X.S.HH D.X.M z₂, D.m • h' = D.lab κ then h.choose else 0

def part (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z) (a : D.X.S.Gam) (κ : X₁.S.HH X₁.M z₁) : D.X.Ω₁ :=
  (∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj (D.X.S.TT D.X.M z₂) (wtChar D _ a) j D.X.ρ.i₀) *
      D.X.S.ev (lift D z₂ (κ : X₁.S.Gam)) j) / D.X.S.th (D.lab (base X₁ z₁))

end GlobalTheory.Poinc.GSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNorms
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.CoverNorm.Isom

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem asIdeal_p_j (V : Cover Y) (y : V.G) : (V.p (V.j y)).asIdeal = ⊥ := by
  rw [← Scheme.Hom.comp_apply, V.pb.w, Scheme.Hom.comp_apply]
  change Ideal.comap (algebraMap (𝓞 F) F) ((V.π ≫ Y.str) y).asIdeal = ⊥
  have := ((V.π ≫ Y.str) y).isPrime
  rw [Ideal.eq_bot_of_prime ((V.π ≫ Y.str) y).asIdeal]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

theorem mem_range_j (V : Cover Y) {x : V.X} (hx : (V.p x).asIdeal = ⊥) : x ∈ Set.range V.j := by
  rw [← V.pb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, V.pb.isoPullback.hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]
  refine ⟨IsLocalRing.closedPoint F, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
  change Ideal.comap (algebraMap (𝓞 F) F) (IsLocalRing.maximalIdeal F) = ⊥
  rw [IsLocalRing.maximalIdeal_eq_bot]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

theorem j_gen_specializes (V : Cover Y) : V.j (genericPoint V.G) ⤳ genericPoint V.X := by
  have h0 : (V.p (genericPoint V.X)).asIdeal = ⊥ :=
    eq_bot_iff.2 (((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2
      ((genericPoint_specializes (V.j (genericPoint V.G))).map V.p.continuous))).trans
        (asIdeal_p_j V _).le)
  obtain ⟨y, hy⟩ := mem_range_j V h0
  exact hy ▸ (genericPoint_specializes y).map V.j.continuous

theorem cxPts_from_generic_fibre (V : Cover Y) (τ : 𝓞 F →+* ℂ) (y' : CxPts V.p τ) :
    ∃ σ : F →+* ℂ, σ.comp (algebraMap (𝓞 F) F) = τ ∧ ∃ z : CxPts (V.π ≫ Y.str) σ, y'.1 = z.1 ≫ V.j := by
  have hτ := ringOfIntegers_hom_complex_injective F τ
  obtain ⟨σ, hσ⟩ : ∃ σ : F →+* ℂ, σ.comp (algebraMap (𝓞 F) F) = τ :=
    ⟨IsFractionRing.lift (K := F) hτ, RingHom.ext fun x => IsFractionRing.lift_algebraMap (K := F) hτ x⟩
  refine ⟨σ, hσ, ?_⟩
  have hw : y'.1 ≫ V.p = spMap σ ≫ spMap (algebraMap (𝓞 F) F) :=
    y'.2.trans ((congrArg spMap hσ.symm).trans (spMap_comp _ _))
  exact ⟨⟨V.pb.lift y'.1 _ hw, V.pb.lift_snd _ _ _⟩, (V.pb.lift_fst _ _ _).symm⟩

end GlobalTheory.CoverNorm.Isom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorPotentialIsSNCBoundary
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O
open GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh

namespace GlobalTheory.DivSec

theorem exists_affine_germ_eq : ∀ (Y : Scheme.{0}) (y : Y) (n : ℕ) (r : Fin n → Y.presheaf.stalk y),
    ∃ (V : Y.affineOpens) (hy : y ∈ V.1) (F : Fin n → Γ(Y, V.1)), ∀ j, Y.presheaf.germ V.1 y hy (F j) = r j := by
  intro Y y n r
  classical
  choose U hU s hs using fun j => TopCat.Presheaf.germ_exist Y.presheaf (r j)
  have hmem : ∀ t : Finset (Fin n), y ∈ t.inf U := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      rw [Finset.inf_insert]
      exact ⟨hU a, ih⟩
  obtain ⟨V, hV, hyV, hVO⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (hmem Finset.univ)
  have hle : ∀ j, V ≤ U j := fun j => le_trans hVO (Finset.inf_le (Finset.mem_univ j))
  refine ⟨⟨V, hV⟩, hyV, fun j => resG Y (hle j) (s j), fun j => ?_⟩
  rw [← hs j]
  exact Y.presheaf.germ_res_apply (homOfLE (hle j)) y hyV (s j)

theorem isCompatChart_of_holAlong : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (n : ℕ)
    (B : FinHolAtlas n (CxPts p σ)), IsAlgAtlas B → ∀ (e : OpenPartialHomeomorph (CxPts p σ) (Fin n → ℂ)),
    (∀ j, HolAlong e.source fun x => e x j) → IsHolTo e.target (fun z => (e.symm z).1) → IsCompatChart B e := by
  intro k _ Y p σ n B hB e hhol hsymm j
  obtain ⟨c, hcj⟩ := hB j
  rw [hcj]
  constructor
  · refine (c.analyticOnNhd_finChart_iff e.open_source e).2 ?_
    refine differentiableOn_pi.2 fun i => ?_
    have hO := GlobalTheory.ChartGlue.isOpen_over c.e e.open_source
    exact hhol i _ _ c.e.symm hO (GlobalTheory.ShFam.Hor.Sec.isHolTo_symm c hO Set.inter_subset_left) (fun b hb => hb.2)
  · have hO : IsOpen (e.target ∩ e.symm ⁻¹' c.finChart.source) := e.isOpen_inter_preimage_symm c.finChart.open_source
    refine (SCV.analyticOnNhd_iff_differentiableOn hO).2 ?_
    intro b hb
    have h1 := GlobalTheory.TrueCx.TorHolo.differentiableAt_chart e.open_target hsymm c hb.1 hb.2
    exact ((EuclideanSpace.equiv (Fin n) ℂ).differentiable.differentiableAt.comp b h1).differentiableWithinAt

end GlobalTheory.DivSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAlongIdIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

noncomputable section
namespace GlobalTheory.PrincSubring

def powLB {S : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) : LB (Out.powObj A 8).left :=
  LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (Out.powPr A uv.1) (Out.powPr A uv.2)).left)
    fun uv => GlobalTheory.W8 uv.1 uv.2

def KerAlong {S : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) {S' : Scheme.{0}} (g : S' ⟶ S) : Prop :=
  ∀ (T : Over S) (a : T.left ⟶ S'), a ≫ g = T.hom → ∀ x : T ⟶ A, IsTrivial (slice A P x) → x = 1

end GlobalTheory.PrincSubring
end
end
