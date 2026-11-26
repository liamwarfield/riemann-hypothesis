module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselVertexLatticeSplitsAlongWitt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOnWeilDatumTransportAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffPolynomialEqZeroOfVanishingOnGLFamily
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.MtRead

variable {D : D7}

def IdFrame {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) : Prop :=
  ∃ hn : V.rank = n, ∀ κ a b, finMat D.sp.cm.sig V.gram (P.ψ κ) a b =
    (GlobalTheory.Mem.R3.swapCast hF).symm ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn b))

variable {S T : HSp D} {n : ℕ}

def RatMatch (φ : GAf D.host.E n ≃* Bridge.Gf S) : Prop :=
  (∀ γ : ReciprocityTheory.Aut.GQ D.host.E n, ∃ γ', Bridge.ratF S γ' = φ γ) ∧
    ∀ γ', ∃ γ : ReciprocityTheory.Aut.GQ D.host.E n, Bridge.ratF S γ' = φ γ

def WtMap (B : Base S T) (φ : GAf D.host.E n ≃* Bridge.Gf S) (R : Type) [CommRing R] [IsDomain R] (e : FractionRing R →+* ℂ)
    {W : Type} [AddCommGroup W] [Module (FractionRing R) W] (ρ : Representation (FractionRing R) (ReciprocityTheory.Aut.GQ D.host.E n) W)
    (ω : W →ₛₗ[e] PolF D T.rank S.rank) : Prop :=
  Function.Injective ω ∧ (∀ w, ω w ∈ B.valSpace) ∧
    (∀ (γ : ReciprocityTheory.Aut.GQ D.host.E n) (γ' : Formalism.L2.Theta.GQ S), Bridge.ratF S γ' = φ γ →
      ∀ w, ω (ρ γ w) = B.act (γ' : GA D S) (ω w)) ∧
    (∀ h, ∀ x ∈ B.coefLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range h, x ∈ Set.range ω) ∧
    ∀ h w, ∃ c : R, c ≠ 0 ∧
      ω (algebraMap R (FractionRing R) c • w) ∈ B.coefLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range h

def LevMatch (B : Base S T) (t : Twist D Circle) (φ : GAf D.host.E n ≃* Bridge.Gf S) {K : Type} [Field K] (e : K →+* ℂ)
    (J : Subgroup (GAf D.host.E n)) (χ : J →* Kˣ) : Prop :=
  (∀ g, g ∈ J ↔ φ g ∈ B.levJ t) ∧
    ∀ g (h : g ∈ J) (h' : φ g ∈ B.levJ t), e ((χ ⟨g, h⟩ : Kˣ) : K) = ((B.levLam t ⟨φ g, h'⟩ : ℂˣ) : ℂ)

theorem finite_kP (P : Pl D.host.E) : Finite (kP P) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot

theorem isOfFinOrder_levFn {m : ℕ} (β : GL (Fin m) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ m) (x : GL (Fin m) (Lev.EAf D)) :
    IsOfFinOrder (levFn β L x) := by
  haveI : ∀ P : Pl D.host.E, Finite (kP P) := finite_kP
  have hprod : ∀ {ι : Type} (s : Finset ι) (f : ι → ℂˣ), (∀ i ∈ s, IsOfFinOrder (f i)) → IsOfFinOrder (∏ i ∈ s, f i) :=
    fun s f h => Finset.prod_induction f IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) IsOfFinOrder.one h
  unfold levFn
  refine (IsOfFinOrder.mul ?_ (hprod _ _ fun P _ => hprod _ _ fun c _ => ?_)).mul (hprod _ _ fun P _ => ?_)
  · unfold ext1
    split_ifs with h
    · exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
    · exact IsOfFinOrder.one
  · exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
  · exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)

theorem mem_range_of_finOrder {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (e : FractionRing R →+* ℂ)
    {x : FractionRing R} {z : ℂˣ} (hz : IsOfFinOrder z) (h : e x = z) : (z : ℂ) ∈ (e.comp (algebraMap R (FractionRing R))).range := by
  obtain ⟨m, hm, h1⟩ := hz.exists_pow_eq_one
  have h2 : x ^ m = 1 := e.injective (by rw [map_pow, h, ← Units.val_pow_eq_pow_val, h1, map_one, Units.val_one])
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow (R := R) hm (h2 ▸ isIntegral_one))
  exact ⟨y, by rw [RingHom.comp_apply, hy, h]⟩

theorem read_abstract {G G' Γ' R W P I V : Type} [Group G] [Group G'] [Group Γ'] [CommRing R] [IsDomain R] [AddCommGroup W]
    [Module (FractionRing R) W] [AddCommGroup P] [Module ℂ P] [Finite I] [AddCommGroup V] [Module (FractionRing R) V]
    (φ : G ≃* G') (Γ J : Subgroup G) (J' : Subgroup G') (ι : Γ' → G') (e : FractionRing R →+* ℂ) (ρ : Γ → W → W) (χ : J → FractionRing R)
    (act : Γ' → P → P) (lam : J' → ℂ) (ω : W →ₛₗ[e] P) (val : Set P)
    (L : G' → Submodule (e.comp (algebraMap R (FractionRing R))).range P)
    (A : Submodule (FractionRing R) (G → W))
    (hA : ∀ f, f ∈ A ↔ (∀ (γ : Γ) g, f (γ * g) = ρ γ (f g)) ∧ ∀ (κ : J) g, f (g * κ) = χ κ • f g)
    (M : Set (G' → P))
    (hM : ∀ F, F ∈ M ↔ ((∀ h, F h ∈ val) ∧ ∀ γ h (k : J'), F (ι γ * h * k) = lam k • act γ (F h)) ∧ ∀ h, F h ∈ L h)
    (h1 : ∃ γ, ι γ = 1 ∧ ∀ x, act γ x = x) (hl1 : lam 1 = 1)
    (hr1 : ∀ γ : Γ, ∃ γ', ι γ' = φ γ) (hr2 : ∀ γ', ∃ γ : Γ, ι γ' = φ γ)
    (hinj : Function.Injective ω) (hval : ∀ w, ω w ∈ val) (heq : ∀ (γ : Γ) γ', ι γ' = φ γ → ∀ w, ω (ρ γ w) = act γ' (ω w))
    (hrange : ∀ h, ∀ x ∈ L h, x ∈ Set.range ω) (hden : ∀ h w, ∃ c : R, c ≠ 0 ∧ ω (algebraMap R (FractionRing R) c • w) ∈ L h)
    (hJ1 : ∀ g, g ∈ J ↔ φ g ∈ J') (hJ2 : ∀ g (h : g ∈ J) (h' : φ g ∈ J'), e (χ ⟨g, h⟩) = lam ⟨φ g, h'⟩)
    (hlam : ∀ k, lam k ∈ (e.comp (algebraMap R (FractionRing R))).range)
    (hact : ∀ γ h (k : J'), ∀ x ∈ L h, act γ x ∈ L (ι γ * h * k))
    (y : I → G') (hy : ∀ h, ∃ i γ, ∃ k : J', h = ι γ * y i * k) (real : V ≃ₗ[FractionRing R] A) :
    ∃ r : V →ₛₗ[e] (G' → P), Function.Injective r ∧ (∀ F ∈ M, F ∈ Set.range r) ∧
      Submodule.span (FractionRing R) {f | r f ∈ M} = ⊤ ∧ ∀ f g, r f (φ g) = ω ((real f).1 g) := by
  let r : V →ₛₗ[e] (G' → P) :=
    { toFun := fun f h => ω ((real f).1 (φ.symm h))
      map_add' := fun f f' => by funext h; simp
      map_smul' := fun c f => by funext h; simp [map_smulₛₗ] }
  have hr_apply : ∀ f g, r f (φ g) = ω ((real f).1 g) := fun f g => by
    change ω ((real f).1 (φ.symm (φ g))) = _
    rw [φ.symm_apply_apply]
  have hlaw : ∀ f γ h (k : J'), r f (ι γ * h * k) = lam k • act γ (r f h) := fun f γ' h k => by
    obtain ⟨γ, hγ⟩ := hr2 γ'
    obtain ⟨g, rfl⟩ := φ.surjective h
    obtain ⟨k, hk⟩ := k
    obtain ⟨κ, rfl⟩ := φ.surjective k
    have hκ := (hJ1 κ).2 hk
    change r f (ι γ' * φ g * φ κ) = _
    have h2 := (hA _).1 (real f).2
    rw [hγ, ← map_mul, ← map_mul, hr_apply, hr_apply, h2.2 ⟨κ, hκ⟩, h2.1, map_smulₛₗ, heq γ γ' hγ, hJ2 κ hκ hk]
  refine ⟨r, fun f f' h => ?_, fun F hF => ?_, ?_, hr_apply⟩
  · refine real.injective (Subtype.ext (funext fun g => hinj ?_))
    rw [← hr_apply, ← hr_apply, h]
  · obtain ⟨⟨-, hF3⟩, hF2⟩ := (hM F).1 hF
    choose u hu using fun g => hrange (φ g) _ (hF2 (φ g))
    have hmem : u ∈ A := by
      refine (hA u).2 ⟨fun γ g => hinj ?_, fun κ g => hinj ?_⟩
      · obtain ⟨γ', hγ⟩ := hr1 γ
        have := hF3 γ' (φ g) 1
        rw [heq γ γ' hγ, hu, hu, map_mul, ← hγ]
        simpa [hl1] using this
      · have hk := (hJ1 κ).1 κ.2
        obtain ⟨γ, hγ, hγ'⟩ := h1
        have := hF3 γ (φ g) ⟨φ κ, hk⟩
        rw [map_smulₛₗ, hu, hu, map_mul, hJ2 κ κ.2 hk]
        simpa [hγ, hγ'] using this
    refine ⟨real.symm ⟨u, hmem⟩, funext fun h => ?_⟩
    obtain ⟨g, rfl⟩ := φ.surjective h
    rw [hr_apply, real.apply_symm_apply, hu]
  · refine eq_top_iff.2 fun f _ => ?_
    haveI := Fintype.ofFinite I
    classical
    choose c hc0 hcm using fun i => hden (y i) ((real f).1 (φ.symm (y i)))
    have hd : algebraMap R (FractionRing R) (∏ i, c i) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact Finset.prod_ne_zero_iff.2 fun i _ => hc0 i
    have hm : r (algebraMap R (FractionRing R) (∏ i, c i) • f) ∈ M := by
      refine (hM _).2 ⟨⟨fun h => hval _, hlaw _⟩, fun h => ?_⟩
      obtain ⟨i, γ, k, rfl⟩ := hy h
      have e1 : r (algebraMap R (FractionRing R) (∏ i, c i) • f) (y i) =
          e (algebraMap R (FractionRing R) (∏ j ∈ Finset.univ.erase i, c j)) •
            ω (algebraMap R (FractionRing R) (c i) • (real f).1 (φ.symm (y i))) := by
        rw [← map_smulₛₗ, smul_smul, ← map_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
        change ω ((real (_ • f)).1 _) = _
        rw [map_smul]
        rfl
      have h2 : r (algebraMap R (FractionRing R) (∏ i, c i) • f) (y i) ∈ L (y i) := by
        rw [e1]
        exact Submodule.smul_mem _ (⟨_, _, rfl⟩ : (e.comp (algebraMap R (FractionRing R))).range) (hcm i)
      rw [hlaw]
      exact Submodule.smul_mem _ (⟨_, hlam k⟩ : (e.comp (algebraMap R (FractionRing R))).range) (hact γ _ k _ h2)
    have := Submodule.smul_mem _ (algebraMap R (FractionRing R) (∏ i, c i))⁻¹ (Submodule.subset_span (R := FractionRing R)
      (s := {f | r f ∈ M}) hm)
    rwa [inv_smul_smul₀ hd] at this

theorem read_cell (B : Base S T) (hB : B.Good) (t : Twist D Circle) (φ : GAf D.host.E n ≃* Bridge.Gf S) (R : Type) [CommRing R]
    [IsDomain R] [IsIntegrallyClosed R] (e : FractionRing R →+* ℂ)
    (hc : IsCoefRing (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range)
    {W : Type} [AddCommGroup W] [Module (FractionRing R) W] (ρ : Representation (FractionRing R) (ReciprocityTheory.Aut.GQ D.host.E n) W)
    (J : Subgroup (GAf D.host.E n)) (χ : J →* (FractionRing R)ˣ) (ω : W →ₛₗ[e] PolF D T.rank S.rank)
    (hr : RatMatch φ) (hω : WtMap B φ R e ρ ω) (hJ : LevMatch B t φ e J χ) {I : Type} [Finite I] (y : I → Bridge.Gf S)
    (hy : Bridge.IsReps (Bridge.ratF S) (B.levJ t) y) {V : Type} [AddCommGroup V] [Module (FractionRing R) V]
    (real : V ≃ₗ[FractionRing R] NX.TypeSpF D.host.E n (FractionRing R) ρ J χ) :
    ∃ r : V →ₛₗ[e] (Bridge.Gf S → PolF D T.rank S.rank), Function.Injective r ∧
      (∀ F ∈ B.mtLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range t, F ∈ Set.range r) ∧
      Submodule.span (FractionRing R)
        {f | r f ∈ B.mtLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range t} = ⊤ ∧
      ∀ f g, r f (φ g) = ω ((real f).1 g) := by
  refine read_abstract φ (ReciprocityTheory.Aut.GQ D.host.E n) J (B.levJ t) (Bridge.ratF S) e (fun γ => ρ γ) (fun κ => (χ κ : FractionRing R))
    (fun γ => B.act (γ : GA D S)) (fun k => ((B.levLam t k : ℂˣ) : ℂ)) ω B.valSpace
    (B.coefLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range) _ (fun _ => Iff.rfl) _
    (fun F => (B.mem_mtLat _ _ _).trans (and_congr_left' B.mem_formsC)) ⟨1, MonoidHom.map_one _, fun x => ?_⟩ ?_ hr.1 hr.2
    hω.1 hω.2.1 hω.2.2.1 hω.2.2.2.1 hω.2.2.2.2 hJ.1 hJ.2 (fun k => ?_)
    (fun γ h k x hx => Base.act_mem_coefLat hB.frame hc γ h k (Base.mem_St_of_mem_levJ k.2) hx) y
    (fun h => (hy h).exists.imp fun _ h => h) real
  · change B.act 1 x = x
    rw [MonoidHom.map_one]
    rfl
  · change ((B.levLam t 1 : ℂˣ) : ℂ) = 1
    rw [MonoidHom.map_one]
    rfl
  · obtain ⟨k, hk⟩ := k
    obtain ⟨κ, rfl⟩ := φ.surjective k
    exact mem_range_of_finOrder e (isOfFinOrder_levFn _ _ _) (hJ.2 κ ((hJ.1 κ).2 hk) hk)

theorem admissible_twist_of_twisting_character {i : D.ntw.Tw} {k : ℕ} {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ}
    (h : TwOK i k Q ψ) : NX.AdmTw D i k Q ψ := by
  obtain ⟨hsplit, hdisj, hopen, hanti, hzk, hram, -⟩ := h
  have hS : ∀ P ∈ Q, P ∉ D.ntw.S0 i := fun P hP => Finset.disjoint_left.1 hdisj hP
  have hz : D.ntw.zk i k ^ (D.ntw.l i ^ k) = 1 := Units.ext (by simpa using (D.ntw.zk_prim i k).pow_eq_one)
  refine ⟨fun P hP => ⟨hsplit P hP, fun h => hS P hP (D.ntw.twistExcludedPlaces_contains_residueChar i h)⟩,
    fun P hP => ⟨fun h => hS P hP (D.ntw.primes_subset_exceptional i h), fun k' h => hS P hP (D.ntw.placesOver_subset_exceptional i k' h)⟩, hopen, hanti, fun σ => ⟨k, ?_⟩,
    fun P hP A hA σ hσ => ?_⟩
  · obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  · by_contra h
    exact hP ((hram P A hA).1 ⟨σ, hσ, h⟩)

theorem eq_of_infOf_eq {m : ℕ} {a b : Fin m → ℤ} (ha : Antitone a) (hb : Antitone b) (h : NG.infOf a = NG.infOf b) : a = b := by
  have key : ∀ c : Fin m → ℤ, NG.infOf c =
      (Finset.univ.val.map fun i : Fin m => c i - (i : ℕ)).map fun z : ℤ => (z : ℂ) + ((m : ℂ) - 1) / 2 := fun c => by
    rw [NG.infOf, Multiset.map_map]
    congr 1
    funext i
    simp only [Function.comp_apply]
    push_cast
    ring
  rw [key, key] at h
  have h2 := Multiset.map_injective (fun x y hxy => by exact_mod_cast add_right_cancel hxy) h
  have sa : ∀ c : Fin m → ℤ, Antitone c → StrictAnti fun i : Fin m => c i - (i : ℕ) := fun c hc i j hij => by
    have := hc hij.le
    have h3 : (i : ℕ) < j := hij
    beta_reduce
    omega
  have hr : Set.range (fun i : Fin m => a i - (i : ℕ)) = Set.range fun i : Fin m => b i - (i : ℕ) := by
    ext z
    have := congrArg (z ∈ ·) h2
    simpa using this
  have h4 := ((sa a ha).range_inj (sa b hb)).1 hr
  funext i
  have := congrFun h4 i
  omega

end GlobalTheory.MtRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidal
noncomputable section

namespace GlobalTheory.HodgeOfTrue

open GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)

section CharUnr

open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [_root_.NumberField.IsTotallyComplex E]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

end CharUnr

section Twist

variable {Γ k : Type} [Group Γ] [Field k] {a : ℕ}

theorem coe_scalar (u : kˣ) : ((GeneralLinearGroup.scalar (Fin a) u : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
    (u : k) • (1 : Matrix (Fin a) (Fin a) k) := by
  ext i j
  by_cases h : i = j <;> simp [GeneralLinearGroup.scalar, Matrix.diagonal, Matrix.one_apply, h]

def twistBy (c : Γ →* kˣ) (r : Γ →* GL (Fin a) k) : Γ →* GL (Fin a) k where
  toFun g := GeneralLinearGroup.scalar (Fin a) (c g) * r g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, map_mul]
    have e : GeneralLinearGroup.scalar (Fin a) (c h) * r g = r g * GeneralLinearGroup.scalar (Fin a) (c h) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_scalar, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    simp only [mul_assoc]
    rw [← mul_assoc (GeneralLinearGroup.scalar (Fin a) (c h)), e, mul_assoc]

theorem coe_twistBy (c : Γ →* kˣ) (r : Γ →* GL (Fin a) k) (g : Γ) :
    (twistBy c r g : Matrix (Fin a) (Fin a) k) = (c g : k) • (r g : Matrix (Fin a) (Fin a) k) := by
  change ((GeneralLinearGroup.scalar (Fin a) (c g) * r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) = _
  rw [Units.val_mul, coe_scalar, Matrix.smul_mul, Matrix.one_mul]

end Twist

section G
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem isPolarized_twist {π : CuspSub E a} (hc : π.IsCsd) {ν : HChar E} {s : ℝ} (hν : ν.IsAbsPow s) :
    ∃ ψ, IsPolarized (π.twist ν) ψ := by
  obtain ⟨ψ, h1, h2⟩ := GlobalTheory.PolChar.exists_compNorm_eq hν
  refine ⟨ψ * quadChar E ^ a, ?_⟩
  constructor
  · intro v
    change ψ.locInf v (-1) * (quadChar E ^ a).locInf v (-1) = (-1) ^ a
    rw [locInf_pow, h2, quadChar_locInf, one_mul]
  · rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one, h1]
    exact GlobalTheory.T.isConjugateDualTwistBy_twist_of_conjSelfDual hc ν

theorem expo_mul (χ χ' : HChar E) (τ : E →+* ℂ) : expo (χ * χ') τ = expo χ τ + expo χ' τ := by
  have h := (CG.hasInfChar_ofChar χ τ).twist χ'
  rw [CG.twist_ofChar, Multiset.map_singleton] at h
  have := h.infChar_eq
  rw [CG.infChar_ofChar] at this
  simpa using this

theorem expo_inv (χ : HChar E) (τ : E →+* ℂ) : expo χ⁻¹ τ = -expo χ τ := by
  have := expo_mul χ χ⁻¹ τ
  rw [mul_inv_cancel, CG.expo_one] at this
  linear_combination -this

theorem isSSRep_twistBy {Γ K : Type} [Group Γ] [Field K] {n : ℕ} (c : Γ →* Kˣ) {ρ : Γ →* GL (Fin n) K} (hs : IsSSRep ρ) :
    IsSSRep (twistBy c ρ) := by
  have key : ∀ W, IsInv (twistBy c ρ) W ↔ IsInv ρ W := fun W => forall_congr' fun g => forall₂_congr fun v _ => by
    rw [coe_twistBy, Matrix.smul_mulVec, W.smul_mem_iff (c g).ne_zero]
  exact fun W hW => (hs W ((key W).1 hW)).imp fun W' h' => ⟨(key W').2 h'.1, h'.2⟩

theorem conj_of_frob (hD : ∀ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite → Dense {g : G E Ω | ∃ w ∉ S, ∃ B : ValuationSubring Ω,
      IsPlaceOver (F := E) B w ∧ IsFrob (F := E) B (normV w) g})
    {r r' : G E Ω →* GL (Fin a) (Qbar l)} (hc : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l)))
    (hc' : Continuous fun g => (r' g : Matrix (Fin a) (Fin a) (Qbar l))) (hs : IsSSRep r) (hs' : IsSSRep r')
    (h : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ (B : ValuationSubring Ω) (g : G E Ω),
      IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g →
      (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly = (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly) :
    ∃ A : GL (Fin a) (Qbar l), ∀ g, r' g = A * r g * A⁻¹ := _root_.GlobalTheory.TripleLocal.conj_of_frob (r := r) (r' := r') hD hc hc' hs hs' h

theorem potCrys_twistBy {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (c : ↥Gw →* (Om l)ˣ) (r : ↥Gw →* GL (Fin a) (Om l))
    (hr : IsPotCrysAt P Bw r) (hc : IsCrysAt P Bw ((GeneralLinearGroup.scalar (Fin 1)).comp c)) :
    IsPotCrysAt P Bw (twistBy c r) := _root_.GlobalTheory.TripleLocal.potCrys_twistBy (P := P) (AI := AI) (Gw := Gw) (O := O) T Bw c r hr hc

end G

theorem exists_halfChar (D : D7) : haveI := host_isCMField D.host; ∃ ξ : HChar D.host.E, (∀ v, ξ.UnrAt v) ∧
    (CG.ofChar ξ).IsCsd ∧ (CG.ofChar ξ⁻¹).IsCsd ∧ ∀ τ, ∃ n : ℤ, expo ξ τ = n + 1 / 2 := by
  have := host_isCMField D.host
  obtain ⟨ξ₀, h⟩ := GlobalTheory.Mem.EtaT.etaT_exists D.R D.host
  let ξ : HChar D.host.E := ξ₀
  have hneg : (-1 : ℂˣ)⁻¹ = -1 := inv_eq_of_mul_eq_one_left (by simp)
  refine ⟨ξ, h.unr, isCsd_ofChar_of_res _ _ (Or.inr h.res), isCsd_ofChar_of_res _ _ (Or.inr ⟨fun v k => ?_, fun w k => ?_⟩), fun τ => ?_⟩
  · have e1 : (ξ.resFin v) k = etaFin (↥D.host.F) v k := h.res.1 v k
    have e2 : (ξ⁻¹.resFin v) k = ((ξ.resFin v) k)⁻¹ := by
      simp only [HChar.resFin, MonoidHom.finsetProd_apply, ← Finset.prod_inv_distrib]
      rfl
    rw [e2, e1]
    unfold etaFin
    split_ifs
    · rw [← inv_zpow, hneg]
    · exact inv_one
  · have e1 : (ξ.resInf w) k = etaInf (↥D.host.F) w k := h.res.2 w k
    have e2 : (ξ⁻¹.resInf w) k = ((ξ.resInf w) k)⁻¹ := by
      simp only [HChar.resInf, MonoidHom.finsetProd_apply, ← Finset.prod_inv_distrib]
      rfl
    rw [e2, e1]
    unfold etaInf
    split_ifs
    · exact hneg
    · exact inv_one
  · have hI : Function.Injective fun i => InfinitePlace.mk (embPsi D.host i) := fun i j e => by
      rcases InfinitePlace.mk_eq_iff.1 e with e | e
      · exact GlobalTheory.HalfIntChars.embPsi_inj D.host e
      · exact (GlobalTheory.HalfIntChars.embPsi_ne_conj D.host j i (e.symm.trans (RingHom.ext fun x => rfl))).elim
    obtain ⟨ρ, b, rfl⟩ := GlobalTheory.JumpDictionaryFoundation.exists_embOver D τ
    have h3 := (GlobalTheory.T.heckeChar_exponent_of_infinityType _ ξ).2.2 _ _ _ hI h.inf (D.eTau ρ)
    cases b
    · exact ⟨0, by rw [show GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D ρ false = embPsi D.host (D.eTau ρ) from rfl, h3.1]; simp⟩
    · refine ⟨-1, ?_⟩
      rw [show GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D ρ true = ComplexEmbedding.conjugate (embPsi D.host (D.eTau ρ)) from
        RingHom.ext (GlobalTheory.JumpDictionaryFoundation.embOver_true_apply D ρ), h3.2]
      norm_num

end GlobalTheory.HodgeOfTrue

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateFormsThetaLiftEqThetaSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateFormsThetaLiftEqThetaSeries
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.ConjTwist

def IsTraceFn {H Γ W : Type} [Group H] [Group Γ] [AddCommGroup W] [Module ℂ W] (ι : Γ →* H)
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup H) (χ : J →* ℂˣ) (z₀ : H) (w : W) (f : H → W) : Prop :=
  (∀ z, (¬ ∃ (γ : Γ) (k : J), z = ι γ * z₀ * k) → f z = 0) ∧
    ∀ L : W →ₗ[ℂ] ℂ, (∀ (γ : Γ) (hγ : z₀⁻¹ * ι γ * z₀ ∈ J), L ((χ ⟨_, hγ⟩ : ℂ) • ρ γ⁻¹ w) = L w) →
      L (f z₀) = (Nat.card (Bridge.stab ι J z₀) : ℂ) * L w

theorem IsTraceFn.post {H Γ W : Type} [Group H] [Group Γ] [AddCommGroup W] [Module ℂ W] (ι : Γ →* H)
    (ρ : Γ →* Module.End ℂ W) {J J' : Subgroup H} (hJ : J' = J) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (τ : ℂ ≃+* ℂ) (T : W →+ W)
    (hs : ∀ (a : ℂ) w, T (a • w) = τ a • T w) (hρ : ∀ γ w, T (ρ γ w) = ρ γ (T w))
    (hχ : ∀ k (hk : k ∈ J) (hk' : k ∈ J'), ((χ' ⟨k, hk'⟩ : ℂˣ) : ℂ) = τ ((χ ⟨k, hk⟩ : ℂˣ) : ℂ))
    {z₀ : H} {w : W} {f : H → W} (hf : IsTraceFn ι ρ J χ z₀ w f) :
    IsTraceFn ι ρ J' χ' z₀ (T w) (fun g => T (f g)) := by
  subst hJ
  refine ⟨fun z hz => ?_, fun L hL => ?_⟩
  · show T (f z) = 0
    rw [hf.1 z hz, map_zero]
  · let L' : W →ₗ[ℂ] ℂ :=
      { toFun := fun v => τ.symm (L (T v))
        map_add' := fun a b => by rw [map_add (f := _), map_add (f := _), map_add (f := _)]
        map_smul' := fun a v => by
          rw [hs, map_smul, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
          rfl }
    have hL' : ∀ v, L' v = τ.symm (L (T v)) := fun v => rfl
    have key := hf.2 L' fun γ hγ => by
      rw [hL', hL', hs, hρ, ← hχ _ hγ hγ, hL γ hγ]
    rw [hL', hL'] at key
    have := congrArg τ key
    rwa [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, map_natCast] at this

theorem IsTraceFn.sum_eq {H Hf W : Type} [Group H] [Group Hf] [AddCommGroup W] [Module ℂ W] (p : H →* Hf)
    (hp : Function.Surjective p) (Γ F R : Subgroup H) (ρ : H →* Module.End ℂ W) (J : Subgroup Hf) (χ : J →* ℂˣ)
    (hdec : ∀ u : H, ∃ k ∈ F, ∃ a ∈ R, u = k * a ∧ p k = p u) (hρ : ∀ k ∈ F, ρ k = 1)
    (Cl : Type) [Fintype Cl] (y : Cl → Hf) (hy : Bridge.IsReps (p.comp Γ.subtype) J y)
    (hfin : ∀ k, Finite (Bridge.stab (p.comp Γ.subtype) J (y k))) (h₀ : H) (hh₀ : h₀ ∈ F) (v : W) (f : Hf → W)
    (hf : IsTraceFn (p.comp Γ.subtype) (ρ.comp Γ.subtype) J χ (p h₀) v f) :
    ∃ r : Cl → H, (∀ k, r k ∈ F) ∧
      Bridge.IsReps (p.comp Γ.subtype) J (fun k => p (r k)) ∧
      ∀ {G' X : Type} [Group G'] (x₀ : X) (om : H × G' →* Module.End ℂ (X → ℂ)) (Λ : W →ₗ[ℂ] (X → ℂ)),
        (∀ γ ∈ Γ, ∀ z v, om (γ, 1) (om z (Λ v)) x₀ = om z (Λ v) x₀) → (∀ a ∈ R, ∀ v, om (a, 1) (Λ v) = Λ (ρ a v)) →
        (∀ k ∈ F, ∀ hk : p k ∈ J, ∀ v, om (k, 1) (Λ v) = ((χ ⟨p k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ v) →
        ∀ g : G', ∑ k, ((J.relIndex J : ℕ) : ℂ)⁻¹ * ((Nat.card (Bridge.stab (p.comp Γ.subtype) J (p (r k))) : ℕ) : ℂ)⁻¹ *
          om (r k, g) (Λ (f (p (r k)))) x₀ = om (h₀, g) (Λ v) x₀ := by
  obtain ⟨y', c₀, hy', e₀⟩ := GlobalTheory.TraceLift.exists_isReps_through _ _ hy (p h₀)
  have hlift : ∀ z : Hf, ∃ k ∈ F, p k = z := fun z => by
    obtain ⟨u, hu⟩ := hp z
    obtain ⟨k, hk, -, -, -, e⟩ := hdec u
    exact ⟨k, hk, e.trans hu⟩
  choose σ hσ hσ' using hlift
  let r : Cl → H := Function.update (fun k => σ (y' k)) c₀ h₀
  have hr : ∀ k, r k ∈ F ∧ p (r k) = y' k := fun k => by
    by_cases hk : k = c₀
    · subst hk
      simp only [r, Function.update_self]
      exact ⟨hh₀, e₀.symm⟩
    · simp only [r, Function.update_of_ne hk]
      exact ⟨hσ _, hσ' _⟩
  have hr0 : r c₀ = h₀ := Function.update_self _ _ _
  have hyr : (fun k => p (r k)) = y' := funext fun k => (hr k).2
  have hf0 := GlobalTheory.TraceLift.finite_stab _ _ hy hfin (p h₀)
  obtain ⟨hz, hv⟩ := hf
  refine ⟨r, fun k => (hr k).1, by rw [hyr]; exact hy', fun {G' X} _ x₀ om Λ hom hΛa hΛk g => ?_⟩
  rw [Finset.sum_eq_single c₀ ?_ (fun h => absurd (Finset.mem_univ _) h)]
  · let L₀ : W →ₗ[ℂ] ℂ := (LinearMap.proj x₀ : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (om (h₀, g)) ∘ₗ Λ
    have hL₀ : ∀ v, L₀ v = om (h₀, g) (Λ v) x₀ := fun v => rfl
    have key := hv L₀ fun γ hγ => ?_
    · have hN : ((Nat.card (Bridge.stab (p.comp Γ.subtype) J (p h₀)) : ℕ) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.2 (Nat.card_pos).ne'
      rw [hr0, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_mul, ← hL₀, key, inv_mul_cancel_left₀ hN, hL₀]
    · obtain ⟨k, hk, b, hb, e, e'⟩ := hdec ((γ : H)⁻¹ * h₀)
      have hκ : h₀⁻¹ * k ∈ F := mul_mem (inv_mem hh₀) hk
      have eκ : p (h₀⁻¹ * k) = ((p h₀)⁻¹ * (p.comp Γ.subtype) γ * p h₀)⁻¹ := by
        show p (h₀⁻¹ * k) = ((p h₀)⁻¹ * p γ * p h₀)⁻¹
        rw [map_mul, e', map_mul, map_inv, map_inv]
        group
      have hκ' : p (h₀⁻¹ * k) ∈ J := by rw [eκ]; exact inv_mem hγ
      have eχ : ((χ ⟨_, hκ'⟩ : ℂˣ) : ℂ)⁻¹ = χ ⟨_, hγ⟩ := by
        rw [show (⟨_, hκ'⟩ : J) = ⟨_, hγ⟩⁻¹ from Subtype.ext eκ, map_inv, Units.val_inv_eq_inv_val, inv_inv]
      have eρ : (ρ.comp Γ.subtype) γ⁻¹ v = ρ b v := by
        have h1 := congrArg ρ e
        rw [map_mul, map_mul, hρ _ hh₀, hρ _ hk, mul_one, one_mul] at h1
        rw [← h1]
        rfl
      have e3 : ((h₀, g) : H × G') * (h₀⁻¹ * k, 1) * (b, 1) = (((γ : H)⁻¹, 1) : H × G') * (h₀, g) := by
        rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_inv_cancel_left, e, mul_one, mul_one, one_mul]
      rw [hL₀, hL₀, map_smul, eρ, ← eχ, ← hΛk _ hκ hκ', ← hΛa b hb, ← Module.End.mul_apply, ← Module.End.mul_apply,
        ← map_mul, ← map_mul, e3, map_mul]
      exact hom _ (inv_mem γ.2) _ _
  · intro k _ hk
    rw [hz _ ?_, map_zero, map_zero]
    · simp
    · intro hex
      obtain ⟨j, -, hu⟩ := hy' (y' k)
      refine hk ((hu k ⟨1, 1, by simp⟩).trans (hu c₀ ?_).symm)
      show ∃ (γ : Γ) (m : J), y' k = (p.comp Γ.subtype) γ * y' c₀ * m
      rw [e₀, ← (hr k).2]
      exact hex


set_option maxHeartbeats 4000000 in
theorem thF_eq_ser_of_isTraceFn {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (hV : VStd D i) (t : T0) (h : GA D (Vc D i)) (hh : h ∈ GfC (Vc D i))
    (w : (R.cV i).W) (x : (R.HV i t).H)
    (hx : IsTraceFn (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ (Formalism.IndefR.FWT.fin (Vc D i) h) w ((R.HV i t).e x))
    (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    R.thF i t x (fun ρ => u ρ) g = ser R i t (R.vP i t) u h w g := by
  refine (hR.thP.thF i t).elim fun thP hPF => ?_
  refine (IsTraceFn.sum_eq (finHom (Vc D i)).rangeRestrict (finHom (Vc D i)).rangeRestrict_surjective (GQ (Vc D i))
    (GfC (Vc D i)) (GinfC (Vc D i)) (R.cV i).ρ (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ
    (GlobalTheory.LiftUnfold.exists_fin_mul_real (Vc D i)) (hR.models.cV i).1 _ (R.B.L i t).pres.y (R.B.L i t).pres.reps
    (fun c => Finite.of_equiv _ ((R.B.L i t).pres.stabI c).toEquiv) h hh w ((R.HV i t).e x) hx).elim fun r hr => ?_
  have hf : (R.HV i t).e x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ :=
    (hR.models.HV i t).2.1.le (LinearMap.mem_range_self _ x)
  have hfin : ∀ k ∈ GfC (Vc D i), ∀ hk : Formalism.IndefR.FWT.fin (Vc D i) k ∈ levJ R i t, ∀ P, R.ωP i t (k, 1) (R.ptP i t P) =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨Formalism.IndefR.FWT.fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.ptP i t P := fun k hk hk' =>
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hR.models.inf
      (hR.thP.ωP i t) _ _ _ _ _ (hR.thP.pt_theta i t) k hk 1 (one_mem _) _
      (GlobalTheory.AdTh.LevelLawCore.omega_level_vP_core D G Pl0 T0 A Ks R F hR i t k hV hk hk')
  have key := GlobalTheory.LiftUnfold.integral_theta (hR.thP.ωP i t) (D.sp.V_sig _) (hR.models.vpos i) (R.cV i) (hR.models.cV i) (R.βV i)
    (R.datVt i t) (fun _ => Iff.rfl) hf
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u)) (fun w => hR.thP.pt_theta i t _)
    (fun a ha w => (hR.thP.ioP i t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _)
    (hR.models.νV i t) _ _ r le_rfl (by rw [Subgroup.relIndex_self]; exact one_ne_zero) hr.2.1 hr.1 g
  have key2 := hr.2.2 (0 : WO (Vc D i) (Wc D i)) (R.ωP i t)
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u))
    (fun γ hγ z v => (hR.thP.ωP i t).om_aut γ hγ 1 (one_mem _) _ ((hR.thP.ωP i t).om_pres _ _ (hR.thP.pt_theta i t _)))
    (fun a ha w => (hR.thP.ioP i t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _) g
  have h1 := congrFun (hPF.2 x u) g
  have h2 := hPF.1.eq ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ u) g
  refine h1.trans (h2.trans (Eq.trans ?_ (key.trans key2)))
  rfl


set_option maxHeartbeats 8000000 in
theorem exists_conjForm_thF_eq_ser : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → ∀ (τ : ℂ ≃+* ℂ) (t t' : T0), FixBase T R i τ → ConjTup R τ t t' → ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ∃ (y : (R.HV i t).H) (y' : (R.HV i t').H), ConjForm R i τ c t t' y y' ∧ ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)), R.thF i t y (fun ρ => u ρ) g = ser R i t (R.vP i t) u h (c x) g ∧ R.thF i t' y' (fun ρ => u ρ) g = ser R i t' (R.vP i t') u h (c x') g := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hCore hFW i Tp tup M hPins c hc τ t t' hFix hConj h hh x x' hxx
  have hX := GlobalTheory.CoefExtC.exists_extC_bijective_unique D G Pl0 T0 A T R F κ v₀ hCore hFW i Tp tup M hPins
  refine hX.elim fun c₁ hc₁ => ?_
  have hb : Function.Bijective c :=
    (congrArg (fun f : VsV D i ℂ →ₗ[ℂ] (R.cV i).W => Function.Bijective f) (hc₁.2.2 c hc)).mpr hc₁.2.1
  refine (exists_conjW M hPins c hc hb τ hFix.host).elim fun TW hTW => ?_
  have hs := hTW.1
  have hTc := hTW.2.1
  have hρ := hTW.2.2
  have hZ := (GlobalTheory.T.conjugate_tuples_conjugate_residue_levels D G Pl0 T0 A T R F κ v₀ hCore τ t t' hConj).2.2.2 i hFix
  have hJ := hZ.1
  have hχ := hZ.2
  have hV := hCore.models.HV i t
  have hV' := hCore.models.HV i t'
  have hfin := GlobalTheory.TraceLift.finite_stab (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.reps
    (fun k => Finite.of_equiv _ ((R.B.L i t).pres.stabI k).toEquiv) (Formalism.IndefR.FWT.fin (Vc D i) h)
  refine (GlobalTheory.TraceLift.exists_traceForm (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
    (levEnv _ (R.βV i) (R.datVt i t)).χ (Formalism.IndefR.FWT.fin (Vc D i) h) hfin (c x)).elim fun f hf => ?_
  have hf1 : IsTraceFn (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ (Formalism.IndefR.FWT.fin (Vc D i) h) (c x) f := hf.2
  have hf2 := IsTraceFn.post (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ hJ _ _ τ TW.toAddMonoidHom hs hρ hχ hf1
  have hm2 := post_mem (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ hJ _ _ τ TW.toAddMonoidHom hs hρ hχ hf.1
  refine (LinearMap.mem_range.1 (hV.2.1.ge hf.1)).elim fun y hy => ?_
  refine (LinearMap.mem_range.1 (hV'.2.1.ge hm2)).elim fun y' hy' => ?_
  have hx' : x' = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x :=
    Subtype.ext (hxx.trans (GlobalTheory.CoefModel.mapVV_coe _ _ _).symm)
  have hcx : TW.toAddMonoidHom (c x) = c x' := (hTc x).trans (congrArg c hx').symm
  refine ⟨y, y', fun k => ?_, fun u g => ⟨?_, ?_⟩⟩
  · refine (hb.2 (f (Formalism.IndefR.FWT.fin (Vc D i) k))).elim fun z hz => ?_
    refine ⟨z, GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) z, GlobalTheory.CoefModel.mapVV_coe _ _ _,
      (congrFun hy _).trans hz.symm, (congrFun hy' _).trans ?_⟩
    exact (congrArg TW hz.symm).trans (hTc z)
  · refine thF_eq_ser_of_isTraceFn R F hCore i hPins.lift.std t h hh (c x) y ?_ u g
    rw [hy]
    exact hf1
  · refine thF_eq_ser_of_isTraceFn R F hCore i hPins.lift.std t' h hh (c x') y' ?_ u g
    rw [hy', ← hcx]
    exact hf2

end GlobalTheory.ConjTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateFormsThetaLiftEqThetaSeriesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugateForms_thetaLift_eq_thetaSeries : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → ∀ (τ : ℂ ≃+* ℂ) (t t' : T0), FixBase T R i τ → ConjTup R τ t t' → ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ∃ (y : (R.HV i t).H) (y' : (R.HV i t').H), ConjForm R i τ c t t' y y' ∧ ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)), R.thF i t y (fun ρ => u ρ) g = ser R i t (R.vP i t) u h (c x) g ∧ R.thF i t' y' (fun ρ => u ρ) g = ser R i t' (R.vP i t') u h (c x') g := by
  first | exact @GlobalTheory.ConjTwist.exists_conjForm_thF_eq_ser | exact GlobalTheory.ConjTwist.exists_conjForm_thF_eq_ser | (intros; apply GlobalTheory.ConjTwist.exists_conjForm_thF_eq_ser <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SpecFac

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fock

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem pureTensorO_add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') (P : PolF D T.rank S.rank) :
    pureTensorO ψ θ S T sS sT BS BT (f + f') P =
      pureTensorO ψ θ S T sS sT BS BT f P + pureTensorO ψ θ S T sS sT BS BT f' P := by
  have hA : ∀ k g, IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k g) :=
    fun k g hg => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ hg
  have hl : ∀ l : List (FVar D T.rank S.rank),
      l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) (f + f') =
        l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) f +
        l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) f' ∧
      IsThetaFunO ψ S T (l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) f) ∧
      IsThetaFunO ψ S T (l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) f') := by
    intro l
    induction l with
    | nil => exact ⟨rfl, hf, hf'⟩
    | cons i l ih =>
      simp only [List.foldr_cons]
      refine ⟨?_, hA i _ ih.2.1, hA i _ ih.2.2⟩
      rw [ih.1]
      exact GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ ih.2.1 ih.2.2
  have e : pureTensorO ψ θ S T sS sT BS BT (f + f') =
      pureTensorO ψ θ S T sS sT BS BT f + pureTensorO ψ θ S T sS sT BS BT f' := by
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    simp only [pureTensorO, pureTensorL, LinearMap.add_apply, Module.Basis.constr_basis, opPow]
    exact (hl _).1
  rw [e, LinearMap.add_apply]

theorem theta_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → WO S T → ℂ) (hf : ∀ a ∈ s, IsThetaFunO ψ S T (f a)) :
    IsThetaFunO ψ S T (∑ a ∈ s, c a • f a) :=
  Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
    fun a ha => GlobalTheory.OrientedHeis.theta_smul _ (hf a ha)

theorem pureTensorO_sum (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → WO S T → ℂ) (hf : ∀ a ∈ s, IsThetaFunO ψ S T (f a))
    (P : PolF D T.rank S.rank) :
    pureTensorO ψ θ S T sS sT BS BT (∑ a ∈ s, c a • f a) P = ∑ a ∈ s, c a • pureTensorO ψ θ S T sS sT BS BT (f a) P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    have := GlobalTheory.FiniteFock.pureTensorO_smul ψ θ S T sS sT BS BT 0 0 P
    rwa [zero_smul, zero_smul] at this
  | insert a s ha ih =>
    have hs : ∀ x ∈ s, IsThetaFunO ψ S T (f x) := fun x hx => hf x (Finset.mem_insert_of_mem hx)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      pureTensorO_add hψ hθ sS BS sT BT (GlobalTheory.OrientedHeis.theta_smul _ (hf a (Finset.mem_insert_self a s)))
        (theta_sum s c f hs) P,
      GlobalTheory.FiniteFock.pureTensorO_smul, ih hs]

theorem series_sum {B : Base S T} (hB : B.Good) (ω : PairRep S T) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (f : ι → WO S T → ℂ) (hf : ∀ a ∈ s, IsThetaFunO B.F.ψ S T (f a)) (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T) :
    series B.F ω (∑ a ∈ s, c a • f a) h P g = ∑ a ∈ s, c a * series B.F ω (f a) h P g := by
  simp only [series_apply, Frame.fock]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pureTensorO_sum hB.frame.vac.1 hB.frame.vac.2.inf _ _ _ _ s c f hf P, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

end Fock

section Spec

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem coef_add (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (a a' : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) :
    ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (a + a'))) : X.Ok i k) =
      ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) *
        ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a')) : X.Ok i k) := by
  rw [map_add (f := _), ofAdd_add, map_mul, Units.val_mul, map_mul]


open Classical in
theorem coef_prod (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (a : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) :
    ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) =
      ∏ PP, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (Pi.single PP (a PP)))) : X.Ok i k) := by
  have e : a = ∑ PP, Pi.single PP (a PP) := (Finset.univ_sum_single a).symm
  conv_lhs => rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ofAdd_sum, map_prod, Units.coe_prod, map_prod]


open Classical in
theorem locFn_specLoc (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) :
    (ρ.B i j b).locFn (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (specLoc ρ Y i j b k Q M χ) =
      ∑ a, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) •
        (ρ.B i j b).locFn (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (fun PP y =>
          ((Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j) PP.1 (a PP) y : ℚ) : ℂ)) := by
  funext y
  simp only [Base.locFn, specLoc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coef_prod ρ Y i b k Q M χ a, Finset.prod_mul_distrib]
  ring


open Classical in
theorem vecAt_specLoc (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) :
    (ρ.B i j b).vecAt (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (specLoc ρ Y i j b k Q M χ) =
      ∑ a, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) •
        (ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j)) a := by
  rw [Base.vecAt, locFn_specLoc]
  change (ρ.B i j b).F.vecL (ρ.B i j b).G _ _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul]
  rfl

theorem coord_open (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (Q : Finset (Pl D.host.E)) (M : ℕ) (P : Pl D.host.E) :
    IsOpen ((coord Y i Q M P).ker : Set (G D.host.E N.Om)) := by
  unfold coord
  split_ifs
  · exact Subgroup.isOpen_mono (H₁ := (Y.delU i Q M).ker)
      (fun g hg => by rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hg, map_one])
      (Y.delU_open i Q M)
  · rw [MonoidHom.ker_one]
    exact isOpen_univ

theorem detChar_tw {ρ : Setup X} (hρ : ρ.Good) {Y : NExp D.R D.host D.what₂ D.LL0 N X} (hY : GlobalTheory.UnivChar.IsUnivChar Y)
    (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) (hχ : TwOK i k Q (χ.comp (Y.delU i Q M)))
    (g : GA D (Wc D j)) :
    ((detChar (Wc D j) (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).chi g : Circle) : ℂ) =
      ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (Multiplicative.toAdd
        (detChar (Wc D j) ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) g)))) :
          X.Ok i k) := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym (detRoot (Wc D j) g)
  have hker : IsOpen ((χ.comp (Y.delU i Q M)).ker : Set (G D.host.E N.Om)) :=
    Subgroup.isOpen_mono (H₁ := (Y.delU i Q M).ker)
      (fun g hg => by rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hg, map_one]) (Y.delU_open i Q M)
  have hn : X.l i ^ M ≠ 0 := NeZero.ne _
  have hpow : (χ.comp (Y.delU i Q M)) σ ^ (X.l i ^ M) = 1 := by
    rw [MonoidHom.comp_apply, ← map_pow]
    have e : Y.delU i Q M σ ^ (X.l i ^ M) = 1 := by
      apply Multiplicative.toAdd.injective
      funext v
      rw [toAdd_pow, toAdd_one, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
      rfl
    rw [e, map_one]
  have hd : Multiplicative.toAdd
      (detChar (Wc D j) ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) g) =
        fun P => Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M P.1 σ) := by
    funext PP
    change Multiplicative.toAdd (ρ.rc.pull (coord Y i (admissibleConjugatePairPlaces X i Q M) M PP.1) (detRoot (Wc D j) g)) = _
    rw [ρ.rc.pull_eq (coord_open Y i _ M PP.1) hσ]
  change ((charOf ρ.rc (ρ.eOk i b k) (χ.comp (Y.delU i Q M)) (detRoot (Wc D j) g) : Circle) : ℂ) = _
  rw [charOf_eq ρ.rc (ρ.eOk i b k) hker hσ hn hpow, hd, MonoidHom.comp_apply,
    ← ofAdd_toAdd (Y.delU i Q M σ), delU_eq_spread hY (twSet_of_twOK hχ) (hρ.ch i) σ]

end Spec

theorem specXi_eq_specSer : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X), ρ.Good →
  ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y →
  ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) →
    ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      specXi ρ Y i j b k Q M χ h P = specSer ρ Y i j b k Q M χ h P := by
  intro D N X ρ hρ Y hY i j b k Q M χ hχ h P
  classical
  funext g
  have hB := hρ.base i j b
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) :=
    GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint D N X ρ hρ i j b _ (fun _ h => isSplit_of_mem_admissibleConjugatePairPlaces h)
      (hχ.2.1.mono_left (admissibleConjugatePairPlaces_subset i Q M))
  have htheta : ∀ a ∈ (Finset.univ : Finset (↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M))),
      IsThetaFunO (ρ.B i j b).F.ψ (Vc D j) (Wc D j) ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))
        (Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j)) a) := fun a _ => by
    have := Base.isThetaFunO_fock_vecAt hB hadm (fun PP y =>
      ((Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j) PP.1 (a PP) y : ℚ) : ℂ)) 1
    rwa [Frame.fock, GlobalTheory.FiniteFock.pureTensorO_one] at this
  unfold specSer
  rw [twistBy_apply, vecAt_specLoc, series_sum hB _ _ _ _ htheta, detChar_tw hρ hY i j b k Q M χ hχ g]
  unfold specXi
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Setup.xi, Base.xiCoef_apply]
  rw [← Equiv.sum_comp (Equiv.addRight (Multiplicative.toAdd (detChar (Wc D j)
    ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) g))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Equiv.coe_addRight, add_sub_cancel_right, coef_add]
  ring

end GlobalTheory.SpecFac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeriesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialised_universal_series_eq_twisted_thetaSeries : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X), ρ.Good →
  ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y →
  ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) →
    ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      specXi ρ Y i j b k Q M χ h P = specSer ρ Y i j b k Q M χ h P := by
  first | exact @GlobalTheory.SpecFac.specXi_eq_specSer | exact GlobalTheory.SpecFac.specXi_eq_specSer | (intros; apply GlobalTheory.SpecFac.specXi_eq_specSer <;> assumption)
end
end
