module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivOfSemilinear
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaReductionBaseLatticeBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultisetBaseLatticeEqJumpsMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneReductionFrobeniusPullbackEqShift

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsQuotOfAdmissible
noncomputable section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open scoped LaurentSeries PowerSeries Pointwise

namespace GlobalTheory.BasePairs

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} {emb : ZMod n → (K₀ →ₐ[Qp] LL)}
    {Γ : GalData G Qp LL O} {k : Type} [Field k] [Algebra O k]

theorem latRep_twLat (T : LocLat G Qp LL O) (θ : G →* Oˣ) (hθ : Continuous fun g => algebraMap O LL (θ g)) (g : G)
    (x : ↥T.L.T) : latRep (twLat T θ hθ).L g x = twistRep (latRep T.L) θ g x :=
  LinearMap.congr_fun (DFunLike.congr_fun (latRep_twLattice T.L θ) g) x

theorem exists_tw_sum [IsTopologicalRing LL] {lam : O} (T T' : LocLat G Qp LL O) (θ : G →* Oˣ)
    (hθ : Continuous fun g => algebraMap O LL (θ g)) (A A' : Ob k G)
    (q : ↥(twLat T θ hθ).L.T →ₗ[O] (Fin A.m → k)) (q' : ↥(twLat T' θ hθ).L.T →ₗ[O] (Fin A'.m → k))
    (h : Onto (twLat T θ hθ) A q) (hk : KerIs lam q) (h' : Onto (twLat T' θ hθ) A' q') (hk' : KerIs lam q') :
    ∃ (C : Ob k G) (r : ↥(twLat (AdmClosure.prodLoc T T') θ hθ).L.T →ₗ[O] (Fin C.m → k))
      (f : LatHom (twLat T θ hθ).L (twLat (AdmClosure.prodLoc T T') θ hθ).L)
      (g : LatHom (twLat T' θ hθ).L (twLat (AdmClosure.prodLoc T T') θ hθ).L)
      (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k)) (b : (Fin A'.m → k) →ₗ[k] (Fin C.m → k)),
      Onto (twLat (AdmClosure.prodLoc T T') θ hθ) C r ∧ KerIs lam r ∧ Function.Bijective (a.coprod b) ∧
      Function.Bijective (f.f.coprod g.f) ∧
      (∀ z ∈ (twLat (AdmClosure.prodLoc T T') θ hθ).L.T, ∃ x ∈ (twLat T θ hθ).L.T, ∃ y ∈ (twLat T' θ hθ).L.T,
        z = f.f x + g.f y) ∧ IsHom A C a ∧ IsHom A' C b ∧
      (∀ (x : ↥(twLat T θ hθ).L.T) (x' : ↥(twLat (AdmClosure.prodLoc T T') θ hθ).L.T),
        (x' : (twLat (AdmClosure.prodLoc T T') θ hθ).V) = f.f x → r x' = a (q x)) ∧
      (∀ (x : ↥(twLat T' θ hθ).L.T) (x' : ↥(twLat (AdmClosure.prodLoc T T') θ hθ).L.T),
        (x' : (twLat (AdmClosure.prodLoc T T') θ hθ).V) = g.f x → r x' = b (q' x)) := by
  let Z := twLat (AdmClosure.prodLoc T T') θ hθ
  let u : ↥Z.L.T ≃ₗ[O] (↥(twLat T θ hθ).L.T × ↥(twLat T' θ hθ).L.T) := StdAdm.prodSubEquiv T.L.T T'.L.T
  obtain ⟨C, r, a, b, hr1, hr2, ha, hb, hab, hz⟩ :=
    exists_sum_reduction (twLat T θ hθ) (twLat T' θ hθ) Z u (fun _ _ => rfl) A A' q q' h hk h' hk'
  let f : LatHom (twLat T θ hθ).L Z.L :=
    { f := LinearMap.inl LL T.V T'.V
      equiv := fun g x => Prod.ext rfl (map_zero ((twLat T' θ hθ).ρ g)).symm
      cont := continuous_id.prodMk continuous_const
      T_le := fun x hx => ⟨hx, Submodule.zero_mem _⟩ }
  let g : LatHom (twLat T' θ hθ).L Z.L :=
    { f := LinearMap.inr LL T.V T'.V
      equiv := fun g x => Prod.ext (map_zero ((twLat T θ hθ).ρ g)).symm rfl
      cont := continuous_const.prodMk continuous_id
      T_le := fun x hx => ⟨Submodule.zero_mem _, hx⟩ }
  refine ⟨C, r, f, g, a, b, hr1, hr2, hab, ?_,
    fun z hz => ⟨z.1, hz.1, z.2, hz.2, Prod.ext (add_zero _).symm (zero_add _).symm⟩, ha, hb,
    fun x x' hx => ?_, fun x x' hx => ?_⟩
  · change Function.Bijective ((LinearMap.inl LL T.V T'.V).coprod (LinearMap.inr LL T.V T'.V))
    rw [LinearMap.coprod_inl_inr]
    exact Function.bijective_id
  · have h1 : (u x').1 = x := Subtype.ext (congrArg Prod.fst hx)
    have h2 : (u x').2 = 0 := Subtype.ext (congrArg Prod.snd hx)
    rw [hz, h1, h2, map_zero, map_zero, add_zero]
  · have h1 : (u x').1 = 0 := Subtype.ext (congrArg Prod.fst hx)
    have h2 : (u x').2 = x := Subtype.ext (congrArg Prod.snd hx)
    rw [hz, h1, h2, map_zero, map_zero, zero_add]

theorem sameSS_base [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] (hlam : Irreducible Γ.lam)
    (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x)
    (hθ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) {A₀ A : Ob k G}
    {q₀ : ↥(twLat Γ.T₀ Γ.χ₁⁻¹ hθ).L.T →ₗ[O] (Fin A₀.m → k)} (h₀ : Onto (twLat Γ.T₀ Γ.χ₁⁻¹ hθ) A₀ q₀)
    (hK₀ : KerIs Γ.lam q₀) (ω : G →* kˣ) (hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g))
    {t μ : ℕ} {U : ZMod n → Multiset ℤ} {T : LocLat G Qp LL O} (hT : SumFull PD emb Γ t U μ T)
    {q : ↥(twLat T Γ.χ₁⁻¹ hθ).L.T →ₗ[O] (Fin A.m → k)} (h : Onto (twLat T Γ.χ₁⁻¹ hθ) A q) (hK : KerIs Γ.lam q) :
    SameSS A.ρ (piRep fun _ : Fin μ => refSum A₀ ω t) := by
  obtain ⟨e₀, he₀⟩ := exists_ref_equiv Γ hs hk A₀ q₀ h₀.1 hK₀
    (fun g x => (congrArg q₀ (latRep_twLat Γ.T₀ _ hθ g x).symm).trans (h₀.2 g x)) ω hω t
  obtain ⟨e, he⟩ := exists_quot_equiv (M := ↥T.L.T) q h.1 hK
  refine sameSS_twist_residue (π := modRep (latRep T.L) Γ.lam) (π' := piRep fun _ : Fin μ => Γ.refRep t)
    hs Γ.χ₁⁻¹ e (fun g x => ?_) (LinearEquiv.piCongrRight fun _ => e₀)
    (fun g x => funext fun j => he₀ g (x j)) (sumFull_sameSS hlam hT)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact (he (twistRep (latRep T.L) Γ.χ₁⁻¹ g x)).trans
    (((congrArg q (latRep_twLat T _ hθ g x).symm).trans (h.2 g x)).trans (congrArg (A.ρ g) (he x).symm))

theorem exists_quot_of_admissible (hs : Function.Surjective (algebraMap O k)) (h0 : algebraMap O k Γ.lam = 0)
    (hθ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) {t : ℕ} {U : ZMod n → Multiset ℤ}
    (A : Ob k G) (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N)
    (e : N ≃ₗ[O] (Fin A.m → k)) (hπ : Admissible PD emb Γ t U π)
    (he : ∀ σ x, e (twistRep π Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) :
    ∃ (μ : ℕ) (T : LocLat G Qp LL O), SumFull PD emb Γ t U μ T ∧
      ∀ (C : Ob k G) (q : ↥(twLat T Γ.χ₁⁻¹ hθ).L.T →ₗ[O] (Fin C.m → k)), Onto (twLat T Γ.χ₁⁻¹ hθ) C q →
        KerIs Γ.lam q → ∃ a, IsHom C A a ∧ Function.Surjective a := by
  obtain ⟨-, μ, T, hT, L₂, s, -, hs', hg, -⟩ := hπ
  refine ⟨μ, T, hT, fun C q hq hK => ?_⟩
  obtain ⟨a, ha⟩ := exists_descend (M := ↥T.L.T) hs h0 q hq.1 hK (e.toLinearMap ∘ₗ s)
  refine ⟨a, fun g y => ?_, fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := hq.1 y
    have h1 : C.ρ g (q x) = q (twistRep (latRep T.L) Γ.χ₁⁻¹ g x) :=
      (hq.2 g x).symm.trans (congrArg q (latRep_twLat T _ hθ g x))
    have h2 : s (twistRep (latRep T.L) Γ.χ₁⁻¹ g x) = twistRep π Γ.χ₁⁻¹ g (s x) :=
      (map_smul s _ _).trans (congrArg (((Γ.χ₁⁻¹ g : Oˣ) : O) • ·) (hg g x))
    exact (congrArg a h1).trans ((ha _).trans ((congrArg e h2).trans ((he g _).trans
      (congrArg (A.ρ g) (ha x).symm))))
  · obtain ⟨x, hx⟩ := (e.surjective.comp hs') y
    exact ⟨q x, (ha x).trans hx⟩

theorem exists_chi_reduction [IsTopologicalRing LL] (hinj : Function.Injective (algebraMap O LL))
    (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x)
    (hθ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (c : ℕ)
    (hc : Continuous fun g => algebraMap O LL (Γ.chi (c + 1) g))
    (ω : G →* kˣ) (hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) :
    ∃ q, Onto (twLat (charLat Qp hinj (Γ.chi (c + 1)) hc) Γ.χ₁⁻¹ hθ) (chr (ω ^ (-(c : ℤ)))) q ∧ KerIs Γ.lam q := by
  obtain ⟨u, -, hu⟩ := charLattice_equiv hinj (Γ.chi (c + 1))
  have hω' : ω = (Units.map (algebraMap O k : O →* k)).comp Γ.ε := MonoidHom.ext fun g => Units.ext (hω g)
  refine exists_char_reduction hs hk (twLat (charLat Qp hinj (Γ.chi (c + 1)) hc) Γ.χ₁⁻¹ hθ) u
    (Γ.χ₁⁻¹ * Γ.chi (c + 1)) (fun g a => ?_) _ fun g => ?_
  · refine (latRep_twLat (charLat Qp hinj (Γ.chi (c + 1)) hc) _ hθ g (u a)).trans ?_
    refine (congrArg (((Γ.χ₁⁻¹ g : Oˣ) : O) • ·) (hu g a).symm).trans ?_
    change ((Γ.χ₁⁻¹ g : Oˣ) : O) • u (((Γ.chi (c + 1) g : Oˣ) : O) • a) =
      (((Γ.χ₁⁻¹ g * Γ.chi (c + 1) g : Oˣ) : O)) • u a
    rw [map_smul, smul_smul, Units.val_mul]
  · rw [hω']
    simp [GalData.chi]

theorem exists_eps_reduction [IsTopologicalRing LL] (hinj : Function.Injective (algebraMap O LL))
    (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x)
    (hc : Continuous fun g => algebraMap O LL (Γ.ε g))
    (ω : G →* kˣ) (hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) :
    ∃ q, Onto (charLat Qp hinj Γ.ε hc) (chr (ω ^ (-(-1 : ℤ)))) q ∧ KerIs Γ.lam q := by
  obtain ⟨u, -, hu⟩ := charLattice_equiv hinj Γ.ε
  refine exists_char_reduction hs hk (charLat Qp hinj Γ.ε hc) u Γ.ε (fun g a => ?_) _ fun g => ?_
  · exact (hu g a).symm.trans (map_smul u _ _)
  · rw [neg_neg, zpow_one, hω]

end Gen

section Sit

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} {emb : ZMod n → (K₀ →ₐ[Qp] LL)}
    {Γ : GalData G Qp LL O} {k : Type} [Field k] [Algebra O k] {l : ℕ} {R : RingPG k l} {F : DFun R n G}
    {r₀ : ℕ} {D : TopData n r₀}
    {RN : ∀ (T : LocLat G Qp LL O) (A : Ob k G), (↥T.L.T →ₗ[O] (Fin A.m → k)) → Lats k n A.m → Prop}


variable (Γ RN) in
def Red (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (N : Lats k n A.m) : Prop :=
  Onto T A q ∧ KerIs Γ.lam q ∧ RN T A q N

abbrev tw (hθ : IsCrysChar PD emb Γ.χ₁⁻¹ fun i => -D.w i) (T : LocLat G Qp LL O) : LocLat G Qp LL O :=
  twLat T Γ.χ₁⁻¹ hθ.1

theorem crys_tw (htw : StdAdm.TwistRule PD emb O) (hθ : IsCrysChar PD emb Γ.χ₁⁻¹ fun i => -D.w i)
    {T : LocLat G Qp LL O} {U : ZMod n → Multiset ℤ} (h : CrysWith PD emb T.ρ U) :
    CrysWith PD emb (tw hθ T).ρ (fun i => (U i).map (· + -D.w i)) :=
  (htw T U _ _ h hθ).1


variable (RN) in
def Base (hθ : IsCrysChar PD emb Γ.χ₁⁻¹ fun i => -D.w i) (A : Ob k G) (N : Lats k n A.m) : Prop :=
  ∃ (μ : ℕ) (T : LocLat G Qp LL O) (q : ↥(tw hθ T).L.T →ₗ[O] (Fin A.m → k)),
    SumFull PD emb Γ D.t D.Ut μ T ∧ Red Γ RN (tw hθ T) A q N

variable [IsTopologicalRing LL] [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]
  (hθ : IsCrysChar PD emb Γ.χ₁⁻¹ fun i => -D.w i)
  (hk : Function.Surjective (algebraMap O k) ∧ ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x) (hlam : Irreducible Γ.lam)
  (hsum : StdAdm.SumRule PD emb O) (htw : StdAdm.TwistRule PD emb O)
  (hobj : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q, Onto T A q → F.Obj A)
  (hex : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q (U : ZMod n → Multiset ℤ), Onto T A q → KerIs Γ.lam q → CrysWith PD emb T.ρ U →
    ∃ N : Lats k n A.m, RN T A q N ∧ ∀ i, IsLat (N i))
  (habc : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q (U : ZMod n → Multiset ℤ), Onto T A q → KerIs Γ.lam q → CrysWith PD emb T.ρ U →
    ∀ N : Lats k n A.m, RN T A q N → ∀ w w' : ZMod n → ℕ, (∀ i, ∀ u ∈ U i, -(w i : ℤ) ≤ u ∧ u ≤ w' i) →
    ABC (F.D A) (fun i => w i) (fun i => w' i) N)
  (hsen : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q (U : ZMod n → Multiset ℤ), Onto T A q → KerIs Γ.lam q → CrysWith PD emb T.ρ U →
    ∀ N : Lats k n A.m, RN T A q N → ∀ i x, sen ((F.D A).γ i) (N i) x = resCount (U i) 0 x)
  (hpoly : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q (U : ZMod n → Multiset ℤ), Onto T A q → KerIs Γ.lam q → CrysWith PD emb T.ρ U →
    ∀ N : Lats k n A.m, RN T A q N → ∀ (i : ZMod n) (s : ℕ),
    (∀ u ∈ U i, ∀ a : ℕ, a < s → (l : ℤ) ∣ (a : ℤ) - u → (a : ℤ) = u) → EPoly ((F.D A).γ i) (N i) s)
  (hrk : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q (U : ZMod n → Multiset ℤ), Onto T A q → KerIs Γ.lam q → CrysWith PD emb T.ρ U →
    ∀ N : Lats k n A.m, RN T A q N → ∀ a : ZMod n → ℤ, A.m = 1 → (∀ i, U i = {a i}) →
    ∀ i, pull ((F.D A).φ i) (N (i - 1)) = sh (a i) (N i))
  (hadd : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q (U : ZMod n → Multiset ℤ), Onto T A q → KerIs Γ.lam q → CrysWith PD emb T.ρ U →
    ∀ (T' : LocLat G Qp LL O) (A' : Ob k G) q' (U' : ZMod n → Multiset ℤ),
    Onto T' A' q' → KerIs Γ.lam q' → CrysWith PD emb T'.ρ U' →
    ∀ (Z : LocLat G Qp LL O) (C : Ob k G) r (V : ZMod n → Multiset ℤ),
    Onto Z C r → KerIs Γ.lam r → CrysWith PD emb Z.ρ V →
    ∀ (f : LatHom T.L Z.L) (g : LatHom T'.L Z.L) (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k))
    (b : (Fin A'.m → k) →ₗ[k] (Fin C.m → k)), Function.Bijective (f.f.coprod g.f) →
    (∀ z ∈ Z.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) → IsHom A C a → IsHom A' C b →
    (∀ (x : ↥T.L.T) (x' : ↥Z.L.T), (x' : Z.V) = f.f x → r x' = a (q x)) →
    (∀ (x : ↥T'.L.T) (x' : ↥Z.L.T), (x' : Z.V) = g.f x → r x' = b (q' x)) →
    ∀ (N : Lats k n A.m) (N' : Lats k n A'.m) (L : Lats k n C.m), RN T A q N → RN T' A' q' N' → RN Z C r L →
    ∀ i, L i = F.push A C a N i ⊔ F.push A' C b N' i)

set_option linter.unusedSectionVars false

include hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd

theorem exists_red {T : LocLat G Qp LL O} {U : ZMod n → Multiset ℤ} (h : CrysWith PD emb T.ρ U) :
    ∃ (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (N : Lats k n A.m),
      A.m = Module.finrank LL T.V ∧ Red Γ RN T A q N := by
  have := StdAdm.finite_lat T
  have := T.L.free
  obtain ⟨A, q, hm, hq, hK, hg⟩ := exists_reduction hk.1 hk.2 (latRep T.L)
  obtain ⟨N, hN, -⟩ := hex T A q U ⟨hq, hg⟩ hK h
  refine ⟨A, q, N, hm.trans ?_, ⟨hq, hg⟩, hK, hN⟩
  have : Submodule.IsFullLattice LL T.L.T :=
    { toIsLattice := Submodule.IsLattice.of_fg LL T.L.fg, span_eq_top := T.L.span }
  rw [Module.finrank, Module.finrank, Submodule.IsLattice.rank' LL]

theorem exists_red_sum {T T' : LocLat G Qp LL O} {U U' : ZMod n → Multiset ℤ} (h : CrysWith PD emb T.ρ U)
    (h' : CrysWith PD emb T'.ρ U') {A A' : Ob k G} {q q' N N'} (hr : Red Γ RN (tw hθ T) A q N)
    (hr' : Red Γ RN (tw hθ T') A' q' N') :
    ∃ C r a b, IsHom A C a ∧ IsHom A' C b ∧ Function.Bijective (a.coprod b) ∧
      Red Γ RN (tw hθ (AdmClosure.prodLoc T T')) C r (fun i => F.push A C a N i ⊔ F.push A' C b N' i) := by
  obtain ⟨C, r, f, g, a, b, hr1, hr2, hab, h1, h2, ha, hb, h3, h4⟩ :=
    exists_tw_sum T T' _ hθ.1 A A' q q' hr.1 hr.2.1 hr'.1 hr'.2.1
  have hZ := crys_tw htw hθ (T := AdmClosure.prodLoc T T')
    (hsum T T' (AdmClosure.prodLoc T T') _ _ (LinearEquiv.refl _ _) (fun _ _ => rfl) h h')
  obtain ⟨L, hL, -⟩ := hex (tw hθ (AdmClosure.prodLoc T T')) C r _ hr1 hr2 hZ
  have key := hadd (tw hθ T) A q _ hr.1 hr.2.1
    (crys_tw htw hθ h) (tw hθ T') A' q' _ hr'.1 hr'.2.1 (crys_tw htw hθ h') (tw hθ (AdmClosure.prodLoc T T')) C r _ hr1 hr2
    hZ f g a b h1 h2 ha hb h3 h4 N N' L hr.2.2 hr'.2.2 hL
  obtain rfl : L = fun i => F.push A C a N i ⊔ F.push A' C b N' i := funext key
  exact ⟨C, r, a, b, ha, hb, hab, hr1, hr2, hL⟩

theorem base_abc {A : Ob k G} {N} (h : Base RN hθ A N) : ABC (F.D A) D.w D.wst N := by
  obtain ⟨μ, T, q, hT, hr⟩ := h
  have key := habc (tw hθ T) A q _ hr.1 hr.2.1
    (crys_tw htw hθ (sumFull_crys hsum hT)) N hr.2.2 (fun i => (D.w i).toNat) (fun i => (D.wst i).toNat)
    (fun i u hu => by
      obtain ⟨u', hu', rfl⟩ := Multiset.mem_map.1 hu
      have := D.mem_Ut i (Multiset.mem_of_mem_nsmul hu')
      have := w_range D i
      simp only [TopData.wst]
      omega)
  have e1 : (fun i => (((D.w i).toNat : ℕ) : ℤ)) = D.w := funext fun i => by
    have := w_range D i
    omega
  have e2 : (fun i => (((D.wst i).toNat : ℕ) : ℤ)) = D.wst := funext fun i => by
    have := w_range D i
    simp only [TopData.wst]
    omega
  rwa [e1, e2] at key

theorem base_sen {A₀ : Ob k G} {q₀ N₀} (h₀ : Red Γ RN (tw hθ Γ.T₀) A₀ q₀ N₀) (ω : G →* kˣ)
    (hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) {A : Ob k G} {N} (h : Base RN hθ A N) :
    ∃ μ : ℕ, SameSS A.ρ (piRep fun _ : Fin μ => refSum A₀ ω D.t) ∧
      ∀ i x, sen ((F.D A).γ i) (N i) x = μ * resCount (D.Ut i) (D.w i) x := by
  obtain ⟨μ, T, q, hT, hr⟩ := h
  refine ⟨μ, ?_, fun i x => ?_⟩
  · exact sameSS_base hlam hk.1 hk.2 hθ.1 h₀.1 h₀.2.1 ω hω hT hr.1 hr.2.1
  · rw [hsen (tw hθ T) A q _ hr.1 hr.2.1
      (crys_tw htw hθ (sumFull_crys hsum hT)) N hr.2.2 i x, resCount_nsmul_map]

theorem base_sum {A A' : Ob k G} {N N'} (h : Base RN hθ A N) (h' : Base RN hθ A' N') :
    ∃ C i j, IsHom A C i ∧ IsHom A' C j ∧ Function.Bijective (i.coprod j) ∧
      Base RN hθ C (fun a => F.push A C i N a ⊔ F.push A' C j N' a) := by
  obtain ⟨μ, T, q, hT, hr⟩ := h
  obtain ⟨μ', T', q', hT', hr'⟩ := h'
  obtain ⟨C, r, a, b, ha, hb, hab, hr⟩ :=
    exists_red_sum hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd (sumFull_crys hsum hT) (sumFull_crys hsum hT') hr hr'
  exact ⟨C, a, b, ha, hb, hab, μ + μ', _, r, AdmClosure.sumFull_prod hT hT', hr⟩

theorem base_e (hT1 : D.T1 l) (hT3 : D.T3 l) {A : Ob k G} {N} (h : Base RN hθ A N) (i : ZMod n) (hi : D.ty i = LType.Bd) :
    EPoly ((F.D A).γ i) (N i) (D.wst i + 1) := by
  obtain ⟨μ, T, q, hT, hr⟩ := h
  have hw := w_range D i
  have key := hpoly (tw hθ T) A q _ hr.1 hr.2.1
    (crys_tw htw hθ (sumFull_crys hsum hT)) N hr.2.2 i (D.wst i + 1).toNat
    (fun u hu a ha hd => by
      obtain ⟨u', hu', rfl⟩ := Multiset.mem_map.1 hu
      exact eq_of_dvd D hT1 hT3 i hi u' (Multiset.mem_of_mem_nsmul hu') a (by omega) hd)
  have e : (((D.wst i + 1).toNat : ℕ) : ℤ) = D.wst i + 1 := by
    simp only [TopData.wst]
    omega
  rwa [e] at key

theorem char_props {T : LocLat G Qp LL O} {e : ℤ} (h : CrysWith PD emb T.ρ fun _ => {e}) {ψ : G →* kˣ} {q N}
    (hr : Red Γ RN T (chr ψ) q N) (i : ZMod n) : IsLat (N i) ∧ CondC ((F.D (chr ψ)).γ i) (N i) ∧
      pull ((F.D (chr ψ)).φ i) (N (i - 1)) = sh e (N i) ∧
      ∀ x, sen ((F.D (chr ψ)).γ i) (N i) x = resCount {e} 0 x := by
  have key := habc T _ q _ hr.1 hr.2.1 h N hr.2.2
    (fun _ => (-e).toNat) (fun _ => e.toNat) (fun i u hu => by
      rw [Multiset.mem_singleton.1 hu]
      omega)
  exact ⟨key.1 i, key.2.2 i,
    hrk T _ q _ hr.1 hr.2.1 h N hr.2.2 (fun _ => e) rfl (fun _ => rfl) i,
    hsen T _ q _ hr.1 hr.2.1 h N hr.2.2 i⟩

theorem exists_model (A : Ob k G) (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N)
    (e : N ≃ₗ[O] (Fin A.m → k)) (hπ : Admissible PD emb Γ D.t D.Ut π) (he : ∀ σ x, e (twistRep π Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) :
    ∃ L, IsModel F (Base RN hθ) A L := by
  obtain ⟨μ, T, hT, h⟩ := exists_quot_of_admissible hk.1 ((hk.2 _).2 dvd_rfl) hθ.1 A N π e hπ he
  obtain ⟨C, q, Nb, -, hr⟩ := exists_red hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd (crys_tw htw hθ (sumFull_crys hsum hT))
  obtain ⟨a, ha, hs⟩ := h C q hr.1 hr.2.1
  exact ⟨_, C, Nb, C, LinearMap.id, a, ⟨μ, T, q, hT, hr⟩, fun _ _ => rfl, Function.injective_id, ha, hs, rfl⟩

theorem exists_std (hD : IsTopGal PD emb D Γ) (hε : IsCrysChar PD emb Γ.ε fun _ => -1)
    {A₀ : Ob k G} {q₀ N₀} (h₀ : Red Γ RN (tw hθ Γ.T₀) A₀ q₀ N₀) (ω : G →* kˣ)
    (hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) :
    IsModel F (Base RN hθ) A₀ N₀ ∧ ∀ e : ℤ, ∃ N : Lats k n 1,
      (-1 ≤ e → F.Obj (chr (ω ^ (-e))) ∧ ∀ i, IsLat (N i) ∧ CondC ((F.D (chr (ω ^ (-e)))).γ i) (N i) ∧
        pull ((F.D (chr (ω ^ (-e)))).φ i) (N (i - 1)) = sh e (N i) ∧
        ∀ x, sen ((F.D (chr (ω ^ (-e)))).γ i) (N i) x = resCount {e} 0 x) ∧
      (0 ≤ e → e < D.t → IsModel F (Base RN hθ) (chr (ω ^ (-e))) N) := by
  have hinj := IsFractionRing.injective O LL
  have hχ := StdAdm.isCrysChar_chi hinj htw hD.2.2.1 hε
  let X : ℕ → LocLat G Qp LL O := fun c => charLat Qp hinj _ (hχ c).1
  have hX₀ : ∀ c : ℕ, CrysWith PD emb (X c).ρ fun i => {D.w i + c} := fun c => (hχ c).2
  have hX : ∀ c : ℕ, CrysWith PD emb (tw hθ (X c)).ρ fun _ => {(c : ℤ)} := fun c => by
    have h := crys_tw htw hθ (T := X c) (hX₀ c)
    simpa using h
  have hXr : ∀ c : ℕ, ∃ q N, Red Γ RN (tw hθ (X c)) (chr (ω ^ (-(c : ℤ)))) q N := fun c => by
    obtain ⟨q, hq, hK⟩ := exists_chi_reduction (Qp := Qp) hinj hk.1 hk.2 hθ.1 c (hχ c).1 ω hω
    obtain ⟨N, hN, -⟩ := hex (tw hθ (X c)) (chr (ω ^ (-(c : ℤ)))) q _ hq hK (hX c)
    exact ⟨q, N, hq, hK, hN⟩
  choose q N hr using hXr
  obtain ⟨T, e, hT, ⟨C, r, L, hL, t0, t1⟩, he⟩ := exists_sum_ind hinj hsum hD.2.1 hχ
    (fun j T => ∃ C r L, Red Γ RN (tw hθ T) C r L ∧ IsTrace F A₀ N₀ C L ∧
      ∀ c : ℕ, c < j → IsTrace F (chr (ω ^ (-(c : ℤ)))) (N c) C L)
    ⟨A₀, q₀, N₀, h₀, IsTrace.refl F A₀ (hobj _ _ _ h₀.1) N₀, fun c hc => absurd hc (Nat.not_lt_zero c)⟩
    (fun j T hT ⟨C, r, L, hL, t0, t1⟩ => by
      obtain ⟨C', r', a, b, ha, hb, hab, hL'⟩ :=
        exists_red_sum hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd (T := T) (T' := X j) hT (hX₀ j) hL (hr j)
      have hC' := hobj _ _ _ hL'.1
      obtain ⟨s0, s1⟩ := isTrace_sum F _ _ C' a b hC' ha hb hab L (N j)
      refine ⟨C', r', _, hL', t0.trans hC' s0, fun c hc => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · exact (t1 c hc).trans hC' s0
      · exact s1) D.t
  have hB : Base RN hθ C L := ⟨1, T, r, (StdAdm.full_of_equiv hlam T e hT he).sumFull, hL⟩
  have hC' := hobj _ _ _ hL.1
  refine ⟨t0.isModel hC' hB, fun e => ?_⟩
  rcases le_or_gt 0 e with he | he
  · obtain ⟨c, rfl⟩ := Int.eq_ofNat_of_zero_le he
    exact ⟨N c, fun _ => ⟨hobj _ _ _ (hr c).1, char_props hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd (hX c) (hr c)⟩,
      fun _ hc => (t1 c (by exact_mod_cast hc)).isModel hC' hB⟩
  · obtain ⟨q', hq, hK⟩ := exists_eps_reduction (Qp := Qp) hinj hk.1 hk.2 hε.1 ω hω
    let Y : LocLat G Qp LL O := charLat Qp hinj _ hε.1
    have hY : CrysWith PD emb Y.ρ fun _ => {-1} := hε.2
    obtain ⟨N', hN, -⟩ := hex Y (chr (ω ^ (-(-1 : ℤ)))) q' _ hq hK hY
    refine ⟨N', fun h => ?_, fun h => absurd h (not_le.2 he)⟩
    obtain rfl : e = -1 := by omega
    exact ⟨hobj Y _ _ hq, char_props hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd (T := Y) hY ⟨hq, hK, hN⟩⟩

theorem exists_modTh [Fact l.Prime] [CharP k l] [NeZero n] (hD : IsTopGal PD emb D Γ)
    (hε : IsCrysChar PD emb Γ.ε fun _ => -1)
    (hne : ∀ ω : G →* kˣ, (∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) → ∀ e : ℕ, 0 < e → e + 1 < l → ω ^ e ≠ 1) :
    ∃ M : ModTh F D, (∀ σ, (M.ω σ : k) = algebraMap O k (Γ.ε σ)) ∧
    (∃ q : ↥(tw hθ Γ.T₀).L.T →ₗ[O] (Fin M.T.m → k), Onto (tw hθ Γ.T₀ : LocLat G Qp LL O) M.T q ∧ KerIs Γ.lam q) ∧
    M.Base = Base RN hθ := by
  obtain ⟨A₀, q₀, N₀, hm, h₀⟩ := exists_red hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd (crys_tw htw hθ hD.2.1)
  let ω : G →* kˣ := (Units.map (algebraMap O k : O →* k)).comp Γ.ε
  have hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g) := fun _ => rfl
  obtain ⟨hs, hN⟩ := exists_std hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd hD hε h₀ ω hω
  choose N hN hM using hN
  refine ⟨{ T := A₀
            T_m := hm.trans hD.1
            ω := ω
            ω_ne := hne ω hω
            Base := Base RN hθ
            base_obj := fun A N ⟨_, _, _, _, h⟩ => hobj _ _ _ h.1
            base_abc := fun A N h => base_abc hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd h
            base_sen := fun A N h => base_sen hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd h₀ ω hω h
            base_sum := fun A N A' N' h h' => base_sum hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd h h'
            base_e := fun h1 h3 A N h => base_e hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd h1 h3 h
            Nstd := N₀
            std_model := hs
            std_sen := fun i x => ?_
            Nχ := N
            χ_obj := fun e h _ => (hN e h).1
            χ_lat := fun e h _ => (hN e h).2
            χ_model := hM
            χ_zero := eq_span_unit F (ω ^ (-(0 : ℤ))) (by simp) (N 0) (fun i => ((hN 0 (by simp)).2 i).1)
              fun i => ((hN 0 (by simp)).2 i).2.2.1 }, hω, ⟨q₀, h₀.1, h₀.2.1⟩, rfl⟩
  have h := resCount_nsmul_map 1 (D.U i) (D.w i) x
  rw [one_nsmul, one_mul] at h
  rw [hsen (tw hθ Γ.T₀) A₀ q₀ _ h₀.1 h₀.2.1
    (crys_tw htw hθ hD.2.1) N₀ h₀.2.2 i x, h]

theorem exists_real [Fact l.Prime] [CharP k l] [NeZero n] (hD : IsTopGal PD emb D Γ)
    (hε : IsCrysChar PD emb Γ.ε fun _ => -1)
    (hne : ∀ ω : G →* kˣ, (∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) → ∀ e : ℕ, 0 < e → e + 1 < l → ω ^ e ≠ 1) :
    ∃ M : ModTh F D, (∀ σ, (M.ω σ : k) = algebraMap O k (Γ.ε σ)) ∧
      (∃ q : ↥Γ.T₀.L.T →ₗ[O] (Fin M.T.m → k), Function.Surjective q ∧
        KerIs Γ.lam q ∧ ∀ σ x, q (twistRep Γ.W₀ Γ.χ₁⁻¹ σ x) = M.T.ρ σ (q x)) ∧
      ∀ (A : Ob k G) (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N)
        (e : N ≃ₗ[O] (Fin A.m → k)), Admissible PD emb Γ D.t D.Ut π →
        (∀ σ x, e (twistRep π Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) → ∃ L, M.Model A L := by
  obtain ⟨M, h1, ⟨q, hq, hK⟩, h3⟩ := exists_modTh hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd hD hε hne
  refine ⟨M, h1, ⟨q, hq.1, hK, fun g x => (congrArg q (latRep_twLat Γ.T₀ _ hθ.1 g x).symm).trans (hq.2 g x)⟩,
    fun A N _ _ π e hπ he => ?_⟩
  have h := exists_model hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd A N π e hπ he
  rwa [← h3] at h

end Sit

end GlobalTheory.BasePairs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EPolyBase
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalApplyComm
namespace GlobalTheory.AevalCommute

theorem pow_apply_comm {O : Type} [CommRing O] {k : Type} [Field k] [Algebra O k]
    {M V : Type} [AddCommGroup M] [Module O M] [AddCommGroup V] [Module k V]
    (J : M →+ V) (ν : Module.End O M) (μ : Module.End k V)
    (hνμ : ∀ y : M, J (ν y) = μ (J y)) (n : ℕ) (y : M) :
    J ((ν ^ n) y) = (μ ^ n) (J y) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hνμ]

theorem aeval_apply_comm {O : Type} [CommRing O] {k : Type} [Field k] [Algebra O k]
    {M V : Type} [AddCommGroup M] [Module O M] [AddCommGroup V] [Module k V]
    (J : M →+ V) (hJ : ∀ (c : O) (y : M), J (c • y) = algebraMap O k c • J y)
    (ν : Module.End O M) (μ : Module.End k V)
    (hνμ : ∀ y : M, J (ν y) = μ (J y)) (f : Polynomial O) (y : M) :
    J (Polynomial.aeval ν f y) = Polynomial.aeval μ (f.map (algebraMap O k)) (J y) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add (f := _), Polynomial.map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
      Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, hJ, pow_apply_comm J ν μ hνμ]

theorem main : ∀ {O : Type} [inst : CommRing O] {k : Type} [inst_1 : Field k] [inst_2 : Algebra O k] {M V : Type} [inst_3 : AddCommGroup M] [inst_4 : Module O M] [inst_5 : AddCommGroup V] [inst_6 : Module k V] (J : M →+ V), (∀ (c : O) (y : M), (J : M → V) (c • y) = (Algebra.algebraMap O k : O → k) c • (J : M → V) y) → ∀ (ν : Module.End O M) (μ : Module.End k V), (∀ (y : M), (J : M → V) ((ν : M → M) y) = (μ : V → V) ((J : M → V) y)) → ∀ (f : Polynomial O) (y : M), (J : M → V) (((Polynomial.aeval ν : Polynomial O → Module.End O M) f : M → M) y) = ((Polynomial.aeval μ : Polynomial k → Module.End k V) (Polynomial.map (Algebra.algebraMap O k) f) : V → V) ((J : M → V) y) :=
  fun J hJ ν μ hνμ f y => aeval_apply_comm J hJ ν μ hνμ f y

end GlobalTheory.AevalCommute
end

noncomputable section
namespace GlobalTheory.BaseLatticeE
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

section Gen
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n₀ : ℕ}
    (W : LocWach PD LL O v n₀) {k : Type} [Field k] [Algebra O k]


omit [TopologicalSpace G] [Algebra Qp LL] [TopologicalSpace LL] in
theorem exists_c (hk : (PD.p : k) = 0) (u : Oˣ) (hu : (u : O) = 1 + (PD.p : O)) :
    ∃ c : ℤ → O, WachUse.IsC PD LL c ∧ ∀ a, algebraMap O k (c a) = -(a : k) := by
  have hU : algebraMap O LL (u : O) = 1 + (PD.p : LL) := by rw [hu]; simp
  have hne : (1 + (PD.p : LL)) ≠ 0 := by rw [← hU]; exact (u.isUnit.map _).ne_zero
  have hinv : algebraMap O LL ((u⁻¹ : Oˣ) : O) = (1 + (PD.p : LL))⁻¹ := by
    rw [← hU]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]; simp
  have hk1 : algebraMap O k (u : O) = 1 := by rw [hu]; simp [hk]
  have hk2 : algebraMap O k ((u⁻¹ : Oˣ) : O) = 1 := by
    have : algebraMap O k ((u⁻¹ : Oˣ) : O) * algebraMap O k (u : O) = 1 := by rw [← map_mul]; simp
    rwa [hk1, mul_one] at this
  have key : ∀ a : ℤ, ∃ x : O, (PD.p : LL) * algebraMap O LL x = 1 - (1 + (PD.p : LL)) ^ a ∧
      algebraMap O k x = -(a : k) := by
    intro a
    induction a using Int.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | succ m ih =>
      obtain ⟨x, hx, hx'⟩ := ih
      refine ⟨x * (u : O) - 1, ?_, ?_⟩
      · rw [zpow_add_one₀ hne, map_sub, map_mul, hU, map_one]
        linear_combination (1 + (PD.p : LL)) * hx
      · rw [map_sub, map_mul, hk1, hx', map_one]; push_cast; ring
    | pred m ih =>
      obtain ⟨x, hx, hx'⟩ := ih
      refine ⟨(x + 1) * ((u⁻¹ : Oˣ) : O), ?_, ?_⟩
      · rw [zpow_sub_one₀ hne, map_mul, hinv, map_add (f := _), map_one]
        have h1 : (1 + (PD.p : LL)) * (1 + (PD.p : LL))⁻¹ = 1 := mul_inv_cancel₀ hne
        linear_combination (1 + (PD.p : LL))⁻¹ * hx + h1
      · rw [map_mul, map_add (f := _), hk2, hx', map_one]; push_cast; ring
  choose c hc hc' using key
  exact ⟨c, hc, hc'⟩

theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n₀) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]; rfl

theorem sum_Del {M : Type} [AddCommMonoid M] (f : W.Gam → M) {δ : W.Gam} (hδ : δ ∈ W.DelF) :
    ∑ ε ∈ W.DelF, f (δ * ε) = ∑ ε ∈ W.DelF, f ε := by
  have hm : ∀ g, g ∈ W.DelF ↔ IsOfFinOrder g := fun g => by
    rw [W.DelF_def, isOfFinOrder_iff_pow_eq_one]
  refine Finset.sum_bij' (fun ε _ => δ * ε) (fun ε _ => δ⁻¹ * ε) ?_ ?_ ?_ ?_ ?_
  · intro a ha; exact (hm _).2 (((hm _).1 hδ).mul ((hm _).1 ha))
  · intro a ha; exact (hm _).2 (((hm _).1 hδ).inv.mul ((hm _).1 ha))
  · intro a _; simp
  · intro a _; simp
  · intro a _; rfl

theorem γA_q {δ : W.Gam} (hδ : δ ∈ W.DelF) :
    W.γA δ (W.π₀ + (PD.p : LetA O n₀)) = W.π₀ + (PD.p : LetA O n₀) := by
  rw [map_add (f := _), map_natCast]
  congr 1
  funext i
  change W.γ₀ δ W.π₀₁ = W.π₀₁
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LocWach.π₀₁, map_add (f := _), map_sub, map_one, map_natCast, map_sum,
    ← sum_Del W (fun ε => W.γ₀ ε (1 + PowerSeries.X)) hδ]
  simp only [map_mul, AlgHom.mul_apply]

theorem γA_e (g : W.Gam) (i : ZMod n₀) : W.γA g (letE i) = letE i := by
  funext j
  change W.γ₀ g ((letE i : LetA O n₀) j) = (letE i : LetA O n₀) j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

theorem card_Del {l : ℕ} (hl : 2 ≤ l) (hk : (PD.p : k) = 0) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩)
    (h1 : ∃ u : (k⟦X⟧)ˣ, ι (vv k) = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ (l - 1))
    (h2 : ι (vv k) = ((PowerSeries.map (algebraMap O k) W.π₀₁ : k⟦X⟧) : k⸨X⸩)) :
    (W.DelF.card : k) = -1 := by
  obtain ⟨u, hu⟩ := h1
  have h3 : (PowerSeries.map (algebraMap O k) W.π₀₁ : k⟦X⟧) = (u : k⟦X⟧) * (PowerSeries.X : k⟦X⟧) ^ (l - 1) := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    rw [map_mul, map_pow]
    rw [h2, vv_eq_coe_X] at hu
    exact hu
  have h4 := congrArg (PowerSeries.constantCoeff (R := k)) h3
  have h5 : PowerSeries.constantCoeff W.π₀₁ = 1 - (PD.p : O) + W.DelF.card := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LocWach.π₀₁, map_add (f := _), map_sub, map_one, map_natCast, map_sum]
    congr 1
    rw [Finset.sum_congr rfl (g := fun _ => (1 : O))]
    · simp
    · intro δ _
      rw [map_add (f := _), map_one, map_add (f := _), (W.γ₀_X δ).1]; simp
  have h6 : l - 1 ≠ 0 := by omega
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, h5] at h4
  simp [h6, hk] at h4
  linear_combination h4

theorem aeval_red {M V : Type} [AddCommGroup M] [Module O M] [AddCommGroup V] [Module k V] (J : M →+ V)
    (hs : ∀ (c : O) y, J (c • y) = algebraMap O k c • J y) (ν : Module.End O M) (μ : Module.End k V)
    (hν : ∀ y, J (ν y) = μ (J y)) (f : Polynomial O) (y : M) :
    J (Polynomial.aeval ν f y) = Polynomial.aeval μ (f.map (algebraMap O k)) (J y) := by
  first
  | exact @_root_.GlobalTheory.AevalCommute.main
  | exact _root_.GlobalTheory.AevalCommute.main
  | (apply _root_.GlobalTheory.AevalCommute.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AevalCommute.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AevalCommute.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AevalCommute.main ..)

variable {W} {l n : ℕ} {R : RingPG k l} {F : DFun R n G} {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {τ : ZMod n → ZMod n₀}
  {γ : W.Gam} (p : Pres W F ι τ γ) (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k))
  (i : ZMod n)

def red : ↥(W.NΔ T) →+ Vc k A.m where
  toFun y := p.j T A q i ⟨y, y.2.2⟩
  map_zero' := map_zero (p.j T A q i)
  map_add' a b := map_add (p.j T A q i) ⟨a, a.2.2⟩ ⟨b, b.2.2⟩

variable {T A q}

theorem red_smul (hq : Onto T A q) (c : O) (y : ↥(W.NΔ T)) :
    red p T A q i (c • y) = algebraMap O k c • red p T A q i y := by
  have := p.j_smul T A q hq i (algebraMap O (LetA O n₀) c) (algebraMap k k⟦X⟧ (algebraMap O k c))
    ⟨y, y.2.2⟩ ⟨(c • y : ↥(W.NΔ T)), (c • y).2.2⟩ ?_ (by rw [algebraMap_smul]; rfl)
  · rw [algebraMap_smul] at this; exact this
  · have h1 : PowerSeries.map (algebraMap O k) (algebraMap O (LetA O n₀) c (τ i)) =
        algebraMap k k⟦X⟧ (algebraMap O k c) := by
      simp [PowerSeries.algebraMap_apply]
    rw [h1]
    exact ι.commutes _

theorem X_smul_eq (m : ℕ) (x : Vc k A.m) : (PowerSeries.X ^ m : k⟦X⟧) • x = vv k ^ (m : ℤ) • x := by
  rw [← algebraMap_smul k⸨X⸩ (PowerSeries.X ^ m : k⟦X⟧) x, zpow_natCast, map_pow, vv_eq_coe_X]
  rfl

theorem red_ν (hq : Onto T A q) (ν : Module.End O ↥(W.NΔ T))
    (hν : ∀ y : ↥(W.NΔ T), W.γD T γ y - y = W.π₀ • ((ν y : ↥(W.NΔ T)) : W.DD T)) (y : ↥(W.NΔ T)) :
    red p T A q i (ν y) = nab ((F.D A).γ i) (red p T A q i y) := by
  have hg : W.γD T γ y ∈ DΔ W T := fun δ hδ => by
    rw [← W.γD_mul, mul_comm, W.γD_mul, y.2.2 δ hδ]
  have h1 := p.j_γ T A q hq i ⟨y, y.2.2⟩ ⟨_, hg⟩ rfl
  have h2 := p.j_smul T A q hq i W.π₀ PowerSeries.X ⟨(ν y : ↥(W.NΔ T)), (ν y).2.2⟩
    (⟨_, hg⟩ - ⟨y, y.2.2⟩) (by rw [← vv_eq_coe_X, p.ι_v]; rfl) (hν y)
  rw [map_sub, h1] at h2
  have h3 := X_smul_eq (A := A) 1 (red p T A q i (ν y))
  rw [pow_one, Nat.cast_one, zpow_one] at h3
  rw [nab_apply_eq]
  change _ = (vv k)⁻¹ • (((F.D A).γ i) (p.j T A q i ⟨y, y.2.2⟩) - p.j T A q i ⟨y, y.2.2⟩)
  rw [h2]
  change _ = (vv k)⁻¹ • ((PowerSeries.X : k⟦X⟧) • red p T A q i (ν y))
  rw [h3, smul_smul, inv_mul_cancel₀ (vv_ne_zero k), one_smul]

theorem red_div (hq : Onto T A q) (hk : (PD.p : k) = 0) (hc : (W.DelF.card : k) = -1) (s : ℕ)
    (y : ↥(W.NΔ T)) (z : W.DD T) (hz : z ∈ W.N T)
    (h : (letE (τ i) : LetA O n₀) • (y : W.DD T) = (W.π₀ + (PD.p : LetA O n₀)) ^ s • z) :
    ∃ z' : ↥(W.NΔ T), red p T A q i y = vv k ^ (s : ℤ) • red p T A q i z' := by
  have hz' : ∑ δ ∈ W.DelF, W.γD T δ z ∈ W.NΔ T := by
    refine ⟨Submodule.sum_mem _ fun δ _ => W.N_Γ T δ z hz, fun δ hδ => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← sum_Del W (fun ε => W.γD T ε z) hδ]
    simp only [W.γD_mul]
  have he : (letE (τ i) : LetA O n₀) • (y : W.DD T) ∈ DΔ W T := fun δ hδ => by
    rw [γD_smulA, γA_e, y.2.2 δ hδ]
  have h1 := p.j_smul T A q hq i (letE (τ i)) 1 ⟨y, y.2.2⟩ ⟨_, he⟩ (by simp [letE]) rfl
  have h2 : W.DelF.card • ((letE (τ i) : LetA O n₀) • (y : W.DD T)) =
      (W.π₀ + (PD.p : LetA O n₀)) ^ s • ∑ δ ∈ W.DelF, W.γD T δ z := by
    rw [Finset.smul_sum, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun δ hδ => ?_
    rw [← he δ hδ, h, γD_smulA, map_pow, γA_q W hδ]
  have h3 := p.j_smul T A q hq i ((W.π₀ + (PD.p : LetA O n₀)) ^ s) (PowerSeries.X ^ s) ⟨_, hz'.2⟩
    (W.DelF.card • ⟨_, he⟩) ?_ h2
  · rw [map_nsmul, h1, one_smul, ← Nat.cast_smul_eq_nsmul k, hc, neg_one_smul, X_smul_eq] at h3
    refine ⟨-⟨_, hz'⟩, ?_⟩
    rw [map_neg, smul_neg]
    exact (neg_eq_iff_eq_neg.1 h3)
  · have h4 : PowerSeries.map (algebraMap O k) (((W.π₀ + (PD.p : LetA O n₀)) ^ s) (τ i)) =
        PowerSeries.map (algebraMap O k) W.π₀₁ ^ s := by
      have h5 : ((PD.p : ℕ) : k⟦X⟧) = 0 := by
        rw [← map_natCast (algebraMap k k⟦X⟧), hk, map_zero]
      rw [Pi.pow_apply, Pi.add_apply, Pi.natCast_apply, map_pow, map_add (f := _), map_natCast, h5, add_zero]
      rfl
    rw [h4, map_pow, map_pow, map_pow, ← p.ι_v, vv_eq_coe_X]

theorem ePoly_gen [CharP k l] (hp : PD.p = l) (hl : 2 ≤ l) (hq : Onto T A q)
    (h1 : ∃ u : (k⟦X⟧)ˣ, ι (vv k) = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ (l - 1))
    (hγ : (W.χΓ γ : O) = 1 + (PD.p : O)) (hS : WachUse.SenOp W) (U : ZMod n₀ → Multiset ℤ)
    (hU : CrysWith PD W.emb T.ρ U) (N : Submodule k⟦X⟧ (Vc k A.m))
    (hN : ∀ y, y ∈ N ↔ ∃ x : ↥(DΔ W T), (x : W.DD T) ∈ W.N T ∧ p.j T A q i x = y) (s : ℕ)
    (hs : ∀ u ∈ U (τ i), ∀ a : ℕ, a < s → (l : ℤ) ∣ (a : ℤ) - u → (a : ℤ) = u) :
    EPoly ((F.D A).γ i) N s := by
  classical
  have hk : (PD.p : k) = 0 := by rw [hp]; exact CharP.cast_eq_zero k l
  have hc := card_Del W hl hk ι h1 p.ι_v
  obtain ⟨c, hc1, hc2⟩ := exists_c (PD := PD) (LL := LL) hk (W.χΓ γ) hγ
  obtain ⟨ν, hν, hmid, -⟩ := hS T U hU γ hγ c hc1
  set I := ((Finset.range s) ×ˢ (U (τ i)).toFinset).image (fun p => (p.1 : ℤ) - p.2) with hI
  have key : ∀ y : ↥(W.NΔ T), Polynomial.aeval (nab ((F.D A).γ i))
      (∏ m ∈ I, (Polynomial.X + Polynomial.C (m : k))) (red p T A q i y) ∈ sh s N := by
    intro y
    obtain ⟨z, hz, h⟩ := hmid (τ i) s y
    obtain ⟨z', hz'⟩ := red_div p i hq hk hc s _ z hz h
    rw [aeval_red (red p T A q i) (red_smul p i hq) ν _ (red_ν p i hq ν hν), Polynomial.map_prod] at hz'
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hc2, map_neg, sub_neg_eq_add] at hz'
    exact mem_sh_iff_exists.2 ⟨_, (hN _).2 ⟨⟨z', z'.2.2⟩, z'.2.1, rfl⟩, hz'.symm⟩
  refine ⟨∏ m ∈ I.erase 0, (Polynomial.X + Polynomial.C (m : k)), ?_, fun x hx => ?_⟩
  · rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
    intro m hm h0
    obtain ⟨hm0, hm⟩ := Finset.mem_erase.1 hm
    obtain ⟨⟨a, u⟩, hau, rfl⟩ := Finset.mem_image.1 hm
    obtain ⟨ha, hu⟩ := Finset.mem_product.1 hau
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add, CharP.intCast_eq_zero_iff k l] at h0
    exact hm0 (sub_eq_zero.2 (hs u (Multiset.mem_toFinset.1 hu) a (Finset.mem_range.1 ha) h0))
  · obtain ⟨x, hx1, rfl⟩ := (hN x).1 hx
    let y : ↥(W.NΔ T) := ⟨x, hx1, x.2⟩
    have hy : p.j T A q i x = red p T A q i y := rfl
    rw [hy]
    by_cases h0 : (0 : ℤ) ∈ I
    · have := key y
      rw [← Finset.mul_prod_erase I _ h0, map_mul, Module.End.mul_apply] at this
      simpa using this
    · have := key (ν y)
      rw [red_ν p i hq ν hν] at this
      rw [Finset.erase_eq_of_notMem h0]
      have h2 : ∀ (f : Polynomial k) (μ : Module.End k (Vc k A.m)) w,
          μ (Polynomial.aeval μ f w) = Polynomial.aeval μ f (μ w) := fun f μ w => by
        have := congrArg (fun g => Polynomial.aeval μ g w) (mul_comm Polynomial.X f)
        simpa using this
      rw [h2]; exact this

end Gen

theorem ePoly_base : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → ∀ {R : RingPG k l} (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam) (p : Pres (S.W H) F ι τ γ), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → (∀ i, (S.W H).emb (τ i) = S.emb i) → ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → GlobalTheory.WachUse.QN (S.W H) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ), Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U → ∀ N : Lats k S.n A.m, (∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y) → ∀ (i : ZMod S.n) (s : ℕ), (∀ u ∈ U i, ∀ a : ℕ, a < s → (l : ℤ) ∣ (a : ℤ) - u → (a : ℤ) = u) → EPoly ((F.D A).γ i) (N i) s := by
  intro l _ P H S k _ _ _ _ R ι F τ γ p hι hτ hγ hQ T A q U hq _ hU N hN i s hs
  have hb : Function.Bijective S.emb := S.hyp.1.2.2.2.1
  have hl : 5 ≤ l := S.hyp.1.1
  let e := Equiv.ofBijective _ hb
  have hp : (P.PD S.K).p = l := P.PD_p S.K
  refine ePoly_gen p i hp (by omega) hq hι.1 (by rw [hp]; exact hγ) hQ.2.2.2.2.2
    (fun j => U (e.symm ((S.W H).emb j))) ⟨hU.1, fun j => ?_⟩ (N i) (hN i) s ?_
  · have := hU.2 (e.symm ((S.W H).emb j))
    have h2 : S.emb (e.symm ((S.W H).emb j)) = (S.W H).emb j := e.apply_symm_apply _
    rwa [h2] at this
  · have h2 : e.symm ((S.W H).emb (τ i)) = i := by rw [hτ]; exact e.symm_apply_apply i
    simpa only [h2] using hs

end GlobalTheory.BaseLatticeE
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionSum
noncomputable section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Present.SumRed

section General
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n₀ : ℕ}

theorem exists_proj {T T' Z : LocLat G Qp LL O} (f : LatHom T.L Z.L) (g : LatHom T'.L Z.L)
    (hb : Function.Bijective (f.f.coprod g.f))
    (hs : ∀ z ∈ Z.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) :
    ∃ (p : LatHom Z.L T.L) (p' : LatHom Z.L T'.L), latAdd (latComp f p) (latComp g p') = latId Z := by
  let e : (T.V × T'.V) ≃ₗ[LL] Z.V := LinearEquiv.ofBijective _ hb
  have he : ∀ x y, e.symm (f.f x + g.f y) = (x, y) := fun x y => by
    rw [LinearEquiv.symm_apply_eq]; rfl
  have hz : ∀ z, f.f (e.symm z).1 + g.f (e.symm z).2 = z := fun z => e.apply_symm_apply z
  have hρ : ∀ σ z, e.symm (Z.ρ σ z) = (T.ρ σ (e.symm z).1, T'.ρ σ (e.symm z).2) := fun σ z => by
    rw [← he, f.equiv, g.equiv, ← map_add (f := _), hz]
  haveI := T.mtop.toContinuousSMul
  haveI := T'.mtop.toContinuousSMul
  refine ⟨⟨LinearMap.fst LL _ _ ∘ₗ e.symm.toLinearMap, fun σ z => ?_,
      IsModuleTopology.continuous_of_linearMap _, fun z h => ?_⟩,
    ⟨LinearMap.snd LL _ _ ∘ₗ e.symm.toLinearMap, fun σ z => ?_,
      IsModuleTopology.continuous_of_linearMap _, fun z h => ?_⟩, ?_⟩
  · exact congrArg Prod.fst (hρ σ z)
  · obtain ⟨x, hx, y, hy, rfl⟩ := hs z h
    change (e.symm _).1 ∈ _
    rw [he]; exact hx
  · exact congrArg Prod.snd (hρ σ z)
  · obtain ⟨x, hx, y, hy, rfl⟩ := hs z h
    change (e.symm _).2 ∈ _
    rw [he]; exact hy
  · unfold latAdd latId
    congr 1
    exact LinearMap.ext hz

variable (W : LocWach PD LL O v n₀)

theorem map_mem {T Z : LocLat G Qp LL O} (f : LatHom T.L Z.L) (x : ↥(DΔ W T)) :
    W.map f (x : W.DD T) ∈ DΔ W Z := fun δ hδ => by
  rw [← W.map_γ, x.2 δ hδ]

theorem red_sum {k : Type} [Field k] [Algebra O k] {l n : ℕ} {R : RingPG k l} {F : DFun R n G}
    {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {τ : ZMod n → ZMod n₀} {γ : W.Gam} (p : Pres W F ι τ γ)
    {T T' Z : LocLat G Qp LL O} {A A' C : Ob k G} {q q' r}
    (hq : Onto T A q) (hq' : Onto T' A' q') (hr : Onto Z C r)
    (hT : IsCrys PD T.ρ) (hT' : IsCrys PD T'.ρ) (hZ : IsCrys PD Z.ρ)
    (f : LatHom T.L Z.L) (g : LatHom T'.L Z.L) (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k))
    (b : (Fin A'.m → k) →ₗ[k] (Fin C.m → k)) (hb : Function.Bijective (f.f.coprod g.f))
    (hs : ∀ z ∈ Z.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) (ha : IsHom A C a) (hb' : IsHom A' C b)
    (hfa : ∀ (x : ↥T.L.T) (x' : ↥Z.L.T), (x' : Z.V) = f.f x → r x' = a (q x))
    (hgb : ∀ (x : ↥T'.L.T) (x' : ↥Z.L.T), (x' : Z.V) = g.f x → r x' = b (q' x))
    (N : Lats k n A.m) (N' : Lats k n A'.m) (L : Lats k n C.m)
    (hN : ∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ W T), (x : W.DD T) ∈ W.N T ∧ p.j T A q i x = y)
    (hN' : ∀ i y, y ∈ N' i ↔ ∃ x : ↥(DΔ W T'), (x : W.DD T') ∈ W.N T' ∧ p.j T' A' q' i x = y)
    (hL : ∀ i y, y ∈ L i ↔ ∃ x : ↥(DΔ W Z), (x : W.DD Z) ∈ W.N Z ∧ p.j Z C r i x = y) (i : ZMod n) :
    L i = F.push A C a N i ⊔ F.push A' C b N' i := by
  obtain ⟨π, π', hπ⟩ := exists_proj f g hb hs
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (hL i y).1 hy
    let x₁ : ↥(DΔ W T) := ⟨_, map_mem W π x⟩
    let x₂ : ↥(DΔ W T') := ⟨_, map_mem W π' x⟩
    have hsum : x = ⟨_, map_mem W f x₁⟩ + ⟨_, map_mem W g x₂⟩ := by
      apply Subtype.ext
      have := W.map_id Z x
      rw [← hπ, W.map_latAdd, W.map_comp, W.map_comp] at this
      exact this.symm
    rw [hsum, map_add (f := _), p.j_map T A q Z C r hq hr f a ha hfa i x₁ _ rfl,
      p.j_map T' A' q' Z C r hq' hr g b hb' hgb i x₂ _ rfl]
    exact Submodule.add_mem_sup
      ⟨_, (hN i _).2 ⟨x₁, W.map_N π hZ hT _ hx, rfl⟩, rfl⟩
      ⟨_, (hN' i _).2 ⟨x₂, W.map_N π' hZ hT' _ hx, rfl⟩, rfl⟩
  · refine sup_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hN i y).1 hy
      exact (hL i _).2 ⟨⟨_, map_mem W f x⟩, W.map_N f hT hZ _ hx,
        p.j_map T A q Z C r hq hr f a ha hfa i x _ rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hN' i y).1 hy
      exact (hL i _).2 ⟨⟨_, map_mem W g x⟩, W.map_N g hT' hZ _ hx,
        p.j_map T' A' q' Z C r hq' hr g b hb' hgb i x _ rfl⟩

end General

theorem reduction_sum : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → ∀ {R : RingPG k l} (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam) (p : Pres (S.W H) F ι τ γ), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → (∀ i, (S.W H).emb (τ i) = S.emb i) → ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → GlobalTheory.WachUse.QN (S.W H) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ), Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U → ∀ (T' : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A' : Ob k S.G) q' (U' : ZMod S.n → Multiset ℤ), Onto T' A' q' → KerIs S.Γ.lam q' → CrysWith (P.PD S.K) S.emb T'.ρ U' → ∀ (Z : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (C : Ob k S.G) r (V : ZMod S.n → Multiset ℤ), Onto Z C r → KerIs S.Γ.lam r → CrysWith (P.PD S.K) S.emb Z.ρ V → ∀ (f : LatHom T.L Z.L) (g : LatHom T'.L Z.L) (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k)) (b : (Fin A'.m → k) →ₗ[k] (Fin C.m → k)), Function.Bijective (f.f.coprod g.f) → (∀ z ∈ Z.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) → IsHom A C a → IsHom A' C b → (∀ (x : ↥T.L.T) (x' : ↥Z.L.T), (x' : Z.V) = f.f x → r x' = a (q x)) → (∀ (x : ↥T'.L.T) (x' : ↥Z.L.T), (x' : Z.V) = g.f x → r x' = b (q' x)) → ∀ (N : Lats k S.n A.m) (N' : Lats k S.n A'.m) (L : Lats k S.n C.m), (∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y) → (∀ i y, y ∈ N' i ↔ ∃ x : ↥(DΔ (S.W H) T'), (x : (S.W H).DD T') ∈ (S.W H).N T' ∧ p.j T' A' q' i x = y) → (∀ i y, y ∈ L i ↔ ∃ x : ↥(DΔ (S.W H) Z), (x : (S.W H).DD Z) ∈ (S.W H).N Z ∧ p.j Z C r i x = y) → ∀ i, L i = F.push A C a N i ⊔ F.push A' C b N' i := by
  intro l _ P H S k _ _ _ _ R ι F τ γ p _ _ _ _ T A q U hq _ hT T' A' q' U' hq' _ hT' Z C r V hr _ hZ
    f g a b hb hs ha hb' hfa hgb N N' L hN hN' hL i
  exact red_sum (S.W H) p hq hq' hr hT.1 hT'.1 hZ.1 f g a b hb hs ha hb' hfa hgb N N' L hN hN' hL i

end GlobalTheory.Present.SumRed
end
end

noncomputable section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open scoped LaurentSeries PowerSeries Pointwise

namespace GlobalTheory.BasePairs

def RedN {l : ℕ} [Fact l.Prime] {P : LocPrime l} {H : LocHW l P} {S : TopSit P} {k : Type} [Field k]
    [Algebra S.O k] {R : RingPG k l} {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {F : DFun R S.n S.G}
    {τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))} {γ : (S.W H).Gam} (p : Pres (S.W H) F ι τ γ)
    (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) (q : ↥T.L.T →ₗ[S.O] (Fin A.m → k)) (N : Lats k S.n A.m) :
    Prop :=
  ∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y

theorem exists_modTh_of_pres {l : ℕ} [Fact l.Prime] {P : LocPrime l} {H : LocHW l P} {S : TopSit P} {k : Type}
    [Field k] [Algebra S.O k] [CharP k l] {R : RingPG k l} {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {F : DFun R S.n S.G}
    {τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))} {γ : (S.W H).Gam} (p : Pres (S.W H) F ι τ γ)
    (hC : S.CrysCalc) (hk : S.IsRes k) (hι : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι)
    (hτ : ∀ i, (S.W H).emb (τ i) = S.emb i) (hγ : ((S.W H).χΓ γ : S.O) = 1 + (l : S.O))
    (hQ : GlobalTheory.WachUse.QN (S.W H)) :
    ∃ M : ModTh F S.D, (∀ σ, (M.ω σ : k) = algebraMap S.O k (S.Γ.ε σ)) ∧
      (∃ q : ↥S.Γ.T₀.L.T →ₗ[S.O] (Fin M.T.m → k), Function.Surjective q ∧
        KerIs S.Γ.lam q ∧ ∀ σ x, q (twistRep S.Γ.W₀ S.Γ.χ₁⁻¹ σ x) = M.T.ρ σ (q x)) ∧
      ∀ (A : Ob k S.G) (N : Type) [AddCommGroup N] [Module S.O N] (π : Representation S.O S.G N)
        (e : N ≃ₗ[S.O] (Fin A.m → k)), S.admitted π → (∀ σ x, e (twistRep π S.Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) →
        ∃ L, M.Model A L := by
  have hG : IsTopGal (P.PD S.K) S.emb S.D S.Γ := S.hyp.2.1
  have : FiniteDimensional ℚ_[l] ↥S.LL.1 := S.LL.2
  have : IsDiscreteValuationRing S.O := by
    unfold TopSit.O Formalism.BasicNotions.Loc.OL
    exact GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt l ↥S.LL.1
  have : IsFractionRing S.O ↥S.LL.1 := by
    unfold TopSit.O Formalism.BasicNotions.Loc.OL
    exact GlobalTheory.isFractionRing_integralClosure_padicInt l ↥S.LL.1
  have hθ : IsCrysChar (P.PD S.K) S.emb S.Γ.χ₁⁻¹ (fun i => -S.D.w i) :=
    (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁ S.D.w hG.2.1 hG.2.2.1).2
  have hlam : Irreducible S.Γ.lam := S.hyp.1.2.2.2.2.2
  have hpoly : ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ),
      Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U →
      ∀ N : Lats k S.n A.m, RedN p T A q N → ∀ (i : ZMod S.n) (s : ℕ),
      (∀ u ∈ U i, ∀ a : ℕ, a < s → (l : ℤ) ∣ (a : ℤ) - u → (a : ℤ) = u) → EPoly ((F.D A).γ i) (N i) s := by
    intro T A q U hq hK hc N hN i s hs
    exact BaseLatticeE.ePoly_base H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc N hN i s hs
  exact exists_real hθ hk hlam hC.1 hC.2.1 p.obj
    (fun T A q U hq hK hc => GlobalTheory.T.wachDeltaInvariants_reduction_isLattice H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc)
    (fun T A q U hq hK hc N hN w w' hw =>
      GlobalTheory.T.phiGamma_reduction_base_lattice_bounds H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc N hN w w' hw)
    (fun T A q U hq hK hc N hN i x =>
      GlobalTheory.T.senMultiset_base_lattice_eq_jumps_mod H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc N hN i x)
    hpoly
    (fun T A q U hq hK hc N hN a hm ha i =>
      GlobalTheory.T.rankOne_reduction_frobeniusPullback_eq_shift H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc N hN a hm ha i)
    (fun T A q U hq hK hc T' A' q' U' hq' hK' hc' Z C r V hr hKr hcr f g a b hb hs ha hb' hfa hgb
        N N' L hN hN' hL i =>
      GlobalTheory.Present.SumRed.reduction_sum H S k hk ι F τ γ p hι hτ hγ hQ T A q U hq hK hc T' A' q' U' hq' hK'
        hc' Z C r V hr hKr hcr f g a b hb hs ha hb' hfa hgb N N' L hN hN' hL i)
    hG hC.2.2.1 (fun ω hω e h0 h1 => omega_pow_ne_one S k ω hω e h0 h1)

theorem real_of_presented : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P)
    (E : LocFon l P AI H) (S : TopSit P), S.RealD H → GlobalTheory.WachUse.QN (S.W H) → S.CrysCalc → S.Real := by
  intro l _ P AI H _ S hR hQ hC
  unfold TopSit.Real
  intro k _ _ _ hk
  have h1 := @hR k _ _ _ hk
  obtain ⟨R, ι, hι, F, τ, γ, hτ, hγ, hp⟩ := h1
  have h2 := exists_modTh_of_pres (H := H) (S := S) (k := k) (R := R) (ι := ι) (F := F)
    (τ := τ) (γ := γ) hp.some hC hk hι hτ hγ hQ
  exact ⟨R, ι, hι, F, h2⟩

end GlobalTheory.BasePairs
