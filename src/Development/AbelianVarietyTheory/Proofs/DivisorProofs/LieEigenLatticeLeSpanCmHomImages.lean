module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormSolutionFields
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubeTrivialAndFiniteFlatSurjectiveMulAbelianSche
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenLatticeImageLeSpanAfterBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmObjHomOfTypeLinearIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmObjHomOfTypeLinearIndependent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.CM.IntCoord
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM.HomIndep

theorem phiP_independent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q) (x : Fin p → 𝓞 E),
    ∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a) = 1 → x = 0 := by
  intro E _ _ _ H K _ _ ρ σ₁ p q X x hx
  classical
  have hU := GlobalTheory.thetaUnifAV_all
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  obtain ⟨τ, hτ⟩ := GlobalTheory.CM.NumInh.exists_char X.split X.ρ_sq
  have FA : ∀ b, GenFib (X.A b).pol := fun b =>
    (GenFib.nonempty_of_baseChange hL.polBaseChange K (X.A b).pol).some
  have FB : GenFib X.B.pol := (GenFib.nonempty_of_baseChange hL.polBaseChange K X.B.pol).some
  have hMex : ∀ j : Fin p ⊕ Fin q, ∃ M, (FA j.isLeft).IsDiffOf FB (X.φ j) M := fun j =>
    ((GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K _ (FA j.isLeft) _ FB (X.φ j) (X.lin j).isMonHom).1).exists
  choose M hM using hMex
  obtain ⟨-, hrank, hinj, hind, -⟩ := GlobalTheory.CM.Indep.letters_independent hU hL E H K ρ σ₁ p q X FA FB M hM
  funext a
  show x a = 0
  have hcA := integral_tangent_coordinates K _ (FA true)
  have hcB := integral_tangent_coordinates K _ FB

  have hne : (FA true).eigLat (X.A true).t.act τ ≠ ⊥ := by
    intro h0
    have h1 := hrank (Sum.inl a, τ)
    rw [if_pos (by simpa using hτ)] at h1
    change latRank K (((FA true).eigLat (X.A true).t.act τ).map ((M (Sum.inl a)).restrictScalars (𝓞 K))) = 1 at h1
    rw [h0] at h1
    have hb : Submodule.span K (((⊥ : Submodule (𝓞 K) (Fin (FA true).P₀.g → K)).map
        ((M (Sum.inl a)).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin FB.P₀.g → K)) : Set (Fin FB.P₀.g → K)) = ⊥ :=
      Submodule.span_eq_bot.2 fun z hz => by
        obtain ⟨y, hy, rfl⟩ := hz
        obtain rfl : y = 0 := (Submodule.mem_bot (𝓞 K)).1 hy
        exact map_zero _
    rw [latRank, hb, finrank_bot] at h1
    exact zero_ne_one h1
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨u, hu, heig⟩ := (hcA.2.2.2.2.2 _ _ τ e).1 he
  have hs : ∀ b, FB.IsCoord (u ≫ ((X.A true).t.act.act (x b) ≫ phiP X b)) (M (Sum.inl b) (τ (x b) • e)) := by
    intro b
    rw [← Category.assoc]
    exact hM (Sum.inl b) _ _ (isCoord_smul (FA true) hu (heig (x b)))
  have hprod : ∀ s : Finset (Fin p), FB.IsCoord (u ≫ ∏ b ∈ s, ((X.A true).t.act.act (x b) ≫ phiP X b))
      (∑ b ∈ s, M (Sum.inl b) (τ (x b) • e)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, comp_one]
      exact isCoord_one FB
    | insert b s hb ih =>
      rw [Finset.prod_insert hb, Finset.sum_insert hb, comp_mul]
      exact isCoord_mul FB (hs b) ih
  have hsum : ∑ b, M (Sum.inl b) (τ (x b) • e) = 0 := by
    have h1 := hprod Finset.univ
    rw [hx, comp_one] at h1
    exact (hcB.1 _ h1.1).unique h1 (isCoord_one FB)
  have hind' := hind.comp (f := fun b : Fin p => ((Sum.inl b, τ) : (Fin p ⊕ Fin q) × (𝓞 E →+* 𝓞 K)))
    (fun b b' h => Sum.inl_injective (Prod.ext_iff.1 h).1)
  have hva := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1 hind' Finset.univ
    (fun b => M (Sum.inl b) (τ (x b) • e))
    (fun b _ => Submodule.subset_span (Submodule.mem_map_of_mem
      (f := (M (Sum.inl b)).restrictScalars (𝓞 K)) (Submodule.smul_mem _ (τ (x b)) he))) hsum a (Finset.mem_univ a)
  have h0 : τ (x a) • e = 0 := hinj (Sum.inl a) (by rw [hva]; exact (map_zero _).symm)
  rw [← algebraMap_smul K (τ (x a)) e, smul_eq_zero] at h0
  have hτa : τ (x a) = 0 :=
    (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).1 (h0.resolve_right he0)
  exact GlobalTheory.CM.ringOfIntegers_hom_injective τ (by rw [hτa, map_zero])

end GlobalTheory.FlatCM.HomIndep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmObjHomOfTypeLinearIndependentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmObjHomOfType_linearIndependent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q)
    (x : Fin p → 𝓞 E), ∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a) = 1 → x = 0 := by
  first | exact @GlobalTheory.FlatCM.HomIndep.phiP_independent | exact GlobalTheory.FlatCM.HomIndep.phiP_independent | (intros; apply GlobalTheory.FlatCM.HomIndep.phiP_independent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowOfBaseChangeEqPowPrincipalAbelianCMTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowOfBaseChangeEqPowPrincipalAbelianCMTriple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem flat_surjective_spMap_ringOfIntegers (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') :
    Flat (spMap (RingOfIntegers.mapRingHom j)) ∧ Surjective (spMap (RingOfIntegers.mapRingHom j)) := by
  letI : Algebra (𝓞 K) (𝓞 K') := (RingOfIntegers.mapRingHom j).toAlgebra
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 K')) := by
    intro a b h
    apply RingOfIntegers.coe_injective
    apply j.injective
    exact congrArg ((↑) : 𝓞 K' → K') h
  haveI : FaithfulSMul (𝓞 K) (𝓞 K') := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : Module.Flat (𝓞 K) (𝓞 K') := inferInstance
  haveI : Algebra.IsIntegral (𝓞 K) (𝓞 K') := by
    constructor
    intro x
    exact IsIntegral.tower_top (R := ℤ) (Algebra.IsIntegral.isIntegral (R := ℤ) x)
  refine ⟨Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance), ⟨fun p => ?_⟩⟩
  let p' : PrimeSpectrum (𝓞 K) := p
  obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 K') p'.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQp⟩

theorem eq_pow_of_baseChange_eq_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (A B : PAT H (Sp (𝓞 K))) (A' B' : PAT H (Sp (𝓞 K'))) (mA : SABMap A'.t A.t (spMap (RingOfIntegers.mapRingHom j)))
    (mB : SABMap B'.t B.t (spMap (RingOfIntegers.mapRingHom j))) (g : A.t.G ⟶ B.t.G) (f' : A'.t.G ⟶ B'.t.G) (n : ℕ),
    0 < n → Serre.IsLinearHom A.t.act B.t.act g → Serre.IsLinearHom A'.t.act B'.t.act f' →
    (f' ^ n).left ≫ mB.φ = mA.φ ≫ g.left →
    ∃ f : A.t.G ⟶ B.t.G, Serre.IsLinearHom A.t.act B.t.act f ∧ f ^ n = g ∧ f'.left ≫ mB.φ = mA.φ ≫ f.left := by
  intro E _ _ _ H K K' _ _ _ _ j A B A' B' mA mB g f' n hn hg hf' hfg
  have hpow : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (m : ℕ), IsMonHom (𝟙 G ^ m) := by
    intro S G _ _ m
    induction m with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))
    | succ m ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 G ^ m) (𝟙 G) ≫ μ[G]))
  have hffs : ∀ {R : Type} [CommRing R] (P : PAT H (Sp R)), IsFinite (𝟙 P.t.G ^ n).left ∧
      Flat (𝟙 P.t.G ^ n).left ∧ Surjective (𝟙 P.t.G ^ n).left := by
    intro R _ P
    exact (ChF.exists_gen_theta_tensor_and_finite_flat_surjective_pow R P.t.G P.t.PP.L
      (P.t.PP.L.pull (fst P.t.G P.t.G).left) P.ab P.t.PP.isLB P.ample (LB.isLB_pull P.t.PP.isLB _)).2 n hn
  have hepi : ∀ {S : Scheme.{0}} {X Y : Over S} (u : X ⟶ Y), Flat u.left → Surjective u.left → Epi u := by
    intro S X Y u h1 h2
    haveI : Epi ((Over.forget S).map u) := Flat.epi_of_flat_of_surjective u.left
    exact (Over.forget S).epi_of_epi_map this
  obtain ⟨hAfin, hAfl, hAsu⟩ := hffs A
  obtain ⟨-, hA'fl, hA'su⟩ := hffs A'
  have hq : QuasiCompact (𝟙 A.t.G ^ n).left := inferInstance
  obtain ⟨hflatj, hsurj⟩ := flat_surjective_spMap_ringOfIntegers K K' j
  have hker : ∀ (T : Over (Sp (𝓞 K))) (x : T ⟶ A.t.G), x ≫ (𝟙 A.t.G ^ n) = 1 → x ≫ g = 1 := by
    intro T x hx
    have hb : pullback.fst T.hom (spMap (RingOfIntegers.mapRingHom j)) ≫ T.hom =
        pullback.snd T.hom (spMap (RingOfIntegers.mapRingHom j)) ≫ spMap (RingOfIntegers.mapRingHom j) :=
      pullback.condition
    obtain ⟨eA, heA⟩ := exists_mulEquiv_of_isGrpPullback mA.cart _ _ hb
    obtain ⟨eB, heB⟩ := exists_mulEquiv_of_isGrpPullback mB.cart _ _ hb
    let prO : Over.mk (pullback.fst T.hom (spMap (RingOfIntegers.mapRingHom j)) ≫ T.hom) ⟶ T :=
      Over.homMk (pullback.fst T.hom (spMap (RingOfIntegers.mapRingHom j))) rfl
    have hE : Epi prO := by
      haveI := hflatj
      haveI := hsurj
      exact hepi prO (inferInstanceAs (Flat (pullback.fst _ _))) (inferInstanceAs (Surjective (pullback.fst _ _)))
    have hxn : x ^ n = 1 := by rw [← hx, MonObj.comp_pow, Category.comp_id]
    have hx' : eA.symm (prO ≫ x) ^ n = 1 := by
      apply eA.injective
      rw [map_pow, map_one, MulEquiv.apply_symm_apply, ← MonObj.comp_pow, hxn, MonObj.comp_one]
    have e2 : eA.symm (prO ≫ x) ≫ (f' ^ n) = 1 := by
      haveI := hf'.isMonHom
      rw [MonObj.comp_pow, ← MonObj.pow_comp, hx', MonObj.one_comp]
    have e1 : eB (eA.symm (prO ≫ x) ≫ (f' ^ n)) = prO ≫ x ≫ g := by
      apply Over.OverMorphism.ext
      rw [heB, Over.comp_left, Category.assoc, hfg, ← Category.assoc, ← heA, MulEquiv.apply_symm_apply]
      simp only [Over.comp_left, Category.assoc]
    have : prO ≫ (x ≫ g) = prO ≫ 1 := by rw [← e1, e2, map_one, MonObj.comp_one]
    exact (cancel_epi prO).1 this
  haveI := hg.isMonHom
  haveI := hpow A.t.G n
  obtain ⟨⟨ψ, hψ, hψg⟩, hEpiA⟩ := exists_monHom_factor_of_flat_surjective _ A.t.G A.t.G B.t.G (𝟙 A.t.G ^ n) g
    (hpow _ n) hg.isMonHom hAfl hAsu hq hker
  haveI := hψ
  have hψn : ψ ^ n = g := by rw [← hψg, MonObj.pow_comp, Category.id_comp]
  have hlin : Serre.IsLinearHom A.t.act B.t.act ψ := by
    refine ⟨hψ, fun c => ?_⟩
    haveI := A.t.act.hom c
    rw [← cancel_epi (𝟙 A.t.G ^ n)]
    have hc : (𝟙 A.t.G ^ n) ≫ A.t.act.act c = A.t.act.act c ≫ (𝟙 A.t.G ^ n) := by
      rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
    rw [reassoc_of% hc, hψg, reassoc_of% hψg]
    exact hg.comm c
  obtain ⟨w, hw, hwc⟩ := PairingFibre.exists_hom mA.cart mB.cart ψ
  haveI := hw
  haveI := hf'.isMonHom
  have hφ : mA.φ ≫ A.t.G.hom = A'.t.G.hom ≫ spMap (RingOfIntegers.mapRingHom j) := mA.cart.1.w
  have hpw : ∀ m : ℕ, (w ^ (m + 1)).left ≫ mB.φ = mA.φ ≫ (ψ ^ (m + 1)).left := by
    intro m
    induction m with
    | zero => rw [zero_add, pow_one, pow_one]; exact hwc
    | succ m ih =>
      rw [pow_succ w, pow_succ ψ]
      exact FamDesc.exists_mul hφ mB.cart ih hwc
  have hwn : w ^ n = f' ^ n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    apply Over.OverMorphism.ext
    apply mB.cart.1.hom_ext
    · rw [hpw m, hψn, hfg]
    · rw [Over.w, Over.w]
  have hwf : w = f' := by
    haveI := hepi (𝟙 A'.t.G ^ n) hA'fl hA'su
    rw [← cancel_epi (𝟙 A'.t.G ^ n), MonObj.pow_comp, MonObj.pow_comp, Category.id_comp, Category.id_comp, hwn]
  refine ⟨ψ, hlin, hψn, ?_⟩
  rw [← hwf]
  exact hwc

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowOfBaseChangeEqPowPrincipalAbelianCMTripleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_pow_of_baseChange_eq_pow_principalAbelianCMTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (A B : PAT H (Sp (𝓞 K))) (A' B' : PAT H (Sp (𝓞 K'))) (mA : SABMap A'.t A.t (spMap (RingOfIntegers.mapRingHom j)))
    (mB : SABMap B'.t B.t (spMap (RingOfIntegers.mapRingHom j))) (g : A.t.G ⟶ B.t.G) (f' : A'.t.G ⟶ B'.t.G) (n : ℕ),
    0 < n → Serre.IsLinearHom A.t.act B.t.act g → Serre.IsLinearHom A'.t.act B'.t.act f' →
    (f' ^ n).left ≫ mB.φ = mA.φ ≫ g.left →
    ∃ f : A.t.G ⟶ B.t.G, Serre.IsLinearHom A.t.act B.t.act f ∧ f ^ n = g ∧ f'.left ≫ mB.φ = mA.φ ≫ f.left := by
  first | exact @GlobalTheory.eq_pow_of_baseChange_eq_pow | exact GlobalTheory.eq_pow_of_baseChange_eq_pow | (intros; apply GlobalTheory.eq_pow_of_baseChange_eq_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionPrincipalTriplesTensorLatti
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionPrincipalTriplesTensorLatti
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.TenPair

theorem spMap_comp_ringHom {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') : spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]
  rfl

theorem mapRingHom_comp {K K' K'' : Type} [Field K] [Field K'] [Field K''] (f : K →+* K') (g : K' →+* K'') :
    (RingOfIntegers.mapRingHom g).comp (RingOfIntegers.mapRingHom f) = RingOfIntegers.mapRingHom (g.comp f) :=
  RingHom.ext fun _ => rfl

theorem exists_isTen_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (A B : PAT H (Sp (𝓞 K))) (r s : ℕ),
    ρ ^ 2 = -(H.d : 𝓞 K) → HasType H A.t.act ρ r 0 → HasType H B.t.act ρ s 0 →
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (j : K →+* K') (ω : 𝓞 K') (C : Ell H (𝓞 K') ω)
      (A' B' : PAT H (Sp (𝓞 K'))) (_ : SABMap A'.t A.t (spMap (RingOfIntegers.mapRingHom j)))
      (_ : SABMap B'.t B.t (spMap (RingOfIntegers.mapRingHom j))) (DA DB : Datum H)
      (hA : DA.La → DA.La → OK H) (hB : DB.La → DB.La → OK H),
      DA.p + DA.q = r ∧ DB.p + DB.q = s ∧ Nonempty (IsTen C DA hA A') ∧ Nonempty (IsTen C DB hB B') := by
  intro E _ _ _ H K _ _ ρ A B r s hρ hA hB
  have hU : ThetaUnifAV := GlobalTheory.thetaUnifAV_all
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hE : HomExtDvr := GlobalTheory.homExtension_semiAbelian_dvr_unconditional
  have hC : CMCurve := GlobalTheory.cmCurve_closed
  have hPB : Out.PolBaseChangeSt := hL.polBaseChange
  haveI : NeZero H.d := ⟨H.d_prime.ne_zero⟩
  obtain ⟨χ, hχ⟩ := GlobalTheory.exists_isKroneckerChar (d := H.d) H.d_prime.ne_zero (Or.inr (by have := H.d_mod; omega))
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hρ₀ : (σ (ρ : K)) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (σ.comp (algebraMap (𝓞 K) K)) hρ
    simpa using this
  obtain ⟨M, _, ω, C, x, hω, hP, -, -⟩ := GlobalTheory.CM.EllExists.exists_ell hC hU hL hE E H χ hχ _ hρ₀
  obtain ⟨k, _, j, i, hj, hi⟩ := PureDeg.exists_compositum K σ M
  obtain ⟨A', mA', -⟩ := PAT.exists_pullback E H _ _ (spMap (RingOfIntegers.mapRingHom j)) A
  obtain ⟨C', φ', hC'⟩ := exists_ellMap hPB E H _ ω C _ (RingOfIntegers.mapRingHom i)
  have e : 2 * RingOfIntegers.mapRingHom i ω - 1 = RingOfIntegers.mapRingHom j ρ := by
    apply RingOfIntegers.ext
    apply Subtype.ext
    have h1 : (((RingOfIntegers.mapRingHom j ρ : 𝓞 k) : k) : ℂ) = σ ρ := hj _
    have h2 : (((RingOfIntegers.mapRingHom i ω : 𝓞 k) : k) : ℂ) = (ω : M) := hi _
    rw [h1, ← hω, ← h2]
    rfl
  have hA' : HasType H A'.t.act (2 * RingOfIntegers.mapRingHom i ω - 1) r 0 := by
    rw [e]
    exact (hasType_baseChange E H _ _ _ A.t A'.t mA' ρ r 0).1 (PureDeg.mapRingHom_injective j) hA
  have hP' : C'.IsPrincipalAt ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) := by
    refine (EllComp.ellMap_comp E H _ ω C _ _ C' _ φ' hC').2.1 _ ?_
    convert hP using 1
    ext a
    exact hi _
  obtain ⟨k₁, _, hk, ω₁, C₁, φ₁, A₁, mA₁, DA, -, ha, hC₁, hDA, -, -, ⟨tA⟩⟩ :=
    GlobalTheory.CM.Recog.exists_isTen_of_hasType hU hL hE E H k _ C' A' r hP' hA'
  let j₁ : K →+* k₁ := (IntermediateField.inclusion hk).toRingHom.comp j
  obtain ⟨B₁, mB₁, -⟩ := PAT.exists_pullback E H _ _ (spMap (RingOfIntegers.mapRingHom j₁)) B
  have e₁ : 2 * ω₁ - 1 = RingOfIntegers.mapRingHom j₁ ρ := by
    have h3 := congrArg (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom) e
    simp only [map_sub, map_mul, map_ofNat, map_one, hC₁.1] at h3
    rw [h3]
    rfl
  have hB₁ : HasType H B₁.t.act (2 * ω₁ - 1) s 0 := by
    rw [e₁]
    exact (hasType_baseChange E H _ _ _ B.t B₁.t mB₁ ρ s 0).1 (PureDeg.mapRingHom_injective j₁) hB
  have hP₁ : C₁.IsPrincipalAt ((algebraMap k₁ ℂ).comp (algebraMap (𝓞 k₁) k₁)) := by
    refine (EllComp.ellMap_comp E H _ _ C' _ _ C₁ _ φ₁ hC₁).2.1 _ ?_
    convert hP' using 1
    ext a
    rfl
  obtain ⟨k₂, _, hk', ω₂, C₂, φ₂, B₂, mB₂, DB, -, hb, hC₂, hDB, -, -, ⟨tB⟩⟩ :=
    GlobalTheory.CM.Recog.exists_isTen_of_hasType hU hL hE E H k₁ ω₁ C₁ B₁ s hP₁ hB₁
  obtain ⟨A₂, mA₂, -⟩ := PAT.exists_pullback E H _ _
    (spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk').toRingHom)) A₁
  obtain ⟨tA₂, -⟩ := isTen_baseChange E H _ ω₁ C₁ DA ha A₁ tA _ ω₂ C₂ _ φ₂ A₂ mA₂ hC₂
  let J : K →+* k₂ := (IntermediateField.inclusion hk').toRingHom.comp j₁
  obtain ⟨nA₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mA' mA₁
  obtain ⟨nA, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp nA₁ mA₂
  obtain ⟨nB, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mB₁ mB₂
  have eA : spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk').toRingHom) ≫
      (spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom) ≫
        spMap (RingOfIntegers.mapRingHom j)) = spMap (RingOfIntegers.mapRingHom J) := by
    rw [spMap_comp_ringHom, spMap_comp_ringHom, mapRingHom_comp, mapRingHom_comp]
  have eB : spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk').toRingHom) ≫
      spMap (RingOfIntegers.mapRingHom j₁) = spMap (RingOfIntegers.mapRingHom J) := by
    rw [spMap_comp_ringHom, mapRingHom_comp]
  exact ⟨k₂, inferInstance, inferInstance, J, ω₂, C₂, A₂, B₂, eA ▸ nA, eB ▸ nB, DA, DB, ha, hb, hDA, hDB,
    ⟨tA₂⟩, ⟨tB⟩⟩

end GlobalTheory.CM.TenPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionPrincipalTriplesTensorLattiStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteExtension_principalTriples_tensorLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (A B : PAT H (Sp (𝓞 K))) (r s : ℕ),
    ρ ^ 2 = -(H.d : 𝓞 K) → HasType H A.t.act ρ r 0 → HasType H B.t.act ρ s 0 →
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (j : K →+* K') (ω : 𝓞 K') (C : Ell H (𝓞 K') ω)
      (A' B' : PAT H (Sp (𝓞 K'))) (_ : SABMap A'.t A.t (spMap (RingOfIntegers.mapRingHom j)))
      (_ : SABMap B'.t B.t (spMap (RingOfIntegers.mapRingHom j))) (DA DB : Datum H)
      (hA : DA.La → DA.La → OK H) (hB : DB.La → DB.La → OK H),
      DA.p + DA.q = r ∧ DB.p + DB.q = s ∧ Nonempty (IsTen C DA hA A') ∧ Nonempty (IsTen C DB hB B') := by
  first | exact @GlobalTheory.CM.TenPair.exists_isTen_pair | exact GlobalTheory.CM.TenPair.exists_isTen_pair | (intros; apply GlobalTheory.CM.TenPair.exists_isTen_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenLatticeImageLeSpanAfterBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenLattice_image_le_span_after_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (A B : PAT H (Sp (𝓞 K))) (A' B' : PAT H (Sp (𝓞 K'))) (mA : SABMap A'.t A.t (spMap (RingOfIntegers.mapRingHom j)))
    (mB : SABMap B'.t B.t (spMap (RingOfIntegers.mapRingHom j))) (n : ℕ) (f : Fin n → (A.t.G ⟶ B.t.G))
    (f' : Fin n → (A'.t.G ⟶ B'.t.G)) (g' : Fin n → (B'.t.G ⟶ A'.t.G)),
    (∀ i, Serre.IsLinearHom A.t.act B.t.act (f i)) → (∀ i, Serre.IsLinearHom A'.t.act B'.t.act (f' i)) →
    (∀ i, Serre.IsLinearHom B'.t.act A'.t.act (g' i)) → (∀ i, (f' i).left ≫ mB.φ = mA.φ ≫ (f i).left) →
    ∏ i, (g' i ≫ f' i) = 𝟙 B'.t.G →
    ∀ (FA : GenFib A.pol) (FB : GenFib B.pol) (M : Fin n → ((Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
    (∀ i, FA.IsDiffOf FB (f i) (M i)) → ∀ (τ : 𝓞 E →+* 𝓞 K), ∀ w ∈ FB.eigLat B.t.act τ,
    (fun k => j (w k)) ∈ Submodule.span (𝓞 K') ((fun (c : Fin FB.P₀.g → K) k => j (c k)) ''
      {v | ∃ i, ∃ e ∈ FA.eigLat A.t.act τ, v = M i e}) := by
  first | exact @GlobalTheory.CM.LieSpanBaseChange.eigLat_image_le_span_diff | exact GlobalTheory.CM.LieSpanBaseChange.eigLat_image_le_span_diff | (intros; apply GlobalTheory.CM.LieSpanBaseChange.eigLat_image_le_span_diff <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTensorRetractOfCmDatumRankOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTensorRetractOfCmDatumRankOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem smul_comm_of_finrank_one (D : Datum H) (h : Module.finrank (𝓞 E) D.La = 1)
    (l : D.La →ₗ[𝓞 E] 𝓞 E) (x y : D.La) : l x • y = l y • x := by
  have := D.fin
  have := D.proj
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨r, s, hr, e⟩ := CMLat.exists_smul_eq_smul h hx y
  have hl : r * l y = s * l x := by rw [← smul_eq_mul, ← map_smul, e, map_smul, smul_eq_mul]
  have h0 : r • (l x • y - l y • x) = 0 := by
    rw [smul_sub, smul_comm r (l x) y, e, smul_smul, smul_smul, hl, mul_comm, sub_self]
  rw [smul_eq_zero] at h0
  exact sub_eq_zero.1 (h0.resolve_left hr)

theorem exists_dualBasis (D : Datum H) :
    ∃ (n : ℕ) (a : Fin n → D.La) (l : Fin n → (D.La →ₗ[𝓞 E] 𝓞 E)), ∀ x, ∑ k, l k x • a k = x := by
  have := D.fin
  have := D.proj
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) D.La
  refine ⟨n, fun k => f (fun j => if k = j then 1 else 0), fun k => LinearMap.proj k ∘ₗ g, fun x => ?_⟩
  have hx : f (g x) = x := LinearMap.congr_fun hfg x
  conv_rhs => rw [← hx, LinearMap.pi_apply_eq_sum_univ f (g x)]
  rfl

theorem exists_sum_comp_eq_id (DA DB : Datum H) (hA : DA.p + DA.q = 1) :
    ∃ (n : ℕ) (α : Fin n → (DA.La →ₗ[𝓞 E] DB.La)) (β : Fin n → (DB.La →ₗ[𝓞 E] DA.La)),
      ∑ i, α i ∘ₗ β i = LinearMap.id := by
  have := DA.fin
  have := DA.proj
  have hr : Module.finrank (𝓞 E) DA.La = 1 := by rw [DA.rank, hA]
  obtain ⟨n, a, l, decA⟩ := exists_dualBasis DA
  obtain ⟨m, b, mu, decB⟩ := exists_dualBasis DB
  have tr : ∑ k, l k (a k) = 1 := by
    have : Nontrivial DA.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [hr]; exact one_pos)
    obtain ⟨x, hx⟩ := exists_ne (0 : DA.La)
    have e : (∑ k, l k (a k)) • x = (1 : 𝓞 E) • x := by
      rw [Finset.sum_smul, one_smul]
      conv_rhs => rw [← decA x]
      exact Finset.sum_congr rfl fun k _ => smul_comm_of_finrank_one DA hr (l k) (a k) x
    have h0 : ((∑ k, l k (a k)) - 1) • x = 0 := by rw [sub_smul, e, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_right hx)
  refine ⟨n * m, fun i => (l (finProdFinEquiv.symm i).1).smulRight (b (finProdFinEquiv.symm i).2),
    fun i => (mu (finProdFinEquiv.symm i).2).smulRight (a (finProdFinEquiv.symm i).1), ?_⟩
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.sum_apply, LinearMap.id_apply]
  rw [finProdFinEquiv.symm.sum_comp (fun p : Fin n × Fin m =>
    ((l p.1).smulRight (b p.2) ∘ₗ (mu p.2).smulRight (a p.1)) y), Fintype.sum_prod_type, Finset.sum_comm]
  conv_rhs => rw [← decB y]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [LinearMap.comp_apply, LinearMap.smulRight_apply, map_smul, smul_eq_mul, smul_smul]
  rw [← Finset.sum_smul, ← Finset.mul_sum, tr, _root_.mul_one]

end GlobalTheory.CM
end

noncomputable section
namespace GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] {ω : R}
  {C : Ell H R ω}

theorem IsTen.isLinearHom_mapLeft {A B : PAT H (Sp R)} {DA DB : Datum H} {hA : DA.La → DA.La → OK H}
    {hB : DB.La → DB.La → OK H} (tA : IsTen C DA hA A) (tB : IsTen C DB hB B) (φ : DA.La →ₗ[𝓞 E] DB.La) :
    Serre.IsLinearHom A.t.act B.t.act (tA.ten.mapLeft tB.ten (φ.restrictScalars (OK H))) := by
  refine ⟨inferInstance, fun s => ?_⟩
  have := A.t.act.hom s
  have := B.t.act.hom s
  refine tA.ten.hom_ext fun m => ?_
  rw [← Category.assoc, ← tA.lin, Serre.IsTensor.tmul_mapLeft, ← Category.assoc, Serre.IsTensor.tmul_mapLeft,
    LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, map_smul, tB.lin]

theorem IsTen.prod_mapLeft {B : PAT H (Sp R)} {DB : Datum H} {hB : DB.La → DB.La → OK H}
    (tB : IsTen C DB hB B) {I : Type} (s : Finset I) (φ : I → (DB.La →ₗ[𝓞 E] DB.La)) :
    ∏ i ∈ s, tB.ten.mapLeft tB.ten ((φ i).restrictScalars (OK H)) =
      tB.ten.mapLeft tB.ten ((∑ i ∈ s, φ i).restrictScalars (OK H)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, LinearMap.restrictScalars_zero, Serre.IsTensor.mapLeft_zero]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, LinearMap.restrictScalars_add, Serre.IsTensor.mapLeft_add]

theorem isTen_retract_of_rank_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (A B : PAT H (Sp R)) (DA DB : Datum H)
    (hA : DA.La → DA.La → OK H) (hB : DB.La → DB.La → OK H), DA.p + DA.q = 1 → IsTen C DA hA A → IsTen C DB hB B →
    ∃ (n : ℕ) (f : Fin n → (A.t.G ⟶ B.t.G)) (g : Fin n → (B.t.G ⟶ A.t.G)),
      (∀ i, Serre.IsLinearHom A.t.act B.t.act (f i)) ∧ (∀ i, Serre.IsLinearHom B.t.act A.t.act (g i)) ∧
      ∏ i, (g i ≫ f i) = 𝟙 B.t.G := by
  intro E _ _ _ H R _ ω C A B DA DB hA hB h tA tB
  obtain ⟨n, α, β, hαβ⟩ := exists_sum_comp_eq_id DA DB h
  refine ⟨n, fun i => tA.ten.mapLeft tB.ten ((α i).restrictScalars (OK H)),
    fun i => tB.ten.mapLeft tA.ten ((β i).restrictScalars (OK H)),
    fun i => tA.isLinearHom_mapLeft tB (α i), fun i => tB.isLinearHom_mapLeft tA (β i), ?_⟩
  have e : ∀ i, tB.ten.mapLeft tA.ten ((β i).restrictScalars (OK H)) ≫ tA.ten.mapLeft tB.ten ((α i).restrictScalars (OK H))
      = tB.ten.mapLeft tB.ten ((α i ∘ₗ β i).restrictScalars (OK H)) := fun i =>
    (Serre.IsTensor.mapLeft_comp _ _ _ _ _).symm
  simp only [e]
  rw [tB.prod_mapLeft, hαβ]
  exact Serre.IsTensor.mapLeft_id _

end GlobalTheory.CM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTensorRetractOfCmDatumRankOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmTensor_retract_of_cmDatum_rank_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (A B : PAT H (Sp R)) (DA DB : Datum H)
    (hA : DA.La → DA.La → OK H) (hB : DB.La → DB.La → OK H), DA.p + DA.q = 1 → IsTen C DA hA A → IsTen C DB hB B →
    ∃ (n : ℕ) (f : Fin n → (A.t.G ⟶ B.t.G)) (g : Fin n → (B.t.G ⟶ A.t.G)),
      (∀ i, Serre.IsLinearHom A.t.act B.t.act (f i)) ∧ (∀ i, Serre.IsLinearHom B.t.act A.t.act (g i)) ∧
      ∏ i, (g i ≫ f i) = 𝟙 B.t.G := by
  first | exact @GlobalTheory.CM.isTen_retract_of_rank_one | exact GlobalTheory.CM.isTen_retract_of_rank_one | (intros; apply GlobalTheory.CM.isTen_retract_of_rank_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfMemSpanRingOfIntegersMapNumberField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfMemSpanRingOfIntegersMapNumberField
open NumberField
open scoped TensorProduct

namespace GlobalTheory.FlatDescent

theorem mem_of_mem_span_of_isBaseChange {A B M M' : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    [Module B M'] [IsScalarTower A B M'] {f : M →ₗ[A] M'} (hf : IsBaseChange B f)
    (N : Submodule A M) (w : M) (hw : f w ∈ Submodule.span B (f '' (N : Set M))) : w ∈ N := by
  let g : B ⊗[A] N →ₗ[B] M' := hf.equiv.toLinearMap ∘ₗ N.subtype.baseChange B
  have hspan : Submodule.span B (f '' (N : Set M)) ≤ LinearMap.range g := by
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨(1 : B) ⊗ₜ[A] (⟨c, hc⟩ : N), by simp [g, IsBaseChange.equiv_tmul]⟩
  obtain ⟨x, hx⟩ := hspan hw
  have h1 : (1 : B) ⊗ₜ[A] w = N.subtype.baseChange B x := by
    apply hf.equiv.injective
    have : hf.equiv (N.subtype.baseChange B x) = f w := hx
    rw [this, IsBaseChange.equiv_tmul, one_smul]
  have hq : N.mkQ ∘ₗ N.subtype = 0 := by
    ext c
    simp
  have h2 : (1 : B) ⊗ₜ[A] (N.mkQ w) = 0 := by
    have := congrArg (N.mkQ.baseChange B) h1
    rw [LinearMap.baseChange_tmul] at this
    rw [this, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hq, LinearMap.baseChange_zero,
      LinearMap.zero_apply]
  have h3 : N.mkQ w = 0 := by
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) (M ⧸ N)
    simpa using h2
  simpa using h3

theorem mem_of_mem_span_map :
    ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (n : ℕ)
    (N : Submodule (𝓞 K) (Fin n → K)) (w : Fin n → K),
    (fun i => j (w i)) ∈ Submodule.span (𝓞 K') ((fun (c : Fin n → K) i => j (c i)) '' (N : Set (Fin n → K))) → w ∈ N := by
  intro K K' _ _ _ _ j n N w hw
  letI := j.toAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K') (nonZeroDivisors (𝓞 K))) K' :=
    IsIntegralClosure.isLocalization (𝓞 K) K K' (𝓞 K')
  have hP : Algebra.IsPushout (𝓞 K) (𝓞 K') K K' :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors (𝓞 K)) K (𝓞 K') K'
  have hb : IsBaseChange (𝓞 K')
      ((IsScalarTower.toAlgHom (𝓞 K) K K').toLinearMap.compLeft (Fin n)) :=
    hP.out.finitePow (Fin n)
  exact mem_of_mem_span_of_isBaseChange hb N w hw

end GlobalTheory.FlatDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfMemSpanRingOfIntegersMapNumberFieldStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_mem_span_ringOfIntegers_map_numberField : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (n : ℕ)
    (N : Submodule (𝓞 K) (Fin n → K)) (w : Fin n → K),
    (fun i => j (w i)) ∈ Submodule.span (𝓞 K') ((fun (c : Fin n → K) i => j (c i)) '' (N : Set (Fin n → K))) → w ∈ N := by
  first | exact @GlobalTheory.FlatDescent.mem_of_mem_span_map | exact GlobalTheory.FlatDescent.mem_of_mem_span_map | (intros; apply GlobalTheory.FlatDescent.mem_of_mem_span_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieEigenLatticeLeSpanCmHomImages
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.FlatCM.HomLat.LieSpan

section Over

variable {S S' : Scheme.{0}} {s : S' ⟶ S} {G B : Over S} {G' B' : Over S'} [GrpObj B] [GrpObj B'] [IsCommMonObj B]
  [IsCommMonObj B'] {φ : G'.left ⟶ G.left} {m : B'.left ⟶ B.left}

theorem one_over (w : φ ≫ G.hom = G'.hom ≫ s) (hm : IsGrpPullback B' B s m) :
    (1 : G' ⟶ B').left ≫ m = φ ≫ (1 : G ⟶ B).left := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hm G'.hom (G'.hom ≫ s) rfl
  let φ₀ : Over.mk (G'.hom ≫ s) ⟶ G := Over.homMk φ w
  have h1 := he 1
  rw [map_one, ← comp_one φ₀] at h1
  exact h1.symm

theorem prod_over (w : φ ≫ G.hom = G'.hom ≫ s) (hm : IsGrpPullback B' B s m) {I : Type} (t : Finset I)
    {x' : I → (G' ⟶ B')} {x : I → (G ⟶ B)} (h : ∀ i, (x' i).left ≫ m = φ ≫ (x i).left) :
    (∏ i ∈ t, x' i).left ≫ m = φ ≫ (∏ i ∈ t, x i).left := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using one_over w hm
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact FamDesc.exists_mul w hm (h a) ih

end Over

section Rel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R R' : Type} [CommRing R] [CommRing R']
  {j : R →+* R'} {A B : PAT H (Sp R)} {A' B' : PAT H (Sp R')} (mA : SABMap A'.t A.t (spMap j))
  (mB : SABMap B'.t B.t (spMap j))

theorem exists_linear_over {f : A.t.G ⟶ B.t.G} (hf : Serre.IsLinearHom A.t.act B.t.act f) :
    ∃ f' : A'.t.G ⟶ B'.t.G, Serre.IsLinearHom A'.t.act B'.t.act f' ∧ f'.left ≫ mB.φ = mA.φ ≫ f.left := by
  haveI := hf.isMonHom
  obtain ⟨f', hm, e⟩ := PairingFibre.exists_hom mA.cart mB.cart f
  refine ⟨f', ⟨hm, fun c => ?_⟩, e⟩
  apply Over.OverMorphism.ext
  apply mB.cart.1.hom_ext
  · have hc := congrArg CommaMorphism.left (hf.comm c)
    simp only [Over.comp_left] at hc ⊢
    rw [Category.assoc, e, ← Category.assoc, mA.act c, Category.assoc, hc, Category.assoc, mB.act c,
      ← Category.assoc, ← Category.assoc, e]
  · simp only [Over.comp_left, Category.assoc, Over.w]

theorem comb_over {n : ℕ} {f : Fin n → (A.t.G ⟶ B.t.G)} {f' : Fin n → (A'.t.G ⟶ B'.t.G)}
    (h : ∀ i, (f' i).left ≫ mB.φ = mA.φ ≫ (f i).left) (x : Fin n → 𝓞 E) :
    (∏ i, (A'.t.act.act (x i) ≫ f' i)).left ≫ mB.φ = mA.φ ≫ (∏ i, (A.t.act.act (x i) ≫ f i)).left := by
  refine prod_over mA.cart.1.w mB.cart _ fun i => ?_
  rw [Over.comp_left, Over.comp_left, Category.assoc, h, ← Category.assoc, mA.act, Category.assoc]

theorem rel_descend (hj : Function.Injective j) {n : ℕ} {f : Fin n → (A.t.G ⟶ B.t.G)}
    {f' : Fin n → (A'.t.G ⟶ B'.t.G)} (h : ∀ i, (f' i).left ≫ mB.φ = mA.φ ≫ (f i).left) (x : Fin n → 𝓞 E)
    (hx : ∏ i, (A'.t.act.act (x i) ≫ f' i) = 1) : ∏ i, (A.t.act.act (x i) ≫ f i) = 1 := by
  have : IsSchemeTheoreticallyDominant (spMap j) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom j) hj
  have : QuasiCompact (spMap j) := inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom j)))
  have := A.ab.smooth
  have : Flat A.t.G.hom := inferInstance
  have : IsSeparated B.t.G.hom := B.t.semi.separated
  refine ExtUnique.over_hom_ext_of_isPullback mA.cart.1 ?_
  rw [← comb_over mA mB h x, hx]
  exact one_over mA.cart.1.w mB.cart

theorem exists_pow_eq {n : ℕ} {f : A.t.G ⟶ B.t.G} {φ : Fin n → (A.t.G ⟶ B.t.G)}
    (hf : Serre.IsLinearHom A.t.act B.t.act f) (hφ : ∀ a, Serre.IsLinearHom A.t.act B.t.act (φ a)) {x₀ : 𝓞 E}
    (h₀ : x₀ ≠ 0) {x : Fin n → 𝓞 E} (h : (A.t.act.act x₀ ≫ f) * ∏ a, (A.t.act.act (x a) ≫ φ a) = 1) :
    ∃ N : ℕ, 0 < N ∧ ∃ y : Fin n → 𝓞 E, f ^ N = ∏ a, (A.t.act.act (y a) ≫ φ a) := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {x₀}))
  have hN : Ideal.absNorm (Ideal.span {x₀}) ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  refine ⟨_, Nat.pos_of_ne_zero hN, fun a => -(z * x a), ?_⟩
  let F : Serre.Pts B.t.act A.t.G := Serre.Pts.mk _ f
  let Φ : Fin n → Serre.Pts B.t.act A.t.G := fun a => Serre.Pts.mk _ (φ a)
  have h1 : x₀ • F + ∑ a, x a • Φ a = 0 := by
    apply Serre.Pts.ext
    rw [Serre.Pts.hom_add, Serre.Pts.hom_sum, Serre.Pts.hom_zero, ← h, hf.comm]
    simp only [Serre.Pts.hom_smul, (hφ _).comm, F, Φ, Serre.Pts.hom_mk]
  have h2 : Ideal.absNorm (Ideal.span {x₀}) • F = ∑ a, (-(z * x a)) • Φ a := by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hz, mul_smul, eq_neg_of_add_eq_zero_left h1, smul_neg, Finset.smul_sum,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [neg_smul, mul_smul]
  have h3 := congrArg Serre.Pts.hom h2
  rw [Serre.Pts.hom_sum] at h3
  simp only [Serre.Pts.hom_smul, ← (hφ _).comm, Φ, Serre.Pts.hom_mk] at h3
  exact h3

end Rel

section Diff

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {A B : PAT H (Sp (𝓞 K))} {FA : GenFib A.pol} {FB : GenFib B.pol}


open IntCoord in
theorem smul_diff_eq {p : ℕ} {φ : Fin p → (A.t.G ⟶ B.t.G)}
    {MP : Fin p → ((Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))} (hMP : ∀ a, FA.IsDiffOf FB (φ a) (MP a))
    {f : A.t.G ⟶ B.t.G} {M : (Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)} (hM : FA.IsDiffOf FB f M) {n : ℕ}
    {x : Fin p → 𝓞 E} (hfn : f ^ n = ∏ a, (A.t.act.act (x a) ≫ φ a)) {τ : 𝓞 E →+* 𝓞 K} {e : Fin FA.P₀.g → K}
    (he : e ∈ FA.eigLat A.t.act τ) : n • M e = ∑ a, ((τ (x a) : 𝓞 K) : K) • MP a e := by
  obtain ⟨u, hu, heig⟩ := ((integral_tangent_coordinates K _ FA).2.2.2.2.2 _ _ τ e).1 he
  have hd := hM u e hu
  have hs : ∀ a, FB.IsCoord (u ≫ (A.t.act.act (x a) ≫ φ a)) (MP a (τ (x a) • e)) := by
    intro a
    rw [← Category.assoc]
    exact hMP a _ _ (isCoord_smul FA hu (heig (x a)))
  have hprod : ∀ s : Finset (Fin p), FB.IsCoord (u ≫ ∏ a ∈ s, (A.t.act.act (x a) ≫ φ a))
      (∑ a ∈ s, MP a (τ (x a) • e)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, comp_one]
      exact isCoord_one FB
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, comp_mul]
      exact isCoord_mul FB (hs a) ih
  have hpow : ∀ m : ℕ, FB.IsCoord ((u ≫ f) ^ m) (m • M e) := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero, zero_smul]
      exact isCoord_one FB
    | succ m ih =>
      rw [pow_succ, succ_nsmul]
      exact isCoord_mul FB ih hd
  have h1 := hpow n
  rw [← comp_pow, hfn] at h1
  rw [((integral_tangent_coordinates K _ FB).1 _ h1.1).unique h1 (hprod Finset.univ)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← algebraMap_smul K (τ (x a)) e, map_smul]

end Diff

theorem exists_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
    {ρ : 𝓞 K} {A B : PAT H (Sp (𝓞 K))} {p q : ℕ} (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) (hA : HasType H A.t.act ρ 1 0)
    (hB : HasType H B.t.act ρ p q) {n : ℕ} (hn : p + q < n) {ψ : Fin n → (A.t.G ⟶ B.t.G)}
    (hψ : ∀ i, Serre.IsLinearHom A.t.act B.t.act (ψ i)) :
    ∃ x : Fin n → 𝓞 E, x ≠ 0 ∧ ∏ i, (A.t.act.act (x i) ≫ ψ i) = 1 := by
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  let β : 𝓞 K →+* ℂ := σ.comp (algebraMap (𝓞 K) K)
  have hβ : Function.Injective β := σ.injective.comp (IsFractionRing.injective (𝓞 K) K)
  obtain ⟨A', mA, -⟩ := PAT.exists_pullback E H _ _ (spMap β) A
  obtain ⟨B', mB, -⟩ := PAT.exists_pullback E H _ _ (spMap β) B
  choose ψ' hψ' e using fun i => exists_linear_over mA mB (hψ i)
  obtain ⟨x, hx, h⟩ := GlobalTheory.T.exists_integer_relation_linear_homs_cm_signature_type E H (β ρ) A' B' p q (by rw [← map_pow, hρ, map_neg, map_natCast])
    ((hasType_baseChange E H _ _ β _ _ mA ρ 1 0).1 hβ hA) ((hasType_baseChange E H _ _ β _ _ mB ρ p q).1 hβ hB)
    n hn ψ' hψ'
  exact ⟨x, hx, rel_descend mA mB hβ e x h⟩

theorem eigLat_le_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0), ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          FB.eigLat X.B.t.act τ ≤ Submodule.span (𝓞 K)
            {w | ∃ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∃ e ∈ FP.eigLat (X.A true).t.act τ, w = ∑ a, τE (c a) • MP a e} := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X FP FB MP hMP τ _ τE hτE w hw
  obtain ⟨K', _, _, j, ω, C, A', B', mA, mB, DA, DB, hA, hB, rA, -, ⟨tA⟩, ⟨tB⟩⟩ :=
    GlobalTheory.T.exists_finiteExtension_principalTriples_tensorLattice E H K ρ (X.A true) X.B 1 p X.ρ_sq X.typeP X.typeB
  obtain ⟨n, f', g', hf', hg', hfg⟩ := GlobalTheory.T.cmTensor_retract_of_cmDatum_rank_one E H _ ω C A' B' DA DB hA hB rA tA tB
  have hj : Function.Injective (RingOfIntegers.mapRingHom j) := fun a b h => by
    apply RingOfIntegers.ext
    apply j.injective
    exact congrArg (fun x : 𝓞 K' => (x : K')) h
  have hφ : ∀ a, Serre.IsLinearHom (X.A true).t.act X.B.t.act (phiP X a) := fun a => X.lin (Sum.inl a)
  choose φ' hφ' eφ using fun a => exists_linear_over mA mB (hφ a)
  have key : ∀ i, ∃ f : (X.A true).t.G ⟶ X.B.t.G, Serre.IsLinearHom (X.A true).t.act X.B.t.act f ∧
      (f' i).left ≫ mB.φ = mA.φ ≫ f.left ∧ ∃ N : ℕ, 0 < N ∧ ∃ y : Fin p → 𝓞 E,
        f ^ N = ∏ a, ((X.A true).t.act.act (y a) ≫ phiP X a) := fun i => by
    obtain ⟨x, hx, h⟩ := exists_rel (ρ := RingOfIntegers.mapRingHom j ρ) (A := A') (B := B') (p := p) (q := 0)
      (by rw [← map_pow, X.ρ_sq, map_neg, map_natCast])
      ((hasType_baseChange E H _ _ _ _ _ mA ρ 1 0).1 hj X.typeP)
      ((hasType_baseChange E H _ _ _ _ _ mB ρ p 0).1 hj X.typeB) (Nat.lt_succ_self p)
      (ψ := Fin.cons (f' i) φ') (Fin.cases (hf' i) hφ')
    rw [Fin.prod_univ_succ] at h
    simp only [Fin.cons_zero, Fin.cons_succ] at h
    have h₀ : x 0 ≠ 0 := fun h₀ => by
      haveI := (hf' i).isMonHom
      rw [h₀, Serre.act_zero, MonObj.one_comp, _root_.one_mul] at h
      have hs := GlobalTheory.T.cmObjHomOfType_linearIndependent E H K ρ σ₁ p 0 X _ (rel_descend mA mB hj eφ _ h)
      exact hx (funext (Fin.cases h₀ fun a => congrFun hs a))
    obtain ⟨N, hN, y, hy⟩ := exists_pow_eq (hf' i) hφ' h₀ h
    obtain ⟨f, hf, e₁, e₂⟩ := GlobalTheory.T.eq_pow_of_baseChange_eq_pow_principalAbelianCMTriple E H K K' j (X.A true) X.B A' B' mA mB _ (f' i) N hN (isLinearHom_prod X y) (hf' i)
      (by rw [hy]; exact comb_over mA mB eφ y)
    exact ⟨f, hf, e₂, N, hN, y, e₁⟩
  choose f hf ef N hN y hy using key
  choose M hM using fun i =>
    (DiffCoord.existsUnique_isDiffOf K _ FP _ FB (f i) (hf i).isMonHom).1.exists
  refine GlobalTheory.T.mem_of_mem_span_ringOfIntegers_map_numberField K K' j _ _ w (Submodule.span_mono (Set.image_mono ?_)
    (GlobalTheory.T.eigenLattice_image_le_span_after_baseChange E H K K' j (X.A true) X.B A' B' mA mB n f f' g' hf hf' hg' ef hfg FP FB M hM τ w hw))
  rintro _ ⟨i, e, he, rfl⟩
  have hE : (N i : E) ≠ 0 := Nat.cast_ne_zero.2 (hN i).ne'
  have hK : (N i : K) ≠ 0 := Nat.cast_ne_zero.2 (hN i).ne'
  refine Submodule.subset_span ⟨fun a => (y i a : E) / N i,
    Submodule.subset_span ⟨N i, hN i, y i, fun a => by field_simp, f i, hf i, hy i⟩, e, he, ?_⟩
  refine smul_right_injective _ hK ?_
  show (N i : K) • M i e = (N i : K) • _
  rw [Nat.cast_smul_eq_nsmul, smul_diff_eq hMP (hM i) (hy i) he, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, map_div₀, hτE, map_natCast, mul_div_cancel₀ _ hK]

end GlobalTheory.FlatCM.HomLat.LieSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieEigenLatticeLeSpanCmHomImagesStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieEigenLattice_le_span_cmHom_images : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0), ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          FB.eigLat X.B.t.act τ ≤ Submodule.span (𝓞 K)
            {w | ∃ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∃ e ∈ FP.eigLat (X.A true).t.act τ, w = ∑ a, τE (c a) • MP a e} := by
  first | exact @GlobalTheory.FlatCM.HomLat.LieSpan.eigLat_le_span | exact GlobalTheory.FlatCM.HomLat.LieSpan.eigLat_le_span | (intros; apply GlobalTheory.FlatCM.HomLat.LieSpan.eigLat_le_span <;> assumption)
end
