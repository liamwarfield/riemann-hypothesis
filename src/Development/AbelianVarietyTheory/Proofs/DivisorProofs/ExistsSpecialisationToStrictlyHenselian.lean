module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeFiniteProjectiveReflexive
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialisationToStrictlyHenselian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialisationToStrictlyHenselian
open IsLocalRing Polynomial

namespace GlobalTheory.Specialise

theorem sepEtale (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (Q : Ideal R) [Q.IsPrime] (L : Type) [Field L] [Algebra R L] [Algebra Q.ResidueField L]
    [IsScalarTower R Q.ResidueField L] (f : A →ₐ[R] L) (a : A) :
    IsSeparable Q.ResidueField (f a) := by
  let P : Ideal A := RingHom.ker f
  haveI : P.IsPrime := RingHom.ker_isPrime f
  have hPQ : Q = P.comap (algebraMap R A) := by
    ext r
    simp only [P, Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply R Q.ResidueField L]
    simp
  haveI : P.LiesOver Q := ⟨hPQ⟩
  letI := Localization.AtPrime.algebraOfLiesOver Q P
  have hsep : Algebra.IsSeparable Q.ResidueField P.ResidueField := inferInstance
  let g : P.ResidueField →ₐ[R] L := Ideal.ResidueField.liftₐ P f le_rfl (fun x hx => by
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    exact isUnit_iff_ne_zero.mpr (fun h => hx h))
  have hg : ∀ x : A, g (algebraMap A P.ResidueField x) = f x := fun x =>
    Ideal.ResidueField.liftₐ_algebraMap _ _ _ _ x
  let g' : P.ResidueField →ₐ[Q.ResidueField] L :=
    { g.toRingHom with
      commutes' := by
        have : g.toRingHom.comp (algebraMap Q.ResidueField P.ResidueField) =
            algebraMap Q.ResidueField L := by
          apply Ideal.ResidueField.ringHom_ext
          ext r
          simp only [RingHom.comp_apply]
          rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
            IsScalarTower.algebraMap_apply R A P.ResidueField]
          exact (hg _).trans (f.commutes r)
        intro c
        exact DFunLike.congr_fun this c }
  have h1 : g' (algebraMap A P.ResidueField a) = f a := hg a
  rw [← h1, isSeparable_map_iff g' g'.toRingHom.injective]
  exact Algebra.IsSeparable.isSeparable _ _

theorem specialisation_exists : ∀ (R S O : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing O]
    [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)] [Algebra R S] [Algebra R O]
    (Q y : Ideal R) [Q.IsPrime] [y.IsPrime], Q ≤ y →
    (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = y →
    (IsLocalRing.maximalIdeal O).comap (algebraMap R O) = Q →
    Module.Flat R S → GlobalTheory.LocAcyc.LocPiecesEtale R S → Nonempty (S →ₐ[R] O) := by
  intro R S O _ _ _ _ _ _ _ _ Q y _ _ hQy hy hQ _ hpieces
  haveI : Algebra.HasGoingDown R S := Algebra.HasGoingDown.of_flat
  haveI : (maximalIdeal S).LiesOver y := ⟨hy.symm⟩
  obtain ⟨Q₂, -, hQ₂p, hQ₂o⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := Q) (q := y) (maximalIdeal S) hQy
  haveI := hQ₂p
  letI : Algebra Q.ResidueField Q₂.ResidueField :=
    (Ideal.ResidueField.map Q Q₂ (algebraMap R S) hQ₂o.over).toAlgebra
  haveI : IsScalarTower R Q.ResidueField Q₂.ResidueField := .of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap,
      ← IsScalarTower.algebraMap_apply]

  have hsepS : ∀ s : S, IsSeparable Q.ResidueField (algebraMap S Q₂.ResidueField s) := by
    intro s
    obtain ⟨ι, _, _, _, Si, -, hcov, hloc⟩ := hpieces
    obtain ⟨i, hi⟩ := hcov s
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hloc i
    let F : Localization.AtPrime q →ₐ[R] Q₂.ResidueField :=
      (IsScalarTower.toAlgHom R S Q₂.ResidueField).comp ((Si i).val.comp (e : _ →ₐ[R] _))
    let f : A →ₐ[R] Q₂.ResidueField :=
      F.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q))
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective q.primeCompl (e.symm ⟨s, hi⟩)
    have hs : algebraMap S Q₂.ResidueField s = F (IsLocalization.mk' _ a t) := by
      simp only [F, AlgHom.comp_apply, hat]
      simp
    have hft : f t ≠ 0 := by
      have : IsUnit (f t) :=
        (IsLocalization.map_units (Localization.AtPrime q) t).map F
      exact this.ne_zero
    have hmul : F (IsLocalization.mk' _ a t) * f t = f a := by
      simp only [f, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← map_mul,
        IsLocalization.mk'_spec]
    have hx : algebraMap S Q₂.ResidueField s = f a * (f t)⁻¹ := by
      rw [hs, eq_mul_inv_iff_mul_eq₀ hft, hmul]
    rw [hx, ← mem_separableClosure_iff]
    refine mul_mem ?_ (inv_mem ?_) <;> rw [mem_separableClosure_iff] <;>
      exact sepEtale R A Q _ f _
  haveI : Algebra.IsSeparable Q.ResidueField Q₂.ResidueField := ⟨fun x => by
    obtain ⟨u, v, -, rfl⟩ := IsFractionRing.div_surjective (A := S ⧸ Q₂) x
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [Ideal.algebraMap_quotient_residueField_mk, Ideal.algebraMap_quotient_residueField_mk,
      ← mem_separableClosure_iff]
    exact div_mem ((mem_separableClosure_iff).2 (hsepS u)) ((mem_separableClosure_iff).2 (hsepS v))⟩

  have hker : ∀ r : R, algebraMap R (ResidueField O) r = 0 ↔ r ∈ Q := by
    intro r
    rw [IsScalarTower.algebraMap_apply R O (ResidueField O), ResidueField.algebraMap_eq,
      residue_eq_zero_iff, ← hQ, Ideal.mem_comap]
  letI : Algebra Q.ResidueField (ResidueField O) :=
    (Ideal.ResidueField.lift Q (algebraMap R (ResidueField O)) (fun r hr => (hker r).2 hr)
      (fun r hr => by
        simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
        exact isUnit_iff_ne_zero.mpr (fun h => hr ((hker r).1 h)))).toAlgebra
  haveI : IsScalarTower R Q.ResidueField (ResidueField O) := .of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra]
    exact (Ideal.ResidueField.lift_algebraMap Q _ _ _ r).symm
  let φ₀ : Q₂.ResidueField →ₐ[Q.ResidueField] ResidueField O := IsSepClosed.lift
  let ψ : S →ₐ[R] ResidueField O :=
    (φ₀.restrictScalars R).comp (IsScalarTower.toAlgHom R S Q₂.ResidueField)
  obtain ⟨φ, -⟩ := (GlobalTheory.IndEtaleHensel.bijective_residue_comp R S O hpieces).2 ψ
  exact ⟨φ⟩

end GlobalTheory.Specialise
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialisationToStrictlyHenselianStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_specialisation_to_strictlyHenselian : ∀ (R S O : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing O]
    [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)] [Algebra R S] [Algebra R O]
    (Q y : Ideal R) [Q.IsPrime] [y.IsPrime], Q ≤ y →
    (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = y →
    (IsLocalRing.maximalIdeal O).comap (algebraMap R O) = Q →
    Module.Flat R S → GlobalTheory.LocAcyc.LocPiecesEtale R S → Nonempty (S →ₐ[R] O) := by
  first | exact @GlobalTheory.Specialise.specialisation_exists | exact GlobalTheory.Specialise.specialisation_exists | (intros; apply GlobalTheory.Specialise.specialisation_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurAndTensorSubmodule
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.IrrTensor

section General
variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (A : ι → Module.End ℂ V)

theorem density [Nontrivial V]
    (hirr : ∀ N : Submodule ℂ V, (∀ Z, ∀ y ∈ N, A Z y ∈ N) → N = ⊥ ∨ N = ⊤)
    (hsch : ∀ T : V →ₗ[ℂ] V, (∀ Z, T ∘ₗ A Z = A Z ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id)
    (f : Module.End ℂ V) (s : Finset V) :
    ∃ r ∈ Algebra.adjoin ℂ (Set.range A), ∀ m ∈ s, f m = r m := by
  let R := Algebra.adjoin ℂ (Set.range A)
  have hA : ∀ Z, A Z ∈ R := fun Z => Algebra.subset_adjoin ⟨Z, rfl⟩
  haveI : IsSimpleModule R V := by
    refine (isSimpleModule_iff R V).2 ?_
    refine { toNontrivial := (Submodule.nontrivial_iff R).2 inferInstance, eq_bot_or_eq_top := fun N => ?_ }
    rcases hirr (N.restrictScalars ℂ) (fun Z y hy => N.smul_mem (⟨A Z, hA Z⟩ : R) hy) with h | h
    · left
      exact (Submodule.restrictScalars_eq_bot_iff ℂ R V).1 h
    · right
      exact (Submodule.restrictScalars_eq_top_iff ℂ R V).1 h
  let F : Module.End (Module.End R V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun g x => by
        obtain ⟨c, hc⟩ := hsch (g.restrictScalars ℂ) (fun Z => LinearMap.ext fun y =>
          g.map_smul (⟨A Z, hA Z⟩ : R) y)
        have hg : ∀ y, g y = c • y := fun y => LinearMap.congr_fun hc y
        show f (g x) = g (f x)
        rw [hg, hg, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density (R := R) F s
  exact ⟨r.1, r.2, fun m hm => hr m hm⟩

variable {W : Type} [AddCommGroup W] [Module ℂ W]

end General

variable {p q : ℕ}

theorem mem_wtSub {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    {μ : Ix p q → ℚ} {v : V} : v ∈ wtSub act μ ↔ ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  simp [wtSub, Submodule.mem_iInf, sub_eq_zero]

theorem root_shift {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    (hl : IsLieAct act) {μ : Ix p q → ℚ} {v : V} (hv : v ∈ wtSub act μ) (a b : Ix p q) :
    act (Eab a b) v ∈ wtSub act (fun c => μ c + ((if c = a then 1 else 0) - (if c = b then 1 else 0))) := by
  rw [mem_wtSub] at hv ⊢
  intro c
  have h := LinearMap.congr_fun (hl (Eab c c) (Eab a b)) v
  have e : (Eab c c * Eab a b - Eab a b * Eab c c : Mat p q) =
      (((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℚ) : ℂ) • Eab a b := by
    unfold Eab
    have e1 : (Matrix.single c c 1 * Matrix.single a b 1 : Mat p q) =
        (if c = a then (1 : ℂ) else 0) • Matrix.single a b 1 := by
      split_ifs with h
      · subst h; simp
      · simp [Matrix.single_mul_single_of_ne, h]
    have e2 : (Matrix.single a b 1 * Matrix.single c c 1 : Mat p q) =
        (if c = b then (1 : ℂ) else 0) • Matrix.single a b 1 := by
      split_ifs with h
      · subst h; simp
      · simp [Matrix.single_mul_single_of_ne, Ne.symm h]
    rw [e1, e2, ← sub_smul]
    congr 1
    split_ifs <;> simp
  rw [e, map_smul, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, hv c, map_smul, eq_sub_iff_add_eq] at h
  rw [← h, Rat.cast_add, add_smul, add_comm]

theorem exists_highest (M : GKMod p q) [Nontrivial M.V] : ∃ μ v, IsHW M.act μ v := by
  obtain ⟨μ₀, v₀, hv₀, hv₀'⟩ : ∃ μ v, v ∈ wtSub M.act μ ∧ v ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨x, hx⟩ := exists_ne (0 : M.V)
    have : (⨆ μ : Ix p q → ℚ, wtSub M.act μ) = ⊥ :=
      iSup_eq_bot.2 fun μ => (Submodule.eq_bot_iff _).2 (h μ)
    have h2 := M.wts x
    rw [this] at h2
    exact hx h2
  obtain ⟨U, hfd, hU, hK⟩ := M.kfin v₀
  let k : Ix p q → ℚ := Sum.elim (fun i => -((i : ℕ) : ℚ)) (fun i => -((i : ℕ) : ℚ))
  let h : (Ix p q → ℚ) → ℚ := fun μ => ∑ a, k a * μ a
  let H : Mat p q := ∑ a, ((k a : ℚ) : ℂ) • Eab a a
  have hKE : ∀ a b : Ix p q, sameBlock a b → IsKC (Eab a b) := by
    intro a b hab c d hcd
    unfold Eab
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hcd hab
  have hH : ∀ x ∈ U, M.act H x ∈ U := by
    intro x hx
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [H, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    exact U.sum_mem fun a _ => U.smul_mem _ (hK _ (hKE a a (by cases a <;> trivial)) x hx)
  let S : Set (Ix p q → ℚ) := {μ | ∃ v ∈ U, v ∈ wtSub M.act μ ∧ v ≠ 0}
  have hfin : (h '' S).Finite := by
    have h1 := Module.End.finite_hasEigenvalue ((M.act H).restrict hH)
    refine (h1.preimage (f := fun x : ℚ => (x : ℂ)) Rat.cast_injective.injOn).subset ?_
    rintro _ ⟨μ, ⟨v, hvU, hv, hv0⟩, rfl⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvU⟩) ⟨?_, fun e => hv0 (congrArg Subtype.val e)⟩
    rw [Module.End.mem_eigenspace_iff]
    apply Subtype.ext
    show M.act H v = ((h μ : ℚ) : ℂ) • v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [H, h, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      mem_wtSub.1 hv, smul_smul, ← Finset.sum_smul]
    push_cast
    rfl
  obtain ⟨_, ⟨μ, ⟨v, hvU, hv, hv0⟩, rfl⟩, hmax⟩ :=
    Set.exists_max_image (h '' S) id hfin ⟨_, μ₀, ⟨v₀, hU, hv₀, hv₀'⟩, rfl⟩
  refine ⟨μ, v, hv0, hv, ?_⟩
  simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]
  intro a b hab
  by_contra hne
  have hs : sameBlock a b := by cases a <;> cases b <;> first | trivial | exact hab
  have hlt : k b < k a := by
    cases a <;> cases b <;> first | exact hab.elim | skip
    all_goals
      simp only [k, Sum.elim_inl, Sum.elim_inr, neg_lt_neg_iff, Nat.cast_lt]
      exact hab
  have := hmax _ ⟨_, ⟨_, hK _ (hKE a b hs) v hvU, root_shift M.lie hv a b, hne⟩, rfl⟩
  simp only [id, h, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  linarith

theorem schur (M : GKMod p q) (hI : IrrGK M) (hA : AdmGK M) (T : M.V →ₗ[ℂ] M.V)
    (hT : ∀ Z, T ∘ₗ M.act Z = M.act Z ∘ₗ T) : ∃ c : ℂ, T = c • LinearMap.id := by
  haveI := hI.1
  obtain ⟨μ, v, hv0, hv⟩ := exists_highest M
  have hf : ∀ Z x, T (M.act Z x) = M.act Z (T x) := fun Z x => LinearMap.congr_fun (hT Z) x
  have hst : ∀ x ∈ hwSub M.act μ, T x ∈ hwSub M.act μ := by
    intro x hx
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
    refine ⟨fun c => ?_, fun c d h => ?_⟩
    · rw [← hf, ← map_smul, ← map_sub, hx.1 c, map_zero]
    · rw [← hf, hx.2 c d h, map_zero]
  haveI := hA μ
  haveI : Nontrivial (hwSub M.act μ) := ⟨⟨⟨v, hv⟩, 0, fun e => hv0 (congrArg Subtype.val e)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T.restrict hst)
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  have hx1 : T x = c • (x : M.V) := congrArg Subtype.val hx.apply_eq_smul
  refine ⟨c, ?_⟩
  rcases hI.2 (LinearMap.ker (T - c • LinearMap.id)) (fun Z y hy => by
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at hy ⊢
    rw [hf, hy, map_smul]) with h | h
  · exact absurd (Subtype.ext ((Submodule.eq_bot_iff _).1 h x (by simp [hx1]))) hx.2
  · exact sub_eq_zero.1 (LinearMap.ker_eq_top.1 h)

end GlobalTheory.IrrTensor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnOfPsiOn
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Semi CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiUnitOfPsiOn

theorem injective_of_isIso {A B : CommRingCat} (f : A ⟶ B) [IsIso f] : Function.Injective f.hom := by
  intro a b e
  have := congrArg (inv f).hom e
  rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply,
    CommRingCat.id_apply] at this

theorem mem_wchart1 {Y B : Scheme.{0}} (M : LB B) (φ : Y ⟶ B) (z : Y) (i : M.ι) (hz : φ z ∈ M.U i) :
    z ∈ LB.wchart M (fun _ : PUnit => φ) (fun _ => i) := Set.mem_iInter.2 fun _ => hz

theorem psiUnitOn_of_psiOn : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Spec (CommRingCat.of R)).Opens), PsiOn D W → ∀ y : D.X, PsiUnitOn D y (W : Set (Spec (CommRingCat.of R))) := by
  intro R _ _ D W ψ y j V _ hVW hj h
  obtain ⟨p, rfl⟩ : ∃ p, j = fun _ => p := ⟨j PUnit.unit, funext fun _ => rfl⟩
  have hle : W.ι ⁻¹ᵁ V ≤ LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c y).left) (fun _ => p) :=
    fun z hz => mem_wchart1 _ _ _ _ (hj hz)
  have hVr : V ≤ W.ι.opensRange := by rw [Scheme.Opens.opensRange_ι]; exact hVW
  haveI := W.ι.isIso_app V hVr
  set u : Γ(W.toScheme, W.ι ⁻¹ᵁ V)ˣ := res hle ((ψ.psi y).s (fun _ => p)) with hu
  set r : Γ(Spec (CommRingCat.of R), V) := (inv (W.ι.app V)).hom u.val with hr
  have hr' : (W.ι.app V).hom r = u.val := by
    rw [hr, ← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
  refine ⟨r, u.isUnit.map (inv (W.ι.app V)).hom, ?_⟩
  have hKr : jK R ⁻¹ᵁ V ≤ (jK R ⁻¹ᵁ W).ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]; exact fun z hz => hVW hz
  haveI := (jK R ⁻¹ᵁ W).ι.isIso_app (jK R ⁻¹ᵁ V) hKr
  apply injective_of_isIso ((jK R ⁻¹ᵁ W).ι.app (jK R ⁻¹ᵁ V))
  refine fn_ext ?_
  intro z hz
  have hι : (jK R ∣_ W) ≫ W.ι = (jK R ⁻¹ᵁ W).ι ≫ jK R := morphismRestrict_ι _ _
  have hzV : jK R ((jK R ⁻¹ᵁ W).ι z) ∈ V := hz
  have hpt : W.ι ((jK R ∣_ W) z) = jK R ((jK R ⁻¹ᵁ W).ι z) := congrArg (fun q => q z) hι
  have hm : (jK R ∣_ W) z ∈ W.ι ⁻¹ᵁ V := by
    show W.ι ((jK R ∣_ W) z) ∈ V
    rw [hpt]; exact hzV
  have h₁ : (𝟙 _ : (jK R ⁻¹ᵁ W).toScheme ⟶ _) z ∈
      LB.wchart D.P.L (fun _ : PUnit => (jK R ∣_ W) ≫ (toUnit (TW W) ≫ D.c y).left) (fun _ => p) :=
    mem_wchart1 _ _ _ _ (hj hm)
  have h₂ : (𝟙 _ : (jK R ⁻¹ᵁ W).toScheme ⟶ _) z ∈
      LB.wchart D.P.L (fun _ : PUnit => (jK R ⁻¹ᵁ W).ι ≫ D.xK y) (fun _ => p) :=
    mem_wchart1 _ _ _ _ (hj hzV)
  have e₃ := (gm_pullGen D.P.L _ _ (ψ.psi y) (jK R ∣_ W) (𝟙 _) z (fun _ => p) h₁).symm.trans
    ((gm_corr D.P.L (ψ.psi_eq y) (𝟙 _) z p h₁ h₂).trans
      (gm_pullGen D.P.L _ _ (D.psi y) (jK R ⁻¹ᵁ W).ι (𝟙 _) z (fun _ => p) h₂))
  rw [Category.id_comp, Category.id_comp] at e₃
  have l₁ := gs_pull (𝟙 _) (jK R ⁻¹ᵁ W).ι z (jK R ⁻¹ᵁ V) hz ((jK R).app V |>.hom r)
  have l₂ := gs_pull (𝟙 _) (jK R ⁻¹ᵁ W).ι z (jK R ⁻¹ᵁ V) hz
    (((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi y).s (fun _ => p)).val)
  rw [Category.id_comp] at l₁ l₂
  rw [l₁, l₂, gs_pull _ _ z V hzV r, ← hι, ← gs_pull _ _ z V hm r, hr', hu,
    gs_unit _ z _ hm]
  erw [gm_res _ z hle hm]
  erw [gs_res _ z h hz]
  rw [gs_unit _ z _ (h hz)]
  exact congrArg Units.val e₃


end GlobalTheory.PsiUnitOfPsiOn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegWBlattnerLeOfBlattnerCone
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegWBlattnerLeOfBlattnerCone
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FlowLemma

open MvPolynomial in
private lemma shiftNu_add_right {p q : ℕ} (c : ℚ) (f g : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ) (a : _root_.Formalism.BasicNotions.TH.Ix p q) :
    _root_.Formalism.BasicNotions.TH.shiftNu c (fun x => f x + g x) a = _root_.Formalism.BasicNotions.TH.shiftNu c f a + g a := by
  cases a <;> simp only [_root_.Formalism.BasicNotions.TH.shiftNu] <;> ring

open MvPolynomial in
private lemma degW_blattner_le_of_sign_lemma {p q : ℕ} (M : _root_.Formalism.BasicNotions.TH.GKMod p q) (lam : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ)
    (c : ℚ) (hC : _root_.GlobalTheory.FockAlg.ConeTypes M lam) (s : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ)
    (hs : ∀ a, s a = 1 ∨ s a = -1)
    (hsν : ∀ a, s a * _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a = |_root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a|)
    (hmono : ∀ a b, lam b < lam a → s b ≤ s a)
    (μ : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ) (v : M.V) (hv : _root_.Formalism.BasicNotions.TH.IsHW M.act μ v) :
    _root_.Formalism.BasicNotions.TH.degW c (_root_.Formalism.BasicNotions.TH.blattner lam) ≤ _root_.Formalism.BasicNotions.TH.degW c μ := by
  obtain ⟨m, hm, rfl⟩ := hC μ v hv
  set Δ : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ := fun x =>
    ∑ a, ∑ b, (m a b : ℚ) * ((if x = a then 1 else 0) - if x = b then 1 else 0) with hΔ
  have key : ∑ x, s x * Δ x = ∑ a, ∑ b, (m a b : ℚ) * (s a - s b) := by
    simp only [hΔ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hnn : 0 ≤ ∑ x, s x * Δ x := by
    rw [key]
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    by_cases h0 : m a b = 0
    · simp [h0]
    · exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 (hmono a b (hm a b h0)))
  have habs : ∀ x y : ℚ, ∀ a, s a * (x + y) ≤ |x + y| := by
    intro x y a
    rcases hs a with h | h <;> rw [h]
    · simpa using le_abs_self (x + y)
    · simpa using neg_le_abs (x + y)
  unfold _root_.Formalism.BasicNotions.TH.degW
  calc ∑ a, |_root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a|
      = ∑ a, s a * _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a := by simp [hsν]
    _ ≤ ∑ a, s a * _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a + ∑ x, s x * Δ x := le_add_of_nonneg_right hnn
    _ = ∑ a, s a * (_root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a + Δ a) := by
        rw [← Finset.sum_add_distrib]; simp [mul_add]
    _ ≤ ∑ a, |_root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a + Δ a| :=
        Finset.sum_le_sum fun a _ => habs _ _ a
    _ = ∑ a, |_root_.Formalism.BasicNotions.TH.shiftNu c (fun x => _root_.Formalism.BasicNotions.TH.blattner lam x + Δ x) a| := by
        simp [shiftNu_add_right]


open MvPolynomial in
theorem _root_.GlobalTheory.FlowLemma.degW_blattner_le (p q : ℕ) (M : _root_.Formalism.BasicNotions.TH.GKMod p q) (lam : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ)
    (c θ : ℚ)
    (hC : _root_.GlobalTheory.FockAlg.ConeTypes M lam)
    (hs : ∀ a, (θ < lam a → 0 ≤ _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a) ∧
      (lam a ≤ θ → _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a ≤ 0))
    (μ : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ) (v : M.V) (hv : _root_.Formalism.BasicNotions.TH.IsHW M.act μ v) :
    _root_.Formalism.BasicNotions.TH.degW c (_root_.Formalism.BasicNotions.TH.blattner lam) ≤ _root_.Formalism.BasicNotions.TH.degW c μ := by
  refine degW_blattner_le_of_sign_lemma M lam c hC (fun a => if θ < lam a then 1 else -1)
    (fun a => ?_) (fun a => ?_) (fun a b hab => ?_) μ v hv
  · split_ifs <;> simp
  · split_ifs with h
    · simp [abs_of_nonneg ((hs a).1 h)]
    · simp [abs_of_nonpos ((hs a).2 (not_lt.1 h))]
  · beta_reduce
    split_ifs with h1 h2 h2 <;> first | exact absurd (h1.trans hab) h2 | norm_num

end GlobalTheory.FlowLemma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegWBlattnerLeOfBlattnerConeStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degW_blattner_le_of_blattnerCone : ∀ (p q : ℕ) (M : GKMod p q) (lam : Ix p q → ℚ) (c θ : ℚ), ConeTypes M lam → (∀ a, (θ < lam a → 0 ≤ shiftNu c (blattner lam) a) ∧ (lam a ≤ θ → shiftNu c (blattner lam) a ≤ 0)) → ∀ μ v, IsHW M.act μ v → degW c (blattner lam) ≤ degW c μ := by
  first | exact @GlobalTheory.FlowLemma.degW_blattner_le | exact GlobalTheory.FlowLemma.degW_blattner_le | (intros; apply GlobalTheory.FlowLemma.degW_blattner_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirCentralAndOnHighestWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirCentralAndOnHighestWeight
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.CasimirHighest

theorem casimir_comm_gen {R I : Type*} [Ring R] [Fintype I] [DecidableEq I] (e : I → I → R)
    (he : ∀ i j k l, e i j * e k l - e k l * e i j =
      (if j = k then e i l else 0) - (if l = i then e k j else 0)) (k l : I) :
    (∑ a, ∑ b, e a b * e b a) * e k l = e k l * ∑ a, ∑ b, e a b * e b a := by
  rw [← sub_eq_zero]
  have h : ∀ a b, e a b * e b a * e k l - e k l * (e a b * e b a) =
      ((if a = k then e a b * e b l else 0) - (if l = b then e a b * e k a else 0)) +
      ((if b = k then e a l * e b a else 0) - (if l = a then e k b * e b a else 0)) := by
    intro a b
    have : e a b * e b a * e k l - e k l * (e a b * e b a) =
        e a b * (e b a * e k l - e k l * e b a) + (e a b * e k l - e k l * e a b) * e b a := by
      noncomm_ring
    rw [this, he, he]
    simp only [mul_sub, sub_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, h]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => if a = k then e a b * e b l else 0),
    Finset.sum_comm (f := fun a b => if l = a then e k b * e b a else 0)]
  simp

theorem casimir_on_highest_rat {V : Type*} [AddCommGroup V] [Module ℂ V] {m : ℕ}
    (e : Fin m → Fin m → Module.End ℂ V)
    (he : ∀ i j, e i j * e j i - e j i * e i j = e i i - e j j)
    (v : V) (κ : Fin m → ℚ) (hv : ∀ i j, i < j → e i j v = 0)
    (hκ : ∀ i, e i i v = (κ i : ℂ) • v) :
    ∑ i, ∑ j, e i j (e j i v) =
      ((∑ i, κ i ^ 2 + ∑ i : Fin m, κ i * ((m : ℚ) - 1 - 2 * (i : ℕ)) : ℚ) : ℂ) • v := by
  have key : ∀ i j, e i j (e j i v) =
      (((if i = j then κ i * κ i else 0) + (if i < j then κ i else 0) -
        (if i < j then κ j else 0) : ℚ) : ℂ) • v := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · have h1 := congrArg (fun f : Module.End ℂ V => f v) (he i j)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, hv i j h, map_zero, sub_zero,
        hκ] at h1
      rw [h1]
      simp [h, h.ne, sub_smul]
    · subst h
      simp [hκ, mul_smul]
    · simp [hv j i h, h.ne', not_lt.mpr h.le]
  have hz : ∑ i : Fin m, ∑ j : Fin m,
      ((if i = j then κ i * κ i else 0) + (if i < j then κ i else 0) -
        (if i < j then κ j else 0) : ℚ)
      = ∑ i, κ i ^ 2 + ∑ i : Fin m, κ i * ((m : ℚ) - 1 - 2 * (i : ℕ)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => if i < j then κ j else 0), ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have a1 : ∑ j : Fin m, (if i < j then κ i else 0) = ((m : ℚ) - 1 - (i : ℕ)) * κ i := by
      rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_lt_eq_Ioi, Fin.card_Ioi,
        nsmul_eq_mul]
      have := i.2
      congr 1
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      simp
    have a2 : ∑ j : Fin m, (if j < i then κ i else 0) = ((i : ℕ) : ℚ) * κ i := by
      rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_gt_eq_Iio, Fin.card_Iio,
        nsmul_eq_mul]
    rw [a1, a2]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  simp only [key]
  rw [← hz]
  simp only [Rat.cast_sum, Finset.sum_smul]

theorem act_Eab_comm {p q : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) (i j k l : Ix p q) :
    act (Eab i j) * act (Eab k l) - act (Eab k l) * act (Eab i j) =
      (if j = k then act (Eab i l) else 0) - (if l = i then act (Eab k j) else 0) := by
  have m : ∀ i j k l : Ix p q, Eab i j * Eab k l = if j = k then Eab i l else 0 := by
    intro i j k l
    split_ifs with hh
    · subst hh; simp [Eab, Matrix.single_mul_single_same]
    · simp [Eab, Matrix.single_mul_single_of_ne, hh]
  rw [← h, m, m, map_sub]
  split_ifs <;> simp

theorem casimir_central_and_highest : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → (∀ Z, casimir act * act Z = act Z * casimir act) ∧ ∀ (μ : Ix p q → ℚ) (v : V), v ∈ hwSub act μ → (∑ a, ∑ b, if sameBlock a b then act (Eab a b) (act (Eab b a) v) else 0) = ((∑ a, μ a ^ 2 + (∑ i : Fin p, μ (.inl i) * ((p : ℚ) - 1 - 2 * (i : ℕ))) + (∑ j : Fin q, μ (.inr j) * ((q : ℚ) - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • v := by
  intro p q V _ _ act h
  refine ⟨fun Z => ?_, fun μ v hv => ?_⟩
  · have hZ : Z = ∑ k, ∑ l, Z k l • Eab k l := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
      simp [Eab, Matrix.smul_single]
    have hc : ∀ k l, casimir act * act (Eab k l) = act (Eab k l) * casimir act := fun k l =>
      casimir_comm_gen (fun a b => act (Eab a b)) (act_Eab_comm h) k l
    rw [hZ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, hc]
  · simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv
    obtain ⟨hw, hr⟩ := hv
    have h1 := casimir_on_highest_rat (fun i j : Fin p => act (Eab (.inl i) (.inl j)))
      (fun i j => by simpa using act_Eab_comm h (.inl i) (.inl j) (.inl j) (.inl i)) v
      (fun i => μ (.inl i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
    have h2 := casimir_on_highest_rat (fun i j : Fin q => act (Eab (.inr i) (.inr j)))
      (fun i j => by simpa using act_Eab_comm h (.inr i) (.inr j) (.inr j) (.inr i)) v
      (fun i => μ (.inr i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
    have s1 : ∀ i j, sameBlock (p := p) (q := q) (.inl i) (.inl j) := fun _ _ => trivial
    have s2 : ∀ i j, sameBlock (p := p) (q := q) (.inr i) (.inr j) := fun _ _ => trivial
    have s3 : ∀ i j, ¬ sameBlock (p := p) (q := q) (.inl i) (.inr j) := fun _ _ => id
    have s4 : ∀ i j, ¬ sameBlock (p := p) (q := q) (.inr i) (.inl j) := fun _ _ => id
    simp only [Fintype.sum_sum_type, if_pos (s1 _ _), if_pos (s2 _ _), if_neg (s3 _ _),
      if_neg (s4 _ _), Finset.sum_const_zero, add_zero, zero_add]
    rw [h1, h2, ← add_smul, ← Rat.cast_add]
    congr 2
    ring

end GlobalTheory.CasimirHighest
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirCentralAndOnHighestWeightStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_central_and_on_highestWeight : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → (∀ Z, casimir act * act Z = act Z * casimir act) ∧ ∀ (μ : Ix p q → ℚ) (v : V), v ∈ hwSub act μ → (∑ a, ∑ b, if sameBlock a b then act (Eab a b) (act (Eab b a) v) else 0) = ((∑ a, μ a ^ 2 + (∑ i : Fin p, μ (.inl i) * ((p : ℚ) - 1 - 2 * (i : ℕ))) + (∑ j : Fin q, μ (.inr j) * ((q : ℚ) - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • v := by
  first | exact @GlobalTheory.CasimirHighest.casimir_central_and_highest | exact GlobalTheory.CasimirHighest.casimir_central_and_highest | (intros; apply GlobalTheory.CasimirHighest.casimir_central_and_highest <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeJetSplitDirectionAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaguerreDerivativePolynomialValueAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaguerreSignedBinomCoeffMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaguerreSignedBinomCoeffMul
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem rco_mul_rco : ∀ k n m j : ℕ, j ≤ m → m ≤ n →
    rco k n m * rco k m j = rco k n j * ((n - j).choose (m - j) : ℤ) := by
  intro k n m j hjm hmn
  have h1 : n.choose m * m.choose j = n.choose j * (n - j).choose (m - j) := by
    first
      | exact Nat.choose_mul hjm
      | exact Nat.choose_mul hmn hjm
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hjm
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have e1 : j + p + q - (j + p) = q := by omega
  have e2 : j + p - j = p := by omega
  have e3 : j + p + q - j = p + q := by omega
  have h2 : ∀ a p q : ℕ, a.ascFactorial p * (a + p).ascFactorial q = a.ascFactorial (p + q) := by
    intro a p q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [← add_assoc, Nat.ascFactorial_succ, Nat.ascFactorial_succ, ← ih, add_assoc a p q]
      ring
  have h3 := h2 (k + j) p q
  rw [e2, e3] at h1
  have h1' : ((j + p + q).choose (j + p) : ℤ) * ((j + p).choose j : ℤ)
      = ((j + p + q).choose j : ℤ) * ((p + q).choose p : ℤ) := by exact_mod_cast h1
  have h3' : ((k + j).ascFactorial p : ℤ) * ((k + (j + p)).ascFactorial q : ℤ)
      = ((k + j).ascFactorial (p + q) : ℤ) := by
    rw [← add_assoc]; exact_mod_cast h3
  unfold rco
  rw [e1, e2, e3, pow_add, ← h3']
  linear_combination ((-1 : ℤ) ^ p * (-1) ^ q * ((k + j).ascFactorial p : ℤ)
    * ((k + (j + p)).ascFactorial q : ℤ)) * h1'

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaguerreSignedBinomCoeffMulStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laguerreSignedBinomCoeff_mul : ∀ k n m j : ℕ, j ≤ m → m ≤ n → rco k n m * rco k m j = rco k n j * ((n - j).choose (m - j) : ℤ) := by
  first | exact @GlobalTheory.HilbFam.rco_mul_rco | exact GlobalTheory.HilbFam.rco_mul_rco | (intros; apply GlobalTheory.HilbFam.rco_mul_rco <;> assumption)
end
end

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem lag_add : ∀ (k n : ℕ) (c s y : ℂ), lag k n (c + s) y =
    ∑ m ∈ Finset.range (n + 1), (rco k n m : ℂ) * s ^ (n - m) * lag k m c y := by
  intro k n c s y
  have hR : ∑ m ∈ Finset.range (n + 1), (rco k n m : ℂ) * s ^ (n - m) * lag k m c y
      = ∑ j ∈ Finset.range (n + 1), ∑ m ∈ Finset.Ico j (n + 1),
        (rco k n m : ℂ) * s ^ (n - m) * ((rco k m j : ℂ) * c ^ (m - j) * y ^ j) := by
    simp only [lag, Finset.mul_sum, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_Ico_comm 0 (n + 1) (fun j m ↦
      (rco k n m : ℂ) * s ^ (n - m) * ((rco k m j : ℂ) * c ^ (m - j) * y ^ j))).symm
  rw [hR, lag]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Finset.sum_Ico_eq_sum_range, add_pow, show n + 1 - j = n - j + 1 by omega,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hp' : p ≤ n - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
  have h := GlobalTheory.T.laguerreSignedBinomCoeff_mul k n (j + p) j (by omega) (by omega)
  have e1 : j + p - j = p := by omega
  have e2 : n - (j + p) = n - j - p := by omega
  rw [e1] at h
  have h' : (rco k n (j + p) : ℂ) * (rco k (j + p) j : ℂ)
      = (rco k n j : ℂ) * ((n - j).choose p : ℂ) := by exact_mod_cast h
  rw [e1, e2]
  linear_combination (-(s ^ (n - j - p) * c ^ p * y ^ j)) * h'

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeJetSplitDirectionAdd
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma piFinset_range_succ_eq_Iic {ι : Type} [Fintype ι] [DecidableEq ι] (κ : ι → ℕ) :
    Fintype.piFinset (fun i => Finset.range (κ i + 1)) = Finset.Iic κ := by
  ext μ
  simp [Fintype.mem_piFinset, Finset.mem_range, Finset.mem_Iic, Pi.le_def, Nat.lt_succ_iff]


open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.jet_split_add : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ), Even k → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → _root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) κ τ (c + v) t = ∑ μ ∈ Finset.Iic κ, ((∏ i, _root_.GlobalTheory.HilbFam.rco k (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i)) * _root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) μ τ c t := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t v κ hk ha hτ
  have hμ := fun μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ =>
    ((_root_.GlobalTheory.HilbFam.hasSum_jet_split F k 𝔞 𝔟 a₀ a x τ c t μ hk ha hτ).mul_left
      (((∏ i, _root_.GlobalTheory.HilbFam.rco k (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i))))
  have hs := hasSum_sum (s := Finset.Iic κ) fun μ _ => hμ μ
  refine (_root_.GlobalTheory.HilbFam.hasSum_jet_split F k 𝔞 𝔟 a₀ a x τ (c + v) t κ hk ha hτ).unique
    (hs.congr_fun fun ξ => ?_)
  simp_rw [_root_.GlobalTheory.HilbFam.lag_add, Finset.prod_univ_sum, piFinset_range_succ_eq_Iic,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  push_cast
  ring

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeJetSplitDirectionAddStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisensteinLatticeJet_split_direction_add : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : Emb F → ℕ), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → jet k (split 𝔞 𝔟 x) κ τ (c + v) t = ∑ μ ∈ Finset.Iic κ, ((∏ i, rco k (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i)) * jet k (split 𝔞 𝔟 x) μ τ c t := by
  first | exact @GlobalTheory.HilbFam.jet_split_add | exact GlobalTheory.HilbFam.jet_split_add | (intros; apply GlobalTheory.HilbFam.jet_split_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfGroupDeterm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfGroupDeterm
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

noncomputable section

namespace GlobalTheory.RegEmbed

variable {K Γ R : Type} [Field K] [Group Γ] [CommRing R] [Algebra K R]
  (act : Γ →* (R →ₐ[K] R)) (H : Subgroup Γ) [Fintype H]

theorem act_mul_apply (a b : Γ) (x : R) : act (a * b) x = act a (act b x) := by
  rw [map_mul]; rfl

theorem act_one_apply (x : R) : act 1 x = x := by
  rw [map_one]; rfl

theorem sum_act_act (x : R) (g : H) : ∑ k : H, act k (act g x) = ∑ k : H, act k x := by
  rw [← Equiv.sum_comp (Equiv.mulRight g⁻¹)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [← act_mul_apply]

theorem act_sum_act (x : R) (g : H) : act g (∑ k : H, act k x) = ∑ k : H, act k x := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft g⁻¹)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Equiv.coe_mulLeft, ← act_mul_apply, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]

def invIn (V₁ : Submodule K R) : Submodule K R where
  carrier := {x | x ∈ V₁ ∧ ∀ h : H, act h x = x}
  add_mem' := fun ha hb => ⟨V₁.add_mem ha.1 hb.1, fun h => by rw [map_add (f := _), ha.2, hb.2]⟩
  zero_mem' := ⟨V₁.zero_mem, fun h => map_zero _⟩
  smul_mem' := fun c x hx => ⟨V₁.smul_mem c hx.1, fun h => by rw [map_smul, hx.2]⟩

def trL : R →ₗ[K] R := ∑ g : H, (act g).toLinearMap

theorem trL_apply (x : R) : trL act H x = ∑ g : H, act g x := by
  simp [trL]

theorem trL_mem (V₁ : Submodule K R) (hV₁ : ∀ h : H, ∀ x ∈ V₁, act h x ∈ V₁) (x : R) (hx : x ∈ V₁) :
    trL act H x ∈ invIn act H V₁ := by
  rw [trL_apply]
  exact ⟨V₁.sum_mem fun g _ => hV₁ g x hx, fun g => act_sum_act act H x g⟩

theorem eq_zero_of_traces [DecidableEq H] (u : R)
    (hdet : (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R) (v : R)
    (hv : ∀ h : H, ∑ g : H, act g (v * act h u) = 0) : v = 0 := by
  have h0 := GlobalTheory.mulVec_eq_zero_of_det_nonZeroDivisor (Matrix.transpose (Matrix.of fun h g : H => act ((h : Γ) * g) u))
    (by rwa [Matrix.det_transpose]) (fun g : H => act g v) (by
      funext h
      rw [Pi.zero_apply, ← hv h]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_mul (act (g : Γ)), act_mul_apply, mul_comm])
  simpa [act_one_apply] using congrFun h0 1

theorem eq_zero_of_sum [DecidableEq H] (u : R)
    (hdet : (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R) (F : H → R)
    (hF : ∀ g h : H, act g (F h) = F h) (h0 : ∑ h : H, F h * act h u = 0) : F = 0 := by
  refine GlobalTheory.mulVec_eq_zero_of_det_nonZeroDivisor _ hdet F ?_
  funext g
  have h2 := congrArg (fun x => act (g : Γ) x) h0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zero] at h2
  rw [Pi.zero_apply, ← h2]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_mul (act (g : Γ)), hF, act_mul_apply, mul_comm]

end GlobalTheory.RegEmbed

namespace GlobalTheory.BadCount


open GlobalTheory.RegEmbed in
theorem embReg_of_groupDet : ∀ (K Γ R : Type) [Field K] [Group Γ] [Finite Γ] [CommRing R] [Algebra K R] (act : Γ →* (R →ₐ[K] R)) (H : Subgroup Γ) [Fintype H] [DecidableEq H] (u : R), (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R → ∀ (V V₁ V₂ : Submodule K R) [FiniteDimensional K V₂] (ρ : Representation K Γ V), (∀ g x, (ρ g x : R) = act g x) → (∀ h : H, ∀ x ∈ V, x * act h u ∈ V₁) → (∀ h : H, ∀ x ∈ V₁, act h x ∈ V₁) → (∀ h : H, ∀ x ∈ V₁, x * act h u ∈ V₂) → ∃ n : ℕ, EmbReg ρ H n ∧ n * Nat.card H ≤ finrank K V₂ := by
  intro K Γ R _ _ _ _ _ act H _ _ u hdet V V₁ V₂ _ ρ hρ hV hV₁ hV₁₂
  let I := invIn act H V₁
  let T : H → (V →ₗ[K] I) := fun h =>
    ((trL act H).comp ((LinearMap.mulRight K (act h u)).comp V.subtype)).codRestrict I
      (fun v => trL_mem act H V₁ hV₁ _ (hV h v v.2))
  have hT : ∀ h v, ((T h v : I) : R) = ∑ g : H, act g (v * act h u) := fun h v => by
    simp [T, trL_apply]
  let Ψ : (H → I) →ₗ[K] V₂ :=
    (∑ h : H, (LinearMap.mulRight K (act h u)).comp (I.subtype.comp (LinearMap.proj h))).codRestrict V₂
      (fun F => by
        simp only [LinearMap.sum_apply, LinearMap.comp_apply]
        exact V₂.sum_mem fun h _ => hV₁₂ h _ (F h).2.1)
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro F hF
    have h0 := eq_zero_of_sum act H u hdet (fun h => (F h : R)) (fun g h => (F h).2.2 g) (by
      have := congrArg Subtype.val hF
      simpa [Ψ] using this)
    funext h
    exact Subtype.ext (congrFun h0 h)
  haveI : Module.Finite K (H → I) := Module.Finite.of_injective Ψ hΨ
  haveI : Module.Finite K I :=
    Module.Finite.of_surjective (LinearMap.proj (R := K) (φ := fun _ : H => I) 1) (fun x => ⟨fun _ => x, rfl⟩)
  have hle := LinearMap.finrank_le_finrank_of_injective hΨ
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
  let b := Module.finBasis K I
  let j : V →ₗ[K] (Fin (finrank K I) → MonoidAlgebra K H) := LinearMap.pi fun i =>
    (MonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap ∘ₗ (Finsupp.linearEquivFunOnFinite K K H).symm.toLinearMap ∘ₗ
      LinearMap.pi (fun h => (LinearMap.proj i ∘ₗ b.equivFun.toLinearMap) ∘ₗ T h)
  have hj : ∀ v i h, (j v i).coeff h = b.equivFun (T h v) i := fun v i h => by
    simp [j]
  refine ⟨finrank K I, ⟨j, ?_, ?_⟩, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hTv : ∀ h, T h v = 0 := fun h => by
      apply b.equivFun.injective
      funext i
      rw [← hj, hv]
      simp
    apply Subtype.ext
    refine eq_zero_of_traces act H u hdet (v : R) fun h => ?_
    rw [← hT, hTv]
    rfl
  · intro h v i
    apply MonoidAlgebra.ext
    ext k
    rw [MonoidAlgebra.single_mul_apply, one_mul, hj, hj]
    have : T k (ρ h v) = T (h⁻¹ * k) v := by
      apply Subtype.ext
      rw [hT, hT, hρ]
      conv_rhs => rw [← sum_act_act act H _ h]
      refine Finset.sum_congr rfl fun g _ => ?_
      congr 1
      rw [map_mul (act (h : Γ)), Subgroup.coe_mul, Subgroup.coe_inv, ← act_mul_apply act (h : Γ) ((h : Γ)⁻¹ * k),
        mul_inv_cancel_left]
    rw [this]
  · rw [Nat.card_eq_fintype_card, mul_comm]
    exact hle

end GlobalTheory.BadCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfGroupDetermStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedsInRegularRepresentationCopies_of_groupDeterminant : ∀ (K Γ R : Type) [Field K] [Group Γ] [Finite Γ] [CommRing R] [Algebra K R] (act : Γ →* (R →ₐ[K] R)) (H : Subgroup Γ) [Fintype H] [DecidableEq H] (u : R), (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R → ∀ (V V1 V2 : Submodule K R) [FiniteDimensional K V2] (ρ : Representation K Γ V), (∀ g x, (ρ g x : R) = act g x) → (∀ h : H, ∀ x ∈ V, x * act h u ∈ V1) → (∀ h : H, ∀ x ∈ V1, act h x ∈ V1) → (∀ h : H, ∀ x ∈ V1, x * act h u ∈ V2) → ∃ n : ℕ, EmbReg ρ H n ∧ n * Nat.card H ≤ finrank K V2 := by
  first | exact @GlobalTheory.BadCount.embReg_of_groupDet | exact GlobalTheory.BadCount.embReg_of_groupDet | (intros; apply GlobalTheory.BadCount.embReg_of_groupDet <;> assumption)
end
end
