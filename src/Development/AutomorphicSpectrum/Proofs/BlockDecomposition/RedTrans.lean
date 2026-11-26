module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAdicCompleteOfPowEqZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedTrans
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.RedTrans

section
variable {O A R₁ R₂ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R₁] [CommRing R₂]
  {I : Ideal A} {γ : DividedPowers I} {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂}
  {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂} {l n s : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem tr_dp (T : Thick (nlFun γ 0 X q (κA O I))) (h : TF l s T) (n : ℕ) :
    IsDPMorphism (redδ T h (n + 1)) (redδ T h n) (lnMap (RingHom.id T.B) l n.le_succ) := by
  have key : ∀ y : T.B, lnMap (RingHom.id T.B) l n.le_succ (Ideal.Quotient.mk (lnT T l (n + 1)) y) =
      Ideal.Quotient.mk (lnT T l n) y := fun y => by
    simp only [lnMap, lnT, Ideal.quotientMap_mk, RingHom.id_apply]
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    rw [Ideal.mem_comap, key]
    exact Ideal.mem_map_of_mem _ hy
  · intro k x hx
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    rw [key]
    simp only [redδ]
    rw [DividedPowers.Quotient.dpow_apply _ _ hy, DividedPowers.Quotient.dpow_apply _ _ hy, key]

variable (d₁ : RedIn δ₁ κ₁ γ l (n + 1)) (d₂ : RedIn δ₂ κ₂ γ l n) {σ' : R₁ →+* R₂}
  (m : Mor (nlFun δ₁ l X q κ₁) (nlFun δ₂ l X q κ₂) σ')

theorem tr_comm (hρ : ∀ x, d₂.ρ (σ' x) = lnMap (RingHom.id A) l n.le_succ (d₁.ρ x))
    (T : Thick (nlFun γ 0 X q (κA O I))) (r : R₁) :
    lnMap (RingHom.id T.B) l n.le_succ (iBar T l (n + 1) (d₁.ρ r)) = iBar T l n (d₂.ρ (σ' r)) := by
  rw [hρ]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (d₁.ρ r)
  rw [← ha]
  simp only [iBar, lnMap, lnT, Ideal.quotientMap_mk, RingHom.id_apply]

def eta (hpt : ∀ (B : CommRingCat.{0}) (y : PtOver X q κ₂ B), (show PtOver X q κ₁ B from m.pt.app B y).1.2 = y.1.2)
    (hρ : ∀ x, d₂.ρ (σ' x) = lnMap (RingHom.id A) l n.le_succ (d₁.ρ x))
    (T : Thick (nlFun γ 0 X q (κA O I))) (h : TF l s T) : redObj T d₁ h ⟶ m.obj (redObj T d₂ h) :=
  mkH (lnMap (RingHom.id T.B) l n.le_succ) (tr_comm d₁ d₂ hρ T) (tr_dp T h n)
    (Ideal.map_le_iff_le_comap.1 (tr_dp T h n).1) (by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
        refine Eq.trans ?_ ((m.obj (redObj T d₂ h)).w r).symm
        exact congrArg (Ideal.Quotient.mk _) (tr_comm d₁ d₂ hρ T r)
      · refine Eq.trans ?_ (hpt _ _).symm
        change Spec.map _ ≫ Spec.map _ ≫ pt T = Spec.map _ ≫ pt T
        rw [← Category.assoc, ← Spec.map_comp]
        congr 2
        exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)))

end

theorem red_trans : ∀ {O A R₁ R₂ Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R₁] [CommRing R₂] [CommRing Λ]
    {I : Ideal A} {γ : DividedPowers I} {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂}
    {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂} {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ l (n + 1)) (d₂ : RedIn δ₂ κ₂ γ l n) {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} (s : ℕ) (𝒱 : Set X.Opens) {σ' : R₁ →+* R₂} (m : Mor (nlFun δ₁ l X q κ₁) (nlFun δ₂ l X q κ₂) σ')
    (c₁ : Λ →+* R₁) (c₂ : Λ →+* R₂) (lam : Λ →+* A) (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam a))
    (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam a)) (h₀ : ∀ a, σ' (c₁ a) = c₂ (RingHom.id Λ a)),
    (∀ (B : CommRingCat.{0}) (y : PtOver X q κ₂ B), (show PtOver X q κ₁ B from m.pt.app B y).1.2 = y.1.2) →
    (∀ x, d₂.ρ (σ' x) = lnMap (RingHom.id A) l n.le_succ (d₁.ρ x)) → ∀ (r : Option ℤ) (j : ℕ) (x : CH.H (B.OM (nlFun δ₁ l X q κ₁) c₁) j),
    (redMor q s d₂ 𝒱 c₂ lam hc₂ r).pull j ((B.omMor m (RingHom.id Λ) h₀).pull j x) =
      trM (TS γ q l s 𝒱) r (l : A) n j ((redMor q s d₁ 𝒱 c₁ lam hc₁ r).pull j x) := by
  intro O A R₁ R₂ Λ _ _ _ _ _ _ I γ J₁ J₂ δ₁ δ₂ κ₁ κ₂ l n d₁ d₂ X q s 𝒱 σ' m c₁ c₂ lam hc₁ hc₂ h₀ hpt hρ r j x
  rw [CrystallineSemistableComparison.pull_pull lam, trM, CrystallineSemistableComparison.pull_pull lam]
  symm
  refine CrystallineSemistableComparison.cr_pull_eq (F := CrystallineSemistableComparison.B.schFn q) (b := nlBase R₁ J₁ δ₁ l) (ht := rfl) (κ := κ₁) _ _ ?η ?nat ?cmp j x
  case η => exact fun T => eta d₁ d₂ m hpt hρ T.obj T.property.1
  case nat =>
    intro T T' f y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l (n + 1)) y
    rfl
  case cmp =>
    intro T y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l (n + 1)) y
    rfl

end GlobalTheory.CompanionTheory.RedTrans
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartRestrictPullBijective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartRestrictPullBijective
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZarCap

attribute [local instance] MvPolynomial.gradedAlgebra

theorem inU_inf {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (V W : X.Opens) (T : Thick (nlFun γ p X q κ)) :
    InU (V ⊓ W) T ↔ InU V T ∧ InU W T := by
  unfold InU
  rw [← le_inf_iff]
  exact Iff.rfl

theorem irrelevant_le_span (K : Type) [Field K] (N : ℕ) :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K)) := by
  intro x hx
  rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hx
  have h0 : AddMonoidAlgebra.coeff x 0 = 0 := by
    erw [MvPolynomial.decomposition.decompose'_apply, MvPolynomial.homogeneousComponent_zero] at hx
    exact MvPolynomial.C_eq_zero.1 hx
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra hne
  have hm0 : m = 0 := Finsupp.ext fun i => by
    by_contra hi
    exact hne ⟨i, Set.mem_univ i, hi⟩
  subst hm0
  exact (MvPolynomial.mem_support_iff.1 hm) h0

theorem iSup_wch {K : Type} [Field K] {X : Scheme.{0}} (N : ℕ) (i : X ⟶ PSpace K N) : (⨆ j, wch i j) = ⊤ := by
  have h := AlgebraicGeometry.Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
    (fun j => MvPolynomial.X j) (irrelevant_le_span K N)
  simp only [wch]
  rw [← Scheme.Hom.preimage_iSup, h, Scheme.Hom.preimage_top]

theorem resU_eq {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) :
    resU (sq (thFil L r) (thFil L r')) h = (incl h).sq (incl_fil h r) (incl_fil h r') := by
  unfold resU CrystallineSemistableComparison.Pb.SMor.sq
  congr 1
  funext T
  refine LinearMap.ext fun x => Subtype.ext ?_
  obtain ⟨z, hz⟩ := x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

private theorem isHecke_div_and_resEtaPow_div {X : Scheme.{0}} {m N : ℕ} (u : Fin m → X.Opens) (w : Fin (N + 1) → X.Opens)
    (hw : (⨆ j, w j) = ⊤) (S : Finset (Fin m)) :
    (⨅ k ∈ S, u k) ≤ ⨆ c : Fin m → Fin (N + 1), ⨅ k ∈ S, (u k ⊓ w (c k)) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · exact le_iSup_of_le (fun _ => 0) (by simp)
  · intro a S ha ih
    rw [Finset.iInf_insert]
    calc u a ⊓ ⨅ k ∈ S, u k ≤ (⨆ j, u a ⊓ w j) ⊓ ⨆ c : Fin m → Fin (N + 1), ⨅ k ∈ S, (u k ⊓ w (c k)) :=
          inf_le_inf (by rw [← inf_iSup_eq, hw, inf_top_eq]) ih
      _ = ⨆ j, ⨆ c : Fin m → Fin (N + 1), (u a ⊓ w j) ⊓ ⨅ k ∈ S, (u k ⊓ w (c k)) := by
          rw [iSup_inf_eq]
          simp_rw [inf_iSup_eq]
      _ ≤ ⨆ c : Fin m → Fin (N + 1), ⨅ k ∈ insert a S, (u k ⊓ w (c k)) := by
          refine iSup_le fun j => iSup_le fun c => le_iSup_of_le (Function.update c a j) ?_
          rw [Finset.iInf_insert]
          refine inf_le_inf (by simp) (le_iInf₂ fun k hk => (iInf₂_le k hk).trans ?_)
          have hka : k ≠ a := fun h => ha (h ▸ hk)
          simp [hka]

theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty)
    (r r' : ℤ) (j : ℕ),
    ∃ h : capS (wK q i y s) S ≤ KS q s {⨅ k ∈ S, uy i y k},
      Function.Bijective ((resU (sq (thFil (smFun X q) r) (thFil (smFun X q) r')) h).pull j) := by
  intro K _ X q N m i y s S hS r r' j
  classical
  have e : capS (wK q i y s) S = KS q s (Set.range fun c : Fin m → Fin (N + 1) => ⨅ k ∈ S, (uy i y k ⊓ wch i (c k))) := by
    funext T
    apply propext
    constructor
    · intro hT
      obtain ⟨k0, hk0⟩ := hS
      refine ⟨(hT k0 hk0).1, ?_⟩
      have hc : ∀ k, ∃ c : Fin (N + 1), k ∈ S → InU (uy i y k ⊓ wch i c) T := by
        intro k
        by_cases hk : k ∈ S
        · obtain ⟨_, V, ⟨c, rfl⟩, hV⟩ := hT k hk
          exact ⟨c, fun _ => hV⟩
        · exact ⟨0, fun h => absurd h hk⟩
      choose c hc using hc
      exact ⟨_, ⟨c, rfl⟩, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun k => uy i y k ⊓ wch i (c k)) S _).2 hc⟩
    · rintro ⟨hT, V, ⟨c, rfl⟩, hV⟩ k hk
      exact ⟨hT, _, ⟨c k, rfl⟩, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun k => uy i y k ⊓ wch i (c k)) S _).1 hV k hk⟩
  rw [e]
  have hle : KS q s (Set.range fun c : Fin m → Fin (N + 1) => ⨅ k ∈ S, (uy i y k ⊓ wch i (c k))) ≤
      KS q s {⨅ k ∈ S, uy i y k} := by
    rintro T ⟨hT, V, ⟨c, rfl⟩, hV⟩
    refine ⟨hT, _, Set.mem_singleton _, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (uy i y) S _).2 fun k hk => ?_⟩
    exact ((inU_inf _ _ _).1 ((GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun k => uy i y k ⊓ wch i (c k)) S _).1 hV k hk)).1
  have hc : ∀ W ∈ ({⨅ k ∈ S, uy i y k} : Set X.Opens),
      W ≤ sSup (Set.range fun c : Fin m → Fin (N + 1) => ⨅ k ∈ S, (uy i y k ⊓ wch i (c k))) := by
    intro W hW
    rw [Set.mem_singleton_iff] at hW
    subst hW
    rw [sSup_range]
    exact isHecke_div_and_resEtaPow_div (uy i y) (wch i) (iSup_wch N i) S
  refine ⟨hle, ?_⟩
  rw [resU_eq]
  exact (GlobalTheory.CompanionTheory.NlZar.zariski_descent (CrystallineSemistableComparison.Pb.TF 1 s) (Or.inl ⟨rfl, 1, s, rfl⟩) _ _ hle hc j).1 r r'

end GlobalTheory.CompanionTheory.ConeZarCap
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartRestrictPullBijectiveStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_restrict_pull_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty)
    (r r' : ℤ) (j : ℕ),
    ∃ h : capS (wK q i y s) S ≤ KS q s {⨅ k ∈ S, uy i y k},
      Function.Bijective ((resU (sq (thFil (smFun X q) r) (thFil (smFun X q) r')) h).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.ConeZarCap.main | exact GlobalTheory.CompanionTheory.ConeZarCap.main | (intros; apply GlobalTheory.CompanionTheory.ConeZarCap.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingUniversalProperty
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingUniversalProperty
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.AcrUniv

theorem pow_mem_map {R B : Type} [CommRing R] [CommRing B] (h : R →+* B) (I : Ideal R) (p : ℕ) (hp : p.Prime)
    (hI : ∀ x ∈ I, x ^ p ∈ Ideal.span {(p : R)}) : ∀ x ∈ I.map h, x ^ p ∈ Ideal.span {(p : B)} := by
  intro x hx
  refine Submodule.span_induction (p := fun x _ => x ^ p ∈ Ideal.span {(p : B)}) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (hI y hy)
    rw [← map_pow, hc, map_mul, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rw [zero_pow hp.ne_zero]; exact zero_mem _
  · intro a b _ _ ha hb
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp a b
    rw [hr]
    exact add_mem (add_mem ha hb) (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))))
  · intro a b _ hb
    rw [smul_eq_mul, mul_pow]
    exact Ideal.mul_mem_left _ _ hb

section Tens

variable {R S T C B : Type} [CommRing R] [CommRing S] [CommRing T] [CommRing C] [CommRing B]
  [Algebra R S] [Algebra R T] [Algebra R C] [Algebra S C] [Algebra T C]
  [IsScalarTower R S C] [IsScalarTower R T C]

open TensorProduct in
theorem tens_ext
    (hs : Function.Surjective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S C)
      (IsScalarTower.toAlgHom R T C) (fun _ _ => Commute.all _ _)))
    (f f' : C →+* B) (h1 : ∀ s, f (algebraMap S C s) = f' (algebraMap S C s))
    (h2 : ∀ t, f (algebraMap T C t) = f' (algebraMap T C t)) : f = f' := by
  refine RingHom.ext fun c => ?_
  obtain ⟨z, rfl⟩ := hs c
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s t =>
    rw [Algebra.TensorProduct.lift_tmul, IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom',
      map_mul, map_mul, h1, h2]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

open TensorProduct in
theorem tens_desc (m n : ℕ)
    (hs : Function.Surjective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S C)
      (IsScalarTower.toAlgHom R T C) (fun _ _ => Commute.all _ _)))
    (hk : ∀ z : S ⊗[R] T, Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S C)
      (IsScalarTower.toAlgHom R T C) (fun _ _ => Commute.all _ _) z = 0 ↔
        z ∈ Ideal.span {(m : S ⊗[R] T) ^ n})
    (u : S →+* B) (v : T →+* B) (huv : ∀ r, u (algebraMap R S r) = v (algebraMap R T r))
    (hm : (m : B) ^ n = 0) :
    ∃ f : C →+* B, (∀ s, f (algebraMap S C s) = u s) ∧ ∀ t, f (algebraMap T C t) = v t := by
  letI : Algebra R B := (u.comp (algebraMap R S)).toAlgebra
  let u' : S →ₐ[R] B := { u with commutes' := fun _ => rfl }
  let v' : T →ₐ[R] B := { v with commutes' := fun r => (huv r).symm }
  let L : S ⊗[R] T →ₐ[R] B := Algebra.TensorProduct.lift u' v' (fun _ _ => Commute.all _ _)
  let Φ : S ⊗[R] T →ₐ[R] C := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S C)
    (IsScalarTower.toAlgHom R T C) (fun _ _ => Commute.all _ _)
  have hker : RingHom.ker (Φ : S ⊗[R] T →+* C) ≤ RingHom.ker (L : S ⊗[R] T →+* B) := by
    intro z hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ((hk z).1 hz)
    rw [RingHom.mem_ker, map_mul, map_pow, map_natCast, hm, mul_zero]
  let f : C →+* B := (Φ : S ⊗[R] T →+* C).liftOfSurjective hs ⟨(L : S ⊗[R] T →+* B), hker⟩
  have hf : ∀ z, f (Φ z) = L z := fun z =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ z
  refine ⟨f, fun s => ?_, fun t => ?_⟩
  · have h := hf (s ⊗ₜ 1)
    simpa [Φ, L, u'] using h
  · have h := hf (1 ⊗ₜ t)
    simpa [Φ, L, v'] using h

end Tens

end GlobalTheory.CompanionTheory.AcrUniv

namespace GlobalTheory.CompanionTheory.AcrUniv

theorem maps_out : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) (B : Type) [CommRing B] (h : (base l).Acr n →+* B), (∀ g : A.A →+* B ⧸ ((base l).PFil n).map h, (∀ a : Ob l, g (A.s a) = Ideal.Quotient.mk _ (h ((base l).toAcr n (WittVector.teichmuller l a)))) → ∃ f : A.Acr n →+* B, f.comp (mapAcr A.fromBase n) = h ∧ ∀ a, Ideal.Quotient.mk _ (f (A.toAcr n (WittVector.teichmuller l a))) = g a) ∧ ∀ f f' : A.Acr n →+* B, f.comp (mapAcr A.fromBase n) = h → f'.comp (mapAcr A.fromBase n) = h → (∀ a, f (A.toAcr n (WittVector.teichmuller l a)) - f' (A.toAcr n (WittVector.teichmuller l a)) ∈ ((base l).PFil n).map h) → f = f' := by
  intro l _ A n B _ h
  have hp : l.Prime := Fact.out
  obtain ⟨⟨π, -, -⟩, hFil, -, -, -, -, -⟩ := GlobalTheory.T.period_ring_base_change_from_universal A n
  obtain ⟨-, -, -, -, -, hpow, -⟩ := GlobalTheory.T.period_ring_base_change_from_universal (base l) n
  have hlB : (l : B) ^ n = 0 := by
    rw [← map_natCast h, ← map_pow, pow_l_acr, map_zero]
  have hlJ : (l : B) ∈ ((base l).PFil n).map h := by
    rw [← map_natCast h]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hJp : ∀ x ∈ ((base l).PFil n).map h, x ^ l ∈ Ideal.span {(l : B)} :=
    pow_mem_map h _ l hp fun x hx => (hpow x hx).2
  have hOb : D.Pf l (Ob l) := ⟨(base l).natCast_l, (base l).perf.1⟩
  have hA : D.Pf l A.A := ⟨A.natCast_l, A.perf.1⟩
  obtain ⟨hts, htk⟩ := RL.tens A n
  have hbs := ((RL.base_acr (base l) isBase_base).2 n).1
  refine ⟨fun g hg => ?_, fun f f' h1 h2 h3 => ?_⟩
  · obtain ⟨⟨f₀, hf₀⟩, -⟩ := GlobalTheory.CompanionTheory.PerfectWittMaps.wittVector_lift l _ n hA hlB hlJ hJp g
    have hc : f₀.comp A.sW = h.comp ((base l).toAcr n) :=
      (GlobalTheory.CompanionTheory.PerfectWittMaps.wittVector_lift l (A := Ob l) _ n hOb hlB hlJ hJp (g.comp A.s)).2 _ _ fun a => by
        rw [RingHom.comp_apply, RingHom.comp_apply, sW, WittVector.map_teichmuller, hf₀]
        exact hg a
    have huv : ∀ r : Ainf l, (h.comp ((base l).cris n)) (algebraMap (Ainf l) (Acris l) r) =
        f₀ (algebraMap (Ainf l) A.W r) := fun r => by
      rw [RingHom.comp_apply, cris_algebraMap]
      have e : (base l).sW r = r := wmap_id r
      rw [e]
      exact (RingHom.congr_fun hc r).symm
    obtain ⟨f, hf1, hf2⟩ := tens_desc l n hts htk (h.comp ((base l).cris n)) f₀ huv hlB
    refine ⟨f, RingHom.ext fun y => ?_, fun a => ?_⟩
    · obtain ⟨a, rfl⟩ := hbs y
      rw [RingHom.comp_apply, mapAcr_cris]
      exact hf1 a
    · have e : f (A.toAcr n (WittVector.teichmuller l a)) = f₀ (WittVector.teichmuller l a) :=
        hf2 (WittVector.teichmuller l a)
      rw [e, hf₀]
  · have hfJ : A.PFil n ≤ (((base l).PFil n).map h).comap f := by
      refine sup_le ?_ ?_
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
        exact hlJ
      · rw [hFil 1, Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap, Ideal.mem_comap, ← RingHom.comp_apply, h1]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_right hx)
    have hw := (GlobalTheory.CompanionTheory.PerfectWittMaps.wittVector_lift l _ n hA hlB hlJ hJp
      ((Ideal.quotientMap _ f hfJ).comp π)).2 (f.comp (A.toAcr n)) (f'.comp (A.toAcr n))
      fun a => Ideal.Quotient.eq.2 (h3 a)
    refine tens_ext hts f f' (fun a => ?_) fun t => RingHom.congr_fun hw t
    have e : algebraMap (Acris l) (A.Acr n) a = mapAcr A.fromBase n ((base l).cris n a) :=
      (mapAcr_cris A.fromBase n a).symm
    rw [e]
    exact RingHom.congr_fun (h1.trans h2.symm) _

end GlobalTheory.CompanionTheory.AcrUniv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingUniversalPropertyStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_ring_universal_property : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) (B : Type) [CommRing B] (h : (base l).Acr n →+* B), (∀ g : A.A →+* B ⧸ ((base l).PFil n).map h, (∀ a : Ob l, g (A.s a) = Ideal.Quotient.mk _ (h ((base l).toAcr n (WittVector.teichmuller l a)))) → ∃ f : A.Acr n →+* B, f.comp (mapAcr A.fromBase n) = h ∧ ∀ a, Ideal.Quotient.mk _ (f (A.toAcr n (WittVector.teichmuller l a))) = g a) ∧ ∀ f f' : A.Acr n →+* B, f.comp (mapAcr A.fromBase n) = h → f'.comp (mapAcr A.fromBase n) = h → (∀ a, f (A.toAcr n (WittVector.teichmuller l a)) - f' (A.toAcr n (WittVector.teichmuller l a)) ∈ ((base l).PFil n).map h) → f = f' := by
  first | exact @GlobalTheory.CompanionTheory.AcrUniv.maps_out | exact GlobalTheory.CompanionTheory.AcrUniv.maps_out | (intros; apply GlobalTheory.CompanionTheory.AcrUniv.maps_out <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallinePointUniversalLift
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallinePointUniversalLift
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.TowerHom

theorem exists_roots {R : Type} [CommRing R] {l : ℕ} (h : ∀ x : R, ∃ y, y ^ l = x) (u : R) :
    ∃ y : ℕ → R, y 0 = u ∧ ∀ m, y (m + 1) ^ l = y m := by
  choose r hr using h
  exact ⟨fun m => Nat.rec u (fun _ z => r z) m, rfl, fun m => hr _⟩

theorem roots_unique {R : Type} [CommRing R] {l : ℕ} (h : ∀ x y : R, x ^ l = y ^ l → x = y) {y z : ℕ → R}
    (h0 : y 0 = z 0) (hy : ∀ m, y (m + 1) ^ l = y m) (hz : ∀ m, z (m + 1) ^ l = z m) (m : ℕ) : y m = z m := by
  induction m with
  | zero => exact h0
  | succ m ih => exact h _ _ (by rw [hy, hz, ih])

theorem pow_sub_pow {R : Type} [CommRing R] {l : ℕ} (F : R →+* R) (hF : ∀ x, F x = x ^ l) (x y : R) (m : ℕ) :
    x ^ l ^ m - y ^ l ^ m = (x - y) ^ l ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ l m, pow_mul, pow_mul, pow_mul, ← ih, ← hF, ← hF, ← hF, map_sub]

theorem iter_root {R : Type} [CommRing R] {l : ℕ} {x : ℕ → R} (hx : ∀ m, x (m + 1) ^ l = x m) (m : ℕ) :
    x m ^ l ^ m = x 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ' l m, pow_mul, hx, ih]

variable {l : ℕ} [Fact l.Prime]

theorem pow_char (A : PAlg l) (x : A.A) : A.frob x = x ^ l := rfl

theorem pow_inj (A : PAlg l) (x y : A.A) (h : x ^ l = y ^ l) : x = y := A.frob_bijective.1 h

theorem pow_surj (A : PAlg l) (x : A.A) : ∃ y, y ^ l = x := A.frob_bijective.2 x

theorem eq_of_roots_mod (A : PAlg l) {x y : ℕ → A.A} (hx : ∀ m, x (m + 1) ^ l = x m) (hy : ∀ m, y (m + 1) ^ l = y m)
    (h : ∀ m, x m - y m ∈ Ideal.span {A.pi}) : x 0 = y 0 := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hH : IsHausdorff (Ideal.span {A.s (pFlat l)}) A.A := A.compl.toIsHausdorff
  refine sub_eq_zero.1 (hH.haus' _ fun n => ?_)
  rw [SModEq.zero, Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id, ← iter_root hx n, ← iter_root hy n,
    pow_sub_pow A.frob (pow_char A)]
  exact Ideal.pow_le_pow_right (Nat.lt_pow_self hl).le (Ideal.pow_mem_pow (h n) _)

theorem mapU_mem {A A' : PAlg l} (φ : A ⟶ A') {x : A.U} (hx : x ∈ Ideal.span {(l : A.U)}) :
    mapU φ x ∈ Ideal.span {(l : A'.U)} := by
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem exists_sharp_cong (A : PAlg l) (x : A.U) : ∃ a, A.sharp a - x ∈ Ideal.span {(l : A.U)} := by
  obtain ⟨a, ha⟩ := (RL.u_mod A).1 (Ideal.Quotient.mk _ x)
  refine ⟨a, ?_⟩
  rw [A.sharpMap_eq] at ha
  simpa using Ideal.Quotient.eq.1 ha

def modEquiv (A : PAlg l) : (A.A ⧸ Ideal.span {A.pi}) ≃+* A.Un 1 :=
  (Ideal.quotEquivOfEq (RL.u_mod A).2.symm).trans (RingHom.quotientKerEquivOfSurjective (RL.u_mod A).1)

theorem modEquiv_mk (A : PAlg l) (a : A.A) : modEquiv A (Ideal.Quotient.mk _ a) = A.aToU1 a := rfl

def gBar (A : PAlg l) {R : Type} [CommRing R] (g : R →+* A.U) : R →+* A.A ⧸ Ideal.span {A.pi} :=
  ((modEquiv A).symm : A.Un 1 →+* A.A ⧸ Ideal.span {A.pi}).comp ((Ideal.Quotient.mk _).comp g)

theorem gBar_iff (A : PAlg l) {R : Type} [CommRing R] (g : R →+* A.U) (r : R) (a : A.A) :
    gBar A g r = Ideal.Quotient.mk _ a ↔ A.sharp a - g r ∈ Ideal.span {(l : A.U)} := by
  have e : gBar A g r = (modEquiv A).symm (Ideal.Quotient.mk _ (g r)) := rfl
  rw [e, RingEquiv.symm_apply_eq, modEquiv_mk, A.sharpMap_eq, eq_comm, Ideal.Quotient.eq, pow_one]

theorem core {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (A' : PAlg l)
    (g : s.R →+* A'.U) (hga : g.comp s.a = A'.oC.comp κ) (u : Fin d → A'.A) (hu : ∀ k, A'.sharp (u k) = g (s.T k)) :
    ∃ φ : 𝒯.A ⟶ A', ((mapU φ).comp 𝒯.g = g ∧ ∀ k, Hom.f φ (𝒯.c k 0).val = u k) ∧
      ∀ φ' : 𝒯.A ⟶ A', (mapU φ').comp 𝒯.g = g → (∀ k, Hom.f φ' (𝒯.c k 0).val = u k) → φ' = φ := by
  have hy : ∀ k, ∃ y : ℕ → A'.A, y 0 = u k ∧ ∀ m, y (m + 1) ^ l = y m := fun k => exists_roots (pow_surj A') (u k)
  choose y hy0 hys using hy
  have hc : ∀ k m, ((𝒯.c k (m + 1)).val) ^ l = (𝒯.c k m).val := fun k m => by
    rw [← Units.val_pow_eq_pow_val, 𝒯.c_succ]
  have ho : ((Ideal.Quotient.mk (Ideal.span {A'.pi})).comp A'.s) (pFlat l) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have h1 : ∀ x w, theta0 l w = κ x → gBar A' g (s.a x) = ((Ideal.Quotient.mk (Ideal.span {A'.pi})).comp A'.s) (w.coeff 0) := by
    intro x w hw
    have hcf : (A'.sW w).coeff 0 = A'.s (w.coeff 0) := WittVector.map_coeff _ _ _
    refine (gBar_iff A' g _ _).2 ?_
    have e1 : g (s.a x) = A'.th (A'.sW w) := by
      rw [← A'.oC_theta0, hw]
      exact RingHom.congr_fun hga x
    have e2 := A'.sharpMap_coeff (A'.sW w)
    rw [hcf, A'.sharpMap_eq] at e2
    rw [e1]
    simpa using Ideal.Quotient.eq.1 e2
  have h2 : ∀ k, Ideal.Quotient.mk (Ideal.span {A'.pi}) (y k 0) = gBar A' g (s.T k) := fun k =>
    ((gBar_iff A' g _ _).2 (by rw [hy0, hu, sub_self]; exact Ideal.zero_mem _)).symm
  have h3 : ∀ k m, Ideal.Quotient.mk (Ideal.span {A'.pi}) (y k (m + 1)) ^ l = Ideal.Quotient.mk (Ideal.span {A'.pi}) (y k m) :=
    fun k m => by rw [← map_pow, hys]
  obtain ⟨f, ⟨hfo, hfg, hfc⟩, hfu⟩ := 𝒯.univ (A'.A ⧸ Ideal.span {A'.pi}) ((Ideal.Quotient.mk _).comp A'.s) (gBar A' g)
    (fun k m => Ideal.Quotient.mk _ (y k m)) ho h1 h2 h3
  obtain ⟨φ, hφ, hφu⟩ := GlobalTheory.CompanionTheory.PerfLift.existsUnique_hom 𝒯.A A' f hfo
  have hφa : ∀ a, Ideal.Quotient.mk (Ideal.span {A'.pi}) (Hom.f φ a) = f a := fun a => RingHom.congr_fun hφ a
  have hck : ∀ k, Hom.f φ (𝒯.c k 0).val = u k := by
    intro k
    rw [← hy0 k]
    refine eq_of_roots_mod A' (x := fun m => Hom.f φ (𝒯.c k m).val) (fun m => ?_) (hys k) fun m => ?_
    · rw [← map_pow, hc]
    · refine Ideal.Quotient.eq.1 ?_
      rw [hφa, hfc]
  have hgφ : (mapU φ).comp 𝒯.g = g := by
    have hE := GlobalTheory.CompanionTheory.EtaleLift.etLift_of_isAdicComplete (Ideal.span {(l : A'.U)}) A'.completeU
      (MvPolynomial (Fin d) O) s.R (MvPolynomial.eval₂Hom s.a fun k => (s.T k : s.R)) s.et
      (g.comp (MvPolynomial.eval₂Hom s.a fun k => (s.T k : s.R))) ((Ideal.Quotient.mk _).comp g) rfl
    refine hE.unique ⟨?_, ?_⟩ ⟨rfl, rfl⟩
    · refine MvPolynomial.ringHom_ext (fun o => ?_) fun k => ?_
      · have e1 : 𝒯.g (s.a o) = 𝒯.A.oC (κ o) := RingHom.congr_fun 𝒯.hg o
        have e2 : g (s.a o) = A'.oC (κ o) := RingHom.congr_fun hga o
        simp only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
        rw [e1, e2, mapU_oC]
      · simp only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
        rw [← 𝒯.c_sharp, mapU_sharp, hck, hu]
    · refine RingHom.ext fun r => ?_
      obtain ⟨a, ha⟩ := exists_sharp_cong 𝒯.A (𝒯.g r)
      have e : gBar A' g r = Ideal.Quotient.mk _ (Hom.f φ a) := by rw [hφa]; exact (hfg r a ha).symm
      have e1 := (gBar_iff A' g r _).1 e
      have e2 := mapU_mem φ ha
      rw [map_sub, mapU_sharp] at e2
      refine Ideal.Quotient.eq.2 ?_
      have e3 : mapU φ (𝒯.g r) - g r = (A'.sharp (Hom.f φ a) - g r) - (A'.sharp (Hom.f φ a) - mapU φ (𝒯.g r)) := by ring
      change mapU φ (𝒯.g r) - g r ∈ _
      rw [e3]
      exact Ideal.sub_mem _ e1 e2
  refine ⟨φ, ⟨hgφ, hck⟩, fun φ' hg' hk' => hφu φ' (hfu _ ⟨?_, ?_, ?_⟩)⟩
  · rw [RingHom.comp_assoc, Hom.comm]
  · intro r a ha
    have e2 := mapU_mem φ' ha
    rw [map_sub, mapU_sharp] at e2
    have e3 : mapU φ' (𝒯.g r) = g r := RingHom.congr_fun hg' r
    rw [e3] at e2
    exact ((gBar_iff A' g r _).2 e2).symm
  · intro k m
    have := roots_unique (pow_inj A') (y := fun m => Hom.f φ' (𝒯.c k m).val) (z := y k)
      ((hk' k).trans (hy0 k).symm) (fun m => by
        rw [← map_pow, hc]) (hys k) m
    exact congrArg (Ideal.Quotient.mk _) this

theorem tower_hom : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (T : (F.pt κ).Elements), ∃ g : s.R →+* T.1.U, F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.2.1 ∧ (∀ φ : 𝒯.obj ⟶ T, (mapU φ.1).comp 𝒯.g = g) ∧ ∀ u : Fin d → T.1.A, (∀ k, T.1.sharp (u k) = g (s.T k)) → ∃! φ : 𝒯.obj ⟶ T, ∀ k, PAlg.Hom.f φ.1 (𝒯.c k 0).val = u k := by
  intro l _ O _ F κ d s 𝒯 T
  obtain ⟨g, hg, hgu⟩ := s.univ (CommRingCat.of T.1.U) T.2.1 (T.1.oC.comp κ) T.2.2
  have hga : g.comp s.a = T.1.oC.comp κ :=
    F.ov_uniq (hg ▸ F.ov_map (CommRingCat.ofHom g) s.ov) T.2.2
  have hall : ∀ φ : 𝒯.obj ⟶ T, (mapU φ.1).comp 𝒯.g = g := by
    intro φ
    refine hgu _ ?_
    have h1 : F.Pt.map (CommRingCat.ofHom (mapU φ.1)) (F.Pt.map (CommRingCat.ofHom 𝒯.g) s.y₀) = T.2.1 :=
      congrArg Subtype.val φ.2
    have h2 : F.Pt.map (CommRingCat.ofHom ((mapU φ.1).comp 𝒯.g)) s.y₀ = T.2.1 := by
      rw [CommRingCat.ofHom_comp, F.Pt.map_comp]
      exact h1
    exact h2
  refine ⟨g, hg, hall, fun u hu => ?_⟩
  obtain ⟨φ, ⟨hφg, hφk⟩, hφu⟩ := core 𝒯 T.1 g hga u hu
  have hpt : (F.pt κ).map φ 𝒯.obj.2 = T.2 := by
    refine Subtype.ext ?_
    change F.Pt.map (CommRingCat.ofHom (mapU φ)) (F.Pt.map (CommRingCat.ofHom 𝒯.g) s.y₀) = T.2.1
    have h2 : F.Pt.map (CommRingCat.ofHom ((mapU φ).comp 𝒯.g)) s.y₀ = T.2.1 := by
      rw [hφg]
      exact hg
    rw [CommRingCat.ofHom_comp, F.Pt.map_comp] at h2
    exact h2
  refine ⟨⟨φ, hpt⟩, hφk, fun φ' hk => CategoryTheory.Functor.Elements.Hom.ext (hφu φ'.1 (hall φ') hk)⟩

end GlobalTheory.CompanionTheory.TowerHom
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallinePointUniversalLiftStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_point_universal_lift : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (T : (F.pt κ).Elements), ∃ g : s.R →+* T.1.U, F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.2.1 ∧ (∀ φ : 𝒯.obj ⟶ T, (mapU φ.1).comp 𝒯.g = g) ∧ ∀ u : Fin d → T.1.A, (∀ k, T.1.sharp (u k) = g (s.T k)) → ∃! φ : 𝒯.obj ⟶ T, ∀ k, PAlg.Hom.f φ.1 (𝒯.c k 0).val = u k := by
  first | exact @GlobalTheory.CompanionTheory.TowerHom.tower_hom | exact GlobalTheory.CompanionTheory.TowerHom.tower_hom | (intros; apply GlobalTheory.CompanionTheory.TowerHom.tower_hom <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeTransport
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.HodgeO

section Transport

variable {R : Type} [CommRing R]

theorem finrank_of_vb {k M : Type} [Field k] [AddCommGroup M] [Module k M] {g : ℕ} (h : VB k M g) :
    Module.finrank k M = g := by
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum k) := inferInstance
  have e := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := k) (M := M)) p
  exact e.symm.trans (h.2.2 p)

theorem vb_of_equiv {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {g : ℕ}
    (e : M ≃ₗ[R] N) (h : VB R M g) : VB R N g :=
  have := h.1
  have := h.2.1
  ⟨Module.Finite.equiv e, Module.Projective.of_equiv e, fun p ↦
    (congrFun (Module.rankAtStalk_eq_of_equiv e) p).symm.trans (h.2.2 p)⟩

def wedgeEquiv {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    ⋀[R]^2 M ≃ₗ[R] ⋀[R]^2 N :=
  LinearEquiv.ofLinear (exteriorPower.map 2 e.toLinearMap) (exteriorPower.map 2 e.symm.toLinearMap)
    (by rw [← exteriorPower.map_comp]; simp)
    (by rw [← exteriorPower.map_comp]; simp)

theorem wedge_transport {M M' N N' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'] (e₁ : M ≃ₗ[R] M') (e₂ : N ≃ₗ[R] N')
    (B : M → M → N) (B' : M' → M' → N') (hB : ∀ a b, e₂ (B a b) = B' (e₁ a) (e₁ b))
    (h : ∃ e : ⋀[R]^2 M ≃ₗ[R] N, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = B a b) :
    ∃ e : ⋀[R]^2 M' ≃ₗ[R] N', ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = B' a b := by
  obtain ⟨e, he⟩ := h
  refine ⟨(wedgeEquiv e₁.symm).trans (e.trans e₂), fun a b ↦ ?_⟩
  have k : wedgeEquiv e₁.symm (exteriorPower.ιMulti R 2 ![a, b]) =
      exteriorPower.ιMulti R 2 ![e₁.symm a, e₁.symm b] := by
    refine (exteriorPower.map_apply_ιMulti _ _).trans (congrArg _ ?_)
    funext i
    fin_cases i <;> rfl
  simp only [LinearEquiv.trans_apply]
  rw [k, he, hB, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

variable {C C' : Type} [Category.{0} C] [Category.{0} C'] {F : C ⥤ CommAlgCat.{0} R}
  {F' : C' ⥤ CommAlgCat.{0} R}

theorem wedge_of_bij (m : CoefMap (RingHom.id R) F F') (h₁ : Function.Bijective m.pull1)
    (h₂ : Function.Bijective m.pull2) (h : Wedge F) : Wedge F' :=
  wedge_transport (LinearEquiv.ofBijective m.pull1 h₁) (LinearEquiv.ofBijective m.pull2 h₂)
    (fun a b ↦ cup F a b) (fun a b ↦ cup F' a b) (fun a b ↦ m.pullCohomologyTwo_cup a b) h

theorem wedge_of_bij' (m : CoefMap (RingHom.id R) F F') (h₁ : Function.Bijective m.pull1)
    (h₂ : Function.Bijective m.pull2) (h : Wedge F') : Wedge F :=
  wedge_transport (LinearEquiv.ofBijective m.pull1 h₁).symm (LinearEquiv.ofBijective m.pull2 h₂).symm
    (fun a b ↦ cup F' a b) (fun a b ↦ cup F a b) (fun a b ↦ by
      refine (LinearEquiv.symm_apply_eq _).2 ?_
      refine Eq.trans ?_ (m.pullCohomologyTwo_cup _ _).symm
      change _ = cup F' (LinearEquiv.ofBijective m.pull1 h₁ _) (LinearEquiv.ofBijective m.pull1 h₁ _)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]) h

theorem hopf_false {b : Prop} (h : Hopf F b) : Hopf F False := by
  obtain ⟨D, _, G, π, m, h₁, h₂, -⟩ := h
  exact ⟨D, _, G, π, m, h₁, h₂, False.elim⟩

end Transport

theorem pack {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {R' : Type} [CommRing R'] [Algebra R R'] (A' : Over (Sp R'))
    {i : GrpObj A'} (φ : A'.left ⟶ A.left) (hφ : IsGrpPullback A' A (spMap (algebraMap R R')) φ) :
    ∃ (A' : Over (Sp R')) (_ : GrpObj A') (φ : A'.left ⟶ A.left),
      IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) ∧ IsAbelianScheme A' ∧
        SmoothOfRelativeDimension g A'.hom :=
  ⟨A', i, φ, hφ.1, GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hφ,
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hφ.1 hg⟩

theorem exists_base {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (R' : Type) [CommRing R'] [Algebra R R'] :
    ∃ (A' : Over (Sp R')) (_ : GrpObj A') (φ : A'.left ⟶ A.left),
      IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) ∧ IsAbelianScheme A' ∧
        SmoothOfRelativeDimension g A'.hom :=
  pack A g hA hg _ _ (isGrpPullback_pullback A (spMap (algebraMap R R')))

theorem low (hD : DescentSt) (hL : LowSt) {P : Type} [SemilatticeInf P] (R' : Type) [CommRing R'] (A' : Over (Sp R'))
    [GrpObj A'] (ha : IsAbelianScheme A') (S' : Sys A'.left P) :
    Function.Bijective (resSys A'.hom S').pull1 ∧ Function.Bijective (resSys A'.hom S').pull2 ∧
      (Stein (OAff A'.hom) ↔ Stein (OSys A'.hom S')) := by
  have := ha.proper
  exact hL R' _ _ (OAff A'.hom) (OSys A'.hom S') (resSys A'.hom S') (hD R' A'.left A'.hom inferInstance P S')

theorem base (hS : SysBCSt) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {P : Type} [SemilatticeInf P] (S : Sys A.left P) (R' : Type)
    [CommRing R'] [Algebra R R'] : ∃ (A' : Over (Sp R')) (_ : GrpObj A') (S' : Sys A'.left P)
      (_ : BC (OSys A.hom S) (OSys A'.hom S')), IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom := by
  have pr := hA.proper
  have sep : IsSeparated A.hom := inferInstance
  obtain ⟨A', _, φ, h, ha, hg'⟩ := exists_base A g hA hg R'
  obtain ⟨S', m, -⟩ := hS R R' A.left A'.left A.hom A'.hom φ h sep P S
  exact ⟨A', _, S', m, ha, hg'⟩

theorem steinU (hD : DescentSt) (hL : LowSt) (hS : SysBCSt) (hSt : SteinSt) {R : Type} [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {P : Type} [SemilatticeInf P] (S : Sys A.left P) : SteinU (OSys A.hom S) := fun R' _ _ ↦ by
  obtain ⟨A', _, S', m, ha, hg'⟩ := base hS A g hA hg S R'
  exact ⟨_, m, (low hD hL R' A' ha S').2.2.1 (hSt R' A' g ha hg')⟩

theorem vbSys (hD : DescentSt) (hL : LowSt) (hH1 : H1StructureBundle) {R : Type} [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {P : Type} [SemilatticeInf P] (S : Sys A.left P) : VB R (H1 (OSys A.hom S)) g :=
  vb_of_equiv (LinearEquiv.ofBijective _ (low hD hL R A hA S).1) (hH1 R A g hA hg)

theorem finFib (hD : DescentSt) (hL : LowSt) (hS : SysBCSt) (hH1 : H1StructureBundle) {R : Type} [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {P : Type} [SemilatticeInf P] (S : Sys A.left P) (k : Type) [Field k] [Algebra R k] :
    ∃ (F' : Pᵒᵖ ⥤ CommAlgCat.{0} k) (_ : BC (OSys A.hom S) F'), Module.finrank k (H1 F') = g := by
  obtain ⟨A', _, S', m, ha, hg'⟩ := base hS A g hA hg S k
  exact ⟨_, m, finrank_of_vb (vbSys hD hL hH1 A' g ha hg' S')⟩

theorem wedgeFib (hD : DescentSt) (hL : LowSt) (hS : SysBCSt) (hWF : WedgeFieldSt) {R : Type} [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {P : Type} [SemilatticeInf P] (S : Sys A.left P) (k : Type) [Field k] [Algebra R k] :
    ∃ (F' : Pᵒᵖ ⥤ CommAlgCat.{0} k) (_ : BC (OSys A.hom S) F'), Wedge F' := by
  obtain ⟨A', _, S', m, ha, hg'⟩ := base hS A g hA hg S k
  have b := low hD hL k A' ha S'
  exact ⟨_, m, wedge_of_bij (resSys A'.hom S') b.1 b.2.1 (hWF k A' g ha hg' (Field.toIsField k))⟩

theorem coreSys (hD : DescentSt) (hL : LowSt) (hS : SysBCSt) (hSt : SteinSt) (hH1 : H1StructureBundle)
    (hWF : WedgeFieldSt) (hHopf : HopfSt) (hPH1 : PerfectH1BaseChange) (hPH2 : PerfectH2FromFibres) (hWO : WedgeOfSt)
    {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {P : Type} [SemilatticeInf P] [Finite P] (S : Sys A.left P)
    (hPf : Perf (OSys A.hom S)) : H1CommutesBaseChange (OSys A.hom S) ∧ Wedge (OSys A.hom S) := by
  have hSU := steinU hD hL hS hSt A g hA hg S
  have hV := vbSys hD hL hH1 A g hA hg S
  have hB : H1CommutesBaseChange (OSys A.hom S) := hPH1 R P (OSys A.hom S) g hPf hSU hV fun k _ _ ↦
    finFib hD hL hS hH1 A g hA hg S k
  obtain ⟨h2, hs⟩ := hPH2 R P (OSys A.hom S) g hPf hSU hV hB fun k _ _ ↦
    wedgeFib hD hL hS hWF A g hA hg S k
  exact ⟨hB, hWO R P (OSys A.hom S) g (hopf_false (hHopf R A g hA hg P S)) hV hB h2 hs⟩

theorem oBC_wedge : DescentSt → LowSt → SysBCSt → PerfSt → SteinSt → H1StructureBundle → WedgeFieldSt → HopfSt → PerfectH1BaseChange →
    PerfectH2FromFibres → WedgeOfSt → OBCSt ∧ WedgeSt := by
  intro hD hL hS hP hSt hH1 hWF hHopf hPH1 hPH2 hWO
  refine ⟨?_, ?_⟩
  · intro R _ A _ g hA hg R' _ _ X' s' φ h
    have pr := hA.proper
    have sep : IsSeparated A.hom := inferInstance
    have sep' : IsSeparated s' := MorphismProperty.of_isPullback h sep
    obtain ⟨P, _, _, S, hPf⟩ := hP R A.left A.hom hA.smooth pr
    have hB := (coreSys hD hL hS hSt hH1 hWF hHopf hPH1 hPH2 hWO A g hA hg S hPf).1
    obtain ⟨S', m, hc⟩ := hS R R' A.left X' A.hom s' φ h sep P S
    obtain ⟨e₀, he₀⟩ := hB R' _ m
    have b₁ := (hL R _ _ _ _ (resSys A.hom S) (hD R A.left A.hom sep P S)).1
    have b₂ := (hL R' _ _ _ _ (resSys s' S') (hD R' X' s' sep' P S')).1
    let e₁ := LinearEquiv.ofBijective _ b₁
    let e₂ := LinearEquiv.ofBijective _ b₂
    refine ⟨(LinearEquiv.baseChange R R' _ _ e₁).trans (e₀.trans e₂.symm), fun c ↦ hc c _ ?_⟩
    refine (he₀ _).symm.trans ?_
    exact (e₂.apply_symm_apply _).symm
  · intro R _ A _ g hA hg
    have pr := hA.proper
    obtain ⟨P, _, _, S, hPf⟩ := hP R A.left A.hom hA.smooth pr
    have hW := (coreSys hD hL hS hSt hH1 hWF hHopf hPH1 hPH2 hWO A g hA hg S hPf).2
    have b := low hD hL R A hA S
    exact wedge_of_bij' (resSys A.hom S) b.1 b.2.1 hW

end GlobalTheory.CompanionTheory.HodgeO
end
end
