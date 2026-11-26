module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLevelCoverOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdealOfLocally
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelEqOfPowEqOfHasTh
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MorphismsGenericSpreadOut

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PowLeftCompOfGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

open GlobalTheory.ThetaObjPull

theorem pow_left_comp_of_grpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A]
    [GrpObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (x' : Out.baseOver S' ⟶ A')
    (x : Out.baseOver S ⟶ A) (e : x'.left ≫ φ = f ≫ x.left) (n : ℕ) :
    (x' ^ n).left ≫ φ = f ≫ (x ^ n).left := by
  have e₁ : pushHom h _ x' = toBase f ≫ x := Over.OverMorphism.ext e
  have e₂ : pushHom h _ (x' ^ n) = toBase f ≫ (x ^ n) := by
    rw [map_pow, e₁]
    exact (map_pow (preHom (toBase f)) _ _).symm
  exact congrArg (fun z => z.left) e₂

theorem gLies_pull : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S S₁ S₂ : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) (c : S₁ ⟶ S) (s₁ : S₁ ⟶ Sp o) (t₁ : TObj g (N' ^ 2) J b s₁) (ψ₁ : t₁.A.left ⟶ A.left) (y : S₂ ⟶ S₁) (s₂ : S₂ ⟶ Sp o), L.IsLB → GLies A act Q c t₁ ψ₁ → LBIso t₁.L (L.pull ψ₁) → y ≫ s₁ = s₂ → ∃ (u : TObj g (N' ^ 2) J b s₂) (ψ : u.A.left ⟶ A.left), TMap u t₁ y ∧ GLies A act Q (y ≫ c) u ψ ∧ LBIso u.L (L.pull ψ) ∧ ∀ i, (u.pt i).left ≫ ψ = y ≫ (t₁.pt i).left ≫ ψ₁ := by
  intro o _ g N' J b S S₁ S₂ A _ L act Q c s₁ t₁ ψ₁ y s₂ hL ⟨h₁, h₂, h₃⟩ hI hs
  obtain ⟨u, φ, k₁, k₂, k₃, k₄⟩ := GlobalTheory.tObj_pull o g (N' ^ 2) J b S₁ S₂ s₁ s₂ y t₁ hs
  refine ⟨u, φ ≫ ψ₁, ⟨φ, k₁, k₂, k₃, k₄⟩, ⟨k₁.comp h₁, fun i => ?_, fun i => ?_⟩, ?_, fun i => ?_⟩
  · rw [← Category.assoc, k₄, Category.assoc, h₂, Category.assoc]
  · rw [← Category.assoc, pow_left_comp_of_grpPullback k₁ _ _ (k₃ i), Category.assoc, h₃, Category.assoc]
  · exact LBIso.trans u.isLB (pull_isLB t₁.isLB _) (pull_isLB hL _) k₂ (lbIso_pull_comp hI φ)
  · rw [← Category.assoc, k₃, Category.assoc]

end GlobalTheory.ZM.NearBuild
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelEqOfGLiesOfHasTh
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

theorem level_eq_of_gLies_of_hasTh : Out.Laws → Out.Laws2 → ∀ (g n j : ℕ) (J : Type), n.Prime → Odd n → 2 ≤ j → ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (S S₁ : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) (c : S₁ ⟶ S) (s₁ : S₁ ⟶ Sp o) (t₁ : TObj g ((n ^ j) ^ 2) J b s₁) (ψ₁ : t₁.A.left ⟶ A.left) (K : Type) [Field K] [IsAlgClosed K] (y y' : Sp K ⟶ S₁) (w : Ix g ((n ^ j) ^ 2) → K), L.IsLB → GLies A act Q c t₁ ψ₁ → LBIso t₁.L (L.pull ψ₁) → y ≫ c = y' ≫ c → y ≫ s₁ = y' ≫ s₁ → t₁.HasTh y w → t₁.HasTh y' w → ∀ i, y ≫ (t₁.pt i).left ≫ ψ₁ = y' ≫ (t₁.pt i).left ≫ ψ₁ := by
  intro hL hL2 g n j J hn hodd hj o _ b S S₁ A _ L act Q c s₁ t₁ ψ₁ K _ _ y y' w hLB hG hI hc hs T T'
  obtain ⟨u, ψ, m, ⟨a₁, -, a₃⟩, l, p⟩ :=
    gLies_pull o g (n ^ j) J b S S₁ _ A L act Q c s₁ t₁ ψ₁ y (y ≫ s₁) hLB hG hI rfl
  obtain ⟨u', ψ', m', ⟨a₁', -, a₃'⟩, l', p'⟩ :=
    gLies_pull o g (n ^ j) J b S S₁ _ A L act Q c s₁ t₁ ψ₁ y' (y ≫ s₁) hLB hG hI hs.symm
  rw [← hc] at a₁' a₃'
  have U : u.HasTh (𝟙 _) w :=
    (GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b _ _ t₁ _ _ u _ K _ _ m).2 (by rwa [Category.id_comp])
  have U' : u'.HasTh (𝟙 _) w :=
    (GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b _ _ t₁ _ _ u' _ K _ _ m').2 (by rwa [Category.id_comp])
  have hp := a₁.1
  let χ : u'.A.left ⟶ u.A.left := hp.lift ψ' u'.A.hom a₁'.1.w
  have e₁ : χ ≫ ψ = ψ' := hp.lift_fst _ _ _
  have e₂ : χ ≫ u.A.hom = u'.A.hom := hp.lift_snd _ _ _
  have c₁ : IsGrpPullback u'.A u.A (𝟙 _) χ :=
    a₁.cancel (a₁'.congr (Category.id_comp _).symm e₁.symm) (by rw [e₂, Category.comp_id])
  have c₀ : LBIso (u.L.pull χ) (L.pull ψ') :=
    l.chartPull (Geo.Tor.chartPullPull u.L χ χ rfl)
      (chartPullSame L (fun _ : PUnit => ψ') (fun _ : PUnit => ψ) (fun _ => 1) χ (fun _ => e₁.symm))
  have c₂ : LBIso u'.L (u.L.pull χ) :=
    LBIso.trans u'.isLB (pull_isLB hLB _) (pull_isLB u.isLB _) l' c₀.symm
  have c₃ : ∀ i, (u'.pt i ^ n ^ j).left ≫ χ = (u.pt i ^ n ^ j).left := fun i => by
    apply hp.hom_ext
    · rw [Category.assoc, e₁, a₃', a₃]
    · rw [Category.assoc, e₂, Over.w, Over.w]
  have c₅ := GlobalTheory.level_eq_of_pow_eq_of_hasTh hL hL2 g n j J hn hodd hj o b K _ u u' χ _ c₁ c₂ c₃ U U'
  intro i
  rw [← p, ← p', ← c₅, Category.assoc, e₁]

end GlobalTheory.ZM.NearBuild
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TmapOfGlies
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

theorem tmap_of_glies : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S S₁ S₂ : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) (c : S₁ ⟶ S) (s₁ : S₁ ⟶ Sp o) (t₁ : TObj g (N' ^ 2) J b s₁) (ψ₁ : t₁.A.left ⟶ A.left) (y : S₂ ⟶ S₁) (s₂ : S₂ ⟶ Sp o) (u : TObj g (N' ^ 2) J b s₂) (ψ : u.A.left ⟶ A.left), L.IsLB → GLies A act Q c t₁ ψ₁ → LBIso t₁.L (L.pull ψ₁) → GLies A act Q (y ≫ c) u ψ → LBIso u.L (L.pull ψ) → (∀ i, (u.pt i).left ≫ ψ = y ≫ (t₁.pt i).left ≫ ψ₁) → TMap u t₁ y := by
  intro o _ g N' J b S S₁ S₂ A _ L act Q c s₁ t₁ ψ₁ y s₂ u ψ hL ⟨h₁, h₄, _⟩ h₂ ⟨k₁, k₄, _⟩ k₂ k₃
  have hp := h₁.1
  obtain ⟨F, hF, hw⟩ : ∃ F : u.A.left ⟶ t₁.A.left, F ≫ ψ₁ = ψ ∧ F ≫ t₁.A.hom = u.A.hom ≫ y :=
    ⟨hp.lift ψ (u.A.hom ≫ y) (by rw [k₁.1.w, Category.assoc]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  subst hF
  refine ⟨F, h₁.cancel k₁ hw, ?_, fun i => ?_, fun j => ?_⟩
  · exact LBIso.trans u.isLB (pull_isLB hL _) (pull_isLB t₁.isLB _) k₂ (lbIso_pull_comp h₂ F).symm
  · apply hp.hom_ext
    · rw [Category.assoc, k₃, Category.assoc]
    · have a₁ : (u.pt i).left ≫ u.A.hom = 𝟙 S₂ := Over.w (u.pt i)
      have a₂ : (t₁.pt i).left ≫ t₁.A.hom = 𝟙 S₁ := Over.w (t₁.pt i)
      rw [Category.assoc, hw, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  · apply hp.hom_ext
    · rw [Category.assoc, k₄, Category.assoc, Category.assoc, h₄]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]

end GlobalTheory.ZM.NearBuild
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRetractionNearOfUniquePoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearBuild

theorem exists_smul_mem_range_of_unique_point (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra.FormallyUnramified R B] (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K)
    (y : B →+* K) (hy : y.comp (algebraMap R B) = x) (hu : ∀ z : B →+* K, z.comp (algebraMap R B) = x → z = y) :
    ∃ f : R, f ∉ RingHom.ker x ∧ ∀ b : B, ∃ a : R, algebraMap R B a = algebraMap R B f * b := by
  let _ : Algebra R K := x.toAlgebra
  let yA : B →ₐ[R] K := { y with commutes' := fun r => RingHom.congr_fun hy r }
  let φ : K ⊗[R] B →ₐ[K] K :=
    Algebra.TensorProduct.lift (Algebra.ofId K K) yA (fun _ _ => Commute.all _ _)
  have hall : ∀ ψ : K ⊗[R] B →ₐ[K] K, ∀ (a : K) (b : B), ψ (a ⊗ₜ[R] b) = a * y b := by
    intro ψ a b
    have hz : ((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight).toRingHom = y := by
      apply hu
      ext r
      exact ((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight).commutes r
    have h1 : ψ ((1 : K) ⊗ₜ[R] b) = y b := by
      have := RingHom.congr_fun hz b
      simpa using this
    have h2 : a ⊗ₜ[R] b = a • ((1 : K) ⊗ₜ[R] b) := by
      rw [TensorProduct.smul_tmul']
      simp
    rw [h2, map_smul, h1, _root_.smul_eq_mul]
  have huniq : ∀ ψ : K ⊗[R] B →ₐ[K] K, ψ = φ := by
    intro ψ
    refine AlgHom.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [hall ψ, hall φ]
    | add s t hs ht => rw [map_add (f := _), map_add (f := _), hs, ht]
  have hsurj := algebraMap_surjective_of_unramified_of_unique_point K (K ⊗[R] B) φ huniq
  set N : Submodule R B := LinearMap.range (Algebra.linearMap R B) with hN
  have hone : N.mkQ (1 : B) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr ⟨1, by simp⟩
  have hzero : ∀ t : K ⊗[R] (B ⧸ N), t = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rfl
    | tmul a c =>
      obtain ⟨b, rfl⟩ := N.mkQ_surjective c
      obtain ⟨c', hc'⟩ := hsurj (a ⊗ₜ[R] b)
      rw [← LinearMap.lTensor_tmul, ← hc', Algebra.TensorProduct.algebraMap_apply, LinearMap.lTensor_tmul, hone,
        TensorProduct.tmul_zero]
    | add s t hs ht => rw [hs, ht, add_zero]
  let p : PrimeSpectrum R := ⟨RingHom.ker x, RingHom.ker_isPrime x⟩
  have hns : p ∉ Module.support R (B ⧸ N) := by
    intro h
    have hnt := nontrivial_tensor_of_mem_support R (B ⧸ N) K p rfl h
    obtain ⟨s, t, hst⟩ := hnt.exists_pair_ne
    exact hst ((hzero s).trans (hzero t).symm)
  rw [Module.mem_support_iff_of_finite] at hns
  obtain ⟨f, hf, hfp⟩ := Set.not_subset.mp hns
  refine ⟨f, hfp, fun b => ?_⟩
  have hfb : f • N.mkQ b = 0 := Module.mem_annihilator.mp hf _
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hfb
  obtain ⟨a, ha⟩ := hfb
  exact ⟨a, by rw [← Algebra.smul_def, ← ha, Algebra.linearMap_apply]⟩

theorem exists_retraction_away (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    (hinj : Function.Injective (algebraMap R B)) (f : R)
    (hf : ∀ b : B, ∃ a : R, algebraMap R B a = algebraMap R B f * b) :
    ∃ r : B →+* Localization.Away f, r.comp (algebraMap R B) = loc f := by
  choose a ha using hf
  set g : Localization.Away f := IsLocalization.Away.invSelf f with hg
  have hfg : loc f f * g = 1 := IsLocalization.Away.mul_invSelf f
  have ha_zero : a 0 = 0 := hinj (by simp only [ha, MulZeroClass.mul_zero, map_zero])
  have ha_one : a 1 = f := hinj (by simp only [ha, _root_.mul_one])
  have ha_add : ∀ b c, a (b + c) = a b + a c := fun b c => hinj (by simp only [ha, map_add (f := _)]; ring)
  have ha_mul : ∀ b c, f * a (b * c) = a b * a c := fun b c => hinj (by simp only [ha, map_mul]; ring)
  have ha_alg : ∀ c, a (algebraMap R B c) = f * c := fun c => hinj (by simp only [ha, map_mul])
  have h_one : loc f (a 1) * g = 1 := by rw [ha_one, hfg]
  have h_mul : ∀ b c, loc f (a (b * c)) * g = loc f (a b) * g * (loc f (a c) * g) := by
    intro b c
    have h := congrArg (loc f) (ha_mul b c)
    rw [map_mul, map_mul] at h
    linear_combination (-(loc f (a (b * c)) * g)) * hfg + g * g * h
  have h_zero : loc f (a 0) * g = 0 := by rw [ha_zero, map_zero, MulZeroClass.zero_mul]
  have h_add : ∀ b c, loc f (a (b + c)) * g = loc f (a b) * g + loc f (a c) * g := by
    intro b c
    rw [ha_add, map_add (f := _), add_mul]
  let r : B →+* Localization.Away f :=
    { toFun := fun b => loc f (a b) * g
      map_one' := h_one
      map_mul' := h_mul
      map_zero' := h_zero
      map_add' := h_add }
  refine ⟨r, ?_⟩
  · ext c
    show loc f (a (algebraMap R B c)) * g = loc f c
    rw [ha_alg, map_mul]
    linear_combination (loc f c) * hfg

theorem exists_retraction_near_of_unique_point :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] [Module.Finite R B] [Algebra.FormallyUnramified R B] (P : Set (Ideal R)), DenseP P → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K), RingHom.ker x = q ∧ ∃! y : B →+* K, y.comp (algebraMap R B) = x) → ∀ q₀ ∈ P, ∃ f : R, f ∉ q₀ ∧ ∃ r : B →+* Localization.Away f, r.comp (algebraMap R B) = loc f ∧ ∀ (T : Type) [CommRing T] (x : Localization.Away f →+* T) (y : B →+* T), y.comp (algebraMap R B) = x.comp (loc f) → y = x.comp r := by
  intro R B _ _ _ _ _ P hD hP q₀ hq₀
  obtain ⟨K, _, _, x, hker, y, hy, hu⟩ := hP q₀ hq₀
  obtain ⟨f, hfk, hfB⟩ := exists_smul_mem_range_of_unique_point R B K x y hy hu
  have hinj : Function.Injective (algebraMap R B) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    refine hD a fun p hp _ => ?_
    obtain ⟨K', _, _, x', hker', y', hy', -⟩ := hP p hp
    rw [← hker', RingHom.mem_ker, ← hy', RingHom.comp_apply, ha, map_zero]
  obtain ⟨r, hr⟩ := exists_retraction_away R B hinj f hfB
  refine ⟨f, hker ▸ hfk, r, hr, fun T _ x' y' hxy => ?_⟩
  ext b
  obtain ⟨a, ha⟩ := hfB b
  have h1 : y' (algebraMap R B a) = x' (loc f a) := RingHom.congr_fun hxy a
  have h2 : y' (algebraMap R B f) = x' (loc f f) := RingHom.congr_fun hxy f
  have h3 : loc f a = loc f f * r b := by
    rw [← RingHom.congr_fun hr a, ← RingHom.congr_fun hr f, RingHom.comp_apply, RingHom.comp_apply, ha, map_mul]
  have hU : IsUnit (x' (loc f f)) := (IsLocalization.Away.algebraMap_isUnit f).map x'
  apply hU.mul_left_cancel
  rw [RingHom.comp_apply, ← map_mul, ← h3, ← h1, ha, map_mul, h2]

end GlobalTheory.ZM.NearBuild
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

theorem nearC_of_polFam_of_kTriv : Out.Laws → Out.Laws2 → ∀ (g n j : ℕ) (J : Type), n.Prime → Odd n → 2 ≤ j → ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)) (q₀ : Ideal R), Den b Mat κ β v q₀ → Ideal.span (Set.range v) = ⊤ → PolFam b Mat κ β v A L act Q → Out.KTriv A L → NearC b Mat κ β v q₀ := by
  intro h1 h2 g n j J hn hodd hj o _ b Mat κ R _ _ _ β v A _ L act Q q₀ hD hv hP hK
  obtain ⟨hD1, hD2⟩ := hD
  obtain ⟨hAb, hdim, hLB, hrig, hsym, hamp, hlab, hgood⟩ := hP
  obtain ⟨hl1, hl2, hl3⟩ := hlab
  let P : Out.PolAV (Sp R) :=
    { A := A, isAb := hAb, g := g, smoothDim := hdim, L := L, isLB := hLB, rigid := hrig, sym := hsym,
      ample := hamp, ktriv := hK }
  have hpos : 0 < n ^ j := pow_pos hn.pos j

  obtain ⟨R₁, _, _, t₁, ψ₁, hfin, het, ⟨hpb₁, hL₁, hact₁, hpt₁⟩, huniv⟩ :=
    GlobalTheory.exists_finiteEtale_level_cover h1 h2 o g (n ^ j) J b R β P act Q hpos ⟨rfl, hl1, hl2, hl3⟩
  have hG₁ : GLies A act Q (spMap (algebraMap R R₁)) t₁ ψ₁ := And.intro hpb₁ (And.intro hact₁ hpt₁)
  have h3 : 3 ≤ n ^ j := by
    have := Nat.odd_iff.1 hodd
    have := hn.two_le
    have : n ≤ n ^ j := Nat.le_self_pow (by omega) n
    omega

  obtain ⟨𝔞, h𝔞⟩ := GlobalTheory.ThetaClosed.exists_ideal_hasTh_iff h1 h2 o g (n ^ j) J b R₁
    (spMap (algebraMap R R₁) ≫ spMap β) t₁ (fun a => algebraMap R R₁ (v a)) hodd.pow h3
    (GlobalTheory.ThetaClosed.span_map_eq_top (algebraMap R R₁) hv)

  have kill : ∀ (K : Type) [Field K] (x : R →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β))
      (y₁ : R₁ →+* K), y₁.comp (algebraMap R R₁) = x → TMap t t₁ (spMap y₁) →
      t.HasTh (𝟙 _) (fun a => x (v a)) → ∀ r ∈ 𝔞, y₁ r = 0 := by
    intro K _ x t y₁ hc hT hth
    apply (h𝔞 K y₁).1
    have h := (GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b (Sp R₁) (spMap (algebraMap R R₁) ≫ spMap β) t₁
      (Sp K) _ t (spMap y₁) K (𝟙 _) (fun a => x (v a)) hT).1 hth
    rw [Category.id_comp] at h
    have hw : (fun a => x (v a)) = fun a => y₁ (algebraMap R R₁ (v a)) := by
      funext a; rw [← hc]; rfl
    rw [hw] at h
    exact h

  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] (y y' : R₁ →+* K),
      y.comp (algebraMap R R₁) = y'.comp (algebraMap R R₁) →
      (∀ r ∈ 𝔞, y r = 0) → (∀ r ∈ 𝔞, y' r = 0) → y = y' := by
    intro K _ _ y y' hyy hy hy'
    have th := (h𝔞 K y).2 hy
    have th' := (h𝔞 K y').2 hy'
    have hw : (fun a => y' (algebraMap R R₁ (v a))) = fun a => y (algebraMap R R₁ (v a)) := by
      funext a; exact (RingHom.congr_fun hyy (v a)).symm
    have hc : spMap y ≫ spMap (algebraMap R R₁) = spMap y' ≫ spMap (algebraMap R R₁) := by
      rw [← spMap_comp, ← spMap_comp, hyy]
    have heq := level_eq_of_gLies_of_hasTh h1 h2 g n j J hn hodd hj o b (Sp R) (Sp R₁) A L act Q
      (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β) t₁ ψ₁ K (spMap y) (spMap y')
      (fun a => y (algebraMap R R₁ (v a))) hLB hG₁ hL₁ hc
      (by rw [← Category.assoc, ← Category.assoc, hc]) th (by rw [← hw]; exact th')
    obtain ⟨u, ψ, hTu, hGu, hLu, hptu⟩ := gLies_pull o g (n ^ j) J b (Sp R) (Sp R₁) (Sp K) A L act Q
      (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β) t₁ ψ₁ (spMap y)
      (spMap (y.comp (algebraMap R R₁)) ≫ spMap β) hLB hG₁ hL₁
      (by rw [spMap_comp, Category.assoc])
    have hc' : spMap y' ≫ spMap (algebraMap R R₁) = spMap (y.comp (algebraMap R R₁)) := by
      rw [← hc, spMap_comp]
    have hGu' : GLies A act Q (spMap (y.comp (algebraMap R R₁))) u ψ := by
      have ⟨g1, g2, g3⟩ := hGu
      rw [← spMap_comp y (algebraMap R R₁)] at g1 g3
      exact And.intro g1 (And.intro g2 g3)
    have hTu' : TMap u t₁ (spMap y') := tmap_of_glies o g (n ^ j) J b (Sp R) (Sp R₁) (Sp K) A L act Q
      (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β) t₁ ψ₁ (spMap y') _ u ψ hLB hG₁ hL₁
      (by rw [hc']; exact hGu') hLu (fun i => (hptu i).trans (heq i))
    have ⟨hg1, hg2, hg3⟩ := hGu'
    obtain ⟨y₀, -, huq⟩ := huniv K (y.comp (algebraMap R R₁)) u ψ ⟨hg1, hLu, hg2, hg3⟩
    exact (huq y ⟨rfl, hptu, hTu⟩).trans (huq y' ⟨hyy.symm, fun i => (hptu i).trans (heq i), hTu'⟩).symm
  have hqa : algebraMap R (R₁ ⧸ 𝔞) = (Ideal.Quotient.mk 𝔞).comp (algebraMap R R₁) :=
    IsScalarTower.algebraMap_eq R R₁ (R₁ ⧸ 𝔞)
  have : Module.Finite R (R₁ ⧸ 𝔞) := Module.Finite.trans R₁ (R₁ ⧸ 𝔞)
  have : Algebra.FormallyUnramified R (R₁ ⧸ 𝔞) := inferInstance

  have hup : ∀ q ∈ objPrimes b Mat κ β v, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K),
      RingHom.ker x = q ∧ ∃! y : R₁ ⧸ 𝔞 →+* K, y.comp (algebraMap R (R₁ ⧸ 𝔞)) = x := by
    intro q hq
    obtain ⟨K, _, _, x, t, hker, hsh, hth⟩ := hq
    obtain ⟨ψ, hG, hLψ⟩ := hgood K x _ t (And.intro rfl (And.intro hsh hth))
    have ⟨hg1, hg2, hg3⟩ := hG
    obtain ⟨y₁, ⟨hy₁c, -, hy₁T⟩, -⟩ := huniv K x t ψ ⟨hg1, hLψ, hg2, hg3⟩
    have hk := kill K x t y₁ hy₁c hy₁T hth
    refine ⟨K, inferInstance, inferInstance, x, hker, Ideal.Quotient.lift 𝔞 y₁ hk, ?_, ?_⟩
    · beta_reduce
      rw [hqa, ← RingHom.comp_assoc, Ideal.Quotient.lift_comp_mk, hy₁c]
    · intro y hy
      apply Ideal.Quotient.ringHom_ext
      rw [Ideal.Quotient.lift_comp_mk]
      apply key K (y.comp (Ideal.Quotient.mk 𝔞)) y₁
      · rw [RingHom.comp_assoc, ← hqa, hy, hy₁c]
      · intro r hr
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
      · exact hk

  obtain ⟨f, hfq, r, hr, -⟩ := exists_retraction_near_of_unique_point R (R₁ ⧸ 𝔞)
    (objPrimes b Mat κ β v) hD1 hup q₀ hD2
  obtain ⟨z, hzdef⟩ : ∃ z : R₁ →+* Localization.Away f, z = r.comp (Ideal.Quotient.mk 𝔞) := ⟨_, rfl⟩
  have hz : z.comp (algebraMap R R₁) = loc f := by
    rw [hzdef, RingHom.comp_assoc, ← hqa, hr]
  have hzk : ∀ x ∈ 𝔞, z x = 0 := by
    intro x hx
    rw [hzdef, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]

  obtain ⟨u, ψ, hTu, hGu, hLu, hptu⟩ := gLies_pull o g (n ^ j) J b (Sp R) (Sp R₁)
    (Sp (Localization.Away f)) A L act Q (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β)
    t₁ ψ₁ (spMap z) (spMap ((loc f).comp β)) hLB hG₁ hL₁
    (by rw [← hz, spMap_comp (z.comp (algebraMap R R₁)) β, spMap_comp z (algebraMap R R₁), Category.assoc])
  refine Exists.intro f (And.intro hfq (Exists.intro u (And.intro ?_ ?_)))
  · have h := (h𝔞 _ z).2 hzk
    apply (GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b (Sp R₁) (spMap (algebraMap R R₁) ≫ spMap β) t₁
      (Sp (Localization.Away f)) _ u (spMap z) (Localization.Away f) (𝟙 _) (fun a => loc f (v a)) hTu).2
    rw [Category.id_comp]
    have hw : (fun a => loc f (v a)) = fun a => z (algebraMap R R₁ (v a)) := by
      funext a; rw [← hz]; rfl
    rw [hw]; exact h
  · intro K _ _ x s t' hg
    obtain ⟨rfl, hsh, hth⟩ := (good_comp (loc f) x t').1 hg
    obtain ⟨ψ', hG', hLψ'⟩ := hgood K (x.comp (loc f)) _ t' (And.intro rfl (And.intro hsh hth))
    have ⟨hg1, hg2, hg3⟩ := hG'
    obtain ⟨y₁, ⟨hy₁c, -, hy₁T⟩, -⟩ := huniv K (x.comp (loc f)) t' ψ' ⟨hg1, hLψ', hg2, hg3⟩
    have hk := kill K (x.comp (loc f)) t' y₁ hy₁c hy₁T hth
    have hyz : y₁ = x.comp z := key K y₁ (x.comp z) (by rw [hy₁c, RingHom.comp_assoc, hz]) hk
      (by intro r' hr'; rw [RingHom.comp_apply, hzk r' hr', map_zero])
    rw [hyz, spMap_comp x z] at hy₁T
    exact TMap.cancel hTu hy₁T

end GlobalTheory.ZM.NearBuild
end
