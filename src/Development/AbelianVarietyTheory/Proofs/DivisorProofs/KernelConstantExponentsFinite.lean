module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
public import Formalism.LocalToGlobal.Divisibility.NumbersLink
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConstantExponentsFinite
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder Pointwise

namespace GlobalTheory.ExponentsFinite

theorem val_le_one {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {p s : ℕ}
    (hp : ((p : ℕ) : 𝓞 K) ∈ P.asIdeal) (hs : Nat.Coprime s p) {x : K} (hx : IsIntegral ℤ ((s : K) * x)) :
    P.valuation K x ≤ 1 := by
  have hsP : ((s : ℕ) : 𝓞 K) ∉ P.asIdeal := by
    intro h
    obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hs).map (Int.castRingHom (𝓞 K))
    simp only [eq_intCast, Int.cast_natCast] at hab
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h) (P.asIdeal.mul_mem_left _ hp)))
  have h1 := (P.valuation_eq_one_iff_notMem (K := K)).2 hsP
  have h2 := P.valuation_le_one (K := K) (⟨_, hx⟩ : 𝓞 K)
  rw [map_natCast] at h1
  change P.valuation K ((s : K) * x) ≤ 1 at h2
  rwa [map_mul, h1, one_mul] at h2

theorem val_det_le_one {K ι Γ : Type} [Field K] [Fintype ι] [DecidableEq ι] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (f : (ι → K) →ₗ[K] (ι → K)) (hf : ∀ i j, v (f (Pi.single j 1) i) ≤ 1) :
    v (LinearMap.det f) ≤ 1 := by
  rw [← LinearMap.det_toMatrix', Matrix.det_apply']
  have : ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, LinearMap.toMatrix' f (σ i) i ∈ v.integer := by
    refine Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _) (Subring.prod_mem _ fun i _ => ?_)
    rw [LinearMap.toMatrix'_apply]
    exact hf _ _
  exact this

theorem val_det_eq_one {K ι Γ : Type} [Field K] [Fintype ι] [DecidableEq ι] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (f : (ι → K) ≃ₗ[K] (ι → K)) (hf : ∀ i j, v (f (Pi.single j 1) i) ≤ 1)
    (hf' : ∀ i j, v (f.symm (Pi.single j 1) i) ≤ 1) :
    v (LinearMap.det (f : (ι → K) →ₗ[K] (ι → K))) = 1 := by
  have h1 := val_det_le_one v (f : (ι → K) →ₗ[K] (ι → K)) hf
  have h2 := val_det_le_one v (f.symm : (ι → K) →ₗ[K] (ι → K)) hf'
  have h3 := congrArg v (LinearEquiv.det_mul_det_symm f)
  rw [map_mul, map_one] at h3
  refine le_antisymm h1 ?_
  calc 1 = _ := h3.symm
    _ ≤ v (LinearMap.det (f : (ι → K) →ₗ[K] (ι → K))) * 1 := by gcongr
    _ = _ := mul_one _

theorem exists_den {K ι : Type} [Field K] [NumberField K] [Finite ι] (c : ι → K) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, IsIntegral ℤ ((n : K) * c i) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image c)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun i => ?_⟩
  have h := hy (c i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [zsmul_eq_mul] at h
  rcases Int.natAbs_eq y with h1 | h1
  · rw [h1, Int.cast_natCast] at h; exact h
  · rw [h1, Int.cast_neg, Int.cast_natCast, neg_mul] at h; simpa using h.neg

theorem exists_den_fg {K E ι κ : Type} [Field K] [NumberField K] [AddCommGroup E] [Finite ι] [Fintype κ]
    (A : Submodule ℤ E) (hA : A.FG) (g : (κ → E) →+ (ι → K)) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : κ → E, (∀ a, x a ∈ A) → ∀ w, IsIntegral ℤ ((n : K) * g x w) := by
  classical
  obtain ⟨S, hS⟩ := hA
  obtain ⟨n, hn, h⟩ := exists_den (fun t : S × κ × ι => g (Pi.single t.2.1 (t.1 : E)) t.2.2)
  refine ⟨n, hn, fun x hx w => ?_⟩
  have key : ∀ a, ∀ y ∈ Submodule.span ℤ (S : Set E), IsIntegral ℤ ((n : K) * g (Pi.single a y) w) := by
    intro a y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h (⟨y, hy⟩, a, w)
    | zero => simpa using isIntegral_zero
    | add y z _ _ hy hz => rw [Pi.single_add, map_add (f := _), Pi.add_apply, mul_add]; exact hy.add hz
    | smul c y _ hy =>
      rw [Pi.single_smul, map_zsmul, Pi.smul_apply, mul_smul_comm]; exact hy.zsmul c
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.univ_sum_single x, map_sum, Finset.sum_apply, Finset.mul_sum]
  exact IsIntegral.sum _ fun a _ => key a _ (hS ▸ hx a)

theorem one_mem (D : D7) : (1 : D.host.E) ∈ D.host.AA0 := by
  have hb : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h => by
      have h3 : D.host.𝔟 ⊔ D.host.conj • D.host.𝔟 = ⊤ := D.host.𝔟_spec.2
      simp [h] at h3
  refine (FractionalIdeal.mem_inv_iff hb).2 fun y hy => ?_
  rw [one_mul]; exact FractionalIdeal.coeIdeal_le_one hy

theorem yFinite : ∀ (D : D7) (γ₀ : IsoK D) (k : KapChoice γ₀), k.YFinite := by
  classical
  intro D γ₀ k
  have hfg : ((D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).restrictScalars ℤ).FG :=
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl D.host.AA0).restrictScalars
  obtain ⟨n, hn, hnx⟩ := exists_den_fg _ hfg γ₀.g.toLinearMap.toAddMonoidHom
  obtain ⟨m, hm, hmx⟩ := exists_den
    (fun t : (Fin 4 × D.what₂.Tau) × Fin 4 => γ₀.g.symm (Pi.single t.1 1) t.2)
  refine (Set.finite_le_nat (n * m)).subset ?_
  rintro p ⟨hp, hsp, hy⟩
  by_contra hlt
  have hlt' : n * m < p := not_le.1 hlt
  have hcop : Nat.Coprime (n * m) p := (Nat.coprime_of_lt_prime (by positivity) hlt' hp).symm
  have hcn : Nat.Coprime n p := Nat.Coprime.coprime_mul_right hcop
  have hcm : Nat.Coprime m p := Nat.Coprime.coprime_mul_left hcop
  obtain ⟨h1, h2⟩ := k.gaP_at p hp hsp
  have hP := k.pp_over p hp hsp
  apply hy
  unfold KapChoice.yP ordK IsoK.detRel
  rw [val_det_eq_one]
  · simp
  · intro i j
    obtain ⟨s, hs, hsx⟩ := h1 (m • γ₀.g.symm (Pi.single j 1)) (fun a => by
      have := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem ⟨_, hmx (j, a)⟩ (one_mem D)
      change ((m : D.host.E) * γ₀.g.symm (Pi.single j 1) a) * 1 ∈ D.host.AA0 at this
      simpa using this)
    obtain ⟨r, hr⟩ := hsx i
    refine val_le_one _ hP (Nat.Coprime.mul_left hs hcm) ?_
    have hi : IsIntegral ℤ (algebraMap (𝓞 D.host.K) D.host.K r) := r.2
    rw [hr, map_nsmul, Pi.smul_apply, nsmul_eq_mul, ← mul_assoc] at hi
    simpa using hi
  · intro i j
    obtain ⟨s, hs, hsx⟩ := h2 (Pi.single j 1) (fun w => by
      by_cases hw : w = j
      · subst hw; simp
      · simp [hw])
    have hi := hnx (s • (k.gaP p).g.symm (Pi.single j 1)) (fun a => by
      have := hsx a
      simpa using this) i
    refine val_le_one _ hP (Nat.Coprime.mul_left hcn hs) ?_
    rw [map_nsmul, Pi.smul_apply, nsmul_eq_mul, ← mul_assoc] at hi
    simpa using hi

end GlobalTheory.ExponentsFinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeTranslateHarrisTaylorPullbackBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeTranslateHarrisTaylorPullbackBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPel.HT.Hecke.PullHecke

theorem isGaloisCover_of_isPullback {X Y X' Y' : Scheme.{0}} {Ga Ga' : Type} [Group Ga] [Group Ga']
    {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y} {ρ' : Ga' → (X' ⟶ X')} {π' : X' ⟶ Y'} {u : X' ⟶ X} {v : Y' ⟶ Y}
    (h : GlobalTheory.ZM.IsGaloisCover Ga ρ π) (hp : IsPullback u π' π v)
    (one' : ρ' 1 = 𝟙 X') (mul' : ∀ a c, ρ' (a * c) = ρ' a ≫ ρ' c) (inj' : Function.Injective ρ')
    (hπ : ∀ a, ρ' a ≫ π' = π')
    (up : ∀ a', ∃ a, ρ' a' ≫ u = u ≫ ρ a) (down : ∀ a, ∃ a', ρ' a' ≫ u = u ≫ ρ a) :
    GlobalTheory.ZM.IsGaloisCover Ga' ρ' π' := by
  refine
    { finite := ?_
      one := one'
      mul := mul'
      inv := hπ
      fin := MorphismProperty.of_isPullback (P := @IsFinite) hp h.fin
      etale := MorphismProperty.of_isPullback (P := @Etale) hp h.etale
      onto := MorphismProperty.of_isPullback (P := @Surjective) hp h.onto
      fibre := ?_ }
  · have := h.finite
    choose σ hσ using up
    refine Finite.of_injective σ fun a c e => inj' ?_
    exact hp.hom_ext (by rw [hσ, hσ, e]) (by rw [hπ, hπ])
  · intro K _ _ y y' e
    obtain ⟨a, ha, ha'⟩ := h.fibre K (y ≫ u) (y' ≫ u) (by simp only [Category.assoc, hp.w, reassoc_of% e])
    obtain ⟨a', ea'⟩ := down a
    have ex : y ≫ ρ' a' = y' := hp.hom_ext
      (by rw [Category.assoc, ea', ← Category.assoc, ha])
      (by rw [Category.assoc, hπ, e])
    refine ⟨a', ex, fun b' hb' => inj' ?_⟩
    obtain ⟨b, eb⟩ := up b'
    have hb'' : y ≫ ρ' b' = y' := hb'
    have hb : b = a := ha' b (by show (y ≫ u) ≫ ρ b = y' ≫ u; rw [Category.assoc, ← eb, ← Category.assoc, hb''])
    subst hb
    exact hp.hom_ext (by rw [eb, ea']) (by rw [hπ, hπ])

end GlobalTheory.UPel.HT.Hecke.PullHecke

namespace GlobalTheory.UPel.HT.Hecke.PullHecke

theorem transl_one {S : Scheme.{0}} {A : Over S} [GrpObj A] : transl (1 : 𝟙_ (Over S) ⟶ A) = 𝟙 A := by
  show 𝟙 A * (toUnit A ≫ 1) = 𝟙 A
  rw [MonObj.comp_one, _root_.mul_one]

theorem transl_mul {S : Scheme.{0}} {A : Over S} [GrpObj A] (a c : 𝟙_ (Over S) ⟶ A) :
    transl (a * c) = transl a ≫ transl c := by
  have e : transl a ≫ transl c = transl a * (toUnit A ≫ c) := by
    show transl a ≫ (𝟙 A * (toUnit A ≫ c)) = _
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (transl a ≫ toUnit A) (toUnit A)]
  rw [e]
  show 𝟙 A * (toUnit A ≫ (a * c)) = (𝟙 A * (toUnit A ≫ a)) * (toUnit A ≫ c)
  rw [MonObj.comp_mul, _root_.mul_assoc]

theorem transl_injective {S : Scheme.{0}} {A : Over S} [GrpObj A] {a c : 𝟙_ (Over S) ⟶ A}
    (h : (transl a).left = (transl c).left) : a = c := by
  have h' : transl a = transl c := Over.OverMorphism.ext h
  rw [← one_comp_transl a, h', one_comp_transl]

theorem grpScheme_square_hom_ext {S : Scheme.{0}} {A : Over S} {X : Scheme.{0}} (u u' : X ⟶ (A ⊗ A).left)
    (h₁ : u ≫ (fst A A).left = u' ≫ (fst A A).left) (h₂ : u ≫ (snd A A).left = u' ≫ (snd A A).left) : u = u' := by
  have hw : u' ≫ (A ⊗ A).hom = u ≫ (A ⊗ A).hom := by
    rw [← Over.w (fst A A), ← Category.assoc, ← h₁, Category.assoc]
  let U : Over.mk (u ≫ (A ⊗ A).hom) ⟶ A ⊗ A := Over.homMk u rfl
  let U' : Over.mk (u ≫ (A ⊗ A).hom) ⟶ A ⊗ A := Over.homMk u' hw
  have : U = U' := CartesianMonoidalCategory.hom_ext _ _ (Over.OverMorphism.ext h₁) (Over.OverMorphism.ext h₂)
  exact congrArg (fun z => z.left) this

theorem grpSchemeSquareProductMap_comp_fst {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (ψ : A ⟶ A') : sq2 ψ ≫ (fst A' A').left = (fst A A).left ≫ ψ.left := by
  show (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left ≫ _ = _
  rw [← Over.comp_left, lift_fst, Over.comp_left]

theorem grpSchemeSquareProductMap_comp_snd {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (ψ : A ⟶ A') : sq2 ψ ≫ (snd A' A').left = (snd A A).left ≫ ψ.left := by
  show (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left ≫ _ = _
  rw [← Over.comp_left, lift_snd, Over.comp_left]

theorem cls_heckePow {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) (h : (GlobalTheory.UPel.HT.Hecke.lbPow L n).IsLB) :
    GlobalTheory.CechPic.cls (GlobalTheory.UPel.HT.Hecke.lbPow L n) h = n • GlobalTheory.CechPic.cls L hL := by
  unfold GlobalTheory.UPel.HT.Hecke.lbPow at h ⊢
  rw [GlobalTheory.CechPic.cls_linComb hL]
  simp [GlobalTheory.CechPic.pull_id]

end GlobalTheory.UPel.HT.Hecke.PullHecke

namespace GlobalTheory.UPel.HT.Hecke.PullHecke

theorem isHecke_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R)
    (f : S' ⟶ S) (o : Obj b (N * k) s) (o' : Obj b N s) (ψ : o.A ⟶ o'.A) (o₁ : Obj b (N * k) (f ≫ s))
    (o₁' : Obj b N (f ≫ s)), IsHecke g c k N o o' ψ → ObjMap o₁ o f → ObjMap o₁' o' f →
    ∃ ψ₁ : o₁.A ⟶ o₁'.A, IsHecke g c k N o₁ o₁' ψ₁ := by
  intro p _ D R _ b g c k N _ _ _ S S' s f o o' ψ o₁ o₁' hH m m'
  obtain ⟨hmon, hlin, heta, hgal, ⟨hP⟩, hdvd⟩ := hH
  have w : (m.φ ≫ ψ.left) ≫ o'.A.hom = o₁.A.hom ≫ f := by
    rw [Category.assoc, Over.w]; exact m.cart.1.w
  let ψ₁ : o₁.A ⟶ o₁'.A := Over.homMk (m'.cart.1.lift (m.φ ≫ ψ.left) o₁.A.hom w) (m'.cart.1.lift_snd _ _ _)
  have hψ₁ : ψ₁.left ≫ m'.φ = m.φ ≫ ψ.left := m'.cart.1.lift_fst _ _ _
  have ext' : ∀ {T : Over S'} (x y : T ⟶ o₁'.A), x.left ≫ m'.φ = y.left ≫ m'.φ → x = y := fun x y e =>
    Over.OverMorphism.ext (m'.cart.1.hom_ext e (by rw [Over.w, Over.w]))

  have pa : ∀ {T : Over S'} (x : T ⟶ o₁.A), pushPt m'.cart.1.w (x ≫ ψ₁) = pushPt m.cart.1.w x ≫ ψ := fun x =>
    Over.OverMorphism.ext (by
      show (x ≫ ψ₁).left ≫ m'.φ = (x.left ≫ m.φ) ≫ ψ.left
      rw [Over.comp_left, Category.assoc, hψ₁, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ o₁.A),
      pushPt m.cart.1.w (x * y) = pushPt m.cart.1.w x * pushPt m.cart.1.w y := fun x y => map_mul (pushHom m.cart _) x y
  have pm' : ∀ {T : Over S'} (x y : T ⟶ o₁'.A),
      pushPt m'.cart.1.w (x * y) = pushPt m'.cart.1.w x * pushPt m'.cart.1.w y := fun x y => map_mul (pushHom m'.cart _) x y
  have inj' : ∀ {T : Over S'} {x y : T ⟶ o₁'.A}, pushPt m'.cart.1.w x = pushPt m'.cart.1.w y → x = y := fun e =>
    ext' _ _ (congrArg (fun z => z.left) e)
  haveI := hmon
  have hmon₁ : IsMonHom ψ₁ := by
    refine isMonHom_of_mul ψ₁ fun T x y => ?_
    apply inj'
    rw [pa, pm, MonObj.mul_comp, ← pa, ← pa, pm']

  have tc : ∀ z, (transl (o₁.eta z)).left ≫ m.φ = m.φ ≫ (transl (o.eta z)).left := by
    intro z
    have hu : pushPt m.cart.1.w (toUnit o₁.A ≫ o₁.eta z) = toUnit _ ≫ o.eta z := Over.OverMorphism.ext (by
      show (toUnit o₁.A ≫ o₁.eta z).left ≫ m.φ = (toUnit (Over.mk (o₁.A.hom ≫ f)) ≫ o.eta z).left
      rw [Over.comp_left, Over.comp_left, Category.assoc, m.eta]
      simp)
    have e : pushPt m.cart.1.w (transl (o₁.eta z)) = pushPt m.cart.1.w (𝟙 o₁.A) ≫ transl (o.eta z) := by
      show pushPt m.cart.1.w (𝟙 o₁.A * (toUnit o₁.A ≫ o₁.eta z)) =
        pushPt m.cart.1.w (𝟙 o₁.A) ≫ (𝟙 o.A * (toUnit o.A ≫ o.eta z))
      rw [pm, hu, MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (_ ≫ toUnit o.A) (toUnit _)]
    have e' : (transl (o₁.eta z)).left ≫ m.φ = ((𝟙 o₁.A : o₁.A ⟶ o₁.A).left ≫ m.φ) ≫ (transl (o.eta z)).left :=
      congrArg (fun z => z.left) e
    rw [e', Over.id_left, Category.id_comp]
  have hp : IsPullback m.φ ψ₁.left ψ.left m'.φ := by
    refine IsPullback.of_bot ?_ hψ₁.symm m'.cart.1
    rw [Over.w ψ₁, Over.w ψ]; exact m.cart.1
  refine ⟨ψ₁, hmon₁, fun c' => ?_, fun x => ?_, ?_, ?_, hdvd⟩
  · apply ext'
    have h₀ := congrArg (fun z => m.φ ≫ z.left) (hlin c')
    simp only [Over.comp_left, Category.assoc] at h₀ ⊢
    rw [hψ₁, m'.act, reassoc_of% hψ₁, reassoc_of% (m.act c')]
    exact h₀
  · apply ext'
    rw [m'.eta, heta]
    simp only [Over.comp_left, Category.assoc]
    rw [hψ₁, reassoc_of% (m.eta (g x))]
  · refine isGaloisCover_of_isPullback hgal hp ?_ (fun a c => ?_) (fun a c e => Subtype.ext (transl_injective e))
      (fun a => ?_) (fun a => ?_) (fun a => ?_)
    · show (transl 1).left = _
      rw [transl_one, Over.id_left]
    · show (transl (a.1 * c.1)).left = _
      rw [transl_mul, Over.comp_left]
    · obtain ⟨h, x, rfl⟩ := a
      have hi : (transl (o.eta (N • g x))).left ≫ ψ.left = ψ.left := hgal.inv ⟨_, mem_heckeSub o g N x⟩
      show (transl (o₁.eta (N • g x))).left ≫ ψ₁.left = ψ₁.left
      refine m'.cart.1.hom_ext ?_ ?_
      · rw [Category.assoc, hψ₁, ← Category.assoc, tc, Category.assoc, hi]
      · rw [Category.assoc, Over.w ψ₁, Over.w]
    · obtain ⟨h, x, rfl⟩ := a
      exact ⟨⟨_, mem_heckeSub o g N x⟩, tc _⟩
    · obtain ⟨h, x, rfl⟩ := a
      exact ⟨⟨_, mem_heckeSub o₁ g N x⟩, tc _⟩
  · have hs1 : m.φ₂ ≫ (fst o.A o.A).left = (fst o₁.A o₁.A).left ≫ m.φ := m.sq.1
    have hs2 : m.φ₂ ≫ (snd o.A o.A).left = (snd o₁.A o₁.A).left ≫ m.φ := m.sq.2
    have hn₀ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
    have hn₁ : (GlobalTheory.UPel.HT.Hecke.lbPow o₁.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hsq : sq2 ψ₁ ≫ m'.φ₂ = m.φ₂ ≫ sq2 ψ := by
      apply grpScheme_square_hom_ext
      · rw [Category.assoc, m'.sq.1, ← Category.assoc, grpSchemeSquareProductMap_comp_fst, Category.assoc, hψ₁, Category.assoc, grpSchemeSquareProductMap_comp_fst,
          ← Category.assoc m.φ₂, hs1, Category.assoc]
      · rw [Category.assoc, m'.sq.2, ← Category.assoc, grpSchemeSquareProductMap_comp_snd, Category.assoc, hψ₁, Category.assoc, grpSchemeSquareProductMap_comp_snd,
          ← Category.assoc m.φ₂, hs2, Category.assoc]
    have c₁ : GlobalTheory.CechPic.cls o₁.P o₁.isLB = GlobalTheory.CechPic.pull m.φ₂ (GlobalTheory.CechPic.cls o.P o.isLB) :=
      (GlobalTheory.CechPic.cls_eq_iff o₁.isLB (pull_isLB o.isLB _)).2 m.pol
    have c₁' : GlobalTheory.CechPic.cls o₁'.P o₁'.isLB = GlobalTheory.CechPic.pull m'.φ₂ (GlobalTheory.CechPic.cls o'.P o'.isLB) :=
      (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o'.isLB _)).2 m'.pol
    have c₀ : GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls o'.P o'.isLB) = (k ^ 2 / c) • GlobalTheory.CechPic.cls o.P o.isLB := by
      rw [← GlobalTheory.CechPic.cls_pull o'.isLB _ (pull_isLB o'.isLB _),
        ← (GlobalTheory.CechPic.cls_eq_iff hn₀ (pull_isLB o'.isLB _)).2 hP, cls_heckePow o.isLB]
    refine ⟨(GlobalTheory.CechPic.cls_eq_iff hn₁ (pull_isLB o₁'.isLB _)).1 ?_⟩
    rw [cls_heckePow o₁.isLB, GlobalTheory.CechPic.cls_pull o₁'.isLB, c₁, c₁', ← GlobalTheory.CechPic.pull_comp, hsq,
      GlobalTheory.CechPic.pull_comp, c₀, map_nsmul]

end GlobalTheory.UPel.HT.Hecke.PullHecke
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeTranslateHarrisTaylorPullbackBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHeckeTranslate_harrisTaylor_pullback_base : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R) (f : S' ⟶ S) (o : Obj b (N * k) s) (o' : Obj b N s) (ψ : o.A ⟶ o'.A) (o₁ : Obj b (N * k) (f ≫ s)) (o₁' : Obj b N (f ≫ s)), IsHecke g c k N o o' ψ → ObjMap o₁ o f → ObjMap o₁' o' f → ∃ ψ₁ : o₁.A ⟶ o₁'.A, IsHecke g c k N o₁ o₁' ψ₁ := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.PullHecke.isHecke_pull) | (exact GlobalTheory.UPel.HT.Hecke.PullHecke.isHecke_pull) | (intros; apply GlobalTheory.UPel.HT.Hecke.PullHecke.isHecke_pull  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingAdjointEqOfPullbackIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingAdjointEqOfPullbackIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.AdjPairing

theorem weilIs_adj_eq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → ∀ α β : A ⟶ A, IsMonHom α → IsMonHom β → LBIso (P.pull (lift (fst A A ≫ α) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ β)).left) → ∀ (n : ℤ) (T : Over S) (a b : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) P n (lift (a ≫ α) 1) (lift 1 b) c → Out.WeilIs (G2 A) P n (lift a 1) (lift 1 (b ≫ β)) c' → c = c' := by
  intro S A _ _ P hA hP α β hα hβ hiso n T a b c c' h h'
  let ψ₁ : G2 A ⟶ G2 A := lift (fst A A ≫ α) (snd A A)
  let ψ₂ : G2 A ⟶ G2 A := lift (fst A A) (snd A A ≫ β)
  haveI : IsMonHom ψ₁ := inferInstanceAs (IsMonHom (lift (fst A A ≫ α) (snd A A)))
  haveI : IsMonHom ψ₂ := inferInstanceAs (IsMonHom (lift (fst A A) (snd A A ≫ β)))
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hL : (P.pull ψ₁.left).IsLB := pull_isLB hP _
  have hx₁ : lift a 1 ≫ ψ₁ = lift (a ≫ α) 1 := by ext <;> simp [ψ₁]
  have hy₁ : lift 1 b ≫ ψ₁ = lift 1 b := by ext <;> simp [ψ₁]
  have hx₂ : lift a 1 ≫ ψ₂ = lift a 1 := by ext <;> simp [ψ₂]
  have hy₂ : lift 1 b ≫ ψ₂ = lift 1 (b ≫ β) := by ext <;> simp [ψ₂]
  have hw₁ : LBIso (lbPow (P.pull ψ₁.left) 1) (P.pull ψ₁.left) := lbIso_lbPow_one hL
  have hw₂ : LBIso (lbPow (P.pull ψ₁.left) 1) (P.pull ψ₂.left) :=
    LBIso.trans (isLB_lbPow hL 1) hL (pull_isLB hP _) (lbIso_lbPow_one hL) hiso
  have h1 := WeilIsogeny.weilIs_pull_hom (d := 1) (x := lift a 1) (y := lift 1 b)
    globalFns_holds hAA hL hP ψ₁ hw₁ (by rw [hx₁, hy₁]; exact h)
  have h2 := WeilIsogeny.weilIs_pull_hom (d := 1) (x := lift a 1) (y := lift 1 b)
    globalFns_holds hAA hL hP ψ₂ hw₂ (by rw [hx₂, hy₂]; exact h')
  rw [Nat.cast_one, _root_.mul_one] at h1 h2
  exact CommutatorPairing.weilIs_unique globalFns_holds hAA hL h1 h2

end GlobalTheory.AdjPairing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingAdjointEqOfPullbackIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_adjoint_eq_of_pullback_iso : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → ∀ α β : A ⟶ A, IsMonHom α → IsMonHom β → LBIso (P.pull (lift (fst A A ≫ α) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ β)).left) → ∀ (n : ℤ) (T : Over S) (a b : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) P n (lift (a ≫ α) 1) (lift 1 b) c → Out.WeilIs (G2 A) P n (lift a 1) (lift 1 (b ≫ β)) c' → c = c' := by
  first | (exact @GlobalTheory.AdjPairing.weilIs_adj_eq) | (exact GlobalTheory.AdjPairing.weilIs_adj_eq) | (intros; apply GlobalTheory.AdjPairing.weilIs_adj_eq  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfNumReads
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ColRows.NumReads

open Formalism.LatticeIndexTer (ph)

theorem ph_zero : ph 0 = 0 := by simp [ph]

theorem N_pred_le (N : NumDatum) (j : ℕ) (hj : j < N.R.m) : N.R.N ((j + 1) - 1) ≤ N.Nm := by
  unfold NumDatum.Nm Ranks.N
  rw [Nat.add_sub_cancel]
  have := Nat.mul_le_mul_right (N.R.t + 1) hj.le
  omega

theorem ofNum_reads : ∀ (N : NumDatum) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (δ : Code N) (T : ℕ)
    (Nc lam0 C0 ce Ch Sw C1 : ℝ) (H : N.NumFacts δ Nc lam0 C0 ce Ch Sw C1),
    Reads N eJ δ T (RecNums.ofNum N eJ δ T Nc lam0 C0 ce Ch Sw C1 H) := by
  intro N J _ eJ δ T Nc lam0 C0 ce Ch Sw C1 H
  refine ⟨?_, ?_, rfl, ?_, ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · intro z
    exact N.mem_topsPl z
  · intro t _
    rfl
  · intro j z
    have hle := N_pred_le N (eJ j).1 (eJ j).2
    show ∑ i : Fin N.Nm, ph (N.nuPad δ ((eJ j).1 + 1) z i) = _
    unfold NumDatum.nuPad
    have e : ∀ i : Fin N.Nm, ph (if i.1 < N.R.N ((eJ j).1 + 1 - 1) then ((N.nu δ ((eJ j).1 + 1) z i.1 : ℚ) : ℝ) else 0) =
        (if i.1 < N.R.N ((eJ j).1 + 1 - 1) then ph ((N.nu δ ((eJ j).1 + 1) z i.1 : ℚ) : ℝ) else 0) := by
      intro i
      split_ifs
      · rfl
      · exact ph_zero
    rw [Finset.sum_congr rfl (fun i _ => e i),
      NumDatum.sum_pad (fun i => ph ((N.nu δ ((eJ j).1 + 1) z i : ℚ) : ℝ)) hle, Nat.add_sub_cancel]
  · intro j z
    have hle := N_pred_le N (eJ j).1 (eJ j).2
    show ∑ i : Fin N.Nm, N.nuPad δ ((eJ j).1 + 1) z i = _
    unfold NumDatum.nuPad NumDatum.nuAbs
    rw [NumDatum.sum_pad (fun i => ((N.nu δ ((eJ j).1 + 1) z i : ℚ) : ℝ)) hle]
    push_cast
    rfl

end GlobalTheory.ColRows.NumReads
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjFiniteUnipotentMemOpenSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjFiniteUnipotentMemOpenSubgroup
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.FinConj

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem finEmb_eq_finGL (E : Type) [Field E] [NumberField E] (a : ℕ) (l : GL (Fin a) (Af E)) :
    finEmb E a l = finGL E a l := by
  have k1 : ∀ (c : Ad E) (x y : Af E), (c - sFin E y + sFin E x).1 = c.1 - 0 + 0 := fun _ _ _ => rfl
  have k2 : ∀ (c : Ad E) (x y : Af E), (c - sFin E y + sFin E x).2 = c.2 - y + x := fun _ _ _ => rfl
  apply (AdelicGLn.prodEquiv E a).injective
  rw [prodEquiv_finEmb]
  refine Prod.ext (Units.ext (Matrix.ext fun i j => ?_)) (Units.ext (Matrix.ext fun i j => ?_))
  · rw [AdelicGLn.prodEquiv_apply_fst]
    change (1 : Matrix (Fin a) (Fin a) (InfiniteAdeleRing E)) i j = ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (sFin E) ((1 : Matrix (Fin a) (Fin a) (Af E)) i j) + sFin E (l i j)).1
    rw [k1, sub_zero, add_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rfl
    · rfl
  · rw [AdelicGLn.prodEquiv_apply_snd]
    change (l : Matrix (Fin a) (Fin a) (Af E)) i j = ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (sFin E) ((1 : Matrix (Fin a) (Fin a) (Af E)) i j) + sFin E (l i j)).2
    rw [k2, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rw [adele_one_snd, sub_self, zero_add]
    · rw [adele_zero_snd, sub_self, zero_add]

theorem unip_eq_unipGL (E : Type) [Field E] [NumberField E] (a r : ℕ) (z : BlockIx a r → Ad E) :
    (unip z : GA E a) = unipGL z := Units.ext rfl

theorem exists_conj_unip_mem :
    ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ ω : Set (GA E a), IsCompact ω →
    ∃ M : ℕ, 0 < M ∧ ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
      ∀ z : BlockIx a r → Ad E, (∀ p, (z p).1 = 0) →
      (∀ p, ∃ c ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E, (z p).2 = (M : Af E) * c) →
      ∃ l ∈ L, (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k)⁻¹ * unip z *
        (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k) = finGL E a l := by
  intro E _ _ a r L hL ω hω
  set U : Subgroup (AdelicGLn.integralFiniteGL E a) := L.comap (AdelicGLn.integralFiniteGL E a).subtype
  have hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL E a)) := hL.preimage continuous_subtype_val
  obtain ⟨M, hM, h⟩ := exists_natCast_conj_unipGL_mem (K := E) (n := a) U hU hω r
  refine ⟨M, hM, fun b hb ρ hρ k hk z hz1 hz2 => ?_⟩
  obtain ⟨u, hu⟩ := h b hb ρ hρ k hk z hz1 hz2
  refine ⟨((u : AdelicGLn.integralFiniteGL E a) : GL (Fin a) (Af E)), u.2, ?_⟩
  rw [unip_eq_unipGL, ← finEmb_eq_finGL]
  exact hu

end GlobalTheory.FinConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjFiniteUnipotentMemOpenSubgroupStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_finiteUnipotent_mem_openSubgroup : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ ω : Set (GA E a), IsCompact ω →
    ∃ M : ℕ, 0 < M ∧ ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
      ∀ z : BlockIx a r → Ad E, (∀ p, (z p).1 = 0) →
      (∀ p, ∃ c ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E, (z p).2 = (M : Af E) * c) →
      ∃ l ∈ L, (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k)⁻¹ * unip z *
        (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k) = finGL E a l := by
  first | exact @GlobalTheory.FinConj.exists_conj_unip_mem | exact GlobalTheory.FinConj.exists_conj_unip_mem | (intros; apply GlobalTheory.FinConj.exists_conj_unip_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDivisionL1Bound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDivisionL1Bound
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem Wts.divided_weight_small_block_le_neg_three_mul {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N) (hH : W.Hyp) (hD : W.IsDiv) (τ : ι) :
    ∀ (k : ℕ) (hk : W.p + k < N), W.u1 τ ⟨W.p + k, hk⟩ ≤ -(3 * (N : ℤ)) := by
  have hT : (4 : ℤ) ≤ W.T := by have := hH.h1; omega
  intro k
  induction k with
  | zero =>
    intro hk
    have h1 := hH.kc_pos
    have h2 := hH.kc_lt
    have hg := ((GlobalTheory.T.dividedWeight_gaps_block_and_bar ι N W hH hD τ ⟨W.p - 1, by omega⟩ ⟨W.p + 0, hk⟩ (by simp; omega)).2.1 (by simp)).2
    have he := (GlobalTheory.T.dividedWeight_entries_signs_sizes ι N W hH hD τ ⟨W.p - 1, by omega⟩).2.1 (by simp; omega)
    have h3 := hH.h2.2
    have hN : (0 : ℤ) ≤ 24 * (N : ℤ) * W.T := by positivity
    have h4 : 0 ≤ W.u1 τ ⟨W.p - 1, by omega⟩ - W.u1 τ ⟨W.p + 0, hk⟩ - 3 * N := by
      by_contra hneg
      push_neg at hneg
      nlinarith
    linarith
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have hg := (GlobalTheory.T.dividedWeight_gaps_block_and_bar ι N W hH hD τ ⟨W.p + k, by omega⟩ ⟨W.p + (k + 1), hk⟩ (by simp; omega)).1 (by simp)
    have hN : (0 : ℤ) ≤ (W.T : ℤ) + W.Dd + 2 + 2 * N := by positivity
    linarith

theorem Wts.abs_u'_le {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N) (hH : W.Hyp) (hD : W.IsDiv) (τ : ι) (i : Fin N) :
    |W.u' τ i| ≤ |W.u1 τ i| := by
  unfold Wts.u'
  split_ifs with h
  · exact le_rfl
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (not_lt.mp h)
    have hlt : W.p + k < N := hk ▸ i.2
    have hi : i = ⟨W.p + k, hlt⟩ := Fin.ext hk
    have h1 := W.divided_weight_small_block_le_neg_three_mul hH hD τ k hlt
    rw [← hi] at h1
    have hN : (0 : ℤ) ≤ N := by positivity
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

theorem divided_weight_size : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → (W.T : ℝ) * l1 W.u1 ≤ l1 W.u + (Fintype.card ι : ℝ) * N * (W.c0 + 4 * N) ∧ l1 W.u' ≤ l1 W.u1 ∧ ∀ τ i, |W.u' τ i| ≤ |W.u1 τ i| := by
  intro ι _ N W hH hD
  refine ⟨?_, ?_, fun τ i => W.abs_u'_le hH hD τ i⟩
  · have key : ∀ τ i, (W.T : ℝ) * |(W.u1 τ i : ℝ)| ≤ |(W.u τ i : ℝ)| + (W.c0 + 4 * N) := by
      intro τ i
      have h1 := (GlobalTheory.T.dividedWeight_entries_signs_sizes ι N W hH hD τ i).1
      have h0 : (0 : ℤ) ≤ ((W.Dd : ℤ) + 1) * |W.u1 τ i| := by positivity
      have h2 : (W.T : ℤ) * |W.u1 τ i| ≤ |W.u τ i| + (W.c0 + 4 * N) := by nlinarith
      exact_mod_cast h2
    unfold l1
    calc (W.T : ℝ) * ∑ τ, ∑ i, |(W.u1 τ i : ℝ)|
        = ∑ τ, ∑ i, (W.T : ℝ) * |(W.u1 τ i : ℝ)| := by simp only [Finset.mul_sum]
      _ ≤ ∑ τ, ∑ i : Fin N, (|(W.u τ i : ℝ)| + (W.c0 + 4 * N)) :=
          Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => key τ i
      _ = _ := by
          simp only [Finset.sum_add_distrib (f := fun i => |(W.u _ i : ℝ)|), Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  · unfold l1
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => ?_
    exact_mod_cast W.abs_u'_le hH hD τ i

end GlobalTheory.MeanTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDivisionL1BoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_division_l1_bound : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → (W.T : ℝ) * l1 W.u1 ≤ l1 W.u + (Fintype.card ι : ℝ) * N * (W.c0 + 4 * N) ∧ l1 W.u' ≤ l1 W.u1 ∧ ∀ τ i, |W.u' τ i| ≤ |W.u1 τ i| := by
  first | exact @GlobalTheory.MeanTop.divided_weight_size | exact GlobalTheory.MeanTop.divided_weight_size | (intros; apply GlobalTheory.MeanTop.divided_weight_size <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamFramedOfPos
namespace GlobalTheory.FamilyFrames

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

theorem posDef_sum_dep {ι γ : Type} {κ : γ → Type} [Fintype ι] [Fintype γ] [∀ c, Fintype (κ c)]
    (G : ∀ c, Matrix (κ c) (κ c) ℂ) (hG : ∀ c, (G c).PosDef) (P : ∀ c, Matrix (κ c) ι ℂ)
    (hinj : ∀ x, (∀ c, P c *ᵥ x = 0) → x = 0) : (∑ c, (P c)ᴴ * G c * P c).PosDef := by
  have hs : ∀ c, ((P c)ᴴ * G c * P c).PosSemidef := fun c =>
    (hG c).posSemidef.conjTranspose_mul_mul_same (P c)
  have hS := Matrix.posSemidef_sum (s := Finset.univ) (fun c _ => hs c)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hS.1 fun x hx => ?_
  rw [Matrix.sum_mulVec, dotProduct_sum]
  obtain ⟨c, hc⟩ : ∃ c, P c *ᵥ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (hinj x hcon)
  refine Finset.sum_pos' (fun c _ => (hs c).dotProduct_mulVec_nonneg x) ⟨c, Finset.mem_univ c, ?_⟩
  have h1 := (hG c).dotProduct_mulVec_pos hc
  have h2 : star x ⬝ᵥ (((P c)ᴴ * G c * P c) *ᵥ x) = star (P c *ᵥ x) ⬝ᵥ (G c *ᵥ (P c *ᵥ x)) := by
    simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [h2]
  exact h1

section Generic

open Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem isSesq_pi {γ : Type} [Fintype γ] {V : γ → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module K (V c)]
    (H : ∀ c, InfinitePlace K → V c → V c → ℂ) (hH : ∀ c, IsSesq (H c)) :
    IsSesq (fun v (x y : ∀ c, V c) => ∑ c, H c v (x c) (y c)) := by
  intro v
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩
  · simp only [Pi.add_apply, fun c => (hH c v).1, Finset.sum_add_distrib]
  · simp only [Pi.add_apply, fun c => (hH c v).2.1, Finset.sum_add_distrib]
  · simp only [Pi.smul_apply, fun c => (hH c v).2.2.1, Finset.mul_sum]
  · simp only [Pi.smul_apply, fun c => (hH c v).2.2.2, Finset.mul_sum]

theorem posAt_pi {γ : Type} [Fintype γ] [DecidableEq γ] {V : γ → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module K (V c)]
    {κ : γ → Type} [∀ c, Fintype (κ c)] [∀ c, DecidableEq (κ c)] (b : ∀ c, Basis (κ c) K (V c))
    (H : ∀ c, InfinitePlace K → V c → V c → ℂ) (hH : ∀ c, IsSesq (H c)) (hP : ∀ c, PosAt (b c) (H c)) :
    PosAt (Pi.basis b) (fun v (x y : ∀ c, V c) => ∑ c, H c v (x c) (y c)) := by
  intro v
  let P : ∀ c, Matrix (κ c) (Σ c, κ c) ℂ := fun c => Matrix.of fun i s => vecAt (b c) v (Pi.basis b s c) i
  have hgram : gramOf (Pi.basis b) (fun (x y : ∀ c, V c) => ∑ c, H c v (x c) (y c)) =
      ∑ c, (P c)ᴴ * gramOf (b c) (H c v) * P c := by
    ext s t
    simp only [Matrix.sum_apply]
    rw [gramOf, Matrix.of_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sesq_eq_sum (hH c) (b c) v]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, P, Matrix.of_apply]
    rw [Finset.sum_comm]
    rfl
  rw [hgram]
  refine posDef_sum_dep _ (fun c => hP c v) P fun x hx => ?_
  funext ⟨c, i⟩
  have h1 := congrFun (hx c) i
  have h2 : ∀ s, P c i s = if s = ⟨c, i⟩ then 1 else 0 := by
    intro s
    have : P c i s = v.embedding ((Pi.basis b).repr (Pi.basis b s) ⟨c, i⟩) := by
      rw [Pi.basis_repr]
      rfl
    rw [this, Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  simpa [Matrix.mulVec, dotProduct, h2] using h1

theorem exists_frames {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (H : InfinitePlace K → V → V → ℂ) (hH : IsSesq H) (hP : PosAt b H) :
    ∃ (n : ℕ) (e : (Fin n → K) ≃ₗ[K] V) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) ∧
      ∀ v x, ((normAt (Pi.basisFun K (Fin n)) X v x ^ 2 : ℝ) : ℂ) = H v (e x) (e x) := by
  let e : (Fin (Fintype.card ι) → K) ≃ₗ[K] V := (b.reindex (Fintype.equivFin ι)).equivFun.symm
  let c := Pi.basisFun K (Fin (Fintype.card ι))
  have hH' := isSesq_comp hH e.toLinearMap
  have hP' := posAt_comp b c hH hP e.toLinearMap e.injective
  have hs := fun v => frameOf_spec (hP' v)
  refine ⟨_, e, fun v => frameOf (gramOf c fun x y => H v (e x) (e y)), fun v => (hs v).1, fun v x => ?_⟩
  rw [← majAt_self]
  have e1 := sesq_eq_sum (isSesq_maj c (fun v => frameOf (gramOf c fun x y => H v (e x) (e y)))) c v x x
  have e2 := sesq_eq_sum hH' c v x x
  rw [gramOf_maj] at e1
  refine e1.trans (Eq.trans ?_ e2.symm)
  have e3 := (hs v).2
  simp only [LinearEquiv.coe_coe] at e3 ⊢
  rw [e3]

theorem famFramed_of_pos (F : Formalism.L2.Col.GFam K) (h : F.Ok)
    (hpos : ∀ b (v : InfinitePlace K), ((F.mem b).gramV.map v.embedding).PosDef) : GlobalTheory.ColRows.FamFramed F h :=
  exists_frames (Pi.basis fun b => (F.mem b).hB (h b)) _
    (isSesq_pi (fun b v (φ ψ : (F.mem b).EqFun) => (F.mem b).ipAt (h b) v φ ψ) fun b => (F.mem b).isSesq_ipAt (h b))
    (posAt_pi _ (fun b v (φ ψ : (F.mem b).EqFun) => (F.mem b).ipAt (h b) v φ ψ) (fun b => (F.mem b).isSesq_ipAt (h b))
      fun b => (F.mem b).posAt_ipAt (h b) (hpos b) _)

end Generic

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

theorem famFramed_chF : ∀ (X : Fields) (hX : X.Ok) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (j : ℕ) (h : (chF W sel mu I u j).Ok), FamFramed (chF W sel mu I u j) h := by
  intro X hX Pr R W _ sel Sg mu I u j h
  exact famFramed_of_pos _ h fun _ v =>
    (roundPk_ratP (W.lamTrue u j) (fun d : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := Pr.vGs) => d.1.Lsh) hX).pos v

end GlobalTheory.FamilyFrames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColsInIsometry
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

noncomputable section

namespace GlobalTheory.ColFirstIso

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S S' : GSD K}

def clEquiv (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D) (hs : ∀ g d, eD (g • d) = eG g • eD d) : S'.Cl ≃ S.Cl :=
  Quotient.congr eD fun a b => by
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨eG g, (hs g b).symm⟩
    · rintro ⟨g, hg⟩
      refine ⟨eG.symm g, eD.injective ?_⟩
      have hg' : g • eD b = eD a := hg
      show eD (eG.symm g • b) = eD a
      rw [hs, MulEquiv.apply_symm_apply, hg']

theorem clEquiv_cls (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D) (hs : ∀ g d, eD (g • d) = eG g • eD d) (d : S'.D) :
    clEquiv eG eD hs (S'.cls d) = S.cls (eD d) := rfl

theorem card_stab (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D) (hs : ∀ g d, eD (g • d) = eG g • eD d) (d : S'.D) :
    Nat.card (MulAction.stabilizer S'.G d) = Nat.card (MulAction.stabilizer S.G (eD d)) := by
  refine Nat.card_congr (eG.toEquiv.subtypeEquiv fun g => ?_)
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  show _ ↔ eG g • eD d = eD d
  rw [← hs, eD.injective.eq_iff]

theorem ipAt_transport (R : S.Rat) (h : S.Ok) (h' : S'.Ok) (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D)
    (hs : ∀ g d, eD (g • d) = eG g • eD d) (v : InfinitePlace K) (φ : S.EqFun) (φ' : S'.D → S'.V)
    (hp : ∀ d, S'.pairAt v (φ' d) (φ' d) = S.pairAt v ((φ : S.D → S.V) (eD d)) ((φ : S.D → S.V) (eD d))) :
    S'.ipAt h' v φ' φ' = S.ipAt h v φ φ := by
  let e := clEquiv eG eD hs
  let s : S.Sec :=
    { rep := fun c => eD (S'.outSec.rep (e.symm c))
      spec := fun c => by
        rw [← clEquiv_cls eG eD hs, S'.outSec.spec]
        exact e.apply_symm_apply c }
  rw [R.ipAt_indep h s v φ φ]
  let _ := h.fintypeCl
  let _ := h'.fintypeCl
  unfold GSD.ipAt
  refine Fintype.sum_equiv e _ _ fun c => ?_
  have h1 : s.rep (e c) = eD (S'.outSec.rep c) := by
    show eD (S'.outSec.rep (e.symm (e c))) = _
    rw [e.symm_apply_apply]
  rw [h1, S'.wt_eq h' S'.outSec c, card_stab eG eD hs, hp]

end Generic

section Frames

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

def decoEquiv (hQ : Q = ∅) : DecoF X.E n ST SG Q ≃ DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) where
  toFun := DecoF.deco
  invFun d := ⟨(d, fun _ => 1), fun P => absurd P.2 (by simp [hQ])⟩
  left_inv p := Subtype.ext (Prod.ext rfl (funext fun P => absurd P.2 (by simp [hQ])))
  right_inv _ := rfl

def grpEquiv (hQ : Q = ∅) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) : FrmG Λ Θ ≃* FormG Λ where
  toFun g := (g.1, g.2.1)
  invFun g := (g.1, g.2, 1)
  left_inv g := Prod.ext rfl (Prod.ext rfl (Subtype.ext (funext fun P => absurd P.2 (by simp [hQ]))))
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem ipAt_frm (hQ : Q = ∅) (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ Λ' : LevFam X.E X.K n SG) (hΛ : Λ' = Λ)
    (Θ : LevQFam X.E X.K n Q) (R : (formGSD C Λ).Rat) (h : (formGSD C Λ).Ok)
    (h' : (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ' Θ).Ok) (v : InfinitePlace X.K) (φ : (formGSD C Λ).EqFun) :
    (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ' Θ).ipAt h' v (fun p => (φ : _ → C.V) (DecoF.deco p))
      (fun p => (φ : _ → C.V) (DecoF.deco p)) = (formGSD C Λ).ipAt h v φ φ := by
  subst hΛ
  exact ipAt_transport R h h' (grpEquiv hQ Λ' Θ) (decoEquiv hQ) (fun _ _ => rfl) v φ _ fun _ => rfl

end Frames

theorem qe_one {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} :
    QE sel ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
  have h : Qprime ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
    change Qprime (1 : Chr X.F X.E X.K) = ∅
    ext v
    simp [Qprime, MonoidHom.ker_one]
  unfold QE
  split_ifs with hf
  · rw [(Set.Finite.toFinset_eq_empty (h := hf)).2 h]
    rfl
  · rfl

theorem colsIn_isometry : ∀ (X : Fields) (hX : X.Ok) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (hL : I.Ok Ch sel mu cst G m2) (u : Pr.Word) (h : (chF W sel mu I u 0).Ok), mu = 1 → (∀ v, IsUnit ((MramH W Ch hX u).X v).det) ∧ ∀ (v : InfinitePlace X.K) (x : Fin (ramDim W Ch hX u) → X.K), ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K (Fin (ramDim W Ch hX u))) (MramH W Ch hX u).X v x ^ 2 : ℝ) : ℂ) = famIpAt (chF W sel mu I u 0) h v (colsIn W Ch hX sel mu cst I hL u x) (colsIn W Ch hX sel mu cst I hL u x) := by
  intro X hX Pr R W Ch sel Sg mu cst I G m2 hL u h hmu
  refine ⟨(colPosH W Ch hX u 0).frameOK_sub (MramV W Ch u) (MramL W Ch u), fun v x => ?_⟩
  have hQ : QE sel (mu : Chr X.F X.E X.K) = ∅ := by
    subst hmu
    exact qe_one sel
  obtain ⟨b, hb⟩ := hL.zero_uniq
  have h1 : famIpAt (chF W sel mu I u 0) h v (colsIn W Ch hX sel mu cst I hL u x) (colsIn W Ch hX sel mu cst I hL u x) =
      (colGSD W Ch u 0).ipAt (colOk W Ch hX u 0) v (colOfCoord W Ch hX u x) (colOfCoord W Ch hX u x) := by
    unfold famIpAt
    rw [Fintype.sum_eq_single b fun b' hb' => absurd (hb b') hb']
    exact ipAt_frm hQ (colVal W u 0 (Pr.vT u) Pr.vGs) (colLev Ch 0) (I.levG 0 b) (hL.zero_G b) (I.levQ 0 b)
      (colRat W Ch hX u 0) (colOk W Ch hX u 0) (h b) v (colOfCoord W Ch hX u x)
  rw [h1, ← (colRat W Ch hX u 0).maj_eq]
  have h2 := (colPosH W Ch hX u 0).sub_maj (MramV W Ch u) v ((ramBas W Ch hX u).equivFun.symm x)
    ((ramBas W Ch hX u).equivFun.symm x)
  rw [thl_majAt_coord, LinearEquiv.apply_symm_apply] at h2
  refine Eq.trans ?_ h2
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity)), Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rfl

end GlobalTheory.ColFirstIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntegersHenselianFiniteResidue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntegersHenselianFiniteResidue
open IsDedekindDomain IsLocalRing

namespace GlobalTheory.IntAdicHensel

theorem henselianLocalRing_and_finite_residueField :
    ∀ (v : HeightOneSpectrum ℤ), HenselianLocalRing (v.adicCompletionIntegers ℚ) ∧
      Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := by
  intro v
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers ℚ)
  haveI : IsPrecomplete (maximalIdeal (v.adicCompletionIntegers ℚ)) (v.adicCompletionIntegers ℚ) :=
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.completion_integers_precomplete v hϖ
  haveI : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers ℚ)) (v.adicCompletionIntegers ℚ) := {}
  haveI := IsAdicComplete.henselianRing (v.adicCompletionIntegers ℚ)
    (maximalIdeal (v.adicCompletionIntegers ℚ))
  refine ⟨GlobalTheory.henselianLocalRing_of_henselianRing _, ?_⟩
  haveI : Finite (ℤ ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  exact Finite.of_equiv _ (GroundTheory.Global.residueFieldEquiv (K := ℚ) v).toEquiv

end GlobalTheory.IntAdicHensel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntegersHenselianFiniteResidueStatement
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicIntegers_henselian_finiteResidue : ∀ (v : HeightOneSpectrum ℤ), HenselianLocalRing (v.adicCompletionIntegers ℚ) ∧ Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := by
  first | (exact @GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField) | (exact GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField) | (intros; apply GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField <;> assumption)
end
end
