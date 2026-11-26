module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.ExistsStalkFactor
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FrobNSucc

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.PullbackFirstFiltrationPrimitive
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord.HasseL

variable {p : ℕ} [Fact p.Prime]

private theorem sub_dual (k : Type) [Field k] : Subsingleton (PrimeSpectrum (DualNumber k)) := by
  have key : ∀ (P : PrimeSpectrum (DualNumber k)) (x : DualNumber k), x ∈ P.asIdeal ↔ x.fst = 0 := by
    intro P x
    have hε : (DualNumber.eps : DualNumber k) ∈ P.asIdeal :=
      P.2.mem_of_pow_mem 2 (by rw [pow_two, DualNumber.eps_mul_eps]; exact P.asIdeal.zero_mem)
    constructor
    · intro hx
      by_contra h0
      have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 h0)
      exact P.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)
    · intro h0
      have e : x = (TrivSqZeroExt.inl x.snd : DualNumber k) * DualNumber.eps := by
        apply TrivSqZeroExt.ext
        · rw [TrivSqZeroExt.fst_mul, h0, DualNumber.fst_eps, mul_zero]
        · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, DualNumber.snd_eps, DualNumber.fst_eps]
          simp
      rw [e]
      exact P.asIdeal.mul_mem_left _ hε
  exact ⟨fun P Q => PrimeSpectrum.ext (Ideal.ext fun x => (key P x).trans (key Q x).symm)⟩

private theorem cancel_sp {k T : Type} [Field k] [CommRing T] (j : DualNumber k →+* T) (hj : Function.Injective j)
    {Y : Scheme.{0}} {g₁ g₂ : Sp (DualNumber k) ⟶ Y} (e : spMap j ≫ g₁ = spMap j ≫ g₂) : g₁ = g₂ := by
  haveI hs : Subsingleton (Sp (DualNumber k)) := sub_dual k
  haveI : Nontrivial T := hj.nontrivial
  obtain ⟨t⟩ : Nonempty (Sp T) := inferInstanceAs (Nonempty (PrimeSpectrum T))
  let x : Sp (DualNumber k) := spMap j t
  have hxy : g₁ x = g₂ x := by
    have := congrArg (fun g : Sp T ⟶ Y => g t) e
    simpa [x] using this
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := g₁ x) (U := ⊤) trivial
  have r1 : Set.range g₁ ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z x, Scheme.Opens.range_ι]
    exact hy
  have r2 : Set.range g₂ ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z x, ← hxy, Scheme.Opens.range_ι]
    exact hy
  haveI : IsAffine U.toScheme := hU
  have f₁ := IsOpenImmersion.lift_fac U.ι g₁ r1
  have f₂ := IsOpenImmersion.lift_fac U.ι g₂ r2
  set h₁ := IsOpenImmersion.lift U.ι g₁ r1
  set h₂ := IsOpenImmersion.lift U.ι g₂ r2
  have e' : spMap j ≫ h₁ = spMap j ≫ h₂ := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, f₁, f₂, e]
  have hm : Mono (Scheme.Hom.appTop (spMap j)) := by
    have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom j)
    have hi : Mono (CommRingCat.ofHom j) := ConcreteCategory.mono_of_injective _ hj
    have : Mono (Scheme.Hom.appTop (spMap j) ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom) := by
      change Mono (Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom j)) ≫ _)
      rw [n]; exact mono_comp _ _
    exact mono_of_mono _ (Scheme.ΓSpecIso (CommRingCat.of T)).hom
  have hh : h₁ = h₂ := by
    apply ext_of_isAffine
    rw [← cancel_mono (Scheme.Hom.appTop (spMap j))]
    have := congrArg Scheme.Hom.appTop e'
    simpa using this
  rw [← f₁, ← f₂, hh]

private theorem frobN_nat {X Y : Scheme.{0}} (hX : (p : Γ(X, ⊤)) = 0) (hY : (p : Γ(Y, ⊤)) = 0) (g : Y ⟶ X) (f : ℕ) :
    frobN p Y hY f ≫ g = g ≫ frobN p X hX f := by
  induction f with
  | zero => simp [frobN]
  | succ n ih =>
    simp only [frobN, Category.assoc, ih]
    rw [← Category.assoc, GlobalTheory.VB.frob_naturality p hX g hY, Category.assoc]

private theorem frobN_sp (T : Type) [CommRing T] (hT : (p : T) = 0) (h : (p : Γ(Sp T, ⊤)) = 0) (f : ℕ) :
    ∃ φ : T →+* T, (∀ x, φ x = x ^ p ^ f) ∧ frobN p (Sp T) h f = spMap φ := by
  induction f with
  | zero => exact ⟨RingHom.id T, fun x => by simp, by rw [frobN]; exact (spMap_id T).symm⟩
  | succ n ih =>
    obtain ⟨φ, h1, h2⟩ := ih
    refine ⟨(frobR p T hT).comp φ, fun x => ?_, ?_⟩
    · rw [RingHom.comp_apply, frobR_apply, h1, pow_succ, pow_mul]
    · rw [frobN, h2, frob_sp p T hT h, GlobalTheory.Cris.spMap_comp]

end UpperTheory.Gal.Ord.HasseL

namespace UpperTheory.Gal.Ord.HasseL

variable {p : ℕ} [Fact p.Prime]

private theorem const_of {k : Type} [Field k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] (ψ : A.left ⟶ A.left)
    (a : A ⟶ A) [IsMonHom a] (f : ℕ) (ha : frobN p A.left (cast_left p k hk A) f ≫ ψ = a.left)
    {T : Type} [CommRing T] [Algebra k T] (τ : T →ₐ[k] DualNumber k) (j : DualNumber k →+* T)
    (u : Over.mk (spMap (algebraMap k T)) ⟶ A) (hj : Function.Injective j) (hq : ∀ x, j (τ x) = x ^ p ^ f)
    (hu : u ≫ a = 1) (v : epsR k ⟶ A) (hv : IsTangent v) (hτ : spMap (τ : T →+* DualNumber k) ≫ u.left = v.left) :
    IsConst (v.left ≫ ψ) := by
  have hT : (p : T) = 0 := by
    have := congrArg (algebraMap k T) hk
    simpa using this
  have hXT := cast_left p T hT (Over.mk (𝟙 (Sp T)))
  have hXk := cast_left p k hk (Over.mk (𝟙 (Sp k)))
  have hA := cast_left p k hk A
  obtain ⟨φ, hφ1, hφ2⟩ := frobN_sp (p := p) T hT hXT f
  obtain ⟨φk, hk1, hk2⟩ := frobN_sp (p := p) k hk hXk f
  have hjτ : φ = j.comp (τ : T →+* DualNumber k) := RingHom.ext fun x => by
    rw [hφ1, RingHom.comp_apply]; exact (hq x).symm
  have hone : (1 : Over.mk (spMap (algebraMap k T)) ⟶ A).left = spMap (algebraMap k T) ≫ η[A].left := by
    simp [Hom.one_def]

  have hR : spMap j ≫ v.left ≫ ψ = spMap (algebraMap k T) ≫ η[A].left := by
    have e1 : spMap j ≫ v.left = u.left ≫ frobN p A.left hA f := by
      rw [← hτ, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, ← hjτ, ← hφ2]
      exact frobN_nat hA hXT u.left f
    rw [← Category.assoc, e1, Category.assoc, ha, ← Over.comp_left, hu, hone]

  have hL : spMap j ≫ spMap ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ v.left ≫ ψ =
      spMap (algebraMap k T) ≫ η[A].left := by
    have c : j.comp (algebraMap k (DualNumber k)) = (algebraMap k T).comp φk := RingHom.ext fun c => by
      have := hq (algebraMap k T c)
      rw [AlgHom.commutes] at this
      rw [RingHom.comp_apply, this, RingHom.comp_apply, hk1, map_pow]
    have e0 : η[A].left ≫ frobN p A.left hA f = frobN p (Sp k) hXk f ≫ η[A].left :=
      (frobN_nat hA hXk η[A].left f).symm
    have e2 : η[A].left ≫ a.left = η[A].left := by
      rw [← Over.comp_left, IsMonHom.one_hom]
    have e3 : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = η[A].left := hv
    have e4 : spMap j ≫ spMap (algebraMap k (DualNumber k)) = spMap (algebraMap k T) ≫ spMap φk := by
      rw [← GlobalTheory.Cris.spMap_comp, c, GlobalTheory.Cris.spMap_comp]
    have e5 : spMap φk ≫ η[A].left ≫ ψ = η[A].left := by
      rw [← hk2, ← Category.assoc, ← e0, Category.assoc, ha, e2]
    have e6 : spMap j ≫ spMap ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ v.left ≫ ψ =
        (spMap j ≫ spMap (algebraMap k (DualNumber k))) ≫ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left) ≫ ψ := by
      rw [GlobalTheory.Cris.spMap_comp]
      simp only [Category.assoc]
    rw [e6, e3, e4, Category.assoc, e5]
  exact cancel_sp j hj (by rw [hL, hR])

end UpperTheory.Gal.Ord.HasseL

namespace UpperTheory.Gal.Ord.HasseL

variable {p : ℕ} [Fact p.Prime]

private theorem eps_pull {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] {σ : k →+* k} {ψ : A.left ⟶ A.left}
    (m : SMor A σ ψ) (E : A ⟶ A) [IsMonHom E] (e : ψ ≫ E.left = E.left ≫ ψ) (h : HdR A) (x : primDR A) :
    h (m.pull (primPull (dp0 k) (𝟙 _) E x)) = push (dp0 k) (𝟙 _) E h (m.pull x) := by
  rw [push_apply]
  have c := (homMor (dp0 k) (𝟙 _) E).comp m
  have e1 : primPull (dp0 k) (𝟙 _) E (m.pull x) = c.pull x :=
    GrpMor.pull_pull m (homMor (dp0 k) (𝟙 _) E) c (fun _ ↦ rfl) e.symm x
  have e2 : m.pull (primPull (dp0 k) (𝟙 _) E x) = c.pull x :=
    GrpMor.pull_pull (homMor (dp0 k) (𝟙 _) E) m c (fun _ ↦ rfl) rfl x
  rw [e1, e2]

private theorem pullback_first_filtration_primitive {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] {σ : k →+* k} {ψ : A.left ⟶ A.left}
    (m : SMor A σ ψ) {x : primDR A} (hx : x ∈ PrimitiveSubmodule A) : m.pull x ∈ PrimitiveSubmodule A :=
  m.isMor.pullback1_mem_hodgeFiltration hx

end UpperTheory.Gal.Ord.HasseL

open UpperTheory.Gal.Ord.HasseL in
theorem UpperTheory.Gal.Ord.hasse :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      ∀ (σ : k →+* k), Function.Bijective σ → ∀ (ψ : o.A.left ⟶ o.A.left) (m : SMor o.A σ ψ), frobN p o.A.left (cast_left p k hk o.A) f ≫ ψ = (o.act.act (algebraMap (𝓞 D.F) D.O π.a)).left →
      ∀ v : epsR k ⟶ o.A, IsTangent v → v ≠ 1 → IsDeep o w (p ^ f) v → ∀ x ∈ PrimitiveSubmodule o.A, m.pull (coh o π.ε x) = 0 := by
  intro p _ D R _ b N hN hNp hm k _ _ hk β o i w f hw hnorm hf π σ hσ ψ m ha v hv hv1 hdeep x hx
  obtain ⟨T, _, _, τ, j, u, hj, hq, hku, hτ⟩ := hdeep
  have hab := o.ab
  obtain ⟨g, hg⟩ := GlobalTheory.AbFieldDim.exists_smoothOfRelativeDimension k o.A hab
  have HL : LieExact o.A := GlobalTheory.T.hodgeLieSequence_exact_abelianScheme GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations
    GlobalTheory.AbCoh.abelianHodgeDeRham k o.A g hab hg
  haveI := hab.smooth
  haveI : AlgebraicGeometry.IsReduced o.A.left := GlobalTheory.isReduced_of_smooth_of_isReduced o.A.hom
  have hA := cast_left p k hk o.A
  haveI hEm : IsMonHom (o.act.act (algebraMap (𝓞 D.F) D.O π.ε)) := o.act.hom _
  haveI hAm : IsMonHom (o.act.act (algebraMap (𝓞 D.F) D.O π.a)) := o.act.hom _

  have hconst : IsConst (v.left ≫ ψ) :=
    const_of hk o.A ψ (o.act.act (algebraMap (𝓞 D.F) D.O π.a)) f ha τ j u hj hq (hku _ π.mem) v hv hτ
  obtain ⟨h₁, hl₁⟩ := HL.2 v hv
  have hforms := (UpperTheory.Gal.Ord.tan k o.A hab σ ψ m hσ.2 v hv).2 hconst
  have hz₁ : ∀ z ∈ PrimitiveSubmodule o.A, h₁ (m.pull z) = 0 := by
    rintro ⟨c, hc⟩ hzF
    have hc' : c ∈ F1 (o.A.hom ≫ 𝟙 _) := hzF
    rw [hodgeFiltration_eq_range] at hc'
    obtain ⟨fm, rfl⟩ := hc'
    have hp : Form.cl _ (m.isMor.pullForm fm) ∈ primDR o.A := by
      rw [IsMor.cl_pullForm]
      exact m.pullback_mem_primitive hc
    have e : m.pull ⟨_, hc⟩ = ⟨_, hp⟩ := Subtype.ext (IsMor.cl_pullForm _ _).symm
    rw [e, hl₁.2, hforms fm hc]

  let τ' : epsR k ⟶ Over.mk (spMap (algebraMap k T)) := Over.homMk (spMap (τ : T →+* DualNumber k)) (by
    simp only [Over.mk_hom]
    rw [← GlobalTheory.Cris.spMap_comp]
    congr 1
    exact τ.comp_algebraMap)
  have hvτ : v = τ' ≫ u := Over.OverMorphism.ext (by simpa [τ'] using hτ.symm)
  have hkill : ∀ c ∈ w, v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => by
    rw [hvτ, Category.assoc, hku c hc, MonObj.comp_one]
  have hvE : v ≫ o.act.act (algebraMap (𝓞 D.F) D.O π.ε) = v := by
    have e : o.act.act (algebraMap (𝓞 D.F) D.O π.ε) = o.act.act (algebraMap (𝓞 D.F) D.O (π.ε - 1)) * 𝟙 o.A := by
      rw [← o.act.one, ← o.act.add, ← map_one (algebraMap (𝓞 D.F) D.O), ← map_add (f := _), sub_add_cancel]
    rw [e, MonObj.comp_mul, hkill _ π.one, Category.comp_id, _root_.one_mul]
  have hlE : IsLieImage (hom o π.ε h₁) v := by
    have := hl₁.push (o.act.act (algebraMap (𝓞 D.F) D.O π.ε))
    rw [hvE] at this
    exact this
  have hd₁ : hom o π.ε h₁ - h₁ ∈ Fil o.A := hlE.sub_mem hl₁
  have hn₁ : h₁ ∉ Fil o.A := fun hh => hv1 ((HL.1 h₁).unique hl₁ (isLieImage_one_iff.2 hh))
  obtain ⟨-, ⟨h₀, -, hall⟩, -⟩ := UpperTheory.Gal.Ord.lie p D R b N hN hNp hm k hk β o i w f hw hnorm hf π
  obtain ⟨l₀, hl₀⟩ := hall h₁
  have hd₀ : h₁ - l₀ • hom o π.ε h₀ ∈ Fil o.A := by
    have := Submodule.sub_mem _ hl₀ hd₁
    have e : hom o π.ε h₁ - l₀ • hom o π.ε h₀ - (hom o π.ε h₁ - h₁) = h₁ - l₀ • hom o π.ε h₀ := by abel
    rwa [e] at this
  have hne : l₀ ≠ 0 := fun e => hn₁ (by simpa [e] using hd₀)

  have hcomm : ψ ≫ (o.act.act (algebraMap (𝓞 D.F) D.O π.ε)).left = (o.act.act (algebraMap (𝓞 D.F) D.O π.ε)).left ≫ ψ := by
    haveI := (UpperTheory.Gal.Ord.epi p o.A.left hA).2 f
    rw [← cancel_epi (frobN p o.A.left hA f), ← Category.assoc, ha, ← Category.assoc,
      frobN_nat hA hA (o.act.act (algebraMap (𝓞 D.F) D.O π.ε)).left f, Category.assoc, ha,
      ← Over.comp_left, ← Over.comp_left, ← o.act.mul, ← o.act.mul, ← map_mul, ← map_mul, mul_comm]
  have hz : ∀ z ∈ PrimitiveSubmodule o.A, hom o π.ε h₀ (m.pull z) = 0 := fun z hzF => by
    have e := (Submodule.mem_dualAnnihilator _).1 hd₀ _ (pullback_first_filtration_primitive m hzF)
    rw [LinearMap.sub_apply, hz₁ z hzF, LinearMap.smul_apply, zero_sub, neg_eq_zero, smul_eq_mul] at e
    exact (mul_eq_zero.1 e).resolve_left hne
  refine (Module.forall_dual_apply_eq_zero_iff k _).1 fun h => ?_
  obtain ⟨l, hl⟩ := hall h
  have e1 : h (m.pull (coh o π.ε x)) = hom o π.ε h (m.pull x) :=
    eps_pull m (o.act.act (algebraMap (𝓞 D.F) D.O π.ε)) hcomm h x
  have e2 := (Submodule.mem_dualAnnihilator _).1 hl _ (pullback_first_filtration_primitive m hx)
  rw [LinearMap.sub_apply, LinearMap.smul_apply, hz x hx, smul_zero, sub_zero] at e2
  rw [e1, e2]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.RankV
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.FrobAdjoint

theorem UpperTheory.Gal.Ord.rankV :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (σ : k →+* k) (V : A.left ⟶ A.left) (m : SMor A σ V), (∀ x, σ x ^ p = x) →
      GlobalTheory.VB.frob A.left p (cast_left p k hk A) ≫ V = ((𝟙 A) ^ p : A ⟶ A).left → ∀ y, m.pull y = 0 → ∃ z, frobDR p k hk A z = y := by
  intro p _ k _ _ hk A _ _ hA σ V m hσ hV y hy
  obtain ⟨e, he, -⟩ := GlobalTheory.deRhamVectorExtension p
  have hn : IsNilpotent (p : k) := ⟨1, by rw [pow_one, hk]⟩
  obtain ⟨g, hg⟩ : ∃ g, SmoothOfRelativeDimension g A.hom := GlobalTheory.T.abelianScheme_specField_smoothOfRelativeDimension k A hA
  obtain ⟨G, t, -⟩ := GlobalTheory.AbelianTower.exists_pDivGroup_tower p k hn A g hA hg
  let A₁ := (Over.pullback (spMap (frobR p k hk))).obj A
  have hπ : IsGrpPullback A₁ A _ _ := isGrpPullback_pullback A (spMap (frobR p k hk))
  have hA₁ : IsAbelianScheme A₁ := isAbelianScheme_pullback_obj _ A hA
  obtain ⟨F, hFm, hF⟩ := GlobalTheory.T.exists_relativeFrobenius_grpScheme_charP p k hk A A₁ _ hπ
  obtain ⟨t₁, ht⟩ := exists_tower hk t hπ
  have mπ := grpMor_of_isGrpPullback hπ
  have hid : (frobR p k hk).comp σ = RingHom.id k := RingHom.ext fun x => (frobR_apply p k hk _).trans (hσ x)
  have hb : spMap (frobR p k hk) ≫ spMap σ = 𝟙 _ := by rw [← GlobalTheory.Cris.spMap_comp, hid, GlobalTheory.Cris.spMap_id]
  have mc := m.comp mπ
  let V₁ : A₁ ⟶ A := Over.homMk (_ ≫ V) (mc.w.trans (by rw [hb, Category.comp_id]))
  have hm : IsMonHom V₁ := isMonHom_of_mul _ fun T x x' => by
    have hw : (T.hom ≫ spMap (frobR p k hk) ≫ spMap σ) = T.hom := by rw [hb, Category.comp_id]
    let j : Over.mk (T.hom ≫ spMap (frobR p k hk) ≫ spMap σ) ⟶ T := Over.homMk (𝟙 _) (by simpa using hw.symm)
    have h := mc.mul T x x' (j ≫ x ≫ V₁) (j ≫ x' ≫ V₁) (by simp [j, V₁]) (by simp [j, V₁])
    rw [← MonObj.comp_mul] at h
    refine Over.OverMorphism.ext ?_
    simpa [j, V₁] using h.symm
  have hFV : F ≫ V₁ = 𝟙 A ^ p := Over.OverMorphism.ext (by
    change F.left ≫ _ ≫ V = _
    rw [← Category.assoc, hF, hV])
  have h0 : primPull (dp0 k) (𝟙 _) V₁ y = 0 := by
    have h1 := GrpMor.pull_pull m mπ (homMor (dp0 k) (𝟙 _) V₁) (fun r => RingHom.congr_fun hid r) rfl y
    rw [hy, map_zero] at h1
    exact h1.symm
  have h1 : rigExtMap (verschiebung hk G) (e hn hA t y) = 0 := by
    rw [← map_eq_verschiebung hk t t₁ ht F V₁ hF hFV, ← he.primPull hn hA₁ hA t₁ t, h0, (e hn hA₁ t₁).map_zero]
  obtain ⟨-, -, -, -, -, h2, h3⟩ := rigExt_field_of_charP p k hk G
  have h4 : e hn hA t y ∈ Submodule.span k (Set.range (absFrob hk G).rig) := h3 ▸ h2 ▸ h1
  have h5 : ∀ z, e hn hA t (frobDR p k hk A z) = (absFrob hk G).rig (e hn hA t z) := fun z => by
    rw [(t.eq_semiOf_iff t (frobMor p k hk A (cast_left p k hk A)) (absFrob hk G)).2 (absFrob_y hk t)]
    exact he hn hn hA hA t t _ z
  have h6 : ∀ u ∈ Submodule.span k (Set.range (absFrob hk G).rig), ∃ z, e hn hA t (frobDR p k hk A z) = u := fun u hu => by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨v, rfl⟩ := hu
      exact ⟨(e hn hA t).symm v, by rw [h5]; exact congrArg (absFrob hk G).rig ((e hn hA t).apply_symm_apply v)⟩
    | zero => exact ⟨0, by rw [map_zero (f := frobDR p k hk A), (e hn hA t).map_zero]⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨b, rfl⟩ := hv
      exact ⟨a + b, by rw [map_add (f := _), map_add (f := _)]⟩
    | smul l u _ hu =>
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨r, rfl⟩ := IsAlgClosed.exists_pow_nat_eq l (Fact.out : p.Prime).pos
      exact ⟨r • a, by rw [map_smulₛₗ, map_smul, frobR_apply]⟩
  obtain ⟨z, hz⟩ := h6 _ h4
  exact ⟨z, (e hn hA t).injective hz⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FrobNNat
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

private theorem frobN_nat (p : ℕ) [Fact p.Prime] {X Y : Scheme.{0}} (hX : (p : Γ(X, ⊤)) = 0) (hY : (p : Γ(Y, ⊤)) = 0)
    (φ : Y ⟶ X) (j : ℕ) : frobN p Y hY j ≫ φ = φ ≫ frobN p X hX j := by
  induction j with
  | zero => simp [frobN]
  | succ j ih =>
    simp only [frobN, Category.assoc, ih]
    rw [← Category.assoc, GlobalTheory.VB.frob_naturality p hX φ hY, Category.assoc]

private theorem rel_mor (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsReduced X] (h : (p : Γ(X, ⊤)) = 0) (f : ℕ) (hf : 0 < f)
    (ψ V g c a q : X ⟶ X) (h1 : frobN p X h f ≫ ψ = a) (h2 : GlobalTheory.VB.frob X p h ≫ V = q) (h3 : a ≫ g = q ≫ c) :
    ψ ≫ frobN p X h (f - 1) ≫ g = V ≫ c := by
  haveI := (UpperTheory.Gal.Ord.epi p X h).2 f
  rw [← cancel_epi (frobN p X h f)]
  obtain ⟨j, rfl⟩ : ∃ j, f = j + 1 := ⟨f - 1, by omega⟩
  have e : frobN p X h (j + 1) = frobN p X h j ≫ GlobalTheory.VB.frob X p h :=
    frobN_nat p h h (GlobalTheory.VB.frob X p h) j |>.symm ▸ rfl
  calc frobN p X h (j + 1) ≫ ψ ≫ frobN p X h (j + 1 - 1) ≫ g
      = (frobN p X h (j + 1) ≫ ψ) ≫ frobN p X h j ≫ g := by simp
    _ = frobN p X h j ≫ a ≫ g := by
        rw [h1, ← Category.assoc, ← frobN_nat p h h a j, Category.assoc]
    _ = frobN p X h j ≫ (GlobalTheory.VB.frob X p h ≫ V) ≫ c := by rw [h3, h2]
    _ = frobN p X h (j + 1) ≫ V ≫ c := by rw [e]; simp

private theorem frobN_mor (p : ℕ) [Fact p.Prime] {k : Type} [Field k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] (j : ℕ) :
    ∃ (ρ : k →+* k) (u : GrpMor (dp0 k) (𝟙 _) A (dp0 k) (𝟙 _) A ρ (spMap ρ) (frobN p A.left (cast_left p k hk A) j)),
      ∀ c, u.pull c = (frobDR p k hk A)^[j] c := by
  induction j with
  | zero =>
    have u : GrpMor (dp0 k) (𝟙 _) A (dp0 k) (𝟙 _) A (RingHom.id k) (spMap (RingHom.id k)) (frobN p A.left (cast_left p k hk A) 0) := by
      rw [GlobalTheory.Cris.spMap_id]
      exact homMor (dp0 k) (𝟙 _) (𝟙 A)
    exact ⟨RingHom.id k, u, fun c ↦ Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)⟩
  | succ j ih =>
    obtain ⟨ρ, u, hu⟩ := ih
    have F := frobMor p k hk A (cast_left p k hk A)
    have K : GrpMor (dp0 k) (𝟙 _) A (dp0 k) (𝟙 _) A ((frobR p k hk).comp ρ) (spMap ((frobR p k hk).comp ρ))
        (frobN p A.left (cast_left p k hk A) (j + 1)) := by
      rw [GlobalTheory.SchRing.spMap_comp']
      exact u.comp F
    refine ⟨_, K, fun c ↦ ?_⟩
    rw [Function.iterate_succ_apply', ← hu]
    exact (GrpMor.pull_pull u F K (fun _ ↦ rfl) rfl c).symm

private theorem act_nat {O : Type} [Ring O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (a : OActN O G) (n : ℕ) :
    a.act (n : O) = (𝟙 G) ^ n := by
  induction n with
  | zero =>
    have := a.add 0 0
    rw [add_zero] at this
    simpa using this
  | succ n ih => rw [Nat.cast_succ, a.add, ih, a.one, pow_succ]

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.rel :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      ∀ (σ τ : k →+* k) (ψ V : o.A.left ⟶ o.A.left) (m : SMor o.A σ ψ) (n : SMor o.A τ V), frobN p o.A.left (cast_left p k hk o.A) f ≫ ψ = (o.act.act (algebraMap (𝓞 D.F) D.O π.a)).left →
      GlobalTheory.VB.frob o.A.left p (cast_left p k hk o.A) ≫ V = ((𝟙 o.A) ^ p : o.A ⟶ o.A).left →
      ∀ y, m.pull ((frobDR p k hk o.A)^[f - 1] (coh o π.g y)) = n.pull (coh o π.c y) := by
  intro p _ D R _ b N _ _ _ k _ _ hk β o i w f _ _ hf π σ τ ψ V m n h1 h2 y
  haveI hg := o.act.hom (algebraMap (𝓞 D.F) D.O π.g)
  haveI hc := o.act.hom (algebraMap (𝓞 D.F) D.O π.c)
  haveI : Smooth o.A.hom := o.ab.smooth
  haveI : IsReduced o.A.left := GlobalTheory.isReduced_of_smooth_of_isReduced o.A.hom
  obtain ⟨ρ, u, hu⟩ := frobN_mor p hk o.A (f - 1)
  have gm := homMor (dp0 k) (𝟙 _) (o.act.act (algebraMap (𝓞 D.F) D.O π.g))
  have cm := homMor (dp0 k) (𝟙 _) (o.act.act (algebraMap (𝓞 D.F) D.O π.c))
  have h3 : o.act.act (algebraMap (𝓞 D.F) D.O π.a) ≫ o.act.act (algebraMap (𝓞 D.F) D.O π.g) =
      ((𝟙 o.A) ^ p : o.A ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O π.c) := by
    rw [← act_nat o.act p, ← o.act.mul, ← o.act.mul]
    congr 1
    rw [← map_mul, ← map_natCast (algebraMap (𝓞 D.F) D.O) p, ← map_mul, mul_comm π.g, π.prod, mul_comm]
  have hmor := rel_mor p (cast_left p k hk o.A) f hf ψ V _ _ _ _ h1 h2 (congrArg (·.left) h3)
  have K1 := gm.comp u
  have K2 := cm.comp n
  have hring : σ.comp ρ = τ := by
    have e1 : (ψ ≫ frobN p o.A.left (cast_left p k hk o.A) (f - 1) ≫ (o.act.act (algebraMap (𝓞 D.F) D.O π.g)).left) ≫ o.A.hom =
        o.A.hom ≫ spMap σ ≫ spMap ρ := by
      rw [Category.assoc, Category.assoc, Over.w, u.w, ← Category.assoc, m.w, Category.assoc]
    have e2 : (V ≫ (o.act.act (algebraMap (𝓞 D.F) D.O π.c)).left) ≫ o.A.hom = o.A.hom ≫ spMap τ := by
      rw [Category.assoc, Over.w, n.w]
    have e3 : o.A.hom ≫ spMap σ ≫ spMap ρ = o.A.hom ≫ spMap τ :=
      e1.symm.trans ((congrArg (· ≫ o.A.hom) hmor).trans e2)
    have e := (MonObj.one : 𝟙_ (Over (Spec (.of k))) ⟶ o.A)
    have e4 : e.left ≫ o.A.hom = 𝟙 _ := Over.w e
    have e5 : spMap σ ≫ spMap ρ = spMap τ := by
      have := congrArg (e.left ≫ ·) e3
      simpa only [← Category.assoc, e4, Category.id_comp] using this
    apply GlobalTheory.SchRing.spMap_inj
    rw [GlobalTheory.SchRing.spMap_comp']
    exact e5
  rw [← hu]
  exact (congrArg m.pull (GrpMor.pull_pull gm u K1 (fun _ ↦ rfl) rfl y)).trans
    ((GrpMor.pull_pull K1 m K2 (fun r ↦ DFunLike.congr_fun hring r) hmor y).trans
      (GrpMor.pull_pull cm n K2 (fun _ ↦ rfl) rfl y).symm)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.PowCardChi
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

section Helpers

variable {k : Type*} [Field k] {C : Type*} {P : Type*} [AddCommGroup P] [Module k P]

private abbrev Gs (ρ : C → Module.End k P) (ψ : C → k) : Submodule k P :=
  ⨅ c, (ρ c).maxGenEigenspace (ψ c)

private theorem rho_congr [CommRing C] (p : ℕ) [CharP k p] (ρ : C → Module.End k P)
    (add : ∀ x y, ρ (x + y) = ρ x + ρ y) (mul : ∀ x y, ρ (x * y) = ρ x * ρ y) (one : ρ 1 = 1)
    {a b : C} (h : (p : C) ∣ a - b) : ρ a = ρ b := by
  let R : C →+* Module.End k P :=
    { toFun := ρ, map_one' := one, map_mul' := mul, map_add' := add,
      map_zero' := by have := add 0 0; simpa using this }
  have hp : ((p : ℕ) : Module.End k P) = 0 := by
    rw [← map_natCast (algebraMap k (Module.End k P)) p, CharP.cast_eq_zero k p, map_zero]
  obtain ⟨e, he⟩ := h
  have h0 : R (a - b) = 0 := by rw [he, map_mul, map_natCast, hp, zero_mul]
  rw [map_sub] at h0
  exact sub_eq_zero.1 h0

private theorem idem_fix (E : Module.End k P) (h : E * E = E) (v : P)
    (hv : v ∈ E.maxGenEigenspace 1) : E v = v := by
  obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
  rw [one_smul] at hn
  have hNN : (E - 1) * (E - 1) = -(E - 1) := by
    rw [sub_mul, mul_sub, mul_sub, h]; simp
  have key : ∀ n : ℕ, ((E - 1) ^ (n + 1)) v = 0 → (E - 1) v = 0 := by
    intro n
    induction n with
    | zero => intro h0; simpa using h0
    | succ n ih =>
      intro h0
      apply ih
      have h1 : (E - 1) ^ (n + 1 + 1) = -(E - 1) ^ (n + 1) := by
        rw [pow_succ (E - 1) (n + 1), pow_succ (E - 1) n, _root_.mul_assoc, hNN, mul_neg]
      rw [h1] at h0
      simpa using h0
  cases n with
  | zero =>
    have : v = 0 := by simpa using hn
    simp [this]
  | succ n =>
    have := key n hn
    simpa [sub_eq_zero] using this

private theorem Phi_pow {p : ℕ} (Φ : P →+ P) (semi : ∀ (l : k) x, Φ (l • x) = l ^ p • Φ x)
    (T : Module.End k P) (comm : ∀ x, Φ (T x) = T (Φ x)) (s : k) (n : ℕ) (v : P) :
    Φ (((T - s • 1) ^ n) v) = ((T - (s ^ p) • 1) ^ n) (Φ v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    have h1 : Φ ((T - s • 1) v) = (T - (s ^ p) • 1) (Φ v) := by
      simp [comm, semi, map_sub]
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h1]

private theorem Phi_maps {p : ℕ} (Φ : P →+ P) (semi : ∀ (l : k) x, Φ (l • x) = l ^ p • Φ x)
    (ρ : C → Module.End k P) (comm : ∀ c x, Φ (ρ c x) = ρ c (Φ x)) (ψ : C → k) (v : P)
    (hv : v ∈ Gs ρ ψ) : Φ v ∈ Gs ρ (fun c => ψ c ^ p) := by
  refine (Submodule.mem_iInf _).2 fun c => ?_
  obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hv c)
  exact (Module.End.mem_maxGenEigenspace _ _ _).2
    ⟨n, by rw [← Phi_pow Φ semi (ρ c) (comm c), hn, map_zero]⟩

private theorem proj_gs (ρ : C → Module.End k P) (hI : iSupIndep (Gs ρ)) (hT : ⨆ ψ, Gs ρ ψ = ⊤)
    (T : Module.End k P) (hTm : ∀ ψ, ∀ v ∈ Gs ρ ψ, T v ∈ Gs ρ ψ) (χ : C → k) (u y : P)
    (hy : y ∈ Gs ρ χ) (h : T u = y) : ∃ u₁ ∈ Gs ρ χ, T u₁ = y := by
  classical
  have hu : u ∈ Gs ρ χ ⊔ ⨆ (ψ) (_ : ψ ≠ χ), Gs ρ ψ := by
    rw [← iSup_split_single (Gs ρ) χ, hT]; exact Submodule.mem_top
  obtain ⟨u₁, h₁, u₂, h₂, rfl⟩ := Submodule.mem_sup.1 hu
  have hmap : (⨆ (ψ) (_ : ψ ≠ χ), Gs ρ ψ) ≤ (⨆ (ψ) (_ : ψ ≠ χ), Gs ρ ψ).comap T :=
    iSup₂_le fun ψ hψ v hv =>
      (le_iSup₂_of_le (f := fun (ψ : C → k) (_ : ψ ≠ χ) => Gs ρ ψ) ψ hψ le_rfl : Gs ρ ψ ≤ _) (hTm ψ v hv)
  have h₃ := hmap h₂
  have h₄ : T u₂ ∈ Gs ρ χ := by
    have : T u₂ = y - T u₁ := by rw [← h, map_add (f := _)]; abel
    rw [this]; exact sub_mem hy (hTm χ _ h₁)
  have h₅ : T u₂ = 0 := (Submodule.disjoint_def.1 (hI χ)) _ h₄ h₃
  exact ⟨u₁, h₁, by rw [← h, map_add (f := _), h₅, add_zero]⟩

private theorem semi_surj [IsAlgClosed k] {p : ℕ} (hp : 0 < p) [FiniteDimensional k P] (Φ : P →+ P)
    (semi : ∀ (l : k) x, Φ (l • x) = l ^ p • Φ x) (A B : Submodule k P) (hm : ∀ x ∈ A, Φ x ∈ B)
    (hinj : ∀ x ∈ A, Φ x = 0 → x = 0) (hd : Module.finrank k A = Module.finrank k B) :
    ∀ y ∈ B, ∃ x ∈ A, Φ x = y := by
  classical
  let b := Module.finBasis k A
  have root : ∀ l : k, ∃ m : k, m ^ p = l := fun l => IsAlgClosed.exists_pow_nat_eq l hp
  choose r hr using root
  let v : Fin (Module.finrank k A) → B := fun i => ⟨Φ (b i : P), hm _ (b i).2⟩
  have hsum : ∀ m : Fin (Module.finrank k A) → k,
      Φ (∑ i, m i • (b i : P)) = ∑ i, m i ^ p • Φ (b i : P) := fun m => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; exact Finset.sum_congr rfl fun i _ => semi _ _
  have hli : LinearIndependent k v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 : Φ (∑ i, r (g i) • (b i : P)) = 0 := by
      rw [hsum]
      have := congrArg Subtype.val hg
      simpa [hr, v] using this
    have hmem : (∑ i, r (g i) • (b i : P)) ∈ A :=
      Submodule.sum_mem _ fun i _ => A.smul_mem _ (b i).2
    have h1 := hinj _ hmem h0
    have h2 : ∑ i, r (g i) • b i = 0 := Subtype.ext (by simpa using h1)
    have h3 := (Fintype.linearIndependent_iff.1 b.linearIndependent) _ h2 i
    rw [← hr (g i), h3, zero_pow hp.ne']
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp [hd])
  intro y hy
  have hy' : (⟨y, hy⟩ : B) ∈ Submodule.span k (Set.range v) := hsp ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hy'
  refine ⟨∑ i, r (c i) • (b i : P), Submodule.sum_mem _ fun i _ => A.smul_mem _ (b i).2, ?_⟩
  rw [hsum]
  have := congrArg Subtype.val hc
  simpa [hr, v] using this

private theorem pow_card_chi [CommRing C] (χ : C →+* k) {q : ℕ} (hq0 : q ≠ 0)
    (hq : Nat.card (C ⧸ RingHom.ker χ) = q) (c : C) : χ c ^ q = χ c := by
  classical
  haveI : Finite (C ⧸ RingHom.ker χ) := Nat.finite_of_card_ne_zero (by rw [hq]; exact hq0)
  letI := Fintype.ofFinite (C ⧸ RingHom.ker χ)
  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  letI : Field (C ⧸ RingHom.ker χ) := Fintype.fieldOfDomain _
  have h := FiniteField.pow_card (Ideal.Quotient.mk (RingHom.ker χ) c)
  rw [← Nat.card_eq_fintype_card, hq] at h
  have h2 := congrArg χ.kerLift h
  rw [map_pow] at h2
  simpa using h2

private theorem pow_ne_chi [CommRing C] {p : ℕ} [Fact p.Prime] (χ : C →+* k) {f j : ℕ}
    (hq : Nat.card (C ⧸ RingHom.ker χ) = p ^ f) (hj : 0 < j) (hjf : j < f) :
    (fun c => χ c ^ p ^ j) ≠ ⇑χ := by
  classical
  intro h
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpj : 1 < p ^ j := Nat.one_lt_pow hj.ne' hp1
  haveI : Finite (C ⧸ RingHom.ker χ) :=
    Nat.finite_of_card_ne_zero (by rw [hq]; exact pow_ne_zero _ (by omega))
  letI := Fintype.ofFinite (C ⧸ RingHom.ker χ)
  let Q : Polynomial k := Polynomial.X ^ p ^ j - Polynomial.X
  have hQ : Q ≠ 0 := Polynomial.X_pow_sub_X_ne_zero hpj
  have hQd : Q.natDegree = p ^ j := Polynomial.natDegree_X_pow_sub_X (R := k) hpj
  have hsub : Finset.univ.image χ.kerLift ⊆ Q.roots.toFinset := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ, Polynomial.IsRoot.def]
    have := congrFun h c
    simp only [Q, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    simp only [RingHom.kerLift_mk]
    rw [this, sub_self]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (RingHom.kerLift_injective χ), Finset.card_univ,
    ← Nat.card_eq_fintype_card, hq] at h1
  have h2 : p ^ f ≤ p ^ j :=
    h1.trans ((Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' Q).trans hQd.le))
  exact absurd h2 (not_le.2 (Nat.pow_lt_pow_right hp1 hjf))

end Helpers

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.alg1 :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (C : Type) [CommRing C] (w : Ideal C) (f : ℕ), 0 < f →
      Nat.card (C ⧸ w) = p ^ f → ∀ (π : Par p w f) (χ : C →+* k) (P : Type 1) [AddCommGroup P] [Module k P] (ρ : C → Module.End k P) (F : Submodule k P)
      (Φ : P →+ P), Lin p π χ ρ F Φ →
      ∀ V W : P →+ P, (∀ y, V y = 0 → ∃ z, Φ z = y) → (∀ y, W (Φ^[f - 1] (ρ π.g y)) = V (ρ π.c y)) → (∀ x ∈ F, W (ρ π.ε x) = 0) →
      ∀ x ∈ F, ∃ z, ρ π.ε x = ρ π.g (Φ^[f] z) := by
  intro p _ k _ _ _ C _ w f hf hcard π χ P _ _ ρ F Φ L V W hV hW hWF x hx
  haveI := L.fin
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hcard' : Nat.card (C ⧸ RingHom.ker χ) = p ^ f := by rw [L.ker]; exact hcard
  have hcg := fun {a b : C} => rho_congr p ρ L.add L.mul L.one (a := a) (b := b)
  have hcomm : ∀ a b, Commute (ρ a) (ρ b) := fun a b => by
    show ρ a * ρ b = ρ b * ρ a
    rw [← L.mul, ← L.mul, mul_comm]
  have hmt : ∀ i j (φ : k), Set.MapsTo (ρ i) ((ρ j).maxGenEigenspace φ) ((ρ j).maxGenEigenspace φ) :=
    fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
  have hI : iSupIndep (Gs ρ) := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo ρ hmt
  have hT : ⨆ ψ, Gs ρ ψ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo ρ hmt
      fun _ => Module.End.iSup_maxGenEigenspace_eq_top _
  have hGm : ∀ a ψ, ∀ v ∈ Gs ρ ψ, ρ a v ∈ Gs ρ ψ := fun a ψ v hv =>
    (Submodule.mem_iInf _).2 fun b => hmt a b _ ((Submodule.mem_iInf _).1 hv b)
  have hEE : ρ π.ε * ρ π.ε = ρ π.ε := by
    rw [← L.mul]; exact hcg π.idem
  have hχε : χ π.ε = 1 := by
    have h1 : π.ε - 1 ∈ RingHom.ker χ := by rw [L.ker]; exact π.one
    have h2 : χ (π.ε - 1) = 0 := h1
    rw [map_sub, map_one] at h2
    exact sub_eq_zero.1 h2
  have hχa : χ π.a = 0 := by
    have h1 : π.a ∈ RingHom.ker χ := by rw [L.ker]; exact π.mem
    exact h1
  have hfix : ∀ ψ : C → k, ψ π.ε = 1 → ∀ v ∈ Gs ρ ψ, ρ π.ε v = v := fun ψ h1 v hv =>
    idem_fix _ hEE v (by have := (Submodule.mem_iInf _).1 hv π.ε; rwa [h1] at this)
  have heig : ∀ (ψ : C → k) (v : P), (∀ c, ρ c v = ψ c • v) → v ∈ Gs ρ ψ := fun ψ v h =>
    (Submodule.mem_iInf _).2 fun c => (Module.End.mem_maxGenEigenspace _ _ _).2
      ⟨1, by simp [h c]⟩
  have hstep : ∀ j, ∀ v ∈ Gs ρ (fun c => χ c ^ p ^ j), Φ v ∈ Gs ρ (fun c => χ c ^ p ^ (j + 1)) := by
    intro j v hv
    have h1 := Phi_maps Φ L.semi ρ L.comm _ v hv
    have h2 : (fun c => χ c ^ p ^ (j + 1)) = fun c => (χ c ^ p ^ j) ^ p :=
      funext fun c => by rw [pow_succ, pow_mul]
    rw [h2]; exact h1
  have hinj : ∀ j, 0 < j → j < f → ∀ v ∈ Gs ρ (fun c => χ c ^ p ^ j), Φ v = 0 → v = 0 := by
    intro j hj hjf v hv h0
    have hvF : v ∈ F := (L.kerΦ v).1 h0
    have hE : ρ π.ε v = v := hfix _ (by simp [hχε]) v hv
    have he : ∀ c, ρ c v = χ c • v := fun c => by
      have := L.eig c v hvF
      rwa [hE] at this
    exact Submodule.disjoint_def.1 (hI.pairwiseDisjoint (pow_ne_chi χ hcard' hj hjf)) v hv (heig _ v he)
  have hsurj : ∀ j, 0 < j → j < f → ∀ u ∈ Gs ρ (fun c => χ c ^ p ^ (j + 1)),
      ∃ v ∈ Gs ρ (fun c => χ c ^ p ^ j), Φ v = u := fun j hj hjf =>
    semi_surj hp0 Φ L.semi _ _ (hstep j) (hinj j hj hjf) ((L.dims j).trans (L.dims (j + 1)).symm)
  obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
  have hchain : ∀ n, n ≤ m → ∀ u ∈ Gs ρ (fun c => χ c ^ p ^ (n + 1)),
      ∃ u' ∈ Gs ρ (fun c => χ c ^ p ^ 1), Φ^[n] u' = u := by
    intro n
    induction n with
    | zero => intro _ u hu; exact ⟨u, hu, rfl⟩
    | succ n ih =>
      intro hn u hu
      obtain ⟨v, hv, rfl⟩ := hsurj (n + 1) (by omega) (by omega) u hu
      obtain ⟨u', h1, rfl⟩ := ih (by omega) v hv
      exact ⟨u', h1, by rw [Function.iterate_succ_apply']⟩
  have hit : ∀ (c : C) (n : ℕ) (v : P), Φ^[n] (ρ c v) = ρ c (Φ^[n] v) := by
    intro c n v
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, L.comm]
  have hye : ∀ c, ρ c (ρ π.ε x) = χ c • ρ π.ε x := fun c => L.eig c x hx
  have hyG : ρ π.ε x ∈ Gs ρ χ := heig _ _ hye
  have hay : ρ π.a (ρ π.ε x) = 0 := by rw [hye, hχa, zero_smul]
  obtain ⟨u, hu⟩ := L.annA _ hay
  have hEy : ρ π.ε (ρ π.ε x) = ρ π.ε x := by
    have := congrArg (fun T : Module.End k P => T x) hEE
    simpa using this
  rw [hEy] at hu
  obtain ⟨u₁, hu₁G, hu₁⟩ := proj_gs ρ hI hT (ρ π.g) (hGm π.g) χ u _ hyG hu.symm
  have hu₁G' : u₁ ∈ Gs ρ (fun c => χ c ^ p ^ (m + 1)) := by
    have h2 : (fun c => χ c ^ p ^ (m + 1)) = ⇑χ := funext fun c => pow_card_chi χ (pow_ne_zero _ hp0.ne') hcard' c
    rw [h2]; exact hu₁G
  obtain ⟨u', hu'G, rfl⟩ := hchain m le_rfl u₁ hu₁G'
  have hEu : ρ π.ε u' = u' := hfix _ (by simp [hχε]) u' hu'G
  have hWy := hWF x hx
  rw [← hu₁, ← hit] at hWy
  have hVz : V (ρ π.c u') = 0 := by
    have := hW u'
    simp only [Nat.add_sub_cancel] at this
    rw [← this]; exact hWy
  obtain ⟨z, hz⟩ := hV _ hVz
  refine ⟨ρ (π.c' * π.ε) z, ?_⟩
  have hΦ : Φ (ρ (π.c' * π.ε) z) = u' := by
    rw [L.comm, hz]
    have h3 : ρ (π.c' * π.ε) * ρ π.c = ρ π.ε := by
      rw [← L.mul]
      apply hcg
      have : π.c' * π.ε * π.c - π.ε = π.c' * π.c * π.ε - π.ε := by ring
      rw [this]; exact π.inv
    have h4 := congrArg (fun T : Module.End k P => T u') h3
    simp only [Module.End.mul_apply] at h4
    rw [h4, hEu]
  rw [Function.iterate_succ_apply, hΦ, hu₁]
end

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

theorem UpperTheory.Gal.Ord.point :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      IsWOrd o w (𝟙 (Sp k)) ∨ NOo hk o π := by
  intro p _ D R _ b N hN hNp hm k _ _ hk β o i w f hw hnorm hf π
  rcases cnt p D R b N hN hNp hm k hk β o i w f hw hnorm hf π with h | ⟨v, hv1, hv2, hv3⟩
  · exact Or.inl h
  right
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (R := k) (Fact.out : p.Prime)).mpr hk
  have hL := lin p D R b N hN hNp hm k hk β o i w f hw hnorm hf π
  obtain ⟨σ, ψ, hσ, m, hψ⟩ := va p D R b N hN hNp hm k hk β o i w f hw hnorm hf π
  have hH := hasse p D R b N hN hNp hm k hk β o i w f hw hnorm hf π σ hσ ψ m hψ v hv1 hv2 hv3
  have hpow : ∀ n : ℕ, o.act.act ((n : D.O)) = 𝟙 o.A ^ n := by
    intro n
    induction n with
    | zero =>
      rw [Nat.cast_zero, pow_zero]
      have h0 := o.act.add 0 0
      rw [add_zero] at h0
      simpa using h0
    | succ n ih => rw [Nat.cast_succ, o.act.add, ih, o.act.one, pow_succ]
  haveI hmon : IsMonHom (o.act.act ((p : D.O))) := o.act.hom _
  have hp0 : ∀ x : ↥(primDR o.A), primPull (dp0 k) (𝟙 (Sp k)) (o.act.act ((p : D.O))) x = 0 := by
    intro x
    have h1 : ((p : D.O)) = (algebraMap (𝓞 D.F) D.O) (p : 𝓞 D.F) := by simp
    have h2 : ∀ n : ℕ, coh o (n : 𝓞 D.F) = (n : k) • (1 : Module.End k ↥(primDR o.A)) := by
      intro n
      induction n with
      | zero =>
        have h0 := hL.add 0 0
        simp only [add_zero] at h0
        simpa using h0
      | succ n ih => rw [Nat.cast_succ, hL.add, ih, hL.one, Nat.cast_succ, add_smul, one_smul]
    have h3 := congrArg (fun φ : Module.End k ↥(primDR o.A) => φ x) (h2 p)
    simp only [hk, zero_smul] at h3
    have h4 : coh o (p : 𝓞 D.F) x = primPull (dp0 k) (𝟙 (Sp k)) (o.act.act ((p : D.O))) x := by
      simp only [coh, h1]
    rw [← h4]
    exact h3
  have mp : SMor o.A (RingHom.id k) (Over.Hom.left (o.act.act ((p : D.O)))) := by
    have := homMor (dp0 k) (𝟙 (Sp k)) (o.act.act ((p : D.O)))
    simpa [SMor, spMap_id] using this
  obtain ⟨τ, V, hτ, n, hτp, hV⟩ := root p k hk o.A o.ab (RingHom.id k) Function.bijective_id _ mp (by
    intro x _
    exact hp0 x)
  have hV' := hV
  rw [hpow] at hV'
  have hrel := rel p D R b N hN hNp hm k hk β o i w f hw hnorm hf π σ τ ψ V m n hψ hV'
  have hrk := rankV p k hk o.A o.ab τ V n (fun x => by simpa using hτp x) hV'
  have hcard : Nat.card (𝓞 D.F ⧸ w) = p ^ f := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]; exact hnorm
  intro x hx
  obtain ⟨z, hz⟩ := alg1 p k (𝓞 D.F) w f hf hcard π (β.comp (b.t i)) ↥(primDR o.A) (coh o) (PrimitiveSubmodule o.A)
    (frobDR p k hk o.A).toAddMonoidHom hL (GrpMor.pull n).toAddMonoidHom (GrpMor.pull m).toAddMonoidHom
    (fun y hy => hrk y hy) (fun y => hrel y) (fun x hx => hH x hx) x hx
  exact Submodule.subset_span ⟨z, hz.symm⟩
