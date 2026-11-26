module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst

namespace GlobalTheory.GalOfCusp

def LocalGlobalAboveL : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a → ∀ π : CuspSub E a, π.IsCsd → (CG.mk π).IsRegAlg →
    ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      IsGalRepOf π (quadChar E ^ a) ι r wt HT →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)), w ∈ placesOver E l → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
      (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
      ∀ rc : IrrGL (k := w.adicCompletion E) → WD h, IsRec h rc →
        wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

end GlobalTheory.GalOfCusp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsSpehOne
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh

namespace GlobalTheory.DiscreteSpectrumCM

theorem isUnitarisable_of_injective {G X Y : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] {ρ : Representation ℂ G X} {τ : Representation ℂ G Y} (q : ρ.IntertwiningMap τ)
    (hq : Function.Injective q) (hu : IsUnitarisable τ) : IsUnitarisable ρ := by
  obtain ⟨B, h1, h2, h3⟩ := hu
  let B' : X →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ := (B.compl₂ q.toLinearMap).comp q.toLinearMap
  have hB : ∀ v w, B' v w = B (q v) (q w) := fun _ _ => rfl
  refine ⟨B', fun v w => by rw [hB, hB, h1], fun v hv => by
    rw [hB]; exact h2 _ fun e => hv (hq (e.trans (map_zero q).symm)), fun g v w => ?_⟩
  rw [hB, hB, ← h3 g (q v) (q w)]
  rw [q.isIntertwining _ _ g v, q.isIntertwining _ _ g w]

section Local

open GlobalTheory.PRep GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem injective_of_irreducible {G X Y : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] {ρ : Representation ℂ G X} {τ : Representation ℂ G Y} (hi : ρ.IsIrreducible)
    (q : ρ.IntertwiningMap τ) (h0 : q.toLinearMap ≠ 0) : Function.Injective q := by
  rcases ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hi).2 (LinearMap.ker q.toLinearMap) (fun g v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    change q (ρ g v) = 0
    rw [q.isIntertwining _ _ g v]
    change τ g (q.toLinearMap v) = 0
    rw [hv, map_zero]) with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exact absurd (LinearMap.ker_eq_top.1 h) h0

theorem isUnitarisable_of_isSpeh_one {a : ℕ} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (GL (Fin a) k) X} (hs : IsSmooth ρ) (hi : ρ.IsIrreducible)
    {τ : Representation ℂ (GL (Fin a) k) Y} (h : IsSpeh (IrrGL.of ρ hs hi) 1 τ) (hu : IsUnitarisable τ) :
    IsUnitarisable ρ := by
  obtain ⟨hd, hτ, p, hp, -⟩ := h
  have key : ∀ y : Fin 1 → IrrGL (k := k), y = (fun _ => IrrGL.of ρ hs hi) → ∀ hd : ∑ i, (y i).1 = a,
      Nonempty ((IrrGL.of ρ hs hi).rep.Equiv (prodIrr y hd)) := by
    rintro _ rfl hd
    exact nonempty_equiv_prodIrr_one _ hd
  obtain ⟨e⟩ := key _ (funext fun _ => by simp [spehFactor]) hd
  let q : ρ.IntertwiningMap τ := p.comp (e.toIntertwiningMap.comp (IrrGL.equivOf ρ hs hi).toIntertwiningMap)
  have hq : Function.Surjective q :=
    hp.comp (e.toLinearEquiv.surjective.comp (IrrGL.equivOf ρ hs hi).toLinearEquiv.surjective)
  refine isUnitarisable_of_injective q (injective_of_irreducible hi q fun h0 => ?_) hu
  have : Nontrivial Y := ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hτ).1
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  obtain ⟨v, rfl⟩ := hq y
  exact hy (LinearMap.congr_fun h0 v)

end Local

section Speh

open GlobalTheory.PRep GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E]

theorem isSpehQuot_of_isSpeh {a d N : ℕ} (h : ∑ _ : Fin d, a = N) {w : HeightOneSpectrum (𝓞 E)} (σ : LocIrr w a)
    (σ' : LocIrr w N) (hs : IsSpeh (IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ) : IsSpehQuot h σ σ' := by
  obtain ⟨hd, -, p, hp, -⟩ := hs
  let T : ∀ i : Fin d, (GlobalTheory.SmGL.twist σ.ρ (detChar (Fin a) (absPow (w.adicCompletion E) (((d : ℂ) - 1) / 2 - (i : ℕ))))).Equiv
      (spehFactor (IrrGL.of σ.ρ σ.smooth σ.irred) d i).rep := fun i =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) _).trans
      ((IrrGL.of σ.ρ σ.smooth σ.irred).twEquiv _ (isSmoothChar_absPow _))
  let M := multiProdEquiv (stdBlocks (fun _ : Fin d => a) h) T
  exact ⟨p.comp M.toIntertwiningMap, hp.comp M.toLinearEquiv.surjective⟩

end Speh

section Inf

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem hasInfCharGL_unique {V : Submodule ℂ (Sm E N)} (hV : V ≠ ⊥) {τ : E →+* ℂ} {m m' : Multiset ℂ}
    (h : HasInfCharGL V τ m) (h' : HasInfCharGL V τ m') : m = m' := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV
  have e : ((m.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod =
      ((m'.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod := by
    refine Polynomial.funext fun u => ?_
    have := smul_left_injective ℂ h0 ((h.2 u φ hφ).symm.trans (h'.2 u φ hφ))
    simpa [Polynomial.eval_multiset_prod, Multiset.map_map] using this
  have e2 := congrArg Polynomial.roots e
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e2
  exact Multiset.map_injective neg_injective e2

end Inf

theorem spehInf_eq (d : ℕ) (m : Multiset ℂ) : GlobalTheory.SphGal.spehInf d m = GlobalTheory.DefiniteBC.spehInf d m := by
  simp only [GlobalTheory.SphGal.spehInf, GlobalTheory.DefiniteBC.spehInf]
  rw [← List.sum_ofFn, ← List.map_coe_finRange_eq_range, List.map_map, List.ofFn_eq_map]
  rfl

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.DiscreteSpectrumCM

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivOfIsSubquotient
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.UnitaryBC

namespace GlobalTheory.BaseChangeBridge

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_equiv_of_isSubquotient {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (hσ : σ.IsIrreducible) (hρ : ρ.IsIrreducible) (h : GlobalTheory.SmGL.IsSubquotient σ ρ) :
    ∃ e : W ≃ₗ[ℂ] V, ∀ g x, e (σ g x) = ρ g (e x) := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨hW, -⟩ := (GlobalTheory.CuspRep.isIrreducible_iff σ).1 hσ
  obtain ⟨-, hρ'⟩ := (GlobalTheory.CuspRep.isIrreducible_iff ρ).1 hρ
  have hS : S.toSubmodule = ⊤ := by
    rcases hρ' S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with e | e
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (0 : W)
      obtain ⟨v, rfl⟩ := hf x
      have hv : v = 0 := by
        exact Subtype.ext ((Submodule.eq_bot_iff _).1 e v v.2)
      subst hv
      exact hx (map_zero f.toLinearMap)
    · exact e
  let g : V →ₗ[ℂ] W := f.toLinearMap ∘ₗ (LinearEquiv.ofTop S.toSubmodule hS).symm.toLinearMap
  have hg : ∀ x v, g (ρ x v) = σ x (g v) := fun x v => by
    have := LinearMap.congr_fun (f.isIntertwining' x) ((LinearEquiv.ofTop S.toSubmodule hS).symm v)
    exact this
  have gsurj : Function.Surjective g := fun y => by
    obtain ⟨v, rfl⟩ := hf y
    refine ⟨(v : V), ?_⟩
    change f ((LinearEquiv.ofTop S.toSubmodule hS).symm (v : V)) = f v
    congr 1
  have ginj : Function.Injective g := by
    rcases hρ' (LinearMap.ker g) (fun x v hv => by
        rw [LinearMap.mem_ker] at hv ⊢
        rw [hg, hv, map_zero]) with e | e
    · exact LinearMap.ker_eq_bot.1 e
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (0 : W)
      obtain ⟨v, rfl⟩ := gsurj y
      exact hy (LinearMap.mem_ker.1 (e ▸ Submodule.mem_top))
  let e0 := LinearEquiv.ofBijective g ⟨ginj, gsurj⟩
  refine ⟨e0.symm, fun x y => e0.injective ?_⟩
  rw [LinearEquiv.apply_symm_apply]
  change σ x y = g (ρ x (e0.symm y))
  rw [hg]
  change σ x y = σ x (e0 (e0.symm y))
  rw [LinearEquiv.apply_symm_apply]

variable {H : Type} [Group H]

theorem isSpherical_of_equiv {σ : Representation ℂ H W} {ρ : Representation ℂ H V} (e : W ≃ₗ[ℂ] V)
    (he : ∀ g x, e (σ g x) = ρ g (e x)) {K : Subgroup H} (h : GlobalTheory.LGrp.IsSpherical σ K) :
    GlobalTheory.LGrp.IsSpherical ρ K := by
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h
  exact (Submodule.ne_bot_iff _).2 ⟨e x, GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← he, GlobalTheory.LGrp.mem_fixed.1 hx k hk],
    by simpa using h0⟩

theorem symm_equivariant {σ : Representation ℂ H W} {ρ : Representation ℂ H V} (e : W ≃ₗ[ℂ] V)
    (he : ∀ g x, e (σ g x) = ρ g (e x)) (g : H) (y : V) : e.symm (ρ g y) = σ g (e.symm y) :=
  e.injective (by rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply])

end General

section Local

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem hasSatGL_of_equiv {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} (e : W ≃ₗ[ℂ] V) (he : ∀ g x, e (σ g x) = ρ g (e x))
    {B : Multiset ℂˣ} (h : GlobalTheory.LFun.HasSatGL w σ B) : GlobalTheory.LFun.HasSatGL w ρ B := by
  refine ⟨isSpherical_of_equiv e he h.1, fun y hy h0 => ?_⟩
  have hx : e.symm y ∈ GlobalTheory.PRep.fixed σ (GlobalTheory.LFun.KGL w (n := n)) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    rw [← symm_equivariant e he, GlobalTheory.LGrp.mem_fixed.1 hy k hk]
  have h0' : e.symm y ≠ 0 := by simpa using h0
  have := (h.2 _ hx h0').map e.toLinearMap he (by simpa using h0)
  simpa using this

end Local

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isCompAlong_of_equiv {π : Submodule ℂ (UA E n → ℂ)} {Gv : Subgroup (UA E n)} {H : Type} [Group H]
    {p : Gv →* H} {σ : Representation ℂ H W} {ρ : Representation ℂ H V} (e : W ≃ₗ[ℂ] V)
    (he : ∀ g x, e (σ g x) = ρ g (e x)) (hρ : ρ.IsIrreducible) (h : IsCompAlong π Gv p σ) :
    IsCompAlong π Gv p ρ := by
  obtain ⟨-, f, h0, hf, hfi⟩ := h
  refine ⟨hρ, f ∘ₗ e.symm.toLinearMap, fun h1 => h0 ?_, fun v => hf _, fun x v => ?_⟩
  · refine LinearMap.ext fun y => ?_
    simpa using LinearMap.congr_fun h1 (e y)
  · simp [symm_equivariant e he, hfi]

end CM

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem main : GlobalTheory.Published.BaseChangeIsobaric → GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    GlobalTheory.Published.BaseChangeDefiniteUnitary := by
  intro hBC hB E _ _ _ hun n hn π hπ
  obtain ⟨c, N, h, V, σ, m, P, H⟩ := hBC E hun n hn π hπ
  refine ⟨c, N, h, V, σ, m, ?_⟩
  have hirr : ∀ w, (locProd h w (σ · w)).IsIrreducible := fun w =>
    ((GlobalTheory.SmGL.MultiIrr.products_irreducible hB (w.adicCompletion E)).1 c N (Fin n) (GlobalTheory.SmGL.stdBlocks N h)
      (fun i => (σ i w).V) (fun i => (σ i w).ρ) (fun i => (σ i w).smooth) (fun i => (σ i w).irred)
      (fun i => GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL E (N i) (V i) (H.discrete i) w (σ i w)
        (H.loc i w))).2.1
  exact
    { pos := H.pos
      discrete := H.discrete
      csd := H.csd
      loc := H.loc
      inf := H.inf
      unram := fun w hw => by
        obtain ⟨e, he⟩ := exists_equiv_of_isSubquotient (P w).irred (hirr w) (H.sub w)
        exact isSpherical_of_equiv e he (H.unram w hw)
      inert := fun w s ϖ q hs hq α hα => by
        obtain ⟨e, he⟩ := exists_equiv_of_isSubquotient (P w).irred (hirr w) (H.sub w)
        exact hasSatGL_of_equiv e he (H.inert w s ϖ q hs hq α hα)
      split := fun w hw => by
        obtain ⟨e, he⟩ := exists_equiv_of_isSubquotient (P w).irred (hirr w) (H.sub w)
        exact isCompAlong_of_equiv e he (hirr w) (H.split w hw)
      weight := H.weight }

end GlobalTheory.BaseChangeBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestriction
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestriction
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilRestrict

open scoped Pointwise

section

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K Ω] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]

theorem comap_eq_of_isPlaceOver {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v') :
    v'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal := by
  ext x
  rw [Ideal.mem_comap, ← h x, ← h' (algebraMap (𝓞 K) (𝓞 L) x), IsScalarTower.algebraMap_apply K L Ω]
  rfl

theorem normV_eq_pow_of_isPlaceOver {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v') :
    ∃ f : ℕ, normV v' = normV v ^ f := by
  have hw := comap_eq_of_isPlaceOver h h'
  have : v'.asIdeal.LiesOver v.asIdeal := ⟨hw.symm⟩
  refine ⟨v'.asIdeal.inertiaDeg (𝓞 K), ?_⟩
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal v'.asIdeal).symm


variable (K) in
def resG : G L Ω →* G K Ω where
  toFun σ := σ.restrictScalars K
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

@[simp] theorem resG_apply (σ : G L Ω) (z : Ω) : resG K σ z = σ z := rfl

theorem continuous_resG [Algebra.IsIntegral L Ω] : Continuous (resG (L := L) (Ω := Ω) K) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  rw [Filter.mem_map]
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff K Ω s).1 hs
  let b := Module.finBasis K E
  have hU : IsOpen (⋂ i, (MulAction.stabilizer (G L Ω) (b i : Ω) : Set (G L Ω))) :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral _
  refine Filter.mem_of_superset (hU.mem_nhds (Set.mem_iInter.2 fun i =>
    (MulAction.stabilizer (G L Ω) _).one_mem)) fun g hg => hEs ?_
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hb : ∀ i, g (b i : Ω) = b i := fun i => by
    have := Set.mem_iInter.1 hg i
    rwa [SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : Ω) := by
    have := congrArg E.val (b.sum_repr ⟨x, hx⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simp only [map_smul] at this
    exact this.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx', map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, resG_apply, hb]

variable {A : ValuationSubring Ω}

theorem resG_mem_Dec {σ : G L Ω} (hσ : σ ∈ Dec (F := L) A) : resG K σ ∈ Dec (F := K) A := by
  have h1 : σ • A = A := hσ
  show (resG K σ) • A = A
  exact h1

theorem resG_mem_Ine {σ : G L Ω} (hσ : σ ∈ Ine (F := L) A) : resG K σ ∈ Ine (F := K) A :=
  ⟨resG_mem_Dec hσ.1, fun x hx => hσ.2 x hx⟩

theorem actsAs_resG {q f a b : ℕ} {σ : G L Ω} (hσ : ActsAs A (q ^ f) σ a b) :
    ActsAs A q (resG K σ) (f * a) (f * b) := by
  refine ⟨resG_mem_Dec hσ.1, fun x hx => ?_⟩
  have e1 : (q ^ f) ^ b = q ^ (f * b) := (pow_mul q f b).symm
  have e2 : (q ^ f) ^ a = q ^ (f * a) := (pow_mul q f a).symm
  have := hσ.2 x hx
  rw [e1, e2] at this
  exact this

variable {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}

def resWeil (h : IsPlaceOver A v) (h' : IsPlaceOver A v') : Weil h' →* Weil h :=
  ((resG K).comp (Weil h').subtype).codRestrict (Weil h) fun σ => by
    obtain ⟨f, hf⟩ := normV_eq_pow_of_isPlaceOver h h'
    obtain ⟨a, b, hab⟩ := (mem_Weil h').1 σ.2
    rw [hf] at hab
    exact (mem_Weil h).2 ⟨_, _, actsAs_resG hab⟩

theorem resWeil_apply (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ : Weil h') (z : Ω) :
    (resWeil h h' σ : G K Ω) z = (σ : G L Ω) z := rfl

def resIne : Ine (F := L) A → Ine (F := K) A := fun σ => ⟨resG K (σ : G L Ω), resG_mem_Ine (K := K) (L := L) (σ := (σ : G L Ω)) σ.2⟩

theorem continuous_resIne [Algebra.IsIntegral L Ω] : Continuous (resIne (K := K) (L := L) (A := A)) :=
  ((continuous_resG (K := K)).comp continuous_subtype_val).subtype_mk _

theorem isSmooth_comp_resWeil [Algebra.IsIntegral L Ω] (h : IsPlaceOver A v) (h' : IsPlaceOver A v')
    {M : Type*} [Monoid M] {f : Weil h →* M} (hf : IsSmooth f) : IsSmooth (f.comp (resWeil h h')) := by
  have e : {σ : Ine (F := L) A | (f.comp (resWeil h h')) (ineIncl h' σ) = 1} =
      resIne ⁻¹' {τ : Ine (F := K) A | f (ineIncl h τ) = 1} := rfl
  show IsOpen {σ : Ine (F := L) A | (f.comp (resWeil h h')) (ineIncl h' σ) = 1}
  rw [e]
  exact hf.preimage continuous_resIne

end

theorem weil_restrict : ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v'), ∃ r : Weil h' →* Weil h, (∀ (σ : Weil h') (z : Ω), (r σ : G K Ω) z = (σ : G L Ω) z) ∧ ∀ (M : Type) [Monoid M] (f : Weil h →* M), GlobalTheory.WeilDeligne.IsSmooth f → GlobalTheory.WeilDeligne.IsSmooth (f.comp r) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h'
  haveI : Algebra.IsIntegral L Ω := (IsAlgClosure.isAlgebraic (R := L) (K := Ω)).isIntegral
  exact ⟨resWeil h h', resWeil_apply h h', fun M _ f hf => isSmooth_comp_resWeil h h' hf⟩

end GlobalTheory.WeilRestrict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestrictionStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_group_restriction : ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v'), ∃ r : Weil h' →* Weil h, (∀ (σ : Weil h') (z : Ω), (r σ : G K Ω) z = (σ : G L Ω) z) ∧ ∀ (M : Type) [Monoid M] (f : Weil h →* M), GlobalTheory.WeilDeligne.IsSmooth f → GlobalTheory.WeilDeligne.IsSmooth (f.comp r) := by
  first | exact @GlobalTheory.WeilRestrict.weil_restrict | exact GlobalTheory.WeilRestrict.weil_restrict | (intros; apply GlobalTheory.WeilRestrict.weil_restrict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSet
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSet
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjPlaceOff

open Formalism.HermitianLattices.Ext.L3

theorem star_eq_hostConj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem isConjPl_iff (D : D7) (P Q : PlE D.host) :
    IsConjPl D.host P Q ↔ ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ conjO D.host.E x ∈ Q.asIdeal := by
  constructor
  · intro h x
    exact h x (conjO D.host.E x) (by rw [conjO_coe, star_eq_hostConj])
  · intro h x y hy
    have : y = conjO D.host.E x := RingOfIntegers.ext (by rw [hy, conjO_coe, star_eq_hostConj])
    subst this
    exact h x

noncomputable def conjPl (D : D7) (P : PlE D.host) : PlE D.host where
  asIdeal := P.asIdeal.comap (conjO D.host.E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply P.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have : conjO D.host.E x ∈ P.asIdeal.comap (conjO D.host.E) := by
      rw [Ideal.mem_comap, conjO_conjO]; exact hx
    rw [h, Ideal.mem_bot] at this
    rw [Ideal.mem_bot, ← conjO_conjO (K := D.host.E) x, this, map_zero]

theorem mem_conjPl (D : D7) (P : PlE D.host) (x : 𝓞 D.host.E) :
    x ∈ (conjPl D P).asIdeal ↔ conjO D.host.E x ∈ P.asIdeal := Iff.rfl

theorem conjPl_conjPl (D : D7) (P : PlE D.host) : conjPl D (conjPl D P) = P := by
  ext x
  rw [mem_conjPl, mem_conjPl, conjO_conjO]

theorem isConjPl_conjPl (D : D7) (P : PlE D.host) : IsConjPl D.host P (conjPl D P) := by
  rw [isConjPl_iff]
  intro x
  rw [mem_conjPl, conjO_conjO]

theorem isConjPl_conjPl' (D : D7) (P : PlE D.host) : IsConjPl D.host (conjPl D P) P := by
  rw [isConjPl_iff]
  intro x
  rfl

theorem conjIdeal_eq (D : D7) (P : PlE D.host) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = (conjPl D P).asIdeal :=
  conjIdeal_eq_comap _

theorem isSplitPl_iff (D : D7) (P : PlE D.host) :
    IsSplitPl D.host P ↔ ∃ x : 𝓞 D.host.E, x ∈ P.asIdeal ∧ conjO D.host.E x ∉ P.asIdeal := by
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, h _ (by rw [conjO_coe, star_eq_hostConj])⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, fun y hy => ?_⟩
    have : y = conjO D.host.E x := RingOfIntegers.ext (by rw [hy, conjO_coe, star_eq_hostConj])
    rw [this]; exact h

theorem conjPl_ne_of_split (D : D7) {P : PlE D.host} (h : IsSplitPl D.host P) :
    (conjPl D P).asIdeal ≠ P.asIdeal := by
  obtain ⟨x, hx, hcx⟩ := (isSplitPl_iff D P).1 h
  intro he
  apply hcx
  rw [← mem_conjPl, he]
  exact hx

theorem isSplitPl_conjPl (D : D7) {P : PlE D.host} (h : IsSplitPl D.host P) :
    IsSplitPl D.host (conjPl D P) := by
  obtain ⟨x, hx, hcx⟩ := (isSplitPl_iff D P).1 h
  rw [isSplitPl_iff]
  refine ⟨conjO D.host.E x, ?_, ?_⟩
  · rw [mem_conjPl, conjO_conjO]; exact hx
  · rw [mem_conjPl, conjO_conjO]; exact hcx

theorem exists_conj_off (D : D7) (S0 : Finset (PlE D.host)) (Sb : Finset (Formalism.L2.DIV.Pl D.host.E))
    (P : PlE D.host)
    (hS0 : ∀ P1 P2, P1 ∈ S0 → IsConjPl D.host P1 P2 → P2 ∈ S0)
    (h2 : placesOver D.host.E 2 ⊆ (S0 : Set (PlE D.host)))
    (hb : ∀ Q ∈ Sb, Q ∈ S0) (hP : IsSplitPl D.host P) (hPS : P ∉ S0) :
    ∃ P' : PlE D.host, IsConjPl D.host P P' ∧ IsSplitPl D.host P' ∧ P' ∉ S0 ∧
      Formalism.IndefR.Bridge.SplitOff P (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      Formalism.IndefR.Bridge.SplitOff P' (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ((2 : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal := by
  have hP'S : conjPl D P ∉ S0 := fun h => hPS (hS0 _ _ h (isConjPl_conjPl' D P))
  have hne := conjPl_ne_of_split D hP
  refine ⟨conjPl D P, isConjPl_conjPl D P, isSplitPl_conjPl D hP, hP'S, ?_, ?_, ?_, ?_⟩
  · refine ⟨by rw [conjIdeal_eq]; exact hne, fun h => hPS (hb _ (by exact_mod_cast h)), ?_⟩
    intro Q hQ he
    rw [conjIdeal_eq] at he
    have : Q = conjPl D P := HeightOneSpectrum.ext he
    exact hP'S (this ▸ hb Q (by exact_mod_cast hQ))
  · refine ⟨by rw [conjIdeal_eq, conjPl_conjPl]; exact hne.symm,
      fun h => hP'S (hb _ (by exact_mod_cast h)), ?_⟩
    intro Q hQ he
    rw [conjIdeal_eq, conjPl_conjPl] at he
    have : Q = P := HeightOneSpectrum.ext he
    exact hPS (this ▸ hb Q (by exact_mod_cast hQ))
  · exact fun h => hPS (h2 h)
  · exact fun h => hP'S (h2 h)

end GlobalTheory.ConjPlaceOff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSetStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugate_splitPlace_off_stableSet : ∀ (D : D7) (S0 : Finset (PlE D.host)) (Sb : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : PlE D.host),
    (∀ P1 P2, P1 ∈ S0 → IsConjPl D.host P1 P2 → P2 ∈ S0) → placesOver D.host.E 2 ⊆ (S0 : Set (PlE D.host)) →
    (∀ Q ∈ Sb, Q ∈ S0) → IsSplitPl D.host P → P ∉ S0 →
    ∃ P' : PlE D.host, IsConjPl D.host P P' ∧ IsSplitPl D.host P' ∧ P' ∉ S0 ∧
      Formalism.IndefR.Bridge.SplitOff P (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      Formalism.IndefR.Bridge.SplitOff P' (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ((2 : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal := by
  first | exact @GlobalTheory.ConjPlaceOff.exists_conj_off | exact GlobalTheory.ConjPlaceOff.exists_conj_off | (intros; apply GlobalTheory.ConjPlaceOff.exists_conj_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DropPlInsert
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def OffPl {S T' : HSp D} (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (u : WO S T') : Prop :=
  u.map (infPart D) = 0 ∧
    ∀ v ∈ Sb, ∀ ε, IsPlaceIdem D v ε → ∀ i j, algebraMap (AF D.host.F) (AE D) ε * u i j = 0

def SuppIn (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (V : HSp D) (g : GA D V) : Prop :=
  (mt V g - 1).map (infPart D) = 0 ∧
    ∀ v, v ∉ Sb → ∀ ε, IsPlaceIdem D v ε → ∀ i j, algebraMap (AF D.host.F) (AE D) ε * (mt V g - 1) i j = 0

def Over (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal

def LikeOff (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ c : WO (Vc D i) (Wc D i) →₀ ℂ, (∀ u ∈ c.support, OffPl Sb u) →
    (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u (R.vP i t)) = 0 →
    (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u f) = 0

def TypeIn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t), SuppIn Sb (Vc D i) κ →
    R.ωP i t (κ, 1) f = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • f

def CleanIn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) →
    (∃ v ∈ Sb, Over PP.1 v) → ∀ κ : G → GA D (Vc D i), IsLifts R i t κ →
      (∀ g, mirC R i PP a tr ε g ≠ 0 → SuppIn Sb (Vc D i) (κ g)) → avgW R i t PP a tr ε κ f = 0

def StepGen (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    Set (WO (Vc D i) (Wc D i) → ℂ) :=
  {φ | ∃ (g : GA D (Wc D i)) (f : WO (Vc D i) (Wc D i) → ℂ),
    TypeIn R i t Sb f ∧ CleanIn R i t Sb f ∧ LikeOff R i t Sb f ∧ φ = R.ωP i t (1, g) f}


open Classical in
def dropPl (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  Sb.erase v

theorem dropPl_insert [DecidableEq (HeightOneSpectrum (𝓞 D.host.F))] {s : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ s) : dropPl (insert v s) v = s := by
  unfold dropPl
  convert Finset.erase_insert hv

end GlobalTheory.DownLift.GenFinite

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SubquotientOfProductOfSupport
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocGL.SupportPerm

theorem isSubquotient_prodIrr_of_hasSupport : ZelevinskyPolynomialRing → BernsteinZelevinskyFiniteness →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
      (n t : ℕ) (τ : IrrRep (GL (Fin n) k)) (x : Fin t → IrrGL (k := k)) (hd : ∑ i, (x i).1 = n),
      HasSupport τ.ρ (Finset.univ.val.map x) → IsSubquotient τ.ρ (prodIrr x hd) := by
  intro hZ _ k _ _ _ _ _ n t τ x hd hs
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hZ k
  have h1 := SupportRing.pos_pc_sub hΨ hs τ.smooth τ.irr
  obtain ⟨hp, ep⟩ := SupportRing.prodIrr_cls hΨ x hd
  refine SupportRing.isSubquotient_of_clsGL_ne hp τ.smooth τ.irr ?_
  have h2 := h1 (IrrGL.of τ.ρ τ.smooth τ.irr)
  rw [SupportRing.pc_map, ← ep] at h2
  have e1 : ∀ (A : GrothGL k) (y : IrrGL (k := k)), Ψ.symm (Ψ A - SupportRing.bas Ψ y) y = A y - 1 := by
    intro A y
    rw [SupportRing.bas, ← map_sub, Ψ.symm_apply_apply, Finsupp.sub_apply, Finsupp.single_eq_same]
  rw [e1] at h2
  intro h3
  rw [h3] at h2
  exact absurd h2 (by norm_num)

end GlobalTheory.LocGL.SupportPerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnDownwardThetaLiftIntegrand
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnDownwardThetaLiftIntegrand
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.DownLift.GenFinite

theorem thetaKO_smul {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (h : GA D S)
    (g : GA D T) (c : ℂ) (f : WO S T → ℂ) : thetaKO om h g (c • f) = c * thetaKO om h g f := by
  simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]

theorem integrableOn_downIntegrand : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP →
    ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ) (l : (R.cV i).W →ₗ[ℂ] ℂ)
      (g : GA D (Wc D i)), IsThetaFunO R.ψ (Vc D i) (Wc D i) f →
      IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y f l g hf
  have hm := hG.core.models
  have hom := (hP i t).datum
  have hx := (hm.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [hm.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have hcont : Continuous fun h => l (R.extV i t y h) :=
    (LinearMap.continuous_of_finiteDimensional l).comp
      (GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) (R.βV i) (R.datVt i t) hx)
  have hinv : ∀ γ ∈ GQ (Vc D i), ∀ h, l (R.extV i t y (γ * h)) = l (R.extV i t y h) := fun γ hγ h =>
    congrArg l (GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx γ hγ h)
  have key := GlobalTheory.DefiniteQuotient.integrableOn_theta D R.ψ hom.std (Vc D i) (Wc D i) _ _ (R.ωP i t) hom hpos ℂ
    (LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) f) (fun x => theta_smul x hf) (fun h => l (R.extV i t y h)) hcont hinv
    (R.νV i t) (R.fdV i t) (hm.νV i t).1.1 (hm.νV i t).2 g
  have e : (fun h => thetaKO (R.ωP i t) h g (LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) f (l (R.extV i t y h)))) =
      fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h) := by
    funext h
    exact (thetaKO_smul (R.ωP i t) h g _ f).trans (mul_comm _ _)
  rw [e] at key
  exact key

end GlobalTheory.DownLift.GenFinite

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnDownwardThetaLiftIntegrandStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_downwardThetaLift_integrand : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := by
  first | exact @GlobalTheory.DownLift.GenFinite.integrableOn_downIntegrand | exact GlobalTheory.DownLift.GenFinite.integrableOn_downIntegrand | (intros; apply GlobalTheory.DownLift.GenFinite.integrableOn_downIntegrand <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterEqProdSupercuspidalSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterEqProdSupercuspidalSupport
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CentralSupport

theorem piTensor_scalar {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a) (c : α → ℂ)
    (h : ∀ a v, ρ a (g a) v = c a • v) (y : ⨂[ℂ] a, X a) : piTensor ρ g y = (∏ a, c a) • y := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, smul_comm, piTensor_tprod]
    congr 1
    simp only [h]
    exact MultilinearMap.map_smul_univ _ _ _

theorem sum_card_mul_modExp {α : Type} [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] :
    ∑ a, (Fintype.card (m a) : ℤ) * modExp m a = 0 := by
  simp only [modExp, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_filter]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prod_absPow {α : Type} (S : Finset α) (c : α → ℂ) : ∏ a ∈ S, absPow k (c a) = absPow k (∑ a ∈ S, c a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, absPow_add]

theorem absPow_pow (s : ℂ) (N : ℕ) (z : kˣ) : absPow k s (z ^ N) = absPow k (N * s) z := by
  ext
  rw [map_pow, Units.val_pow_eq_pow_val, val_absPow, val_absPow, Complex.cpow_nat_mul]

theorem deltaHalf_scalar {α : Type} [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] (z : kˣ) : deltaHalf k m (fun a => GeneralLinearGroup.scalar (m a) z) = 1 := by
  have hd : ∀ a, GeneralLinearGroup.det (GeneralLinearGroup.scalar (m a) z) = z ^ Fintype.card (m a) := fun a => by
    ext; simp [GeneralLinearGroup.scalar]
  rw [deltaHalf_apply]
  simp only [hd, absPow_pow]
  rw [← MonoidHom.finsetProd_apply, prod_absPow]
  have h0 : ∑ a, ((Fintype.card (m a) : ℕ) : ℂ) * ((modExp m a : ℂ) / 2) = 0 := by
    have := congrArg (fun t : ℤ => (t : ℂ) / 2) (sum_card_mul_modExp m)
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_zero, zero_div, Finset.sum_div] at this
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [h0, absPow_zero, MonoidHom.one_apply]

theorem hasCentralChar_multiProd_prod {α n : Type} [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n]
    {c : α → Type} [∀ a, Fintype (c a)] [∀ a, DecidableEq (c a)] (e : (Σ a, c a) ≃ n)
    {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (c a) k) (X a)) (ω : α → kˣ →* ℂˣ)
    (hω : ∀ a, HasCentralChar (σ a) (ω a)) : HasCentralChar (multiProd e σ) (∏ a, ω a) := by
  intro z f
  have h1 : leviEmb k e (fun a => GeneralLinearGroup.scalar (c a) z) = GeneralLinearGroup.scalar n z := by
    ext i j
    obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b', y'⟩, rfl⟩ := e.surjective j
    by_cases hb : b = b'
    · subst hb
      rw [leviEmb_apply_same]
      simp [GeneralLinearGroup.scalar, diagonal_apply]
    · rw [leviEmb_apply_ne _ _ _ hb]
      simp [GeneralLinearGroup.scalar, diagonal_apply, hb]
  have h4 := parInd_law e (piTensor σ) f
    ⟨_, leviEmb_mem_parab k e (fun a => GeneralLinearGroup.scalar (c a) z)⟩
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  have h5 := h4 x
  rw [leviProj_leviEmb, deltaHalf_scalar, piTensor_scalar σ _ (fun a => (ω a z : ℂ)) (fun a => hω a z)] at h5
  have hc : x * GeneralLinearGroup.scalar n z = GeneralLinearGroup.scalar n z * x := by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  show f.1.1 (x * GeneralLinearGroup.scalar n z) = ((∏ a, ω a) z : ℂ) • f.1.1 x
  rw [hc, ← h1, MonoidHom.finsetProd_apply, Units.coe_prod]
  simpa using h5

theorem centralChar_eq_prod_support : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)) (s : Multiset (IrrGL (k := k)))
    (ω : kˣ →* ℂˣ), HasSupport x.rep s → HasCentralChar x.rep ω → ∃ f : IrrGL (k := k) → kˣ →* ℂˣ,
      (∀ y ∈ s, HasCentralChar y.rep (f y)) ∧ ∀ z, ω z = (s.map fun y => f y z).prod := by
  intro _ k _ _ _ _ _ x s ω hs hω
  choose f _ hf using fun y : IrrGL (k := k) => LocGL.exists_smooth_hasCentralChar y.2.rep.smooth y.2.rep.irr
  refine ⟨f, fun y _ => hf y, fun z => ?_⟩
  obtain ⟨h, x', rfl, hi, -, e, hsub⟩ := hs
  have hcen := hasCentralChar_multiProd_prod e (fun a => (x' a).rep) (fun a => f (x' a)) (fun a => hf (x' a))
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : x.2.rep.V)
  have h1 := Model.scalar_of_isSubquotient hsub (hcen z) v
  rw [hω] at h1
  have h2 := smul_left_injective ℂ hv h1
  rw [Multiset.map_map]
  change ω z = ∏ a, f (x' a) z
  apply Units.ext
  rw [h2, MonoidHom.finsetProd_apply]

end GlobalTheory.CentralSupport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterEqProdSupercuspidalSupportStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralCharacter_eq_prod_supercuspidalSupport : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)) (s : Multiset (IrrGL (k := k))) (ω : kˣ →* ℂˣ), HasSupport x.rep s → HasCentralChar x.rep ω → ∃ f : IrrGL (k := k) → kˣ →* ℂˣ, (∀ y ∈ s, HasCentralChar y.rep (f y)) ∧ ∀ z, ω z = (s.map fun y => f y z).prod := by
  first | exact @GlobalTheory.CentralSupport.centralChar_eq_prod_support | exact GlobalTheory.CentralSupport.centralChar_eq_prod_support | (intros; apply GlobalTheory.CentralSupport.centralChar_eq_prod_support <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGapNonemptyAndRecordNonempty
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocTheoryTied
open Formalism Formalism.BasicNotions
namespace GlobalTheory.MemLoc

theorem exists_locTheory_tied : ∃ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)),
    Nonempty (∀ (l : ℕ) [Fact l.Prime], LocTied l (L l) (A l)) := by
  choose P A h using exists_locPrime_tied
  exact ⟨fun l _ => P l, fun l _ => A l, ⟨fun l _ => (h l).some⟩⟩
end GlobalTheory.MemLoc
end

open Formalism Formalism.BasicNotions
namespace GlobalTheory.MemLoc

theorem localGap_nonempty : ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R),
    Nonempty (Formalism.BasicNotions.Examples₂.LocalGap H) := by
  intro R H
  obtain ⟨L, A, ⟨T⟩⟩ := exists_locTheory_tied
  exact ⟨⟨L, A, T⟩⟩

theorem record_nonempty : Nonempty Formalism.BasicNotions.D7 :=
  Formalism.BasicNotions.Examples₂.record_nonempty_of_localGap (localGap_nonempty _)

end GlobalTheory.MemLoc
end
