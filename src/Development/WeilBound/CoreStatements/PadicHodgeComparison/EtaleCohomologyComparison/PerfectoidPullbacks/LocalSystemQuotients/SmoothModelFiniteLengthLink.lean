module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.IsProperOfProj
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelOneGradedFinite
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.PolyAll

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelOneVanishAboveDim
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelOneVanishAboveDim
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.WittLevel.Van

theorem dividedPowerFiltration_eq_bot {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (hJ : J = ⊥) {r : ℕ} (hr : 1 ≤ r) :
    pdP δ r = ⊥ := by
  subst hJ
  refine Ideal.span_eq_bot.2 ?_
  rintro _ ⟨l, hl, hs, rfl⟩
  have h : ∃ p ∈ l, p.1 ≠ 0 := by
    by_contra h
    push Not at h
    have : (l.map Prod.fst).sum = 0 := List.sum_eq_zero (by simpa using h)
    omega
  obtain ⟨p, hp, h0⟩ := h
  refine List.prod_eq_zero (List.mem_map.2 ⟨p, hp, ?_⟩)
  have e : p.2 = 0 := hl p hp
  rw [e]
  exact δ.dpow_eval_zero h0

theorem van_on {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (hI : I = ⊥) (p : ℕ) (hp : p ≠ 0)
    (hn : IsNilpotent (p : R)) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) {V : X.Opens} {e : ℕ}
    (c : Coord q V e) (d : ℕ) (he : e ≤ d) (j : ℕ) :
    Subsingleton (CH.H (sq (sFil (St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {V}) ((d : ℤ) + 1)) (IdF.bot _)) j) := by
  obtain ⟨c', -, -⟩ := GlobalTheory.CompanionTheory.FlatChartP.exists_flat_chart γ p hp hn q κ c
  have hgood := GlobalTheory.CompanionTheory.ChartMaps.good c'
  have hQ : ∀ T, St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {V} T → InU V T := by
    rintro T ⟨-, W, rfl, h⟩
    exact h
  have hD : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {V} c'.D := ⟨trivial, V, rfl, c'.inV⟩
  have hpow : ∀ r, c'.D.pdPow r = (pdP γ r).map c'.D.i := fun r =>
    GlobalTheory.CompanionTheory.ChartFil.dividedPowerFiltration_eq_map γ c'.D.δ c'.D.i c'.D.compat c'.J_eq r
  obtain ⟨PQ, hPQ⟩ := CrystallineSemistableComparison.Pb.Site.poly_all' γ p hp q κ ⊤ (Or.inl rfl) {V}
  refine CrystallineSemistableComparison.Pb.vanishing_of_ladder e PQ (a := sFil _) (b := fun _ => IdF.bot _) (c'.frame hgood _ hQ hD) ((d : ℤ) + 1)
    ⟨fun r' T x hx => ?_, fun r' _ => (hPQ r').1, fun r' _ => (hPQ r').2.1⟩ (fun r' h1 _ x hx => ?_) j
  · have h0 : x = 0 := hx
    rw [h0]
    exact Ideal.zero_mem _
  · have h2 : (show c'.D.B from x) ∈ c'.D.pdPow r'.toNat := hx
    rw [hpow, dividedPowerFiltration_eq_bot γ hI (by omega), Ideal.map_bot] at h2
    exact h2

theorem Im_one_eq_bot (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] : Wc.Im l k 1 = ⊥ := by
  refine (Ideal.map_eq_bot_iff_le_ker _).2 ?_
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  simpa using Ideal.mem_span_singleton_self _

theorem nat_eq_zero (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] :
    ((l : ℕ) : Wc.Wm l k 1) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
  simpa using Ideal.mem_span_singleton_self _

theorem witt_level_one_filtration_vanish : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (U : Cov q) (d : ℕ), (∀ α, U.d α ≤ d) →
    ∀ j, Subsingleton (CH.H (sq (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) ((d : ℤ) + 1)) (IdF.bot _)) j) := by
  intro l _ k _ _ _ O _ X q ρ U d hd j
  have hp : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hn : IsNilpotent ((l : ℕ) : Wc.Wm l k 1) := by
    rw [nat_eq_zero]
    exact IsNilpotent.zero
  refine (GlobalTheory.T.stable_cover_cech_vanishing.1 (sq (thFil (nlFun (Wc.pd l k 1) l X q ((Wc.res l k 1).comp ρ)) ((d : ℤ) + 1)) (IdF.bot _))
    (⊤ : ObjectProperty (Thick (nlFun (Wc.pd l k 1) l X q ((Wc.res l k 1).comp ρ)))) U.U 0).2.1 (fun S hS j => ?_) j
  obtain ⟨α, hα⟩ := id hS
  obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (U.c α) (iInf₂_le α hα) (U.inter S hS)
  exact van_on (Wc.pd l k 1) (Im_one_eq_bot l k) l hp hn q _ c' d (hd α) j

end GlobalTheory.CompanionTheory.WittLevel.Van
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelOneVanishAboveDimStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_level_one_vanish_above_dim : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (U : Cov q) (d : ℕ), (∀ α, U.d α ≤ d) →
    ∀ j, Subsingleton (CH.H (sq (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) ((d : ℤ) + 1)) (IdF.bot _)) j) := by
  first | exact @GlobalTheory.CompanionTheory.WittLevel.Van.witt_level_one_filtration_vanish | exact GlobalTheory.CompanionTheory.WittLevel.Van.witt_level_one_filtration_vanish | (intros; apply GlobalTheory.CompanionTheory.WittLevel.Van.witt_level_one_filtration_vanish <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthWittCohomology
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthWittCohomology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LevelOne

universe w w'

theorem mapH_injective {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K : Cx.{w} R} {L : Cx.{w'} R'}
    (φ : Cx.Hom K L σ) (hi : ∀ n, Function.Injective (φ.f n)) (hs : ∀ n, Function.Surjective (φ.f n)) (n : ℕ) :
    Function.Injective (φ.mapH n) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h0 : φ.mapZ n z ∈ (L.B n).submoduleOf (L.Z n) := (Submodule.Quotient.mk_eq_zero _).1 hx
  have h1 : φ.f n z.1 ∈ L.B n := h0
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  change z.1 ∈ K.B n
  cases n with
  | zero =>
    have h2 : φ.f 0 z.1 = 0 := h1
    exact hi 0 (h2.trans (map_zero _).symm)
  | succ n =>
    obtain ⟨w, hw⟩ := h1
    obtain ⟨w', rfl⟩ := hs n w
    rw [φ.comm] at hw
    exact ⟨w', hi _ hw⟩

theorem isNoetherian_of_surj {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (h : Function.Surjective (algebraMap R S)) [IsNoetherian S M] : IsNoetherian R M := by
  let f : Submodule R M →o Submodule S M :=
    { toFun := fun N =>
        { carrier := N
          add_mem' := N.add_mem
          zero_mem' := N.zero_mem
          smul_mem' := fun c x hx => by
            obtain ⟨r, rfl⟩ := h c
            rw [algebraMap_smul]
            exact N.smul_mem r hx }
      monotone' := fun _ _ h => h }
  have hf : StrictMono f := Monotone.strictMono_of_injective f.monotone fun N N' e => by
    ext x
    exact iff_of_eq (congrArg (fun P : Submodule S M => x ∈ P) e)
  rw [isNoetherian_iff']
  exact hf.wellFoundedGT

section Witt

variable (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l]

theorem span_l_isMaximal : (Ideal.span {(l : WittVector l k) ^ 1}).IsMaximal := by
  have e : Ideal.span {(l : WittVector l k) ^ 1} = RingHom.ker (WittVector.constantCoeff (p := l) (R := k)) := by
    ext x
    rw [pow_one, WittVector.mem_span_p_iff_coeff_zero_eq_zero, RingHom.mem_ker, WittVector.constantCoeff_apply]
  rw [e]
  exact RingHom.ker_isMaximal_of_surjective _ (WittVector.constantCoeff_surjective l)

theorem wm_artinian : IsArtinianRing (Wc.Wm l k 1) := by
  haveI := span_l_isMaximal l k
  letI := Ideal.Quotient.field (Ideal.span {(l : WittVector l k) ^ 1})
  infer_instance

end Witt

section Site

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
  (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k)

abbrev QAll : ObjectProperty (Thick (nlFun (Wc.pd l k 1) l X q ((Wc.res l k 1).comp ρ))) :=
  St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ {⊤}

theorem qAll_all (T : Thick (nlFun (Wc.pd l k 1) l X q ((Wc.res l k 1).comp ρ))) : QAll q ρ T :=
  ⟨trivial, ⊤, rfl, fun _ _ => trivial⟩

def toAll : CH.Mor (Wc.OM l (B.schFn q) ρ 1) (CH.modF (sP (QAll q ρ)).A) (Ideal.Quotient.mk _) where
  G := (QAll q ρ).ι
  τ T := { toFun := fun z => z, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  nat _ _ := rfl

theorem toAll_inj (n : ℕ) : Function.Injective ((toAll q ρ).hom.f n) := by
  intro f f' h
  funext s
  exact congrFun h (s ⋙ (QAll q ρ).lift (𝟭 _) (qAll_all q ρ))

theorem toAll_surj (n : ℕ) : Function.Surjective ((toAll q ρ).hom.f n) := by
  intro g
  exact ⟨fun s => g (s ⋙ (QAll q ρ).lift (𝟭 _) (qAll_all q ρ)), rfl⟩

theorem toAll_pull_inj (j : ℕ) : Function.Injective ((toAll q ρ).pull j) :=
  mapH_injective _ (toAll_inj q ρ) (toAll_surj q ρ) j

end Site

theorem finiteLength_level_one : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (j : ℕ),
    Module.Finite (Wc.Wm l k 1) (HO (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ {⊤}) j) →
    IsFiniteLength (WittVector l k) (CH.H (Wc.OM l (B.schFn q) ρ 1) j) := by
  intro l _ k _ _ _ O _ X q ρ j hfin
  haveI := wm_artinian l k
  letI : Module (WittVector l k) (HO (QAll q ρ) j) := Module.compHom _ (algebraMap (WittVector l k) (Wc.Wm l k 1))
  haveI : IsScalarTower (WittVector l k) (Wc.Wm l k 1) (HO (QAll q ρ) j) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hsurj : Function.Surjective (algebraMap (WittVector l k) (Wc.Wm l k 1)) := Ideal.Quotient.mk_surjective
  haveI : IsNoetherian (Wc.Wm l k 1) (HO (QAll q ρ) j) := inferInstance
  haveI : IsArtinian (Wc.Wm l k 1) (HO (QAll q ρ) j) := inferInstance
  haveI : IsNoetherian (WittVector l k) (HO (QAll q ρ) j) := isNoetherian_of_surj hsurj
  haveI : IsArtinian (WittVector l k) (HO (QAll q ρ) j) := isArtinian_of_surjective_algebraMap hsurj
  let f : CH.H (Wc.OM l (B.schFn q) ρ 1) j →ₗ[WittVector l k] HO (QAll q ρ) j :=
    { toFun := (toAll q ρ).pull j
      map_add' := map_add _
      map_smul' := fun r x => ((toAll q ρ).pull j).map_smulₛₗ r x }
  have hf : Function.Injective f := toAll_pull_inj q ρ j
  exact isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨isNoetherian_of_injective f hf, isArtinian_of_injective f hf⟩

end GlobalTheory.CompanionTheory.LevelOne
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthWittCohomologyStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_length_witt_cohomology : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (j : ℕ),
    Module.Finite (Wc.Wm l k 1) (HO (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ {⊤}) j) →
    IsFiniteLength (WittVector l k) (CH.H (Wc.OM l (B.schFn q) ρ 1) j) := by
  first | exact @GlobalTheory.CompanionTheory.LevelOne.finiteLength_level_one | exact GlobalTheory.CompanionTheory.LevelOne.finiteLength_level_one | (intros; apply GlobalTheory.CompanionTheory.LevelOne.finiteLength_level_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquarePullBijectiveOfAcyclic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquarePullBijectiveOfAcyclic
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LengthOneCochainExactness

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

noncomputable def incl (b : IdF A) : CH.Mor (sq b (IdF.bot A)) (CH.modF A) (RingHom.id R) where
  G := 𝟭 C
  τ T := (AlgEquiv.quotientBot R (A.obj T)).toLinearMap ∘ₗ (sqM b (IdF.bot A) T).subtype
  nat φ x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

theorem incl_mem (b : IdF A) {T : C} (x : (sq b (IdF.bot A)).obj T) : (incl b).τ T x ∈ b.S T := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  exact hy

theorem cochain_exact (a b : IdF A) (ha : ∀ T, a.S T = ⊤) :
    (∀ n, Function.Injective ((incl b).hom.f n)) ∧
    (∀ n, Function.Exact ((incl b).hom.f n) ((toSq a b ha).hom.f n)) ∧
    ∀ n, Function.Surjective ((toSq a b ha).hom.f n) := by
  refine ⟨fun n x y hxy => ?_, fun n y => ⟨fun hy => ?_, ?_⟩, fun n y => ?_⟩
  · funext s
    have h : (incl b).τ _ (x (s ⋙ 𝟭 C)) = (incl b).τ _ (y (s ⋙ 𝟭 C)) := congrFun hxy s
    exact Subtype.ext ((AlgEquiv.quotientBot R _).injective h)
  · have hm : ∀ s : ComposableArrows C n,
        (show A.obj (s.obj (Fin.last n)) from y s) ∈ b.S (s.obj (Fin.last n)) := fun s => by
      have h := congrArg Subtype.val (congrFun hy s)
      exact Ideal.Quotient.eq_zero_iff_mem.1 h
    exact ⟨fun s => sqMk b (IdF.bot A) _ (hm s), rfl⟩
  · rintro ⟨x, rfl⟩
    funext s
    exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 (incl_mem b (x (s ⋙ 𝟭 C))))
  · have hm : ∀ s : ComposableArrows C n, ∃ t : A.obj (s.obj (Fin.last n)),
        Ideal.Quotient.mk _ t = (show sqM a b _ from y s).1 :=
      fun s => Ideal.Quotient.mk_surjective _
    choose t ht using hm
    exact ⟨t, funext fun s => Subtype.ext (ht s)⟩

theorem pull_toSq_bijective (a b : IdF A) (ha : ∀ T, a.S T = ⊤) :
    (∀ j, Subsingleton (CH.H (sq b (IdF.bot A)) j)) →
      ∀ j, Function.Bijective ((toSq a b ha).pull j) := by
  intro hv j
  obtain ⟨hf, hfg, hg⟩ := cochain_exact a b ha
  obtain ⟨δ, -, -, hex, hex2, -⟩ := CrystallineSemistableComparison.P.les _ _ hf hfg hg
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (hex j x).1 hx
    rw [(hv j).elim y 0, map_zero]
  · intro y
    obtain ⟨x, hx⟩ := (hex2 j y).1 ((hv (j + 1)).elim _ _)
    exact ⟨x, hx⟩

end GlobalTheory.CompanionTheory.LengthOneCochainExactness
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquarePullBijectiveOfAcyclicStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_pull_bijective_of_acyclic : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) (ha : ∀ T, a.S T = ⊤),
    (∀ j, Subsingleton (CH.H (sq b (IdF.bot A)) j)) → ∀ j, Function.Bijective ((toSq a b ha).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.LengthOneCochainExactness.pull_toSq_bijective | exact GlobalTheory.CompanionTheory.LengthOneCochainExactness.pull_toSq_bijective | (intros; apply GlobalTheory.CompanionTheory.LengthOneCochainExactness.pull_toSq_bijective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredModuleFiniteOfGraded
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredModuleFiniteOfGraded
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LenDev

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem finite_mid [IsNoetherianRing R] {M₁ M₂ M₃ : Type 1} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (e : Function.Exact f g)
    [Module.Finite R M₁] [Module.Finite R M₃] : Module.Finite R M₂ := by
  have h₁ : Module.Finite R (LinearMap.ker g) := by
    rw [LinearMap.exact_iff.1 e]
    exact Module.Finite.range f
  have h₂ : Module.Finite R (M₂ ⧸ LinearMap.ker g) :=
    Module.Finite.equiv g.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker g)

theorem H_subsingleton (F : C ⥤ ModuleCat.{0} R) (h : ∀ T, Subsingleton (F.obj T)) (n : ℕ) :
    Subsingleton (CH.H F n) := by
  have hX : Subsingleton ((CH.cx F).X n) := ⟨fun a b => funext fun s => (h _).elim _ _⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).1 x
  obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).1 y
  have e : a = b := hX.elim _ _
  subst e
  rfl

theorem sqM_rep (a b : IdF A) (T : C) (x : sqM a b T) :
    ∃ (y : A.obj T) (hy : y ∈ a.S T), x = sqMk a b y hy := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  exact ⟨y, hy, rfl⟩

theorem sq_self_subsingleton (a : IdF A) (T : C) : Subsingleton ((sq a a).obj T) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x', hx, rfl⟩ := sqM_rep a a T x
  obtain ⟨y', hy, rfl⟩ := sqM_rep a a T y
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ x' = Ideal.Quotient.mk _ y'
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hx, Ideal.Quotient.eq_zero_iff_mem.2 hy]

variable {a b c : IdF A}

theorem sq_inj (hba : ∀ T, b.S T ≤ a.S T) (T : C) :
    Function.Injective ((sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).τ T) := by
  intro x y h
  obtain ⟨x', hx, rfl⟩ := sqM_rep b c T x
  obtain ⟨y', hy, rfl⟩ := sqM_rep b c T y
  have h' := congrArg (fun z : sqM a c T => z.1) h
  exact Subtype.ext h'

theorem sq_exact (hba : ∀ T, b.S T ≤ a.S T) (hcb : ∀ T, c.S T ≤ b.S T) (T : C) :
    Function.Exact ((sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).τ T)
      ((sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).τ T) := by
  intro x
  obtain ⟨x', hx, rfl⟩ := sqM_rep a c T x
  constructor
  · intro h
    have h' : (Ideal.Quotient.mk (b.S T) x') = 0 := congrArg Subtype.val h
    exact ⟨sqMk b c x' (Ideal.Quotient.eq_zero_iff_mem.1 h'), rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨y', hy', rfl⟩ := sqM_rep b c T y
    have e : (Ideal.Quotient.mk (c.S T) y') = Ideal.Quotient.mk (c.S T) x' := congrArg Subtype.val hy
    refine Subtype.ext ?_
    change Ideal.Quotient.mk (b.S T) x' = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have := Ideal.Quotient.eq.1 e
    have h2 := hcb T this
    have h3 := (b.S T).sub_mem hy' h2
    simpa using h3

theorem sq_surj (hcb : ∀ T, c.S T ≤ b.S T) (T : C) :
    Function.Surjective ((sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).τ T) := by
  intro x
  obtain ⟨x', hx, rfl⟩ := sqM_rep a b T x
  exact ⟨sqMk a c x' hx, rfl⟩

theorem sq_les (hba : ∀ T, b.S T ≤ a.S T) (hcb : ∀ T, c.S T ≤ b.S T) (n : ℕ) :
    Function.Exact ((sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).pull n)
      ((sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).pull n) := by
  obtain ⟨δ, -, -, e, -⟩ := CrystallineSemistableComparison.P.les
    (sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).hom
    (sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).hom
    (fun n x y h => funext fun s => sq_inj hba _ (congrFun h s))
    (fun n y => ⟨fun hy => ⟨fun s => ((sq_exact hba hcb _ (y s)).1 (congrFun hy s)).choose,
        funext fun s => ((sq_exact hba hcb _ (y s)).1 (congrFun hy s)).choose_spec⟩, by
      rintro ⟨x, rfl⟩
      funext s
      exact (sq_exact hba hcb _ _).2 ⟨_, rfl⟩⟩)
    (fun n y => ⟨fun s => (sq_surj hcb _ (y s)).choose, funext fun s => (sq_surj hcb _ (y s)).choose_spec⟩)
  exact e n

theorem finite_dev [IsNoetherianRing R] (a : ℕ → IdF A) (hanti : ∀ k l, k ≤ l → ∀ T, (a l).S T ≤ (a k).S T) (s n : ℕ)
    (hgr : ∀ r, r < s → Module.Finite R (CH.H (sq (a r) (a (r + 1))) n)) :
    ∀ (d r : ℕ), r + d = s → Module.Finite R (CH.H (sq (a r) (a s)) n) := by
  intro d
  induction d with
  | zero =>
    intro r h
    obtain rfl : r = s := by omega
    have := H_subsingleton _ (sq_self_subsingleton (a r)) n
    exact Module.Finite.of_finite
  | succ d ih =>
    intro r h
    have := ih (r + 1) (by omega)
    have := hgr r (by omega)
    exact finite_mid _ _ (sq_les (hanti r (r + 1) (by omega)) (hanti (r + 1) s (by omega)) n)

theorem finite_H_sq : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (Fil : ℤ → IdF A),
    (∀ r r' : ℤ, r ≤ r' → ∀ T, (Fil r').S T ≤ (Fil r).S T) → ∀ s : ℕ,
    (∀ r : ℕ, r < s → ∀ j, Module.Finite R (CH.H (sq (Fil r) (Fil ((r : ℤ) + 1))) j)) →
    ∀ j, Module.Finite R (CH.H (sq (Fil 0) (Fil s)) j) := by
  intro R _ _ C _ A Fil hanti s hgr j
  have key := finite_dev (fun r : ℕ => Fil (r : ℤ))
    (fun k l h T => hanti _ _ (by exact_mod_cast h) T) s j
    (fun r hr => by
      have h := hgr r hr j
      rw [← Nat.cast_succ] at h
      exact h) s 0 (by omega)
  beta_reduce at key
  rw [Nat.cast_zero] at key
  exact key

end GlobalTheory.CompanionTheory.LenDev
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredModuleFiniteOfGradedStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtered_module_finite_of_graded : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (Fil : ℤ → IdF A),
    (∀ r r' : ℤ, r ≤ r' → ∀ T, (Fil r').S T ≤ (Fil r).S T) → ∀ s : ℕ,
    (∀ r : ℕ, r < s → ∀ j, Module.Finite R (CH.H (sq (Fil r) (Fil ((r : ℤ) + 1))) j)) →
    ∀ j, Module.Finite R (CH.H (sq (Fil 0) (Fil s)) j) := by
  first | exact @GlobalTheory.CompanionTheory.LenDev.finite_H_sq | exact GlobalTheory.CompanionTheory.LenDev.finite_H_sq | (intros; apply GlobalTheory.CompanionTheory.LenDev.finite_H_sq <;> assumption)
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

private lemma isHecke_div_and_resEtaPow_div {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (d : ℕ)
    (hvan : ∀ j, Subsingleton (CH.H (sq (sFil Q (↑d + 1)) (IdF.bot (sP Q).A)) j))
    (hN : IsNoetherianRing b.R)
    (hgr : ∀ r j : ℕ, Module.Finite b.R (CH.H (sq (sFil Q ↑r) (sFil Q (↑r + 1))) j)) (j : ℕ) :
    Module.Finite b.R (HO Q j) := by
  have hfin := GlobalTheory.T.filtered_module_finite_of_graded (sFil Q) (fun r r' h T => (isFil Q).anti h T) (d + 1) (fun r _ j' => hgr r j') j
  rw [Nat.cast_add, Nat.cast_one] at hfin
  have ha : ∀ T, (sFil Q 0).S T = ⊤ := fun T => (isFil Q).top 0 le_rfl T
  have hb := GlobalTheory.T.square_pull_bijective_of_acyclic (sFil Q 0) (sFil Q (↑d + 1)) ha ?hv j
  · exact Module.Finite.of_surjective (hM := hfin) (LinearEquiv.ofBijective _ hb).symm.toLinearMap
      (LinearEquiv.ofBijective _ hb).symm.surjective
  · exact hvan

theorem wittCohomology_finite_length {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] [Smooth q] (ρ : O →+* k) (j : ℕ) :
    IsFiniteLength (WittVector l k) (CH.H (Wc.OM l (B.schFn q) ρ 1) j) := by
  obtain ⟨U⟩ := (CrystallineSemistableComparison.Pb.cov_ex q).1 inferInstance
  refine GlobalTheory.T.finite_length_witt_cohomology q ρ j ?_
  have hvan := GlobalTheory.T.witt_level_one_vanish_above_dim q ρ U (Finset.univ.sup U.d) (fun α => Finset.le_sup (Finset.mem_univ α))
  have hfin := isHecke_div_and_resEtaPow_div _ _ hvan ?hN ?hgr j
  · refine Module.Finite.of_surjective (hM := hfin)
      (LinearEquiv.ofBijective ((incl ?hle).o.pull j) ?hb).symm.toLinearMap (LinearEquiv.surjective _)
    · intro T hT
      exact ⟨hT.1, ⊤, Set.mem_singleton _, by simp [InU]⟩
    · refine (CrystallineSemistableComparison.Pb.zar ⊤ ?u (Set.range U.U) {⊤} _ ?hcov j).2.2
      · exact Or.inr ⟨(Fact.out : l.Prime).ne_zero, Or.inl rfl⟩
      · intro W hW
        rw [Set.mem_singleton_iff.mp hW, sSup_range, U.cover]
  · exact GlobalTheory.T.truncated_witt_isNoetherian
  · exact GlobalTheory.T.witt_level_one_graded_finite q ρ U

theorem smooth_model_finite_length_link {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K)
    (hM : M.Sm) (j : ℕ) : IsFiniteLength (WittVector l r.k) ((Wc.HS l (B.schFn M.p) r.ρ j).M 1) := by
  have : IsProper M.p := sm_proper hM
  have : Smooth M.p := hM.2
  exact wittCohomology_finite_length M.p r.ρ j

end CrystallineSemistableComparison.Pb
