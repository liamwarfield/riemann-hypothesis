module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryArchimedean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupFiniteDimensionalRepContainsHighestW
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralCompactLe
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open Neutral.B1 hiding G IsPlaceOver

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocDict

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

abbrev Kbar (w : HeightOneSpectrum (𝓞 E)) : Type := AlgebraicClosure (w.adicCompletion E)

abbrev GalLoc (w : HeightOneSpectrum (𝓞 E)) : Type := Kbar w ≃ₐ[w.adicCompletion E] Kbar w

def IsLocEmb (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (ι : Ω →ₐ[E] Kbar w) : Prop :=
  ∀ z, z ∈ A ↔ IsIntegral (w.adicCompletionIntegers E) (ι z)

def Lifts {w : HeightOneSpectrum (𝓞 E)} (ι : Ω →ₐ[E] Kbar w) (g : GalLoc w) (σ : G E Ω) : Prop :=
  ∀ z, g (ι z) = ι (σ z)

theorem Lifts.eq {w : HeightOneSpectrum (𝓞 E)} {ι : Ω →ₐ[E] Kbar w} {g : GalLoc w} {σ σ' : G E Ω}
    (H : Lifts ι g σ) (H' : Lifts ι g σ') : σ = σ' :=
  AlgEquiv.ext fun z => ι.toRingHom.injective ((H z).symm.trans (H' z))

variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

def HasNormGroups (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w) (a : Weil h →* (w.adicCompletion E)ˣ) : Prop :=
  ∀ L : IntermediateField (w.adicCompletion E) (Kbar w), IsFiniteAbelian (w.adicCompletion E) L →
    ∀ (σ : Weil h) (g : GalLoc w), Lifts ι g σ → ((∀ z ∈ L, g z = z) ↔ a σ ∈ normGroup (w.adicCompletion E) L)

end GlobalTheory.LocDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqIotaIffEqTransCastAdelicGroup
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.JIota

theorem heq_iota_iff_eq_trans_castAdelicGroup (D : D7) (I : Formalism.MainNotions.S.AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ι : GA D (D.sp.Y 0) ≃* I.GA) :
    HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv ↔
      ι = ((Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm)).toMulEquiv := by
  subst h
  rw [heq_iff_eq]
  constructor
  · intro e; subst e; rfl
  · intro e; subst e; rfl

theorem heq_iota_iff : ∀ (D : D7) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (ι : GA D (D.sp.Y 0) ≃* St.B.I.GA), HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv ↔ ι = (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv :=
  fun D St h ι => heq_iota_iff_eq_trans_castAdelicGroup D St.B.I h ι

end GlobalTheory.Mem.JIota
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

variable {F : Type} [Field F] {ι : Type} {m : ι → ℕ}

def Reps {X Y : GlobalTheory.ProjVar.Var F} (Eb : Fr (ratOf X) m 0) (S : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn)
    (f : Y.X ⟶ X.X) : Prop :=
  (ratOf X).IsHom (ratOf Y) φ f ∧
    (∀ z', ∀ A' ∈ S.S z', ∀ A ∈ Eb.S (f z'), Par 0 ((ratOf Y).O z').toSubring (A' * (A.map φ)⁻¹)) ∧
    ∀ (K : Type) [Field K] (x : Sp K ⟶ X.X), ∀ A ∈ Eb.S (x (IsLocalRing.closedPoint K)), ∀ h : Mat m K,
      Par 0 ⊤ h → ∃! p : Sp K ⟶ Y.X, p ≫ f = x ∧ Bears S φ A h p

theorem Refines.reps {X Y : GlobalTheory.ProjVar.Var F} {Eb : Fr (ratOf X) m 0} {S : Fr (ratOf Y) m m}
    {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (h : Refines Eb S φ f) : Reps Eb S φ f :=
  ⟨h.hom, h.sub, h.lifts⟩

def CoBear {X Y₁ Y₂ : GlobalTheory.ProjVar.Var F} (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn)
    (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) {K : Type} [Field K] (x : Sp K ⟶ X.X) (p₁ : Sp K ⟶ Y₁.X)
    (p₂ : Sp K ⟶ Y₂.X) : Prop :=
  ∃ A ∈ Eb.S (x (IsLocalRing.closedPoint K)), ∃ h : Mat m K, Par 0 ⊤ h ∧ Bears S₁ φ₁ A h p₁ ∧ Bears S₂ φ₂ A h p₂

end GlobalTheory.FlagBundle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.Branching

noncomputable section

namespace GlobalTheory.DefU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def infSpan (φ : UA E n → ℂ) : Submodule ℂ (UA E n → ℂ) :=
  Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)

theorem RU_mem_infSpan (φ : UA E n → ℂ) {x : UA E n} (hx : x ∈ infU E n) {ψ : UA E n → ℂ} (hψ : ψ ∈ infSpan φ) :
    RU E n x ψ ∈ infSpan φ := by
  have : infSpan φ ≤ (infSpan φ).comap (RU E n x) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    show RU E n x (RU E n k φ) ∈ infSpan φ
    rw [RU_RU]
    exact Submodule.subset_span ⟨⟨x * k, mul_mem hx k.2⟩, rfl⟩
  exact this hψ

theorem mem_infU_of_mem_embU {τ : E →+* ℂ} {x : UA E n} (hx : x ∈ embU n τ) : x ∈ infU E n :=
  (Subgroup.mem_inf.1 hx).1

theorem exists_hasWeightAt (U : AutSub E n) (τ : E →+* ℂ) : ∃ lam, HasWeightAt U.V τ lam := by
  obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n τ
  obtain ⟨φ, hφU, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot U.isAut.ne_bot
  let j : Matrix.unitaryGroup (Fin n) ℂ →* UA E n := (embU n τ).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hj : ∀ u, j u ∈ infU E n := fun u => mem_infU_of_mem_embU (e.symm u).2
  let S := infSpan φ
  have hφS : φ ∈ S := by
    have : RU E n (1 : infU E n) φ ∈ S := Submodule.subset_span ⟨1, rfl⟩
    simpa using this
  have hS : S ≤ U.V := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact U.isAut.stable _ _ hφU)
  haveI : FiniteDimensional ℂ S := (U.isAut.aut φ hφU).kfin
  haveI : Nontrivial S := ⟨⟨⟨φ, hφS⟩, 0, fun h => hφ0 (congrArg Subtype.val h)⟩⟩
  let ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) S :=
    sub ((RU E n).comp j) S (fun u ψ hψ => RU_mem_infSpan φ (hj u) hψ)
  have hρ : ∀ u (v : S), (ρ u v : UA E n → ℂ) = RU E n (j u) v := fun _ _ => rfl
  have hcont : ∀ (l : Module.Dual ℂ S) (v : S), Continuous fun u => l (ρ u v) := by
    let P : Submodule ℂ (Module.Dual ℂ S) :=
      { carrier := {l | ∀ v : S, Continuous fun u => l (ρ u v)}
        add_mem' := fun ha hb v => (ha v).add (hb v)
        zero_mem' := fun _ => continuous_const
        smul_mem' := fun c _ ha v => (ha v).const_smul c }
    have hev : ∀ g : UA E n, (LinearMap.proj g ∘ₗ S.subtype : Module.Dual ℂ S) ∈ P := fun g v => by
      have hv : Continuous (v : UA E n → ℂ) := (U.isAut.aut _ (hS v.2)).cont
      have : Continuous fun u => (j u : UA E n) := continuous_subtype_val.comp e.symm.continuous
      exact hv.comp ((continuous_const_mul g).comp this)
    have h1 : P.dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext (funext fun g => hv _ (hev g)))
    have hP : P = ⊤ := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := P), h1, Submodule.dualAnnihilator_bot]
    intro l v
    have : l ∈ P := hP ▸ Submodule.mem_top
    exact this v
  obtain ⟨lam, f, hf⟩ := GlobalTheory.T.unitaryGroup_finiteDimensionalRep_contains_highestWeightRep n S ρ hcont
  refine ⟨lam, isIrreducible_smallRep_id n lam, S.subtype ∘ₗ f.toLinearMap, fun h0 => hf ?_,
    fun v => hS (f v).2, fun x v => ?_⟩
  · refine Representation.IntertwiningMap.ext (LinearMap.ext fun v => Subtype.ext ?_)
    simpa using LinearMap.congr_fun h0 v
  · have h1 : ((cEmb τ).comp (embU n τ).subtype) x = unitaryIncl n (e x) := (he x).symm
    rw [h1]
    have h2 := Representation.IntertwiningMap.isIntertwining _ _ f (e x) v
    change (f (smallRep (unitaryIncl n) lam (e x) v)).1 = _
    rw [h2, hρ]
    change RU E n ((e.symm (e x) : embU n τ) : UA E n) (f v).1 = _
    rw [e.symm_apply_apply]
    rfl

theorem hasWeightAt_unique (U : AutSub E n) (τ : E →+* ℂ) {lam lam' : DomWeight n} (h : HasWeightAt U.V τ lam)
    (h' : HasWeightAt U.V τ lam') : lam = lam' := by
  obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n τ
  obtain ⟨r, -, hr1, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryArchimedeanPoints E n τ
  let s : Matrix.unitaryGroup (Fin n) ℂ →* UA E n := (embU n τ).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have mk : ∀ mu, HasWeightAt U.V τ mu →
      ∃ f : (smallRep (unitaryIncl n) mu).IntertwiningMap (U.rep.comp s), f ≠ 0 := by
    rintro mu ⟨-, F, hF0, hFm, hFi⟩
    refine ⟨⟨F.codRestrict U.V hFm, fun u => ?_⟩, fun h0 => hF0 ?_⟩
    · ext v : 1
      apply Subtype.ext
      show F (sqRep ℂ n mu (unitaryIncl n u) v) = RU E n (s u) (F v)
      have : unitaryIncl n u = ((cEmb τ).comp (embU n τ).subtype) (e.symm u) := by
        have h3 := he (e.symm u)
        rw [e.apply_symm_apply] at h3
        exact h3
      rw [this, hFi]
      rfl
    · ext v : 1
      exact congrArg Subtype.val (DFunLike.congr_fun h0 v :)
  obtain ⟨f, hf⟩ := mk lam h
  obtain ⟨f', hf'⟩ := mk lam' h'
  have hc : ∀ g, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y) := fun g =>
    ⟨e (r g), fun y => by
      change Commute ((((e.symm (e (r g))) : embU n τ) : UA E n)⁻¹ * g) ((e.symm y : embU n τ) : UA E n)
      rw [e.symm_apply_apply]
      exact hr g _⟩
  obtain ⟨ee⟩ := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor _ _ _ _ _ U.rep s _ _ U.isIrreducible_rep (isIrreducible_smallRep_unitary n lam)
    (isIrreducible_smallRep_unitary n lam') hc f hf).2 f' hf'
  by_contra hne
  have h0 := intertwining_unitary_eq_zero n lam lam' hne ee.toIntertwiningMap
  obtain ⟨v, hv⟩ := exists_ne (0 : nablaSq ℂ n lam)
  exact hv (ee.injective ((DFunLike.congr_fun h0 v).trans (map_zero ee).symm))

theorem AU.existsUnique_hasWt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n)
    (τ : E →+* ℂ), ∃! lam : DomWeight n, π.HasWt τ lam := by
  intro E _ _ _ n π τ
  obtain ⟨U, rfl⟩ := AU.mk_surjective π
  obtain ⟨lam, h⟩ := exists_hasWeightAt U τ
  exact ⟨lam, h, fun mu hmu => (hasWeightAt_unique U τ h hmu).symm⟩

end GlobalTheory.DefU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAtStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_weight_definiteUnitary_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n) (τ : E →+* ℂ), ∃! lam : DomWeight n, π.HasWt τ lam := by
  first | exact @GlobalTheory.DefU.AU.existsUnique_hasWt | exact GlobalTheory.DefU.AU.existsUnique_hasWt | (intros; apply GlobalTheory.DefU.AU.existsUnique_hasWt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem exists_subsingleton_coh_twist_tens_lbPow : ∀ (k : Type) [Field k] {Y : Scheme.{0}} (f : Y ⟶ Sp k), IsProjOver f → ∀ (A N : LB Y), IsAmpleLB A → N.IsLB → ∀ (G : Y.Modules) [IsFiniteQC G] (B : ℕ), ∃ j₁ : ℕ, ∀ j m : ℕ, j₁ ≤ j → m < B → ∀ p, 0 < p → Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p) := by
  intro k _ Y f hf A N hA hN G _ B
  letI := algebraΓOfHom f
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hf).1
  have H (m : Fin B) : ∃ q : ℕ, ∀ n ≥ q, ∀ p, 0 < p →
      Subsingleton (coh (twist (twist G (lbPow N m)) (lbPow A n)) p) :=
    have := isFiniteQC_twist (F := G) (isLB_lbPow hN m)
    eventually_atTop.1 (hA.eventually_subsingleton_coh_twist (f := f) (fun _ => rfl) _)
  choose q hq using H
  obtain ⟨Q, hQ⟩ := Finite.exists_le q
  refine ⟨Q, fun j m hj hm p hp => ?_⟩
  have := hq ⟨m, hm⟩ j ((hQ _).trans hj) p hp
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq G (isLB_lbPow hN m)
    (isLB_lbPow hA.isLB j) (isLB_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m)) (by
      rw [cls_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m),
        ← cls_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m) (isLB_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m)),
        ← cls_tens (isLB_lbPow hN m) (isLB_lbPow hA.isLB j) (isLB_tens (isLB_lbPow hN m) (isLB_lbPow hA.isLB j))]
      exact (cls_eq_iff _ _).2 (tens_comm_iso (isLB_lbPow hA.isLB j) (isLB_lbPow hN m)))
  exact (cohOn.mapIso k ⊤ p e).symm.injective.subsingleton

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPowIff
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ArInt

theorem interNum_one_lbPow_of_curve {κ : Type} [Field κ] {C : Scheme.{0}} [Algebra κ Γ(C, ⊤)]
    [IsProper (strHom κ (X := C))] {H N : LB C} (hH : IsAmpleLB H) (hd : topologicalKrullDim C = 1)
    (hN : N.IsLB) (n : ℕ) :
    interNum κ (structureModule C) ![lbPow N n] = n * interNum κ (structureModule C) ![N] := by
  induction n with
  | zero =>
    rw [interNum_eq_zero_of_cls_eq_zero κ _ (isLB_vecOne (isLB_lbPow hN 0)) 0
      ((cls_lbPow hN 0 _).trans (zero_nsmul _))]
    simp
  | succ n ih =>
    rw [interNum_one_of_cls_eq_add hH hd (isLB_lbPow hN (n + 1)) (isLB_lbPow hN n) hN
      (by
        calc
          _ = (n + 1) • cls N hN := cls_lbPow hN (n + 1) _
          _ = n • cls N hN + cls N hN := succ_nsmul _ _
          _ = _ := by rw [cls_lbPow hN n _]), ih]
    push_cast
    ring

theorem nefFib_pow_iff : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0})
    (p : X ⟶ Sp k), IsProjOver p → ∀ (L : HermLB p) (m : ℕ), 0 < m →
      (ArInt.NefFib (L.pow m) ↔ ArInt.NefFib L) := by
  intro k _ _ X p hp L m hm
  obtain ⟨hpr, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have key : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type)
      [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 →
      topSelfIntersection κ ((L.pow m).B.pull i) 1 = m * topSelfIntersection κ (L.B.pull i) 1 := by
    intro Z i _ _ κ _ _ _ hd
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
    have : IsProper (strHom κ (X := Z)) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
    have hAZ := hA.pull_of_isClosedImmersion i
    have hN : (L.B.pull i).IsLB := LB.isLB_pull L.isLB i
    have e1 : topSelfIntersection κ ((L.pow m).B.pull i) 1 =
        interNum κ (structureModule Z) ![lbPow (L.B.pull i) m] :=
      interNum_congr_cls κ _ (fun _ => LB.isLB_pull (L.pow m).isLB i)
        (isLB_vecOne (isLB_lbPow hN m)) fun j => by
          fin_cases j
          exact (cls_pull (L.pow m).isLB i _).trans
            ((congrArg (pull i) (cls_lbPow L.isLB m (L.pow m).isLB)).trans
              ((map_nsmul (pull i) m _).trans (cls_lbPow hN m _).symm))
    have e2 : topSelfIntersection κ (L.B.pull i) 1 = interNum κ (structureModule Z) ![L.B.pull i] := by
      rw [topSelf_def]
      congr 1
      funext j
      fin_cases j
      rfl
    rw [e1, e2]
    exact interNum_one_lbPow_of_curve hAZ hd hN m
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  constructor
  · intro h Z i _ _ κ _ _ _ hd
    have h' := h Z i κ hd
    rw [key Z i κ hd] at h'
    exact (mul_nonneg_iff_of_pos_left hm').1 h'
  · intro h Z i _ _ κ _ _ _ hd
    rw [key Z i κ hd]
    exact mul_nonneg hm'.le (h Z i κ hd)

end GlobalTheory.ArInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMovPair
noncomputable section

open MeasureTheory
open scoped Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.ThetaGrowth
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilSupBound

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
  {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem continuous_mov_pair (hθ : IsInfFam θ) (u : RW T S) :
    Continuous fun p : GA D S × GA D T => mov θ p.1⁻¹ p.2⁻¹ u := by
  refine continuous_pi fun τ => ?_
  unfold mov
  simp only [inv_inv]
  exact (((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp
    ((GlobalTheory.RealWeil.continuous_mt T).2.comp continuous_snd)).matrix_mul continuous_const).matrix_mul
    ((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp ((GlobalTheory.RealWeil.continuous_mt S).1.comp continuous_fst))

theorem uniform_level_pair (hom : IsWeilDatumO ψ S T χS χT om) {U : AddSubgroup (WO S T)}
    (hU : IsOpen (U : Set (WO S T))) {C : Set (GA D S × GA D T)} (hC : IsCompact C) :
    ∃ K₀ ∈ 𝓝 (0 : WO S T), IsCompact K₀ ∧ ∀ p ∈ C, ∀ φ, IsThetaFunO ψ S T φ →
      (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u φ = φ) → ∀ u ∈ K₀, u.map (infPart D) = 0 →
        heisO ψ S T u (om p φ) = om p φ := by
  obtain ⟨i1, i2, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have hcont : Continuous fun z : WO S T × (GA D S × GA D T) => actO S T z.2.1⁻¹ z.2.2⁻¹ z.1 := by
    unfold actO
    simp only [inv_inv]
    exact (((GlobalTheory.RealWeil.continuous_mt T).2.comp (continuous_snd.comp continuous_snd)).matrix_mul
      continuous_fst).matrix_mul ((GlobalTheory.RealWeil.continuous_mt S).1.comp (continuous_fst.comp continuous_snd))
  have hev : ∀ᶠ u in 𝓝 (0 : WO S T), ∀ p ∈ C, actO S T p.1⁻¹ p.2⁻¹ u ∈ U := by
    refine hC.eventually_forall_of_forall_eventually fun p _ => ?_
    refine hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds ?_)
    show actO S T p.1⁻¹ p.2⁻¹ 0 ∈ U
    unfold actO
    rw [Matrix.mul_zero, Matrix.zero_mul]
    exact U.zero_mem
  obtain ⟨K₀, h0, hsub, hK₀⟩ := LocallyCompactSpace.local_compact_nhds (X := WA T S) 0 _ hev
  refine ⟨K₀, h0, hK₀, fun ⟨g, h⟩ hp φ hφ hl u hu hinf => ?_⟩
  have hv : (actO S T g⁻¹ h⁻¹ u).map (infPart D) = 0 := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hinf, Matrix.mul_zero, Matrix.zero_mul]
  have e := hom.om_heis g h (actO S T g⁻¹ h⁻¹ u) φ hφ
  rw [hl _ (hsub hu _ hp) hv, actO_mul, mul_inv_cancel, mul_inv_cancel, actO_one] at e
  exact e.symm

theorem cube_bound_at (hom : IsWeilDatumO ψ S T χS χT om) (hc : Chart θ σ) {N : ℕ}
    (b : Module.Basis (Fin N) ℝ (RW T S)) {K₀ : Set (WO S T)} (h0 : K₀ ∈ 𝓝 (0 : WO S T)) (hK₀ : IsCompact K₀) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ p φ, IsThetaFunO ψ S T φ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T u (om p φ) = om p φ) → ∀ B : ℝ, (∀ w, ‖φ w‖ ≤ B) → ∀ y,
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) 1),
        ‖om p φ (y + ∑ i, iotaW σ T S (t i • b i))‖ ^ 2 ≤ c * B ^ 2 := by
  obtain ⟨c, hc0, hcube⟩ := cube_bound hom hc b h0 hK₀
  refine ⟨c, hc0, fun ⟨g, h⟩ φ hφ hl B hB y => ?_⟩
  have e := hom.om_heis g h (actO S T g⁻¹ h⁻¹ y) φ hφ
  rw [actO_mul, mul_inv_cancel, mul_inv_cancel, actO_one] at e
  have hn := GlobalTheory.HeisOrtho.norm_heisO (S := S) (T := T) hom.std.1
  have key := hcube (g, h) _ (GlobalTheory.ThetaClosed.thetaClosed ψ θ hom.std hc.inf S T φ hφ |>.1 (actO S T g⁻¹ h⁻¹ y))
    (fun w hw => by
      generalize hu : w - iotaW σ T S (piW θ T S w) = u at hw
      have hinf : u.map (infPart D) = 0 := by
        have hp : piW θ T S u = 0 := by
          rw [← hu, AddMonoidHom.map_sub, hc.pi_iota, sub_self]
        ext i j
        exact ThetaCont.infPart_eq_zero hc _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
      rw [e, hn, hn]
      conv_rhs => rw [← hl u hw hinf, hn, ← hu]
      congr 2
      abel_nf) B (fun w => by rw [hn]; exact hB _)
  simp only [e, hn, zero_add] at key
  simpa only [add_comm y] using key

theorem exists_sup_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ C : Set (GA D S × GA D T), IsCompact C →
      ∃ c : ℝ, ∀ p ∈ C, ∀ w, ‖om p f w‖ ≤ c := by
  intro D ψ S T χS χT om hom f hf C hC
  have hψ := hom.std
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have b := Module.finBasis ℝ (RW T S)
  generalize Module.finrank ℝ (RW T S) = N at b
  obtain ⟨U, hU, hl⟩ := hf.level
  obtain ⟨K₀, h0, hK₀, hlev⟩ := uniform_level_pair hom hU hC
  obtain ⟨c, hc0, hcube⟩ := cube_bound_at hom hc b h0 hK₀
  obtain ⟨C₁, hC₁0, hC₁⟩ := words_bound (dvL hc hψ S T) (fun w => (LinearMap.proj w).comp (thetaSub ψ S T).subtype)
    (fun (m : thetaSub ψ S T) => theta_bounded hψ m.2) N ⟨f, hf⟩
  obtain ⟨κ, hκ⟩ := hC.exists_bound_of_continuousOn
    (f := fun (p : GA D S × GA D T) (i : Fin N) => mov θ p.1⁻¹ p.2⁻¹ (b i))
    (continuous_pi fun i => continuous_mov_pair hθ (b i)).continuousOn
  refine ⟨√(4 ^ N * (c * (C₁ * max 1 κ ^ N) ^ 2)), fun ⟨g, h⟩ hp w => ?_⟩
  let wd : List (RW T S) → thetaSub ψ S T := fun l => l.foldl (fun m z => dvL hc hψ S T z m) ⟨f, hf⟩
  let A : ℕ → Set (WO S T → ℂ) := fun p =>
    {F | ∃ l : List (RW T S), l.length ≤ p ∧ (∀ u ∈ l, ‖u‖ ≤ max 1 κ) ∧ F = om (g, h) (wd l).1}
  refine Real.le_sqrt_of_sq_le (sobolev_iter N 0 (fun i r => iotaW σ T S (r • b i)) A (c * (C₁ * max 1 κ ^ N) ^ 2) w
    (fun i => (hc.continuous_iota T S).comp (continuous_id.smul continuous_const))
    (fun p q hpq F ⟨l, h1, h2⟩ => ⟨l, h1.trans hpq, h2⟩) ?_ ?_ (om (g, h) f) ⟨[], le_rfl, by simp, rfl⟩)
  · rintro p _ ⟨l, h1, h2, rfl⟩
    have hF := hom.om_pres (g, h) _ (wd l).2
    refine ⟨hF.cont, fun i => ⟨_, ⟨l ++ [mov θ g⁻¹ h⁻¹ (b i)], by simpa using h1, fun u hu => ?_, ?_⟩,
      sobolev_step hc hψ (b i) hF⟩⟩
    · rcases List.mem_append.1 hu with hu | hu
      · exact h2 u hu
      · rw [List.mem_singleton.1 hu]
        exact ((norm_le_pi_norm (fun i => mov θ g⁻¹ h⁻¹ (b i)) i).trans (hκ (g, h) hp)).trans (le_max_right _ _)
    · rw [dv_om hom hc g h (b i) (wd l).2]
      simp only [wd, List.foldl_append]
      rfl
  · rintro _ ⟨l, h1, h2, rfl⟩
    exact hcube (g, h) _ (wd l).2 (hlev (g, h) hp _ (wd l).2 fun u hu h0 => words_level hc hψ h0 l _ (hl u hu h0)) _
      (hC₁ _ (le_max_left _ _) l (by simpa using h1) h2) w

end GlobalTheory.WeilSupBound

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeNonempty
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemN

theorem nonempty_nbc_of_isEmpty_loc :
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (nd : NData R H what₂) (A : NAut nd),
      IsEmpty nd.Loc → Nonempty (NBC A) := by
  intro R H what₂ nd A hL
  exact ⟨{
    AU := fun _ => Empty
    multAU := fun _ x => x.elim
    sphAU := fun _ x => x.elim
    locAU := fun _ x => x.elim
    satAU := fun _ x => x.elim
    satAU_card := fun _ x => x.elim
    Wt := fun _ => Empty
    infW := fun _ x => x.elim
    infW_card := fun _ x => x.elim
    wtAU := fun _ x => x.elim
    infW_alg := fun _ x => x.elim
    embAV := fun i => hL.elim i
    embAV_inj := fun i => hL.elim i
    embAV_loc := fun i => hL.elim i
    embAV_sat := fun i => hL.elim i
    embAV_sph := fun i => hL.elim i
    embAV_inf := fun i => hL.elim i }⟩

end GlobalTheory.MemN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClsAt
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PtId

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}

def ClsAt {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    {H : Geo.Tor.Host D.host.E} {Dw : Datum H} (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (δ : ℤˣ) : Prop :=
  ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (g q0 : ℕ) (X : Data D.host.E D.R.r) (hq : X.p0 + q0 = D.R.r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (x₀ : Frame X.Ψ D.R.r) (vr : Harm.Var X.Ψ q0 X.p0 (Fin (Vc D i).rank) ≃ FVar D (Wc D i).rank (Vc D i).rank), IsMod (Wc D i) (rank_Wc i) X → IsSympl X bas → IsONFr X x₀ → IsInvOf (Wc D i) (rank_Wc i) X x₀ (cart (R.MW i (sg0 D A))) → IsBasOf (Wc D i) (rank_Wc i) X hq x₀ (onb (R.MW i (sg0 D A))) → IsVarOf (Vc D i) (Wc D i) X q0 vr → ∀ (bad N : ℕ) (h : GA D (Vc D i)) (k : GA D (Wc D i)) (Λ : GenLat D.host.E (Vc D i).rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) (e : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → h ∈ GfC (Vc D i) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h y → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ (Wc D i) (rank_Wc i) ι k mk → ∀ Y : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E, IsRoots l₂ (latR (rank_Wc i) (latG (Wc D i) k)) mk N Y → ∀ (v : TF (Vc D i).rank g) (a : ℂ), IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) (latR (rank_Wc i) (latG (Wc D i) k))) v → Reads R.θ (Vc D i) (Wc D i) (rank_Wc i) X bas idx (R.ωP i t (1, k) (R.vacP i)) (a • v) (frMove R.θ (Wc D i) (rank_Wc i) X k x₀) → ∀ (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin (Vc D i).rank)) (d : ℕ), P.IsHomogeneous d → thetaKO (R.ωP i t) h k (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i t) (MvPolynomial.rename vr P)) = ((δ : ℤ) : ℂ) ^ d * (-1) ^ d * ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d * a * ((((Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) * ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ * thP X hq bas idx (gphi X bas (H.w0 : D.host.E) Λ.La (latR (rank_Wc i) (latG (Wc D i) k)) v (hatC l₂ φ) Y) P (frMove R.θ (Wc D i) (rank_Wc i) X k x₀)

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def IoAt (O : OMDat T.toCore R i Tp tup) (v₀ : (R.MW i (sg0 D A)).Vec) (ka : ℂ) : Prop :=
  ∀ (lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank), (∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨ (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1))) → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ ρ) → ∀ (t : T0) (v : VsV D i O.c'.F), R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) (O.c0' v)) = ka • pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i t) (MvPolynomial.rename lt (MvPolynomial.map (inC O.c') (O.io v)))

def CovAt (O : OMDat T.toCore R i Tp tup) (c0 : ℂ) : Prop :=
  ∀ (t : Tp) (X : Data D.host.E D.R.r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))) (k : GA D (Wc D i)) (xk : (AE D)ˣ) (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → IsSympl X bas → IdxIs O.c' (inC O.c') X idx e → latR (rank_Wc i) (latG (Wc D i) k) = X.Λ → IsDetRoot (Wc D i) k xk → IsMark (O.dδ t).l₂ X.Λ mk → MarkAd (O.dδ t).l₂ (Wc D i) (rank_Wc i) (iotaW T i) k mk → letI : Algebra (O.dδ t).c₂.F ℂ := ((inC O.c').comp ((O.dδ t).eF.symm : (O.dδ t).c₂.F →+* O.c'.F)).toAlgebra; ∀ (y₂ : FrPt (O.dδ t).Xo₂ (O.dδ t).c₂ ℂ) (A₂ : AnFib X bas idx e (frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.x₀ ((i : ℕ) + 1) O.s0 τ.1)) X.Λ y₂), A₂.Marked mk → evR (O.dδ t).Xo₂ (O.dδ t).c₂ (O.dδ t).cδ y₂ = c0 * ((R.xi (tup t) xk : Circle) : ℂ)

def degW {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : ℕ :=
  ∑ τ : E →+* ℂ, ∑ j : Fin (Dw.mult τ), a (τ, j)

end GlobalTheory.PtId
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesRingOfIntegersFull
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Pj

namespace GlobalTheory.Mem

theorem Base.OtoLL_injective' (B : Base) : Function.Injective B.OtoLL := by
  intro x y h
  apply RingOfIntegers.ext
  exact Subtype.ext h

theorem hermitianCodeWordStages_ringOfIntegers_full : ∀ X : Stages, OFull X.toD7 := by
  intro X
  refine ⟨X.B.OtoLL_injective', ?_⟩
  let f : X.B.Ks →+* ℂ := X.B.embLL.comp (algebraMap X.B.Ks X.B.LL)
  have hle : FO X.toD7 ≤ f.toRatAlgHom.fieldRange := by
    rw [FO, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, rfl⟩
    exact ⟨algebraMap (𝓞 X.B.Ks) X.B.Ks y, rfl⟩
  intro z hz hint
  obtain ⟨x, rfl⟩ := hle hz
  have hx : IsIntegral ℤ x := (isIntegral_algHom_iff f.toIntAlgHom f.injective).1 hint
  exact ⟨(⟨x, hx⟩ : 𝓞 X.B.Ks), rfl⟩

end GlobalTheory.Mem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ISupRangeWeightMapsEqTopDefiniteUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ISupRangeWeightMapsEqTopDefiniteUnitary
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

theorem iSup_range_weight_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (τ : E →+* ℂ) (lam : DomWeight n), HasWeightAt π.V τ lam → (⨆ f : Representation.IntertwiningMap ((GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype)) (π.rep.comp (embU n τ).subtype), LinearMap.range f.toLinearMap) = ⊤ := by
  intro E _ _ _ n π τ lam h
  obtain ⟨-, f, hf0, hfm, hf⟩ := h
  obtain ⟨e, he⟩ := GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n τ
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.exists_embRet E n τ
  have heq : (GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype) =
      (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) lam).comp e.toMulEquiv.toMonoidHom := by
    ext x : 1
    change GlobalTheory.Branching.sqRep ℂ n lam (cEmb τ (x : UA E n)) =
      GlobalTheory.Branching.sqRep ℂ n lam (GlobalTheory.Branching.unitaryIncl n (e x))
    rw [he]
  have hσ : Representation.IsIrreducible ((GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype)) := by
    rw [heq]
    exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv _ e.toMulEquiv
      (GlobalTheory.Branching.isIrreducible_smallRep_unitary n lam)
  let F : Representation.IntertwiningMap ((GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype))
      (π.rep.comp (embU n τ).subtype) :=
    ⟨f.codRestrict π.V hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h0 =>
    hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h0 v))
  exact (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (embU n τ) π.V _ _ π.rep (embU n τ).subtype _ _
    π.isIrreducible_rep hσ hσ (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1

end GlobalTheory.DefU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ISupRangeWeightMapsEqTopDefiniteUnitaryStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iSup_range_weightMaps_eq_top_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (τ : E →+* ℂ) (lam : DomWeight n), HasWeightAt π.V τ lam → (⨆ f : Representation.IntertwiningMap ((GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype)) (π.rep.comp (embU n τ).subtype), LinearMap.range f.toLinearMap) = ⊤ := by
  first | exact @GlobalTheory.DefU.iSup_range_weight_eq_top | exact GlobalTheory.DefU.iSup_range_weight_eq_top | (intros; apply GlobalTheory.DefU.iSup_range_weight_eq_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIntersectionNumberGroundFieldChange
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIntersectionNumberGroundFieldChange
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory

namespace GroundFieldChange

theorem finsum_const_mul_int (c : ℤ) (f : ℕ → ℤ) : ∑ᶠ n, c * f n = c * ∑ᶠ n, f n :=
  (mul_finsum f c).symm

theorem hdim_fieldChange (κ κ' : Type) [Field κ] [Field κ'] [Algebra κ κ'] (Z : Scheme.{0})
    [Algebra κ' Γ(Z, ⊤)] [Algebra κ Γ(Z, ⊤)] [IsScalarTower κ κ' Γ(Z, ⊤)] (F : Z.Modules)
    (n : ℕ) : hdim κ F n = Module.finrank κ κ' * hdim κ' F n := by
  rw [hdim_def, hdim_def, Module.finrank_mul_finrank]

theorem chi_fieldChange (κ κ' : Type) [Field κ] [Field κ'] [Algebra κ κ'] (Z : Scheme.{0})
    [Algebra κ' Γ(Z, ⊤)] [Algebra κ Γ(Z, ⊤)] [IsScalarTower κ κ' Γ(Z, ⊤)] (F : Z.Modules) :
    chi κ F = (Module.finrank κ κ' : ℤ) * chi κ' F := by
  rw [chi_def, chi_def, ← finsum_const_mul_int]
  refine finsum_congr fun n ↦ ?_
  rw [hdim_fieldChange κ κ' Z F n, Nat.cast_mul]
  ring

theorem interNum_fieldChange : ∀ (κ κ' : Type) [Field κ] [Field κ'] [Algebra κ κ'] (Z : Scheme.{0})
    [Algebra κ' Γ(Z, ⊤)] [Algebra κ Γ(Z, ⊤)] [IsScalarTower κ κ' Γ(Z, ⊤)] (G : Z.Modules)
    {ι : Type} [Fintype ι] (L : ι → LB Z),
    interNum κ G L = (Module.finrank κ κ' : ℤ) * interNum κ' G L := by
  intro κ κ' _ _ _ Z _ _ _ G ι _ L
  rw [interNum_def, interNum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [chi_fieldChange κ κ' Z]
  ring

end GroundFieldChange

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIntersectionNumberGroundFieldChangeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIntersectionNumber_groundFieldChange : ∀ (κ κ' : Type) [Field κ] [Field κ'] [Algebra κ κ'] (Z : Scheme.{0}) [Algebra κ' Γ(Z, ⊤)] [Algebra κ Γ(Z, ⊤)] [IsScalarTower κ κ' Γ(Z, ⊤)] (G : Z.Modules) {ι : Type} [Fintype ι] (L : ι → LB Z), interNum κ G L = (Module.finrank κ κ' : ℤ) * interNum κ' G L := by
  first | exact @GlobalTheory.GroundFieldChange.interNum_fieldChange | exact GlobalTheory.GroundFieldChange.interNum_fieldChange | (intros; apply GlobalTheory.GroundFieldChange.interNum_fieldChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesHasRootOfUnity
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Pj

namespace GlobalTheory.Mem

theorem exp_div_mul_eq_zpow_mul_zpow {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h : Nat.Coprime p q) :
    ∃ a b : ℤ, Complex.exp (2 * Real.pi * Complex.I / ((p * q : ℕ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I / ((p * (p - 1) : ℕ) : ℂ)) ^ a *
        Complex.exp (2 * Real.pi * Complex.I / ((q * (q - 1) : ℕ) : ℂ)) ^ b := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 h
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  refine ⟨v * p', u * q', ?_⟩
  rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  have h1 : (p' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h2 : (q' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h3 : (p' : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  have h4 : (q' : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  have h5 : (u : ℂ) * (p' + 1) + v * (q' + 1) = 1 := by exact_mod_cast huv
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  linear_combination (-1 : ℂ) * h5

theorem Base.exists_root_mul (B : Base) : ∃ y : B.O, B.embLL (B.OtoLL y) =
    Complex.exp (2 * Real.pi * Complex.I / ((B.host.g 0 * B.host.g 1 : ℕ) : ℂ)) := by
  have p0 := B.host.g_prime 0
  have p1 := B.host.g_prime 1
  obtain ⟨z₀, hz₀, e₀⟩ := B.roots_Ks (B.host.g 0 * (B.host.g 0 - 1)) (by simp)
  obtain ⟨z₁, hz₁, e₁⟩ := B.roots_Ks (B.host.g 1 * (B.host.g 1 - 1)) (by simp)
  obtain ⟨a, b, hab⟩ := exp_div_mul_eq_zpow_mul_zpow p0.two_le p1.two_le
    ((Nat.coprime_primes p0 p1).2 B.host.g_ne)
  have hmem : z₀ ^ a * z₁ ^ b ∈ B.Ks := mul_mem (zpow_mem hz₀ a) (zpow_mem hz₁ b)
  have he : B.embLL (z₀ ^ a * z₁ ^ b) =
      Complex.exp (2 * Real.pi * Complex.I / ((B.host.g 0 * B.host.g 1 : ℕ) : ℂ)) := by
    rw [map_mul, map_zpow₀, map_zpow₀, e₀, e₁, hab]
  have hne : B.host.g 0 * B.host.g 1 ≠ 0 := mul_ne_zero p0.ne_zero p1.ne_zero
  have hint : IsIntegral ℤ (B.embLL (z₀ ^ a * z₁ ^ b)) := by
    rw [he]
    exact (Complex.isPrimitiveRoot_exp _ hne).isIntegral (Nat.pos_of_ne_zero hne)
  have hint' : IsIntegral ℤ (z₀ ^ a * z₁ ^ b) :=
    (isIntegral_algHom_iff B.embLL.toIntAlgHom B.embLL.injective).1 hint
  refine ⟨⟨⟨z₀ ^ a * z₁ ^ b, hmem⟩, ?_⟩, he⟩
  exact (isIntegral_algHom_iff (B.Ks.val : B.Ks →+* B.LL).toIntAlgHom Subtype.val_injective).1 hint'

theorem hermitianCodeWordStages_has_rootOfUnity : ∀ X : Stages, OZeta X.toD7 := fun X => X.B.exists_root_mul

end GlobalTheory.Mem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsModelHolomorphicIntegralExtremalWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsModelHolomorphicIntegralExtremalWeight
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLift

theorem holShape_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_order → ∀ i, HolShape (R.MW i (sg0 D A)) ∧ ∃ w, WtIs (R.MW i (sg0 D A)) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R ho i
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 = (Wc D i).rank :=
    fun τ => GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW i τ
  have hc : ∀ ρ, Formalism.QuantumDeterminants.IsHCParam ((R.MW i (sg0 D A)).lam ρ) := fun ρ => by
    have he := (R.MW i (sg0 D A)).enum ρ
    refine ⟨he.1, fun a => ?_⟩
    obtain ⟨-, f, hf, hS⟩ := he
    have hp : Links.parAt (Wc D i) (sg0 D A) ρ = Formalism.L2.NTheta.holPar _ _ (Formalism.L2.NTheta.wtOf D (Wc D i) ρ) := by
      rw [hs]; exact GlobalTheory.ThetaFiresProbe.parAt_fixed _ ρ
    rw [hp] at hS
    have hm : (f a, (R.MW i (sg0 D A)).ε ρ a) ∈ Formalism.L2.NTheta.holPar _ _ (Formalism.L2.NTheta.wtOf D (Wc D i) ρ) := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hm
    have hx1 := congrArg Prod.fst hx
    have hn : (((Wc D i).rank : ℕ) : ℝ) = (((Wc D i).sig (tauE D ρ)).1 : ℝ) + ((Wc D i).sig (tauE D ρ)).2 := by
      rw [← hpq ρ]; push_cast; rfl
    dsimp only at hx1
    rw [hf a, ← hx1, hn]
    rcases x with c | c
    · refine ⟨Formalism.L2.NTheta.wtOf D (Wc D i) ρ (Sum.inl c) - ((Wc D i).sig (tauE D ρ)).2 - (c : ℕ), ?_⟩
      simp only [Formalism.L2.NTheta.holEnt, Sum.elim_inl]
      push_cast
      ring
    · refine ⟨Formalism.L2.NTheta.wtOf D (Wc D i) ρ (Sum.inr c) - (c : ℕ), ?_⟩
      simp only [Formalism.L2.NTheta.holEnt, Sum.elim_inr]
      push_cast
      ring
  refine ⟨fun ρ => ⟨hc ρ, _, (Nat.le_add_right _ _).trans (hpq ρ).le, fun a => ho i ρ a⟩, ?_⟩
  choose w hw using fun ρ a => Formalism.QuantumDeterminants.low_k_integrable_holds _ ((R.MW i (sg0 D A)).ε ρ) _ (hc ρ).2 a
  exact ⟨fun ρ c => w ρ (revNeg ((R.MW i (sg0 D A)).ε ρ) (arr (nNeg ((R.MW i (sg0 D A)).ε ρ)) c)),
    fun ρ c => (hw ρ _).symm⟩

end GlobalTheory.DefLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsModelHolomorphicIntegralExtremalWeightStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forms_model_holomorphic_integral_extremal_weight : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_order → ∀ i, HolShape (R.MW i (sg0 D A)) ∧ ∃ w, WtIs (R.MW i (sg0 D A)) w := by
  first | exact @GlobalTheory.DefLift.holShape_fixed | exact GlobalTheory.DefLift.holShape_fixed | (intros; apply GlobalTheory.DefLift.holShape_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubsetImageOfIsClosedImmersion
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubsetImageOfIsClosedImmersion
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem support_pushforward_subset_image_of_isClosedImmersion :
    ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsClosedImmersion g] (E : Y.Modules),
      support ((Scheme.Modules.pushforward g).obj E) ⊆ g '' support E := by
  intro X Y g _ E y hy
  by_contra hyn
  rw [mem_support_iff, ← not_subsingleton_iff_nontrivial] at hy
  apply hy
  have hemb := g.isClosedEmbedding
  refine subsingleton_of_forall_eq 0 fun t => ?_
  obtain ⟨U, hyU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ t

  let Z0 : Set Y := {z | ∃ hz : z ∈ g ⁻¹ᵁ U, E.presheaf.germ (g ⁻¹ᵁ U) z hz s = 0}
  have hZ0 : IsOpen Z0 := by
    rw [isOpen_iff_forall_mem_open]
    rintro z ⟨hz, hzs⟩
    obtain ⟨W, hzW, iU, iV, he⟩ := TopCat.Presheaf.germ_eq E.presheaf z hz hz s 0
      (by rw [hzs, map_zero])
    refine ⟨W, fun z' hz' => ⟨(leOfHom iU) hz', ?_⟩, W.2, hzW⟩
    have := TopCat.Presheaf.germ_res_apply E.presheaf iU z' hz' s
    rw [he, map_zero, map_zero] at this
    exact this.symm
  obtain ⟨V', hV', hV'e⟩ := hemb.isInducing.isOpen_iff.1 hZ0
  let V : X.Opens := U ⊓ ⟨V' ∪ (Set.range g)ᶜ, hV'.union hemb.isClosed_range.isOpen_compl⟩
  have hyV : y ∈ V := by
    refine ⟨hyU, ?_⟩
    by_cases hr : y ∈ Set.range g
    · obtain ⟨z, rfl⟩ := hr
      have hzs : z ∉ support E := fun h => hyn ⟨z, h, rfl⟩
      have hz : z ∈ g ⁻¹ᵁ U := hyU
      refine Or.inl (show z ∈ g ⁻¹' V' from hV'e ▸ ⟨hz, (notMem_support_iff.1 hzs).elim _ _⟩)
    · exact Or.inr hr
  have hVU : V ≤ U := inf_le_left
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hVU) y hyV]
  have h0 : ((Scheme.Modules.pushforward g).obj E).presheaf.map (homOfLE hVU).op s = 0 := by
    refine section_eq_zero_of_germ (F := E) _ fun z hz => ?_
    have hz' : z ∈ Z0 := by
      rw [← hV'e]
      rcases hz.2 with h | h
      · exact h
      · exact absurd ⟨z, rfl⟩ h
    obtain ⟨hzU, hzs⟩ := hz'
    rw [Scheme.Modules.pushforward_obj_presheaf_map]
    exact (TopCat.Presheaf.germ_res_apply E.presheaf ((Opens.map g.base).map (homOfLE hVU)) z hz s).trans hzs
  rw [h0, map_zero]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubsetImageOfIsClosedImmersionStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_pushforward_subset_image : ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsClosedImmersion g] (E : Y.Modules), support ((Scheme.Modules.pushforward g).obj E) ⊆ g '' support E := by
  first | exact @GlobalTheory.support_pushforward_subset_image_of_isClosedImmersion | exact GlobalTheory.support_pushforward_subset_image_of_isClosedImmersion | (intros; apply GlobalTheory.support_pushforward_subset_image_of_isClosedImmersion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTameGenAt
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemTame

theorem exists_tameGenAt :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v → ∃ γ : G E Ω, TameGenAt A γ :=
  @GlobalTheory.TameInertiaGen.exists_tameGenAt

end GlobalTheory.MemTame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinUMulInfU
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

theorem exists_finU_mul_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : UA E n),
    ∃ k ∈ finU (E := E) (n := n), ∃ x ∈ infU E n, g = k * x := by
  intro E _ _ _ n g
  let k : UA E n := ⟨finGL E n (GeneralLinearGroup.map (pFin E) g.1), ClassFin.finGL_mem_UA _ (ClassFin.cT_pFin g)⟩
  have hk : k ∈ finU (E := E) (n := n) := pInf_finGL _
  refine ⟨k, hk, k⁻¹ * g, ?_, (mul_inv_cancel_left k g).symm⟩
  change GeneralLinearGroup.map (pFin E) (k⁻¹ * g).1 = 1
  have h : GeneralLinearGroup.map (pFin E) k.1 = GeneralLinearGroup.map (pFin E) g.1 := pFin_finGL _
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h, inv_mul_cancel]

end GlobalTheory.DefU
end
