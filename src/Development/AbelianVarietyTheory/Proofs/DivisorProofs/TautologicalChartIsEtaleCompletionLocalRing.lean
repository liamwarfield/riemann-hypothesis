module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiFiniteOfRigidAtB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegResidueFieldOfIsOpenImmersion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiFiniteTautologicalChartClosedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiFiniteTautologicalChartClosedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem quasiFinite_of_tautB : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → (∀ p : Sp (ChartRing k m e), ξ p = ξ (closedPoint _) → p = closedPoint _) ∧ ((residue (ChartRing k m e)).comp (Scheme.stalkClosedPointTo ξ).hom).Finite := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hU hS k _ m e C hC ξ hξ
  obtain ⟨⟨_, _, _, _, ⟨_, _, hft⟩, _⟩, ⟨n, s, ε, τ₀, h1, h2, h3, h4, hP⟩⟩ := hC
  have hb : ξ ≫ π ≫ zs = spMap C.b := by
    refine GlobalTheory.ChartQF.eq_spMap_of_injective (algebraMap _ (FractionRing (ChartRing k m e)))
      (IsFractionRing.injective _ _) _ _ ?_
    have e1 : i ≫ zs = pullback.snd _ _ := hU.1.2.2.2.2.1
    have e2 : j ≫ π = i := hU.2.2.2.2.1.2.2.2.2.1
    show jK _ ≫ _ = jK _ ≫ _
    rw [← Category.assoc, ← hξ, Category.assoc, reassoc_of% e2, e1, C.y_over]
  exact GlobalTheory.ChartQF.quasiFinite_of_pointRigid ξ (π ≫ zs) C.b hb hft fun K _ _ ev k₀ hk hemb hq hd =>
    hP K ev k₀ hk hemb (hS _ C (GlobalTheory.ChartQF.base_chartRing C.toFam) ξ hξ n s ε τ₀ h1 h2 h3 h4 K ev k₀ hk hq hd)

end GlobalTheory.UCanon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiFiniteTautologicalChartClosedPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiFinite_tautologicalChart_closedPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → (∀ p : Sp (ChartRing k m e), ξ p = ξ (closedPoint _) → p = closedPoint _) ∧ ((residue (ChartRing k m e)).comp (Scheme.stalkClosedPointTo ξ).hom).Finite := by
  first | exact @GlobalTheory.UCanon.quasiFinite_of_tautB | exact GlobalTheory.UCanon.quasiFinite_of_tautB | (intros; apply GlobalTheory.UCanon.quasiFinite_of_tautB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFiniteOfRingKrullDimEqLocalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFiniteOfRingKrullDimEqLocalDomain
open IsLocalRing

namespace GlobalTheory


open IsLocalRing in
theorem _root_.GlobalTheory.injective_of_finite_of_ringKrullDim_eq_of_local_domain :
    ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R]
      [IsLocalRing R] (ψ : B →+* R), ψ.Finite → ringKrullDim R = ringKrullDim B →
      Function.Injective ψ := by
  intro B R _ _ _ _ _ _ ψ hψ hdim
  letI : Algebra B R := ψ.toAlgebra
  haveI : Module.Finite B R := hψ
  have hlt : ringKrullDim B < ⊤ := ringKrullDim_lt_top
  have hne : ringKrullDim B ≠ ⊥ := fun h =>
    (WithBot.bot_lt_coe (0 : ℕ∞)).not_ge (h ▸ (ringKrullDim_nonneg_of_nontrivial (R := B)))
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hne
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℕ∞) = m := by
    refine ENat.ne_top_iff_exists.mp ?_
    rintro rfl
    exact hlt.ne hm.symm
  exact _root_.GlobalTheory.CohenStructure.injective_of_ringKrullDim_eq (A := B) (S := R) hm.symm
    (hdim.trans hm.symm)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFiniteOfRingKrullDimEqLocalDomainStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_of_finite_of_ringKrullDim_eq_localDomain : ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R] [IsLocalRing R] (ψ : B →+* R), ψ.Finite → ringKrullDim R = ringKrullDim B → Function.Injective ψ := by
  first | exact @GlobalTheory.injective_of_finite_of_ringKrullDim_eq_of_local_domain | exact GlobalTheory.injective_of_finite_of_ringKrullDim_eq_of_local_domain | (intros; apply GlobalTheory.injective_of_finite_of_ringKrullDim_eq_of_local_domain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveFiniteOfUniqueEmbeddingCompleteNormal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveFiniteOfUniqueEmbeddingCompleteNormal
open IsLocalRing

namespace GlobalTheory.DegreeOne

theorem surjective_of_unique_injective_localHom : ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [IsIntegrallyClosed B] [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (ψ : B →+* R), IsAdicComplete (maximalIdeal B) B → Function.Injective ψ → ψ.Finite → (∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [CharZero R'], IsAdicComplete (maximalIdeal R') R' → ∀ f g : R →+* R', Function.Injective f → Function.Injective g → IsLocalHom f → IsLocalHom g → f.comp ψ = g.comp ψ → f = g) → Function.Surjective ψ := by
  intro B R _ _ _ _ _ _ _ _ _ ψ hB hinj hfin huniq
  haveI := hB
  letI : Algebra B R := ψ.toAlgebra
  haveI : Module.Finite B R := hfin
  haveI : Algebra.IsIntegral B R := Algebra.IsIntegral.of_finite B R
  haveI : FaithfulSMul B R := (faithfulSMul_iff_algebraMap_injective B R).2 hinj
  haveI : CharZero B := ⟨fun m n h => Nat.cast_injective (R := R) (by simpa only [map_natCast] using congrArg ψ h)⟩
  let K := FractionRing B
  let M := FractionRing R
  have hBM : Function.Injective (algebraMap B M) := by
    rw [IsScalarTower.algebraMap_eq B R M]
    exact (IsFractionRing.injective R M).comp hinj
  haveI : FaithfulSMul B M := (faithfulSMul_iff_algebraMap_injective B M).2 hBM
  letI : Algebra K M := FractionRing.liftAlgebra B M
  haveI : IsScalarTower B K M := FractionRing.isScalarTower_liftAlgebra B M
  haveI : Module.Finite K M := Module.Finite.of_isLocalization B R (Rₚ := K) (Sₚ := M) (nonZeroDivisors B)
  haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing B (K := K)
  let Ω := AlgebraicClosure M
  let L := IntermediateField.normalClosure K M Ω
  haveI : FiniteDimensional K L := normalClosure.is_finiteDimensional K M Ω
  haveI : IsScalarTower B K Ω := inferInstance
  haveI : IsScalarTower B K L := inferInstance
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let C := integralClosure B L
  haveI : Module.Finite B C := IsIntegralClosure.finite B K L C
  haveI : IsLocalRing C := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := B) C
  haveI : IsNoetherianRing C := IsNoetherianRing.of_finite B C
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K
  haveI : CharZero C := ⟨fun m n h => Nat.cast_injective (R := L) (by simpa using congrArg Subtype.val h)⟩
  have hCc : IsAdicComplete (maximalIdeal C) C := CompleteFiniteExtension.isAdicComplete_of_finite_local B C

  have hK : ∀ b : B, algebraMap K L (algebraMap B K b) = algebraMap B L b := fun b =>
    (IsScalarTower.algebraMap_apply B K L b).symm
  have key : ∀ σ : M →ₐ[K] Ω, ∃ f : R →+* C, Function.Injective f ∧ IsLocalHom f ∧ f.comp ψ = algebraMap B C ∧
      ∀ r, ((f r : L) : Ω) = σ (algebraMap R M r) := by
    intro σ
    have hmem : ∀ x, (σ.toRingHom.comp (algebraMap R M)) x ∈ L := fun x =>
      σ.fieldRange_le_normalClosure ⟨_, rfl⟩
    let g₀ : R →+* L := (σ.toRingHom.comp (algebraMap R M)).codRestrict L hmem
    have hg₀ : ∀ b, g₀ (algebraMap B R b) = algebraMap B L b := by
      intro b
      apply Subtype.val_injective
      show σ (algebraMap R M (algebraMap B R b)) = _
      rw [← IsScalarTower.algebraMap_apply B R M, IsScalarTower.algebraMap_apply B K M, σ.commutes,
        ← hK]
      rfl
    let g : R →ₐ[B] L := { g₀ with commutes' := hg₀ }
    have hC : ∀ r, g r ∈ C := fun r => (Algebra.IsIntegral.isIntegral (R := B) r).map g
    let f : R →+* C := (g : R →+* L).codRestrict C hC
    have hcomm : f.comp ψ = algebraMap B C := by
      ext b
      exact congrArg Subtype.val (hg₀ b)
    have hfinj : Function.Injective f := fun x y h =>
      IsFractionRing.injective R M (σ.injective (congrArg (fun c : C => ((c : L) : Ω)) h))
    have hfi : f.IsIntegral := by
      letI : Algebra R C := f.toAlgebra
      haveI : IsScalarTower B R C := IsScalarTower.of_algebraMap_eq' hcomm.symm
      intro c
      exact (integralClosure.isIntegral c).tower_top
    exact ⟨f, hfinj, RingHom.IsIntegral.isLocalHom hfi hfinj, hcomm, fun r => rfl⟩
  choose f hfi hfl hfc hfv using key
  have hemb : ∀ σ τ : M →ₐ[K] Ω, σ = τ := by
    intro σ τ
    have h := huniq C hCc (f σ) (f τ) (hfi σ) (hfi τ) (hfl σ) (hfl τ) ((hfc σ).trans (hfc τ).symm)
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (nonZeroDivisors R) (S := M)
    ext r
    simp only [RingHom.comp_apply, AlgHom.coe_toRingHom]
    rw [← hfv σ r, ← hfv τ r, h]
  have hrank : Module.finrank K M = 1 := by
    rw [← Field.finSepDegree_eq_finrank_of_isSeparable K M]
    unfold Field.finSepDegree
    haveI : Subsingleton (Field.Emb K M) := ⟨hemb⟩
    exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨IsAlgClosed.lift⟩⟩
  have hbot : (⊥ : Subalgebra K M) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one hrank
  intro r
  obtain ⟨k, hk⟩ := Algebra.mem_bot.1 (hbot.symm ▸ Algebra.mem_top : algebraMap R M r ∈ (⊥ : Subalgebra K M))
  have hki : IsIntegral B k := by
    have h1 : IsIntegral B (algebraMap K M k) := hk ▸
      (Algebra.IsIntegral.isIntegral (R := B) r).map (IsScalarTower.toAlgHom B R M)
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom B K M) (algebraMap K M).injective).1 h1
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hki
  refine ⟨b, IsFractionRing.injective R M ?_⟩
  rw [← hk, ← IsScalarTower.algebraMap_apply B K M, IsScalarTower.algebraMap_apply B R M]
  rfl

end GlobalTheory.DegreeOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveFiniteOfUniqueEmbeddingCompleteNormalStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_finite_of_unique_embedding_complete_normal : ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [IsIntegrallyClosed B] [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (ψ : B →+* R), IsAdicComplete (maximalIdeal B) B → Function.Injective ψ → ψ.Finite → (∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [CharZero R'], IsAdicComplete (maximalIdeal R') R' → ∀ f g : R →+* R', Function.Injective f → Function.Injective g → IsLocalHom f → IsLocalHom g → f.comp ψ = g.comp ψ → f = g) → Function.Surjective ψ := by
  first | exact @GlobalTheory.DegreeOne.surjective_of_unique_injective_localHom | exact GlobalTheory.DegreeOne.surjective_of_unique_injective_localHom | (intros; apply GlobalTheory.DegreeOne.surjective_of_unique_injective_localHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfMaximalIdealLeRadicalCompleteNakayama
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfMaximalIdealLeRadicalCompleteNakayama
open IsLocalRing

namespace GlobalTheory.CompleteNakayamaLocal

theorem exists_fg_sup_pow_eq_top {B R : Type} [CommRing B] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra B R]
    (hres : Module.Finite B (R ⧸ maximalIdeal R)) (n : ℕ) :
    ∃ P : Submodule B R, P.FG ∧ P ⊔ (maximalIdeal R ^ n).restrictScalars B = ⊤ := by
  obtain ⟨T, hT⟩ := (Module.Finite.fg_top (R := B) (M := R ⧸ maximalIdeal R))
  choose lift hlift using fun x : R ⧸ maximalIdeal R => Ideal.Quotient.mk_surjective x

  have hTop : Submodule.span B (lift '' (T : Set _)) ⊔ (maximalIdeal R).restrictScalars B = ⊤ := by
    rw [eq_top_iff]
    intro r _
    have hr : Ideal.Quotient.mk (maximalIdeal R) r ∈ Submodule.span B (T : Set _) := by
      rw [hT]; trivial
    have hmap : Submodule.span B (T : Set (R ⧸ maximalIdeal R)) =
        (Submodule.span B (lift '' (T : Set _))).map
          (Ideal.Quotient.mkₐ B (maximalIdeal R)).toLinearMap := by
      rw [Submodule.map_span, ← Set.image_comp]
      congr 1
      ext x
      simp [hlift]
    rw [hmap] at hr
    obtain ⟨t, ht, hte⟩ := hr
    have hu : r - t ∈ maximalIdeal R := by
      rw [← Ideal.Quotient.eq]
      simpa using hte.symm
    rw [Submodule.mem_sup]
    exact ⟨t, ht, r - t, hu, by ring⟩
  induction n with
  | zero => exact ⟨⊥, Submodule.fg_bot, by simp⟩
  | succ n ih =>
    obtain ⟨P, hP, hPtop⟩ := ih
    obtain ⟨gens, hgens⟩ := (IsNoetherian.noetherian (maximalIdeal R ^ n) : (maximalIdeal R ^ n).FG)
    let G : Set R := Set.image2 (· * ·) (lift '' (T : Set _)) (gens : Set R)
    have hGf : G.Finite := ((T.finite_toSet.image _).image2 _ gens.finite_toSet)
    refine ⟨P ⊔ Submodule.span B G, hP.sup (Submodule.fg_def.2 ⟨G, hGf, rfl⟩), ?_⟩

    have key : ∀ y ∈ maximalIdeal R ^ n, ∀ r : R,
        r * y ∈ Submodule.span B G ⊔ (maximalIdeal R ^ (n + 1)).restrictScalars B := by
      intro y hy
      rw [← hgens] at hy
      induction hy using Submodule.span_induction with
      | mem g hg =>
        intro r
        have hr : r ∈ (⊤ : Submodule B R) := trivial
        rw [← hTop, Submodule.mem_sup] at hr
        obtain ⟨t, ht, u, hu, rfl⟩ := hr
        rw [add_mul]
        refine Submodule.add_mem_sup ?_ ?_
        · have : t * g ∈ (Submodule.span B (lift '' (T : Set _))).map (LinearMap.mulRight B g) :=
            ⟨t, ht, rfl⟩
          rw [Submodule.map_span] at this
          refine Submodule.span_mono ?_ this
          rintro _ ⟨s, hs, rfl⟩
          exact ⟨s, hs, g, hg, rfl⟩
        · show u * g ∈ maximalIdeal R ^ (n + 1)
          rw [pow_succ']
          exact Ideal.mul_mem_mul hu (hgens ▸ Submodule.subset_span hg)
      | zero => intro r; simp
      | add a b _ _ ha hb => intro r; rw [mul_add]; exact Submodule.add_mem _ (ha r) (hb r)
      | smul s a _ ha => intro r; rw [smul_eq_mul, ← mul_assoc]; exact ha (r * s)
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ (⊤ : Submodule B R) := trivial
    rw [← hPtop, Submodule.mem_sup] at hx
    obtain ⟨p, hp, y, hy, rfl⟩ := hx
    have hy' := key y hy 1
    rw [one_mul, Submodule.mem_sup] at hy'
    obtain ⟨a, ha, c, hc, rfl⟩ := hy'
    rw [Submodule.mem_sup]
    refine ⟨p + a, Submodule.add_mem_sup hp ha, c, hc, by ring⟩

theorem finite_of_maximalIdeal_le_radical : ∀ (B R : Type) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (ψ : B →+* R),
    IsAdicComplete (maximalIdeal B) B → IsLocalHom ψ →
    maximalIdeal R ≤ ((maximalIdeal B).map ψ).radical → ((residue R).comp ψ).Finite →
    ψ.Finite := by
  intro B R _ _ _ _ _ _ ψ hB hψ hrad hres
  letI : Algebra B R := ψ.toAlgebra
  set J : Ideal R := (maximalIdeal B).map (algebraMap B R) with hJdef
  have hJm : J ≤ maximalIdeal R := by
    refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => (mem_maximalIdeal x).1 hx (isUnit_of_map_unit ψ x h)
  haveI : IsHausdorff J R := ⟨fun x hx => IsHausdorff.haus (I := maximalIdeal R) inferInstance x
    fun n => (hx n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJm n))⟩
  obtain ⟨e, he⟩ : ∃ e, maximalIdeal R ^ e ≤ J :=
    Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have hres' : Module.Finite B (R ⧸ maximalIdeal R) := hres
  obtain ⟨P, hP, hPtop⟩ := exists_fg_sup_pow_eq_top hres' e
  haveI : Module.Finite B (R ⧸ J) := by
    refine ⟨?_⟩
    have : (⊤ : Submodule B (R ⧸ J)) = P.map (Ideal.Quotient.mkₐ B J).toLinearMap := by
      refine le_antisymm ?_ le_top
      rintro z -
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hx : x ∈ (⊤ : Submodule B R) := trivial
      rw [← hPtop, Submodule.mem_sup] at hx
      obtain ⟨p, hp, y, hy, rfl⟩ := hx
      refine ⟨p, hp, ?_⟩
      show Ideal.Quotient.mk J p = Ideal.Quotient.mk J (p + y)
      rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 (he hy), add_zero]
    rw [this]
    exact hP.map _
  exact GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal B)

end GlobalTheory.CompleteNakayamaLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfMaximalIdealLeRadicalCompleteNakayamaStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_of_maximalIdeal_le_radical_complete_nakayama : ∀ (B R : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (ψ : B →+* R), IsAdicComplete (maximalIdeal B) B → IsLocalHom ψ → maximalIdeal R ≤ ((maximalIdeal B).map ψ).radical → ((residue R).comp ψ).Finite → ψ.Finite := by
  first | exact @GlobalTheory.CompleteNakayamaLocal.finite_of_maximalIdeal_le_radical | exact GlobalTheory.CompleteNakayamaLocal.finite_of_maximalIdeal_le_radical | (intros; apply GlobalTheory.CompleteNakayamaLocal.finite_of_maximalIdeal_le_radical <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartIsEtaleCompletionLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TautEtaleB

theorem isEtaleCompletion_of_forall_eq_inj (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R]
    (hAd : IsDomain (AdicCompletion (maximalIdeal A) A))
    (hAn : IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A))
    (hR : IsAdicComplete (maximalIdeal R) R) (φ : A →+* R) (hφ : IsLocalHom φ)
    (hprim : maximalIdeal R ≤ ((maximalIdeal A).map φ).radical)
    (hres : ((residue R).comp φ).Finite) (hdim : ringKrullDim R = ringKrullDim A)
    (hinj : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R']
      [IsIntegrallyClosed R'] [CharZero R'], IsAdicComplete (maximalIdeal R') R' →
      ∀ f g : R →+* R', Function.Injective f → Function.Injective g → IsLocalHom f → IsLocalHom g →
        f.comp φ = g.comp φ → f = g) :
    GlobalTheory.Toroidal.IsEtaleCompletion φ := by
  let B := AdicCompletion (maximalIdeal A) A
  haveI : IsNoetherianRing B := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _
  obtain ⟨ψ, hψl, hψ⟩ := GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_comp A R hR φ hφ
  have hmap : (maximalIdeal B).map ψ = (maximalIdeal A).map φ := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hψ]
  have hresψ : ((residue R).comp ψ).Finite := by
    have e : ((residue R).comp ψ).comp (algebraMap A B) = (residue R).comp φ := by
      rw [RingHom.comp_assoc, hψ]
    exact RingHom.Finite.of_comp_finite (e ▸ hres)
  have hfin : ψ.Finite := GlobalTheory.T.finite_of_maximalIdeal_le_radical_complete_nakayama B R ψ inferInstance hψl (hmap ▸ hprim) hresψ
  have hdB : ringKrullDim R = ringKrullDim B := by rw [hdim, UpperTheory.V.CA.g_dimcpl]
  have hi : Function.Injective ψ := GlobalTheory.T.injective_of_finite_of_ringKrullDim_eq_localDomain B R ψ hfin hdB
  have hs : Function.Surjective ψ := GlobalTheory.T.surjective_finite_of_unique_embedding_complete_normal B R ψ inferInstance hi hfin
    (fun R' _ _ _ _ _ _ hR' f g hf' hg' hf hg h => hinj R' hR' f g hf' hg' hf hg (by
      rw [← hψ, ← RingHom.comp_assoc, h, RingHom.comp_assoc]))
  refine ⟨?_, ?_, hres⟩
  · rw [← hψ]
    refine RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian _)) ?_
    exact RingHom.Flat.of_bijective ⟨hi, hs⟩
  · rw [← hmap]
    exact map_maximalIdeal_of_surjective ψ hs

theorem charZero_essFiniteType_stalk (K : Type) [Field K] [CharZero K] [FiniteDimensional ℚ K] {X : Scheme.{0}}
    (f : X ⟶ Sp K) [LocallyOfFiniteType f] (x : X) :
    CharZero (X.presheaf.stalk x) ∧ Algebra.EssFiniteType ℤ (X.presheaf.stalk x) := by
  let y : PrimeSpectrum K := f x
  letI : Algebra K ((Sp K).presheaf.stalk (f x)) := StructureSheaf.stalkAlgebra _ y
  haveI : IsLocalization.AtPrime ((Sp K).presheaf.stalk (f x)) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := algebraMap K ((Sp K).presheaf.stalk (f x))
  have h₁ : (f.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap f x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  have hσ : Function.Injective ((f.stalkMap x).hom.comp φ) := RingHom.injective _
  refine ⟨charZero_of_injective_ringHom hσ, ?_⟩
  have hQ : Algebra.EssFiniteType ℤ ℚ := Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)
  have hK : Algebra.EssFiniteType ℤ K := Algebra.EssFiniteType.comp ℤ ℚ K
  refine RingHom.essFiniteType_algebraMap.1 ?_
  convert (RingHom.essFiniteType_algebraMap.2 hK).comp (h₂.comp h₁) using 1
  exact Subsingleton.elim _ _

theorem exists_fracMap {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (ψ : A →+* B)
    (hψ : Function.Injective ψ) : ∃ fK : FractionRing A →+* FractionRing B, spMap fK ≫ jK A = jK B ≫ spMap ψ := by
  have hg : Function.Injective ((algebraMap B (FractionRing B)).comp ψ) :=
    (IsFractionRing.injective B (FractionRing B)).comp hψ
  let fK : FractionRing A →+* FractionRing B :=
    IsFractionRing.lift (K := FractionRing A) (L := FractionRing B) (g := (algebraMap B (FractionRing B)).comp ψ) hg
  have e0 : fK.comp (algebraMap A (FractionRing A)) = (algebraMap B (FractionRing B)).comp ψ := by
    ext x
    rw [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (K := FractionRing A) (L := FractionRing B) hg x
  refine ⟨fK, ?_⟩
  have e1 : CommRingCat.ofHom (algebraMap A (FractionRing A)) ≫ CommRingCat.ofHom fK =
      CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap B (FractionRing B)) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e0]
  have e2 := congrArg Spec.map e1
  rw [Spec.map_comp, Spec.map_comp] at e2
  exact e2

theorem tautB_isEtaleCompletion : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hSep k _ m e C hT ξ hξ
  obtain ⟨hqf, hfin⟩ := GlobalTheory.T.quasiFinite_tautologicalChart_closedPoint Xo c φ hpq hpf hns zs i OZ N d J π j BD hU hSep C hT ξ hξ
  have hdimS := ringKrullDim_stalk_eq_of_isTaut hU C hT.1 ξ hξ hfin
  haveI hcF : CharZero (ChartRing k m e) := (C.b.charZero_iff C.b.injective).1 inferInstance
  have hAdm := GlobalTheory.MumfordChart.admissibleBase_chartRing k m e
  haveI : IsNoetherianRing (ChartRing k m e) := hAdm.1
  haveI : IsIntegrallyClosed (ChartRing k m e) := hAdm.2.2.1
  have hRc : IsAdicComplete (maximalIdeal (ChartRing k m e)) (ChartRing k m e) := hAdm.2.2.2
  have hdimR : ringKrullDim (ChartRing k m e) = ((m + e : ℕ) : WithBot ℕ∞) := by
    rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries k (Fin m ⊕ Fin e), ringKrullDim_eq_zero_of_field]
    simp [Nat.card_sum]
  obtain ⟨⟨-, -, -, -, hizs, -⟩, -, -, -, ⟨⟨hnorm, -⟩, hproj, -, -, hji, -⟩, -⟩ := hU
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  haveI := c.fin
  set x := ξ (closedPoint (ChartRing k m e)) with hx
  haveI : IsDomain (S.presheaf.stalk x) := hnorm.isDomain_stalk x
  haveI : IsIntegrallyClosed (S.presheaf.stalk x) := hnorm.isIntegrallyClosed_stalk x
  obtain ⟨hc0, hess⟩ := charZero_essFiniteType_stalk c.F (π ≫ zs) x
  haveI := hc0
  haveI := hess
  haveI : IsNoetherianRing (S.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  obtain ⟨hAd, hAn⟩ := GlobalTheory.T.adicCompletion_isDomain_and_isIntegrallyClosed (S.presheaf.stalk x)
  set ψ := (Scheme.stalkClosedPointTo ξ).hom with hψ
  have eξ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have hpt : ∀ p : Sp (ChartRing k m e), ξ p = S.fromSpecStalk x (Spec.map (Scheme.stalkClosedPointTo ξ) p) := by
    intro p
    conv_lhs => rw [← eξ]
    rfl
  have hprim : maximalIdeal (ChartRing k m e) ≤ ((maximalIdeal (S.presheaf.stalk x)).map ψ).radical := by
    intro r hr
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hle, hP⟩
    have hc : Ideal.comap ψ P = maximalIdeal (S.presheaf.stalk x) :=
      ((maximalIdeal.isMaximal _).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.1 hle)).symm
    have hq : (⟨P, hP⟩ : Sp (ChartRing k m e)) = closedPoint (ChartRing k m e) := by
      refine hqf _ ((hpt _).trans (Eq.trans ?_ (hpt (closedPoint _)).symm))
      congr 1
      refine PrimeSpectrum.ext ?_
      show Ideal.comap ψ P = Ideal.comap ψ (maximalIdeal (ChartRing k m e))
      rw [hc]
      refine le_antisymm ?_ (le_maximalIdeal (Ideal.comap_ne_top _ (maximalIdeal.isMaximal _).ne_top))
      intro a ha
      exact map_nonunit ψ a ha
    have hP' : P = maximalIdeal (ChartRing k m e) := congrArg PrimeSpectrum.asIdeal hq
    rw [hP']
    exact hr
  have hinj : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R']
      [IsIntegrallyClosed R'] [CharZero R'], IsAdicComplete (maximalIdeal R') R' →
      ∀ f g : ChartRing k m e →+* R', Function.Injective f → Function.Injective g → IsLocalHom f → IsLocalHom g →
        f.comp ψ = g.comp ψ → f = g := by
    intro R' _ _ _ _ _ _ hR' f g hfi hgi hfl hgl hfg
    have hB : GlobalTheory.Mum.Base R' := ⟨⟨inferInstance, inferInstance, inferInstance, hR'⟩, inferInstance⟩
    obtain ⟨fK, hfK⟩ := exists_fracMap f hfi
    obtain ⟨gK, hgK⟩ := exists_fracMap g hgi
    obtain ⟨-, -, -, hInj, -⟩ := hT.1
    refine hInj R' hB f g hfi hgi hfl hgl (spMap fK) (spMap gK) hfK hgK ?_
    have hsp : spMap f ≫ Spec.map (Scheme.stalkClosedPointTo ξ) = spMap g ≫ Spec.map (Scheme.stalkClosedPointTo ξ) := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext a
      exact congrArg (fun h : S.presheaf.stalk x →+* R' => h a) hfg
    have hfξ : spMap f ≫ ξ = spMap g ≫ ξ := by
      calc spMap f ≫ ξ = spMap f ≫ (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ S.fromSpecStalk x) := by rw [eξ]
        _ = spMap g ≫ (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ S.fromSpecStalk x) := by
          rw [← Category.assoc, hsp, Category.assoc]
        _ = spMap g ≫ ξ := by rw [eξ]
    rw [← cancel_mono j, Category.assoc, Category.assoc, hξ, ← Category.assoc, ← Category.assoc, hfK, hgK,
      Category.assoc, Category.assoc, hfξ]
  exact isEtaleCompletion_of_forall_eq_inj (S.presheaf.stalk x) (ChartRing k m e) hAd hAn hRc ψ inferInstance hprim hfin
    (by rw [hdimR, hdimS]) hinj

end GlobalTheory.TautEtaleB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartIsEtaleCompletionLocalRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautologicalChart_isEtaleCompletion_localRing : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom := by
  first | exact @GlobalTheory.TautEtaleB.tautB_isEtaleCompletion | exact GlobalTheory.TautEtaleB.tautB_isEtaleCompletion | (intros; apply GlobalTheory.TautEtaleB.tautB_isEtaleCompletion <;> assumption)
end
