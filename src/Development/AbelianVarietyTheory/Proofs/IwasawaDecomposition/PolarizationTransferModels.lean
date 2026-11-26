module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericLieMultiplicitiesUniformisedGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocalization
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnitHmE

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TraitOrder

theorem idlAlong_eq_map {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R] (χ : Sp R ⟶ X)
    (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
    idlAlong J χ = (J.ideal U).map (χ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of R)).hom).hom := by
  have hx : χ (closedPoint R) ∈ U.1 := hle trivial
  unfold idlAlong
  rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
  congr 2

theorem idlAlong_comp {X : Scheme.{0}} (J : X.IdealSheafData) {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] (χ : Sp R ⟶ X) (f : R →+* S) : idlAlong J (spMap f ≫ χ) = (idlAlong J χ).map f := by
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
  have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
  have hle' : ⊤ ≤ (spMap f ≫ χ) ⁻¹ᵁ U := fun x _ => hle (show spMap f x ∈ (⊤ : (Sp R).Opens) from trivial)
  rw [idlAlong_eq_map J χ ⟨U, hU⟩ hle, idlAlong_eq_map J _ ⟨U, hU⟩ hle', Ideal.map_map]
  congr 1
  have e : (spMap f ≫ χ).appLE U ⊤ hle' = χ.appLE U ⊤ hle ≫ (spMap f).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
  rfl

theorem map_injective {R S : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S] [IsDomain S]
    [IsLocalRing S] (f : R →+* S) (hf : Function.Injective f) [IsLocalHom f] {I J : Ideal R}
    (h : I.map f = J.map f) : I = J := by
  letI := f.toAlgebra
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
  have : IsLocalHom (algebraMap R S) := ‹IsLocalHom f›
  have : Module.Flat R S := inferInstance
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) I, ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) J]
  exact congrArg _ h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem comp {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {h : S'' ⟶ S} (e : g ≫ f = h) (m : SABMap t' t f) (m' : SABMap t'' t' g) : Nonempty (SABMap t'' t h) :=
  e ▸ ⟨(sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m').choose⟩

theorem cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {h : S'' ⟶ S} (e : g ≫ f = h) (m : SABMap t' t f) (n : SABMap t'' t h) : Nonempty (SABMap t'' t' g) := by
  subst e
  exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n).choose⟩

end GlobalTheory.TraitOrder
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletion
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.CharRank

open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.Serre GlobalTheory.EigenSplit Matrix GlobalTheory.LieUnif
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)
open scoped CategoryTheory.Obj

theorem trace_of_unif_loc {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    {D : DegData R (maximalIdeal R)} {P : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D P G) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X] {oD : D.OAct O}
    {oP : P.OAct O} {aG : OAct O G} (hl : U.OLinear O oD oP aG.toRingAct) [IsCommMonObj D.toPre.P.A]
    [Smooth D.toPre.P.A.hom] {g h r : ℕ} {v : Fin g → (epsR R ⟶ G)} (hv : IsLieBasis v)
    {ρ : O →+* Module.End R (Fin g → R)} (hρ : ∀ a c, prodPts (ρ a c) v = prodPts c v ≫ aG.act a)
    {w : Fin h → (epsR R ⟶ D.toPre.P.A)} (hw : IsLieBasis w)
    {ρB : O →+* Module.End R (Fin h → R)}
    (hρB : ∀ a c, prodPts (ρB a c) w = prodPts c w ≫ (ofRingAct oD.onB.toRingAct).act a)
    (b : Module.Basis (Fin r) ℤ D.toPre.X) (a : O) :
    LinearMap.trace R _ (ρ a) = LinearMap.trace R _ (ρB a) + (latTrace b a : R) := by
  have key : ∀ e : ℕ, LinearMap.trace R _ (ρ a) - (LinearMap.trace R _ (ρB a) + (latTrace b a : R)) ∈
      maximalIdeal R ^ (e + 1) := fun e => by
    let f := Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))
    have : IsLocalRing (R ⧸ maximalIdeal R ^ (e + 1)) := by
      have : Nontrivial (R ⧸ maximalIdeal R ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 fun h =>
        (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h.symm.le.trans (Ideal.pow_le_self (Nat.succ_ne_zero e))))
      exact IsLocalRing.of_surjective' f Ideal.Quotient.mk_surjective
    have := U.smooth
    obtain ⟨v', ρ', hv', hρ', hM⟩ := ToricRank.exists_action_pullback hv hρ f
    obtain ⟨w', ρB', hw', hρB', hMB⟩ := ToricRank.exists_action_pullback hw hρB f
    let gc := U.gt e
    have := gc.q_hom
    have := gc.i_hom
    have := gc.q_flat
    have := gc.q_surj
    have := gc.q_affine
    have := (H1.torus_dim (Sp (R ⧸ maximalIdeal R ^ (e + 1))) D.toPre.X).smooth
    have : Smooth gc.q.left := by
      refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
        ((H1.torsor_pullback gc.i gc.q gc.isKernel).map (Over.forget _)).flip
        ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact gc.q.left)⟩ ?_
      exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
    let aK := @Diag.diagAct (Sp (R ⧸ maximalIdeal R ^ (e + 1))) O _ D.toPre.X _ (Module.compHom _ (starRingEnd O))
    let MK : O → Matrix (Fin r) (Fin r) (R ⧸ maximalIdeal R ^ (e + 1)) := fun x =>
      (LinearMap.toMatrix b b (DistribSMul.toAddMonoidHom D.toPre.X (star x)).toIntLinearMap).map (Int.castRingHom _)
    have hvK := Diag.isLieBasis_dualBasis (R := R ⧸ maximalIdeal R ^ (e + 1)) b
    have hMK : ∀ x i, IsLieComb (MK x i) (fun i => Diag.lieVec (Diag.dualBasis _ b i))
        (Diag.lieVec (Diag.dualBasis _ b i) ≫ aK.act x) := fun x i =>
      Diag.isLieComb_comp_diagMap b b (DistribSMul.toAddMonoidHom D.toPre.X (star x)) i
    have hi : IsLinearHom aK (aG.pullback (thick R _ e) G) gc.i := ⟨inferInstance, fun x => by
      obtain ⟨t, ht, hi⟩ := hl.i_lin e x
      obtain rfl := ConstBasis.eq_diagMap (DistribSMul.toAddMonoidHom D.toPre.X (star x)) ht
      exact hi.symm⟩
    have h := trace_level (K := splitTorus (Sp (R ⧸ maximalIdeal R ^ (e + 1))) D.toPre.X) (aK := aK)
      (aG := aG.pullback (thick R _ e) G) (aB := (ofRingAct oD.onB.toRingAct).pullback (thick R _ e) _)
      (i := gc.i) (q := gc.q) hi ⟨inferInstance, hl.q_lin e⟩ gc.isKernel hvK hv' hw' a
      (MK a) ((LinearMap.toMatrix' (ρ a))ᵀ.map f) ((LinearMap.toMatrix' (ρB a))ᵀ.map f)
      (fun c => (ConstBasis.prodPts_act hvK hMK a c).symm) (fun c => by rw [← hM, hρ']) (fun c => by rw [← hMB, hρB'])
    rw [← Ideal.Quotient.eq, map_add (f := _), map_intCast, trace_map_eq, trace_map_eq, h]
    refine (add_comm _ _).trans (congrArg _ ?_)
    simp [MK, latTrace, Matrix.trace]
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top,
    Ideal.mem_iInf]
  intro n
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (key n)

theorem lieMult_unif_loc {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (t : SAB H (Sp R))
    (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] (f : R →+* F) (hf : Function.Injective f)
    (τ : 𝓞 E →+* F) (N : ℕ) (hN : LieMult t.act (spMap f) τ N) :
    letI := H.starRing; ∃ n, LieMult (ofRingAct P.oD.onB.toRingAct) (spMap f) τ n ∧
      n + Module.finrank (𝓞 E) P.D.toPre.X = N := by
  classical
  letI := H.starRing
  haveI : CharZero F := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  have := P.U.smooth
  have : Smooth P.D.toPre.P.A.hom := P.D.toPre.P.smoothDim.smooth
  obtain ⟨g, v, hv⟩ := Chart.exists_isLieBasis t.G P.U.smooth
  obtain ⟨ρ, hρ⟩ := LieEigen.exists_action hv t.act
  obtain ⟨h, w, hw⟩ := Chart.exists_isLieBasis P.D.toPre.P.A this
  obtain ⟨ρB, hρB⟩ := LieEigen.exists_action hw (ofRingAct P.oD.onB.toRingAct)
  let b := Module.finBasis ℤ P.D.toPre.X
  have htr := trace_of_unif_loc P.U.toUnifPre P.lin hv hρ hw hρB b
  obtain ⟨v', ρ', hv', hρ', hM⟩ := ToricRank.exists_action_pullback hv hρ f
  obtain ⟨w', ρB', hw', hρB', hMB⟩ := ToricRank.exists_action_pullback hw hρB f
  let aG := t.act.pullback (spMap f) t.G
  let aB := (ofRingAct P.oD.onB.toRingAct).pullback (spMap f) P.D.toPre.P.A
  haveI := Module.Finite.of_basis (Lie.basis aG hv')
  haveI := Module.Finite.of_basis (Lie.basis aB hw')
  have tG : ∀ a, LinearMap.trace F (Lie aG) (Module.toModuleEnd F (Lie aG) a) = f (LinearMap.trace R _ (ρ a)) :=
    fun a => by rw [trace_map_eq]; exact trace_lie hv' aG a _ (fun c => by rw [← hM, hρ'])
  have tB : ∀ a, LinearMap.trace F (Lie aB) (Module.toModuleEnd F (Lie aB) a) = f (LinearMap.trace R _ (ρB a)) :=
    fun a => by rw [trace_map_eq]; exact trace_lie hw' aB a _ (fun c => by rw [← hMB, hρB'])
  let σ : (E →+* F) → 𝓞 E →+* F := fun i => i.comp (algebraMap (𝓞 E) E)
  have hinj : Function.Injective σ := fun i j hij =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) hij
  have hσ : IsSplitting σ := by
    simpa using isSplitting_of_isDomain hinj (NumberField.Embeddings.card E F) (RingHom.id F)
      (isUnit_discr_of_charZero F)
  obtain ⟨j, rfl⟩ : ∃ j, σ j = τ :=
    ⟨IsFractionRing.lift (injective_of_charZero τ), RingHom.ext fun x => IsFractionRing.lift_algebraMap (injective_of_charZero τ) x⟩
  have : Module.Finite (𝓞 E) P.D.toPre.X := .of_restrictScalars_finite ℤ _ _
  have he : ∀ {X : Over (Sp F)} [GrpObj X] [IsCommMonObj X] (a : OAct (𝓞 E) X),
      Lie.eig a (σ j) = eigenSub (Module.toModuleEnd F (Lie a)) (σ j) := fun a =>
    Submodule.ext fun v => by rw [mem_eigenSub]; rfl
  have hm := mult_eq hinj (fun i => Module.finrank F (eigenSub (Module.toModuleEnd F (Lie aG)) (σ i)))
    (fun i => Module.finrank F (eigenSub (Module.toModuleEnd F (Lie aB)) (σ i)))
    (Module.finrank (𝓞 E) P.D.toPre.X) (fun a => by
      have hT := trace_eq_sum hσ (torusRep (𝓞 E) P.D.toPre.X F) a
      simp only [fun i => finrank_eigenSub_torusRep (X := P.D.toPre.X) (σ i) (injective_of_charZero _)] at hT
      rw [← trace_eq_sum hσ, ← trace_eq_sum hσ, ← hT, tG, tB, htr, trace_torusRep b, map_add (f := _), map_intCast]) j
  rw [Lie.lieMult_iff_finrank (isLinearPullback_pullback _ (spMap f)), he] at hN
  refine ⟨_, ?_, hm.symm.trans hN.2⟩
  rw [Lie.lieMult_iff_finrank (isLinearPullback_pullback _ (spMap f)), he]
  exact ⟨inferInstance, rfl⟩

theorem bar_rt_neg {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.bar H.rt = -H.rt := by
  have h1 : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  refine (sq_eq_sq_iff_eq_or_eq_neg.mp h1).resolve_left fun h => ?_
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h2 : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E) := by
    rw [← IsCMField.complexEmbedding_complexConj, ← H.bar_eq, h]
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2
  have h3 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (φ.comp (algebraMap (𝓞 E) E)) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  rw [hr] at h3
  have h4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h3
  have h5 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

theorem exists_chars {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [IsAlgClosed K] [CharZero K] (δ : K) (hδ : δ ^ 2 = -(H.d : K)) :
    ∃ τ₁ τ₂ : 𝓞 E →+* K, τ₁ H.rt = δ ∧ τ₂ H.rt ≠ δ := by
  let e₀ : E →ₐ[ℚ] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let τ₀ : 𝓞 E →+* K := e₀.toRingHom.comp (algebraMap (𝓞 E) E)
  let τ' : 𝓞 E →+* K := τ₀.comp (H.bar : 𝓞 E →+* 𝓞 E)
  have h' : τ' H.rt = -τ₀ H.rt := by
    change τ₀ (H.bar H.rt) = _
    rw [bar_rt_neg, map_neg]
  have h0 : (τ₀ H.rt) ^ 2 = δ ^ 2 := by rw [← map_pow, H.rt_sq, map_neg, map_natCast, hδ]
  have hne : δ ≠ -δ := fun h => by
    have h2 : δ = 0 := by
      have : (2 : K) * δ = 0 := by linear_combination h
      exact (mul_eq_zero.1 this).resolve_left two_ne_zero
    rw [h2] at hδ
    have : (H.d : K) = 0 := by linear_combination hδ
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h0 with h | h
  · exact ⟨τ₀, τ', h, by rw [h', h]; exact fun e => hne e.symm⟩
  · exact ⟨τ', τ₀, by rw [h', h, neg_neg], by rw [h]; exact fun e => hne e.symm⟩

end GlobalTheory.CharRank
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

namespace GlobalTheory.CycAwayReg
open NumberField

theorem isDedekindDomain_closure {Ω K : Type} [Field Ω] [CharZero Ω] [Field K] [CharZero K] {n : ℕ} [NeZero n]
    [IsCyclotomicExtension {n} ℚ K] (φ : K →+* Ω) {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    IsDedekindDomain (Subring.closure {φ ζ, (n : Ω)⁻¹}) := by
  haveI : NumberField K := IsCyclotomicExtension.numberField {n} ℚ _
  have h0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  set T : Subring Ω := Subring.closure {φ ζ, (n : Ω)⁻¹} with hTdef
  let io : 𝓞 K →+* Ω := φ.comp (algebraMap _ K)
  have hio : Function.Injective io := φ.injective.comp RingOfIntegers.coe_injective
  have hmem : ∀ x, io x ∈ T := by
    intro x
    obtain ⟨y, hy⟩ := (IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton hζ).isIntegral_iff.1
      (RingOfIntegers.isIntegral_coe x)
    have h1 : (y : K) ∈ Subring.closure ({ζ} : Set K) := by
      exact Algebra.mem_adjoin_iff.1 y.2 |> fun h => (Subring.closure_le.2 (by
        rintro _ (⟨r, rfl⟩ | h)
        · exact intCast_mem (Subring.closure ({ζ} : Set K)) r
        · exact Subring.subset_closure h)) h
    have h2 : Subring.closure ({ζ} : Set K) ≤ T.comap φ := by
      rw [Subring.closure_le]
      rintro _ rfl
      exact Subring.subset_closure (Or.inl rfl)
    have h3 : io x = φ y := congrArg φ hy.symm
    rw [h3]
    exact h2 h1
  letI : Algebra (𝓞 K) T := (io.codRestrict _ hmem).toAlgebra
  have hL : IsLocalization (Submonoid.powers (n : 𝓞 K)) T := by
    refine GlobalTheory.CycAway.isLocalization_of_le_closure h0 _ _ (fun x y h => hio (congrArg (fun z : T => (z : Ω)) h))
      (Subring.subset_closure (Or.inr rfl)) (Subring.closure_mono ?_)
    rintro x (rfl | h)
    · exact Or.inl ⟨hζ.toInteger, rfl⟩
    · exact Or.inr h
  have hn' : (n : 𝓞 K) ≠ 0 := by exact_mod_cast NeZero.ne n
  exact IsLocalization.isDedekindDomain _ (powers_le_nonZeroDivisors_of_noZeroDivisors hn') _

theorem isDedekindDomain_cycAway_of_ne_zero {n : ℕ} (hn : n ≠ 0) : IsDedekindDomain (cycAway n) := by
  haveI : NeZero n := ⟨hn⟩
  let K := CyclotomicField n ℚ
  let φ : K →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ)).toRingHom
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ K
  have hz : IsPrimitiveRoot (φ (IsCyclotomicExtension.zeta n ℚ K)) n := hζ.map_of_injective φ.injective
  have he : IsPrimitiveRoot (zeta n) n := Complex.isPrimitiveRoot_exp n hn
  obtain ⟨k, hk, hkc⟩ := hz.eq_pow_of_pow_eq_one he.pow_eq_one
  have hζk := hζ.pow_of_coprime k (hz.pow_iff_coprime (Nat.pos_of_ne_zero hn) k |>.1 (hkc ▸ he))
  have := isDedekindDomain_closure φ hζk
  rwa [map_pow, hkc] at this

theorem isDedekindDomain_cycAway (n : ℕ) : IsDedekindDomain (cycAway n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : cycAway 0 = cycAway 1 := by
      have hb : ∀ m : ℕ, m ≤ 1 → cycAway m = ⊥ := by
        intro m hm
        refine le_antisymm (Subring.closure_le.2 ?_) bot_le
        rintro _ (rfl | rfl)
        · interval_cases m <;> simp [zeta]
        · interval_cases m <;> simp
      rw [hb 0 zero_le_one, hb 1 le_rfl]
    rw [h]
    exact isDedekindDomain_cycAway_of_ne_zero one_ne_zero
  · exact isDedekindDomain_cycAway_of_ne_zero hn.ne'

end GlobalTheory.CycAwayReg

namespace GlobalTheory.CycAwayReg

end GlobalTheory.CycAwayReg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL]
  {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}

def CrdOver {L L' : Type} [Field L] [Field L'] (ι : L →+* L') {n n' : ℕ} (x : Fin n → L) (x' : Fin n' → L') : Prop :=
  n = n' ∧ ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = ι (x k)


set_option maxHeartbeats 4000000 in
def RSideW (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) : Prop :=
  HEq R'.ψ z.R.ψ ∧ HEq R'.θ z.R.θ ∧ HEq R'.βW z.R.βW ∧ HEq R'.βY z.R.βY ∧ HEq R'.ΛY z.R.ΛY ∧ HEq R'.nW z.R.nW ∧ HEq R'.βV z.R.βV ∧
  HEq R'.ΛV z.R.ΛV ∧ HEq R'.ΛW z.R.ΛW ∧ HEq R'.Pg z.R.Pg ∧ HEq R'.eG z.R.eG ∧ HEq R'.Sb z.R.Sb ∧
  (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (R'.cV i').W (z.R.cV i).W ∧ HEq (R'.cV i').ρ (z.R.cV i).ρ ∧ HEq (R'.cV i').nW (z.R.cV i).nW ∧
    HEq (R'.cV i').iW (z.R.cV i).iW ∧ HEq (R'.vacP i') (z.R.vacP i) ∧ HEq (R'.ioP i') (z.R.ioP i) ∧
    HEq (R'.BV i') (z.R.BV i) ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).H (z.R.MW i (w.st Z).toD7.what₂.embLL).H ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).nacg (z.R.MW i (w.st Z).toD7.what₂.embLL).nacg ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).ips (z.R.MW i (w.st Z).toD7.what₂.embLL).ips ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).σ (z.R.MW i (w.st Z).toD7.what₂.embLL).σ ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).lam (z.R.MW i (w.st Z).toD7.what₂.embLL).lam ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).ε (z.R.MW i (w.st Z).toD7.what₂.embLL).ε ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).fr (z.R.MW i (w.st Z).toD7.what₂.embLL).fr ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).enum (z.R.MW i (w.st Z).toD7.what₂.embLL).enum ∧
    HEq (R'.HW i' (w'.st Z').toD7.what₂.embLL) (z.R.HW i (w.st Z).toD7.what₂.embLL) ∧
    HEq (R'.νW i') (z.R.νW i) ∧ HEq (R'.fdW i') (z.R.fdW i) ∧
    ∀ (ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL),
      (∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x) →
      (∀ σ' : (w'.st Z').toD7.what₂.LL →+* ℂ,
        (HEq (R'.MW i' σ').H (z.R.MW i (σ'.comp ι)).H ∧
          HEq (R'.MW i' σ').nacg (z.R.MW i (σ'.comp ι)).nacg ∧
          HEq (R'.MW i' σ').ips (z.R.MW i (σ'.comp ι)).ips ∧
          HEq (R'.MW i' σ').σ (z.R.MW i (σ'.comp ι)).σ ∧
          HEq (R'.MW i' σ').lam (z.R.MW i (σ'.comp ι)).lam ∧
          HEq (R'.MW i' σ').ε (z.R.MW i (σ'.comp ι)).ε ∧
          HEq (R'.MW i' σ').fr (z.R.MW i (σ'.comp ι)).fr ∧
          HEq (R'.MW i' σ').enum (z.R.MW i (σ'.comp ι)).enum) ∧
        HEq (R'.HW i' σ') (z.R.HW i (σ'.comp ι)) ∧
        HEq (R'.gW i' σ') (z.R.gW i (σ'.comp ι)) ∧
        ∀ x x', CrdOver ι x x' → HEq ((R'.FW i').j σ' x') ((z.R.FW i).j (σ'.comp ι) x)) ∧
      ((∀ x x', CrdOver ι x x' → (x' ∈ (R'.FW i').WK ↔ x ∈ (z.R.FW i).WK)) ∧
        ∀ x' ∈ (R'.FW i').WK, ∃ x : Fin (z.R.nW i) → (w.st Z).toD7.what₂.LL, CrdOver ι x x') ∧
      (∀ g' g, HEq g' g → (((R'.FW i').chi g' : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) =
        ι (((z.R.FW i).chi g : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) ∧
      (∀ g' g, HEq g' g → ∀ x x', CrdOver ι x x' → CrdOver ι ((z.R.FW i).ρ g x) ((R'.FW i').ρ g' x')) ∧
      HEq (R'.FW i').Pt (z.R.FW i).Pt ∧
      (∀ lp' lp, HEq lp' lp → ∀ y' y, HEq y' y → ∀ (φ' : (R'.FW i').WK) (φ : (z.R.FW i).WK), CrdOver ι φ.1 φ'.1 →
        (R'.FW i').nrm lp' y' φ' = (z.R.FW i).nrm lp y φ)) ∧
  ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ (ok : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).Ok)
      (ok' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).Ok)
      (φ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).EqFun)
      (φ' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).EqFun),
      (∀ d d', HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (φ'.1 d').1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (φ.1 d).1)) →
      HEq (R'.B.jL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).res ok' φ' :))))
        (z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok φ :))))


set_option maxHeartbeats 4000000 in
def RSide (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) : Prop :=
  RSideW z Wt' R' ∧ ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (R'.ωP i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.ωP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq (R'.vP i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.vP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (R'.HV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.HV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq (R'.thF i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.thF i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (R'.thG i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.thG i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq (R'.νV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.νV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (R'.fdV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.fdV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))))

end GlobalTheory.Mem.R3.Rw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicCoreTransportEnlargedCoefficientBase
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicCoreTransportEnlargedCoefficientBase
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

section EnlAux

variable {B B' : Base}

def enlEmb (hR : Set.range B.embLL ⊆ Set.range B'.embLL) : B.LL →+* B'.LL :=
  (RingEquiv.ofBijective B'.embLL.rangeRestrict
      ⟨fun x y h => B'.embLL.injective (congrArg Subtype.val h), B'.embLL.rangeRestrict_surjective⟩).symm.toRingHom.comp
    ((Subring.inclusion fun x hx => RingHom.mem_range.2 (hR (RingHom.mem_range.1 hx))).comp B.embLL.rangeRestrict)

theorem enlEmb_spec (hR : Set.range B.embLL ⊆ Set.range B'.embLL) (x : B.LL) :
    B'.embLL (enlEmb hR x) = B.embLL x := by
  have h := congrArg Subtype.val ((RingEquiv.ofBijective B'.embLL.rangeRestrict
      ⟨fun x y h => B'.embLL.injective (congrArg Subtype.val h), B'.embLL.rangeRestrict_surjective⟩).apply_symm_apply
    ((Subring.inclusion fun x hx => RingHom.mem_range.2 (hR (RingHom.mem_range.1 hx))) (B.embLL.rangeRestrict x)))
  exact h

def ksEquiv (hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom) : B.Ks ≃ₐ[ℚ] B'.Ks :=
  (B.Ks.equivMap B.embLL.toRatAlgHom).trans ((IntermediateField.equivOfEq (F := ℚ) (E := ℂ) (S := B.Ks.map B.embLL.toRatAlgHom) (T := B'.Ks.map B'.embLL.toRatAlgHom) hK.symm).trans (B'.Ks.equivMap B'.embLL.toRatAlgHom).symm)

theorem ksEquiv_spec (hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom) (x : B.Ks) : B'.embLL ((ksEquiv hK x : B'.Ks) : B'.LL) = B.embLL (x : B.LL) := by
  have h3 : (B'.Ks.equivMap B'.embLL.toRatAlgHom) (ksEquiv hK x) =
      IntermediateField.equivOfEq (F := ℚ) (E := ℂ) (S := B.Ks.map B.embLL.toRatAlgHom) (T := B'.Ks.map B'.embLL.toRatAlgHom) hK.symm (B.Ks.equivMap B.embLL.toRatAlgHom x) := by
    exact (B'.Ks.equivMap B'.embLL.toRatAlgHom).apply_symm_apply _
  have h4 := congrArg Subtype.val h3
  rw [IntermediateField.coe_equivMap_apply] at h4
  rw [RingHom.toRatAlgHom_apply] at h4
  rw [h4]
  change ((B.Ks.equivMap B.embLL.toRatAlgHom x : B.Ks.map B.embLL.toRatAlgHom) : ℂ) = _
  rw [IntermediateField.coe_equivMap_apply]
  rfl

def oEquiv (hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom) : B.O ≃+* B'.O := RingOfIntegers.mapRingEquiv (ksEquiv hK).toRingEquiv

theorem oEquiv_spec (hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom) (x : B.O) : B'.embLL (B'.OtoLL (oEquiv hK x)) = B.embLL (B.OtoLL x) := by
  have h := RingOfIntegers.mapRingEquiv_apply (ksEquiv hK).toRingEquiv x
  change B'.embLL (((oEquiv hK x : B'.Ks)) : B'.LL) = B.embLL ((x : B.Ks) : B.LL)
  rw [show (oEquiv hK x : B'.Ks) = ksEquiv hK (x : B.Ks) from h]
  exact ksEquiv_spec hK x

end EnlAux

section EnlAux2

variable {B B' : Base}

theorem enlEmb_Ks (hR : Set.range B.embLL ⊆ Set.range B'.embLL)
    (hK : B'.embLL '' (B'.Ks : Set B'.LL) = B.embLL '' (B.Ks : Set B.LL)) {x : B'.LL} (hx : x ∈ B'.Ks) :
    ∃ x₀ ∈ B.Ks, enlEmb hR x₀ = x := by
  obtain ⟨x₀, hx₀, he⟩ : B'.embLL x ∈ B.embLL '' (B.Ks : Set B.LL) := hK ▸ ⟨x, hx, rfl⟩
  exact ⟨x₀, hx₀, B'.embLL.injective (by rw [enlEmb_spec, he])⟩

theorem coefficientFieldEnlarge_mem_larger_fixedField (hR : Set.range B.embLL ⊆ Set.range B'.embLL)
    (hL : B.embLL '' (B.LL0 : Set B.LL) ⊆ B'.embLL '' (B'.LL0 : Set B'.LL)) {x : B.LL} (hx : x ∈ B.LL0) :
    enlEmb hR x ∈ B'.LL0 := by
  obtain ⟨x', hx', he⟩ : B.embLL x ∈ B'.embLL '' (B'.LL0 : Set B'.LL) := hL ⟨x, hx, rfl⟩
  have : enlEmb hR x = x' := B'.embLL.injective (by rw [enlEmb_spec, he])
  rw [this]
  exact hx'

end EnlAux2

section CdAux

abbrev withCd (D : D7) (c₀ : CDHaar) : D7 := { D with cd := c₀ }

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
  {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {r : ℕ}

theorem finVol_withCd (D : D7) (c₀ : CDHaar) (h : D.cd = c₀) (V : HSp D) :
    Formalism.L2.Pj.FinVol (D := withCd D c₀) V ↔ Formalism.L2.Pj.FinVol (D := D) V := by
  subst h
  rfl

theorem cuspL2_withCd (D : D7) (c₀ : CDHaar) (h : D.cd = c₀) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r)
    (σ : c.F →+* ℂ) (V : HSp D) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ) :
    Formalism.L2.Pj.CuspL2 (D := withCd D c₀) U σ V dict mu ↔ Formalism.L2.Pj.CuspL2 (D := D) U σ V dict mu := by
  subst h
  rfl

theorem peterssonDefinite_iff_of_eq_compactDualHaar (D : D7) (c₀ : CDHaar) (h : D.cd = c₀) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r)
    (σ : c.F →+* ℂ) (V : HSp D) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ)
    (h₁ : Formalism.L2.Pj.CuspL2 (D := withCd D c₀) U σ V dict mu) (h₂ : Formalism.L2.Pj.CuspL2 (D := D) U σ V dict mu) :
    Formalism.L2.Pj.L2DefiniteCuspForms (D := withCd D c₀) U σ V dict mu h₁ ↔ Formalism.L2.Pj.L2DefiniteCuspForms (D := D) U σ V dict mu h₂ := by
  subst h
  rfl

end CdAux

theorem exists_adelicCore_transport_enlargedCoefficientBase : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt),
    Enl0 B B' → HEq f' f → CoreP z →
    ∃ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) ∧
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) ∧
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) ∧
      HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota ∧
      Formalism.L2.Pj.LawsCore core'.toCore ∧ core'.Q.Canon ∧ (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) ∧ core'.pb = f'.P.pb := by
  intro B B' f f' T T' w w' Z Z' hX Wt z hE hf hC
  have hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom := SetLike.coe_injective hE.2.1
  obtain ⟨h1, hKs, hLL0, hR⟩ := hE
  have hι := enlEmb_spec hR
  have hι0 := fun x (hx : x ∈ B.LL0) => coefficientFieldEnlarge_mem_larger_fixedField hR hLL0 hx
  have hιK := fun x (hx : x ∈ B'.Ks) => enlEmb_Ks hR hKs hx
  have hO := oEquiv_spec hK
  rcases B' with ⟨P'⟩
  change P' = B.toPre at h1
  subst h1
  have hff := eq_of_heq hf
  subst hff
  obtain ⟨hL, hCa, hDim, hpb⟩ := hC
  have hcd : (w'.st Z').toD7.cd = (w.st Z).toD7.cd := Tr.cd_eq _ _
  let g : z.core.Q.c.F →+* _ := (enlEmb hR).comp ((algebraMap (↥z.core.Q.c.F) (w.st Z).toD7.what₂.LL) : z.core.Q.c.F →+* B.LL)
  let Q' : Formalism.L2.Pj.Par (w'.st Z').toD7 :=
    { H := (z.core.Q.H), l := (z.core.Q.l), c := (z.core.Q.c), Dw := (z.core.Q.Dw), Xo := (z.core.Q.Xo),
      eO := (by with_unfolding_all exact ((z.core.Q.eO.trans (oEquiv hK)) :)) }
  let core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7 :=
    { toCore :=
        { Q := Q', U := (z.core.U), V := (z.core.V), dict := (z.core.dict), mu := (z.core.mu),
          Kf := (z.core.Kf), pb := (z.core.pb) }
      cE := (z.core.cE), chiW := (z.core.chiW), x₀ := (z.core.x₀), iota := (z.core.iota) }
  refine ⟨core', (g.toAlgebra), ?_⟩

  refine ⟨fun y => (hι _).trans (z.alg_eq y), fun y => hι0 _ (z.fieldValues_mem_fixedField y), fun x hx => ?_,
    (HEq.refl z.core.Q.H), (HEq.refl z.core.Q.l), (HEq.refl z.core.Q.c), (HEq.refl z.core.Q.Dw),
    (HEq.refl z.core.Q.Xo), (HEq.refl z.core.U), (HEq.refl z.core.V), (HEq.refl z.core.dict),
    (HEq.refl z.core.mu), (HEq.refl z.core.Kf), (HEq.refl z.core.cE), (HEq.refl z.core.chiW),
    (HEq.refl z.core.x₀), (HEq.refl z.core.iota), ?_, (hCa), (hDim), (hpb)⟩
  · obtain ⟨x₀, hx₀, he⟩ := hιK x hx
    obtain ⟨y, hy⟩ := z.Ks_le x₀ hx₀
    exact ⟨y, (congrArg (enlEmb hR) hy).trans he⟩
  · have hPF : Q'.PinField := fun x => (hO (z.core.Q.eO x)).trans (hL.pins.2.2.1 x)
    exact
      { pins := ⟨(hL.pins.left), (hL.pins.right.left), hPF, (hL.pins.right.right.right)⟩
        half := (hL.half)
        evalWD := (hL.evalWD)
        unf := (hL.unf)
        unTest := (hL.unTest)
        chiTriv := (hL.chiTriv)
        dictU := (hL.dictU)
        spaceW := (hL.spaceW)
        levelK := (hL.levelK)
        xiAbs := (hL.xiAbs)
        muUnit := (hL.muUnit)
        muCont := (hL.muCont)
        finVol := fun j hj σ hσ => (finVol_withCd (w'.st Z').toD7 (w.st Z).toD7.cd hcd _).1 ((hL.finVol j hj σ hσ))
        cuspFD := (hL.cuspFD)
        supDef := (hL.supDef)
        cuspidalL2Subspace := fun j hj σ hσ => (cuspL2_withCd (w'.st Z').toD7 (w.st Z).toD7.cd hcd _ _ _ _ _).1 ((hL.cuspidalL2Subspace j hj σ hσ))
        l2Def := fun j hj σ hσ =>
          (peterssonDefinite_iff_of_eq_compactDualHaar (w'.st Z').toD7 (w.st Z).toD7.cd hcd _ _ _ _ _ ((hL.cuspidalL2Subspace j hj σ hσ)) _).1 ((hL.l2Def j hj σ hσ))
        unitIndep := (hL.unitIndep)
        ptNe := (hL.ptNe)
        cuspMul := (hL.cuspMul)
        latZ := (hL.latZ)
        cuNe := (hL.cuNe)
        expo := (hL.expo) }

end GlobalTheory.Mem.R3.Rw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicCoreTransportEnlargedCoefficientBaseStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicCore_transport_enlargedCoefficientBase_alt : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt),
    Enl0 B B' → HEq f' f → CoreP z →
    ∃ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) ∧
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) ∧
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) ∧
      HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota ∧
      Formalism.L2.Pj.LawsCore core'.toCore ∧ core'.Q.Canon ∧ (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) ∧ core'.pb = f'.P.pb := by
  first | exact @GlobalTheory.Mem.R3.Rw.exists_adelicCore_transport_enlargedCoefficientBase | exact GlobalTheory.Mem.R3.Rw.exists_adelicCore_transport_enlargedCoefficientBase | (intros; apply GlobalTheory.Mem.R3.Rw.exists_adelicCore_transport_enlargedCoefficientBase <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.MonPeriods

theorem exists_isMonomial_levelOne : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {W : Type}
    [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (t : SAB H (Sp W))
    (P : PELUnif (maximalIdeal W) t), ∃ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] := by
  intro E _ _ _ H W _ _ _ hW ϖ hϖ t P
  obtain ⟨hdvr, hcomp, hchar⟩ := hW
  haveI := hdvr
  haveI := hcomp
  haveI := hchar
  letI := H.starRing
  choose Q hQ using QForm.exists_QVal hϖ P.D
  have hQ' : QForm.IsQ P.D.toPre ϖ Q := hQ
  have hex : ∀ χ, ∃ r, PsiCoord P.D.toPre χ r := fun χ =>
    ((GlobalTheory.PsiCoordLocal.main W P.D inferInstance χ).1).imp fun _ h => h.1
  have hv : ∀ χ, HasVal ϖ (algebraMap W (FractionRing W) (hex χ).choose) (Q χ) := fun χ =>
    GlobalTheory.ValForm.hasVal_coord (hQ χ) (hex χ).choose_spec
  have h0 : ∀ a, 0 ≤ Q a := fun a => by
    by_cases ha : a = 0
    · rw [ha, QForm.Q_zero hϖ P.D hQ']
    · exact zero_le_one.trans (QForm.Q_pos hϖ P.D hQ' ha)
  have hbal : ∀ (x : 𝓞 E) a b, QForm.bOf P.D.toPre Q (x • a) b = QForm.bOf P.D.toPre Q a (H.bar x • b) := by
    intro x a b
    obtain ⟨u, hu⟩ := GlobalTheory.PeriodBalance.coord_balance P.D.toPre P.oD x a b (hex (x • a + b)).choose_spec
      (hex (x • a)).choose_spec (hex b).choose_spec (hex (a + H.bar x • b)).choose_spec (hex a).choose_spec
      (hex (H.bar x • b)).choose_spec
    have h1 := hasVal_mul_unit (GlobalTheory.ValForm.hasVal_mul hϖ (GlobalTheory.ValForm.hasVal_mul hϖ (hv (x • a + b)) (hv a))
      (hv (H.bar x • b))) u
    have h2 := GlobalTheory.ValForm.hasVal_mul hϖ (GlobalTheory.ValForm.hasVal_mul hϖ (hv (a + H.bar x • b)) (hv (x • a))) (hv b)
    rw [← map_mul, _root_.mul_comm, hu] at h1
    have := hasVal_unique hϖ h1 h2
    simp only [QForm.bOf]
    linarith
  let be : LinearMap.BilinForm ℤ P.D.toPre.X :=
    LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ P.D hQ' a b)
      (fun a a' b => by simp only [map_add (f := _), AddMonoidHom.add_apply])
      (fun c a b => by simp only [map_zsmul, AddMonoidHom.smul_apply, smul_eq_mul])
      (fun a b b' => by simp only [map_add (f := _)])
      (fun c a b => by simp only [map_zsmul, smul_eq_mul])
  have hbe : ∀ a b, be a b = QForm.bOf P.D.toPre Q a b := fun _ _ => rfl
  refine ⟨be, ⟨fun y z => ?_, fun a y z => ?_, fun y z => by simp⟩, fun y => ?_⟩
  · rw [hbe, hbe, QForm.bOf_comm]
  · rw [hbe, hbe]
    exact hbal a y z
  · obtain ⟨u, hu⟩ := hv y
    set r := (hex y).choose with hr
    have hn : (((Q y).toNat : ℕ) : ℤ) = Q y := Int.toNat_of_nonneg (h0 y)
    have e : r = ↑u * ϖ ^ (Q y).toNat := by
      apply IsFractionRing.injective W (FractionRing W)
      rw [hu, map_mul, map_pow, _root_.mul_comm, ← zpow_natCast, hn]
    refine ⟨u, fun _ => (Q y).toNat, fun i => ?_, ?_⟩
    · fin_cases i
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [hbe, ← QForm.two_Q_eq hϖ P.D hQ', hn]
    · have hc : PsiCoord P.D.toPre y r := (hex y).choose_spec
      rw [e] at hc
      simpa using hc

end GlobalTheory.MonPeriods
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExponentialModelFiberOfUniformisationExp
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExponentialModelFiberOfUniformisationExp
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom isDerivAt0_unique)
open GlobalTheory.TrueCx.TorFrHolo (isDerivAt0_of_cart isHolTo_lift)

section Push

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {g : ℕ}
  {ty : Fin g → (E →+* ℂ)} {σ₀ : KA l →+* ℂ} (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n)
  (P : (Fu.Di i).La →+ (Fin g → ℂ))

theorem isHolTo_ex_fixed (hP : IsPeriod (Fu.Di i) ty P) : IsHolTo Set.univ fun z => (Fu.ex i P z).left := by
  have h1 := (Fu.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  exact GlobalTheory.LocLift.isHolTo_comp h1 isOpen_univ (β := fun z => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
    fun _ _ => ⟨trivial, trivial⟩

theorem isHolTo_liftEx (hP : IsPeriod (Fu.Di i) ty P)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) :
    IsHolTo Set.univ fun z => liftEx Z Fu y i P hu z ≫ Z.m.φ := by
  have h1 := (Fu.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  have h2 := isHolTo_lift Z.m0.toSABMap.cart.1 isOpen_univ (fun _ z => (Fu.ex i P z).left) (fun _ => y) h1
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.ThetaHol.isHolTo_const y) (fun _ z => by rw [Over.w (Fu.ex i P z), ← hu]; rfl)
  have h3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 Z.m.φ
  exact GlobalTheory.LocLift.isHolTo_comp h3 isOpen_univ (β := fun z => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
    fun _ _ => ⟨trivial, trivial⟩

theorem isDerivAt0_liftEx (hP : IsPeriod (Fu.Di i) ty P)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left}
    (hv : v ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y)
    (hd : IsDerivAt0 (fun z => (Fu.ex i P z).left) w (v ≫ Z.m0.toSABMap.φ)) :
    IsDerivAt0 (liftEx Z Fu y i P hu) w v :=
  isDerivAt0_of_cart Z.m0.toSABMap.cart.1 y (fun z => liftEx_snd Z Fu y i P hu z)
    (by simpa only [liftEx_fst] using isHolTo_ex_fixed Fu i P hP) hv
    (by simpa only [liftEx_fst] using hd)

theorem isDerivAt0_ex_of_push (hP : IsPeriod (Fu.Di i) ty P)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left}
    (hv : v ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y)
    (hd : IsDerivAt0 (fun z => liftEx Z Fu y i P hu z ≫ Z.m.φ) w (v ≫ Z.m.φ)) :
    IsDerivAt0 (fun z => (Fu.ex i P z).left) w (v ≫ Z.m0.toSABMap.φ) := by
  have h := isDerivAt0_comp_hom (isDerivAt0_of_cart Z.m.cart.1 y (fun z => liftEx_snd Z Fu y i P hu z)
    (isHolTo_liftEx Z Fu y i P hP hu) hv hd) Z.m0.toSABMap.φ
  simpa only [liftEx_fst] using h

end Push

theorem isExpAt_pushEx : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → IsExpAt Z.t p (pushEx Z Fu y i P p hu hp) := by
  intro E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hu hp hP
  subst hp
  obtain ⟨t1, t2, t3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo σ₀ g ty Fu i P hP
  refine ⟨fun a b => ?_, fun w => ?_, fun v hv => ?_⟩
  · let L : (Fin g → ℂ) → (Over.mk y ⟶ Z.oF.t.G) := fun z =>
      Over.homMk (liftEx Z Fu y i P hu z) (liftEx_snd Z Fu y i P hu z)
    have hL : (L (a + b)).left = (L a * L b).left := by
      refine Z.m0.toSABMap.cart.1.hom_ext ?_ ?_
      · have e1 := Z.m0.toSABMap.cart.2 (Over.mk y) (L a) (L b) (pushPt Z.m0.toSABMap.cart.1.w (L a))
          (pushPt Z.m0.toSABMap.cart.1.w (L b)) rfl rfl
        refine Eq.trans ?_ e1
        refine (liftEx_fst Z Fu y i P hu (a + b)).trans ?_
        rw [Fu.ex_add i P hP]
        exact mul_left_congr hu _ _ _ _ (liftEx_fst Z Fu y i P hu a).symm (liftEx_fst Z Fu y i P hu b).symm
      · rw [Over.w, Over.w]
    refine Over.OverMorphism.ext ?_
    have e2 := Z.m.cart.2 (Over.mk y) (L a) (L b) (pushEx Z Fu y i P _ hu rfl a) (pushEx Z Fu y i P _ hu rfl b) rfl rfl
    refine Eq.trans ?_ e2.symm
    exact congrArg (· ≫ Z.m.φ) hL
  · obtain ⟨v, hv, -⟩ := t2 w
    have ht := t1 w v hv
    obtain ⟨v', k1, rfl⟩ := GlobalTheory.ShFam.OpenReg.exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
      (by rw [ht.1, hu, Category.assoc])
    refine ⟨v' ≫ Z.m.φ, ⟨(GlobalTheory.ShFam.OpenReg.tan_iff Z.m rfl k1).2
      ((GlobalTheory.ShFam.OpenReg.tan_iff Z.m0.toSABMap hu.symm k1).1 ht),
      isDerivAt0_comp_hom (isDerivAt0_liftEx Z Fu y i P hP hu k1 hv) Z.m.φ⟩, fun v₂ hv₂ => ?_⟩
    exact isDerivAt0_unique hv₂.2 (isDerivAt0_comp_hom (isDerivAt0_liftEx Z Fu y i P hP hu k1 hv) Z.m.φ)
  · obtain ⟨v', k1, rfl⟩ := GlobalTheory.ShFam.OpenReg.exists_lift Z.m (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
      (by rw [hv.1, Category.assoc])
    have h1 := (GlobalTheory.ShFam.OpenReg.tan_iff Z.m rfl k1).1 hv
    have h2 := (GlobalTheory.ShFam.OpenReg.tan_iff Z.m0.toSABMap hu.symm k1).2 h1
    obtain ⟨w, hw, hw'⟩ := t3 _ h2
    exact ⟨w, isDerivAt0_comp_hom (isDerivAt0_liftEx Z Fu y i P hP hu k1 hw) Z.m.φ,
      fun w' h' => hw' w' (isDerivAt0_ex_of_push Z Fu y i P hP hu k1 h')⟩

end GlobalTheory.ShFam.Hor.LogCh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExponentialModelFiberOfUniformisationExpStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isExponential_modelFiber_of_uniformisationExp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → IsExpAt Z.t p (pushEx Z Fu y i P p hu hp) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.isExpAt_pushEx | exact GlobalTheory.ShFam.Hor.LogCh.isExpAt_pushEx | (intros; apply GlobalTheory.ShFam.Hor.LogCh.isExpAt_pushEx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFlagBaseHolds
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht
open MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.Cht.FlagBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem comp_listProd {B : Scheme.{0}} {G : Over B} [GrpObj G] {X Y : Over B} (e : X ⟶ Y) (L : List (Y ⟶ G)) :
    e ≫ L.prod = (L.map (e ≫ ·)).prod := by
  induction L with
  | nil => exact MonObj.comp_one e
  | cons a L ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]

theorem isCombAtG_bc {X : Scheme.{0}} (t : SAB H X) {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S')
    {x : Sp S ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {a : Fin m → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) :
    IsCombAtG t (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ v j) (fun j => ψ (a j)) (spMap (dualMap ψ) ≫ w) := by
  obtain ⟨u, hu, hw⟩ := h
  have he : spMap (dualMap ψ) ≫ (tEpsG x).hom = (tEpsG (spMap ψ ≫ x)).hom := by
    show spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap ψ ≫ x
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    apply RingHom.ext
    intro r
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let e : tEpsG (spMap ψ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap ψ)) he
  refine ⟨fun i => e ≫ u i, fun i => ?_, ?_⟩
  · show spMap (dualMap ψ) ≫ (u i).left = spMap (epsMul (ψ (a i))) ≫ spMap (dualMap ψ) ≫ v i
    rw [hu i, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    apply RingHom.ext
    intro r
    ext <;> simp [dualMap, epsMul, _root_.mul_comm]
  · have hl : (List.ofFn fun i => e ≫ u i) = (List.ofFn u).map (e ≫ ·) := by
      rw [List.map_ofFn]
      rfl
    rw [hl, ← comp_listProd, Over.comp_left, hw]
    rfl

end GlobalTheory.LocM.Cht.FlagBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsCoverModels
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TorRef


open IsLocalRing in
theorem isEtaleCompletion_comp_bij {B A R : Type} [CommRing B] [IsLocalRing B] [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (e : B →+* A) (he : Function.Bijective e) (φ : A →+* R)
    (h : Toroidal.IsEtaleCompletion φ) : Toroidal.IsEtaleCompletion (φ.comp e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨RingHom.Flat.comp (RingHom.Flat.of_bijective he) h1, ?_, ?_⟩
  · rw [← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]
    exact h2
  · rw [← RingHom.comp_assoc]
    exact RingHom.Finite.comp h3 (RingHom.Finite.of_surjective e he.2)

end GlobalTheory.TorRef

namespace GlobalTheory.TorRef

end GlobalTheory.TorRef
end
