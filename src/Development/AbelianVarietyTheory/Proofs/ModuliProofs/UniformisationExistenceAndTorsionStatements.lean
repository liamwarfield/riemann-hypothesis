module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataUniformisationOfTorsionCou
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBaseModelSemiAbelian
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyFromVeryDensePoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationExistenceAndTorsionStatements
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThmUOfAllSet
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ZH

theorem thmU_of_allSet : Laws → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → GlobalTheory.UU.AllSet (fun {V} _ _ _ {A} {G} _ _ s => ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), U.gen = s.gen) → ThmUSt := by
  intro hL hext hall V _ _ _ _ hV A G _ _ hG hE hS gen hgen
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_uniformisationData_of_semiAbelianSymmetry hL hext V hV A G hG hE hS gen hgen
  obtain ⟨D, U, hU⟩ := hall V A G s
  exact ⟨D, U, hU.trans hs⟩
end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationExistenceAndTorsionStatements
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZH

theorem thmU_and_uTors : GlobalTheory.ZH.ThmUSt ∧ GlobalTheory.ZH.UTorsSt := by
  obtain ⟨L, L2, L3, L4, L5, -⟩ := GlobalTheory.T.all_six_abelian_scheme_laws_hold
  refine ⟨GlobalTheory.ZH.thmU_of_allSet L GlobalTheory.homExtension_semiAbelian_dvr (by
    have h := GlobalTheory.T.exists_degenerationData_uniformisation_of_torsionCount (GlobalTheory.T.card_torsion_points_abelianVariety L.globalFns L.rigidity) L L2
    intro V _ _ _ A G _ _ s
    obtain ⟨D, U, -, hg, -⟩ := h V A G s
    exact ⟨D, U, hg⟩), GlobalTheory.T.uniformisation_torsion_eq_of_laws L L2 L3 L4 L5⟩

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationExistenceAndTorsionStatementsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationExistence_and_torsion_statements : GlobalTheory.ZH.ThmUSt ∧ GlobalTheory.ZH.UTorsSt := by
  first | exact @GlobalTheory.ZH.thmU_and_uTors | exact GlobalTheory.ZH.thmU_and_uTors | (intros; apply GlobalTheory.ZH.thmU_and_uTors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalModelSystemAmpleFramesFullLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelRaises
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.LocalModelExists

theorem exists_model_raises : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (b : RZ H (n * l₀.M) 1 →+* O), 0 < n → l₀.Dvd l → IsDedFrac β → IsInc (RZ H (n * l₀.M) 1).subtype (c.F.val.toRingHom.comp β) b → ∃ Y : Model (Xo l) c β, Raises B Y := by
  intro L1 L2 L3 E _ _ _ H D Xo n N T hN l₀ l B c O _ β b hn hd hβ hb
  obtain ⟨o, ⟨m0⟩⟩ := GlobalTheory.obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ _ (Xo l).s
    (pullback.fst (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ (Xo l).s)
    (pullback.fst (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) rfl rfl
    (by simp [spMap]) (Xo l).univ
  obtain ⟨k, r, ν, hr, hk, hlev, hfin, -, -⟩ :=
    GlobalTheory.LevelMapField.exists_levelMap L1 L2 L3 E H D Xo hN l₀ l c o m0 hd
  have hpos : 0 < n * l₀.M := Nat.mul_pos hn (by have := l₀.three_le; omega)
  have hB : IsDedFrac B.β := by
    have aux : ∀ a : ℕ, l₀.A = a → a = 1 → ∀ β₀ : RZ H (n * l₀.M) a →+* KA l₀,
        IsInc (RZ H (n * l₀.M) a).subtype (KA l₀).val.toRingHom β₀ → IsDedFrac β₀ := by
      intro a ha h1
      subst ha
      exact (GlobalTheory.T.cmModelCoefficientSubring_dedekind_compatible_embedding E H l₀ (n * l₀.M) 0 hpos (by simp [h1])).2.2
    exact aux 1 B.A_one rfl B.β B.β_inc
  have hcomp : β.comp b = k.comp B.β := by
    refine RingHom.ext fun x => Subtype.ext ?_
    exact (hb x).trans ((hk (B.β x)).trans (B.β_inc x)).symm
  have hsm : Smooth (pullback.snd (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
    have := (Xo l).smooth
    have : Smooth (Xo l).s := SmoothOfRelativeDimension.smooth D.dim _
    infer_instance
  have hnorm0 := (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm).2.1
  have hnorm : Geo.Tor.IsNormalScheme _ := fun x => ⟨hnorm0.1 x, hnorm0.2 x⟩
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_normal_model_above_finite_cover E H _ _ _ (Xo l₀).s (Xo l₀).univ.t B.β _ _ _
    (pullback.snd (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) o.t β B.C b k r hr ν hB hβ hcomp
    hnorm hfin
  exact ⟨⟨C.X, C.s, C.normal, C.proj, C.flat, C.jQ, C.jQ_over, C.jQ_open, C.jQ_dense, C.t, o, m0, C.m, C.ab_gen⟩,
    b, r, ν, hb, hlev, hC⟩

end GlobalTheory.LocalModelExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalModelSystemAmpleFramesFullLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.SystemAmple

theorem exists_system_ampFrames : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → Out.Laws3 → TopAmpExists → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∃ S : System Xo, ∀ i, ∃ k : ℕ, Nonempty (GlobalTheory.LN.AmpFrames (S.T i).t.G (S.T i).t.PP.L ((S.n i ^ k) ^ 2)) := by
  intro hx h1 h2 h3 htop E _ _ _ H D Xo hpq hN
  classical
  obtain ⟨⟨n₀, n₁, a₀, a₁, hne⟩, -⟩ := GlobalTheory.Models.exists_two_auxiliary_inert_odd_primes_coprime_level E H
  let n : Bool → ℕ := fun i => cond i n₁ n₀
  have aux : ∀ i, AuxiliaryInertOddPrime H (n i) := fun i => by cases i <;> assumption
  choose J k T hJ hamp using fun i => htop E H D hpq Xo (n i) (aux i)
  let B : ∀ i (l₀ : Level H), l₀.A = 1 → BaseModel (T i) l₀ := fun i l₀ h =>
    (GlobalTheory.T.exists_base_model_semiAbelian hx h1 h2 h3 E H D Xo hpq hN (n i) (J i) (T i) l₀ (aux i) (hJ i) h).some
  let ch : ℕ → Bool := fun p => decide (n₀ = p)
  have ch_ne : ∀ p, n (ch p) ≠ p := by
    intro p
    by_cases h : n₀ = p
    · have : ch p = true := by simp [ch, h]
      rw [this]
      exact fun h' => hne (h.trans h'.symm)
    · have : ch p = false := by simp [ch, h]
      rw [this]
      exact h
  have key : ∀ (p : ℕ) (W : ValuationSubring ℂ) (_ : p.Prime) (_ : (p : ℂ) ∈ W.nonunits) (i : Idx H p),
      ∃ Y : Model (Xo i.l) i.c (i.c.V W).subtype, ∃ (l₀ : Level H) (h : IsPrimeToPart l₀ i.l p),
        Raises (B (ch p) l₀ h.1) Y := by
    intro p W hp hW i
    obtain ⟨hex, hsp, -⟩ := GlobalTheory.Models.primeToPart_spec E H p hp
    obtain ⟨l₀, h⟩ := hex i.l i.good
    obtain ⟨hdvd, hcop, -⟩ := hsp i.l l₀ h
    obtain ⟨hded, -, hb⟩ := (GlobalTheory.CoeffRings.coeff_isDedFrac E H i.l i.c).2.2.2 p W hp hW
    have hnp : (n (ch p)).Coprime p := (Nat.coprime_primes (aux _).1 hp).2 (ch_ne p)
    have hz : zeta 1 ∈ i.c.F := by
      have : zeta 1 = 1 := by simp [zeta]
      rw [this]; exact one_mem _
    obtain ⟨b, hbi⟩ := hb (n (ch p) * l₀.M) 1 (Nat.Coprime.mul_left hnp hcop) one_pos hz
    obtain ⟨Y, hY⟩ := GlobalTheory.LocalModelExists.exists_model_raises h1 h2 h3 E H D Xo _ _ (T (ch p)) hN l₀ i.l
      (B (ch p) l₀ h.1) i.c _ (i.c.V W).subtype b (aux _).1.pos hdvd hded hbi
    exact ⟨Y, l₀, h, hY⟩
  choose Y hY using key
  exact ⟨⟨n, J, aux, hJ, T, B, ch, ch_ne, Y, hY⟩, fun i => ⟨k i, hamp i⟩⟩

end GlobalTheory.SystemAmple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalModelSystemAmpleFramesFullLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localModelSystem_ampleFrames_fullLevel : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → Out.Laws3 → TopAmpExists → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∃ S : System Xo, ∀ i, ∃ k : ℕ, Nonempty (GlobalTheory.LN.AmpFrames (S.T i).t.G (S.T i).t.PP.L ((S.n i ^ k) ^ 2)) := by
  first | exact @GlobalTheory.SystemAmple.exists_system_ampFrames | exact GlobalTheory.SystemAmple.exists_system_ampFrames | (intros; apply GlobalTheory.SystemAmple.exists_system_ampFrames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DescendToThetaConstantField
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DescendToThetaConstantField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem descend_to_theta_field : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (K₀ K : Type) [Field K₀] [Field K] [IsAlgClosed K] (β : o →+* K₀) (e : K₀ →+* K) (s : Sp K ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s) (v : Ix g ((n ^ j) ^ 2) → K₀), s = spMap e ≫ spMap β → t.Shape Mat κ → t.Prim w w' → t.HasTh (𝟙 _) (fun a => e (v a)) → ∃ t₀ : TObj g ((n ^ j) ^ 2) J b (spMap β), TMap t t₀ (spMap e) ∧ t₀.Shape Mat κ ∧ t₀.Prim w w' ∧ t₀.HasTh (𝟙 _) v := by
  intro hL hL2 g J _ Mat κ n w w' hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.exists_theta_family_from_very_dense_points hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b K₀ K _ _ _ β e s t v hs hsh hpr hth => ?_⟩
  subst hs

  have hdense : VeryDense (objPrimes b Mat κ β v) := by
    intro q f hq hf
    have hq0 : q = ⊥ := (Ideal.eq_bot_or_top q).resolve_right hq.ne_top
    have hker : RingHom.ker e = q := by
      rw [hq0]; exact (RingHom.injective_iff_ker_eq_bot e).mp e.injective
    exact ⟨q, ⟨K, inferInstance, inferInstance, e, t, hker, hsh, hth⟩, hq, le_rfl, hf⟩
  obtain ⟨t₀, hth₀, hu⟩ := hj₀ j hj o b K₀ β v hdense

  have hmap : TMap t t₀ (spMap e) := hu K e t hsh hth
  obtain ⟨-, -, hdesc⟩ := GlobalTheory.shape_prim_pull_and_descend o g ((n ^ j) ^ 2) J b Mat κ w w' _ _ _ _ _ t₀ t hmap
  obtain ⟨hS, hP⟩ := hdesc K₀ rfl inferInstance inferInstance
  exact ⟨t₀, hmap, hS hsh, hP inferInstance hpr, hth₀⟩

end GlobalTheory.ZM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DescendToThetaConstantFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descend_to_thetaConstant_field : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (K₀ K : Type) [Field K₀] [Field K] [IsAlgClosed K] (β : o →+* K₀) (e : K₀ →+* K) (s : Sp K ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s) (v : Ix g ((n ^ j) ^ 2) → K₀), s = spMap e ≫ spMap β → t.Shape Mat κ → t.Prim w w' → t.HasTh (𝟙 _) (fun a => e (v a)) → ∃ t₀ : TObj g ((n ^ j) ^ 2) J b (spMap β), TMap t t₀ (spMap e) ∧ t₀.Shape Mat κ ∧ t₀.Prim w w' ∧ t₀.HasTh (𝟙 _) v := by
  first | exact @GlobalTheory.ZM.descend_to_theta_field | exact GlobalTheory.ZM.descend_to_theta_field | (intros; apply GlobalTheory.ZM.descend_to_theta_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientClassifyingMapIsogenyUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientClassifyingMapIsogenyUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory

theorem heckeQuot_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o o₁ o₂ : Ob D l s) (ψ₁ : o.t.G ⟶ o₁.t.G) (ψ₂ : o.t.G ⟶ o₂.t.G) (K : Set o.t.G.left) (f₁ f₂ : S ⟶ Xo.X) (n₁ : ObjMap o₁ Xo.univ f₁) (n₂ : ObjMap o₂ Xo.univ f₂), admitted l 𝔓 p → HeckeSet D o.t 𝔓 p i K → f₁ ≫ Xo.s = s → f₂ ≫ Xo.s = s → IsIsog o o₁ p ψ₁ → IsIsog o o₂ p ψ₂ → KerSet ψ₁ K → KerSet ψ₂ K → f₁ = f₂ ∧ ψ₁.left ≫ n₁.toSABMap.φ = ψ₂.left ≫ n₂.toSABMap.φ := by
  intro E _ _ _ H D l Xo P p i S hS s o o₁ o₂ ψ₁ ψ₂ K f₁ f₂ n₁ n₂ hA hK h₁ h₂ i₁ i₂ k₁ k₂
  obtain ⟨-, -, hp, hpP, hM⟩ := hA
  have hnat : ∀ {T : Over S} (x : T ⟶ o.t.G) (n : ℕ), x ≫ o.t.act.act (n : 𝓞 E) = x ^ n := by
    intro T x n
    induction n with
    | zero =>
      have h := o.t.act.add 0 0
      rw [add_zero] at h
      have h0 : o.t.act.act 0 = 1 := by simpa using h
      rw [Nat.cast_zero, pow_zero, h0, MonObj.comp_one]
    | succ n ih => rw [Nat.cast_succ, o.t.act.add, MonObj.comp_mul, ih, o.t.act.one, Category.comp_id, pow_succ]
  have hkill : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ o.t.G),
      Set.range z.left ⊆ K → z ^ p ^ 2 = 1 := by
    intro k _ _ x z hz
    obtain ⟨C, hC, hH⟩ := hK k x
    have hzC := hH.2.2.1 ((hC z).2 hz)
    have hbar : (p : 𝓞 E) ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
      rwa [map_natCast] at this
    have h := hzC ((p ^ 2 : ℕ) : 𝓞 E) (by
      rw [Nat.cast_pow, pow_two]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hbar)
    rwa [hnat] at h
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_iso_quotients_same_kernel_reduced_base E H D l p S s o o₁ o₂ ψ₁ ψ₂ K hp hM i₁ i₂ k₁ k₂ hkill
  obtain ⟨m', hm'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2
    f₂ (𝟙 S) n₂).1 m
  have hf : f₁ = 𝟙 S ≫ f₂ :=
    (Xo.rep S s hS o₁).unique ⟨h₁, ⟨n₁⟩⟩ ⟨by rw [Category.id_comp, h₂], ⟨m'⟩⟩
  refine ⟨by rw [hf, Category.id_comp], ?_⟩
  subst hf
  have e := GlobalTheory.obj_rigid_closed GlobalTheory.firstFiveLaws.1 E H D l _ _ _ _ _ _ _ _ Xo.univ o₁ _ (Or.inl hS)
    n₁.toSABMap m'.toSABMap (fun a => ⟨_, n₁.eta a, m'.eta a⟩)
  rw [e, hm', ← Category.assoc, hm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientClassifyingMapIsogenyUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeQuotient_classifyingMap_isogeny_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o o₁ o₂ : Ob D l s) (ψ₁ : o.t.G ⟶ o₁.t.G) (ψ₂ : o.t.G ⟶ o₂.t.G) (K : Set o.t.G.left) (f₁ f₂ : S ⟶ Xo.X) (n₁ : ObjMap o₁ Xo.univ f₁) (n₂ : ObjMap o₂ Xo.univ f₂), admitted l 𝔓 p → HeckeSet D o.t 𝔓 p i K → f₁ ≫ Xo.s = s → f₂ ≫ Xo.s = s → IsIsog o o₁ p ψ₁ → IsIsog o o₂ p ψ₂ → KerSet ψ₁ K → KerSet ψ₂ K → f₁ = f₂ ∧ ψ₁.left ≫ n₁.toSABMap.φ = ψ₂.left ≫ n₂.toSABMap.φ := by
  first | exact @GlobalTheory.heckeQuot_unique | exact GlobalTheory.heckeQuot_unique | (intros; apply GlobalTheory.heckeQuot_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointDeterminesShapeComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointDeterminesShapeComplex
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem isThetaPt_unit_mul {S : Scheme.{0}} (P : Out.PolAV S) (k : ℕ) {T : Over S} {I : Type}
    (x : I → (T ⟶ P.A)) (v : I → Γ(T.left, ⊤)) (c : Γ(T.left, ⊤)) (hc : IsUnit c)
    (H : Out.IsThetaPt P k x v) : Out.IsThetaPt P k x (fun i => c * v i) := by
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3 p
  obtain ⟨c', hc'⟩ := hc.map V.ι.appTop.hom
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, (c' * (show Γ(V.toScheme, ⊤)ˣ from u) : Γ(V.toScheme, ⊤)ˣ), a1, a2, a3, a4, a5, a6, a7, fun i => ?_⟩
  have aux : ∀ (a : Γ(T.left, ⊤)) (u₀ : Γ(V.toScheme, ⊤)ˣ) (w₀ : Γ(V.toScheme, ⊤)),
      V.ι.appTop.hom a = u₀.val * w₀ → V.ι.appTop.hom (c * a) = (c' * u₀).val * w₀ := by
    intro a u₀ w₀ h
    rw [map_mul, h, Units.val_mul, hc', _root_.mul_assoc]
  exact aux (v i) u (w i) (a8 i)

theorem TObj.HasTh.unit_smul {o : Type} [CommRing o] {S : Scheme.{0}} {g N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {R : Type} [CommRing R]
    {x : Sp R ⟶ S} {v : Ix g (N' ^ 2) → R} (H : t.HasTh x v) {c : R} (hc : IsUnit c) :
    t.HasTh x (c • v) := by
  have h := isThetaPt_unit_mul t.pol N' (T := Over.mk x) _ _ _
    (hc.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) H
  unfold TObj.HasTh
  convert h using 2 with a
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c (v a)

theorem tmap_of_hasTh_complex : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (t t' : TObj g ((n ^ j) ^ 2) J b (spMap em)) (v : Ix g ((n ^ j) ^ 2) → ℂ) (c : ℂ), c ≠ 0 → t.Shape Mat κ → t'.Shape Mat κ → t.HasTh (𝟙 _) v → t'.HasTh (𝟙 _) (c • v) → TMap t' t (𝟙 _) := by
  intro hL hL2 g J _ Mat κ n hn hodd
  obtain ⟨j₀, H⟩ := GlobalTheory.T.exists_theta_family_from_very_dense_points hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b em t t' v c hc hs hs' hv hv' => ?_⟩
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id (CommRingCat.of ℂ)
  have hv'' : t'.HasTh (𝟙 _) v := by
    have h := hv'.unit_smul (IsUnit.mk0 c⁻¹ (inv_ne_zero hc))
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
  have key : ∀ s : Sp ℂ ⟶ Sp o, s = spMap (RingHom.id ℂ) ≫ spMap em →
      ∀ t t' : TObj g ((n ^ j) ^ 2) J b s, t.Shape Mat κ → t'.Shape Mat κ →
        t.HasTh (𝟙 _) v → t'.HasTh (𝟙 _) v → TMap t' t (𝟙 _) := by
    intro s hs t t' h1 h1' h2 h2'
    subst hs
    have hvd : VeryDense (objPrimes b Mat κ em v) := by
      intro q f hq hf
      have hq0 : q = ⊥ := (Ideal.eq_bot_or_top q).resolve_right hq.ne_top
      subst hq0
      refine ⟨⊥, ⟨ℂ, inferInstance, inferInstance, RingHom.id ℂ, t, ?_, h1, h2⟩, hq, le_rfl, hf⟩
      exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.id ℂ).injective
    obtain ⟨t₀, -, h₀⟩ := H j hj o b ℂ em v hvd
    have m := h₀ ℂ (RingHom.id ℂ) t h1 h2
    have m' := h₀ ℂ (RingHom.id ℂ) t' h1' h2'
    refine ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ t₀ t t').2 _ (𝟙 _) m).2 ?_
    rwa [Category.id_comp]
  exact key _ (by rw [hid, Category.id_comp]) t t' hs hs' hv hv''

end GlobalTheory.ZM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointDeterminesShapeComplexStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPoint_determines_shape_complex : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (t t' : TObj g ((n ^ j) ^ 2) J b (spMap em)) (v : Ix g ((n ^ j) ^ 2) → ℂ) (c : ℂ), c ≠ 0 → t.Shape Mat κ → t'.Shape Mat κ → t.HasTh (𝟙 _) v → t'.HasTh (𝟙 _) (c • v) → TMap t' t (𝟙 _) := by
  first | exact @GlobalTheory.ZM.tmap_of_hasTh_complex | exact GlobalTheory.ZM.tmap_of_hasTh_complex | (intros; apply GlobalTheory.ZM.tmap_of_hasTh_complex <;> assumption)
end
end
