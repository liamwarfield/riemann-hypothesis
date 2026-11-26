module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersRamificationLevelPlaces
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebra
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NatCastKPZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocKIntMem
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjectiveOfIndep
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridHeckeCharactersExist
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

noncomputable section
namespace GlobalTheory.HeckeCharsOfSquare

variable {D : D7}

theorem isHeckeChar_mul {χ ψ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hψ : IsHeckeChar D ψ) :
    IsHeckeChar D (χ * ψ) :=
  ⟨hχ.1.mul hψ.1, fun x => by rw [MonoidHom.mul_apply, hχ.2 x, hψ.2 x, mul_one]⟩

theorem isHeckeChar_inv {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ :=
  ⟨hχ.1.inv, fun x => by rw [MonoidHom.inv_apply, hχ.2 x, inv_one]⟩

theorem isHeckeChar_div {χ ψ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hψ : IsHeckeChar D ψ) :
    IsHeckeChar D (χ / ψ) := by
  rw [div_eq_mul_inv]; exact isHeckeChar_mul hχ (isHeckeChar_inv hψ)

theorem isHeckeChar_pow {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (n : ℕ) : IsHeckeChar D (χ ^ n) :=
  ⟨hχ.1.pow n, fun x => by rw [MonoidHom.pow_apply, hχ.2 x, one_pow]⟩

theorem resEta_of_mod {χ : (AE D)ˣ →* Circle} {a b : ℕ} (h : ResEta D χ a) (hab : a % 2 = b % 2) : ResEta D χ b := by
  refine ⟨h.1, fun η hη x => ?_⟩
  rw [h.2 η hη x, ← Nat.mod_add_div a 2, ← Nat.mod_add_div b 2, pow_add, pow_add, pow_mul, pow_mul,
    GlobalTheory.EtaTildeOddParity.isEta_sq D η hη x, one_pow, one_pow, hab]

theorem resEta_mul {χ ψ : (AE D)ˣ →* Circle} {a b : ℕ} (hχ : ResEta D χ a) (hψ : ResEta D ψ b) :
    ResEta D (χ * ψ) (a + b) :=
  ⟨hχ.1, fun η hη x => by rw [MonoidHom.mul_apply, hχ.2 η hη x, hψ.2 η hη x, pow_add]⟩

theorem resEta_inv {χ : (AE D)ˣ →* Circle} {a : ℕ} (hχ : ResEta D χ a) : ResEta D χ⁻¹ a := by
  refine ⟨hχ.1, fun η hη x => ?_⟩
  rw [MonoidHom.inv_apply, hχ.2 η hη x, ← inv_pow]
  have h2 := GlobalTheory.EtaTildeOddParity.isEta_sq D η hη x
  rw [inv_eq_of_mul_eq_one_right (by rw [← sq, h2] : η x * η x = 1)]

theorem resEta_pow {χ : (AE D)ˣ →* Circle} {a : ℕ} (hχ : ResEta D χ a) (k : ℕ) : ResEta D (χ ^ k) (a * k) :=
  ⟨hχ.1, fun η hη x => by rw [MonoidHom.pow_apply, hχ.2 η hη x, pow_mul]⟩

theorem resEta_div {χ ψ : (AE D)ˣ →* Circle} {a b : ℕ} (hχ : ResEta D χ a) (hψ : ResEta D ψ b) :
    ResEta D (χ / ψ) (a + b) := by
  rw [div_eq_mul_inv]; exact resEta_mul hχ (resEta_inv hψ)

theorem resEta_of_att {μ η : (AE D)ˣ →* Circle} {a b : ℕ} (ha : ResEta D (Lift.attChr μ η a) a)
    (hb : ResEta D (Lift.attChr μ η b) b) (hab : Odd (a + b)) : ResEta D μ 0 ∧ ResEta D η 1 := by
  rcases Nat.even_or_odd a with hae | hao
  · have hbo : Odd b := (Nat.odd_add'.1 hab).2 hae
    have hna : ¬ Odd a := Nat.not_odd_iff_even.2 hae
    simp only [Lift.attChr, hna, if_false] at ha
    simp only [Lift.attChr, hbo, if_true] at hb
    have hμ : ResEta D μ 0 := resEta_of_mod ha (by rw [Nat.even_iff.1 hae])
    refine ⟨hμ, resEta_of_mod (χ := η) (a := a + b) ?_ (by rw [Nat.odd_iff.1 hab])⟩
    have e : η = μ / (μ * η⁻¹) := by rw [div_mul_eq_div_div, div_self', one_div, inv_inv]
    rw [e]; exact resEta_div ha hb
  · have hbe : Even b := by
      rcases Nat.even_or_odd b with h | h
      · exact h
      · exact absurd hab (Nat.not_odd_iff_even.2 (hao.add_odd h))
    have hnb : ¬ Odd b := Nat.not_odd_iff_even.2 hbe
    simp only [Lift.attChr, hao, if_true] at ha
    simp only [Lift.attChr, hnb, if_false] at hb
    have hμ : ResEta D μ 0 := resEta_of_mod hb (by rw [Nat.even_iff.1 hbe])
    refine ⟨hμ, resEta_of_mod (χ := η) (a := b + a) ?_ (by rw [add_comm, Nat.odd_iff.1 hab])⟩
    have e : η = μ / (μ * η⁻¹) := by rw [div_mul_eq_div_div, div_self', one_div, inv_inv]
    rw [e]; exact resEta_div hb ha

end GlobalTheory.HeckeCharsOfSquare

namespace GlobalTheory.HeckeCharsOfSquare

end GlobalTheory.HeckeCharsOfSquare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CrdLatEqLatFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

namespace GlobalTheory.ConjPlaceRed

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem resS_conj_zero (τ : E →ₐ[F] E) (w w' : Pl E)
    (hc : ∀ c ∈ w.asIdeal, ∃ c' ∈ w'.asIdeal, (c' : E) = τ (c : E)) (s t : Formalism.L2.Herm.intAf F E)
    (ht : (t : E ⊗[F] Formalism.L2.Herm.Af F) = Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) (s : E ⊗[F] Formalism.L2.Herm.Af F))
    (hs : resS F w s = 0) : resS F w' t = 0 := by
  let σ : Formalism.L2.Herm.intAf F E →+* Formalism.L2.Herm.intAf F E :=
    ((Formalism.UG.sigR τ (Formalism.L2.Herm.Af F)).comp
      (Formalism.L2.Herm.intAf F E).subtype).codRestrict _ (fun x => GlobalTheory.ResConjPlace.conj_mem_int τ x.2)
  have hts : t = σ s := Subtype.ext ht
  have h3 : idS F w.asIdeal ≤ (idS F w'.asIdeal).comap σ := by
    refine Ideal.map_le_iff_le_comap.2 fun c hcw => ?_
    obtain ⟨c', hc', hcc⟩ := hc c hcw
    have : σ (oToS F E c) = oToS F E c' := by
      apply Subtype.ext
      show τ (c : E) ⊗ₜ[F] _ = (c' : E) ⊗ₜ[F] _
      rw [hcc]; rfl
    rw [Ideal.mem_comap, Ideal.mem_comap, this]
    exact Ideal.mem_map_of_mem _ hc'
  rw [hts]
  rw [GlobalTheory.GeoActCompare.resS_eq_resI, GlobalTheory.GeoActCompare.resI_eq_zero_iff] at hs ⊢
  exact h3 hs

theorem resS_conj_ite (τ : E →ₐ[F] E) (w w' : Pl E)
    (hc : ∀ c ∈ w.asIdeal, ∃ c' ∈ w'.asIdeal, (c' : E) = τ (c : E)) (s t : Formalism.L2.Herm.intAf F E)
    (ht : (t : E ⊗[F] Formalism.L2.Herm.Af F) = Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) (s : E ⊗[F] Formalism.L2.Herm.Af F))
    (b : Prop) [Decidable b] (hs : resS F w s = if b then 1 else 0) : resS F w' t = if b then 1 else 0 := by
  let c : Formalism.L2.Herm.intAf F E := if b then 1 else 0
  have hc1 : resS F w c = if b then 1 else 0 := by
    simp only [c]; split_ifs <;> simp
  have hc2 : resS F w' c = if b then 1 else 0 := by
    simp only [c]; split_ifs <;> simp
  have hcs : Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) (c : E ⊗[F] Formalism.L2.Herm.Af F) = (c : E ⊗[F] Formalism.L2.Herm.Af F) := by
    simp only [c]; split_ifs <;> simp
  have h0 := resS_conj_zero τ w w' hc (s - c) (t - c) (by
    rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, map_sub, ht, hcs]) (by
    rw [map_sub, hs, hc1, sub_self])
  rw [map_sub, sub_eq_zero, hc2] at h0
  exact h0

end General

variable {D : D7}

theorem crdLat_eq_latFrame (V : HSp D) : Formalism.L2.Herm.crdLat V V.L0 = GlobalTheory.PlaceModel.latFrame V := by
  ext y
  rw [GlobalTheory.PlaceModel.mem_latFrame]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have e : ∑ i, (Formalism.L2.Herm.crd V v) i • V.frame i = v := V.frame.sum_equivFun v
    show ∑ i, (Formalism.L2.Herm.crd V v) i • V.frame i ∈ V.L0
    rw [e]; exact hv
  · intro hy
    refine ⟨_, hy, ?_⟩
    show V.frame.equivFun (∑ i, y i • V.frame i) = y
    rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.ConjPlaceRed

namespace GlobalTheory.ConjPlaceRed

theorem Lv_eq_latFrame (D : D7) : Formalism.L2.SG.InstExistsPf.Lv D = GlobalTheory.PlaceModel.latFrame (Yc D 0) := by
  ext y
  rw [Formalism.L2.SG.InstExistsPf.mem_Lv]
  exact (GlobalTheory.PlaceModel.mem_latFrame (Yc D 0) y).symm

theorem mem_Lf (D : D7) (v : Fin (Yc D 0).rank → EAf D) :
    v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.PlaceModel.latFrame (Yc D 0)) ↔
      v ∈ lamAf (F := D.host.F) (Formalism.L2.SG.InstExistsPf.Lv D) := by
  rw [Lv_eq_latFrame]
  exact (Set.ext_iff.1 (Formalism.IndefR.Eqv.lamAf_eq_hatL (V := Yc D 0) (GlobalTheory.PlaceModel.latFrame (Yc D 0))) v).symm

theorem mem_St_of_Kset (D : D7) (β : GL (Fin (Yc D 0).rank) (EAf D)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf)
    (hβ : IsFrame β (GlobalTheory.PlaceModel.latFrame (Yc D 0))) (hx : x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset) :
    x.1 ∈ St β := by
  have hS : ∀ v, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ↔
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat x *ᵥ v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf := hx
  have hSi : ∀ v, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ↔
      (((x.1)⁻¹ : GL (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) _) : Matrix _ _ _) *ᵥ v ∈
        (Formalism.L2.SG.InstExistsPf.instOf D).Lf :=
    (Formalism.UG.stabGL (Formalism.L2.SG.InstExistsPf.instOf D).Lf).inv_mem hx
  refine (GlobalTheory.LevSplit.mem_St_iff β _ hβ (x.1 : GL (Fin (Yc D 0).rank) (EAf D))).2 ⟨fun y hy => (mem_Lf D _).2 ((hS y).1 ((mem_Lf D y).1 hy)),
    fun y hy => (mem_Lf D _).2 ((hSi y).1 ((mem_Lf D y).1 hy))⟩


set_option maxHeartbeats 1000000 in
theorem redFn_conj_eq_one : ∀ (D : D7) (β : GL (Fin (Yc D 0).rank) (EAf D)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf)
    (PP PP' : Formalism.L2.DIV.Pl D.host.E),
    IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset →
    Formalism.IndefR.Lev.IsConjPl PP' PP → Formalism.L2.DIV.redFn β PP' x.1 = 1 → Formalism.L2.DIV.redFn β PP x.1 = 1 := by
  intro D β x PP PP' hβ hx hc h1
  rw [crdLat_eq_latFrame] at hβ
  have hsd := GlobalTheory.PlaceModel.isSelfDualC_latFrame (Yc D 0)
  obtain ⟨m, s, s', hs, hd⟩ := GlobalTheory.LatVacDual.dualFamily D (Yc D 0) _ hsd
  obtain ⟨G, hG⟩ := GlobalTheory.FrameGram.exists_unit_adelic star (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (fun _ => GlobalTheory.LevSplit.sigR_int) (fun _ => rfl) (Yc D 0).gram β _ hβ (fun y hy => (hsd.2 y).1 hy) s s' hs hd
  obtain ⟨h, hh⟩ := mem_St_of_Kset D β x hβ hx
  have hU : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype h * β⁻¹ ∈
      Formalism.UG.UJ (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
        ((Yc D 0).gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) := by
    have e : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype h * β⁻¹ = x.1 := hh
    rw [e]
    exact x.2
  have key := GlobalTheory.FrameMove.conj_gram_sub (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (Formalism.L2.Herm.intAf D.host.F D.host.E) _ β G h hG hU
  rw [← hh, redFn_frGL] at h1 ⊢
  have h1' : Formalism.UG.bc (resS D.host.F PP') h⁻¹ = 1 := by rw [map_inv, h1, inv_one]
  have h2 : Formalism.UG.bc (resS D.host.F PP) (G * h * G⁻¹) = 1 := by
    apply Units.ext
    ext i j
    have hz : resS D.host.F PP' ((h⁻¹).val j i) = if j = i then 1 else 0 := by
      have e : ((Formalism.UG.bc (resS D.host.F PP') h⁻¹ : GL (Fin (Yc D 0).rank) (kP PP')) : Matrix _ _ (kP PP')) j i =
          resS D.host.F PP' ((h⁻¹).val j i) := rfl
      rw [← e, h1', Units.val_one, Matrix.one_apply]
    have h0 := resS_conj_ite D.sp.cm.sig PP' PP hc _ _ (key i j) (j = i) hz
    refine h0.trans ?_
    rw [Units.val_one, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  rw [map_mul, map_mul, map_inv] at h2
  exact conj_eq_one_iff.1 h2

end GlobalTheory.ConjPlaceRed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlueSmoothOfCompactSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlueSmoothOfCompactSupport
open GlobalTheory.Orb
open scoped Topology ContDiff Manifold

noncomputable section

namespace GlobalTheory

theorem glue_smooth_of_compactSupport : ∀ (H : Type) [TopologicalSpace H] (X : Type) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] (c : H → X) (f : H → ℂ), Continuous c →
    HasCompactSupport f →
    (∀ a, ∃ V : Set X, IsOpen V ∧ c a ∈ V ∧ ∃ Φ : X → ℂ, ContDiffOn ℝ ∞ Φ V ∧
      ∀ g, c g ∈ V → f g = Φ (c g)) →
    ∃ Φ : X → ℂ, ContDiff ℝ ∞ Φ ∧ ∀ g, f g = Φ (c g) := by
  intro H _ X _ _ _ c f hc hf hloc
  choose V hVo hcV Φ hΦ hfΦ using hloc
  have hs : IsClosed (c '' tsupport f) := (hf.isCompact.image hc).isClosed
  have hcov : c '' tsupport f ⊆ ⋃ a, V a := by
    rintro _ ⟨a, -, rfl⟩
    exact Set.mem_iUnion.2 ⟨a, hcV a⟩
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, X) hs V hVo hcov
  refine ⟨fun y => ∑ᶠ a, χ a y • Φ a y, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    refine χ.contDiffAt_finsum fun a hy => ?_
    exact (hΦ a).contDiffAt ((hVo a).mem_nhds (hχ a hy))
  · intro g
    have hterm : ∀ a, χ a (c g) • Φ a (c g) = χ a (c g) • f g := by
      intro a
      by_cases h0 : χ a (c g) = 0
      · simp [h0]
      · have hmem : c g ∈ V a := hχ a (subset_tsupport _ h0)
        rw [hfΦ a g hmem]
    simp only [hterm]
    by_cases hg : g ∈ tsupport f
    · rw [← finsum_smul, χ.sum_eq_one ⟨g, hg, rfl⟩, one_smul]
    · have : f g = 0 := image_eq_zero_of_notMem_tsupport hg
      simp [this]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlueSmoothOfCompactSupportStatement
open GlobalTheory.Orb
open scoped Topology ContDiff Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_contDiff_comp_of_locally_smooth_compactSupport : ∀ (H : Type) [TopologicalSpace H] (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] (c : H → X) (f : H → ℂ), Continuous c → HasCompactSupport f → (∀ a, ∃ V : Set X, IsOpen V ∧ c a ∈ V ∧ ∃ Φ : X → ℂ, ContDiffOn ℝ ∞ Φ V ∧ ∀ g, c g ∈ V → f g = Φ (c g)) → ∃ Φ : X → ℂ, ContDiff ℝ ∞ Φ ∧ ∀ g, f g = Φ (c g) := by
  first | exact @GlobalTheory.glue_smooth_of_compactSupport | exact GlobalTheory.glue_smooth_of_compactSupport | (intros; apply GlobalTheory.glue_smooth_of_compactSupport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosedSubgroupOfLocalStabilizerPairs
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosedSubgroupOfLocalStabilizerPairs
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabDense

section Generic

theorem units_tendsto {M ι : Type} [Monoid M] [TopologicalSpace M] {l : Filter ι} {f : ι → Mˣ} {u : Mˣ}
    (h1 : Filter.Tendsto (fun i => (f i : M)) l (nhds (u : M)))
    (h2 : Filter.Tendsto (fun i => (((f i)⁻¹ : Mˣ) : M)) l (nhds ((u⁻¹ : Mˣ) : M))) :
    Filter.Tendsto f l (nhds u) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact h1.prodMk_nhds (MulOpposite.continuous_op.continuousAt.tendsto.comp h2)

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem cut_mul {a b : A} (hab : a * b = 0) (m : Matrix n n A) :
    (a + b) • m + (1 - (a + b)) • (1 : Matrix n n A) =
      (a • m + (1 - a) • (1 : Matrix n n A)) * (b • m + (1 - b) • (1 : Matrix n n A)) := by
  simp only [add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul]
  linear_combination (norm := module) hab • (2 • m - m * m - 1)

omit [Fintype n] in
theorem cut_entry (a : A) (m : Matrix n n A) (i j : n) :
    (a • m + (1 - a) • (1 : Matrix n n A)) i j = a * (m - 1) i j + (1 : Matrix n n A) i j := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

omit [Fintype n] in
theorem cut_supp {a : A} (ha : a * a = a) (m : Matrix n n A) (i j : n) :
    a * (a • m + (1 - a) • (1 : Matrix n n A) - 1) i j = (a • m + (1 - a) • (1 : Matrix n n A) - 1) i j := by
  rw [Matrix.sub_apply, cut_entry, add_sub_cancel_right, ← mul_assoc, ha]

theorem sum_idem {R ι : Type} [CommRing R] (p : ι → R) (s : Finset ι) (h : ∀ i, p i * p i = p i)
    (h0 : ∀ i j, i ≠ j → p i * p j = 0) : (∑ i ∈ s, p i) * (∑ i ∈ s, p i) = ∑ i ∈ s, p i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => h0 i j (Ne.symm hji)) (fun hi' => absurd hi hi'), h i]

end Generic

variable {D : D7}

theorem exists_placeIdem (v : HeightOneSpectrum (𝓞 D.host.F)) : ∃ ε, IsPlaceIdem D v ε := by
  classical
  refine ⟨pairA D.host.F 0 (singleV D.host.F v 1), singleV D.host.F v 1, rfl, ?_, fun w hw => ?_⟩
  · exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) v 1
  · exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) 1 hw

theorem placeIdem_mul {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hv : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, -, hα0⟩ := h
  obtain ⟨α', rfl, -, hα0'⟩ := h'
  have hz : α * α' = 0 := by
    refine RestrictedProduct.ext _ _ fun w => ?_
    show α w * α' w = 0
    by_cases hw : w = v
    · have hw' : α' w = 0 := hα0' w (by rw [hw]; exact hv)
      rw [hw', mul_zero]
    · have hw' : α w = 0 := hα0 w hw
      rw [hw', zero_mul]
  rw [show pairA D.host.F 0 α * pairA D.host.F 0 α' = pairA D.host.F (0 * 0) (α * α') from rfl, hz, mul_zero]
  rfl

theorem placeIdem_idem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    ε * ε = ε := by
  obtain ⟨α, rfl, hα1, hα0⟩ := h
  have hz : α * α = α := by
    refine RestrictedProduct.ext _ _ fun w => ?_
    show α w * α w = α w
    by_cases hw : w = v
    · have hw' : α w = 1 := by rw [hw]; exact hα1
      rw [hw', mul_one]
    · have hw' : α w = 0 := hα0 w hw
      rw [hw', mul_zero]
  rw [show pairA D.host.F 0 α * pairA D.host.F 0 α = pairA D.host.F (0 * 0) (α * α) from rfl, hz, mul_zero]

theorem mt_inj (V : HSp D) {g h : GA D V} (e : Formalism.L2.Theta.mt V g = Formalism.L2.Theta.mt V h) : g = h := by
  apply Subtype.ext
  apply Units.ext
  exact e

theorem tendsto_of_mt {ι : Type} {l : Filter ι} (V : HSp D) {f : ι → GA D V} {g : GA D V}
    (h1 : Filter.Tendsto (fun i => Formalism.L2.Theta.mt V (f i)) l (nhds (Formalism.L2.Theta.mt V g)))
    (h2 : Filter.Tendsto (fun i => Formalism.L2.Theta.mt V (f i)⁻¹) l (nhds (Formalism.L2.Theta.mt V g⁻¹))) :
    Filter.Tendsto f l (nhds g) := by
  have hind : Topology.IsInducing
      (Subtype.val : ↥(HR (AF D.host.F) D.sp.cm.sig V.gram) → GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) :=
    Topology.IsInducing.subtypeVal
  exact hind.tendsto_nhds_iff.2 (units_tendsto h1 h2)

theorem infPart_entry (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) (i j : Fin V.rank) :
    infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
  have h1 : infHom V g = 1 := (MonoidHom.mem_ker).1 hg
  have h2 := congrArg (fun x : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) h1
  simp only [infHom, MonoidHom.comp_apply, Formalism.UG.bc] at h2
  have e1 : infPart D (Formalism.L2.Theta.mt V g i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := h2
  have e2 : infPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [Matrix.sub_apply, map_sub, e1, e2, sub_self]

theorem exists_trunc (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F) (hε : ∀ v, IsPlaceIdem D v (ε v))
    (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) :
    ∃ κ : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V → GA D V,
      (∀ g, κ ∅ g = 1) ∧
      (∀ v s (hv : v ∉ s) g, κ (Finset.cons v s hv) g = κ {v} g * κ s g) ∧
      (∀ v g, Stab V β g → Stab V β (κ {v} g) ∧ SuppPl (ε v) V (κ {v} g)) ∧
      ∀ g, Stab V β g → Filter.Tendsto (fun s => κ s g) Filter.atTop (nhds g) := by
  have hid : ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.F)), (∑ v ∈ s, ε v) * (∑ v ∈ s, ε v) = ∑ v ∈ s, ε v :=
    fun s => sum_idem ε s (fun v => placeIdem_idem (hε v)) (fun v w hvw => placeIdem_mul (hε v) (hε w) hvw)
  choose K hK using fun s => GlobalTheory.T.idempotent_twisted_group_endomorphism D V β (∑ v ∈ s, ε v) (hid s)
  have hKm : ∀ s x, Formalism.L2.Theta.mt V (K s x) = algebraMap (AF D.host.F) (AE D) (∑ v ∈ s, ε v) • Formalism.L2.Theta.mt V x +
      (1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ s, ε v)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) :=
    fun s x => (hK s x).1
  refine ⟨fun s g => K s g, fun g => ?_, fun v s hv g => ?_, fun v g hg => ⟨(hK {v} g).2 hg, fun i j => ?_⟩, fun g hg => ?_⟩
  · apply mt_inj V
    rw [hKm, Finset.sum_empty, map_zero, zero_smul, sub_zero, one_smul, zero_add, GlobalTheory.AdelicLatMove.mt_one]
  · apply mt_inj V
    show Formalism.L2.Theta.mt V (K _ g) = Formalism.L2.Theta.mt V (K {v} g * K s g)
    rw [hKm, GlobalTheory.AdelicLatMove.mt_mul, hKm, hKm, Finset.sum_cons, Finset.sum_singleton, map_add (f := _)]
    apply cut_mul
    rw [← map_mul, Finset.mul_sum, Finset.sum_eq_zero (fun w hw => placeIdem_mul (hε v) (hε w) (fun hvw => hv (by rw [hvw]; exact hw))), map_zero]
  · show algebraMap (AF D.host.F) (AE D) (ε v) * (Formalism.L2.Theta.mt V (K {v} g) - 1) i j = (Formalism.L2.Theta.mt V (K {v} g) - 1) i j
    rw [hKm, Finset.sum_singleton]
    exact cut_supp (by rw [← map_mul, placeIdem_idem (hε v)]) _ i j
  · have key : ∀ x : GA D V, x ∈ GfC V →
        Filter.Tendsto (fun s => Formalism.L2.Theta.mt V (K s x)) Filter.atTop (nhds (Formalism.L2.Theta.mt V x)) := by
      intro x hx
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      simp only [hKm, cut_entry]
      have hlim := (GlobalTheory.T.tendsto_finitePlaceTruncation_adeleE D ε hε ((Formalism.L2.Theta.mt V x - 1) i j) (infPart_entry V hx i j)).add_const
        ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)
      have e : (Formalism.L2.Theta.mt V x - 1) i j + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j = Formalism.L2.Theta.mt V x i j := by
        rw [Matrix.sub_apply, sub_add_cancel]
      rw [e] at hlim
      exact hlim
    refine tendsto_of_mt V (key g hg.1) ?_
    simpa only [map_inv] using key g⁻¹ (inv_mem hg.1)

theorem mem_of_local (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (H : Subgroup (GA D S × GA D T)) (hH : IsClosed (H : Set (GA D S × GA D T)))
    (hloc : ∀ v ε, IsPlaceIdem D v ε → ∀ g h, Stab S βS g → Stab T βT h → SuppPl ε S g → SuppPl ε T h → (g, h) ∈ H)
    (g : GA D S) (h : GA D T) (hg : Stab S βS g) (hh : Stab T βT h) : (g, h) ∈ H := by
  choose ε hε using fun v => exists_placeIdem (D := D) v
  obtain ⟨κS, hS0, hSc, hS1, hSt⟩ := exists_trunc ε hε S βS
  obtain ⟨κT, hT0, hTc, hT1, hTt⟩ := exists_trunc ε hε T βT
  have hmem : ∀ s, (κS s g, κT s h) ∈ H := by
    intro s
    induction s using Finset.cons_induction with
    | empty => rw [hS0, hT0]; exact H.one_mem
    | cons v s hv ih =>
      rw [hSc v s hv, hTc v s hv]
      exact H.mul_mem (hloc v (ε v) (hε v) _ _ (hS1 v g hg).1 (hT1 v h hh).1 (hS1 v g hg).2 (hT1 v h hh).2) ih
  exact hH.mem_of_tendsto ((hSt g hg).prodMk_nhds (hTt h hh)) (Filter.Eventually.of_forall hmem)

end GlobalTheory.StabDense

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosedSubgroupOfLocalStabilizerPairsStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closedSubgroup_of_localStabilizerPairs : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (H : Subgroup (GA D S × GA D T)), IsClosed (H : Set (GA D S × GA D T)) → (∀ v ε, IsPlaceIdem D v ε → ∀ g h, Stab S βS g → Stab T βT h → SuppPl ε S g → SuppPl ε T h → (g, h) ∈ H) → ∀ g h, Stab S βS g → Stab T βT h → (g, h) ∈ H := by
  first | exact @GlobalTheory.StabDense.mem_of_local | exact GlobalTheory.StabDense.mem_of_local | (intros; apply GlobalTheory.StabDense.mem_of_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarRightInvariantCompact
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible IsIrredSubrep)
open scoped InnerProductSpace
open scoped Pointwise

namespace GlobalTheory.CompactRight

theorem map_mul_right_eq_of_mem_compact {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (k : G) (hk : k ∈ K) : Measure.map (· * k) μ = μ := by
  set c := Measure.haarScalarFactor (Measure.map (· * k) μ) μ with hc
  have hmapEq : Measure.map (· * k) μ = c • μ := Measure.isMulLeftInvariant_eq_smul _ μ
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
  set S : Set G := V * (K : Set G) with hS
  have hScpt : IsCompact S := hVc.mul hK
  have hVsubS : V ⊆ S := by
    intro v hv
    exact Set.mem_mul.2 ⟨v, hv, 1, K.one_mem, mul_one v⟩
  have hSpre : (· * k) ⁻¹' S = S := by
    ext x
    simp only [Set.mem_preimage, hS, Set.mem_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨v, hv, a, ha, hva⟩
      refine ⟨v, hv, a * k⁻¹, K.mul_mem ha (K.inv_mem hk), ?_⟩
      rw [← mul_assoc, hva, mul_inv_cancel_right]
    · rintro ⟨v, hv, a, ha, hva⟩
      exact ⟨v, hv, a * k, K.mul_mem ha hk, by rw [← mul_assoc, hva]⟩
  have hSpos : μ S ≠ 0 := (lt_of_lt_of_le (Measure.measure_pos_of_mem_nhds (μ := μ) hV1) (measure_mono hVsubS)).ne'
  have hSfin : μ S ≠ ⊤ := hScpt.measure_lt_top.ne
  have hmapS : Measure.map (· * k) μ S = μ S := by
    rw [show (· * k) = (MeasurableEquiv.mulRight k : G → G) from rfl, MeasurableEquiv.map_apply]
    exact congrArg μ hSpre
  have hcOne : c = 1 := by
    have hcEq : (c : ENNReal) * μ S = 1 * μ S := by
      have hcS := hmapS
      rw [hmapEq, smul_apply, ENNReal.smul_def, smul_eq_mul] at hcS
      rw [one_mul]
      exact hcS
    exact_mod_cast (ENNReal.mul_left_inj hSpos hSfin).1 hcEq
  rw [hmapEq, hcOne, one_smul]

end GlobalTheory.CompactRight
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalProjectionEqOfIdempotentPatch
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalProjectionEqOfIdempotentPatch
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompIdem

theorem projV_eq_of_idem : ∀ {D : D7} (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g k : GA D T) (ε : AE D), compFin D.host.F D.host.E v ε = 1 → Formalism.L2.Theta.mt T k = ε • Formalism.L2.Theta.mt T g + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) → projV T v k = projV T v g := by
  intro D T v g k ε hε h
  apply GlobalTheory.AdelicU.matHom_injective _ D.sp.cm.sig T.gram
  apply Units.ext
  show (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram (proj D.sp.cm.sig T.gram v k)).1 =
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram (proj D.sp.cm.sig T.gram v g)).1
  rw [GlobalTheory.AdelicU.matHom_proj, GlobalTheory.AdelicU.matHom_proj]
  show ((GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram k).1).map (compFin D.host.F D.host.E v) =
    ((GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram g).1).map (compFin D.host.F D.host.E v)
  change (Formalism.L2.Theta.mt T k).map _ = (Formalism.L2.Theta.mt T g).map _
  rw [h, GlobalTheory.CompStab.map_idem, hε, sub_self, zero_smul, add_zero, one_smul]

end GlobalTheory.CompIdem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalProjectionEqOfIdempotentPatchStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localProjection_eq_of_idempotent_patch : ∀ {D : D7} (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g k : GA D T) (ε : AE D), compFin D.host.F D.host.E v ε = 1 → Formalism.L2.Theta.mt T k = ε • Formalism.L2.Theta.mt T g + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) → projV T v k = projV T v g := by
  first | exact @GlobalTheory.CompIdem.projV_eq_of_idem | exact GlobalTheory.CompIdem.projV_eq_of_idem | (intros; apply GlobalTheory.CompIdem.projV_eq_of_idem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaximalCompactActsOnFockVectorsBySubstitution
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaximalCompactActsOnFockVectorsBySubstitution
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompact

theorem det_isUnit_of_onb {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ}
    (h : Formalism.IndefR.Datum.IsONBasis G s B p) : IsUnit B.det := by
  obtain ⟨ε, hε, hB, -⟩ := h
  have hd : (Bᴴ * G * B).det ≠ 0 := by
    rw [hB, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
    rcases hε a with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
  rw [Matrix.det_mul] at hd
  exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hd)

theorem comm_of_onb {k : ℕ} {G s B κ : Matrix (Fin k) (Fin k) ℂ} {p : ℕ}
    (h : Formalism.IndefR.Datum.IsONBasis G s B p) (hκ : IsKMat p κ) : s * (B * κ * B⁻¹) = B * κ * B⁻¹ * s := by
  have hu := det_isUnit_of_onb h
  obtain ⟨ε, hε, -, hs⟩ := h
  obtain ⟨-, hκ0⟩ := hκ
  have hBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hu
  have hiB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hu
  have hcomm : (diagonal fun a => (ε a : ℂ)) * κ = κ * diagonal fun a => (ε a : ℂ) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : (i.val < p ↔ j.val < p)
    · have hij' : ε i = ε j := by
        rcases hε i with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩ <;> rcases hε j with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩
        · rw [hi1, hj1]
        · exact absurd (hij.mp hi2) (by omega)
        · exact absurd (hij.mpr hj2) (by omega)
        · rw [hi1, hj1]
      rw [hij', mul_comm]
    · rw [hκ0 i j hij, mul_zero, zero_mul]
  have hs' : s = B * (diagonal fun a => (ε a : ℂ)) * B⁻¹ := by
    calc s = s * (B * B⁻¹) := by rw [hBi, mul_one]
      _ = B * (diagonal fun a => (ε a : ℂ)) * B⁻¹ := by rw [← mul_assoc, hs]
  rw [hs']
  simp only [mul_assoc]
  rw [← mul_assoc B⁻¹ B, hiB, one_mul, ← mul_assoc B⁻¹ B, hiB, one_mul, ← mul_assoc _ κ, hcomm, mul_assoc κ]

theorem compAt_of_atTau {D : D7} {θ : InfFam D} {S : HSp D} {τ : D.what₂.Tau}
    {M : Matrix (Fin S.rank) (Fin S.rank) ℂ} {g : GA D S} (h : IsAtTau θ S τ M g) :
    compAt θ τ (Formalism.L2.Theta.mt S g) = M ∧ ∀ ρ, ρ ≠ τ → compAt θ ρ (Formalism.L2.Theta.mt S g) = 1 := by
  obtain ⟨-, h1, h2⟩ := h
  refine ⟨Eq.trans ?_ h1, fun ρ hρ => Eq.trans ?_ (h2 ρ hρ)⟩
  · rfl
  · rfl

theorem om_pureTensorO_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → ∀ (τ : D.what₂.Tau) κS κT, IsKMat (pS τ) κS → IsKMat (pT τ) κT → ∀ g h, IsAtTau θ S τ (BS τ * κS * (BS τ)⁻¹) g → IsAtTau θ T τ (BT τ * κT * (BT τ)⁻¹) h → ∀ c : ℂ, om (g, h) f = c • f → ∀ P, om (g, h) (pureTensorO ψ θ S T sS sT BS BT f P) = c • pureTensorO ψ θ S T sS sT BS BT f (fockSub τ (pS τ) (pT τ) κS κT P) := by
  intro D ψ θ S T χS χT om hW hθ sS BS sT BT pS pT hpS hpT hcS hcT hoS hoT f hf τ κS κT hκS hκT g h hg hh c hc P
  have hstd : IsStdChar D ψ (-1) := hW.std
  obtain ⟨hgτ, hgρ⟩ := compAt_of_atTau hg
  obtain ⟨hhτ, hhρ⟩ := compAt_of_atTau hh
  have hcomS : ∀ ρ, sS ρ * compAt θ ρ (Formalism.L2.Theta.mt S g) = compAt θ ρ (Formalism.L2.Theta.mt S g) * sS ρ := by
    intro ρ
    by_cases hρ : ρ = τ
    · subst hρ
      rw [hgτ]
      exact comm_of_onb (hoS ρ) hκS
    · rw [hgρ ρ hρ, mul_one, one_mul]
  have hcomT : ∀ ρ, sT ρ * compAt θ ρ (Formalism.L2.Theta.mt T h) = compAt θ ρ (Formalism.L2.Theta.mt T h) * sT ρ := by
    intro ρ
    by_cases hρ : ρ = τ
    · subst hρ
      rw [hhτ]
      exact comm_of_onb (hoT ρ) hκT
    · rw [hhρ ρ hρ, mul_one, one_mul]
  have key := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS
    (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt S g) * BS ρ) sT sT BT
    (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt T h) * BT ρ) g h hcomS hcomT (fun _ => rfl) (fun _ => rfl) f hf P).2
  rw [key, hc, GlobalTheory.FiniteFock.pureTensorO_smul]
  have e2 := GlobalTheory.T.fockPolynomialVector_maximalCompact_moved_bases D ψ θ S T hstd hθ sS BS sT BT pS pT hpS hpT hcS hcT hoS hoT f hf τ κS κT hκS hκT
    (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt S g) * BS ρ) (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt T h) * BT ρ) ?_ ?_ ?_ P
  · rw [e2]
  · show compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ = BS τ * κS
    rw [hgτ, mul_assoc, Matrix.nonsing_inv_mul _ (det_isUnit_of_onb (hoS τ)), mul_one]
  · show compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ = BT τ * κT
    rw [hhτ, mul_assoc, Matrix.nonsing_inv_mul _ (det_isUnit_of_onb (hoT τ)), mul_one]
  · intro ρ hρ
    refine ⟨?_, ?_⟩
    · show compAt θ ρ (Formalism.L2.Theta.mt S g) * BS ρ = BS ρ
      rw [hgρ ρ hρ, one_mul]
    · show compAt θ ρ (Formalism.L2.Theta.mt T h) * BT ρ = BT ρ
      rw [hhρ ρ hρ, one_mul]

end GlobalTheory.FockCompact
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaximalCompactActsOnFockVectorsBySubstitutionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalCompact_acts_on_fockVectors_by_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → ∀ (τ : D.what₂.Tau) κS κT, IsKMat (pS τ) κS → IsKMat (pT τ) κT → ∀ g h, IsAtTau θ S τ (BS τ * κS * (BS τ)⁻¹) g → IsAtTau θ T τ (BT τ * κT * (BT τ)⁻¹) h → ∀ c : ℂ, om (g, h) f = c • f → ∀ P, om (g, h) (pureTensorO ψ θ S T sS sT BS BT f P) = c • pureTensorO ψ θ S T sS sT BS BT f (fockSub τ (pS τ) (pT τ) κS κT P) := by
  first | exact @GlobalTheory.FockCompact.om_pureTensorO_compact | exact GlobalTheory.FockCompact.om_pureTensorO_compact | (intros; apply GlobalTheory.FockCompact.om_pureTensorO_compact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubOneIffEntries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KgFrame

open Formalism.L2.DIV Formalism.L2.Herm Formalism.UG
open scoped TensorProduct Matrix

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem dvd_of_forall_mem (g : ℕ) (hg : 1 ≤ g) (hr : (Ideal.span {(g : 𝓞 E)}).IsRadical)
    (b : 𝓞 E) (hb : ∀ PP : Pl E, (g : 𝓞 E) ∈ PP.asIdeal → b ∈ PP.asIdeal) : (g : 𝓞 E) ∣ b := by
  have hg0 : (g : 𝓞 E) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  rw [← Ideal.mem_span_singleton]
  refine hr ?_
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro J ⟨hJ, hp⟩
  have hJ0 : J ≠ ⊥ := by
    intro e
    rw [e, le_bot_iff, Ideal.span_singleton_eq_bot] at hJ
    exact hg0 hJ
  exact hb ⟨J, hp, hJ0⟩ (hJ (Ideal.mem_span_singleton_self _))

theorem entries_iff_red (g : ℕ) (hg : 1 ≤ g) (hr : (Ideal.span {(g : 𝓞 E)}).IsRadical) (y : GL (Fin n) (intAf F E)) :
    (∀ i j, ∃ t : intAf F E, (y : Matrix (Fin n) (Fin n) (intAf F E)) i j -
        (1 : Matrix (Fin n) (Fin n) (intAf F E)) i j = g • t) ↔
      ∀ PP : Pl E, (g : 𝓞 E) ∈ PP.asIdeal → bc (resS F PP) y = 1 := by
  constructor
  · intro h PP hP
    have hgk : ((g : ℕ) : kP PP) = 0 := by
      have := Ideal.Quotient.eq_zero_iff_mem.2 hP
      rwa [map_natCast] at this
    apply Units.ext
    ext i j
    obtain ⟨t, ht⟩ := h i j
    have h1 := congrArg (resS F PP) ht
    rw [map_sub, map_nsmul, nsmul_eq_mul, hgk, zero_mul, sub_eq_zero] at h1
    show resS F PP ((y : Matrix (Fin n) (Fin n) (intAf F E)) i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j
    rw [h1]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · intro h i j
    refine lc_div g (by omega) (dvd_of_forall_mem g hg hr) _ fun PP hP => ?_
    have h1 := congrArg (fun M : GL (Fin n) (kP PP) => (M : Matrix (Fin n) (Fin n) (kP PP)) i j) (h PP hP)
    change resS F PP ((y : Matrix (Fin n) (Fin n) (intAf F E)) i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j at h1
    rw [map_sub, h1]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]

theorem sub_one_iff_entries (Λ : Submodule (𝓞 E) (Fin n → E)) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hβ : IsFrame β Λ)
    (g : ℕ) (y : GL (Fin n) (intAf F E)) :
    (∀ v ∈ hatL (F := F) Λ, ∃ z ∈ hatL (F := F) Λ,
      (((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) *ᵥ v =
        (g : E ⊗[F] Formalism.L2.Herm.Af F) • z) ↔
    ∀ i j, ∃ t : intAf F E, (y : Matrix (Fin n) (Fin n) (intAf F E)) i j -
        (1 : Matrix (Fin n) (Fin n) (intAf F E)) i j = g • t := by
  classical
  set B : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) with hB
  set Bi : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) :=
    ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) with hBi
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) :=
    (y : Matrix (Fin n) (Fin n) (intAf F E)).map (intAf F E).subtype with hY
  have hXe : ((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = B * Y * Bi :=
    lc_frGL_coe β y
  have hBiB : Bi * B = 1 := Units.inv_mul β
  have hBBi : B * Bi = 1 := Units.mul_inv β
  have hX1 : ((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1 = B * (Y - 1) * Bi := by
    rw [hXe, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hBBi]
  have hYe : ∀ i j, Y i j - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j =
      (((y : Matrix (Fin n) (Fin n) (intAf F E)) i j - (1 : Matrix (Fin n) (Fin n) (intAf F E)) i j : intAf F E) :
        E ⊗[F] Formalism.L2.Herm.Af F) := by
    intro i j
    rw [← lc_one_coe]
    rfl
  constructor
  · intro h i j
    obtain ⟨z, hz, e⟩ := h _ (lc_frame_mem hβ (Pi.single j 1) (fun k => by rw [Pi.single_apply]; split_ifs; exacts [one_mem _, zero_mem _]))
    have hc := (hβ z).1 hz
    refine ⟨⟨(Bi *ᵥ z) i, hc i⟩, ?_⟩
    apply Subtype.ext
    rw [← hYe]
    have e2 := congrArg (fun w => (Bi *ᵥ w) i) e
    beta_reduce at e2
    have hconj : Bi * (B * (Y - 1) * Bi) * B = Y - 1 := by
      calc Bi * (B * (Y - 1) * Bi) * B = (Bi * B) * (Y - 1) * (Bi * B) := by simp only [Matrix.mul_assoc]
        _ = Y - 1 := by rw [hBiB, Matrix.one_mul, Matrix.mul_one]
    rw [hX1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hB, hconj, Matrix.mulVec_smul, Matrix.mulVec_single_one] at e2
    rw [Pi.smul_apply, smul_eq_mul] at e2
    rw [show (Y i j - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j) = (Y - 1).col j i from rfl, e2]
    simp [nsmul_eq_mul]
  · intro h
    choose t ht using h
    set M' : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := fun i j => ((t i j : intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) with hM'
    have hYM : Y - 1 = (g : E ⊗[F] Formalism.L2.Herm.Af F) • M' := by
      ext i j
      rw [Matrix.sub_apply, hYe, ht i j]
      rw [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      rfl
    refine fun v hv => ⟨B *ᵥ (M' *ᵥ (Bi *ᵥ v)), lc_frame_mem hβ _ fun i => ?_, ?_⟩
    · have hc := (hβ v).1 hv
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (t i j).2 (hc j)
    · rw [hX1, hYM, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

end Gen

theorem Lf_eq (D : D7) : (Formalism.L2.SG.InstExistsPf.instOf D).Lf =
      hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := by
  have hΛ : Formalism.L2.SG.InstExistsPf.Lv D = Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0 := by
    rw [Formalism.L2.SG.InstExistsPf.Lv_eq_map]; rfl
  show lamAf (F := ↥D.host.F) (Formalism.L2.SG.InstExistsPf.Lv D) = _
  rw [hΛ]
  unfold lamAf hatL Formalism.UG.latS
  rw [Set.image_eq_range]
  rfl


set_option maxHeartbeats 2000000 in
theorem mem_Kg_iff_redFn : ∀ (D : D7) (β : GL (Fin (Yc D 0).rank) (EAf D)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (g : ℕ),
    IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset → 1 ≤ g →
    (Ideal.span {(g : 𝓞 D.host.E)}).IsRadical →
    (x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kg g ↔
      ∀ PP : Formalism.L2.DIV.Pl D.host.E, (g : 𝓞 D.host.E) ∈ PP.asIdeal → Formalism.L2.DIV.redFn β PP x.1 = 1) := by
  intro D β x g hβ hx hg hr
  have hLf := Lf_eq D
  have hSt : x.1 ∈ St β := by
    rw [stabilizer_eq_stabilizer_lattice _ _ _ _ β hβ, ← hLf]
    exact hx
  obtain ⟨y, hy⟩ := hSt
  have hred : ∀ PP : Pl D.host.E, redFn β PP x.1 = bc (resS D.host.F PP) y := fun PP => by
    rw [← hy, redFn_frGL]

  have key := (sub_one_iff_entries _ β hβ g y).trans (entries_iff_red g hg hr y)
  have hfm : (Formalism.L2.SG.InstExistsPf.instOf D).fmat x = (frGL β y).val := by
    show x.1.val = _
    rw [← hy]
  have hv1 := fun v => SetLike.ext_iff.1 hLf v
  constructor
  · intro hk PP hP
    refine (hred PP).trans (key.1 (fun v hv => ?_) PP hP)
    obtain ⟨z, hz, e⟩ := hk.2 v ((hv1 v).2 hv)
    refine ⟨z, (hv1 z).1 hz, ?_⟩
    rw [← hfm]
    exact e
  · intro h
    refine ⟨hx, fun v hv => ?_⟩
    obtain ⟨z, hz, e⟩ := key.2 (fun PP hP => (hred PP).symm.trans (h PP hP)) v ((hv1 v).1 hv)
    refine ⟨z, (hv1 z).2 hz, ?_⟩
    rw [hfm]
    exact e

end GlobalTheory.KgFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParameterSphericalUnramifiedUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParameterSphericalUnramifiedUnitary
noncomputable section

namespace GlobalTheory.LFun.ExSatU

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem exists_hasSatU : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (ϖ : w.adicCompletion E) (σ : w.adicCompletion E →+* w.adicCompletion E) (q n : ℕ),
    IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V),
    ρ.IsIrreducible → IsAdmissible ρ → GlobalTheory.LGrp.IsSpherical ρ (KU σ n) → ∃ α, HasSatU ϖ q ρ α := by
  intro E _ _ w ϖ σ q n hU V _ _ ρ hi ha hs
  obtain ⟨ho, hc⟩ := GlobalTheory.T.isOpen_isCompact_unitaryIntegralPoints (w.adicCompletion E) ϖ σ q n hU
  exact GlobalTheory.LFun.SatCompare.exists_hasSatU hU ⟨ha.1, hi⟩ (ha.2 _ ho hc) hs

end GlobalTheory.LFun.ExSatU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParameterSphericalUnramifiedUnitaryStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satake_parameter_spherical_unramifiedUnitary : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (ϖ : w.adicCompletion E) (σ : w.adicCompletion E →+* w.adicCompletion E) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V), ρ.IsIrreducible → IsAdmissible ρ → GlobalTheory.LGrp.IsSpherical ρ (KU σ n) → ∃ α, HasSatU ϖ q ρ α := by
  first | exact @GlobalTheory.LFun.ExSatU.exists_hasSatU | exact GlobalTheory.LFun.ExSatU.exists_hasSatU | (intros; apply GlobalTheory.LFun.ExSatU.exists_hasSatU <;> assumption)
end
end
