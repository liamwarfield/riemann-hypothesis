module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VolumePeriodProjectionSetEqFamilyLevel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHaarVolumeOfConjugateLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCosetProjectionVolumeConstMul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCosetProjectionVolumeConstMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

noncomputable section

namespace GlobalTheory.CellLevel

variable {D : D7}

theorem finE_range_eq (V : HSp D) : ((Lev.finE V).comp (GfC V).subtype).range = (Lev.finE V).range := by
  refine le_antisymm (fun y ⟨g, hg⟩ => ⟨g.1, hg⟩) ?_
  rintro _ ⟨g, rfl⟩
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g)
  refine ⟨⟨k, MonoidHom.mem_ker.2 k1⟩, ?_⟩
  show Formalism.UG.bc (Lev.swapAE D) (finHom V k) = Formalism.UG.bc (Lev.swapAE D) (finHom V g)
  rw [k2]

theorem relIndex_comap_fin (V : HSp D) (K K' : Subgroup (GL (Fin V.rank) (Lev.EAf D))) :
    (K.comap ((Lev.finE V).comp (GfC V).subtype)).relIndex (K'.comap ((Lev.finE V).comp (GfC V).subtype)) =
      (K.comap (Lev.finE V)).relIndex (K'.comap (Lev.finE V)) := by
  rw [Subgroup.relIndex_comap, Subgroup.relIndex_comap, Subgroup.map_comap_eq, Subgroup.map_comap_eq,
    finE_range_eq]

theorem isCompact_comap_fin (V : HSp D) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))} (h : IsCO V K) :
    IsCompact ((K.comap ((Lev.finE V).comp (GfC V).subtype) : Subgroup (GfC V)) : Set (GfC V)) := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  convert h.2 using 1
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact Lev.mem_levA.2 ⟨g.2, hg⟩
  · intro hy
    obtain ⟨h1, h2⟩ := Lev.mem_levA.1 hy
    exact ⟨⟨y, h1⟩, h2, rfl⟩

theorem isOpen_comap_fin (V : HSp D) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    (h : IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))) :
    IsOpen ((K.comap ((Lev.finE V).comp (GfC V).subtype) : Subgroup (GfC V)) : Set (GfC V)) :=
  h.preimage continuous_subtype_val

theorem relIndex_ne_zero (V : HSp D) {K K₃ : Subgroup (GL (Fin V.rank) (Lev.EAf D))} (h : IsCO V K)
    (h₃ : IsOpen ((K₃.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))) :
    (K₃.comap ((Lev.finE V).comp (GfC V).subtype)).relIndex (K.comap ((Lev.finE V).comp (GfC V).subtype)) ≠ 0 := by
  have := GlobalTheory.LocVec.finiteIndex_of_isOpen (K.comap ((Lev.finE V).comp (GfC V).subtype)) (isCompact_comap_fin V h) subset_rfl
    ((K₃.comap ((Lev.finE V).comp (GfC V).subtype)).subgroupOf (K.comap ((Lev.finE V).comp (GfC V).subtype)))
    ((isOpen_comap_fin V h₃).preimage continuous_subtype_val)
  exact this.index_ne_zero

theorem vol_ratio (V : HSp D) {K₁ K₂ : Subgroup (GL (Fin V.rank) (Lev.EAf D))} (h₁ : IsCO V K₁) (h₂ : IsCO V K₂)
    (ν : Measure (GfC V)) [ν.IsHaarMeasure] {μ μ' : Measure (GA D V)} (hμ : Lev.IsMeasLevDef V K₁ μ)
    (hμ' : Lev.IsMeasLevDef V K₂ μ') (x : ℝ≥0) (hx : μ = x • μ') :
    ν {g | Lev.finE V g.1 ∈ K₂} = ν {g | Lev.finE V g.1 ∈ K₁} * x := by
  obtain ⟨hLC, hSC, hT2, hB, hTG, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB; haveI := hTG
  haveI : μ.IsHaarMeasure := hμ.1
  have h₃ : IsOpen (((K₁ ⊓ K₂).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := h₁.1.inter h₂.1
  have hA₁ : μ (K₁.comap (Lev.finE V)) = 1 := GlobalTheory.Mass.Levels.measure_comap_finE hμ
  have hA₂ : μ (K₂.comap (Lev.finE V)) = x := by
    rw [hx, Measure.smul_apply, GlobalTheory.Mass.Levels.measure_comap_finE hμ', ENNReal.smul_def, smul_eq_mul, mul_one]
  have n₁ := relIndex_ne_zero V h₁ h₃
  have n₂ := relIndex_ne_zero V h₂ h₃
  rw [relIndex_comap_fin] at n₁ n₂
  haveI : (((K₁ ⊓ K₂).comap (Lev.finE V)).subgroupOf (K₁.comap (Lev.finE V))).FiniteIndex := ⟨n₁⟩
  haveI : (((K₁ ⊓ K₂).comap (Lev.finE V)).subgroupOf (K₂.comap (Lev.finE V))).FiniteIndex := ⟨n₂⟩
  have e₁ := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ (Subgroup.comap_mono inf_le_left) h₃.measurableSet μ
  have e₂ := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ (Subgroup.comap_mono inf_le_right) h₃.measurableSet μ
  rw [hA₁] at e₁
  rw [hA₂] at e₂
  have m₁ := relIndex_ne_zero V h₁ h₃
  have m₂ := relIndex_ne_zero V h₂ h₃
  haveI : ((((K₁ ⊓ K₂).comap ((Lev.finE V).comp (GfC V).subtype))).subgroupOf
    (K₁.comap ((Lev.finE V).comp (GfC V).subtype))).FiniteIndex := ⟨m₁⟩
  haveI : ((((K₁ ⊓ K₂).comap ((Lev.finE V).comp (GfC V).subtype))).subgroupOf
    (K₂.comap ((Lev.finE V).comp (GfC V).subtype))).FiniteIndex := ⟨m₂⟩
  have f₁ := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ (Subgroup.comap_mono inf_le_left)
    (isOpen_comap_fin V h₃).measurableSet ν
  have f₂ := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ (Subgroup.comap_mono inf_le_right)
    (isOpen_comap_fin V h₃).measurableSet ν
  rw [relIndex_comap_fin] at f₁ f₂
  change ν (K₂.comap ((Lev.finE V).comp (GfC V).subtype)) = ν (K₁.comap ((Lev.finE V).comp (GfC V).subtype)) * x
  rw [← f₁, ← f₂]
  have key : ∀ (p q a m X : ENNReal), p * m = 1 → q * m = X → q * a = p * a * X := by
    intro p q a m X h1 h2
    rw [← h2, ← mul_one (q * a), ← h1]
    ring
  exact key _ _ _ _ _ e₁ e₂

theorem vol_pos (V : HSp D) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))} (h : IsCO V K)
    (ν : Measure (GfC V)) [ν.IsHaarMeasure] : 0 < ν.real {g | Lev.finE V g.1 ∈ K} := by
  obtain ⟨hLC, hSC, hT2, hB, hTG, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB; haveI := hTG
  refine ENNReal.toReal_pos ?_ ?_
  · exact ((isOpen_comap_fin V h.1).measure_pos ν ⟨1, one_mem _⟩).ne'
  · exact ((isCompact_comap_fin V h).measure_lt_top).ne

end GlobalTheory.CellLevel

namespace GlobalTheory.CellLevel

theorem pr_vol_of (hpr : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D, ∀ (hj : j < D.R.m) (ν : Measure (GfC (ch.G.V (.top j)))),
    ν.IsHaarMeasure → ∃ c : ℝ, 0 < c ∧ ∀ t Φ β b, IsRep t ch.S.B s β b → ∀ hb : b j ∈ GfC _,
      ν.real (prSet ch.G j ⟨b j, hb⟩) = c * ν.real {g | Lev.finE (ch.G.V (.top j)) g.1 ∈ ch.S.toGridChoice.levTop t Φ β j hj}) : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D, ∀ ν : Measure (GfC (ch.G.V (.top j))), ν.IsHaarMeasure →
    ∃ κ' : ℝ, 0 < κ' ∧ ∀ t Φ β b, IsRep t ch.S.B s β b → ∀ M M' : Vol ch.G, M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' →
      ∀ x : ℝ≥0, M.ν (.top j) = x • M'.ν (.top j) → ∀ hb : b j ∈ GfC _, ν.real (prSet ch.G j ⟨b j, hb⟩) = κ' * x := by
  refine big_mono ?_ hpr
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch h s j hj ν hν
  have hjm : j < D.R.m := by
    simp only [idx, List.mem_range'_1] at hj
    omega
  have hj1 : 1 ≤ j := by
    simp only [idx, List.mem_range'_1] at hj
    omega
  obtain ⟨c, hc, hcb⟩ := h s j hj hjm ν hν
  have hMax : IsCO (ch.G.V (.top j)) (ch.G.levMax (.top j)) :=
    congLev_open_compact _ (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _
      (ch.G.isV (X := .top j) (show j ≤ D.R.m by omega) (fun _ h => Node.noConfusion h)).sd)
      (by simp)
  refine ⟨c * ν.real {g | Lev.finE (ch.G.V (.top j)) g.1 ∈ ch.G.levMax (.top j)}, mul_pos hc (vol_pos _ hMax ν), ?_⟩
  intro t Φ β b hb M M' hM hM' x hx hbj
  rw [hcb t Φ β b hb hbj]
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have h1 : Lev.IsMeasLevDef _ (ch.G.levMax (.top (j' + 1))) (M.ν (.top (j' + 1))) := by
    have := hM.vtx (.top (j' + 1)) (show j' + 1 ≤ D.R.m by omega)
    unfold Vol.IsAt at this
    rw [if_pos (show Node.neg D.R.m (.top (j' + 1)) = 0 from rfl)] at this
    exact this.1
  have h2 : Lev.IsMeasLevDef _ (ch.S.toGridChoice.levTop t Φ β (j' + 1) hjm) (M'.ν (.top (j' + 1))) := by
    have := hM'.1 (j' + 1) hjm
    unfold Vol.IsAt at this
    rw [if_pos (show Node.neg D.R.m (.top (j' + 1)) = 0 from rfl)] at this
    exact this.1
  have e := vol_ratio _ hMax (GridChoice.isCO_levTop _ _ t Φ β hjm) ν h1 h2 x hx
  simp only [Measure.real, e, ENNReal.toReal_mul, ENNReal.coe_toReal, mul_assoc]

end GlobalTheory.CellLevel

namespace GlobalTheory.CellLevel

theorem pr_vol : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D, ∀ ν : Measure (GfC (ch.G.V (.top j))), ν.IsHaarMeasure →
    ∃ κ' : ℝ, 0 < κ' ∧ ∀ t Φ β b, IsRep t ch.S.B s β b → ∀ M M' : Vol ch.G, M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' →
      ∀ x : ℝ≥0, M.ν (.top j) = x • M'.ν (.top j) → ∀ hb : b j ∈ GfC _, ν.real (prSet ch.G j ⟨b j, hb⟩) = κ' * x := pr_vol_of GlobalTheory.T.volume_periodProjectionSet_eq_familyLevel

end GlobalTheory.CellLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCosetProjectionVolumeConstMulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCosetProjection_volume_const_mul : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D, ∀ ν : Measure (GfC (ch.G.V (.top j))), ν.IsHaarMeasure →
    ∃ κ' : ℝ, 0 < κ' ∧ ∀ t Φ β b, IsRep t ch.S.B s β b → ∀ M M' : Vol ch.G, M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' →
      ∀ x : ℝ≥0, M.ν (.top j) = x • M'.ν (.top j) → ∀ hb : b j ∈ GfC _, ν.real (prSet ch.G j ⟨b j, hb⟩) = κ' * x := by
  first | exact @GlobalTheory.CellLevel.pr_vol | exact GlobalTheory.CellLevel.pr_vol | (intros; apply GlobalTheory.CellLevel.pr_vol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePointsRowPeriodConjLevelFubini
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodSubgroupFinitePointsSemidirect
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodSubgroupFinitePointsSemidirect
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

noncomputable section

namespace GlobalTheory.RowGrpSemi

theorem finite_split {X Y : Type} [Group X] [TopologicalSpace X] [Group Y] [TopologicalSpace Y]
    (Xf : Subgroup X) (Yf : Subgroup Y) (N R K : Subgroup X) (s : Y →* X) (p : R → Y)
    (hR : R = N ⊔ s.range) (hconj : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) (hs : Continuous s) (hp : Continuous p)
    (hpn : ∀ n ∈ N, ∀ h (hm : n * s h ∈ R), p ⟨n * s h, hm⟩ = h) (hsf : ∀ y ∈ Yf, s y ∈ Xf)
    (hkey : ∀ n ∈ N, ∀ h, n * s h ∈ Xf → h ∈ Yf) (hK : K ≤ Xf) :
    ∃ (π : R.subgroupOf Xf →* Yf) (σ : Yf →* R.subgroupOf Xf),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ N.subgroupOf Xf) ∧
      ∀ b : Xf, {g : Yf | ∃ n ∈ N, (b.1)⁻¹ * (n * s g.1) * b.1 ∈ K} = π '' {r | b⁻¹ * r.1 * b ∈ K.subgroupOf Xf} := by

  have hnorm : s.range ≤ Subgroup.normalizer (N : Set X) := by
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hconj n hn y, fun hn => ?_⟩
    have := hconj _ hn y⁻¹
    have e : s y⁻¹ * (s y * n * (s y)⁻¹) * (s y⁻¹)⁻¹ = n := by rw [map_inv]; group
    rwa [e] at this
  have hdec : ∀ x ∈ R, ∃ n ∈ N, ∃ h, x = n * s h := by
    intro x hx
    rw [hR, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N s.range hnorm] at hx
    obtain ⟨n, hn, _, ⟨h, rfl⟩, e⟩ := hx
    exact ⟨n, hn, h, e.symm⟩
  have hmemR : ∀ n ∈ N, ∀ h, n * s h ∈ R := fun n hn h => by
    rw [hR]; exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)
  have hpeq : ∀ x y (hx : x ∈ R) (hy : y ∈ R), x = y → p ⟨x, hx⟩ = p ⟨y, hy⟩ := by
    rintro x _ hx hy rfl; rfl
  have hval : ∀ x (hx : x ∈ R), ∃ n ∈ N, x = n * s (p ⟨x, hx⟩) := by
    intro x hx
    obtain ⟨n, hn, h, rfl⟩ := hdec x hx
    exact ⟨n, hn, by rw [hpn n hn h hx]⟩
  have hpmul : ∀ x y (hx : x ∈ R) (hy : y ∈ R) (hxy : x * y ∈ R), p ⟨x * y, hxy⟩ = p ⟨x, hx⟩ * p ⟨y, hy⟩ := by
    intro x y hx hy hxy
    obtain ⟨n, hn, h, rfl⟩ := hdec x hx
    obtain ⟨n', hn', h', rfl⟩ := hdec y hy
    have e : n * s h * (n' * s h') = (n * (s h * n' * (s h)⁻¹)) * s (h * h') := by rw [map_mul]; group
    rw [hpeq _ _ hxy (hmemR _ (mul_mem hn (hconj n' hn' h)) _) e, hpn _ (mul_mem hn (hconj n' hn' h)),
      hpn n hn h, hpn n' hn' h']
  have hp1 : ∀ (h1 : (1 : X) ∈ R), p ⟨1, h1⟩ = 1 := by
    intro h1
    rw [hpeq 1 (1 * s 1) h1 (hmemR 1 N.one_mem 1) (by rw [map_one, one_mul]), hpn 1 N.one_mem 1]
  have hfin : ∀ x (hx : x ∈ R), x ∈ Xf → p ⟨x, hx⟩ ∈ Yf := by
    intro x hx hxf
    obtain ⟨n, hn, e⟩ := hval x hx
    exact hkey n hn _ (e ▸ hxf)
  have hRf : ∀ r : R.subgroupOf Xf, r.1.1 ∈ R := fun r => Subgroup.mem_subgroupOf.1 r.2
  let π : R.subgroupOf Xf →* Yf :=
    { toFun := fun r => ⟨p ⟨r.1.1, hRf r⟩, hfin _ _ r.1.2⟩
      map_one' := Subtype.ext (hp1 _)
      map_mul' := fun r r' => Subtype.ext (hpmul _ _ (hRf r) (hRf r') (hRf (r * r'))) }
  have hsR : ∀ y, s y ∈ R := fun y => by rw [hR]; exact Subgroup.mem_sup_right ⟨y, rfl⟩
  let σ : Yf →* R.subgroupOf Xf :=
    { toFun := fun y => ⟨⟨s y.1, hsf _ y.2⟩, Subgroup.mem_subgroupOf.2 (hsR _)⟩
      map_one' := Subtype.ext (Subtype.ext (map_one s))
      map_mul' := fun y y' => Subtype.ext (Subtype.ext (map_mul s _ _)) }
  have hπ : ∀ r, (π r).1 = p ⟨r.1.1, hRf r⟩ := fun r => rfl
  refine ⟨π, σ, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hp.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)).subtype_mk _
  · exact ((hs.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  · intro y
    apply Subtype.ext
    rw [hπ]
    exact (hpeq _ (1 * s y.1) _ (hmemR 1 N.one_mem _) (one_mul _).symm).trans (hpn 1 N.one_mem _ _)
  · intro r
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h1' : p ⟨r.1.1, hRf r⟩ = 1 := by rw [← hπ, h1]; rfl
      obtain ⟨n, hn, e⟩ := hval _ (hRf r)
      rw [h1', map_one, mul_one] at e
      exact e ▸ hn
    · intro hn
      apply Subtype.ext
      rw [hπ]
      exact (hpeq _ (r.1.1 * s 1) _ (hmemR _ hn 1) (by rw [map_one, mul_one])).trans (hpn _ hn 1 _)
  · intro b
    ext g
    constructor
    · rintro ⟨n, hn, hk⟩
      have hxf : n * s g.1 ∈ Xf := by
        have e : n * s g.1 = b.1 * ((b.1)⁻¹ * (n * s g.1) * b.1) * (b.1)⁻¹ := by group
        rw [e]
        exact mul_mem (mul_mem b.2 (hK hk)) (inv_mem b.2)
      refine ⟨⟨⟨n * s g.1, hxf⟩, Subgroup.mem_subgroupOf.2 (hmemR n hn _)⟩, ?_, ?_⟩
      · show ((b⁻¹ * ⟨n * s g.1, hxf⟩ * b : Xf) : X) ∈ K
        exact hk
      · apply Subtype.ext
        rw [hπ]
        exact hpn n hn _ _
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨n, hn, e⟩ := hval _ (hRf r)
      refine ⟨n, hn, ?_⟩
      rw [hπ, ← e]
      exact hr

end GlobalTheory.RowGrpSemi

namespace GlobalTheory.RowGrpSemi

open GlobalTheory.Core.Mi

theorem key_jac {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {n : GA D S} (hn : n ∈ flagN d) (h : GA D S₀)
    (hf : n * d.emb0 h ∈ GfC S) : h ∈ GfC S₀ := by
  rw [CenAct.mem_GfC_iff] at hf ⊢
  have := GlobalTheory.LevNorm.finf_sand d.p0 _ d.j0 hf d.p0_j0
  rwa [GlobalTheory.JacProj.witt_anisotropic_block_flag_mul_embedded d hn h] at this

theorem jac_case {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (N R K : Subgroup (GA D S)) (s : GA D S₀ →* GA D S)
    (hN : N = flagN d) (hs : s = d.emb0) (hR : R = N ⊔ s.range) (hK : K ≤ GfC S) :
    ∃ (π : R.subgroupOf (GfC S) →* GfC S₀) (σ : GfC S₀ →* R.subgroupOf (GfC S)),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ N.subgroupOf (GfC S)) ∧
      ∀ b : GfC S, {g : GfC S₀ | ∃ n ∈ N, (b.1)⁻¹ * (n * s g.1) * b.1 ∈ K} =
        π '' {r | b⁻¹ * r.1 * b ∈ K.subgroupOf (GfC S)} := by
  subst hN hs hR
  exact finite_split (GfC S) (GfC S₀) (flagN d) _ K d.emb0 (GlobalTheory.JacProj.proj d) rfl
    (fun n hn h => GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn h) d.continuous_embed (GlobalTheory.JacProj.continuous_proj d)
    (fun n hn h _ => GlobalTheory.JacProj.proj_mul d h ⟨n, hn⟩) (fun y hy => CenAct.witt_embedding_mem_finite_unitary_points d hy)
    (fun n hn h hf => key_jac d hn h hf) hK

theorem bes_case {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (N R K : Subgroup (GA D S))
    (s : GA D A →* GA D S) (hN : N = flagN d) (hs : s = embA d o) (hR : R = N ⊔ s.range) (hK : K ≤ GfC S) :
    ∃ (π : R.subgroupOf (GfC S) →* GfC A) (σ : GfC A →* R.subgroupOf (GfC S)),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ N.subgroupOf (GfC S)) ∧
      ∀ b : GfC S, {g : GfC A | ∃ n ∈ N, (b.1)⁻¹ * (n * s g.1) * b.1 ∈ K} =
        π '' {r | b⁻¹ * r.1 * b ∈ K.subgroupOf (GfC S)} := by
  subst hN hs hR
  obtain ⟨p, hp, hpn⟩ := GlobalTheory.BesProj.exists_continuous_proj D S S₀ A L ρ d o
  refine finite_split (GfC S) (GfC A) (flagN d) _ K (embA d o) p rfl (fun n hn h => ?_)
    (d.continuous_embed.comp (o.continuous_emb.comp (continuous_id.prodMk continuous_const))) hp (fun n hn h _ => hpn h ⟨n, hn⟩) (fun y hy => CenAct.embA_mem_GfC d o hy)
    (fun n hn h hf => ?_) hK
  · rw [embA_apply]
    exact GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn _
  · rw [embA_apply] at hf
    have h0 := key_jac d hn _ hf
    have h1 : embA d o h ∈ GfC S := by rw [embA_apply]; exact CenAct.witt_embedding_mem_finite_unitary_points d h0
    exact GlobalTheory.LevNorm.mem_GfC_of_embA d o h1

end GlobalTheory.RowGrpSemi

namespace GlobalTheory.CellMass

theorem rowGrp_finite_semidirect : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R), ∀ j ∈ idx D,
    IsClosed (((rowGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    IsClosed (((rowN ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    (rowN ch.G j).subgroupOf (GfC _) ≤ (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))) ∧
    IsOpen (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    IsCompact (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    ∃ (π : (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))) →* GfC (ch.G.V (.top j)))
      (σ : GfC (ch.G.V (.top j)) →* (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ (rowN ch.G j).subgroupOf (GfC _)) ∧
      ∀ b : GfC (ch.G.V (.grid D.R.m j)), prSet ch.G j b = π '' {r | b⁻¹ * r.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch j hj
  have hj' := List.mem_range'_1.1 hj
  have sp := GlobalTheory.RowGrpSplit.grpAt_all ch j hj
  have hNfl : ∃ (S₀ : HSp D) (ρ : ℕ) (d : HypDec (ch.G.V (.grid D.R.m j)) S₀ ρ), rowN ch.G j = flagN d := by
    by_cases h1 : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m
    · exact ⟨_, _, _, by unfold rowN; rw [dite_eq_left h1]⟩
    · have h2 : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m := by omega
      exact ⟨_, _, _, by unfold rowN; rw [dite_eq_right h1, dite_eq_left h2]⟩
  have hNc : IsClosed ((rowN ch.G j : Subgroup (GA D (ch.G.V (.grid D.R.m j)))) : Set (GA D (ch.G.V (.grid D.R.m j)))) := by
    obtain ⟨S₀, ρ, d, e⟩ := hNfl
    rw [e]
    exact GlobalTheory.Mem.TrueRecord.isClosed_NFlag _ (isIsoSub_e d)
  refine ⟨?_, ?_, ?_, sp.opn, ?_, ?_⟩
  · rw [Subgroup.coe_subgroupOf]
    exact sp.clR.preimage continuous_subtype_val
  · rw [Subgroup.coe_subgroupOf]
    exact hNc.preimage continuous_subtype_val
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [rowGrp_eq]
    exact Subgroup.mem_sup_left hx
  · rw [Subgroup.coe_subgroupOf]
    exact sp.clB.isClosedEmbedding_subtypeVal.isCompact_preimage sp.cpt
  · by_cases h1 : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m
    · exact GlobalTheory.RowGrpSemi.jac_case (rowJac ch.G j (by omega) ((D.R.m - 1 - j) / 2) (by omega)) _ _ _ _
        (by unfold rowN; rw [dite_eq_left h1]) (by unfold rowEmb; rw [dite_eq_left h1]) (rowGrp_eq ch.G j) sp.le
    · have h2 : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m := by omega
      exact GlobalTheory.RowGrpSemi.bes_case (besDecAt ch.G j _ h2) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) _ _ _ _
        (by unfold rowN; rw [dite_eq_right h1, dite_eq_left h2]) (by unfold rowEmb; rw [dite_eq_right h1, dite_eq_left h2]) (rowGrp_eq ch.G j) sp.le

end GlobalTheory.CellMass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodSubgroupFinitePointsSemidirectStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowPeriodSubgroup_finitePoints_semidirect : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R), ∀ j ∈ idx D,
    IsClosed (((rowGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    IsClosed (((rowN ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    (rowN ch.G j).subgroupOf (GfC _) ≤ (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))) ∧
    IsOpen (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    IsCompact (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    ∃ (π : (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))) →* GfC (ch.G.V (.top j)))
      (σ : GfC (ch.G.V (.top j)) →* (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ (rowN ch.G j).subgroupOf (GfC _)) ∧
      ∀ b : GfC (ch.G.V (.grid D.R.m j)), prSet ch.G j b = π '' {r | b⁻¹ * r.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} := by
  first | exact @GlobalTheory.CellMass.rowGrp_finite_semidirect | exact GlobalTheory.CellMass.rowGrp_finite_semidirect | (intros; apply GlobalTheory.CellMass.rowGrp_finite_semidirect <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarTraceConjEqConstMulKernelImage
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarTraceConjEqConstMulKernelImage
open MeasureTheory
open scoped Pointwise ENNReal

namespace GlobalTheory.RowFubini

theorem relIndex_eq_of_le_of_cover {G : Type*} [Group G] (H s t : Subgroup G) (hst : s ≤ t)
    (hcov : ∀ g ∈ t, ∃ a ∈ s, a⁻¹ * g ∈ H) : H.relIndex s = H.relIndex t := by
  unfold Subgroup.relIndex Subgroup.index
  refine Nat.card_congr (Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE H hst)
    ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE H hst).injective, ?_⟩)
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨a, ha, hg⟩ := hcov g g.2
    refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
    rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa using hg

theorem relIndex_split {G Y : Type*} [Group G] [Group Y] (π : G →* Y) (A B : Subgroup G)
    (hBA : B ≤ A) :
    B.relIndex A = B.relIndex (A ⊓ π.ker) * (B.map π).relIndex (A.map π) := by
  set S := (B ⊔ π.ker) ⊓ A with hS
  have hBS : B ≤ S := le_inf le_sup_left hBA
  have hSA : S ≤ A := inf_le_right
  have h1 : B.relIndex A = B.relIndex S * S.relIndex A :=
    (Subgroup.relIndex_mul_relIndex B S A hBS hSA).symm
  have h2 : S.relIndex A = (B.map π).relIndex (A.map π) := by
    rw [Subgroup.relIndex_map_map, hS, Subgroup.inf_relIndex_right]
    refine relIndex_eq_of_le_of_cover _ _ _ le_sup_left ?_
    intro g hg
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hg
    obtain ⟨a, ha, n, hn, rfl⟩ := hg
    exact ⟨a, ha, by simpa using (le_sup_right : π.ker ≤ B ⊔ π.ker) hn⟩
  have h3 : B.relIndex S = B.relIndex (A ⊓ π.ker) := by
    refine (relIndex_eq_of_le_of_cover _ _ _ ?_ ?_).symm
    · exact le_inf (inf_le_right.trans le_sup_right) inf_le_left
    · intro g hg
      have hgA : g ∈ A := hg.2
      have hg1 : g ∈ π.ker ⊔ B := sup_comm B π.ker ▸ hg.1
      rw [← SetLike.mem_coe, Subgroup.normal_mul] at hg1
      obtain ⟨m, hm, b, hb, rfl⟩ := hg1
      refine ⟨m, ⟨?_, hm⟩, by simpa using hb⟩
      have : m = (m * b) * b⁻¹ := by group
      rw [this]
      exact A.mul_mem hgA (A.inv_mem (hBA hb))
  rw [h1, h2, h3]

end GlobalTheory.RowFubini

namespace GlobalTheory.RowFubini

section Meas

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]

theorem finiteIndex_subgroupOf (H L : Subgroup G) (hH : IsOpen (H : Set G))
    (hL : IsCompact (L : Set G)) : (H.subgroupOf L).FiniteIndex := by
  have : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have ho : IsOpen ((H.subgroupOf L : Subgroup L) : Set L) :=
    hH.preimage continuous_subtype_val
  have : Finite (L ⧸ H.subgroupOf L) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.finiteIndex_of_finite_quotient

theorem measure_eq_relIndex_mul (μ : Measure G) [μ.IsMulLeftInvariant] (H L : Subgroup G)
    (hHL : H ≤ L) (hH : IsOpen (H : Set G)) (hL : IsCompact (L : Set G)) :
    μ L = (H.relIndex L : ℝ≥0∞) * μ H := by
  have := finiteIndex_subgroupOf H L hH hL
  obtain ⟨s, hs, -⟩ := (H.subgroupOf L).exists_isComplement_left 1
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  have hU : (⋃ a : s, (a.val : L) • (H : Set G)) = (L : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_smul_set, SetLike.mem_coe]
    constructor
    · rintro ⟨a, h, hh, rfl⟩
      exact L.mul_mem a.val.2 (hHL hh)
    · intro hx
      obtain ⟨⟨b, h⟩, hbh, -⟩ := hs.existsUnique ⟨x, hx⟩
      refine ⟨b, (h.val : G), Subgroup.mem_subgroupOf.mp h.2, ?_⟩
      have := congrArg Subtype.val hbh
      exact this
  have hdisj : Pairwise (Function.onFun Disjoint fun a : s => (a.val : L) • (H : Set G)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨h1, hh1, rfl⟩ ⟨h2, hh2, he⟩
    apply hab
    have hh1' : (⟨h1, hHL hh1⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh1
    have hh2' : (⟨h2, hHL hh2⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh2
    have e : (a.val : L) * ⟨h1, hHL hh1⟩ = (b.val : L) * ⟨h2, hHL hh2⟩ := Subtype.ext he.symm
    have := (hs.existsUnique ((a.val : L) * ⟨h1, hHL hh1⟩)).unique
      (y₁ := (a, ⟨_, hh1'⟩)) (y₂ := (b, ⟨_, hh2'⟩)) rfl e.symm
    exact congrArg Prod.fst this
  have hHm : MeasurableSet (H : Set G) := hH.measurableSet
  symm
  calc (H.relIndex L : ℝ≥0∞) * μ H = ∑' a : s, μ ((a.val : L) • (H : Set G)) := by
        simp [measure_smul, hs.encard_left, Subgroup.relIndex]
    _ = μ (⋃ a : s, (a.val : L) • (H : Set G)) :=
        (measure_iUnion hdisj fun a => hHm.const_smul _).symm
    _ = μ L := by rw [hU]

theorem measure_pos_lt_top (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (hc : IsCompact (H : Set G)) : 0 < μ H ∧ μ H < ∞ :=
  ⟨hH.measure_pos μ ⟨1, H.one_mem⟩, hc.measure_lt_top⟩

end Meas

end GlobalTheory.RowFubini

namespace GlobalTheory.RowFubini

section Top

variable {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]

theorem comap_open_compact (R Q : Subgroup X) (hR : IsClosed (R : Set X))
    (hQo : IsOpen (Q : Set X)) (hQc : IsCompact (Q : Set X)) :
    IsOpen ((Q.comap R.subtype : Subgroup R) : Set R) ∧
      IsCompact ((Q.comap R.subtype : Subgroup R) : Set R) :=
  ⟨hQo.preimage continuous_subtype_val, hR.isClosedEmbedding_subtypeVal.isCompact_preimage hQc⟩

theorem map_open_compact {Y : Type*} [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    (A : Subgroup X) (π : X →* Y) (σ : Y →* X) (hπ : Continuous π) (hσ : Continuous σ)
    (hsec : ∀ y, π (σ y) = y) (hAo : IsOpen (A : Set X)) (hAc : IsCompact (A : Set X)) :
    IsOpen ((A.map π : Subgroup Y) : Set Y) ∧ IsCompact ((A.map π : Subgroup Y) : Set Y) := by
  refine ⟨Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_, ?_⟩
  · refine Filter.mem_of_superset ((hAo.preimage hσ).mem_nhds ?_) ?_
    · simp [A.one_mem]
    · intro y hy
      exact Subgroup.mem_map.mpr ⟨σ y, hy, hsec y⟩
  · rw [Subgroup.coe_map]
    exact hAc.image hπ

def conjSub (K : Subgroup X) (b : X) : Subgroup X := K.comap (MulAut.conj b⁻¹).toMonoidHom

omit [TopologicalSpace X] [IsTopologicalGroup X] in
theorem mem_conjSub (K : Subgroup X) (b x : X) : x ∈ conjSub K b ↔ b⁻¹ * x * b ∈ K := by
  simp [conjSub]

theorem conjSub_open_compact (K : Subgroup X) (b : X) (hKo : IsOpen (K : Set X))
    (hKc : IsCompact (K : Set X)) :
    IsOpen (conjSub K b : Set X) ∧ IsCompact (conjSub K b : Set X) := by
  let h : X ≃ₜ X := (Homeomorph.mulLeft b⁻¹).trans (Homeomorph.mulRight b)
  have e : (conjSub K b : Set X) = h ⁻¹' (K : Set X) := by
    ext x; simp [h, mem_conjSub]
  rw [e]
  exact ⟨hKo.preimage h.continuous, h.isCompact_preimage.mpr hKc⟩

end Top

end GlobalTheory.RowFubini

namespace GlobalTheory.RowFubini

theorem cross_identity {X Y : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [MeasurableSpace X] [BorelSpace X]
    [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [MeasurableSpace Y] [BorelSpace Y]
    (R N : Subgroup X) (π : R →* Y) (σ : Y →* R)
    (hR : IsClosed (R : Set X)) (hN : IsClosed (N : Set X)) (hNR : N ≤ R)
    (hπ : Continuous π) (hσ : Continuous σ) (hsec : ∀ y, π (σ y) = y)
    (hker : ∀ r : R, π r = 1 ↔ r.1 ∈ N)
    (ρ : Measure R) [ρ.IsMulLeftInvariant] (la : Measure N) [la.IsMulLeftInvariant]
    (ν : Measure Y) [ν.IsMulLeftInvariant] (Q₁ Q₂ : Subgroup X) (h12 : Q₁ ≤ Q₂)
    (h1o : IsOpen (Q₁ : Set X)) (h1c : IsCompact (Q₁ : Set X))
    (h2o : IsOpen (Q₂ : Set X)) (h2c : IsCompact (Q₂ : Set X)) :
    ρ.real (Q₂.comap R.subtype) * la.real (Q₁.comap N.subtype) *
        ν.real ((Q₁.comap R.subtype).map π) =
      ρ.real (Q₁.comap R.subtype) * la.real (Q₂.comap N.subtype) *
        ν.real ((Q₂.comap R.subtype).map π) := by
  obtain ⟨a1o, a1c⟩ := comap_open_compact R Q₁ hR h1o h1c
  obtain ⟨a2o, a2c⟩ := comap_open_compact R Q₂ hR h2o h2c
  obtain ⟨n1o, -⟩ := comap_open_compact N Q₁ hN h1o h1c
  obtain ⟨-, n2c⟩ := comap_open_compact N Q₂ hN h2o h2c
  obtain ⟨p1o, -⟩ := map_open_compact _ π σ hπ hσ hsec a1o a1c
  obtain ⟨-, p2c⟩ := map_open_compact _ π σ hπ hσ hsec a2o a2c
  have hA : Q₁.comap R.subtype ≤ Q₂.comap R.subtype := Subgroup.comap_mono h12
  have ea := measure_eq_relIndex_mul ρ _ _ hA a1o a2c
  have en := measure_eq_relIndex_mul la _ _ (Subgroup.comap_mono h12) n1o n2c
  have ep := measure_eq_relIndex_mul ν _ _ (Subgroup.map_mono hA) p1o p2c
  have hmap : (Q₂.comap N.subtype).map (Subgroup.inclusion hNR) = Q₂.comap R.subtype ⊓ π.ker := by
    ext r
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨hn, (hker _).2 n.2⟩
    · rintro ⟨hq, hk⟩
      exact ⟨⟨r.1, (hker r).1 hk⟩, hq, rfl⟩
  have hidx : (Q₁.comap R.subtype).relIndex (Q₂.comap R.subtype ⊓ π.ker) =
      (Q₁.comap N.subtype).relIndex (Q₂.comap N.subtype) := by
    rw [← hmap, ← Subgroup.relIndex_comap]
    rfl
  have hs := relIndex_split π _ _ hA
  rw [hidx] at hs
  simp only [measureReal_def, ← ENNReal.toReal_mul]
  rw [ea, en, ep, hs]
  congr 1
  push_cast
  ring

theorem haar_trace_conj_eq : ∀ {X Y : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X] [BorelSpace X]
    [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [MeasurableSpace Y] [BorelSpace Y]
    (R N K : Subgroup X) (π : R →* Y) (σ : Y →* R),
    IsClosed (R : Set X) → IsClosed (N : Set X) → N ≤ R → IsOpen (K : Set X) → IsCompact (K : Set X) →
    Continuous π → Continuous σ → (∀ y, π (σ y) = y) → (∀ r : R, π r = 1 ↔ r.1 ∈ N) →
    ∀ ρ : Measure R, ρ.IsHaarMeasure →
    ∃ (κ : ℝ) (la : Measure N) (ν : Measure Y), 0 < κ ∧ la.IsHaarMeasure ∧ ν.IsHaarMeasure ∧ ∀ b : X,
      ρ.real {r : R | b⁻¹ * r.1 * b ∈ K} = κ * la.real {n : N | b⁻¹ * n.1 * b ∈ K} * ν.real (π '' {r : R | b⁻¹ * r.1 * b ∈ K}) := by
  intro X Y _ _ _ _ _ _ _ _ _ _ R N K π σ hR hN hNR hKo hKc hπ hσ hsec hker ρ hρ
  obtain ⟨aKo, aKc⟩ := comap_open_compact R K hR hKo hKc
  obtain ⟨nKo, nKc⟩ := comap_open_compact N K hN hKo hKc
  obtain ⟨pKo, pKc⟩ := map_open_compact _ π σ hπ hσ hsec aKo aKc
  let la : Measure N := Measure.haarMeasure ⟨⟨_, nKc⟩, by
    show (interior ((K.comap N.subtype : Subgroup N) : Set N)).Nonempty
    rw [nKo.interior_eq]; exact ⟨1, Subgroup.one_mem _⟩⟩
  let ν : Measure Y := Measure.haarMeasure ⟨⟨_, pKc⟩, by
    show (interior (((K.comap R.subtype).map π : Subgroup Y) : Set Y)).Nonempty
    rw [pKo.interior_eq]; exact ⟨1, Subgroup.one_mem _⟩⟩
  have hla : la.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hν : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have pos : ∀ Q : Subgroup X, IsOpen (Q : Set X) → IsCompact (Q : Set X) →
      0 < ρ.real (Q.comap R.subtype) ∧ 0 < la.real (Q.comap N.subtype) ∧
        0 < ν.real ((Q.comap R.subtype).map π) := by
    intro Q ho hc
    obtain ⟨ao, ac⟩ := comap_open_compact R Q hR ho hc
    obtain ⟨no, nc⟩ := comap_open_compact N Q hN ho hc
    obtain ⟨po, pc⟩ := map_open_compact _ π σ hπ hσ hsec ao ac
    obtain ⟨a1, a2⟩ := measure_pos_lt_top ρ _ ao ac
    obtain ⟨n1, n2⟩ := measure_pos_lt_top la _ no nc
    obtain ⟨p1, p2⟩ := measure_pos_lt_top ν _ po pc
    exact ⟨ENNReal.toReal_pos a1.ne' a2.ne, ENNReal.toReal_pos n1.ne' n2.ne,
      ENNReal.toReal_pos p1.ne' p2.ne⟩
  obtain ⟨aK, nK, pK⟩ := pos K hKo hKc
  refine ⟨ρ.real (K.comap R.subtype) /
    (la.real (K.comap N.subtype) * ν.real ((K.comap R.subtype).map π)), la, ν,
    div_pos aK (mul_pos nK pK), hla, hν, fun b => ?_⟩
  obtain ⟨hCo, hCc⟩ := conjSub_open_compact K b hKo hKc
  have hDo : IsOpen ((conjSub K b ⊓ K : Subgroup X) : Set X) := hCo.inter hKo
  have hDc : IsCompact ((conjSub K b ⊓ K : Subgroup X) : Set X) :=
    hCc.inter_right (K.isClosed_of_isOpen hKo)
  obtain ⟨-, nD, pD⟩ := pos _ hDo hDc
  have e1 := cross_identity R N π σ hR hN hNR hπ hσ hsec hker ρ la ν _ _ inf_le_left hDo hDc
    hCo hCc
  have e2 := cross_identity R N π σ hR hN hNR hπ hσ hsec hker ρ la ν _ _ inf_le_right hDo hDc
    hKo hKc
  have sR : {r : R | b⁻¹ * r.1 * b ∈ K} = ((conjSub K b).comap R.subtype : Subgroup R) := by
    ext r; exact (mem_conjSub K b r.1).symm
  have sN : {n : N | b⁻¹ * n.1 * b ∈ K} = ((conjSub K b).comap N.subtype : Subgroup N) := by
    ext n; exact (mem_conjSub K b n.1).symm
  rw [sR, sN, ← Subgroup.coe_map, div_mul_eq_mul_div, div_mul_eq_mul_div,
    eq_div_iff (mul_pos nK pK).ne']
  apply mul_right_cancel₀ (mul_pos nD pD).ne'
  linear_combination (la.real (K.comap N.subtype) * ν.real ((K.comap R.subtype).map π)) * e1 -
    (la.real ((conjSub K b).comap N.subtype) *
      ν.real (((conjSub K b).comap R.subtype).map π)) * e2

end GlobalTheory.RowFubini
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarTraceConjEqConstMulKernelImageStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_trace_conj_eq_const_mul_kernel_image : ∀ {X Y : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X] [BorelSpace X]
    [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [MeasurableSpace Y] [BorelSpace Y]
    (R N K : Subgroup X) (π : R →* Y) (σ : Y →* R),
    IsClosed (R : Set X) → IsClosed (N : Set X) → N ≤ R → IsOpen (K : Set X) → IsCompact (K : Set X) →
    Continuous π → Continuous σ → (∀ y, π (σ y) = y) → (∀ r : R, π r = 1 ↔ r.1 ∈ N) →
    ∀ ρ : Measure R, ρ.IsHaarMeasure →
    ∃ (κ : ℝ) (la : Measure N) (ν : Measure Y), 0 < κ ∧ la.IsHaarMeasure ∧ ν.IsHaarMeasure ∧ ∀ b : X,
      ρ.real {r : R | b⁻¹ * r.1 * b ∈ K} = κ * la.real {n : N | b⁻¹ * n.1 * b ∈ K} * ν.real (π '' {r : R | b⁻¹ * r.1 * b ∈ K}) := by
  first | exact @GlobalTheory.RowFubini.haar_trace_conj_eq | exact GlobalTheory.RowFubini.haar_trace_conj_eq | (intros; apply GlobalTheory.RowFubini.haar_trace_conj_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePointsRowPeriodConjLevelFubini
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

noncomputable section

namespace GlobalTheory.CellMass

theorem cell_fubini : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ j ∈ idx D,
    ∀ ρ : Measure ((rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))), ρ.IsHaarMeasure →
    ∃ (κ : ℝ) (la : Measure ((rowN ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))))) (ν : Measure (GfC (ch.G.V (.top j)))),
      0 < κ ∧ la.IsHaarMeasure ∧ ν.IsHaarMeasure ∧ ∀ b : GfC (ch.G.V (.grid D.R.m j)),
        ρ.real {r | b⁻¹ * r.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} =
          κ * la.real {n | b⁻¹ * n.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} * ν.real (prSet ch.G j b) := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => ?_⟩⟩
  intro j hj ρ hρ
  obtain ⟨-, -, -, h4, h5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (ch.G.V (.grid D.R.m j))
  obtain ⟨-, -, -, i4, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (ch.G.V (.top j))
  obtain ⟨c1, c2, c3, c4, c5, π, σ, hπ, hσ, hπσ, hker, hpr⟩ := GlobalTheory.T.rowPeriodSubgroup_finitePoints_semidirect ch j hj
  obtain ⟨κ, la, ν, hκ, hla, hν, h⟩ := GlobalTheory.T.haar_trace_conj_eq_const_mul_kernel_image _ _ _ π σ c1 c2 c3 c4 c5 hπ hσ hπσ hker ρ hρ
  exact ⟨κ, la, ν, hκ, hla, hν, fun b => by rw [hpr b]; exact h b⟩

end GlobalTheory.CellMass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePointsRowPeriodConjLevelFubiniStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePoints_rowPeriod_conjLevel_fubini : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ j ∈ idx D,
    ∀ ρ : Measure ((rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))), ρ.IsHaarMeasure →
    ∃ (κ : ℝ) (la : Measure ((rowN ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))))) (ν : Measure (GfC (ch.G.V (.top j)))),
      0 < κ ∧ la.IsHaarMeasure ∧ ν.IsHaarMeasure ∧ ∀ b : GfC (ch.G.V (.grid D.R.m j)),
        ρ.real {r | b⁻¹ * r.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} =
          κ * la.real {n | b⁻¹ * n.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} * ν.real (prSet ch.G j b) := by
  first | exact @GlobalTheory.CellMass.cell_fubini | exact GlobalTheory.CellMass.cell_fubini | (intros; apply GlobalTheory.CellMass.cell_fubini <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingCellMassEqConstMulLocalCoefficients
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CellMass


set_option maxHeartbeats 1600000 in
theorem cell_mass : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ)
    (ρ : ∀ j, Measure ((rowGrp ch.G j).subgroupOf (GfC _))) (μ : ∀ j, Measure (GfC (ch.G.V (.grid D.R.m j)))),
    (∀ j ∈ idx D, (ρ j).IsHaarMeasure ∧ (μ j).IsHaarMeasure) → ∀ j ∈ idx D, ∃ c : ℂ, ∀ t Φ β b, IsRep t ch.S.B s β b →
      ∀ M M' : Vol ch.G, M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' → ∀ x : ℝ≥0, M.ν (.top j) = x • M'.ν (.top j) →
        ∀ hb : b j ∈ GfC _, cellWt (ρ j) (μ j) ((latGrp ch.G j).subgroupOf _) ⟨b j, hb⟩ * ((x : ℝ) : ℂ) =
          c * (GlobalTheory.RowWt.colCoef ch t β j : ℂ) := by
  refine GlobalTheory.RowReal.big_mono ?_ (Big.and GlobalTheory.T.finitePoints_rowPeriod_conjLevel_fubini (Big.and GlobalTheory.T.doubleCosetProjection_volume_const_mul GlobalTheory.T.exists_haar_volume_of_conjugate_lattice))
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch h s ρ μ hH j hj
  obtain ⟨hA, hB, hC⟩ := h
  obtain ⟨κ, la, ν, hκ, hla, hν, hAeq⟩ := hA j hj (ρ j) (hH j hj).1
  obtain ⟨κ', hκ', hBeq⟩ := hB s j hj ν hν
  obtain ⟨V₀, hV₀, hCeq⟩ := hC s j hj la hla
  have hjm : j ≤ D.R.m := by rw [idx, List.mem_range'_1] at hj; omega
  refine ⟨(((μ j).real (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup _) : Set (GfC _)) / (κ * κ' * V₀) : ℝ) : ℂ),
    fun t Φ β b hb M M' hM hM' x hx hbj => ?_⟩
  have e1 := hAeq ⟨b j, hbj⟩
  have e2 := hBeq t Φ β b hb M M' hM hM' x hx hbj
  have e3 := hCeq t β b hb hbj
  have hx0 : (x : ℝ) ≠ 0 := by
    intro h0
    have hH' := (hM.vtx (.top j) hjm).haar_fund.1
    have hz : M.ν (.top j) = 0 := by
      rw [hx, show x = 0 from NNReal.coe_eq_zero.1 h0, zero_smul]
    have hpos := Measure.IsOpenPosMeasure.open_pos (μ := M.ν (.top j)) Set.univ isOpen_univ Set.univ_nonempty
    rw [hz] at hpos
    exact hpos rfl
  set lv := la.real {n | (⟨b j, hbj⟩ : GfC _)⁻¹ * n.1 * ⟨b j, hbj⟩ ∈ (latGrp ch.G j).subgroupOf (GfC _)} with hlv
  set cc : ℝ := (GlobalTheory.RowWt.colCoef ch t β j : ℝ) with hcc
  have hlv0 : lv ≠ 0 := fun h0 => by rw [h0, zero_mul] at e3; exact hV₀.ne' e3.symm
  unfold cellWt
  rw [e1, e2]
  have key : (μ j).real (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup _) : Set (GfC _)) / (κ * lv * (κ' * x)) * x =
      (μ j).real (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup _) : Set (GfC _)) / (κ * κ' * V₀) * cc := by
    have hcc0 : cc ≠ 0 := fun h0 => by rw [h0, mul_zero] at e3; exact hV₀.ne' e3.symm
    have hk1 := hκ.ne'
    have hk2 := hκ'.ne'
    rw [← e3]
    field_simp
  have := congrArg (fun r : ℝ => (r : ℂ)) key
  simp only [hcc] at this
  push_cast at this ⊢
  exact this

end GlobalTheory.CellMass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingCellMassEqConstMulLocalCoefficientsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_cell_mass_eq_const_mul_local_coefficients : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ)
    (ρ : ∀ j, Measure ((rowGrp ch.G j).subgroupOf (GfC _))) (μ : ∀ j, Measure (GfC (ch.G.V (.grid D.R.m j)))),
    (∀ j ∈ idx D, (ρ j).IsHaarMeasure ∧ (μ j).IsHaarMeasure) → ∀ j ∈ idx D, ∃ c : ℂ, ∀ t Φ β b, IsRep t ch.S.B s β b →
      ∀ M M' : Vol ch.G, M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' → ∀ x : ℝ≥0, M.ν (.top j) = x • M'.ν (.top j) →
        ∀ hb : b j ∈ GfC _, cellWt (ρ j) (μ j) ((latGrp ch.G j).subgroupOf _) ⟨b j, hb⟩ * ((x : ℝ) : ℂ) =
          c * (GlobalTheory.RowWt.colCoef ch t β j : ℂ) := by
  first | exact @GlobalTheory.CellMass.cell_mass | exact GlobalTheory.CellMass.cell_mass | (intros; apply GlobalTheory.CellMass.cell_mass <;> assumption)
end
