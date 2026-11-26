module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExpFourClauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneVectorOfMultiplicityOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebra
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.CuspMult.EqCut

section Cosets

variable {Γ : Type} [Group Γ] {H J : Subgroup Γ}

theorem isDC_sub_iff (hJ : J ≤ H) (a : H) (R : Finset H) :
    Bridge.IsDC (J.subgroupOf H) a R ↔ Bridge.IsDC J (a : Γ) (R.map (Function.Embedding.subtype _)) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun b hb => ?_, ?_⟩
    · obtain ⟨b', hb', rfl⟩ := Finset.mem_map.1 hb
      obtain ⟨k₁, k₂, e⟩ := h1 b' hb'
      exact ⟨⟨k₁.1.1, k₁.2⟩, ⟨k₂.1.1, k₂.2⟩, congrArg Subtype.val e⟩
    · rintro g ⟨k₁, k₂, rfl⟩
      obtain ⟨b, ⟨hb, hb2⟩, hu⟩ := h2 _ ⟨⟨⟨k₁.1, hJ k₁.2⟩, k₁.2⟩, ⟨⟨k₂.1, hJ k₂.2⟩, k₂.2⟩, rfl⟩
      refine ⟨b.1, ⟨Finset.mem_map.2 ⟨b, hb, rfl⟩, hb2⟩, ?_⟩
      rintro y ⟨hy, hy2⟩
      obtain ⟨y', hy', rfl⟩ := Finset.mem_map.1 hy
      exact congrArg Subtype.val (hu y' ⟨hy', hy2⟩)
  · rintro ⟨h1, h2⟩
    refine ⟨fun b hb => ?_, ?_⟩
    · obtain ⟨k₁, k₂, e⟩ := h1 b.1 (Finset.mem_map.2 ⟨b, hb, rfl⟩)
      exact ⟨⟨⟨k₁.1, hJ k₁.2⟩, k₁.2⟩, ⟨⟨k₂.1, hJ k₂.2⟩, k₂.2⟩, Subtype.ext e⟩
    · rintro g ⟨k₁, k₂, rfl⟩
      obtain ⟨b, ⟨hb, hb2⟩, hu⟩ := h2 _ ⟨⟨k₁.1.1, k₁.2⟩, ⟨k₂.1.1, k₂.2⟩, rfl⟩
      obtain ⟨b', hb', rfl⟩ := Finset.mem_map.1 hb
      refine ⟨b', ⟨hb', hb2⟩, ?_⟩
      rintro y ⟨hy, hy2⟩
      exact Subtype.ext (hu y.1 ⟨Finset.mem_map.2 ⟨y, hy, rfl⟩, hy2⟩)

theorem exists_lift_of_isDC (hJ : J ≤ H) (a : H) (R' : Finset Γ) (h : Bridge.IsDC J (a : Γ) R') :
    ∃ R : Finset H, R.map (Function.Embedding.subtype _) = R' := by
  classical
  refine ⟨R'.subtype (· ∈ H), Finset.subtype_map_of_mem fun b hb => ?_⟩
  obtain ⟨k₁, k₂, rfl⟩ := h.1 b hb
  exact H.mul_mem (H.mul_mem (hJ k₁.2) a.2) (hJ k₂.2)

end Cosets

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem levChi_flag {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hs : L.s = 0) (hQ : L.Q = ∅)
    (κ : GA D V) : levChi V β (flagL L) κ = 1 := by
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V κ)) = 1 := subgroupCharExtension_one_apply _ _
  have hs' : (flagL L).s = 0 := hs
  have hQ' : (flagL L).Q = ∅ := hQ
  unfold levChi levFn
  rw [h2, hs', hQ']
  simp

theorem levChi_flag1 {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hs : L.s = 0) (hQ : L.Q = ∅)
    (κ : GA D V) : levChi V β (flag1L L) κ = 1 := by
  rw [← levChi_flag (β := β) hs hQ κ]
  unfold levChi
  rw [levFn_flag1]

theorem hasType_flag1 {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (P : LevelP L.Pg L.r ℂ)
    {F : GA D V → ℂ} (hF : HasType V β (withP L P) F) : HasType V β (flag1L L) F := by
  intro κ hκ h
  have e : rTup β L (finE V κ) = 1 := Subgroup.mem_bot.1 hκ.2.2
  have hm : κ ∈ levG V β (withP L P) := by
    refine ⟨hκ.1, hκ.2.1, ?_⟩
    show rTup β L (finE V κ) ∈ P.H
    rw [e]; exact P.H.one_mem
  rw [hF κ hm h]
  unfold levChi
  rw [levFn_withP, e, blockDiagonalExtendByOnePrimeField_one, one_mul, levFn_flag1]

theorem gaL_apply {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hs : L.s = 0) (hQ : L.Q = ∅)
    {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) {F : GA D V → ℂ}
    (hF : HasType V β (flag1L L) F) (κ : G → GA D V) (hκ : ∀ g, IsLevelLift V β L (eG g) (κ g)) (h : GA D V) :
    gaL V β L eG c F h = ∑ g, c g * F (h * κ g) := by
  unfold gaL
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  have := level_action_spec hF ⟨κ g, hκ g⟩ (κ g) (hκ g) h
  rw [levChi_flag hs hQ, inv_one, one_mul] at this
  rw [← this]
  rfl

theorem alg_sum (M : DSModel V S) {ι : Type} (s : Finset ι) (κ : ι → GfC V) (c : ι → ℂ) (a : ℂ) (T : MMap M) :
    (finRep M).asAlgebraHom (∑ i ∈ s, MonoidAlgebra.single (κ i) (c i) - MonoidAlgebra.single 1 a) T = 0 ↔
      ∀ v x, ∑ i ∈ s, c i * T v (x * (κ i : GA D V)) = a * T v x := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum, LinearMap.sub_apply, sub_eq_zero, LinearMap.sum_apply]
  simp only [Representation.asAlgebraHom_single, map_one, LinearMap.smul_apply, Module.End.one_apply]
  rw [MultilinearMap.ext_iff]
  refine forall_congr' fun v => ?_
  rw [funext_iff]
  refine forall_congr' fun x => ?_
  rw [MultilinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem alg_one (M : DSModel V S) (k : GfC V) (a : ℂ) (T : MMap M) :
    (finRep M).asAlgebraHom (MonoidAlgebra.single k 1 - MonoidAlgebra.single 1 a) T = 0 ↔
      ∀ v x, T v (x * (k : GA D V)) = a * T v x := by
  have := alg_sum M (Finset.univ : Finset Unit) (fun _ => k) (fun _ => 1) a T
  simpa only [Finset.univ_unique, Finset.sum_singleton, one_mul] using this

theorem mem_hPart (M : DSModel V S) (J : Subgroup (GA D V)) {Pl0 : Type} (ok : Set Pl0)
    (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) (T : MMap M) :
    T ∈ hPart M J ok pl q Sg ↔ ∀ P ∈ ok, ∀ k ≤ V.rank, ∀ α, IsHeckeAt V (pl P) k α → ∀ R, Bridge.IsDC J α⁻¹ R →
      ∀ v x, ∑ γ ∈ R, T v (x * γ) = ((Sg P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) * T v x := by
  unfold hPart
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, MultilinearMap.ext_iff, funext_iff]
  rfl

theorem good_hecke_eq_killed : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (P : LevelP L.Pg L.r ℂ) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]), L.s = 0 → L.Q = ∅ → LiftsExist V β L → goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) (gaL V β L eG c) ⊓ hPart M (levG V β (flag1L L)) ok pl q Sg = allMaps θ M ⊓ killed (finRep M) (eqSet V β L eG c P ok pl q Sg) := by
  intro D V S θ M β L G _ _ eG c P Pl0 ok pl q Sg hs hQ hlift
  have hJ : levG V β (flag1L L) ≤ GfC V := fun _ h => h.1
  ext T
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_goodPart, mem_killed, mem_hPart, GlobalTheory.MultMem.mem_mult_iff,
    GlobalTheory.MultMem.mem_mult_iff]
  constructor
  · rintro ⟨⟨hm, hg⟩, hh⟩
    refine ⟨⟨hm.aut, hm.cusp, fun _ _ h => h.elim, hm.equiv, hm.cont⟩, ?_⟩
    rintro x ((⟨k, hk, rfl⟩ | ⟨κ, hκ, rfl⟩) | ⟨P0, hP0, k, hk, α, R, hα, hR, rfl⟩)
    · exact (alg_one M k _ T).2 fun v x => hm.lev v k hk x
    · refine (alg_sum M _ κ c 1 T).2 fun v x => ?_
      have hF : HasType V β (flag1L L) (T v) := hasType_flag1 P fun k hk h => hm.lev v k hk h
      rw [← gaL_apply hs hQ eG c hF (fun g => κ g) hκ x, hg v, one_mul]
    · refine (alg_sum M R (fun γ => γ) (fun _ => 1) _ T).2 fun v x => ?_
      have := hh P0 hP0 k hk α hα _ ((isDC_sub_iff hJ α⁻¹ R).1 hR) v x
      rw [Finset.sum_map] at this
      simp only [one_mul]
      exact this
  · rintro ⟨hm, hk⟩
    have hlev : ∀ v, HasType V β (withP L P) (T v) := fun v k hkk x =>
      (alg_one M ⟨k, hkk.1⟩ _ T).1 (hk _ (Or.inl (Or.inl ⟨⟨k, hkk.1⟩, hkk, rfl⟩))) v x
    refine ⟨⟨⟨hm.aut, hm.cusp, fun v k hkk x => hlev v k hkk x, hm.equiv, hm.cont⟩, fun v => ?_⟩, ?_⟩
    · choose κ hκ using fun g => hlift (eG g)
      funext x
      rw [gaL_apply hs hQ eG c (hasType_flag1 P (hlev v)) κ hκ x]
      have := (alg_sum M Finset.univ (fun g => (⟨κ g, (hκ g).1⟩ : GfC V)) c 1 T).1
        (hk _ (Or.inl (Or.inr ⟨fun g => ⟨κ g, (hκ g).1⟩, hκ, rfl⟩))) v x
      rw [one_mul] at this
      exact this
    · intro P0 hP0 k hkr α hα R' hR' v x
      have hαf : α ∈ GfC V := by
        obtain ⟨e, ϖ, -, -, -, h⟩ := hα
        exact h.1
      obtain ⟨R, rfl⟩ := exists_lift_of_isDC hJ (⟨α, hαf⟩ : GfC V)⁻¹ R' hR'
      have hR := (isDC_sub_iff hJ (⟨α, hαf⟩ : GfC V)⁻¹ R).2 hR'
      have := (alg_sum M R (fun γ => γ) (fun _ => 1) _ T).1
        (hk _ (Or.inr ⟨P0, hP0, k, hkr, ⟨α, hαf⟩, R, hα, hR, rfl⟩)) v x
      simp only [one_mul] at this
      rw [Finset.sum_map]
      exact this

end GlobalTheory.CuspMult.EqCut

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebraStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodForms_eq_killed_by_groupAlgebra : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (P : LevelP L.Pg L.r ℂ) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]), L.s = 0 → L.Q = ∅ → LiftsExist V β L → goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) (gaL V β L eG c) ⊓ hPart M (levG V β (flag1L L)) ok pl q Sg = allMaps θ M ⊓ killed (finRep M) (eqSet V β L eG c P ok pl q Sg) := by
  first | exact @GlobalTheory.CuspMult.EqCut.good_hecke_eq_killed | exact GlobalTheory.CuspMult.EqCut.good_hecke_eq_killed | (intros; apply GlobalTheory.CuspMult.EqCut.good_hecke_eq_killed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermCColMulVec
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.RealCoord

section Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def perL (X : Data E r) (x : Frame X.Ψ r) : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ × Fin r → ℂ) where
  toFun := perC X x
  map_add' u v := by
    funext p
    simp only [perC, Pi.add_apply]
    split_ifs
    · simp only [hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
    · rw [Matrix.mulVec_add, Pi.add_apply]
  map_smul' c u := by
    funext p
    simp only [perC, Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · simp only [hermC, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · rw [Matrix.mulVec_smul, Pi.smul_apply]

theorem hermC_col_mulVec (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) (a : Fin r)
    (c : Fin r → ℂ) : hermC τ G (FD.col x a) (x *ᵥ c) = ∑ b, FD.gram τ G x a b * conj (c b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, FD.gram, FD.col, Matrix.of_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum,
    Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem perL_injective (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : Function.Injective (perL X x) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro u hu
  funext τ
  have hd : (mat x τ).det ≠ 0 := (hx τ).1
  have hA : (X.gramPos x τ).det ≠ 0 := by
    have h := (hx τ).2 ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
    intro h0
    have e : dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ = (X.gramPos x τ).det := rfl
    rw [e, h0] at h
    simp at h
  set c : Fin r → ℂ := (mat x τ)⁻¹ *ᵥ u τ with hc
  have hu' : u τ = mat x τ *ᵥ c := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd), Matrix.one_mulVec]
  have h2 : ∀ a : Fin r, ¬ (a : ℕ) < X.p0 → c a = 0 := fun a ha => by
    have := congrFun hu (τ, a)
    change perC X x u (τ, a) = 0 at this
    simpa only [perC, if_neg ha] using this
  have h1 : X.gramPos x τ *ᵥ (fun b => conj (c (Fin.castLE X.p0_le b))) = 0 := by
    funext a
    have ha : ((Fin.castLE X.p0_le a : Fin r) : ℕ) < X.p0 := a.2
    have := congrFun hu (τ, Fin.castLE X.p0_le a)
    change perC X x u (τ, Fin.castLE X.p0_le a) = 0 at this
    simp only [perC, if_pos ha] at this
    rw [hu', hermC_col_mulVec] at this
    rw [Pi.zero_apply, ← this]
    simp only [Matrix.mulVec, dotProduct, Data.gramPos, Matrix.submatrix_apply]
    refine Fintype.sum_of_injective (Fin.castLE X.p0_le) (Fin.castLE_injective _) _ _ (fun b hb => ?_) fun _ => rfl
    rw [h2 b fun h => hb ⟨⟨b, h⟩, rfl⟩, map_zero, mul_zero]
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hA h1
  have h4 : c = 0 := by
    funext a
    by_cases ha : (a : ℕ) < X.p0
    · have := congrFun h3 ⟨a, ha⟩
      simpa using this
    · exact h2 a ha
  rw [hu', h4, Matrix.mulVec_zero]
  rfl

theorem perL_bijective (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : Function.Bijective (perL X x) := by
  refine ⟨perL_injective X hx, ?_⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 (perL_injective X hx)
  simp [Module.finrank_pi_fintype, mul_assoc]

end Lin

variable {D : D7}

theorem realM_tauE (θ : InfFam D) {m n : ℕ} (w : Mx D m n) (ρ : D.what₂.Tau) :
    realM θ w (tauE D ρ) = compAt θ ρ w := by
  have h : ∃ ρ', tauE D ρ = tauE D ρ' := ⟨ρ, rfl⟩
  rw [realM, dite_eq_left h, ← GlobalTheory.PointAtPlace.tauE_injective h.choose_spec]

theorem realM_add (θ : InfFam D) {m n : ℕ} (v w : Mx D m n) (τ : D.host.E →+* ℂ) :
    realM θ (v + w) τ = realM θ v τ + realM θ w τ := by
  unfold realM
  split_ifs with h
  · funext i j
    show θ _ (infPart D (v i j + w i j)) = θ _ (infPart D (v i j)) + θ _ (infPart D (w i j))
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _)]
  · rw [add_zero]

theorem continuous_realM {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.host.E →+* ℂ) (i : Fin m) (j : Fin n) :
    Continuous fun w : Mx D m n => realM θ w τ i j := by
  unfold realM
  split_ifs with h
  · exact (GlobalTheory.FockCompare.continuous_comp hθ _).comp ((continuous_apply j).comp (continuous_apply i))
  · exact continuous_const

theorem realM_lineAt {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (ρ : D.what₂.Tau) (u : Matrix (Fin m) (Fin n) ℂ)
    (t : ℝ) (τ : D.host.E →+* ℂ) : realM θ (lineAt θ ρ u t) τ = t • realM θ (lineAt θ ρ u 1) τ := by
  have hL : IsLineAt θ ρ u (lineAt θ ρ u) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n ρ u)
  unfold realM
  split_ifs with h
  · rw [hL.2.2, hL.2.2]
    split_ifs
    · funext i j
      simp
    · rw [smul_zero]
  · rw [smul_zero]

theorem zOf_coordinates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r), (∀ (γ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (v : WO V W), v.map (infPart D) = (ratW W V γ).map (infPart D) → zOf θ V W hr X idx x v = fun b => pv X idx x (colsR hr γ b)) ∧ (∀ v w : WO V W, zOf θ V W hr X idx x (v + w) = zOf θ V W hr X idx x v + zOf θ V W hr X idx x w) ∧ (∀ (τ : D.what₂.Tau) (u : Matrix (Fin W.rank) (Fin V.rank) ℂ) (t : ℝ), zOf θ V W hr X idx x (lineAt θ τ u t) = (t : ℂ) • zOf θ V W hr X idx x (lineAt θ τ u 1)) ∧ Continuous (zOf θ V W hr X idx x ) ∧ (x ∈ X.dom → ∃ p : (Fin V.rank → Fin g → ℂ) →+ WO V W, Continuous p ∧ (∀ z, (p z).map (finPart D) = 0 ∧ zOf θ V W hr X idx x (p z) = z) ∧ ∀ w : WO V W, w.map (finPart D) = 0 → p (zOf θ V W hr X idx x w) = w) := by
  intro D ψ θ V W r g hr X bas idx _ hθ _ _ hM _ x
  have hz : ∀ w b j, zOf θ V W hr X idx x w b j =
      perL X x (fun τ a => realM θ w τ.1 (Fin.cast hr.symm a) b) (idx j) := fun _ _ _ => rfl
  refine ⟨fun γ v hv => ?_, fun v w => ?_, fun ρ u t => ?_, ?_, fun hx => ?_⟩
  · funext b j
    show perC X x _ (idx j) = per X x _ (idx j)
    rw [← perC_emb]
    congr 1
    funext τ a
    obtain ⟨ρ, hρ⟩ := (hM.psi τ.1).1 τ.2
    have e : infPart D (v (Fin.cast hr.symm a) b) = infPart D (incA D (γ (Fin.cast hr.symm a) b)) :=
      congrFun (congrFun hv _) _
    show realM θ v τ.1 _ _ = τ.1 (γ (Fin.cast hr.symm a) b)
    rw [hρ, realM_tauE, ← GlobalTheory.FockCompare.comp_incA hθ, ← e]
    rfl
  · funext b j
    rw [Pi.add_apply, Pi.add_apply, hz, hz, hz, ← Pi.add_apply (perL X x _), ← map_add (f := _)]
    refine congrFun (congrArg (perL X x) ?_) _
    funext τ a
    rw [realM_add]
    rfl
  · funext b j
    rw [Pi.smul_apply, Pi.smul_apply, hz, hz, Complex.coe_smul, ← Pi.smul_apply t (perL X x _), ← map_smul]
    refine congrFun (congrArg (perL X x) ?_) _
    funext τ a
    rw [realM_lineAt hθ]
    rfl
  · refine continuous_pi fun b => continuous_pi fun j => ?_
    simp only [hz]
    exact (continuous_apply (idx j)).comp ((perL X x).continuous_of_finiteDimensional.comp
      (continuous_pi fun τ => continuous_pi fun a => continuous_realM hθ τ.1 _ b))
  · obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
    let L := LinearEquiv.ofBijective (perL X x) (perL_bijective X hx)
    have hL : ∀ u, L u = perL X x u := fun _ => rfl
    let pl : D.what₂.Tau → X.Ψ := fun ρ => ⟨tauE D ρ, (hM.psi _).2 ⟨ρ, rfl⟩⟩
    let p : (Fin V.rank → Fin g → ℂ) →+ WO V W :=
      { toFun := fun z => Matrix.of fun i b => σ fun ρ => L.symm (fun q => z b (idx.symm q)) (pl ρ) (Fin.cast hr i)
        map_zero' := by
          funext i b
          have : (fun q => (0 : Fin V.rank → Fin g → ℂ) b (idx.symm q)) = 0 := rfl
          rw [Matrix.of_apply, this, map_zero]
          exact σ.map_zero
        map_add' := fun z z' => by
          funext i b
          have : (fun q => (z + z') b (idx.symm q)) = (fun q => z b (idx.symm q)) + fun q => z' b (idx.symm q) := rfl
          rw [Matrix.of_apply, this, map_add (f := _)]
          exact σ.map_add _ _ }
    have hp : ∀ z i b, p z i b = σ fun ρ => L.symm (fun q => z b (idx.symm q)) (pl ρ) (Fin.cast hr i) :=
      fun _ _ _ => rfl
    refine ⟨p, ?_, fun z => ⟨?_, ?_⟩, fun w hw => ?_⟩
    · refine continuous_pi fun i => continuous_pi fun b => hσ.cont.comp (continuous_pi fun ρ => ?_)
      exact (continuous_apply (Fin.cast hr i)).comp ((continuous_apply (pl ρ)).comp
        (L.symm.toLinearMap.continuous_of_finiteDimensional.comp
          (continuous_pi fun q => (continuous_apply (idx.symm q)).comp (continuous_apply b))))
    · funext i b
      exact hσ.fin _
    · funext b j
      have e : (fun (τ : X.Ψ) a => realM θ (p z) τ.1 (Fin.cast hr.symm a) b) =
          L.symm (fun q => z b (idx.symm q)) := by
        funext τ a
        obtain ⟨ρ, hρ⟩ := (hM.psi τ.1).1 τ.2
        obtain rfl : τ = pl ρ := Subtype.ext hρ
        show realM θ (p z) (tauE D ρ) _ _ = _
        rw [realM_tauE]
        exact hσ.comp _ ρ
      rw [hz, e, ← hL, LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply]
    · funext i b
      have e : (fun q => zOf θ V W hr X idx x w b (idx.symm q)) =
          L (fun τ a => realM θ w τ.1 (Fin.cast hr.symm a) b) := by
        funext q
        rw [hz, Equiv.apply_symm_apply, hL]
      rw [hp, e, LinearEquiv.symm_apply_apply]
      refine sub_eq_zero.1 (hσ.ext _ ?_ fun ρ => ?_)
      · have e1 : finPart D (w i b) = 0 := congrFun (congrFun hw i) b
        rw [RingHom.map_sub, hσ.fin, e1, sub_zero]
      · rw [RingHom.map_sub, RingHom.map_sub, hσ.comp, sub_eq_zero]
        show realM θ w (tauE D ρ) i b = _
        rw [realM_tauE]
        rfl

end GlobalTheory.AdTh.RealCoord

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLinearCombination
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.CuspFormLin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {d : ℕ}

theorem growth_smul_add (c : ℂ) {f f' : GL (Fin d) (Cinf E) → ℂ}
    (h : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * height y ^ N)
    (h' : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f' y‖ ≤ C * height y ^ N) :
    ∃ (C : ℝ) (N : ℕ), ∀ y, ‖c * f y + f' y‖ ≤ C * height y ^ N := by
  obtain ⟨C, N, h⟩ := h
  obtain ⟨C', N', h'⟩ := h'
  refine ⟨‖c‖ * |C| + |C'|, N + N', fun y => ?_⟩
  have h1 := one_le_height y
  have e : ‖f y‖ ≤ |C| * height y ^ (N + N') :=
    (h y).trans (mul_le_mul (le_abs_self C) (pow_le_pow_right₀ h1 (Nat.le_add_right N N'))
      (by positivity) (abs_nonneg C))
  have e' : ‖f' y‖ ≤ |C'| * height y ^ (N + N') :=
    (h' y).trans (mul_le_mul (le_abs_self C') (pow_le_pow_right₀ h1 (Nat.le_add_left N' N))
      (by positivity) (abs_nonneg C'))
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, add_mul, mul_assoc]
  exact add_le_add (mul_le_mul_of_nonneg_left e (norm_nonneg c)) e'

theorem isAutForm_smul_add (c : ℂ) {φ ψ : Sm E d} (h : IsAutForm φ) (h' : IsAutForm ψ) :
    IsAutForm (c • φ + ψ) := by
  refine { left := ?_, level := ?_, kfin := ?_, zfin := ?_, growth := ?_ }
  · intro γ g
    change c * φ.1 _ + ψ.1 _ = c * φ.1 _ + ψ.1 _
    rw [h.left, h'.left]
  · refine isOpen_stab_of_mem_nhds (finRep E d) (c • φ + ψ) (Filter.mem_of_superset
      ((h.level.inter h'.level).mem_nhds ⟨by simp, by simp⟩) ?_)
    intro k hk
    have h1 : finRep E d k φ = φ := hk.1
    have h2 : finRep E d k ψ = ψ := hk.2
    change finRep E d k (c • φ + ψ) = c • φ + ψ
    rw [map_add (f := _), map_smul, h1, h2]
  · have := h.kfin
    have := h'.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E d k φ) ⊔
      Submodule.span ℂ (Set.range fun k => cptRep E d k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    change cptRep E d k (c • φ + ψ) ∈ _
    rw [map_add (f := _), map_smul]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
      (Submodule.subset_span ⟨k, rfl⟩)
  · have := h.zfin
    have := h'.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E d) => z φ) '' Zalg E d) ⊔
        Submodule.span ℂ ((fun z : Module.End ℂ (Sm E d) => z ψ) '' Zalg E d)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    change z (c • φ + ψ) ∈ _
    rw [map_add (f := _), map_smul]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩))
      (Submodule.subset_span ⟨z, hz, rfl⟩)
  · intro g
    exact growth_smul_add c (h.growth g) (h'.growth g)

theorem isCuspForm_smul_add (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (d : ℕ) (c : ℂ)
    (φ ψ : Sm E d) (h : IsCuspForm φ) (h' : IsCuspForm ψ) : IsCuspForm (c • φ + ψ) := by
  refine ⟨isAutForm_smul_add c h.1 h'.1, fun r h0 h1 _ _ ν 𝓕 hν h𝓕 g => ?_⟩
  have i := CuspidalL2GL.integrableOn_unip (ContAut.continuous_of_isOpen_stab E d φ h.1.level) h.1.left ν h𝓕 g
  have i' := CuspidalL2GL.integrableOn_unip (ContAut.continuous_of_isOpen_stab E d ψ h'.1.level) h'.1.left ν h𝓕 g
  change ∫ x in 𝓕, (c * φ.1 (unip x * g) + ψ.1 (unip x * g)) ∂ν = 0
  rw [integral_add (i.const_mul c) i', integral_const_mul, h.2 r h0 h1 ν 𝓕 hν h𝓕 g, h'.2 r h0 h1 ν 𝓕 hν h𝓕 g,
    mul_zero, add_zero]

end GlobalTheory.CuspFormLin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModelsMultiplicityEqual
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.ConjDim

variable {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar}

def conjMap (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (T : MMap M) : MMap M' where
  toFun v' := star (T fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩)
  map_update_add' v' i x y := by
    have e : ∀ z : M'.sm i, (fun τ => (⟨c τ (Function.update v' i z τ), (h τ _).1 (Function.update v' i z τ).2⟩ : M.sm τ)) =
        Function.update (fun τ => (⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩ : M.sm τ)) i ⟨c i z, (h i _).1 z.2⟩ := by
      intro z
      funext τ
      by_cases hτ : τ = i
      · subst hτ; simp
      · simp [Function.update_of_ne hτ]
    rw [e, e, e, ← star_add, ← T.map_update_add]
    congr 3
    ext; simp
  map_update_smul' v' i a x := by
    have e : ∀ z : M'.sm i, (fun τ => (⟨c τ (Function.update v' i z τ), (h τ _).1 (Function.update v' i z τ).2⟩ : M.sm τ)) =
        Function.update (fun τ => (⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩ : M.sm τ)) i ⟨c i z, (h i _).1 z.2⟩ := by
      intro z
      funext τ
      by_cases hτ : τ = i
      · subst hτ; simp
      · simp [Function.update_of_ne hτ]
    rw [e, e]
    have e2 : (⟨c i ((a • x : M'.sm i) : M'.H i), (h i _).1 (a • x).2⟩ : M.sm i) = star a • ⟨c i x, (h i _).1 x.2⟩ := by
      ext; exact (c i).map_smulₛₗ a x
    rw [e2, T.map_update_smul, star_smul]
    simp only [RingHom.id_apply, star_star]

theorem conjMap_apply (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (T : MMap M) (v' : M'.Vec) :
    conjMap M M' c h T v' = star (T fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) := rfl

theorem conjMap_eq_zero (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (T : MMap M) (hT : conjMap M M' c h T = 0) : T = 0 := by
  refine MultilinearMap.ext fun v => ?_
  have h1 := congrArg (fun U : MMap M' => U fun τ => ⟨(c τ).symm (v τ), (h τ _).2 (by simpa using (v τ).2)⟩) hT
  simp only [conjMap_apply, LinearIsometryEquiv.apply_symm_apply, Subtype.coe_eta, MultilinearMap.zero_apply,
    star_eq_zero] at h1
  exact h1

theorem mult_congr (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) {J : Set (GA D V)}
    {χ χ' : GA D V → ℂ} (hχ : ∀ k ∈ J, χ' k = χ k) {T : MMap M} (hT : T ∈ Mult θ M J χ) : T ∈ Mult θ M J χ' := by
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
  exact ⟨hT.aut, hT.cusp, fun v k hk g => by rw [hχ k hk]; exact hT.lev v k hk g, hT.equiv, hT.cont⟩

theorem rank_le (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w))
    (J : Set (GA D V)) (χ χ' : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (J0 : Subgroup (GA D V)) {Pl0 : Type}
    (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg Sg' : Pl0 → ℂ[X])
    (hχ : ∀ k ∈ J, χ' k = star (χ k)) (he : ∀ φ : GA D V → ℂ, e' (star φ) = star (e φ))
    (hS : ∀ P k, (Sg' P).coeff k = star ((Sg P).coeff k)) :
    Module.rank ℂ (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)) ≤
      Module.rank ℂ (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q Sg' : Submodule ℂ (MMap M')) := by
  obtain ⟨h, hM⟩ := GlobalTheory.T.complexConjugation_maps_multiplicitySpace θ M M' c hc
  have key : ∀ T ∈ (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)),
      conjMap M M' c h T ∈ (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q Sg' : Submodule ℂ (MMap M')) := by
    rintro T ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · obtain ⟨T', hT', e1⟩ := hM J χ T h1
      have : conjMap M M' c h T = T' := by
        refine MultilinearMap.ext fun v' => funext fun g => ?_
        rw [e1 v' (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (fun _ => rfl) g]
        rfl
      rw [this]
      exact mult_congr θ M' hχ hT'
    · have h2' : ∀ v, e (T v) = T v := fun v => by
        have := congrArg (fun U : MMap M => U v) (sub_eq_zero.1 (LinearMap.mem_ker.1 h2))
        exact this
      refine LinearMap.mem_ker.2 (sub_eq_zero.2 (MultilinearMap.ext fun v' => ?_))
      show e' (conjMap M M' c h T v') = conjMap M M' c h T v'
      rw [conjMap_apply, he, h2']
    · simp only [hPart, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker] at h3 ⊢
      intro P hP k hk α hα R hR
      have h4 := sub_eq_zero.1 (h3 P hP k hk α hα R hR)
      refine sub_eq_zero.2 (MultilinearMap.ext fun v' => funext fun g => ?_)
      have h5 : ∑ γ ∈ R, T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (g * γ) =
          ((Sg P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) * T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) g :=
        congrArg (fun U : MMap M => U (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) g) h4
      show ∑ γ ∈ R, star (T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (g * γ)) =
          ((Sg' P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) * star (T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) g)
      rw [← star_sum, h5, hS]
      simp
  let j : (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)) →+
      (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q Sg' : Submodule ℂ (MMap M')) :=
    AddMonoidHom.mk' (fun T => ⟨conjMap M M' c h T, key T T.2⟩) fun T T' =>
      Subtype.ext (MultilinearMap.ext fun v' => star_add _ _)
  refine rank_le_of_injective_injective (star : ℂ → ℂ) j (fun r hr => star_eq_zero.1 hr) ?_ ?_
  · refine (injective_iff_map_eq_zero j).2 fun T hT => Subtype.ext ?_
    exact conjMap_eq_zero M M' c h T (congrArg Subtype.val hT)
  · intro r T
    refine Subtype.ext (MultilinearMap.ext fun v' => ?_)
    show star (star r • (T : MMap M) _) = r • star ((T : MMap M) _)
    rw [star_smul, star_star]

theorem conj_rank : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → ∀ (J : Set (GA D V)) (χ χ' : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (J0 : Subgroup (GA D V)) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]), (∀ k ∈ J, χ' k = star (χ k)) → (∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) → Module.rank ℂ (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)) = Module.rank ℂ (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q (fun P => (Sg P).map (starRingEnd ℂ)) : Submodule ℂ (MMap M')) := by
  intro D V S S' θ M M' c hc J χ χ' e e' J0 Pl0 ok pl q Sg hχ he
  refine le_antisymm (rank_le θ M M' c hc J χ χ' e e' J0 ok pl q Sg _ hχ he fun P k => by simp) ?_
  refine rank_le θ M' M (fun τ => (c τ).symm) ?_ J χ' χ e' e J0 ok pl q _ Sg ?_ ?_ ?_
  · intro τ g hg w
    apply (c τ).injective
    rw [hc τ g hg]
    simp
  · intro k hk
    rw [hχ k hk, star_star]
  · intro φ
    rw [← star_star φ, he, star_star, star_star]
  · intro P k
    simp

end GlobalTheory.ConjDim

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameIntegralGramMatrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameGram

theorem form_mem_span {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (T : Set (Fin n → R))
    (hT : ∀ x ∈ T, ∀ y ∈ T, ∑ i, ∑ j, σ (x i) * J i j * y j ∈ S) :
    ∀ x ∈ Submodule.span S T, ∀ y ∈ Submodule.span S T, ∑ i, ∑ j, σ (x i) * J i j * y j ∈ S := by
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact hT x hx y hy
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      exact S.add_mem ha hb
    | smul c a _ ha =>
      have : ∑ i, ∑ j, σ (x i) * J i j * (c • a) j = (c : R) * ∑ i, ∑ j, σ (x i) * J i j * a j := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        show _ * ((c : R) * a j) = _
        ring
      rw [this]; exact S.mul_mem c.2 ha
  | zero => simp
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
    exact S.add_mem ha hb
  | smul c a _ ha =>
    have : ∑ i, ∑ j, σ ((c • a) i) * J i j * y j = σ (c : R) * ∑ i, ∑ j, σ (a i) * J i j * y j := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      show σ ((c : R) * a i) * _ * _ = _
      rw [map_mul]; ring
    rw [this]; exact S.mul_mem (hσ _ c.2) ha

theorem exists_unit {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n m : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (β : GL (Fin n) R) (H : Set (Fin n → R))
    (hβ : ∀ x, x ∈ H ↔ ∀ i, (β⁻¹).1.mulVec x i ∈ S)
    (hH : ∀ x ∈ H, ∀ y ∈ H, ∑ i, ∑ j, σ (x i) * J i j * y j ∈ S)
    (s s' : Fin m → Fin n → R) (hs : ∀ i, s i ∈ H) (hs' : ∀ i, s' i ∈ H)
    (hd : ∀ a j, ∑ i, s i a * ∑ k, σ (s' i k) * J k j = if a = j then 1 else 0) :
    ∃ G : GL (Fin n) S, S.subtype.mapMatrix G.1 = (β.1.map σ)ᵀ * J * β.1 := by
  have hcol : ∀ j, (fun i => β.1 i j) ∈ H := by
    intro j
    rw [hβ]
    intro k
    have : (β⁻¹).1.mulVec (fun i => β.1 i j) k = ((β⁻¹).1 * β.1) k j := rfl
    rw [this, Units.inv_mul, Matrix.one_apply]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  have a1 : ∀ i j, ((β.1.map σ)ᵀ * J * β.1) i j ∈ S := by
    intro i j
    have := hH _ (hcol i) _ (hcol j)
    rw [Finset.sum_comm] at this
    simpa only [Matrix.mul_apply, Finset.sum_mul, Matrix.transpose_apply, Matrix.map_apply] using this
  let P : Matrix (Fin n) (Fin m) R := Matrix.of fun a i => s i a
  let P' : Matrix (Fin n) (Fin m) R := Matrix.of fun a i => s' i a
  have hP : P * ((P'.map σ)ᵀ * J) = 1 := by
    ext a j
    rw [Matrix.one_apply, ← hd]
    rfl
  have a2 : ∀ i j, (((β⁻¹).1 * P) * (((β⁻¹).1 * P').map σ)ᵀ) i j ∈ S := by
    intro i j
    rw [Matrix.mul_apply]
    exact S.sum_mem fun k _ => S.mul_mem ((hβ _).1 (hs k) i) (hσ _ ((hβ _).1 (hs' k) j))
  have hinv : (((β⁻¹).1 * P) * (((β⁻¹).1 * P').map σ)ᵀ) * ((β.1.map σ)ᵀ * J * β.1) = 1 := by
    have e : (((β⁻¹).1 * P').map σ)ᵀ * (β.1.map σ)ᵀ = (P'.map σ)ᵀ := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    calc _ = (β⁻¹).1 * (P * (((((β⁻¹).1 * P').map σ)ᵀ * (β.1.map σ)ᵀ) * J)) * β.1 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e, hP, Matrix.mul_one, Units.inv_mul]
  let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, a1 i j⟩
  let M' : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, a2 i j⟩
  have hM : S.subtype.mapMatrix M = (β.1.map σ)ᵀ * J * β.1 := rfl
  have hM' : S.subtype.mapMatrix M' = ((β⁻¹).1 * P) * (((β⁻¹).1 * P').map σ)ᵀ := rfl
  have inj : Function.Injective (S.subtype.mapMatrix (m := Fin n)) := by
    intro A B h
    ext i j
    exact congrFun (congrFun h i) j
  have p2 : M' * M = 1 := inj (by rw [map_mul, map_one, hM, hM', hinv])
  exact ⟨⟨M, M', mul_eq_one_comm.1 p2, p2⟩, hM⟩

theorem exists_unit_adelic {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n m : ℕ}
    (c : E → E) (σ : E ⊗[F] Formalism.L2.Herm.Af F →+* E ⊗[F] Formalism.L2.Herm.Af F)
    (hσ : ∀ s ∈ Formalism.L2.Herm.intAf F E, σ s ∈ Formalism.L2.Herm.intAf F E)
    (hσι : ∀ x, σ (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) x) = Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (c x))
    (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hβ : IsFrame β Λ) (hΛ : ∀ y ∈ Λ, ∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, c (x i) * J i j * y j)
    (s s' : Fin m → Fin n → E) (hs : ∀ i, s i ∈ Λ ∧ s' i ∈ Λ)
    (hd : ∀ a j, ∑ i, s i a * ∑ k, c (s' i k) * J k j = if a = j then 1 else 0) :
    ∃ G : GL (Fin n) (Formalism.L2.Herm.intAf F E), (intGL F E n G).val =
      Formalism.UG.cT σ β.1 * J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) * β.1 := by
  let ι : E →+* E ⊗[F] Formalism.L2.Herm.Af F := Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)
  replace hσι : ∀ x, σ (ι x) = ι (c x) := hσι
  have hmem : ∀ x ∈ Λ, (fun i => ι (x i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := fun x hx =>
    Submodule.subset_span ⟨x, hx, rfl⟩
  refine exists_unit (Formalism.L2.Herm.intAf F E) σ hσ (J.map ι) β
    (Formalism.L2.Herm.hatL (F := F) Λ) hβ ?_ (fun i a => ι (s i a)) (fun i a => ι (s' i a))
    (fun i => hmem _ (hs i).1) (fun i => hmem _ (hs i).2) ?_
  · refine form_mem_span _ σ hσ _ _ ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨b, hb⟩ := hΛ y hy x hx
    have : ∑ i, ∑ j, σ (ι (x i)) * (J.map ι) i j * ι (y j) = ι b := by
      rw [hb]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, RingHom.map_mul, hσι, Matrix.map_apply]
    show ∑ i, ∑ j, σ (ι (x i)) * (J.map ι) i j * ι (y j) ∈ _
    rw [this]
    exact (oToS F E b).2
  · intro a j
    have := congrArg ι (hd a j)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, RingHom.map_mul, ← hσι, apply_ite ι, RingHom.map_one, RingHom.map_zero] at this
    exact this

theorem gram_unimodular : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∃ G : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E), (intGL D.host.F D.host.E V.rank G).val = BadPlacesGoodCoefficients.gramIn V β := by
  intro D V β Λ N hB
  have hsd := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D V β Λ N ⟨1, by rw [pow_one]; exact hB⟩
  obtain ⟨m, s, s', hs, hd⟩ := GlobalTheory.LatVacDual.dualFamily D V Λ hsd
  exact exists_unit_adelic star (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (fun _ => GlobalTheory.LevSplit.sigR_int)
    (fun _ => rfl) V.gram β Λ hB.1 (fun y hy => (hsd.2 y).1 hy) s s' hs hd

end GlobalTheory.FrameGram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitDetRoot
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitDetRoot

theorem infPart_sigR_one (D : D7) (x : AE D) (hx : infPart D x = 1) :
    infPart D (sigR (AF D.host.F) D.sp.cm.sig x) = 1 := by
  have h := GlobalTheory.DetRootCong.map_sigR (F := D.host.F) (E := D.host.E)
    (AlgHom.fst D.host.F (InfiniteAdeleRing D.host.F) (Af D.host.F)) D.sp.cm.sig x
  refine h.trans ?_
  exact (congrArg _ hx).trans (map_one _)

end GlobalTheory.UnitDetRoot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspIndProdCharOfIsProdCuspChar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneWhittakerVectorDimHolds
namespace GlobalTheory.GenericProduct

theorem oneGenericVector : OneGenericVector := GlobalTheory.T.whittakerSpaceDim_parabolicInduction_cuspidal_eq_one

theorem genericMultOne_holds : GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.GenericMultOne := genericMultOne oneGenericVector

theorem oneWhittakerVector_holds : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector :=
  GlobalTheory.CuspidalIdempotentCharacters.genericMultOne_iff.1 genericMultOne_holds

end GlobalTheory.GenericProduct
end

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealOneVector

theorem isCuspIndProdChar_of_isProdCuspChar {E : Type} [Field E] [NumberField E] {K : Type} [Field K] (s : K →+* ℂ)
    (Pg : Finset (Pl E)) (r : ℕ) (χ : G0 Pg r → K) (h : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar s Pg r χ) :
    GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.IsCuspIndProdChar Pg r s χ := by
  obtain ⟨θ, hθ, hχ⟩ := h
  refine ⟨θ, fun PP => ?_, hχ⟩
  obtain ⟨d, b, σ, hσ, hx⟩ := hθ PP
  exact ⟨b, Fin d → ℂ, inferInstance, inferInstance, inferInstance, σ, hσ, hx⟩

theorem typeSum_base_eq_card : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_levels F → (∀ χ ∈ A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar D.what₂.embLL R.Pg D.R.r fun g => χ (R.eG.symm g)) → ∀ [Fintype F.P0], ∀ χ ∈ A.X, ∑ h : F.P0, χ (h : G) * (((F.ψ0 h)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) = (Fintype.card F.P0 : D.what₂.LL) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hlev hind _ χ hχ
  have h := GlobalTheory.OneForm.oneVector_of_whittaker R F GlobalTheory.GenericProduct.oneWhittakerVector_holds hlev
    (fun χ hχ => isCuspIndProdChar_of_isProdCuspChar _ _ _ _ (hind χ hχ)) χ hχ
  rw [← Nat.card_eq_fintype_card, ← h, GlobalTheory.OneForm.typeSum]
  congr 1
  exact congrArg (fun i => @Finset.univ _ i) (Subsingleton.elim _ _)

end GlobalTheory.RealOneVector
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralAdelicElementExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameMove

open Formalism.UG (bc cT)

theorem conj_gram {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (β G h : GL (Fin n) A) (hG : G.val = cT σ β.val * J * β.val)
    (hx : β * h * β⁻¹ ∈ Formalism.UG.UJ σ J) :
    (G * h * G⁻¹).val = cT σ (h⁻¹).val := by
  have hx' : cT σ (β * h * β⁻¹).val * J * (β * h * β⁻¹).val = J := hx
  have e1 : cT σ h.val * G.val * h.val = G.val := by
    have e : (β * h * β⁻¹).val * β.val = β.val * h.val := by
      rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul]
    calc cT σ h.val * G.val * h.val = cT σ (β.val * h.val) * J * (β.val * h.val) := by
          rw [hG, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ β.val * (cT σ (β * h * β⁻¹).val * J * (β * h * β⁻¹).val) * β.val := by
          rw [← e, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = G.val := by rw [hx', hG]
  have e2 : cT σ (h⁻¹).val * cT σ h.val = 1 := by
    rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
  calc (G * h * G⁻¹).val = (cT σ (h⁻¹).val * cT σ h.val) * (G.val * h.val * (G⁻¹).val) := by
        rw [e2, Matrix.one_mul]; rfl
    _ = cT σ (h⁻¹).val * ((cT σ h.val * G.val * h.val) * (G⁻¹).val) := by simp only [Matrix.mul_assoc]
    _ = cT σ (h⁻¹).val := by rw [e1, Units.mul_inv, Matrix.mul_one]

theorem conj_gram_sub {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (O : Subring A) (J : Matrix (Fin n) (Fin n) A)
    (β : GL (Fin n) A) (G h : GL (Fin n) O) (hG : (bc O.subtype G).val = cT σ β.val * J * β.val)
    (hx : β * bc O.subtype h * β⁻¹ ∈ Formalism.UG.UJ σ J) (i j : Fin n) :
    (((G * h * G⁻¹).val i j : O) : A) = σ ((h⁻¹).val j i : O) := by
  have c := conj_gram σ J β (bc O.subtype G) (bc O.subtype h) hG hx
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul] at c
  exact congrFun (congrFun c i) j

end GlobalTheory.FrameMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentPreservesLatticeHat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.LatLoc

theorem loc_transfer {R : Type} [CommRing R] {n : ℕ} {S : Subring R} (H₀ H₁ : Submodule S (Fin n → R)) (N : ℕ)
    (u : S) (ε : R) (hu : (u : R) * N = ε) (hε : ε * ε = ε) (h : ∀ y ∈ H₀, (N : R) • y ∈ H₁) (z : Fin n → R)
    (hz : (fun a => ε * z a) ∈ H₀) : (fun a => ε * z a) ∈ H₁ := by
  have h1 := H₁.smul_mem u (h _ hz)
  convert h1 using 1
  funext a
  show ε * z a = (u : R) * ((N : R) * (ε * z a))
  rw [← mul_assoc, hu, ← mul_assoc, hε]


end GlobalTheory.LatLoc
end
