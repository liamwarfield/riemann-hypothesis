module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiagonalConjEdgeSumAddCharFiniteField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridNuUnitTrivial
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem hasIwasawa_KAd_selfDual : ∀ (D : D7) (A : HSp D) (L : Lat A) (a : GL (Fin A.rank) (AE D)), IsSelfDualC A L → IsMaj A a → HasIwasawa D.sp.cm.sig (dblSp A).gram (KAd D.sp.cm.sig (dblSp A).gram L a) := by
  intro D A L a hL ha
  have : Submodule.IsFullLattice D.host.E L := Formalism.IndefR.Fin.PDA.selfDual_isFullLattice A L hL
  refine HasIwasawa.adelic (fun v => ?_) (fun w => GlobalTheory.T.iwasawa_doubled_hermitian_space_real_place D A a ha w)
  by_cases hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v
  · exact GlobalTheory.T.hasIwasawaDecomposition_doubled_split_place D A L hL v hv
  · exact GlobalTheory.T.iwasawa_doubled_hermitian_space_nonsplit_place D A L hL v hv

theorem hasIwasawa_Khat (D : D7) (A : HSp D) (a : GL (Fin A.rank) (AE D)) (ha : IsMaj A a) :
    HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
  hasIwasawa_KAd_selfDual D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) ha

end GlobalTheory.Core.Rk.IP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLatticeStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice : ∀ (D : D7) (A : HSp D) (L : Lat A) (a : GL (Fin A.rank) (AE D)), IsSelfDualC A L → IsMaj A a → HasIwasawa D.sp.cm.sig (dblSp A).gram (KAd D.sp.cm.sig (dblSp A).gram L a) := by
  first | exact @GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual | exact GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual | (intros; apply GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqOfSplitPartAgreeSupportedAtSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqOfSplitPartAgreeSupportedAtSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

noncomputable section

namespace GlobalTheory.UnitSplit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem mt_mul (S : HSp D) (g g' : GA D S) : mt S (g * g') = mt S g * mt S g' := by
  simp [Formalism.L2.Theta.mt]

theorem mt_one (S : HSp D) : mt S 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem eq_of_parts {A : Type*} [CommRing A] {e f m m' o : A} (k1 : (e + f) * (m - o) = m - o)
    (k2 : (e + f) * (m' - o) = m' - o) (k3 : e * m = e * m') (k4 : f * m' = f * m) : m = m' := by
  linear_combination (-1 : A) * k1 + k2 + k3 - k4

theorem mt_unit (S : HSp D) (g : GA D S) :
    ((mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) * mt S g = (HSpace.gram S).map (incA D) := g.2

theorem gram_mul_conj_inv (S : HSp D) (e : AE D) (g : GA D S) :
    (HSpace.gram S).map (incA D) * (cA D e • mt S g⁻¹) =
      ((e • mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) := by
  have hu := mt_unit S g
  have h1 : mt S g * mt S g⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  have hmap : (e • mt S g).map (cA D) = cA D e • (mt S g).map (cA D) := by
    ext i j; simp [Matrix.map_apply, map_mul]
  rw [hmap, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  calc (HSpace.gram S).map (incA D) * mt S g⁻¹
      = ((mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) * mt S g * mt S g⁻¹ := by rw [hu]
    _ = ((mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) := by
        rw [Matrix.mul_assoc _ (mt S g), h1, Matrix.mul_one]

theorem eq_of_split_part : ∀ (D : D7) (S : HSp D) (e : AE D) (h h' : GA D S), IsSplitIdem D e → SuppAt e S h →
    SuppAt e S h' → (∀ i j, e * Formalism.L2.Theta.mt S h i j = e * Formalism.L2.Theta.mt S h' i j) → h = h' := by
  intro D S e h h' _ hs hs' hee
  have hJu : IsUnit ((HSpace.gram S).map (incA D)).det := by
    have hd : ((HSpace.gram S).map (incA D)).det = incA D (HSpace.gram S).det := by
      rw [RingHom.map_det]; rfl
    rw [hd]; exact (gram_isUnit_det S).map _
  have hE : e • mt S h = e • mt S h' := by
    ext i j; simp only [Matrix.smul_apply, smul_eq_mul]; exact hee i j
  have hN : cA D e • mt S h⁻¹ = cA D e • mt S h'⁻¹ := by
    have h2 := (gram_mul_conj_inv S e h).trans
      ((congrArg (fun X : Matrix (Fin S.rank) (Fin S.rank) (AE D) => (X.map (cA D)).transpose * (HSpace.gram S).map (incA D)) hE).trans
        (gram_mul_conj_inv S e h').symm)
    have h3 := congrArg (fun X => ((HSpace.gram S).map (incA D))⁻¹ * X) h2
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJu, Matrix.one_mul] using h3
  have a1 : mt S h⁻¹ * mt S h = 1 := by rw [← mt_mul, inv_mul_cancel, mt_one]
  have a2 : mt S h' * mt S h'⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  have hM : cA D e • mt S h' = cA D e • mt S h := by
    calc cA D e • mt S h' = cA D e • (mt S h' * mt S h⁻¹ * mt S h) := by
          rw [Matrix.mul_assoc, a1, Matrix.mul_one]
      _ = mt S h' * (cA D e • mt S h⁻¹) * mt S h := by
          simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = mt S h' * (cA D e • mt S h'⁻¹) * mt S h := by rw [hN]
      _ = cA D e • mt S h := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, a2, Matrix.one_mul]
  have hMM : mt S h = mt S h' := by
    ext i j
    have k1 := hs i j
    have k2 := hs' i j
    have k3 := hee i j
    have k4 : cA D e * mt S h' i j = cA D e * mt S h i j := by
      have := congrFun (congrFun hM i) j
      simp only [Matrix.smul_apply, smul_eq_mul] at this; exact this
    simp only [Matrix.sub_apply] at k1 k2
    exact eq_of_parts k1 k2 k3 k4
  exact Subtype.ext (Units.ext hMM)

end GlobalTheory.UnitSplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqOfSplitPartAgreeSupportedAtSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_splitPart_agree_supportedAtSplitPlace : ∀ (D : D7) (S : HSp D) (e : AE D) (h h' : GA D S), IsSplitIdem D e → SuppAt e S h → SuppAt e S h' →
    (∀ i j, e * Formalism.L2.Theta.mt S h i j = e * Formalism.L2.Theta.mt S h' i j) → h = h' := by
  first | exact @GlobalTheory.UnitSplit.eq_of_split_part | exact GlobalTheory.UnitSplit.eq_of_split_part | (intros; apply GlobalTheory.UnitSplit.eq_of_split_part <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

noncomputable section
namespace GlobalTheory.FrameAt
variable {D : D7}

theorem mem_congGrp (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ ∀ i j, (Formalism.L2.Theta.mt V g - 1) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  have key : ∀ i j, (Ideal.Quotient.mk I) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ I)) i j := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  constructor
  · intro h i j
    have := congrArg (fun u : GL (Fin V.rank) (AE D ⧸ I) => u.1 i j) h
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one] at this
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq, key]
    exact this
  · intro h
    ext i j
    have := h i j
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq, key] at this
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one]
    exact this

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem mt_mul (g h : GA D S) : Formalism.L2.Theta.mt S (g * h) = Formalism.L2.Theta.mt S g * Formalism.L2.Theta.mt S h := by
  simp [Formalism.L2.Theta.mt, map_mul]

theorem mt_one : Formalism.L2.Theta.mt S (1 : GA D S) = 1 := by
  simp [Formalism.L2.Theta.mt, map_one]

theorem pr_e (p : SplitPt D k) : p.pr p.e = 1 := by
  have h1 := p.pr_sec (p.pr 1)
  rw [p.sec_pr, mul_one, map_one] at h1
  exact h1

theorem gl_map (β : Frame p S n) (g : GL n k) :
    (Formalism.L2.Theta.mt S (β.gl g)).map p.pr = β.b * g.val * β.b' := β.gl_mat g

theorem gl_inj (β : Frame p S n) : Function.Injective β.gl := by
  intro g g' h
  have h1 := congrArg (fun x => β.b' * (Formalism.L2.Theta.mt S x).map p.pr * β.b) h
  simp only [gl_map] at h1
  have e1 : ∀ x : Matrix n n k, β.b' * (β.b * x * β.b') * β.b = x := by
    intro x
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, β.b'b, Matrix.one_mul, Matrix.mul_assoc, β.b'b, Matrix.mul_one]
  rw [e1, e1] at h1
  exact Units.ext h1

theorem det_at (β : Frame p S n) (g : GL n k) :
    ∃ x : (AE D)ˣ, IsDetAt p.e S (β.gl g) x ∧ p.pr x = g.val.det := by
  set a := (Formalism.L2.Theta.mt S (β.gl g)).det
  set c := (Formalism.L2.Theta.mt S (β.gl g⁻¹)).det
  have hee : p.e * p.e = p.e := p.split.1
  have hac : a * c = 1 := by
    simp only [a, c]
    rw [← Matrix.det_mul, ← mt_mul, ← map_mul, mul_inv_cancel, map_one, mt_one, Matrix.det_one]
  refine ⟨⟨p.e * a + (1 - p.e), p.e * c + (1 - p.e), ?_, ?_⟩, rfl, ?_⟩
  · linear_combination (2 - a - c) * hee + p.e * p.e * hac
  · linear_combination (2 - a - c) * hee + p.e * p.e * hac
  · simp only [Units.val_mk, map_add (f := _), map_mul, map_sub, map_one, pr_e p, one_mul, sub_self, add_zero]
    simp only [a]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, gl_map, Matrix.mul_assoc, Matrix.det_comm' β.bb' β.b'b, Matrix.mul_assoc, β.b'b,
      Matrix.mul_one]
end

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem mem_grpAt_iff (β : Frame p S n) (h : GA D S) : h ∈ grpAt S (· = p.v) ↔ ∃ g, h = β.gl g := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  have hL := (GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D p.v ε hε).1
  unfold grpAt
  rw [mem_congGrp]
  constructor
  · intro hh
    have hsupp : SuppAt p.e S h := by
      intro i j
      rw [hsum]
      exact (hL _).1 (hh i j)
    let M := (Formalism.L2.Theta.mt S h).map p.pr
    let M' := (Formalism.L2.Theta.mt S h⁻¹).map p.pr
    have hMM : M * M' = 1 := by
      simp only [M, M']
      rw [← Matrix.map_mul, ← mt_mul, mul_inv_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have hM'M : M' * M = 1 := by
      simp only [M, M']
      rw [← Matrix.map_mul, ← mt_mul, inv_mul_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have e2 : ∀ X Y : Matrix (Fin S.rank) (Fin S.rank) k,
        β.b' * X * β.b * (β.b' * Y * β.b) = β.b' * (X * Y) * β.b := by
      intro X Y
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc β.b β.b', β.bb', Matrix.one_mul]
    let g : GL n k := ⟨β.b' * M * β.b, β.b' * M' * β.b, by rw [e2, hMM, Matrix.mul_one, β.b'b],
      by rw [e2, hM'M, Matrix.mul_one, β.b'b]⟩
    refine ⟨g, GlobalTheory.T.eq_of_splitPart_agree_supportedAtSplitPlace D S p.e h (β.gl g) p.split hsupp (β.gl_supp g) ?_⟩
    intro i j
    rw [← p.sec_pr, ← p.sec_pr]
    congr 1
    have := congrArg (fun X => X i j) (gl_map β g)
    simp only [Matrix.map_apply] at this
    rw [this]
    show M i j = (β.b * (β.b' * M * β.b) * β.b') i j
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc β.b β.b', β.bb', Matrix.one_mul, Matrix.mul_one]
  · rintro ⟨g, rfl⟩ i j
    rw [(hL _)]
    have := β.gl_supp g i j
    rw [hsum] at this
    exact this
end

theorem frame_facts : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n), (∀ h : GA D S, h ∈ grpAt S (· = p.v) ↔ ∃ g, h = β.gl g) ∧ Function.Injective β.gl ∧ Continuous β.gl ∧ (∀ L : Lat S, IsSelfDualC S L → ∃ Λ : Submodule 𝒪[k] (n → k), Λ.IsLattice k ∧ β.IsLat L Λ ∧ ∀ g, InK S L (· = p.v) (β.gl g) ↔ g • Λ = Λ) ∧ (∀ (L : Lat S) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S L → Λ.IsFullLattice k → ∃ M : Lat S, IsSelfDualC S M ∧ β.IsLat M Λ ∧ latV S M (· ≠ p.v) = latV S L (· ≠ p.v)) ∧ ∀ g, ∃ x : (AE D)ˣ, IsDetAt p.e S (β.gl g) x ∧ p.pr x = g.val.det := by
  intro D k _ _ _ _ p S n _ _ β
  refine ⟨mem_grpAt_iff β, gl_inj β, GlobalTheory.T.continuous_splitPlaceHermitianFrame_GL_embedding D k p S n β, GlobalTheory.T.selfDual_splitComponent_isLattice_stabilizer_eq D k p S n β, ?_, det_at β⟩
  intro L Λ hL hΛ
  first
  | exact GlobalTheory.T.exists_selfDual_lattice_with_prescribed_splitComponent D k p S n β L Λ hL hΛ
  | exact GlobalTheory.T.exists_selfDual_lattice_with_prescribed_splitComponent D k p S n β L Λ hL hΛ.toIsLattice

end GlobalTheory.FrameAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFramePropertiesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceHermitianFrame_properties : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n), (∀ h : GA D S, h ∈ grpAt S (· = p.v) ↔ ∃ g, h = β.gl g) ∧ Function.Injective β.gl ∧ Continuous β.gl ∧ (∀ L : Lat S, IsSelfDualC S L → ∃ Λ : Submodule 𝒪[k] (n → k), Λ.IsLattice k ∧ β.IsLat L Λ ∧ ∀ g, InK S L (· = p.v) (β.gl g) ↔ g • Λ = Λ) ∧ (∀ (L : Lat S) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S L → Λ.IsFullLattice k → ∃ M : Lat S, IsSelfDualC S M ∧ β.IsLat M Λ ∧ latV S M (· ≠ p.v) = latV S L (· ≠ p.v)) ∧ ∀ g, ∃ x : (AE D)ˣ, IsDetAt p.e S (β.gl g) x ∧ p.pr x = g.val.det := by
  first | exact @GlobalTheory.FrameAt.frame_facts | exact GlobalTheory.FrameAt.frame_facts | (intros; apply GlobalTheory.FrameAt.frame_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardUnitaryChartDoubledSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardUnitaryChartDoubledSpace
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.ChartExist

open Formalism.UG

variable {R : Type} [CommRing R]

theorem cT_mul_gen (σ : R →+* R) {m p q : Type} [Fintype p] (M : Matrix m p R) (N : Matrix p q R) :
    cT σ (M * N) = cT σ N * cT σ M := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one_gen (σ : R →+* R) {n : Type} [Fintype n] [DecidableEq n] : cT σ (1 : Matrix n n R) = 1 := by
  simp [cT]

variable {n : Type} [Fintype n] [DecidableEq n]

theorem conj_mem (σ : R →+* R) (Q J : Matrix n n R) (T : GL n R) (c : Rˣ)
    (hT : cT σ (T : Matrix n n R) * Q * T = (c : R) • J) (g : GL n R) (hg : g ∈ UJ σ Q) :
    T⁻¹ * g * T ∈ UJ σ J := by
  have hg' : cT σ (g : Matrix n n R) * Q * g = Q := hg
  show cT σ (((T⁻¹ * g * T : GL n R)) : Matrix n n R) * J * ((T⁻¹ * g * T : GL n R) : Matrix n n R) = J
  have h1 : ((T⁻¹ : GL n R) : Matrix n n R) * T = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (T : Matrix n n R) * ((T⁻¹ : GL n R) : Matrix n n R) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h3 : cT σ ((T⁻¹ : GL n R) : Matrix n n R) * cT σ (T : Matrix n n R) = 1 := by
    rw [← cT_mul_gen, h2, cT_one_gen]
  have hJ : J = ((c⁻¹ : Rˣ) : R) • (cT σ (T : Matrix n n R) * Q * T) := by
    rw [hT, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [hJ]
  simp only [Units.val_mul, cT_mul_gen, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = cT σ (T : Matrix n n R) * cT σ (g : Matrix n n R) *
        (cT σ ((T⁻¹ : GL n R) : Matrix n n R) * cT σ (T : Matrix n n R)) * Q *
        ((T : Matrix n n R) * ((T⁻¹ : GL n R) : Matrix n n R)) * g * T := by
          simp only [Matrix.mul_assoc]
    _ = cT σ (T : Matrix n n R) * (cT σ (g : Matrix n n R) * Q * g) * T := by
          rw [h3, h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = cT σ (T : Matrix n n R) * Q * T := by rw [hg']

theorem conj_back (σ : R →+* R) (Q J : Matrix n n R) (T : GL n R) (c : Rˣ)
    (hT : cT σ (T : Matrix n n R) * Q * T = (c : R) • J) :
    cT σ ((T⁻¹ : GL n R) : Matrix n n R) * J * ((T⁻¹ : GL n R) : Matrix n n R) = ((c⁻¹ : Rˣ) : R) • Q := by
  have h2 : (T : Matrix n n R) * ((T⁻¹ : GL n R) : Matrix n n R) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h3 : cT σ ((T⁻¹ : GL n R) : Matrix n n R) * cT σ (T : Matrix n n R) = 1 := by
    rw [← cT_mul_gen, h2, cT_one_gen]
  have hJ : J = ((c⁻¹ : Rˣ) : R) • (cT σ (T : Matrix n n R) * Q * T) := by
    rw [hT, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [hJ, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc cT σ ((T⁻¹ : GL n R) : Matrix n n R) * (cT σ (T : Matrix n n R) * Q * T) * ((T⁻¹ : GL n R) : Matrix n n R)
      = (cT σ ((T⁻¹ : GL n R) : Matrix n n R) * cT σ (T : Matrix n n R)) * Q *
        ((T : Matrix n n R) * ((T⁻¹ : GL n R) : Matrix n n R)) := by simp only [Matrix.mul_assoc]
    _ = Q := by rw [h3, h2, Matrix.one_mul, Matrix.mul_one]

def conjEquiv (σ : R →+* R) (Q J : Matrix n n R) (T : GL n R) (c : Rˣ)
    (hT : cT σ (T : Matrix n n R) * Q * T = (c : R) • J) : UJ σ Q ≃* UJ σ J where
  toFun g := ⟨T⁻¹ * g.1 * T, conj_mem σ Q J T c hT g.1 g.2⟩
  invFun h := ⟨T * h.1 * T⁻¹, by
    have := conj_mem σ J Q T⁻¹ c⁻¹ (conj_back σ Q J T c hT) h.1 h.2
    rwa [inv_inv] at this⟩
  left_inv g := by ext1; simp [mul_assoc]
  right_inv h := by ext1; simp [mul_assoc]
  map_mul' g h := by ext1; simp [mul_assoc]

end GlobalTheory.StdUnn.ChartExist


open GlobalTheory.StdUnn.ChartExist in
theorem GlobalTheory.StdUnn.ChartExist.gram_adelic (D : D7) (A : HSp D) (μ : D.host.E)
    (hgram : (Tm A μ)ᴴ * (dblSp A).gram * Tm A μ = μ • Jst D A.rank)
    (T : GL (Fin (A.rank + A.rank)) (AE D)) (hTv : T.val = rat (Tm A μ)) (c : (AE D)ˣ) (hc : (c : AE D) = incA D μ) :
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) T.val
      * (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF D.host.F) (dblSp A).gram : Matrix (Fin (A.rank + A.rank)) (Fin (A.rank + A.rank)) (AE D)) * T.val
      = (c : AE D) • Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF D.host.F) (Jst D A.rank) := by
  have e1 : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) T.val = ((Tm A μ)ᴴ).map (incA D) := by
    rw [hTv]; ext i j; rfl
  rw [e1, hTv, hc]
  change ((Tm A μ)ᴴ).map (incA D) * ((dblSp A).gram).map (incA D) * (Tm A μ).map (incA D) = (incA D μ) • (Jst D A.rank).map (incA D)
  rw [← Matrix.map_mul, ← Matrix.map_mul, hgram]
  ext i j
  simp [Matrix.map_apply, map_mul]


open GlobalTheory.StdUnn.ChartExist in
theorem GlobalTheory.StdUnn.chart_exists : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∃ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ := by
  intro D A μ hμ
  obtain ⟨hgram, hdet, -⟩ := GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ
  have hdetR : IsUnit (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)).det := by
    have : (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)).det = incA D (Tm A μ).det := by
      rw [RingHom.map_det]; rfl
    rw [this]; exact hdet.map (incA D)
  let T : GL (Fin (A.rank + A.rank)) (AE D) := Matrix.nonsingInvUnit _ hdetR
  have hTv : T.val = rat (Tm A μ) := rfl
  have hμu : IsUnit (incA D μ) := (Ne.isUnit hμ.1).map (incA D)
  refine ⟨conjEquiv (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) _ _ T hμu.unit
    (gram_adelic D A μ hgram T hTv hμu.unit hμu.unit_spec), ?_⟩
  intro g
  show (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) * (T⁻¹ * g.1 * T).val = g.1.val * rat (Tm A μ)
  rw [← hTv]
  simp only [Units.val_mul, ← Matrix.mul_assoc]
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardUnitaryChartDoubledSpaceStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardUnitaryChart_doubledSpace : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∃ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ := by
  first | exact @GlobalTheory.StdUnn.chart_exists | exact GlobalTheory.StdUnn.chart_exists | (intros; apply GlobalTheory.StdUnn.chart_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RightTranslateCommutesCenterAction
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.CentreRight

open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.PointAtPlaceHom
open Formalism.MainNotions.StandardLattice (infMat)

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem rTr_mem_fin {u : GA D V} (hu : u ∈ GfC V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) : rTr V u φ ∈ SmFun θ V := by
  intro n τs Xs hX g
  have := hφ n τs Xs hX (g * u)
  convert this using 2 with t
  unfold rTr
  rw [mul_assoc, mul_assoc, comm_of_mem V (list_prod_mem fun a ha => ?_) hu]
  obtain ⟨b, rfl⟩ := List.mem_ofFn.1 ha
  exact atTau_mem V _ _

theorem rTr_mul (u a : GA D V) (φ : GA D V → ℂ) : rTr V (u * a) φ = rTr V u (rTr V a φ) := by
  funext g
  simp only [rTr, mul_assoc]

theorem decomp (hθ : IsInfFam θ) (x : GA D V) : ∃ u ∈ GfC V, ∃ a, IsRealPt θ a ∧ x = u * a := by
  obtain ⟨u, hu, a, ha, e⟩ := Formalism.IndefR.TopMult.ga_decomp x
  exact ⟨u, hu, a, ⟨ha, GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a⟩, e⟩

theorem rTr_mem_all (hθ : IsInfFam θ) (x : GA D V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) : rTr V x φ ∈ SmFun θ V := by
  obtain ⟨u, hu, a, ha, rfl⟩ := decomp hθ x
  rw [rTr_mul]
  exact rTr_mem_fin hu (rTr_mem hθ ha hφ)

theorem gelf_rTr_all (hθ : IsInfFam θ) (x : GA D V) (τ : D.what₂.Tau) (k : ℕ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) :
    gelf θ V τ k (rTr V x φ) = rTr V x (gelf θ V τ k φ) := by
  obtain ⟨u, hu, a, ha, rfl⟩ := decomp hθ x
  rw [rTr_mul, rTr_mul, GlobalTheory.Mem.FinTranslate.gelf_rTr hu, gelf_rTr hθ ha τ k hφ]

end GlobalTheory.RegSch.CentreRight

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymm
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymm
open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem continuous_mat_pt (D : D7) (n : ℕ) : Continuous (mat : G D n → _) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_of_mat_pt {D : D7} {n : ℕ} {X : Type} [TopologicalSpace X] {φ : X → G D n}
    (h : Continuous fun x => mat (φ x)) (h' : Continuous fun x => mat (φ x)⁻¹) : Continuous φ :=
  Continuous.subtype_mk (f := fun x => AdelicU.matHom _ D.sp.cm.sig (Jst D n) (φ x))
    (Units.continuous_iff.2 ⟨h, h'⟩) _

theorem chart_continuous : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → Continuous κ ∧ Continuous κ.symm := by
  intro D A μ hμ κ hκ
  have hT := (Tm_gram_inv D A μ hμ).2.1
  have h₁ : (rat (Tm A μ)⁻¹ : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) * rat (Tm A μ) = 1 := by
    rw [← rat_mul, Matrix.nonsing_inv_mul _ hT, rat_one]
  have h₂ : (rat (Tm A μ) : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) * rat (Tm A μ)⁻¹ = 1 := by
    rw [← rat_mul, Matrix.mul_nonsing_inv _ hT, rat_one]
  have e₁ : ∀ g, mat (κ g) = (rat (Tm A μ)⁻¹ : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) *
      (Formalism.L2.Theta.mt (dblSp A) g * rat (Tm A μ)) := fun g => by
    rw [← hκ g, ← Matrix.mul_assoc, h₁, Matrix.one_mul]
  have e₂ : ∀ x, Formalism.L2.Theta.mt (dblSp A) (κ.symm x) =
      (rat (Tm A μ) : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) * mat x * rat (Tm A μ)⁻¹ := fun x => by
    have := hκ (κ.symm x)
    rw [κ.apply_symm_apply] at this
    rw [this]
    exact ((Matrix.mul_assoc _ _ _).trans ((congrArg _ h₂).trans (Matrix.mul_one _))).symm
  have c₁ : Continuous fun g => mat (κ g) := by
    simp only [e₁]
    exact continuous_const.matrix_mul ((continuous_mt (dblSp A)).matrix_mul continuous_const)
  refine ⟨continuous_of_mat_pt c₁ ?_, continuous_of_mt (dblSp A) ?_⟩
  · simp only [← map_inv]
    exact c₁.comp continuous_inv
  · simp only [e₂]
    exact (continuous_const.matrix_mul (continuous_mat_pt D A.rank)).matrix_mul continuous_const

end GlobalTheory.StdUnn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymmStatement
open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_standardUnitaryChart_and_symm : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → Continuous κ ∧ Continuous κ.symm := by
  first | exact @GlobalTheory.StdUnn.chart_continuous | exact GlobalTheory.StdUnn.chart_continuous | (intros; apply GlobalTheory.StdUnn.chart_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIff
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.ChartRat

variable {D : D7}

theorem mem_GF_iff {n : ℕ} (g : G D n) : g ∈ GF D n ↔ mat g ∈ ratMx D (n + n) (n + n) := by
  constructor
  · rintro ⟨γ, -, h⟩
    exact ⟨γ.1, congrArg Units.val h⟩
  · rintro ⟨γ, hγ⟩
    replace hγ : rat γ = mat g := hγ
    have h : γᴴ * Jst D n * γ = Jst D n := by
      apply rat_injective
      rw [rat_mul, rat_mul, rat_conjTranspose, hγ]
      exact g.2
    have hdet : γ.det ≠ 0 := by
      intro h0
      have hu : IsUnit (mat g).det := Matrix.isUnits_det_units _
      rw [← hγ, rat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at hu
      have h01 : (0 : AE D) = 1 := isUnit_zero_iff.1 hu
      exact zero_ne_one (incA_injective (D := D) (by rw [map_zero, map_one]; exact h01))
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero γ hdet, h, Units.ext hγ⟩

end GlobalTheory.StdUnn.ChartRat

namespace GlobalTheory.StdUnn

theorem chart_mem_GF_iff : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank,
    IsChart A μ κ → ∀ g, g ∈ GQ (dblSp A) ↔ κ g ∈ GF D A.rank := by
  intro D A μ hμ κ hκ g
  obtain ⟨-, hdet, -⟩ := GlobalTheory.T.doubledBasisSkewColumnMatrix_gram_inverse D A μ hμ
  have hTi : rat (Tm A μ)⁻¹ * rat (Tm A μ) = 1 := by
    rw [← rat_mul, Matrix.nonsing_inv_mul _ hdet, rat_one]
  have hTi' : rat (Tm A μ) * rat (Tm A μ)⁻¹ = 1 := by
    rw [← rat_mul, Matrix.mul_nonsing_inv _ hdet, rat_one]
  have e1 : mat (κ g) = rat (Tm A μ)⁻¹ * (mt (dblSp A) g * rat (Tm A μ)) := by
    rw [← hκ g, ← Matrix.mul_assoc, hTi, Matrix.one_mul]
  have e2 : mt (dblSp A) g = rat (Tm A μ) * mat (κ g) * rat (Tm A μ)⁻¹ := by
    rw [hκ g, Matrix.mul_assoc, hTi', Matrix.mul_one]
  rw [GlobalTheory.MixModel.mem_GQ_iff, ChartRat.mem_GF_iff]
  constructor
  · intro h
    rw [e1]
    exact ratMx_mul (rat_mem _) (ratMx_mul h (rat_mem _))
  · intro h
    rw [e2]
    exact ratMx_mul (ratMx_mul (rat_mem _) h) (rat_mem _)

end GlobalTheory.StdUnn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIffStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardUnitaryChart_mem_rational_iff : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ g, g ∈ GQ (dblSp A) ↔ κ g ∈ GF D A.rank := by
  first | exact @GlobalTheory.StdUnn.chart_mem_GF_iff | exact GlobalTheory.StdUnn.chart_mem_GF_iff | (intros; apply GlobalTheory.StdUnn.chart_mem_GF_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterActionSmoothCommuting
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CentreComm

open GlobalTheory.Mem.AutSpace

variable {D : D7} {θ : InfFam D} {V : HSp D}


variable (θ V) in
def CommOnSm (A B : (GA D V → ℂ) → (GA D V → ℂ)) : Prop := ∀ f ∈ SmFun θ V, A (B f) = B (A f)

theorem lin_sum {T : (GA D V → ℂ) → (GA D V → ℂ)} (hT : LinOnSm θ V T) {α : Type} (s : Finset α)
    (g : α → GA D V → ℂ) (hg : ∀ a ∈ s, g a ∈ SmFun θ V) : T (∑ a ∈ s, g a) = ∑ a ∈ s, T (g a) := by
  induction s using Finset.induction_on with
  | empty => simpa using hT.smul 0 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hT.add _ (hg a (by simp)) _
      (Submodule.sum_mem _ fun b hb => hg b (by simp [hb])), ih fun b hb => hg b (by simp [hb])]

theorem comm_foldr {T : (GA D V → ℂ) → (GA D V → ℂ)} {α : Type} (A : α → (GA D V → ℂ) → (GA D V → ℂ))
    (l : List α) (hl : ∀ a ∈ l, LinOnSm θ V (A a)) (hc : ∀ a ∈ l, CommOnSm θ V T (A a)) :
    CommOnSm θ V T fun f => l.foldr (fun a g => A a g) f := by
  induction l with
  | nil => exact fun _ _ => rfl
  | cons a l ih =>
    intro f hf
    have h2 := linOnSm_foldr A l fun b hb => hl b (by simp [hb])
    simp only [List.foldr_cons]
    rw [hc a (by simp) _ (h2.mem f hf), ih (fun b hb => hl b (by simp [hb])) (fun b hb => hc b (by simp [hb])) f hf]

theorem comm_gelf {T : (GA D V → ℂ) → (GA D V → ℂ)} (hT : LinOnSm θ V T) {τ : D.what₂.Tau}
    (hc : ∀ Z, CommOnSm θ V T (RderC θ V τ Z)) (k : ℕ) : CommOnSm θ V T (gelf θ V τ k) := by
  have hl : ∀ idx : Fin (k + 1) → Fin V.rank, ∀ S ∈ (List.ofFn fun a : Fin (k + 1) =>
      RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)), LinOnSm θ V S ∧ CommOnSm θ V T S := fun idx S hS => by
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hS
    exact ⟨linOnSm_RderC τ _, hc _⟩
  intro f hf
  simp only [gelf]
  rw [lin_sum hT _ _ fun idx _ => (linOnSm_foldr (fun S => S) _ fun S hS => (hl idx S hS).1).mem f hf]
  exact Finset.sum_congr rfl fun idx _ =>
    comm_foldr (fun S => S) _ (fun S hS => (hl idx S hS).1) (fun S hS => (hl idx S hS).2) f hf

theorem gelf_RderC (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (k : ℕ) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    CommOnSm θ V (gelf θ V τ k) (RderC θ V τ' Z) := by
  intro f hf
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ' Z
  simp only [RderC]
  rw [(linOnSm_gelf τ k).add _ (Rder_mem hf h1) _ (Submodule.smul_mem _ _ (Rder_mem hf h2)), (linOnSm_gelf τ k).smul,
    GlobalTheory.CuspLie.gelf_Rder hθ h1 hf, GlobalTheory.CuspLie.gelf_Rder hθ h2 hf]

end GlobalTheory.CentreComm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentAtTauMemStabilizer
noncomputable section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabAtPlace

variable {D : D7} {θ : InfFam D} {T T₀ : HSp D} {r : ℕ}

theorem mx_ext (hθ : IsInfFam θ) {m n : ℕ} {A B : Mx D m n} (hf : A.map (finPart D) = B.map (finPart D))
    (hi : ∀ τ, compAt θ τ A = compAt θ τ B) : A = B := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  ext i j
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · rw [RingHom.map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun hf i) j)
  · rw [RingHom.map_sub, RingHom.map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun (hi τ) i) j)

theorem comp_mul (τ : D.what₂.Tau) {m n k : ℕ} (A : Mx D m n) (B : Mx D n k) :
    compAt θ τ (A ⬝ B) = compAt θ τ A * compAt θ τ B :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem absE_single (hθ : IsInfFam θ) (x : (AE D)ˣ) (τ : D.what₂.Tau) (hf : finPart D (x : AE D) = 1)
    (hi : ∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) :
    absE D.host.F D.host.E x = ‖θ τ (infPart D (x : AE D))‖₊ ^ 2 := by
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).1
  haveI := hcm.1
  have e1 : (∏ᶠ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v x)) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by rw [GlobalTheory.HalfModTorus.unitFin_eq_one v _ hf, map_one]
  have hw : ∀ τ : D.what₂.Tau, absEw D.host.F D.host.E
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
      (unitInf D.host.F D.host.E _ x) = ‖θ τ (infPart D (x : AE D))‖₊ ^ 2 := by
    intro τ
    let t' : GlobalTheory.AdelicU.EmbOver D.host.E (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) :=
      ⟨tauE D τ, (InfinitePlace.embedding_mk_eq_of_isReal
        (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))).symm⟩
    rw [absEw_eq_sq hcm t', GlobalTheory.AutFunCompare.isInfEmb_unique _ _ _ (hθ τ) (GlobalTheory.AdelicU.isInfEmb_infProj t')]
    exact congrArg (fun z : ℂ => ‖z‖₊ ^ 2) (GlobalTheory.HalfModTorus.compInf_eq _ t' _)
  have e2 : (∏ w, absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w x)) = ‖θ τ (infPart D (x : AE D))‖₊ ^ 2 := by
    rw [← (GlobalTheory.CMTypePlaces.places_bijective D).prod_comp
      (fun w => absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w x))]
    simp only [hw]
    refine Finset.prod_eq_single τ (fun τ' _ c => ?_) fun c => absurd (Finset.mem_univ _) c
    rw [hi τ' c, nnnorm_one, one_pow]
  rw [absE_apply, e1, e2, mul_one]

end GlobalTheory.StabAtPlace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeightIoLe
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section
namespace GlobalTheory.Grow.IoHeight

theorem height_io_le (D : D7) (A : HSp D) (g₁ g₂ : GA D A) :
    GlobalTheory.Grow.height (dblSp A) (io A (g₁, g₂)) ≤ GlobalTheory.Grow.height A g₁ * GlobalTheory.Grow.height A g₂ := by
  have h := GlobalTheory.BlockHeight.heightGL_blk_le D.host.F (finSumFinEquiv (m := A.rank) (n := A.rank))
    (Formalism.L2.Theta.matHom (dblSp A) (io A (g₁, g₂))) (Formalism.L2.Theta.matHom A g₁) (Formalism.L2.Theta.matHom A g₂) rfl rfl
  show ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ) ≤ ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ) * ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ)
  exact_mod_cast h

theorem main : ∀ (D : D7) (A : HSp D), ∃ (C : ℝ) (c : ℕ), ∀ g₁ g₂ : GA D A, GlobalTheory.Grow.height (dblSp A) (io A (g₁, g₂)) ≤ C * (GlobalTheory.Grow.height A g₁ * GlobalTheory.Grow.height A g₂) ^ c :=
  fun D A => ⟨1, 1, fun g₁ g₂ => by simpa using height_io_le D A g₁ g₂⟩

end GlobalTheory.Grow.IoHeight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartSiegelLeviDetEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartSiegelLeviDetEq
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn

open Matrix GlobalTheory.Doubling

theorem chart_lowerLeft_zero {D : D7} {n : ℕ} {g : G D n} (hg : g ∈ P D n) (i j : Fin n) :
    mat g (Fin.natAdd n i) (Fin.castAdd n j) = 0 := by
  have hx : (Pi.single (Fin.castAdd n j) 1 : Fin (n + n) → AE D) ∈ upperHalf D n := by
    rw [upperHalf, LinearMap.mem_ker]
    funext k
    rw [LinearMap.funLeft_apply, Pi.zero_apply, finSumFinEquiv_apply_right]
    exact Pi.single_eq_of_ne (fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega) _
  have h1 := (hg (Pi.single (Fin.castAdd n j) 1)).1 hx
  rw [upperHalf, LinearMap.mem_ker] at h1
  have h2 := congrFun h1 i
  rw [LinearMap.funLeft_apply, Pi.zero_apply, finSumFinEquiv_apply_right, mulVec_single_one] at h2
  exact h2

end GlobalTheory.StdUnn

namespace GlobalTheory.StdUnn

open Matrix GlobalTheory.Doubling

theorem chart_levi_mul {D : D7} {A : HSp D} {μ : D.host.E} {κ : GA D (dblSp A) ≃* G D A.rank}
    (hκ : IsChart A μ κ) (p : GA D (dblSp A)) (hp : κ p ∈ P D A.rank) :
    leviMat finSumFinEquiv (mt (dblSp A) p) * rat A.gram⁻¹ = rat A.gram⁻¹ * blkA (mat (κ p)) := by
  ext i j
  have h := congrFun (congrFun (hκ p) (Fin.castAdd A.rank i)) (Fin.castAdd A.rank j)
  simp only [Matrix.mul_apply, Fin.sum_univ_add] at h
  simp only [Matrix.mul_apply, leviMat, blkA, toBlocks₁₁, toBlocks₁₂, Matrix.of_apply, submatrix_apply, add_mul,
    Finset.sum_add_distrib, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  simp only [Tm, rat, Matrix.map_apply, submatrix_apply, id, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, fromCols_apply_inl, fromCols_apply_inr, dblDec, stackRows,
    fromRows_apply_inl, fromRows_apply_inr, chart_lowerLeft_zero hp, mul_zero, Finset.sum_const_zero, add_zero] at h
  simp only [Matrix.add_apply, Matrix.of_apply, add_mul, Finset.sum_add_distrib, rat, Matrix.map_apply]
  exact h.symm

end GlobalTheory.StdUnn

namespace GlobalTheory.StdUnn

open Matrix GlobalTheory.Doubling

theorem chart_aP_eq_det : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank,
    IsChart A μ κ → ∀ (p : siegel A) (a : GL (Fin A.rank) (AE D)), blkA (mat (κ p)) = a.1 →
      aP A p = Matrix.GeneralLinearGroup.det a := by
  intro D A μ hμ κ hκ p a ha
  have hP : κ p ∈ P D A.rank := (GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D A μ hμ κ hκ p).1 p.2
  have h1 := congrArg Matrix.det (chart_levi_mul hκ p hP)
  rw [ha, Matrix.det_mul, Matrix.det_mul] at h1
  have hu : IsUnit (rat (D := D) A.gram⁻¹).det := by
    rw [rat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
    rw [Matrix.det_nonsing_inv]
    rw [Ring.inverse_eq_inv']
    exact inv_ne_zero (gram_det_ne A)
  refine Units.ext ?_
  change (leviMat finSumFinEquiv (mt (dblSp A) (p : GA D (dblSp A)))).det = a.1.det
  exact hu.mul_left_cancel (by rw [mul_comm]; exact h1)

end GlobalTheory.StdUnn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartSiegelLeviDetEqStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardUnitaryChart_siegelLeviDet_eq : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (p : siegel A) (a : GL (Fin A.rank) (AE D)), blkA (mat (κ p)) = a.1 → aP A p = Matrix.GeneralLinearGroup.det a := by
  first | exact @GlobalTheory.StdUnn.chart_aP_eq_det | exact GlobalTheory.StdUnn.chart_aP_eq_det | (intros; apply GlobalTheory.StdUnn.chart_aP_eq_det <;> assumption)
end
end
