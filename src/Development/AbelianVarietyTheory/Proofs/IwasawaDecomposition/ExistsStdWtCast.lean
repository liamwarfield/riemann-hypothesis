module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsClassSetPresentationCoefficientMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VvCastBVVRepr
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSelfDualLatticeCoordsIffIntegralPosSpace
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowLat

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev sw (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
  (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toAlgHom.toRingHom

abbrev swi (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    E ⊗[F] FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F ⊗[F] E :=
  (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm.toAlgHom.toRingHom

theorem swi_sw (z : FiniteAdeleRing (𝓞 F) F ⊗[F] E) : swi F E (sw F E z) = z :=
  (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm_apply_apply z

theorem swi_tmul (a : FiniteAdeleRing (𝓞 F) F) (x : E) : swi F E (x ⊗ₜ[F] a) = a ⊗ₜ[F] x := by
  show (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm (x ⊗ₜ[F] a) = a ⊗ₜ[F] x
  rw [AlgEquiv.symm_apply_eq]; rfl

theorem mem_stdLat_iff {m : ℕ} (y : Fin m → E) :
    y ∈ Formalism.L2.Col.stdLat E m ↔ ∀ i, y i ∈ Set.range (algebraMap (𝓞 E) E) := by
  simp [Formalism.L2.Col.stdLat, Submodule.mem_pi, Submodule.mem_one]

theorem intAf_mem {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Formalism.MainNotions.StandardLattice.intAf F) : a ∈ Formalism.UG.intAd F := fun v => ha v

theorem intAd_mem {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Formalism.UG.intAd F) : a ∈ Formalism.MainNotions.StandardLattice.intAf F := fun v => ha v

variable {n m : ℕ} (e : Fin n ≃ Fin m) (L : Set (Fin n → E))

theorem latHat_to_latS (hL : ∀ x, x ∈ L ↔ ∀ i, x i ∈ Set.range (algebraMap (𝓞 E) E)) (w : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E)
    (hw : w ∈ Formalism.MainNotions.StandardLattice.latHat F E L) :
    (fun j => sw F E (w (e.symm j))) ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) (Formalism.L2.Col.stdLat E m) := by
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    have hmem : (1 : E) ⊗ₜ[F] a ∈ Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F) :=
      Subring.subset_closure (Or.inr ⟨⟨a, intAf_mem ha⟩, rfl⟩)
    have hx' : (fun j => x (e.symm j)) ∈ Formalism.L2.Col.stdLat E m := (mem_stdLat_iff _).2 fun j => (hL x).1 hx _
    have h2 : (fun j => sw F E (a ⊗ₜ[F] x (e.symm j))) =
        (⟨_, hmem⟩ : Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) •
          (fun j => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x (e.symm j))) := by
      funext j
      show x (e.symm j) ⊗ₜ[F] a = ((1 : E) ⊗ₜ[F] a) * (x (e.symm j) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hx', rfl⟩)
  | zero =>
    have : (fun j => sw F E ((0 : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E) (e.symm j))) = 0 := by
      funext j; simp
    rw [this]; exact zero_mem _
  | add y z _ _ hy hz =>
    have : (fun j => sw F E ((y + z) (e.symm j))) = (fun j => sw F E (y (e.symm j))) + (fun j => sw F E (z (e.symm j))) := by
      funext j; simp
    rw [this]; exact add_mem hy hz
  | neg y _ hy =>
    have : (fun j => sw F E ((-y) (e.symm j))) = -(fun j => sw F E (y (e.symm j))) := by
      funext j; simp
    rw [this]; exact neg_mem hy

theorem mul_latHat (hL : ∀ x, x ∈ L ↔ ∀ i, x i ∈ Set.range (algebraMap (𝓞 E) E)) (s : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hs : s ∈ Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) :
    ∀ w ∈ Formalism.MainNotions.StandardLattice.latHat F E L, (fun i => swi F E s * w i) ∈ Formalism.MainNotions.StandardLattice.latHat F E L := by
  induction hs using Subring.closure_induction with
  | mem s hs =>
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      rcases hs with ⟨⟨c, hc⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
      · obtain ⟨o, rfl⟩ := RingHom.mem_range.1 hc
        apply AddSubgroup.subset_closure
        refine ⟨a, ha, fun i => algebraMap (𝓞 E) E o * x i, (hL _).2 fun i => ?_, ?_⟩
        · obtain ⟨p, hp⟩ := (hL x).1 hx i
          exact ⟨o * p, by rw [map_mul, hp]⟩
        · funext i
          show swi F E (algebraMap (𝓞 E) E o ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * (a ⊗ₜ[F] x i) =
            a ⊗ₜ[F] (algebraMap (𝓞 E) E o * x i)
          rw [swi_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      · apply AddSubgroup.subset_closure
        refine ⟨b * a, intAd_mem (mul_mem hb (intAf_mem ha)), x, hx, ?_⟩
        funext i
        show swi F E ((1 : E) ⊗ₜ[F] b) * (a ⊗ₜ[F] x i) = (b * a) ⊗ₜ[F] x i
        rw [swi_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    | zero =>
      have : (fun i => swi F E s * (0 : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E) i) = 0 := by
        funext i; simp
      rw [this]; exact zero_mem _
    | add y z _ _ hy hz =>
      have : (fun i => swi F E s * (y + z) i) = (fun i => swi F E s * y i) + (fun i => swi F E s * z i) := by
        funext i; simp [mul_add]
      rw [this]; exact add_mem hy hz
    | neg y _ hy =>
      have : (fun i => swi F E s * (-y) i) = -(fun i => swi F E s * y i) := by
        funext i; simp
      rw [this]; exact neg_mem hy
  | zero =>
    intro w _
    have : (fun i => swi F E 0 * w i) = 0 := by funext i; simp
    rw [this]; exact zero_mem _
  | one =>
    intro w hw
    have : (fun i => swi F E 1 * w i) = w := by funext i; simp
    rw [this]; exact hw
  | add s t _ _ hs ht =>
    intro w hw
    have : (fun i => swi F E (s + t) * w i) = (fun i => swi F E s * w i) + (fun i => swi F E t * w i) := by
      funext i; simp [add_mul]
    rw [this]; exact add_mem (hs w hw) (ht w hw)
  | neg s _ hs =>
    intro w hw
    have : (fun i => swi F E (-s) * w i) = -(fun i => swi F E s * w i) := by
      funext i; simp
    rw [this]; exact neg_mem (hs w hw)
  | mul s t _ _ hs ht =>
    intro w hw
    have : (fun i => swi F E (s * t) * w i) = (fun i => swi F E s * (fun i => swi F E t * w i) i) := by
      funext i; simp [mul_assoc]
    rw [this]; exact hs _ (ht w hw)

theorem latS_to_latHat (hL : ∀ x, x ∈ L ↔ ∀ i, x i ∈ Set.range (algebraMap (𝓞 E) E)) (v : Fin m → E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hv : v ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) (Formalism.L2.Col.stdLat E m)) :
    (fun i => swi F E (v (e i))) ∈ Formalism.MainNotions.StandardLattice.latHat F E L := by
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨1, intAd_mem (one_mem _), fun i => x (e i), (hL _).2 fun i => (mem_stdLat_iff x).1 hx _, ?_⟩
    funext i
    show swi F E (x (e i) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x (e i)
    exact swi_tmul _ _
  | zero =>
    have : (fun i => swi F E ((0 : Fin m → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (e i))) = 0 := by
      funext i; simp
    rw [this]; exact zero_mem _
  | add y z _ _ hy hz =>
    have : (fun i => swi F E ((y + z) (e i))) = (fun i => swi F E (y (e i))) + (fun i => swi F E (z (e i))) := by
      funext i; simp
    rw [this]; exact add_mem hy hz
  | smul s y _ hy =>
    have : (fun i => swi F E ((s • y) (e i))) = (fun i => swi F E (s : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * (fun i => swi F E (y (e i))) i) := by
      funext i
      show swi F E ((s : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * y (e i)) = _
      rw [map_mul]
    rw [this]; exact mul_latHat L hL _ s.2 _ hy

theorem mem_iff_swap (hL : ∀ x, x ∈ L ↔ ∀ i, x i ∈ Set.range (algebraMap (𝓞 E) E))
    (g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)) (x : Fin n → E) :
    ((g⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)) : Matrix (Fin n) (Fin n) _).mulVec
        (fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i) ∈ Formalism.MainNotions.StandardLattice.latHat F E L ↔
      (fun j => x (e.symm j)) ∈ Formalism.UG.CS.globLat
        (Units.map (Matrix.reindexAlgEquiv (E ⊗[F] FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) e).toMonoidHom
          (Formalism.UG.bc (sw F E) g)) (Formalism.L2.Col.stdLat E m) := by
  set w := ((g⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)) : Matrix (Fin n) (Fin n) _).mulVec
        (fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i) with hw
  have hv : (((Units.map (Matrix.reindexAlgEquiv (E ⊗[F] FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) e).toMonoidHom
          (Formalism.UG.bc (sw F E) g))⁻¹ : GL (Fin m) _) : Matrix (Fin m) (Fin m) _).mulVec
        (fun j => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x (e.symm j))) = fun j => sw F E (w (e.symm j)) := by
    rw [← map_inv, ← map_inv]
    funext j
    rw [hw]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Formalism.UG.inclE]
  show w ∈ _ ↔ _ ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) (Formalism.L2.Col.stdLat E m)
  rw [hv]
  constructor
  · exact latHat_to_latS e L hL w
  · intro h
    have := latS_to_latHat e L hL _ h
    simpa [swi_sw] using this

end Gen

theorem mem_selfDualLatticeCoords_iff_integral_posSpace (D : D7) (W : HSpace D.host.E) (hstar : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ)
    (hW : W = Formalism.BasicNotions.Examples₂.posSpace hstar N) (x : Fin W.rank → D.host.E) :
    x ∈ L0c D W ↔ ∀ i, x i ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := by
  subst hW
  revert x
  show ∀ x : Fin N → D.host.E, (∑ i, x i • (Pi.basisFun D.host.E (Fin N)) i) ∈ Formalism.BasicNotions.Examples₂.stdLat N ↔
    ∀ i, x i ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)
  intro x
  have hsum : (∑ i, x i • (Pi.basisFun D.host.E (Fin N)) i) = x := by
    simpa only [Pi.basisFun_repr] using (Pi.basisFun D.host.E (Fin N)).sum_repr x
  rw [hsum, Formalism.BasicNotions.Examples₂.stdLat, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩ i
    refine ⟨c i, ?_⟩
    have e1 : (∑ j, c j • (Pi.basisFun D.host.E (Fin N)) j) i = c i • (1 : D.host.E) := by
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · simp [Pi.basisFun_apply]
      · intro b _ hb
        simp [Pi.basisFun_apply, Pi.single_apply, Ne.symm hb]
      · simp
    rw [← congrFun hc i, e1, Algebra.smul_def, mul_one]
  · intro hx
    choose c hc using hx
    refine ⟨c, ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp [Pi.basisFun_apply, Algebra.smul_def, hc]
    · intro b _ hb
      simp [Pi.basisFun_apply, Pi.single_apply, Ne.symm hb]
    · simp

theorem mem_selfDualLatticeCoords_iff_integral_rowSpace (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok)
    (x : Fin X.toD7.sp.X'.rank → X.toD7.host.E) :
    x ∈ L0c X.toD7 X.toD7.sp.X' ↔ ∀ i, x i ∈ Set.range (algebraMap (𝓞 X.toD7.host.E) X.toD7.host.E) := by
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  exact mem_selfDualLatticeCoords_iff_integral_posSpace X.toD7 X.toD7.sp.X' hs _ h2 x

theorem hLat_eq_decoAd_N : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), X.B.fields.Ok → I.Ok →
    ∀ (U : Set I.ι) (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X'),
      Bridge.hLat X.toD7.sp.X' h = ((RowAd.decoAd X I t h).1.N).map
        (LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (RowAd.rank_X' X).symm).symm).toLinearMap := by
  intro X px I _ hI U t h
  have hN : (RowAd.decoAd X I t h).1.N = Formalism.UG.CS.globLat (RowAd.ptE X h) (Formalism.L2.Col.stdLat _ _) := by
    unfold RowAd.decoAd Formalism.L2.Col.decoOf
    split_ifs with h1
    · rfl
    · exact absurd (Formalism.L2.Col.decorated_lattice_exists X.toD7.sp.cm _ _ _ _ (RowDeco.ptE_mem_UAd X I hI h)) h1
  rw [hN]
  unfold Bridge.hLat
  conv_rhs => rw [← Submodule.span_eq ((Formalism.UG.CS.globLat (RowAd.ptE X h) (Formalism.L2.Col.stdLat _ _)).map
        (LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (RowAd.rank_X' X).symm).symm).toLinearMap)]
  congr 1
  ext x
  exact (mem_iff_swap (finCongr (RowAd.rank_X' X)) (L0c X.toD7 X.toD7.sp.X') (mem_selfDualLatticeCoords_iff_integral_rowSpace X I hI) h.1 x).trans
    (Submodule.mem_map_equiv (e := LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (RowAd.rank_X' X).symm).symm) _).symm

end GlobalTheory.Mem.R3.RowLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowActSmulOfWeight
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.RowsSign

open MvPolynomial
open scoped ComplexOrder

section General

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem degree_of_colWeight {ν : Fin n → ℕ} (m : Fin n × Fin n →₀ ℕ)
    (h : Finsupp.weight (Formalism.GradedWeylDivisibility.colW n n) m = ν) : (m.sum fun _ k => k) = ∑ j, ν j := by
  classical
  rw [← h, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply]

theorem rowAct_smul_of_weight {R : Type} [CommRing R] {ν : Fin n → ℕ} (c : R) (g : Matrix (Fin n) (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW n n) f ν) :
    Formalism.GradedWeylDivisibility.rowAct R (c • g) f = c ^ (∑ j, ν j) • Formalism.GradedWeylDivisibility.rowAct R g f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← degree_of_colWeight m (hf (mem_support_iff.mp hm))]
  have h1 : ∀ v : Fin n × Fin n, (∑ b : Fin n, C ((c • g) v.1 b) * X (b, v.2) : MvPolynomial (Fin n × Fin n) R) =
      C c * ∑ b : Fin n, C (g v.1 b) * X (b, v.2) := by
    intro v
    simp only [Matrix.smul_apply, smul_eq_mul, C_mul, Finset.mul_sum, mul_assoc]
  simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_monomial, h1, Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, smul_eq_C_mul, C_pow]
  ring

def totDeg (lam : ι → DomWeight n) : ℕ := ∑ τ, ∑ j, (lam τ).natW j

theorem blockAct_smul_of_mem (lam : ι → DomWeight n) (a : K) (M : ι → Matrix (Fin n) (Fin n) K)
    {y : Formalism.L2.DIV.Pol K ι n} (hy : y ∈ Formalism.L2.DIV.VV K lam) :
    Formalism.GradedWeylDivisibility.blockAct K (fun τ => a • M τ) y = a ^ totDeg lam • Formalism.GradedWeylDivisibility.blockAct K M y := by
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hy
  induction hy using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨F, hF, rfl⟩ := hP
    have hT := (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n (fun τ => a • M τ)).1
    have hT' := (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n M).1
    have h2 : ∀ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.rowAct K (a • M τ) (F τ)) =
        C (a ^ (∑ j, (lam τ).natW j)) * Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.rowAct K (M τ) (F τ)) := by
      intro τ
      rw [rowAct_smul_of_weight a (M τ) (F τ) (Formalism.GradedWeylDivisibility.mem_dualWeyl_iff.1 (hF τ)).1, map_smul, smul_eq_C_mul]
    rw [map_prod, map_prod]
    simp only [hT, hT']
    rw [Finset.prod_congr rfl fun τ _ => h2 τ, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum,
      smul_eq_C_mul]
    rfl
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, map_smul, hx, smul_comm]

variable [StarRing K]

def negSign (lam : ι → DomWeight n) : K := gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * (-1) ^ totDeg lam

theorem pairK_neg (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) (x y : Formalism.L2.DIV.VV K lam) :
    pairK lam (fun τ => -G τ) x y = negSign lam * pairK lam G x y := by
  have hy := blockAct_smul_of_mem lam (-1 : K) (fun τ => (G τ)ᵀ) y.2
  have hT : (fun τ => (-G τ)ᵀ) = fun τ => (-1 : K) • (G τ)ᵀ := by
    funext τ
    rw [Matrix.transpose_neg, neg_one_smul]
  have hg : gramTw lam (fun τ => -G τ) = gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * gramTw lam G := by
    unfold gramTw
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← mul_zpow, ← Matrix.det_mul, neg_mul, one_mul]
  simp only [pairK, pairP, LinearMap.domRestrict₁₂_apply, LinearMap.smul_apply, LinearMap.compl₂_apply,
    AlgHom.toLinearMap_apply, smul_eq_mul]
  rw [hT, hy, map_smul, hg, negSign, smul_eq_mul]
  ring

theorem negSign_mul_self (lam : ι → DomWeight n) : negSign (K := K) lam * negSign lam = 1 := by
  have hd : ((-1 : Matrix (Fin n) (Fin n) K)).det * ((-1 : Matrix (Fin n) (Fin n) K)).det = 1 := by
    rw [← Matrix.det_mul, neg_mul_neg, one_mul, Matrix.det_one]
  have hz : ∀ e : ℤ, ((-1 : Matrix (Fin n) (Fin n) K)).det ^ e * ((-1 : Matrix (Fin n) (Fin n) K)).det ^ e = 1 := by
    intro e
    rw [← mul_zpow, hd, _root_.one_zpow]
  have hp : ((-1 : K) ^ totDeg lam) * (-1) ^ totDeg lam = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hgg : gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) = 1 := by
    unfold gramTw
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun τ _ => hz _
  calc negSign (K := K) lam * negSign lam
      = (gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K))) *
        (((-1 : K) ^ totDeg lam) * (-1) ^ totDeg lam) := by unfold negSign; ring
    _ = 1 := by rw [hgg, hp, one_mul]

end General

end GlobalTheory.RowsSign

namespace GlobalTheory.RowsSign

open scoped ComplexOrder InnerProductSpace

theorem pairV_neg_one_eq {E K : Type} [Field E] [Field K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ}
    (emb : ι → E →+* K) (lam : ι → DomWeight n) (φ : K →+* ℂ) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (c0 : Formalism.L2.DIV.VV K lam →ₛₗ[φ] W)
    (h : ∀ x y, inner ℂ (c0 x) (c0 y) = φ (pairV emb lam (-1) x y)) :
    ∀ x y, pairV emb lam (-1) x y = pairV emb lam 1 x y := by
  have hG : gramK emb (-1 : Matrix (Fin n) (Fin n) E) = fun τ => -(gramK emb 1 τ) := by
    funext τ
    ext i j
    simp [gramK, Matrix.neg_apply, Matrix.one_apply]
  have hneg : ∀ x y, pairV emb lam (-1) x y = negSign lam * pairV emb lam 1 x y := by
    intro x y
    unfold pairV
    rw [hG, pairK_neg]
  by_cases hnt : Nontrivial (Formalism.L2.DIV.VV K lam)
  · rcases mul_self_eq_one_iff.1 (negSign_mul_self (K := K) lam) with hc | hc
    · intro x y
      rw [hneg, hc, one_mul]
    · exfalso
      have hpos := Formalism.L2.DIV.pairPos K ι n lam (gramK emb 1) φ (fun τ => by
        have : ((gramK emb (1 : Matrix (Fin n) (Fin n) E) τ).map φ) = 1 := by
          ext i j
          simp [gramK, Matrix.one_apply]
        rw [this]
        exact Matrix.PosDef.one)
      obtain ⟨i⟩ := (bVV K lam).index_nonempty
      have h1 := hpos.diag_pos (i := i)
      simp only [Matrix.of_apply] at h1
      have h2 := h (bVV K lam i) (bVV K lam i)
      rw [hneg, hc, neg_one_mul, map_neg] at h2
      have h3 := inner_self_nonneg (𝕜 := ℂ) (x := c0 (bVV K lam i))
      rw [h2, map_neg, RCLike.re_to_complex] at h3
      have h4 := (Complex.lt_def.1 h1).1
      have h5 : (φ (pairV emb lam 1 (bVV K lam i) (bVV K lam i))).re =
          (φ (pairK lam (gramK emb 1) (bVV K lam i) (bVV K lam i))).re := rfl
      simp only [Complex.zero_re] at h4
      linarith
  · rw [not_nontrivial_iff_subsingleton] at hnt
    intro x y
    rw [Subsingleton.elim x 0]
    simp

end GlobalTheory.RowsSign

open GlobalTheory.RowsSign in
theorem GlobalTheory.RowsSign.pairV_gramR_eq : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (c0R : Formalism.L2.DIV.VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W), cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) → Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) → (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) → ∀ x y, pairV (labLL X.toD7) (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) gramR x y = pairV (labLL X.toD7) (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) X.toD7.sp.X'.gram x y := by
  intro X px I hI cX gramR c0R hcX hg htie hinner x y
  have hJ : X.toD7.sp.X'.gram = 1 := by
    obtain ⟨hs, -, h2, -⟩ := hI.spaces
    change X.B.sp.X'.gram = 1
    rw [h2]
    refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
    simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]
  rcases hg with rfl | rfl
  · rfl
  · rw [hJ] at hinner ⊢
    exact pairV_neg_one_eq _ _ _ c0R hinner x y
end
end

noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.RowStd

section Cast

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] {n n' : ℕ}

def castSp (h : n = n') : (Fin n → E) ≃ₗ[E] (Fin n' → E) :=
  LinearEquiv.funCongrLeft E E (finCongr h).symm

def SameWt (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n') : Prop :=
  ∀ τ i, (lam' τ).w i = (lam τ).w (Fin.cast h.symm i)

theorem sameWt_eq (lam lam' : ι → DomWeight n) (hl : SameWt rfl lam lam') : lam' = lam := by
  funext τ
  cases h1 : lam' τ with
  | mk w a =>
    cases h2 : lam τ with
    | mk w' a' =>
      have : w = w' := funext fun i => by
        have := hl τ i
        rw [h1, h2] at this
        simpa using this
      subst this
      rfl

def vvCast (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n') (hl : SameWt h lam lam') :
    VV K lam ≃ₗ[K] VV K lam' := by
  subst h
  exact LinearEquiv.ofEq _ _ (by rw [sameWt_eq lam lam' hl])

end Cast

section CastLemmas

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] {n n' : ℕ}

theorem vvCast_self (lam : ι → DomWeight n) (hl : SameWt rfl lam lam) :
    vvCast (K := K) rfl lam lam hl = LinearEquiv.refl K (VV K lam) := by
  ext x
  rfl

theorem vvCast_rhoV (emb : ι → E →+* K) (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (hl : SameWt h lam lam') (g : GL (Fin n) E) (g' : GL (Fin n') E) (hg : MatEq g' g) (v : VV K lam) :
    vvCast h lam lam' hl (rhoV emb lam g v) = rhoV emb lam' g' (vvCast h lam lam' hl v) := by
  subst h
  have e := sameWt_eq lam lam' hl
  subst e
  have hg' : g' = g := Units.ext (Matrix.ext fun i j => hg.2 i j i j rfl rfl)
  subst hg'
  rw [vvCast_self]
  rfl

end CastLemmas

section CastLemmas2

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] {n n' : ℕ}

theorem castSp_self : castSp (E := E) (rfl : n = n) = LinearEquiv.refl E (Fin n → E) := by
  ext x i
  rfl

theorem vvCast_pairV [StarRing K] (emb : ι → E →+* K) (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (hl : SameWt h lam lam') (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin n') (Fin n') E)
    (hJ : ∀ i j, J' i j = J (Fin.cast h.symm i) (Fin.cast h.symm j)) (x y : VV K lam) :
    pairV emb lam' J' (vvCast h lam lam' hl x) (vvCast h lam lam' hl y) = pairV emb lam J x y := by
  subst h
  have e := sameWt_eq lam lam' hl
  subst e
  have hJ' : J' = J := Matrix.ext fun i j => hJ i j
  subst hJ'
  rw [vvCast_self]
  rfl

theorem vvCast_bVV_repr [StarRing K] (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (hl : SameWt h lam lam') (i : VVIdx lam) (j : VVIdx lam') :
    (bVV K lam').repr (vvCast h lam lam' hl (bVV K lam i)) j ∈ Formalism.DivisionValues.cmMax K := by
  subst h
  have e := sameWt_eq lam lam' hl
  subst e
  rw [vvCast_self, LinearEquiv.refl_apply, Module.Basis.repr_self]
  by_cases hij : i = j
  · subst hij
    rw [Finsupp.single_eq_same]
    exact (Formalism.DivisionValues.cmMax K).one_mem
  · rw [Finsupp.single_eq_of_ne (Ne.symm hij)]
    exact (Formalism.DivisionValues.cmMax K).zero_mem

theorem vvCast_nabAt [NumberField K] (emb : ι → E →+* K) (h : n = n') (lam : ι → DomWeight n)
    (lam' : ι → DomWeight n') (hl : SameWt h lam lam') (N : Submodule (𝓞 E) (Fin n → E)) :
    (nabAt emb lam N).map (((vvCast (K := K) h lam lam' hl).toLinearMap).restrictScalars (𝓞 K)) =
      nabAt emb lam' (N.map (((castSp (E := E) h).toLinearMap).restrictScalars (𝓞 E))) := by
  subst h
  have e := sameWt_eq lam lam' hl
  subst e
  rw [vvCast_self, castSp_self]
  simp only [LinearEquiv.refl_toLinearMap, LinearMap.restrictScalars_id, Submodule.map_id]

theorem vvCast_delAt [NumberField K] (emb : ι → E →+* K) (h : n = n') (lam : ι → DomWeight n)
    (lam' : ι → DomWeight n') (hl : SameWt h lam lam') (N : Submodule (𝓞 E) (Fin n → E)) :
    (delAt emb lam N).map (((vvCast (K := K) h lam lam' hl).toLinearMap).restrictScalars (𝓞 K)) =
      delAt emb lam' (N.map (((castSp (E := E) h).toLinearMap).restrictScalars (𝓞 E))) := by
  subst h
  have e := sameWt_eq lam lam' hl
  subst e
  rw [vvCast_self, castSp_self]
  simp only [LinearEquiv.refl_toLinearMap, LinearMap.restrictScalars_id, Submodule.map_id]

end CastLemmas2

section CastLemmas3

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] {n n' : ℕ}

theorem vvCast_bVV (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n') (hl : SameWt h lam lam') :
    ∃ f : VVIdx lam ≃ VVIdx lam', ∀ i, vvCast (K := K) h lam lam' hl (bVV K lam i) = bVV K lam' (f i) := by
  subst h
  have e := sameWt_eq lam lam' hl
  subst e
  exact ⟨Equiv.refl _, fun i => by rw [vvCast_self]; rfl⟩

theorem one_cast (h : n = n') (i j : Fin n') :
    (1 : Matrix (Fin n') (Fin n') E) i j = (1 : Matrix (Fin n) (Fin n) E) (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  simp only [Matrix.one_apply, Fin.cast_inj]

end CastLemmas3

section Gram

open GlobalTheory.Mem GlobalTheory.Mem.Col2

theorem gram_X'_eq_one (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (h : I.Ok) : X.toD7.sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := h.spaces
  change X.B.sp.X'.gram = 1
  rw [h2]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

end Gram

end GlobalTheory.Mem.R3.RowStd

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.RowStd

theorem sameWt_true (X : Stages) :
    SameWt (RowAd.rank_X' X).symm X.B.wts.sgTrue (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) :=
  RowWeight.lamRdef_eq_sgTrue X

def wtCast (X : Stages) :
    VV X.toD7.what₂.LL X.B.wts.sgTrue ≃ₗ[X.toD7.what₂.LL] VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) :=
  vvCast (RowAd.rank_X' X).symm _ _ (sameWt_true X)


set_option maxHeartbeats 4000000 in
theorem exists_coef : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∃ c : VV X.B.fields.K X.B.wts.sgTrue →ₛₗ[X.B.embLL] cX.W,
      (∀ v, c v = c0R (wtCast X v)) ∧
      (∀ (γ : GQ X.toD7.sp.X') (γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (g : GL (Fin (X.B.R.N X.B.R.m - 1)) X.B.fields.E),
        Bridge.IsRatMat X.toD7.sp.X' γ γE → MatEq γE g → ∀ v, c (rhoV X.B.fields.emb X.B.wts.sgTrue g v) = cX.coef.ρ γ (c v)) ∧
      LinearIndependent ℂ (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) ∧
      Submodule.span ℂ (Set.range fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) = ⊤ ∧
      (∀ x y, inner ℂ (c x) (c y) = X.B.embLL (pairV X.B.fields.emb X.B.wts.sgTrue 1 x y)) ∧
      ∀ t (P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ),
        (∀ x, P.coef x = c x) →
        (∀ c', RowAd.decoAd X I t (P.y c') = (Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).outSec.rep c') →
        Bridge.CoefTie X.toD7.sp.X' cX.coef P (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) c0R (pairV (labLL X.toD7) _ gramR)
          (nabAt (labLL X.toD7) _) (delAt (labLL X.toD7) _) := by
  intro X px I hX U Xg tr L hI cX gramR c0R hc hgr hM hin
  have hw := sameWt_true X
  let e0 : VV X.toD7.what₂.LL X.B.wts.sgTrue ≃ₗ[X.toD7.what₂.LL] VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) :=
    vvCast (RowAd.rank_X' X).symm _ _ hw
  let c : VV X.B.fields.K X.B.wts.sgTrue →ₛₗ[X.B.embLL] cX.W := (by with_unfolding_all exact (c0R.comp e0.toLinearMap :))
  have hgram := gram_X'_eq_one X I hI
  have hpair : ∀ x y, pairV (labLL X.toD7) (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) gramR (e0 x) (e0 y) =
      pairV X.B.fields.emb X.B.wts.sgTrue 1 x y := by
    intro x y
    rw [GlobalTheory.RowsSign.pairV_gramR_eq X px I hI cX gramR c0R hc hgr hM hin, hgram]
    exact vvCast_pairV (labLL X.toD7) _ _ _ hw 1 1 (one_cast (RowAd.rank_X' X).symm) x y
  have hInter : ∀ (γ : GQ X.toD7.sp.X') (γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (g : GL (Fin (X.B.R.N X.B.R.m - 1)) X.B.fields.E),
      Bridge.IsRatMat X.toD7.sp.X' γ γE → MatEq γE g → ∀ v, c (rhoV X.B.fields.emb X.B.wts.sgTrue g v) = cX.coef.ρ γ (c v) := by
    intro γ γE g hγ hm v
    have key := vvCast_rhoV (labLL X.toD7) _ _ _ hw g γE hm v
    exact (congrArg c0R key).trans (hM.1 γ γE hγ _)
  obtain ⟨f, hf⟩ := vvCast_bVV (K := X.toD7.what₂.LL) (RowAd.rank_X' X).symm _ _ hw
  have hcf : (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) =
      (fun j => c0R (bVV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) j)) ∘ f := by
    funext i
    exact congrArg c0R (hf i)
  have hli : LinearIndependent ℂ (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) := by
    rw [hcf]
    exact hM.2.1.comp f f.injective
  have hsp : Submodule.span ℂ (Set.range fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) = ⊤ := by
    have h2 := f.surjective.range_comp (fun j => c0R (bVV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) j))
    rw [hcf]
    refine Eq.trans ?_ hM.2.2
    exact congrArg (Submodule.span ℂ) h2
  have hinn : ∀ x y, inner ℂ (c x) (c y) = X.B.embLL (pairV X.B.fields.emb X.B.wts.sgTrue 1 x y) := by
    intro x y
    exact (hin _ _).trans (congrArg X.toD7.what₂.embLL (hpair x y))
  refine ⟨c, fun v => rfl, hInter, hli, hsp, hinn, fun t P hPc hPy => ⟨e0, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i j
    exact vvCast_bVV_repr _ _ _ hw i j
  · intro x
    exact hPc x
  · intro x x'
    exact hpair x x'
  · intro c'
    rw [RowLat.hLat_eq_decoAd_N X px I hX hI U t (P.y c'), hPy c']
    exact vvCast_nabAt (labLL X.toD7) _ _ _ hw _
  · intro c'
    rw [RowLat.hLat_eq_decoAd_N X px I hX hI U t (P.y c'), hPy c']
    exact vvCast_delAt (labLL X.toD7) _ _ _ hw _

end GlobalTheory.Mem.R3.RowStd
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.RowStd


set_option maxHeartbeats 4000000 in
theorem exists_std_wtCast : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    L.βX = 1 → ∃ c : VV X.B.fields.K X.B.wts.sgTrue →ₛₗ[X.B.embLL] cX.W,
      (∀ v, c v = c0R (wtCast X v)) ∧
      LinearIndependent ℂ (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) ∧
      Submodule.span ℂ (Set.range fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) = ⊤ ∧
      (∀ x y, inner ℂ (c x) (c y) = X.B.embLL (pairV X.B.fields.emb X.B.wts.sgTrue 1 x y)) ∧
      (∀ (γ : GQ X.toD7.sp.X') (γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (g : GL (Fin (X.B.R.N X.B.R.m - 1)) X.B.fields.E),
        Bridge.IsRatMat X.toD7.sp.X' γ γE → MatEq γE g → ∀ v, c (rhoV X.B.fields.emb X.B.wts.sgTrue g v) = cX.coef.ρ γ (c v)) ∧
      ∀ t, ∃ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ,
        (∀ (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) (h : Bridge.Gf X.toD7.sp.X'),
          P.ext (f : _ → _) h = c ((((Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1 (GlobalTheory.Mem.R3.RowAd.decoAd X I t h))) ∧
        Bridge.CoefTie X.toD7.sp.X' cX.coef P (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) c0R (pairV (labLL X.toD7) _ gramR)
          (nabAt (labLL X.toD7) _) (delAt (labLL X.toD7) _) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hc hgr hM hin hb
  obtain ⟨c, hc0, hInter, hli, hsp, hinn, hT⟩ := exists_coef X px I hX U Xg tr L hI cX gramR c0R hc hgr hM hin
  refine ⟨c, hc0, hli, hsp, hinn, hInter, fun t => ?_⟩
  obtain ⟨P, hPc, hPy, hPe⟩ := GlobalTheory.T.rowsClassSet_presentation_coefficientMap X px I hX U Xg tr L eG hI hV hL hG hb cX c hInter hli hsp hinn t
  exact ⟨P, hPe, hT t P hPc hPy⟩


end GlobalTheory.Mem.R3.RowStd
