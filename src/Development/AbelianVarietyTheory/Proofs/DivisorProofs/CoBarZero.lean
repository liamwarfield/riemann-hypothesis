module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesOverSplitPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PstAndWdAtOfIsRegAlg
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.VacShape

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {D : D7} {a a' : ℕ}

def coBar (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (u : Matrix (Fin a') (Fin (a + a')) (AE D.host.F D.host.E)) : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) :=
  -((1 : GL (Fin a') (Fv D.host.F Bs.v₁)).1ᵀ * Γ.V'.J.map Bs.τ₁ * u.map (piW (Bs.τ₁.comp D.sp.cm.sig)) *
    (Γ.W.J.map Bs.τ₁)ᵀ * (1 : GL (Fin (a + a')) (Fv D.host.F Bs.v₁)).1)

theorem coBar_add (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (u u' : Matrix (Fin a') (Fin (a + a')) (AE D.host.F D.host.E)) :
    coBar Bs Γ (u + u') = coBar Bs Γ u + coBar Bs Γ u' := by
  unfold coBar
  rw [Matrix.map_add _ (map_add _)]
  simp only [Matrix.mul_add, Matrix.add_mul, neg_add]

theorem coBar_zero (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a') : coBar Bs Γ 0 = 0 := by
  unfold coBar
  rw [Matrix.map_zero _ (map_zero _)]
  simp

def Sa (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E))
    (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)) :
    AddSubgroup (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)) where
  carrier := {Y | ∃ u ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁, u.map (piW Bs.τ₁) = 0 ∧ coBar Bs Γ u = Y}
  zero_mem' := ⟨0, zero_mem _, Matrix.map_zero _ (map_zero _), coBar_zero Bs Γ⟩
  add_mem' := by
    rintro _ _ ⟨u, hu, hu0, rfl⟩ ⟨u', hu', hu0', rfl⟩
    exact ⟨u + u', add_mem hu hu', by rw [Matrix.map_add _ (map_add _), hu0, hu0', add_zero], coBar_add Bs Γ u u'⟩
  neg_mem' := by
    rintro _ ⟨u, hu, hu0, rfl⟩
    refine ⟨-u, neg_mem hu, by rw [Matrix.map_neg _ (map_neg _), hu0, neg_zero], ?_⟩
    have := coBar_add Bs Γ u (-u)
    rw [add_neg_cancel, coBar_zero] at this
    show coBar Bs Γ (-u) = -coBar Bs Γ u
    exact (neg_eq_of_add_eq_zero_right this.symm).symm

def Bd (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E))
    (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)) : Set (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)) :=
  {Y | ∀ x : Matrix (Fin a') (Fin (a + a')) (AE D.host.F D.host.E), At (evFin D.host.F Bs.v₁) x →
    x.map (piW Bs.τ₁) = 0 → coBar Bs Γ x = Y → ∀ u ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      u.map (piW (Bs.τ₁.comp D.sp.cm.sig)) = 0 →
      Bs.ψ (symp (cA D.sp.cm.sig) (-1) (incM D.host.F Γ.V'.J) (incM D.host.F Γ.W.J) x u) = 1}

end GlobalTheory.VacShape

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacFlip

open GlobalTheory.DblVac

open Matrix

section Idem

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {ι κ : Type} [Fintype ι] [DecidableEq ι]

theorem idem_sandwich {e : R} (he : e * e = e) (N X : Matrix ι ι A) :
    ((1 - e) • (1 : Matrix ι ι A) + e • N) * X * ((1 - e) • (1 : Matrix ι ι A) + e • N) =
      (1 - e) • X + e • (N * X * N) := by
  have h11 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
  have h10 : (1 - e) * e = 0 := by linear_combination -he
  have h01 : e * (1 - e) = 0 := by linear_combination -he
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
    h11, h10, h01, he, zero_smul, add_zero, zero_add]

end Idem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mul_idem_eq_zero (v : Pl (F := F)) {x : AF F} (hx : evFin F v x = 0) : x * GlobalTheory.LatVac.liftV v 1 = 0 :=
  GlobalTheory.LatVac.at_liftV v 1 x hx

theorem idem_mul_self (v : Pl (F := F)) : GlobalTheory.LatVac.liftV v 1 * GlobalTheory.LatVac.liftV v 1 = (GlobalTheory.LatVac.liftV v 1 : AF F) := by
  have h := mul_idem_eq_zero v (x := GlobalTheory.LatVac.liftV v 1 - 1)
    (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
  rwa [sub_mul, one_mul, sub_eq_zero] at h

def flipM (d : ℕ) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := fromBlocks 1 0 0 (-1)

theorem flipM_mul_self (d : ℕ) : flipM (F := F) (E := E) d * flipM d = 1 := by
  simp [flipM, fromBlocks_multiply, ← fromBlocks_one]

theorem flipM_transpose (d : ℕ) : (flipM (F := F) (E := E) d)ᵀ = flipM d := by
  simp [flipM, fromBlocks_transpose]

theorem flipM_dbl {d : ℕ} (J : Matrix (Fin d) (Fin d) (AE F E)) : flipM d * dbl J * flipM d = dbl J := by
  simp [flipM, dbl, fromBlocks_multiply]

theorem flipM_diagCols (d : ℕ) : flipM (F := F) (E := E) d * diagCols (Fin d) = antiCols d := by
  change @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
    (flipM (F := F) (E := E) d) (diagCols (Fin d)) = antiCols d
  simp [flipM, diagCols, antiCols, Matrix.fromBlocks_mul_fromRows]

theorem flipM_antiCols (d : ℕ) : flipM (F := F) (E := E) d * antiCols d = diagCols (Fin d) := by
  change @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
    (flipM (F := F) (E := E) d) (antiCols d) = diagCols (Fin d)
  simp [flipM, antiCols, diagCols, Matrix.fromBlocks_mul_fromRows]

theorem flipM_map (σ : E →ₐ[F] E) (d : ℕ) : (flipM (F := F) (E := E) d).map (cA σ) = flipM d := by
  ext (i | i) (j | j) <;> simp [flipM, Matrix.one_apply] <;> split_ifs <;> simp

section Idem2

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem idem_conj_cols {e : R} (he : e * e = e) (N Q : Matrix ι ι A) (D Ac : Matrix ι κ A) (T : Matrix κ κ A)
    (hND : N * D = Ac) (hNA : N * Ac = D) (hQ : (1 - e) • Q = (1 - e) • (1 : Matrix ι ι A))
    (hQA : Q * Ac = Ac * T) :
    (((1 - e) • (1 : Matrix ι ι A) + e • N) * Q * ((1 - e) • (1 : Matrix ι ι A) + e • N)) * D =
      D * ((1 - e) • (1 : Matrix κ κ A) + e • T) := by
  have hQD : (1 - e) • (Q * D) = (1 - e) • D := by
    rw [← Matrix.smul_mul, hQ, Matrix.smul_mul, Matrix.one_mul]
  rw [idem_sandwich he, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hQD,
    Matrix.mul_assoc, Matrix.mul_assoc, hND, hQA, ← Matrix.mul_assoc, hNA, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.mul_one]

theorem idem_unit {e : R} (he : e * e = e) (T Ti : Matrix κ κ A) (h : T * Ti = 1) :
    ((1 - e) • (1 : Matrix κ κ A) + e • T) * ((1 - e) • (1 : Matrix κ κ A) + e • Ti) = 1 := by
  have h11 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
  have h10 : (1 - e) * e = 0 := by linear_combination -he
  have h01 : e * (1 - e) = 0 := by linear_combination -he
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
    h11, h10, h01, he, zero_smul, add_zero, zero_add, h]
  rw [← add_smul, sub_add_cancel, one_smul]

end Idem2

def flipAt (v : Pl (F := F)) (d : ℕ) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
  (1 - GlobalTheory.LatVac.liftV v 1 : AF F) • (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) +
    (GlobalTheory.LatVac.liftV v 1 : AF F) • flipM d

theorem flipAt_mul_self (v : Pl (F := F)) (d : ℕ) : flipAt (E := E) v d * flipAt v d = 1 := by
  have h := idem_sandwich (idem_mul_self v) (flipM (F := F) (E := E) d) 1
  rw [Matrix.mul_one, Matrix.mul_one, flipM_mul_self, ← add_smul, sub_add_cancel, one_smul] at h
  exact h

theorem flipAt_transpose (v : Pl (F := F)) (d : ℕ) : (flipAt (E := E) v d)ᵀ = flipAt v d := by
  simp only [flipAt, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, flipM_transpose]

theorem flipAt_map (σ : E →ₐ[F] E) (v : Pl (F := F)) (d : ℕ) : (flipAt (E := E) v d).map (cA σ) = flipAt v d := by
  ext i j
  have h1 : (cA σ) ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) i j) = (1 : Matrix _ _ (AE F E)) i j :=
    congrFun (congrFun (Matrix.map_one (cA σ) (map_zero _) (map_one _)) i) j
  have h2 : (cA σ) (flipM (F := F) (E := E) d i j) = flipM d i j := congrFun (congrFun (flipM_map σ d) i) j
  simp only [flipAt, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add (f := _), map_smul, h1, h2]

theorem flipAt_unitary (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) :
    (flipAt (E := E) v d)ᵀ * dbl (incM F W.J) * (flipAt v d).map (cA σ) = dbl (incM F W.J) := by
  rw [flipAt_transpose, flipAt_map, flipAt, idem_sandwich (idem_mul_self v), flipM_dbl, ← add_smul, sub_add_cancel,
    one_smul]

def flipPt (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : UD σ W :=
  ⟨⟨flipAt v d, flipAt v d, flipAt_mul_self v d, flipAt_mul_self v d⟩, flipAt_unitary σ W v⟩

theorem matD_flipPt (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : matD (flipPt σ W v) = flipAt v d := rfl

theorem matD_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g h : UD σ W) : matD (g * h) = matD g * matD h := rfl

theorem matD_inv_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : matD g⁻¹ * matD g = 1 := by
  exact congrArg Units.val (inv_mul_cancel (g : GL (Fin d ⊕ Fin d) (AE F E)))

theorem mul_mem_KD {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {g h : UD σ W} (hg : g ∈ KD σ W v)
    (hh : h ∈ KD σ W v) : g * h ∈ KD σ W v := by
  refine ⟨fun x hx => ?_, fun z hz => ?_⟩
  · have e1 : matD (g * h) - 1 = (matD g - 1) * matD h + (matD h - 1) := by
      rw [matD_mul, Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e1, smul_add, ← Matrix.smul_mul, hg.1 x hx, hh.1 x hx, Matrix.zero_mul, add_zero]
  · have e2 : matD (g * h)⁻¹ = matD h⁻¹ * matD g⁻¹ := by rw [_root_.mul_inv_rev, matD_mul]
    rw [matD_mul, ← Matrix.mulVec_mulVec, e2, ← Matrix.mulVec_mulVec]
    exact ⟨(hg.2 _ (hh.2 z hz).1).1, (hh.2 _ (hg.2 z hz).2).2⟩

theorem inv_mem_KD {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {g : UD σ W} (hg : g ∈ KD σ W v) :
    g⁻¹ ∈ KD σ W v := by
  refine ⟨fun x hx => ?_, fun z hz => ?_⟩
  · have e1 : matD g⁻¹ - 1 = -(matD g⁻¹ * (matD g - 1)) := by
      rw [Matrix.mul_sub, matD_inv_mul, Matrix.mul_one, neg_sub]
    rw [e1, smul_neg, ← Matrix.mul_smul, hg.1 x hx, Matrix.mul_zero, neg_zero]
  · rw [inv_inv]
    exact ⟨(hg.2 z hz).2, (hg.2 z hz).1⟩

theorem idem_smul_mem_latAt {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) {y : Fin d → AE F E}
    (hy : y ∈ GlobalTheory.InertSph.latAt W v) : (GlobalTheory.LatVac.liftV v 1 : AF F) • y ∈ GlobalTheory.InertSph.latAt W v := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v 1 * a, ?_, ?_, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul, GlobalTheory.LatVac.evFin_liftV, one_mul]
      exact hv
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem flipAt_mulVec_inl (v : Pl (F := F)) {d : ℕ} (z : Fin d ⊕ Fin d → AE F E) (i : Fin d) :
    (flipAt v d *ᵥ z) (Sum.inl i) = z (Sum.inl i) := by
  simp [flipAt, flipM, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, smul_mul_assoc, neg_mul, Finset.sum_neg_distrib]
  rw [← add_smul, sub_add_cancel, one_smul]

theorem flipAt_mulVec_inr (v : Pl (F := F)) {d : ℕ} (z : Fin d ⊕ Fin d → AE F E) (i : Fin d) :
    (flipAt v d *ᵥ z) (Sum.inr i) =
      z (Sum.inr i) - (GlobalTheory.LatVac.liftV v 1 : AF F) • z (Sum.inr i) - (GlobalTheory.LatVac.liftV v 1 : AF F) • z (Sum.inr i) := by
  simp [flipAt, flipM, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, smul_mul_assoc, neg_mul, Finset.sum_neg_distrib]
  rw [sub_smul, one_smul]; abel

theorem flipAt_mulVec_mem_latD (v : Pl (F := F)) {d : ℕ} (W : Spc F E d) {z : Fin d ⊕ Fin d → AE F E} (hz : z ∈ latD W v) :
    flipAt v d *ᵥ z ∈ latD W v := by
  have hl : (flipAt v d *ᵥ z) ∘ Sum.inl = z ∘ Sum.inl := funext (flipAt_mulVec_inl v z)
  have hr : (flipAt v d *ᵥ z) ∘ Sum.inr = z ∘ Sum.inr - (GlobalTheory.LatVac.liftV v 1 : AF F) • (z ∘ Sum.inr) -
      (GlobalTheory.LatVac.liftV v 1 : AF F) • (z ∘ Sum.inr) := funext fun i => by
    simp only [Function.comp_apply, Pi.sub_apply, Pi.smul_apply, flipAt_mulVec_inr]
  have h2 := idem_smul_mem_latAt W v hz.2
  refine ⟨?_, ?_⟩
  · rw [hl]; exact hz.1
  · rw [hr]; exact sub_mem (sub_mem hz.2 h2) h2

theorem flipPt_mem_KD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : flipPt σ W v ∈ KD σ W v := by
  refine ⟨fun x hx => ?_, fun z hz => ⟨flipAt_mulVec_mem_latD v W hz, flipAt_mulVec_mem_latD v W hz⟩⟩
  have e1 : matD (flipPt σ W v) - 1 = (GlobalTheory.LatVac.liftV v 1 : AF F) • (flipM d - 1) := by
    rw [matD_flipPt, flipAt, smul_sub, sub_smul, one_smul]; abel
  rw [e1, smul_smul, mul_idem_eq_zero v hx, zero_smul]

theorem flipPt_conj_anti_diag : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d)
    (v : Pl (F := F)), ∃ w₀ ∈ GlobalTheory.DblVac.KD σ W v, ∀ q ∈ GlobalTheory.DblVac.KD σ W v, q ∈ GlobalTheory.DblVac.PAnti σ W →
      w₀ * q * w₀⁻¹ ∈ GlobalTheory.DblVac.KD σ W v ∧ w₀ * q * w₀⁻¹ ∈ GlobalTheory.DblVac.PDiag σ W := by
  intro F E _ _ _ _ _ σ d W v
  have hw := flipPt_mem_KD σ W v
  refine ⟨flipPt σ W v, hw, fun q hq hqa => ⟨mul_mem_KD (mul_mem_KD hw hq) (inv_mem_KD hw), ?_⟩⟩
  obtain ⟨T, hT⟩ := hqa
  have he := idem_mul_self (F := F) v
  have hQ : (1 - GlobalTheory.LatVac.liftV v 1 : AF F) • matD q =
      (1 - GlobalTheory.LatVac.liftV v 1 : AF F) • (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) := by
    have h0 := hq.1 (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rwa [smul_sub, sub_eq_zero] at h0
  refine ⟨⟨(1 - GlobalTheory.LatVac.liftV v 1 : AF F) • (1 : Matrix (Fin d) (Fin d) (AE F E)) +
      (GlobalTheory.LatVac.liftV v 1 : AF F) • (T : Matrix (Fin d) (Fin d) (AE F E)),
    (1 - GlobalTheory.LatVac.liftV v 1 : AF F) • (1 : Matrix (Fin d) (Fin d) (AE F E)) +
      (GlobalTheory.LatVac.liftV v 1 : AF F) • ((T⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)),
    idem_unit he _ _ (Units.mul_inv T), idem_unit he _ _ (Units.inv_mul T)⟩, ?_⟩
  show (flipAt v d * matD q * flipAt v d) * diagCols (Fin d) = diagCols (Fin d) *
    ((1 - GlobalTheory.LatVac.liftV v 1 : AF F) • (1 : Matrix (Fin d) (Fin d) (AE F E)) +
      (GlobalTheory.LatVac.liftV v 1 : AF F) • (T : Matrix (Fin d) (Fin d) (AE F E)))
  exact idem_conj_cols he (flipM d) (matD q) _ _ _ (flipM_diagCols d) (flipM_antiCols d) hQ hT

end GlobalTheory.DblVacFlip
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMemStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diagOneNegOne_conj_antidiagonalStabilizer_mem : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d)
    (v : Pl (F := F)), ∃ w₀ ∈ GlobalTheory.DblVac.KD σ W v, ∀ q ∈ GlobalTheory.DblVac.KD σ W v, q ∈ GlobalTheory.DblVac.PAnti σ W →
      w₀ * q * w₀⁻¹ ∈ GlobalTheory.DblVac.KD σ W v ∧ w₀ * q * w₀⁻¹ ∈ GlobalTheory.DblVac.PDiag σ W := by
  first | exact @GlobalTheory.DblVacFlip.flipPt_conj_anti_diag | exact GlobalTheory.DblVacFlip.flipPt_conj_anti_diag | (intros; apply GlobalTheory.DblVacFlip.flipPt_conj_anti_diag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.CMImag

theorem exists_imag_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∃ c : E, c ≠ 0 ∧ σ c = -c := by
  intro F E _ _ _ _ _ σ h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hconj : ∀ x, τ (σ x) = star (τ x) := h.2.2.2 τ
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    apply τ.injective
    rw [hconj, hconj, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    have hTC := h.2.1
    apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hconj x
    rw [hall x] at this
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this.symm
  obtain ⟨x, hx⟩ := hne
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hinv, neg_sub]

end GlobalTheory.CMImag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
noncomputable section

namespace GlobalTheory.RatWeilOp

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def act {R κ : Type} [CommRing R] [Fintype κ] (a : Matrix (κ ⊕ κ) (κ ⊕ κ) R) (w : (κ → R) × (κ → R)) : (κ → R) × (κ → R) :=
  ((a *ᵥ Sum.elim w.1 w.2) ∘ Sum.inl, (a *ᵥ Sum.elim w.1 w.2) ∘ Sum.inr)

theorem act_mul {R κ : Type} [CommRing R] [Fintype κ] (a b : Matrix (κ ⊕ κ) (κ ⊕ κ) R) (w : (κ → R) × (κ → R)) :
    act (a * b) w = act a (act b w) := by
  simp only [act, Matrix.mulVec_mulVec, Sum.elim_comp_inl_inr]

theorem act_fromBlocks {R κ : Type} [CommRing R] [Fintype κ] (A B C D : Matrix κ κ R) (w : (κ → R) × (κ → R)) :
    act (Matrix.fromBlocks A B C D) w = (A *ᵥ w.1 + B *ᵥ w.2, C *ᵥ w.1 + D *ᵥ w.2) := by
  simp only [act, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]

variable {F : Type} [Field F] [NumberField F]

def ind (κ : Type) (v : Pl F) : (κ → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

def IsFam {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : Prop :=
  (∀ v, φ v ∈ SB (κ → Fv F v)) ∧ ∀ᶠ v in cofinite, φ v = ind κ v

def IsOp {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (a : Matrix (κ ⊕ κ) (κ ⊕ κ) F)
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) (c : ℂ) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ) : Prop :=
  c ≠ 0 ∧ Function.Surjective ei ∧
  (∀ v, Set.BijOn (ev v) (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _)) ∧
  (∀ v (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v), ev v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) =
    schr (GlobalTheory.LatVac.psiAt ψ v) (act (a.map (algebraMap F (Fv F v))) w) (ev v φ)) ∧
  (∀ᶠ v in cofinite, ev v (ind κ v) = ind κ v) ∧
  ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), IsFam φ →
    e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) (fun v => ev v (φ v)) ∧
    (∀ w : (κ → AF F) × (κ → AF F), e (schr ψ w (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) =
      schr ψ (act (a.map (algebraMap F (AF F))) w) (e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ))) ∧
    thetaSum F (e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) = c * thetaSum F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)

def HasOp {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (a : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop :=
  ∃ e c ei ev, IsOp ψ a e c ei ev

theorem IsOp.isFam {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} {a : Matrix (κ ⊕ κ) (κ ⊕ κ) F} {e c ei ev}
    (h : IsOp ψ a e c ei ev) {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) : IsFam fun v => ev v (φ v) := by
  obtain ⟨-, -, hbij, -, hind, -⟩ := h
  refine ⟨fun v => (hbij v).mapsTo (hφ.1 v), ?_⟩
  filter_upwards [hφ.2, hind] with v h1 h2
  rw [h1, h2]

theorem HasOp.mul {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} {a b : Matrix (κ ⊕ κ) (κ ⊕ κ) F}
    (ha : HasOp ψ a) (hb : HasOp ψ b) : HasOp ψ (a * b) := by
  obtain ⟨e₁, c₁, ei₁, ev₁, h₁⟩ := ha
  obtain ⟨e₂, c₂, ei₂, ev₂, h₂⟩ := hb
  have h₂' := h₂
  obtain ⟨hc₁, hs₁, hb₁, hw₁, hi₁, hp₁⟩ := h₁
  obtain ⟨hc₂, hs₂, hb₂, hw₂, hi₂, hp₂⟩ := h₂
  refine ⟨e₁ ∘ₗ e₂, c₁ * c₂, ei₁.comp ei₂, fun v => ev₁ v ∘ₗ ev₂ v, mul_ne_zero hc₁ hc₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact hs₁.comp hs₂
  · intro v
    exact (hb₁ v).comp (hb₂ v)
  · intro v w φ hφ
    simp only [LinearMap.comp_apply]
    rw [hw₂ v w φ hφ, hw₁ v _ _ ((hb₂ v).mapsTo hφ), Matrix.map_mul, act_mul]
  · filter_upwards [hi₁, hi₂] with v h1 h2
    simp only [LinearMap.comp_apply, h2, h1]
  · intro f φ hφ
    have hφ' : IsFam fun v => ev₂ v (φ v) := IsOp.isFam h₂' hφ
    obtain ⟨hq₂, hw₂', ht₂⟩ := hp₂ f φ hφ
    obtain ⟨hq₁, hw₁', ht₁⟩ := hp₁ (ei₂ f) (fun v => ev₂ v (φ v)) hφ'
    refine ⟨?_, ?_, ?_⟩
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply, hq₂, hq₁]
    · intro w
      simp only [LinearMap.comp_apply]
      rw [hw₂' w, hq₂, hw₁' _, Matrix.map_mul, act_mul]
    · simp only [LinearMap.comp_apply]
      rw [hq₂, ht₁, ← hq₂, ht₂, mul_assoc]

end GlobalTheory.RatWeilOp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGenerato
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGenerato
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

namespace GlobalTheory.LatParam

theorem vecMulVec_sum_zsmul {E : Type} [Field E] {n d kx ky : ℕ} (ex : Fin kx → Fin n → E) (fy : Fin ky → Fin d → E)
    (c : Fin kx → ℤ) (c' : Fin ky → ℤ) :
    Matrix.vecMulVec (∑ i, c i • ex i) (∑ j, c' j • fy j) =
      ∑ m : Fin kx × Fin ky, (c m.1 * c' m.2) • Matrix.vecMulVec (ex m.1) (fy m.2) := by
  ext a b
  simp only [Matrix.vecMulVec_apply, Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply,
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [zsmul_eq_mul, Int.cast_mul]; ring

theorem latAtV_param : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d), X.L.IsLattice E → Y.L.IsLattice E → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
    ∃ (M : Type) (_ : Fintype M) (g : M → Matrix (Fin n) (Fin d) E), ∀ γ,
      γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v ↔ ∃ a : M → v.adicCompletionIntegers F,
        γ = ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m) := by
  intro F E _ _ _ _ _ n d X Y hX hY v
  obtain ⟨kx, ex, hex⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hX.fg.restrictScalars (R := ℤ))
  obtain ⟨ky, fy, hfy⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hY.fg.restrictScalars (R := ℤ))
  let I : Matrix (Fin n) (Fin d) E →+ Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
    (inclR (F := F) (E := E) (AF F)).toAddMonoidHom.mapMatrix
  have hI : ∀ J, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J = I J := fun J => rfl
  refine ⟨Fin kx × Fin ky, inferInstance, fun m => Matrix.vecMulVec (ex m.1) (fy m.2), fun γ => ⟨fun h => ?_, ?_⟩⟩
  · induction h using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hint, x, hx, y, hy, rfl⟩ := hz
      have hx' : x ∈ Submodule.span ℤ (Set.range ex) := by rw [hex]; exact hx
      have hy' : y ∈ Submodule.span ℤ (Set.range fy) := by rw [hfy]; exact hy
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx'
      obtain ⟨c', rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'
      refine ⟨fun m => ⟨(c m.1 * c' m.2) • GlobalTheory.AdelicU.evFin F v a, zsmul_mem hint _⟩, ?_⟩
      have ha' := GlobalTheory.VacAny.eq_atPlace_of_at v a ha
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hI, vecMulVec_sum_zsmul, map_sum, map_zsmul, Finset.smul_sum, map_zsmul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← ha', smul_comm, smul_assoc]
    | zero => exact ⟨fun _ => 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by simp only [Pi.add_apply, AddMemClass.coe_add, map_add (f := _), add_smul, Finset.sum_add_distrib]⟩
    | neg x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨-a, by simp only [Pi.neg_apply, NegMemClass.coe_neg, map_neg, neg_smul, Finset.sum_neg_distrib]⟩
  · rintro ⟨a, rfl⟩
    refine AddSubgroup.sum_mem _ fun m _ => AddSubgroup.subset_closure ?_
    refine ⟨_, ?_, ?_, ex m.1, ?_, fy m.2, ?_, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
    · rw [GlobalTheory.EmbChart.evFin_atPlace]; exact (a m).2
    · have : ex m.1 ∈ Submodule.span ℤ (Set.range ex) := Submodule.subset_span ⟨m.1, rfl⟩
      rw [hex] at this; exact this
    · have : fy m.2 ∈ Submodule.span ℤ (Set.range fy) := Submodule.subset_span ⟨m.2, rfl⟩
      rw [hfy] at this; exact this

end GlobalTheory.LatParam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGeneratoStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorLatticeAtFinitePlace_eq_integral_span_generators : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d), X.L.IsLattice E → Y.L.IsLattice E → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
    ∃ (M : Type) (_ : Fintype M) (g : M → Matrix (Fin n) (Fin d) E), ∀ γ,
      γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v ↔ ∃ a : M → v.adicCompletionIntegers F,
        γ = ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m) := by
  first | exact @GlobalTheory.LatParam.latAtV_param | exact GlobalTheory.LatParam.latAtV_param | (intros; apply GlobalTheory.LatParam.latAtV_param <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceVecPairAsAdeles
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {JA : Matrix α α E} {JB : Matrix β β E}

def actLin (p : GlobalTheory.WeilM.UG c JA × GlobalTheory.WeilM.UG c JB) : Matrix α β E ≃ₗ[R] Matrix α β E where
  toFun x := GlobalTheory.WeilM.actAB c p x
  invFun x := (((p.1⁻¹ : GlobalTheory.WeilM.UG c JA) : GL α E) : Matrix α α E) * x *
    (((p.2⁻¹ : GlobalTheory.WeilM.UG c JB) : GL β E) : Matrix β β E)ᵀ
  map_add' x y := by simp [GlobalTheory.WeilM.actAB, Matrix.mul_add, Matrix.add_mul]
  map_smul' r x := by simp [GlobalTheory.WeilM.actAB, Matrix.mul_smul, Matrix.smul_mul]
  left_inv x := by
    simp only [GlobalTheory.WeilM.actAB, Subgroup.coe_inv, ← Matrix.mul_assoc]
    rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      Matrix.mul_one]
  right_inv x := by
    simp only [GlobalTheory.WeilM.actAB, Subgroup.coe_inv, ← Matrix.mul_assoc]
    rw [Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
      Matrix.mul_one]

end Gen

variable (F : Type) [Field F] [NumberField F]

def finE {κ : Type} (y : κ → FiniteAdeleRing (𝓞 F) F) : κ → AdeleRing (𝓞 F) F := fun i => (0, y i)

def finE2 {κ : Type} (m : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) := (finE F m.1, finE F m.2)

def infE {κ : Type} (z : κ → mixedEmbedding.mixedSpace F) : κ → AdeleRing (𝓞 F) F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i), 0)

def mixedSpaceVecPairAsAdeles {κ : Type} (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) := (infE F v.1, infE F v.2)

def slice {κ : Type} (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    (κ → mixedEmbedding.mixedSpace F) → ℂ :=
  fun z => Φ fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i), y i)

def schrInf (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {κ : Type} [Fintype κ]
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) : (κ → mixedEmbedding.mixedSpace F) → ℂ :=
  fun z => ψ (infE F z ⬝ᵥ infE F v.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (infE F v.1 ⬝ᵥ infE F v.2)) * f (z + v.1)

variable {F}

theorem dot_infE {κ : Type} [Fintype κ] (x : κ → AdeleRing (𝓞 F) F) (z : κ → mixedEmbedding.mixedSpace F) :
    x ⬝ᵥ infE F z = infE F (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) ⬝ᵥ infE F z := by
  simp only [dotProduct, infE]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Prod.ext ?_ ?_
  · show (x i).1 * _ = _ * _
    rw [RingEquiv.symm_apply_apply]
  · show (x i).2 * 0 = (0 : FiniteAdeleRing (𝓞 F) F) * 0
    rw [mul_zero, mul_zero]

theorem pureA_schrInf (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {κ : Type} [Fintype κ]
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.pureA F (schrInf F ψ v f) g = GlobalTheory.WeilM.schr ψ (mixedSpaceVecPairAsAdeles F v) (GlobalTheory.WeilM.pureA F f g) := by
  funext x
  simp only [GlobalTheory.WeilM.pureA, schrInf, GlobalTheory.WeilM.schr, mixedSpaceVecPairAsAdeles]
  rw [dot_infE x v.2, mul_assoc]
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) + v.1 =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + infE F v.1) i).1 := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 + v.1 i =
      InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v.1 i))
    rw [map_add (f := _), RingEquiv.apply_symm_apply]
  have h2 : (fun i => (x i).2) = fun i => ((x + infE F v.1) i).2 := by
    funext i
    show (x i).2 = (x i).2 + 0
    rw [add_zero]
  rw [h1, h2]

theorem slice_schr (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {κ : Type} [Fintype κ]
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    slice F (GlobalTheory.WeilM.schr ψ (mixedSpaceVecPairAsAdeles F v) Φ) y = schrInf F ψ v (slice F Φ y) := by
  funext z
  simp only [slice, schrInf, GlobalTheory.WeilM.schr, mixedSpaceVecPairAsAdeles]
  congr 2
  · congr 1
    refine (dot_infE _ v.2).trans ?_
    congr 2
    funext i
    exact RingEquiv.apply_symm_apply _ _
  · funext i
    refine Prod.ext ?_ ?_
    · exact (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ _).symm
    · exact add_zero _

theorem pureA_add {κ : Type} (f f' : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.pureA F (f + f') g = GlobalTheory.WeilM.pureA F f g + GlobalTheory.WeilM.pureA F f' g := by
  funext x
  simp only [GlobalTheory.WeilM.pureA, Pi.add_apply, add_mul]

theorem pureA_smul {κ : Type} (a : ℂ) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.pureA F (a • f) g = a • GlobalTheory.WeilM.pureA F f g := by
  funext x
  simp only [GlobalTheory.WeilM.pureA, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem exists_schwartz_slice {κ : Type} [Fintype κ] (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    ∃ s : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ z, s z = slice F Φ y z := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, -, rfl⟩ := hx
    refine ⟨g y • f, fun z => ?_⟩
    simp only [SchwartzMap.smul_apply, smul_eq_mul, slice, GlobalTheory.WeilM.pureA, RingEquiv.apply_symm_apply]
    exact mul_comm _ _
  | zero => exact ⟨0, fun z => rfl⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hx'
    exact ⟨s + s', fun z => by rw [SchwartzMap.add_apply, hs, hs']; rfl⟩
  | smul a x _ hx =>
    obtain ⟨s, hs⟩ := hx
    exact ⟨a • s, fun z => by rw [SchwartzMap.smul_apply, hs]; rfl⟩

end GlobalTheory.WeilAdm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.InertLagChar

variable {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} {κ : Type} [Fintype κ]

def diagW (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) (Φ : (κ ⊕ κ → Fv F v) → ℂ)
    (w : (κ → Fv F v) × (κ → Fv F v)) : ℂ :=
  ∫ x, schr ψ (Sum.elim w.1 0, Sum.elim w.2 0) Φ (Sum.elim x x) ∂μ

def lagInt (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) {N : ℕ} (ν : @Measure (Fin N → Fv F v) (borel _))
    (j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v)) (Φ : (κ ⊕ κ → Fv F v) → ℂ) : ℂ :=
  ∫ y, diagW ψ μ Φ (j y) ∂ν


open NumberField IsDedekindDomain MeasureTheory in
open scoped TensorProduct Matrix in
variable {F : Type} [Field F] [NumberField F] {v : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {κ : Type} [Fintype κ] in
theorem _root_.GlobalTheory.InertLagChar.diagW_zero (ψ : AddChar (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ℂ)
    (μ : @Measure (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (borel _)) (Φ : (κ ⊕ κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) :
    _root_.GlobalTheory.InertLagChar.diagW ψ μ Φ 0 = ∫ x, Φ (Sum.elim x x) ∂μ := by
  unfold _root_.GlobalTheory.InertLagChar.diagW _root_.GlobalTheory.WeilM.schr
  simp

end GlobalTheory.InertLagChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharUnramifiedOfSplitsCompletelyAbovePla
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharUnramifiedOfSplitsCompletelyAbovePla
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SplitFullyUnr

open IsDedekindDomain NumberField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ramificationIdx_eq_one_of_splitsFully (v : HeightOneSpectrum (𝓞 F))
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully E v) (q : Ideal (𝓞 E)) (hq : q ∈ (v.asIdeal.under ℤ).primesOver (𝓞 E)) :
    q.ramificationIdx ℤ = 1 := by
  classical
  set P : Ideal ℤ := v.asIdeal.under ℤ with hP
  have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hfin : (P.primesOver (𝓞 E)).Finite := Set.finite_of_ncard_pos (by rw [h]; exact hn)
  letI : Fintype (P.primesOver (𝓞 E)) := hfin.fintype
  have hcard : Fintype.card (P.primesOver (𝓞 E)) = Module.finrank ℚ E := by
    rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]; exact h
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E)
  rw [RingOfIntegers.rank] at hsum
  have hpos : ∀ r ∈ (Finset.univ : Finset (P.primesOver (𝓞 E))),
      (fun _ => 1) r ≤ r.1.ramificationIdx ℤ * r.1.inertiaDeg ℤ := fun r _ =>
    Nat.mul_pos (Ideal.ramificationIdx_pos (R := ℤ) r.1) (Ideal.inertiaDeg_pos r.1 ℤ)
  have hall := (Finset.sum_eq_sum_iff_of_le hpos).1 (by rw [← Fintype.card_eq_sum_ones, hcard, hsum])
  have hm := (hall ⟨q, hq⟩ (Finset.mem_univ _)).symm
  exact Nat.eq_one_of_mul_eq_one_right hm

theorem under_eq_span_of_mem (w : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime)
    (hw : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) : w.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
  have : NeZero w.asIdeal := ⟨w.ne_bot⟩
  have hq := Nat.absNorm_under_prime w.asIdeal
  have hd : (Ideal.absNorm (w.asIdeal.under ℤ) : ℤ) ∣ (p : ℤ) := by
    rw [← Int.cast_mem_ideal_iff]; simpa using hw
  have he : Ideal.absNorm (w.asIdeal.under ℤ) = p :=
    (Nat.prime_dvd_prime_iff_eq hq hp).1 (Int.natCast_dvd_natCast.1 hd)
  rw [← Int.ideal_span_absNorm_eq_self (w.asIdeal.under ℤ), he]

theorem not_mem_sq_of_ramificationIdx {p : ℕ} (hl : p.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hv : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) (he : w.asIdeal.ramificationIdx ℤ = 1) :
    ((p : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {((p : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ w.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have := w.isPrime
  have : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) w.asIdeal hb] at he
  intro hsq
  have hne : Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) w.asIdeal ≠ 1 := by
    rw [Ideal.ramificationIdx'_ne_one_iff hle, hmap, Ideal.span_le]; simpa using hsq
  exact hne he

theorem not_le_differentIdeal (v : HeightOneSpectrum (𝓞 F)) (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully E v) :
    ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal := by
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  set p := Ideal.absNorm (v.asIdeal.under ℤ) with hpdef
  have hp : p.Prime := Nat.absNorm_under_prime v.asIdeal
  have hpv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := Int.absNorm_under_mem v.asIdeal
  have hP : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := (Int.ideal_span_absNorm_eq_self _).symm
  have hE : ∀ w : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ w.asIdeal → ((p : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := by
    intro w hw
    have hmem : w.asIdeal ∈ (v.asIdeal.under ℤ).primesOver (𝓞 E) :=
      ⟨w.isPrime, ⟨by rw [hP, under_eq_span_of_mem w hp hw]⟩⟩
    exact not_mem_sq_of_ramificationIdx hp w hw (ramificationIdx_eq_one_of_splitsFully v h _ hmem)
  have hnd := GlobalTheory.SplitUnram.not_dvd_different hp v hpv (GlobalTheory.SplitUnram.not_mem_sq_of_ext hE v)
  exact fun hle => hnd (Ideal.dvd_iff_le.2 hle)

end GlobalTheory.SplitFullyUnr

theorem GlobalTheory.SplitFullyUnr.psiUnr_of_splitsFully : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully D.host.E v → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr W.ψ v := by
  intro D T L sc G W v hv
  exact GlobalTheory.BaseGoodPlace.psiUnr_of_not_le W.ψ_std v (GlobalTheory.SplitFullyUnr.not_le_differentIdeal v hv)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharUnramifiedOfSplitsCompletelyAbovePlaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localAddCharUnramified_of_splitsCompletelyAbovePlace : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully D.host.E v → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr W.ψ v := by
  first | exact @GlobalTheory.SplitFullyUnr.psiUnr_of_splitsFully | exact GlobalTheory.SplitFullyUnr.psiUnr_of_splitsFully | (intros; apply GlobalTheory.SplitFullyUnr.psiUnr_of_splitsFully <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped ENNReal Classical

namespace GlobalTheory.WeilL2Words

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def arch1 (z : mixedEmbedding.mixedSpace F) : AdeleRing (𝓞 F) F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z, 0)

def IsStdInf (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : Prop :=
  ∃ ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ, (∀ z : mixedEmbedding.mixedSpace F, z ≠ 0 → ∃ u, ℓ (z * u) ≠ 0) ∧
    ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)

def arch (x : κ → mixedEmbedding.mixedSpace F) : κ → AdeleRing (𝓞 F) F := fun i => arch1 F (x i)

def archPair (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) :=
  (arch F h.1, arch F h.2)

def archPart (a : κ → AdeleRing (𝓞 F) F) : κ → mixedEmbedding.mixedSpace F :=
  fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1

def l2A (μ : @Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : ℝ≥0∞ :=
  @lintegral _ (borel _) μ fun y => ∫⁻ x, ‖Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2

variable [Invertible (2 : AdeleRing (𝓞 F) F)]

def dS (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : (κ → AdeleRing (𝓞 F) F) → ℂ :=
  fun a => deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) Φ a) 0

def word (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hs : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : (κ → AdeleRing (𝓞 F) F) → ℂ :=
  hs.foldr (fun h g => dS F ψ h g) Φ

theorem word_cons (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (h) (hs) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    word F ψ (h :: hs) Φ = dS F ψ h (word F ψ hs Φ) := rfl

end GlobalTheory.WeilL2Words

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductRepresentationReorderEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductRepresentationReorderEquiv
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.PlacingProd

theorem multiProd_placing_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h n : ℕ) (d : Fin h → ℕ) (e e' : (Σ a, Fin (d a)) ≃ Fin n) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), Nonempty ((multiProd e π).Equiv (multiProd e' π)) := by
  intro k _ _ _ _ h n d e e' X _ _ π
  exact (GlobalTheory.SmGL.Placing.parInd_jac_placing k (Fin h) (Fin n) (fun a => Fin (d a)) e e' _).1 _

end GlobalTheory.PlacingProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductRepresentationReorderEquivStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_representation_reorder_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h n : ℕ) (d : Fin h → ℕ) (e e' : (Σ a, Fin (d a)) ≃ Fin n) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), Nonempty ((multiProd e π).Equiv (multiProd e' π)) := by
  first | exact @GlobalTheory.PlacingProd.multiProd_placing_equiv | exact GlobalTheory.PlacingProd.multiProd_placing_equiv | (intros; apply GlobalTheory.PlacingProd.multiProd_placing_equiv <;> assumption)
end
end
