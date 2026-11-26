module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceVacuumIsLocalVacuumChart

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBddD
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBddC
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBddB
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LThBdd

variable {D : D7} {n : ℕ}

theorem map_upper_unipotent_block {R : Type} [CommRing R] (f : AE D →+* R) (b : Mx D n n) :
    (blk4 (1 : Mx D n n) b 0 1).map f = blk4 1 (b.map f) 0 1 := by
  simp only [blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_one _ f.map_zero f.map_one,
    Matrix.map_zero _ f.map_zero]

theorem val_bc_matHom {R : Type} [CommRing R] (f : AE D →+* R) (g : G D n) :
    ((Formalism.UG.bc f (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) g) : GL (Fin (n + n)) R) : Matrix (Fin (n + n)) (Fin (n + n)) R) =
      (mat g).map f := rfl

theorem proj_eq_one_iff {v : Pl D} {g : G D n} :
    GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1 ↔ (mat g).map (cv D v) = 1 := by
  rw [← (matHom_injective _ D.sp.cm.sig (Jst D n)).eq_iff, matHom_proj, map_one]
  constructor
  · intro h
    have := congrArg Units.val h
    rwa [val_bc_matHom, Units.val_one] at this
  · intro h
    apply Units.ext
    rw [val_bc_matHom, Units.val_one]
    exact h

theorem projArch_eq_one_iff {w : InfinitePlace D.host.F} {g : G D n} :
    projArch D.sp.cm.sig (Jst D n) w g = 1 ↔ (mat g).map (compInf D.host.F D.host.E w) = 1 := by
  rw [← (matHom_injective _ D.sp.cm.sig (Jst D n)).eq_iff, matHom_projArch, map_one]
  constructor
  · intro h
    have := congrArg Units.val h
    rwa [val_bc_matHom, Units.val_one] at this
  · intro h
    apply Units.ext
    rw [val_bc_matHom, Units.val_one]
    exact h

theorem nb_mem_atPts {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (x : hermA D n)
    (hinf : ∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) (hoff : ∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) :
    nb x ∈ atPts D.sp.cm.sig (Jst D n) {v} := by
  rw [mem_atPts, mem_finPts_iff_forall]
  refine ⟨fun w => ?_, fun u hu => ?_⟩
  · rw [projArch_eq_one_iff, hnb x, map_upper_unipotent_block]
    have : x.1.map (compInf D.host.F D.host.E w) = 0 := by
      ext i j; exact hinf w i j
    rw [this]; exact GlobalTheory.StdUnn.Model.block_matrix_one
  · rw [proj_eq_one_iff, hnb x, map_upper_unipotent_block]
    have : x.1.map (cv D u) = 0 := by
      ext i j; exact hoff u (by simpa using hu) i j
    rw [this]; exact GlobalTheory.StdUnn.Model.block_matrix_one

theorem commute_of_atPts {v : Pl D} {a g : G D n} (ha : a ∈ atPts D.sp.cm.sig (Jst D n) {v})
    (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1) : a * g = g * a := by
  rw [mem_atPts, mem_finPts_iff_forall] at ha
  apply GAd_ext
  · intro w; simp [map_mul, ha.1 w]
  · intro u
    by_cases h : u = v
    · subst h; simp [hg]
    · simp [ha.2 u (by simpa using h)]

theorem mulVec_mem_iff {A : Type} [CommRing A] {ι : Type} [Fintype ι] [DecidableEq ι] (R : Subring A)
    {M M' : Matrix ι ι A} (hM : ∀ i j, M i j ∈ R) (hM' : ∀ i j, M' i j ∈ R) (h : M' * M = 1) (y : ι → A) :
    (∀ i, y i ∈ R) ↔ ∀ i, (M *ᵥ y) i ∈ R := by
  have key : ∀ N : Matrix ι ι A, (∀ i j, N i j ∈ R) → ∀ z : ι → A, (∀ i, z i ∈ R) → ∀ i, (N *ᵥ z) i ∈ R :=
    fun N hN z hz i => by
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => R.mul_mem (hN i j) (hz j)
  refine ⟨key M hM y, fun hy => ?_⟩
  have : y = M' *ᵥ (M *ᵥ y) := by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  rw [this]; exact key M' hM' _ hy

theorem block_matrix_entry_property {A : Type} (p : A → Prop) {a b c d : Matrix (Fin n) (Fin n) A}
    (ha : ∀ i j, p (a i j)) (hb : ∀ i j, p (b i j)) (hc : ∀ i j, p (c i j)) (hd : ∀ i j, p (d i j)) :
    ∀ i j, p (blk4 a b c d i j) := by
  intro i j
  simp only [blk4, Matrix.submatrix_apply]
  generalize finSumFinEquiv.symm i = x
  generalize finSumFinEquiv.symm j = y
  rcases x with x | x <;> rcases y with y | y
  · exact ha x y
  · exact hb x y
  · exact hc x y
  · exact hd x y

theorem mem_K_of_atPts {v : Pl D} {g : G D n} (hg : g ∈ atPts D.sp.cm.sig (Jst D n) {v})
    (hv : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v) :
    g ∈ K D n := by
  rw [mem_atPts, mem_finPts_iff_forall] at hg
  unfold GlobalTheory.StdUnn.K levelAll
  refine Subgroup.mem_inf.2 ⟨mem_levelOpen.2 fun u => ?_, Subgroup.mem_iInf.2 fun w => ?_⟩
  · by_cases h : u = v
    · subst h; exact hv
    · rw [hg.2 u (by simpa using h)]; exact one_mem _
  · rw [Subgroup.mem_comap, hg.1 w]; exact one_mem _

theorem stab_of_entries {v : Pl D} (g : G D n) (hM : ∀ i j, cv D v (mat g i j) ∈ intLoc D.host.F D.host.E v)
    (hM' : ∀ i j, cv D v (mat g⁻¹ i j) ∈ intLoc D.host.F D.host.E v) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v := by
  have e : ∀ (h : G D n) i j, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v h)).1 i j =
      cv D v (mat h i j) := fun h i j => by rw [matHom_proj]; rfl
  rw [mem_stabLoc]
  intro y
  rw [mem_latLoc_stdLattice, mem_latLoc_stdLattice]
  refine mulVec_mem_iff _
    (M' := (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g⁻¹)).1)
    (fun i j => by rw [e]; exact hM i j) (fun i j => by rw [e]; exact hM' i j) ?_ y
  rw [← Units.val_mul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Units.val_one]

theorem mat_inj {g h : G D n} (e : mat g = mat h) : g = h := Subtype.ext (Units.ext e)

theorem nb_neg_mul {nb : hermA D n → G D n} (hnb : IsNMap nb) (o : hermA D n) : nb (-o) * nb o = 1 := by
  apply mat_inj
  show mat (nb (-o)) * mat (nb o) = mat 1
  rw [hnb, hnb, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
  simp only [AddSubgroup.coe_neg, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    neg_add_cancel, add_neg_cancel]
  rw [GlobalTheory.StdUnn.Model.block_matrix_one]
  rfl

theorem nb_mem_KAt {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (o : hermA D n) (ho : IntAt v o) :
    nb o ∈ KAt D n v := by
  have ha := nb_mem_atPts hnb o ho.1 ho.2.1
  have h1 : ∀ i j, cv D v ((1 : Mx D n n) i j) ∈ intLoc D.host.F D.host.E v := fun i j => by
    rw [Matrix.one_apply]
    split_ifs
    · rw [map_one]; exact one_mem _
    · rw [map_zero]; exact zero_mem _
  have h0 : ∀ i j, cv D v ((0 : Mx D n n) i j) ∈ intLoc D.host.F D.host.E v := fun i j => by
    rw [Matrix.zero_apply, map_zero]; exact zero_mem _
  have hinv : (nb o)⁻¹ = nb (-o) := (eq_inv_of_mul_eq_one_left (nb_neg_mul hnb o)).symm
  have hst := stab_of_entries (v := v) (nb o)
    (by rw [hnb o]; exact block_matrix_entry_property (fun a => cv D v a ∈ intLoc D.host.F D.host.E v) h1 ho.2.2 h0 h1)
    (by
      rw [hinv, hnb (-o)]
      exact block_matrix_entry_property (fun a => cv D v a ∈ intLoc D.host.F D.host.E v) h1
        (fun i j => by rw [AddSubgroup.coe_neg, Matrix.neg_apply, map_neg]; exact neg_mem (ho.2.2 i j)) h0 h1)
  exact Subgroup.mem_inf.2 ⟨mem_K_of_atPts ha hst, ha⟩

def cjv (nb : hermA D n → G D n) (v : Pl D) (x : hermA D n) : G D n →* GLoc D.sp.cm.sig (Jst D n) v :=
  (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v).comp (MulAut.conj (nb x)⁻¹).toMonoidHom

theorem cjv_apply (nb : hermA D n → G D n) (v : Pl D) (x : hermA D n) (k : G D n) :
    cjv nb v x k = GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v ((nb x)⁻¹ * k * nb x) := by
  simp [cjv, MulAut.conj_apply]

def Ucut (nb : hermA D n → G D n) (v : Pl D) (s : Finset (hermA D n)) : Subgroup (G D n) where
  carrier := {k | ∀ x ∈ s, cjv nb v x k ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v}
  one_mem' := fun x _ => by rw [map_one]; exact one_mem _
  mul_mem' := fun ha hb x hx => by rw [map_mul]; exact mul_mem (ha x hx) (hb x hx)
  inv_mem' := fun ha x hx => by rw [map_inv]; exact inv_mem (ha x hx)

theorem mem_Ucut {nb : hermA D n → G D n} {v : Pl D} {s : Finset (hermA D n)} {k : G D n} :
    k ∈ Ucut nb v s ↔ ∀ x ∈ s, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v ((nb x)⁻¹ * k * nb x) ∈
      stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v := by
  show (∀ x ∈ s, _) ↔ _
  simp only [cjv_apply]

theorem isOpen_Ucut (nb : hermA D n → G D n) (v : Pl D) (s : Finset (hermA D n)) :
    IsOpen (Ucut nb v s : Set (G D n)) := by
  have : (Ucut nb v s : Set (G D n)) = ⋂ x ∈ s, (fun k => GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v ((nb x)⁻¹ * k * nb x)) ⁻¹'
      (stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v : Set _) := by
    ext k
    simp only [SetLike.mem_coe, mem_Ucut, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  haveI : Submodule.IsFullLattice D.host.E (stdLattice D.host.E (n + n)) := isLattice_stdLattice
  exact isOpen_biInter_finset fun x _ => (isOpen_stabLoc _ _ _ v).preimage
    ((continuous_proj _ _ v).comp ((continuous_const.mul continuous_id).mul continuous_const))

theorem mem_Ucut_of_proj {nb : hermA D n → G D n} {v : Pl D} {s : Finset (hermA D n)} {k k' : G D n}
    (h : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v k = GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v k')
    (hk : k ∈ Ucut nb v s) : k' ∈ Ucut nb v s := by
  rw [mem_Ucut] at hk ⊢
  intro x hx
  have := hk x hx
  rwa [map_mul, map_mul, h, ← map_mul, ← map_mul] at this

theorem conj_mem_KAt {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) {k : G D n}
    (hk : k ∈ Ucut nb v C.s) (hkv : k ∈ atPts D.sp.cm.sig (Jst D n) {v}) {x : hermA D n} (hx : x ∈ C.s) :
    (nb x)⁻¹ * k * nb x ∈ KAt D n v := by
  have ha := nb_mem_atPts hnb x (C.inf x hx) (C.off x hx)
  have hm : (nb x)⁻¹ * k * nb x ∈ atPts D.sp.cm.sig (Jst D n) {v} := mul_mem (mul_mem (inv_mem ha) hkv) ha
  exact Subgroup.mem_inf.2 ⟨mem_K_of_atPts hm ((mem_Ucut.1 hk) x hx), hm⟩

def locPart (v : Pl D) (g : G D n) : G D n :=
  emb D.sp.cm.sig (Jst D n) v (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g)

theorem locPart_mem_atPts (v : Pl D) (g : G D n) : locPart v g ∈ atPts D.sp.cm.sig (Jst D n) {v} := by
  rw [mem_atPts, mem_finPts]
  exact ⟨by simp [locPart], fun u hu => proj_emb_ne _ _ (by simpa using hu) _⟩

theorem proj_locPart (v : Pl D) (g : G D n) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v (locPart v g) = GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g :=
  proj_emb_self _ _ _ _

theorem continuous_locPart (v : Pl D) : Continuous (locPart (n := n) v) :=
  (continuous_emb _ _ v).comp (continuous_proj _ _ v)

end PositivityTheory.Rg.Rsw.L.LThBdd

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LThBdd

variable {D : D7} {n : ℕ} {W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D W.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ W.rank n)}

theorem eval_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → schwartzA θ W.rank n) (X : Mx D W.rank n) :
    (∑ i ∈ s, c i • f i).1 X = ∑ i ∈ s, c i * (f i).1 X := by
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem omega_nb (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) (x : hermA D n)
    (Φ : schwartzA θ W.rank n) (X : Mx D W.rank n) : (ω (nb x) Φ).1 X = pch ψ x.1 (ip W X X) * Φ.1 X := by
  exact hω.unip (nb x) x.1 (hnb x) Φ X

theorem omega_cut (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) {g : G D n}
    (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1) (X : Mx D W.rank n) :
    (ω g Ψ').1 X = cutF ψ C (ip W X X) * (ω g Ψ).1 X := by
  subst hΨ'
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul]
  rw [eval_sum, show cutF ψ C (ip W X X) = ∑ x ∈ C.s, C.co x * pch ψ x.1 (ip W X X) from rfl,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hcomm : nb x * g = g * nb x :=
    PositivityTheory.Rg.Rsw.L.LThBdd.commute_of_atPts
      (PositivityTheory.Rg.Rsw.L.LThBdd.nb_mem_atPts hnb x (C.inf x hx) (C.off x hx)) hg
  rw [← Module.End.mul_apply, ← map_mul, ← hcomm, map_mul, Module.End.mul_apply,
    omega_nb hω hnb x, mul_assoc]

theorem pch_eq_one (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (Ψ : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ) {g : G D n}
    (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1) (X : Mx D W.rank n) (hX : (ω g Ψ).1 X ≠ 0)
    (o : hermA D n) (ho : IntAt v o) : pch ψ o.1 (ip W X X) = 1 := by
  have hk := PositivityTheory.Rg.Rsw.L.LThBdd.nb_mem_KAt hnb o ho
  have hfix : ω (nb o) (ω g Ψ) = ω g Ψ := by
    rw [← Module.End.mul_apply, ← map_mul,
      PositivityTheory.Rg.Rsw.L.LThBdd.commute_of_atPts (Subgroup.mem_inf.mp hk).2 hg, map_mul,
      Module.End.mul_apply, hΨ _ hk]
  have h := omega_nb hω hnb o (ω g Ψ) X
  rw [hfix] at h
  exact mul_right_cancel₀ hX (h.symm.trans (one_mul _).symm)

theorem inner_rat' (ξ : Matrix (Fin W.rank) (Fin n) D.host.E) :
    GlobalTheory.StdUnn.inner W (rat ξ : Mx D W.rank n) (rat ξ) = rat (gramQ W ξ) := by
  rw [show GlobalTheory.StdUnn.inner W (rat ξ : Mx D W.rank n) (rat ξ) =
      GlobalTheory.MixModel.adj (rat ξ) * (GlobalTheory.MixModel.rat (Formalism.BasicNotions.HSpace.gram W) * rat ξ) from rfl,
    ← GlobalTheory.MixModel.rat_conjTranspose, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul,
    ← GlobalTheory.MixModel.cT_sig]
  rfl

theorem ip_mt_rat (h : GA D W) (ξ : Matrix (Fin W.rank) (Fin n) D.host.E) :
    ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ)) = rat (gramQ W ξ) := by
  calc ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ))
      = GlobalTheory.MixModel.adj (mt W h⁻¹ * rat ξ) * (GlobalTheory.MixModel.gA W * (mt W h⁻¹ * rat ξ)) := rfl
    _ = GlobalTheory.MixModel.adj (rat ξ : Mx D W.rank n) *
          ((GlobalTheory.MixModel.adj (mt W h⁻¹) * (GlobalTheory.MixModel.gA W * mt W h⁻¹)) * rat ξ) := by
        rw [GlobalTheory.MixModel.adj_mul]
        simp only [Matrix.mul_assoc]
    _ = GlobalTheory.StdUnn.inner W (rat ξ : Mx D W.rank n) (rat ξ) := by
        rw [GlobalTheory.MixModel.mt_unitary]
        rfl
    _ = rat (gramQ W ξ) := inner_rat' ξ

theorem rank_gramQ_le (ξ : Matrix (Fin W.rank) (Fin n) D.host.E) : (gramQ W ξ).rank ≤ ξ.rank := by
  exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_mul_le_right _ _)

theorem term_zero (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (hC : C.Kills ψ W.rank) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) {g : G D n} (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1)
    (h : GA D W) (ξ : Matrix (Fin W.rank) (Fin n) D.host.E) (hξ : ξ.rank ≠ W.rank) :
    (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ)) = 0 := by
  rw [omega_cut hω hnb C Ψ Ψ' hΨ' hg, ip_mt_rat]
  by_cases h0 : (ω g Ψ).1 (mm (mt W h⁻¹) (rat ξ)) = 0
  · rw [h0, mul_zero]
  · have hq : gramQ W ξ = ξᴴ * (Formalism.BasicNotions.HSpace.gram W * ξ) := by
      rw [← GlobalTheory.MixModel.cT_sig]
      rfl
    have hherm : ((gramQ W ξ).map ⇑(D.sp.cm.sig)).transpose = gramQ W ξ := by
      change Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (gramQ W ξ) = gramQ W ξ
      rw [GlobalTheory.MixModel.cT_sig, hq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, GlobalTheory.MixModel.gram_conjTranspose, Matrix.mul_assoc]
    have hlt : (gramQ W ξ).rank < W.rank :=
      (rank_gramQ_le ξ).trans_lt (lt_of_le_of_ne (Matrix.rank_le_height ξ) hξ)
    have hcut := hC (⟨gramQ W ξ, hherm⟩ : PositivityTheory.GramSchwartzFunctions.HermE D n) hlt (fun o ho => by
      have := pch_eq_one hω hnb Ψ hΨ hg _ h0 o ho
      rwa [ip_mt_rat] at this)
    rw [show cutF ψ C (rat (gramQ W ξ)) = 0 from hcut, zero_mul]

theorem theta_nb (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (hC : C.Kills ψ W.rank) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) (x : hermA D n) {g : G D n}
    (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1) (h : GA D W) :
    theta ω Ψ' (nb x * g) h =
      ∑' y : {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank},
        pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat y.1)) (mm (mt W h⁻¹) (rat y.1))) * (ω g Ψ').1 (mm (mt W h⁻¹) (rat y.1)) := by
  have hfun : ∀ ξ : Matrix (Fin W.rank) (Fin n) D.host.E,
      ((ω (nb x * g)) Ψ').1 (mm (mt W h⁻¹) (rat ξ)) =
        pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ))) *
          (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ)) := by
    intro ξ
    rw [map_mul, Module.End.mul_apply]
    exact omega_nb hω hnb x _ _
  have hsub : Function.support (fun ξ : Matrix (Fin W.rank) (Fin n) D.host.E =>
      pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ))) *
        (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ))) ⊆ {y | y.rank = W.rank} := by
    intro ξ hξ
    by_contra hne
    apply hξ
    show _ * _ = 0
    rw [term_zero hω hnb C hC Ψ Ψ' hΨ hΨ' hg h ξ hne, mul_zero]
  calc theta ω Ψ' (nb x * g) h
      = ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E, ((ω (nb x * g)) Ψ').1 (mm (mt W h⁻¹) (rat ξ)) := rfl
    _ = ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E,
          pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ))) *
            (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ)) := tsum_congr hfun
    _ = _ := (tsum_subtype_eq_of_support_subset hsub).symm

theorem fix_open {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) (Ψ Ψ' : schwartzA θ W.rank n)
    (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ) (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) {k : G D n}
    (hk : k ∈ Ucut nb v C.s) (hkv : k ∈ atPts D.sp.cm.sig (Jst D n) {v}) : ω k Ψ' = Ψ' := by
  subst hΨ'
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hc := PositivityTheory.Rg.Rsw.L.LThBdd.conj_mem_KAt hnb C hk hkv hx
  congr 1
  calc ω k (ω (nb x) Ψ) = ω (nb x * ((nb x)⁻¹ * k * nb x)) Ψ := by
        rw [show nb x * ((nb x)⁻¹ * k * nb x) = k * nb x by group, map_mul, Module.End.mul_apply]
    _ = ω (nb x) (ω ((nb x)⁻¹ * k * nb x) Ψ) := by rw [map_mul, Module.End.mul_apply]
    _ = ω (nb x) Ψ := by rw [hΨ _ hc]

end PositivityTheory.Rg.Rsw.L.LThBdd

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LThBdd

variable {D : D7} {n : ℕ} {W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D W.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ W.rank n)}

theorem theta_cont (hθ : IsInfFam θ) (Φ : schwartzA θ W.rank n)
    (hcont : Continuous fun u : G D n × Mx D W.rank n => (ω u.1 Φ).1 u.2)
    (hmaj : ∀ C : Set (G D n), IsCompact C → ∃ M ∈ schwartzA θ W.rank n, ∀ g ∈ C, ∀ x, ‖(ω g Φ).1 x‖ ≤ ‖M x‖) :
    Continuous fun u : G D n × GA D W => theta ω Φ u.1 u.2 := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  obtain ⟨Qg, hQg, hpg⟩ := exists_compact_mem_nhds p.1
  obtain ⟨Qh, hQh, hph⟩ := exists_compact_mem_nhds p.2
  obtain ⟨M, hM, hMb⟩ := hmaj Qg hQg
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates D θ hθ W.rank n
  obtain ⟨-, K, hK, hC⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ W.rank n M (GlobalTheory.T.isSchwartzBruhatAdelicMatrix_of_mem_adelicSchwartz D θ hθ W.rank n M hM)
  obtain ⟨K', hK', hmul⟩ := GlobalTheory.T.adelicMatrixSchwartzMajorant_inv_mul_le D θ hθ W n Qh hQh K hK
  obtain ⟨C, hC⟩ := hC N
  obtain ⟨C₂, hC₂, hmul'⟩ := hmul N
  obtain ⟨b, hb, hb'⟩ := hN K' {0} hK' isCompact_singleton
  have hterm : ∀ ξ : Matrix (Fin W.rank) (Fin n) D.host.E,
      Continuous fun u : G D n × GA D W => (ω u.1 Φ).1 (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n)) := fun ξ =>
    hcont.comp (continuous_fst.prodMk (((GlobalTheory.LatNhds.continuous_mt_inv W).comp continuous_snd).matrix_mul
      continuous_const))
  have hon : ContinuousOn (fun u : G D n × GA D W => ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E,
      (ω u.1 Φ).1 (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))) (Qg ×ˢ Qh) := by
    refine continuousOn_tsum (fun ξ => (hterm ξ).continuousOn) (hb.mul_left (|C| * C₂)) fun ξ u hu => ?_
    have h1 := hMb u.1 hu.1 (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))
    have h2 := hC (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))
    have h3 := hmul' u.2 hu.2 (rat ξ : Mx D W.rank n)
    have h4 := hb' 0 rfl ξ
    rw [zero_add] at h4
    have hm0 := GlobalTheory.Unf.maj_nonneg θ K N (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))
    calc ‖(ω u.1 Φ).1 (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))‖
        ≤ C * GlobalTheory.Unf.maj θ K N (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n)) := h1.trans h2
      _ ≤ |C| * GlobalTheory.Unf.maj θ K N (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hm0
      _ ≤ |C| * (C₂ * GlobalTheory.Unf.maj θ K' N (rat ξ : Mx D W.rank n)) := mul_le_mul_of_nonneg_left h3 (abs_nonneg C)
      _ ≤ |C| * (C₂ * b ξ) := by gcongr
      _ = |C| * C₂ * b ξ := by ring
  exact hon.continuousAt (prod_mem_nhds hpg hph)

theorem theta_full (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (hC : C.Kills ψ W.rank) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) {g : G D n}
    (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1) (h : GA D W) :
    theta ω Ψ' g h = ∑' y : {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank},
      (ω g Ψ').1 (mm (mt W h⁻¹) (rat y.1)) := by
  unfold theta
  have hsupp : Function.support (fun ξ : Matrix (Fin W.rank) (Fin n) D.host.E => (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ))) ⊆
      {y : Matrix (Fin W.rank) (Fin n) D.host.E | y.rank = W.rank} := by
    intro ξ hξ
    by_contra hr
    exact hξ (term_zero hω hnb C hC Ψ Ψ' hΨ hΨ' hg h ξ hr)
  exact (tsum_subtype_eq_of_support_subset hsupp).symm

theorem bound_triv (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (hC : C.Kills ψ W.rank) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) (hLB : LatBound) (hθ : IsInfFam θ)
    (hmaj : ∀ Q : Set (G D n), IsCompact Q → ∃ M ∈ schwartzA θ W.rank n, ∀ g ∈ Q, ∀ x, ‖(ω g Ψ').1 x‖ ≤ ‖M x‖)
    (Q : Set (G D n)) (hQ : IsCompact Q) :
    ∃ b : ℝ, ∀ g ∈ Q, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1 → ∀ h, ‖theta ω Ψ' g h‖ ≤ b := by
  obtain ⟨M, hM, hMb⟩ := hmaj Q hQ
  obtain ⟨B, hB⟩ := hLB D θ hθ W n M hM
  refine ⟨B, fun g hg hgv h => ?_⟩
  rw [theta_full hω hnb C hC Ψ Ψ' hΨ hΨ' hgv h]
  have e : ‖∑' y : {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank},
      (ω g Ψ').1 (mm (mt W h⁻¹) (rat y.1))‖ₑ ≤ B :=
    (enorm_tsum_le_tsum_enorm).trans ((ENNReal.tsum_le_tsum fun y => by
      have := hMb g hg (mm (mt W h⁻¹) (rat y.1))
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal this).trans (hB h))
  have e2 : ENNReal.ofReal ‖∑' y : {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank},
      (ω g Ψ').1 (mm (mt W h⁻¹) (rat y.1))‖ ≤ ENNReal.ofReal B := by
    rw [ofReal_norm, ENNReal.ofReal_coe_nnreal]; exact e
  exact (ENNReal.ofReal_le_ofReal_iff B.2).1 e2

end PositivityTheory.Rg.Rsw.L.LThBdd

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBddA
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LThBdd

variable {D : D7} {n : ℕ}

theorem theta_levi {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hχ : IsHeckeChar D χ) (hω : IsWeilSch ψ χ θ V μ ω)
    (g : G D n) (a : GL (Fin n) D.host.E) (hg : mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))))
    (Φ : schwartzA θ V.rank n) :
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  let a' : GL (Fin n) (AE D) := Matrix.GeneralLinearGroup.map (incA D) a
  have hdet : Matrix.GeneralLinearGroup.det a' =
      Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det a) := by
    apply Units.ext
    simp [a', Matrix.GeneralLinearGroup.map]
    exact (RingHom.map_det _ _).symm
  have h1 : absA D (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]; exact absE_inclR _
  have h2 : χ (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]; exact hχ.2 _
  have hinv : (a'⁻¹).1 = (a⁻¹).1.map (incA D) := by
    show ((Matrix.GeneralLinearGroup.map (incA D) a)⁻¹).1 = _
    rw [← map_inv]; rfl
  have hg' : mat g = blk4 a'.1 0 0 (adj (a'⁻¹).1) := by
    rw [hinv]; exact hg
  have hm : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      (ω g Φ).1 (ξ.map (incA D)) = Φ.1 ((ξ * a.1).map (incA D)) := by
    intro ξ
    rw [hω.levi g a' hg' Φ, h1, h2]
    have e : (HMul.hMul (ξ.map (incA D)) a'.1 : Mx D V.rank n) = (ξ * a.1).map (incA D) := by
      rw [Matrix.map_mul]; rfl
    rw [e]
    simp [npow]
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    { toFun := fun ξ => ξ * a.1
      invFun := fun ξ => ξ * (a⁻¹).1
      left_inv := fun ξ => by
        show ξ * a.1 * (a⁻¹).1 = ξ
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      right_inv := fun ξ => by
        show ξ * (a⁻¹).1 * a.1 = ξ
        rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one] }
  simp_rw [hm]
  exact e.tsum_eq (fun ξ => Φ.1 (ξ.map (incA D)))

theorem theta_unip {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hψ : IsCharAF D.host.F ψ) (hω : IsWeilSch ψ χ θ V μ ω)
    (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E) (hg : mat g = blk4 1 (b.map (incA D)) 0 1)
    (Φ : schwartzA θ V.rank n) :
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  refine tsum_congr fun ξ => ?_
  rw [hω.unip g (b.map (incA D)) hg Φ (ξ.map (incA D)), GlobalTheory.CompanionTheory.ThetaInv.psi_unip_rat hψ, one_mul]

open GlobalTheory.CompanionTheory.ThetaPoisson in
theorem theta_weyl {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hψ : IsCharAF D.host.F ψ) (hθ : IsInfFam θ) {𝓕 : Set (Mx D V.rank n)} (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    (hω : IsWeilSch ψ χ θ V μ ω) (g : G D n) (hg : mat g = blk4 0 1 (-1) 0) (Φ : schwartzA θ V.rank n) :
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D V.rank n
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have hT := isHermND_gram V
  obtain ⟨h1, h2⟩ := GlobalTheory.T.rationalAdelicMatrices_self_annihilator D V.rank n V.gram hT ψ hψ
  have hs := pairing_symm (n := n) hT ψ
  have hval : ∀ x, (ω g Φ).1 x = ∫ y, Φ.1 y * GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing V.gram ψ y x ∂μ := fun x => by
    rw [hω.weyl g hg Φ x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [hs y x]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing, GlobalTheory.SiegelWeilLitCompare.gramQ_eq]
    rfl
  haveI := hμ.1
  have key := poisson_translates (ratMx D V.rank n) K hK hKc (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing (n := n) V.gram ψ)
    (fun y => ?_) hs (fun x x' y => ?_) (fun x y => hψ.2.1 _) h1 h2 μ 𝓕 hμ.2.1 hμ.2.2 (f := Φ.1) ?_
    (translates_bound hθ Φ) ?_
  · simp only [← hval] at key
    rw [tsum_ratMx, tsum_ratMx (fun x => (ω g Φ).1 x)] at key
    exact key.symm
  · simp only [hs _ y]
    haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    have ht : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA (D := D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
    exact hψ.1.comp (ht.comp (continuous_const.matrix_mul continuous_id).matrix_trace)
  · simp only [hs _ y]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.gramQ GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.mmul
    rw [Matrix.mul_add, Matrix.trace_add, map_add (f := _), AddChar.map_add_eq_mul]
  · exact (GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ _ n Φ.1
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ _ n Φ.1 Φ.2)).1
  · simp only [← hval]
    exact (ratEquiv D V.rank n).summable_iff.1 (GlobalTheory.SiegelWeilLitCompare.summable_rat hθ (ω g Φ))

theorem thetaInv' {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hψ : IsCharAF D.host.F ψ) (hχ : IsHeckeChar D χ) (hθ : IsInfFam θ) {𝓕 : Set (Mx D V.rank n)}
    (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕) (hω : IsWeilSch ψ χ θ V μ ω) (Φ : schwartzA θ V.rank n) {γ : G D n}
    (hγ : γ ∈ GF D n) :
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω γ Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  let S : Subgroup (G D n) :=
    { carrier := {γ | ∀ Φ : schwartzA θ V.rank n,
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω γ Φ).1 (ξ.map (incA D)) =
          ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D))}
      one_mem' := fun Φ => by simp
      mul_mem' := fun {g h} hg hh Φ => by
        rw [map_mul, Module.End.mul_apply]
        exact (hg _).trans (hh Φ)
      inv_mem' := fun {g} hg Φ => by
        have := hg (ω g⁻¹ Φ)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
        exact this.symm }
  have hle : GF D n ≤ S := GlobalTheory.T.rational_group_le_of_generators_mem D n S (fun g a hg Φ => theta_levi hχ hω g a hg Φ)
    (fun g b hg Φ => theta_unip hψ hω g b hg Φ)
    (fun g hg Φ => theta_weyl hψ hθ hμ hω g hg Φ)
  exact hle hγ Φ

theorem theta_rat {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hψ : IsCharAF D.host.F ψ) (hχ : IsHeckeChar D χ) (hθ : IsInfFam θ) {𝓕 : Set (Mx D V.rank n)}
    (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕) (hω : IsWeilSch ψ χ θ V μ ω) (Φ : schwartzA θ V.rank n) {γ : G D n}
    (hγ : γ ∈ GF D n) (g : G D n) (h : GA D V) : theta ω Φ (γ * g) h = theta ω Φ g h := by
  have hc := (GlobalTheory.WeilSchComm.subst_mem_and_comm D n V ψ χ θ hθ μ 𝓕 hμ ω hω h⁻¹).2 γ (ω g Φ)
    (GlobalTheory.WeilSchComm.subst θ V n h⁻¹ (ω g Φ)) (fun _ => rfl)
  have ht := thetaInv' hψ hχ hθ hμ hω (GlobalTheory.WeilSchComm.subst θ V n h⁻¹ (ω g Φ)) hγ
  simp only [hc] at ht
  unfold theta
  rw [map_mul, Module.End.mul_apply]
  exact ht

end PositivityTheory.Rg.Rsw.L.LThBdd

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LThBdd

variable {D : D7} {n : ℕ} {W : HSp D} {θ : InfFam D} {ω : G D n →* Module.End ℂ (schwartzA θ W.rank n)}

theorem bound_all {v : Pl D} (U : Subgroup (G D n)) (hUo : IsOpen (U : Set (G D n))) (Φ : schwartzA θ W.rank n)
    (hrat : ∀ γ ∈ GF D n, ∀ g h, theta ω Φ (γ * g) h = theta ω Φ g h)
    (hfix : ∀ k ∈ U, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ω k Φ = Φ)
    (hU : ∀ k k' : G D n, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v k = GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v k' →
      k ∈ U → k' ∈ U)
    (hdec : ∀ g : G D n, ∃ γ ∈ GF D n, ∃ g' : G D n, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g' = 1 ∧
      ∃ k ∈ U, k ∈ atPts D.sp.cm.sig (Jst D n) {v} ∧ g = γ * g' * k)
    (hb : ∀ Q : Set (G D n), IsCompact Q → ∃ b : ℝ, ∀ g ∈ Q, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1 →
      ∀ h, ‖theta ω Φ g h‖ ≤ b)
    (K₀ : Set (G D n)) (hK₀ : IsCompact K₀) : ∃ b : ℝ, ∀ g ∈ K₀, ∀ h, ‖theta ω Φ g h‖ ≤ b := by
  have hred : ∀ γ ∈ GF D n, ∀ g' k, k ∈ U → k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ∀ h,
      theta ω Φ (γ * g' * k) h = theta ω Φ g' h := by
    intro γ hγ g' k hk hkv h
    rw [mul_assoc, hrat γ hγ]
    unfold theta
    rw [map_mul, Module.End.mul_apply, hfix k hk hkv]
  choose γf hγf g'f hg'f kf hkf hkvf hgf using hdec
  obtain ⟨W₀, hW₀c, hW₀1, hW₀U⟩ := exists_compact_subset hUo (one_mem U)
  have hW₀n : W₀ ∈ 𝓝 (1 : G D n) := mem_interior_iff_mem_nhds.1 hW₀1
  have hN : ∀ g₀ : G D n, {g | g₀⁻¹ * g ∈ W₀} ∈ 𝓝 g₀ := fun g₀ =>
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hW₀n)
  obtain ⟨t, -, hcov⟩ := hK₀.elim_nhds_subcover (fun g₀ => {g | g₀⁻¹ * g ∈ W₀}) fun g₀ _ => hN g₀
  let τ : G D n → G D n := fun ε => ε * (locPart v ε)⁻¹
  have hτ : Continuous τ := continuous_id.mul ((continuous_locPart v).inv)
  let Q : Set (G D n) := ⋃ g₀ ∈ t, (fun ε => g'f g₀ * τ ε) '' W₀
  have hQ : IsCompact Q := t.isCompact_biUnion fun g₀ _ => hW₀c.image (continuous_const.mul hτ)
  obtain ⟨b, hb'⟩ := hb Q hQ
  refine ⟨b, fun g hg h => ?_⟩
  obtain ⟨g₀, hg₀t, hgg₀⟩ := Set.mem_iUnion₂.1 (hcov hg)
  set ε := g₀⁻¹ * g with hε
  have hεW : ε ∈ W₀ := hgg₀
  set εv := locPart v ε with hεv
  set ε' := τ ε with hε'
  have hpv : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v ε' = 1 := by
    show GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v (ε * (locPart v ε)⁻¹) = 1
    rw [map_mul, map_inv, proj_locPart, mul_inv_cancel]
  have hc : kf g₀ * ε' = ε' * kf g₀ := commute_of_atPts (hkvf g₀) hpv
  have hsplit : ε' * εv = ε := by
    show ε * (locPart v ε)⁻¹ * locPart v ε = ε
    group
  have hkU : kf g₀ * εv ∈ U := mul_mem (hkf g₀) (hU ε εv (proj_locPart v ε).symm (hW₀U hεW))
  have hkv : kf g₀ * εv ∈ atPts D.sp.cm.sig (Jst D n) {v} := mul_mem (hkvf g₀) (locPart_mem_atPts v ε)
  have heq : g = γf g₀ * (g'f g₀ * ε') * (kf g₀ * εv) := by
    calc g = g₀ * ε := by rw [hε]; group
      _ = γf g₀ * g'f g₀ * kf g₀ * (ε' * εv) := by rw [← hgf g₀, hsplit]
      _ = γf g₀ * g'f g₀ * (kf g₀ * ε') * εv := by simp only [mul_assoc]
      _ = γf g₀ * g'f g₀ * (ε' * kf g₀) * εv := by rw [hc]
      _ = _ := by simp only [mul_assoc]
  rw [heq, hred _ (hγf g₀) _ _ hkU hkv]
  refine hb' _ (Set.mem_iUnion₂.2 ⟨g₀, hg₀t, ε, hεW, rfl⟩) ?_ h
  rw [map_mul, hg'f g₀, hpv, one_mul]

end PositivityTheory.Rg.Rsw.L.LThBdd

namespace PositivityTheory.Rg.Rsw.L

open LThBdd in
theorem thBdd : WMaj → LatBound → WeakApproximationFinitePlace → ThBdd := by
  intro hWM hLB hWA D n W ψ hψ χ hχ hη θ hθ μ hμ ω hω nb hnb v C hC Ψ Ψ' hΨ hΨ'
  obtain ⟨𝓕, hμ'⟩ := hμ
  have hW := hWM D n W ψ hψ χ hχ hη θ hθ μ ⟨𝓕, hμ'⟩ ω hω Ψ'
  have hrat : ∀ γ ∈ GF D n, ∀ g h, theta ω Ψ' (γ * g) h = theta ω Ψ' g h :=
    fun γ hγ g h => theta_rat hψ hχ hθ hμ' hω Ψ' hγ g h
  have hfix : ∀ k ∈ Ucut nb v C.s, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ω k Ψ' = Ψ' :=
    fun k hk hkv => fix_open hnb C Ψ Ψ' hΨ hΨ' hk hkv
  refine ⟨theta_cont hθ Ψ' hW.1 hW.2, hrat, ⟨Ucut nb v C.s, isOpen_Ucut _ _ _, hfix⟩, fun K₀ hK₀ => ?_,
    fun x g hg => ⟨omega_cut hω hnb C Ψ Ψ' hΨ' hg, theta_nb hω hnb C hC Ψ Ψ' hΨ hΨ' x hg⟩⟩
  exact bound_all (Ucut nb v C.s) (isOpen_Ucut _ _ _) Ψ' hrat hfix (fun k k' e hk => mem_Ucut_of_proj e hk)
    (fun g => hWA D n v (Ucut nb v C.s) (isOpen_Ucut _ _ _) g)
    (bound_triv hω hnb C hC Ψ Ψ' hΨ hΨ' hLB hθ hW.2) K₀ hK₀

end PositivityTheory.Rg.Rsw.L

end
