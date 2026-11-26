module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvarianceOfConstantFourierCoefficient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocMIterateDiag

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutLowB
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutLowA
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCutLow

variable {D : D7} {n : ℕ}

theorem matHom_proj_val (v : Pl D) (g : G D n) :
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (proj D.sp.cm.sig (Jst D n) v g)).1 = (mat g).map (cv D v) := by
  rw [GlobalTheory.AdelicU.matHom_proj]; rfl

theorem matHom_projArch_val (w : InfinitePlace D.host.F) (g : G D n) :
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (projArch D.sp.cm.sig (Jst D n) w g)).1 =
      (mat g).map (compInf D.host.F D.host.E w) := by
  rw [GlobalTheory.AdelicU.matHom_projArch]; rfl

theorem block_matrix_diagonal_one_eq_one {R : Type} [CommRing R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem block_matrix_entry_property {R : Type} [CommRing R] (S : Subring R) {a b c d : Matrix (Fin n) (Fin n) R}
    (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S) (hc : ∀ i j, c i j ∈ S) (hd : ∀ i j, d i j ∈ S) (i j : Fin (n + n)) :
    blk4 a b c d i j ∈ S := by
  unfold blk4
  simp only [Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i' | i' <;> rcases finSumFinEquiv.symm j with j' | j' <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  exacts [ha _ _, hb _ _, hc _ _, hd _ _]

theorem map_mat_nb {nb : hermA D n → G D n} (hnb : IsNMap nb) {S : Type} [CommRing S] (f : AE D →+* S) (x : hermA D n) :
    (mat (nb x)).map f = blk4 1 (x.1.map f) 0 1 := by
  rw [hnb x, GlobalTheory.CompanionTheory.FourierN.blk4_map_alt, Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_zero _ (map_zero f)]

theorem proj_nb_eq_one {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {x : hermA D n}
    (hx : ∀ i j, cv D v (x.1 i j) = 0) : proj D.sp.cm.sig (Jst D n) v (nb x) = 1 := by
  refine GlobalTheory.AdelicU.matHom_injective _ _ _ (Units.ext ?_)
  rw [map_one, Units.val_one, matHom_proj_val, map_mat_nb hnb]
  have : x.1.map (cv D v) = 0 := Matrix.ext fun i j => hx i j
  rw [this, block_matrix_diagonal_one_eq_one]

theorem projArch_nb_eq_one {nb : hermA D n → G D n} (hnb : IsNMap nb) (w : InfinitePlace D.host.F) {x : hermA D n}
    (hx : ∀ i j, compInf D.host.F D.host.E w (x.1 i j) = 0) : projArch D.sp.cm.sig (Jst D n) w (nb x) = 1 := by
  refine GlobalTheory.AdelicU.matHom_injective _ _ _ (Units.ext ?_)
  rw [map_one, Units.val_one, matHom_projArch_val, map_mat_nb hnb]
  have : x.1.map (compInf D.host.F D.host.E w) = 0 := Matrix.ext fun i j => hx i j
  rw [this, block_matrix_diagonal_one_eq_one]

theorem nb_mem_atPts {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {x : hermA D n}
    (hinf : ∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) (hoff : ∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) :
    nb x ∈ atPts D.sp.cm.sig (Jst D n) {v} :=
  GlobalTheory.AdelicU.mem_atPts.2 ⟨GlobalTheory.AdelicU.mem_finPts_iff_forall.2 fun w => projArch_nb_eq_one hnb w (hinf w),
    fun v' hv' => proj_nb_eq_one hnb v' (hoff v' (by simpa using hv'))⟩

theorem nb_neg {nb : hermA D n → G D n} (hnb : IsNMap nb) (x : hermA D n) : nb (-x) = (nb x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← GlobalTheory.CompanionTheory.FourierN.nb_add hnb, neg_add_cancel, GlobalTheory.CompanionTheory.FourierN.nb_zero hnb])

theorem proj_nb_entry {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {y : hermA D n}
    (hy : ∀ i j, cv D v (y.1 i j) ∈ intLoc D.host.F D.host.E v) (i j : Fin (n + n)) :
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (proj D.sp.cm.sig (Jst D n) v (nb y))).1 i j ∈ intLoc D.host.F D.host.E v := by
  rw [matHom_proj_val, map_mat_nb hnb]
  refine block_matrix_entry_property _ (fun a b => ?_) (fun a b => hy a b) (fun a b => ?_) (fun a b => ?_) i j
  · rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  · exact zero_mem _
  · rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem proj_nb_mem_stabLoc {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {x : hermA D n}
    (hx : ∀ i j, cv D v (x.1 i j) ∈ intLoc D.host.F D.host.E v) :
    proj D.sp.cm.sig (Jst D n) v (nb x) ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v := by
  refine GlobalTheory.AdelicU.mem_stabLoc_stdLattice_iff.2 ⟨proj_nb_entry hnb v hx, ?_⟩
  have e : (proj D.sp.cm.sig (Jst D n) v (nb x))⁻¹ = proj D.sp.cm.sig (Jst D n) v (nb (-x)) := by
    rw [nb_neg hnb, map_inv]
  rw [e]
  refine proj_nb_entry hnb v fun i j => ?_
  have h1 : cv D v ((-x).1 i j) = -cv D v (x.1 i j) := RingHom.map_neg (cv D v) (x.1 i j)
  rw [h1]
  exact neg_mem (hx i j)

theorem mem_KAt_of {v : Pl D} {y : G D n}
    (h1 : y ∈ levelOpen D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n))) (h2 : y ∈ atPts D.sp.cm.sig (Jst D n) {v}) :
    y ∈ KAt D n v := by
  refine Subgroup.mem_inf.2 ⟨?_, h2⟩
  show y ∈ levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1
  refine GlobalTheory.AdelicU.mem_levelAll.2 ⟨GlobalTheory.AdelicU.mem_levelOpen.1 h1, fun w => ?_⟩
  rw [GlobalTheory.AdelicU.mem_finPts_iff_forall.1 (GlobalTheory.AdelicU.mem_atPts.1 h2).1 w]
  exact one_mem _

theorem nb_mem_KAt {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {x : hermA D n} (hx : IntAt v x) :
    nb x ∈ KAt D n v := by
  refine mem_KAt_of (GlobalTheory.AdelicU.mem_levelOpen.2 fun v' => ?_) (nb_mem_atPts hnb v hx.1 hx.2.1)
  by_cases h : v' = v
  · subst h; exact proj_nb_mem_stabLoc hnb _ hx.2.2
  · rw [proj_nb_eq_one hnb v' (hx.2.1 v' h)]; exact one_mem _

theorem commute_of_atPts {v : Pl D} {x g : G D n} (hx : x ∈ atPts D.sp.cm.sig (Jst D n) {v})
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) : x * g = g * x :=
  (GlobalTheory.AdelicU.commute_atPts_awayPts _ _ hx (GlobalTheory.AdelicU.mem_awayPts.2 fun u hu => by
    rw [Finset.mem_singleton.1 hu]; exact hg)).eq

def lev (nb : hermA D n → G D n) (s : Finset (hermA D n)) : Subgroup (G D n) :=
  ⨅ x : s, (levelOpen D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n))).comap (MulAut.conj (nb x.1)⁻¹).toMonoidHom

theorem isOpen_lev (nb : hermA D n → G D n) (s : Finset (hermA D n)) : IsOpen (lev nb s : Set (G D n)) := by
  have : Submodule.IsFullLattice D.host.E (stdLattice D.host.E (n + n)) := GlobalTheory.AdelicU.isLattice_stdLattice
  rw [lev, Subgroup.coe_iInf]
  refine isOpen_iInter_of_finite fun x => ?_
  rw [Subgroup.coe_comap]
  exact (GlobalTheory.AdelicU.isOpen_levelOpen _ _ _).preimage ((continuous_mul_const _).comp (continuous_const_mul _))

theorem conj_mem_KAt {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) {k : G D n}
    (hk : k ∈ lev nb C.s) (hkv : k ∈ atPts D.sp.cm.sig (Jst D n) {v}) {x : hermA D n} (hx : x ∈ C.s) :
    (nb x)⁻¹ * k * nb x ∈ KAt D n v := by
  have h1 := Subgroup.mem_iInf.1 hk ⟨x, hx⟩
  rw [Subgroup.mem_comap] at h1
  have hat := nb_mem_atPts hnb v (C.inf x hx) (C.off x hx)
  refine mem_KAt_of ?_ (mul_mem (mul_mem (inv_mem hat) hkv) hat)
  simpa [MulAut.conj_apply] using h1

end PositivityTheory.Rg.Rsw.L.LCutLow

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

namespace PositivityTheory.Rg.Rsw.L.LCutLow

open GlobalTheory.CompanionTheory.PcFc (chn)

variable {D : D7} {n : ℕ}

theorem chn_eq (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (b : hermA D n) :
    chn ψ β b = ψ (-GlobalTheory.CompanionTheory.FourierN.pr β.1 b.1) := rfl

theorem chn_cont {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) : Continuous (chn ψ β) :=
  hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr β.1).neg.comp continuous_subtype_val)

theorem chn_per {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) (γ : hermA D n)
    (hγ : γ ∈ ratHerm D n) (x : hermA D n) : chn ψ β (γ + x) = chn ψ β x := by
  rw [chn_eq, chn_eq, show (γ + x).1 = γ.1 + x.1 from rfl, GlobalTheory.CompanionTheory.FourierN.pr_add_right, neg_add, AddChar.map_add_eq_mul,
    GlobalTheory.CompanionTheory.FourierN.ker_of_rat hψ γ hγ, one_mul]

theorem per_nb {F : G D n → ℂ} (hinv : LeftInv (GF D n) F) {nb : hermA D n → G D n} (hnb : IsNMap nb) (g : G D n)
    (γ : hermA D n) (hγ : γ ∈ ratHerm D n) (x : hermA D n) : F (nb (γ + x) * g) = F (nb x * g) := by
  rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]
  exact hinv _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _

theorem cont_nb {F : G D n → ℂ} (hF : Continuous F) {nb : hermA D n → G D n} (hnb : IsNMap nb) (g : G D n) :
    Continuous (fun b => F (nb b * g)) :=
  hF.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_nb hnb).mul continuous_const)

theorem pch_rat (ψ : AddChar (AF D.host.F) ℂ) (x : Mx D n n) (β : HermE D n) :
    pch ψ x (rat β.1) = ψ (GlobalTheory.CompanionTheory.FourierN.pr β.1 x) := by
  show ψ (halfTr (Matrix.trace (x * β.1.map (incA D)))) = ψ (halfTr (Matrix.trace (β.1.map (incA D) * x)))
  rw [Matrix.trace_mul_comm]

theorem fc_eq (ψ : AddChar (AF D.host.F) ℂ) (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n)
    (F : G D n → ℂ) (β : HermE D n) (g : G D n) :
    fc ψ lam 𝓖 nb F β g = ∫ b in 𝓖, F (nb b * g) * chn ψ β b ∂lam := rfl

theorem chn_shift (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (b x : hermA D n) :
    chn ψ β b = chn ψ β (b + x) * pch ψ x.1 (rat β.1) := by
  rw [chn_eq, chn_eq, pch_rat, ← AddChar.map_add_eq_mul]
  congr 1
  rw [show (b + x).1 = b.1 + x.1 from rfl, GlobalTheory.CompanionTheory.FourierN.pr_add_right]
  abel

set_option synthInstance.maxHeartbeats 400000 in
theorem fc_nb_mul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hinv : LeftInv (GF D n) F) (β : HermE D n) (x : hermA D n) (g : G D n) :
    fc ψ lam 𝓖 nb F β (nb x * g) = pch ψ x.1 (rat β.1) * fc ψ lam 𝓖 nb F β g := by
  obtain ⟨hnb, hlam, hFD, -⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (hermA D n) := GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : DiscreteTopology (ratHerm D n) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  have : Countable (ratHerm D n) := countable_of_Lindelof_of_discrete
  have hper : ∀ γ ∈ ratHerm D n, ∀ b, F (nb (γ + b) * g) * chn ψ β (γ + b) = F (nb b * g) * chn ψ β b := fun γ hγ b => by
    rw [per_nb hinv hnb g γ hγ b, chn_per hψ β γ hγ b]
  have h : ∫ b in 𝓖, F (nb (b + x) * g) * chn ψ β (b + x) ∂lam = ∫ b in 𝓖, F (nb b * g) * chn ψ β b ∂lam :=
    GlobalTheory.CompanionTheory.ConstN.setIntegral_add_right (ratHerm D n) lam hFD (fun b => F (nb b * g) * chn ψ β b) hper x
  rw [fc_eq, fc_eq, ← h, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun b => ?_)
  show F (nb b * (nb x * g)) * chn ψ β b = pch ψ x.1 (rat β.1) * (F (nb (b + x) * g) * chn ψ β (b + x))
  rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc, chn_shift ψ β b x]
  ring

set_option synthInstance.maxHeartbeats 400000 in
theorem integrableOn_fc {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hF : Continuous F) (hinv : LeftInv (GF D n) F) (β : HermE D n) (h : G D n) :
    IntegrableOn (fun b => F (nb b * h) * chn ψ β b) 𝓖 lam := by
  obtain ⟨hnb, hlam, hFD, h1⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (hermA D n) := GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : DiscreteTopology (ratHerm D n) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  have : Countable (ratHerm D n) := countable_of_Lindelof_of_discrete
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)
  obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.PcFc.exists_bound_of_periodic (ratHerm D n) hK hcov _ (cont_nb hF hnb h)
    (per_nb hinv hnb h)
  refine Measure.integrableOn_of_bounded (M := M) (by rw [h1]; exact ENNReal.one_ne_top)
    ((cont_nb hF hnb h).mul (chn_cont hψ β)).aestronglyMeasurable (.of_forall fun b => ?_)
  rw [norm_mul, show ‖chn ψ β b‖ = 1 from hψ.2.1 _, mul_one]
  exact hM b

theorem fc_fix {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hinv : LeftInv (GF D n) F) {v : Pl D} (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g) (β : HermE D n)
    {x : hermA D n} (hx : IntAt v x) {g : G D n} (hg : proj D.sp.cm.sig (Jst D n) v g = 1) :
    fc ψ lam 𝓖 nb F β g = pch ψ x.1 (rat β.1) * fc ψ lam 𝓖 nb F β g := by
  rw [← fc_nb_mul hψ hC hinv β x g, fc_eq, fc_eq]
  refine integral_congr_ae (.of_forall fun b => ?_)
  show F (nb b * g) * _ = F (nb b * (nb x * g)) * _
  rw [commute_of_atPts (nb_mem_atPts hC.1 v hx.1 hx.2.1) hg, ← mul_assoc, hK _ (nb_mem_KAt hC.1 v hx) _]

theorem fc_cutR {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hF : Continuous F) (hinv : LeftInv (GF D n) F) {v : Pl D} (C : Cut D n v) (β : HermE D n) {g : G D n}
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) :
    fc ψ lam 𝓖 nb (cutR nb C F) β g = cutF ψ C (rat β.1) * fc ψ lam 𝓖 nb F β g := by
  have e : ∀ b, cutR nb C F (nb b * g) * chn ψ β b =
      ∑ x ∈ C.s, C.co x * (F (nb b * (nb x * g)) * chn ψ β b) := fun b => by
    unfold cutR
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mul_assoc (nb b) g, ← commute_of_atPts (nb_mem_atPts hC.1 v (C.inf x hx) (C.off x hx)) hg, mul_assoc]
  calc fc ψ lam 𝓖 nb (cutR nb C F) β g
      = ∫ b in 𝓖, ∑ x ∈ C.s, C.co x * (F (nb b * (nb x * g)) * chn ψ β b) ∂lam :=
        integral_congr_ae (.of_forall e)
    _ = ∑ x ∈ C.s, ∫ b in 𝓖, C.co x * (F (nb b * (nb x * g)) * chn ψ β b) ∂lam :=
        integral_finsetSum _ fun x _ => (integrableOn_fc hψ hC hF hinv β (nb x * g)).const_mul _
    _ = ∑ x ∈ C.s, C.co x * fc ψ lam 𝓖 nb F β (nb x * g) :=
        Finset.sum_congr rfl fun x _ => integral_const_mul _ _
    _ = ∑ x ∈ C.s, C.co x * (pch ψ x.1 (rat β.1) * fc ψ lam 𝓖 nb F β g) :=
        Finset.sum_congr rfl fun x _ => by rw [fc_nb_mul hψ hC hinv]
    _ = cutF ψ C (rat β.1) * fc ψ lam 𝓖 nb F β g := by
        rw [cutF, Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by ring

end PositivityTheory.Rg.Rsw.L.LCutLow

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

namespace PositivityTheory.Rg.Rsw.L.LCutLow

open GlobalTheory.CompanionTheory.PcFc (chn)

variable {D : D7} {n : ℕ}

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (t : AF D.host.F) : conj (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 t)]

theorem cutR_left {nb : hermA D n → G D n} {v : Pl D} (C : Cut D n v) {F : G D n → ℂ} (hinv : LeftInv (GF D n) F) :
    LeftInv (GF D n) (cutR nb C F) := fun γ hγ g => by
  unfold cutR
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_assoc, hinv γ hγ]

theorem cutR_cont {nb : hermA D n → G D n} {v : Pl D} (C : Cut D n v) {F : G D n → ℂ} (hF : Continuous F) :
    Continuous (cutR nb C F) := by
  unfold cutR
  exact continuous_finsetSum _ fun x _ => continuous_const.mul (hF.comp (continuous_id.mul continuous_const))

theorem cutR_lev {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) {F : G D n → ℂ}
    (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g) {k : G D n} (hk : k ∈ lev nb C.s)
    (hkv : k ∈ atPts D.sp.cm.sig (Jst D n) {v}) (g : G D n) : cutR nb C F (g * k) = cutR nb C F g := by
  unfold cutR
  refine Finset.sum_congr rfl fun x hx => ?_
  have e : g * k * nb x = g * nb x * ((nb x)⁻¹ * k * nb x) := by group
  rw [e, hK _ (conj_mem_KAt hnb C hk hkv hx)]

theorem fc_cutR_low {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hF : Continuous F) (hinv : LeftInv (GF D n) F) {v : Pl D} (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g)
    (C : Cut D n v) {r : ℕ} (hkill : C.Kills ψ r) (β : HermE D n) (hβ : β.1.rank < r) {g : G D n}
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) : fc ψ lam 𝓖 nb (cutR nb C F) β g = 0 := by
  rw [fc_cutR hψ hC hF hinv C β hg]
  by_cases h : ∀ x : hermA D n, IntAt v x → pch ψ x.1 (rat β.1) = 1
  · rw [hkill β hβ h, zero_mul]
  · push Not at h
    obtain ⟨x, hx, hne⟩ := h
    have e := fc_fix hψ hC hinv hK β hx hg
    have h0 : (1 - pch ψ x.1 (rat β.1)) * fc ψ lam 𝓖 nb F β g = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
    rw [(mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 (Ne.symm hne)), mul_zero]

theorem vanish_at {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (hFP : FourierPt) {nb : hermA D n → G D n}
    (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) {r : ℕ} (hkill : C.Kills ψ r) {F : G D n → ℂ} (hF : Continuous F)
    (hinv : LeftInv (GF D n) F) (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g) (hR : RankLT ψ F r) {g : G D n}
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) : cutR nb C F g = 0 := by
  obtain ⟨lam, 𝓖, hcov⟩ := GlobalTheory.CompanionTheory.HermVol.exists_isCovolOneH D n
  have hC : CoefData (D := D) (n := n) nb lam 𝓖 := ⟨hnb, hcov⟩
  have hco : ∀ β : HermE D n, ∫ x in 𝓖, cutR nb C F (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam = 0 := by
    intro β
    have e : ∫ x in 𝓖, cutR nb C F (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam = fc ψ lam 𝓖 nb (cutR nb C F) β g := by
      rw [fc_eq]
      refine integral_congr_ae (.of_forall fun b => ?_)
      show _ * conj (pch ψ b.1 (rat β.1)) = _ * chn ψ β b
      rw [pch_rat, conj_psi hψ, chn_eq]
    rw [e]
    by_cases hβ : β.1.rank < r
    · exact fc_cutR_low hψ hC hF hinv hK C hkill β hβ hg
    · rw [fc_cutR hψ hC hF hinv C β hg, hR nb lam 𝓖 hC β (not_lt.1 hβ) g, mul_zero]
  have key := hFP D n ψ hψ lam 𝓖 hcov (fun b => cutR nb C F (nb b * g)) (cont_nb (cutR_cont C hF) hnb g)
    (fun γ hγ b => per_nb (cutR_left C hinv) hnb g γ hγ b) hco
  have h0 := congrFun key 0
  simp only [GlobalTheory.CompanionTheory.FourierN.nb_zero hnb, one_mul, Pi.zero_apply] at h0
  exact h0

end PositivityTheory.Rg.Rsw.L.LCutLow

namespace PositivityTheory.Rg.Rsw.L

open LCutLow in
theorem cutLow : FourierPt → WeakApproximationFinitePlace → CutLow := by
  intro hFP hWA D n r ψ hψ nb hnb v C hkill F hF hinv hK
  have hlev : ∀ k ∈ lev nb C.s, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ∀ g, cutR nb C F (g * k) = cutR nb C F g :=
    fun k hk hkv g => cutR_lev hnb C hK hk hkv g
  refine ⟨fun hR => ?_, ⟨lev nb C.s, isOpen_lev nb C.s, hlev⟩, fun lam 𝓖 hC β g hg =>
    ⟨fc_cutR hψ hC hF hinv C β hg, fun hβ => fc_cutR_low hψ hC hF hinv hK C hkill β hβ hg⟩⟩
  funext g
  obtain ⟨γ, hγ, g', hg', k, hk, hkv, rfl⟩ := hWA D n v (lev nb C.s) (isOpen_lev nb C.s) g
  show cutR nb C F (γ * g' * k) = 0
  rw [hlev k hk hkv, cutR_left C hinv γ hγ g']
  exact vanish_at hψ hFP hnb C hkill hF hinv hK hR hg'

end PositivityTheory.Rg.Rsw.L

end
