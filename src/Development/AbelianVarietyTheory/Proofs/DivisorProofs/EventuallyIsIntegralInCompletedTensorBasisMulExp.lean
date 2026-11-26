module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCentralizerComm
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralInCompletedTensorBasisMulExp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralInCompletedTensorBasisMulExp
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

theorem basV_repr_mul (G : HTGroup p) (v : AwayP p) (a b : Qv v ⊗[ℚ] G.C) (k : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (a * b) k = ∑ i, ∑ j, (basV G v).repr a i * (basV G v).repr b j *
      algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr
        (Module.finBasis ℚ G.C i * Module.finBasis ℚ G.C j) k) := by
  conv_lhs => rw [← (basV G v).sum_repr a, ← (basV G v).sum_repr b]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul, map_sum, map_smul, Finset.sum_apply',
    Finsupp.smul_apply, smul_eq_mul, basV, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.basis_repr_tmul,
    Finsupp.mapRange_apply]
  rw [Finset.sum_comm]


omit [Fact p.Prime] in
theorem eventually_rat_mem_integers (q : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) q ∈ v.1.adicCompletionIntegers ℚ := by
  have h : ∀ᶠ w in (Filter.cofinite : Filter (HeightOneSpectrum ℤ)),
      algebraMap ℚ (w.adicCompletion ℚ) q ∈ w.adicCompletionIntegers ℚ :=
    (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2
  exact Subtype.val_injective.tendsto_cofinite.eventually h

theorem isIntV_mul_eventually (G : HTGroup p) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a b : Qv v ⊗[ℚ] G.C,
      IsIntV G v a → IsIntV G v b → IsIntV G v (a * b) := by
  have h : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ i j k : Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr
        (Module.finBasis ℚ G.C i * Module.finBasis ℚ G.C j) k) ∈ v.1.adicCompletionIntegers ℚ := by
    simp only [Filter.eventually_all]
    intro i j k
    exact eventually_rat_mem_integers _
  filter_upwards [h] with v hv a b ha hb k
  rw [basV_repr_mul]
  exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
    Subring.mul_mem _ (Subring.mul_mem _ (ha i) (hb j)) (hv i j k)

theorem isIntV_mul_eventually' : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a b : Qv v ⊗[ℚ] G.C,
      IsIntV G v a → IsIntV G v b → IsIntV G v (a * b) :=
  fun _ _ G => isIntV_mul_eventually G

end GlobalTheory.OrbFinAf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralInCompletedTensorBasisMulExpStatement
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_isIntegralInCompletedTensorBasis_mul_explicit : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a b : Qv v ⊗[ℚ] G.C, IsIntV G v a → IsIntV G v b → IsIntV G v (a * b) := by
  first | (exact @GlobalTheory.OrbFinAf.isIntV_mul_eventually') | (exact GlobalTheory.OrbFinAf.isIntV_mul_eventually') | (intros; apply GlobalTheory.OrbFinAf.isIntV_mul_eventually' <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapAllComparison
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.OneMapAllCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Level

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory CategoryTheory.Hom.group in
theorem levR_congr (c : Coeff l) (hA : l.A = 1) {p q : (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}
    (h : ∀ a, p.1 a - q.1 a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) : levR p y y' ↔ levR q y y' := by
  have e : ∀ a, Xo.univ.eta (p.1 a) = Xo.univ.eta (q.1 a) := fun a => by
    rw [← sub_add_cancel (p.1 a) (q.1 a), Xo.univ.eta_add, Xo.univ.eta_ker _ (h a), one_mul]
  have e1 : ∀ a, Xo.univ.etaA a = 1 := fun a => by
    have := Xo.univ.etaA_ker a
    rwa [hA, one_smul] at this
  unfold levR IsLevMove
  simp only [e, e1]

variable {G : Type} [Group G] {lev lev' : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}

theorem rel_congr (c : Coeff l) (hA : l.A = 1)
    (h : ∀ g a, (lev g).1 a - (lev' g).1 a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) :
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev g y y') =
      fun {S : Type} [CommRing S] [Algebra c.F S] (g : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev' g y y' := by
  funext S _ _ g y y'
  exact propext (levR_congr c hA (h g) y y')

theorem actLev_congr (c : Coeff l) (hA : l.A = 1)
    (h : ∀ g a, (lev g).1 a - (lev' g).1 a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) :
    actLev (Xo := Xo) c lev = actLev c lev' := by
  funext g
  unfold actLev
  rw [rel_congr c hA h]

theorem second_level_eq_one {c : Coeff l} {n : ℕ} {Tup : Type} {dδ : Tup → DeltaDat Xo c n} (h : CovPin Xo c dδ) (t : Tup) :
    l.A = 1 := by
  have h1 := (h t).1.1.2.2
  rw [(h t).2.1] at h1
  exact Nat.dvd_one.1 h1

end Level

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def TypeCoprime : Prop :=
  ∀ PP ∈ R.Pg, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal






def LevUnique (i : Fin D.R.m) : Prop :=
  ∀ lev lev' : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La,
    LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev → LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev' →
      ∀ g a, lev g a - lev' g a ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw ((i : ℕ) + 1)).La)

variable (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ)

variable {T R κ v₀ O ph}

variable (T R κ v₀ O ph)

end GlobalTheory.OneMapAllCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompactUnitaryAdelicImageIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompactUnitaryAdelicImageIntegral
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem eventually_int_of_isCompact {p : ℕ} (K : Set (AfP p)) (hK : IsCompact K) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a ∈ K, AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ := by
  obtain ⟨s, hs⟩ := hK.elim_directed_cover
    (fun s : Finset (AwayP p) => {z : AfP p | ∀ v ∉ s, AfP.eval v z ∈ v.1.adicCompletionIntegers ℚ})
    (fun s => RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _) (p := fun v => v ∉ s))
    (fun y _ => by
      have h : {v : AwayP p | ¬ AfP.eval v y ∈ v.1.adicCompletionIntegers ℚ}.Finite := y.2
      refine Set.mem_iUnion.2 ⟨h.toFinset, fun v hv => ?_⟩
      by_contra hc
      exact hv ((Set.Finite.mem_toFinset _).2 hc))
    (fun s t => ⟨s ∪ t, fun y hy v hv => hy v fun h => hv (Finset.mem_union_left _ h),
      fun y hy v hv => hy v fun h => hv (Finset.mem_union_right _ h)⟩)
  rw [Filter.eventually_cofinite]
  refine (s.finite_toSet).subset fun v hv => ?_
  by_contra hvs
  exact hv fun a ha => hs ha v hvs

theorem repr_map_eval {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (y : AfP p ⊗[ℚ] G.C)
    (i : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C) y) i =
      AfP.eval v ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr y i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r c =>
    simp only [basV, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem cptInt : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω →
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), piV G v '' Ω ⊆ IntV G v := by
  intro p _ G Ω hΩ
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  set bA := Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C) with hbA
  have hrep : ∀ i, Continuous (fun y : AfP p ⊗[ℚ] G.C => bA.repr y i) := fun i => by
    have := IsModuleTopology.continuous_of_linearMap (R := AfP p) (bA.coord i)
    exact this
  have hg1 : Continuous (fun g : G.GAf => (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
  have hg2 : Continuous (fun g : G.GAf => ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) :=
    Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val)
  have hg3 : Continuous (fun g : G.GAf => (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p)) :=
    Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
  have hg4 : Continuous (fun g : G.GAf => ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p)) :=
    Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)
  have h1 := Filter.eventually_all.2 fun i => eventually_int_of_isCompact _ (hΩ.image ((hrep i).comp hg1))
  have h2 := Filter.eventually_all.2 fun i => eventually_int_of_isCompact _ (hΩ.image ((hrep i).comp hg2))
  have h3 := eventually_int_of_isCompact _ (hΩ.image hg3)
  have h4 := eventually_int_of_isCompact _ (hΩ.image hg4)
  filter_upwards [h1, h2, h3, h4] with v hv1 hv2 hv3 hv4
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
  · have e : ((((piV G v g : Gv G v) : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)
          (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := rfl
    rw [e, repr_map_eval]
    exact hv1 i _ ⟨g, hg, rfl⟩
  · have e : (((((piV G v g : Gv G v) : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)
          ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := rfl
    rw [e, repr_map_eval]
    exact hv2 i _ ⟨g, hg, rfl⟩
  · exact hv3 _ ⟨g, hg, rfl⟩
  · exact hv4 _ ⟨g, hg, rfl⟩

end GlobalTheory.OrbFinAf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompactUnitaryAdelicImageIntegralStatement
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_compact_unitaryAdelic_image_integral : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω → ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), piV G v '' Ω ⊆ IntV G v := by
  first | (exact @GlobalTheory.OrbFinAf.cptInt) | (exact GlobalTheory.OrbFinAf.cptInt) | (intros; apply GlobalTheory.OrbFinAf.cptInt  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueNormSqOfSimilitudeHermitianSignature
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueNormSqOfSimilitudeHermitianSignature
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.EigenvalueNormSignature

theorem form_mulVec {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    star (M *ᵥ x) ⬝ᵥ A *ᵥ (M *ᵥ y) = star x ⬝ᵥ (Mᴴ * A * M) *ᵥ y := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem det_ne_zero_of_sig {n : ℕ} {h : Matrix (Fin n) (Fin n) ℂ} (hh : h.IsHermitian)
    (hs : sigPosH hh + sigNegH hh = n) : h.det ≠ 0 := by
  intro hd
  rw [hh.det_eq_prod_eigenvalues] at hd
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hd
  have hi0 : hh.eigenvalues i = 0 := by simpa using hi
  unfold sigPosH sigNegH at hs
  have hdis : Disjoint (fun j : Fin n => 0 < hh.eigenvalues j) (fun j => hh.eigenvalues j < 0) := by
    rw [Pi.disjoint_iff]; intro j
    simp only [Prop.disjoint_iff]
    rintro ⟨h1, h2⟩; linarith
  rw [← Fintype.card_subtype_or_disjoint _ _ hdis] at hs
  have hlt : Fintype.card {j : Fin n // 0 < hh.eigenvalues j ∨ hh.eigenvalues j < 0} < Fintype.card (Fin n) :=
    Fintype.card_subtype_lt (p := fun j => 0 < hh.eigenvalues j ∨ hh.eigenvalues j < 0) (x := i)
      (by rw [hi0]; simp)
  rw [Fintype.card_fin] at hlt
  omega

end GlobalTheory.EigenvalueNormSignature

namespace GlobalTheory


open GlobalTheory.EigenvalueNormSignature in
theorem eig_norm_sq_of_similitude : ∀ (n : ℕ) (h Q Γ : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (Z : GL (Fin n) ℂ) (c : ℝ),
    sigPosH hh ≤ 1 → sigPosH hh + sigNegH hh = n → Q = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * Z → c ≠ 0 →
    Γᴴ * Q * Γ = (c : ℂ) • Q →
    (sigPosH hh = 0 ∨ ∃ (μ : ℂ) (x₀ : Fin n → ℂ), Γ *ᵥ x₀ = μ • x₀ ∧ 0 < (star x₀ ⬝ᵥ (Q *ᵥ x₀)).re) →
    ∀ (w : ℂ) (x : Fin n → ℂ), x ≠ 0 → Γ *ᵥ x = w • x → ‖w‖ ^ 2 = c := by
  intro n h Q Γ hh Z c hle hs hQ hc hΓ hcase w x hx hw
  have hdet := det_ne_zero_of_sig hh hs
  set Zm : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ) with hZm
  have hZinj : ∀ v : Fin n → ℂ, v ≠ 0 → Zm *ᵥ v ≠ 0 := by
    intro v hv h0
    apply hv
    have : ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ (Zm *ᵥ v) = v := by
      rw [mulVec_mulVec, hZm, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, one_mulVec]
    rw [← this, h0, mulVec_zero]
  have hB : ∀ u v : Fin n → ℂ, star u ⬝ᵥ Q *ᵥ v = star (Zm *ᵥ u) ⬝ᵥ h *ᵥ (Zm *ᵥ v) := by
    intro u v; rw [form_mulVec, hQ]

  have hsim : ∀ (a b : ℂ) (u v : Fin n → ℂ), Γ *ᵥ u = a • u → Γ *ᵥ v = b • v →
      (star a * b - c) * (star u ⬝ᵥ Q *ᵥ v) = 0 := by
    intro a b u v hu hv
    have e := form_mulVec Γ Q u v
    rw [hΓ, hu, hv] at e
    simp only [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_mulVec] at e
    rw [RCLike.star_def] at e ⊢
    linear_combination e
  have hnorm : ∀ a : ℂ, star a * a = (c : ℂ) → ‖a‖ ^ 2 = c := by
    intro a ha
    have : ((‖a‖ ^ 2 : ℝ) : ℂ) = c := by
      rw [← ha, RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast this
  by_cases hq : star x ⬝ᵥ Q *ᵥ x = 0
  · rcases hcase with h0 | ⟨μ, x₀, hμ, hpos⟩
    · have := herm_negDef_of_sigPosH_eq_zero h hh hdet h0 (Zm *ᵥ x) (hZinj x hx)
      rw [← hB, hq] at this; simp at this
    · have h1 : sigPosH hh = 1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
        · have hx₀ : x₀ ≠ 0 := by rintro rfl; simp at hpos
          have := herm_negDef_of_sigPosH_eq_zero h hh hdet h0 (Zm *ᵥ x₀) (hZinj x₀ hx₀)
          rw [← hB] at this; linarith
        · exact h1
      have hμμ := hsim μ μ x₀ x₀ hμ hμ
      have hq0 : star x₀ ⬝ᵥ Q *ᵥ x₀ ≠ 0 := fun e => by rw [e] at hpos; simp at hpos
      have hμc : star μ * μ = (c : ℂ) := sub_eq_zero.mp ((mul_eq_zero.mp hμμ).resolve_right hq0)
      by_cases hb : star x₀ ⬝ᵥ Q *ᵥ x = 0
      · have := re_form_neg_of_orth_of_sigPosH_eq_one h hh hdet h1 (Zm *ᵥ x₀) (Zm *ᵥ x)
          (by rw [← hB]; exact hpos) (by rw [← hB]; exact hb) (hZinj x hx)
        rw [← hB, hq] at this; simp at this
      · have hμw := sub_eq_zero.mp ((mul_eq_zero.mp (hsim μ w x₀ x hμ hw)).resolve_right hb)
        have hμ0 : star μ ≠ 0 := by
          intro e; rw [e, zero_mul] at hμc; exact hc (by exact_mod_cast hμc.symm)
        have hwμ : w = μ := mul_left_cancel₀ hμ0 (hμw.trans hμc.symm)
        rw [hwμ]; exact hnorm μ hμc
  · exact hnorm w (sub_eq_zero.mp ((mul_eq_zero.mp (hsim w w x x hw hw)).resolve_right hq))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueNormSqOfSimilitudeHermitianSignatureStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvalue_normSq_of_similitude_hermitian_signature : ∀ (n : ℕ) (h Q Γ : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (Z : GL (Fin n) ℂ) (c : ℝ),
    sigPosH hh ≤ 1 → sigPosH hh + sigNegH hh = n → Q = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * Z → c ≠ 0 →
    Γᴴ * Q * Γ = (c : ℂ) • Q →
    (sigPosH hh = 0 ∨ ∃ (μ : ℂ) (x₀ : Fin n → ℂ), Γ *ᵥ x₀ = μ • x₀ ∧ 0 < (star x₀ ⬝ᵥ (Q *ᵥ x₀)).re) →
    ∀ (w : ℂ) (x : Fin n → ℂ), x ≠ 0 → Γ *ᵥ x = w • x → ‖w‖ ^ 2 = c := by
  first | (exact @GlobalTheory.eig_norm_sq_of_similitude) | (exact GlobalTheory.eig_norm_sq_of_similitude) | (intros; apply GlobalTheory.eig_norm_sq_of_similitude <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedSimilitudePairMinpolyRootsNormSqEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedSimilitudePairMinpolyRootsNormSqEq
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.MarkEll

theorem star_mulVec_dot {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) :
    star (M *ᵥ a) ⬝ᵥ (A *ᵥ (M *ᵥ b)) = star a ⬝ᵥ ((Mᴴ * A * M) *ᵥ b) := by
  rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_vecMul, Matrix.mul_assoc]

theorem normSq_eq_of_form {n : ℕ} (Γ A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hΓ : Γᴴ * A * Γ = (c : ℂ) • A)
    (x : Fin n → ℂ) (w : ℂ) (hx : Γ *ᵥ x = w • x) (h0 : star x ⬝ᵥ (A *ᵥ x) ≠ 0) : ‖w‖ ^ 2 = c := by
  have h := star_mulVec_dot Γ A x x
  rw [hΓ, hx] at h
  simp only [Matrix.smul_mulVec, mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h
  rw [← mul_assoc] at h
  have h2 : w * star w = (c : ℂ) := mul_right_cancel₀ h0 h
  have h3 : ((‖w‖ ^ 2 : ℝ) : ℂ) = (c : ℂ) := by
    rw [← h2, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact_mod_cast h3

theorem natDegree_minpoly_le_tmul {F A : Type} [Field F] [Ring A] [Algebra F A] (K : Type)
    [Field K] [Algebra F K] (g : A) (hK : IsIntegral K ((1 : K) ⊗ₜ[F] g)) :
    (minpoly F g).natDegree ≤ (minpoly K ((1 : K) ⊗ₜ[F] g)).natDegree := by
  set x : K ⊗[F] A := (1 : K) ⊗ₜ[F] g with hx
  have hli : LinearIndependent K (fun j : Fin (minpoly F g).natDegree => x ^ (j : ℕ)) := by
    have h := Module.Flat.linearIndependent_one_tmul (S := K) (linearIndependent_pow (K := F) g)
    convert h using 1
    funext j
    simp [hx, Algebra.TensorProduct.tmul_pow]
  by_contra hlt
  push_neg at hlt
  have hsum := Polynomial.aeval_eq_sum_range' hlt x
  rw [minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly K x).coeff i • x ^ i)] at hsum
  have hc := Fintype.linearIndependent_iff.mp hli (fun i => (minpoly K x).coeff i) hsum.symm
  apply minpoly.ne_zero hK
  ext i
  rw [Polynomial.coeff_zero]
  by_cases hi : i < (minpoly F g).natDegree
  · exact hc ⟨i, hi⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem eigA : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (g : G.C) (v : InfinitePlace G.F) (z : ℂ),
    (minpoly G.F g).natDegree = G.n → (minpoly G.F g).eval₂ v.embedding z = 0 →
    ∃ x : Fin G.n → ℂ, x ≠ 0 ∧ G.psi v g *ᵥ x = z • x := by
  intro p _ G g v z hdeg hz
  letI alg : Algebra G.F ℂ := v.embedding.toAlgebra
  have halg : ∀ a : G.F, algebraMap G.F ℂ a = v.embedding a := fun a => rfl
  let ψF : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ :=
    { G.psi v with
      commutes' := fun a => by
        change G.psi v (algebraMap G.F G.C a) = _
        rw [G.psi_F]
        ext i j
        simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply, halg] }
  let Θ : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψF (fun a _ => Algebra.commute_algebraMap_left a _)
  have hinj : Function.Injective Θ :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain Θ.toRingHom).resolve_right
      (by haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩; exact not_subsingleton _)
  set x : ℂ ⊗[G.F] G.C := (1 : ℂ) ⊗ₜ[G.F] g with hx
  have hxi : IsIntegral ℂ x := IsIntegral.of_finite ℂ x
  have hge := natDegree_minpoly_le_tmul ℂ g hxi
  have hΘx : Θ x = G.psi v g := by
    rw [hx]
    first
      | (erw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl)
      | (show (Algebra.ofId ℂ (Matrix (Fin G.n) (Fin G.n) ℂ)) 1 * ψF g = G.psi v g
         rw [map_one, one_mul]; rfl)
      | simp [Θ, ψF]
  have hmin : minpoly ℂ (G.psi v g) = minpoly ℂ x := by rw [← hΘx]; exact minpoly.algHom_eq Θ hinj x
  have hgi : IsIntegral G.F g := IsIntegral.of_finite G.F g
  have hdvd : minpoly ℂ (G.psi v g) ∣ (minpoly G.F g).map (algebraMap G.F ℂ) := by
    apply minpoly.dvd
    rw [Polynomial.aeval_map_algebraMap]
    change Polynomial.aeval (ψF g) (minpoly G.F g) = 0
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hmon : ((minpoly G.F g).map (algebraMap G.F ℂ)).Monic := (minpoly.monic hgi).map _
  have heq : (minpoly G.F g).map (algebraMap G.F ℂ) = minpoly ℂ (G.psi v g) := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic ?_) hmon hdvd ?_
    · exact IsIntegral.of_finite ℂ _
    · rw [Polynomial.natDegree_map, hmin]; exact hge
  have hroot : (minpoly ℂ (Matrix.toLin' (G.psi v g))).IsRoot z := by
    rw [Matrix.minpoly_toLin', ← heq, Polynomial.IsRoot, Polynomial.eval_map]
    exact hz
  obtain ⟨y, hy⟩ := (Module.End.hasEigenvalue_iff_isRoot.mpr hroot).exists_hasEigenvector
  refine ⟨y, hy.2, ?_⟩
  have := hy.apply_eq_smul
  rwa [Matrix.toLin'_apply] at this

theorem normSq_of_eigenvector {p : ℕ} [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ) (ha : G.a = 1)
    (hm : P.Mark μ) (v : InfinitePlace G.F) (x : Fin G.n → ℂ) (hx0 : x ≠ 0) (w : ℂ)
    (hx : G.psi v P.γ *ᵥ x = w • x) : ‖w‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  obtain ⟨-, -, hΓ⟩ := GlobalTheory.LKMid.pair_form_laws p G P v
  obtain ⟨Z, hZ⟩ := GlobalTheory.LKMid.Pair.gram_psi_inv_congr p G P v
  set A := G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) with hAdef
  set Γ := G.psi v P.γ with hΓdef
  have hΓ' : Γᴴ * A * Γ = ((((P.c : ℚ) : ℝ)) : ℂ) • A := by rw [hΓ]; push_cast; rfl
  have cong : ∀ a b : Fin G.n → ℂ, star a ⬝ᵥ (A *ᵥ b) =
      star ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a) ⬝ᵥ (G.gram v *ᵥ ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ b)) := by
    intro a b; rw [star_mulVec_dot, ← hZ]
  have Zne : ∀ a : Fin G.n → ℂ, a ≠ 0 → (Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a ≠ 0 := by
    intro a ha h
    apply ha
    have := congrArg (fun y => ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ y) h
    simpa only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, mulVec_zero] using this
  have hc0 : ((((P.c : ℚ) : ℝ)) : ℂ) ≠ 0 := by
    have : ((P.c : ℚ)) ≠ 0 := P.c.ne_zero
    exact_mod_cast this
  rcases G.sig v with ⟨h1, -⟩ | ⟨h0, -⟩
  · obtain ⟨v0, hv0, x0, hx0e, hpos⟩ := hm
    have hv : v = v0 := by
      have hcard : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} ≤ 1 := by
        have := ha; unfold HTGroup.a at this; omega
      haveI := Fintype.card_le_one_iff_subsingleton.mp hcard
      exact congrArg Subtype.val (Subsingleton.elim (⟨v, h1⟩ : {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1})
        ⟨v0, hv0⟩)
    subst hv
    have hS0 : star x0 ⬝ᵥ (A *ᵥ x0) ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
    have hμ : ‖μ‖ ^ 2 = ((P.c : ℚ) : ℝ) := normSq_eq_of_form Γ A _ hΓ' x0 μ hx0e hS0
    by_cases hw : w = μ
    · rw [hw]; exact hμ
    · have hS : star x0 ⬝ᵥ (A *ᵥ x) = 0 := by
        by_contra hne
        have h := star_mulVec_dot Γ A x0 x
        rw [hΓ', hx0e, hx] at h
        simp only [Matrix.smul_mulVec, mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct,
          smul_eq_mul] at h
        rw [← mul_assoc] at h
        have h2 := mul_right_cancel₀ hne h
        have hμ2 : μ * star μ = ((((P.c : ℚ) : ℝ)) : ℂ) := by
          rw [← hμ, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        have hμ0 : star μ ≠ 0 := by
          intro h0; apply hc0; rw [← hμ2, h0, mul_zero]
        apply hw
        apply mul_right_cancel₀ hμ0
        rw [hμ2]
        first | exact h2 | (rw [mul_comm]; exact h2)
      apply normSq_eq_of_form Γ A _ hΓ' x w hx
      intro h
      have hneg := GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one (G.gram v) (G.gram_herm v) (G.gram_det v) h1 _ _
        (by rw [← cong]; exact hpos) (by rw [← cong]; exact hS) (Zne x hx0)
      rw [← cong, h] at hneg; simp at hneg
  · apply normSq_eq_of_form Γ A _ hΓ' x w hx
    intro h
    have hneg := GlobalTheory.herm_negDef_of_sigPosH_eq_zero (G.gram v) (G.gram_herm v) (G.gram_det v) h0 _ (Zne x hx0)
    rw [← cong, h] at hneg; simp at hneg

theorem mark_ell : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ (φ : G.F →+* ℂ) (z : ℂ), P.pol.eval₂ φ z = 0 → ‖z‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  intro p _ G P μ ha hm φ z hz
  have hdeg : (minpoly G.F (P.γ : G.C)).natDegree = G.n := P.reg.1
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · obtain ⟨x, hx0, hx⟩ := eigA p G (P.γ : G.C) (InfinitePlace.mk φ) z hdeg (by rw [h]; exact hz)
    exact normSq_of_eigenvector G P μ ha hm _ x hx0 z hx
  · have hz' : (minpoly G.F (P.γ : G.C)).eval₂ (InfinitePlace.mk φ).embedding (star z) = 0 := by
      have e : (InfinitePlace.mk φ).embedding = (starRingEnd ℂ).comp φ := by
        rw [h]; ext x; simp [ComplexEmbedding.conjugate_coe_eq]
      have := Polynomial.hom_eval₂ P.pol φ (starRingEnd ℂ) z
      rw [hz, map_zero] at this
      rw [e]; exact this.symm
    obtain ⟨x, hx0, hx⟩ := eigA p G (P.γ : G.C) (InfinitePlace.mk φ) (star z) hdeg hz'
    have := normSq_of_eigenvector G P μ ha hm _ x hx0 (star z) hx
    rwa [norm_star] at this

end GlobalTheory.LKMid.MarkEll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedSimilitudePairMinpolyRootsNormSqEqStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.marked_similitude_pair_minpoly_roots_normSq_eq : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ → ∀ (φ : G.F →+* ℂ) (z : ℂ), P.pol.eval₂ φ z = 0 → ‖z‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  first | (exact @GlobalTheory.LKMid.MarkEll.mark_ell) | (exact GlobalTheory.LKMid.MarkEll.mark_ell) | (intros; apply GlobalTheory.LKMid.MarkEll.mark_ell  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixLineConjIff
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem fixLine_conj_iff {n : Type} [Fintype n] [DecidableEq n] (A B : GL n ℂ) (z : n → ℂ) :
    (∃ c : ℂ, (A : Matrix n n ℂ) *ᵥ z = c • z) ↔
      ∃ c : ℂ, ((B * A * B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ ((B : Matrix n n ℂ) *ᵥ z) =
        c • ((B : Matrix n n ℂ) *ᵥ z) := by
  have key : ((B * A * B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ ((B : Matrix n n ℂ) *ᵥ z) =
      (B : Matrix n n ℂ) *ᵥ ((A : Matrix n n ℂ) *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, ← Matrix.mulVec_mulVec]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [key, hc, Matrix.mulVec_smul]⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [key, ← Matrix.mulVec_smul] at hc
    have h := congrArg (fun w => ((B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ w) hc
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h
    rwa [inv_mul_cancel_left] at h

theorem fixL_conj_iff : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ)
    (y g : grp G β) (z : Fin G.n → ℂ),
    FixL G v β y z ↔ FixL G v β (g * y * g⁻¹) ((toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
  intro p _ G v β y g z
  unfold FixL
  rw [map_mul, map_mul, map_inv]
  exact fixLine_conj_iff _ _ z

end GlobalTheory.LKCx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassPullbackVeryAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassPullbackVeryAmple
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic

theorem eff_pull_of_veryAmpleBy : ∀ (R : Type) [CommRing R] {X Y : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (hH : H.IsLB), GlobalTheory.AbLaw.VeryAmpleBy f H s → ∀ (φ : Y ⟶ X), Nonempty Y → GlobalTheory.EffBound.Eff (GlobalTheory.CechPic.pull φ (GlobalTheory.CechPic.cls H hH)) := by
  intro R _ X Y f H m s hH hva φ hY
  obtain ⟨y⟩ := hY
  have hy : φ y ∈ ⨆ i, nonzeroLocus (s i) := by rw [hva.1]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  have hy' : y ∈ nonzeroLocus (GlobalTheory.secPull (s i) φ) := by
    rw [GlobalTheory.nonzeroLocus_secPull]; exact hi
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy'
  have hne : (GlobalTheory.secPull (s i) φ).f k ≠ 0 := by
    intro h0
    rw [h0, Scheme.basicOpen_zero] at hk
    exact hk
  rw [← cls_pull hH φ (pull_isLB hH φ)]
  exact eff_of_sec _ _ _ k hne

end GlobalTheory.EffBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassPullbackVeryAmpleStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEffectivePicClass_pullback_veryAmple : ∀ (R : Type) [CommRing R] {X Y : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (hH : H.IsLB), GlobalTheory.AbLaw.VeryAmpleBy f H s → ∀ (φ : Y ⟶ X), Nonempty Y → GlobalTheory.EffBound.Eff (GlobalTheory.CechPic.pull φ (GlobalTheory.CechPic.cls H hH)) := by
  first | exact @GlobalTheory.EffBound.eff_pull_of_veryAmpleBy | exact GlobalTheory.EffBound.eff_pull_of_veryAmpleBy | (intros; apply GlobalTheory.EffBound.eff_pull_of_veryAmpleBy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupActionRingHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupActionRingHom
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.OrbFinAfFixed

theorem rat_eventually_int (p : ℕ) (q : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) q ∈ v.1.adicCompletionIntegers ℚ := by
  have h : ∀ᶠ w in (Filter.cofinite : Filter (HeightOneSpectrum ℤ)),
      algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q w ∈ w.adicCompletionIntegers ℚ :=
    (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2
  have h2 : ∀ᶠ w in (Filter.cofinite : Filter (HeightOneSpectrum ℤ)),
      algebraMap ℚ (w.adicCompletion ℚ) q ∈ w.adicCompletionIntegers ℚ :=
    h.mono fun w hw => by rwa [FiniteAdeleRing.algebraMap_apply] at hw
  exact (Subtype.val_injective.tendsto_cofinite).eventually h2

theorem basV_repr_one_tmul (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (c : G.C) (i) :
    (basV G v).repr ((1 : Qv v) ⊗ₜ[ℚ] c) i = algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr c i) := by
  simp [basV, Algebra.TensorProduct.basis_repr_tmul]

theorem isIntV_one_tmul_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (c : G.C),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] c) := by
  intro p _ G c
  have h : ∀ i, ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr c i) ∈ v.1.adicCompletionIntegers ℚ :=
    fun i => rat_eventually_int p _
  refine (Filter.eventually_all.2 h).mono fun v hv i => ?_
  rw [basV_repr_one_tmul]
  exact hv i

end GlobalTheory.OrbFinAfFixed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupActionRingHomStatement
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_isIntV_one_tmul : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (c : G.C), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] c) := by
  first | (exact @GlobalTheory.OrbFinAfFixed.isIntV_one_tmul_eventually) | (exact GlobalTheory.OrbFinAfFixed.isIntV_one_tmul_eventually) | (intros; apply GlobalTheory.OrbFinAfFixed.isIntV_one_tmul_eventually  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationAlgebraMapEqOfInertPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationAlgebraMapEqOfInertPlace
open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory.InertValRestr

theorem liesOver_of_isInertAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) : w.asIdeal.LiesOver v.asIdeal := by
  refine ⟨?_⟩
  have hP : w.asIdeal.IsPrime := w.isPrime
  have hc : (w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).IsPrime := inferInstance
  refine v.isMaximal.eq_of_le hc.ne_top ?_
  show v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
  rw [← hin]
  exact Ideal.le_comap_map

theorem ramificationIdx'_eq_one_of_isInertAt {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) : v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
  have hP : w.asIdeal.IsPrime := w.isPrime
  apply Ideal.ramificationIdx'_spec
  · rw [hin, pow_one]
  · rw [hin]
    exact not_le_of_gt (Ideal.pow_succ_lt_pow w.ne_bot 1 |>.trans_eq (pow_one _))

theorem valuation_algebraMap_of_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ x : F, w.valuation E (algebraMap F E x) = v.valuation F x := by
  intro F E _ _ _ _ _ v w hin x
  have := liesOver_of_isInertAt v w hin
  rw [← HeightOneSpectrum.valuation_liesOver (K := F) E v w x,
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
    ramificationIdx'_eq_one_of_isInertAt v w hin, pow_one]

end GlobalTheory.InertValRestr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationAlgebraMapEqOfInertPlaceStatement
open NumberField IsDedekindDomain
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_algebraMap_eq_of_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ x : F, w.valuation E (algebraMap F E x) = v.valuation F x := by
  first | exact @GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt | exact GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt | (intros; apply GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularElementSeparableMinpoly
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx

theorem commute_units_conj {A : Type*} [Monoid A] (U : Aˣ) {a e : A} (h : Commute a e) :
    Commute ((U : A) * a * ↑U⁻¹) ((U : A) * e * ↑U⁻¹) := by
  unfold Commute SemiconjBy at *
  calc (U : A) * a * ↑U⁻¹ * ((U : A) * e * ↑U⁻¹) = U * (a * e) * ↑U⁻¹ := by
        simp only [mul_assoc, Units.inv_mul_cancel_left]
    _ = U * (e * a) * ↑U⁻¹ := by rw [h]
    _ = _ := by simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem comm_of_conj {A : Type*} [Monoid A] (U : Aˣ) (e : A)
    (h : ∀ a b : A, Commute a ((U : A) * e * ↑U⁻¹) → Commute b ((U : A) * e * ↑U⁻¹) → Commute a b)
    (a b : A) (ha : Commute a e) (hb : Commute b e) : Commute a b := by
  have h1 := h _ _ (commute_units_conj U ha) (commute_units_conj U hb)
  have h2 := commute_units_conj U⁻¹ h1
  have e1 : ∀ z : A, ((U⁻¹ : Aˣ) : A) * ((U : A) * z * ↑U⁻¹) * ↑(U⁻¹)⁻¹ = z := by
    intro z; simp [mul_assoc]
  rwa [e1, e1] at h2

variable {p : ℕ} [Fact p.Prime]

theorem ubc_val_eq (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t)
    (y : grp G β) (h : G.GAf) (w : AwayP p) :
    ∃ U : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
    ((ubcMap (AfP.eval w) (h⁻¹ * toAfF G β x t hx y * h)).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      (U : w.1.adicCompletion ℚ ⊗[ℚ] G.C) * ((1 : w.1.adicCompletion ℚ) ⊗ₜ (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) *
        ((U⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
  set φ : AfP p ⊗[ℚ] G.C →ₐ[ℚ] w.1.adicCompletion ℚ ⊗[ℚ] G.C :=
    Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) with hφ
  have hm : ((ubcMap (AfP.eval w) (toAfF G β x t hx y)).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      φ x * ((1 : w.1.adicCompletion ℚ) ⊗ₜ (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * φ ↑x⁻¹ := by
    show φ ((x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ↑x⁻¹) = _
    rw [map_mul, map_mul]
    congr 2
  refine ⟨((ubcMap (AfP.eval w) h).1.1)⁻¹ * Units.map φ.toMonoidHom x, ?_⟩
  rw [map_mul, map_mul, map_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, Units.val_mul, _root_.mul_inv_rev, inv_inv]
  rw [hm]
  simp only [Units.coe_map, MonoidHom.coe_coe, mul_assoc]
  rw [Units.coe_map_inv]
  rfl

end GlobalTheory.LKCx

namespace GlobalTheory.LKCx

end GlobalTheory.LKCx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjugatesAlgebraRelation
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.Div

theorem conj_of_twist : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (y₁ y₂ : grp G β) (y₀ c₁ c₂ w : G.Cˣ) (r : ℚ),
    (((y₁ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c₁ * y₀ * ((c₁⁻¹ : G.Cˣ) : G.C) →
    (((y₂ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c₂ * y₀ * ((c₂⁻¹ : G.Cˣ) : G.C) →
    (y₁ : G.Cˣ × ℚˣ).2 = (y₂ : G.Cˣ × ℚˣ).2 → Commute (w : G.C) y₀ → 0 < r →
    (((c₂⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₂⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C r * ((w : G.C) * (((c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₁⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * ((β : G.C) * sh G (w : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) →
    ∃ γ : grp G β, y₂ = γ * y₁ * γ⁻¹ := by
  intro p _ G β y₁ y₂ y₀ c₁ c₂ w r h1 h2 hs hw hr H
  have shm : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have shc : sh G ((c₂⁻¹ : G.Cˣ) : G.C) * sh G (c₂ : G.C) = 1 := by
    rw [← shm, Units.mul_inv]; simp [sh]
  have hR : algebraMap ℚ G.C r⁻¹ * algebraMap ℚ G.C r = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hr.ne', map_one]
  set ru : ℚˣ := Units.mk0 r hr.ne' with hru

  have HX : (w : G.C) * (((c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₁⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
      ((β : G.C) * sh G (w : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C r⁻¹ *
      (((c₂⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₂⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) := by
    rw [H, ← mul_assoc (algebraMap ℚ G.C r⁻¹), hR, one_mul]
  have mem : ((c₂ * w * c₁⁻¹, ru⁻¹) : G.Cˣ × ℚˣ) ∈ grp G β := by
    refine ⟨?_, ?_⟩
    · change ((c₂ * w * c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₂ * w * c₁⁻¹ : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((ru⁻¹ : ℚˣ) : ℚ) * β
      rw [Units.val_inv_eq_inv_val, hru, Units.val_mk0]
      simp only [Units.val_mul, shm]
      calc (c₂ : G.C) * w * ((c₁⁻¹ : G.Cˣ) : G.C) * β * (sh G ((c₁⁻¹ : G.Cˣ) : G.C) * (sh G (w : G.C) * sh G (c₂ : G.C)))
          = c₂ * ((w : G.C) * (((c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₁⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
            ((β : G.C) * sh G (w : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) * β * sh G (c₂ : G.C) := by
            simp only [mul_assoc, Units.inv_mul_cancel_left]
        _ = algebraMap ℚ G.C r⁻¹ * ((c₂ : G.C) * ((c₂⁻¹ : G.Cˣ) : G.C) * β *
              (sh G ((c₂⁻¹ : G.Cˣ) : G.C) * sh G (c₂ : G.C))) := by
            rw [HX, Algebra.left_comm]
            simp only [mul_assoc, Units.inv_mul_cancel_left]
        _ = _ := by rw [shc, Units.mul_inv, one_mul, mul_one]
    · change 0 < ((ru⁻¹ : ℚˣ) : ℚ)
      rw [Units.val_inv_eq_inv_val, hru, Units.val_mk0]; exact inv_pos.2 hr
  refine ⟨⟨_, mem⟩, ?_⟩
  have e1 : (y₁ : G.Cˣ × ℚˣ).1 = c₁ * y₀ * c₁⁻¹ := Units.ext (by rw [h1]; simp)
  have e2 : (y₂ : G.Cˣ × ℚˣ).1 = c₂ * y₀ * c₂⁻¹ := Units.ext (by rw [h2]; simp)
  have hwu : w * y₀ = y₀ * w := Units.ext (by simpa using hw.eq)
  have hwu' : ∀ x : G.Cˣ, w * (y₀ * x) = y₀ * (w * x) := fun x => by rw [← mul_assoc, hwu, mul_assoc]
  apply Subtype.ext
  apply Prod.ext
  · show (y₂ : G.Cˣ × ℚˣ).1 = (c₂ * w * c₁⁻¹) * (y₁ : G.Cˣ × ℚˣ).1 * (c₂ * w * c₁⁻¹)⁻¹
    rw [e1, e2]
    simp only [_root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, hwu', mul_inv_cancel_left]
  · show (y₂ : G.Cˣ × ℚˣ).2 = ru⁻¹ * (y₁ : G.Cˣ × ℚˣ).2 * ru⁻¹⁻¹
    rw [hs, mul_comm ru⁻¹, mul_assoc, mul_inv_cancel, mul_one]

end GlobalTheory.Div
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTuplePinsOrientationStandardFrameLevelMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTuplePinsOrientationStandardFrameLevelMap
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BasePins

theorem orient_std_lev : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) , R.toLevCh.Is A.μ0 → LawsJ T → ∀ i, OMPins T R κ v₀ O i → T.pb = R.C.P.pb ∧ VStd D i ∧ LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) (O i).lev := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hL hT i hO
  exact ⟨GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R hT.toLawsM hL (hO.2.tuple ()).half, hO.2.lift.std, hO.2.lift.lev⟩

end GlobalTheory.BasePins
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTuplePinsOrientationStandardFrameLevelMapStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseTuple_pins_orientation_standardFrame_levelMap : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) , R.toLevCh.Is A.μ0 → LawsJ T → ∀ i, OMPins T R κ v₀ O i → T.pb = R.C.P.pb ∧ VStd D i ∧ LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) (O i).lev := by
  first | exact @GlobalTheory.BasePins.orient_std_lev | exact GlobalTheory.BasePins.orient_std_lev | (intros; apply GlobalTheory.BasePins.orient_std_lev <;> assumption)
end
end
