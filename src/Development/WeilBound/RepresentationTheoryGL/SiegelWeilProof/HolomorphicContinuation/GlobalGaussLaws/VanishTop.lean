module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayFact
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SigTop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SummableOfAbsTheta
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawB
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ValZeroOfTens
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LamTop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TwoSided

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GIwasawa
namespace PositivityTheory.Rg.Sw.Glob

theorem gIwasawa : GIwasawa := GlobalTheory.StdUnn.Iwasawa.exists_mul

end PositivityTheory.Rg.Sw.Glob
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LinSecOf
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

theorem thetaInt_smul {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n))
    (ν : Measure (GA D V)) (Φ : schwartzA θ V.rank n) (a : ℂ) (g : G D n) :
    thetaInt ω ν (a • Φ) g = a * thetaInt ω ν Φ g := by
  have h : GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω (a • Φ) g) = fun q => a * GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ g) q := by
    funext q
    simp [GlobalTheory.AutomorphicL2Unitary.descend, theta, map_smul, tsum_mul_left]
  simp only [thetaInt, h, MeasureTheory.average, MeasureTheory.integral_const_mul]

theorem tens_fP_add {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ)
    (Ψ : Mx D m n → ℂ) (P Q : PX m n) :
    tens θ τ fr (fP c (P + Q)) Ψ = tens θ τ fr (fP c P) Ψ + tens θ τ fr (fP c Q) Ψ := by
  funext x
  simp only [tens, fP, evX, map_add (f := _), Pi.add_apply]
  ring

theorem tens_fP_smul {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ)
    (Ψ : Mx D m n → ℂ) (a : ℂ) (P : PX m n) :
    tens θ τ fr (fP c (a • P)) Ψ = a • tens θ τ fr (fP c P) Ψ := by
  funext x
  simp only [tens, fP, evX, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, Pi.smul_apply, smul_eq_mul]
  ring

theorem linSec_of : ThLin → LinSec := by
  intro hTL D n V ψ χ θ μ ω H l s ν τ ε fr ι c Ψ hΨ
  have hl0 : ∀ τ, l τ ≠ 0 := lNZ D ψ θ l c.hψ c.hθ c.hl
  have hm : ∀ P, tens θ τ fr (fP (cLoc l τ) P) Ψ ∈ schwartzA θ V.rank n ∧
      tens θ τ fr (fP (cLoc l τ) P) Ψ ∈ fockA θ V n l s :=
    fun P => tensMem D n V θ l s τ ε fr c.hθ hl0 c.hs c.hfr Ψ hΨ P
  have hphi : ∀ P, phiS θ τ fr (cLoc l τ) Ψ P = ⟨_, (hm P).1⟩ := fun P => dif_pos (hm P).1
  have hadd : ∀ P Q, phiS θ τ fr (cLoc l τ) Ψ (P + Q) = phiS θ τ fr (cLoc l τ) Ψ P + phiS θ τ fr (cLoc l τ) Ψ Q := by
    intro P Q
    rw [hphi, hphi, hphi]
    exact Subtype.ext (tens_fP_add θ τ fr _ Ψ P Q)
  have hsmul : ∀ (a : ℂ) P, phiS θ τ fr (cLoc l τ) Ψ (a • P) = a • phiS θ τ fr (cLoc l τ) Ψ P := by
    intro a P
    rw [hphi, hphi]
    exact Subtype.ext (tens_fP_smul θ τ fr _ Ψ a P)
  have hstd : ∀ P, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (phiS θ τ fr (cLoc l τ) Ψ P) := fun P =>
    ⟨c.hψ, c.hχ, c.hη, c.hθ, c.hμ, c.hω, c.hH, c.hl, c.hs, c.hν, by rw [hphi]; exact (hm P).2⟩
  refine ⟨{ toFun := fun P => secF ω τ fr (cLoc l τ) Ψ P
            map_add' := fun P Q => by
              funext g
              simp only [secF, hadd, map_add (f := _), Submodule.coe_add, Pi.add_apply]
            map_smul' := fun a P => by
              funext g
              simp only [secF, hsmul, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] },
          { toFun := fun P => thF ω ν τ fr (cLoc l τ) Ψ P
            map_add' := fun P Q => by
              funext g
              simp only [thF, Pi.add_apply]
              rw [hadd]
              exact hTL D n V ψ χ θ μ ω H l s ν _ _ (hstd P) (hstd Q) c.hr g
            map_smul' := fun a P => by
              funext g
              simp only [thF, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
              rw [hsmul]
              exact thetaInt_smul ω ν _ a g }, fun P => rfl, fun P => rfl⟩

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseTau
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseC
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseB
noncomputable section

open Matrix Topology

namespace PositivityTheory.Rg.Sw.Glob.DenseP

variable {n : ℕ}

theorem inG_nUh {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (nU b) := by
  simp only [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hb]
  simp

theorem inG_mL {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A.det) : InG (fromBlocks A 0 0 (A⁻¹)ᴴ) := by
  have h1 : Aᴴ * (A⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hA, Matrix.conjTranspose_one]
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hA
  simp only [InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero]
  simp [h1, h2]

def hpart (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A + Aᴴ)

theorem hpart_herm (A : Matrix (Fin n) (Fin n) ℂ) : (hpart A)ᴴ = hpart A := by
  simp only [hpart, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  rw [add_comm]
  congr 1
  simp

theorem hpart_of_herm {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : hpart b = b := by
  rw [hpart, hb, ← two_smul ℂ b, smul_smul]; norm_num

def nuE (A : Matrix (Fin n) (Fin n) ℂ) : GR n := mkGR (nU (hpart A)) (inG_nUh (hpart_herm A))

theorem continuous_hpart : Continuous (hpart (n := n)) := by
  have h : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A + Aᴴ :=
    (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)).add (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)).matrix_conjTranspose
  exact h.const_smul (1 / 2 : ℂ)

theorem nU_mul_neg (b : Matrix (Fin n) (Fin n) ℂ) : nU b * nU (-b) = 1 := by
  simp [nU, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]

theorem continuous_nU : Continuous (nU (n := n)) :=
  Continuous.matrix_fromBlocks continuous_const continuous_id continuous_const continuous_const

theorem continuous_nuE : Continuous (nuE (n := n)) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · show Continuous fun A => nU (hpart A)
    exact continuous_nU.comp continuous_hpart
  · show Continuous fun A : Matrix (Fin n) (Fin n) ℂ => (nU (hpart A))⁻¹
    have e : (fun A : Matrix (Fin n) (Fin n) ℂ => (nU (hpart A))⁻¹) = fun A => nU (-hpart A) := by
      funext A
      exact Matrix.inv_eq_right_inv (nU_mul_neg _)
    rw [e]
    exact continuous_nU.comp continuous_hpart.neg


open Classical in
def mlE (A : Matrix (Fin n) (Fin n) ℂ) : GR n :=
  if h : IsUnit A.det then mkGR (fromBlocks A 0 0 (A⁻¹)ᴴ) (inG_mL h) else 1

theorem mlE_of {A : Matrix (Fin n) (Fin n) ℂ} (h : IsUnit A.det) :
    mlE A = mkGR (fromBlocks A 0 0 (A⁻¹)ᴴ) (inG_mL h) := by
  unfold mlE; exact dif_pos h

theorem isOpen_unitDet : IsOpen {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} := by
  have : {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} = (fun A : Matrix (Fin n) (Fin n) ℂ => A.det) ⁻¹' {z | z ≠ 0} :=
    Set.ext fun A => isUnit_iff_ne_zero
  rw [this]
  exact isOpen_ne.preimage (Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)))

theorem continuousOn_inv_mat : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹) {A | IsUnit A.det} := by
  have e : (fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [e]
  have h1 : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ => (A.det)⁻¹) {A | IsUnit A.det} :=
    ContinuousOn.inv₀ (Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) ℂ))).continuousOn
      fun A hA => isUnit_iff_ne_zero.1 hA
  have h2 : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A.adjugate :=
    Continuous.matrix_adjugate (continuous_id (X := Matrix (Fin n) (Fin n) ℂ))
  exact h1.smul h2.continuousOn

theorem inv_mL {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A.det) :
    (fromBlocks A 0 0 (A⁻¹)ᴴ)⁻¹ = fromBlocks A⁻¹ 0 0 Aᴴ := by
  refine Matrix.inv_eq_right_inv ?_
  have h1 : (A⁻¹)ᴴ * Aᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hA, Matrix.conjTranspose_one]
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.mul_nonsing_inv _ hA, h1, ← Matrix.fromBlocks_one]

theorem continuousOn_mlE : ContinuousOn (mlE (n := n)) {A | IsUnit A.det} := by
  have hind : Topology.IsInducing (fun g : GR n => Units.embedProduct _ (g : GL (Fin n ⊕ Fin n) ℂ)) :=
    Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal
  rw [hind.continuousOn_iff]
  have hi := continuousOn_inv_mat (n := n)
  have hc : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ =>
      (fromBlocks A 0 0 (A⁻¹)ᴴ, MulOpposite.op (fromBlocks A⁻¹ 0 0 Aᴴ))) {A | IsUnit A.det} := by
    rw [continuousOn_iff_continuous_restrict]
    have hi' : Continuous fun A : {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} => A.1⁻¹ := hi.restrict
    refine Continuous.prodMk ?_ ?_
    · exact Continuous.matrix_fromBlocks continuous_subtype_val continuous_const continuous_const
        hi'.matrix_conjTranspose
    · exact MulOpposite.continuous_op.comp (Continuous.matrix_fromBlocks hi' continuous_const continuous_const
        continuous_subtype_val.matrix_conjTranspose)
  refine ContinuousOn.congr hc fun A hA => ?_
  simp only [Function.comp_apply, mlE_of hA]
  show ((fromBlocks A 0 0 (A⁻¹)ᴴ), MulOpposite.op (fromBlocks A 0 0 (A⁻¹)ᴴ)⁻¹) = _
  rw [inv_mL hA]

theorem nuE_mem_closure {K : Type} [Field K] (τ : K →+* ℂ) (hτ : DenseRange τ) (A : Matrix (Fin n) (Fin n) ℂ) :
    nuE A ∈ closure (Set.range fun e : Matrix (Fin n) (Fin n) K => nuE (e.map τ)) := by
  have hd : DenseRange (fun e : Matrix (Fin n) (Fin n) K => e.map τ) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => hτ
  have h1 : nuE A ∈ nuE '' closure (Set.range fun e : Matrix (Fin n) (Fin n) K => e.map τ) := by
    rw [hd.closure_range]; exact ⟨A, trivial, rfl⟩
  have h2 := image_closure_subset_closure_image continuous_nuE h1
  rwa [← Set.range_comp] at h2

theorem mlE_mem_closure {K : Type} [Field K] (τ : K →+* ℂ) (hτ : DenseRange τ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUnit A.det) :
    mlE A ∈ closure (mlE '' ({A | IsUnit A.det} ∩ Set.range fun e : Matrix (Fin n) (Fin n) K => e.map τ)) := by
  have hd : DenseRange (fun e : Matrix (Fin n) (Fin n) K => e.map τ) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => hτ
  have hc : ContinuousAt (mlE (n := n)) A := (continuousOn_mlE (n := n)).continuousAt (isOpen_unitDet.mem_nhds hA)
  rw [mem_closure_iff_nhds]
  intro t ht
  have h1 : mlE ⁻¹' t ∩ {A | IsUnit A.det} ∈ 𝓝 A := Filter.inter_mem (hc ht) (isOpen_unitDet.mem_nhds hA)
  obtain ⟨U, hU, hUo, hAU⟩ := mem_nhds_iff.1 h1
  obtain ⟨e, he⟩ := hd.exists_mem_open hUo ⟨A, hAU⟩
  exact ⟨mlE (e.map τ), (hU he).1, e.map τ, ⟨(hU he).2, e, rfl⟩, rfl⟩

end PositivityTheory.Rg.Sw.Glob.DenseP
end
end

noncomputable section

open Matrix Topology
open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DenseP

open Formalism.IndefR.Eqv (psiT psiT_inclR)

variable {D : D7} {n : ℕ}

theorem denseRange_of_not_isReal' {K : Type} [Field K] (σ : K →+* ℂ)
    (h : ¬ NumberField.ComplexEmbedding.IsReal σ) : DenseRange σ := by
  have hc : IsClosed (σ.fieldRange.topologicalClosure : Set ℂ) :=
    Subfield.isClosed_topologicalClosure _
  rcases Complex.subfield_eq_of_closed hc with h1 | h1
  · exfalso
    apply h
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have hx : σ x ∈ σ.fieldRange.topologicalClosure := Subfield.le_topologicalClosure _ ⟨x, rfl⟩
    rw [h1] at hx
    obtain ⟨r, hr⟩ := hx
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← hr]
    exact Complex.conj_ofReal r
  · have : closure (Set.range σ) = Set.univ := by
      have := congrArg (fun S : Subfield ℂ => (S : Set ℂ)) h1
      exact this
    exact dense_iff_closure_eq.2 this

theorem tauE_not_real (τ : D.what₂.Tau) : ¬ NumberField.ComplexEmbedding.IsReal (tauE D τ) := by
  intro h
  rw [NumberField.ComplexEmbedding.isReal_iff] at h
  have h1 : starRingEnd ℂ (tauE D τ D.host.xi0) = tauE D τ D.host.xi0 := by
    have := congrArg (fun f : D.host.E →+* ℂ => f D.host.xi0) h
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this
  have h2 : tauE D τ (star D.host.xi0) = starRingEnd ℂ (tauE D τ D.host.xi0) := Formalism.IndefR.Eqv.tauE_star D τ _
  rw [Formalism.IndefR.Datum.Brg.star_purely_imaginary_eq_neg, map_neg, h1] at h2
  have h3 : tauE D τ D.host.xi0 = 0 := by
    have : (2 : ℂ) * tauE D τ D.host.xi0 = 0 := by linear_combination -h2
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  exact Formalism.IndefR.Fin.embedding_xi_zero_ne_zero ((map_eq_zero_iff _ (tauE D τ).injective).1 h3)

theorem denseRange_tauE (τ : D.what₂.Tau) : DenseRange (tauE D τ) := denseRange_of_not_isReal' _ (tauE_not_real τ)

theorem sig_apply (x : D.host.E) : D.sp.cm.sig x = star x := rfl

theorem cT_map_tauE (τ : D.what₂.Tau) {k : ℕ} (u : Matrix (Fin k) (Fin k) D.host.E) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u).map (tauE D τ) = (u.map (tauE D τ))ᴴ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply, sig_apply, Formalism.IndefR.Eqv.tauE_star]

theorem block_matrix_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  rw [blk4, blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map]

theorem map0 (τ : D.what₂.Tau) : (0 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = 0 :=
  map_zero (RingHom.mapMatrix (tauE D τ))

theorem map1 (τ : D.what₂.Tau) : (1 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = 1 :=
  map_one (RingHom.mapMatrix (tauE D τ))

theorem mapn1 (τ : D.what₂.Tau) : (-1 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = -1 := by
  show RingHom.mapMatrix (tauE D τ) (-1) = -1
  rw [map_neg, map_one]

theorem map_smul_E (τ : D.what₂.Tau) {k : ℕ} (c : D.host.E) (X : Matrix (Fin k) (Fin k) D.host.E) :
    (c • X).map (tauE D τ) = (tauE D τ c) • X.map (tauE D τ) := by
  ext i j; simp [Matrix.map_apply, Matrix.smul_apply]

theorem Jst_map (τ : D.what₂.Tau) : (Jst D n).map (tauE D τ) = Glob.reidx (JJ n) := by
  rw [Jst, block_matrix_map, map0, map1, mapn1]
  rfl

theorem reidx_mul (a b : M2 n) : Glob.reidx (a * b) = Glob.reidx a * Glob.reidx b := by
  simp [Glob.reidx, Matrix.submatrix_mul_equiv]

theorem reidx_one : Glob.reidx (1 : M2 n) = 1 := by
  simp [Glob.reidx, Matrix.submatrix_one_equiv]

theorem reidx_conjTranspose (a : M2 n) : Glob.reidx aᴴ = (Glob.reidx a)ᴴ := by
  simp [Glob.reidx, Matrix.conjTranspose_submatrix]

theorem inG_JJc : InG (JJ n) := by
  simp only [InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp

theorem mat_one : mat (1 : G D n) = 1 := by simp [mat]

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := by simp [mat]

theorem ratPt_of (τ : D.what₂.Tau) (u : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (M : M2 n) (hM : InG M)
    (hu : u.map (tauE D τ) = Glob.reidx M) : ∃ γ ∈ GF D n, (mat γ).map (psiT D τ) = Glob.reidx M := by
  have hdet : IsUnit u.det := by
    have h1 : tauE D τ u.det = M.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hu, Glob.reidx, Matrix.det_submatrix_equiv_self]
    have h2 : M.det ≠ 0 := (isUnit_det_of_inG hM).ne_zero
    refine isUnit_iff_ne_zero.2 fun h0 => h2 ?_
    rw [← h1, h0, map_zero]
  let U : GL (Fin (n + n)) D.host.E := ⟨u, u⁻¹, Matrix.mul_nonsing_inv u hdet, Matrix.nonsing_inv_mul u hdet⟩
  have hU : U ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) := by
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u * Jst D n * u = Jst D n
    have key : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u * Jst D n * u).map (tauE D τ) =
        (Jst D n).map (tauE D τ) := by
      rw [Matrix.map_mul, Matrix.map_mul, cT_map_tauE, Jst_map, hu, ← reidx_conjTranspose, ← reidx_mul, ← reidx_mul, hM]
    exact Matrix.map_injective (tauE D τ).injective key
  refine ⟨GlobalTheory.AdelicU.ratEmb D.sp.cm.sig (Jst D n) ⟨U, hU⟩, ?_, ?_⟩
  · show _ ∈ GlobalTheory.AdelicU.ratPts D.sp.cm.sig (Jst D n)
    rw [← GlobalTheory.AdelicU.range_ratEmb]; exact MonoidHom.mem_range.2 ⟨_, rfl⟩
  · show (u.map (inclR (AF D.host.F))).map (psiT D τ) = _
    rw [Matrix.map_map]
    have : (⇑(psiT D τ) ∘ ⇑(inclR (AF D.host.F))) = ⇑(tauE D τ) := funext fun e => psiT_inclR D τ e
    rw [this, hu]

def gam (D : D7) (n : ℕ) (τ : D.what₂.Tau) : Subgroup (GR n) where
  carrier := {y | ∃ γ ∈ GF D n, (mat γ).map (psiT D τ) = Glob.reidx (mR y)}
  one_mem' := ⟨1, one_mem _, by
    rw [mat_one, Matrix.map_one _ (map_zero _) (map_one _)]
    exact reidx_one.symm⟩
  mul_mem' := by
    rintro a b ⟨γ, hγ, ea⟩ ⟨γ', hγ', eb⟩
    refine ⟨γ * γ', mul_mem hγ hγ', ?_⟩
    rw [mat_mul, Matrix.map_mul, ea, eb]
    exact (reidx_mul _ _).symm
  inv_mem' := by
    rintro a ⟨γ, hγ, ea⟩
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    have h1 : (mat γ⁻¹).map (psiT D τ) * (mat γ).map (psiT D τ) = 1 := by
      rw [← Matrix.map_mul, ← mat_mul, inv_mul_cancel, mat_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : Glob.reidx (mR a) * Glob.reidx (mR a⁻¹) = 1 := by
      rw [← reidx_mul]
      show Glob.reidx (mR (a * a⁻¹)) = 1
      rw [mul_inv_cancel]; exact reidx_one
    calc (mat γ⁻¹).map (psiT D τ) = (mat γ⁻¹).map (psiT D τ) * (Glob.reidx (mR a) * Glob.reidx (mR a⁻¹)) := by
          rw [h2, Matrix.mul_one]
      _ = Glob.reidx (mR a⁻¹) := by rw [← Matrix.mul_assoc, ← ea, h1, Matrix.one_mul]

theorem mkGR_ext {g : M2 n} (hg : InG g) {h : GR n} (e : mR h = g) : h = mkGR g hg :=
  Subtype.ext (Units.ext e)

theorem gens_mem (τ : D.what₂.Tau) (h : GR n) (hh : IsNElt h ∨ IsMElt h ∨ IsWElt h) :
    h ∈ (gam D n τ).topologicalClosure := by
  rcases hh with ⟨b, hb, e⟩ | ⟨A, hA, e⟩ | e
  · have hh : h = nuE b := by
      rw [mkGR_ext (inG_nUh (hpart_herm b)) (show mR h = nU (hpart b) by rw [hpart_of_herm hb]; exact e)]; rfl
    rw [hh]
    refine closure_mono ?_ (nuE_mem_closure (tauE D τ) (denseRange_tauE τ) b)
    rintro _ ⟨e', rfl⟩
    have hβ : ((2 : D.host.E)⁻¹ • (e' + Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')).map (tauE D τ) =
        hpart (e'.map (tauE D τ)) := by
      rw [map_smul_E, Matrix.map_add _ (map_add (tauE D τ)), cT_map_tauE, map_inv₀, map_ofNat, hpart, one_div]
    obtain ⟨γ, hγ, he⟩ := ratPt_of τ (blk4 1 ((2 : D.host.E)⁻¹ • (e' + Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')) 0 1)
      (nU (hpart (e'.map (tauE D τ)))) (inG_nUh (hpart_herm _)) (by
        rw [block_matrix_map, map0, map1, hβ]
        rfl)
    exact ⟨γ, hγ, he⟩
  · have hh : h = mlE A := by rw [mlE_of hA]; exact mkGR_ext (inG_mL hA) e
    rw [hh]
    refine closure_mono ?_ (mlE_mem_closure (tauE D τ) (denseRange_tauE τ) A hA)
    rintro _ ⟨B, ⟨hB, e', rfl⟩, rfl⟩
    have hdet : IsUnit e'.det := by
      have h1 : tauE D τ e'.det = (e'.map (tauE D τ)).det := by rw [RingHom.map_det, RingHom.mapMatrix_apply]
      refine isUnit_iff_ne_zero.2 fun h0 => (hB : IsUnit (e'.map (tauE D τ)).det).ne_zero ?_
      rw [← h1, h0, map_zero]
    have hcd : IsUnit (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e').det := by
      have h1 : tauE D τ (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e').det = ((e'.map (tauE D τ))ᴴ).det := by
        rw [RingHom.map_det, RingHom.mapMatrix_apply, cT_map_tauE]
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      have : ((e'.map (tauE D τ))ᴴ).det = 0 := by rw [← h1, h0, map_zero]
      rw [Matrix.det_conjTranspose, star_eq_zero] at this
      exact (hB : IsUnit (e'.map (tauE D τ)).det).ne_zero this
    have hinv : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')⁻¹).map (tauE D τ) =
        ((e'.map (tauE D τ))⁻¹)ᴴ := by
      rw [Matrix.conjTranspose_nonsing_inv, ← cT_map_tauE]
      refine (Matrix.inv_eq_right_inv ?_).symm
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hcd, Matrix.map_one _ (map_zero _) (map_one _)]
    obtain ⟨γ, hγ, he⟩ := ratPt_of τ (blk4 e' 0 0 (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')⁻¹)
      (fromBlocks (e'.map (tauE D τ)) 0 0 ((e'.map (tauE D τ))⁻¹)ᴴ) (inG_mL hB) (by
        rw [block_matrix_map, hinv, map0]
        rfl)
    refine ⟨γ, hγ, ?_⟩
    rw [he, mlE_of hB]
    rfl
  · refine (gam D n τ).le_topologicalClosure ?_
    obtain ⟨γ, hγ, he⟩ := ratPt_of τ (Jst D n) (JJ n) inG_JJc (Jst_map τ)
    exact ⟨γ, hγ, by rw [he, e]⟩

theorem gam_dense (hgen : GenSt) (τ : D.what₂.Tau) (g : GR n) : g ∈ closure (gam D n τ : Set (GR n)) := by
  have h1 : Subgroup.closure {h : GR n | IsNElt h ∨ IsMElt h ∨ IsWElt h} ≤ (gam D n τ).topologicalClosure :=
    (Subgroup.closure_le _).2 fun h hh => gens_mem τ h hh
  exact h1 (hgen n g)

end PositivityTheory.Rg.Sw.Glob.DenseP
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseA
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob.DenseP

variable {n : ℕ}

theorem ext_mR {x y : GR n} (h : mR x = mR y) : x = y := Subtype.ext (Units.ext h)

theorem mR_mul (x y : GR n) : mR (x * y) = mR x * mR y := rfl

theorem mR_inv (x : GR n) : mR x⁻¹ = (mR x)⁻¹ := by
  unfold mR
  rw [Subgroup.coe_inv, Matrix.coe_units_inv]

theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp [JJ, Matrix.fromBlocks_multiply]

theorem inv_JJ : (JJ n)⁻¹ = -JJ n :=
  Matrix.inv_eq_left_inv (by rw [Matrix.neg_mul, JJ_mul_JJ, neg_neg])

theorem inv_nU (x : Matrix (Fin n) (Fin n) ℂ) : (nU x)⁻¹ = nU (-x) :=
  Matrix.inv_eq_left_inv (by unfold nU; simp [Matrix.fromBlocks_multiply])

theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (nU b) := by
  unfold InG nU JJ
  rw [Matrix.fromBlocks_conjTranspose]
  simp [Matrix.fromBlocks_multiply, hb]

theorem inG_lev {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a.det) : InG (fromBlocks a 0 0 (a⁻¹)ᴴ) := by
  have haH : IsUnit aᴴ.det := by rw [Matrix.det_conjTranspose]; exact ha.star
  have h1 : aᴴ * a⁻¹ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ ha, Matrix.conjTranspose_one]
  have h1' : aᴴ * aᴴ⁻¹ = 1 := Matrix.mul_nonsing_inv _ haH
  have h2 : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul _ ha
  unfold InG JJ
  rw [Matrix.fromBlocks_conjTranspose]
  simp [Matrix.fromBlocks_multiply, h1, h2]

theorem inG_JJ : InG (JJ n) := by
  have hH : (JJ n)ᴴ = -JJ n := by
    unfold JJ
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]
    simp
  unfold InG
  rw [hH, Matrix.neg_mul, JJ_mul_JJ, neg_neg, Matrix.one_mul]

def nEl (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) : GR n := mkGR (nU b) (inG_nU hb)

def mEl (a : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) : GR n := mkGR (fromBlocks a 0 0 (a⁻¹)ᴴ) (inG_lev ha)

def wEl : GR n := mkGR (JJ n) inG_JJ

theorem blocks_of_inG {a b c d : Matrix (Fin n) (Fin n) ℂ} (h : InG (fromBlocks a b c d)) :
    aᴴ * c = cᴴ * a ∧ aᴴ * d - cᴴ * b = 1 ∧ dᴴ * a - bᴴ * c = 1 ∧ bᴴ * d = dᴴ * b := by
  unfold InG JJ at h
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h
  have e11 := congrArg Matrix.toBlocks₁₁ h
  have e12 := congrArg Matrix.toBlocks₁₂ h
  have e21 := congrArg Matrix.toBlocks₂₁ h
  have e22 := congrArg Matrix.toBlocks₂₂ h
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂] at e11 e12 e21 e22
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← sub_eq_zero, ← e11]; noncomm_ring
  · rw [← e12]; noncomm_ring
  · have k : -(dᴴ * a - bᴴ * c) = -1 := by rw [← e21]; noncomm_ring
    exact neg_inj.mp k
  · rw [← sub_eq_zero, ← e22]; noncomm_ring

theorem cross_of_inG {a b c d : Matrix (Fin n) (Fin n) ℂ} (h : InG (fromBlocks a b c d)) : c * dᴴ = d * cᴴ := by
  obtain ⟨h11, h12, h21, h22⟩ := blocks_of_inG h
  have hl : fromBlocks dᴴ (-bᴴ) (-cᴴ) aᴴ * fromBlocks a b c d = 1 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    refine Matrix.fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩
    · rw [← h21]; noncomm_ring
    · rw [Matrix.neg_mul, h22]; abel
    · rw [Matrix.neg_mul, ← h11]; abel
    · rw [← h12]; noncomm_ring
  have hr : fromBlocks a b c d * fromBlocks dᴴ (-bᴴ) (-cᴴ) aᴴ = 1 := mul_eq_one_comm.mp hl
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at hr
  have e := congrArg Matrix.toBlocks₂₁ hr
  simp only [Matrix.toBlocks_fromBlocks₂₁] at e
  rw [← sub_eq_zero, ← e]; noncomm_ring

theorem det_ne (g : GR n) : ((mR g).toBlocks₂₂ - Complex.I • (mR g).toBlocks₂₁).det ≠ 0 := by
  set a := (mR g).toBlocks₁₁
  set b := (mR g).toBlocks₁₂
  set c := (mR g).toBlocks₂₁
  set d := (mR g).toBlocks₂₂
  have hA : mR g = fromBlocks a b c d := (Matrix.fromBlocks_toBlocks _).symm
  have hU : InG (fromBlocks a b c d) := by rw [← hA]; exact g.2
  have hc := cross_of_inG hU
  have hG : IsUnit (fromBlocks a b c d).det := by rw [← hA]; exact isUnit_det_of_inG g.2
  intro h0
  have h0' : (d - Complex.I • c)ᴴ.det = 0 := by rw [Matrix.det_conjTranspose, h0, star_zero]
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0'
  have hMH : (d - Complex.I • c)ᴴ = dᴴ + Complex.I • cᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul]
    simp [sub_eq_add_neg, Complex.conj_I]
  rw [hMH, Matrix.add_mulVec, Matrix.smul_mulVec] at hMv
  set w := cᴴ *ᵥ v
  set u := dᴴ *ᵥ v
  have hu : u = -(Complex.I • w) := eq_neg_of_add_eq_zero_left hMv
  have k1 : star v ⬝ᵥ ((c * dᴴ) *ᵥ v) = star w ⬝ᵥ u := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    congr 1
    have := Matrix.star_mulVec cᴴ v
    rw [Matrix.conjTranspose_conjTranspose] at this
    exact this.symm
  have k2 : star v ⬝ᵥ ((d * cᴴ) *ᵥ v) = star u ⬝ᵥ w := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    congr 1
    have := Matrix.star_mulVec dᴴ v
    rw [Matrix.conjTranspose_conjTranspose] at this
    exact this.symm
  have k3 : star w ⬝ᵥ u = star u ⬝ᵥ w := by rw [← k1, ← k2, hc]
  rw [hu] at k3
  simp only [dotProduct_neg, neg_dotProduct, dotProduct_smul, smul_dotProduct, star_neg, star_smul, smul_eq_mul,
    Complex.star_def, Complex.conj_I] at k3
  have hS : star w ⬝ᵥ w = 0 := by
    have k4 : (2 * Complex.I) * (star w ⬝ᵥ w) = 0 := by linear_combination -k3
    rcases mul_eq_zero.mp k4 with h2 | h2
    · exact absurd h2 (mul_ne_zero two_ne_zero Complex.I_ne_zero)
    · exact h2
  have hw : w = 0 := dotProduct_star_self_eq_zero.mp hS
  have hu0 : u = 0 := by rw [hu, hw, smul_zero, neg_zero]
  have hz : (fromBlocks a b c d)ᴴ *ᵥ Sum.elim (0 : Fin n → ℂ) v = 0 := by
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_zero, zero_add]
    show Sum.elim w u = 0
    rw [hw, hu0]
    exact Sum.elim_zero_zero
  have hz0 : Sum.elim (0 : Fin n → ℂ) v ≠ 0 := by
    intro hz'
    apply hv
    funext i
    have := congrFun hz' (Sum.inr i)
    simpa using this
  have hdet : (fromBlocks a b c d)ᴴ.det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hz0, hz⟩
  rw [Matrix.det_conjTranspose] at hdet
  exact hG.ne_zero (star_eq_zero.mp hdet)

theorem exists_real (c d : Matrix (Fin n) (Fin n) ℂ) (h : (d - Complex.I • c).det ≠ 0) :
    ∃ t : ℝ, (d + (t : ℂ) • c).det ≠ 0 := by
  classical
  let P : Polynomial ℂ := (d.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • c.map Polynomial.C).det
  have hev : ∀ z : ℂ, P.eval z = (d + z • c).det := by
    intro z
    rw [show P.eval z = Polynomial.evalRingHom z P from rfl, RingHom.map_det]
    congr 1
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply]
    ring
  have hP : P ≠ 0 := by
    intro h0
    apply h
    have := hev (-Complex.I)
    rw [h0, Polynomial.eval_zero, neg_smul, ← sub_eq_add_neg] at this
    exact this.symm
  have hfin : (Complex.ofReal ⁻¹' {x : ℂ | P.IsRoot x}).Finite :=
    (Polynomial.finite_setOfPred_isRoot hP).preimage Complex.ofReal_injective.injOn
  obtain ⟨t, -, ht⟩ := Set.infinite_univ.exists_notMem_finite hfin
  refine ⟨t, ?_⟩
  rw [← hev]
  exact ht

abbrev genSet (n : ℕ) : Set (GR n) := {h : GR n | IsNElt h ∨ IsMElt h ∨ IsWElt h}

theorem mem_of_unit (h : GR n) (hd : IsUnit (mR h).toBlocks₂₂.det) : h ∈ Subgroup.closure (genSet n) := by
  set a := (mR h).toBlocks₁₁
  set b := (mR h).toBlocks₁₂
  set c := (mR h).toBlocks₂₁
  set d := (mR h).toBlocks₂₂
  have hA : mR h = fromBlocks a b c d := (Matrix.fromBlocks_toBlocks _).symm
  have hU : InG (fromBlocks a b c d) := by rw [← hA]; exact h.2
  obtain ⟨h11, h12, h21, h22⟩ := blocks_of_inG hU
  have e1 : d * d⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have e1' : d⁻¹ * d = 1 := Matrix.nonsing_inv_mul _ hd
  have e2 : d⁻¹ᴴ * dᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
  have hβ : (b * d⁻¹)ᴴ = b * d⁻¹ := by
    calc (b * d⁻¹)ᴴ = d⁻¹ᴴ * bᴴ * (d * d⁻¹) := by rw [e1, Matrix.mul_one, Matrix.conjTranspose_mul]
      _ = d⁻¹ᴴ * (bᴴ * d) * d⁻¹ := by simp only [Matrix.mul_assoc]
      _ = d⁻¹ᴴ * (dᴴ * b) * d⁻¹ := by rw [h22]
      _ = (d⁻¹ᴴ * dᴴ) * b * d⁻¹ := by simp only [Matrix.mul_assoc]
      _ = b * d⁻¹ := by rw [e2, Matrix.one_mul]
  have hdH : IsUnit dᴴ.det := by rw [Matrix.det_conjTranspose]; exact hd.star
  have hα : IsUnit (dᴴ)⁻¹.det := Matrix.isUnit_nonsing_inv_det _ hdH
  have hαinv : ((dᴴ)⁻¹)⁻¹ᴴ = d := by
    rw [Matrix.nonsing_inv_nonsing_inv _ hdH, Matrix.conjTranspose_conjTranspose]
  have k1 : dᴴ * (b * d⁻¹) = bᴴ := by
    rw [← Matrix.mul_assoc, ← h22, Matrix.mul_assoc, e1, Matrix.mul_one]
  have k2 : b * d⁻¹ * d = b := by rw [Matrix.mul_assoc, e1', Matrix.mul_one]
  let n1 := nEl (b * d⁻¹) hβ
  let m1 := mEl (dᴴ)⁻¹ hα
  let l1 := m1⁻¹ * n1⁻¹ * h
  have hm1 : (mR m1)⁻¹ = fromBlocks dᴴ 0 0 d⁻¹ := by
    show (fromBlocks (dᴴ)⁻¹ 0 0 ((dᴴ)⁻¹)⁻¹ᴴ)⁻¹ = _
    rw [hαinv]
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    refine Matrix.fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩
    · rw [Matrix.mul_nonsing_inv _ hdH]; noncomm_ring
    · noncomm_ring
    · noncomm_ring
    · rw [e1']; noncomm_ring
  have hl1 : mR l1 = fromBlocks 1 0 (d⁻¹ * c) 1 := by
    show (mR m1)⁻¹ * (mR n1)⁻¹ * mR h = _
    rw [hm1, show mR n1 = nU (b * d⁻¹) from rfl, inv_nU, hA]
    unfold nU
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    refine Matrix.fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩
    · calc _ = dᴴ * a - (dᴴ * (b * d⁻¹)) * c := by noncomm_ring
        _ = 1 := by rw [k1]; exact h21
    · calc _ = dᴴ * (b - b * d⁻¹ * d) := by noncomm_ring
        _ = 0 := by rw [k2, sub_self, Matrix.mul_zero]
    · noncomm_ring
    · calc _ = d⁻¹ * d := by noncomm_ring
        _ = 1 := e1'
  have he : (d⁻¹ * c)ᴴ = d⁻¹ * c := by
    have hU1 : InG (mR l1) := l1.2
    rw [hl1] at hU1
    unfold InG JJ at hU1
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hU1
    have k := congrArg Matrix.toBlocks₁₁ hU1
    simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.conjTranspose_one, Matrix.conjTranspose_zero] at k
    rw [eq_comm, ← sub_eq_zero, ← k]; noncomm_ring
  have hneg : (-(d⁻¹ * c))ᴴ = -(d⁻¹ * c) := by rw [Matrix.conjTranspose_neg, he]
  let n2 := nEl (-(d⁻¹ * c)) hneg
  have hl1' : l1 = wEl * n2 * wEl⁻¹ := by
    apply ext_mR
    rw [hl1, mR_mul, mR_mul, mR_inv, show mR (wEl (n := n)) = JJ n from rfl, show mR n2 = nU (-(d⁻¹ * c)) from rfl,
      inv_JJ]
    unfold JJ nU
    rw [Matrix.fromBlocks_neg, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    refine Matrix.fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring
  have hn1 : n1 ∈ Subgroup.closure (genSet n) := Subgroup.subset_closure (Or.inl ⟨_, hβ, rfl⟩)
  have hm1' : m1 ∈ Subgroup.closure (genSet n) := Subgroup.subset_closure (Or.inr (Or.inl ⟨_, hα, rfl⟩))
  have hw : (wEl : GR n) ∈ Subgroup.closure (genSet n) := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hn2 : n2 ∈ Subgroup.closure (genSet n) := Subgroup.subset_closure (Or.inl ⟨_, hneg, rfl⟩)
  have hl : l1 ∈ Subgroup.closure (genSet n) := by
    rw [hl1']
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hw hn2) (Subgroup.inv_mem _ hw)
  have hh : h = n1 * m1 * l1 := by
    show h = n1 * m1 * (m1⁻¹ * n1⁻¹ * h)
    group
  rw [hh]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn1 hm1') hl

theorem genSt : GenSt := by
  intro n g
  have hA : mR g = fromBlocks (mR g).toBlocks₁₁ (mR g).toBlocks₁₂ (mR g).toBlocks₂₁ (mR g).toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks _).symm
  obtain ⟨t, ht⟩ := exists_real _ _ (det_ne g)
  have htH : ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = (t : ℂ) • 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  let nt := nEl ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) htH
  have hnt : nt ∈ Subgroup.closure (genSet n) := Subgroup.subset_closure (Or.inl ⟨_, htH, rfl⟩)
  have hh : g * nt ∈ Subgroup.closure (genSet n) := by
    apply mem_of_unit
    rw [mR_mul, show mR nt = nU ((t : ℂ) • 1) from rfl, hA]
    unfold nU
    rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂]
    have e : (mR g).toBlocks₂₁ * ((t : ℂ) • 1) + (mR g).toBlocks₂₂ * 1 =
        (mR g).toBlocks₂₂ + (t : ℂ) • (mR g).toBlocks₂₁ := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.mul_one, add_comm]
    rw [e]
    exact isUnit_iff_ne_zero.2 ht
  have hg : g = g * nt * nt⁻¹ := by group
  rw [hg]
  exact Subgroup.mul_mem _ hh (Subgroup.inv_mem _ hnt)

end PositivityTheory.Rg.Sw.Glob.DenseP
end
end

noncomputable section

open Matrix Topology
open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open Formalism.IndefR.Eqv (psiT thetaC)

theorem denseTau : DenseTau := by
  intro D n θ τ ι hθ hι y O hO hy
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  have hcl := DenseP.gam_dense (D := D) DenseP.genSt τ y
  obtain ⟨y', hy'O, γ, hγ, hγe⟩ := mem_closure_iff.1 hcl O hO hy
  have hc : ∀ τ' (w : Formalism.IndefR.Datum.Mx D (n + n) (n + n)), compAt (thetaC D) τ' w = w.map (psiT D τ') :=
    fun _ _ => rfl
  have hy' : (mat (ι y')).map (psiT D τ) = Glob.reidx (mR y') := (hc τ _).symm.trans (hι.2 y').1
  refine ⟨γ, hγ, y', hy'O, γ * (ι y')⁻¹, by group, fun y'' => ?_⟩
  have hR : (mat (γ * (ι y')⁻¹)).map (psiT D τ) = 1 := by
    have h1 : (mat γ).map (psiT D τ) = (mat (γ * (ι y')⁻¹)).map (psiT D τ) * (mat (ι y')).map (psiT D τ) := by
      rw [← Matrix.map_mul, ← DenseP.mat_mul, inv_mul_cancel_right]
    rw [hγe, hy'] at h1
    have h2 : Glob.reidx (mR y') * Glob.reidx (mR y'⁻¹) = 1 := by
      rw [← DenseP.reidx_mul]
      show Glob.reidx (mR (y' * y'⁻¹)) = 1
      rw [mul_inv_cancel]; exact DenseP.reidx_one
    calc (mat (γ * (ι y')⁻¹)).map (psiT D τ)
        = (mat (γ * (ι y')⁻¹)).map (psiT D τ) * (Glob.reidx (mR y') * Glob.reidx (mR y'⁻¹)) := by
          rw [h2, Matrix.mul_one]
      _ = 1 := by rw [← Matrix.mul_assoc, ← h1, h2]
  generalize γ * (ι y')⁻¹ = x at hR ⊢
  apply Subtype.ext
  apply Units.ext
  show mat (x * ι y'') = mat (ι y'' * x)
  rw [DenseP.mat_mul, DenseP.mat_mul]
  apply Formalism.IndefR.Eqv.mat_ext D
  · intro τ'
    rw [Matrix.map_mul, Matrix.map_mul]
    by_cases h : τ' = τ
    · subst h; rw [hR]; simp only [Matrix.one_mul, Matrix.mul_one]
    · have h1 : (mat (ι y'')).map (psiT D τ') = 1 := by rw [← hc]; exact (hι.2 y'').2.1 τ' h
      rw [h1]; simp only [Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.map_mul, Matrix.map_mul, (hι.2 y'').2.2]; simp only [Matrix.one_mul, Matrix.mul_one]

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ReidxConjTranspose
noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open EmbP
open Formalism.IndefR.Eqv (psiT thetaC eq_thetaC)

variable {D : D7} {n : ℕ}

theorem reidx_conjTranspose (a : M2 n) : reidx aᴴ = (reidx a)ᴴ := by
  simp only [reidx, Matrix.conjTranspose_submatrix]

theorem continuous_reidx : Continuous (fun a : M2 n => reidx a) :=
  continuous_id.matrix_submatrix _ _

theorem Jst_map (τ : D.what₂.Tau) : (Jst D n).map (tauE D τ) = reidx (JJ n) := by
  ext i j
  simp only [Jst, blk4, reidx, JJ, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

theorem mR_mul (a b : GR n) : mR (a * b) = mR a * mR b := rfl

theorem mR_one : mR (1 : GR n) = 1 := rfl

theorem mR_mul_inv (a : GR n) : mR a * mR a⁻¹ = 1 := by
  rw [← mR_mul, mul_inv_cancel, mR_one]

theorem mR_inv_mul (a : GR n) : mR a⁻¹ * mR a = 1 := by
  rw [← mR_mul, inv_mul_cancel, mR_one]

theorem reidx_unitary (τ : D.what₂.Tau) (y : GR n) :
    (reidx (mR y))ᴴ * (Jst D n).map (tauE D τ) * reidx (mR y) = (Jst D n).map (tauE D τ) := by
  have h : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  rw [Jst_map, ← reidx_conjTranspose, ← reidx_mul, ← reidx_mul, h]

def iotaF (τ : D.what₂.Tau) (y : GR n) : G D n :=
  (⟨⟨atMN D τ (reidx (mR y)), atMN D τ (reidx (mR y⁻¹)),
      by rw [← atMN_mul, ← reidx_mul, mR_mul_inv, reidx_one, atMN_one],
      by rw [← atMN_mul, ← reidx_mul, mR_inv_mul, reidx_one, atMN_one]⟩,
    atMN_unitary D τ (Jst D n) _ (reidx_unitary τ y)⟩ : HR (AF D.host.F) D.sp.cm.sig (Jst D n))

def iota (τ : D.what₂.Tau) : GR n →* G D n where
  toFun := iotaF τ
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    show atMN D τ (reidx (mR 1)) = 1
    rw [mR_one, reidx_one, atMN_one]
  map_mul' a b := by
    apply Subtype.ext
    apply Units.ext
    show atMN D τ (reidx (mR (a * b))) = atMN D τ (reidx (mR a)) * atMN D τ (reidx (mR b))
    rw [mR_mul, reidx_mul, atMN_mul]

theorem continuous_iota (τ : D.what₂.Tau) : Continuous (iota (D := D) (n := n) τ) := by
  have hm : Continuous fun y : GR n => mR y := Units.continuous_val.comp continuous_subtype_val
  have hmi : Continuous fun y : GR n => mR y⁻¹ := hm.comp continuous_inv
  refine continuous_induced_rng.2 ?_
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_atMN D τ).comp (continuous_reidx.comp hm)
  · exact (continuous_atMN D τ).comp (continuous_reidx.comp hmi)

theorem sEmb : SEmb := by
  intro D n θ τ hθ
  obtain rfl := eq_thetaC D hθ
  refine ⟨iota τ, continuous_iota τ, fun y => ⟨?_, fun τ' hτ' => ?_, ?_⟩⟩
  · have e := psi_atMN D τ τ (reidx (mR y))
    rw [if_pos rfl] at e
    exact e
  · have e := psi_atMN D τ τ' (reidx (mR y))
    rw [if_neg hτ'] at e
    exact e
  · exact fin_atMN D τ (reidx (mR y))

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GIk
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem gIk : GIk := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι _hC L hL ρ hρ Ψ hΨ P g k hk
  have key : ω (ι k) (phiS θ τ fr (cLoc l τ) Ψ P) = phiS θ τ fr (cLoc l τ) Ψ (ρ k P) := by
    have h1 := hL k Ψ hΨ P
    rw [hρ k P hk] at h1
    have hmem : tens θ τ fr (fP (cLoc l τ) (ρ k P)) Ψ ∈ schwartzA θ V.rank n := by
      rw [← h1]; exact (ω (ι k) (phiS θ τ fr (cLoc l τ) Ψ P)).2
    apply Subtype.ext
    rw [h1]
    unfold phiS
    rw [dite_eq_left hmem]
  unfold thF thetaInt theta
  simp only [map_mul, Module.End.mul_apply, key]

end PositivityTheory.Rg.Sw.Glob
end
end

namespace PositivityTheory.Rg.Sw.Glob

theorem top (hA : AbsThm) (hLF : LocFact) (hAA : AwayAct)
    (hLi : LocInst) (hTA : PositivityTheory.PfSWUS.ThetaAuto) (hLC : LieComm) (hDO : DerivOne) (hId : GIdil)
    (hE : EisStrong) (hC : PositivityTheory.PfSWUS.CoefND)
    (hW : GlobalTheory.Published.WeilThetaConvergence) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, GlobalTheory.Cont.HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (GlobalTheory.StdUnn.s0 V n) (GlobalTheory.StdUnn.thetaInt ω ν Φ g) := by
  have hTM := tensMem
  have hTL := thLin_of hW
  exact main hA sFrame sEmb sigOK splitFock hTM (locOpEx_of_locFact hLF) hLi (linSec_of hTL)
    (gSplit_of gIwasawa hAA hLF awayIn schFP hTM lNZ) (gIauto_of hTA hTM) gIk
    (gIinv_of hTM hTL hLC hDO) hId hE gLamBd (gLsing PositivityTheory.Rg.Sw.twoSided' denseTau) hC
    (convRight_of hE) hTL lNZ

end PositivityTheory.Rg.Sw.Glob
