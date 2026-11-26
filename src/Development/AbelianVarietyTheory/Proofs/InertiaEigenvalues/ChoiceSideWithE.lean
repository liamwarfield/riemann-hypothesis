module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralPoleRapidKernelSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulSchurEulerProduct

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChoiceSideWithE
noncomputable section

namespace GlobalTheory.ChoiceRead

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section Choice

variable {D : D7}

abbrev Tgt (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ) : Type :=
  FractionRing (c.Oe w) ⊗[D.ntw.Ok (c.twI w) (c.k' w)]
    D.nexp.MtV (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w)))

def BasisAt (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ)
    (e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j) : Prop :=
  ∀ b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j),
    LinearIndependent (FractionRing (c.Oe w)) (fun i => e (b i)) ∧
      Submodule.span (FractionRing (c.Oe w)) (Set.range fun i => e (b i)) = ⊤

def latT (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ) : Submodule (c.Oe w) (Tgt c w j) :=
  Submodule.span (c.Oe w)
      ((TensorProduct.mk (D.ntw.Ok (c.twI w) (c.k' w)) (FractionRing (c.Oe w))
          (D.nexp.MtV (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w)))) 1) ''
        (D.nexp.MtLat (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))) :
          Set (D.nexp.MtV (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))))))

def latS (w : D.what₂.places.Pl) (j : ℕ) : Set (D.what₂.MtL (D.what₂.muTw w) j) :=
  {x | D.what₂.jMt (D.what₂.muTw w) j x ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen}

def LatAt (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ)
    (e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j) (t : FractionRing (c.Oe w)) : Prop :=
  Submodule.span (c.Oe w) (e '' latS w j) = Submodule.span (c.Oe w) ((fun y => t • y) '' (latT c w j : Set (Tgt c w j)))

theorem BasisAt.smul {c : NChoice D} {w : D.what₂.places.Pl} {j : ℕ}
    {e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j} (h : BasisAt c w j e) (u : (FractionRing (c.Oe w))ˣ) :
    BasisAt c w j ((u : FractionRing (c.Oe w)) • e) := by
  intro b
  obtain ⟨h1, h2⟩ := h b
  refine ⟨?_, ?_⟩
  · exact h1.units_smul (fun _ => u)
  · have h3 : (Set.range fun i => ((u : FractionRing (c.Oe w)) • e) (b i)) =
        (u : FractionRing (c.Oe w)) • Set.range fun i => e (b i) := by
      rw [← Set.range_smul]; rfl
    rw [h3, Submodule.span_smul_eq_of_isUnit _ _ u.isUnit, h2]

theorem LatAt.smul_inv {c : NChoice D} {w : D.what₂.places.Pl} {j : ℕ}
    {e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j} (u : (FractionRing (c.Oe w))ˣ)
    (h : LatAt c w j e (u : FractionRing (c.Oe w))) :
    Submodule.span (c.Oe w) ((((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • e) '' latS w j) = latT c w j := by
  let f : Tgt c w j →ₗ[c.Oe w] Tgt c w j :=
    { toFun := fun y => ((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • y
      map_add' := fun _ _ => smul_add _ _ _
      map_smul' := fun r y => by
        simp only [RingHom.id_apply]
        rw [← algebraMap_smul (FractionRing (c.Oe w)) r y, ← algebraMap_smul (FractionRing (c.Oe w)) r,
          smul_smul, smul_smul, mul_comm] }
  have h1 : ((((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • e) '' latS w j) = f '' (e '' latS w j) := by
    rw [Set.image_image]; rfl
  rw [h1, Submodule.span_image, h, ← Submodule.span_image, Set.image_image]
  have h2 : (fun y => f ((u : FractionRing (c.Oe w)) • y)) = id := by
    funext y
    show ((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • ((u : FractionRing (c.Oe w)) • y) = y
    rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [h2, Set.image_id, Submodule.span_eq]

def withE (c : NChoice D) (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j) : NChoice D :=
  { c with
    eMt := E
    eMt_basis := fun w j hw h1 h2 b => hb w j hw h1 h2 b
    eMt_lat := fun w j hw h1 h2 => hl w j hw h1 h2 }

def tupWithE {cf : CharFrame D} {c : NChoice D} (tp : TupTied D cf c) (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j) : TupTied D cf (withE c E hb hl) :=
  { tp with }

theorem choiceSide_withE {cf : CharFrame D} {mt : MtFam D} {exp : NExpTied D} {c : NChoice D} {tp : TupTied D cf c}
    (h : GlobalTheory.HeightCounting.ChoiceSide D cf mt exp c tp) (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j) :
    GlobalTheory.HeightCounting.ChoiceSide D cf mt exp (withE c E hb hl) (tupWithE tp E hb hl) :=
  ⟨⟨h.nct.twOf_eq, h.nct.twSide_eq, h.nct.Q_eq, h.nct.psi_eq, h.nct.embedding_baseField_condition⟩,
    ⟨h.choice.twI_conj, h.choice.sd_place, h.choice.emb_side, h.choice.sd_conj, h.choice.one, h.choice.conj⟩,
    h.off, h.adm, h.psi, h.eMt_level⟩


open Classical in
def pick (c : NChoice D)
    (G : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ i : Fin D.R.m,
      D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1)) :
    ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j
  | w, 0 => c.eMt w 0
  | w, k + 1 => if h : D.what₂.muAt w ≠ D.what₂.mu0 ∧ k < D.R.m then G w h.1 ⟨k, h.2⟩ else c.eMt w (k + 1)

theorem pick_eq (c : NChoice D)
    (G : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ i : Fin D.R.m,
      D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1))
    (w : D.what₂.places.Pl) (hw : D.what₂.muAt w ≠ D.what₂.mu0) (i : Fin D.R.m) : pick c G w (i.1 + 1) = G w hw i := by
  simp only [pick, dite_eq_left (And.intro hw i.2)]

theorem pick_prop (c : NChoice D)
    (G : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ i : Fin D.R.m,
      D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1))
    (p : ∀ w j, (D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j) → Prop)
    (h : ∀ w hw (i : Fin D.R.m), p w (i.1 + 1) (G w hw i)) :
    ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → p w j (pick c G w j) := by
  intro w j hw h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have := h w hw ⟨k, by omega⟩
  rwa [← pick_eq c G w hw ⟨k, by omega⟩] at this

end Choice

section Rows

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {S : RatDat D.ntw}

def ThetaAt (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (YS : NExpRealS R cG S) (c : NChoice D) (w : D.what₂.places.Pl)
    (i : Fin D.R.m) (e : D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1)) (t : FractionRing (c.Oe w)) :
    Prop :=
  ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (i.1 + 1), ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK S (i.1 + 1)),
    (R.FW i).j (sg0 D A3.A) ((YS.fi i).e (∑ k, a k • (show ↥(S.A (i.1 + 1)).WK from f k).1)) =
      Y.mj.eW i (D.what₂.thetaP (D.what₂.muTw w) (i.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (i.1 + 1) x)) →
    NChoice.thPe D c w (i.1 + 1) (e x) =
      t • ∑ k, c.embW w (a k) ⊗ₜ[D.ntw.O (c.twI w)]
        (YS.eF (c.twI w) (i.1 + 1) (c.sd w) (by omega) (by omega)).symm ((1 : KB S (c.twI w) (c.sd w)) ⊗ₜ[S.Ks] f k)

theorem ThetaAt.smul_inv {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {YS : NExpRealS R cG S} {c : NChoice D}
    {w : D.what₂.places.Pl} {i : Fin D.R.m} {e : D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1)}
    (u : (FractionRing (c.Oe w))ˣ) (h : ThetaAt Y YS c w i e (u : FractionRing (c.Oe w))) :
    ThetaAt Y YS c w i ((((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w))) • e) 1 := by
  intro x hx n a f hf
  rw [one_smul, LinearMap.smul_apply, map_smul, h x hx n a f hf, smul_smul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_smul]

theorem emtTheta_withE {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {YS : NExpRealS R cG S} {c : NChoice D}
    (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j)
    (h : ∀ w (i : Fin D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 → ThetaAt Y YS c w i (E w (i.1 + 1)) 1) :
    GlobalTheory.HeightCounting.EMtTheta Y YS (withE c E hb hl) := by
  intro w i hw x hx n a f hf
  have := h w i hw x hx n a f hf
  rw [one_smul] at this
  exact this

end Rows

end GlobalTheory.ChoiceRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergPartialLPoleAtOneConj
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergPartialLPoleAtOneConj
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup
  Formalism.L2.Host GlobalTheory.JSW
open scoped ENNReal nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.RSPole


open GlobalTheory.CuspRep.CuspidalL2GL in
theorem exists_haar_fundamentalDomains : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    ∃ (μ : Measure (GA E a)) (_ : μ.IsHaarMeasure) (𝓕 𝓕' : Set (GA E a)),
      IsFundamentalDomain (ratGL E a).range 𝓕 μ ∧ IsFundamentalDomain (latticeGL E a) 𝓕' μ := by
  intro E _ _ _ a
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.t2Space_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  haveI : DiscreteTopology (ratGL E a).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E a
  obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (ratGL E a).range
  obtain ⟨𝓕', -, -, h𝓕'⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (latticeGL E a)
  exact ⟨Measure.haar, inferInstance, 𝓕, 𝓕', h𝓕 _, h𝓕' _⟩


open GlobalTheory.Petersson GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep.CuspidalL2GL in
theorem setIntegral_mul_conj_ne_zero_rapid {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (π₀ : CuspSub E a) (ω : HChar E) (hω : ω.IsUnitary) (hωc : π₀.HasCentChar ω) (φ : Sm E a)
    (hφ : φ ∈ π₀.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π₀) (h0 : φ ≠ 0) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (𝓕' : Set (GA E a)) (h𝓕 : IsFundamentalDomain (latticeGL E a) 𝓕' μ) :
    ∫ g in 𝓕', φ.1 g * starRingEnd ℂ (φ.1 g) ∂μ ≠ 0 := by
  have hR : φ.1 ∈ GlobalTheory.JSW.rspan π₀ := by
    rcases hφ with h | h
    · exact GlobalTheory.JSW.mem_rspan h
    · rw [GlobalTheory.JSW.rspan_eq_mspanR]; exact h
  have h1 : φ.1 ≠ 0 := fun e => h0 (Subtype.ext e)
  have hb : φ.1 ∈ bddForms E a ω :=
    (GlobalTheory.JSW.rspan_bdd_pet_eq_zero μ hω hωc (ψ := 0) (zero_mem _) (fun _ _ => by simp [pet, descend]) hR).1
  obtain ⟨r, hr, e⟩ := pet_self_pos μ hω hb h1
  rw [← (pet_eq_setIntegral hω hb hb h𝓕).2, e]
  exact_mod_cast hr.ne'

theorem rs_pole_conj : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π → ∃ L : ℝ → ℝ, (∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat π w.1) ((sat π w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (L x : ℂ) ∧ 1 ≤ L x) ∧ ContinuousOn L (Set.Ioi 1) ∧ ∃ c : ℝ, 0 < c ∧ Tendsto (fun x => (x - 1) * L x) (𝓝[>] 1) (𝓝 c) := by
  intro E _ _ _ a π ha hπ T hT
  obtain ⟨α, ℓ, Φ, J, η, π₀, ω, φ, hα, hπ₀, hω, hωc, hφ, hφ0, hΦc, hΦs, hΦr, hΦpos, hΦ0, hZ⟩ := GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E a π ha hπ T hT
  set q : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → ℕ := fun w => Ideal.absNorm w.1.asIdeal with hqdef
  have hq : ∀ w, 2 ≤ q w := fun w => HeightOneSpectrum.one_lt_absNorm w.1
  obtain ⟨μ, hμ, 𝓕, 𝓕', h𝓕, h𝓕'⟩ := exists_haar_fundamentalDomains E a
  obtain ⟨H, hHc, hH1, hZH'⟩ := hZ μ 𝓕 h𝓕
  have hZH : ∀ x : ℝ, 1 < x → _ := fun x hx => (hZH' x hx).2
  have hHpos : ∀ x : ℝ, 1 < x → 0 < H x := fun x hx => (hZH' x hx).1
  set D : ℝ → ℝ := fun x => (eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal with hDdef
  obtain ⟨hprod, hcont⟩ := GlobalTheory.T.hasProd_localRankinSelbergFactor_self_of_eulerProduct _ q a α hq fun x hx => (hZH x hx).1
  refine ⟨D, fun x hx => ?_, hcont, ?_⟩
  · have e : (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat π w.1)
        ((sat π w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) = fun w => locL (q w)
        (Finset.univ.val.map (α w)) ((Finset.univ.val.map (α w)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) := by
      funext w; rw [hα w]
    rw [e]
    exact hprod x hx
  · obtain ⟨c, hc0, hlim⟩ := GlobalTheory.T.rankinSelberg_theta_integral_pole_rapid_kernel_span E a ℓ Φ hΦc hΦs hΦr J η μ 𝓕 𝓕' h𝓕 h𝓕'
    have hc : c ≠ 0 := hc0 hΦpos hΦ0
    have hT2 := (hlim π₀ π₀ ω hω hωc hωc φ φ hφ hφ).2
    have hP := setIntegral_mul_conj_ne_zero_rapid π₀ ω hω hωc φ hφ hφ0 μ 𝓕' h𝓕'
    set P := ∫ g in 𝓕', φ.1 g * starRingEnd ℂ (φ.1 g) ∂μ
    have hH : Tendsto (fun x : ℝ => ((H x : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 ((H 1 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hHc
    have hH0 : ((H 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hH1.ne'
    have hdiv := hT2.div hH hH0
    have hev : ∀ᶠ x in 𝓝[>] (1 : ℝ), ((x - 1 : ℝ) : ℂ) * thetaZ μ 𝓕 ℓ φ.1 φ.1 Φ J η x / ((H x : ℝ) : ℂ) =
        (((x - 1) * D x : ℝ) : ℂ) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [(hZH x hx).2]
      have : ((H x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hHpos x hx).ne'
      simp only [hDdef]
      push_cast
      field_simp
    have hlim2 : Tendsto (fun x : ℝ => (((x - 1) * D x : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 (c * P / ((H 1 : ℝ) : ℂ))) :=
      (hdiv.congr' hev)
    have hre := (Complex.continuous_re.tendsto _).comp hlim2
    have him := (Complex.continuous_im.tendsto _).comp hlim2
    simp only [Function.comp_def, Complex.ofReal_re, Complex.ofReal_im] at hre him
    have him0 : (c * P / ((H 1 : ℝ) : ℂ)).im = 0 := tendsto_nhds_unique tendsto_const_nhds him |>.symm
    have hne : c * P / ((H 1 : ℝ) : ℂ) ≠ 0 := div_ne_zero (mul_ne_zero hc hP) hH0
    have hnn : 0 ≤ (c * P / ((H 1 : ℝ) : ℂ)).re := by
      refine ge_of_tendsto hre ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : (1 : ℝ) < x := hx
      have h1 := (hprod x hx').2
      exact mul_nonneg (by linarith) (by linarith)
    refine ⟨_, lt_of_le_of_ne hnn fun h0 => hne (Complex.ext h0.symm him0), hre⟩

end GlobalTheory.RSPole
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergPartialLPoleAtOneConjStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelberg_partialL_pole_at_one_conj : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π → ∃ L : ℝ → ℝ, (∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat π w.1) ((sat π w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (L x : ℂ) ∧ 1 ≤ L x) ∧ ContinuousOn L (Set.Ioi 1) ∧ ∃ c : ℝ, 0 < c ∧ Tendsto (fun x => (x - 1) * L x) (𝓝[>] 1) (𝓝 c) := by
  first | (exact @GlobalTheory.RSPole.rs_pole_conj) | (exact GlobalTheory.RSPole.rs_pole_conj) | (intros; apply GlobalTheory.RSPole.rs_pole_conj  <;> assumption)
end
end
