module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionModPrimeLevelPrimeSmulEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RbarData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

def ssRep {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) : Γ →* GL (Fin a) k :=
  Classical.epsilon fun ρ' : Γ →* GL (Fin a) k => IsSSRep ρ' ∧ ρ.ker ≤ ρ'.ker ∧
    ∀ g, (ρ' g : Matrix (Fin a) (Fin a) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly

def BcGood (D : D7) (Rw : RowSide D) (σ : D.what₂.FT) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) : Prop :=
  (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π ∧ ∀ τ, (D.naut.infG p.π τ).Nodup ∧
      ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.r : ℂ) - (p.d : ℂ)) / 2) ∧
  rankIso D.nd D.naut Sig = D.R.r ∧ ∀ w, IsSplitPl D.host w → isoLoc D.nd D.naut Sig w = Rw.locR σ w


open Classical in
def bcOf (D : D7) (Rw : RowSide D) (σ : D.what₂.FT) : Multiset (ℕ × ℕ) :=
  if h : ∃ Sig, BcGood D Rw σ Sig then Multiset.ofList (h.choose.map fun p => (p.a, p.d)) else {(D.R.r, 1)}

def RbarData {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (σ : D.what₂.FT) (lam : D.what₂.places.Pl) : Prop :=
  ∃ i : X.nd.Loc, X.nd.w i = lam ∧ ∃ (Sig : List (Formalism.BasicNotions.Part Y.naut.CG))
    (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)),
    HasParamW X.nd Y.naut i σ Sig ∧ IsRepOfSig X.nd Y.naut i Sig ρ


open Classical in
def rbarOf {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (σ : D.what₂.FT) (lam : D.what₂.places.Pl) :
    G D.host.E X.nd.Om →* GL (Fin D.R.r) (Fb (D.what₂.places.resChar lam) (D.what₂.places.resChar_prime lam)) :=
  if h : RbarData Y σ lam then
    ssRep (mapRep (((fbCast (h.choose_spec.1 ▸ X.nd.w_l h.choose).symm (X.nd.lPrime h.choose).out
        (D.what₂.places.resChar_prime lam)).toRingHom.comp
      ((Y.naut.kFbar h.choose).comp (IsLocalRing.residue (X.nd.O h.choose))))) h.choose_spec.2.choose_spec.choose)
  else 1

def mtSup {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (i : X.nd.Loc) (σ' : (lay0 D).ntypes.Par) :
    Submodule ℂ (D.what₂.Mt (X.nd.mu i) (X.nd.j i)) :=
  ⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = (lay0 D).ntypes.locPar σ' w) ∧
      IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)}, Y.naut.typeV i P

def castMt {D : D7} {μ μ' : D.what₂.Tup} {j j' : ℕ} (h1 : μ = μ') (h2 : j = j') (M : Submodule ℂ (D.what₂.Mt μ j)) :
    Submodule ℂ (D.what₂.Mt μ' j') := by
  subst h1; subst h2; exact M


open Classical in
def mtParOf {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (μ : D.what₂.Tup) (j : ℕ) (σ' : (lay0 D).ntypes.Par) :
    Submodule ℂ (D.what₂.Mt μ j) :=
  if h : ∃ i, X.nd.mu i = μ ∧ X.nd.j i = j then castMt h.choose_spec.1 h.choose_spec.2 (mtSup Y h.choose σ') else ⊥

end GlobalTheory.HeightCounting

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyCoeffCongrSamePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyCoeffCongrSamePlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

theorem eventually_map_residue_eq {Γ O : Type} [TopologicalSpace Γ] [CommRing O] [IsLocalRing O]
    [TopologicalSpace O] [IsTopologicalRing O]
    (hO : IsOpen ((IsLocalRing.maximalIdeal O : Ideal O) : Set O)) {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) O) (hM : Continuous M) (g0 : Γ) :
    ∀ᶠ g in nhds g0, (M g).map (IsLocalRing.residue O) = (M g0).map (IsLocalRing.residue O) := by
  have h : ∀ a b, ∀ᶠ g in nhds g0, M g a b - M g0 a b ∈ IsLocalRing.maximalIdeal O := by
    intro a b
    have hc : Continuous fun g => M g a b - M g0 a b := (hM.matrix_elem a b).sub continuous_const
    exact hc.continuousAt.preimage_mem_nhds (hO.mem_nhds (by simp))
  have h2 : ∀ᶠ g in nhds g0, ∀ a b, M g a b - M g0 a b ∈ IsLocalRing.maximalIdeal O := by
    rw [Filter.eventually_all]; intro a; rw [Filter.eventually_all]; exact h a
  filter_upwards [h2] with g hg
  ext a b
  simp only [Matrix.map_apply]
  exact (Ideal.Quotient.eq).2 (hg a b)

theorem sub_mem_nonunits_vs {K : Type} [Field K] (A : ValuationSubring K) {x y : K}
    (hx : x ∈ A.nonunits) (hy : y ∈ A.nonunits) : x - y ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at *
  exact lt_of_le_of_lt (A.valuation.map_sub x y) (max_lt hx hy)

theorem charpoly_coeff_congr_same_place : ∀ (D : D7) (Rw : RowSide D) (Pl : PlSide D) (X : LocNd (lay0 D)) (Y : LocAut X), GlobalTheory.RowTie.ChebSplit D.nd → (∀ i σ w, Y.locW i σ w = Rw.locR σ w) → (∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ Pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (Pl.plκ (X.nd.w i) (IsLocalRing.residue (Pl.plB (X.nd.w i)) ⟨_, h⟩)) = Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y)) → ∀ (σ : D.what₂.FT) (i i' : X.nd.Loc), X.nd.w i = X.nd.w i' → ∀ (Sig Sig' : List (Formalism.BasicNotions.Part Y.naut.CG)) (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)) (ρ' : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i')), HasParamW X.nd Y.naut i σ Sig → IsRepOfSig X.nd Y.naut i Sig ρ → HasParamW X.nd Y.naut i' σ Sig' → IsRepOfSig X.nd Y.naut i' Sig' ρ' → ∀ (g : G D.host.E X.nd.Om) (n : ℕ), iotaO X.nd Y.naut i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) - iotaO X.nd Y.naut i' ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) ∈ (Pl.plB (X.nd.w i)).nonunits := by
  classical
  intro D Rw Pl X Y hCheb hRw hPl σ i i' hw Sig Sig' ρ ρ' hP hR hP' hR' g n
  have key : ∀ (j : X.nd.Loc) (y y' : X.nd.O j), IsLocalRing.residue (X.nd.O j) y = IsLocalRing.residue (X.nd.O j) y' →
      iotaO X.nd Y.naut j y - iotaO X.nd Y.naut j y' ∈ (Pl.plB (X.nd.w j)).nonunits := by
    intro j y y' hyy
    obtain ⟨h1, e1⟩ := hPl j y
    obtain ⟨h2, e2⟩ := hPl j y'
    have hres : IsLocalRing.residue (Pl.plB (X.nd.w j)) ⟨_, h1⟩ = IsLocalRing.residue (Pl.plB (X.nd.w j)) ⟨_, h2⟩ := by
      apply (Pl.plκ (X.nd.w j)).injective
      apply (fbCast (X.nd.w_l j) (D.what₂.places.resChar_prime (X.nd.w j)) (X.nd.lPrime j).out).injective
      rw [e1, e2, hyy]
    have hm := (Ideal.Quotient.eq).1 hres
    have hv := (ValuationSubring.valuation_lt_one_iff _ _).1 hm
    rw [ValuationSubring.mem_nonunits_iff]
    simpa using hv
  have key' := key i'
  rw [← hw] at key'
  have hO : ∀ j, IsOpen ((IsLocalRing.maximalIdeal (X.nd.O j) : Ideal (X.nd.O j)) : Set (X.nd.O j)) := fun j => by
    simpa using (isAdic_iff.1 (X.nd.O_adic j)).1 1
  have hclosed : IsClosed {g : G D.host.E X.nd.Om |
      iotaO X.nd Y.naut i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) -
        iotaO X.nd Y.naut i' ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) ∈
        (Pl.plB (X.nd.w i)).nonunits} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro g0 hg0
    have e1 := eventually_map_residue_eq (hO i) (fun g => (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i))) hR.1 g0
    have e2 := eventually_map_residue_eq (hO i') (fun g => (ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i'))) hR'.1 g0
    filter_upwards [e1, e2] with g h1 h2
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hg0 ⊢
    intro hg
    apply hg0
    have c1 : IsLocalRing.residue (X.nd.O i) ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) =
        IsLocalRing.residue (X.nd.O i) ((ρ g0 : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) := by
      rw [← Polynomial.coeff_map, ← Polynomial.coeff_map, ← Matrix.charpoly_map, ← Matrix.charpoly_map, h1]
    have c2 : IsLocalRing.residue (X.nd.O i') ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) =
        IsLocalRing.residue (X.nd.O i') ((ρ' g0 : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) := by
      rw [← Polynomial.coeff_map, ← Polynomial.coeff_map, ← Matrix.charpoly_map, ← Matrix.charpoly_map, h2]
    have := sub_mem_nonunits_vs _ hg (sub_mem_nonunits_vs _ (key i _ _ c1) (key' _ _ c2))
    convert this using 1
    ring
  have hfin := Filter.eventually_cofinite.1 hR.2.2
  have hfin' := Filter.eventually_cofinite.1 hR'.2.2
  have hdense := hCheb (hfin.toFinset ∪ hfin'.toFinset)
  have hE := hdense.mono (s₂ := {g : G D.host.E X.nd.Om |
      iotaO X.nd Y.naut i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) -
        iotaO X.nd Y.naut i' ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) ∈
        (Pl.plB (X.nd.w i)).nonunits}) (fun s hs => by
    obtain ⟨w, hwS, hsplit, B, hB, hF⟩ := hs
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not] at hwS
    obtain ⟨q1, q2⟩ := hwS
    have r1 := q1 B s hB hF
    have r2 := q2 B s hB hF
    have eqloc : isoLoc X.nd Y.naut Sig w = isoLoc X.nd Y.naut Sig' w :=
      (hP.2.2 w hsplit).trans ((hRw i σ w).trans ((hRw i' σ w).symm.trans (hP'.2.2 w hsplit).symm))
    rw [Set.mem_setOf_eq, ← Polynomial.coeff_map, ← Polynomial.coeff_map, r1, r2, eqloc, sub_self, ValuationSubring.mem_nonunits_iff,
      map_zero]
    exact zero_lt_one)
  have hc := hE.closure_eq
  rw [hclosed.closure_eq] at hc
  exact Set.eq_univ_iff_forall.1 hc g

end GlobalTheory.HeightCounting
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyCoeffCongrSamePlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_coeff_congr_same_place_alt : ∀ (D : D7) (Rw : RowSide D) (Pl : PlSide D) (X : LocNd (lay0 D)) (Y : LocAut X), GlobalTheory.RowTie.ChebSplit D.nd → (∀ i σ w, Y.locW i σ w = Rw.locR σ w) → (∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ Pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (Pl.plκ (X.nd.w i) (IsLocalRing.residue (Pl.plB (X.nd.w i)) ⟨_, h⟩)) = Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y)) → ∀ (σ : D.what₂.FT) (i i' : X.nd.Loc), X.nd.w i = X.nd.w i' → ∀ (Sig Sig' : List (Formalism.BasicNotions.Part Y.naut.CG)) (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)) (ρ' : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i')), HasParamW X.nd Y.naut i σ Sig → IsRepOfSig X.nd Y.naut i Sig ρ → HasParamW X.nd Y.naut i' σ Sig' → IsRepOfSig X.nd Y.naut i' Sig' ρ' → ∀ (g : G D.host.E X.nd.Om) (n : ℕ), iotaO X.nd Y.naut i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) - iotaO X.nd Y.naut i' ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) ∈ (Pl.plB (X.nd.w i)).nonunits := by
  first | exact @GlobalTheory.HeightCounting.charpoly_coeff_congr_same_place | exact GlobalTheory.HeightCounting.charpoly_coeff_congr_same_place | (intros; apply GlobalTheory.HeightCounting.charpoly_coeff_congr_same_place <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

theorem ss_exists : ∀ {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k), ∃ ρ' : Γ →* GL (Fin a) k, IsSSRep ρ' ∧ ρ.ker ≤ ρ'.ker ∧ ∀ g, (ρ' g : Matrix (Fin a) (Fin a) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly := GlobalTheory.T.exists_semisimplification_matrix_rep_same_charpoly

theorem indep : ∀ (D : D7) (Rw : RowSide D) (Pl : PlSide D) (X : LocNd (lay0 D)) (Y : LocAut X), GlobalTheory.RowTie.ChebSplit D.nd → (∀ i σ w, Y.locW i σ w = Rw.locR σ w) → (∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ Pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (Pl.plκ (X.nd.w i) (IsLocalRing.residue (Pl.plB (X.nd.w i)) ⟨_, h⟩)) = Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y)) → ∀ (σ : D.what₂.FT) (i i' : X.nd.Loc), X.nd.w i = X.nd.w i' → ∀ (Sig Sig' : List (Formalism.BasicNotions.Part Y.naut.CG)) (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)) (ρ' : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i')), HasParamW X.nd Y.naut i σ Sig → IsRepOfSig X.nd Y.naut i Sig ρ → HasParamW X.nd Y.naut i' σ Sig' → IsRepOfSig X.nd Y.naut i' Sig' ρ' → ∀ (g : G D.host.E X.nd.Om) (n : ℕ), iotaO X.nd Y.naut i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) - iotaO X.nd Y.naut i' ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) ∈ (Pl.plB (X.nd.w i)).nonunits := GlobalTheory.T.charpoly_coeff_congr_same_place_alt

theorem ssRep_spec {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) :
    IsSSRep (ssRep ρ) ∧ ρ.ker ≤ (ssRep ρ).ker ∧
    ∀ g, (ssRep ρ g : Matrix (Fin a) (Fin a) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly :=
  Classical.epsilon_spec (ss_exists ρ)

theorem castMt_eq {D : D7} {μ μ' : D.what₂.Tup} {j j' : ℕ} (h1 : μ = μ') (h2 : j = j') (M : Submodule ℂ (D.what₂.Mt μ j))
    (M' : Submodule ℂ (D.what₂.Mt μ' j')) (h : HEq M M') : castMt h1 h2 M = M' := by
  subst h1; subst h2; exact eq_of_heq h

theorem isOpen_ker_mapRep {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {O : Type} [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] (I : Ideal O) (hI : IsOpen (I : Set O)) {k : Type} [CommRing k] (φ : O →+* k)
    (hφ : I ≤ RingHom.ker φ) {a : ℕ} (ρ : Γ →* GL (Fin a) O)
    (hρ : Continuous fun g => (ρ g : Matrix (Fin a) (Fin a) O)) :
    IsOpen ((mapRep φ ρ).ker : Set Γ) := by
  let U : Set Γ := ⋂ i : Fin a, ⋂ j : Fin a, (fun g => (ρ g : Matrix (Fin a) (Fin a) O) i j - (1 : Matrix (Fin a) (Fin a) O) i j) ⁻¹' (I : Set O)
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hI.preimage ?_
    exact ((continuous_apply j).comp ((continuous_apply i).comp hρ)).sub continuous_const
  have h1 : (1 : Γ) ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_preimage, map_one, Units.val_one, sub_self]
    intro i j; exact I.zero_mem
  have hsub : U ⊆ ((mapRep φ ρ).ker : Set Γ) := by
    intro g hg
    simp only [U, Set.mem_iInter, Set.mem_preimage] at hg
    show mapRep φ ρ g = 1
    apply Units.ext
    ext i j
    have := hφ (hg i j)
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    simp only [mapRep, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply, Units.val_one]
    change φ ((ρ g : Matrix (Fin a) (Fin a) O) i j) = (1 : Matrix (Fin a) (Fin a) k) i j
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hU.mem_nhds h1) hsub)

theorem isSSRep_one {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} : IsSSRep (1 : Γ →* GL (Fin a) k) := by
  intro W _
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
  exact ⟨W', fun g v hv => by simpa using hv, hW'⟩

theorem fbCast_trans {p q r : ℕ} (h1 : p = q) (h2 : q = r) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (x : Fb p hp) :
    fbCast h2 hq hr (fbCast h1 hp hq x) = fbCast (h1.trans h2) hp hr x := by
  subst h1; subst h2; rfl

theorem plκ_cast (D : D7) (Pl : PlSide D) {lam lam' : D.what₂.places.Pl} (h : lam = lam') {p : ℕ} (hp : p.Prime)
    (h1 : D.what₂.places.resChar lam = p) (h1' : D.what₂.places.resChar lam' = p) (z z' : ℂ) (hz : z ∈ Pl.plB lam)
    (hz' : z' ∈ Pl.plB lam') (hd : z - z' ∈ (Pl.plB lam).nonunits) :
    fbCast h1 (D.what₂.places.resChar_prime lam) hp (Pl.plκ lam (IsLocalRing.residue (Pl.plB lam) ⟨z, hz⟩)) =
      fbCast h1' (D.what₂.places.resChar_prime lam') hp (Pl.plκ lam' (IsLocalRing.residue (Pl.plB lam') ⟨z', hz'⟩)) := by
  subst h
  have : IsLocalRing.residue (Pl.plB lam) ⟨z, hz⟩ = IsLocalRing.residue (Pl.plB lam) ⟨z', hz'⟩ := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    rw [ValuationSubring.mem_nonunits_iff] at hd
    simpa using hd
  rw [this]

theorem charpoly_mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL (Fin a) B) : Matrix (Fin a) (Fin a) B).charpoly = (ρ g : Matrix (Fin a) (Fin a) A).charpoly.map f := by
  rw [← Matrix.charpoly_map]
  rfl

theorem isSSRep_rbarOf {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (σ : D.what₂.FT) (lam : D.what₂.places.Pl) :
    IsSSRep (rbarOf Y σ lam) := by
  unfold rbarOf
  split_ifs with h
  · exact (ssRep_spec _).1
  · exact isSSRep_one

set_option maxHeartbeats 1000000 in
theorem rbar_tie_at (D : D7) (Rw : RowSide D) (Pl : PlSide D) (X : LocNd (lay0 D)) (Y : LocAut X)
    (hCheb : GlobalTheory.RowTie.ChebSplit D.nd) (hloc : ∀ i σ w, Y.locW i σ w = Rw.locR σ w)
    (hplB : ∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ Pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (Pl.plκ (X.nd.w i) (IsLocalRing.residue (Pl.plB (X.nd.w i)) ⟨_, h⟩)) = Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y))
    (i : X.nd.Loc) (σ : D.what₂.FT) (Sig : List (Formalism.BasicNotions.Part Y.naut.CG))
    (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)) (hP : HasParamW X.nd Y.naut i σ Sig)
    (hR : IsRepOfSig X.nd Y.naut i Sig ρ) (g : G D.host.E X.nd.Om) :
    ((rbarOf Y σ (X.nd.w i) g : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).map
        (fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out).toRingHom =
      (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.map ((Y.naut.kFbar i).comp (IsLocalRing.residue (X.nd.O i))) := by
  have hex : RbarData Y σ (X.nd.w i) := ⟨i, rfl, Sig, ρ, hP, hR⟩
  unfold rbarOf
  rw [dite_eq_left hex, (ssRep_spec _).2.2 g, charpoly_mapRep, Polynomial.map_map]
  have hw0 := hex.choose_spec.1
  have hs := hex.choose_spec.2.choose_spec.choose_spec
  generalize hex.choose_spec.2.choose_spec.choose = ρ0 at hs ⊢
  generalize hex.choose_spec.2.choose = Sig0 at hs ρ0 ⊢
  ext n
  rw [Polynomial.coeff_map, Polynomial.coeff_map]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  obtain ⟨hz0, e0⟩ := hplB hex.choose ((ρ0 g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O hex.choose)).charpoly.coeff n)
  obtain ⟨hz, e⟩ := hplB i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n)
  rw [← e0, ← e, fbCast_trans, fbCast_trans]
  exact plκ_cast D Pl hw0 _ _ _ _ _ hz0 hz
    (indep D Rw Pl X Y hCheb hloc hplB σ _ i hw0 Sig0 Sig ρ0 ρ hs.1 hs.2 hP hR g n)


set_option maxHeartbeats 1000000 in
theorem locTy_exists : ∀ (D : D7) (Rw : RowSide D) (Pl : PlSide D) (X : LocNd (lay0 D)) (Y : LocAut X), BlocksUnique D → GlobalTheory.RowTie.ChebSplit D.nd → (∀ i σ w, Y.locW i σ w = Rw.locR σ w) → (∀ i : X.nd.Loc, Y.naut.iotaQC i = qCast (X.nd.w_l i) (Pl.ι (X.nd.w i))) → (∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ Pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (Pl.plκ (X.nd.w i) (IsLocalRing.residue (Pl.plB (X.nd.w i)) ⟨_, h⟩)) = Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y)) → (∀ i k v, X.nd.gam0 i (D.naut.plGw k v) = D.ntypes.tg k v) → (∀ (i : X.nd.Loc) k v, X.nd.l i ≠ D.host.g k → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ u : (ZMod (D.host.g k))ˣ, (u = D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩ ∨ u = (D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩)⁻¹) ∧ iotaO X.nd Y.naut i ((X.nd.chi i 1 (D.ntypes.tg k v) : (X.nd.O i)ˣ) : X.nd.O i) = D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)))) → (∀ (i i' : X.nd.Loc) (σ' : (lay0 D).ntypes.Par), X.nd.mu i = X.nd.mu i' → X.nd.j i = X.nd.j i' → HEq (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = (lay0 D).ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)}, Y.naut.typeV i P) (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = (lay0 D).ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i' P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i']) Y.naut.etaTinv)}, Y.naut.typeV i' P)) → ∃ Z : LocTy Y, BcTie X.nd Y.naut Z.ntypes ∧ RbarTie X.nd Y.naut Z.ntypes ∧ MtParTie X.nd Y.naut Z.ntypes ∧ ∀ σ lam, IsSSRep (Z.rbar σ lam) := by
  intro D Rw Pl X Y hBU hCheb hloc hiota hplB hgam hchi hMt
  refine ⟨{ bc := bcOf D Rw, bc_pos := ?_, bc_sum := ?_, rbar := rbarOf Y, rbar_open := ?_, heckeLoc_gamma_places := hgam, chiT_tg := ?_, MtPar := mtParOf Y }, ?_, ?_, ?_, ?_⟩
  · intro σ p hp
    unfold bcOf at hp
    split_ifs at hp with h
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hp)
      obtain ⟨h1, h2, -⟩ := h.choose_spec.1 q hq
      exact ⟨h1, h2⟩
    · rw [Multiset.mem_singleton] at hp; subst hp
      refine ⟨?_, Nat.one_pos⟩
      have := D.R.m_add_three_le_k; have := D.R.two_le_m
      simp only [Ranks.r]; omega
  · intro σ
    unfold bcOf
    split_ifs with h
    · have := h.choose_spec.2.1
      simp only [Multiset.map_coe, Multiset.sum_coe, List.map_map]
      simpa [rankIso, Function.comp_def] using this
    · simp
  · intro σ lam
    show IsOpen (((rbarOf Y σ lam).ker : Subgroup _) : Set (G D.host.E X.nd.Om))
    unfold rbarOf
    split_ifs with h
    · apply Subgroup.isOpen_mono (ssRep_spec _).2.1
      have hc := h.choose_spec.2.choose_spec.choose_spec.2.1
      refine isOpen_ker_mapRep (IsLocalRing.maximalIdeal (X.nd.O h.choose)) ?_ _ ?_ _ hc
      · have := (isAdic_iff.1 (X.nd.O_adic h.choose)).1 1
        simpa using this
      · intro y hy
        rw [RingHom.mem_ker]
        simp [(IsLocalRing.residue_eq_zero_iff y).2 hy]
    · simp [MonoidHom.ker_one]
  · intro i k v hk
    obtain ⟨u, hu, he⟩ := hchi i k v hk
    rcases hu with rfl | rfl
    · exact Or.inl he
    · exact Or.inr he
  · intro i σ Sig hP hcsd hinf
    have hg : BcGood D Rw σ Sig := ⟨fun p hp => ⟨(hP.1 p hp).1, (hP.1 p hp).2, hcsd p hp, hinf p hp⟩, hP.2.1,
      fun w hw => (hP.2.2 w hw).trans (hloc i σ w)⟩
    have hex : ∃ Sig, BcGood D Rw σ Sig := ⟨Sig, hg⟩
    show bcOf D Rw σ = _
    unfold bcOf
    rw [dite_eq_left hex]
    have h0 := hex.choose_spec
    refine hBU _ _ (fun p hp => ?_) h0.2.1 hg.2.1 (fun w hw => (h0.2.2 w hw).trans (hg.2.2 w hw).symm)
    rcases List.mem_append.1 hp with hp | hp
    · exact h0.1 p hp
    · exact hg.1 p hp
  · intro i σ Sig ρ hP hR
    refine ⟨?_, rbar_tie_at D Rw Pl X Y hCheb hloc hplB i σ Sig ρ hP hR⟩
    exact isSSRep_rbarOf Y σ (X.nd.w i)
  · intro i σ'
    show mtParOf Y (X.nd.mu i) (X.nd.j i) σ' = mtSup Y i σ'
    have hex : ∃ i', X.nd.mu i' = X.nd.mu i ∧ X.nd.j i' = X.nd.j i := ⟨i, rfl, rfl⟩
    unfold mtParOf
    rw [dite_eq_left hex]
    exact castMt_eq _ _ _ _ (hMt _ _ σ' hex.choose_spec.1 hex.choose_spec.2)
  · exact fun σ lam => isSSRep_rbarOf Y σ lam

end GlobalTheory.HeightCounting

end
