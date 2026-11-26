module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.SecondProjWeightVectorZero

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.FirstProjMkVecEqMulVec
noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

variable {D : D7}

theorem hEmb_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {r k : ℕ} (M : Matrix (Fin k) (Fin k) A) :
    (hEmb r M).map f = hEmb r (M.map f) := by
  unfold hEmb midEmb
  simp only [Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero f), Matrix.map_one _ (map_zero f) (map_one f)]

section Vec

variable (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (Idx D.R.rS D.R.k) (FpX X p))

def mkVec (w : Idx D.R.rS D.R.k → FpX X p) : Fin X.B.I.n → TpX X p :=
  fun m => θ.symm (((Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ w) ((idxEquiv X) m), 0)

theorem firstProj_mkVec_eq_mulVec (w : Idx D.R.rS D.R.k → FpX X p) :
    pr1 θ (mkVec X p θ Q w) ∘ (idxEquiv X).symm = (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ w := by
  funext i
  simp [pr1, mkVec]

theorem secondProj_mkVec_zero (w : Idx D.R.rS D.R.k → FpX X p) : pr2 θ (mkVec X p θ Q w) = 0 := by
  funext m
  simp [pr2, mkVec]

theorem crd_mkVec (w : Idx D.R.rS D.R.k → FpX X p) : crd X p θ Q (mkVec X p θ Q w) = w := by
  unfold crd
  rw [firstProj_mkVec_eq_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem eq_of_crd (v w : Fin X.B.I.n → TpX X p) (h1 : crd X p θ Q v = crd X p θ Q w) (h2 : pr2 θ v = pr2 θ w) :
    v = w := by
  have h3 : pr1 θ v ∘ (idxEquiv X).symm = pr1 θ w ∘ (idxEquiv X).symm := by
    have := congrArg (fun x => (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ x) h1
    simpa [crd, Matrix.mulVec_mulVec] using this
  funext m
  apply θ.injective
  have hm := congrFun h3 (idxEquiv X m)
  have hm2 := congrFun h2 m
  simp only [Function.comp_apply, Equiv.symm_apply_apply] at hm
  simp only [pr1, pr2] at hm hm2
  exact Prod.ext hm hm2

theorem oep_int (hL : LatBasis X p θ (reindex₂ X p Q)) (t : TpX X p) (ht : t ∈ OEp X p) :
    (θ t).1 ∈ p.1.adicCompletionIntegers X.B.I.F := by
  have hk : Nonempty (Idx D.R.rS D.R.k) := by
    have hn := imA_n_pos X
    rw [← card_idx X] at hn
    exact Fintype.card_pos_iff.1 hn
  obtain ⟨s0⟩ := hk
  set μ := mkVec X p θ Q (Pi.single s0 1) with hμ
  have hμL : μ ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    refine lat_of_crd X p θ Q hL μ (secondProj_mkVec_zero X p θ Q _) fun s => ?_
    rw [crd_mkVec]
    by_cases hs : s = s0
    · subst hs; simp
    · simp [Pi.single_apply, hs]
  have h2 := crd_int_of_lat X p θ Q hL _ (imA_lat_OEp X p ht hμL) s0
  rw [crd_smul, crd_mkVec] at h2
  simpa using h2

end Vec

end PIW.MassDataColumns
end
end

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

variable {D : D7}

def InG (X : HidaSetting D) (p : TypX X) (z : FpX X p) : Prop :=
  ∃ y : p.1.adicCompletionIntegers X.B.I.F, z = ((gOf p : ℕ) : FpX X p) * (y : FpX X p)

theorem inG_add {X : HidaSetting D} {p : TypX X} {a b : FpX X p} (ha : InG X p a) (hb : InG X p b) : InG X p (a + b) := by
  obtain ⟨y1, rfl⟩ := ha
  obtain ⟨y2, rfl⟩ := hb
  exact ⟨y1 + y2, by push_cast; ring⟩

theorem inG_sub {X : HidaSetting D} {p : TypX X} {a b : FpX X p} (ha : InG X p a) (hb : InG X p b) : InG X p (a - b) := by
  obtain ⟨y1, rfl⟩ := ha
  obtain ⟨y2, rfl⟩ := hb
  exact ⟨y1 - y2, by push_cast; ring⟩

theorem inG_zero {X : HidaSetting D} {p : TypX X} : InG X p 0 := ⟨0, by simp⟩

theorem inG_mul_int {X : HidaSetting D} {p : TypX X} {a : FpX X p} (c : FpX X p)
    (hc : c ∈ p.1.adicCompletionIntegers X.B.I.F) (ha : InG X p a) : InG X p (c * a) := by
  obtain ⟨y, rfl⟩ := ha
  exact ⟨⟨c, hc⟩ * y, by push_cast; ring⟩

theorem inG_g_mul {X : HidaSetting D} {p : TypX X} (y : p.1.adicCompletionIntegers X.B.I.F) :
    InG X p (((gOf p : ℕ) : FpX X p) * (y : FpX X p)) := ⟨y, rfl⟩

theorem inG_sum {X : HidaSetting D} {p : TypX X} {ι : Type} (s : Finset ι) (f : ι → FpX X p)
    (h : ∀ i ∈ s, InG X p (f i)) : InG X p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (inG_zero (X := X) (p := p))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inG_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

section Span

variable (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
  (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (Q : GL (Idx D.R.rS D.R.k) (FpX X p))

theorem unipotent_fixes_basisVector (b : Fin D.R.rS) :
    ((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (xuP X hb u p) : GL (Fin X.B.I.n) (TpX X p)) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)) *ᵥ
        ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.eX b)) =
      ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.eX b)) := by
  have h1 := vecV_fmat X hb p (X.xu u) (Formalism.L2.SG.HidaSetting.incl X.B.I (crdOf X.B.I X.ιE X.bas (X.eX b)))
  rw [(X.xu_fix u b).1, vecV_incl] at h1
  exact h1.symm

theorem span_coord (hLB : LatBasis X p θ (reindex₂ X p Q))
    (hy1 : ∀ s, ¬ IsW s → ((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ
        (pr1 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ∘ (idxEquiv X).symm) =
          (Pi.single s (1 : FpX X p) : Idx D.R.rS D.R.k → FpX X p))
    (hW : WClause X hb u p θ Q) (i j : Fin D.R.k) (hij : i ≤ j) (a : Fin X.B.I.n → TpX X p)
    (ha : a ∈ Submodule.span (p.1.adicCompletionIntegers X.B.I.F)
      {w | ∃ t ∈ OEp X p, ∃ s ∈ (Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) ∪
        (fun j' => PI.FinKW.vecV X.B.I p.1 (X.bw j')) '' {j' | j'.1 < i.1}, w = t • s}) :
    InG X p (crd X p θ Q (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (xuP X hb u p) :
      GL (Fin X.B.I.n) (TpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)) *ᵥ a) (wI j)) := by
  set A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p) :=
    ((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (xuP X hb u p) : GL (Fin X.B.I.n) (TpX X p)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)) with hA
  have hAK : HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (xuP X hb u p) ∈
      Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := unipotent_mem_localStabilizer X hb u p

  have hgen : ∀ s ∈ (Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) ∪
      (fun j' => PI.FinKW.vecV X.B.I p.1 (X.bw j')) '' {j' | j'.1 < i.1},
      InG X p (crd X p θ Q (A *ᵥ s) (wI j)) := by
    rintro s (⟨b, rfl⟩ | ⟨j', hj', rfl⟩)
    · have hd : PI.FinKW.vecV X.B.I p.1 (X.e0 b) - ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.eX b)) ∈
          gLam X p := by
        rw [← vecV_incl, ← MassDataIdxSteps.imA_vecV_sub]
        exact loc_of_InAt X p _ (X.basisApprox b).1
      have hsplit : A *ᵥ PI.FinKW.vecV X.B.I p.1 (X.e0 b) =
          A *ᵥ (PI.FinKW.vecV X.B.I p.1 (X.e0 b) - ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.eX b))) +
            ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.eX b)) := by
        rw [Matrix.mulVec_sub, hA, unipotent_fixes_basisVector X hb u p b]
        abel
      rw [hsplit, crd_add, Pi.add_apply]
      have he : crd X p θ Q (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.eX b))) =
          Pi.single (Sum.inl b) 1 := hy1 (Sum.inl b) (not_isW_inl b)
      rw [he]
      have h0 : (Pi.single (Sum.inl b) (1 : FpX X p) : Idx D.R.rS D.R.k → FpX X p) (wI j) = 0 := by
        simp [Pi.single_apply, wI]
      rw [h0, add_zero]
      obtain ⟨y, hy⟩ := crd_gLam X p θ Q hLB _ (kloc_gLam X p _ hAK _ hd) (wI j)
      exact ⟨y, hy⟩
    · obtain ⟨c, hc⟩ := coords_weight_vector X hb u p θ Q hW j'
      have hne : j' ≠ j := by
        intro e
        subst e
        exact absurd hij (not_le.2 hj')
      rw [show A *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw j') = _ from rfl, hc]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have h0 : (Pi.single (wI j') (1 : FpX X p) : Idx D.R.rS D.R.k → FpX X p) (wI j) = 0 := by
        simp [Pi.single_apply, wI, hne.symm]
      rw [h0, zero_sub]
      exact ⟨-c (wI j), by push_cast; ring⟩
  induction ha using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨t, ht, s, hs, rfl⟩ := hw
    rw [Matrix.mulVec_smul, crd_smul, Pi.smul_apply, smul_eq_mul]
    exact inG_mul_int _ (oep_int X p θ Q hLB t ht) (hgen s hs)
  | zero =>
    rw [Matrix.mulVec_zero, crd_zero]
    exact inG_zero
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add, crd_add, Pi.add_apply]
    exact inG_add hx hy
  | smul c x _ hx =>
    rw [Matrix.mulVec_smul, crd_osmul, Pi.smul_apply, smul_eq_mul]
    exact inG_mul_int _ c.2 hx

end Span

end PIW.MassDataColumns
