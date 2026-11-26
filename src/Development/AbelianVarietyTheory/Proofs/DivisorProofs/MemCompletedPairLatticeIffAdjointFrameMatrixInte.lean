module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLatOfIsIntMAdjConjHalf
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ConjLatAdj

section General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT _root_.Formalism.L2.Pj
  IsDedekindDomain NumberField Matrix GlobalTheory.LatVac GlobalTheory.AdelicLatMove GlobalTheory.PlaceVec GlobalTheory.DatumFourier

variable {D : D7}

theorem tie_mul_inv_mem {Q : HeightOneSpectrum (𝓞 D.host.E)} {f : AE D} (hf : GlobalTheory.IdemSupport.Comparison₂ Q f)
    (hQ : FractionalIdeal.count D.host.E Q D.host.AA = 0) {c : D.host.E} (hc : c ∈ D.host.AA⁻¹) :
    toEAf D (f * incA D c) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have h0 : FractionalIdeal.count D.host.E Q D.host.AA⁻¹ = 0 := by
    rw [FractionalIdeal.count_inv, hQ, neg_zero]
  obtain ⟨b, t, ht, hbc⟩ := GlobalTheory.exists_den_not_mem_of_count_eq_zero Q _ h0 hc
  have ht0 : t ≠ 0 := fun h => ht (h ▸ Q.asIdeal.zero_mem)
  have ht0' : (t : D.host.E) ≠ 0 := by simpa using ht0
  have h1 : finPart D (f * incA D ((t : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h; exact ht ((hf t ht0).2 h)
  have h2 := mul_mem (GlobalTheory.IdemIntegral.toEAf_mem_of_finPart h1) (GlobalTheory.IdemIntegral.eToEAf_int D b)
  have e : c = (t : D.host.E)⁻¹ * (b : D.host.E) := by
    rw [eq_inv_mul_iff_mul_eq₀ ht0']
    exact hbc
  rw [e, map_mul (incA D), ← mul_assoc, map_mul (toEAf D)]
  exact h2

theorem toEAf_cA_idem_mul_inv_mem {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (hP : GlobalTheory.ExportSeries.PlacesOK Pg Q)
    {c : D.host.E} (hc : c ∈ D.host.AA⁻¹) :
    toEAf D (cA D (GlobalTheory.ExportSeries.idem Pg) * incA D c) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨P, h1, -, hsp⟩ := hP.split
  have hS : GlobalTheory.ExportSeries.SplitSet Pg := hsp.mono h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.ExportSeries.idem, map_sum, Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => ?_
  have ht : GlobalTheory.IdemSupport.Comparison₂ PP (GlobalTheory.ExportSeries.idemAt PP) := (hS.isIdemAt hPP).2
  refine tie_mul_inv_mem ht.conj ?_ hc
  exact hP.prime PP (Or.inl hPP) _ (Or.inr ((GlobalTheory.IdemSupport.isConjPl_iff PP _).2 rfl))


set_option maxHeartbeats 4000000 in
theorem mem_latO_of_adj_int {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (hP : GlobalTheory.ExportSeries.PlacesOK Pg Q) {x : WO S T}
    (hx : IsHalf (cA D (GlobalTheory.ExportSeries.idem Pg)) x) (hi : IsIntM (frMapAdj S T βS βT x)) :
    x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  set e : AE D := GlobalTheory.ExportSeries.idem Pg with he_def
  have he : IsIdemSum e Pg := by
    obtain ⟨P, h1, -, hsp⟩ := hP.split
    exact (hsp.mono h1).isIdemSum
  obtain ⟨L, pa, pc, hpa, hpc, hac⟩ := GlobalTheory.HostAAPartition.host_AA_partition D
  have hpc' : ∀ l, pc l ∈ D.host.AA⁻¹ := fun l => by
    refine (FractionalIdeal.mem_inv_iff (GlobalTheory.HostAAPartition.host_AA_ne_zero D)).2 fun y hy => ?_
    obtain ⟨b, hb⟩ := hpc l y hy
    exact (FractionalIdeal.mem_one_iff _).2 ⟨b, hb⟩
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D S ΛS hS
  obtain ⟨m, t, t', ht, htt⟩ := GlobalTheory.LatVacDual.dualFamily D T ΛT hT
  obtain ⟨s₁, hs₁⟩ : ∃ A : Matrix (Fin S.rank) (Fin n) D.host.E, A = Matrix.of fun a k => s k a := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ A : Matrix (Fin S.rank) (Fin n) D.host.E, A = Matrix.of fun a k => s' k a := ⟨_, rfl⟩
  obtain ⟨t₁, ht₁⟩ : ∃ A : Matrix (Fin T.rank) (Fin m) D.host.E, A = Matrix.of fun a k => t k a := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂⟩ : ∃ A : Matrix (Fin T.rank) (Fin m) D.host.E, A = Matrix.of fun a k => t' k a := ⟨_, rfl⟩
  have e1 : s₁ * (s₂ᴴ * S.gram) = 1 := by
    subst hs₁ hs₂
    exact Matrix.ext fun a j => (hss a j).trans (Matrix.one_apply).symm
  have e2 : t₁ * (t₂ᴴ * T.gram) = 1 := by
    subst ht₁ ht₂
    exact Matrix.ext fun a j => (htt a j).trans (Matrix.one_apply).symm
  obtain ⟨w, hw⟩ : ∃ w : Matrix (Fin m) (Fin n) (AE D), w = (t₂ᴴ * T.gram).map (incA D) * x * s₁.map (incA D) := ⟨_, rfl⟩
  have hx' : cA D e • x = x := Matrix.ext hx
  have hw1 : cA D e • w = w := by rw [hw, ← Matrix.smul_mul, ← Matrix.mul_smul, hx']
  have hG : T.gramᴴ = T.gram := Matrix.ext fun i j => gram_star T j i
  have hw2 : ((w.map (toEAf D)).map (cF D))ᵀ = (s₁ᴴ * S.gram).map (eToEAf D) * βS.val * frMapAdj S T βS βT x *
      ((βT⁻¹).val * t₂.map (eToEAf D)) := by
    rw [hw, Matrix.map_mul (f := toEAf D), Matrix.map_mul (f := toEAf D), Matrix.map_mul (f := cF D),
      Matrix.map_mul (f := cF D), Matrix.transpose_mul,
      Matrix.transpose_mul, conj_map, conj_map, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
      frMapAdj_eq, Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc βS.val, Units.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc βT.val, Units.mul_inv, Matrix.one_mul,
      ← Matrix.mul_assoc (S.gram.map (eToEAf D)), gram_map_mul_inv, Matrix.one_mul]
  have hcol : ∀ a, (fun k => βS.val k a) ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS := fun a => by
    refine (fS _).2 fun i => ?_
    have e : ((βS⁻¹).val *ᵥ fun k => βS.val k a) i = ((βS⁻¹).val * βS.val) i a := rfl
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have i1 : IsIntM ((s₁ᴴ * S.gram).map (eToEAf D) * βS.val) := fun k a => by
    refine GlobalTheory.PairIntegral.sum_mem_intAf ΛS (fun j => (s₁ᴴ * S.gram) k j) (fun y hy => ?_) _ (hcol a)
    obtain ⟨b, hb⟩ := (hS.2 y).1 hy _ (hs k).1
    refine ⟨b, hb.trans ?_⟩
    rw [Finset.sum_comm, hs₁]
    exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
  have i2 : IsIntM ((βT⁻¹).val * t₂.map (eToEAf D)) := fun a k => by
    rw [ht₂]
    exact (fT _).1 (pure_mem_hatL ΛT 1 (one_mem _) _ (ht k).2) a
  have hwe : ∀ i k, cA D e * w i k = w i k := fun i k => congrFun (congrFun hw1 i) k
  have hw3 : ∀ i k l, toEAf D (w i k * incA D (pc l)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun i k l => by
    have h1 : cF D (toEAf D (w i k)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [show cF D (toEAf D (w i k)) = _ from congrFun (congrFun hw2 k) i, Matrix.mul_apply]
      refine sum_mem fun p _ => mul_mem ?_ (i2 p i)
      rw [Matrix.mul_apply]
      exact sum_mem fun q _ => mul_mem (i1 k q) (hi q p)
    have h2 : toEAf D (w i k) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      have := cF_mem_int h1
      rwa [cF_cF_toEAf] at this
    rw [← hwe i k, mul_comm (cA D e) (w i k), mul_assoc, RingHom.map_mul]
    exact mul_mem h2 (toEAf_cA_idem_mul_inv_mem hP (hpc' l))
  have hxw : x = t₁.map (incA D) * w * (s₂ᴴ * S.gram).map (incA D) := by
    rw [hw, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, e2, Matrix.mul_assoc, ← Matrix.map_mul, e1,
      Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _),
      Matrix.one_mul, Matrix.mul_one]
  have hsum : x = ∑ k, ∑ i, ∑ l, (w i k * incA D (pc l)) • finTens 1 (genMap S T (pa l) (s' k) (t i)) := by
    rw [hxw]
    ext a j
    simp only [Matrix.mul_apply (M := t₁.map (incA D) * w), Matrix.mul_apply (M := t₁.map (incA D)), Matrix.sum_apply,
      Finset.sum_mul, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    have h0 : infPart D (w i k) = 0 := by
      rw [← hwe i k, RingHom.map_mul, infPart_cA (idemSum_infPart he), zero_mul]
    have hterm : ∀ l, (w i k * incA D (pc l)) * finTens 1 (genMap S T (pa l) (s' k) (t i)) a j =
        w i k * incA D (pc l * pa l * (t₁ a i * (s₂ᴴ * S.gram) k j)) := fun l => by
      have h4 : finPart D (finTens 1 (genMap S T (pa l) (s' k) (t i)) a j) =
          finPart D (incA D (pa l * t₁ a i * (s₂ᴴ * S.gram) k j)) := by
        rw [ht₁, hs₂]; rfl
      refine GlobalTheory.SplitScalar.adele_ext (by simp only [RingHom.map_mul, h0, zero_mul]) ?_
      rw [RingHom.map_mul, RingHom.map_mul, h4, ← RingHom.map_mul, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul (incA D)]
      congr 3
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl fun l _ => hterm l, ← Finset.mul_sum, ← map_sum, ← Finset.sum_mul]
    have hac' : ∑ l, pc l * pa l = 1 := by rw [← hac]; exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [hac', one_mul, Matrix.map_apply, Matrix.map_apply, mul_comm (incA D (t₁ a i)), mul_assoc, ← RingHom.map_mul]
  rw [hsum]
  exact sum_mem fun k _ => sum_mem fun i _ => sum_mem fun l _ =>
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_mem_intAE (hw3 i k l)) _
      (finTens_mem_latO (one_mem_intAf _) (AddSubgroup.subset_closure ⟨_, hpa l, _, (hs k).2, _, (ht i).1, rfl⟩))

end General

end GlobalTheory.ConjLatAdj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedPairLatticeIffAdjointFrameMatrixInte
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.QHalfLat

variable {D : D7}
open scoped Matrix

theorem frMapAdj_gen {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {c : AE D} {α : Af D.host.F}
    (hα : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {a : D.host.E} (hca : toEAf D (c * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {s : Fin S.rank → D.host.E} (hs : s ∈ ΛS) {t : Fin T.rank → D.host.E} (ht : t ∈ ΛT) :
    IsIntM (frMapAdj S T βS βT (c • GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t))) := by
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.ConjHalfInt.map_gen, GlobalTheory.ConjHalfInt.adj_shape, Matrix.mul_smul, Matrix.smul_mul]
  refine GlobalTheory.ConjHalfInt.isIntM_smul (GlobalTheory.PlaceVec.cF_mem_int (mul_mem hca hα)) ?_
  have hA : (S.gram⁻¹).map (eToEAf D) *
      ((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
      Matrix.of fun m (_ : Fin 1) => eToEAf D (s m) := by
    ext m z
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, GlobalTheory.ConjHalfInt.cF_eToEAf,
      ← map_mul, ← map_sum]
    rw [GlobalTheory.ConjHalfInt.gram_inv_star]
  have hB : ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ * T.gram.map (eToEAf D) =
      Matrix.of fun (_ : Fin 1) m => eToEAf D (∑ l, star (t l) * T.gram l m) := by
    ext z m
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, GlobalTheory.ConjHalfInt.cF_eToEAf,
      ← map_mul, ← map_sum]
  have e : (βS⁻¹).val * (S.gram⁻¹).map (eToEAf D) *
      (((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ *
        ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ) *
      (T.gram.map (eToEAf D) * βT.val) =
      ((βS⁻¹).val * ((S.gram⁻¹).map (eToEAf D) *
        ((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ)) *
      ((((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ * T.gram.map (eToEAf D)) *
        βT.val) := by
    simp only [Matrix.mul_assoc]
  rw [e, hA, hB]
  exact GlobalTheory.ConjHalfInt.isIntM_mul (GlobalTheory.ConjHalfInt.frame_col_int fS hs) (GlobalTheory.ConjHalfInt.pair_row_int hT fT ht)

theorem isIntM_adj_of_mem {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {c : AE D} (hc : ∀ a ∈ D.host.AA, toEAf D (c * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {x : WO S T} (hx : IsHalf c x)
    (hl : x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    IsIntM (frMapAdj S T βS βT x) := by
  have hx' : c • x = x := Matrix.ext hx
  rw [← hx']
  refine GlobalTheory.LatVac.latO_induction (p := fun u => IsIntM (frMapAdj S T βS βT (c • u))) ?_ ?_ ?_ ?_ hl
  · intro α hα M hM
    have hα' : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      exact frMapAdj_gen hS hT fS fT hα' (hc a ha) hs ht
    | zero =>
      rw [GlobalTheory.LatVac.finTens_zero, smul_zero, GlobalTheory.ConjHalfInt.frMapAdj_zero]
      exact fun _ _ => zero_mem _
    | add M N _ _ hM hN =>
      rw [GlobalTheory.LatVac.finTens_add, smul_add, GlobalTheory.PlaceVec.frMapAdj_add]
      exact fun i j => add_mem (hM i j) (hN i j)
    | neg M _ hM =>
      rw [GlobalTheory.LatVac.finTens_neg, smul_neg, GlobalTheory.ConjHalfInt.frMapAdj_neg]
      exact fun i j => neg_mem (hM i j)
  · rw [smul_zero, GlobalTheory.ConjHalfInt.frMapAdj_zero]
    exact fun _ _ => zero_mem _
  · intro u v hu hv
    rw [smul_add, GlobalTheory.PlaceVec.frMapAdj_add]
    exact fun i j => add_mem (hu i j) (hv i j)
  · intro u hu
    rw [smul_neg, GlobalTheory.ConjHalfInt.frMapAdj_neg]
    exact fun i j => neg_mem (hu i j)

theorem placesOK_of {e : AE D} {Q : Finset (Pl D.host.E)} (he : IsIdemSum e Q)
    (hQ : ∀ PP ∈ Q, ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) : GlobalTheory.ExportSeries.PlacesOK Q ∅ := by
  refine ⟨⟨Q, subset_rfl, Finset.empty_subset _, (⟨e, he⟩ : ∃ e : AE D, IsIdemSum e Q)⟩, Finset.disjoint_empty_right _, ?_⟩
  rintro PP (hPP | hPP) PP' hPP'
  · rcases hPP' with rfl | hc
    · exact GlobalTheory.HalfCompare.primeToAA_of_not_mem (hQ _ hPP)
    · rw [(GlobalTheory.IdemSupport.isConjPl_iff PP PP').1 hc]
      refine GlobalTheory.HalfCompare.primeToAA_of_not_mem ?_
      rw [GlobalTheory.IdemSupport.mem_cP, map_natCast]
      exact hQ PP hPP
  · simp at hPP

end GlobalTheory.QHalfLat


open GlobalTheory.QHalfLat in
theorem GlobalTheory.QHalfLat.isIntM_adj_iff_mem_latP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ t : WO (Vc D i) (Wc D i), IsHalf (cA D eQ) t → (IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (t)) ↔ t ∈ lattice₂ R i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i _ Q hQt eQ he t ht
  have hSV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have hSW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  obtain ⟨cV, hBV⟩ := hC.lev.βV i
  obtain ⟨cW, hBW⟩ := hC.lev.βW i
  have hFV : Formalism.L2.DIV.IsFrame (R.βV i) (R.ΛV i) := hBV.1
  have hFW : Formalism.L2.DIV.IsFrame (R.βW i) (R.ΛW i) := hBW.1
  obtain ⟨t0, ht0⟩ := hQt
  have hbad : ∀ PP ∈ Q, ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal :=
    fun PP hPP => hG.2 t0 PP (ht0 hPP)
  have hP := placesOK_of he hbad
  have hid : GlobalTheory.ExportSeries.idem Q = eQ :=
    GlobalTheory.DatumFourier.idemSum_unique (Vc D i) he (show GlobalTheory.ExportSeries.SplitSet Q from ⟨eQ, he⟩).isIdemSum
  have ht' : IsHalf (cA D (GlobalTheory.ExportSeries.idem Q)) t := by rw [hid]; exact ht
  constructor
  · intro hi
    exact GlobalTheory.ConjLatAdj.mem_latO_of_adj_int hSV hSW hFV hFW hP ht' hi
  · intro hl
    exact isIntM_adj_of_mem hSV hSW hFV hFW (fun a ha => GlobalTheory.ConjHalfInt.toEAf_cA_idem_mul_mem hP ha) ht' hl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedPairLatticeIffAdjointFrameMatrixInteStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedPairLattice_iff_adjointFrameMatrix_integral_conjHalf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ t : WO (Vc D i) (Wc D i), IsHalf (cA D eQ) t → (IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (t)) ↔ t ∈ lattice₂ R i) := by
  first | exact @GlobalTheory.QHalfLat.isIntM_adj_iff_mem_latP | exact GlobalTheory.QHalfLat.isIntM_adj_iff_mem_latP | (intros; apply GlobalTheory.QHalfLat.isIntM_adj_iff_mem_latP <;> assumption)
end
