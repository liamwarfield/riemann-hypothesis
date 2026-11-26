module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PPieceStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PHtDesc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtSideGoodHolds

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PTotCont
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.totCont_of :
    GlobalTheory.GalV.VFin → DegCont → TotCont := by
  classical
  intro hVF hDC l _ k Ω _ _ _ _ hl X p hp v μ
  haveI := hp
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : Algebra.IsAlgebraic k Ω := IsAlgClosure.isAlgebraic
  have hu : IsUnit (l : Ω) := by
    have h := (map_ne_zero (algebraMap k Ω)).mpr hl
    rw [map_natCast] at h
    exact h.isUnit
  have hfin : ∀ n : ℤ, Module.Finite ℤ_[l] (Hl l (sch.obj (geom Ω p)) n 0) := fun n =>
    (hVF l Ω hu (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) n 0).1
  have hv : ∀ σ, μ (galTot l Ω p σ v) = ∑ n ∈ v.support,
      (μ ∘ₗ DirectSum.lof ℚ_[l] ℤ (fun n => HQ l (sch.obj (geom Ω p)) n 0) n)
        (galHQ l Ω p n 0 σ (v n)) := by
    intro σ
    conv_lhs => rw [← DirectSum.sum_support_of v]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LinearMap.comp_apply]
    congr 1
    exact DirectSum.lmap_lof (fun n => galHQ l Ω p n 0 σ) n (v n)
  simp_rw [hv]
  exact continuous_finsetSum _ fun n _ => hDC l k Ω p inferInstance inferInstance n 0 (hfin n) (v n) _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.EqZeroOfLowBlk
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.Int.Geo

private def blk (k : Type) [Field k] {d : ℕ} (c : Fin d → ℕ) (i : ℕ) : Submodule k (Fin d → k) where
  carrier := {v | ∀ j, c j ≠ i → v j = 0}
  zero_mem' _ _ := rfl
  add_mem' ha hb j h := by simp [ha j h, hb j h]
  smul_mem' r v hv j h := by simp [hv j h]

theorem grSS_of :
    GrHom → SSOfSum → GrSS := by
  intro _ hSS Γ k _ _ d ρ₀ ρ c hJH hρ
  obtain ⟨hinv, hmax⟩ := hJH
  have key : ∀ (g : Γ) (i : ℕ) (u : Fin d → k), u ∈ blk k c i → ∀ a,
      (↑(ρ g) : Matrix (Fin d) (Fin d) k).mulVec u a =
        if c a = i then (↑(ρ₀ g) : Matrix (Fin d) (Fin d) k).mulVec u a else 0 := by
    intro g i u hu a
    simp only [Matrix.mulVec, dotProduct, hρ]
    split_ifs with h
    · refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs with h'
      · rfl
      · simp [hu b (by omega)]
    · refine Finset.sum_eq_zero fun b _ => ?_
      split_ifs with h'
      · simp [hu b (by omega)]
      · simp
  have hblk : ∀ i, IsInv ρ (blk k c i) := by
    intro i g u hu j hj
    rw [key g i u hu j, if_neg hj]
  have hsup : ⨆ i, blk k c i = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun j _ => ?_
    refine Submodule.mem_iSup_of_mem (c j) ?_
    intro a ha
    rw [Pi.single_eq_of_ne]
    rintro rfl
    exact ha rfl
  refine hSS Γ k d ρ (fun i => blk k c i) hblk ?_ hsup
  intro i U hU hUle
  have hlow : low k c i ≤ low k c (i + 1) := fun v hv j hj => hv j (by omega)
  have hblkle : blk k c i ≤ low k c (i + 1) := fun v hv j hj => hv j (by omega)
  have hdisj : ∀ v, v ∈ blk k c i → v ∈ low k c i → v = 0 := by
    intro v h1 h2
    funext j
    by_cases h : c j = i
    · exact h2 j h.ge
    · exact h1 j h
  have hU'inv : IsInv ρ₀ (low k c i ⊔ U) := by
    intro g v hv
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
    rw [Matrix.mulVec_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (hinv i g w hw)) ?_
    have huB := hUle hu
    rw [← sub_add_cancel ((↑(ρ₀ g) : Matrix (Fin d) (Fin d) k).mulVec u)
      ((↑(ρ g) : Matrix (Fin d) (Fin d) k).mulVec u)]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (hU g u hu))
    intro a ha
    rw [Pi.sub_apply, key g i u huB a]
    split_ifs with h
    · exact sub_self _
    · rw [hinv (i + 1) g u (hblkle huB) a (by omega), sub_zero]
  rcases hmax i _ hU'inv le_sup_left (sup_le hlow (hUle.trans hblkle)) with h | h
  · left
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    have hv' : v ∈ low k c i := by
      rw [← h]
      exact Submodule.mem_sup_right hv
    exact hdisj v (hUle hv) hv'
  · right
    apply le_antisymm hUle
    intro v hv
    have hv' : v ∈ low k c i ⊔ U := by
      rw [h]
      exact hblkle hv
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hv'
    have hwB : w ∈ blk k c i := by
      have := Submodule.sub_mem _ hv (hUle hu)
      simpa using this
    rw [hdisj w hwB hw, zero_add]
    exact hu

end UpperTheory.Gal.Int.Geo
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PRelDim
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.relDim_of :
    RelDim := by
  intro k _ X p hp hX
  haveI := hp
  haveI := hX
  haveI : ConnectedSpace X := inferInstance
  exact CrystallineSemistableComparison.exists_smoothOfRelativeDimension p
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PFlagMove
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.flagMove_of :
    FlagMove := by
  intro Γ k _ _ d ρ W P W' hW' hJH
  have hPP : ∀ w : Fin d → k, (↑P : Matrix (Fin d) (Fin d) k).mulVec
      ((↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hPP' : ∀ w : Fin d → k, (↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec
      ((↑P : Matrix (Fin d) (Fin d) k).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hc : ∀ g v, (↑P : Matrix (Fin d) (Fin d) k).mulVec ((↑(cj P ρ g) : Matrix (Fin d) (Fin d) k).mulVec v) =
      (↑(ρ g) : Matrix (Fin d) (Fin d) k).mulVec ((↑P : Matrix (Fin d) (Fin d) k).mulVec v) := by
    intro g v
    rw [cj_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPP]
  refine ⟨fun i g v hv => ?_, fun i U hU h1 h2 => ?_⟩
  · rw [hW', hc]
    exact hJH.1 i g _ ((hW' i v).1 hv)
  · let U0 : Submodule k (Fin d → k) := U.map (Matrix.mulVecLin (↑P : Matrix (Fin d) (Fin d) k))
    have hmem : ∀ v, v ∈ U ↔ (↑P : Matrix (Fin d) (Fin d) k).mulVec v ∈ U0 := by
      intro v
      constructor
      · intro hv
        exact ⟨v, hv, rfl⟩
      · rintro ⟨u, hu, he⟩
        have huv : u = v := by
          have := congrArg (fun w => (↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec w) he
          simpa [Matrix.mulVecLin_apply, hPP'] using this
        exact huv ▸ hu
    have hinv : IsInv ρ U0 := by
      rintro g w ⟨u, hu, rfl⟩
      refine ⟨(↑(cj P ρ g) : Matrix (Fin d) (Fin d) k).mulVec u, hU g u hu, ?_⟩
      simp only [Matrix.mulVecLin_apply]
      exact hc g u
    have hlo : W i ≤ U0 := by
      intro w hw
      refine ⟨(↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec w, h1 ((hW' i _).2 (by rw [hPP]; exact hw)), ?_⟩
      simp only [Matrix.mulVecLin_apply]
      exact hPP w
    have hhi : U0 ≤ W (i + 1) := by
      rintro w ⟨u, hu, rfl⟩
      exact (hW' (i + 1) u).1 (h2 hu)
    rcases hJH.2 i U0 hinv hlo hhi with h | h
    · left
      ext v
      rw [hmem, h, hW']
    · right
      ext v
      rw [hmem, h, hW']
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.POpUniq
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem l_unit (l : ℕ) {k : Type} [Field k] (hl : (l : k) ≠ 0) (Ω : Type) [Field Ω] [Algebra k Ω] :
    IsUnit (l : Γ(G3.sp Ω, ⊤)) := by
  have h1 : (l : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap k Ω)]
    exact (_root_.map_ne_zero _).mpr hl
  have h3 := h1.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  simpa [map_natCast] using h3

theorem UpperTheory.Gal.Int.Geo.opUniq_of :
    G3.HopSpec → G3.OpEx.{1} → G3.OpEt → G3.EtGood → G3.BcSplits → OpUniq := by
  intro hHop hEx hEt hGood hBc l _ k _ hl H Ω _ _ g d hd T hT
  obtain ⟨hhop, -⟩ := hHop l hl H Ω g d hd
  have hsplit : G3.GalSplit (H.sΩ Ω g) := by
    unfold GlobalTheory.GalV.IsCorrOp at hT
    unfold G3.GalSplit
    obtain ⟨W, c, G, i1, i2, a, J, i3, σ, hG, hS, -⟩ := hT
    exact ⟨W, c, G, i1, i2, a, J, i3, σ, hG, hS⟩
  have hgood := hGood l (G3.sp Ω) (l_unit l hl Ω)
  haveI : IsFinite (H.s g) := hd.1
  haveI : Etale (H.s g) := hd.2.1
  have hbc := hBc (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) H.q (H.s g ≫ H.q) H.q (H.s g) rfl
    (𝟙 _) (Category.id_comp _) Empty (fun e => e.elim) (fun e => e.elim)
  haveI : IsFinite (H.sΩ Ω g) := hbc.1
  haveI : Etale (H.sΩ Ω g) := hbc.2.1
  let p : H.geomZ Ω ⟶ G3.sp Ω := pullback.snd H.q (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
  have hcomm : H.tΩ Ω g ≫ p = H.sΩ Ω g ≫ p := by
    simp only [p, HTower.sΩ, HTower.tΩ, HTower.geomZ, geom, geomMap]
    erw [pullback.lift_snd, pullback.lift_snd]
  obtain ⟨A, -, huniq⟩ := (hEx (G3.et l (G3.sp Ω)) hgood p p (H.sΩ Ω g) (H.tΩ Ω g) hcomm).1 hsplit
  have h1 := huniq T ((hEt l p p _ _ hcomm T).mpr hT)
  have h2 := huniq (hop l H Ω g) ((hEt l p p _ _ hcomm _).mpr hhop)
  exact h1.trans h2.symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PHopGal
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem comm_of_conj {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (A G G' : M →ₗ[R] M)
    (h : G ∘ₗ A ∘ₗ G' = A) (hid : G' ∘ₗ G = LinearMap.id) : A ∘ₗ G = G ∘ₗ A := by
  calc A ∘ₗ G = (G ∘ₗ A ∘ₗ G') ∘ₗ G := by rw [h]
    _ = G ∘ₗ A ∘ₗ (G' ∘ₗ G) := by simp only [LinearMap.comp_assoc]
    _ = G ∘ₗ A := by rw [hid, LinearMap.comp_id]

theorem UpperTheory.Gal.Int.Geo.hopGal_of :
    G3.HopSpec → OpConj → OpUniq → HopGal := by
  intro hS hC hU l _ k _ hl H Ω _ _ g d hd σ
  refine comm_of_conj _ _ (galTot l Ω H.q σ⁻¹)
    (hU l k hl H Ω g d hd _ (hC l k H Ω g _ σ (hS l hl H Ω g d hd).1)) ?_
  rw [← GlobalTheory.GalV.galTot_mul, inv_mul_cancel, GlobalTheory.GalV.galTot_one]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PMatEx
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.matEx_of :
    MatEx := by
  intro Γ L _ _ M _ _ a h1 hmul U hU d b
  let f : Γ → (U →ₗ[L] U) := fun g => (a g).restrict (fun x hx => hU g x hx)
  have hfv : ∀ g (x : U), ((f g x : U) : M) = a g (x : M) := fun g x => rfl
  have hf1 : f 1 = LinearMap.id := by
    ext x
    simp [hfv, h1]
  have hfm : ∀ g h, f (g * h) = f g ∘ₗ f h := by
    intro g h
    ext x
    simp [hfv, hmul]
  let φ : Γ →* Matrix (Fin d) (Fin d) L :=
    { toFun := fun g => LinearMap.toMatrix b b (f g)
      map_one' := by
        simp only [hf1, LinearMap.toMatrix_id]
      map_mul' := by
        intro g h
        simp only [hfm]
        exact LinearMap.toMatrix_comp b b b (f g) (f h) }
  let ρ : Γ →* GL (Fin d) L := φ.toHomUnits
  have hρ : ∀ g, ((ρ g : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) = LinearMap.toMatrix b b (f g) :=
    fun g => MonoidHom.coe_toHomUnits φ g
  refine ⟨ρ, ?_, ?_⟩
  · intro g j
    simp only [hρ, LinearMap.toMatrix_apply]
    rw [← hfv]
    have e := congrArg Subtype.val (b.sum_repr (f g (b j)))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e
    exact e.symm
  · intro i j
    obtain ⟨μ, hμ⟩ := LinearMap.exists_extend (b.coord i)
    refine ⟨μ, fun g => ?_⟩
    rw [hρ, LinearMap.toMatrix_apply, ← hfv]
    have hc : μ (U.subtype (f g (b j))) = b.coord i (f g (b j)) := by
      rw [← LinearMap.comp_apply, hμ]
    rw [Module.Basis.coord_apply] at hc
    exact hc.symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.POpConj
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem splits_transport {Z Y W Z' Y' : Scheme.{0}} {J : Type} {s : Y ⟶ Z} {c : W ⟶ Z} {σ : J → (W ⟶ Y)}
    (y : Y ⟶ Y') [IsIso y] (z : Z ⟶ Z') [IsIso z] (s' : Y' ⟶ Z') (hy : y ≫ s' = s ≫ z)
    (h : GlobalTheory.GalV.Splits s c σ) : GlobalTheory.GalV.Splits s' (c ≫ z) (fun j => σ j ≫ y) := by
  obtain ⟨h0, hi⟩ := h
  have h1 : ∀ j, (σ j ≫ y) ≫ s' = c ≫ z := fun j => by
    rw [Category.assoc, hy, ← Category.assoc, h0 j]
  refine ⟨h1, ?_⟩
  have ec : (pullback.fst s c ≫ y) ≫ s' = pullback.snd s c ≫ c ≫ z := by
    rw [Category.assoc, hy, ← Category.assoc, pullback.condition, Category.assoc]
  have ec' : (pullback.fst s' (c ≫ z) ≫ inv y) ≫ s = pullback.snd s' (c ≫ z) ≫ c := by
    rw [← cancel_mono z, Category.assoc, Category.assoc, Category.assoc, ← hy, IsIso.inv_hom_id_assoc,
      pullback.condition]
  let e : pullback s c ⟶ pullback s' (c ≫ z) := pullback.lift _ _ ec
  let e' : pullback s' (c ≫ z) ⟶ pullback s c := pullback.lift _ _ ec'
  have e1 : e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ y := pullback.lift_fst _ _ _
  have e2 : e ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have e1' : e' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ inv y := pullback.lift_fst _ _ _
  have e2' : e' ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have he : IsIso e := by
    refine ⟨e', pullback.hom_ext ?_ ?_, pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc, e1', ← Category.assoc, e1, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, e2', e2, Category.id_comp]
    · rw [Category.assoc, e1, ← Category.assoc, e1', Category.assoc, IsIso.inv_hom_id, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, e2, e2', Category.id_comp]
  have key : (Sigma.desc (fun j => pullback.lift (σ j ≫ y) (𝟙 W) (by rw [h1 j, Category.id_comp])) :
      ∐ (fun _ : J => W) ⟶ pullback s' (c ≫ z)) =
      Sigma.desc (fun j => pullback.lift (σ j) (𝟙 W) (by rw [h0 j, Category.id_comp])) ≫ e := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_desc, Sigma.ι_desc_assoc]
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, e1, pullback.lift_fst_assoc]
    · rw [pullback.lift_snd, Category.assoc, e2, pullback.lift_snd]
  rw [key]
  exact IsIso.comp_isIso

private theorem galMap_geomMap {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y) (hu : u ≫ q = p)
    (σ : Ω ≃ₐ[k] Ω) : galMap Ω p σ ≫ geomMap Ω p u hu = geomMap Ω p u hu ≫ galMap Ω q σ := by
  apply pullback.hom_ext
  · simp only [geomMap, Category.assoc, pullback.lift_fst, galMap_fst, galMap_fst_assoc]
  · simp only [geomMap, Category.assoc, pullback.lift_snd, galMap_snd, galMap_snd_assoc, pullback.lift_snd_assoc]

private theorem galMap_inv_comp {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) (σ : Ω ≃ₐ[k] Ω) : galMap Ω p σ⁻¹ ≫ galMap Ω p σ = 𝟙 _ := by
  rw [← galMap_mul, inv_mul_cancel, galMap_one]

private theorem galMap_isIso {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) (σ : Ω ≃ₐ[k] Ω) : IsIso (galMap Ω p σ) :=
  ⟨galMap Ω p σ⁻¹, by rw [← galMap_mul, mul_inv_cancel, galMap_one], galMap_inv_comp Ω p σ⟩

theorem UpperTheory.Gal.Int.Geo.opConj_of :
    OpConj := by
  rintro l _ k _ H Ω _ _ g T σ ⟨W, c, G, _, _, a, J, _, σj, ⟨hf, he, hsu, h1, hm, hc⟩, hS, hT⟩
  have hz' : IsIso (galMap Ω H.q σ⁻¹) := galMap_isIso Ω H.q σ⁻¹
  have hy' : IsIso (galMap Ω (H.s g ≫ H.q) σ⁻¹) := galMap_isIso Ω _ σ⁻¹
  have hs : galMap Ω (H.s g ≫ H.q) σ⁻¹ ≫ H.sΩ Ω g = H.sΩ Ω g ≫ galMap Ω H.q σ⁻¹ :=
    galMap_geomMap Ω (H.s g) rfl σ⁻¹
  have ht : galMap Ω (H.s g ≫ H.q) σ⁻¹ ≫ H.tΩ Ω g = H.tΩ Ω g ≫ galMap Ω H.q σ⁻¹ :=
    galMap_geomMap Ω (H.t g) (H.comm g) σ⁻¹
  refine ⟨W, c ≫ galMap Ω H.q σ⁻¹, G, inferInstance, inferInstance, a, J, inferInstance,
    fun j => σj j ≫ galMap Ω (H.s g ≫ H.q) σ⁻¹, ⟨inferInstance, inferInstance, inferInstance, h1, hm, ?_⟩,
    splits_transport _ _ _ hs hS, fun x => ?_⟩
  · simpa only [Category.comp_id] using
      splits_transport (𝟙 W) (galMap Ω H.q σ⁻¹) (c ≫ galMap Ω H.q σ⁻¹) (Category.id_comp _) hc
  · have hL : ∀ v, GlobalTheory.GalV.pullTot l (sch.map (c ≫ galMap Ω H.q σ⁻¹)) (galTot l Ω H.q σ v) =
        GlobalTheory.GalV.pullTot l (sch.map c) v := fun v => by
      unfold galTot
      rw [← LinearMap.comp_apply, ← GlobalTheory.GalV.pullTot_comp, ← Functor.map_comp, Category.assoc,
        galMap_inv_comp, Category.comp_id]
    simp only [LinearMap.comp_apply]
    rw [hL, hT]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold galTot
    rw [← LinearMap.comp_apply, ← GlobalTheory.GalV.pullTot_comp, ← Functor.map_comp, Category.assoc, Category.assoc, ht]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PDegFin
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.degFin_of :
    KunnethLefschetz.QDual → CrystallineSemistableComparison.InSum → A9 → KunnethLefschetz.ProjBC → KunnethLefschetz.SumCl → KunnethLefschetz.SumHl → KunnethLefschetz.PiBC → RelDim → CompSum → DegFin := by
  intro hQ hS a9 h1 h2 h5 h6 hR hC l _ k _ _ hk X p hp hproj
  have hprop : IsProper p := h1.2 _ p hproj
  obtain ⟨r, Y, j, hj, hY⟩ := hC k p hp hprop
  have hsm : ∀ s, Smooth (j s ≫ p) := fun s => by
    have := hj.1 s
    infer_instance
  choose d hd using fun s => hR k (j s ≫ p) (hsm s) (hY s)
  have hD : ∀ s, KunnethLefschetz.Dual l (d s) (Y s) := fun s => by
    have := hj.1 s
    have := h2 j hj s
    refine hQ l k hk (d s) (j s ≫ p) ⟨inferInstance, hd s⟩ ?_ (hY s)
    obtain ⟨N, i, hi, e⟩ := hproj
    exact ⟨N, j s ≫ i, inferInstance, by rw [Category.assoc]; exact congrArg (j s ≫ ·) e⟩
  have hb := fun n : ℤ => KunnethLefschetz.sumQ (l := l) h5 h6 hS j hj n
  refine ⟨fun n => ?_, ((2 * Finset.univ.sup d : ℕ) : ℤ), fun n hn => ?_⟩
  · have := fun s => (hD s).1 n
    exact FiniteDimensional.of_injective (LinearMap.pi fun s => LateralTheory.EtaleTrace.pb l (j s) n) (hb n).1
  · rcases hn with hn | hn
    · have hs : ∀ i, Subsingleton (HtL l i (sch.obj X) n 0) := fun i =>
        (a9 (ZMod (l ^ i)) (tw (l ^ i) 0)).1 _ n hn
      have : Subsingleton (Hl l (sch.obj X) n 0) :=
        ⟨fun a b => Subtype.ext (funext fun i => Subsingleton.elim _ _)⟩
      infer_instance
    · refine ⟨fun x y => (hb n).1 (funext fun s => ((hD s).2.1 n ?_).elim _ _)⟩
      have : d s ≤ Finset.univ.sup d := Finset.le_sup (Finset.mem_univ s)
      omega
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PContGL
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.contGL_of :
    ContGL := by
  intro Γ k _ _ _ _ _ _ d ρ
  constructor
  · intro hρ i j
    exact (Units.continuous_val.comp hρ).matrix_elem i j
  · intro h
    have hval : Continuous fun g : Γ => ((ρ g : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) :=
      continuous_matrix h
    rw [Units.continuous_iff]
    refine ⟨hval, ?_⟩
    have hinv : (fun g : Γ => (((ρ g)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k)) =
        fun g => ((ρ g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) := by
      funext g
      rw [map_inv]
    rw [hinv]
    exact hval.comp continuous_inv
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PGrHom
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.grHom_of :
    GrHom := by
  intro Γ k _ _ d ρ₀ c hinv
  have mem : ∀ (i : ℕ) (v : Fin d → k), v ∈ low k c i ↔ ∀ j, i ≤ c j → v j = 0 :=
    fun _ _ => Iff.rfl
  have hbt : ∀ g, (ρ₀ g : Matrix (Fin d) (Fin d) k).BlockTriangular c := by
    intro g i j hij
    have hv : (Pi.single j (1 : k) : Fin d → k) ∈ low k c (c j + 1) := by
      rw [mem]
      intro j' hj'
      by_cases h : j' = j
      · subst h
        omega
      · simp [Pi.single_apply, h]
    have hw := (mem _ _).1 (hinv (c j + 1) g _ hv) i (by omega)
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hw
  let D : Matrix (Fin d) (Fin d) k → Matrix (Fin d) (Fin d) k :=
    fun M => Matrix.of fun i j => if c i = c j then M i j else 0
  have hD : ∀ M i j, D M i j = if c i = c j then M i j else 0 := fun _ _ _ => rfl
  have hmul : ∀ M N : Matrix (Fin d) (Fin d) k, M.BlockTriangular c → N.BlockTriangular c →
      D (M * N) = D M * D N := by
    intro M N hM hN
    ext i j
    simp only [hD, Matrix.mul_apply]
    split_ifs with hij
    · apply Finset.sum_congr rfl
      intro l _
      by_cases h1 : c i = c l
      · rw [if_pos h1, if_pos (h1 ▸ hij)]
      · rw [if_neg h1, zero_mul]
        rcases lt_or_gt_of_ne h1 with h | h
        · rw [hN (show c j < c l by omega), mul_zero]
        · rw [hM h, zero_mul]
    · symm
      apply Finset.sum_eq_zero
      intro l _
      split_ifs with h1 h2 <;> simp_all
  have hone : D 1 = 1 := by
    ext i j
    simp only [hD, Matrix.one_apply]
    split_ifs <;> simp_all
  have hunit : ∀ g h : Γ, D (ρ₀ g) * D (ρ₀ h) = D (ρ₀ (g * h)) := by
    intro g h
    rw [← hmul _ _ (hbt g) (hbt h), map_mul, Units.val_mul]
  refine ⟨hbt, ⟨{ toFun := fun g => ⟨D (ρ₀ g), D (ρ₀ g⁻¹), ?_, ?_⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩⟩
  · rw [hunit, mul_inv_cancel, map_one, Units.val_one, hone]
  · rw [hunit, inv_mul_cancel, map_one, Units.val_one, hone]
  · apply Units.ext
    show D (ρ₀ 1) = 1
    rw [map_one, Units.val_one, hone]
  · intro x y
    apply Units.ext
    show D (ρ₀ (x * y)) = D (ρ₀ x) * D (ρ₀ y)
    rw [hunit]
  · intro g i j
    rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PDegCont
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.degCont_of :
    StabOpen → DegCont := by
  intro hst l _ k Ω _ _ _ _ X p hqc hqs n i hfin v μ
  have habs := LateralTheory.EWeil.AbsContPf.AbsCont_of LateralTheory.EWeil.ChevPf.Chev_of
  have key : ∀ (φ : Hl l (sch.obj (geom Ω p)) n i →ₗ[ℤ_[l]] ℚ_[l]) (x : Hl l (sch.obj (geom Ω p)) n i),
      Continuous fun σ : Gal(Ω/k) => φ (galHl l Ω p n i σ x) := by
    intro φ x
    refine habs l Gal(Ω/k) (Hl l (sch.obj (geom Ω p)) n i) (galHl l Ω p n i)
      (fun m => LinearMap.ker (LateralTheory.EWeil.ContinCut.evk l (sch.obj (geom Ω p)) n i m))
      (LateralTheory.EWeil.ContinCut.evk_anti l _ n i) ?_ ?_ φ x
    · intro y hy
      apply Subtype.ext
      funext m
      simpa [LateralTheory.EWeil.ContinCut.evk] using hy m
    · intro y m
      have hset : {σ : Gal(Ω/k) | (galHl l Ω p n i σ) y - y ∈
          LinearMap.ker (LateralTheory.EWeil.ContinCut.evk l (sch.obj (geom Ω p)) n i m)} =
          {σ | (galHl l Ω p n i σ y).1 m = y.1 m} := by
        ext σ
        simp [LateralTheory.EWeil.ContinCut.evk, sub_eq_zero]
      rw [hset]
      exact hst l k Ω p hqc hqs n i y m
  induction v using TensorProduct.induction_on with
  | zero => simpa using continuous_const
  | tmul q x =>
    have hφ := key ((μ.restrictScalars ℤ_[l]) ∘ₗ (TensorProduct.mk ℤ_[l] ℚ_[l] _ 1)) x
    refine (Continuous.mul (continuous_const : Continuous fun _ : Gal(Ω/k) => q) hφ).congr ?_
    intro σ
    have e : galHQ l Ω p n i σ (q ⊗ₜ x) = q • ((1 : ℚ_[l]) ⊗ₜ (galHl l Ω p n i σ x)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp [GlobalTheory.EtC.galHQ]
    rw [e, map_smul, smul_eq_mul]
    rfl
  | add a b ha hb =>
    exact (ha.add hb).congr fun σ => by simp only [map_add (f := _), Pi.add_apply]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PSSOfSum
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem invariant_sup_alt {Γ k : Type} [Group Γ] [Field k] {d : ℕ} {ρ : Γ →* GL (Fin d) k}
    {U V : Submodule k (Fin d → k)} (hU : IsInv ρ U) (hV : IsInv ρ V) : IsInv ρ (U ⊔ V) := by
  intro g v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  rw [Matrix.mulVec_add]
  exact Submodule.add_mem_sup (hU g a ha) (hV g b hb)

private theorem invariant_inf {Γ k : Type} [Group Γ] [Field k] {d : ℕ} {ρ : Γ →* GL (Fin d) k}
    {U V : Submodule k (Fin d → k)} (hU : IsInv ρ U) (hV : IsInv ρ V) : IsInv ρ (U ⊓ V) := by
  intro g v hv
  exact ⟨hU g v hv.1, hV g v hv.2⟩

private theorem invariant_bot_alt {Γ k : Type} [Group Γ] [Field k] {d : ℕ} (ρ : Γ →* GL (Fin d) k) :
    IsInv ρ (⊥ : Submodule k (Fin d → k)) := by
  intro g v hv
  rw [(Submodule.mem_bot k).1 hv, Matrix.mulVec_zero]
  exact Submodule.zero_mem _

theorem UpperTheory.Gal.Int.Geo.sSOfSum_of :
    SSOfSum := by
  intro Γ k _ _ d ρ B hB hS hT W hW
  obtain ⟨W', ⟨hinv, hdis⟩, hmax⟩ :=
    (wellFounded_gt (α := Submodule k (Fin d → k))).has_min
      {X | IsInv ρ X ∧ Disjoint W X} ⟨⊥, invariant_bot_alt ρ, disjoint_bot_right⟩
  have key : ∀ i, B i ≤ W ⊔ W' := by
    intro i
    rcases hS i (B i ⊓ (W ⊔ W')) (invariant_inf (hB i) (invariant_sup_alt hW hinv)) inf_le_left with h | h
    · have hd : Disjoint W (W' ⊔ B i) := by
        rw [Submodule.disjoint_def]
        intro w hw hw2
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw2
        have h2 : (a + b) + -a ∈ W ⊔ W' := Submodule.add_mem_sup hw (neg_mem ha)
        have h3 : (a + b) + -a = b := by abel
        rw [h3] at h2
        have hbU : b ∈ B i ⊓ (W ⊔ W') := ⟨hb, h2⟩
        rw [h] at hbU
        have hb0 : b = 0 := (Submodule.mem_bot k).1 hbU
        subst hb0
        rw [add_zero] at hw ⊢
        exact Submodule.disjoint_def.1 hdis a hw ha
      have hle : W' ⊔ B i ≤ W' := by
        by_contra hn
        exact hmax _ ⟨invariant_sup_alt hinv (hB i), hd⟩
          (lt_of_le_not_ge le_sup_left hn)
      exact (le_sup_right.trans hle).trans le_sup_right
    · exact inf_eq_left.1 h
  refine ⟨W', hinv, hdis, codisjoint_iff.2 ?_⟩
  exact top_le_iff.1 (hT ▸ iSup_le key)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PFlagEx
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem inv_top {Γ k : Type} [Group Γ] [Field k] {d : ℕ} (ρ : Γ →* GL (Fin d) k) :
    IsInv ρ (⊤ : Submodule k (Fin d → k)) := by
  intro g v _
  exact Submodule.mem_top

private theorem inv_bot {Γ k : Type} [Group Γ] [Field k] {d : ℕ} (ρ : Γ →* GL (Fin d) k) :
    IsInv ρ (⊥ : Submodule k (Fin d → k)) := by
  intro g v hv
  rw [Submodule.mem_bot] at hv ⊢
  subst hv
  exact Matrix.mulVec_zero _

private theorem flag_step {Γ k : Type} [Group Γ] [Field k] {d : ℕ} (ρ : Γ →* GL (Fin d) k)
    (W : Submodule k (Fin d → k)) (hW : IsInv ρ W) :
    ∃ W' : Submodule k (Fin d → k), IsInv ρ W' ∧ W ≤ W' ∧ (W ≠ ⊤ → W < W') ∧
      ∀ U, IsInv ρ U → W ≤ U → U ≤ W' → U = W ∨ U = W' := by
  by_cases h : W = ⊤
  · subst h
    exact ⟨⊤, hW, le_rfl, fun h => (h rfl).elim, fun U _ h1 h2 => Or.inl (le_antisymm h2 h1)⟩
  · have hne : {U : Submodule k (Fin d → k) | IsInv ρ U ∧ W < U}.Nonempty :=
      ⟨⊤, inv_top ρ, lt_top_iff_ne_top.2 h⟩
    obtain ⟨M, ⟨hMi, hMl⟩, hmin⟩ :=
      (wellFounded_lt (α := Submodule k (Fin d → k))).has_min _ hne
    refine ⟨M, hMi, hMl.le, fun _ => hMl, fun U hU h1 h2 => ?_⟩
    rcases eq_or_lt_of_le h1 with e | l
    · exact Or.inl e.symm
    · rcases eq_or_lt_of_le h2 with e | l2
      · exact Or.inr e
      · exact (hmin U ⟨hU, l⟩ l2).elim

theorem UpperTheory.Gal.Int.Geo.flagEx_of :
    FlagEx := by
  intro Γ k _ _ d ρ
  choose f hf using
    (fun (W : {W : Submodule k (Fin d → k) // IsInv ρ W}) => flag_step ρ W.1 W.2)
  let S : ℕ → {W : Submodule k (Fin d → k) // IsInv ρ W} :=
    fun i => Nat.rec ⟨⊥, inv_bot ρ⟩ (fun _ w => ⟨f w, (hf w).1⟩) i
  have key : ∀ i, (S i).1 = ⊤ ∨ i ≤ Module.finrank k (S i).1 := by
    intro i
    induction i with
    | zero => exact Or.inr (Nat.zero_le _)
    | succ n ih =>
      by_cases ht : (S n).1 = ⊤
      · left
        have h1 : (S n).1 ≤ (S (n + 1)).1 := (hf (S n)).2.1
        rw [ht] at h1
        exact top_le_iff.1 h1
      · right
        have hlt : (S n).1 < (S (n + 1)).1 := (hf (S n)).2.2.1 ht
        have h2 := Submodule.finrank_lt_finrank_of_lt hlt
        rcases ih with h | h
        · exact absurd h ht
        · omega
  refine ⟨fun i => (S i).1, monotone_nat_of_le_succ fun i => (hf (S i)).2.1, rfl, ?_,
    fun i => (S i).2, fun i U hU h1 h2 => (hf (S i)).2.2.2 U hU h1 h2⟩
  rcases key d with h | h
  · exact h
  · apply Submodule.eq_top_of_finrank_eq
    have h3 := Submodule.finrank_le (S d).1
    simp only [Module.finrank_fin_fun] at h3 ⊢
    omega
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PMatConj
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem conj_basis {L : Type} [Field L] {M : Type*} [AddCommGroup M] [Module L M]
    (U : Submodule L M) {d : ℕ} (b : Module.Basis (Fin d) L U) (P : GL (Fin d) L) :
    ∃ b' : Module.Basis (Fin d) L U,
      ∀ j, (b' j).1 = ∑ i, (P : Matrix (Fin d) (Fin d) L) i j • (b i).1 := by
  have h1 : (P : Matrix (Fin d) (Fin d) L) * ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) * (P : Matrix (Fin d) (Fin d) L) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let e : U ≃ₗ[L] U := LinearEquiv.ofLinear (Matrix.toLin b b (P : Matrix (Fin d) (Fin d) L))
    (Matrix.toLin b b ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L))
    (by rw [← Matrix.toLin_mul b b b, h1, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul b b b, h2, Matrix.toLin_one])
  refine ⟨b.map e, fun j => ?_⟩
  have h : e (b j) = ∑ i, (P : Matrix (Fin d) (Fin d) L) i j • b i :=
    Matrix.toLin_self b b _ j
  simp [h]

private theorem conj_mat {L : Type} [Field L] {M : Type*} [AddCommGroup M] [Module L M]
    (f : M →ₗ[L] M) {d : ℕ} (x y : Fin d → M) (A P Q : Matrix (Fin d) (Fin d) L) (hPQ : P * Q = 1)
    (hx : ∀ j, f (x j) = ∑ i, A i j • x i) (hy : ∀ j, y j = ∑ i, P i j • x i) (j : Fin d) :
    f (y j) = ∑ i, (Q * A * P) i j • y i := by
  have key : ∀ (B : Matrix (Fin d) (Fin d) L) (j : Fin d),
      ∑ i, B i j • y i = ∑ t, (P * B) t j • x t := by
    intro B j
    simp only [hy, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  rw [key, show P * (Q * A * P) = A * P by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul], hy j]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, hx, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]

theorem UpperTheory.Gal.Int.Geo.matConj_of :
    MatConj := by
  intro l _ k _ H Ω _ _ L _ _ θ d ρ P ⟨b, hb⟩
  obtain ⟨b', hb'⟩ := conj_basis _ b P
  refine ⟨b', fun σ j => ?_⟩
  have h1 : (P : Matrix (Fin d) (Fin d) L) * ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [cj_apply, Units.val_mul, Units.val_mul]
  exact conj_mat (galV l H Ω L σ) (fun i => (b i).1) (fun i => (b' i).1) _ _ _ h1 (hb σ) hb' j
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.VFinOf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace UpperTheory.Gal.Int.Geo

private theorem red_pow_add_apply_eq (hA : A11) (l : ℕ) [Fact (Nat.Prime l)] (E : Spc) (n i : ℤ)
    (x : Hl l E n i) (m a : ℕ) :
    red (l ^ (m + a)) (l ^ m) E n i ((x : (j : ℕ) → HtL l j E n i) (m + a)) =
      (x : (j : ℕ) → HtL l j E n i) m := by
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hx : ∀ k : ℕ, red (l ^ (k + 1)) (l ^ k) E n i ((x : (j : ℕ) → HtL l j E n i) (k + 1)) =
      (x : (j : ℕ) → HtL l j E n i) k := x.2
  induction a with
  | zero =>
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl⟩
    exact (hA (l ^ m) (l ^ m) dvd_rfl E).2.2.1 n i _
  | succ a ih =>
    haveI : NeZero (l ^ (m + (a + 1))) := ⟨pow_ne_zero _ hl⟩
    have h4 := (hA (l ^ (m + (a + 1))) (l ^ (m + a)) (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ m)
      (pow_dvd_pow l (by omega)) n i ((x : (j : ℕ) → HtL l j E n i) (m + (a + 1)))
    rw [← h4]
    exact (congrArg (red (l ^ (m + a)) (l ^ m) E n i) (hx (m + a))).trans ih

private theorem red_pow_apply_eq_of_le (hA : A11) (l : ℕ) [Fact (Nat.Prime l)] (E : Spc) (n i : ℤ)
    (x : Hl l E n i) (m M : ℕ) (h : m ≤ M) :
    red (l ^ M) (l ^ m) E n i ((x : (j : ℕ) → HtL l j E n i) M) = (x : (j : ℕ) → HtL l j E n i) m := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le h
  exact red_pow_add_apply_eq hA l E n i x m a

private theorem exists_eq_pow_smul_of_lev_eq_zero (hA : A11) (l : ℕ) [Fact (Nat.Prime l)] (E : Spc) (n i : ℤ)
    (hf : ∀ m : ℕ, Finite (Ht (l ^ m) E n i)) (hB : ∀ b : ℕ, LateralTheory.KummerTheory.BockData l b E i) (b : ℕ)
    (x : Hl l E n i) (hx : LateralTheory.KummerTheory.lev l x b = 0) : ∃ y : Hl l E n i, x = (l : ℤ_[l]) ^ b • y := by
  obtain ⟨u, d, hud⟩ := hB b
  let xs : (j : ℕ) → HtL l j E n i := x
  have hmem : ∀ k : ℕ, red (l ^ (k + 1)) (l ^ k) E n i (xs (k + 1)) = xs k := x.2
  let S : ℕ → Type 1 := fun a => {z : Ht (l ^ a) E n i // u a n z = xs (b + a)}
  have hS : ∀ (a : ℕ) (z : S (a + 1)), u a n (red (l ^ (a + 1)) (l ^ a) E n i z.1) = xs (b + a) := by
    intro a z
    rw [← (hud a n).2.2.2.2.2 z.1, z.2]
    exact hmem (b + a)
  let F : ℕᵒᵖ ⥤ Type 1 :=
    Functor.ofOpSequence (X := S) (fun a => TypeCat.ofHom (fun z => ⟨_, hS a z⟩ : S (a + 1) → S a))
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => by
    show Finite (S j.unop)
    haveI := hf j.unop
    exact Subtype.finite
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => by
    show Nonempty (S j.unop)
    obtain ⟨z, hz⟩ := ((hud j.unop n).1 (xs (b + j.unop))).1
      (by rw [red_pow_apply_eq_of_le hA l E n i x b (b + j.unop) (by omega)]; exact hx)
    exact ⟨⟨z, hz⟩⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  let ys : (j : ℕ) → HtL l j E n i := fun j => (s (Opposite.op j)).1
  have hy : ys ∈ HlSub l E n i := by
    show ∀ k : ℕ, red (l ^ (k + 1)) (l ^ k) E n i (ys (k + 1)) = ys k
    intro k
    have := hs (homOfLE (Nat.le_succ k)).op
    rw [Functor.ofOpSequence_map_homOfLE_succ] at this
    exact congrArg Subtype.val this
  refine ⟨⟨ys, hy⟩, ?_⟩
  apply Subtype.ext
  funext m
  show xs m = ((l : ℤ_[l]) ^ b • ys) m
  rw [Pi.smul_apply, show (l : ℤ_[l]) ^ b = ((l ^ b : ℕ) : ℤ_[l]) by push_cast; rfl,
    Nat.cast_smul_eq_nsmul]
  have hym : red (l ^ (b + m)) (l ^ m) E n i (ys (b + m)) = ys m :=
    red_pow_apply_eq_of_le hA l E n i ⟨ys, hy⟩ m (b + m) (by omega)
  have h5 : u m n (ys m) = xs (b + m) := (s (Opposite.op m)).2
  rw [← hym]
  erw [← map_nsmul]
  erw [← (hud m n).2.2.2.1 (ys (b + m))]
  erw [hym, h5]
  exact (red_pow_apply_eq_of_le hA l E n i x m (b + m) (by omega)).symm

theorem vFin_of (h : KunnethLefschetz.In) : GlobalTheory.GalV.VFin := by
  intro l _ k _ _ hl X p _ n i
  have hInv : GlobalTheory.EtC.Inv l (sch.obj X) := by
    intro U hU
    obtain ⟨f⟩ := hU
    have g : U ⟶ X := f
    have := hl.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (g ≫ p).appTop).hom
    simpa using this
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hfin : ∀ m : ℕ, Finite (Ht (l ^ m) (sch.obj X) n i) := by
    intro m
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl0⟩
    exact h.e4 (l ^ m) k (by push_cast; exact hl.pow m) p n i
  have hM : Module.Finite ℤ_[l] (Hl l (sch.obj X) n i) :=
    LateralTheory.EWeil.AdicFinPf.AdicFin_of l (sch.obj X) n i hfin
      (fun b x hx => exists_eq_pow_smul_of_lev_eq_zero h.a11 l (sch.obj X) n i hfin
        (fun b' => LateralTheory.Fin.Bock.etale_bockstein_sequence_adic_finiteness h.a7 h.a8 h.a10 h.a11 l b' (sch.obj X) i hInv) b x hx)
  exact ⟨hM, Module.Finite.base_change ℤ_[l] ℚ_[l] _⟩

end UpperTheory.Gal.Int.Geo

end
end

namespace UpperTheory.Gal.Int.Geo

theorem bcSplits : G3.BcSplits := G3.pBcSplits (G3.pSplitsBasic (G3.pSplitsPts G3.pIsoPts) G3.pPtsOfSplits)

theorem etGood : G3.EtGood := G3.pEtGood (G3.pEtnGood (G3.pFEtBasic G3.pPtsOfSplits) G3.pEtTr)

theorem galClos : G3.GalClos := G3.pGalClos (G3.pGalClosD (G3.pSplitsPts G3.pIsoPts) (G3.pOrdEx G3.pOrdStep))

theorem hopSpec : G3.HopSpec := G3.pHopSpec etGood (G3.pBcGood bcSplits (G3.pBcGal bcSplits)) galClos (G3.pOpEx G3.pOpTr)
  G3.pOpTr G3.pOpEt (G3.pOpBc bcSplits (G3.pBcGal bcSplits)) bcSplits

theorem grEx : GrEx := grEx_of flagEx_of flagBasis_of flagMove_of grHom_of (grSS_of grHom_of sSOfSum_of)

theorem hopGal : HopGal := hopGal_of hopSpec opConj_of (opUniq_of hopSpec (G3.pOpEx G3.pOpTr) G3.pOpEt etGood bcSplits)

theorem pieceStab : PieceStab := pieceStab_of hopGal

theorem degFin (h : KunnethLefschetz.Core) : DegFin :=
  degFin_of h.qDual KunnethLefschetz.inSum_holds h.inputs.a9 KunnethLefschetz.projBC_holds KunnethLefschetz.sumCl_holds KunnethLefschetz.sumHl_holds KunnethLefschetz.piBC_holds relDim_of compSum_of

theorem htotFin (h : KunnethLefschetz.Core) : HtotFin := htotFin_of (degFin h)

theorem degCont : DegCont := degCont_of (stabOpen_of htDesc_of)

theorem totCont (h : KunnethLefschetz.Core) : TotCont := totCont_of (vFin_of h.inputs) degCont

theorem repEx_core (h : KunnethLefschetz.Core) : RepEx :=
  repEx_of grEx contGL_of matEx_of matConj_of pieceStab (htotFin h) extCont_of (totCont h) KunnethLefschetz.projBC_holds

theorem repEx_holds : RepEx := repEx_core KunnethLefschetz.core_holds

end UpperTheory.Gal.Int.Geo
