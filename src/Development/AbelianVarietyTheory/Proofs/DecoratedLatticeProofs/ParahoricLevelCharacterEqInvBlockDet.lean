module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameCoordsMemSelfDualLatticeCoordsIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelCharacterEqInvBlockDet
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelCharacterEqInvBlockDet
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.LevChr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_sub_lt {m : Type} [Fintype m] [DecidableEq m] {A B : Matrix m m k} (hA : IntM A) (hB : IntM B)
    (h : MaxM (A - B)) : valuation k (A.det - B.det) < 1 := by
  let A' : Matrix m m 𝒪[k] := fun i j => ⟨A i j, hA i j⟩
  let B' : Matrix m m 𝒪[k] := fun i j => ⟨B i j, hB i j⟩
  have eA : A.det = ((A'.det : 𝒪[k]) : k) := by
    change _ = (algebraMap 𝒪[k] k) A'.det
    rw [RingHom.map_det]; rfl
  have eB : B.det = ((B'.det : 𝒪[k]) : k) := by
    change _ = (algebraMap 𝒪[k] k) B'.det
    rw [RingHom.map_det]; rfl
  rw [eA, eB, ← residue_eq_iff_lt, RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  exact (residue_eq_iff_lt (A' i j) (B' i j)).2 (by simpa using h i j)

end GlobalTheory.LevChr

namespace GlobalTheory.LevChr

theorem secondBlockIndex_eq_one_iff_basisNumbering {K s T j n : ℕ} {e : StepData.Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j ≃ Fin n}
    (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e) (a : Fin n) :
    Formalism.L2.DIV.blk2 (K + (s + 1)) a = 1 ↔ ∃ p, e.symm a = .inr p := by
  have h0 := he (e.symm a)
  rw [e.apply_symm_apply] at h0
  have hb : Formalism.L2.DIV.blk2 (K + (s + 1)) a = 1 ↔ ¬ a.val < K + (s + 1) := by
    unfold Formalism.L2.DIV.blk2; split_ifs with h <;> simp [h]
  rw [hb]
  rcases hc : e.symm a with (i | i) | p <;> rw [hc] at h0 <;> simp only [GlobalTheory.SymBridge.zPos] at h0
  · have := i.2; simp; omega
  · have := i.2; simp; omega
  · simp; omega

end GlobalTheory.LevChr

theorem GlobalTheory.LevChr.lam_eq_inv_xi : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (ι : E →+* k), (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) → (∀ y : k, y ∈ 𝒪[k] → ∃ z : 𝓞 E, valuation k (y - ι z) < 1) → ∀ (K T s j d : ℕ) (hd : j + d = s + 1) (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (ξ : (𝓞 E ⧸ PP.asIdeal)ˣ →* ℂˣ), (∀ (z : 𝓞 E) (u : kˣ) (r : (𝓞 E ⧸ PP.asIdeal)ˣ), (u : k) = ι z → (r : 𝓞 E ⧸ PP.asIdeal) = Ideal.Quotient.mk PP.asIdeal z → δ u = (ξ r)⁻¹) → ∀ (n : ℕ) (e : Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j ≃ Fin n), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e → ∀ (x : GL (XIx (Fin K) (Fin T) j ⊕ Fin d) k) (hx : x ∈ ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).J) (R : GL (Fin n) (𝓞 E ⧸ PP.asIdeal)), (∀ (a a' : Fin n) (z : 𝓞 E), R.val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm a')) - ι z) < 1) → R ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (K + (s + 1))) → (ξ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 (K + (s + 1))) 1 R))⁻¹ = ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).lam ⟨x, hx⟩ := by
  intro E _ _ k _ _ _ _ PP ι _h1 _h2 K T s j d hd δ hδ η ξ hRes n e he x hx R hR hTri
  have hx' : (plainFrame (k := k) (stdOrd (Fin K) (Fin T) j d hd)).conj.symm x ∈
      (parahoric (Fin K ⊕ Fin (s + 1)) (Fin j × Fin T) δ hδ).J := hx
  change _ = (parahoric (Fin K ⊕ Fin (s + 1)) (Fin j × Fin T) δ hδ).lam ⟨_, hx'⟩
  obtain ⟨hKO, hC⟩ := mem_parahoric.1 hx'
  obtain ⟨-, D, hD, hDv⟩ := exists_diag_blocks hKO hC
  rw [parahoric_lam ⟨_, hx'⟩ D hDv]
  have hy : ((plainFrame (k := k) (stdOrd (Fin K) (Fin T) j d hd)).conj.symm x).val =
      x.val.submatrix (stdOrd (Fin K) (Fin T) j d hd) (stdOrd (Fin K) (Fin T) j d hd) := by
    change ((reGL (stdOrd (Fin K) (Fin T) j d hd)).symm
      ((MulAut.conj (1 : GL (XIx (Fin K) (Fin T) j ⊕ Fin d) k)).symm x)).val = _
    rw [reGL_symm_val, MulAut.conj_symm_apply]
    simp
  have hDe : ∀ p p', D.val p p' =
      x.val (stdOrd (Fin K) (Fin T) j d hd (.inr p)) (stdOrd (Fin K) (Fin T) j d hd (.inr p')) := by
    intro p p'; rw [hDv, hy]; rfl

  have hb := GlobalTheory.LevChr.secondBlockIndex_eq_one_iff_basisNumbering he
  let f : Fin j × Fin T ≃ {a : Fin n // Formalism.L2.DIV.blk2 (K + (s + 1)) a = 1} :=
    Equiv.ofBijective (fun p => ⟨e (.inr p), (hb _).2 ⟨p, by simp⟩⟩)
      ⟨fun p p' h => Sum.inr_injective (e.injective (congrArg Subtype.val h)), fun a => by
        obtain ⟨p, hp⟩ := (hb a.1).1 a.2
        exact ⟨p, Subtype.ext (by simp [← hp])⟩⟩

  choose Z hZ using fun a a' => Ideal.Quotient.mk_surjective (I := PP.asIdeal) (R.val a a')
  let Zf : Matrix (Fin j × Fin T) (Fin j × Fin T) (𝓞 E) := fun p p' => Z (e (.inr p)) (e (.inr p'))
  have hdet : ((Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 (K + (s + 1))) 1 R : (𝓞 E ⧸ PP.asIdeal)ˣ) : 𝓞 E ⧸ PP.asIdeal) =
      Ideal.Quotient.mk PP.asIdeal Zf.det := by
    rw [Formalism.L2.DIV.diag_block_det_val 1 hTri, ← Matrix.det_submatrix_equiv_self f, RingHom.map_det]
    congr 1
    ext p p'
    show R.val (e (.inr p)) (e (.inr p')) = Ideal.Quotient.mk PP.asIdeal (Z (e (.inr p)) (e (.inr p')))
    rw [hZ]

  have hA : IntM D.val := intM_of_mem_KO hD
  have hM : MaxM (D.val - (ι.comp (algebraMap (𝓞 E) E)).mapMatrix Zf) := fun p p' => by
    have h := hR (e (.inr p)) (e (.inr p')) _ (hZ _ _).symm
    simp only [Equiv.symm_apply_apply] at h
    show valuation k (D.val p p' - ι (Z (e (.inr p)) (e (.inr p')) : E)) < 1
    rw [hDe]; exact h
  have hB : IntM ((ι.comp (algebraMap (𝓞 E) E)).mapMatrix Zf) := fun p p' => by
    have h := sub_mem (hA p p') (hM.intM p p')
    simpa using h
  have hlt := GlobalTheory.LevChr.det_sub_lt hA hB hM
  rw [← RingHom.map_det] at hlt
  have hlt' : valuation k (((Matrix.GeneralLinearGroup.det D : kˣ) : k) - ι (Zf.det : E)) < 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hlt
  have hv1 : valuation k ((Matrix.GeneralLinearGroup.det D : kˣ) : k) = 1 := valuation_det_of_mem_KO hD
  have hvz : valuation k (ι (Zf.det : E)) = 1 := by
    have h : valuation k (ι (Zf.det : E) - (Matrix.GeneralLinearGroup.det D : kˣ)) <
        valuation k ((Matrix.GeneralLinearGroup.det D : kˣ) : k) := by
      rw [hv1, ← Valuation.map_neg, neg_sub]; exact hlt'
    rw [Valuation.map_eq_of_sub_lt _ h, hv1]
  have hz0 : ι (Zf.det : E) ≠ 0 := by
    intro h; rw [h, map_zero] at hvz; exact zero_ne_one hvz
  set u : kˣ := Units.mk0 (ι (Zf.det : E)) hz0 with hu
  have htame : δ (u⁻¹ * Matrix.GeneralLinearGroup.det D) = 1 := by
    apply hδ
    have e1 : ((u⁻¹ * Matrix.GeneralLinearGroup.det D : kˣ) : k) - 1 =
        (ι (Zf.det : E))⁻¹ * (((Matrix.GeneralLinearGroup.det D : kˣ) : k) - ι (Zf.det : E)) := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, hu, Units.val_mk0, mul_sub, inv_mul_cancel₀ hz0]
    rw [e1, map_mul, map_inv₀, hvz, inv_one, one_mul]; exact hlt'
  rw [show Matrix.GeneralLinearGroup.det D = u * (u⁻¹ * Matrix.GeneralLinearGroup.det D) by group, map_mul, htame,
    mul_one]
  exact (hRes Zf.det u _ (by rw [hu, Units.val_mk0]) hdet).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelCharacterEqInvBlockDetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricLevelCharacter_eq_inv_blockDet : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (ι : E →+* k), (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) → (∀ y : k, y ∈ 𝒪[k] → ∃ z : 𝓞 E, valuation k (y - ι z) < 1) → ∀ (K T s j d : ℕ) (hd : j + d = s + 1) (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (ξ : (𝓞 E ⧸ PP.asIdeal)ˣ →* ℂˣ), (∀ (z : 𝓞 E) (u : kˣ) (r : (𝓞 E ⧸ PP.asIdeal)ˣ), (u : k) = ι z → (r : 𝓞 E ⧸ PP.asIdeal) = Ideal.Quotient.mk PP.asIdeal z → δ u = (ξ r)⁻¹) → ∀ (n : ℕ) (e : Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j ≃ Fin n), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e → ∀ (x : GL (XIx (Fin K) (Fin T) j ⊕ Fin d) k) (hx : x ∈ ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).J) (R : GL (Fin n) (𝓞 E ⧸ PP.asIdeal)), (∀ (a a' : Fin n) (z : 𝓞 E), R.val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm a')) - ι z) < 1) → R ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (K + (s + 1))) → (ξ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 (K + (s + 1))) 1 R))⁻¹ = ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).lam ⟨x, hx⟩ := by
  first | exact @GlobalTheory.LevChr.lam_eq_inv_xi | exact GlobalTheory.LevChr.lam_eq_inv_xi | (intros; apply GlobalTheory.LevChr.lam_eq_inv_xi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLevelData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevPin


set_option maxHeartbeats 4000000 in
theorem exists_levelData : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (pk W) u (mkGeo m b))), (commOf (pk W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → ∀ (l : ∀ PP : (pk W).Pg, LocX a (pk W).βX PP.1) (S : ∀ PP, SymData (l PP).k (l PP).s D.R.k), SymRead W l S → (∀ PP, LocY (l PP) y v.N (pk W).βY b fun j c hc => ((S PP).T (Fin D.R.t)).bas j c hc) → (∀ PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((l PP).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (l PP).FT) → ∃ JG eG eGT dG, ∃ (n : ℕ) (G : Fin n → GLoc { v with JG := JG, eG := eG, eGT := eGT, dG := dG }) (pl : Fin n ≃ (pk W).Pg), GPin G ∧ (∀ j, GlobalTheory.FinPl.CombAt (· ∈ v.gP) (eG j) ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) (dG j) ∧ ∀ h, GlobalTheory.FinPl.CombAt (· ∈ v.gP) (eGT j h)) ∧ (∀ j row col, GRead (⟨mkGeo m b, j, row, col⟩ : FamCh W u) G pl) ∧ ∀ i, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((G i).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (G i).FT ∧ (G i).z₀ = fun r => (ofSplit (G i).q).pr (a.ζ₀ r) := by
  intro D L hT Gi Gl Kc Yd cX ex W u _ a y m b v hc hτ hNT hgP hTP l S hSym hY hStd
  classical
  have hψ : IsStdChar D (pk W).ψ (-1) := hc.std
  choose ν hν using fun PP : (pk W).Pg => GlobalTheory.SplitWeil.exists_isUnitVol (l PP).k
  choose eg egT cg heg hegT hcm hcp hct sEg sCg using fun PP => exists_locComb (l PP) (S PP) (hY PP) (ν PP) hψ
  have hPv : ∀ PP : (pk W).Pg, (l PP).q.v ∈ v.gP := fun PP => (hgP _).2 ⟨PP.1, PP.2, (l PP).under⟩
  let n := Fintype.card (pk W).Pg
  let pl : Fin n ≃ (pk W).Pg := (Fintype.equivFin _).symm

  have hEG : ∀ j, ∃ c' : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, (∀ w ∈ c'.support, GlobalTheory.FinPl.MxAt (· ∈ v.gP) w) ∧
      ∀ f, comb (pk W).ψ _ _ c' f = (List.finRange n).foldr (fun i f' => comb (pk W).ψ _ _ (eg (pl i) j) f') f := fun j =>
    exists_fold _ _ _ _ (fun i => eg (pl i) j) (fun i w hw => mxAt_of_half (l (pl i)).q (hPv (pl i)) w (sEg (pl i) j w hw)) _
  choose eG hEGs hEGf using hEG
  have hDG : ∀ j, ∃ c' : WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ, (∀ w ∈ c'.support, GlobalTheory.FinPl.MxAt (· ∈ v.gP) w) ∧
      ∀ f, comb (pk W).ψ _ _ c' f = (List.finRange n).foldr (fun i f' => comb (pk W).ψ _ _ (cg (pl i) j) f') f := fun j =>
    exists_fold _ _ _ _ (fun i => cg (pl i) j) (fun i w hw => mxAt_of_half (l (pl i)).q (hPv (pl i)) w (sCg (pl i) j w hw)) _
  choose dG hDGs hDGf using hDG
  have hsj : ∀ (i : Fin n) (j : ℕ), j + 2 * 0 + 2 = D.R.m → (l (pl i)).s = j := fun i j h => by
    have := (l (pl i)).hs
    omega
  let eT : ∀ (i : Fin n) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m), WO (Yc D (j + 1)) D.sp.X' →₀ ℂ := fun i j h =>
    cast (congrArg (fun n' => WO (Yc D (n' + 1)) D.sp.X' →₀ ℂ) (hsj i j h)) (egT (pl i))
  have hEGT : ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ c' : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ,
      (∀ w ∈ c'.support, GlobalTheory.FinPl.MxAt (· ∈ v.gP) w) ∧
      ∀ f, comb (pk W).ψ _ _ c' f = (List.finRange n).foldr (fun i f' => comb (pk W).ψ _ _ (eT i j h) f') f := fun j h =>
    exists_fold _ _ _ _ (fun i => eT i j h) (fun i => mxAt_cast (F := fun n' => Yc D (n' + 1)) (hsj i j h) _
      (fun w hw => mxAt_of_half (l (pl i)).q (hPv (pl i)) w ((hegT (pl i)).1 w hw))) _
  choose eGT hEGTs hEGTf using hEGT

  let JG : ∀ j, Subgroup (GA D (Yc D j)) := fun j => GlobalTheory.FinPl.grpAt (Yc D j) (· ∈ v.gP) ⊓
    ⨅ (i : Fin n) (a' : ℕ) (ha : j + a' = (l (pl i)).s + 1),
      frameSub ((GeneralLinearGroup.map (l (pl i)).q.pr).comp (matHom (Yc D j))) ((hY (pl i)).FY j a' ha)
        ((((S (pl i)).T (Fin D.R.t)).lev j a' ha).J)
  let v' : VCom (commOf (pk W) u (mkGeo m b)) := { v with JG := JG, eG := eG, eGT := eGT, dG := dG }
  let G : Fin n → GLoc v' := fun i =>
    { k := (l (pl i)).k
      ν := ν (pl i)
      unitVol := hν (pl i)
      q := (l (pl i)).q
      unit := (l (pl i)).unit
      s := (l (pl i)).s
      hs := (l (pl i)).hs
      S := S (pl i)
      char := hSym.char (pl i)
      FX := (l (pl i)).FX
      FT := (l (pl i)).FT
      FM := (l (pl i)).FM
      FY := (hY (pl i)).FY
      sc := (hY (pl i)).sc
      sc_unit := (hY (pl i)).sc_unit
      sc_step := (hY (pl i)).sc_step
      hz_unit := (hY (pl i)).hz_unit
      bes := (hY (pl i)).bes
      jac := (hY (pl i)).jac
      z₀ := fun r => (ofSplit (l (pl i)).q).pr (a.ζ₀ r)
      last := (l (pl i)).last
      tau := fun h => by
        rw [show v'.τ = y.τ from hτ]
        exact (hY (pl i)).tau h
      latX := (l (pl i)).latX
      latM := (l (pl i)).latM
      latY := (hY (pl i)).latY
      latT := by
        rw [show v'.NT = a.LT from hNT]
        exact (l (pl i)).latT
      eg := eg (pl i)
      eg_is := heg (pl i)
      egT := egT (pl i)
      egT_is := hegT (pl i)
      cg := cg (pl i)
      cg_mid := hcm (pl i)
      cg_pen := hcp (pl i)
      cg_top := hct (pl i) }
  refine ⟨JG, eG, eGT, dG, n, G, pl, ?_, fun j => ⟨hEGs j, hDGs j, hEGTs j⟩, ?_, fun i => ⟨(hStd (pl i)).1, (hStd (pl i)).2, rfl⟩⟩

  · refine ⟨fun i i' h => pl.injective (Subtype.ext (under_inj hTP (pl i).2 (pl i').2 ?_)), fun p => ?_, fun j _ g => ?_,
      fun j _ f _ => hEGf j f, fun j h => ⟨fun i => eT i j h, fun i => cast_heq _ _, fun f _ => hEGTf j h f⟩,
      fun j _ f _ => hDGf j f⟩
    · have e1 := (l (pl i)).under
      have e2 := (l (pl i')).under
      change (l (pl i)).q.v = (l (pl i')).q.v at h
      rw [← e1, ← e2, h]
    · change p ∈ v.gP ↔ ∃ i, p = (l (pl i)).q.v
      rw [hgP]
      constructor
      · rintro ⟨PP, hPP, rfl⟩
        refine ⟨pl.symm ⟨PP, hPP⟩, ?_⟩
        rw [(l _).under, Equiv.apply_symm_apply]
      · rintro ⟨i, rfl⟩
        exact ⟨(pl i).1, (pl i).2, (l _).under⟩
    · change g ∈ JG j ↔ _
      simp only [JG, Subgroup.mem_inf, Subgroup.mem_iInf, mem_frameSub]
      rfl
  · intro j row col
    refine ⟨fun i => ⟨(l (pl i)).idem, (l (pl i)).under⟩, fun i j h1 h2 => hSym.mu (pl i) j h1 h2,
      fun i j c hc => (hY (pl i)).frame j c hc, fun i => (l (pl i)).frameTop, fun g => ⟨?_, ?_⟩⟩
    · rw [hSym.grp g]
      constructor
      · intro h i
        exact h (pl i)
      · intro h PP
        obtain ⟨i, rfl⟩ := pl.surjective PP
        exact h i
    · intro hg x hx
      rw [hSym.chr g hg (Equiv.piCongrLeft (fun PP => (S PP).P.J) pl x) (fun PP => ?_)]
      · rw [← Equiv.prod_comp pl]
        simp only [Equiv.piCongrLeft_apply_apply]
        rfl
      · obtain ⟨i, rfl⟩ := pl.surjective PP
        rw [Equiv.piCongrLeft_apply_apply]
        exact hx i

end GlobalTheory.LevPin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineSimilitudeMapsSelfDualLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineSimilitudeMapsSelfDualLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitLineSim

open GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_not_int : ∃ x : k, x ∉ 𝒪[k] := by
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  refine ⟨r⁻¹, fun h => ?_⟩
  have h1 : valuation k r⁻¹ ≤ 1 := h
  have hr : r ≠ 0 := hr0
  have : (1 : ValueGroupWithZero k) ≤ valuation k r := by
    calc (1 : ValueGroupWithZero k) = valuation k (r * r⁻¹) := by rw [mul_inv_cancel₀ hr, map_one]
      _ = valuation k r * valuation k r⁻¹ := map_mul _ _ _
      _ ≤ valuation k r * 1 := by gcongr
      _ = valuation k r := mul_one _
  exact absurd hr1 (not_lt.2 this)

theorem mul_sec' (q : SplitPt D k) (a : AE D) (b : k) : a * q.sec b = q.sec (q.pr a * b) := by
  rw [mul_comm, FrameLat.sec_mul_right, mul_comm]

theorem mul_csec (q : SplitPt D k) (a : AE D) (b : k) :
    a * cA D (q.sec b) = cA D (q.sec (q.pr (cA D a) * b)) := by
  rw [← mul_sec', map_mul, Formalism.L2.Theta.cA_cA]

theorem mulVec_sec' (q : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (A : Fin n → k) :
    (M *ᵥ fun i => q.sec (A i)) = fun j => q.sec ((M.map q.pr *ᵥ A) j) := by
  funext j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, mul_sec', map_sum]

theorem mulVec_csec (q : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (B : Fin n → k) :
    (M *ᵥ fun i => cA D (q.sec (B i))) = fun j => cA D (q.sec ((M.map (fun a => q.pr (cA D a)) *ᵥ B) j)) := by
  funext j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, mul_csec, map_sum]

theorem pr_cA_sec (q : SplitPt D k) (c : k) : q.pr (cA D (q.sec c)) = 0 := by
  have he : q.pr (cA D q.e) = 0 := by
    have h1 : q.pr (cA D q.e * q.e) = 0 := by rw [FrameLat.cAe_mul_e, map_zero]
    have pe : q.pr q.e = 1 := by rw [← FrameLat.sec_one, q.pr_sec]
    rwa [map_mul, pe, mul_one] at h1
  rw [← FrameLat.e_mul_sec q c, map_mul, map_mul, he, zero_mul]

theorem pr_cA_xi_int (q : SplitPt D k) (h : q.UnitAA) : q.pr (cA D (incA D D.host.xi0)) ∈ 𝒪[k] := by
  have hid : cA D (q.sec 1) ∈ idAt D (· = q.v) := FrameLat.csec_mem_idAt (p := q) 1
  have hc : cA D (q.sec 1) ∈ intAt D (· = q.v) := by
    refine (GlobalTheory.SplitIntComp.mem_intAt_iff q hid).2 ⟨?_, ?_⟩
    · rw [pr_cA_sec]; exact zero_mem _
    · rw [Formalism.L2.Theta.cA_cA, q.pr_sec]; exact one_mem _
  have h2 := (h.1 _ hc).1
  have h3 := ((GlobalTheory.SplitIntComp.mem_intAt_iff q h2.1).1 h2).2
  rwa [map_mul, Formalism.L2.Theta.cA_cA, map_mul, q.pr_sec, mul_one] at h3

theorem pr_xi_int (q : SplitPt D k) (h : q.UnitAA) : q.pr (incA D D.host.xi0) ∈ 𝒪[k] :=
  (GlobalTheory.SplitIntComp.val_xi q h).le

end GlobalTheory.SplitLineSim

namespace GlobalTheory.SplitLineSim
open GlobalTheory.FinPl

theorem line_sim_maps : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (L L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (LL : GlobalTheory.FinPl.Lat L) (LZ : GlobalTheory.FinPl.Lat L'') (zL : Fin L.rank → k) (z₀ : Fin L''.rank → k) (u : k), q.UnitAA → IsSelfDualC L LL → IsSelfDualC L'' LZ → L.rank = 1 → L''.rank = 1 → (∀ y : k, y ∈ 𝒪[k] ↔ (fun i => q.sec (zL i * y)) ∈ GlobalTheory.FinPl.latV L LL (· = q.v)) → (∀ y : k, y ∈ 𝒪[k] ↔ (fun i => q.sec (z₀ i * y)) ∈ GlobalTheory.FinPl.latV L'' LZ (· = q.v)) → valuation k u = 1 → τ.map (ofSplit q).pr *ᵥ z₀ = u • zL → τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ y ∈ GlobalTheory.FinPl.latV L'' LZ (· = q.v), (rat τ : Mx D L.rank L''.rank) *ᵥ y ∈ GlobalTheory.FinPl.latV L LL (· = q.v) := by
  intro D k _ _ _ _ q L L'' τ LL LZ zL z₀ u hU hLL hLZ hr hr'' hcL hcZ hu hτz hτ y hy
  haveI : Unique (Fin L.rank) := ⟨⟨⟨0, by omega⟩⟩, fun j => Fin.ext (by have := j.2; omega)⟩
  haveI : Unique (Fin L''.rank) := ⟨⟨⟨0, by omega⟩⟩, fun j => Fin.ext (by have := j.2; omega)⟩
  set j0 : Fin L.rank := default with hj0
  set i0 : Fin L''.rank := default with hi0
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  have hu_int : u ∈ 𝒪[k] := hu.le
  have hui_int : u⁻¹ ∈ 𝒪[k] := by
    show valuation k u⁻¹ ≤ 1
    rw [map_inv₀, hu, inv_one]

  have h1 : q.pr (incA D (τ j0 i0)) * z₀ i0 = u * zL j0 := by
    have := congrFun hτz j0
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_unique, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have hzL : zL j0 ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_not_int (k := k)
    apply hx
    rw [hcL]
    have : (fun i => q.sec (zL i * x)) = 0 := by
      funext i
      rw [Subsingleton.elim i j0, h0, zero_mul, map_zero]
      rfl
    rw [this]
    exact zero_mem _
  have hz0 : z₀ i0 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact hzL ((mul_eq_zero.1 h1.symm).resolve_left hu0)

  have hyS : ∀ i, y i ∈ idAt D (· = q.v) := FrameLat.latV_supp hy
  set A : Fin L''.rank → k := fun i => q.pr (y i) with hA
  set B : Fin L''.rank → k := fun i => q.pr (cA D (y i)) with hB
  have hyAB : y = (fun i => q.sec (A i)) + fun i => cA D (q.sec (B i)) := by
    funext i
    exact GlobalTheory.SplitIntComp.eq_sec_add_csec q (hyS i)
  rw [hyAB] at hy
  obtain ⟨hyA, hyB⟩ := (FrameLat.decomp hLZ A B).1 hy
  rw [hyAB, Matrix.mulVec_add, mulVec_sec', mulVec_csec]
  refine (FrameLat.decomp hLL _ _).2 ⟨?_, ?_⟩
  ·
    set c : k := A i0 / z₀ i0 with hc
    have hcA : ∀ i, z₀ i * c = A i := fun i => by
      rw [Subsingleton.elim i i0, hc, mul_div_cancel₀ _ hz0]
    have hcint : c ∈ 𝒪[k] := (hcZ c).2 (by simpa only [hcA] using hyA)
    have : (fun j => q.sec ((((rat τ : Mx D L.rank L''.rank)).map q.pr *ᵥ A) j)) =
        fun j => q.sec (zL j * (u * c)) := by
      funext j
      rw [Subsingleton.elim j j0]
      congr 1
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_unique]
      rw [← hcA i0]
      change q.pr (incA D (τ j0 i0)) * (z₀ i0 * c) = _
      rw [← mul_assoc, h1]
      ring
    rw [this]
    exact (hcL _).1 (mul_mem hu_int hcint)
  ·
    rw [FrameLat.csec_mem_iff hLL]
    intro x hx
    have h00 : star (τ j0 i0) * (L.gram j0 j0 * τ j0 i0) = -(D.host.xi0 * star D.host.xi0) * L''.gram i0 i0 := by
      have := congrFun (congrFun hτ i0) i0
      rw [Matrix.mul_apply, Fintype.sum_unique, Matrix.mul_apply, Fintype.sum_unique,
        Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul] at this
      exact this
    let φ : D.host.E →+* k := (q.pr.comp (cA D)).comp (incA D)
    have hφs : ∀ t : D.host.E, φ (star t) = q.pr (incA D t) := fun t => by
      show q.pr (cA D (incA D (star t))) = _
      rw [FrameLat.cA_incA, star_star]

    have e3 : q.pr (incA D (τ j0 i0)) * (q.pr (cA D (incA D (L.gram j0 j0))) * q.pr (cA D (incA D (τ j0 i0)))) =
        -(q.pr (cA D (incA D D.host.xi0)) * q.pr (incA D D.host.xi0)) * q.pr (cA D (incA D (L''.gram i0 i0))) := by
      have h2 := congrArg φ h00
      rw [map_mul, map_mul, map_mul, map_neg, map_mul, hφs (τ j0 i0), hφs D.host.xi0] at h2
      exact h2
    have hcw_int : -(q.pr (cA D (incA D D.host.xi0)) * q.pr (incA D D.host.xi0)) ∈ 𝒪[k] :=
      neg_mem (mul_mem (pr_cA_xi_int q hU) (pr_xi_int q hU))
    obtain ⟨c', hc'⟩ : ∃ c' : k, c' = x j0 / zL j0 := ⟨_, rfl⟩
    have hxc : ∀ j, zL j * c' = x j := fun j => by
      rw [Subsingleton.elim j j0, hc', mul_div_cancel₀ _ hzL]
    have hc'int : c' ∈ 𝒪[k] := (hcL c').2 (by simpa only [hxc] using hx)

    have hz1 : (fun i => q.sec (z₀ i)) ∈ latV L'' LZ (· = q.v) := by
      simpa only [mul_one] using (hcZ 1).1 (one_mem _)
    have hZB := (FrameLat.csec_mem_iff hLZ B).1 hyB z₀ hz1
    simp only [Fintype.sum_unique] at hZB
    have hinv : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
    have e0 : ((((rat τ : Mx D L.rank L''.rank)).map (fun a => q.pr (cA D a)) *ᵥ B) j0) =
        q.pr (cA D (incA D (τ j0 i0))) * B i0 := by
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_unique]
      rfl
    simp only [Fintype.sum_unique]
    rw [e0, ← hxc j0]
    have key : zL j0 * c' * q.pr (cA D (incA D (L.gram j0 j0))) * (q.pr (cA D (incA D (τ j0 i0))) * B i0) =
        c' * u⁻¹ * (-(q.pr (cA D (incA D D.host.xi0)) * q.pr (incA D D.host.xi0))) *
          (z₀ i0 * q.pr (cA D (incA D (L''.gram i0 i0))) * B i0) := by
      linear_combination (c' * u⁻¹ * z₀ i0 * B i0) * e3 -
        (c' * u⁻¹ * q.pr (cA D (incA D (L.gram j0 j0))) * q.pr (cA D (incA D (τ j0 i0))) * B i0) * h1 -
        (c' * q.pr (cA D (incA D (L.gram j0 j0))) * q.pr (cA D (incA D (τ j0 i0))) * B i0 * zL j0) * hinv
    rw [key]
    exact mul_mem (mul_mem (mul_mem hc'int hui_int) hcw_int) hZB

end GlobalTheory.SplitLineSim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineSimilitudeMapsSelfDualLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_line_similitude_maps_selfDual_lattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (L L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (LL : GlobalTheory.FinPl.Lat L) (LZ : GlobalTheory.FinPl.Lat L'') (zL : Fin L.rank → k) (z₀ : Fin L''.rank → k) (u : k), q.UnitAA → IsSelfDualC L LL → IsSelfDualC L'' LZ → L.rank = 1 → L''.rank = 1 → (∀ y : k, y ∈ 𝒪[k] ↔ (fun i => q.sec (zL i * y)) ∈ GlobalTheory.FinPl.latV L LL (· = q.v)) → (∀ y : k, y ∈ 𝒪[k] ↔ (fun i => q.sec (z₀ i * y)) ∈ GlobalTheory.FinPl.latV L'' LZ (· = q.v)) → valuation k u = 1 → τ.map (ofSplit q).pr *ᵥ z₀ = u • zL → τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ y ∈ GlobalTheory.FinPl.latV L'' LZ (· = q.v), (rat τ : Mx D L.rank L''.rank) *ᵥ y ∈ GlobalTheory.FinPl.latV L LL (· = q.v) := by
  first | exact @GlobalTheory.SplitLineSim.line_sim_maps | exact GlobalTheory.SplitLineSim.line_sim_maps | (intros; apply GlobalTheory.SplitLineSim.line_sim_maps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalPlaceComponentStabilisesLatticeTwisted
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalPlaceComponentStabilisesLatticeTwisted
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Classical

namespace GlobalTheory.LocSuppTw

variable {D : D7}

theorem datum_specQ (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (e : AE D)
    (x : WO S T)
    (hx : (if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) *
      omegaQ Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) ≠ 0) :
    IsIntM (frMapO S T βS βT x) ∧
    (∀ PP ∈ L.Pg, IsUnit (topL S.rank (redM PP (frMapO S T βS βT x))).det) ∧
    ∃ a : ∀ PP : ↥L.Pg, GL (Fin S.rank) (kP PP.1),
      (∀ PP : ↥L.Pg, ((a PP : GL (Fin S.rank) (kP PP.1)) : Matrix (Fin S.rank) (Fin S.rank) (kP PP.1)) =
        topL S.rank (redM PP.1 (frMapO S T βS βT x))) ∧
      (∀ PP : ↥L.Pg, a PP ∈ blockTri (blkOf L.r L.t)) ∧ (fun PP => upperLeftBlock L.hr (a PP)) ∈ L.P.H := by
  by_cases hc : IsHalf e x ∧ IsIntM (frMapO S T βS βT x)
  · rw [if_pos hc] at hx
    have hG := left_ne_zero_of_mul hx
    unfold omegaG at hG
    split_ifs at hG with hd
    · refine ⟨hc.2, fun PP hPP => ?_, hd.2⟩
      obtain ⟨a, ha, -, -⟩ := hd.2
      rw [← ha ⟨PP, hPP⟩]
      exact Matrix.isUnits_det_units (a ⟨PP, hPP⟩)
    · exact absurd rfl hG
  · rw [if_neg hc] at hx
    exact absurd rfl hx

theorem idemSum_left {e : AE D} {P Q : Finset (Pl D.host.E)} (h : IsIdemSum e (P ∪ Q)) :
    ∃ e₁ : AE D, IsIdemSum e₁ P := by
  obtain ⟨e₁, h₁⟩ := GlobalTheory.ExportSeries.SplitSet.mono ⟨e, h⟩ Finset.subset_union_left
  exact ⟨e₁, h₁⟩

theorem isIntM_smul' {b a : ℕ} {c : EAf D} (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) : IsIntM (c • N) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact mul_mem hc (hN i j)

theorem redM_smul_of_res {b a : ℕ} {c : EAf D} (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (PP : Pl D.host.E)
    (h1 : Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = 1) {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) :
    redM PP (c • N) = redM PP N := by
  ext i j
  have h2 : (c • N) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := isIntM_smul' hc hN i j
  have hsub : (⟨(c • N) i j, h2⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨c, hc⟩ * ⟨N i j, hN i j⟩ :=
    Subtype.ext (by simp [Matrix.smul_apply])
  unfold redM
  rw [dite_eq_left h2, dite_eq_left (hN i j), hsub, map_mul, h1, one_mul]

end GlobalTheory.LocSuppTw

namespace GlobalTheory.LocSuppTw

theorem smul_mul_gen {R : Type} [CommRing R] {a b c : ℕ} (f : R) (A : Matrix (Fin a) (Fin b) R)
    (G : Matrix (Fin b) (Fin c) R) : (f • A) * G = f • (A * G) := by
  ext i k
  simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc]

theorem tri_of_mul_eq {κ : Type} [Field κ] {n r t : ℕ} (hr : r ≤ n) {a b R : GL (Fin n) κ} (h : b * R = a)
    (ha : a ∈ blockTri (blkOf r t)) (hb : b ∈ blockTri (blkOf r t)) (ha1 : upperLeftBlock hr a = 1) (hb1 : upperLeftBlock hr b = 1) :
    R ∈ blockTri (blkOf r t) ∧ upperLeftBlock hr R = 1 := by
  have hR : R = b⁻¹ * a := by rw [← h, inv_mul_cancel_left]
  have hmem : R ∈ blockTri (blkOf r t) := by
    rw [hR]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) ha
  refine ⟨hmem, ?_⟩
  have hle := blockTri_blkOf_le (κ := κ) (n := n) r t
  have ha2 := hle ha
  have hb2 := hle hb
  unfold upperLeftBlock at ha1 hb1 ⊢
  rw [hR, extendMatrixByIdentityAlongIndices_mul (blkR hr) (Subgroup.inv_mem _ hb2) ha2, extendOne_inv (blkR hr) hb2, ha1, hb1, inv_one, one_mul]


set_option maxHeartbeats 1000000 in
theorem finE_gAt_mem : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D), IsSelfDualC S ΛS → Formalism.L2.DIV.IsFrame βS ΛS → S.rank ≤ T.rank → IsIdemSum e (L.Pg ∪ L.Q) → L.P.H = ⊥ → ∀ (g : GA D S) (x : WO S T), (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ L.Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) x ≠ 0 → (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ L.Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) (actO S T g 1 x) ≠ 0 → ∀ PP ∈ L.Pg, (∀ PP' ∈ L.Pg ∪ L.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → PP' = PP) → Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g) ∈ Formalism.L2.DIV.St βS ∧ Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) ∧ Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g))) = 1 := by
  intro D S T ΛS βS βT L χ ξ e hSD hFr hST hId hH g x hx hgx PP hPP _
  have hHalf : IsHalf e x := by
    by_contra hn
    exact hx (if_neg fun h => hn h.1)
  obtain ⟨hI1, hU1, a, ha, haT, haH⟩ := datum_specQ S T βS βT L χ ξ L.Q e x hx
  obtain ⟨hI2, hU2, a', ha', ha'T, ha'H⟩ := datum_specQ S T βS βT L χ ξ L.Q e (actO S T g 1 x) hgx

  obtain ⟨γ, hγ⟩ : ∃ γ : GL (Fin S.rank) (Lev.EAf D), γ = βS⁻¹ * Lev.finE S g * βS := ⟨_, rfl⟩
  have hact : frMapO S T βS βT (actO S T g 1 x) = frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val := by
    rw [hγ]
    exact GlobalTheory.T.frameMatrix_weilPairAction_left_inv D S T βS βT g x

  obtain ⟨e₁, h₁⟩ := idemSum_left hId
  obtain ⟨hc, hres⟩ := GlobalTheory.InnerSteps.resS_idemSum h₁
  have hcc : toEAf D e₁ * toEAf D e₁ = toEAf D e₁ := by
    rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self h₁]
  have hmul : toEAf D e₁ • frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val =
      toEAf D e₁ • (frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) := smul_mul_gen _ _ _
  have hI2' : IsIntM (frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) := by
    rw [← hact]
    exact hI2
  have hu1 : IsIntM (toEAf D e₁ • frMapO S T βS βT x) := isIntM_smul' hc hI1
  have hu1g : IsIntM (toEAf D e₁ • frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) := by
    rw [hmul]
    exact isIntM_smul' hc hI2'
  have hsupp : ∀ i j, toEAf D e₁ * (toEAf D e₁ • frMapO S T βS βT x) i j = (toEAf D e₁ • frMapO S T βS βT x) i j := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hcc]
  have hred1 : ∀ PP ∈ L.Pg, redM PP (toEAf D e₁ • frMapO S T βS βT x) = redM PP (frMapO S T βS βT x) :=
    fun PP hP => redM_smul_of_res hc PP (hres PP hP) hI1
  have hred2 : ∀ PP ∈ L.Pg, redM PP (toEAf D e₁ • frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) =
      redM PP (frMapO S T βS βT (actO S T g 1 x)) := by
    intro PP hP
    rw [hmul, hact]
    exact redM_smul_of_res hc PP (hres PP hP) hI2'

  obtain ⟨hγ1, hγ2, htop⟩ := GlobalTheory.T.integral_idempotent_mul_of_unit_topBlock_reductions (D := D) T.rank S.rank hST L.Pg e₁ h₁ (toEAf D e₁ • frMapO S T βS βT x) γ
    hu1 hu1g hsupp (fun PP hP => by rw [hred1 PP hP]; exact hU1 PP hP) (fun PP hP => by rw [hred2 PP hP]; exact hU2 PP hP)
  obtain ⟨hγ3, hγ4⟩ := GlobalTheory.T.selfDualFrame_conj_integral_smul_of_integral S ΛS βS hSD hFr (Lev.finE S g) (GlobalTheory.LevSplit.finE_mem_UA S g) γ hγ e₁ hγ1 hγ2

  obtain ⟨hεε, hεc⟩ := GlobalTheory.T.idempotentSum_add_conj_idempotent_conj_fixed L.Pg e₁ h₁
  obtain ⟨k, -, hk⟩ := GlobalTheory.T.exists_idempotent_component_of_group_element S (GlobalTheory.LevelNbhd.finPartG S g) (e₁ + cA D e₁)
    (GlobalTheory.LevelNbhd.finPartG_mem_GfC S g) hεε hεc
  have hkE := GlobalTheory.T.finiteEmbedding_idempotent_patch_in_frame S βS (GlobalTheory.LevelNbhd.finPartG S g) k (e₁ + cA D e₁) hk
  rw [GlobalTheory.SuppLevO.finE_finPartG, ← hγ] at hkE
  obtain ⟨hkSt, hkred⟩ := GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction S.rank βS γ (Lev.finE S k) L.Pg e₁ h₁ hγ1 hγ2 hγ3 hγ4 hkE
  have hpk : GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) k =
      GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g :=
    (GlobalTheory.T.localProjection_eq_of_idempotent_patch S _ (GlobalTheory.LevelNbhd.finPartG S g) k _ (GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one L.Pg e₁ h₁ PP hPP) hk).trans
      (GlobalTheory.SuppLevO.proj_finPartG S g _)
  have hyv : GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g) =
      GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g :=
    GlobalTheory.AdelicU.proj_emb_self (σ := D.sp.cm.sig) (J := S.gram) _ _

  have hkloc := (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D S βS ΛS hFr k).mp hkSt
  have hyS : Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g) ∈ Formalism.L2.DIV.St βS := by
    rw [GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D S βS ΛS hFr]
    intro w
    by_cases hw : w = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
    · subst hw
      rw [hyv, ← hpk]
      exact hkloc _
    · show GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram w (GlobalTheory.AdelicU.emb D.sp.cm.sig S.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))
        (GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g)) ∈ _
      rw [GlobalTheory.AdelicU.proj_emb_ne (h := hw)]
      exact one_mem _

  have hk' : Lev.finE S k = Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g) *
      Lev.finE S ((gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)⁻¹ * k) := by
    rw [map_mul, map_inv, mul_inv_cancel_left]
  have hk'S : Lev.finE S ((gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)⁻¹ * k) ∈ Formalism.L2.DIV.St βS := by
    rw [map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hyS) hkSt
  have hproj1 : GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))
      ((gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, hpk, hyv, inv_mul_cancel]
  have hR : Formalism.L2.DIV.redFn βS PP (Lev.finE S k) =
      Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)) := by
    rw [hk', Formalism.L2.DIV.redFn_mul hyS hk'S, GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D S βS _ PP hk'S hproj1, mul_one]

  have hmulGL : a' ⟨PP, hPP⟩ * Formalism.L2.DIV.redFn βS PP (Lev.finE S k) = a ⟨PP, hPP⟩ := by
    apply Units.ext
    rw [Units.val_mul, hkred PP hPP, ha' ⟨PP, hPP⟩, ha ⟨PP, hPP⟩]
    have htopPP := htop PP hPP
    rw [hred2 PP hPP, hred1 PP hPP] at htopPP
    exact htopPP
  have hrb : ∀ b : ∀ PP : ↥L.Pg, GL (Fin S.rank) (kP PP.1), (fun PP => upperLeftBlock L.hr (b PP)) ∈ L.P.H →
      ∀ PP, upperLeftBlock L.hr (b PP) = 1 := by
    intro b hb PP'
    rw [hH, Subgroup.mem_bot] at hb
    exact congrFun hb PP'
  obtain ⟨h1, h2⟩ := tri_of_mul_eq L.hr hmulGL (haT _) (ha'T _) (hrb a haH _) (hrb a' ha'H _)
  rw [← hR]
  exact ⟨hyS, h1, h2⟩

end GlobalTheory.LocSuppTw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalPlaceComponentStabilisesLatticeTwistedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalPlace_component_stabilises_lattice_twisted : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D), IsSelfDualC S ΛS → Formalism.L2.DIV.IsFrame βS ΛS → S.rank ≤ T.rank → IsIdemSum e (L.Pg ∪ L.Q) → L.P.H = ⊥ → ∀ (g : GA D S) (x : WO S T), (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ L.Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) x ≠ 0 → (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ L.Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) (actO S T g 1 x) ≠ 0 → ∀ PP ∈ L.Pg, (∀ PP' ∈ L.Pg ∪ L.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → PP' = PP) → Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g) ∈ Formalism.L2.DIV.St βS ∧ Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) ∧ Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g))) = 1 := by
  first | exact @GlobalTheory.LocSuppTw.finE_gAt_mem | exact GlobalTheory.LocSuppTw.finE_gAt_mem | (intros; apply GlobalTheory.LocSuppTw.finE_gAt_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameColumnsUnitScaling
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrimSplitLine

open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cA_sec_mul' (p : SplitPt D k) (a : AE D) (t : k) :
    cA D (p.sec t) * a = cA D (p.sec (t * p.pr (cA D a))) := by
  rw [← sec_mul_right, RingHom.map_mul, Formalism.L2.Theta.cA_cA]

theorem colMul_split (q : SplitPt D k) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) {a : AE D}
    (ha : a ∈ idAt D (· = q.v)) :
    colMul d.jX i a = (fun r => q.sec (q.pr a * q.pr (incA D (d.e r i)))) +
      (fun r => cA D (q.sec (q.pr (cA D a) * q.pr (cA D (incA D (d.e r i)))))) := by
  funext r
  change a * incA D (d.e r i) = _
  conv_lhs => rw [GlobalTheory.SplitIntComp.eq_sec_add_csec q ha]
  rw [add_mul, sec_mul_right, cA_sec_mul' q, Pi.add_apply]

theorem mul_unit_mem_iff {b u : k} (hu : valuation k u = 1) : b * u ∈ 𝒪[k] ↔ b ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, Valuation.map_mul, hu, mul_one]

theorem colMul_mem_latV_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (i : Fin ρ) (y₁ y₂ : Y) (u₁ u₂ : k), IsSelfDualC S L → IntIn q S F L → valuation k u₁ = 1 → valuation k u₂ = 1 → (∀ r, F.β r y₁ = u₁ * q.pr (incA D (d.e r i))) → (∀ l, ∑ r, ∑ t, F.β r l * q.pr (cA D (incA D (HSpace.gram S r t))) * q.pr (cA D (incA D (d.e t i))) = if l = y₂ then u₂ else 0) → ∀ a : AE D, (GlobalTheory.FinPl.colMul d.jX i a ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = q.v)) := by
  intro D k _ _ _ _ q S S₀ ρ d L Y _ _ F i y₁ y₂ u₁ u₂ hL hF hu₁ hu₂ hcol₁ hcol₂ a
  have hu₁0 : u₁ ≠ 0 := by
    rintro rfl
    rw [Valuation.map_zero] at hu₁
    exact zero_ne_one hu₁
  have hu₂i : u₂ ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hu₂.le
  have key : ∀ a ∈ idAt D (· = q.v), (colMul d.jX i a ∈ latV S L (· = q.v) ↔
      q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k]) := by
    intro a ha
    rw [colMul_split q d i ha, decomp hL]
    refine and_congr ?_ ?_
    · have h1 : (fun r => q.sec (q.pr a * q.pr (incA D (d.e r i)))) =
          fun r => q.sec ((F.β *ᵥ Pi.single y₁ (q.pr a * u₁⁻¹)) r) := by
        funext r
        congr 1
        simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hcol₁]
        field_simp
      rw [h1, ← hF]
      constructor
      · intro h
        have := h y₁
        rw [Pi.single_eq_same] at this
        rwa [mul_unit_mem_iff (by rw [map_inv₀, hu₁, inv_one])] at this
      · intro h j
        by_cases hj : j = y₁
        · subst hj
          rw [Pi.single_eq_same, mul_unit_mem_iff (by rw [map_inv₀, hu₁, inv_one])]
          exact h
        · rw [Pi.single_eq_of_ne hj]
          exact zero_mem _
    · rw [csec_mem_iff hL]
      set b := q.pr (cA D a) with hb
      have hsum : ∀ y : Y → k, ∑ r, ∑ t, (F.β *ᵥ y) r * q.pr (cA D (incA D (HSpace.gram S r t))) *
          (b * q.pr (cA D (incA D (d.e t i)))) = b * u₂ * y y₂ := by
        intro y
        have hr : b * u₂ * y y₂ = ∑ l, y l * b * (∑ r, ∑ t, F.β r l * q.pr (cA D (incA D (HSpace.gram S r t))) *
            q.pr (cA D (incA D (d.e t i)))) := by
          simp only [hcol₂, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
        rw [hr]
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
        symm
        refine Finset.sum_comm.trans (Finset.sum_congr rfl fun r _ => Finset.sum_comm.trans
          (Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun l _ => ?_))
        ring
      constructor
      · intro h
        have h2 := h (F.β *ᵥ Pi.single y₂ 1) ((hF _).1 fun j => by
          by_cases hj : j = y₂
          · subst hj; rw [Pi.single_eq_same]; exact one_mem _
          · rw [Pi.single_eq_of_ne hj]; exact zero_mem _)
        rw [hsum, Pi.single_eq_same, mul_one, mul_unit_mem_iff hu₂] at h2
        exact h2
      · intro hb' x hx
        have hx' : x = F.β *ᵥ (F.γ *ᵥ x) := by rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
        rw [hx'] at hx ⊢
        rw [hsum]
        exact mul_mem (mul_mem hb' hu₂i) ((hF _).2 hx y₂)
  constructor
  · intro h
    have ha := GlobalTheory.FinPl.SuppShift.idAt_of_colMul d h
    exact (GlobalTheory.SplitIntComp.mem_intAt_iff q ha).2 ((key a ha).1 h)
  · intro h
    exact (key a h.1).2 ((GlobalTheory.SplitIntComp.mem_intAt_iff q h.1).1 h)

end GlobalTheory.PrimSplitLine

end
end
