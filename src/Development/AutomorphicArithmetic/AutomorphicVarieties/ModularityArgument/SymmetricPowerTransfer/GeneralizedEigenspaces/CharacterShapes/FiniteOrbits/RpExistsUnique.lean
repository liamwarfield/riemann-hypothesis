module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OutInvMulMem

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RpExistsUnique
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

private theorem rp_exists_unique {I : Type} {Gv Hv : I → Type} [∀ v, Group (Gv v)] [∀ v, Group (Hv v)]
    (K : ∀ v, Subgroup (Gv v)) (S : Finset I) (e : ∀ v, v ∈ S → (Gv v →* Hv v))
    (he : ∀ v h, Function.Bijective (e v h)) (w : ∀ v, Hv v) :
    ∃! g : RP Gv K, (∀ v (h : v ∈ S), e v h (g.1 v) = w v) ∧ ∀ v, v ∉ S → g.1 v = 1 := by
  classical
  let x : ∀ v, Gv v := fun v => if h : v ∈ S then Function.surjInv (he v h).2 (w v) else 1
  have hx : x ∈ RP Gv K := by
    show ∀ᶠ v in Filter.cofinite, x v ∈ K v
    refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
    by_contra h
    rw [Finset.mem_coe] at h
    exact hv (by simp [x, h, one_mem])
  refine ⟨⟨x, hx⟩, ⟨fun v h => ?_, fun v h => ?_⟩, ?_⟩
  · show e v h (x v) = w v
    simp only [x, dif_pos h]
    exact Function.surjInv_eq _ _
  · show x v = 1
    simp [x, h]
  · rintro g ⟨h1, h2⟩
    apply Subtype.ext
    funext v
    by_cases h : v ∈ S
    · apply (he v h).1
      rw [h1 v h]
      show w v = e v h (x v)
      simp only [x, dif_pos h]
      exact (Function.surjInv_eq _ _).symm
    · rw [h2 v h]
      show 1 = x v
      simp [x, h]

private theorem det_dg_inv {k : Type} [Field k] (t : kˣ) :
    ((dg ![t, t⁻¹] : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = 1 := by
  simp [dg, val_diagT, Matrix.det_diagonal, Fin.prod_univ_two]

end UpperTheory.V.Z.Sym.So

private theorem mem_su_of_det_eq_one {K : Type} [Field K] {D : K} (x : DX D) (hx : (Glob.mt x).det = 1) :
    x ∈ SU D := by
  rw [SU, MonoidHom.mem_ker]
  refine Units.ext ?_
  rw [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  exact hx

theorem UpperTheory.V.Z.Sym.So.elEx :
    UpperTheory.V.Z.Sym.So.ElEx := by
  intro F _ _ Δ A hA
  have loc := fun v (h : v ∈ A.Sg) => (datOk F Δ A hA).2.2.1 v h
  have bU : ∀ v (h : v ∈ A.Sg), Function.Bijective (eU (A.hs v h)) := fun v h =>
    (eU_facts (Kv v) (Ov v) (loc v h).1 (loc v h).2.1 _ (A.s v) (A.hs v h) (loc v h).2.2.1).1
  have bD : ∀ v (h : v ∈ A.Sg), Function.Bijective (eD (A.hs v h)) := fun v h =>
    (eD_facts (Kv v) (Ov v) (loc v h).1 (loc v h).2.1 _ (A.s v) (A.hs v h) (loc v h).2.2.1).1
  refine ⟨fun d => ?_, fun d => ?_, ?_, ?_, ?_⟩
  · exact rp_exists_unique (Hv := fun v => GL (Fin 3) (Kv v)) _ A.Sg (fun v h => eU (A.hs v h)) bU
      (fun v => dg (d v))
  · exact rp_exists_unique (Hv := fun v => GL (Fin 2) (Kv v)) _ A.Sg (fun v h => eD (A.hs v h)) bD
      (fun v => dg (d v))
  · rintro g g' d d' ⟨hg1, hg2⟩ ⟨hg1', hg2'⟩
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · show eU (A.hs v h) (g.1 v * g'.1 v) = dg (d v * d' v)
      rw [map_mul, hg1 v h, hg1' v h]
      exact (map_mul (diagT (Kv v) (Fin 3)) _ _).symm
    · show g.1 v * g'.1 v = 1
      rw [hg2 v h, hg2' v h, mul_one]
  · rintro g g' d d' ⟨hg1, hg2⟩ ⟨hg1', hg2'⟩
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · show eD (A.hs v h) (g.1 v * g'.1 v) = dg (d v * d' v)
      rw [map_mul, hg1 v h, hg1' v h]
      exact (map_mul (diagT (Kv v) (Fin 2)) _ _).symm
    · show g.1 v * g'.1 v = 1
      rw [hg2 v h, hg2' v h, mul_one]
  · rintro g t ⟨hg1, hg2⟩
    simp only [SA, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro v
    show g.1 v ∈ SU (cv v Δ)
    by_cases h : v ∈ A.Sg
    · have hfac := (eD_facts (Kv v) (Ov v) (loc v h).1 (loc v h).2.1 _ (A.s v) (A.hs v h)
        (loc v h).2.2.1).2.2.2.2.1 (g.1 v)
      have hd := hg1 v h
      have h2 : ((dg (SD.dS t v) : GL (Fin 2) (Kv v)) : Matrix (Fin 2) (Fin 2) (Kv v)).det = 1 :=
        det_dg_inv (t v)
      refine mem_su_of_det_eq_one _ ?_
      rw [hfac.1, hd, h2, map_one]
    · exact (hg2 v h).symm ▸ one_mem _

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.UfDg
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem uf_dg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (V : Lev k) (d d' : Fin 2 → kˣ) (hd : Dom d) (hd' : Dom d') : UF (V.J 2) (dg d) (dg d') := by
  intro g
  have h := dCMul k V 2 d d' hd hd' g
  have hm : dg (d * d') = dg d * dg d' := map_mul _ _ _
  simp only [Lev.DC, hm] at h
  exact h

theorem UpperTheory.V.Z.Sym.So.dMul :
    UpperTheory.V.Z.Sym.So.DMul := by
  intro F _ _ Δ A hA g d hg
  classical
  let P := rpg (fun v => ↥(DX ((cv v) Δ))) (fun v => KD ((cv v) Δ) (Ov v))
  have hpv : ∀ (x : DA Δ) v, P.p v x = (x : (v : Pl F) → ↥(DX ((cv v) Δ))) v := fun _ _ => rfl
  have hU : ∀ v ∉ A.Sg, A.dat.J2v v = KD ((cv v) Δ) (Ov v) := by
    intro v hv
    simp [Dat.J2v, SD.dat, hv]
  have hJ : ∀ v (hv : v ∈ A.Sg),
      A.dat.J2v v = Subgroup.comap (eD (A.hs v hv)) ((A.V v).J 2) := by
    intro v hv
    simp [Dat.J2v, SD.dat, hv, Lev.data]
  have hok := datOk F Δ A hA
  have hout : ∀ (x : DA Δ) (e : ParN F 2), A.IsElD x e → ∀ v ∉ A.Sg, P.p v x ∈ A.dat.J2v v := by
    intro x e hx v hv
    rw [hU v hv, hpv, hx.2 v hv]
    exact one_mem _
  have hbox := uFBox (Pl F) (DA Δ) (fun v => ↥(DX ((cv v) Δ))) (fun v => KD ((cv v) Δ) (Ov v))
    A.dat.J2v P A.Sg hU g (hout g d hg)
  have key : ∀ v (hv : v ∈ A.Sg),
      UpperTheory.V.AlgebraTools.FinOrb (A.dat.J2v v) (A.dat.J2v v) (P.p v g) ∧
      ∀ (g' : DA Δ) (d' : ParN F 2), A.IsElD g' d' → Dom (d v) → Dom (d' v) →
        UF (A.dat.J2v v) (P.p v g) (P.p v g') := by
    intro v hv
    obtain ⟨hI, h2, hs0, -, -⟩ := hok.2.2.1 v hv
    have hb := (eD_facts (Kv v) (Ov v) hI h2 ((cv v) Δ) (A.s v) (A.hs v hv) hs0).1
    rw [hJ v hv]
    constructor
    · have dm := dcMap _ _ ℂ (eD (A.hs v hv)) hb ((A.V v).J 2) (P.p v g) (P.p v g)
      rw [dm.2.1, hpv, hg.1 v hv]
      exact ((finFacts (Kv v) (A.V v)).2.2.2.2.2 2).1 _
    · intro g' d' hg' hd hd'
      have dm := dcMap _ _ ℂ (eD (A.hs v hv)) hb ((A.V v).J 2) (P.p v g) (P.p v g')
      rw [dm.2.2.1, hpv, hpv, hg.1 v hv, hg'.1 v hv]
      exact uf_dg (A.V v) (d v) (d' v) hd hd'
  refine ⟨hbox.2.1 (fun v hv => (key v hv).1), fun g' d' hg' hd hd' => ?_⟩
  exact hbox.2.2 g' (hout g' d' hg') (fun v hv => (key v hv).2 g' d' hg' (hd v hv) (hd' v hv))

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.TorPart
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Local

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem det_dg (d : Fin 2 → kˣ) : GeneralLinearGroup.det (dg d) = d 0 * d 1 := by
  ext
  simp [dg, val_diagT, Matrix.det_diagonal, Fin.prod_univ_two]

private theorem det_mem (V : Lev k) (g : GL (Fin 2) k) (hg : g ∈ V.J 2) : GeneralLinearGroup.det g ∈ V.H := by
  obtain ⟨a, ha, s, hs, b, hb, rfl⟩ := (factJ k V 2).1 g hg
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hs
  have hau : a ∈ unipB k (Fin 2) := (glIwa k 2).N_le ha
  have hb0 : b ∈ Subgroup.comap (GlobalTheory.CuspRep.invT 2 k) (unipB k (Fin 2)) ⊓ Kc k 2 (V.c + 1) := hb
  have hbl := GlAx.mem_low.1 (Subgroup.mem_inf.1 hb0).1
  have hal := (mem_unipB k).1 hau
  have da : GeneralLinearGroup.det a = 1 := by
    ext
    simp only [GeneralLinearGroup.val_det_apply, Units.val_one]
    rw [Matrix.det_of_upperTriangular (fun i j hij => hal.1 i j hij)]
    simp [hal.2]
  have db : GeneralLinearGroup.det b = 1 := by
    ext
    simp only [GeneralLinearGroup.val_det_apply, Units.val_one]
    rw [Matrix.det_of_lowerTriangular _ (fun i j hij => hbl.1 i j hij)]
    simp [hbl.2]
  rw [map_mul, map_mul, da, db, one_mul, mul_one]
  have ht' : ∀ i, t i ∈ V.H := fun i => ht i (Set.mem_univ i)
  rw [show diagT k (Fin 2) t = dg t from rfl, det_dg]
  exact V.H.mul_mem (ht' 0) (ht' 1)

private theorem loc {O : Type} [CommRing O] [Algebra O k] (hO : IsInts k O) (h2 : (2 : k) ≠ 0) {Δ s : k} (hs : s * s = Δ)
    (hs0 : s ≠ 0) (V : Lev k) (u : DX Δ) (hu : eD hs u ∈ V.J 2) :
    ∃ c : DX Δ, eD hs c ∈ V.J 2 ∧ u * c⁻¹ ∈ SU Δ ∧ c⁻¹ * u ∈ SU Δ ∧ ∃ x : kˣ, eD hs c = dg ![x, 1] := by
  obtain ⟨hbij, -, -, -, hdet, -⟩ := eD_facts k O hO h2 Δ s hs hs0
  obtain ⟨c, hc⟩ := hbij.2 (dg ![GeneralLinearGroup.det (eD hs u), 1])
  have hxH : GeneralLinearGroup.det (eD hs u) ∈ V.H := det_mem V _ hu
  have hcJ : eD hs c ∈ V.J 2 := by
    rw [hc]
    apply V.dg_mem
    intro i
    fin_cases i
    · simpa using hxH
    · simpa using V.H.one_mem
  have hdet1 : ∀ w : DX Δ, GeneralLinearGroup.det (eD hs w) = 1 → w ∈ SU Δ := by
    intro w hw
    show GeneralLinearGroup.det ((DX Δ).subtype w) = 1
    apply Units.ext
    have h0 := (hdet w).1
    simp only [GeneralLinearGroup.val_det_apply, Units.val_one, Subgroup.coe_subtype]
    rw [h0, ← GeneralLinearGroup.val_det_apply, hw]
    simp
  have hec : GeneralLinearGroup.det (eD hs c) = GeneralLinearGroup.det (eD hs u) := by
    rw [hc, det_dg]
    simp
  refine ⟨c, hcJ, hdet1 _ ?_, hdet1 _ ?_, _, hc⟩
  · rw [map_mul, map_inv, map_mul, map_inv, hec, mul_inv_cancel]
  · rw [map_mul, map_inv, map_mul, map_inv, hec, inv_mul_cancel]

end Local

theorem UpperTheory.V.Z.Sym.So.torPart :
    UpperTheory.V.Z.Sym.So.TorPart := by
  classical
  intro F _ _ Δ A hA u hu
  obtain ⟨-, -, hloc, -, hU2⟩ := datOk F Δ A hA
  obtain ⟨huJ, huK⟩ := (hU2 u).1 hu
  have hex : ∀ v (h : v ∈ A.Sg), ∃ c : DX ((cv v) Δ), eD (A.hs v h) c ∈ (A.V v).J 2 ∧
      u.1 v * c⁻¹ ∈ SU ((cv v) Δ) ∧ c⁻¹ * u.1 v ∈ SU ((cv v) Δ) ∧
      ∃ x : (Kv v)ˣ, eD (A.hs v h) c = dg ![x, 1] := by
    intro v h
    obtain ⟨hO, h2, hs0, -, -⟩ := hloc v h
    exact loc hO h2 (A.hs v h) hs0 (A.V v) _ (huJ v h)
  let cf : (v : Pl F) → DX ((cv v) Δ) := fun v =>
    if h : v ∈ A.Sg then Classical.choose (hex v h) else u.1 v
  have cf_in : ∀ v (h : v ∈ A.Sg), cf v = Classical.choose (hex v h) := fun v h => dif_pos h
  have cf_out : ∀ v, v ∉ A.Sg → cf v = u.1 v := fun v h => dif_neg h
  have hcRP : cf ∈ RP (fun v => DX ((cv v) Δ)) (fun v => KD ((cv v) Δ) (Ov v)) := by
    show ∀ᶠ v in Filter.cofinite, cf v ∈ KD ((cv v) Δ) (Ov v)
    rw [Filter.eventually_cofinite]
    refine A.Sg.finite_toSet.subset (fun v hv => ?_)
    by_contra h
    exact hv (by rw [cf_out v h]; exact huK v h)
  let c : DA Δ := ⟨cf, hcRP⟩
  have hSA : ∀ w : DA Δ, (∀ v, w.1 v ∈ SU ((cv v) Δ)) → w ∈ SA Δ := by
    intro w hw
    exact Subgroup.mem_iInf.2 (fun v => hw v)
  refine ⟨c, (hU2 c).2 ⟨fun v h => ?_, fun v h => ?_⟩, hSA _ (fun v => ?_), hSA _ (fun v => ?_),
    fun g d hgd => ?_⟩
  · show eD _ (cf v) ∈ _
    rw [cf_in v h]
    exact (Classical.choose_spec (hex v h)).1
  · show cf v ∈ _
    rw [cf_out v h]
    exact huK v h
  · show u.1 v * (cf v)⁻¹ ∈ SU ((cv v) Δ)
    by_cases h : v ∈ A.Sg
    · rw [cf_in v h]
      exact (Classical.choose_spec (hex v h)).2.1
    · rw [cf_out v h, mul_inv_cancel]
      exact one_mem _
  · show (cf v)⁻¹ * u.1 v ∈ SU ((cv v) Δ)
    by_cases h : v ∈ A.Sg
    · rw [cf_in v h]
      exact (Classical.choose_spec (hex v h)).2.2.1
    · rw [cf_out v h, inv_mul_cancel]
      exact one_mem _
  · apply Subtype.ext
    funext v
    show cf v * g.1 v = g.1 v * cf v
    by_cases h : v ∈ A.Sg
    · rw [cf_in v h]
      obtain ⟨hO, h2, hs0, -, -⟩ := hloc v h
      have hinj := (eD_facts (Kv v) (Ov v) hO h2 _ _ (A.hs v h) hs0).1.1
      obtain ⟨-, -, -, x, hx⟩ := Classical.choose_spec (hex v h)
      apply hinj
      rw [map_mul, map_mul, hx, hgd.1 v h]
      show diagT _ (Fin 2) ![x, 1] * diagT _ (Fin 2) (d v) = diagT _ (Fin 2) (d v) * diagT _ (Fin 2) ![x, 1]
      rw [← map_mul, ← map_mul, mul_comm]
    · rw [hgd.2 v h, mul_one, one_mul]

end
end
