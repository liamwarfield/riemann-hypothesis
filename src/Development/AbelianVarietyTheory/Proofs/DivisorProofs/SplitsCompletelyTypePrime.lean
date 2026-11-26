module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeepsCuspLatticeNorm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqPlGwOrIsConjPl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.TypePlacesExhaust

variable {R : Ranks} (H : Host R)

def cInt : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv

def conjPl (w : HeightOneSpectrum (𝓞 H.E)) : HeightOneSpectrum (𝓞 H.E) :=
  HeightOneSpectrum.comap ((cInt H).symm : 𝓞 H.E →+* 𝓞 H.E) (cInt H).symm.surjective w

variable {H}

theorem mem_conjPl (w : HeightOneSpectrum (𝓞 H.E)) (y : 𝓞 H.E) :
    y ∈ (conjPl H w).asIdeal ↔ (cInt H).symm y ∈ w.asIdeal := Iff.rfl

theorem isConjPl_conjPl (w : HeightOneSpectrum (𝓞 H.E)) : IsConjPl H w (conjPl H w) := by
  intro x y hy
  have e : y = cInt H x := RingOfIntegers.ext (by rw [hy]; rfl)
  subst e
  rw [mem_conjPl, RingEquiv.symm_apply_apply]

theorem conjPl_injective : Function.Injective (conjPl H) := by
  intro w w' h
  apply HeightOneSpectrum.ext
  ext x
  have := congrArg (fun u : HeightOneSpectrum (𝓞 H.E) => cInt H x ∈ u.asIdeal) h
  simp only [mem_conjPl, RingEquiv.symm_apply_apply] at this
  exact Iff.of_eq this

theorem conjPl_mem_placesOver {p : ℕ} {w : HeightOneSpectrum (𝓞 H.E)} (hw : w ∈ placesOver H.E p) :
    conjPl H w ∈ placesOver H.E p := by
  show ((p : ℕ) : 𝓞 H.E) ∈ (conjPl H w).asIdeal
  rw [mem_conjPl, map_natCast]
  exact hw

theorem finrank_E (H : Host R) : Module.finrank ℚ H.E = 2 * R.f := by
  rw [H.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring_nf

theorem eq_plGw_or_isConjPl : ∀ (D : D7) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k),
    ∃ v : D.nd.PlG k, w = D.naut.plGw k v ∨ IsConjPl D.host (D.naut.plGw k v) w := by
  intro D k w hw
  classical
  set S := placesOver D.host.E (D.host.g k) with hSdef
  set A : Set (HeightOneSpectrum (𝓞 D.host.E)) := D.naut.plGw k '' Set.univ with hAdef
  set B : Set (HeightOneSpectrum (𝓞 D.host.E)) := conjPl D.host '' A with hBdef
  have hAS : A ⊆ S := by
    rintro _ ⟨v, -, rfl⟩
    exact D.naut.plGw_over k v
  have hBS : B ⊆ S := by
    rintro _ ⟨u, hu, rfl⟩
    exact conjPl_mem_placesOver (hAS hu)
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro _ ⟨v, -, rfl⟩ ⟨_, ⟨v', -, rfl⟩, h⟩
    exact D.naut.plGw_nconj k v' v (h ▸ isConjPl_conjPl _)
  have hS : S.ncard = 2 * D.R.f := by rw [hSdef, D.nd.g_split k, finrank_E]
  have hSfin : S.Finite := Set.finite_of_ncard_pos (by
    rw [hS, ← finrank_E D.host]
    exact Module.finrank_pos)
  have hA : A.ncard = D.R.f := by
    rw [hAdef, Set.ncard_image_of_injective _ (D.naut.plGw_inj k), Set.ncard_univ, Nat.card_eq_fintype_card,
      D.nd.card_PlG k]
  have hB : B.ncard = D.R.f := by
    rw [hBdef, Set.ncard_image_of_injective _ conjPl_injective, hA]
  have hAfin : A.Finite := hSfin.subset hAS
  have hBfin : B.Finite := hSfin.subset hBS
  have hU : A ∪ B = S := Set.eq_of_subset_of_ncard_le (Set.union_subset hAS hBS)
    (by rw [Set.ncard_union_eq hdisj hAfin hBfin, hA, hB, hS]; ring_nf; rfl) hSfin
  rw [← hU] at hw
  rcases hw with ⟨v, -, rfl⟩ | ⟨_, ⟨v, -, rfl⟩, rfl⟩
  · exact ⟨v, Or.inl rfl⟩
  · exact ⟨v, Or.inr (isConjPl_conjPl _)⟩

end GlobalTheory.TypePlacesExhaust
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelChangeUnitriangularUnipotentModPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelChangeUnitriangularUnipotentModPlace
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.ShareOn.UnipLevel

theorem pow_apply_eq_zero_of_strict {K : Type} [CommRing K] {n : ℕ} (S : Matrix (Fin n) (Fin n) K)
    (hS : ∀ a b : Fin n, b ≤ a → S a b = 0) (m : ℕ) :
    ∀ a b : Fin n, (b : ℕ) < a + m → (S ^ m) a b = 0 := by
  induction m with
  | zero =>
    intro a b h
    rw [pow_zero, Matrix.one_apply, if_neg]
    intro hab
    rw [hab] at h
    omega
  | succ m ih =>
    intro a b h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : b ≤ j
    · rw [hS j b hj, mul_zero]
    · have hj' : (j : ℕ) < a + m := by
        have : (j : ℕ) < b := Fin.lt_def.1 (not_le.1 hj)
        omega
      rw [ih a j hj', zero_mul]

end GlobalTheory.ShareOn.UnipLevel
namespace GlobalTheory.ShareOn.UnipLevel


set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem levUnip_mod_place : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp),
    RunsOk (fw2 p) r → ∀ (i : Fin D.R.m) (u : p.P.Gp) (k : Fin 2) (v : D.nd.PlG k),
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp (((p.R.eG.trans p.cG) u ⟨k, v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k))) →
    ∀ x : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l,
      (((r.lev i u).toLinearMap - LinearMap.id : Module.End (𝓞 D.host.E) (LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)) ^ D.R.r) x ∈
        ((D.naut.plGw k v).asIdeal • ⊤ : Submodule (𝓞 D.host.E) (LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p r hr i u k v hU x
  classical
  obtain ⟨v'⟩ := GlobalTheory.ShareOn.nonempty_place D
  have hlev : Formalism.IndefR.FWT.LevIs (R2 p) i (Formalism.IndefR.FWT.iotaW p.T i) p.T.Q.l.M (Mfr p.T.Q.l)
      (fun g => liftLa (r.lev i g)) := hr.level v' i
  have hL := hr.laws v'
  have hι : LatEmb (Wc D i) (Formalism.IndefR.FWT.iotaW p.T i) := GlobalTheory.TraceLattice.latEmb_iotaW hL i
  have hβ : IsSDFrame (Wc D i) ((R2 p).βW i) ((R2 p).ΛW i) 1 := p.charW.base.lev.βW i
  obtain ⟨plg, iso, hplg, -, -, hG⟩ := p.grpRecPin
  have hrk : D.R.r = (p.T.Q.Dw ((i : ℕ) + 1)).p + (p.T.Q.Dw ((i : ℕ) + 1)).q :=
    (hL.j.unf _ ⟨Nat.le_add_left _ _, i.2⟩ _ (r.used v').full.toCore.good_σ₀).1
  set PPs := plg ⟨k, v⟩ with hPPs
  obtain ⟨φ, hφs, hφk⟩ := GlobalTheory.T.lattice_coordinates_mod_prime_selfDual_stabilizer D (Wc D i) ((R2 p).βW i) ((R2 p).ΛW i) hβ _ _ hι PPs.1
  obtain ⟨κ, hκ, hκa⟩ := hlev u
  have hMbP : p.T.Q.l.Mb ≤ PPs.1.asIdeal := by
    rw [hr.half]
    exact Ideal.prod_le_inf.trans (Finset.inf_le PPs.2)
  have hM : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ PPs.1.asIdeal := hMbP (GlobalTheory.LevDesc.natCast_M_mem _)
  have hSt : Lev.finE (Wc D i) κ ∈ St ((R2 p).βW i) := parLev_St hκ.2.1
  have hkill : ∀ c ∈ PPs.1.asIdeal, ∀ y, φ (c • y) = 0 := by
    intro c hc y
    rw [map_smul]
    funext j
    rw [Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 hc, zero_mul]
  have hcop : p.T.Q.l.Mb ⊔ Mfr p.T.Q.l = ⊤ := p.T.Q.l.coprime
  obtain ⟨c₁, hc₁, w, hw, hcw⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ p.T.Q.l.Mb ⊔ Mfr p.T.Q.l)
  set f := liftLa (r.lev i u) with hf
  set N : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (kP PPs.1) :=
    (redFn ((R2 p).βW i) PPs.1 (Lev.finE (Wc D i) κ)).1 with hN
  have hfφ : ∀ a, φ (f a) = N *ᵥ φ a := by
    intro a
    have ha : a = c₁ • a + w • a := by rw [← add_smul, hcw, one_smul]
    have h1 := hφk κ hSt p.T.Q.l.M hM (w • a) (f (w • a)) (hκa (w • a) (Submodule.smul_mem_smul hw Submodule.mem_top))
    have h2 : φ (w • a) = φ a := by
      conv_rhs => rw [ha]
      rw [map_add (f := _), hkill c₁ (hMbP hc₁), zero_add]
    have h3 : φ (f a) = φ (f (w • a)) := by
      conv_lhs => rw [ha]
      rw [map_add (f := _), map_add (f := _), map_smul, hkill c₁ (hMbP hc₁), zero_add]
    rw [h3, h1, h2]
  have hrank : (Wc D i).rank = D.R.r := Formalism.IndefR.FWT.rank_Wc i
  have h5 : (R2 p).eG u PPs = upperLeftBlock ((R2 p).datWp i (R2 p).triv).hr (redFn ((R2 p).βW i) PPs.1 (Lev.finE (Wc D i) κ)) :=
    (congrFun hκ.2.2 PPs).symm
  have h6 := upper_block_val_submatrix ((R2 p).datWp i (R2 p).triv).hr (blockTri_blkOf_le _ _ (parLev_g hκ.2.1 PPs.2))
  have h7 : (R2 p).eG u PPs = Formalism.UG.bc (iso ⟨k, v⟩ : ZMod (D.host.g k) →+* kP PPs.1) ((p.R.eG.trans p.cG) u ⟨k, v⟩) :=
    hG u ⟨k, v⟩
  rw [← h5, h7] at h6
  have hsub : ∀ a' b' : Fin D.R.r, N (Fin.castLE ((R2 p).datWp i (R2 p).triv).hr a') (Fin.castLE ((R2 p).datWp i (R2 p).triv).hr b') =
      iso ⟨k, v⟩ ((((p.R.eG.trans p.cG) u ⟨k, v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k))) a' b') := by
    intro a' b'
    have := congrFun (congrFun h6 a') b'
    exact this.symm
  have hstrict : ∀ a b : Fin (Wc D i).rank, b ≤ a → (N - 1) a b = 0 := by
    intro a b hab
    have ha' : (a : ℕ) < D.R.r := hrank ▸ a.2
    have hb' : (b : ℕ) < D.R.r := hrank ▸ b.2
    have e1 : N a b = iso ⟨k, v⟩ ((((p.R.eG.trans p.cG) u ⟨k, v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k)))
        ⟨a, ha'⟩ ⟨b, hb'⟩) := hsub ⟨a, ha'⟩ ⟨b, hb'⟩
    rw [Matrix.sub_apply, e1]
    rcases lt_or_eq_of_le hab with h | h
    · rw [(hU ⟨a, ha'⟩ ⟨b, hb'⟩).1 h, map_zero, Matrix.one_apply_ne (ne_of_gt h), sub_zero]
    · have hab' : (⟨a, ha'⟩ : Fin D.R.r) = ⟨b, hb'⟩ := by
        ext; show (a : ℕ) = b; rw [h]
      rw [(hU ⟨a, ha'⟩ ⟨b, hb'⟩).2 hab', map_one, h, Matrix.one_apply_eq, sub_self]
  have hnil : (N - 1) ^ D.R.r = 0 := by
    ext a b
    rw [Matrix.zero_apply]
    exact pow_apply_eq_zero_of_strict _ hstrict D.R.r a b (by have := b.2; omega)
  have hpow : ∀ (m : ℕ) a, φ (((f - LinearMap.id : Module.End (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) ^ m) a) = ((N - 1) ^ m) *ᵥ φ a := by
    intro m
    induction m with
    | zero => intro a; rw [pow_zero, pow_zero, Module.End.one_apply, Matrix.one_mulVec]
    | succ m ih =>
      intro a
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, ← Matrix.mulVec_mulVec, LinearMap.sub_apply, LinearMap.id_apply,
        map_sub, hfφ, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hker : ∀ y, φ y = 0 → y ∈ PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) := by
    intro y hy
    haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
    haveI hfin : Finite (kP PPs.1) := Finite.of_equiv _ (iso ⟨k, v⟩).toEquiv
    haveI : Finite (𝓞 D.host.E ⧸ PPs.1.asIdeal) := hfin
    haveI := (p.T.Q.Dw ((i : ℕ) + 1)).fin
    haveI := (p.T.Q.Dw ((i : ℕ) + 1)).proj
    have hle : PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) ≤ LinearMap.ker φ := by
      rw [Submodule.smul_le]
      intro c hc z _
      exact hkill c hc z
    let ψ := (PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)).liftQ φ hle
    have hψs : Function.Surjective ψ := by
      intro z
      obtain ⟨y', rfl⟩ := hφs z
      exact ⟨Submodule.Quotient.mk y', rfl⟩
    have hc0 : Nat.card (kP PPs.1) ≠ 0 := Nat.card_pos.ne'
    have hN1 : Nat.card ((p.T.Q.Dw ((i : ℕ) + 1)).La ⧸ PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)) =
        Nat.card (kP PPs.1) ^ (Wc D i).rank := by
      rw [GlobalTheory.natCard_quot_smul_top_of_projective, (p.T.Q.Dw ((i : ℕ) + 1)).rank, ← hrk, hrank]
    have hN2 : Nat.card (Fin (Wc D i).rank → kP PPs.1) = Nat.card (kP PPs.1) ^ (Wc D i).rank := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]
    haveI : Finite ((p.T.Q.Dw ((i : ℕ) + 1)).La ⧸ PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)) :=
      Nat.finite_of_card_ne_zero (by rw [hN1]; exact pow_ne_zero _ hc0)
    have hb := hψs.bijective_of_nat_card_le (by rw [hN1, hN2])
    have h0 : ψ (Submodule.Quotient.mk y) = ψ 0 := by
      rw [map_zero]
      exact hy
    exact (Submodule.Quotient.mk_eq_zero _).1 (hb.1 h0)
  have hmk : ∀ (m : ℕ) a, ((((r.lev i u).toLinearMap - LinearMap.id : Module.End (𝓞 D.host.E) (LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)) ^ m)
      ((p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)).mkQ a)) =
      (p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)).mkQ
        (((f - LinearMap.id : Module.End (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) ^ m) a) := by
    intro m
    induction m with
    | zero => intro a; rfl
    | succ m ih =>
      intro a
      rw [pow_succ, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, hf, ← liftLa_spec,
        ← map_sub, ← hf, ih, pow_succ, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.id_apply]
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hP : ((plg ⟨k, v⟩ : ↥p.R.Pg) : Pl D.host.E) = D.naut.plGw k v := hplg ⟨k, v⟩
  rw [← hP, ← hPPs]
  have hx := hmk D.R.r a
  rw [Submodule.mkQ_apply] at hx
  rw [hx]
  refine GlobalTheory.LevDesc.map_mem_smul_top _ (hker _ ?_)
  rw [hpow, hnil, Matrix.zero_mulVec]

end GlobalTheory.ShareOn.UnipLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelChangeUnitriangularUnipotentModPlaceStatement
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelChange_unitriangular_unipotent_modPlace : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp),
    RunsOk (fw2 p) r → ∀ (i : Fin D.R.m) (u : p.P.Gp) (k : Fin 2) (v : D.nd.PlG k),
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp (((p.R.eG.trans p.cG) u ⟨k, v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k))) →
    ∀ x : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l,
      (((r.lev i u).toLinearMap - LinearMap.id : Module.End (𝓞 D.host.E) (LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)) ^ D.R.r) x ∈
        ((D.naut.plGw k v).asIdeal • ⊤ : Submodule (𝓞 D.host.E) (LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)) := by
  first | exact @GlobalTheory.ShareOn.UnipLevel.levUnip_mod_place | exact GlobalTheory.ShareOn.UnipLevel.levUnip_mod_place | (intros; apply GlobalTheory.ShareOn.UnipLevel.levUnip_mod_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeOverTypePrimeFixedPlaceOrConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeOverTypePrimeFixedPlaceOrConj
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimesOnto

theorem prime_eq_plGw_or_conj : ∀ (D : D7) (k : Fin 2) (P : Ideal (𝓞 D.host.E)), P.IsPrime → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P →
    ∃ v : D.nd.PlG k, P = (D.naut.plGw k v).asIdeal ∨
      P = (D.naut.plGw k v).asIdeal.map
        ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv : 𝓞 D.host.E ≃+* 𝓞 D.host.E) :
          𝓞 D.host.E →+* 𝓞 D.host.E) := by
  intro D k P hP hg
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hg
    have h0 : ((D.host.g k : ℕ) : 𝓞 D.host.E) = ((0 : ℕ) : 𝓞 D.host.E) := by simpa using hg
    have := Nat.cast_injective h0
    exact (D.host.g_prime k).ne_zero this
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨P, hP, hne⟩
  have hw : w ∈ Formalism.BasicNotions.placesOver D.host.E (D.host.g k) := hg
  obtain ⟨v, hv | hv⟩ := GlobalTheory.TypePlacesExhaust.eq_plGw_or_isConjPl D k w hw
  · exact ⟨v, Or.inl (congrArg HeightOneSpectrum.asIdeal hv)⟩
  · refine ⟨v, Or.inr ?_⟩
    set c : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
      RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv with hc
    rw [Ideal.map_comap_of_equiv]
    ext y
    rw [Ideal.mem_comap]
    have key : (y : D.host.E) = D.host.conj ((c.symm y : 𝓞 D.host.E) : D.host.E) := by
      rw [← GlobalTheory.HeightCounting.FormsStep.complexConj_eq_hostConj]
      have : c (c.symm y) = y := c.apply_symm_apply y
      rw [← congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) this]
      rfl
    exact ((hv (c.symm y) y key).symm.trans Iff.rfl)
end GlobalTheory.TypePrimesOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeOverTypePrimeFixedPlaceOrConjStatement
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_over_typePrime_fixedPlace_or_conj : ∀ (D : D7) (k : Fin 2) (P : Ideal (𝓞 D.host.E)), P.IsPrime → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P →
    ∃ v : D.nd.PlG k, P = (D.naut.plGw k v).asIdeal ∨
      P = (D.naut.plGw k v).asIdeal.map
        ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv : 𝓞 D.host.E ≃+* 𝓞 D.host.E) :
          𝓞 D.host.E →+* 𝓞 D.host.E) := by
  first | exact @GlobalTheory.TypePrimesOnto.prime_eq_plGw_or_conj | exact GlobalTheory.TypePrimesOnto.prime_eq_plGw_or_conj | (intros; apply GlobalTheory.TypePrimesOnto.prime_eq_plGw_or_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentModIdealOfTrivialModHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentModIdealOfTrivialModHalf
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipModHalf

theorem zpow_sub_one_eq_mul {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (ℓ : A ≃ₗ[R] A) (n : ℤ) :
    ∃ X : Module.End R A, Commute ((ℓ : Module.End R A) - 1) X ∧
      ((ℓ ^ n : A ≃ₗ[R] A) : Module.End R A) - 1 = ((ℓ : Module.End R A) - 1) * X := by
  have h1 : (ℓ.symm : Module.End R A) * (ℓ : Module.End R A) = 1 := by
    ext y; simp
  have h2 : (ℓ : Module.End R A) * (ℓ.symm : Module.End R A) = 1 := by
    ext y; simp
  have hDℓ : Commute ((ℓ : Module.End R A) - 1) (ℓ : Module.End R A) :=
    (Commute.refl _).sub_left (Commute.one_left _)
  have hDs : Commute ((ℓ : Module.End R A) - 1) (ℓ.symm : Module.End R A) := by
    show _ = _
    rw [sub_mul, mul_sub, h2, h1, one_mul, mul_one]
  induction n using Int.induction_on with
  | zero => exact ⟨0, Commute.zero_right _, by ext y; simp⟩
  | succ k ih =>
    obtain ⟨X, hc, hX⟩ := ih
    refine ⟨(ℓ : Module.End R A) * X + 1, (hDℓ.mul_right hc).add_right (Commute.one_right _), ?_⟩
    have e : ((ℓ ^ ((k : ℤ) + 1) : A ≃ₗ[R] A) : Module.End R A)
        = (ℓ : Module.End R A) * ((ℓ ^ (k : ℤ) : A ≃ₗ[R] A) : Module.End R A) := by
      ext y; rw [add_comm, zpow_add, zpow_one]; rfl
    rw [e, eq_add_of_sub_eq hX]
    noncomm_ring
  | pred k ih =>
    obtain ⟨X, hc, hX⟩ := ih
    refine ⟨(ℓ.symm : Module.End R A) * X - (ℓ.symm : Module.End R A),
      (hDs.mul_right hc).sub_right hDs, ?_⟩
    have e : ((ℓ ^ (-(k : ℤ) - 1) : A ≃ₗ[R] A) : Module.End R A)
        = (ℓ.symm : Module.End R A) * ((ℓ ^ (-(k : ℤ)) : A ≃ₗ[R] A) : Module.End R A) := by
      ext y; rw [sub_eq_neg_add, zpow_add, zpow_neg_one]; rfl
    rw [e, eq_add_of_sub_eq hX]
    set s : Module.End R A := (ℓ.symm : Module.End R A)
    set l : Module.End R A := (ℓ : Module.End R A)
    have : s * ((l - 1) * X + 1) - 1 = (l - 1) * (s * X - s) + (s * l - 1) * X
        - (l * s - 1) * X + (l * s - 1) := by noncomm_ring
    rw [this, h1, h2]; simp

end GlobalTheory.UnipModHalf

namespace GlobalTheory.UnipModHalf

open Matrix

theorem unip_mod_half : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (L' : Submodule (𝓞 E) (Fin r → E)) (Mb P : Ideal (𝓞 E)), Mb ≤ P →
    ∀ {A : Type} [AddCommGroup A] [Module (𝓞 E) A] (φ : A ≃ₗ[𝓞 E] (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L'))))
      (ℓ : A ≃ₗ[𝓞 E] A) (n : ℤ),
    (∀ x : A, ((ℓ.toLinearMap - LinearMap.id : Module.End (𝓞 E) A) ^ r) x ∈ P • (⊤ : Submodule (𝓞 E) A)) →
    ∀ γ t : Matrix (Fin r) (Fin r) E, (∀ w ∈ L', Matrix.mulVec γ w ∈ L') → (∀ w ∈ L', Matrix.mulVec γ w - w ∈ Mb • L') →
    (∀ w : L', ∃ hw : Matrix.mulVec t w ∈ L',
      Submodule.Quotient.mk (p := Mb • (⊤ : Submodule (𝓞 E) L')) ⟨_, hw⟩ = φ ((ℓ ^ n) (φ.symm (Submodule.Quotient.mk w)))) →
    ∀ w ∈ L', Matrix.mulVec ((γ * t - 1) ^ r) w ∈ P • L' := by
  intro E _ _ r L' Mb P hMP A _ _ φ ℓ n hℓ γ t hγ hγ1 ht w hw

  let tL : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := (Matrix.mulVecLin t).restrictScalars (𝓞 E)
  let gL : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := (Matrix.mulVecLin γ).restrictScalars (𝓞 E)
  let T : Module.End (𝓞 E) L' := tL.restrict (fun x hx => (ht ⟨x, hx⟩).1)
  let G : Module.End (𝓞 E) L' := gL.restrict (fun x hx => hγ x hx)
  let U : Module.End (𝓞 E) L' := G * T - 1
  have hU : ∀ x : L', ((U x : L') : Fin r → E) = γ *ᵥ (t *ᵥ (x : Fin r → E)) - x := by
    intro x; rfl
  have hpow : ∀ k : ℕ, ∀ x : L', ((γ * t - 1) ^ k) *ᵥ (x : Fin r → E) = (((U ^ k) x : L') : Fin r → E) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, pow_succ', Module.End.mul_apply, hU,
        Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]

  have hsub : ∀ (I : Ideal (𝓞 E)) (z : L'), (z : Fin r → E) ∈ I • L' → z ∈ I • (⊤ : Submodule (𝓞 E) L') := by
    intro I z hz
    have e : I • L' = (I • (⊤ : Submodule (𝓞 E) L')).map L'.subtype := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top]
    rw [e] at hz
    obtain ⟨u, hu, huz⟩ := hz
    have : u = z := Subtype.ext huz
    exact this ▸ hu
  set ℓn : Module.End (𝓞 E) A := ((ℓ ^ n : A ≃ₗ[𝓞 E] A) : Module.End (𝓞 E) A)
  have hπU : ∀ x : L', (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (U x) = φ ((ℓn - 1) (φ.symm ((Mb • (⊤ : Submodule (𝓞 E) L')).mkQ x))) := by
    intro x
    have hG : (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (G (T x)) = (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (T x) := by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact hsub Mb _ (hγ1 _ (T x).2)
    have hT : (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ (T x) = φ ((ℓ ^ n) (φ.symm ((Mb • (⊤ : Submodule (𝓞 E) L')).mkQ x))) := (ht x).2
    simp only [U, LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply, map_sub, hG, hT]
    simp [ℓn]
  have hπUk : ∀ k : ℕ, ∀ x : L', (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ ((U ^ k) x) = φ (((ℓn - 1) ^ k) (φ.symm ((Mb • (⊤ : Submodule (𝓞 E) L')).mkQ x))) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, hπU, ih, LinearEquiv.symm_apply_apply, pow_succ',
        Module.End.mul_apply]

  obtain ⟨X, hc, hX⟩ := zpow_sub_one_eq_mul ℓ n
  have hℓ' : ∀ y : A, ((ℓn - 1) ^ r) y ∈ P • (⊤ : Submodule (𝓞 E) A) := by
    intro y
    rw [show ℓn - 1 = ((ℓ : Module.End (𝓞 E) A) - 1) * X from hX, hc.mul_pow, Module.End.mul_apply]
    have := hℓ ((X ^ r) y)
    rwa [← Module.End.one_eq_id] at this

  have hQ : (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ ((U ^ r) ⟨w, hw⟩) ∈ P • (⊤ : Submodule (𝓞 E) (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L')))) := by
    rw [hπUk]
    have hm : ((P • (⊤ : Submodule (𝓞 E) A)).map (φ : A →ₗ[𝓞 E] (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L'))))) ≤ P • ⊤ := by
      rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
    exact hm (Submodule.mem_map_of_mem (hℓ' _))
  have hL : (U ^ r) ⟨w, hw⟩ ∈ P • (⊤ : Submodule (𝓞 E) L') := by
    have e : P • (⊤ : Submodule (𝓞 E) (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L')))) = (P • (⊤ : Submodule (𝓞 E) L')).map (Mb • (⊤ : Submodule (𝓞 E) L')).mkQ := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    rw [e] at hQ
    have hQ' := Submodule.mem_comap.mpr hQ
    rw [Submodule.comap_map_mkQ] at hQ'
    have hle : Mb • (⊤ : Submodule (𝓞 E) L') ≤ P • (⊤ : Submodule (𝓞 E) L') := Submodule.smul_mono_left hMP
    exact (sup_le hle le_rfl) hQ'
  have key := hpow r ⟨w, hw⟩
  simp only at key
  rw [key]
  have e : P • L' = (P • (⊤ : Submodule (𝓞 E) L')).map L'.subtype := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  rw [e]
  exact Submodule.mem_map_of_mem hL

end GlobalTheory.UnipModHalf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentModIdealOfTrivialModHalfStatement
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_mod_ideal_of_trivial_mod_half : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (L' : Submodule (𝓞 E) (Fin r → E)) (Mb P : Ideal (𝓞 E)), Mb ≤ P →
    ∀ {A : Type} [AddCommGroup A] [Module (𝓞 E) A] (φ : A ≃ₗ[𝓞 E] (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L'))))
      (ℓ : A ≃ₗ[𝓞 E] A) (n : ℤ),
    (∀ x : A, ((ℓ.toLinearMap - LinearMap.id : Module.End (𝓞 E) A) ^ r) x ∈ P • (⊤ : Submodule (𝓞 E) A)) →
    ∀ γ t : Matrix (Fin r) (Fin r) E, (∀ w ∈ L', Matrix.mulVec γ w ∈ L') → (∀ w ∈ L', Matrix.mulVec γ w - w ∈ Mb • L') →
    (∀ w : L', ∃ hw : Matrix.mulVec t w ∈ L',
      Submodule.Quotient.mk (p := Mb • (⊤ : Submodule (𝓞 E) L')) ⟨_, hw⟩ = φ ((ℓ ^ n) (φ.symm (Submodule.Quotient.mk w)))) →
    ∀ w ∈ L', Matrix.mulVec ((γ * t - 1) ^ r) w ∈ P • L' := by
  first | exact @GlobalTheory.UnipModHalf.unip_mod_half | exact GlobalTheory.UnipModHalf.unip_mod_half | (intros; apply GlobalTheory.UnipModHalf.unip_mod_half <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUnipotentModIdealModConjIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUnipotentModIdealModConjIdeal
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipConjIdeal

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_sub_left (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G (x - y) z = ReciprocityTheory.ChartRestriction.G.FD.herm G x z - ReciprocityTheory.ChartRestriction.G.FD.herm G y z := by
  simp [ReciprocityTheory.ChartRestriction.G.FD.herm, sub_mul, Finset.sum_sub_distrib]

theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (a : E) (x z : Fin r → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G (a • x) z = a * ReciprocityTheory.ChartRestriction.G.FD.herm G x z := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem herm_smul_right (G : Matrix (Fin r) (Fin r) E) (a : E) (x z : Fin r → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G x (a • z) = ReciprocityTheory.ChartRestriction.G.FD.cc a * ReciprocityTheory.ChartRestriction.G.FD.herm G x z := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, ReciprocityTheory.ChartRestriction.G.FD.cc, Pi.smul_apply, smul_eq_mul, map_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem herm_adjoint_pow (G : Matrix (Fin r) (Fin r) E) (β : GL (Fin r) E)
    (hU : ∀ v w, ReciprocityTheory.ChartRestriction.G.FD.herm G ((β : Matrix (Fin r) (Fin r) E) *ᵥ v)
      ((β : Matrix (Fin r) (Fin r) E) *ᵥ w) = ReciprocityTheory.ChartRestriction.G.FD.herm G v w) (k : ℕ) (x y : Fin r → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm G ((((β : Matrix (Fin r) (Fin r) E) - 1) ^ k) *ᵥ x) y =
      ReciprocityTheory.ChartRestriction.G.FD.herm G x (((((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) - 1) ^ k) *ᵥ y) := by
  have step : ∀ x z : Fin r → E, ReciprocityTheory.ChartRestriction.G.FD.herm G (((β : Matrix (Fin r) (Fin r) E) - 1) *ᵥ x) z =
      ReciprocityTheory.ChartRestriction.G.FD.herm G x ((((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) - 1) *ᵥ z) := by
    intro x z
    have hz : (β : Matrix (Fin r) (Fin r) E) *ᵥ (((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ z) = z := by
      rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
    rw [sub_mulVec, sub_mulVec, one_mulVec, one_mulVec, herm_sub_left]
    conv_lhs => rw [← hz, hU]
    simp [ReciprocityTheory.ChartRestriction.G.FD.herm, Finset.sum_sub_distrib, mul_sub, ReciprocityTheory.ChartRestriction.G.FD.cc]
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mulVec_mulVec, ih, step, mulVec_mulVec, ← pow_succ']

end GlobalTheory.UnipConjIdeal

namespace GlobalTheory.UnipConjIdeal

open Matrix

theorem pow_sub_one_mem_conj_ideal_smul : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r) (β : GL (Fin r) E),
    (∀ v w, herm X.Gm (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v) (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) w) =
      herm X.Gm v w) →
    (∀ v, v ∈ X.L' ↔ Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v ∈ X.L') →
    ∀ P : Ideal (𝓞 E), (∀ v ∈ X.L', Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈ P • X.L') →
    ∀ v ∈ X.L', Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈
      P.map ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E ≃+* 𝓞 E) : 𝓞 E →+* 𝓞 E) • X.L' := by
  intro E _ _ _ r X β hU hL P hP v hv
  have hsm : ∀ (p : 𝓞 E) (w : Fin r → E), p • w = (p : E) • w := fun p w => (algebraMap_smul E p w).symm
  set βm : Matrix (Fin r) (Fin r) E := (β : Matrix (Fin r) (Fin r) E) with hβm
  set βi : Matrix (Fin r) (Fin r) E := ((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hβi
  have h1 : βi * βm = 1 := Units.inv_mul β
  have h2 : βm * βi = 1 := Units.mul_inv β

  have hinv : ∀ w ∈ X.L', βi *ᵥ w ∈ X.L' := by
    intro w hw
    refine (hL _).mpr ?_
    rw [mulVec_mulVec, h2, one_mulVec]; exact hw
  have hBpow : ∀ k : ℕ, ∀ w ∈ X.L', ((-βi) ^ k) *ᵥ w ∈ X.L' := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
      intro w hw
      rw [pow_succ', ← mulVec_mulVec, neg_mulVec]
      exact X.L'.neg_mem (hinv _ (ih w hw))

  have hfac : βi - 1 = (-βi) * (βm - 1) := by
    rw [neg_mul, mul_sub, h1, mul_one]; abel
  have hcomm : Commute (-βi) (βm - 1) := by
    unfold Commute SemiconjBy
    rw [neg_mul, mul_neg, mul_sub, sub_mul, h1, h2, mul_one, one_mul]
  have hadjpow : (βi - 1) ^ r = (-βi) ^ r * (βm - 1) ^ r := by
    rw [hfac, hcomm.mul_pow]
  by_cases hP0 : P = ⊥
  · subst hP0
    have h0 := hP v hv
    rw [Submodule.bot_smul, Submodule.mem_bot] at h0
    rw [h0]; exact zero_mem _
  obtain ⟨c, hcP, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  obtain ⟨P', hPP'⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem P).mpr hcP)
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc0

  have hi : ∀ w ∈ P • X.L', ∀ p' ∈ P', ((c : E)⁻¹ * p') • w ∈ X.L' := by
    intro w hw
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro p hp l hl p' hp'
      have hm : p * p' ∈ Ideal.span {c} := by rw [hPP']; exact Ideal.mul_mem_mul hp hp'
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hm
      have : ((c : E)⁻¹ * p') • (p • l) = t • l := by
        rw [hsm, hsm, smul_smul]
        congr 1
        have : (p : E) * p' = t * c := by exact_mod_cast ht.symm
        field_simp
        linear_combination this
      rw [this]; exact X.L'.smul_mem t hl
    · intro x y hx hy p' hp'
      rw [smul_add]; exact X.L'.add_mem (hx p' hp') (hy p' hp')

  have hii : ∀ z ∈ X.L', ∀ p' ∈ P', ((c : E)⁻¹ * p') • (((βi - 1) ^ r) *ᵥ z) ∈ X.L' := by
    intro z hz p' hp'
    rw [hadjpow, ← mulVec_mulVec, ← mulVec_smul]
    exact hBpow r _ (hi _ (hP z hz) p' hp')

  set σ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv with hσdef
  have hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = ReciprocityTheory.ChartRestriction.G.FD.cc (x : E) := fun x => rfl
  have hcc : ∀ x : E, ReciprocityTheory.ChartRestriction.G.FD.cc (ReciprocityTheory.ChartRestriction.G.FD.cc x) = x := by
    intro x; simp [ReciprocityTheory.ChartRestriction.G.FD.cc]

  have hiii : ∀ p' ∈ P', ((σ c : E)⁻¹ * (σ p' : E)) • (((βm - 1) ^ r) *ᵥ v) ∈ X.L' := by
    intro p' hp'
    refine X.L'_dual _ fun z hz => ?_
    rw [herm_smul_left, herm_adjoint_pow X.Gm β hU r v z]
    have : (σ c : E)⁻¹ * (σ p' : E) = ReciprocityTheory.ChartRestriction.G.FD.cc ((c : E)⁻¹ * p') := by
      rw [hσ, hσ, ReciprocityTheory.ChartRestriction.G.FD.cc, ReciprocityTheory.ChartRestriction.G.FD.cc, ReciprocityTheory.ChartRestriction.G.FD.cc, map_mul, map_inv₀]
    rw [this, ← herm_smul_right]
    exact X.L'_int v hv _ (hii z hz p' hp')

  have hmul : P.map (σ : 𝓞 E →+* 𝓞 E) * P'.map (σ : 𝓞 E →+* 𝓞 E) = Ideal.span {σ c} := by
    rw [← Ideal.map_mul, ← hPP', Ideal.map_span, Set.image_singleton]; rfl
  have hd : σ c ∈ P.map (σ : 𝓞 E →+* 𝓞 E) * P'.map (σ : 𝓞 E →+* 𝓞 E) := by
    rw [hmul]; exact Ideal.mem_span_singleton_self _
  have hσc : (σ c : E) ≠ 0 := by
    intro h; apply hcE
    have := congrArg ReciprocityTheory.ChartRestriction.G.FD.cc h
    rw [hσ, hcc] at this
    simpa [ReciprocityTheory.ChartRestriction.G.FD.cc] using this
  have key : ∀ u, u ∈ P.map (σ : 𝓞 E →+* 𝓞 E) * P'.map (σ : 𝓞 E →+* 𝓞 E) →
      ((σ c : E)⁻¹ * u) • (((βm - 1) ^ r) *ᵥ v) ∈ P.map (σ : 𝓞 E →+* 𝓞 E) • X.L' := by
    intro u hu
    refine Submodule.mul_induction_on hu ?_ ?_
    · intro q hq q' hq'
      obtain ⟨p', hp', rfl⟩ := (Ideal.mem_map_of_equiv σ q').mp hq'
      have : ((σ c : E)⁻¹ * ((q * σ p' : 𝓞 E) : E)) • (((βm - 1) ^ r) *ᵥ v) =
          q • (((σ c : E)⁻¹ * (σ p' : E)) • (((βm - 1) ^ r) *ᵥ v)) := by
        rw [hsm, smul_smul]; congr 1; push_cast; ring
      rw [this]
      exact Submodule.smul_mem_smul hq (hiii p' hp')
    · intro x y hx hy
      rw [show ((x + y : 𝓞 E) : E) = (x : E) + y by push_cast; rfl, mul_add, add_smul]
      exact Submodule.add_mem _ hx hy
  have := key _ hd
  rwa [inv_mul_cancel₀ hσc, one_smul] at this

end GlobalTheory.UnipConjIdeal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUnipotentModIdealModConjIdealStatement
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_unipotent_mod_ideal_mod_conjIdeal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r) (β : GL (Fin r) E),
    (∀ v w, herm X.Gm (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v) (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) w) =
      herm X.Gm v w) →
    (∀ v, v ∈ X.L' ↔ Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v ∈ X.L') →
    ∀ P : Ideal (𝓞 E), (∀ v ∈ X.L', Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈ P • X.L') →
    ∀ v ∈ X.L', Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈
      P.map ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E ≃+* 𝓞 E) : 𝓞 E →+* 𝓞 E) • X.L' := by
  first | exact @GlobalTheory.UnipConjIdeal.pow_sub_one_mem_conj_ideal_smul | exact GlobalTheory.UnipConjIdeal.pow_sub_one_mem_conj_ideal_smul | (intros; apply GlobalTheory.UnipConjIdeal.pow_sub_one_mem_conj_ideal_smul <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem splitsCompletely_typePrime (D : D7) (k : Fin 2) : SplitsCompletely D.host.E (D.host.g k) := by
  refine ⟨D.host.g_prime k, ?_⟩
  have hg0 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.host.g_prime k).ne_zero
  have h := D.nd.g_split k
  rw [← h]
  have : {P : Ideal (𝓞 D.host.E) | P.IsPrime ∧ ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P} =
      (fun v : HeightOneSpectrum (𝓞 D.host.E) => v.asIdeal) '' {v : HeightOneSpectrum (𝓞 D.host.E) | ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal} := by
    ext P
    constructor
    · rintro ⟨hP, hg⟩
      have hne : P ≠ ⊥ := fun h0 => hg0 (by rw [h0] at hg; simpa using hg)
      exact ⟨⟨P, hP, hne⟩, hg, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.isPrime, hv⟩
  rw [this, Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)]
  rfl

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem half_le_plGw (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (k : Fin 2) (v : D.nd.PlG k) :
    p.T.Q.l.Mb ≤ (D.naut.plGw k v).asIdeal := by
  rw [h.half]
  obtain ⟨plg, -, hplg, -, -, -⟩ := p.grpRecPin
  have hmem : D.naut.plGw k v ∈ (R2 p).Pg := by
    rw [← hplg ⟨k, v⟩]
    exact (plg ⟨k, v⟩).2
  exact (Ideal.prod_le_inf).trans (Finset.inf_le hmem)

theorem levelCondition_restrict_of_halfUnipotent (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m) {C : Type} [Finite C]
    [MulAction p.P.Gp C] (M : TwoLevels D.host.E D.R.r p.P.Gp C) (ka : Wt M.Ψ D.R.r) (hg : ∀ k : Fin 2, 3 * D.R.r < D.host.g k)
    (hM : RunModel p r h i M ka) : ∀ H : Subgroup p.P.Gp, HalfUnip p H → LevelHyp (sub M H) := by
  intro H hH
  obtain ⟨k, hk⟩ := hH
  obtain ⟨v0, e, -, -, -, hd1, φ, hd2⟩ := hM
  refine ⟨D.host.g k, splitsCompletely_typePrime D k, hg k, ?_⟩
  intro c β hβ P hP hgP
  obtain ⟨u, huc, γ, hγ, rfl⟩ := hβ
  have huc' : (u : p.P.Gp) • c = c := huc
  have hγL : ∀ w, w ∈ (M.comp c).L' ↔ Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ (M.comp c).L' :=
    M.Γ_L' c γ hγ
  have htL : ∀ w, w ∈ (M.comp c).L' ↔
      Matrix.mulVec (M.tr u c : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ (M.comp c).L' := by
    intro w
    have := M.tr_L' u c w
    rwa [huc'] at this
  have half : ∀ v : D.nd.PlG k, ∀ w ∈ (M.comp c).L',
      Matrix.mulVec ((((γ * M.tr u c : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) - 1) ^ D.R.r) w ∈
        (D.naut.plGw k v).asIdeal • (M.comp c).L' := by
    intro v w hw
    obtain ⟨n, hn⟩ := hd2 c u huc'
    rw [Units.val_mul]
    exact GlobalTheory.T.unipotent_mod_ideal_of_trivial_mod_half _ _ _ (half_le_plGw p r h k v) (φ c) (r.lev i u) n (GlobalTheory.T.levelChange_unitriangular_unipotent_modPlace p r h i u k v (hk u u.2 v)) _ _ (fun w hw => (hγL w).1 hw)
      (hd1 c γ hγ) hn w hw
  obtain ⟨v, rfl | rfl⟩ := GlobalTheory.T.prime_over_typePrime_fixedPlace_or_conj D k P hP hgP
  · exact half v
  · refine GlobalTheory.T.unitary_unipotent_mod_ideal_mod_conjIdeal (M.comp c) (γ * M.tr u c) ?_ ?_ _ (half v)
    · intro a b
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ((M.comp c).Γ_stab γ hγ).1, M.comp_Gm c, M.tr_herm]
    · intro a
      rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      exact (htL a).trans (hγL _)

end GlobalTheory.ShareOn

end
