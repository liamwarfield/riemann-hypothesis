module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsGenerateIdealAlongComapOfTwisted
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackO1IsoBlowupTwistDual
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackO1IsoBlowupTwistDual
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ProjSpace GlobalTheory.Cartier

namespace GlobalTheory.ProjBlowup

private theorem gm_id_val_eq_germ {X : Scheme.{0}} {V : X.Opens} (y : X) (hy : y ∈ V) (a : Γ(X, V)ˣ) :
    (gm (𝟙 X) y V a).val = X.presheaf.germ V y hy a.val := by
  simp only [gm, pullU, dif_pos (show (𝟙 X) y ∈ V from hy)]
  simp
  rfl

private theorem germ_res_val_eq_germ {X : Scheme.{0}} {V W : X.Opens} (h : W ≤ V) (y : X) (hy : y ∈ W)
    (a : Γ(X, V)ˣ) : X.presheaf.germ W y hy (res h a).val = X.presheaf.germ V y (h hy) a.val := by
  simp [res]

theorem isLB_of_chartPull_id {X : Scheme.{0}} {A B : LB X} (hB : B.IsLB) (a : ChartPull A B (𝟙 X))
    (hc : ⨆ i, A.U i = ⊤) : A.IsLB := {
  cover := hc
  g_self := by
    obtain ⟨idx, hle, hg⟩ := a
    intro i
    apply Units.ext
    refine TopCat.Presheaf.section_ext X.sheaf _ _ _ (fun y hy => ?_)
    have hy' : y ∈ B.U (idx i) := hle i hy
    change X.presheaf.germ (A.U i) y hy (res _ (A.g i i)).val = X.presheaf.germ (A.U i) y hy (1 : Γ(X, A.U i)ˣ).val
    rw [germ_res_val_eq_germ, ← gm_id_val_eq_germ, hg y i i hy hy,
      gm_id_val_eq_germ y (show y ∈ B.U (idx i) ⊓ B.U (idx i) from ⟨hy', hy'⟩),
      ← germ_res_val_eq_germ (le_inf le_rfl le_rfl : B.U (idx i) ≤ _) y hy', hB.g_self (idx i)]
    simp
  cocycle := by
    obtain ⟨idx, hle, hg⟩ := a
    intro i j k
    apply Units.ext
    refine TopCat.Presheaf.section_ext X.sheaf _ _ _ (fun y hy => ?_)
    have hi : y ∈ A.U i := hy.1.1
    have hj : y ∈ A.U j := hy.1.2
    have hk : y ∈ A.U k := hy.2
    have hi' : y ∈ B.U (idx i) := hle i hi
    have hj' : y ∈ B.U (idx j) := hle j hj
    have hk' : y ∈ B.U (idx k) := hle k hk
    change X.presheaf.germ _ y hy ((res _ (A.g i j)).val * (res _ (A.g j k)).val) =
      X.presheaf.germ _ y hy (res _ (A.g i k)).val
    rw [map_mul, germ_res_val_eq_germ, germ_res_val_eq_germ, germ_res_val_eq_germ, ← gm_id_val_eq_germ, ← gm_id_val_eq_germ,
      ← gm_id_val_eq_germ, hg y i j hi hj, hg y j k hj hk, hg y i k hi hk,
      gm_id_val_eq_germ y (show y ∈ B.U (idx i) ⊓ B.U (idx j) from ⟨hi', hj'⟩),
      gm_id_val_eq_germ y (show y ∈ B.U (idx j) ⊓ B.U (idx k) from ⟨hj', hk'⟩),
      gm_id_val_eq_germ y (show y ∈ B.U (idx i) ⊓ B.U (idx k) from ⟨hi', hk'⟩)]
    have hB3 := congrArg (fun u : Γ(X, B.U (idx i) ⊓ B.U (idx j) ⊓ B.U (idx k))ˣ =>
      X.presheaf.germ _ y (show y ∈ B.U (idx i) ⊓ B.U (idx j) ⊓ B.U (idx k) from ⟨⟨hi', hj'⟩, hk'⟩) u.val)
      (hB.cocycle (idx i) (idx j) (idx k))
    simp only [Units.val_mul, map_mul, germ_res_val_eq_germ] at hB3
    exact hB3 }

private theorem gm_id_res_eq {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (y : X) (hy : y ∈ V)
    (a : Γ(X, U)ˣ) : gm (𝟙 X) y V (res h a) = gm (𝟙 X) y U a := by
  apply Units.ext
  rw [gm_id_val_eq_germ y hy, gm_id_val_eq_germ y (h hy), germ_res_val_eq_germ]

private theorem gs_resG_eq {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {U V : X.Opens} (h : V ≤ U) (hy : f y ∈ V)
    (a : Γ(X, U)) : gs f y V (resG X h a) = gs f y U a :=
  gs_res f y h hy a

private theorem mul_eq_unit_mul_of_relations {S : Type _} [CommRing S] (G t t' : Sˣ) (ap aq fp fq sp sq : S)
    (h5 : (t' : S) * t = 1) (E1 : sp = ap * fp) (E2 : sq = aq * fq) (E3 : sp = G * sq) (E4 : fp = t * fq) :
    ap * fp = ((G * t' : Sˣ) : S) * aq * fp := by
  rw [Units.val_mul]
  linear_combination (-1 : S) * E1 + E3 + (G : S) * E2 - ((G : S) * aq * fq) * h5 - ((G : S) * t' * aq) * E4

theorem lbIso_pull_O1_of_proportional (R : Type) [CommRing R] (X W : Scheme.{0}) (J : X.IdealSheafData)
    (L₀ : LB X) (m : ℕ) (σ : Fin (m + 1) → L₀.Sec) (g : W ⟶ X) (ψ : W ⟶ PSpace R m) (D : GlobalTheory.EffCartierData W)
    (hL : L₀.IsLB) (hJ : Generates J σ) (hP : Proportional σ g ψ) (hD : D.idealSheaf = J.comap g) :
    LBIso ((GlobalTheory.ProjSpace.O1 R m).pull ψ) (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)) := by
  classical
  have hT : (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)).IsLB :=
    GlobalTheory.CechPic.isLB_tens (pull_isLB hL g) (GlobalTheory.CechPic.isLB_dual D.isLB_lb)
  have hGA := generatesAlong_comap_of_generates X W J L₀ m σ g hJ
  rw [← hD] at hGA
  have loc : ∀ (k : L₀.ι) (d : D.ι) (A : W.affineOpens) (hk : A.1 ≤ g ⁻¹ᵁ L₀.U k) (hd : A.1 ≤ D.U d),
      ∃ a c : Fin (m + 1) → Γ(W, A.1), (∀ j, (g.appLE (L₀.U k) A.1 hk).hom ((σ j).f k) =
        a j * resG W hd (D.f d)) ∧ ∑ j, c j * a j = 1 := by
    intro k d A hk hd
    refine exists_quot_of_span_eq (D.regular d A.1 hd) ?_
    rw [← D.ideal_idealSheaf A d hd, hGA.2 k A hk]
  let Idx := {p : L₀.ι × D.ι × W.affineOpens // p.2.2.1 ≤ g ⁻¹ᵁ L₀.U p.1 ∧ p.2.2.1 ≤ D.U p.2.1}
  let tI : Idx → (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)).ι := fun p => (fun _ => p.1.1, p.1.2.1)
  have hle : ∀ p : Idx, p.1.2.2.1 ≤ (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)).U (tI p) :=
    fun p y hy => ⟨mem_pull.2 (p.2.1 hy), p.2.2 hy⟩
  let N : LB W :=
    { ι := Idx
      U := fun p => p.1.2.2.1
      g := fun p q => res (inf_le_inf (hle p) (hle q))
        ((GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)).g (tI p) (tI q)) }
  let cp : ChartPull N (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)) (𝟙 W) :=
    ⟨tI, hle, fun y p q hp hq => gm_id_res_eq _ y (show y ∈ N.U p ⊓ N.U q from ⟨hp, hq⟩) _⟩
  have hcov : ⨆ p, N.U p = ⊤ := by
    refine eq_top_iff.2 (fun y _ => ?_)
    have hgy : g y ∈ ⨆ k, L₀.U k := by rw [hL.cover]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hgy
    obtain ⟨d, hd⟩ := D.exists_mem y
    obtain ⟨A, hyA, hA⟩ := GlobalTheory.EffCartierData.exists_affine_le (X := W)
      (show y ∈ g ⁻¹ᵁ L₀.U k ⊓ D.U d from ⟨hk, hd⟩)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(k, d, A), hA.trans inf_le_left, hA.trans inf_le_right⟩, hyA⟩
  have hN : N.IsLB := isLB_of_chartPull_id hT cp hcov
  have H2 : LBIso N (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)) := GlobalTheory.CechPic.iso_of_chart hT cp
  choose af cf haf hcf using fun p : Idx => loc p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2
  have hcomp : ∀ (j : Fin (m + 1)) (p q : Idx),
      resG W (inf_le_left : N.U p ⊓ N.U q ≤ N.U p) (af p j) =
        (N.g p q : Γ(W, N.U p ⊓ N.U q)) * resG W (inf_le_right : N.U p ⊓ N.U q ≤ N.U q) (af q j) := by
    intro j p q
    have hV : N.U p ⊓ N.U q ≤ D.U p.1.2.1 := inf_le_left.trans p.2.2
    refine (mul_cancel_right_mem_nonZeroDivisors (D.regular p.1.2.1 _ hV)).1 ?_
    refine fn_ext (fun y hy => ?_)
    have hyp : y ∈ p.1.2.2.1 := hy.1
    have hyq : y ∈ q.1.2.2.1 := hy.2
    rw [gs_mul (𝟙 W) y _ hy, gs_mul (𝟙 W) y _ hy, gs_mul (𝟙 W) y _ hy, gs_resG_eq _ y _ hy,
      gs_resG_eq _ y _ hy, gs_resG_eq _ y _ hy, gs_unit (𝟙 W) y _ hy]
    change _ = (gm (𝟙 W) y _ (res _ _)).val * _ * _
    rw [gm_id_res_eq _ y hy, GlobalTheory.CechPic.gm_tens _ _ _ y _ _ (hle p hyp) (hle q hyq),
      gm_pull_g L₀ g (𝟙 W) y _ _ (hle p hyp).1 (hle q hyq).1]
    have E1 := congrArg (gs (𝟙 W) y (N.U p)) (haf p j)
    rw [gs_appLE g _ _ _ (𝟙 W) y hyp, gs_mul _ _ _ hyp, gs_resG_eq _ _ _ hyp] at E1
    have E2 := congrArg (gs (𝟙 W) y (N.U q)) (haf q j)
    rw [gs_appLE g _ _ _ (𝟙 W) y hyq, gs_mul _ _ _ hyq, gs_resG_eq _ _ _ hyq] at E2
    have hk2 : (𝟙 W ≫ g) y ∈ L₀.U p.1.1 ⊓ L₀.U q.1.1 := ⟨p.2.1 hyp, q.2.1 hyq⟩
    have E3 := congrArg (gs (𝟙 W ≫ g) y (L₀.U p.1.1 ⊓ L₀.U q.1.1)) ((σ j).compat p.1.1 q.1.1)
    rw [gs_res _ _ _ hk2, gs_mul _ _ _ hk2, gs_unit _ _ _ hk2, gs_res _ _ _ hk2] at E3
    have hd2 : (𝟙 W) y ∈ D.U p.1.2.1 ⊓ D.U q.1.2.1 := ⟨p.2.2 hyp, q.2.2 hyq⟩
    have E4 := congrArg (gs (𝟙 W) y (D.U p.1.2.1 ⊓ D.U q.1.2.1)) (D.trans_spec p.1.2.1 q.1.2.1)
    rw [gs_resG_eq _ _ _ hd2, gs_mul _ _ _ hd2, gs_unit _ _ _ hd2, gs_resG_eq _ _ _ hd2] at E4
    have E5 : ((gm (𝟙 W) y ((GlobalTheory.CechPic.dual D.lb).U (tI p).2 ⊓ (GlobalTheory.CechPic.dual D.lb).U (tI q).2))
        ((GlobalTheory.CechPic.dual D.lb).g (tI p).2 (tI q).2)).val *
        (gm (𝟙 W) y (D.U p.1.2.1 ⊓ D.U q.1.2.1) (D.trans p.1.2.1 q.1.2.1)).val = 1 := by
      change (gm (𝟙 W) y (D.U p.1.2.1 ⊓ D.U q.1.2.1) (D.trans p.1.2.1 q.1.2.1)⁻¹).val *
        (gm (𝟙 W) y (D.U p.1.2.1 ⊓ D.U q.1.2.1) (D.trans p.1.2.1 q.1.2.1)).val = 1
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    exact mul_eq_unit_mul_of_relations _ _ _ _ _ _ _ _ _ E5 E1 E2 E3 E4
  let t : Fin (m + 1) → N.Sec := fun j => { f := fun p => af p j, compat := fun p q => hcomp j p q }
  have ht : ⨆ i, Out.nonzeroLocus (t i) = ⊤ := by
    refine eq_top_iff.2 (fun y _ => ?_)
    have hy : y ∈ ⨆ p, N.U p := by rw [hcov]; trivial
    obtain ⟨p, hyp⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨j, hj⟩ := exists_mem_basicOpen_of_sum (hcf p) hyp
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, GlobalTheory.basicOpen_le_nonzeroLocus (t j) p hj⟩
  have hch : ∀ y : W, ∃ i, y ∈ ψ ⁻¹ᵁ chart R m i := by
    intro y
    have h := iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord R m) ψ
    have hy : y ∈ ⨆ i, Out.nonzeroLocus (secPull (coord R m i) ψ) := by rw [h]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    refine ⟨i, ?_⟩
    have e := toProj_preimage_chart (ψ ≫ PSpace.str R m) (fun i => secPull (coord R m i) ψ)
      (iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord R m) ψ) i
    rw [toProj_secPull_coord] at e
    rw [e]
    exact hi
  have hψ : ψ = toProj (ψ ≫ PSpace.str R m) t ht := by
    refine eq_toProj_of_locally (s := t) ht rfl (fun y => ?_)
    have hy : y ∈ ⨆ p, N.U p := by rw [hcov]; trivial
    obtain ⟨p, hyp⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨i, hi⟩ := hch y
    refine ⟨N.U p ⊓ ψ ⁻¹ᵁ chart R m i, ⟨hyp, hi⟩, p, inf_le_left, i, inf_le_right,
      resG W inf_le_left (af p i), fun j => ?_⟩
    have hV : N.U p ⊓ ψ ⁻¹ᵁ chart R m i ≤ D.U p.1.2.1 := inf_le_left.trans p.2.2
    have hk' : N.U p ⊓ ψ ⁻¹ᵁ chart R m i ≤ g ⁻¹ᵁ L₀.U p.1.1 := inf_le_left.trans p.2.1
    refine (mul_cancel_right_mem_nonZeroDivisors (D.regular p.1.2.1 _ hV)).1 ?_
    refine fn_ext (fun z hz => ?_)
    have hzp : z ∈ N.U p := hz.1
    have Ej := congrArg (gs (𝟙 W) z (N.U p)) (haf p j)
    rw [gs_appLE g _ _ _ (𝟙 W) z hzp, gs_mul _ _ _ hzp, gs_resG_eq _ _ _ hzp] at Ej
    have Ei := congrArg (gs (𝟙 W) z (N.U p)) (haf p i)
    rw [gs_appLE g _ _ _ (𝟙 W) z hzp, gs_mul _ _ _ hzp, gs_resG_eq _ _ _ hzp] at Ei
    have Eh := congrArg (gs (𝟙 W) z _) (hP _ p.1.1 hk' i inf_le_right j)
    rw [gs_appLE g _ _ _ (𝟙 W) z hz, gs_mul _ _ _ hz, gs_appLE g _ _ _ (𝟙 W) z hz] at Eh
    rw [gs_mul _ _ _ hz, gs_mul _ _ _ hz, gs_mul _ _ _ hz, gs_resG_eq _ _ _ hz, gs_resG_eq _ _ _ hz,
      gs_resG_eq _ _ _ hz]
    linear_combination (-1 : W.presheaf.stalk z) * Ej + Eh + gs (𝟙 W) z _ (pullRatio ψ _ i inf_le_right j) * Ei
  have H1 : LBIso ((O1 R m).pull ψ) N := by
    have h := lbIso_pullback_O1_toProj (ψ ≫ PSpace.str R m) t ht
    rw [← hψ] at h
    exact h
  exact LBIso.trans (pull_isLB (O1_isLB R m) ψ) hN hT H1 H2

end GlobalTheory.ProjBlowup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackO1IsoBlowupTwistDualStatement
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_O1_iso_blowup_twist_dual : ∀ (R : Type) [CommRing R] (X W : Scheme.{0}) (J : X.IdealSheafData) (L₀ : LB X) (m : ℕ)
    (σ : Fin (m + 1) → L₀.Sec) (g : W ⟶ X) (ψ : W ⟶ PSpace R m) (D : GlobalTheory.EffCartierData W), L₀.IsLB →
    GlobalTheory.ProjBlowup.Generates J σ → GlobalTheory.ProjBlowup.Proportional σ g ψ → D.idealSheaf = J.comap g →
    LBIso ((GlobalTheory.ProjSpace.O1 R m).pull ψ) (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)) := by
  first | exact @GlobalTheory.ProjBlowup.lbIso_pull_O1_of_proportional | exact GlobalTheory.ProjBlowup.lbIso_pull_O1_of_proportional | (intros; apply GlobalTheory.ProjBlowup.lbIso_pull_O1_of_proportional <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmExtensionLocalFieldProductRingExistsSmulEq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveSeqNormOne
namespace GlobalTheory.InjectiveSeqNormOne

theorem exists_injective_seq_norm_one {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) :
    ∃ a : ℕ → E, Function.Injective a ∧ ∀ k : ℕ, a k * σ (a k) = 1 := by
  obtain ⟨-, hE, -, hσ⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  have hinv : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hσ, hσ, star_star])
  have hy : ∃ y, σ y ≠ y := by
    by_contra hcon
    push Not at hcon
    have hc : (NumberField.InfinitePlace.mk τ).IsComplex := hE.isComplex _
    rw [NumberField.InfinitePlace.isComplex_mk_iff] at hc
    apply hc
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hσ τ x
    rw [hcon] at this
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    exact this.symm
  obtain ⟨y, hy⟩ := hy
  have h1 : ∀ k : ℕ, (k : E) + y ≠ 0 := by
    intro k hk
    apply hy
    have : y = -(k : E) := by linear_combination hk
    rw [this, map_neg, map_natCast]
  have h2 : ∀ k : ℕ, (k : E) + σ y ≠ 0 := by
    intro k hk
    apply h1 k
    have := congrArg σ hk
    rwa [map_add, map_natCast, hinv, map_zero] at this
  refine ⟨fun k => ((k : E) + y) / ((k : E) + σ y), ?_, ?_⟩
  · intro k m hkm
    have hkm' := (div_eq_div_iff (h2 k) (h2 m)).1 hkm
    have h3 : ((k : E) - m) * (σ y - y) = 0 := by linear_combination hkm'
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact_mod_cast sub_eq_zero.1 h4
    · exact absurd (sub_eq_zero.1 h4) hy
  · intro k
    have a1 := h1 k
    have a2 := h2 k
    simp only [map_div₀, map_add (f := _), map_natCast, hinv]
    field_simp

end GlobalTheory.InjectiveSeqNormOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmExtensionLocalFieldProductRingExistsSmulEq
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeWittLoc

open Matrix Formalism.UG

theorem exists_quasiReflection {S : Type} [CommRing S] (s : S →+* S) (hs : ∀ a, s (s a) = a) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, s (J j i) = J i j) (w : Fin n → S) (c : S)
    (hc : c + s c = c * s c * hform s J w w) :
    ∃ g g' : Matrix (Fin n) (Fin n) S, g' * g = 1 ∧ cT s g * J = J * g' ∧
      ∀ z, g *ᵥ z = z - (c * hform s J w z) • w := by
  let r : Fin n → S := fun j => ∑ i, s (w i) * J i j
  have hr : ∀ z, r ⬝ᵥ z = hform s J w z := fun z => by
    simp only [r, dotProduct, hform, Finset.sum_mul]
    exact Finset.sum_comm
  let P : Matrix (Fin n) (Fin n) S := vecMulVec w r
  have hPP : P * P = hform s J w w • P := by
    ext i j
    rw [← hr]
    simp only [P, Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hPJ : cT s P * J = J * P := by
    ext i j
    have h1 : s (r i) = ∑ k, J i k * w k := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [r, map_sum, map_mul, hs, hJ]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [P, cT, Matrix.mul_apply, vecMulVec_apply, transpose_apply, map_apply, map_mul]
    calc ∑ k, s (w k) * s (r i) * J k j = s (r i) * r j := by
          simp only [r, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = _ := by
          rw [h1, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
  refine ⟨1 - c • P, 1 - s c • P, ?_, ?_, fun z => ?_⟩
  · rw [sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, smul_mul_smul_comm, hPP, smul_smul,
      mul_comm (s c) c, ← hc, add_smul]
    abel
  · have : cT s (1 - c • P) = 1 - s c • cT s P := by
      ext i j
      simp [cT, Matrix.one_apply, eq_comm]
    rw [this, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, hPJ, Matrix.one_mul,
      Matrix.mul_one]
  · rw [sub_mulVec, one_mulVec, smul_mulVec, ← hr, ← smul_smul]
    congr 1
    ext i
    simp only [P, Matrix.mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem exists_unitary {S : Type} [CommRing S] (s : S →+* S) (hs : ∀ a, s (s a) = a) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, s (J j i) = J i j) (x y : Fin n → S) (β v : S)
    (hx : hform s J x x = β) (hy : hform s J y y = β) (hv : v * s v = 1)
    (hD : IsUnit (β - v * hform s J y x)) :
    ∃ γ : GL (Fin n) S, cT s γ.1 * J * γ.1 = J ∧ γ.1 *ᵥ x = y := by
  have hsym : ∀ a b, s (hform s J a b) = hform s J b a := fun a b => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hform, map_sum, map_mul, hs, hJ]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hl : ∀ z, hform s J (x - s v • y) z = hform s J x z - v * hform s J y z := fun z => by
    simp only [hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, hs,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hrr : ∀ z, hform s J z (x - s v • y) = hform s J z x - s v * hform s J z y := fun z => by
    simp only [hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨c, hc⟩ := hD.exists_left_inv
  have hβ : s β = β := by rw [← hx, hsym]
  have hc' : s c * (β - s v * hform s J x y) = 1 := by
    have := congrArg s hc
    rwa [map_mul, map_sub, map_mul, hsym, hβ, map_one] at this
  obtain ⟨g, g', h1, h2, h3⟩ := exists_quasiReflection s hs J hJ (x - s v • y) c (by
    rw [hl, hrr, hrr, hx, hy]
    linear_combination (-c) * hc' - s c * hc - c * s c * β * hv)
  have h4 : g * g' = 1 := mul_eq_one_comm.1 h1
  refine ⟨⟨v • g, s v • g', ?_, ?_⟩, ?_, ?_⟩
  · rw [smul_mul_smul_comm, hv, h4, one_smul]
  · rw [smul_mul_smul_comm, mul_comm, hv, h1, one_smul]
  · have : cT s (v • g) = s v • cT s g := by
      ext i j
      simp [cT]
    show cT s (v • g) * J * (v • g) = J
    rw [this, Matrix.smul_mul, smul_mul_smul_comm, h2, Matrix.mul_assoc, h1, mul_comm, hv, one_smul,
      Matrix.mul_one]
  · show (v • g) *ᵥ x = y
    rw [smul_mulVec, h3, hl, hx, hc, one_smul, sub_sub_cancel, smul_smul, hv, one_smul]

theorem exists_isUnit_sub {S : Type} [CommRing S] [Finite (MaximalSpectrum S)] (v : ℕ → S)
    (hv : ∀ k l, k ≠ l → IsUnit (v k - v l)) (β t : S) (hβ : IsUnit β) :
    ∃ k, IsUnit (β - v k * t) := by
  by_contra h
  push Not at h
  choose m hm hmem using fun k => exists_max_ideal_of_mem_nonunits (h k)
  obtain ⟨k, l, hkl, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k => (⟨m k, hm k⟩ : MaximalSpectrum S))
  have he' : m k = m l := congrArg MaximalSpectrum.asIdeal he
  have h1 := hmem l
  rw [← he'] at h1
  have h2 : (v k - v l) * t ∈ m k := by
    have := (m k).sub_mem h1 (hmem k)
    convert this using 1
    ring
  have h3 : t ∈ m k := ((m k).unit_mul_mem_iff_mem (hv k l hkl)).1 h2
  have h4 : β ∈ m k := by
    have := (m k).add_mem (hmem k) ((m k).mul_mem_left (v k) h3)
    rwa [sub_add_cancel] at this
  exact (hm k).ne_top ((m k).eq_top_of_isUnit_mem h4 hβ)

theorem exists_normOne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ a : ℕ → E, Function.Injective a ∧ ∀ k, a k * σ (a k) = 1 := by
  first
  | exact @_root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one
  | exact _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one
  | (apply _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one ..)

theorem exists_smul_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (β : R) (x y : (Fin 1 → Fin M → R ⊗[F] E)), IsUnit β → qR R σ J (x 0) = β → qR R σ J (y 0) = β → ∃ g : HA R σ J, g • x = y := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ hR' M J hJ β x y hβ hx hy
  have := hR'.1
  have : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R (R ⊗[F] E)
  obtain ⟨a, ha, hn⟩ := exists_normOne hcm
  obtain ⟨k, hk⟩ := exists_isUnit_sub (fun k => inclR R (a k))
    (fun k l hkl => by
      rw [← map_sub]
      exact (IsUnit.mk0 _ (sub_ne_zero.2 (ha.ne hkl))).map _)
    (algebraMap R (R ⊗[F] E) β) (hR R σ J (y 0) (x 0)) (hβ.map _)
  obtain ⟨γ, h1, h2⟩ := exists_unitary (sigR R σ) (GlobalTheory.SelfDualLatticeCompare.sigR_sigR R hcm) (JR R J)
    (fun i j => by
      show (1 : R) ⊗ₜ[F] σ (J j i) = (1 : R) ⊗ₜ[F] J i j
      rw [hJ.1])
    (x 0) (y 0) (algebraMap R (R ⊗[F] E) β) (inclR R (a k))
    (by rw [← hx]; exact GlobalTheory.SelfDualLatticeCompare.hR_self R hcm hJ _)
    (by rw [← hy]; exact GlobalTheory.SelfDualLatticeCompare.hR_self R hcm hJ _)
    (by
      show inclR R (a k) * inclR R (σ (a k)) = 1
      rw [← map_mul, hn, map_one])
    hk
  refine ⟨(⟨γ, h1⟩ : HR R σ J), ?_⟩
  funext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  exact h2

end GlobalTheory.GaugeWittLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmExtensionLocalFieldProductRingExistsSmulEqStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmExtension_localFieldProductRing_exists_smul_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (β : R) (x y : (Fin 1 → Fin M → R ⊗[F] E)), IsUnit β → qR R σ J (x 0) = β → qR R σ J (y 0) = β → ∃ g : HA R σ J, g • x = y := by
  first | exact @GlobalTheory.GaugeWittLoc.exists_smul_eq | exact GlobalTheory.GaugeWittLoc.exists_smul_eq | (intros; apply GlobalTheory.GaugeWittLoc.exists_smul_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsModulusTopOfIsTotallyComplex
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals GlobalTheory.RayFieldCompare GlobalTheory.Mem.LocTriv GlobalTheory.RayFromArtin
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt IsUnifAt exists_unif ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists
open scoped nonZeroDivisors

namespace GlobalTheory.UnramModulus

theorem inInertia_restrict {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (L : Type) [Field L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K L]
    {v : HeightOneSpectrum (𝓞 K)} {A : ValuationSubring Ω} (hA : IsPlaceOver A v) {σ : G K Ω}
    (hσ : σ ∈ Ine (F := K) A) : GlobalTheory.NT.InInertia L v (AlgEquiv.restrictNormalHom L σ) := by
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A fun x =>
    (A.valuation_le_one_iff _).1 (valuation_int_le_one A x)
  have hf : ∀ x, x ∈ (IsLocalRing.maximalIdeal A).comap f ↔ A.valuation (algebraMap L Ω (x : L)) < 1 := fun x =>
    A.valuation_lt_one_iff (f x)
  refine ⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, ⟨?_⟩, fun x => ?_⟩
  · ext x
    rw [Ideal.mem_under, hf, ← hA x, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  · rw [hf]
    have := hσ.2 _ (valuation_int_le_one A x)
    rw [← σ.restrictNormal_commutes L, ← map_sub] at this
    exact this

theorem rayIdl_le {K : Type} [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)) {U : Subgroup (Ideles K)}
    (ho : IsOpen (U : Set (Ideles K))) (hi : infConn K ≤ U)
    (hu : ∀ v x, IsUnitAt v x → localIdele K v x ∈ U) : rayIdl 𝔪 ≤ U := by
  rintro b ⟨hb, -, hb'⟩
  let c : Ideles K := Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) (infPart b)
  have e : b = c * finPartI K b := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
  rw [e]
  refine mul_mem (hi ⟨_, hb', rfl⟩) ?_
  refine (U.isClosed_of_isOpen ho).mem_of_tendsto
    (tendsto_part (a := finPartI K b) hb fun _ => rfl) (Filter.Eventually.of_forall fun S => ?_)
  exact Subgroup.prod_mem _ fun v _ => hu v _ (hb v)

theorem isModulus_top (H : GlobalTheory.Published.GlobalArtinReciprocity) (K M : Type) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [IsAbelianGalois K M] (hM : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn M 𝔭)
    (χ : (M ≃ₐ[K] M) →* ℂˣ) : GlobalTheory.NT.IsModulus M χ ⊤ := by
  let Ω := AlgebraicClosure K
  obtain ⟨art, ha⟩ := H K Ω
  let j : M →ₐ[K] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let : Algebra M Ω := j.toRingHom.toAlgebra
  have : IsScalarTower K M Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  let : CommGroup (M ≃ₐ[K] M) := { (inferInstance : Group (M ≃ₐ[K] M)) with mul_comm := mul_comm' }
  let φ : G K Ω →* (M ≃ₐ[K] M) := AlgEquiv.restrictNormalHom M
  have hφ : Continuous φ := by
    refine continuous_of_isOpen_ker' φ ?_
    have : FiniteDimensional K j.fieldRange := j.equivFieldRange.toLinearEquiv.finiteDimensional
    refine Subgroup.isOpen_mono (fun σ hσ => ?_) j.fieldRange.fixingSubgroup_isOpen
    ext x
    apply (algebraMap M Ω).injective
    exact (σ.restrictNormal_commutes M x).trans (hσ ⟨_, x, rfl⟩)
  let θ : Ideles K →* (M ≃ₐ[K] M) := (liftAb φ hφ).comp art
  have hθ : Continuous θ := (continuous_liftAb φ hφ).comp ha.quot.continuous
  have ho : IsOpen (θ.ker : Set (Ideles K)) := (isOpen_discrete {1}).preimage hθ
  have hk : (diagUnits K).range ⊔ infConn K ≤ θ.ker := fun x hx => by
    have hk : x ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hk, map_one]
  have hr : rayGrp ⊤ ≤ θ.ker := by
    refine sup_le (le_sup_left.trans hk) (rayIdl_le ⊤ ho (le_sup_right.trans hk) fun v x hx => ?_)
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨τ, hτ, e⟩ := (ha.ine v A hA _).1 ⟨x, hx, rfl⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← e, liftAb_toAb]
    exact hM v _ (inInertia_restrict M hA hτ)
  let ψ : idealsPrimeTo (⊤ : Ideal (𝓞 K)) →* (M ≃ₐ[K] M) := (θ.comp (unifIdl ⊤))⁻¹
  have hψ : ∀ 𝔭 h, GlobalTheory.NT.UnramIn M 𝔭 ∧ GlobalTheory.NT.IsFrob M 𝔭 (ψ (primeElt ⊤ 𝔭 h)) := fun v hv => by
    refine ⟨hM v, ?_⟩
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨σ, hσ, e'⟩ := (ha.frob v A hA _).1 ⟨_, isUnifAt_unif v, rfl⟩
    have : ψ (primeElt ⊤ v hv) = AlgEquiv.restrictNormalHom M σ := by
      rw [MonoidHom.inv_apply, MonoidHom.comp_apply, unifIdl, extend_primeElt, MonoidHom.comp_apply,
        ← e', liftAb_toAb, map_inv, inv_inv]
    rw [this]
    exact isFrob_restrict M hA hσ
  refine ⟨top_ne_bot, fun 𝔭 _ => ?_, fun α β hr' => ?_⟩
  · obtain ⟨σ, hσ⟩ := GlobalTheory.NT.exists_isFrob M 𝔭
    rw [GlobalTheory.NT.heckeVal_of_unramIn M χ (hM 𝔭) hσ]
    exact Units.ne_zero _
  · have ha0 : Ideal.span {α} ≠ ⊥ := by simpa using hr'.1
    have hb0 : Ideal.span {β} ≠ ⊥ := by simpa using hr'.2.1
    obtain ⟨A, hA'⟩ := exists_integral ⊤ _ ha0 hr'.2.2.1
    obtain ⟨B, hB'⟩ := exists_integral ⊤ _ hb0 hr'.2.2.2.1
    rw [heckeIdeal_eq M ⊤ ψ hψ χ _ ha0 A hA', heckeIdeal_eq M ⊤ ψ hψ χ _ hb0 B hB']
    have h1 : B⁻¹ * A ∈ (rayPrincipal ⊤).subgroupOf (idealsPrimeTo (⊤ : Ideal (𝓞 K))) := by
      rw [Subgroup.mem_subgroupOf]
      have haK : (α : K) ≠ 0 := by exact_mod_cast hr'.1
      have hbK : (β : K) ≠ 0 := by exact_mod_cast hr'.2.1
      refine ⟨Units.mk0 ((α : K) / β) (div_ne_zero haK hbK), ⟨α, β, hr', by simp [hbK]⟩, ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv, eq_inv_mul_iff_mul_eq]
      apply Units.ext
      rw [Units.val_mul, hA', hB', coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton,
        FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
      congr 1
      exact mul_div_cancel₀ _ hbK
    have h2 : ψ (B⁻¹ * A) = 1 := by
      rw [MonoidHom.inv_apply, inv_eq_one]
      exact hr ((unifIdl_mem_rayGrp_iff top_ne_bot _).2 h1)
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    rw [h2]

theorem isModulus_top_of_isTotallyComplex : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (K M : Type) [Field K]
    [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M],
    (∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn M 𝔭) → ∀ χ : (M ≃ₐ[K] M) →* ℂˣ, GlobalTheory.NT.IsModulus M χ ⊤ :=
  fun H K M _ _ _ _ _ _ _ hM χ => isModulus_top H K M hM χ

end GlobalTheory.UnramModulus

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsGaloisOfIsRayFieldTop
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Published

namespace GlobalTheory.RayTopGalois

theorem count_comap {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [DecidableEq (Associates (Ideal R))] [∀ p : Associates (Ideal R), Decidable (Irreducible p)]
    [DecidableEq (Associates (Ideal S))] [∀ p : Associates (Ideal S), Decidable (Irreducible p)]
    (e : R ≃+* S) (p : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    (Associates.mk (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal).count (Associates.mk (I.comap e.symm)).factors =
      (Associates.mk p.asIdeal).count (Associates.mk I).factors := by
  have hI' : I.comap e.symm ≠ ⊥ := by
    rw [← Ideal.map_comap_of_equiv]
    exact fun h => hI ((Ideal.map_eq_bot_iff_of_injective e.injective).1 h)
  refine eq_of_forall_le_iff fun k => ?_
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI') (HeightOneSpectrum.associates_irreducible _),
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI) (HeightOneSpectrum.associates_irreducible _),
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Associates.mk_le_mk_iff_dvd,
    Ideal.dvd_iff_le, Ideal.dvd_iff_le]
  have : (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal = p.asIdeal.map (e : R →+* S) := by
    rw [Ideal.map_comap_of_equiv]; rfl
  rw [this, ← Ideal.map_pow, Ideal.map_comap_of_equiv]
  exact Ideal.comap_le_comap_iff_of_surjective e.symm e.symm.surjective _ _

section Transport

variable {K K' N : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field N] [NumberField N]
  [Algebra K N] [Algebra K' N] (s : K ≃+* K') (hs : ∀ x, algebraMap K' N (s x) = algebraMap K N x)

def autEquiv : (N ≃ₐ[K] N) ≃* (N ≃ₐ[K'] N) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by
    obtain ⟨y, rfl⟩ := s.surjective x
    rw [hs]; exact σ.commutes y
  invFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by
    rw [← hs]; exact σ.commutes _
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

abbrev primeEquiv : HeightOneSpectrum (𝓞 K) ≃ HeightOneSpectrum (𝓞 K') :=
  HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s)

include hs in
omit [NumberField K] [NumberField K'] [NumberField N] in
theorem liesOver_iff (𝔭 : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 N)) :
    P.LiesOver (primeEquiv s 𝔭).asIdeal ↔ P.LiesOver 𝔭.asIdeal := by
  have h : ∀ x : 𝓞 K, algebraMap (𝓞 K') (𝓞 N) (RingOfIntegers.mapRingEquiv s x) = algebraMap (𝓞 K) (𝓞 N) x :=
    fun x => RingOfIntegers.ext (hs x)
  have h2 : ∀ x : 𝓞 K, RingOfIntegers.mapRingEquiv s x ∈ (primeEquiv s 𝔭).asIdeal ↔ x ∈ 𝔭.asIdeal := fun x => by
    change (RingOfIntegers.mapRingEquiv s).symm (RingOfIntegers.mapRingEquiv s x) ∈ 𝔭.asIdeal ↔ _
    rw [RingEquiv.symm_apply_apply]
  refine ⟨fun ⟨H⟩ => ⟨Ideal.ext fun x => ?_⟩, fun ⟨H⟩ => ⟨Ideal.ext fun x => ?_⟩⟩
  · rw [← h2, H, Ideal.mem_under, Ideal.mem_under, h]
  · obtain ⟨y, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective x
    rw [h2, H, Ideal.mem_under, Ideal.mem_under, h]

theorem absNorm_primeEquiv (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm (primeEquiv s 𝔭).asIdeal = Ideal.absNorm 𝔭.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine (Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv s) ?_).toEquiv).symm
  exact (Ideal.map_comap_of_equiv _).symm

omit [NumberField N] in
theorem isFrob_iff' (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : N ≃ₐ[K] N) :
    IsFrob N (primeEquiv s 𝔭) (autEquiv s hs σ) ↔ IsFrob N 𝔭 σ := by
  unfold IsFrob
  rw [absNorm_primeEquiv]
  exact exists_congr fun P => and_congr_right' (and_congr (liesOver_iff s hs 𝔭 P) Iff.rfl)

omit [NumberField K] [NumberField K'] [NumberField N] in
theorem inInertia_iff' (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : N ≃ₐ[K] N) :
    InInertia N (primeEquiv s 𝔭) (autEquiv s hs σ) ↔ InInertia N 𝔭 σ :=
  exists_congr fun P => and_congr_right' (and_congr (liesOver_iff s hs 𝔭 P) Iff.rfl)

theorem heckeVal_transport [IsGalois K N] [IsGalois K' N] (χ : (N ≃ₐ[K'] N) →* ℂˣ) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    heckeVal N χ (primeEquiv s 𝔭) = heckeVal N (χ.comp (autEquiv s hs).toMonoidHom) 𝔭 := by
  by_cases h : ∀ τ, InInertia N (primeEquiv s 𝔭) τ → χ τ = 1
  · obtain ⟨σ, hσ⟩ := exists_isFrob N 𝔭
    rw [heckeVal_eq N _ 𝔭 (fun τ hτ => h _ ((inInertia_iff' s hs 𝔭 τ).2 hτ)) hσ,
      heckeVal_eq N χ _ h ((isFrob_iff' s hs 𝔭 σ).2 hσ)]
    rfl
  · rw [heckeVal_eq_zero N χ _ h, heckeVal_eq_zero N _ 𝔭 fun h' => h fun τ hτ => ?_]
    obtain ⟨σ, rfl⟩ := (autEquiv s hs).surjective τ
    exact h' σ ((inInertia_iff' s hs 𝔭 σ).1 hτ)

theorem heckeIdeal_transport [IsGalois K N] [IsGalois K' N] (χ : (N ≃ₐ[K'] N) →* ℂˣ) {a : 𝓞 K} (ha : a ≠ 0) :
    heckeIdeal N χ (Ideal.span {RingOfIntegers.mapRingEquiv s a}) =
      heckeIdeal N (χ.comp (autEquiv s hs).toMonoidHom) (Ideal.span {a}) := by
  have e : Ideal.span {RingOfIntegers.mapRingEquiv s a} =
      (Ideal.span {a}).comap (RingOfIntegers.mapRingEquiv s).symm := by
    rw [← Ideal.map_comap_of_equiv, Ideal.map_span, Set.image_singleton]
    rfl
  unfold heckeIdeal
  rw [← finprod_comp_equiv (primeEquiv s)]
  refine finprod_congr fun 𝔭 => ?_
  rw [heckeVal_transport s hs, e, count_comap _ _ (by simpa using ha)]


include hs in
theorem isModulus_top_transport [IsGalois K N] [IsGalois K' N] (h : ∀ χ : (N ≃ₐ[K] N) →* ℂˣ, IsModulus N χ ⊤)
    (χ : (N ≃ₐ[K'] N) →* ℂˣ) : IsModulus N χ ⊤ := by
  have hc : ∀ J : Ideal (𝓞 K), IsCoprime J ⊤ := fun J => by
    rw [← Ideal.one_eq_top]; exact isCoprime_one_right
  refine ⟨top_ne_bot, fun 𝔭 _ => ?_, fun α β hr => ?_⟩
  · obtain ⟨𝔮, rfl⟩ := (primeEquiv s).surjective 𝔭
    rw [heckeVal_transport s hs]
    exact (h _).2.1 𝔮 fun h => 𝔮.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd h))
  · obtain ⟨a, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective α
    obtain ⟨b, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective β
    have ha : a ≠ 0 := fun h => hr.1 (by rw [h, map_zero])
    have hb : b ≠ 0 := fun h => hr.2.1 (by rw [h, map_zero])
    rw [heckeIdeal_transport s hs χ ha, heckeIdeal_transport s hs χ hb]
    refine (h _).2.2 a b ⟨ha, hb, hc _, hc _, trivial, fun φ => ?_⟩
    have := hr.2.2.2.2.2 (φ.comp s.symm.toRingHom)
    change 0 < φ (s.symm (s a)) * φ (s.symm (s b)) at this
    rwa [s.symm_apply_apply, s.symm_apply_apply] at this

include hs in
omit [NumberField K] [NumberField K'] in
theorem isAbelianGalois_transport [CharZero K] [IsAbelianGalois K N] : IsAbelianGalois K' N := by
  have : IsGalois K' N := IsGalois.of_equiv_equiv (f := s) (g := RingEquiv.refl N) (RingHom.ext hs)
  have : IsMulCommutative (N ≃ₐ[K'] N) := ⟨⟨fun a b => by
    obtain ⟨a, rfl⟩ := (autEquiv s hs).surjective a
    obtain ⟨b, rfl⟩ := (autEquiv s hs).surjective b
    rw [← map_mul, ← map_mul, mul_comm' a b]⟩⟩
  exact {}

end Transport

theorem exists_extension {L N : Type} [Field L] [NumberField L] [Field N] [NumberField N] [i : Algebra L N]
    (h : IsRayField L N ⊤) (s : L ≃+* L) :
    ∃ f : N →+* N, ∀ x, f (algebraMap L N x) = algebraMap L N (s x) := by
  have hab := h.1
  let j : Algebra L N := ((@algebraMap L N _ _ i).comp s.symm.toRingHom).toAlgebra
  have hs : ∀ x, @algebraMap L N _ _ j (s x) = @algebraMap L N _ _ i x := fun x =>
    congrArg (@algebraMap L N _ _ i) (s.symm_apply_apply x)
  have hab' := @isAbelianGalois_transport L L N _ _ _ _ i j s hs _ hab
  have hm := @GlobalTheory.RayMaximal.isModulus_of_isRay L _ _ N _ _ i hab ⊤ ⊤ h.2 dvd_rfl top_ne_bot
  obtain ⟨f⟩ := @rayClassFieldMaximalSt_holds L N N _ _ _ _ i hab _ _ j hab' ⊤ top_ne_bot h.2
    (@isModulus_top_transport L L N _ _ _ _ _ _ i j s hs (@IsAbelianGalois.toIsGalois _ _ _ _ i hab)
      (@IsAbelianGalois.toIsGalois _ _ _ _ j hab') hm)
  refine ⟨@AlgHom.toRingHom L N N _ _ _ j i f, fun x => ?_⟩
  rw [← hs]
  exact @AlgHom.commutes L N N _ _ _ j i f (s x)

theorem isGalois_of_isRayField_top : ∀ (K L N : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field N]
    [NumberField N] [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] [IsGalois K L],
    GlobalTheory.Mem.Fld.IsRayField L N ⊤ → IsGalois K N := by
  intro K L N _ _ _ _ _ _ _ _ _ _ _ h
  have hab := h.1
  refine IsGalois.of_fixedField_eq_bot K N (eq_bot_iff.2 fun x hx => ?_)
  rw [IntermediateField.mem_fixedField_iff] at hx
  obtain ⟨y, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := L) x).2 fun σ =>
    hx (σ.restrictScalars K) trivial
  obtain ⟨z, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) y).2 fun s => by
    obtain ⟨f, hf⟩ := exists_extension h s.toRingEquiv
    let g : N →ₐ[K] N := { f with
      commutes' := fun k => by
        rw [IsScalarTower.algebraMap_apply K L N]
        exact (hf _).trans (congrArg _ (s.commutes k)) }
    exact (algebraMap L N).injective ((hf y).symm.trans
      (hx (AlgEquiv.ofBijective g (Algebra.IsAlgebraic.algHom_bijective g)) trivial))
  rw [← IsScalarTower.algebraMap_apply]
  exact IntermediateField.algebraMap_mem _ z

end GlobalTheory.RayTopGalois

end
end
