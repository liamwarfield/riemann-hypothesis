module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealCentreActsByCharacterOnIsotypicSlices
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiamondTranslatesScalarFormsSumIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistTranslationsActAtLevelPrimeProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCombinationScalarFormValuesStabiliserInvariStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCombinationScalarFormValuesStabilizerInvariant
namespace GlobalTheory.AdForm.StabTrans
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV _root_.Formalism.L2.Ker Formalism.UG _root_.Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.Col2.BwLat GlobalTheory.LvT.Built.ValLat Formalism.HermitianLatticesTheory GlobalTheory.Mem.Col2.ValTie

theorem chi_stab {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} (chOf : (I.stp u a i).Cl → Ch)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (k : Ch → GA B (B.R.N i))
    (hR : I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
      (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k)
    (c : (I.stp u a i).Cl) (s : (I.stp u a i).Stab c) (κ : (K (chOf c)).lev.U)
    (hy : (fun g y x : GA B (B.R.N i) => y = g * y * x) (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
          ((I.stp u a i).gam c.1 s.1)) ((K (chOf c)).y ⟨c, rfl⟩).1 κ.1) :
    ((K (chOf c)).lev.chi κ : ℂ) = B.embLL ((I.stp u a i).chr c.1 s.1 : B.LLˣ) := by
  have h0 := (hR.pt c).of_extTo (I.Q_subset_SQ a) ((LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a))
  have h1 := RatMove.isPtOf_ratAd _ _ B.sp.cm _ _ _ _ s.1.1⁻¹ _ _ h0
  have h2 := lev_part_smul _ _ s.1 ((I.stp u a i).rep c).1.1 (congrArg (fun q => q.1.1) s.2)
  have h3 : ∀ g y x k : GA B (B.R.N i), y = g * y * x → g⁻¹ * (y * k) = y * x * k := fun g y x k h => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_assoc, ← h]
  have h4 : ratAd B.host.F (s.1.1⁻¹) = (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
      ((I.stp u a i).gam c.1 s.1))⁻¹ := by
    rw [ratAd, map_inv, map_inv]
    rfl
  rw [h4, h3 _ _ _ _ hy, ← h2] at h1
  exact hR.chr c κ (1, s.1.2) (map_one (_root_.Formalism.L2.Col.ufGL B.fields.E (B.R.N i))) h1

end GlobalTheory.AdForm.StabTrans

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
open GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.StabTrans
open _root_.Formalism.L2.Theta

theorem finM_mul' {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) :
    finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.finM_mul V g h

theorem rTrans_mul {G : Type} [Monoid G] (a b : G) (F : G → ℂ) : rTrans (a * b) F = rTrans a (rTrans b F) := by
  funext x
  simp only [rTrans, mul_assoc]

theorem rTrans_one {G : Type} [Monoid G] (F : G → ℂ) : rTrans (1 : G) F = F := by
  funext x
  simp only [rTrans, mul_one]

theorem rTrans_list_prod {G α : Type} [Monoid G] (f : α → G) (F : G → ℂ) (h : ∀ i, rTrans (f i) F = F) :
    ∀ L : List α, rTrans (L.map f).prod F = F
  | [] => by simpa using rTrans_one F
  | i :: L => by
    rw [List.map_cons, List.prod_cons, rTrans_mul, rTrans_list_prod f F h L, h i]

end GlobalTheory.AdForm.StabTrans


set_option maxHeartbeats 12000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.AdForm.trans_stab : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∀ (e : (I.stp u a j).Cl) (s : (I.stp u a j).Stab e), (I.stp u a j).tr B.fields.emb B.embLL e.1 s.1 ((fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e) = (fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e := by
  intro B X I hI hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hT j hj c hc φ hφ hinv e s
  let eY : (I.chain l u a).Y j ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) j hj :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun z => ⟨z.1, z.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hR := hA.reads j hj
  have hV := GlobalTheory.Mem.Col2.TC.val_tied I hI hP l Z u a j hj (A.bad j) (Ch j) (A.chOf j) (A.K j hj) eY ⟨A.kb j, hR⟩ (fun _ => rfl)
  have hF := (hV.Fi φ).1 hφ
  obtain ⟨Ψ, hΨ, he⟩ := Submodule.mem_map.1 (hF (A.chOf j e))
  have hAd : Ψ ∈ AdFun (A.K j hj (A.chOf j e)).lev (embT (I.rec7 l Z)) := (Submodule.mem_inf.1 hΨ).1
  have hfun : (fun (c : {c // A.chOf j c = A.chOf j e}) (z : Frames (gramC (gramN (I.rec7 l Z) j hj) (embT (I.rec7 l Z)))) =>
      φ c.1 ⟨z.1, z.2⟩) = fun c => Ψ ((A.K j hj (A.chOf j e)).y c) := he.symm
  have rdΨ : ∀ (w : (I.chain l u a).Y j) (g0 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), g0 ∈ GfC _ →
      ∀ x : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F),
      x.1.1 = finM _ (rankN (I.rec7 l Z) j hj) g0 →
      A.rd θ j hj (A.chOf j e) φ w g0 = Ψ x ⟨w.1, w.2⟩ := by
    intro w g0 hg0 x hx
    have hval := (GlobalTheory.AdForm.rdS_val (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X j) (B.R.N j) (rankN (I.rec7 l Z) j hj)
      (gramN (I.rec7 l Z) j hj) rfl (B.T u) (I.rec7 l Z).R.f (A.bad j) (A.K j hj (A.chOf j e)).lev _
      (A.K j hj (A.chOf j e)).y (A.K j hj (A.chOf j e)).y_bij Ψ hAd ⟨w.1, w.2⟩ g0).2.2 x ⟨w.1, w.2⟩ hx (fun τ => by
        have h1 := GlobalTheory.AdForm.ChartVal.infM_fin' θ _ (rankN (I.rec7 l Z) j hj) g0 hg0 τ
        show w.1 τ = infM θ _ _ g0 τ * w.1 τ
        erw [h1, Matrix.one_mul])
    show rdS θ _ (rankN (I.rec7 l Z) j hj) (A.K j hj (A.chOf j e)).lev (A.K j hj (A.chOf j e)).y
      (fun c z => φ c.1 ⟨z.1, z.2⟩) ⟨w.1, w.2⟩ g0 = _
    rw [hfun]
    exact hval
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = Formalism.L2.Col.embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  refine ((GlobalTheory.Mem.Col2.ValTie.stab_inv_iff (E := B.host.E) (F := B.host.F) (sg := sigD (I.rec7 l Z)) (J := gramN (I.rec7 l Z) j hj) (I.stp u a j) B.fields.emb B.embLL e (A.K j hj (A.chOf j e)).lev hemb
    ((A.K j hj (A.chOf j e)).y ⟨e, rfl⟩).1 ((A.K j hj (A.chOf j e)).stabI ⟨e, rfl⟩) (hR.stab e)
    ((A.K j hj (A.chOf j e)).stabI_range ⟨e, rfl⟩)
    (GlobalTheory.AdForm.StabTrans.chi_stab I hI l Z u a j hj (A.chOf j) (A.K j hj) (A.kb j) hR e)
    _ (fun z => ⟨z.1, z.2⟩) (fun _ => rfl)).2 ?_) s
  intro γ hγ κ hy z z' hz

  clear hF hV he hΨ
  obtain ⟨⟨eι, -⟩, -⟩ := id hT
  haveI : Fintype ι := Fintype.ofEquiv _ eι.symm
  classical
  have hJnd : (Finset.univ : Finset ι).toList.Nodup := Finset.nodup_toList _
  have hJall : ∀ i, i ∈ (Finset.univ : Finset ι).toList := fun i => Finset.mem_toList.2 (Finset.mem_univ i)
  obtain ⟨hlev1, hlev2⟩ := GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hI hP l Z u a Ch A hA k ι p β Q L hT _ hJnd hJall j hj (A.chOf j e)
  obtain ⟨kA, hkAf, hkAe⟩ := GlobalTheory.Core.Mi.PinModel.exists_finM ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj)
    ⟨κ.1, (((A.K j hj (A.chOf j e)).lev.U_eq κ.1).1 κ.2).1⟩
  have hkAU : kA ∈ A.U j (A.chOf j e) := (hA.U j hj _ kA).2 ⟨hkAf, κ, hkAe.symm⟩
  obtain ⟨g, hg, κ', hκ'off, hdec⟩ := hlev2 kA hkAU
  have hPK : ((Finset.univ : Finset ι).toList.map fun i => (β j i).gl (g i)).prod ∈
      (A.chi j (A.chOf j e)).ker.map (A.U j (A.chOf j e)).subtype := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨h, h1⟩ := hlev1 i (g i) (hg i)
    exact ⟨⟨_, h⟩, h1, rfl⟩
  obtain ⟨P0, hP0chi, hP0e⟩ := Subgroup.mem_map.1 hPK
  rw [MonoidHom.mem_ker] at hP0chi
  set P := ((Finset.univ : Finset ι).toList.map fun i => (β j i).gl (g i)).prod with hPdef
  have hP0e' : P0.1 = P := hP0e
  have hκ'U : κ' ∈ A.U j (A.chOf j e) := by
    have : κ' = P0.1⁻¹ * kA := by rw [hdec, hP0e']; group
    rw [this]
    exact mul_mem (inv_mem P0.2) hkAU
  obtain ⟨κ'', hκ''⟩ := ((hA.U j hj _ κ').1 hκ'U).2
  have hchi : ((A.K j hj (A.chOf j e)).lev.chi κ : ℂ) = ((A.K j hj (A.chOf j e)).lev.chi κ'' : ℂ) := by
    rw [← hA.chi j hj _ ⟨kA, hkAU⟩ κ hkAe.symm, ← hA.chi j hj _ ⟨κ', hκ'U⟩ κ'' hκ'']
    have e1 : (⟨kA, hkAU⟩ : A.U j (A.chOf j e)) = P0 * ⟨κ', hκ'U⟩ := Subtype.ext (by
      show kA = P0.1 * κ'
      rw [hP0e', hdec])
    rw [e1, map_mul, hP0chi, one_mul]

  obtain ⟨-, -, hAtF, -, hcm, -, -, hOff, -⟩ := GlobalTheory.FinPl.SetCut.grp_split (I.rec7 l Z) ((I.rec7 l Z).sp.X j) (Finset.univ.image fun i => (p i).v)
  have hPQ : (fun x => ∃ i, x = (p i).v) = (· ∈ (Finset.univ.image fun i => (p i).v)) := by
    funext x
    apply propext
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩
  have hκ'at : κ' ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∉ (Finset.univ.image fun i => (p i).v)) := by
    have h1 : κ' ∈ GfC _ ⊓ grpOff ((I.rec7 l Z).sp.X j) (fun x => ∃ i, x = (p i).v) :=
      ⟨((hA.U j hj _ κ').1 hκ'U).1, hκ'off⟩
    rw [hOff] at h1
    have hPQn : (fun x => ¬ ∃ i, x = (p i).v) = (· ∉ (Finset.univ.image fun i => (p i).v)) :=
      funext fun x => congrArg Not (congrFun hPQ x)
    rw [hPQn] at h1
    exact h1
  have hcomm : ∀ g' ∈ c.support, g' * κ' = κ' * g' := fun g' hg' => hcm g' (hPQ ▸ hc g' hg') κ' hκ'at
  have hsuppF : ∀ g' ∈ c.support, g' ∈ GfC ((I.rec7 l Z).sp.X j) := fun g' hg' => hAtF (hPQ ▸ hc g' hg')
  have hPf : P ∈ GfC ((I.rec7 l Z).sp.X j) := hP0e' ▸ ((hA.U j hj _ P0.1).1 P0.2).1
  have hhe := hA.h j hj (A.chOf j e) ⟨e, rfl⟩
  have term : ∀ g' ∈ c.support, A.rd θ j hj (A.chOf j e) φ ⟨z.1, z.2⟩ (A.h j (A.chOf j e) ⟨e, rfl⟩ * g') =
      ((A.K j hj (A.chOf j e)).lev.chi κ'' : ℂ) * A.rd θ j hj (A.chOf j e) φ ⟨z'.1, z'.2⟩ (A.h j (A.chOf j e) ⟨e, rfl⟩ * P * g') := by
    intro g' hg'
    obtain ⟨x1, hx1⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl
      (A.h j (A.chOf j e) ⟨e, rfl⟩ * g')
    obtain ⟨x2, hx2⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl
      (A.h j (A.chOf j e) ⟨e, rfl⟩ * P * g')
    have a1 := rdΨ ⟨z.1, z.2⟩ _ (mul_mem hhe.1 (hsuppF g' hg')) x1 hx1
    have a2 := rdΨ ⟨z'.1, z'.2⟩ _ (mul_mem (mul_mem hhe.1 hPf) (hsuppF g' hg')) x2 hx2
    rw [a1, a2]
    refine hAd γ hγ x2 x1 κ'' ?_ z z' hz
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hx1, hx2, hκ'']
    have hyv := congrArg Units.val hy
    erw [Units.val_mul, Units.val_mul] at hyv
    have hk : kA * g' = P * g' * κ' := by rw [hdec, mul_assoc, ← hcomm g' hg', ← mul_assoc]
    have e2 := congrArg (finM ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj)) hk
    simp only [StabTrans.finM_mul'] at e2 ⊢
    conv_lhs => rw [hhe.2, hyv, ← hhe.2]
    erw [← hkAe]
    simp only [Matrix.mul_assoc] at e2 ⊢
    rw [← e2]
    try rfl
  have hinvP := congrFun (StabTrans.rTrans_list_prod (fun i => (β j i).gl (g i)) (trc c (A.rd θ j hj (A.chOf j e) φ ⟨z'.1, z'.2⟩))
    (fun i => hinv _ _ i (g i) (hg i)) (Finset.univ : Finset ι).toList) (A.h j (A.chOf j e) ⟨e, rfl⟩)
  rw [← hPdef] at hinvP
  show trc c (A.rd θ j hj (A.chOf j e) φ ⟨z.1, z.2⟩) (A.h j (A.chOf j e) ⟨e, rfl⟩) =
    ((A.K j hj (A.chOf j e)).lev.chi κ : ℂ) * trc c (A.rd θ j hj (A.chOf j e) φ ⟨z'.1, z'.2⟩) (A.h j (A.chOf j e) ⟨e, rfl⟩)
  rw [← hinvP, hchi]
  simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g' hg' => ?_
  rw [term g' hg']
  ring
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
open GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCombination_scalarForm_values_stabiliser_invariant : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∀ (e : (I.stp u a j).Cl) (s : (I.stp u a j).Stab e), (I.stp u a j).tr B.fields.emb B.embLL e.1 s.1 ((fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e) = (fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e := by
  first | exact @GlobalTheory.AdForm.trans_stab | exact GlobalTheory.AdForm.trans_stab | (intros; apply GlobalTheory.AdForm.trans_stab <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCombinationScalarFormValuesMemWeylModule
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCombinationScalarFormValuesMemWeylModule
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
open GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.TransAct


set_option maxHeartbeats 1000000 in
theorem trc_val_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∀ e : (I.stp u a j).Cl, (fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e ∈ ValC (Gr B.fields.emb B.embLL (B.R.N j)) (Col2.lamT (B.hcW u) j) := by
  intro B X I hI hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hS j hj c hc φ hφ hinv e
  have hR := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hI hP l Z u a Ch A hA j hj (A.chOf j e)).1
  have key : ∀ g, (fun z : (I.chain l u a).Y j =>
      A.rd θ j hj (A.chOf j e) φ z (A.h j (A.chOf j e) ⟨e, rfl⟩ * g)) ∈
      ValC (Gr B.fields.emb B.embLL (B.R.N j)) (Col2.lamT (B.hcW u) j) := by
    intro g
    obtain ⟨γ, hγ, e', g', hg', κ, hκ, hdec⟩ := hR.dec (A.h j (A.chOf j e) ⟨e, rfl⟩ * g)
    let U : (I.rec7 l Z).what₂.Tau → GL (Fin (B.R.N j)) ℂ := fun τ =>
      ((Matrix.isUnit_iff_isUnit_det _).2 (RdVal.infM_unit θ _ (rankN (I.rec7 l Z) j hj) g' τ)).unit
    have hfun : (fun z : (I.chain l u a).Y j =>
        A.rd θ j hj (A.chOf j e) φ z (A.h j (A.chOf j e) ⟨e, rfl⟩ * g)) =
        (A.chi j (A.chOf j e) ⟨κ, hκ⟩ : ℂ) • GlobalTheory.Mem.ColAd.lT (Gr B.fields.emb B.embLL (B.R.N j)) U (φ e'.1) := by
      funext z
      rw [hdec]
      exact (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hI hP l Z u a Ch A hA θ hθ j hj φ hφ).2 (A.chOf j e) z γ hγ e' g' hg' ⟨κ, hκ⟩
        (GlobalTheory.Mem.ColAd.frL (Gr B.fields.emb B.embLL (B.R.N j)) U z) (fun τ => rfl)
    rw [hfun]
    exact Submodule.smul_mem _ _ (GlobalTheory.Mem.ColAd.lT_mem _ _ U (hφ e'.1).1)
  have hsum : (fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) =>
      trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e =
      ∑ g ∈ c.support, c g • (fun z : (I.chain l u a).Y j =>
        A.rd θ j hj (A.chOf j e) φ z (A.h j (A.chOf j e) ⟨e, rfl⟩ * g)) := by
    funext z
    simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply]
  rw [hsum]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (key g)

end GlobalTheory.AdForm.TransAct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCombinationScalarFormValuesMemWeylModuleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
open GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCombination_scalarForm_values_mem_weylModule : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∀ e : (I.stp u a j).Cl, (fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e ∈ ValC (Gr B.fields.emb B.embLL (B.R.N j)) (Col2.lamT (B.hcW u) j) := by
  first | exact @GlobalTheory.AdForm.TransAct.trc_val_mem | exact GlobalTheory.AdForm.TransAct.trc_val_mem | (intros; apply GlobalTheory.AdForm.TransAct.trc_val_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCombinationScalarFormKeepsAdelicLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCombinationScalarFormKeepsAdelicLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
open GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.TransLaw

theorem trc_apply' {D : D7} {V : HSp D} (c : GA D V →₀ ℂ) (f : GA D V → ℂ) (x : GA D V) :
    trc c f x = ∑ g ∈ c.support, c g * f (x * g) := by
  simp [trc, rTrans, Finset.sum_apply]

theorem list_prod_right {G : Type} [Group G] (F : G → ℂ) (L : List G) (hL : ∀ a ∈ L, ∀ z, F (z * a) = F z) (z : G) :
    F (z * L.prod) = F z := by
  induction L generalizing z with
  | nil => simp
  | cons a L ih =>
    rw [List.prod_cons, ← mul_assoc, ih (fun b hb => hL b (List.mem_cons_of_mem _ hb)) (z * a), hL a List.mem_cons_self]

theorem list_prod_chi {G : Type} [Group G] (U : Subgroup G) (χ : U →* ℂˣ) (L : List G)
    (hL : ∀ a ∈ L, ∃ h : a ∈ U, χ ⟨a, h⟩ = 1) : ∃ h : L.prod ∈ U, χ ⟨_, h⟩ = 1 := by
  induction L with
  | nil => exact ⟨U.one_mem, χ.map_one⟩
  | cons a L ih =>
    obtain ⟨ha, hχa⟩ := hL a List.mem_cons_self
    obtain ⟨hP, hχP⟩ := ih (fun b hb => hL b (List.mem_cons_of_mem _ hb))
    refine ⟨by rw [List.prod_cons]; exact U.mul_mem ha hP, ?_⟩
    have e : (⟨(a :: L).prod, by rw [List.prod_cons]; exact U.mul_mem ha hP⟩ : U) = ⟨a, ha⟩ * ⟨L.prod, hP⟩ := by
      apply Subtype.ext; simp [List.prod_cons]
    rw [e, map_mul, hχa, hχP, one_mul]

set_option maxHeartbeats 1000000 in
theorem rd_laws {B : Base} {X : PreX B.toPre} (I : TC B X) (hok : I.Ok) (hpins : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch) (hA : A.Is) (θ : InfFam (I.rec7 l Z)) (hθ : IsInfFam θ)
    (j : ℕ) (hj : j ≤ B.R.m) (φ : ColT I l u a j) (hφ : φ ∈ (I.fm l u a).Fi j) (b : Ch j) (y : (I.chain l u a).Y j) :
    (∀ γ ∈ GQ ((I.rec7 l Z).sp.X j), ∀ g, A.rd θ j hj b φ y (γ * g) = A.rd θ j hj b φ y g) ∧
    (∀ κ : A.U j b, ∀ g, A.rd θ j hj b φ y (g * κ.1) = (A.chi j b κ : ℂ) * A.rd θ j hj b φ y g) ∧
    (∀ k ∈ GinfC ((I.rec7 l Z).sp.X j), ∀ y' : (I.chain l u a).Y j,
      IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) k) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ →
      ∀ g, A.rd θ j hj b φ y (g * k) = A.rd θ j hj b φ y' g) := by
  let eY : (I.chain l u a).Y j ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) j hj :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun z => ⟨z.1, z.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hV := GlobalTheory.Mem.Col2.TC.val_tied I hok hpins l Z u a j hj (A.bad j) (Ch j) (A.chOf j) (A.K j hj) eY
    ⟨A.kb j, hA.reads j hj⟩ (fun _ => rfl)
  have hF := (hV.Fi φ).1 hφ
  obtain ⟨hL, hK, hR, -⟩ := GlobalTheory.AdForm.RdLaw.rdS_laws (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X j) (B.R.N j) (rankN (I.rec7 l Z) j hj)
      (gramN (I.rec7 l Z) j hj) rfl (B.T u) (I.rec7 l Z).R.f (A.bad j) (A.K j hj b).lev {c // A.chOf j c = b}
      (A.K j hj b).y (A.K j hj b).y_bij _ (fun c z => φ c.1 ⟨z.1, z.2⟩) (hF b) ⟨y.1, y.2⟩
  refine ⟨fun γ hγ g => hL γ hγ g, fun κ g => ?_, fun k hk y' hy g => hR k hk ⟨y'.1, y'.2⟩ hy g⟩
  obtain ⟨hκf, κ', hκ'⟩ := (hA.U j hj b κ.1).1 κ.2
  rw [hA.chi j hj b κ κ' hκ']
  exact hK κ.1 hκf κ' hκ' g

end GlobalTheory.AdForm.TransLaw


open GlobalTheory.AdForm.TransLaw in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.AdForm.trc_rd_laws : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∀ b y, ∀ γ ∈ GQ ((I.rec7 l Z).sp.X j), ∀ (e : {e // A.chOf j e = b}), ∀ g ∈ GinfC ((I.rec7 l Z).sp.X j), ∀ (κ : A.U j b) (y' : (I.chain l u a).Y j),
        IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) g) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ →
        trc c (A.rd θ j hj b φ y) (γ * (A.h j b e * g) * κ.1) = (A.chi j b κ : ℂ) * trc c (A.rd θ j hj b φ y') (A.h j b e) := by
  intro B X I hok hpins l Z u a Ch A hA θ hθ K _ _ _ _ ι p β Q L hT j hj c hc φ hφ hinv b y γ hγ e g0 hg0 κ y' hy
  obtain ⟨hLy, hKy, hRy⟩ := rd_laws I hok hpins l Z u a Ch A hA θ hθ j hj φ hφ b y
  have hT' := hT
  obtain ⟨⟨eι, -⟩, -⟩ := hT'
  haveI : Fintype ι := Fintype.ofEquiv _ eι.symm
  obtain ⟨hstab, hdec⟩ := GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hok hpins l Z u a Ch A hA K ι p β Q L hT Finset.univ.toList
    (Finset.nodup_toList _) (fun i => Finset.mem_toList.2 (Finset.mem_univ _)) j hj b
  obtain ⟨gs, hgs, κ', hκ'off, hκeq⟩ := hdec κ.1 κ.2
  set s := (Finset.univ.toList.map fun i => (β j i).gl (gs i)).prod with hs
  obtain ⟨hsU, hχs⟩ := list_prod_chi (A.U j b) (A.chi j b) (Finset.univ.toList.map fun i => (β j i).gl (gs i)) (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact hstab i (gs i) (hgs i))
  have hκ'U : κ' ∈ A.U j b := by
    have : κ' = s⁻¹ * κ.1 := by rw [hκeq, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]; exact (A.U j b).mul_mem ((A.U j b).inv_mem hsU) κ.2
  have hχκ : A.chi j b κ = A.chi j b ⟨κ', hκ'U⟩ := by
    have e1 : κ = (⟨s, hsU⟩ : A.U j b) * ⟨κ', hκ'U⟩ := Subtype.ext hκeq
    rw [e1, map_mul, hχs, one_mul]
  set F := trc c (A.rd θ j hj b φ y) with hF

  have hcomm : ∀ g' ∈ c.support, κ' * g' = g' * κ' := fun g' hg' =>
    ((GlobalTheory.FinPlLoc.part_grp (fun x => ∃ i, x = (p i).v) ((I.rec7 l Z).sp.X j)).2.1 g' (hc g' hg') κ' hκ'off).symm

  have step1 : ∀ x, F (x * κ.1) = (A.chi j b κ : ℂ) * F (x * s) := by
    intro x
    rw [hF, trc_apply', trc_apply', Finset.mul_sum]
    refine Finset.sum_congr rfl fun g' hg' => ?_
    rw [hκeq, ← mul_assoc, mul_assoc (x * s), hcomm g' hg', ← mul_assoc, hKy ⟨κ', hκ'U⟩, hχκ]
    ring

  have step2 : ∀ x, F (x * s) = F x := by
    intro x
    refine list_prod_right F _ ?_ x
    intro a' ha' z
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha'
    exact congrFun (hinv b y i (gs i) (hgs i)) z

  have step3 : F (γ * (A.h j b e * g0)) = trc c (A.rd θ j hj b φ y') (A.h j b e) := by
    rw [hF, trc_apply', trc_apply']
    refine Finset.sum_congr rfl fun g' hg' => ?_
    have hfin : g' ∈ GfC ((I.rec7 l Z).sp.X j) := GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (hc g' hg')
    rw [mul_assoc γ, hLy γ hγ, mul_assoc, ← GlobalTheory.FinTranslate.comm_fin_real _ hfin hg0, ← mul_assoc,
      hRy g0 hg0 y' hy]
  rw [step1, step2, step3]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCombinationScalarFormKeepsAdelicLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
open GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCombination_scalarForm_keeps_adelicLaws : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∀ b y, ∀ γ ∈ GQ ((I.rec7 l Z).sp.X j), ∀ (e : {e // A.chOf j e = b}), ∀ g ∈ GinfC ((I.rec7 l Z).sp.X j), ∀ (κ : A.U j b) (y' : (I.chain l u a).Y j),
        IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) g) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ →
        trc c (A.rd θ j hj b φ y) (γ * (A.h j b e * g) * κ.1) = (A.chi j b κ : ℂ) * trc c (A.rd θ j hj b φ y') (A.h j b e) := by
  first | exact @GlobalTheory.AdForm.trc_rd_laws | exact GlobalTheory.AdForm.trc_rd_laws | (intros; apply GlobalTheory.AdForm.trc_rd_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistTranslationsActAtLevelPrimeProof
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
namespace GlobalTheory.AdForm.TransAct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_Fi : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      (fun e z => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩) : ColT I l u a j) ∈ (I.fm l u a).Fi j := by
  intro B X I hI hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hS j hj c hc φ hφ hinv e
  exact ⟨GlobalTheory.T.heckeCombination_scalarForm_values_mem_weylModule I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj c hc φ hφ hinv e,
    fun s => GlobalTheory.T.heckeCombination_scalarForm_values_stabiliser_invariant I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj c hc φ hφ hinv e s⟩

theorem twTransAct : TwTrans' := by
  intro B X I hI hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hS j hj c hc φ hφ hinv
  refine ⟨_, mem_Fi I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj c hc φ hφ hinv, fun b y => funext fun g => ?_⟩
  obtain ⟨γ, hγ, e, g', hg', κ, hκ, rfl⟩ := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hI hP l Z u a Ch A hA j hj b).1.dec g
  obtain ⟨e, rfl⟩ := e
  let M : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ := infM θ _ (rankN (I.rec7 l Z) j hj) g'
  have hu : ∀ τ, IsUnit (M τ * y.1 τ).det := fun τ => by
    rw [Matrix.det_mul]; exact (RdVal.infM_unit θ _ (rankN (I.rec7 l Z) j hj) g' τ).mul (y.2 τ)
  let y' : (I.chain l u a).Y j := ⟨fun τ => M τ * y.1 τ, hu⟩
  have htr : IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) g') ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ := fun τ => rfl
  have h1 := (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hI hP l Z u a Ch A hA θ hθ j hj _
    (mem_Fi I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj c hc φ hφ hinv)).2 (A.chOf j e) y γ hγ ⟨e, rfl⟩ g' hg' ⟨κ, hκ⟩ y' htr
  rw [h1, GlobalTheory.T.heckeCombination_scalarForm_keeps_adelicLaws I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj c hc φ hφ hinv _ y γ hγ ⟨e, rfl⟩ g' hg' ⟨κ, hκ⟩ y' htr]

end GlobalTheory.AdForm.TransAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistTranslationsActAtLevelPrimeProofStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistTranslationsActAtLevelPrime_proof : GlobalTheory.AdForm.TwTrans' := by
  first | exact @GlobalTheory.AdForm.TransAct.twTransAct | exact GlobalTheory.AdForm.TransAct.twTransAct | (intros; apply GlobalTheory.AdForm.TransAct.twTransAct <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistRamifiedIffScalarFormsRamified
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleColumnScalarAdelicFormContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleColumnScalarAdelicFormContinuous
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.RamCont

variable {D : D7}

theorem infM_mul' (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn (g * h) τ = infM θ V hn g τ * infM θ V hn h τ := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.infM_mul θ V g h τ

theorem infM_fin' (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : k ∈ GfC V) (τ : D.what₂.Tau) :
    infM θ V hn k τ = 1 := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.infM_fin θ V k hk τ

theorem continuous_infM' (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {n : ℕ} (hn : V.rank = n) (τ : D.what₂.Tau) :
    Continuous fun g : GA D V => infM θ V hn g τ := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.continuous_infM θ hθ V τ

theorem pf_mul (V : HSp D) (g h : GA D V) :
    GlobalTheory.AdForm.RdLaw.pf V (g * h) = GlobalTheory.AdForm.RdLaw.pf V g * GlobalTheory.AdForm.RdLaw.pf V h := by
  apply Subtype.ext
  show GlobalTheory.AdForm.RdLaw.PGL D V.rank (matHom V (g * h)) =
    GlobalTheory.AdForm.RdLaw.PGL D V.rank (matHom V g) * GlobalTheory.AdForm.RdLaw.PGL D V.rank (matHom V h)
  rw [map_mul, map_mul]

theorem pf_inv (V : HSp D) (g : GA D V) : GlobalTheory.AdForm.RdLaw.pf V g⁻¹ = (GlobalTheory.AdForm.RdLaw.pf V g)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pf_mul, inv_mul_cancel, GlobalTheory.AdForm.RdLaw.pf_one]

theorem pf_inv_mul_mem (V : HSp D) (g : GA D V) : (GlobalTheory.AdForm.RdLaw.pf V g)⁻¹ * g ∈ GinfC V := by
  rw [GlobalTheory.CentreTarget.mem_GinfC, ← pf_inv, GlobalTheory.CentreTarget.mt_mul, Matrix.map_mul, GlobalTheory.AdForm.RdLaw.mt_pf,
    GlobalTheory.AdForm.RdLaw.PM_map, GlobalTheory.AdForm.RdLaw.finPart_eps, RingHom.map_sub, RingHom.map_one,
    GlobalTheory.AdForm.RdLaw.finPart_eps, sub_self, zero_smul, add_zero, one_smul, ← Matrix.map_mul,
    ← GlobalTheory.CentreTarget.mt_mul, inv_mul_cancel]
  show (matHom V 1).1.map _ = 1
  rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem infM_mul_pf (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k d : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn (k * ((GlobalTheory.AdForm.RdLaw.pf V d)⁻¹ * d)) τ = infM θ V hn k τ * infM θ V hn d τ := by
  rw [infM_mul' θ V hn k, infM_mul' θ V hn _ d, infM_fin' θ V hn _ (inv_mem (GlobalTheory.AdForm.RdLaw.pf_fin V d)), one_mul]

end GlobalTheory.AdForm.RamCont

namespace GlobalTheory.AdForm.RamCont

theorem rd_continuous : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ b y, Continuous (A.rd θ j hj b φ y) := by
  classical
  intro B X I hI hPins l Z u a Ch A hA θ hθ j hj φ hφ b y
  obtain ⟨hreps, -, -⟩ := GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hI hPins l Z u a Ch A hA j hj b
  have hchi := GlobalTheory.T.continuous_chartLevelCharacters_adelic_tuple I hI hPins l Z u a Ch A hA j hj b
  obtain ⟨hval, hrd⟩ := GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hI hPins l Z u a Ch A hA θ hθ j hj φ hφ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X j).gram
  rw [continuous_iff_continuousAt]
  intro g0
  obtain ⟨γ, hγ, c, k, hk, κ, hκ, e0⟩ := hreps.dec g0
  obtain ⟨P, -, hP⟩ := hval c.1
  let V := (I.rec7 l Z).sp.X j
  let hn := rankN (I.rec7 l Z) j hj
  have hpc : Continuous fun g : GA (I.rec7 l Z) V => GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) :=
    (GlobalTheory.AdForm.RdLaw.continuous_pf V).comp (continuous_const_mul g0⁻¹)
  let p : GA (I.rec7 l Z) V → GfC V := fun g => ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), GlobalTheory.AdForm.RdLaw.pf_fin V _⟩
  have hp : Continuous p := hpc.subtype_mk _
  let O : Set (GA (I.rec7 l Z) V) := {g | GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b}
  have hO : IsOpen O := by
    have h1 := hreps.opn.preimage hp
    have e : O = p ⁻¹' (((A.U j b).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) := by
      ext g
      show GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b ↔ p g ∈ (A.U j b).subgroupOf (GfC V)
      rw [Subgroup.mem_subgroupOf]
    rw [e]; exact h1
  have hg0 : g0 ∈ O := by
    show GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g0) ∈ A.U j b
    rw [inv_mul_cancel, GlobalTheory.AdForm.RdLaw.pf_one]; exact one_mem _
  let G : GA (I.rec7 l Z) V → ℂ := fun g =>
    if h : GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b then ((A.chi j b ⟨_, h⟩ : ℂˣ) : ℂ) else 0
  have hG : ContinuousAt G g0 := by
    have hc : ContinuousOn G O := by
      rw [continuousOn_iff_continuous_restrict]
      have e : (fun x : O => G x.1) = fun x : O => ((A.chi j b ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * x.1), x.2⟩ : ℂˣ) : ℂ) := by
        funext x
        exact dif_pos x.2
      show Continuous fun x : O => G x.1
      rw [e]
      exact hchi.comp ((hpc.comp continuous_subtype_val).subtype_mk _)
    exact hc.continuousAt (hO.mem_nhds hg0)
  let M : GA (I.rec7 l Z) V → (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ :=
    fun g τ => (show Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ from infM θ V hn k τ * infM θ V hn (g0⁻¹ * g) τ) * y.1 τ
  have hMu : ∀ g τ, IsUnit (M g τ).det := fun g τ => by
    simp only [M]
    erw [det_mul, det_mul]
    exact ((GlobalTheory.AdForm.RdVal.infM_unit θ V hn k τ).mul (GlobalTheory.AdForm.RdVal.infM_unit θ V hn _ τ)).mul (y.2 τ)
  have hM : ∀ τ, Continuous fun g =>
      (1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) τ * M g τ := by
    intro τ
    have h1 : Continuous fun g : GA (I.rec7 l Z) V => infM θ V hn (g0⁻¹ * g) τ :=
      (continuous_infM' θ hθ V hn τ).comp (continuous_const_mul g0⁻¹)
    show Continuous fun g : GA (I.rec7 l Z) V => (1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) τ * ((show Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ from infM θ V hn k τ * infM θ V hn (g0⁻¹ * g) τ) * y.1 τ)
    exact continuous_const.matrix_mul ((continuous_const.matrix_mul h1).matrix_mul continuous_const)
  let Φ : GA (I.rec7 l Z) V → ℂ := fun g =>
    (∏ τ, ((1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) τ * M g τ).det ^
      shiftOf (Formalism.L2.Forms.lamT (D := I.rec7 l Z) u j) τ) *
    MvPolynomial.eval (fun q : (I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N j) × Fin ((I.rec7 l Z).R.N j) =>
      ((1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) q.1 * M g q.1) q.2.1 q.2.2) P
  have hΦ : Continuous Φ := by
    refine Continuous.mul (continuous_finsetProd _ fun τ _ => ((hM τ).matrix_det).zpow₀ _ fun g => Or.inl ?_) ?_
    · rw [Pi.one_apply, one_mul]; exact (hMu g τ).ne_zero
    · exact (MvPolynomial.continuous_eval P).comp (continuous_pi fun q => (hM q.1).matrix_elem q.2.1 q.2.2)
  refine ContinuousAt.congr (f := fun g => ((A.chi j b ⟨κ, hκ⟩ : ℂˣ) : ℂ) * G g * Φ g)
    ((continuousAt_const.mul hG).mul hΦ.continuousAt) ?_
  filter_upwards [hO.mem_nhds hg0] with g hg
  have hU : GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b := hg
  have hδi : (GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g) ∈ GinfC V := pf_inv_mul_mem V _
  have hδf : GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ GfC V := GlobalTheory.AdForm.RdLaw.pf_fin V _
  have hκf : κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ GfC V := mul_mem (hreps.le hκ) hδf
  have eg : g = γ * (A.h j b c * (k * ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g)))) *
      (κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g)) := by
    have hc := Formalism.IndefR.Eqv.Act.comm_inf_fin hδi hκf
    calc g = g0 * (GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) * ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g))) := by group
      _ = γ * (A.h j b c * k) * ((κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g)) *
          ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g))) := by rw [e0]; group
      _ = γ * (A.h j b c * k) * (((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g)) *
          (κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))) := by rw [hc]
      _ = _ := by group
  let y' : (I.chain l u a).Y j := ⟨M g, hMu g⟩
  have htr : IsTr (G := fun _ => 1) (infM θ V hn (k * ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g)))) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ := by
    intro τ
    rw [infM_mul_pf θ V hn k (g0⁻¹ * g) τ]
    rfl
  have key := hrd b y γ hγ c _ (mul_mem hk hδi) ⟨κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), mul_mem hκ hU⟩ y' htr
  rw [show A.rd θ j hj b φ y g = _ from (congrArg (A.rd θ j hj b φ y) eg).trans key]
  have e1 : (⟨κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), mul_mem hκ hU⟩ : A.U j b) =
      ⟨κ, hκ⟩ * ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), hU⟩ := rfl
  have e2 : G g = ((A.chi j b ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), hU⟩ : ℂˣ) : ℂ) := dif_pos hU
  have e3 : Φ g = φ c.1 y' := congrFun hP ⟨M g, hMu g⟩
  rw [e1, map_mul, Units.val_mul, e2, e3, mul_assoc]

end GlobalTheory.AdForm.RamCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleColumnScalarAdelicFormContinuousStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupleColumn_scalarAdelicForm_continuous : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ b y, Continuous (A.rd θ j hj b φ y) := by
  first | exact @GlobalTheory.AdForm.RamCont.rd_continuous | exact GlobalTheory.AdForm.RamCont.rd_continuous | (intros; apply GlobalTheory.AdForm.RamCont.rd_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedLevelStabilizerIffAllData
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedLevelStabilizerIffAllData
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem ramIff_all : ∀ D : D7, RamIff D := by
  intro D k _ _ _ _ p n _ _ S β P g hg φ
  letI := Fintype.ofFinite 𝓀[k]ˣ
  have rp : ∀ x (F : GA D S → ℂ), β.rep x F = rTrans (β.gl x) F := fun _ _ => rfl
  rw [finsum_eq_sum_of_fintype]
  constructor
  · rintro ⟨Φ, ⟨he, hr, hc⟩, rfl⟩
    refine ⟨hc P, fun x hx => ?_, ?_⟩
    · rw [← rp, ← he x P, hx]
    · rw [← (mem_Mram Φ).1 hr P]
      exact Finset.sum_congr rfl fun s _ => by rw [← rp, ← he, hg]
  · rintro ⟨hc, hs, h0⟩
    let v : levelVec β.rep P := ⟨φ, fun x hx => hs x hx⟩
    have hv : ∀ x : GL n k, formOf β.rep P v (x • P) = β.rep x φ := formOf_smul β.rep P v
    refine ⟨formOf β.rep P v, ⟨formOf_mem _ _ _, (mem_Mram _).2 fun Q => ?_, fun Q => ?_⟩, by simpa using hv 1⟩
    · obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) P Q
      have : ∀ s : 𝓀[k]ˣ, formOf β.rep P v (s • h • P) = β.rep h (rTrans (β.gl (g s)) φ) := by
        intro s
        rw [← smul_comm h s P, ← hg, smul_smul, hv, map_mul, Module.End.mul_apply, rp (g s)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_congr rfl fun s _ => this s, ← map_sum, h0, map_zero]
    · obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) P Q
      rw [hv, rp]
      exact ⟨fun γ hγ y => by simp only [rTrans]; rw [mul_assoc, hc.1 γ hγ], hc.2.comp (continuous_id.mul continuous_const)⟩

end GlobalTheory.SeeSaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedLevelStabilizerIffAllDataStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedLevel_stabilizer_iff_all_data : ∀ D : D7, GlobalTheory.SeeSaw.RamIff D := by
  first | exact @GlobalTheory.SeeSaw.ramIff_all | exact GlobalTheory.SeeSaw.ramIff_all | (intros; apply GlobalTheory.SeeSaw.ramIff_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistRamifiedIffScalarFormsRamified
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem rd_mul_level {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch) (hA : A.Is)
    (θ : InfFam (I.rec7 l Z)) (hθ : IsInfFam θ) (j : ℕ) (hj : j ≤ B.R.m) (φ : ColT I l u a j) (hφ : φ ∈ (I.fm l u a).Fi j)
    (b : Ch j) (y : (I.chain l u a).Y j) (x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (γ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))
    (hγ : γ ∈ GQ ((I.rec7 l Z).sp.X j)) (κ : A.U j b) :
    A.rd θ j hj b φ y (γ * x * κ.1) = (A.chi j b κ : ℂ) * A.rd θ j hj b φ y x := by
  obtain ⟨γ0, hγ0, c, k0, hk0, κ0, hκ0, rfl⟩ := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hOk hP l Z u a Ch A hA j hj b).1.dec x
  have hrd := (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hOk hP l Z u a Ch A hA θ hθ j hj φ hφ).2 b y
  let y' : (I.chain l u a).Y j := ⟨fun τ => (show Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ from infM θ _ (rankN (I.rec7 l Z) j hj) k0 τ) * y.1 τ, fun τ => by
    rw [Matrix.det_mul]; exact (GlobalTheory.AdForm.RdVal.infM_unit θ _ (rankN (I.rec7 l Z) j hj) k0 τ).mul (y.2 τ)⟩
  have hy' : IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) k0) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ := fun _ => rfl
  rw [hrd γ0 hγ0 c k0 hk0 ⟨κ0, hκ0⟩ y' hy']
  have e : γ * (γ0 * (A.h j b c * k0) * κ0) * κ.1 = (γ * γ0) * (A.h j b c * k0) * ((⟨κ0, hκ0⟩ : A.U j b) * κ).1 := by
    simp only [Subgroup.coe_mul, mul_assoc]
  rw [e, hrd (γ * γ0) (Subgroup.mul_mem _ hγ hγ0) c k0 hk0 (⟨κ0, hκ0⟩ * κ) y' hy', map_mul, Units.val_mul]
  ring

theorem ram_iff_scalar_ram : TwRam' := by
  intro B X I hOk hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hStd j hj φ hφ
  have hlaw := rd_mul_level I hOk hP l Z u a Ch A hA θ hθ j hj φ hφ
  have hcont : ∀ b y, IsContAut _ (A.rd θ j hj b φ y) := fun b y =>
    ⟨fun γ hγ g => by simpa using hlaw b y g γ hγ 1, GlobalTheory.T.tupleColumn_scalarAdelicForm_continuous I hOk hP l Z u a Ch A hA θ hθ j hj φ hφ b y⟩
  refine ⟨hcont, ?_⟩
  obtain ⟨e, he⟩ := hStd.1
  have : Finite ι := Finite.of_equiv _ e.symm
  haveI := Fintype.ofFinite ι
  have hlev := GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hOk hP l Z u a Ch A hA k ι p β Q L hStd (Finset.univ.toList) (Finset.nodup_toList _)
    (fun i => Finset.mem_toList.2 (Finset.mem_univ i)) j hj
  have hfix : ∀ b y i (x : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), x • Q j i = Q j i →
      rTrans ((β j i).gl x) (A.rd θ j hj b φ y) = A.rd θ j hj b φ y := by
    intro b y i x hx
    obtain ⟨hm, h1⟩ := (hlev b).1 i x hx
    funext g
    have := hlaw b y g 1 (Subgroup.one_mem _) ⟨_, hm⟩
    simpa [rTrans, h1] using this
  choose gS hgS using fun (i : ι) (s : 𝓀[k]ˣ) =>
    MulAction.exists_smul_eq (GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (Q j i) (s • Q j i)
  have hram : ∀ b y i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (A.rd θ j hj b φ y) ↔
      ∑ᶠ s, rTrans ((β j i).gl (gS i s)) (A.rd θ j hj b φ y) = 0 := by
    intro b y i
    rw [GlobalTheory.T.ramifiedLevel_stabilizer_iff_all_data (I.rec7 l Z) k (p i) (Fin _) _ (β j i) (Q j i) (gS i) (hgS i)]
    exact ⟨fun h => h.2.2, fun h => ⟨hcont b y, fun x hx => hfix b y i x hx, h⟩⟩
  have hdia := fun i => GlobalTheory.T.diamondTranslates_scalarForms_sum_iff I hOk hP l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj φ hφ i (e i) (he i) (gS i) (hgS i)
  simp only [hram]
  unfold RamT
  constructor
  · rintro ⟨-, hR⟩ b y i
    exact (hdia i).2 (fun c => hR (e i) c) b y
  · intro h
    refine ⟨hφ, fun v c => ?_⟩
    obtain ⟨i, rfl⟩ := e.surjective v
    exact (hdia i).1 (fun b y => h b y i) c

end GlobalTheory.AdForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistRamifiedIffScalarFormsRamifiedStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistRamified_iff_scalarFormsRamified : GlobalTheory.AdForm.TwRam' := by
  first | exact @GlobalTheory.AdForm.ram_iff_scalar_ram | exact GlobalTheory.AdForm.ram_iff_scalar_ram | (intros; apply GlobalTheory.AdForm.ram_iff_scalar_ram <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsActOnRamifiedColumns
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.TwSProof

section Local

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {p : ι → SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem ramAt_fixed {p₀ : SplitPt D k} {β : Frame p₀ S n} {P : Pair k n} {φ₀ : GA D S → ℂ} (h : GlobalTheory.FinPl.RamAt β P φ₀) {g : GL n k}
    (hg : g • P = P) : rTrans (β.gl g) φ₀ = φ₀ := by
  obtain ⟨φ, ⟨heq, -, -⟩, rfl⟩ := h
  have := heq g P
  rw [hg] at this
  exact this.symm

theorem comb_foldr (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k) (χ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ i) 1) (η : ι → 𝓀[k]ˣ) (J : List ι) :
    ∃ c : GA D S →₀ ℂ, (∀ g ∈ c.support, g ∈ grpAt S fun x => ∃ i, x = (p i).v) ∧
      ∀ φ, J.foldr (fun i f => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) f) φ = trc c φ := by
  have hsub : ∀ i, grpAt S (· = (p i).v) ≤ grpAt S fun v => ∃ i, v = (p i).v :=
    fun i => AllBij.congGrp_mono S (AllBij.idAt_mono fun v hv => ⟨i, hv⟩)
  induction J with
  | nil =>
    refine ⟨Finsupp.single 1 1, fun g hg => ?_, fun φ => ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg)]; exact Subgroup.one_mem _
    · exact (AllBij.act_single_one φ).symm
  | cons i l ih =>
    obtain ⟨c, hc, hl⟩ := ih
    obtain ⟨-, -, C, -, hC, -⟩ := ramBijective_holds D k (p i) n q (χ i) (hχ i) _ rfl (η i) S (β i) (Q i)
    refine ⟨AllBij.cmul (Finsupp.mapDomain (β i).gl C) c, fun g hg => ?_, fun φ => ?_⟩
    · exact AllBij.cmul_mem (S := grpAt S fun v => ∃ i, v = (p i).v)
        (fun g h => hsub i (AllBij.mapDomain_mem _ (AllBij.gl_mem (β i)) C g h))
        (fun g h => hc g (Finsupp.mem_support_iff.2 h)) g (Finsupp.mem_support_iff.1 hg)
    · show sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) (l.foldr _ φ) = _
      rw [hl, hC, AllBij.sum_rep_eq]
      exact (AllBij.act_cmul _ _ _).symm

theorem sOp_keeps (hinj : Function.Injective fun i => (p i).v) (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k)
    (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1) (ε : 𝓀[k]ˣ) (i : ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') φ) :
    IsContAut S (sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) ε φ) ∧
      ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') (sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) ε φ) := by
  obtain ⟨hbij, -, c, -, hc, -⟩ := ramBijective_holds D k (p i) n q (χ i) (hχ i) _ rfl ε S (β i) (Q i)
  have hT : ∀ φ, sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) ε φ = AllBij.act (Finsupp.mapDomain (β i).gl c) φ :=
    fun φ => (hc φ).trans (AllBij.sum_rep_eq _ _ _)
  have hC := AllBij.mapDomain_mem _ (AllBij.gl_mem (β i)) c
  refine ⟨by rw [hT]; exact AllBij.isContAut_act _ hφ.1, fun i' => ?_⟩
  rcases eq_or_ne i' i with rfl | hne
  · exact hbij.mapsTo (hφ.2 i')
  · rw [hT]
    exact AllBij.ramAt_act _ _ _ (fun x hx g => AllBij.grpAt_comm S (fun e => hne (hinj e)) (hC x hx)
      (AllBij.gl_mem _ g)) (hφ.2 i')

theorem foldr_keeps (hinj : Function.Injective fun i => (p i).v) (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k)
    (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1) (ε : ι → 𝓀[k]ˣ) (l : List ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') φ) :
    IsContAut S (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (ε i) φ') φ) ∧
      ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (ε i) φ') φ) := by
  induction l with
  | nil => exact hφ
  | cons i l ih => exact sOp_keeps hinj β Q q χ hχ (ε i) i ih

end Local

theorem twS : TwS' := by
  intro B X I hOk hPins l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hStd J q χ hχ
  have hinj : Function.Injective fun i => (p i).v := GlobalTheory.T.splitPoints_lie_over_distinct_places I hOk hPins l Z u p β Q L hStd
  have key : ∀ j (hj : j ≤ B.R.m) φ, RamT (I := I) (l := l) (u := u) (a := a) j φ → ∀ η : ι → 𝓀[k]ˣ,
      ∃ φ', RamT (I := I) (l := l) (u := u) (a := a) j φ' ∧ ∀ b y, A.rd θ j hj b φ' y =
        J.foldr (fun i f => sOp (β j i) (Q j i) q (resChar (χ i) (hχ i) q) (η i) f) (A.rd θ j hj b φ y) := by
    intro j hj φ hφ η
    obtain ⟨c, hc, hfold⟩ := comb_foldr (β j) (Q j) q χ hχ η J
    have hram := GlobalTheory.T.twistRamified_iff_scalarFormsRamified I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj φ hφ.1
    have hR : ∀ b y, IsContAut _ (trc c (A.rd θ j hj b φ y)) ∧
        ∀ i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (trc c (A.rd θ j hj b φ y)) := by
      intro b y
      rw [← hfold]
      exact foldr_keeps hinj (β j) (Q j) q χ hχ η J ⟨hram.1 b y, fun i => hram.2.1 hφ b y i⟩
    obtain ⟨φ', hφ'F, hφ'⟩ := GlobalTheory.T.twistTranslationsActAtLevelPrime_proof I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj c hc φ hφ.1
      (fun b y i g hg => ramAt_fixed ((hR b y).2 i) hg)
    refine ⟨φ', ?_, fun b y => (hφ' b y).trans (hfold _).symm⟩
    have hram' := GlobalTheory.T.twistRamified_iff_scalarFormsRamified I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj φ' hφ'F
    exact hram'.2.2 fun b y i => by rw [hφ' b y]; exact (hR b y).2 i
  classical
  refine ⟨fun j η φ => if h : j ≤ B.R.m ∧ RamT (I := I) (l := l) (u := u) (a := a) j φ then
    (key j h.1 φ h.2 η).choose else φ, ?_⟩
  intro j hj φ hφ
  have hram := GlobalTheory.T.twistRamified_iff_scalarFormsRamified I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj φ hφ.1
  refine ⟨fun b y => ⟨hram.1 b y, fun i => hram.2.1 hφ b y i⟩, fun η => ?_⟩
  have h : j ≤ B.R.m ∧ RamT (I := I) (l := l) (u := u) (a := a) j φ := ⟨hj, hφ⟩
  simp only [dif_pos h]
  exact (key j hj φ hφ η).choose_spec

end GlobalTheory.AdForm.TwSProof

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsActOnRamifiedColumnsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrime_operators_act_on_ramified_columns : GlobalTheory.AdForm.TwS' := by
  first | exact @GlobalTheory.AdForm.TwSProof.twS | exact GlobalTheory.AdForm.TwSProof.twS | (intros; apply GlobalTheory.AdForm.TwSProof.twS <;> assumption)
end
