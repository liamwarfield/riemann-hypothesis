module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechRepresentativeChernClassTangentValue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinCombPullbackTransportIsoWithValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGensOfDataFrom

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.PerfectField
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.EqOneOfIsRep
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

open GlobalTheory.Points GlobalTheory.CechKS.PrismDlog

section General

variable {R : Type} [CommRing R] {Y : Scheme.{0}} (s : Y ⟶ Sp R)

theorem le_of_pts {U V : Y.Opens} (h : ∀ P : Pt s, P.In U → P.In V) : U ≤ V := by
  intro y hy
  obtain ⟨U', hU', hy', hsub⟩ := exists_isAffineOpen_mem_and_subset (U := U) hy
  have hP : (Pt.aff s ⟨U', hU'⟩).In U' := hU'.fromSpec_preimage_self.ge
  have h2 := h _ (hP.mono hsub)
  have : y ∈ Set.range hU'.fromSpec := by rw [hU'.range_fromSpec]; exact hy'
  obtain ⟨z, rfl⟩ := this
  exact h2 (Set.mem_univ z)

theorem valR_hom {P Q : Pt s} (φ : P.Hom Q) {U : Y.Opens} (h : P.In U) (f : Γ(Y, U)) :
    valR Q.x U f = φ.ρ (valR P.x U f) := by
  rw [← φ.pt, valR_spMap_comp _ _ _ h]; rfl

theorem exists_secA {J : Type} (W : J → Y.Opens) (hW : ⨆ k, W k = ⊤) (U : Y.Opens) (a : J → PtFn s)
    (h₁ : ∀ k k' (P : Pt s), P.In U → P.In (W k) → P.In (W k') → a k P = a k' P)
    (h₂ : ∀ k, IsNat (U ⊓ W k) (a k)) :
    ∃ f : Γ(Y, U), ∀ k (P : Pt s), P.In U → P.In (W k) → valR P.x U f = a k P := by
  classical
  let F : PtFn s := fun P ↦ if h : ∃ k, P.In (W k) then a h.choose P else 0
  have hF : ∀ k (P : Pt s), P.In U → P.In (W k) → F P = a k P := fun k P hU hk ↦ by
    have h : ∃ k, P.In (W k) := ⟨k, hk⟩
    simp only [F, dif_pos h]
    exact h₁ _ _ P hU h.choose_spec hk
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover R Y s J (fun k ↦ U ⊓ W k) U (fun k ↦ inf_le_left)
    (by rw [← inf_iSup_eq, hW, inf_top_eq]) F fun k P Q φ hP ↦ by
      rw [hF k P (hP.mono inf_le_left) (hP.mono inf_le_right),
        hF k Q ((hP.map φ).mono inf_le_left) ((hP.map φ).mono inf_le_right)]
      exact h₂ k P Q φ hP
  exact ⟨f, fun k P hU hk ↦ (hf k P (hU.inf hk)).symm.trans (hF k P hU hk)⟩

theorem valR_mul_inv {C : Type} [CommRing C] (x : Sp C ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(Y, U)ˣ) :
    valR x U u.val * valR x U u⁻¹.val = 1 := by
  rw [← valR_mul _ _ h, Units.mul_inv, valR_one _ _ h]

theorem triv_of_local {M : LB Y} (hM : M.IsLB) {J : Type} (W : J → Y.Opens) (hW : ⨆ k, W k = ⊤) (c : J → M.ι)
    (hc : ∀ k, W k ≤ M.U (c k)) (u : ∀ k, Γ(Y, W k)ˣ)
    (hu : ∀ k k' (P : Pt s), P.In (W k) → P.In (W k') →
      valR P.x _ (u k).val = valR P.x _ (M.g (c k) (c k')).val * valR P.x _ (u k').val) : GlobalTheory.AbLaw.Triv M := by
  let a : M.ι → J → PtFn s := fun i k P ↦ valR P.x _ (M.g i (c k)).val * valR P.x _ (u k).val
  let a' : M.ι → J → PtFn s := fun i k P ↦ valR P.x _ (M.g i (c k))⁻¹.val * valR P.x _ (u k)⁻¹.val
  have e₁ : ∀ i k k' (P : Pt s), P.In (M.U i) → P.In (W k) → P.In (W k') → a i k P = a i k' P := by
    intro i k k' P hi hk hk'
    simp only [a]
    rw [hu k k' P hk hk', ← _root_.mul_assoc,
      valR_cocycle M hM P.x i (c k) (c k') ((hi.inf (hk.mono (hc k))).inf (hk'.mono (hc k')))]
  have e₂ : ∀ i k (P : Pt s), P.In (M.U i) → P.In (W k) → a i k P * a' i k P = 1 := by
    intro i k P hi hk
    simp only [a, a']
    rw [_root_.mul_mul_mul_comm, valR_mul_inv _ _ (hi.inf (hk.mono (hc k))), valR_mul_inv _ _ hk, _root_.mul_one]
  have e₃ : ∀ i k k' (P : Pt s), P.In (M.U i) → P.In (W k) → P.In (W k') → a' i k P = a' i k' P := by
    intro i k k' P hi hk hk'
    have h1 := e₂ i k P hi hk
    have h2 := e₂ i k' P hi hk'
    rw [← e₁ i k k' P hi hk hk'] at h2
    linear_combination (a' i k' P) * h1 - (a' i k P) * h2
  have n₁ : ∀ i k, IsNat (M.U i ⊓ W k) (a i k) := fun i k P Q φ hP ↦ by
    simp only [a]
    rw [map_mul, valR_hom s φ (hP.mono inf_le_right), valR_hom s φ (hP.mono (inf_le_inf_left _ (hc k)))]
  have n₂ : ∀ i k, IsNat (M.U i ⊓ W k) (a' i k) := fun i k P Q φ hP ↦ by
    simp only [a']
    rw [map_mul, valR_hom s φ (hP.mono inf_le_right), valR_hom s φ (hP.mono (inf_le_inf_left _ (hc k)))]
  choose f hf using fun i ↦ exists_secA s W hW (M.U i) (a i) (e₁ i) (n₁ i)
  choose f' hf' using fun i ↦ exists_secA s W hW (M.U i) (a' i) (e₃ i) (n₂ i)
  have hff : ∀ i, f i * f' i = 1 := fun i ↦
    eq_of_valR_eq_on_cover s W hW _ _ _ fun P k hi hk ↦ by
      rw [valR_mul _ _ hi, valR_one _ _ hi, hf i k P hi hk, hf' i k P hi hk, e₂ i k P hi hk]
  refine ⟨⟨fun i ↦ Units.mkOfMulEqOne _ _ (hff i)⟩, fun i j ↦ Units.ext ?_⟩
  refine eq_of_valR_eq_on_cover s W hW _ _ _ fun P k hij hk ↦ ?_
  have hi : P.In (M.U i) := hij.mono inf_le_left
  have hj : P.In (M.U j) := hij.mono inf_le_right
  rw [Units.val_mul, valR_mul _ _ hij]
  change valR P.x _ ((Y.presheaf.map (homOfLE inf_le_left).op).hom (f i)) =
    _ * valR P.x _ ((Y.presheaf.map (homOfLE inf_le_right).op).hom (f j))
  rw [valR_res _ _ hij, valR_res _ _ hij, hf i k P hi hk, hf j k P hj hk]
  simp only [a]
  rw [← _root_.mul_assoc, valR_cocycle M hM P.x i j (c k) (hij.inf (hk.mono (hc k)))]

end General

def evEps {B : Type} [CommRing B] (e : B) (he : e * e = 0) : DualNumber B →+* B where
  toFun c := c.fst + c.snd * e
  map_one' := by simp
  map_mul' x y := by
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    linear_combination (-(x.snd * y.snd)) * he
  map_zero' := by simp
  map_add' x y := by simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add]; ring

section Tr

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

@[reducible] def sndPt (P : Pt (epsR K ⊗ A).hom) : GPt A where
  B := P.B
  x := P.x ≫ (snd (epsR K) A).left
  w := by rw [Category.comp_id, Category.assoc, Over.w, P.w]

def fstHomPt (P : Pt (epsR K ⊗ A).hom) : DualNumber K →+* P.B :=
  (Spec.preimage (P.x ≫ (fst (epsR K) A).left : Sp P.B ⟶ Sp (DualNumber K))).hom

theorem spMap_fstHomPt (P : Pt (epsR K ⊗ A).hom) : spMap (fstHomPt P) = P.x ≫ (fst (epsR K) A).left :=
  Spec.map_preimage _

theorem fstHomPt_sq (P : Pt (epsR K ⊗ A).hom) : fstHomPt P DualNumber.eps * fstHomPt P DualNumber.eps = 0 := by
  rw [← map_mul, DualNumber.eps_mul_eps, map_zero]

theorem fstHomPt_comp (P : Pt (epsR K ⊗ A).hom) :
    (fstHomPt P).comp (algebraMap K (DualNumber K)) = algebraMap K P.B := by
  have e : spMap ((fstHomPt P).comp (algebraMap K (DualNumber K))) = spMap (algebraMap K P.B) := by
    rw [GlobalTheory.Cris.spMap_comp, spMap_fstHomPt, ← P.w, Category.assoc]
    exact congrArg (P.x ≫ ·) (Over.w (fst (epsR K) A))
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem pt_transl [IsCommMonObj A] (v : epsR K ⟶ A) (P : Pt (epsR K ⊗ A).hom) :
    P.x ≫ (lift (fst (epsR K) A ≫ v) (snd (epsR K) A) ≫ μ[A]).left =
      spMap (evEps _ (fstHomPt_sq P)) ≫ (sndPt P).trx v := by
  obtain ⟨x', v', hx', hv', hw⟩ := (sndPt P).isTransl_trx v
  have i1 : (evEps _ (fstHomPt_sq P)).comp (algebraMap P.B (DualNumber P.B)) = RingHom.id _ :=
    RingHom.ext fun b ↦ by simp [evEps, TrivSqZeroExt.algebraMap_eq_inl]
  have i2 : (evEps _ (fstHomPt_sq P)).comp (dualMap (algebraMap K P.B)) = fstHomPt P :=
    RingHom.ext fun c ↦ by
      have h1 : ∀ k, algebraMap K P.B k = fstHomPt P (algebraMap K _ k) := fun k ↦
        (RingHom.congr_fun (fstHomPt_comp P) k).symm
      have h2 : c = algebraMap K _ c.fst + algebraMap K _ c.snd * DualNumber.eps := by
        ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
      conv_rhs => rw [h2, map_add (f := _), map_mul, ← h1, ← h1]
      simp [evEps, dualMap, Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl]
  let y : Over.mk (spMap (algebraMap K P.B)) ⟶ epsR K ⊗ A := Over.homMk P.x P.w
  let j : Over.mk (spMap (algebraMap K P.B)) ⟶
      Over.mk (spMap ((algebraMap P.B (DualNumber P.B)).comp (algebraMap K P.B))) :=
    Over.homMk (spMap (evEps _ (fstHomPt_sq P))) (by
      change spMap _ ≫ spMap _ = spMap _
      rw [← GlobalTheory.Cris.spMap_comp, ← RingHom.comp_assoc, i1, RingHom.id_comp])
  have e1 : j ≫ x' = y ≫ snd (epsR K) A := by
    apply Over.OverMorphism.ext
    change spMap _ ≫ x'.left = P.x ≫ _
    rw [hx', ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, i1, GlobalTheory.Cris.spMap_id, Category.id_comp]
  have e2 : j ≫ v' = y ≫ fst (epsR K) A ≫ v := by
    apply Over.OverMorphism.ext
    change spMap _ ≫ v'.left = P.x ≫ (fst (epsR K) A).left ≫ v.left
    rw [hv', ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, i2, spMap_fstHomPt, Category.assoc]
  have e3 : y ≫ ((fst (epsR K) A ≫ v) * snd (epsR K) A) = j ≫ (x' * v') := by
    rw [MonObj.comp_mul, MonObj.comp_mul, e1, e2, _root_.mul_comm]
  rw [← hw]
  exact congrArg Over.Hom.left e3

theorem triv_translDiff [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB) {v : epsR K ⟶ A} (hv : IsTangent v)
    {J : Type} (V : J → A.left.Opens) (hV : ⨆ j, V j = ⊤) (τ : J → L.ι) (hτ : ∀ j, V j ≤ L.U (τ j))
    (n : ∀ j, Γ(A.left, V j))
    (hn : ∀ j j' (P : GPt A), P.In (V j) → P.In (V j') →
      valR P.x _ (n j) - valR P.x _ (n j') = dlog L v (τ j) (τ j') P) :
    GlobalTheory.AbLaw.Triv (Out.translDiff A L v) := by
  let a := (lift (fst (epsR K) A ≫ v) (snd (epsR K) A) ≫ μ[A]).left
  let b := (snd (epsR K) A).left
  let p : (epsR K ⊗ A).left ⟶ Sp (DualNumber K) := (fst (epsR K) A).left
  have hab : ∀ (U : A.left.Opens) (P : Pt (epsR K ⊗ A).hom), P.In (b ⁻¹ᵁ U) → ⊤ ≤ (P.x ≫ a) ⁻¹ᵁ U := by
    intro U P hP
    have h1 : (sndPt P).In U := hP
    have h2 : ⊤ ≤ ((sndPt P).trx v) ⁻¹ᵁ U := h1.tr hv
    simp only [a]
    rw [pt_transl]
    exact fun z _ ↦ h2 (Set.mem_univ _)
  have hle : ∀ U : A.left.Opens, b ⁻¹ᵁ U ≤ a ⁻¹ᵁ U := fun U ↦ le_of_pts (epsR K ⊗ A).hom (hab U)
  have hsq : ∀ U, constFn p U DualNumber.eps * constFn p U DualNumber.eps = 0 := fun U ↦ by
    simp only [constFn, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  refine triv_of_local (epsR K ⊗ A).hom (LB.isLB_linComb hL _ _) (fun j ↦ b ⁻¹ᵁ V j)
    (by rw [← Scheme.Hom.preimage_iSup, hV, Scheme.Hom.preimage_top]) (fun j _ ↦ τ j) ?_
    (fun j ↦ Units.mkOfMulEqOne (1 + constFn p _ DualNumber.eps * (b.app (V j)).hom (n j))
      (1 - constFn p _ DualNumber.eps * (b.app (V j)).hom (n j))
      (by linear_combination (-((b.app (V j)).hom (n j)) ^ 2) * hsq (b ⁻¹ᵁ V j))) ?_
  · intro j y hy
    refine Set.mem_iInter.2 fun k ↦ ?_
    fin_cases k
    · exact hle _ (hτ j hy)
    · exact hτ j hy
  · intro j j' P hj hj'
    have hu : ∀ j, P.In (b ⁻¹ᵁ V j) → valR P.x (b ⁻¹ᵁ V j)
        (1 + constFn p _ DualNumber.eps * (b.app (V j)).hom (n j)) =
        1 + fstHomPt P DualNumber.eps * valR (sndPt P).x _ (n j) := fun j hj ↦ by
      rw [valR_add _ _ hj, valR_mul _ _ hj, valR_one _ _ hj, valR_constFn _ _ _ hj, ← valR_comp]
      rfl
    have q : (sndPt P).In (V j) := hj
    have q' : (sndPt P).In (V j') := hj'
    have qq : (sndPt P).In (L.U (τ j) ⊓ L.U (τ j')) := (q.mono (hτ j)).inf (q'.mono (hτ j'))
    have hw : ∀ j, b ⁻¹ᵁ V j ≤ LB.wchart L ![a, b] fun _ ↦ τ j := by
      intro j y hy
      refine Set.mem_iInter.2 fun k ↦ ?_
      fin_cases k
      · exact hle _ (hτ j hy)
      · exact hτ j hy
    have hPw : P.In (LB.wchart L ![a, b] (fun _ ↦ τ j) ⊓ LB.wchart L ![a, b] fun _ ↦ τ j') :=
      (hj.mono (hw j)).inf (hj'.mono (hw j'))
    have la : LB.wchart L ![a, b] (fun _ ↦ τ j) ⊓ LB.wchart L ![a, b] (fun _ ↦ τ j') ≤
        a ⁻¹ᵁ (L.U (τ j) ⊓ L.U (τ j')) :=
      le_inf (inf_le_left.trans (LB.wchart_le L ![a, b] _ 0)) (inf_le_right.trans (LB.wchart_le L ![a, b] _ 0))
    have lb : LB.wchart L ![a, b] (fun _ ↦ τ j) ⊓ LB.wchart L ![a, b] (fun _ ↦ τ j') ≤
        b ⁻¹ᵁ (L.U (τ j) ⊓ L.U (τ j')) :=
      le_inf (inf_le_left.trans (LB.wchart_le L ![a, b] _ 1)) (inf_le_right.trans (LB.wchart_le L ![a, b] _ 1))
    have eg : (LB.LinComb L ![a, b] ![1, -1]).g (fun _ ↦ τ j) (fun _ ↦ τ j') =
        res la (pullU a _ (L.g (τ j) (τ j'))) * res lb (pullU b _ (L.g (τ j) (τ j'))⁻¹) := by
      simp only [LB.LinComb, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg, map_inv]
      rfl
    have ev : valR P.x _ ((LB.LinComb L ![a, b] ![1, -1]).g (fun _ ↦ τ j) (fun _ ↦ τ j')).val =
        valR (P.x ≫ a) _ (L.g (τ j) (τ j')).val * valR (sndPt P).x _ (L.g (τ j) (τ j'))⁻¹.val := by
      rw [eg, Units.val_mul]
      refine (valR_mul _ _ hPw _ _).trans (congrArg₂ (· * ·) ?_ ?_)
      · exact (valR_res _ la hPw _).trans (valR_comp _ _ _ _).symm
      · exact (valR_res _ lb hPw _).trans (valR_comp _ _ _ _).symm
    have et : valR (P.x ≫ a) _ (L.g (τ j) (τ j')).val = valR (sndPt P).x _ (L.g (τ j) (τ j')).val +
        (valR ((sndPt P).trx v) _ (L.g (τ j) (τ j')).val).snd * fstHomPt P DualNumber.eps := by
      simp only [a]
      rw [pt_transl, valR_spMap_comp _ _ _ (qq.tr hv), ← fst_valR_trx (sndPt P) hv _ qq]
      rfl
    have h1 := valR_mul_inv (sndPt P).x _ qq (L.g (τ j) (τ j'))
    have h2 := hn j j' (sndPt P) q q'
    have h3 := fstHomPt_sq P
    refine (hu j hj).trans (Eq.trans ?_ (congrArg₂ (· * ·) ev (hu j' hj')).symm)
    rw [et]
    simp only [dlog] at h2
    generalize valR (sndPt P).x _ (L.g (τ j) (τ j')).val = g at *
    generalize valR (sndPt P).x _ (L.g (τ j) (τ j'))⁻¹.val = g' at *
    generalize (valR ((sndPt P).trx v) _ (L.g (τ j) (τ j')).val).snd = w at *
    generalize valR (sndPt P).x _ (n j) = m at *
    generalize valR (sndPt P).x _ (n j') = m' at *
    generalize fstHomPt P DualNumber.eps = e at *
    linear_combination (-(1 + e * m')) * h1 + e * h2 - (w * g' * m') * h3

theorem eq_one_of_isRep [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB) (hK : Out.KTriv A L) {v : epsR K ⟶ A}
    (hv : IsTangent v) {J : Type} (V : J → A.left.Opens) (hV : ⨆ j, V j = ⊤) (τ : J → L.ι)
    (hτ : ∀ j, V j ≤ L.U (τ j)) (c : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))))
    (hc : IsRep V c fun j j' ↦ dlog L v (τ j) (τ j')) (hF : H1.mk _ c ∈ F1 (A.hom ≫ 𝟙 (Sp K))) : v = 1 := by
  rw [hodgeFiltration_eq_range] at hF
  obtain ⟨ω, hω⟩ := hF
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 hω.symm
  obtain ⟨G, h1, h2⟩ := hc
  have hg' : ∀ (P Q : GPt A) (φ : P.Hom Q), GlobalTheory.Cris.ev c φ.triv = g Q.triv - φ.ρ (g P.triv) := fun P Q φ ↦ by
    have e := congrFun (congrFun (congrFun hg P.triv) Q.triv) φ.triv
    have z : ω.1.1 P.triv Q.triv φ.triv = 0 := ω.2 φ.triv rfl rfl
    have key : ∀ x y t : Q.B, x = y - t → t = 0 → y = x := fun x y t a b ↦ by rw [a, b, sub_zero]
    exact key _ _ _ e z
  have ex : ∀ j, ∃ n : Γ(A.left, V j), ∀ P : GPt A, P.In (V j) → G j P - g P.triv = valR P.x _ n := fun j ↦ by
    obtain ⟨n, hn⟩ := GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover K _ (A.hom ≫ 𝟙 (Sp K)) Unit (fun _ ↦ V j) (V j) (fun _ ↦ le_rfl)
      (le_iSup (fun _ : Unit ↦ V j) ()) (fun P ↦ G j P - g P.triv) fun _ P Q φ hP ↦ by
        have a := h1 j P Q φ hP
        rw [hg'] at a
        have key : ∀ x y z t : Q.B, x - y = z - t → z - x = t - y := fun x y z t h ↦ by linear_combination -h
        exact (key _ _ _ _ a).trans (map_sub φ.ρ _ _).symm
    exact ⟨n, hn ()⟩
  choose n hn using ex
  have ht := triv_translDiff hL hv V hV τ hτ n fun j j' P hj hj' ↦ by
    rw [← hn j P hj, ← hn j' P hj', sub_sub_sub_cancel_right]
    exact h2 j j' P hj hj'
  have hD : (Out.translDiff A L v).IsLB := LB.isLB_linComb hL _ _
  refine hK (DualNumber K) _ v fun p ↦ ⟨⊤, trivial, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  rw [cls_pull hD, (cls_eq_zero_iff hD).2 ht, map_zero]

end Tr

end CrystallinePoints.Pd
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.FinrankOfRankAtStalk
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

open GlobalTheory.PolForm

set_option maxHeartbeats 1000000 in
theorem chern_eq_sum (hFree : AbelianDeRham.Free) (hHodge : AbelianDeRham.Hodge) {K : Type} [Field K]
    {A : Over (Sp K)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {L : LB A.left} {ψ : LinearMap.BilinForm K (HdR A)} (hψ : IsPolForm (dp0 K) (𝟙 _) A L ψ)
    (hiso : ∀ x ∈ Fil A, ∀ y ∈ Fil A, ψ x y = 0) :
    ∃ (I : Type) (_ : Fintype I) (c : I → primDR A) (ω : I → Form (A.hom ≫ 𝟙 (Sp K)))
      (hω : ∀ k, Form.cl _ (ω k) ∈ primDR A),
      IsChern (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L (∑ k, cup _ (c k).1 (Form.cl _ (ω k))) ∧
        ∀ f ∈ Fil A, ∀ x : HdR A, ψ f x = ∑ k, f (c k) * x ⟨_, hω k⟩ := by
  obtain ⟨-, hfin, -, -, e, he⟩ := hFree K A g hA hg
  obtain ⟨-, ⟨N, hN⟩, -⟩ := hHodge K A g hA hg
  obtain ⟨n, a, b, hch, rfl⟩ := hψ
  let pF := Submodule.projectionOnto (PrimitiveSubmodule A) N hN
  let pN := Submodule.projectionOnto N (PrimitiveSubmodule A) hN.symm
  have hsplit : ∀ c : primDR A, ((pF c : primDR A)) + (pN c : primDR A) = c :=
    Submodule.projection_add_projection_eq_self hN
  have hpN : ∀ c ∈ PrimitiveSubmodule A, pN c = 0 := fun c hc ↦
    (Submodule.projectionOnto_apply_eq_zero_iff hN.symm).2 hc

  have hvan : ∀ x y : Module.Dual K (primDR A),
      ∑ k, (x (pN (a k)) * y (pN (b k)) - x (pN (b k)) * y (pN (a k))) = 0 := by
    intro x y
    have hmem : ∀ z : Module.Dual K (primDR A), z ∘ₗ N.subtype ∘ₗ pN ∈ Fil A := fun z ↦
      (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by simp [hpN c hc]
    have := hiso _ (hmem x) _ (hmem y)
    rw [wedgeForm_apply] at this
    simpa using this
  have h0 : ∑ k, exteriorPower.ιMulti K 2
      ![((pN (a k) : primDR A) : FirstDeRham (A.hom ≫ 𝟙 (Sp K))), ((pN (b k) : primDR A) : FirstDeRham _)] = 0 := by
    haveI : FiniteDimensional K (FirstDeRham (A.hom ≫ 𝟙 (Sp K))) := hfin
    apply wedge_two_eq_zero
    intro f
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [pairingDual_ιMulti_two]
    exact hvan (f 0 ∘ₗ (primDR A).subtype) (f 1 ∘ₗ (primDR A).subtype)

  have hform : ∀ c : PrimitiveSubmodule A, ∃ w : Form (A.hom ≫ 𝟙 (Sp K)),
      Form.cl _ w = ((c : primDR A) : FirstDeRham (A.hom ≫ 𝟙 (Sp K))) := fun c ↦ by
    have hc := c.2
    change ((c : primDR A) : FirstDeRham (A.hom ≫ 𝟙 (Sp K))) ∈ F1 _ at hc
    rw [hodgeFiltration_eq_range] at hc
    exact hc
  choose form hform using hform
  have hanti : ∀ u v : FirstDeRham (A.hom ≫ 𝟙 (Sp K)),
      cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) u v = -cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) v u := fun u v ↦ by
    rw [← he, ← he, ← map_neg, ιMulti_two_swap]
  have key : ∀ a₁ a₂ b₁ b₂ : FirstDeRham (A.hom ≫ 𝟙 (Sp K)),
      cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a₁ + a₂) (b₁ + b₂) =
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a₁ + a₂) b₁ +
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (-b₂) a₁ + cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) a₂ b₂ := by
    intro a₁ a₂ b₁ b₂
    simp only [map_add (f := _), LinearMap.add_apply, map_neg, LinearMap.neg_apply]
    rw [hanti a₁ b₂]
    abel
  have hZ : ∑ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (pN (a k) : primDR A).1 (pN (b k) : primDR A).1 = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_zero e, ← h0, map_sum]
    exact Finset.sum_congr rfl fun k _ ↦ (he _ _).symm
  obtain ⟨ω, hωdef⟩ : ∃ ω : Fin n ⊕ Fin n → Form (A.hom ≫ 𝟙 (Sp K)),
      ω = Sum.elim (fun k ↦ form (pF (b k))) (fun k ↦ form (pF (a k))) := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : Fin n ⊕ Fin n → primDR A,
      c = Sum.elim a (fun k ↦ -(pN (b k) : primDR A)) := ⟨_, rfl⟩
  have hωl : ∀ k, Form.cl (A.hom ≫ 𝟙 (Sp K)) (ω (Sum.inl k)) = (pF (b k) : primDR A).1 := fun k ↦ by
    rw [hωdef, Sum.elim_inl, hform]
  have hωr : ∀ k, Form.cl (A.hom ≫ 𝟙 (Sp K)) (ω (Sum.inr k)) = (pF (a k) : primDR A).1 := fun k ↦ by
    rw [hωdef, Sum.elim_inr, hform]
  have hcl : ∀ k, c (Sum.inl k) = a k := fun k ↦ by rw [hcdef, Sum.elim_inl]
  have hcr : ∀ k, c (Sum.inr k) = -(pN (b k) : primDR A) := fun k ↦ by rw [hcdef, Sum.elim_inr]
  have hω : ∀ k, Form.cl (A.hom ≫ 𝟙 (Sp K)) (ω k) ∈ primDR A := fun k ↦ by
    rcases k with k | k
    · rw [hωl]; exact Subtype.property _
    · rw [hωr]; exact Subtype.property _
  have hsum : ∑ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (c k).1 (Form.cl _ (ω k)) =
      ∑ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a k).1 (b k).1 := by
    have e3 : ∀ k, cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a k).1 (b k).1 =
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (a k).1 (pF (b k) : primDR A).1 +
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (-(pN (b k) : primDR A).1) (pF (a k) : primDR A).1 +
        cup (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (pN (a k) : primDR A).1 (pN (b k) : primDR A).1 :=
      fun k ↦ by
      have ha := congrArg Subtype.val (hsplit (a k))
      have hb := congrArg Subtype.val (hsplit (b k))
      rw [Submodule.coe_add] at ha hb
      rw [← ha, ← hb]
      exact key _ _ _ _
    rw [Fintype.sum_sum_type]
    simp only [hcl, hcr, hωl, hωr, Submodule.coe_neg]
    rw [Finset.sum_congr rfl fun k _ ↦ e3 k, Finset.sum_add_distrib, Finset.sum_add_distrib, hZ,
      add_zero]
  refine ⟨Fin n ⊕ Fin n, inferInstance, c, ω, hω, by rw [hsum]; exact hch, ?_⟩
  intro f hf x
  rw [Fil, Submodule.mem_dualAnnihilator] at hf
  have hfF : ∀ c : PrimitiveSubmodule A, f c = 0 := fun c ↦ hf _ c.2
  have hfa : ∀ k, f (a k) = f (pN (a k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (a k)]
    rw [map_add (f := _), hfF, zero_add]
  have hfb : ∀ k, f (b k) = f (pN (b k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (b k)]
    rw [map_add (f := _), hfF, zero_add]
  have hxa : ∀ k, x (a k) = x (pF (a k)) + x (pN (a k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (a k)]
    rw [map_add (f := _)]
  have hxb : ∀ k, x (b k) = x (pF (b k)) + x (pN (b k)) := fun k ↦ by
    conv_lhs => rw [← hsplit (b k)]
    rw [map_add (f := _)]
  have hxl : ∀ k, x ⟨_, hω (Sum.inl k)⟩ = x (pF (b k)) := fun k ↦
    congrArg x (Subtype.ext (hωl k))
  have hxr : ∀ k, x ⟨_, hω (Sum.inr k)⟩ = x (pF (a k)) := fun k ↦
    congrArg x (Subtype.ext (hωr k))
  have hv := hvan f x
  rw [wedgeForm_apply, Fintype.sum_sum_type]
  simp only [hxl, hxr, hcl, hcr, map_neg]
  simp only [hfa, hfb, hxa, hxb]
  rw [← Finset.sum_add_distrib, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← hv]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

theorem perf_of_lag {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (F : Submodule K V) (g : ℕ) (hV : Module.finrank K V = 2 * g) (hF : Module.finrank K F = g)
    (ψ : LinearMap.BilinForm K V) (alt : ψ.IsAlt) (iso : ∀ x ∈ F, ∀ y ∈ F, ψ x y = 0)
    (rad : ∀ x, (∀ f ∈ F, ψ f x = 0) → x ∈ F) : LinearMap.IsPerfPair ψ := by
  let T : V →ₗ[K] Module.Dual K F := (ψ ∘ₗ F.subtype).flip
  have hker : LinearMap.ker T = F := by
    ext x
    exact ⟨fun h ↦ rad x fun f hf ↦ LinearMap.congr_fun (LinearMap.mem_ker.1 h) ⟨f, hf⟩,
      fun h ↦ LinearMap.mem_ker.2 (LinearMap.ext fun f ↦ iso f.1 f.2 x h)⟩
  have hr : LinearMap.range T = ⊤ := by
    have := LinearMap.finrank_range_add_finrank_ker T
    rw [hker, hF, hV] at this
    apply Submodule.eq_top_of_finrank_eq
    rw [Subspace.dual_finrank_eq, hF]
    omega
  have inj : ∀ f, (∀ x, ψ f x = 0) → f = 0 := fun f h ↦ by
    have hf : f ∈ F := rad f fun y _ ↦ by rw [← alt.neg_eq, h, neg_zero]
    have : (⟨f, hf⟩ : F) = 0 := (Module.forall_dual_apply_eq_zero_iff K _).1 fun l ↦ by
      obtain ⟨x, rfl⟩ := LinearMap.range_eq_top.1 hr l
      exact h x
    exact congrArg Subtype.val this
  refine LinearMap.IsPerfPair.of_injective ((injective_iff_map_eq_zero _).2 fun f hf ↦ inj f fun x ↦ ?_)
    ((injective_iff_map_eq_zero _).2 fun f hf ↦ inj f fun x ↦ ?_)
  · rw [hf]; rfl
  · have := LinearMap.congr_fun hf x
    rw [← alt.neg_eq]
    exact neg_eq_zero.2 this

theorem finrank_of_rankAtStalk {K : Type} {V : Type*} [Field K] [AddCommGroup V] [Module K V] {g : ℕ}
    (h : ∀ p : PrimeSpectrum K, Module.rankAtStalk V p = g) : Module.finrank K V = g := by
  have := h (Classical.arbitrary _)
  rw [Module.rankAtStalk_eq_finrank_of_free] at this
  simpa using this

end CrystallinePoints.Pd
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

theorem perfect_field (hF : AbelianDeRham.Free) (hH : AbelianDeRham.Hodge) {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {L : LB A.left} (hL : L.IsLB) {ψ : LinearMap.BilinForm K (HdR A)} (hψ : IsPolForm (dp0 K) (𝟙 _) A L ψ) (hiso : ∀ x ∈ Fil A, ∀ y ∈ Fil A, ψ x y = 0) (hK : ReciprocityTheory.ChartRestriction.G.Out.KTriv A L) : LinearMap.IsPerfPair ψ := by
  classical
  haveI := hA.comm
  obtain ⟨I, _, c, ω, hω, hch, hψf⟩ := chern_eq_sum hF hH hA hg hψ hiso
  obtain ⟨hfin, -, hrk⟩ := AbelianDeRham.Free.prim hF hA hg
  obtain ⟨hLie, -, -, -, hrkF⟩ := hH K A g hA hg
  have d1 : Module.finrank K (primDR A) = 2 * g := finrank_of_rankAtStalk hrk
  have d2 : Module.finrank K (PrimitiveSubmodule A) = g := finrank_of_rankAtStalk hrkF
  have d3 : Module.finrank K (Fil A) = g := by
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq (PrimitiveSubmodule A)
    rw [d1, d2] at this
    change g + Module.finrank K (Fil A) = _ at this
    omega
  refine perf_of_lag (Fil A) g (Subspace.dual_finrank_eq.trans d1) d3 ψ hψ.isAlt hiso fun x hx ↦ ?_
  obtain ⟨v, hv, -⟩ := hLie.1 x
  choose z hz using fun k ↦ H1.mk_surjective _ (c k).1
  have hmem : ∑ k, tanVal v (ω k) • c k ∈ PrimitiveSubmodule A := by
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := PrimitiveSubmodule A), Submodule.mem_dualCoannihilator]
    intro f hf
    have e := hx f hf
    rw [hψf f hf] at e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_smul, smul_eq_mul, hv.2 (ω k) (hω k), _root_.mul_comm]
  have hch' : IsChern (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L (∑ k, cup _ (H1.mk _ (z k)) (Form.cl _ (ω k))) := by
    simpa only [hz] using hch
  let J : Type := {p : A.left.affineOpens × L.ι // p.1.1 ≤ L.U p.2}
  have hr := GlobalTheory.T.isCechRepresentative_chernClass_tangentValue K A hA L hL I z ω hch' v hv.1 J (fun j ↦ j.1.1) (fun j ↦ j.1.2) fun j ↦ j.2
  have hcov : ⨆ j : J, j.1.1.1 = ⊤ := by
    refine eq_top_iff.2 fun p _ ↦ ?_
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ p))
    obtain ⟨U, hU, hp, hle⟩ := exists_isAffineOpen_mem_and_subset (U := L.U k) hk
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨U, hU⟩, k), hle⟩, hp⟩
  have h1 : v = 1 := eq_one_of_isRep hL hK hv.1 _ hcov _ (fun j ↦ j.2) _ hr (by
    have := Submodule.mem_comap.1 hmem
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul] at this
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hz]
    exact this)
  subst h1
  exact isLieImage_one_iff.1 hv

end CrystallinePoints.Pd
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.IsPerfPairOfSurjective
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

theorem eq_top_of_residue {R : Type} {G : Type*} [CommRing R] [AddCommGroup G] [Module R G]
    [Module.Finite R G] [Module.Projective R G] (N : Submodule R (Module.Dual R G))
    (h : ∀ m : Ideal R, m.IsMaximal → ∀ ψ : Module.Dual R G, ∃ χ ∈ N, ∀ x, ψ x - χ x ∈ m) :
    N = ⊤ := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R G
  have hm : ∀ (m : Ideal R) (χ : Module.Dual R G), (∀ x, χ x ∈ m) →
      χ ∈ m • (⊤ : Submodule R (Module.Dual R G)) := fun m χ hχ ↦ by
    have e : χ = ∑ i, χ (f (Pi.single i 1)) • (LinearMap.proj i ∘ₗ g) := by
      ext x
      have e1 : x = f (g x) := (LinearMap.congr_fun hfg x).symm
      conv_lhs => rw [e1, pi_eq_sum_univ' (g x)]
      simp [mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hχ _) Submodule.mem_top
  rw [eq_top_iff]
  intro ψ _
  by_contra hψ
  have hI : N.comap (LinearMap.toSpanSingleton R _ ψ) ≠ ⊤ := fun e ↦ hψ (by
    have : (1 : R) ∈ N.comap (LinearMap.toSpanSingleton R _ ψ) := e ▸ Submodule.mem_top
    simpa using this)
  obtain ⟨m, hmax, hle⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m
    (⊤ : Submodule R (Module.Dual R G ⧸ N)) Module.Finite.fg_top (by
      intro q _
      obtain ⟨φ, rfl⟩ := N.mkQ_surjective q
      obtain ⟨χ, hχ, hx⟩ := h m hmax φ
      have e : N.mkQ φ = N.mkQ (φ - χ) := by
        rw [map_sub, show N.mkQ χ = 0 from (Submodule.Quotient.mk_eq_zero N).2 hχ, sub_zero]
      rw [e, ← Submodule.range_mkQ N, ← Submodule.map_top, ← Submodule.map_smul'']
      exact Submodule.mem_map_of_mem (hm m _ hx))
  have h1 : r ∈ m := hle (by
    have := hr0 (N.mkQ ψ) Submodule.mem_top
    rw [← map_smul] at this
    simpa using (Submodule.Quotient.mk_eq_zero N).1 this)
  exact hmax.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using m.sub_mem h1 hr))

theorem exists_mem_Fil_corr (hF' : AbelianDeRham.Free) (hH : AbelianDeRham.Hodge) (hB : AbelianDeRham.BaseChange)
    {R : Type} [CommRing R] {T : Type} [CommRing T] [Algebra T R]
    (su : Function.Surjective (algebraMap T R)) {C : Over (Sp T)} [GrpObj C] {g : ℕ} (hC : IsAbelianScheme C)
    (gC : SmoothOfRelativeDimension g C.hom) {A : Over (Sp R)} [GrpObj A] {φ : A.left ⟶ C.left}
    (h : IsGrpPullback A C (spMap (algebraMap T R)) φ) {f : HdR A} (hf : f ∈ Fil A) :
    ∃ d ∈ Fil C, (AbelianDeRham.bcMor h).Corr d f := by
  obtain ⟨-, hF⟩ := hB T C g hC gC R A φ h
  obtain ⟨-, ⟨N, hN⟩, -⟩ := hH T C g hC gC
  haveI : Module.Projective T (primDR C) := (hF'.prim hC gC).2.1
  let l : primDR C →ₗ[T] R :=
    { toFun c := f ((AbelianDeRham.bcMor h).pull c)
      map_add' := fun a b => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun a b => by rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
  obtain ⟨d₀, hd₀⟩ := Module.projective_lifting_property (Algebra.linearMap T R) l su
  have e₀ : ∀ c, algebraMap T R (d₀ c) = f ((AbelianDeRham.bcMor h).pull c) := fun c => LinearMap.congr_fun hd₀ c
  have z : ∀ c ∈ PrimitiveSubmodule C, f ((AbelianDeRham.bcMor h).pull c) = 0 := fun c hc =>
    (Submodule.mem_dualAnnihilator _).1 hf _ (hF ▸ Submodule.subset_span ⟨c, hc, rfl⟩)
  let p : primDR C →ₗ[T] primDR C := N.subtype ∘ₗ N.linearProjOfIsCompl _ hN.symm
  have p0 : ∀ c ∈ PrimitiveSubmodule C, p c = 0 := fun c hc =>
    (congrArg N.subtype (Submodule.linearProjOfIsCompl_apply_right hN.symm ⟨c, hc⟩)).trans (map_zero _)
  have p1 : ∀ c, c - p c ∈ PrimitiveSubmodule C := fun c => by
    obtain ⟨a, b, rfl, -⟩ := Submodule.existsUnique_add_of_isCompl hN c
    have e : p b = b := congrArg N.subtype (Submodule.linearProjOfIsCompl_apply_left hN.symm b)
    rw [map_add (f := _), p0 a a.2, e, zero_add, add_sub_cancel_right]
    exact a.2
  refine ⟨d₀ ∘ₗ p, (Submodule.mem_dualAnnihilator _).2 fun c hc => ?_, fun c => ?_⟩
  · rw [LinearMap.comp_apply, p0 c hc, map_zero]
  · rw [LinearMap.comp_apply, e₀, ← sub_eq_zero, ← map_sub, ← map_sub]
    exact z _ (p1 c)

theorem exists_corr (hF' : AbelianDeRham.Free) {R : Type} [CommRing R] {T : Type} [CommRing T] [Algebra T R]
    (su : Function.Surjective (algebraMap T R)) {C : Over (Sp T)} [GrpObj C] {g : ℕ} (hC : IsAbelianScheme C)
    (gC : SmoothOfRelativeDimension g C.hom) {A : Over (Sp R)} [GrpObj A] {φ : A.left ⟶ C.left}
    (h : IsGrpPullback A C (spMap (algebraMap T R)) φ) (f : HdR A) : ∃ d, (AbelianDeRham.bcMor h).Corr d f := by
  haveI : Module.Projective T (primDR C) := (hF'.prim hC gC).2.1
  let l : primDR C →ₗ[T] R :=
    { toFun c := f ((AbelianDeRham.bcMor h).pull c)
      map_add' := fun a b => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun a b => by rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
  obtain ⟨d₀, hd₀⟩ := Module.projective_lifting_property (Algebra.linearMap T R) l su
  have e₀ : ∀ c, algebraMap T R (d₀ c) = f ((AbelianDeRham.bcMor h).pull c) := fun c => LinearMap.congr_fun hd₀ c
  exact ⟨d₀, fun c ↦ (e₀ c).symm⟩

theorem isPerfPair_of_surjective {R : Type} {G : Type*} [CommRing R] [AddCommGroup G] [Module R G]
    [Module.IsReflexive R G] (ψ : LinearMap.BilinForm R G) (ha : ψ.IsAlt) (hs : Function.Surjective ψ) :
    LinearMap.IsPerfPair ψ := by
  have hi : Function.Injective ψ := (injective_iff_map_eq_zero _).2 fun x hx ↦ by
    refine (Module.bijective_dual_eval R G).1 (LinearMap.ext fun χ ↦ ?_)
    obtain ⟨y, rfl⟩ := hs χ
    rw [Module.Dual.eval_apply, map_zero, LinearMap.zero_apply, ← ha.neg_eq, hx, LinearMap.zero_apply, neg_zero]
  have hf : ∀ x, LinearMap.flip ψ x = ψ (-x) := fun x ↦ LinearMap.ext fun y ↦ by
    rw [LinearMap.flip_apply, map_neg, LinearMap.neg_apply, ha.neg_eq]
  refine ⟨⟨hi, hs⟩, fun x y h ↦ neg_injective (hi (by rw [← hf, ← hf, h])), fun χ ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hs χ
  exact ⟨-y, by rw [hf, neg_neg]⟩

theorem perfect_ring_of (hP : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      ∀ L : LB A.left, L.IsLB → ∀ ψ : LinearMap.BilinForm K (HdR A), IsPolForm (dp0 K) (𝟙 _) A L ψ →
      (∀ x ∈ Fil A, ∀ y ∈ Fil A, ψ x y = 0) → ReciprocityTheory.ChartRestriction.G.Out.KTriv A L → LinearMap.IsPerfPair ψ)
    (hF : AbelianDeRham.Free) (hH : AbelianDeRham.Hodge) (hB : AbelianDeRham.BaseChange) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {L : LB A.left} (hL : L.IsLB) {ψ : LinearMap.BilinForm R (HdR A)} (hψ : IsPolForm (dp0 R) (𝟙 _) A L ψ) (hiso : ∀ x ∈ Fil A, ∀ y ∈ Fil A, ψ x y = 0) (hK : ReciprocityTheory.ChartRestriction.G.Out.KTriv A L) : LinearMap.IsPerfPair ψ := by
  obtain ⟨_, _, -⟩ := hF.prim hA hg
  refine isPerfPair_of_surjective ψ hψ.isAlt (LinearMap.range_eq_top.1 (eq_top_of_residue _ fun m hm χ ↦ ?_))
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have su : Function.Surjective (algebraMap R (R ⧸ m)) := Ideal.Quotient.mk_surjective
  obtain ⟨A', _, φ, h⟩ : ∃ (A' : Over (Sp (R ⧸ m))) (_ : GrpObj A') (φ : A'.left ⟶ A.left),
      IsGrpPullback A' A (spMap (algebraMap R (R ⧸ m))) φ := ⟨_, inferInstance, _, isGrpPullback_pullback A _⟩
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h
  have hg' := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  obtain ⟨ψ', hψ', k⟩ := hψ.pull (AbelianDeRham.bcMor h)
  have hL' : (L.pull φ).IsLB := pull_isLB hL φ
  obtain ⟨w, hw⟩ := GlobalTheory.Cris.ChernExists.lbIso_refl hL'
  have perf := hP (R ⧸ m) A' g hA' hg' _ hL' ψ' hψ' (fun x' hx' y' hy' ↦ by
    obtain ⟨x, hx, ex⟩ := exists_mem_Fil_corr hF hH hB su hA hg h hx'
    obtain ⟨y, hy, ey⟩ := exists_mem_Fil_corr hF hH hB su hA hg h hy'
    rw [k _ _ _ _ ex ey, hiso x hx y hy, map_zero]) (kTriv_pull h hL hL' ((isGen_iff w).1 hw) hK)
  obtain ⟨c, rfl⟩ := (Module.bijective_dual_eval R (primDR A)).2 χ
  obtain ⟨x', hx'⟩ := perf.bijective_left.2 (Module.Dual.eval _ _ ((AbelianDeRham.bcMor h).pull c))
  obtain ⟨x, ex⟩ := exists_corr hF su hA hg h x'
  refine ⟨ψ x, ⟨x, rfl⟩, fun y ↦ ?_⟩
  obtain ⟨y', ey⟩ := (hB R A g hA hg (R ⧸ m) A' φ h).1.exists y
  refine Ideal.Quotient.eq.1 ?_
  have e := k _ _ _ _ ex ey
  rw [hx'] at e
  exact ((ey c).symm.trans e)

end CrystallinePoints.Pd
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

theorem perfect_ring (hF : AbelianDeRham.Free) (hH : AbelianDeRham.Hodge) (hB : AbelianDeRham.BaseChange) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {L : LB A.left} (hL : L.IsLB) {ψ : LinearMap.BilinForm R (HdR A)} (hψ : IsPolForm (dp0 R) (𝟙 _) A L ψ) (hiso : ∀ x ∈ Fil A, ∀ y ∈ Fil A, ψ x y = 0) (hK : ReciprocityTheory.ChartRestriction.G.Out.KTriv A L) : LinearMap.IsPerfPair ψ :=
  perfect_ring_of (fun _ _ _ _ _ hA hg _ hL _ hψ hiso hK ↦ perfect_field hF hH hA hg hL hψ hiso hK)
    hF hH hB hA hg hL hψ hiso hK

end CrystallinePoints.Pd
