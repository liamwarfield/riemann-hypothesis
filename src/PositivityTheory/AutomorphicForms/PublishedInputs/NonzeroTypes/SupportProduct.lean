module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpTop
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpCount
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpRes
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PIndDetK
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpOrd
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpSupp

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpPiEta
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct

namespace UpperTheory.TNZ.Grp

namespace P_spPiEta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} (G : Grp k n)

theorem twD_hasDetVec {Y : Fin G.s → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)) (a : Fin G.s)
    (h : HasDetVec (τ a) (G.μ a)) : HasDetVec (G.twD τ a) (G.μ a) := by
  obtain ⟨v, hv0, hv⟩ := h
  refine ⟨v, hv0, fun g hg => ?_⟩
  have h1 := detChar_of_mem_KO
    (isUnram_absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))) hg
  rw [twD, twist_apply, h1, hv g hg, Units.val_one, one_smul]

theorem twD_isSmooth {Y : Fin G.s → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)) (a : Fin G.s)
    (h : IsSmooth (τ a)) : IsSmooth (G.twD τ a) :=
  isSmooth_twist h (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem jacU_eq_jac {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (m : Levi k fun a : Fin G.s => Fin (G.d a)) (hm : m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a)))
    (y : Jacquet π (unipRad k G.e)) : jacU G.e π m y = jac G.e π m y := by
  rw [jac, twist_apply, MonoidHom.inv_apply, deltaHalf_of_mem_leviK hm, inv_one, Units.val_one, one_smul]

end P_spPiEta

theorem step_spPiEta {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : G.SpecialRepresentationEtaProp := by
  unfold SpecialRepresentationEtaProp
  intro hLift Y _ _ τ hsm hdet
  obtain ⟨v, hv0, hv⟩ := step_tensorVec k G.s G.d Y (G.twD τ) G.μ
    (fun a => P_spPiEta.twD_hasDetVec G τ a (hdet a))
  have hsm' : IsSmooth (piTensor (G.twD τ)) :=
    isSmooth_piTensor fun a => P_spPiEta.twD_isSmooth G τ a (hsm a)
  obtain ⟨f, hf1, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one G.e (piTensor (G.twD τ)) hsm' v
  let φ := Model.evalOne G.e (Representation.IntertwiningMap.id (multiProd G.e (G.twD τ)))
  have hφ : φ (Submodule.Quotient.mk f) = v := hf1
  let T : Subrepresentation (piTensor (G.twD τ)) := φ.range
  have hmem : ∀ x, φ x ∈ T.toSubmodule := fun x =>
    (Representation.IntertwiningMap.mem_range _ _ _ _).2 ⟨x, rfl⟩
  let ψ : (jac G.e (multiProd G.e (G.twD τ))).IntertwiningMap T.toRepresentation :=
    ⟨LinearMap.codRestrict T.toSubmodule φ.toLinearMap hmem, fun g => LinearMap.ext fun x => Subtype.ext (φ.isIntertwining _ _ g x)⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨w, hw⟩
    obtain ⟨x, rfl⟩ := (Representation.IntertwiningMap.mem_range _ _ _ _).1 hw
    exact ⟨x, rfl⟩
  have hsub : IsSubquotient T.toRepresentation (jac G.e (multiProd G.e (G.twD τ))) :=
    IsSubquotient.of_surjective ψ hψ
  have hη : G.HasEtaVec T.toRepresentation := by
    refine ⟨⟨v, hφ ▸ hmem _⟩, fun h => hv0 (congrArg Subtype.val h), fun m hm => ?_⟩
    apply Subtype.ext
    exact hv m fun a => hm a (Set.mem_univ a)
  obtain ⟨y, hy0, hy⟩ := hLift _ _ _ T.toRepresentation
    (isSmooth_jac G.e (isSmooth_parInd _ _)) hsub hη
  refine ⟨y, hy0, fun m hm => ?_⟩
  exact (P_spPiEta.jacU_eq_jac G _ m hm y).trans (hy m hm)

end UpperTheory.TNZ.Grp
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpUniq
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace P_spUniq

variable {n : ℕ} (G : Grp k n)

abbrev LG : Type := Levi k fun a : Fin G.s => Fin (G.d a)

abbrev KG : Subgroup (LG G) := leviK k (m := fun a : Fin G.s => Fin (G.d a))

theorem eta_mul (x y : LG G) : G.eta (x * y) = G.eta x * G.eta y := by
  simp only [Grp.eta, Pi.mul_apply, map_mul, Units.val_mul, Finset.prod_mul_distrib]

theorem eta_ne_zero (x : LG G) : G.eta x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _

def etaKer : Subgroup (LG G) := Subgroup.pi Set.univ fun a => (detChar (Fin (G.d a)) (G.μ a)).ker

theorem isOpen_etaKer : IsOpen (etaKer G : Set (LG G)) := by
  rw [etaKer, Subgroup.coe_pi]
  exact isOpen_set_pi Set.finite_univ fun a _ => (G.smooth a).detChar

theorem eta_eq_one {x : LG G} (hx : x ∈ etaKer G) : G.eta x = 1 := by
  refine Finset.prod_eq_one fun a _ => ?_
  have h := (Subgroup.mem_pi Set.univ).1 hx a (Set.mem_univ a)
  rw [MonoidHom.mem_ker, detChar_apply] at h
  rw [h, Units.val_one]

theorem isCompact_KG : IsCompact (KG G : Set (LG G)) := by
  show IsCompact ((Subgroup.pi Set.univ fun a => KO k (Fin (G.d a)) : Subgroup (LG G)) : Set (LG G))
  rw [Subgroup.coe_pi]
  exact isCompact_univ_pi fun _ => GlobalTheory.SplitFlip.isCompact_KO

section Avg

variable {W : Type} [AddCommGroup W] [Module ℂ W]

theorem mem_etaSp (ρ : Representation ℂ (LG G) W) (w : W) :
    w ∈ G.etaSp ρ ↔ ∀ m ∈ KG G, ρ m w = G.eta m • w := by
  simp only [Grp.etaSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem map_mem_etaSp {W' : Type} [AddCommGroup W'] [Module ℂ W'] {ρ : Representation ℂ (LG G) W}
    {ρ' : Representation ℂ (LG G) W'} (F : ρ.IntertwiningMap ρ') {w : W} (hw : w ∈ G.etaSp ρ) :
    F w ∈ G.etaSp ρ' := by
  rw [mem_etaSp] at hw ⊢
  intro m hm
  rw [← F.isIntertwining, hw m hm, map_smul]

def stab (ρ : Representation ℂ (LG G) W) (w : W) : Subgroup (LG G) where
  carrier := {g | ρ g w = w}
  mul_mem' := by
    intro a b ha hb
    have ha' : ρ a w = w := ha
    have hb' : ρ b w = w := hb
    show ρ (a * b) w = w
    rw [map_mul, Module.End.mul_apply, hb', ha']
  one_mem' := by
    show ρ 1 w = w
    rw [map_one, Module.End.one_apply]
  inv_mem' := by
    intro a ha
    have ha' : ρ a w = w := ha
    show ρ a⁻¹ w = w
    calc ρ a⁻¹ w = ρ a⁻¹ (ρ a w) := by rw [ha']
      _ = w := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_U (ρ : Representation ℂ (LG G) W) (hρ : IsSmooth ρ) (w₁ w₂ : W) :
    ∃ U : Subgroup (KG G), Finite (KG G ⧸ U) ∧
      ∀ u ∈ U, G.eta (u : LG G) = 1 ∧ ρ (u : LG G) w₁ = w₁ ∧ ρ (u : LG G) w₂ = w₂ := by
  let H : Subgroup (LG G) := etaKer G ⊓ stab G ρ w₁ ⊓ stab G ρ w₂
  have hH : IsOpen (H : Set (LG G)) := ((isOpen_etaKer G).inter (hρ w₁)).inter (hρ w₂)
  have : CompactSpace (KG G) := isCompact_iff_compactSpace.mp (isCompact_KG G)
  refine ⟨H.subgroupOf (KG G), Subgroup.quotient_finite_of_isOpen _ ?_, fun u hu => ?_⟩
  · exact hH.preimage continuous_subtype_val
  · have hu' : (u : LG G) ∈ H := Subgroup.mem_subgroupOf.1 hu
    exact ⟨eta_eq_one G hu'.1.1, hu'.1.2, hu'.2⟩

variable (U : Subgroup (KG G)) [Fintype (KG G ⧸ U)]

def avg (ρ : Representation ℂ (LG G) W) : W →ₗ[ℂ] W :=
  ∑ c : KG G ⧸ U, (G.eta (c.out : LG G))⁻¹ • ρ (c.out : LG G)

theorem avg_apply (ρ : Representation ℂ (LG G) W) (w : W) :
    avg G U ρ w = ∑ c : KG G ⧸ U, (G.eta (c.out : LG G))⁻¹ • ρ (c.out : LG G) w := by
  simp only [avg, LinearMap.sum_apply, LinearMap.smul_apply]

theorem avg_intertwine {W' : Type} [AddCommGroup W'] [Module ℂ W'] {ρ : Representation ℂ (LG G) W}
    {ρ' : Representation ℂ (LG G) W'} (F : ρ.IntertwiningMap ρ') (w : W) :
    F (avg G U ρ w) = avg G U ρ' (F w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [avg_apply, avg_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, F.isIntertwining]

theorem avg_mem (ρ : Representation ℂ (LG G) W) (A : Submodule ℂ W) (hA : ∀ m : LG G, ∀ w ∈ A, ρ m w ∈ A)
    {w : W} (hw : w ∈ A) : avg G U ρ w ∈ A := by
  rw [avg_apply]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hA _ _ hw)

theorem avg_of_mem_etaSp (ρ : Representation ℂ (LG G) W) {w : W} (hw : w ∈ G.etaSp ρ) :
    avg G U ρ w = (Fintype.card (KG G ⧸ U) : ℂ) • w := by
  rw [avg_apply]
  have h : ∀ c : KG G ⧸ U, (G.eta (c.out : LG G))⁻¹ • ρ (c.out : LG G) w = w := fun c => by
    rw [(mem_etaSp G ρ w).1 hw _ c.out.2, smul_smul, inv_mul_cancel₀ (eta_ne_zero G _), one_smul]
  rw [Finset.sum_congr rfl fun c _ => h c, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

theorem avg_mem_etaSp (ρ : Representation ℂ (LG G) W) {w : W}
    (hU : ∀ u ∈ U, G.eta (u : LG G) = 1 ∧ ρ (u : LG G) w = w) : avg G U ρ w ∈ G.etaSp ρ := by
  rw [mem_etaSp]
  intro m hm
  let m' : KG G := ⟨m, hm⟩
  have key : ∀ c : KG G ⧸ U, ρ m ((G.eta (c.out : LG G))⁻¹ • ρ (c.out : LG G) w) =
      G.eta m • ((G.eta ((m' • c).out : LG G))⁻¹ • ρ ((m' • c).out : LG G) w) := by
    intro c
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U (m' * c.out)
    have hc : m' • c = (QuotientGroup.mk (m' * c.out) : KG G ⧸ U) := by
      conv_lhs => rw [← QuotientGroup.out_eq' c]
      rfl
    rw [hc, hh]
    have h1 := hU (h : KG G) h.2
    have e1 : (((m' * c.out * (h : KG G) : KG G)) : LG G) = m * (c.out : LG G) * ((h : KG G) : LG G) := rfl
    rw [e1, eta_mul, eta_mul, h1.1, mul_one, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h1.2,
      map_smul, smul_smul]
    congr 1
    have h2 := eta_ne_zero G m
    have h3 := eta_ne_zero G (c.out : LG G)
    field_simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [avg_apply, map_sum, Finset.sum_congr rfl fun c _ => key c, ← Finset.smul_sum]
  congr 1
  exact Fintype.sum_equiv (MulAction.toPerm m') _ _ (fun c => rfl)

end Avg

theorem sup_inf_etaSp {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (LG G) W) (hρ : IsSmooth ρ)
    (A B : Submodule ℂ W) (hA : ∀ m : LG G, ∀ w ∈ A, ρ m w ∈ A) (hB : ∀ m : LG G, ∀ w ∈ B, ρ m w ∈ B) :
    (A ⊔ B) ⊓ G.etaSp ρ = A ⊓ G.etaSp ρ ⊔ B ⊓ G.etaSp ρ := by
  refine le_antisymm ?_ (le_inf (sup_le_sup inf_le_left inf_le_left) (sup_le inf_le_right inf_le_right))
  intro v hv
  obtain ⟨hv, hvE⟩ := Submodule.mem_inf.1 hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨U, hfin, hU⟩ := exists_U G ρ hρ a b
  let _ := Fintype.ofFinite (KG G ⧸ U)
  have hN : (Fintype.card (KG G ⧸ U) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h1 := avg_of_mem_etaSp G U ρ hvE
  rw [map_add (f := _)] at h1
  have hav : a + b = (Fintype.card (KG G ⧸ U) : ℂ)⁻¹ • (avg G U ρ a + avg G U ρ b) := by
    rw [h1, smul_smul, inv_mul_cancel₀ hN, one_smul]
  rw [hav]
  refine Submodule.smul_mem _ _ (Submodule.add_mem_sup ⟨avg_mem G U ρ A hA ha, ?_⟩ ⟨avg_mem G U ρ B hB hb, ?_⟩)
  · exact avg_mem_etaSp G U ρ fun u hu => ⟨(hU u hu).1, (hU u hu).2.1⟩
  · exact avg_mem_etaSp G U ρ fun u hu => ⟨(hU u hu).1, (hU u hu).2.2⟩

theorem twKer_le_map {Γ W W' : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {σ : Representation ℂ Γ W} {τ : Representation ℂ Γ W'} (f : σ.IntertwiningMap τ) (hf : Function.Surjective f)
    (N : Subgroup Γ) : twKer τ N 1 ≤ (twKer σ N 1).map f.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨u, v, rfl⟩
  obtain ⟨x, rfl⟩ := hf v
  refine ⟨σ u x - (((1 : N →* ℂˣ) u : ℂˣ) : ℂ) • x, Submodule.subset_span ⟨u, x, rfl⟩, ?_⟩
  simp [f.isIntertwining]

section Jac

variable {V : Type} [AddCommGroup V] [Module ℂ V] (I : Representation ℂ (GL (Fin n) k) V)

def jm {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {π : Representation ℂ (GL (Fin n) k) W} {τ : Representation ℂ (GL (Fin n) k) W'} (f : π.IntertwiningMap τ) :
    (jacU G.e π).IntertwiningMap (jacU G.e τ) :=
  jacquetMap f (unipRad k G.e) (leviEmb k G.e) (by
    intro g
    have hg : leviEmb k G.e g ∈ parab k G.e := (mem_parab_iff (R := k)).2 fun a b i j h => by
      simp [leviEmb, blockDiagonal'_apply, h.ne']
    exact parab_le_normalizer k G.e hg)

theorem jm_injective {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {π : Representation ℂ (GL (Fin n) k) W} {τ : Representation ℂ (GL (Fin n) k) W'} (hτ : IsSmooth τ)
    (f : π.IntertwiningMap τ) (hf : Function.Injective f) : Function.Injective (jm G f) :=
  GlobalTheory.JacquetExact.jacMap_injective G.e hτ f hf

def img (X : Subrepresentation I) : Submodule ℂ (Jacquet I (unipRad k G.e)) :=
  X.toSubmodule.map (twKer I (unipRad k G.e) 1).mkQ

theorem img_stable (X : Subrepresentation I) (m : LG G) (w : Jacquet I (unipRad k G.e)) (hw : w ∈ img G I X) :
    jacU G.e I m w ∈ img G I X := by
  obtain ⟨x, hx, rfl⟩ := hw
  exact ⟨I (leviEmb k G.e m) x, X.apply_mem_toSubmodule _ hx, rfl⟩

theorem img_inf (hI : IsSmooth I) (X Y : Subrepresentation I) : img G I (X ⊓ Y) = img G I X ⊓ img G I Y := by
  refine le_antisymm (Submodule.map_inf_le _) ?_
  intro v hv
  obtain ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩ := Submodule.mem_inf.1 hv
  have hd : x - y ∈ twKer I (unipRad k G.e) 1 := by
    have h := hxy.symm
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
    exact h
  let Q := I.quotient Y.toSubmodule (fun g _ hv => Y.apply_mem_toSubmodule g hv)
  let p : I.IntertwiningMap Q := ⟨Y.toSubmodule.mkQ, fun _ => LinearMap.ext fun _ => rfl⟩
  have hQ : IsSmooth Q := (IsSubquotient.of_surjective p (Submodule.mkQ_surjective _)).isSmooth hI
  let g : (subQuot X Y).IntertwiningMap Q :=
    ⟨Submodule.mapQ _ _ X.toSubmodule.subtype le_rfl,
      fun _ => Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)⟩
  have hg : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun z hz => ?_
    obtain ⟨x', rfl⟩ := Submodule.Quotient.mk_surjective _ z
    change (Submodule.Quotient.mk (x' : V) : V ⧸ Y.toSubmodule) = 0 at hz
    have hx'' : (x' : V) ∈ Y.toSubmodule := (Submodule.Quotient.mk_eq_zero Y.toSubmodule).1 hz
    exact (Submodule.Quotient.mk_eq_zero _).2 hx''
  let xX : X.toSubmodule := ⟨x, hx⟩
  have h0 : jm G g (Submodule.Quotient.mk (Submodule.Quotient.mk xX)) = 0 := by
    show (Submodule.Quotient.mk (Submodule.Quotient.mk x : V ⧸ Y.toSubmodule) : Jacquet Q (unipRad k G.e)) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    have h2 := GlobalTheory.JacquetExact.map_mem_twKer p hd
    have h3 : p (x - y) = Submodule.Quotient.mk x := by
      show Submodule.Quotient.mk (x - y) = _
      rw [Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).2 hy, sub_zero]
    rwa [h3] at h2
  have h4 : (Submodule.Quotient.mk xX : X.toSubmodule ⧸ Y.toSubmodule.comap X.toSubmodule.subtype) ∈
      twKer (subQuot X Y) (unipRad k G.e) 1 := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact jm_injective G hQ g hg (h0.trans (map_zero (jm G g)).symm)
  let q : X.toRepresentation.IntertwiningMap (subQuot X Y) := ⟨Submodule.mkQ _, fun _ => LinearMap.ext fun _ => rfl⟩
  obtain ⟨t, ht, htx⟩ := twKer_le_map q (Submodule.mkQ_surjective _) (unipRad k G.e) h4
  have h5 : ((xX - t : X.toSubmodule) : V) ∈ Y.toSubmodule := by
    have : (Submodule.Quotient.mk (xX - t) : X.toSubmodule ⧸ Y.toSubmodule.comap X.toSubmodule.subtype) = 0 := by
      rw [Submodule.Quotient.mk_sub, ← htx]
      exact sub_self _
    exact (Submodule.Quotient.mk_eq_zero (Y.toSubmodule.comap X.toSubmodule.subtype)).1 this
  let ι : X.toRepresentation.IntertwiningMap I := ⟨X.toSubmodule.subtype, fun _ => LinearMap.ext fun _ => rfl⟩
  have ht' : ((t : X.toSubmodule) : V) ∈ twKer I (unipRad k G.e) 1 := GlobalTheory.JacquetExact.map_mem_twKer ι ht
  refine ⟨x - (t : V), ⟨X.toSubmodule.sub_mem hx t.2, h5⟩, ?_⟩
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  simpa using neg_mem ht'

def dd (X : Subrepresentation I) : ℕ := Module.finrank ℂ ↥(img G I X ⊓ G.etaSp (jacU G.e I))

theorem dd_mono [FiniteDimensional ℂ ↥(G.etaSp (jacU G.e I))] {X Y : Subrepresentation I} (h : X ≤ Y) :
    dd G I X ≤ dd G I Y := by
  have : FiniteDimensional ℂ ↥(img G I Y ⊓ G.etaSp (jacU G.e I)) := Submodule.finiteDimensional_of_le inf_le_right
  exact Submodule.finrank_mono (inf_le_inf_right _ (Submodule.map_mono fun x hx => h hx))

theorem dd_modular (hI : IsSmooth I) [FiniteDimensional ℂ ↥(G.etaSp (jacU G.e I))] (X Y : Subrepresentation I) :
    dd G I (X ⊔ Y) + dd G I (X ⊓ Y) = dd G I X + dd G I Y := by
  have hJ := isSmooth_jacU G.e hI
  unfold dd
  rw [img_inf G I hI, show img G I (X ⊔ Y) = img G I X ⊔ img G I Y from Submodule.map_sup _ _ _,
    sup_inf_etaSp G _ hJ _ _ (img_stable G I X) (img_stable G I Y), inf_inf_distrib_right]
  have : FiniteDimensional ℂ ↥(img G I X ⊓ G.etaSp (jacU G.e I)) := Submodule.finiteDimensional_of_le inf_le_right
  have : FiniteDimensional ℂ ↥(img G I Y ⊓ G.etaSp (jacU G.e I)) := Submodule.finiteDimensional_of_le inf_le_right
  exact Submodule.finrank_sup_add_finrank_inf_eq _ _

def kerSub {A : Type} [AddCommGroup A] [Module ℂ A] {α : Representation ℂ (GL (Fin n) k) A}
    (S : Subrepresentation I) (f : S.toRepresentation.IntertwiningMap α) : Subrepresentation I where
  toSubmodule := (LinearMap.ker f.toLinearMap).map S.toSubmodule.subtype
  apply_mem_toSubmodule g := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨S.toRepresentation g x, ?_, rfl⟩
    have hx' : f x = 0 := hx
    show f (S.toRepresentation g x) = 0
    rw [f.isIntertwining, hx', map_zero]

theorem kerSub_le {A : Type} [AddCommGroup A] [Module ℂ A] {α : Representation ℂ (GL (Fin n) k) A}
    (S : Subrepresentation I) (f : S.toRepresentation.IntertwiningMap α) : kerSub I S f ≤ S := by
  intro v hv
  obtain ⟨x, -, rfl⟩ := hv
  exact x.2

theorem kerEquiv {A : Type} [AddCommGroup A] [Module ℂ A] {α : Representation ℂ (GL (Fin n) k) A}
    (S : Subrepresentation I) (f : S.toRepresentation.IntertwiningMap α) (hf : Function.Surjective f) :
    Nonempty ((subQuot S (kerSub I S f)).Equiv α) := by
  have hc : (kerSub I S f).toSubmodule.comap S.toSubmodule.subtype = LinearMap.ker f.toLinearMap :=
    Submodule.comap_map_eq_of_injective Subtype.val_injective _
  refine ⟨Representation.Equiv.mk ((Submodule.quotEquivOfEq _ _ hc).trans
    (f.toLinearMap.quotKerEquivOfSurjective hf)) fun g => ?_⟩
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
  exact f.isIntertwining _ _ g x

theorem lt_of_hasEtaVec (hI : IsSmooth I) [FiniteDimensional ℂ ↥(G.etaSp (jacU G.e I))]
    {A : Type} [AddCommGroup A] [Module ℂ A] {α : Representation ℂ (GL (Fin n) k) A}
    (S : Subrepresentation I) (f : S.toRepresentation.IntertwiningMap α) (hf : Function.Surjective f)
    (hη : G.HasEtaVec (jacU G.e α)) : dd G I (kerSub I S f) < dd G I S := by
  obtain ⟨z, hz0, hz⟩ := hη
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨y, rfl⟩ := hf a
  let ι : S.toRepresentation.IntertwiningMap I := ⟨S.toSubmodule.subtype, fun _ => LinearMap.ext fun _ => rfl⟩
  have hS : IsSmooth S.toRepresentation := (IsSubquotient.of_injective ι Subtype.val_injective).isSmooth hI
  let y' : Jacquet S.toRepresentation (unipRad k G.e) := Submodule.Quotient.mk y
  obtain ⟨U, hfin, hU⟩ := exists_U G (jacU G.e S.toRepresentation) (isSmooth_jacU G.e hS) y' y'
  let _ := Fintype.ofFinite (KG G ⧸ U)
  have hwE : avg G U (jacU G.e S.toRepresentation) y' ∈ G.etaSp (jacU G.e S.toRepresentation) :=
    avg_mem_etaSp G U _ fun u hu => ⟨(hU u hu).1, (hU u hu).2.1⟩
  have hzE : (Submodule.Quotient.mk (f y) : Jacquet α (unipRad k G.e)) ∈ G.etaSp (jacU G.e α) :=
    (mem_etaSp G _ _).2 hz
  have hFw : jm G f (avg G U (jacU G.e S.toRepresentation) y') =
      (Fintype.card (KG G ⧸ U) : ℂ) • (Submodule.Quotient.mk (f y) : Jacquet α (unipRad k G.e)) := by
    rw [avg_intertwine]
    exact avg_of_mem_etaSp G U _ hzE
  have hFw0 : jm G f (avg G U (jacU G.e S.toRepresentation) y') ≠ 0 := by
    rw [hFw]
    exact smul_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero) hz0
  have hvE : jm G ι (avg G U (jacU G.e S.toRepresentation) y') ∈ G.etaSp (jacU G.e I) := map_mem_etaSp G _ hwE
  have hvS : jm G ι (avg G U (jacU G.e S.toRepresentation) y') ∈ img G I S := by
    obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (avg G U (jacU G.e S.toRepresentation) y')
    rw [← hu]
    exact ⟨u, u.2, rfl⟩
  have hvX : jm G ι (avg G U (jacU G.e S.toRepresentation) y') ∉ img G I (kerSub I S f) := by
    rintro ⟨x, ⟨x', hx', rfl⟩, hxv⟩
    have hw : avg G U (jacU G.e S.toRepresentation) y' = Submodule.Quotient.mk x' :=
      jm_injective G hI ι Subtype.val_injective (show _ = jm G ι (Submodule.Quotient.mk x') from hxv.symm)
    apply hFw0
    rw [hw]
    have hx'' : f x' = 0 := hx'
    show (Submodule.Quotient.mk (f x') : Jacquet α (unipRad k G.e)) = 0
    rw [hx'', Submodule.Quotient.mk_zero]
  have : FiniteDimensional ℂ ↥(img G I S ⊓ G.etaSp (jacU G.e I)) := Submodule.finiteDimensional_of_le inf_le_right
  have hle : img G I (kerSub I S f) ⊓ G.etaSp (jacU G.e I) ≤ img G I S ⊓ G.etaSp (jacU G.e I) :=
    inf_le_inf_right _ (Submodule.map_mono fun x hx => kerSub_le I S f hx)
  have hlt : img G I (kerSub I S f) ⊓ G.etaSp (jacU G.e I) < img G I S ⊓ G.etaSp (jacU G.e I) := by
    refine lt_of_le_of_ne hle fun h => hvX ?_
    have hmem : jm G ι (avg G U (jacU G.e S.toRepresentation) y') ∈ img G I S ⊓ G.etaSp (jacU G.e I) :=
      Submodule.mem_inf.2 ⟨hvS, hvE⟩
    rw [← h] at hmem
    exact (Submodule.mem_inf.1 hmem).1
  exact Submodule.finrank_lt_finrank_of_lt hlt

end Jac

end P_spUniq


open P_spUniq in
theorem step_spUniq {n : ℕ} (G : Grp k n) : G.SphericalVectorUniqueness := by
  intro hLat V _ _ I hI hfin hle A B _ _ _ _ α β hα hβ hsa hsb hηa hηb
  haveI := hfin
  obtain ⟨Sa, fa, hfa⟩ := hsa
  obtain ⟨Sb, fb, hfb⟩ := hsb
  refine hLat (GL (Fin n) k) V I (dd G I) (fun X Y h => dd_mono G I h) (dd_modular G I hI) ?_ A B α β hα hβ
    ⟨kerSub I Sa fa, Sa, kerSub_le I Sa fa, lt_of_hasEtaVec G I hI Sa fa hfa hηa, kerEquiv I Sa fa hfa⟩
    ⟨kerSub I Sb fb, Sb, kerSub_le I Sb fb, lt_of_hasEtaVec G I hI Sb fb hfb hηb, kerEquiv I Sb fb hfb⟩
  exact (Submodule.finrank_mono inf_le_right).trans hle

end UpperTheory.TNZ.Grp
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpLift
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_spLift

variable {Γ V W : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_eigen_lift {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (hρ : IsSmooth ρ)
    (f : ρ.IntertwiningMap σ) {L : Subgroup Γ} (hL : IsCompact (L : Set Γ)) (χ : Γ → ℂ)
    (u : V) (hu : f u ≠ 0) (hχ : ∀ g ∈ L, σ g (f u) = χ g • f u) :
    ∃ v : V, v ≠ 0 ∧ ∀ g ∈ L, ρ g v = χ g • v :=
  _root_.UpperTheory.Reformulated.B.DYka2.main hρ f hL χ u hu hχ

end UpperTheory.TNZ.Grp.P_spLift

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_spLift {n : ℕ} (G : Grp k n) : G.SpecialLiftProp := by
  intro W X _ _ _ _ ρ σ hρ hsq hη
  obtain ⟨S, f, hf⟩ := hsq
  obtain ⟨y, hy, hyη⟩ := hη
  obtain ⟨u, rfl⟩ := hf y
  have hS : IsSmooth S.toRepresentation := fun v => by
    have : {g | S.toRepresentation g v = v} = {g | ρ g (v : W) = v} := by
      ext g
      simp only [Set.mem_ofPred_eq, Subtype.ext_iff]
      rfl
    rw [this]
    exact hρ v
  have hL : IsCompact ((leviK k (fun a : Fin G.s => Fin (G.d a))) :
      Set (Levi k fun a : Fin G.s => Fin (G.d a))) := by
    rw [leviK, Subgroup.coe_pi]
    exact isCompact_univ_pi fun a => GlobalTheory.SplitFlip.isCompact_KO
  obtain ⟨v, hv, hvη⟩ := P_spLift.exists_eigen_lift hS f hL G.eta u hy hyη
  refine ⟨(v : W), fun h => hv (Subtype.ext h), fun m hm => ?_⟩
  exact congrArg Subtype.val (hvη m hm)

end UpperTheory.TNZ.Grp
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpTwBasic
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

namespace P_spTwBasic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_detAbsPow (N : ℕ) (s : ℂ) : IsSmoothChar (detChar (Fin N) (absPow k s)) :=
  (GlobalTheory.SmGL.isSmoothChar_of_isUnram (GlobalTheory.SmGL.isUnram_absPow k s)).detChar

theorem hasDetVec_twist_absPow {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (η : kˣ →* ℂˣ) (s : ℂ) (h : HasDetVec ρ η) :
    HasDetVec (GlobalTheory.SmGL.twist ρ (detChar (Fin N) (absPow k s))) η := by
  obtain ⟨v, hv0, hv⟩ := h
  refine ⟨v, hv0, fun g hg => ?_⟩
  rw [GlobalTheory.SmGL.twist_apply, GlobalTheory.LocGL.detChar_of_mem_KO (GlobalTheory.SmGL.isUnram_absPow k s) hg, hv g hg,
    Units.val_one, one_smul]

end P_spTwBasic

theorem step_spTwBasic {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : G.NonzeroBasicTwistOfSpecialForm := by
  intro Y _ _ τ a hs hi hd
  unfold twD
  exact ⟨GlobalTheory.SmGL.isSmooth_twist hs (P_spTwBasic.isSmoothChar_detAbsPow _ _),
    GlobalTheory.LocGL.isIrreducible_twist hi _, P_spTwBasic.hasDetVec_twist_absPow _ _ _ hd⟩

end UpperTheory.TNZ.Grp
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpLat
noncomputable section

open scoped Classical

open GlobalTheory.SmGL

namespace UpperTheory.TNZ.P_spLat

variable {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {I : Representation ℂ Γ V}

theorem eqvInt {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    {α : Representation ℂ Γ A} {β : Representation ℂ Γ B} (e : α.Equiv β) (g : Γ) (v : A) :
    e (α g v) = β g (e v) :=
  Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v

def eqvTrans {A B C : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] {α : Representation ℂ Γ A} {β : Representation ℂ Γ B}
    {γ : Representation ℂ Γ C} (e : α.Equiv β) (f : β.Equiv γ) : α.Equiv γ :=
  Representation.Equiv.mk (e.toLinearEquiv.trans f.toLinearEquiv) (fun g => by
    ext v
    show f (e (α g v)) = γ g (f (e v))
    rw [eqvInt e, eqvInt f])

theorem dich {A : Type} [AddCommGroup A] [Module ℂ A] {α : Representation ℂ Γ A} (hα : α.IsIrreducible)
    (X Y S : Subrepresentation I) (e : (subQuot Y X).Equiv α) :
    Y ⊓ S ≤ X ∨ Y ≤ S ⊔ X := by
  let T : Subrepresentation α :=
    ⟨((S.toSubmodule.comap Y.toSubmodule.subtype).map
        (X.toSubmodule.comap Y.toSubmodule.subtype).mkQ).map e.toLinearMap, by
      rintro g _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨_, ⟨Y.toRepresentation g v, S.apply_mem_toSubmodule g hv, rfl⟩, ?_⟩
      exact eqvInt e g (Submodule.Quotient.mk v)⟩
  rcases hα.eq_bot_or_eq_top T with hT | hT
  · left
    intro v hv
    obtain ⟨hvY, hvS⟩ := hv
    have hm : e (Submodule.Quotient.mk (⟨v, hvY⟩ : Y.toSubmodule)) ∈ T.toSubmodule :=
      ⟨_, ⟨⟨v, hvY⟩, hvS, rfl⟩, rfl⟩
    rw [hT] at hm
    have h0 : e (Submodule.Quotient.mk (⟨v, hvY⟩ : Y.toSubmodule)) = 0 := (Submodule.mem_bot ℂ).1 hm
    rw [map_eq_zero_iff e (EquivLike.injective e), Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  · right
    intro v hvY
    have hm : e (Submodule.Quotient.mk (⟨v, hvY⟩ : Y.toSubmodule)) ∈ T.toSubmodule := by
      rw [hT]; exact Submodule.mem_top
    obtain ⟨_, ⟨w, hwS, rfl⟩, hw⟩ := hm
    have hw' := EquivLike.injective e hw
    have hx0 := (Submodule.Quotient.eq (X.toSubmodule.comap Y.toSubmodule.subtype)).1 hw'
    have hx : (w : V) - v ∈ X.toSubmodule := hx0
    show v ∈ S.toSubmodule ⊔ X.toSubmodule
    refine Submodule.mem_sup.2 ⟨w, hwS, v - w, ?_, by abel⟩
    simpa using X.toSubmodule.neg_mem hx

def eqv (Z W Y X : Subrepresentation I) (hZY : Z ≤ Y) (hY : Y ≤ Z ⊔ X)
    (hW : Z ⊓ W = Z ⊓ X) : (subQuot Z W).Equiv (subQuot Y X) := by
  let f : Z.toSubmodule →ₗ[ℂ] (Y.toSubmodule ⧸ X.toSubmodule.comap Y.toSubmodule.subtype) :=
    (X.toSubmodule.comap Y.toSubmodule.subtype).mkQ ∘ₗ Submodule.inclusion hZY
  have hf : Function.Surjective f := by
    rintro ⟨⟨v, hv⟩⟩
    obtain ⟨z, hz, x, hx, rfl⟩ := Submodule.mem_sup.1 (hY hv)
    refine ⟨⟨z, hz⟩, ?_⟩
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    refine (Submodule.Quotient.eq _).2 ?_
    show z - (z + x) ∈ X.toSubmodule
    simpa using X.toSubmodule.neg_mem hx
  have hker : W.toSubmodule.comap Z.toSubmodule.subtype = LinearMap.ker f := by
    ext ⟨v, hv⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker, f,
      LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show v ∈ W.toSubmodule ↔ v ∈ X.toSubmodule
    have h := congrArg Subrepresentation.toSubmodule hW
    simp only [Subrepresentation.toSubmodule_inf] at h
    constructor
    · intro hw
      have : v ∈ Z.toSubmodule ⊓ W.toSubmodule := ⟨hv, hw⟩
      rw [h] at this
      exact this.2
    · intro hx
      have : v ∈ Z.toSubmodule ⊓ X.toSubmodule := ⟨hv, hx⟩
      rw [← h] at this
      exact this.2
  refine Representation.Equiv.mk ((Submodule.quotEquivOfEq _ _ hker).trans
    (f.quotKerEquivOfSurjective hf)) (fun g => ?_)
  refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply]
  rfl

end UpperTheory.TNZ.P_spLat

namespace UpperTheory.TNZ

open P_spLat in
theorem step_spLat : SpecialLatticeProp := by
  intro Γ V _ _ _ I d hmono hmod htop A B _ _ _ _ α β hα hβ h₁ h₂
  obtain ⟨X₁, Y₁, hXY₁, hd₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨X₂, Y₂, hXY₂, hd₂, ⟨e₂⟩⟩ := h₂
  have hY₁ : d Y₁ ≤ 1 := (hmono le_top).trans htop
  have hY₂ : d Y₂ ≤ 1 := (hmono le_top).trans htop
  have hZ : d (Y₁ ⊓ Y₂) = 1 := by
    have := hmod Y₁ Y₂
    have := (hmono (le_top : Y₁ ⊔ Y₂ ≤ ⊤)).trans htop
    have := hmono (inf_le_left : Y₁ ⊓ Y₂ ≤ Y₁)
    omega
  have hN : d (X₁ ⊔ X₂) = 0 := by
    have := hmod X₁ X₂
    omega
  set Z := Y₁ ⊓ Y₂ with hZdef
  set N := X₁ ⊔ X₂ with hNdef
  have side : ∀ (C : Type) [AddCommGroup C] [Module ℂ C] (γ : Representation ℂ Γ C), γ.IsIrreducible →
      ∀ X Y : Subrepresentation I, X ≤ Y → X ≤ N → Z ≤ Y → d X = 0 → (subQuot Y X).Equiv γ →
      Y ≤ Z ⊔ X ∧ Z ⊓ N = Z ⊓ X := by
    intro C _ _ γ hγ X Y hXY hXN hZY hX e
    refine ⟨?_, ?_⟩
    · rcases dich hγ X Y Z e with h | h
      · exfalso
        have h' : Z ≤ X := by
          have : Y ⊓ Z = Z := inf_eq_right.2 hZY
          rw [← this]; exact h
        have := hmono h'
        omega
      · exact h
    · rcases dich hγ X Y N e with h | h
      · apply le_antisymm
        · exact le_inf inf_le_left ((inf_le_inf_right N hZY).trans h)
        · exact inf_le_inf_left Z hXN
      · exfalso
        have h' : Z ≤ N := hZY.trans (h.trans (sup_le le_rfl hXN))
        have := hmono h'
        omega
  have hd1 : d X₁ = 0 := by omega
  have hd2 : d X₂ = 0 := by omega
  obtain ⟨s₁, t₁⟩ := side A α hα X₁ Y₁ hXY₁ le_sup_left inf_le_left hd1 e₁
  obtain ⟨s₂, t₂⟩ := side B β hβ X₂ Y₂ hXY₂ le_sup_right inf_le_right hd2 e₂
  exact ⟨eqvTrans (eqvTrans e₁.symm (eqv Z N Y₁ X₁ inf_le_left s₁ t₁).symm)
    (eqvTrans (eqv Z N Y₂ X₂ inf_le_right s₂ t₂) e₂)⟩

end UpperTheory.TNZ
end
end

namespace UpperTheory.TNZ.Grp

theorem step_suppProd {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : G.SupportOfProductProp :=
  step_spTop G UpperTheory.TNZ.step_spLat (step_spUniq G) (step_spCount G) (step_spLift G) (step_spTwBasic G) (step_spRes G)
    (step_spPiEta G) step_spOrd (step_spPiSub G) (step_spSupp G) UpperTheory.TNZ.step_cuspSupp UpperTheory.TNZ.step_prodIrr
    UpperTheory.TNZ.step_tensorVec

end UpperTheory.TNZ.Grp
