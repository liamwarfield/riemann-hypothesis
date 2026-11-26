module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.IndepFinset
open scoped TensorProduct

namespace UpperTheory.V.Z.J.D

section SlopeTestRemainingChoices

variable {G W W' : Type} [Group G] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

private lemma stable_eq {τ : Representation ℂ G W'} (hτ : τ.IsIrreducible) (P : Submodule ℂ W')
    (hP : ∀ g, ∀ v ∈ P, τ g v ∈ P) : P = ⊥ ∨ P = ⊤ := by
  haveI : IsSimpleOrder (Subrepresentation τ) := hτ
  rcases eq_bot_or_eq_top (⟨P, fun g _ hv => hP g _ hv⟩ : Subrepresentation τ) with h | h
  · left
    exact congrArg Subrepresentation.toSubmodule h
  · right
    exact congrArg Subrepresentation.toSubmodule h

private lemma indep_fin {τ : Representation ℂ G W'} {ρ : Representation ℂ G W} (hτ : AbsIrr τ) :
    ∀ (n : ℕ) (b : Fin n → (W' →ₗ[ℂ] W)), (∀ i, Intw τ ρ (b i)) → LinearIndependent ℂ b →
      ∀ u : Fin n → W', ∑ i, b i (u i) = 0 → u = 0 := by
  intro n
  induction n with
  | zero => intro b _ _ u _; exact Subsingleton.elim _ _
  | succ n ih =>
    intro b hb hli u hu
    have hli' : LinearIndependent ℂ fun i : Fin n => b i.succ :=
      hli.comp _ (Fin.succ_injective n)
    have ih' := ih (fun i => b i.succ) (fun i => hb i.succ) hli'
    let A : (Fin n → W') →ₗ[ℂ] W := ∑ i, (b i.succ) ∘ₗ LinearMap.proj i
    have hA : ∀ v, A v = ∑ i, b i.succ (v i) := fun v => by simp [A, LinearMap.sum_apply]
    have hAinj : Function.Injective A := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      exact ih' v (by rw [← hA]; exact hv)
    have hAeq : ∀ g v, A (fun i => τ g (v i)) = ρ g (A v) := fun g v => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hA, hA, map_sum]
      exact Finset.sum_congr rfl fun i _ => hb i.succ g (v i)
    have hsum : b 0 (u 0) + A (fun i => u i.succ) = 0 := by
      rw [hA, ← hu, Fin.sum_univ_succ]
    let P : Submodule ℂ W' := (LinearMap.range A).comap (b 0)
    have hP : ∀ g, ∀ v ∈ P, τ g v ∈ P := by
      rintro g v ⟨y, hy⟩
      refine ⟨fun i => τ g (y i), ?_⟩
      rw [hAeq, hy]
      exact (hb 0 g v).symm
    rcases stable_eq hτ.1 P hP with h | h
    · have h0 : u 0 = 0 := by
        have : u 0 ∈ P := ⟨-fun i => u i.succ, by
          rw [map_neg]; exact (eq_neg_of_add_eq_zero_left hsum |>.symm ▸ rfl)⟩
        rw [h] at this
        simpa using this
      have h1 : (fun i : Fin n => u i.succ) = 0 := by
        apply ih'
        rw [← hA, ← hsum, h0]
        simp
      funext i
      refine Fin.cases h0 (fun j => ?_) i
      exact congrFun h1 j
    · exfalso
      have hall : ∀ v, ∃ y, A y = b 0 v := fun v => by
        have : v ∈ P := h ▸ Submodule.mem_top
        exact this
      choose T hT using hall
      have hTadd : ∀ v v', T (v + v') = T v + T v' := fun v v' =>
        hAinj (by rw [map_add (f := _), hT, hT, hT, map_add (f := _)])
      have hTsmul : ∀ (a : ℂ) v, T (a • v) = a • T v := fun a v =>
        hAinj (by rw [map_smul, hT, hT, map_smul])
      have hTg : ∀ g v i, T (τ g v) i = τ g (T v i) := fun g v i => by
        have : T (τ g v) = fun i => τ g (T v i) :=
          hAinj (by rw [hAeq, hT, hT]; exact hb 0 g v)
        exact congrFun this i
      have hc : ∀ i : Fin n, ∃ a : ℂ, ∀ v, T v i = a • v := fun i => by
        obtain ⟨a, ha⟩ := hτ.2
          { toFun := fun v => T v i
            map_add' := fun v v' => by rw [hTadd]; rfl
            map_smul' := fun a v => by rw [hTsmul]; rfl } (fun g v => hTg g v i)
        exact ⟨a, fun v => by simpa using LinearMap.congr_fun ha v⟩
      choose c hc using hc
      have hrel : ∑ i, (Fin.cons (1 : ℂ) (fun j => -c j) : Fin (n + 1) → ℂ) i • b i = 0 := by
        rw [Fin.sum_univ_succ]
        ext v
        simp only [Fin.cons_zero, Fin.cons_succ, one_smul, LinearMap.add_apply, LinearMap.sum_apply,
          LinearMap.smul_apply, LinearMap.zero_apply, neg_smul, Finset.sum_neg_distrib]
        rw [← hT v, hA]
        simp only [hc, map_smul]
        simp
      have := Fintype.linearIndependent_iff.1 hli _ hrel 0
      simp at this

private lemma indep_finset {τ : Representation ℂ G W'} {ρ : Representation ℂ G W} (hτ : AbsIrr τ)
    {κ : Type} (b : κ → (W' →ₗ[ℂ] W)) (hb : ∀ i, Intw τ ρ (b i)) (hli : LinearIndependent ℂ b)
    (s : Finset κ) (u : κ → W') (hu : ∑ i ∈ s, b i (u i) = 0) : ∀ i ∈ s, u i = 0 := by
  let e : Fin s.card ≃ s := s.equivFin.symm
  have h := indep_fin hτ s.card (fun j => b (e j)) (fun j => hb _)
    (hli.comp _ (Subtype.val_injective.comp e.injective)) (fun j => u (e j)) (by
      rw [e.sum_comp (fun i : s => b i (u i)), Finset.sum_coe_sort s fun i => b i (u i)]
      exact hu)
  intro i hi
  have := congrFun h (e.symm ⟨i, hi⟩)
  simpa using this

end SlopeTestRemainingChoices

section Main

variable {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

private def intwSub (τ : Representation ℂ G W') (ρ : Representation ℂ G W) : Submodule ℂ (W' →ₗ[ℂ] W) where
  carrier := {f | Intw τ ρ f}
  add_mem' {f f'} h h' g v := by simp [h g v, h' g v]
  zero_mem' g v := by simp
  smul_mem' a f h g v := by simp [h g v]

private lemma comm_inl (ρ : Representation ℂ (G × H) W) (g : G) (h : H) (w : W) :
    ρ (g, 1) (ρ (1, h) w) = ρ (1, h) (ρ (g, 1) w) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  simp

private def kap (ρ : Representation ℂ (G × H) W) (τ : Representation ℂ G W') :
    Representation ℂ H (intwSub τ (ρ.comp (MonoidHom.inl G H))) where
  toFun h :=
    { toFun := fun φ => ⟨ρ (1, h) ∘ₗ φ.1, fun g v => by
        have := φ.2 g v
        simp only [LinearMap.comp_apply, MonoidHom.comp_apply, MonoidHom.inl_apply] at this ⊢
        rw [this, comm_inl]⟩
      map_add' := fun φ φ' => by ext; simp
      map_smul' := fun a φ => by ext; simp }
  map_one' := by
    ext φ v
    show ρ (1, 1) (φ.1 v) = φ.1 v
    rw [Prod.mk_one_one, map_one]
    rfl
  map_mul' h h' := by
    ext φ v
    show ρ (1, h * h') (φ.1 v) = ρ (1, h) (ρ (1, h') (φ.1 v))
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]

private def evl (τ : Representation ℂ G W') (ρ : Representation ℂ G W) :
    W' ⊗[ℂ] intwSub τ ρ →ₗ[ℂ] W :=
  TensorProduct.lift (LinearMap.flip (Submodule.subtype (intwSub τ ρ)))

private lemma evl_tmul (τ : Representation ℂ G W') (ρ : Representation ℂ G W) (w : W') (φ : intwSub τ ρ) :
    evl τ ρ (w ⊗ₜ φ) = φ.1 w := by
  simp [evl]

private lemma evl_inj {τ : Representation ℂ G W'} {ρ : Representation ℂ G W} (hτ : AbsIrr τ) :
    Function.Injective (evl τ ρ) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  let B := Module.Basis.ofVectorSpace ℂ (intwSub τ ρ)
  let e := TensorProduct.equivFinsuppOfBasisRight (M := W') B
  have hz' : z = (e z).sum fun i w => w ⊗ₜ B i := by
    have := TensorProduct.equivFinsuppOfBasisRight_symm_apply B (e z)
    rw [← this, e.symm_apply_apply]
  have hsum : ∑ i ∈ (e z).support, (B i).1 (e z i) = 0 := by
    rw [← hz]
    conv_rhs => rw [hz']
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => (evl_tmul τ ρ _ _).symm
  have hli : LinearIndependent ℂ fun i => (B i).1 :=
    B.linearIndependent.map' (intwSub τ ρ).subtype (Submodule.ker_subtype _)
  have h0 := indep_finset hτ (fun i => (B i).1) (fun i => (B i).2) hli _ (e z) hsum
  have : e z = 0 := by
    ext i
    by_cases hi : i ∈ (e z).support
    · simpa using h0 i hi
    · simpa using hi
  simpa using this

private lemma evl_surj {τ : Representation ℂ G W'} {ρ : Representation ℂ G W} (hI : Isot ρ τ) :
    Function.Surjective (evl τ ρ) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  refine hI.trans (iSup_le fun f => ?_)
  rintro _ ⟨w, rfl⟩
  exact ⟨w ⊗ₜ ⟨f.1, f.2⟩, evl_tmul τ ρ w ⟨f.1, f.2⟩⟩

end Main

theorem step :
    Step := by
  intro G H W W' _ _ _ _ _ _ ρ τ hτ hI
  refine ⟨intwSub τ (ρ.comp (MonoidHom.inl G H)), inferInstance, inferInstance, kap ρ τ,
    LinearEquiv.ofBijective (evl τ _) ⟨evl_inj hτ, evl_surj hI⟩, ?_⟩
  rintro ⟨g, h⟩ z
  show evl τ _ (box τ (kap ρ τ) (g, h) z) = ρ (g, h) (evl τ _ z)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul w φ =>
    have := φ.2 g w
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply] at this
    show evl τ _ (τ g w ⊗ₜ kap ρ τ h φ) = _
    rw [evl_tmul, evl_tmul]
    show ρ (1, h) (φ.1 (τ g w)) = _
    rw [this, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

end UpperTheory.V.Z.J.D
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.PiIsot
open UpperTheory.V.Z.J.D
open scoped TensorProduct

namespace UpperTheory.V.Z.J.D

section Ins

variable {I : Type} [DecidableEq I]

private def ins {β : I → Type} (i₀ : I) (a : β i₀) (b : ∀ j : {i // i ≠ i₀}, β j.1) : ∀ i, β i :=
  fun i => if h : i = i₀ then h ▸ a else b ⟨i, h⟩

private lemma ins_self {β : I → Type} (i₀ : I) (a : β i₀) (b : ∀ j : {i // i ≠ i₀}, β j.1) :
    ins i₀ a b i₀ = a := by
  simp [ins]

private lemma ins_ne {β : I → Type} (i₀ : I) (a : β i₀) (b : ∀ j : {i // i ≠ i₀}, β j.1)
    (j : {i // i ≠ i₀}) : ins i₀ a b j.1 = b j := by
  simp [ins, j.2]

private lemma ins_res {β : I → Type} (i₀ : I) (g : ∀ i, β i) :
    ins i₀ (g i₀) (fun j => g j.1) = g := by
  funext i
  by_cases h : i = i₀
  · subst h; exact ins_self _ _ _
  · exact ins_ne i₀ _ _ ⟨i, h⟩

private def insHom (Gi : I → Type) [∀ i, Group (Gi i)] (i₀ : I) :
    (Gi i₀ × ∀ j : {i // i ≠ i₀}, Gi j.1) →* ∀ i, Gi i where
  toFun p := ins i₀ p.1 p.2
  map_one' := by
    funext i
    by_cases h : i = i₀
    · subst h; exact ins_self _ _ _
    · exact ins_ne i₀ _ _ ⟨i, h⟩
  map_mul' p q := by
    funext i
    by_cases h : i = i₀
    · subst h
      simp only [Pi.mul_apply, ins_self, Prod.fst_mul]
    · have := fun (r : Gi i₀ × ∀ j : {i // i ≠ i₀}, Gi j.1) => ins_ne i₀ r.1 r.2 ⟨i, h⟩
      simp only [Pi.mul_apply] at this ⊢
      rw [this, this, this]
      rfl

private lemma insHom_res (Gi : I → Type) [∀ i, Group (Gi i)] (i₀ : I) (g : ∀ i, Gi i) :
    insHom Gi i₀ (g i₀, fun j => g j.1) = g :=
  ins_res i₀ g

private lemma insHom_inl (Gi : I → Type) [∀ i, Group (Gi i)] (i₀ : I) :
    (insHom Gi i₀).comp (MonoidHom.inl _ _) = MonoidHom.mulSingle Gi i₀ := by
  ext a i
  by_cases h : i = i₀
  · subst h
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
    exact ins_self _ _ _
  · simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h]
    exact ins_ne i₀ _ _ ⟨i, h⟩

private lemma insHom_inr (Gi : I → Type) [∀ i, Group (Gi i)] (i₀ : I) (j : {i // i ≠ i₀}) :
    ((insHom Gi i₀).comp (MonoidHom.inr _ _)).comp (MonoidHom.mulSingle (fun j : {i // i ≠ i₀} => Gi j.1) j) =
      MonoidHom.mulSingle Gi j.1 := by
  ext a i
  by_cases h : i = i₀
  · subst h
    simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, MonoidHom.mulSingle_apply,
      Pi.mulSingle_eq_of_ne (Ne.symm j.2)]
    exact ins_self _ _ _
  · simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, MonoidHom.mulSingle_apply]
    refine (ins_ne i₀ _ _ ⟨i, h⟩).trans ?_
    by_cases hj : i = j.1
    · subst hj
      simp
    · rw [Pi.mulSingle_eq_of_ne hj]
      have e : (⟨i, h⟩ : {i // i ≠ i₀}) ≠ j := fun e => hj (congrArg Subtype.val e)
      change (Pi.mulSingle j a : ∀ j : {i // i ≠ i₀}, Gi j.1) ⟨i, h⟩ = 1
      rw [Pi.mulSingle_eq_of_ne e]

private lemma res_update {β : I → Type} (i₀ i : I) (h : i ≠ i₀) (m : ∀ i, β i) (x : β i)
    [DecidableEq {i // i ≠ i₀}] [DecidableEq I] :
    (fun j : {i // i ≠ i₀} => Function.update m i x j.1) =
      Function.update (fun j : {i // i ≠ i₀} => m j.1) ⟨i, h⟩ x := by
  funext j
  by_cases hj : j = ⟨i, h⟩
  · subst hj; simp
  · rw [Function.update_of_ne hj, Function.update_of_ne (fun e => hj (Subtype.ext e))]

private lemma res_update_self {β : I → Type} (i₀ : I) (m : ∀ i, β i) (x : β i₀) [DecidableEq I] :
    (fun j : {i // i ≠ i₀} => Function.update m i₀ x j.1) = fun j : {i // i ≠ i₀} => m j.1 :=
  funext fun j : {i // i ≠ i₀} => Function.update_of_ne j.2 _ _

private def split (Wi : I → Type) [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] (i₀ : I) :
    (⨂[ℂ] i, Wi i) →ₗ[ℂ] Wi i₀ ⊗[ℂ] (⨂[ℂ] j : {i // i ≠ i₀}, Wi j.1) :=
  PiTensorProduct.lift
    { toFun := fun m => m i₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun j : {i // i ≠ i₀} => m j.1)
      map_update_add' := by
        intro _ m i x y
        by_cases h : i = i₀
        · subst h
          simp only [Function.update_self, res_update_self, TensorProduct.add_tmul]
        · classical
          simp only [Function.update_of_ne (Ne.symm h), res_update i₀ i h,
            MultilinearMap.map_update_add, TensorProduct.tmul_add]
      map_update_smul' := by
        intro _ m i c x
        by_cases h : i = i₀
        · subst h
          simp only [Function.update_self, res_update_self, TensorProduct.smul_tmul', RingHom.id_apply]
        · classical
          simp only [Function.update_of_ne (Ne.symm h), res_update i₀ i h,
            MultilinearMap.map_update_smul, TensorProduct.tmul_smul] }

private lemma split_tprod (Wi : I → Type) [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] (i₀ : I)
    (m : ∀ i, Wi i) :
    split Wi i₀ (PiTensorProduct.tprod ℂ m) =
      m i₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun j : {i // i ≠ i₀} => m j.1) := by
  simp [split]

private lemma split_range (Wi : I → Type) [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] (i₀ : I) :
    LinearMap.range (split Wi i₀) = ⊤ := by
  refine LinearMap.range_eq_top.2 fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x + y, map_add _ _ _⟩
  | tmul w t =>
    induction t using PiTensorProduct.induction_on with
    | smul_tprod r m =>
      refine ⟨r • PiTensorProduct.tprod ℂ (ins i₀ w m), ?_⟩
      rw [map_smul, split_tprod, ins_self, TensorProduct.tmul_smul]
      congr 3
      funext j
      exact ins_ne i₀ _ _ j
    | add a b ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨y, hy⟩ := hb
      exact ⟨x + y, by rw [map_add (f := _), hx, hy, TensorProduct.tmul_add]⟩

private lemma piRep_tprod {Gi Wi : I → Type} [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)]
    [∀ i, Module ℂ (Wi i)] (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) (g : ∀ i, Gi i) (m : ∀ i, Wi i) :
    piRep τ g (PiTensorProduct.tprod ℂ m) = PiTensorProduct.tprod ℂ fun i => τ i (g i) (m i) := by
  simp only [piRep, MonoidHom.comp_apply, PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
  rfl

private lemma split_intw [Fintype I] {Gi Wi : I → Type} [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)]
    [∀ i, Module ℂ (Wi i)] (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) (i₀ : I) (g : ∀ i, Gi i)
    (t : ⨂[ℂ] i, Wi i) :
    split Wi i₀ (piRep τ g t) =
      box (τ i₀) (piRep fun j : {i // i ≠ i₀} => τ j.1) (g i₀, fun j => g j.1) (split Wi i₀ t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, map_smul, map_smul, map_smul, piRep_tprod, split_tprod, split_tprod]
    simp only [box, Representation.tprod_apply, TensorProduct.map_tmul, MonoidHom.comp_apply,
      MonoidHom.coe_fst, MonoidHom.coe_snd, piRep_tprod]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end Ins

private lemma piIsot_empty {I : Type} [Fintype I] [DecidableEq I] [IsEmpty I] (Gi Wi : I → Type)
    [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)]
    (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) {X : Type} [AddCommGroup X] [Module ℂ X]
    (κ : Representation ℂ (∀ i, Gi i) X) : Isot κ (piRep τ) := by
  intro x _
  let f : (⨂[ℂ] i, Wi i) →ₗ[ℂ] X :=
    (LinearMap.toSpanSingleton ℂ X x).comp (PiTensorProduct.isEmptyEquiv I).toLinearMap
  have hf : Intw (piRep τ) κ f := by
    intro g v
    have hg : g = 1 := Subsingleton.elim _ _
    subst hg
    simp
  refine Submodule.mem_iSup_of_mem ⟨f, hf⟩ ⟨PiTensorProduct.tprod ℂ isEmptyElim, ?_⟩
  simp [f, PiTensorProduct.isEmptyEquiv_apply_tprod]

private lemma piIsot_card (hB : BoxIsot) (hP : PiIrr) (n : ℕ) :
    ∀ (I : Type) [Fintype I] [DecidableEq I], Fintype.card I = n → ∀ (Gi Wi : I → Type) [∀ i, Group (Gi i)]
      [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] (τ : ∀ i, Representation ℂ (Gi i) (Wi i)),
      (∀ i, AbsIrr (τ i)) → ∀ (X : Type) [AddCommGroup X] [Module ℂ X]
      (κ : Representation ℂ (∀ i, Gi i) X), (∀ i, Isot (κ.comp (MonoidHom.mulSingle Gi i)) (τ i)) →
      Isot κ (piRep τ) := by
  induction n with
  | zero =>
    intro I _ _ hc Gi Wi _ _ _ τ _ X _ _ κ _
    haveI : IsEmpty I := Fintype.card_eq_zero_iff.1 hc
    exact piIsot_empty Gi Wi τ κ
  | succ n ih =>
    intro I _ _ hc Gi Wi _ _ _ τ hτ X _ _ κ hκ
    haveI : Nonempty I := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨i₀⟩ := ‹Nonempty I›
    have hJ : Fintype.card {i // i ≠ i₀} = n := by
      simp [Fintype.card_subtype_compl, hc]
    let J := {i // i ≠ i₀}
    let κ' : Representation ℂ (Gi i₀ × ∀ j : J, Gi j.1) X := κ.comp (insHom Gi i₀)
    have h1 : Isot (κ'.comp (MonoidHom.inl _ _)) (τ i₀) := by
      have : κ'.comp (MonoidHom.inl _ _) = κ.comp (MonoidHom.mulSingle Gi i₀) := by
        rw [← insHom_inl]; rfl
      rw [this]
      exact hκ i₀
    have h2 : Isot (κ'.comp (MonoidHom.inr _ _)) (piRep fun j : J => τ j.1) := by
      refine ih J hJ (fun j => Gi j.1) (fun j => Wi j.1) (fun j => τ j.1) (fun j => hτ j.1) X
        (κ'.comp (MonoidHom.inr _ _)) fun j => ?_
      have : (κ'.comp (MonoidHom.inr _ _)).comp (MonoidHom.mulSingle (fun j : J => Gi j.1) j) =
          κ.comp (MonoidHom.mulSingle Gi j.1) := by
        rw [← insHom_inr]; rfl
      rw [this]
      exact hκ j.1
    have h3 := hB _ _ _ _ (τ i₀) (piRep fun j : J => τ j.1) (hτ i₀)
      (hP J (fun j => Gi j.1) (fun j => Wi j.1) (fun j => τ j.1) fun j => hτ j.1) X κ' h1 h2
    refine le_trans h3 (iSup_le fun f => ?_)
    have hf : Intw (piRep τ) κ (f.1.comp (split Wi i₀)) := by
      intro g t
      have := f.2 (g i₀, fun j => g j.1) (split Wi i₀ t)
      simp only [LinearMap.comp_apply]
      rw [split_intw, this]
      change κ (insHom Gi i₀ _) _ = _
      rw [insHom_res]
    refine le_iSup_of_le ⟨_, hf⟩ ?_
    rw [LinearMap.range_comp_of_range_eq_top _ (split_range Wi i₀)]

theorem piIsot :
    BoxIsot → PiIrr → PiIsot := by
  intro hB hP I _ _ Gi Wi _ _ _ τ hτ X _ _ κ hκ
  exact piIsot_card hB hP _ I rfl Gi Wi τ hτ X κ hκ

end UpperTheory.V.Z.J.D
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.NormCardLt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z.J.D

namespace UpperTheory.V.Z.J.D

section Emb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {l : ℕ} [Fact l.Prime]

private theorem norm_unif_lt (j : k →+* Qbar l) (hj : Continuous j) : ‖j (unif k : k)‖ < 1 := by
  have hv : Tendsto (fun n : ℕ => ((unif k : kˣ) : k) ^ n) atTop (nhds 0) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff]
    intro γ _
    obtain ⟨N, hN⟩ := exists_pow_lt₀ (ValuativeRel.uniformizer_lt_one (R := k)) γ
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [Set.mem_setOf_eq, map_pow, GlAx.unif_spec]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' ValuativeRel.uniformizer_lt_one.le hn) hN
  have hj' : Tendsto (fun n : ℕ => (j (unif k : k)) ^ n) atTop (nhds 0) := by
    have := (hj.tendsto 0).comp hv
    simpa [Function.comp_def, map_pow] using this
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp hj'

end Emb

section Pow

variable {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] (w : Plc L)

private theorem pow_ne (h : (L →+* Qbar l) → ℤ) :
    algPow w h ((unif (w.adicCompletion L) : (w.adicCompletion L)ˣ) : w.adicCompletion L) ≠ 0 := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite {j : w.adicCompletion L →+* Qbar l // Continuous j}
  unfold algPow
  rw [finprod_eq_prod_of_fintype]
  exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ((map_ne_zero j.1).2 (Units.ne_zero _))

private theorem pow_anti {h h' : (L →+* Qbar l) → ℤ} (hh : ∀ τ, h τ ≤ h' τ) :
    ‖algPow w h' ((unif (w.adicCompletion L) : (w.adicCompletion L)ˣ) : w.adicCompletion L)‖ ≤
      ‖algPow w h ((unif (w.adicCompletion L) : (w.adicCompletion L)ˣ) : w.adicCompletion L)‖ := by
  classical
  haveI : Finite {j : w.adicCompletion L →+* Qbar l // Continuous j} :=
    GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite {j : w.adicCompletion L →+* Qbar l // Continuous j}
  unfold algPow
  rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, norm_prod, norm_prod]
  refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_
  rw [norm_zpow, norm_zpow]
  have hlt := norm_unif_lt (k := w.adicCompletion L) (l := l) j.1 j.2
  have hpos : 0 < ‖j.1 ((unif (w.adicCompletion L) : (w.adicCompletion L)ˣ) : w.adicCompletion L)‖ :=
    norm_pos_iff.mpr ((_root_.map_ne_zero _).mpr (Units.ne_zero _))
  exact zpow_le_zpow_right_of_le_one₀ hpos hlt.le (hh _)

private theorem card_dvd (hl : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) : l ∣ Nat.card 𝓀[w.adicCompletion L] := by
  have hc : Nat.card 𝓀[w.adicCompletion L] = Nat.card (𝓞 L ⧸ w.asIdeal) := by
    have := GlobalTheory.LocLanglands.resCard_eq_normV (E := L) w
    simpa [GlobalTheory.SplitWeil.resCard, Formalism.ConjugateSelfDual.normV] using this
  rw [hc]
  haveI := w.isPrime
  have hz : ((l : ℕ) : 𝓞 L ⧸ w.asIdeal) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem (I := w.asIdeal)).mpr hl
    simpa using this
  have hdvd : addOrderOf (1 : 𝓞 L ⧸ w.asIdeal) ∣ l := by
    apply addOrderOf_dvd_of_nsmul_eq_zero
    simpa [nsmul_eq_mul] using hz
  have hord : addOrderOf (1 : 𝓞 L ⧸ w.asIdeal) = l := by
    rcases (Nat.dvd_prime (Fact.out : l.Prime)).mp hdvd with h | h
    · have h1 := addOrderOf_nsmul_eq_zero (1 : 𝓞 L ⧸ w.asIdeal)
      rw [h, one_nsmul] at h1
      exact absurd h1 one_ne_zero
    · exact h
  rw [← hord]
  exact addOrderOf_dvd_natCard _

private theorem norm_card_lt (hl : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) :
    ‖((Nat.card 𝓀[w.adicCompletion L] : ℕ) : Qbar l)‖ < 1 := by
  obtain ⟨m, hm⟩ := card_dvd w hl
  rw [hm, Nat.cast_mul, ← map_natCast (algebraMap ℚ_[l] (Qbar l)) l,
    ← map_natCast (algebraMap ℚ_[l] (Qbar l)) m, ← map_mul]
  have he : ‖algebraMap ℚ_[l] (Qbar l) ((l : ℚ_[l]) * (m : ℚ_[l]))‖ = ‖(l : ℚ_[l]) * (m : ℚ_[l])‖ :=
    PadicAlgCl.norm_extends l _
  rw [he, norm_mul]
  have hm1 : ‖(m : ℚ_[l])‖ ≤ 1 := by
    simpa using Padic.norm_int_le_one (p := l) (m : ℤ)
  calc ‖(l : ℚ_[l])‖ * ‖(m : ℚ_[l])‖ ≤ ‖(l : ℚ_[l])‖ * 1 :=
        mul_le_mul_of_nonneg_left hm1 (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact Padic.norm_p_lt_one

end Pow

private theorem prod_le {M : Type} [CommMonoid M] {n : ℕ} (f : ℕ → M) (j : Fin n) :
    ∏ i with i ≤ j, f (i : ℕ) = ∏ k ∈ Finset.range (j + 1), f k := by
  classical
  refine Finset.prod_nbij (fun i : Fin n => (i : ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_range]
    have : (i : ℕ) ≤ (j : ℕ) := hi
    omega
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_range] at hk
    refine ⟨⟨k, by omega⟩, ?_, rfl⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    show k ≤ (j : ℕ)
    omega
  · intro i _
    rfl

private theorem prod_tele {U : ℕ → ℂ} (h : ∀ k, U k ≠ 0) (m : ℕ) :
    ∏ k ∈ Finset.range m, U (k + 1) / U k = U m / U 0 := by
  induction m with
  | zero => simp [h 0]
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    field_simp [h m, h 0]

private theorem exp_core {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (a : Fin n → Qbar l) (u : Fin n → ℂ) (q : ℕ)
    (ha : ∀ i, a i ≠ 0) (hanti : ∀ i i', i ≤ i' → ‖a i'‖ ≤ ‖a i‖) (hq0 : (q : Qbar l) ≠ 0)
    (hq1 : ‖(q : Qbar l)‖ < 1) (hu : ∀ j, ‖ι.symm (u j)‖ = 1) :
    ∃ ω : Fin n → ℂˣ, Function.Injective ω ∧ ∀ j : Fin n,
      ι (∏ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1, a i) * u j =
        ∏ i with i ≤ j, (ω i : ℂ) * ((q : ℂ) ^ (i : ℕ))⁻¹ := by
  classical
  have hq0' : (q : ℂ) ≠ 0 := by
    intro h
    apply hq0
    have : q = 0 := by exact_mod_cast h
    simp [this]
  have hqpos : 0 < ‖(q : Qbar l)‖ := norm_pos_iff.mpr hq0
  let A : ℕ → Qbar l := fun k => if h : k < n then a ⟨k, h⟩ else 1
  let W : ℕ → Qbar l := fun k => if h : k < n then ι.symm (u ⟨k, h⟩) else 1
  have hAne : ∀ k, A k ≠ 0 := by
    intro k
    by_cases h : k < n
    · simp only [A, dif_pos h]; exact ha _
    · simp only [A, dif_neg h]; exact one_ne_zero
  have hWn : ∀ k, ‖W k‖ = 1 := by
    intro k
    by_cases h : k < n
    · simp only [W, dif_pos h]; exact hu _
    · simp only [W, dif_neg h]; exact norm_one
  have hWne : ∀ k, W k ≠ 0 := fun k => norm_ne_zero_iff.mp (by rw [hWn k]; exact one_ne_zero)
  let T : ℕ → Qbar l := fun k =>
    (∏ i ∈ Finset.range (k + 1), A i) * W k * ∏ i ∈ Finset.range (k + 1), (q : Qbar l) ^ i
  have hTne : ∀ k, T k ≠ 0 := by
    intro k
    refine mul_ne_zero (mul_ne_zero ?_ (hWne k)) ?_
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => hAne i
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ hq0
  let Tm : ℕ → Qbar l := fun k => if k = 0 then 1 else T (k - 1)
  have hTm0 : Tm 0 = 1 := by simp [Tm]
  have hTms : ∀ k, Tm (k + 1) = T k := by intro k; simp [Tm]
  have hTmne : ∀ k, Tm k ≠ 0 := by
    intro k
    rcases k with _ | k
    · rw [hTm0]; exact one_ne_zero
    · rw [hTms]; exact hTne k
  let U : ℕ → ℂ := fun k => ι (Tm k)
  have hUne : ∀ k, U k ≠ 0 := fun k => (_root_.map_ne_zero ι).mpr (hTmne k)
  let ω : Fin n → ℂˣ := fun i =>
    Units.mk0 (U ((i : ℕ) + 1) / U i) (div_ne_zero (hUne _) (hUne _))
  let G : ℕ → ℝ := fun k => ∏ i ∈ Finset.range k, (‖A i‖ * ‖(q : Qbar l)‖ ^ i)
  have hGs : ∀ k, G (k + 1) = G k * (‖A k‖ * ‖(q : Qbar l)‖ ^ k) :=
    fun k => Finset.prod_range_succ _ _
  have hG : ∀ k, k ≤ n → ‖Tm k‖ = G k := by
    intro k hk
    rcases k with _ | k
    · rw [hTm0, norm_one]; rfl
    · rw [hTms]
      simp only [T, G, norm_mul, norm_prod, norm_pow, hWn k, mul_one, Finset.prod_mul_distrib]
  have hGne : ∀ k, G k ≠ 0 := by
    intro k
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      mul_ne_zero (norm_ne_zero_iff.mpr (hAne i)) (pow_ne_zero _ hqpos.ne')
  have hnorm : ∀ i : Fin n, ‖ι.symm (ω i : ℂ)‖ = ‖a i‖ * ‖(q : Qbar l)‖ ^ (i : ℕ) := by
    intro i
    have e1 : ι.symm (ω i : ℂ) = Tm ((i : ℕ) + 1) / Tm i := by
      simp only [ω, Units.val_mk0, U, map_div₀, RingEquiv.symm_apply_apply]
    rw [e1, norm_div, hG _ (Nat.succ_le_of_lt i.isLt), hG _ i.isLt.le, hGs,
      mul_div_cancel_left₀ _ (hGne _)]
    simp only [A, dif_pos i.isLt]
  have hsa : StrictAnti (fun i : Fin n => ‖a i‖ * ‖(q : Qbar l)‖ ^ (i : ℕ)) := by
    intro i i' hii
    have h1 : ‖a i'‖ ≤ ‖a i‖ := hanti i i' hii.le
    have h2 : ‖(q : Qbar l)‖ ^ (i' : ℕ) < ‖(q : Qbar l)‖ ^ (i : ℕ) :=
      pow_lt_pow_right_of_lt_one₀ hqpos hq1 (Fin.lt_iff_val_lt_val.mp hii)
    have h3 : 0 < ‖a i‖ := norm_pos_iff.mpr (ha i)
    calc ‖a i'‖ * ‖(q : Qbar l)‖ ^ (i' : ℕ) ≤ ‖a i‖ * ‖(q : Qbar l)‖ ^ (i' : ℕ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ < ‖a i‖ * ‖(q : Qbar l)‖ ^ (i : ℕ) := mul_lt_mul_of_pos_left h2 h3
  refine ⟨ω, ?_, ?_⟩
  · intro i i' h
    apply hsa.injective
    show ‖a i‖ * ‖(q : Qbar l)‖ ^ (i : ℕ) = ‖a i'‖ * ‖(q : Qbar l)‖ ^ (i' : ℕ)
    rw [← hnorm i, ← hnorm i', h]
  · intro j
    have hL : (∏ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1, a i) =
        ∏ k ∈ Finset.range (j + 1), A k := by
      rw [← prod_le A j]
      refine Finset.prod_congr ?_ ?_
      · ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor <;> intro h
        · exact Fin.le_iff_val_le_val.mpr (by omega)
        · have := Fin.le_iff_val_le_val.mp h
          omega
      · intro i _
        simp only [A, dif_pos i.isLt]
    have hR : (∏ i with i ≤ j, (ω i : ℂ) * ((q : ℂ) ^ (i : ℕ))⁻¹) =
        ∏ k ∈ Finset.range (j + 1), (U (k + 1) / U k * ((q : ℂ) ^ k)⁻¹) :=
      prod_le (fun k => U (k + 1) / U k * ((q : ℂ) ^ k)⁻¹) j
    have hWj : ι (W j) = u j := by simp only [W, dif_pos j.isLt, RingEquiv.apply_symm_apply]
    have hqp : (∏ k ∈ Finset.range (j + 1), (q : ℂ) ^ k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ hq0'
    have hUj : U ((j : ℕ) + 1) =
        ι (∏ k ∈ Finset.range (j + 1), A k) * u j * ∏ k ∈ Finset.range (j + 1), (q : ℂ) ^ k := by
      simp only [U, hTms, T, map_mul, hWj, map_prod, map_pow, map_natCast]
    have hU0 : U 0 = 1 := by simp only [U, hTm0, map_one]
    rw [hL, hR, Finset.prod_mul_distrib, prod_tele hUne, Finset.prod_inv_distrib, hUj, hU0,
      div_one, mul_assoc _ (∏ k ∈ Finset.range (j + 1), (q : ℂ) ^ k), mul_inv_cancel₀ hqp, mul_one]

end UpperTheory.V.Z.J.D

theorem UpperTheory.V.Z.J.D.slope :
    Slope := by
  intro L Ω _ _ _ _ _ l _ n c H hA ι lam v u hu
  have hl := hA.Sl_over v
  obtain ⟨ω, h1, h2⟩ := exp_core ι
    (fun i => algPow (H.Sl v) (lowW lam i) ((unif ((H.Sl v).adicCompletion L) : ((H.Sl v).adicCompletion L)ˣ) : (H.Sl v).adicCompletion L))
    u (Nat.card 𝓀[(H.Sl v).adicCompletion L]) (fun i => pow_ne _ _)
    (fun i i' h => pow_anti _ fun τ => (lam τ).anti (Fin.rev_le_rev.2 h))
    (Nat.cast_ne_zero.2 Nat.card_pos.ne') (norm_card_lt _ hl) hu
  exact ⟨ω, h1, fun j => h2 j⟩
end
