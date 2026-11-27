import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic
import PEqualNP.Defs

open scoped BigOperators
namespace PEqualNP.Outside.L_lib_1043

def sign {n z : ℕ} (σ : Fin z → Fin n → Bool) (s : Fin z) (i : Fin n) : ℝ :=
  if σ s i then 1 else -1

lemma sign_sq {n z : ℕ} (σ : Fin z → Fin n → Bool) (s : Fin z) (i : Fin n) :
    sign σ s i ^ 2 = 1 := by
  unfold sign
  split <;> norm_num

lemma sign_abs {n z : ℕ} (σ : Fin z → Fin n → Bool) (s : Fin z) (i : Fin n) :
    |sign σ s i| = 1 := by
  unfold sign
  split <;> norm_num

abbrev Moments {n z : ℕ} (σ : Fin z → Fin n → Bool) :=
  ∀ I : Finset (Fin n), I.Nonempty → I.card ≤ 4 →
    (∑ s : Fin z, ∏ i ∈ I, sign σ s i) = 0

lemma mean_pair {n z : ℕ} (σ : Fin z → Fin n → Bool) (hm : Moments σ)
    (i j : Fin n) :
    (∑ s : Fin z, sign σ s i * sign σ s j) =
      if i = j then (z : ℝ) else 0 := by
  classical
  by_cases h : i = j
  · subst j
    simp only [← pow_two, sign_sq]
    simp
  · have hp := hm {i,j} (by simp) (by simp [h])
    simpa only [Finset.prod_pair h, if_neg h] using hp

lemma mean_four_distinct {n z : ℕ} (σ : Fin z → Fin n → Bool) (hm : Moments σ)
    (i j k l : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (∑ s : Fin z, sign σ s i * sign σ s j * sign σ s k * sign σ s l) = 0 := by
  classical
  have hp := hm {i,j,k,l} (by simp) (by simp [hij,hik,hil,hjk,hjl,hkl])
  convert hp using 1
  apply Finset.sum_congr rfl
  intro s _
  simp only [Finset.prod_insert (a := i) (s := {j,k,l}) (by simp [hij,hik,hil]),
    Finset.prod_insert (a := j) (s := {k,l}) (by simp [hjk,hjl]), Finset.prod_pair hkl]
  ring

lemma cancel1 {n z : ℕ} (σ : Fin z → Fin n → Bool) (s : Fin z) (i j k : Fin n) :
    sign σ s i * sign σ s i * sign σ s j * sign σ s k =
      sign σ s j * sign σ s k := by
  rw [← pow_two, sign_sq]
  ring

lemma cancel2 {n z : ℕ} (σ : Fin z → Fin n → Bool) (s : Fin z) (i j k : Fin n) :
    sign σ s i * sign σ s j * sign σ s i * sign σ s k =
      sign σ s j * sign σ s k := by
  calc
    _ = sign σ s i * sign σ s i * sign σ s j * sign σ s k := by ring
    _ = _ := cancel1 σ s i j k

lemma cancel3 {n z : ℕ} (σ : Fin z → Fin n → Bool) (s : Fin z) (i j k : Fin n) :
    sign σ s i * sign σ s j * sign σ s k * sign σ s i =
      sign σ s j * sign σ s k := by
  calc
    _ = sign σ s i * sign σ s i * sign σ s j * sign σ s k := by ring
    _ = _ := cancel1 σ s i j k

set_option maxHeartbeats 1000000 in
lemma mean_four {n z : ℕ} (σ : Fin z → Fin n → Bool) (hm : Moments σ)
    (i j k l : Fin n) :
    (∑ s : Fin z, sign σ s i * sign σ s j * sign σ s k * sign σ s l) =
      (z : ℝ) * ((if i = j ∧ k = l then 1 else 0) +
        (if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0) -
        2*(if i = j ∧ j = k ∧ k = l then 1 else 0)) := by
  classical
  by_cases hij : i = j
  · subst j
    simp_rw [cancel1, mean_pair σ hm]
    by_cases hkl : k = l
    · subst l
      by_cases hik : i = k
      · subst k; norm_num
      · simp [hik, Ne.symm hik]
    · have h1 : ¬ (i = k ∧ i = l) := by
        rintro ⟨rfl,h⟩
        exact hkl h
      have h2 : ¬ (i = l ∧ i = k) := by
        rintro ⟨h,rfl⟩
        exact hkl h
      simp [hkl,h1,h2]
  by_cases hik : i = k
  · subst k
    simp_rw [cancel2, mean_pair σ hm]
    simp only [hij, Ne.symm hij, false_and, and_false, ite_false, true_and,
      and_true, ite_true]
    split_ifs <;> ring
  by_cases hil : i = l
  · subst l
    simp_rw [cancel3, mean_pair σ hm]
    simp only [hij, hik, Ne.symm hij, Ne.symm hik, false_and, and_false,
      ite_false, true_and, and_true, ite_true]
    split_ifs <;> ring
  by_cases hjk : j = k
  · subst k
    have hc s : sign σ s i * sign σ s j * sign σ s j * sign σ s l =
        sign σ s i * sign σ s l := by
      calc
        _ = sign σ s j * sign σ s j * sign σ s i * sign σ s l := by ring
        _ = _ := cancel1 σ s j i l
    simp_rw [hc, mean_pair σ hm]
    simp [hij,hik,hil]
  by_cases hjl : j = l
  · subst l
    have hc s : sign σ s i * sign σ s j * sign σ s k * sign σ s j =
        sign σ s i * sign σ s k := by
      calc
        _ = sign σ s j * sign σ s j * sign σ s i * sign σ s k := by ring
        _ = _ := cancel1 σ s j i k
    simp_rw [hc, mean_pair σ hm]
    simp [hij,hik,hil]
  by_cases hkl : k = l
  · subst l
    have hc s : sign σ s i * sign σ s j * sign σ s k * sign σ s k =
        sign σ s i * sign σ s j := by
      calc
        _ = sign σ s k * sign σ s k * sign σ s i * sign σ s j := by ring
        _ = _ := cancel1 σ s k i j
    simp_rw [hc, mean_pair σ hm]
    simp [hij,hik,hil]
  rw [mean_four_distinct σ hm i j k l hij hik hil hjk hjl hkl]
  simp [hij,hik,hil,hjk,hjl,hkl]

def linearForm {n z : ℕ} (σ : Fin z → Fin n → Bool) (v : Fin n → ℝ) (s : Fin z) :=
  ∑ i, v i * sign σ s i

lemma second_moment {n z : ℕ} (σ : Fin z → Fin n → Bool) (hm : Moments σ)
    (v : Fin n → ℝ) :
    (∑ s, linearForm σ v s ^ 2) = (z : ℝ) * ∑ i, v i ^ 2 := by
  classical
  have expand s : linearForm σ v s ^ 2 =
      ∑ i, ∑ j, (v i * v j) * (sign σ s i * sign σ s j) := by
    simp only [linearForm, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i, ∑ j, (v i * v j) * ∑ s, sign σ s i * sign σ s j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = _ := by
      simp_rw [mean_pair σ hm]
      simp [mul_ite, Finset.mul_sum, pow_two, mul_comm]


set_option maxHeartbeats 2000000 in
lemma fourth_moment {n z : ℕ} (σ : Fin z → Fin n → Bool) (hm : Moments σ)
    (v : Fin n → ℝ) :
    (∑ s, linearForm σ v s ^ 4) =
      (z : ℝ) * (3 * (∑ i, v i ^ 2)^2 - 2 * ∑ i, v i ^ 4) := by
  classical
  have expand s : linearForm σ v s ^ 4 =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (v i * v j * v k * v l) *
          (sign σ s i * sign σ s j * sign σ s k * sign σ s l) := by
    simp only [linearForm, pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i, ∑ j, ∑ k, ∑ l, (v i*v j*v k*v l) *
        ∑ s, sign σ s i * sign σ s j * sign σ s k * sign σ s l := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
    _ = _ := by
      simp_rw [mean_four σ hm]
      simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ite_and, mul_ite, mul_zero, mul_one]
      simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.sum_const_zero, Finset.mem_univ, ite_true]
      ring_nf
      try simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring


lemma quartic_abs_bound (x t : ℝ) (ht : 0 ≤ t) :
    3*t^2*x^2 ≤ x^4+2*t^3*|x| := by
  have h4 : |x|^4 = x^4 := by
    calc
      _ = (|x|^2)^2 := by ring
      _ = (x^2)^2 := by rw [sq_abs]
      _ = _ := by ring
  have hi : |x| *(|x| -t)^2*(|x| +2*t) = x^4+2*t^3*|x| -3*t^2*x^2 := by
    calc
      _ = |x|^4+2*t^3*|x| -3*t^2*|x|^2 := by ring
      _ = _ := by rw [h4,sq_abs]
  have hp := mul_nonneg
    (mul_nonneg (abs_nonneg x) (sq_nonneg (|x| -t)))
    (show 0 ≤ |x| +2*t by positivity)
  rw [hi] at hp
  linarith

lemma strict_support_lower {n z : ℕ} (σ : Fin z → Fin n → Bool) (hm : Moments σ)
    (hz : 0 < z) (v : Fin n → ℝ) (hv : v ≠ 0) :
    (z : ℝ) * Real.sqrt (3 * ∑ i, v i^2) <
      3 * ∑ s, |linearForm σ v s| := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    ext i
    simpa using not_exists.mp h i
  let V : ℝ := ∑ i, v i^2
  let W : ℝ := ∑ i, v i^4
  let t : ℝ := Real.sqrt (3*V)
  let L : ℝ := ∑ s, |linearForm σ v s|
  have hV : 0 < V :=
    lt_of_lt_of_le (sq_pos_of_ne_zero hi)
      (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))
  have hvi4 : 0 < v i^4 := by
    simpa only [← pow_mul] using pow_pos (sq_pos_of_ne_zero hi) 2
  have hW : 0 < W :=
    lt_of_lt_of_le hvi4
      (Finset.single_le_sum (f := fun j : Fin n => v j^4) (fun j _ => by positivity) (Finset.mem_univ i))
  have hzr : (0 : ℝ) < z := by exact_mod_cast hz
  have ht : 0 < t := Real.sqrt_pos.2 (by positivity)
  have htsq : t^2 = 3*V := Real.sq_sqrt (by positivity)
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Fin z))) =>
    quartic_abs_bound (linearForm σ v s) t (le_of_lt ht))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [second_moment σ hm v, fourth_moment σ hm v, htsq] at hsum
  change 3*(3*V)*((z : ℝ)*V) ≤ (z : ℝ)*(3*V^2-2*W)+2*t^3*L at hsum
  have hh : 3*(z : ℝ)*V^2 < t^3*L := by
    nlinarith [mul_pos hzr hW]
  have ht4 : t^4 = 9*V^2 := by
    calc
      _ = (t^2)^2 := by ring
      _ = _ := by rw [htsq]; ring
  have hid : t^3*(3*L-(z : ℝ)*t) = 3*(t^3*L-3*(z : ℝ)*V^2) := by
    calc
      _ = 3*(t^3*L)-(z : ℝ)*t^4 := by ring
      _ = _ := by rw [ht4]; ring
  have hprod : 0 < t^3*(3*L-(z : ℝ)*t) := by
    rw [hid]
    linarith
  have hdiff : 0 < 3*L-(z : ℝ)*t := by
    by_contra h
    have hd : 3*L-(z : ℝ)*t ≤ 0 := by linarith
    have hn := mul_nonpos_of_nonneg_of_nonpos (le_of_lt (pow_pos ht 3)) hd
    linarith
  exact (sub_pos.mp hdiff)

lemma strict_support {n z : ℕ} (σ : Fin z → Fin n → Bool) (hm : Moments σ)
    (hz : 0 < z) (v a : Fin n → ℝ) (hv : v ≠ 0) :
    (2*(z : ℝ)/(1+3*∑ i, a i^2))*(∑ i, v i*a i) <
      ∑ s, |linearForm σ v s| := by
  let V : ℝ := ∑ i, v i^2
  let U : ℝ := ∑ i, a i^2
  let D : ℝ := ∑ i, v i*a i
  let t := Real.sqrt (3*V)
  let B := 1+3*U
  let T := (2*(z : ℝ)/B)*D
  have hV : 0 ≤ V := Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  have hU : 0 ≤ U := Finset.sum_nonneg (fun i _ => sq_nonneg (a i))
  have hB : 0 < B := by dsimp [B]; positivity
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have htsq : t^2 = 3*V := Real.sq_sqrt (by positivity)
  have hc : D^2 ≤ V*U := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v a
  have hsq : (6*D)^2 ≤ (B*t)^2 := by
    calc
      _ = 36*D^2 := by ring
      _ ≤ 36*(V*U) := mul_le_mul_of_nonneg_left hc (by norm_num)
      _ ≤ _ := by
        rw [mul_pow,htsq]
        dsimp [B]
        nlinarith [mul_nonneg hV (sq_nonneg (1-3*U))]
  have hlin : 6*D ≤ B*t := le_of_sq_le_sq hsq (mul_nonneg (le_of_lt hB) ht)
  have hzr : (0 : ℝ) ≤ z := by positivity
  have hscale := mul_le_mul_of_nonneg_left hlin hzr
  have hTeq : B*T = 2*(z : ℝ)*D := by
    dsimp [T]
    field_simp
  have hT : 3*T ≤ (z : ℝ)*t := by
    by_contra h
    have hp : 0 < B*(3*T-(z : ℝ)*t) := mul_pos hB (by linarith)
    nlinarith [hscale,hTeq]
  have hs := strict_support_lower σ hm hz v hv
  change (z : ℝ)*t < 3*∑ s, |linearForm σ v s| at hs
  change T < _
  linarith



def corr {n z : ℕ} (σ : Fin z → Fin n → Bool) :
    (Fin z → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun f i := ∑ s, f s * sign σ s i
  map_add' := by
    intro f g
    ext i
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c f
    ext i
    simp [Finset.mul_sum, mul_assoc]

lemma corr_apply {n z : ℕ} (σ : Fin z → Fin n → Bool)
    (f : Fin z → ℝ) (i : Fin n) :
    corr σ f i = ∑ s, f s * sign σ s i := rfl

lemma corr_linearForm {n z : ℕ} (σ : Fin z → Fin n → Bool) (hm : Moments σ)
    (v : Fin n → ℝ) :
    corr σ (linearForm σ v) = (z : ℝ) • v := by
  classical
  ext i
  simp only [corr_apply, linearForm, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, mean_pair σ hm]
  simp [mul_ite, mul_comm]

lemma corr_surjective {n z : ℕ} (σ : Fin z → Fin n → Bool) (hm : Moments σ)
    (hz : 0 < z) : Function.Surjective (corr σ) := by
  intro v
  refine ⟨linearForm σ (fun i => v i/(z : ℝ)), ?_⟩
  rw [corr_linearForm σ hm]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  have hzr : (z : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hz)
  field_simp

def cube (z : ℕ) : Set (Fin z → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Ioo (-1) 1)

lemma cube_mem {z : ℕ} (f : Fin z → ℝ) :
    f ∈ cube z ↔ ∀ s, -1 < f s ∧ f s < 1 := by
  simp [cube, Set.mem_pi]

lemma cube_convex (z : ℕ) : Convex ℝ (cube z) :=
  convex_pi (fun _ _ => convex_Ioo (-1) 1)

lemma cube_open (z : ℕ) : IsOpen (cube z) := by
  have he : cube z = ⋂ s : Fin z, {f : Fin z → ℝ | -1 < f s ∧ f s < 1} := by
    ext f
    simp [cube_mem]
  rw [he]
  apply isOpen_iInter_of_finite
  intro s
  have h1 : IsOpen {f : Fin z → ℝ | (-1 : ℝ) < f s} :=
    isOpen_lt continuous_const (continuous_apply s)
  have h2 : IsOpen {f : Fin z → ℝ | f s < (1 : ℝ)} :=
    isOpen_lt (continuous_apply s) continuous_const
  exact h1.inter h2

lemma cube_zero (z : ℕ) : (0 : Fin z → ℝ) ∈ cube z := by
  rw [cube_mem]
  intro s
  norm_num

lemma functional_repr {n : ℕ} (φ : (Fin n → ℝ) →L[ℝ] ℝ) (x : Fin n → ℝ) :
    φ x = ∑ i, φ (Pi.single i 1) * x i := by
  classical
  have he : x = ∑ i, x i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  conv_lhs => rw [he]
  simp [map_sum, map_smul, mul_comm]

lemma functional_corr {n z : ℕ} (σ : Fin z → Fin n → Bool)
    (φ : (Fin n → ℝ) →L[ℝ] ℝ) (f : Fin z → ℝ) :
    φ (corr σ f) = ∑ s, f s * linearForm σ (fun i => φ (Pi.single i 1)) s := by
  rw [functional_repr]
  simp only [corr_apply, linearForm, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  ring



set_option maxHeartbeats 1000000 in
lemma real_decoder_image {n z : ℕ} (σ : Fin z → Fin n → Bool) (hm : Moments σ)
    (hz : 0 < z) (a : Fin n → ℝ) :
    (fun i => (2*(z : ℝ)/(1+3*∑ j, a j^2))*a i) ∈ corr σ '' cube z := by
  classical
  let T : (Fin z → ℝ) →L[ℝ] (Fin n → ℝ) := (corr σ).toContinuousLinearMap
  let β : Fin n → ℝ := fun i => (2*(z : ℝ)/(1+3*∑ j, a j^2))*a i
  let D : Set (Fin n → ℝ) := T '' cube z
  change β ∈ D
  have hsurj : Function.Surjective T := corr_surjective σ hm hz
  have hconvex : Convex ℝ D := (cube_convex z).linear_image T.toLinearMap
  have hopen : IsOpen D := T.isOpenMap hsurj _ (cube_open z)
  by_contra hnot
  obtain ⟨φ,hsep⟩ := geometric_hahn_banach_open_point hconvex hopen hnot
  have hzero : (0 : Fin n → ℝ) ∈ D := by
    refine ⟨0,cube_zero z,?_⟩
    exact map_zero T
  have hpos : 0 < φ β := by simpa using hsep 0 hzero
  let v : Fin n → ℝ := fun i => φ (Pi.single i 1)
  have hv : v ≠ 0 := by
    intro he
    have hr := functional_repr φ β
    change φ β = ∑ i, v i * β i at hr
    rw [he] at hr
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hr
    linarith
  let L : ℝ := ∑ s, |linearForm σ v s|
  have hrepr : φ β = (2*(z : ℝ)/(1+3*∑ j, a j^2))*(∑ i, v i*a i) := by
    rw [functional_repr]
    change (∑ i, v i * ((2*(z : ℝ)/(1+3*∑ j, a j^2))*a i)) = _
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hbound : φ β < L := by
    rw [hrepr]
    exact strict_support σ hm hz v a hv
  have hL : 0 < L := lt_trans hpos hbound
  let α : ℝ := (1+φ β/L)/2
  have hrpos : 0 < φ β/L := div_pos hpos hL
  have hrlt : φ β/L < 1 := (div_lt_one hL).2 hbound
  have hα : 0 < α := by dsimp [α]; linarith
  have hα1 : α < 1 := by dsimp [α]; linarith
  have hαeq : α*L = (L+φ β)/2 := by
    dsimp [α]
    field_simp
  have hαL : φ β < α*L := by rw [hαeq]; linarith
  let g : Fin z → ℝ := fun s =>
    α*(if 0 ≤ linearForm σ v s then 1 else -1)
  have hg : g ∈ cube z := by
    rw [cube_mem]
    intro s
    dsimp [g]
    split_ifs <;> constructor <;> nlinarith
  have hcalc : φ (T g) = α*L := by
    change φ (corr σ g) = _
    rw [functional_corr]
    change (∑ s, g s * linearForm σ v s) = _
    dsimp only [g,L]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : 0 ≤ linearForm σ v s
    · simp only [if_pos hs,abs_of_nonneg hs]
      ring
    · simp only [if_neg hs,abs_of_neg (lt_of_not_ge hs)]
      ring
  have hbad := hsep (T g) (show T g ∈ D from ⟨g,hg,rfl⟩)
  rw [hcalc] at hbad
  linarith


def signQ {n z : ℕ} (σ : Fin z → Fin n → Bool) (s : Fin z) (i : Fin n) : ℚ :=
  if σ s i then 1 else -1

lemma cast_sign {n z : ℕ} (σ : Fin z → Fin n → Bool) (s : Fin z) (i : Fin n) :
    (signQ σ s i : ℝ) = sign σ s i := by
  unfold signQ sign
  split <;> norm_num

lemma finite_margin {z : ℕ} (f : Fin z → ℝ) (hf : ∀ s, |f s| < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s, |f s|+δ < 1 := by
  classical
  have aux (S : Finset (Fin z)) : ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, |f s|+δ < 1 := by
    induction S using Finset.induction_on with
    | empty =>
      exact ⟨1,by norm_num,by simp⟩
    | @insert i S hi ih =>
      obtain ⟨δ,hδ,hS⟩ := ih
      refine ⟨min δ ((1-|f i|)/2),lt_min hδ (by linarith [hf i]),?_⟩
      intro s hs
      rcases Finset.mem_insert.mp hs with he|hs
      · subst s
        have hb := min_le_right δ ((1-|f i|)/2)
        linarith [hf i]
      · have hb := min_le_left δ ((1-|f i|)/2)
        linarith [hS s hs]
  obtain ⟨δ,hδ,hS⟩ := aux Finset.univ
  exact ⟨δ,hδ,fun s => hS s (Finset.mem_univ s)⟩

set_option maxHeartbeats 1000000 in
lemma rational_correction {n z : ℕ} (σ : Fin z → Fin n → Bool) (hm : Moments σ)
    (hz : 0 < z) (b : Fin n → ℚ) (f : Fin z → ℝ)
    (hf : ∀ s, |f s| < 1)
    (hfc : ∀ i, corr σ f i = (z : ℝ)*(b i : ℝ)) :
    ∃ g : Fin z → ℚ, (∀ s, -1 ≤ g s ∧ g s ≤ 1) ∧
      ∀ i, (∑ s, g s * signQ σ s i) = (z : ℚ)*b i := by
  classical
  obtain ⟨δ,hδ,hmargin⟩ := finite_margin f hf
  let ε : ℝ := δ/(2*((n : ℝ)+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεeq : ((n : ℝ)+1)*ε = δ/2 := by
    dsimp [ε]
    field_simp
  have hrats : ∀ s, ∃ q : ℚ, f s-ε < (q : ℝ) ∧ (q : ℝ) < f s+ε :=
    fun s => exists_rat_btwn (by linarith)
  choose q hq using hrats
  let qr : Fin z → ℝ := fun s => (q s : ℝ)
  have hqabs s : |qr s-f s| < ε := by
    apply abs_lt.mpr
    dsimp [qr]
    constructor <;> linarith [(hq s).1,(hq s).2]
  have hzr : (0 : ℝ) < z := by exact_mod_cast hz
  have hzne : (z : ℝ) ≠ 0 := ne_of_gt hzr
  let e : Fin n → ℝ := fun i => (b i : ℝ)-corr σ qr i/(z : ℝ)
  have heq i : e i = (∑ s, (f s-qr s)*sign σ s i)/(z : ℝ) := by
    have hs : (∑ s, (f s-qr s)*sign σ s i) =
        (z : ℝ)*(b i : ℝ)-corr σ qr i := by
      simp only [sub_mul,Finset.sum_sub_distrib]
      rw [← corr_apply σ f i,← corr_apply σ qr i,hfc i]
    rw [hs]
    dsimp [e]
    field_simp
  have heBound i : |e i| ≤ ε := by
    rw [heq,abs_div,abs_of_pos hzr]
    apply (div_le_iff₀ hzr).2
    calc
      |∑ s, (f s-qr s)*sign σ s i| ≤
          ∑ s, |(f s-qr s)*sign σ s i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s : Fin z, ε := by
        apply Finset.sum_le_sum
        intro s _
        rw [abs_mul,sign_abs,mul_one,abs_sub_comm]
        exact le_of_lt (hqabs s)
      _ = ε*(z : ℝ) := by simp [mul_comm]
  let eQ : Fin n → ℚ := fun i =>
    b i-(∑ s, q s*signQ σ s i)/(z : ℚ)
  have heCast i : (eQ i : ℝ) = e i := by
    simp [eQ,e,corr_apply,qr,cast_sign]
  let g : Fin z → ℚ := fun s => q s+∑ i, eQ i*signQ σ s i
  have hgCast s : (g s : ℝ) = qr s+linearForm σ e s := by
    simp [g,qr,linearForm,heCast,cast_sign]
  have hlinBound s : |linearForm σ e s| ≤ (n : ℝ)*ε := by
    unfold linearForm
    calc
      |∑ i, e i*sign σ s i| ≤ ∑ i, |e i*sign σ s i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ε := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul,sign_abs,mul_one]
        exact heBound i
      _ = (n : ℝ)*ε := by simp
  have hgBound s : |(g s : ℝ)| < 1 := by
    have hqr : |qr s| ≤ |f s|+ε := by
      calc
        |qr s| = |qr s-f s+f s| := by ring_nf
        _ ≤ |qr s-f s|+|f s| := abs_add_le _ _
        _ ≤ |f s|+ε := by linarith [hqabs s]
    rw [hgCast]
    have ht := abs_add_le (qr s) (linearForm σ e s)
    nlinarith [hlinBound s,hmargin s,hεeq]
  have hfun : (fun s => (g s : ℝ)) = qr+linearForm σ e := by
    ext s
    exact hgCast s
  have hcorr : corr σ (fun s => (g s : ℝ)) =
      (z : ℝ) • (fun i => (b i : ℝ)) := by
    rw [hfun,map_add,corr_linearForm σ hm]
    ext i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    dsimp [e]
    field_simp <;> ring
  refine ⟨g,?_,?_⟩
  · intro s
    have hb : (-1 : ℝ) ≤ (g s : ℝ) ∧ (g s : ℝ) ≤ 1 :=
      abs_le.mp (le_of_lt (hgBound s))
    exact_mod_cast hb
  · intro i
    have hc : (∑ s, (g s : ℝ)*(signQ σ s i : ℝ)) =
        (z : ℝ)*(b i : ℝ) := by
      simp only [cast_sign]
      exact congr_fun hcorr i
    exact_mod_cast hc


lemma solve : ∀ (n z : Nat), 0 < z → ∀ σ : Fin z → Fin n → Bool,
  let sign := fun (s : Fin z) (i : Fin n) => if σ s i then (1 : ℚ) else -1
  (∀ I : Finset (Fin n), I.Nonempty → I.card ≤ 4 →
    (∑ s : Fin z, ∏ i ∈ I, sign s i) = 0) →
  ∀ a : Fin n → ℚ,
    let normSq := ∑ i : Fin n, (a i)^2
    ∃ f : Fin z → ℚ, (∀ s, -1 ≤ f s ∧ f s ≤ 1) ∧
      ∀ i, (1+3*normSq)*(∑ s : Fin z, f s * sign s i) = 2*(z : ℚ)*a i :=
by
  classical
  intro n z hz σ
  dsimp only
  intro hmQ a
  have hm : Moments σ := by
    intro I hI hcard
    have hq := hmQ I hI hcard
    change (∑ s : Fin z, ∏ i ∈ I, signQ σ s i) = 0 at hq
    have hc := congrArg (fun x : ℚ => (x : ℝ)) hq
    simpa only [Rat.cast_sum,Rat.cast_prod,cast_sign,Rat.cast_zero] using hc
  let ar : Fin n → ℝ := fun i => (a i : ℝ)
  let U : ℚ := ∑ i, a i^2
  let B : ℚ := 1+3*U
  let b : Fin n → ℚ := fun i => 2*a i/B
  obtain ⟨f,hfcube,hfeq⟩ := real_decoder_image σ hm hz ar
  have hf : ∀ s, |f s| < 1 := by
    intro s
    exact abs_lt.mpr ((cube_mem f).1 hfcube s)
  have hfc : ∀ i, corr σ f i = (z : ℝ)*(b i : ℝ) := by
    intro i
    have hi := congr_fun hfeq i
    change corr σ f i = (2*(z : ℝ)/(1+3*∑ j, ar j^2))*ar i at hi
    rw [hi]
    dsimp [b,B,U,ar]
    push_cast
    ring
  obtain ⟨g,hg,hcorr⟩ := rational_correction σ hm hz b f hf hfc
  refine ⟨g,hg,?_⟩
  intro i
  change B*(∑ s, g s*signQ σ s i) = 2*(z : ℚ)*a i
  rw [hcorr i]
  have hU : 0 ≤ U := Finset.sum_nonneg (fun i _ => sq_nonneg (a i))
  have hB : B ≠ 0 := ne_of_gt (show 0 < B by dsimp [B]; positivity)
  dsimp [b]
  field_simp
  <;> ring

end PEqualNP.Outside.L_lib_1043

theorem PEqualNP.Outside.L_lib_1043 : ∀ (n z : Nat), 0 < z → ∀ σ : Fin z → Fin n → Bool,
  let sign := fun (s : Fin z) (i : Fin n) => if σ s i then (1 : ℚ) else -1
  (∀ I : Finset (Fin n), I.Nonempty → I.card ≤ 4 →
    (∑ s : Fin z, ∏ i ∈ I, sign s i) = 0) →
  ∀ a : Fin n → ℚ,
    let normSq := ∑ i : Fin n, (a i)^2
    ∃ f : Fin z → ℚ, (∀ s, -1 ≤ f s ∧ f s ≤ 1) ∧
      ∀ i, (1+3*normSq)*(∑ s : Fin z, f s * sign s i) = 2*(z : ℚ)*a i :=
  PEqualNP.Outside.L_lib_1043.solve
