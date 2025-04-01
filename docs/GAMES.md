
**Step-by-Step Explanation and Tactic Explanation:**

1. **Initial Goal:**
   ```lean4
   2 + 2 = 4
   ```
   We need to prove that the sum of 2 and 2 equals 4.

2. **nth_rewrite 2 [two_eq_succ_one]:**
   - **Tactic Explanation:** `nth_rewrite` allows replacing a specific occurrence of a pattern in the current goal. Here, we're replacing the **second occurrence** of `2` with its definition as the successor of `1` (`succ(1)`), using the lemma `two_eq_succ_one` which states `2 = succ(1)`.
   - **Resulting Goal:**
     ```lean4
     2 + succ(1) = 4
     ```

3. **rewrite [add_succ]:**
   - **Tactic Explanation:** The lemma `add_succ` defines how to add a successor: `a + succ(b) = succ(a + b)`. Applying this rewrites `2 + succ(1)` to `succ(2 + 1)`.
   - **Resulting Goal:**
     ```lean4
     succ(2 + 1) = 4
     ```

4. **rewrite [one_eq_succ_zero]:**
   - **Tactic Explanation:** The lemma `one_eq_succ_zero` states `1 = succ(0)`. Replacing `1` with `succ(0)` in the expression `2 + 1`.
   - **Resulting Goal:**
     ```lean4
     succ(2 + succ(0)) = 4
     ```

5. **rewrite [add_succ, add_zero]:**
   - **Tactic Explanation:**
     - First, `add_succ` is applied to `2 + succ(0)`, resulting in `succ(2 + 0)`.
     - Then, `add_zero` simplifies `2 + 0` to `2`.
   - **Resulting Goal:**
     ```lean4
     succ(succ(2)) = 4
     ```

6. **rewrite [← three_eq_succ_two]:**
   - **Tactic Explanation:** The `←` symbol indicates using the lemma `three_eq_succ_two` in reverse. The lemma states `3 = succ(2)`, so reversing it gives `succ(2) = 3`. This replaces `succ(2)` with `3`.
   - **Resulting Goal:**
     ```lean4
     succ(3) = 4
     ```

7. **rewrite [← four_eq_succ_three]:**
   - **Tactic Explanation:** Similarly, using `four_eq_succ_three` in reverse (`4 = succ(3)` becomes `succ(3) = 4`), replacing `succ(3)` with `4`.
   - **Resulting Goal:**
     ```lean4
     4 = 4
     ```

8. **rfl:**
   - **Tactic Explanation:** The `rfl` tactic checks that the left-hand side and right-hand side of the equation are **definitionally equal** (i.e., they are the same by definition). Since `4 = 4` is trivially true, the proof is complete.

**Summary of Tactics Used:**
- **`nth_rewrite`:** Replaces a specific occurrence of a term using a given equality.
- **`rewrite`:** Applies a lemma to rewrite parts of the goal that match the lemma's pattern.
- **`←` (Reverse Rewrite):** Uses an equality in reverse to replace terms.
- **`rfl`:** Proves an equality by reflexivity when both sides are definitionally the same.
