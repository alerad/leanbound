/-
Minimal debug file for atanh coefficients issue.
-/
import LeanCert.Core.IntervalRat.Taylor

-- Test 1: Direct map with explicit type
#eval
  let result := (List.range 11).map (fun i =>
    if i % 2 = 1 then (1 : ℚ) / (i : ℚ) else (0 : ℚ))
  dbg_trace "Direct map: {result}"
  pure ()

-- Test 2: Check what List.map returns for our lambda
#eval
  let f : ℕ → ℚ := fun i => if i % 2 = 1 then 1 / (i : ℚ) else (0 : ℚ)
  let coeffs := (List.range 11).map f
  dbg_trace "With explicit f: {coeffs}"
  pure ()

-- Test 3: More explicit version
#eval
  let coeffs : List ℚ := [0, 1, 0, 1/3, 0, 1/5, 0, 1/7, 0, 1/9, 0]
  dbg_trace "Manual coeffs: {coeffs}"
  pure ()

-- Test 4: Debug the condition
#eval do
  for i in List.range 11 do
    let cond := i % 2 == 1  -- Use == for Bool instead of = for Prop
    let val : ℚ := if cond then 1 / (i : ℚ) else 0
    IO.println s!"i={i}, i % 2 = {i % 2}, cond={cond}, val={val}"
