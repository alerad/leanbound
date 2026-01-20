/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean.Data.Json
import LeanCert.Core.Expr
import LeanCert.Engine.IntervalEval
import LeanCert.Engine.IntervalEvalDyadic
import LeanCert.Engine.IntervalEvalAffine
import LeanCert.Engine.Optimization.Global
import LeanCert.Engine.Optimization.Gradient
import LeanCert.Engine.Integrate
import LeanCert.Validity.Bounds
import LeanCert.ML.Distillation

/-!
# LeanBridge: JSON-RPC Bridge for Python Integration

This module implements a stateless, type-safe JSON-RPC bridge over Standard I/O.
The compiled binary acts as a "Math Kernel" or "Oracle" that Python can communicate with.

## Protocol

We use a simplified JSON-RPC 2.0 style over line-delimited JSON.

### Data Types
- **Rational Numbers:** `{"n": 1, "d": 3}` for 1/3 (exact representation)
- **Expressions:** Recursive JSON objects matching `LeanCert.Core.Expr`
- **Intervals:** `{"lo": Rat, "hi": Rat}`

### Request Format
```json
{ "id": 1, "method": "eval_interval", "params": { "expr": {...}, "box": [...] } }
```

### Response Format
```json
{ "id": 1, "result": { "lo": {...}, "hi": {...} }, "error": null }
```

## Supported Methods
- `eval_interval`: Evaluate expression over a box using interval arithmetic
- `eval_interval_dyadic`: High-performance evaluation using Dyadic arithmetic (avoids denominator explosion)
- `eval_interval_affine`: Affine arithmetic evaluation (tracks correlations, tighter bounds)
- `global_min`: Find global minimum using branch-and-bound optimization
- `global_max`: Find global maximum using branch-and-bound optimization
- `check_bound`: Verify a bound certificate
- `integrate`: Compute rigorous bounds on a definite integral
- `forward_interval`: Propagate intervals through a neural network (SequentialNet)
-/

open LeanCert.Core LeanCert.Engine LeanCert.Engine.Optimization

-- LExpr is defined in LeanCert.Meta.ProveContinuous (imported via Certificate)
-- to avoid ambiguity with Lean.Expr

namespace LeanCert.Bridge

open Lean

/-! ## 1. Serialization Helpers -/

/-- Raw rational for JSON IO. Uses Int numerator and Nat denominator. -/
structure RawRat where
  n : Int
  d : Nat
  deriving Repr, Inhabited

instance : FromJson RawRat where
  fromJson? j := do
    let n ← j.getObjValAs? Int "n"
    let d ← j.getObjValAs? Nat "d"
    return { n, d }

instance : ToJson RawRat where
  toJson r := Json.mkObj [("n", toJson r.n), ("d", toJson r.d)]

/-- Convert RawRat to Lean's Rat type -/
def RawRat.toRat (r : RawRat) : ℚ :=
  if r.d = 0 then 0 else r.n / r.d

/-- Convert Rat to RawRat for JSON serialization -/
def toRawRat (q : ℚ) : RawRat :=
  { n := q.num, d := q.den }

/-- Raw interval for JSON IO -/
structure RawInterval where
  lo : RawRat
  hi : RawRat
  deriving Repr, Inhabited

instance : FromJson RawInterval where
  fromJson? j := do
    let lo ← j.getObjValAs? RawRat "lo"
    let hi ← j.getObjValAs? RawRat "hi"
    return { lo, hi }

instance : ToJson RawInterval where
  toJson i := Json.mkObj [("lo", toJson i.lo), ("hi", toJson i.hi)]

/-- Convert RawInterval to IntervalRat, using default for invalid intervals -/
def RawInterval.toInterval (r : RawInterval) : IntervalRat :=
  let lo := r.lo.toRat
  let hi := r.hi.toRat
  if h : lo ≤ hi then { lo := lo, hi := hi, le := h } else IntervalRat.singleton 0

/-- Convert IntervalRat to RawInterval -/
def toRawInterval (i : IntervalRat) : RawInterval :=
  { lo := toRawRat i.lo, hi := toRawRat i.hi }

/-! ### Dyadic Serialization -/

/-- Raw Dyadic for JSON IO. Uses mantissa and exponent. -/
structure RawDyadic where
  mantissa : Int
  exponent : Int
  deriving Repr, Inhabited

instance : FromJson RawDyadic where
  fromJson? j := do
    let mantissa ← j.getObjValAs? Int "mantissa"
    let exponent ← j.getObjValAs? Int "exponent"
    return { mantissa, exponent }

instance : ToJson RawDyadic where
  toJson d := Json.mkObj [("mantissa", toJson d.mantissa), ("exponent", toJson d.exponent)]

/-- Convert RawDyadic to Dyadic -/
def RawDyadic.toDyadic (r : RawDyadic) : Core.Dyadic :=
  { mantissa := r.mantissa, exponent := r.exponent }

/-- Convert Dyadic to RawDyadic -/
def toRawDyadic (d : Core.Dyadic) : RawDyadic :=
  { mantissa := d.mantissa, exponent := d.exponent }

/-- Raw Dyadic interval for JSON IO -/
structure RawDyadicInterval where
  lo : RawDyadic
  hi : RawDyadic
  deriving Repr, Inhabited

instance : FromJson RawDyadicInterval where
  fromJson? j := do
    let lo ← j.getObjValAs? RawDyadic "lo"
    let hi ← j.getObjValAs? RawDyadic "hi"
    return { lo, hi }

instance : ToJson RawDyadicInterval where
  toJson i := Json.mkObj [("lo", toJson i.lo), ("hi", toJson i.hi)]

/-- Convert RawDyadicInterval to IntervalDyadic, using default for invalid intervals -/
def RawDyadicInterval.toInterval (r : RawDyadicInterval) : Core.IntervalDyadic :=
  let lo := r.lo.toDyadic
  let hi := r.hi.toDyadic
  if h : lo.toRat ≤ hi.toRat then { lo := lo, hi := hi, le := h }
  else Core.IntervalDyadic.singleton Core.Dyadic.zero

/-- Convert IntervalDyadic to RawDyadicInterval -/
def toRawDyadicInterval (i : Core.IntervalDyadic) : RawDyadicInterval :=
  { lo := toRawDyadic i.lo, hi := toRawDyadic i.hi }

/-- Dyadic configuration for JSON IO -/
structure RawDyadicConfig where
  precision : Int := -53
  taylorDepth : Nat := 10
  roundAfterOps : Nat := 0
  deriving Repr, Inhabited

instance : FromJson RawDyadicConfig where
  fromJson? j := do
    let precision := (j.getObjValAs? Int "precision").toOption.getD (-53)
    let taylorDepth := (j.getObjValAs? Nat "taylorDepth").toOption.getD 10
    let roundAfterOps := (j.getObjValAs? Nat "roundAfterOps").toOption.getD 0
    return { precision, taylorDepth, roundAfterOps }

instance : ToJson RawDyadicConfig where
  toJson c := Json.mkObj [
    ("precision", toJson c.precision),
    ("taylorDepth", toJson c.taylorDepth),
    ("roundAfterOps", toJson c.roundAfterOps)
  ]

/-- Convert RawDyadicConfig to DyadicConfig -/
def RawDyadicConfig.toDyadicConfig (r : RawDyadicConfig) : DyadicConfig :=
  { precision := r.precision, taylorDepth := r.taylorDepth, roundAfterOps := r.roundAfterOps }

/-! ### Affine Config Serialization -/

/-- Affine configuration for JSON IO -/
structure RawAffineConfig where
  taylorDepth : Nat := 10
  maxNoiseSymbols : Nat := 0
  deriving Repr, Inhabited

instance : FromJson RawAffineConfig where
  fromJson? j := do
    let taylorDepth := (j.getObjValAs? Nat "taylorDepth").toOption.getD 10
    let maxNoiseSymbols := (j.getObjValAs? Nat "maxNoiseSymbols").toOption.getD 0
    return { taylorDepth, maxNoiseSymbols }

instance : ToJson RawAffineConfig where
  toJson c := Json.mkObj [
    ("taylorDepth", toJson c.taylorDepth),
    ("maxNoiseSymbols", toJson c.maxNoiseSymbols)
  ]

/-- Convert RawAffineConfig to AffineConfig -/
def RawAffineConfig.toAffineConfig (r : RawAffineConfig) : AffineConfig :=
  { taylorDepth := r.taylorDepth, maxNoiseSymbols := r.maxNoiseSymbols }

/-! ## 2. Expression Deserialization -/

/-- Recursive FromJson for LExpr AST -/
partial def rawExprFromJson (j : Json) : Except String LExpr := do
  let kind ← j.getObjValAs? String "kind"
  match kind with
  | "const" =>
    let q ← j.getObjValAs? RawRat "val"
    return Expr.const q.toRat
  | "var" =>
    let idx ← j.getObjValAs? Nat "idx"
    return Expr.var idx
  | "neg" =>
    let e ← rawExprFromJson (← j.getObjVal? "e")
    return Expr.neg e
  | "add" =>
    let e1 ← rawExprFromJson (← j.getObjVal? "e1")
    let e2 ← rawExprFromJson (← j.getObjVal? "e2")
    return Expr.add e1 e2
  | "sub" =>
    let e1 ← rawExprFromJson (← j.getObjVal? "e1")
    let e2 ← rawExprFromJson (← j.getObjVal? "e2")
    return Expr.add e1 (Expr.neg e2)  -- Desugar to add + neg
  | "mul" =>
    let e1 ← rawExprFromJson (← j.getObjVal? "e1")
    let e2 ← rawExprFromJson (← j.getObjVal? "e2")
    return Expr.mul e1 e2
  | "div" =>
    let e1 ← rawExprFromJson (← j.getObjVal? "e1")
    let e2 ← rawExprFromJson (← j.getObjVal? "e2")
    return Expr.div e1 e2
  | "sin" =>
    let e ← rawExprFromJson (← j.getObjVal? "e")
    return Expr.sin e
  | "cos" =>
    let e ← rawExprFromJson (← j.getObjVal? "e")
    return Expr.cos e
  | "exp" =>
    let e ← rawExprFromJson (← j.getObjVal? "e")
    return Expr.exp e
  | "log" =>
    let e ← rawExprFromJson (← j.getObjVal? "e")
    return Expr.log e
  | "pow" =>
    -- Integer power: pow(e, n) where n is a natural number
    let base ← rawExprFromJson (← j.getObjVal? "base")
    let exp ← j.getObjValAs? Nat "exp"
    return Expr.pow base exp
  | "sqrt" =>
    -- sqrt(x) = exp(log(x)/2) for positive x
    let e ← rawExprFromJson (← j.getObjVal? "e")
    return Expr.exp (Expr.div (Expr.log e) (Expr.const 2))
  | "inv" =>
    let e ← rawExprFromJson (← j.getObjVal? "e")
    return Expr.inv e
  | "tan" =>
    -- tan(x) = sin(x) / cos(x)
    let e ← rawExprFromJson (← j.getObjVal? "e")
    return Expr.div (Expr.sin e) (Expr.cos e)
  | "atan" =>
    let e ← rawExprFromJson (← j.getObjVal? "e")
    return Expr.atan e
  | "arsinh" =>
    let e ← rawExprFromJson (← j.getObjVal? "e")
    return Expr.arsinh e
  | "atanh" =>
    let e ← rawExprFromJson (← j.getObjVal? "e")
    return Expr.atanh e
  | "sinc" =>
    let e ← rawExprFromJson (← j.getObjVal? "e")
    return Expr.sinc e
  | "erf" =>
    let e ← rawExprFromJson (← j.getObjVal? "e")
    return Expr.erf e
  | "abs" =>
    -- |x| = sqrt(x²) (derived definition from Expr.lean)
    let e ← rawExprFromJson (← j.getObjVal? "e")
    return Expr.abs e
  | "sinh" =>
    -- Native sinh expression with proper interval bounds
    let e ← rawExprFromJson (← j.getObjVal? "e")
    return Expr.sinh e
  | "cosh" =>
    -- Native cosh expression with cosh(x) ≥ 1 bounds
    let e ← rawExprFromJson (← j.getObjVal? "e")
    return Expr.cosh e
  | "tanh" =>
    -- Native tanh expression with tight [-1, 1] bounds (no interval explosion!)
    let e ← rawExprFromJson (← j.getObjVal? "e")
    return Expr.tanh e
  | "min" =>
    -- min(a, b) = (a + b - |a - b|) / 2
    let e1 ← rawExprFromJson (← j.getObjVal? "e1")
    let e2 ← rawExprFromJson (← j.getObjVal? "e2")
    let diff := Expr.add e1 (Expr.neg e2)
    let absDiff := Expr.abs diff
    return Expr.div (Expr.add (Expr.add e1 e2) (Expr.neg absDiff)) (Expr.const 2)
  | "max" =>
    -- max(a, b) = (a + b + |a - b|) / 2
    let e1 ← rawExprFromJson (← j.getObjVal? "e1")
    let e2 ← rawExprFromJson (← j.getObjVal? "e2")
    let diff := Expr.add e1 (Expr.neg e2)
    let absDiff := Expr.abs diff
    return Expr.div (Expr.add (Expr.add e1 e2) absDiff) (Expr.const 2)
  | other => throw s!"Unknown expression kind: {other}"

instance : FromJson LExpr where
  fromJson? := rawExprFromJson

/-! ## 3. Request Structures -/

/-- Request for interval evaluation -/
structure EvalRequest where
  expr : LExpr
  box  : Array RawInterval
  taylorDepth : Nat := 10

instance : FromJson EvalRequest where
  fromJson? j := do
    let expr ← j.getObjValAs? LExpr "expr"
    let boxJson ← j.getObjVal? "box"
    let boxArr ← match boxJson with
      | Json.arr arr => arr.mapM (FromJson.fromJson? (α := RawInterval))
      | _ => throw "box must be an array"
    let taylorDepth := (j.getObjValAs? Nat "taylorDepth").toOption.getD 10
    return { expr, box := boxArr, taylorDepth }

/-- Request for global optimization -/
structure OptimizeRequest where
  expr : LExpr
  box  : Array RawInterval
  maxIters : Nat := 1000
  tolerance : RawRat := { n := 1, d := 1000 }
  useMonotonicity : Bool := true
  taylorDepth : Nat := 10

instance : FromJson OptimizeRequest where
  fromJson? j := do
    let expr ← j.getObjValAs? LExpr "expr"
    let boxJson ← j.getObjVal? "box"
    let boxArr ← match boxJson with
      | Json.arr arr => arr.mapM (FromJson.fromJson? (α := RawInterval))
      | _ => throw "box must be an array"
    let maxIters := (j.getObjValAs? Nat "maxIters").toOption.getD 1000
    let tolerance := (j.getObjValAs? RawRat "tolerance").toOption.getD { n := 1, d := 1000 }
    let useMonotonicity := (j.getObjValAs? Bool "useMonotonicity").toOption.getD true
    let taylorDepth := (j.getObjValAs? Nat "taylorDepth").toOption.getD 10
    return { expr, box := boxArr, maxIters, tolerance, useMonotonicity, taylorDepth }

/-- Request for bound checking -/
structure CheckBoundRequest where
  expr : LExpr
  box  : Array RawInterval
  bound : RawRat
  isUpperBound : Bool  -- true for upper bound, false for lower bound
  taylorDepth : Nat := 10

instance : FromJson CheckBoundRequest where
  fromJson? j := do
    let expr ← j.getObjValAs? LExpr "expr"
    let boxJson ← j.getObjVal? "box"
    let boxArr ← match boxJson with
      | Json.arr arr => arr.mapM (FromJson.fromJson? (α := RawInterval))
      | _ => throw "box must be an array"
    let bound ← j.getObjValAs? RawRat "bound"
    let isUpperBound ← j.getObjValAs? Bool "isUpperBound"
    let taylorDepth := (j.getObjValAs? Nat "taylorDepth").toOption.getD 10
    return { expr, box := boxArr, bound, isUpperBound, taylorDepth }

/-- Request for numerical integration -/
structure IntegrateRequest where
  expr : LExpr
  interval : RawInterval
  partitions : Nat := 10
  taylorDepth : Nat := 10

instance : FromJson IntegrateRequest where
  fromJson? j := do
    let expr ← j.getObjValAs? LExpr "expr"
    let interval ← j.getObjValAs? RawInterval "interval"
    let partitions := (j.getObjValAs? Nat "partitions").toOption.getD 10
    let taylorDepth := (j.getObjValAs? Nat "taylorDepth").toOption.getD 10
    return { expr, interval, partitions, taylorDepth }

/-- Request for root finding -/
structure FindRootsRequest where
  expr : LExpr
  interval : RawInterval
  maxIter : Nat := 1000
  tolerance : RawRat := { n := 1, d := 1000 }
  taylorDepth : Nat := 10

instance : FromJson FindRootsRequest where
  fromJson? j := do
    let expr ← j.getObjValAs? LExpr "expr"
    let interval ← j.getObjValAs? RawInterval "interval"
    let maxIter := (j.getObjValAs? Nat "maxIter").toOption.getD 1000
    let tolerance := (j.getObjValAs? RawRat "tolerance").toOption.getD { n := 1, d := 1000 }
    let taylorDepth := (j.getObjValAs? Nat "taylorDepth").toOption.getD 10
    return { expr, interval, maxIter, tolerance, taylorDepth }

/-- Request for unique root finding via Newton contraction -/
structure FindUniqueRootRequest where
  expr : LExpr
  interval : RawInterval
  taylorDepth : Nat := 10

instance : FromJson FindUniqueRootRequest where
  fromJson? j := do
    let expr ← j.getObjValAs? LExpr "expr"
    let interval ← j.getObjValAs? RawInterval "interval"
    let taylorDepth := (j.getObjValAs? Nat "taylorDepth").toOption.getD 10
    return { expr, interval, taylorDepth }

/-- Request for adaptive verification using optimization -/
structure VerifyAdaptiveRequest where
  expr : LExpr
  box : Array RawInterval
  bound : RawRat
  isUpperBound : Bool
  maxIters : Nat := 1000
  tolerance : RawRat := { n := 1, d := 1000 }
  taylorDepth : Nat := 10

instance : FromJson VerifyAdaptiveRequest where
  fromJson? j := do
    let expr ← j.getObjValAs? LExpr "expr"
    let boxJson ← j.getObjVal? "box"
    let boxArr ← match boxJson with
      | Json.arr arr => arr.mapM (FromJson.fromJson? (α := RawInterval))
      | _ => throw "box must be an array"
    let bound ← j.getObjValAs? RawRat "bound"
    let isUpperBound ← j.getObjValAs? Bool "isUpperBound"
    let maxIters := (j.getObjValAs? Nat "maxIters").toOption.getD 1000
    let tolerance := (j.getObjValAs? RawRat "tolerance").toOption.getD { n := 1, d := 1000 }
    let taylorDepth := (j.getObjValAs? Nat "taylorDepth").toOption.getD 10
    return { expr, box := boxArr, bound, isUpperBound, maxIters, tolerance, taylorDepth }

/-- Request for high-performance Dyadic interval evaluation -/
structure EvalDyadicRequest where
  expr : LExpr
  box  : Array RawInterval
  config : RawDyadicConfig := {}

instance : FromJson EvalDyadicRequest where
  fromJson? j := do
    let expr ← j.getObjValAs? LExpr "expr"
    let boxJson ← j.getObjVal? "box"
    let boxArr ← match boxJson with
      | Json.arr arr => arr.mapM (FromJson.fromJson? (α := RawInterval))
      | _ => throw "box must be an array"
    let config := (j.getObjValAs? RawDyadicConfig "config").toOption.getD {}
    return { expr, box := boxArr, config }

/-- Request for Affine interval evaluation (tracks correlations) -/
structure EvalAffineRequest where
  expr : LExpr
  box  : Array RawInterval
  config : RawAffineConfig := {}

instance : FromJson EvalAffineRequest where
  fromJson? j := do
    let expr ← j.getObjValAs? LExpr "expr"
    let boxJson ← j.getObjVal? "box"
    let boxArr ← match boxJson with
      | Json.arr arr => arr.mapM (FromJson.fromJson? (α := RawInterval))
      | _ => throw "box must be an array"
    let config := (j.getObjValAs? RawAffineConfig "config").toOption.getD {}
    return { expr, box := boxArr, config }

/-- Request for global optimization with Dyadic backend -/
structure OptimizeDyadicRequest where
  expr : LExpr
  box  : Array RawInterval
  maxIters : Nat := 1000
  tolerance : RawRat := { n := 1, d := 1000 }
  useMonotonicity : Bool := true
  taylorDepth : Nat := 10
  precision : Int := -53

instance : FromJson OptimizeDyadicRequest where
  fromJson? j := do
    let expr ← j.getObjValAs? LExpr "expr"
    let boxJson ← j.getObjVal? "box"
    let boxArr ← match boxJson with
      | Json.arr arr => arr.mapM (FromJson.fromJson? (α := RawInterval))
      | _ => throw "box must be an array"
    let maxIters := (j.getObjValAs? Nat "maxIters").toOption.getD 1000
    let tolerance := (j.getObjValAs? RawRat "tolerance").toOption.getD { n := 1, d := 1000 }
    let useMonotonicity := (j.getObjValAs? Bool "useMonotonicity").toOption.getD true
    let taylorDepth := (j.getObjValAs? Nat "taylorDepth").toOption.getD 10
    let precision := (j.getObjValAs? Int "precision").toOption.getD (-53)
    return { expr, box := boxArr, maxIters, tolerance, useMonotonicity, taylorDepth, precision }

/-- Request for global optimization with Affine backend -/
structure OptimizeAffineRequest where
  expr : LExpr
  box  : Array RawInterval
  maxIters : Nat := 1000
  tolerance : RawRat := { n := 1, d := 1000 }
  useMonotonicity : Bool := true
  taylorDepth : Nat := 10
  maxNoiseSymbols : Nat := 0

instance : FromJson OptimizeAffineRequest where
  fromJson? j := do
    let expr ← j.getObjValAs? LExpr "expr"
    let boxJson ← j.getObjVal? "box"
    let boxArr ← match boxJson with
      | Json.arr arr => arr.mapM (FromJson.fromJson? (α := RawInterval))
      | _ => throw "box must be an array"
    let maxIters := (j.getObjValAs? Nat "maxIters").toOption.getD 1000
    let tolerance := (j.getObjValAs? RawRat "tolerance").toOption.getD { n := 1, d := 1000 }
    let useMonotonicity := (j.getObjValAs? Bool "useMonotonicity").toOption.getD true
    let taylorDepth := (j.getObjValAs? Nat "taylorDepth").toOption.getD 10
    let maxNoiseSymbols := (j.getObjValAs? Nat "maxNoiseSymbols").toOption.getD 0
    return { expr, box := boxArr, maxIters, tolerance, useMonotonicity, taylorDepth, maxNoiseSymbols }

/-! ### Neural Network Forward Interval Request -/

/-- A raw layer for JSON deserialization -/
structure RawLayer where
  weights : Array (Array RawRat)
  bias : Array RawRat
  deriving Repr, Inhabited

instance : FromJson RawLayer where
  fromJson? j := do
    let rawWeights ← j.getObjValAs? (Array (Array RawRat)) "weights"
    let rawBias ← j.getObjValAs? (Array RawRat) "bias"
    return { weights := rawWeights, bias := rawBias }

/-- Convert RawLayer to ML.Layer -/
def RawLayer.toLayer (r : RawLayer) : LeanCert.ML.Layer where
  weights := r.weights.toList.map (fun row => row.toList.map RawRat.toRat)
  bias := r.bias.toList.map RawRat.toRat

/-- Request for neural network forward interval propagation -/
structure ForwardIntervalRequest where
  layers : Array RawLayer
  input : Array RawInterval
  precision : Int := -53
  deriving Repr, Inhabited

instance : FromJson ForwardIntervalRequest where
  fromJson? j := do
    let layers ← j.getObjValAs? (Array RawLayer) "layers"
    let input ← j.getObjValAs? (Array RawInterval) "input"
    let precision := (j.getObjValAs? Int "precision").toOption.getD (-53)
    return { layers, input, precision }

/-- Request for derivative interval evaluation (for Lipschitz bounds).
    Computes bounds on all partial derivatives over a box. -/
structure DerivIntervalRequest where
  expr : LExpr
  box : Array RawInterval
  taylorDepth : Nat := 10

instance : FromJson DerivIntervalRequest where
  fromJson? j := do
    let expr ← j.getObjValAs? LExpr "expr"
    let boxJson ← j.getObjVal? "box"
    let boxArr ← match boxJson with
      | Json.arr arr => arr.mapM (FromJson.fromJson? (α := RawInterval))
      | _ => throw "box must be an array"
    let taylorDepth := (j.getObjValAs? Nat "taylorDepth").toOption.getD 10
    return { expr, box := boxArr, taylorDepth }

/-! ## 4. Request Handlers -/

/-- Handle interval evaluation request -/
def handleEvalInterval (req : EvalRequest) : Json :=
  -- Convert raw box to IntervalEnv
  let intervals := req.box.toList.map RawInterval.toInterval
  let env : IntervalEnv := fun i => intervals.getD i (IntervalRat.singleton 0)

  -- Run computation using evaluator with division support
  let cfg : EvalConfig := { taylorDepth := req.taylorDepth }
  let result := evalIntervalCoreWithDiv req.expr env cfg

  -- Serialize result
  Json.mkObj [
    ("lo", toJson (toRawRat result.lo)),
    ("hi", toJson (toRawRat result.hi))
  ]

/-- Handle high-performance Dyadic interval evaluation request.

This evaluator uses Dyadic arithmetic (n * 2^e) instead of rationals,
preventing denominator explosion for deep expressions. It's 10-100x
faster for complex expressions like neural networks or nested Taylor series.

The result is returned both as Dyadic (exact) and as Rational (for
compatibility with the existing API). -/
def handleEvalIntervalDyadic (req : EvalDyadicRequest) : Json :=
  -- Convert raw box to Dyadic interval environment
  let intervals := req.box.toList.map RawInterval.toInterval
  let cfg := req.config.toDyadicConfig

  -- Create Dyadic environment from rational intervals
  let dyadicEnv : IntervalDyadicEnv := fun i =>
    let irat := intervals.getD i (IntervalRat.singleton 0)
    Core.IntervalDyadic.ofIntervalRat irat cfg.precision

  -- Run Dyadic evaluation
  let result := evalIntervalDyadic req.expr dyadicEnv cfg

  -- Convert result to rational for compatibility
  let resultRat := result.toIntervalRat

  -- Return both Dyadic and Rational representations
  Json.mkObj [
    ("lo", toJson (toRawRat resultRat.lo)),
    ("hi", toJson (toRawRat resultRat.hi)),
    ("dyadic", Json.mkObj [
      ("lo", toJson (toRawDyadic result.lo)),
      ("hi", toJson (toRawDyadic result.hi))
    ])
  ]

/-- Handle Affine interval evaluation request.

This evaluator uses Affine Arithmetic to track correlations between variables,
solving the "dependency problem" in interval arithmetic. For example:
- Interval: x - x on [-1, 1] gives [-2, 2]
- Affine: x - x on [-1, 1] gives [0, 0] (exact!)

Affine arithmetic gives 50-90% tighter bounds for expressions with repeated
variables, which is common in neural network verification. -/
def handleEvalIntervalAffine (req : EvalAffineRequest) : Json :=
  -- Convert raw box to Affine environment
  let intervals := req.box.toList.map RawInterval.toInterval
  let cfg := req.config.toAffineConfig

  -- Create Affine environment from rational intervals
  let affineEnv := toAffineEnv intervals

  -- Run Affine evaluation
  let result := evalIntervalAffine req.expr affineEnv cfg

  -- Convert result to interval
  let resultInterval := result.toInterval

  Json.mkObj [
    ("lo", toJson (toRawRat resultInterval.lo)),
    ("hi", toJson (toRawRat resultInterval.hi)),
    ("affine", Json.mkObj [
      ("c0", toJson (toRawRat result.c0)),
      ("radius", toJson (toRawRat result.deviationBound))
    ])
  ]

/-- Handle global minimization request -/
def handleGlobalMin (req : OptimizeRequest) : Json :=
  let box : Box := req.box.toList.map RawInterval.toInterval
  let cfg : GlobalOptConfig := {
    maxIterations := req.maxIters,
    tolerance := req.tolerance.toRat,
    useMonotonicity := req.useMonotonicity,
    taylorDepth := req.taylorDepth
  }

  let result := globalMinimizeCoreDiv req.expr box cfg

  -- Include bestBox for counterexample concretization
  let bestBoxJson := Json.arr (result.bound.bestBox.map (fun i => toJson (toRawInterval i))).toArray

  Json.mkObj [
    ("lo", toJson (toRawRat result.bound.lo)),
    ("hi", toJson (toRawRat result.bound.hi)),
    ("remainingBoxes", toJson result.remainingBoxes.length),
    ("bestBox", bestBoxJson)
  ]

/-- Handle global maximization request -/
def handleGlobalMax (req : OptimizeRequest) : Json :=
  let box : Box := req.box.toList.map RawInterval.toInterval
  let cfg : GlobalOptConfig := {
    maxIterations := req.maxIters,
    tolerance := req.tolerance.toRat,
    useMonotonicity := req.useMonotonicity,
    taylorDepth := req.taylorDepth
  }

  let result := globalMaximizeCoreDiv req.expr box cfg

  -- Include bestBox for counterexample concretization
  let bestBoxJson := Json.arr (result.bound.bestBox.map (fun i => toJson (toRawInterval i))).toArray

  Json.mkObj [
    ("lo", toJson (toRawRat result.bound.lo)),
    ("hi", toJson (toRawRat result.bound.hi)),
    ("remainingBoxes", toJson result.remainingBoxes.length),
    ("bestBox", bestBoxJson)
  ]

/-- Handle global minimization request with Dyadic backend -/
def handleGlobalMinDyadic (req : OptimizeDyadicRequest) : Json :=
  let box : Box := req.box.toList.map RawInterval.toInterval
  let cfg : GlobalOptConfigDyadic := {
    maxIterations := req.maxIters,
    tolerance := req.tolerance.toRat,
    useMonotonicity := req.useMonotonicity,
    taylorDepth := req.taylorDepth,
    precision := req.precision
  }

  let result := globalMinimizeDyadic req.expr box cfg

  let bestBoxJson := Json.arr (result.bound.bestBox.map (fun i => toJson (toRawInterval i))).toArray

  Json.mkObj [
    ("lo", toJson (toRawRat result.bound.lo)),
    ("hi", toJson (toRawRat result.bound.hi)),
    ("remainingBoxes", toJson result.remainingBoxes.length),
    ("bestBox", bestBoxJson)
  ]

/-- Handle global maximization request with Dyadic backend -/
def handleGlobalMaxDyadic (req : OptimizeDyadicRequest) : Json :=
  let box : Box := req.box.toList.map RawInterval.toInterval
  let cfg : GlobalOptConfigDyadic := {
    maxIterations := req.maxIters,
    tolerance := req.tolerance.toRat,
    useMonotonicity := req.useMonotonicity,
    taylorDepth := req.taylorDepth,
    precision := req.precision
  }

  let result := globalMaximizeDyadic req.expr box cfg

  let bestBoxJson := Json.arr (result.bound.bestBox.map (fun i => toJson (toRawInterval i))).toArray

  Json.mkObj [
    ("lo", toJson (toRawRat result.bound.lo)),
    ("hi", toJson (toRawRat result.bound.hi)),
    ("remainingBoxes", toJson result.remainingBoxes.length),
    ("bestBox", bestBoxJson)
  ]

/-- Handle global minimization request with Affine backend -/
def handleGlobalMinAffine (req : OptimizeAffineRequest) : Json :=
  let box : Box := req.box.toList.map RawInterval.toInterval
  let cfg : GlobalOptConfigAffine := {
    maxIterations := req.maxIters,
    tolerance := req.tolerance.toRat,
    useMonotonicity := req.useMonotonicity,
    taylorDepth := req.taylorDepth,
    maxNoiseSymbols := req.maxNoiseSymbols
  }

  let result := globalMinimizeAffine req.expr box cfg

  let bestBoxJson := Json.arr (result.bound.bestBox.map (fun i => toJson (toRawInterval i))).toArray

  Json.mkObj [
    ("lo", toJson (toRawRat result.bound.lo)),
    ("hi", toJson (toRawRat result.bound.hi)),
    ("remainingBoxes", toJson result.remainingBoxes.length),
    ("bestBox", bestBoxJson)
  ]

/-- Handle global maximization request with Affine backend -/
def handleGlobalMaxAffine (req : OptimizeAffineRequest) : Json :=
  let box : Box := req.box.toList.map RawInterval.toInterval
  let cfg : GlobalOptConfigAffine := {
    maxIterations := req.maxIters,
    tolerance := req.tolerance.toRat,
    useMonotonicity := req.useMonotonicity,
    taylorDepth := req.taylorDepth,
    maxNoiseSymbols := req.maxNoiseSymbols
  }

  let result := globalMaximizeAffine req.expr box cfg

  let bestBoxJson := Json.arr (result.bound.bestBox.map (fun i => toJson (toRawInterval i))).toArray

  Json.mkObj [
    ("lo", toJson (toRawRat result.bound.lo)),
    ("hi", toJson (toRawRat result.bound.hi)),
    ("remainingBoxes", toJson result.remainingBoxes.length),
    ("bestBox", bestBoxJson)
  ]

/-- Handle bound checking request -/
def handleCheckBound (req : CheckBoundRequest) : Json :=
  let intervals := req.box.toList.map RawInterval.toInterval
  let env : IntervalEnv := fun i => intervals.getD i (IntervalRat.singleton 0)
  let cfg : EvalConfig := { taylorDepth := req.taylorDepth }
  let result := evalIntervalCoreWithDiv req.expr env cfg
  let bound := req.bound.toRat

  let verified := if req.isUpperBound then
    decide (result.hi ≤ bound)  -- Upper bound: max value ≤ bound
  else
    decide (bound ≤ result.lo)  -- Lower bound: bound ≤ min value

  Json.mkObj [
    ("verified", toJson verified),
    ("computed_lo", toJson (toRawRat result.lo)),
    ("computed_hi", toJson (toRawRat result.hi))
  ]

/-- Computable single-interval integration.
    Bounds the integral using interval arithmetic: width * f_bounds -/
def integrateIntervalCore1 (e : LExpr) (I : IntervalRat) (cfg : EvalConfig := {}) : IntervalRat :=
  let fBound := evalIntervalCoreWithDiv e (fun _ => I) cfg
  IntervalRat.mul (IntervalRat.singleton I.width) fBound

/-- Computable uniform partition integration -/
def integrateIntervalCore (e : LExpr) (I : IntervalRat) (n : Nat) (cfg : EvalConfig := {}) : IntervalRat :=
  if n = 0 then IntervalRat.singleton 0
  else
    let width := (I.hi - I.lo) / n
    let parts := List.range n |>.map fun i =>
      let lo := I.lo + width * i
      let hi := I.lo + width * (i + 1)
      if h : lo ≤ hi then { lo := lo, hi := hi, le := h }
      else IntervalRat.singleton lo
    parts.foldl (fun acc J =>
      let fBound := evalIntervalCoreWithDiv e (fun _ => J) cfg
      let contribution := IntervalRat.mul (IntervalRat.singleton J.width) fBound
      IntervalRat.add acc contribution
    ) (IntervalRat.singleton 0)

/-- Handle integration request -/
def handleIntegrate (req : IntegrateRequest) : Json :=
  let I := req.interval.toInterval
  let n := max 1 req.partitions
  let cfg : EvalConfig := { taylorDepth := req.taylorDepth }
  let result := integrateIntervalCore req.expr I n cfg

  Json.mkObj [
    ("lo", toJson (toRawRat result.lo)),
    ("hi", toJson (toRawRat result.hi))
  ]

/-! ## Root Finding (Computable) -/

/-- Root status for computable root finding -/
inductive RootStatusCore where
  | noRoot     -- Interval excludes zero
  | hasRoot    -- Sign change detected (IVT applies)
  | unknown    -- Cannot determine
  deriving Repr, DecidableEq

instance : ToJson RootStatusCore where
  toJson s := match s with
    | .noRoot => "noRoot"
    | .hasRoot => "hasRoot"
    | .unknown => "unknown"

/-- Check if interval excludes zero (computable) -/
def excludesZeroCore (I : IntervalRat) : Bool :=
  I.hi < 0 || 0 < I.lo

/-- Check if function has opposite signs at endpoints (computable) -/
def signChangeCore (e : LExpr) (I : IntervalRat) (cfg : EvalConfig) : Bool :=
  let flo := evalIntervalCoreWithDiv e (fun _ => IntervalRat.singleton I.lo) cfg
  let fhi := evalIntervalCoreWithDiv e (fun _ => IntervalRat.singleton I.hi) cfg
  (flo.hi < 0 && 0 < fhi.lo) || (fhi.hi < 0 && 0 < flo.lo)

/-- Determine root status (computable) -/
def checkRootStatusCore (e : LExpr) (I : IntervalRat) (cfg : EvalConfig) : RootStatusCore :=
  let fI := evalIntervalCoreWithDiv e (fun _ => I) cfg
  if excludesZeroCore fI then
    RootStatusCore.noRoot
  else if signChangeCore e I cfg then
    RootStatusCore.hasRoot
  else
    RootStatusCore.unknown

/-- Result of computable bisection root finding -/
structure BisectionResultCore where
  intervals : List (IntervalRat × RootStatusCore)
  iterations : Nat

/-- Computable bisection root finding worker -/
def bisectRootGoCore (e : LExpr) (tol : ℚ) (maxIter : Nat)
    (work : List (IntervalRat × RootStatusCore)) (iter : Nat)
    (done : List (IntervalRat × RootStatusCore)) (cfg : EvalConfig) : BisectionResultCore :=
  match iter, work with
  | 0, _ =>
    { intervals := done ++ work
      iterations := maxIter }
  | _, [] =>
    { intervals := done
      iterations := maxIter - iter }
  | n + 1, (J, _) :: rest =>
    let status := checkRootStatusCore e J cfg
    match status with
    | RootStatusCore.noRoot =>
      -- Discard this interval
      bisectRootGoCore e tol maxIter rest n done cfg
    | RootStatusCore.hasRoot =>
      if J.width ≤ tol then
        bisectRootGoCore e tol maxIter rest n ((J, RootStatusCore.hasRoot) :: done) cfg
      else
        let (J₁, J₂) := J.bisect
        bisectRootGoCore e tol maxIter ((J₁, .unknown) :: (J₂, .unknown) :: rest) n done cfg
    | RootStatusCore.unknown =>
      if J.width ≤ tol then
        bisectRootGoCore e tol maxIter rest n ((J, RootStatusCore.unknown) :: done) cfg
      else
        let (J₁, J₂) := J.bisect
        bisectRootGoCore e tol maxIter ((J₁, .unknown) :: (J₂, .unknown) :: rest) n done cfg

/-- Computable bisection root finding -/
def bisectRootCore (e : LExpr) (I : IntervalRat) (maxIter : Nat) (tol : ℚ) (cfg : EvalConfig) : BisectionResultCore :=
  bisectRootGoCore e tol maxIter [(I, RootStatusCore.unknown)] maxIter [] cfg

/-- Handle root finding request -/
def handleFindRoots (req : FindRootsRequest) : Json :=
  let I := req.interval.toInterval
  let cfg : EvalConfig := { taylorDepth := req.taylorDepth }
  let result := bisectRootCore req.expr I req.maxIter req.tolerance.toRat cfg

  let roots := result.intervals.map fun (J, status) =>
    Json.mkObj [
      ("lo", toJson (toRawRat J.lo)),
      ("hi", toJson (toRawRat J.hi)),
      ("status", toJson status)
    ]

  Json.mkObj [
    ("roots", Json.arr roots.toArray),
    ("iterations", toJson result.iterations)
  ]

/-- Handle unique root finding request via Newton contraction.

    Checks if Newton contraction holds, indicating a unique root exists.
    This is a stronger result than bisection (which only proves existence). -/
def handleFindUniqueRoot (req : FindUniqueRootRequest) : Json :=
  let I := req.interval.toInterval
  let cfg : EvalConfig := { taylorDepth := req.taylorDepth }

  -- Check if Newton contraction holds (computable version)
  let contracts := Validity.RootFinding.checkNewtonContractsCore req.expr I cfg

  -- Also get the Newton step result for the refined interval
  let newtonResult := Validity.RootFinding.newtonStepCore req.expr I cfg

  match newtonResult with
  | none =>
    -- Newton step failed (derivative contains 0 or other issue)
    Json.mkObj [
      ("unique", toJson false),
      ("reason", "newton_step_failed"),
      ("interval", Json.mkObj [
        ("lo", toJson (toRawRat I.lo)),
        ("hi", toJson (toRawRat I.hi))
      ])
    ]
  | some N =>
    if contracts then
      -- Contraction! Unique root exists in N (and hence in I)
      Json.mkObj [
        ("unique", toJson true),
        ("reason", "newton_contraction"),
        ("interval", Json.mkObj [
          ("lo", toJson (toRawRat N.lo)),
          ("hi", toJson (toRawRat N.hi))
        ])
      ]
    else
      -- Newton step succeeded but didn't contract
      -- Still may have a root, but uniqueness not proven
      Json.mkObj [
        ("unique", toJson false),
        ("reason", "no_contraction"),
        ("interval", Json.mkObj [
          ("lo", toJson (toRawRat N.lo)),
          ("hi", toJson (toRawRat N.hi))
        ])
      ]

/-- Handle adaptive verification request using optimization -/
def handleVerifyAdaptive (req : VerifyAdaptiveRequest) : Json :=
  let box : Box := req.box.toList.map RawInterval.toInterval
  let cfg : GlobalOptConfig := {
    maxIterations := req.maxIters,
    tolerance := req.tolerance.toRat,
    useMonotonicity := true,
    taylorDepth := req.taylorDepth
  }
  let bound := req.bound.toRat

  -- For upper bound: verify f <= c ⟺ min(c - f) >= 0
  -- For lower bound: verify f >= c ⟺ min(f - c) >= 0
  let testExpr := if req.isUpperBound then
    Expr.add (Expr.const bound) (Expr.neg req.expr)  -- c - f
  else
    Expr.add req.expr (Expr.neg (Expr.const bound))  -- f - c

  let result := globalMinimizeCore testExpr box cfg
  let verified := decide (result.bound.lo ≥ 0)

  Json.mkObj [
    ("verified", toJson verified),
    ("minValue", toJson (toRawRat result.bound.lo)),
    ("remainingBoxes", toJson result.remainingBoxes.length)
  ]

/-- Handle neural network forward interval propagation request.

This handler takes a sequential neural network (list of layers) and an input
interval vector, then propagates the intervals through the network using
verified interval arithmetic.

Each layer performs: y = ReLU(W·x + b) (with ReLU for all but last layer)

Returns: Array of output intervals -/
def handleForwardInterval (req : ForwardIntervalRequest) : Json :=
  -- Convert raw layers to ML.Layer
  let layers : List LeanCert.ML.Layer := req.layers.toList.map RawLayer.toLayer

  -- Convert raw input intervals to IntervalVector (using Dyadic)
  let input : LeanCert.Engine.IntervalVector :=
    req.input.toList.map (fun ri =>
      let irat := ri.toInterval
      Core.IntervalDyadic.ofIntervalRat irat req.precision)

  -- Build SequentialNet and run forward propagation
  let net : LeanCert.ML.Distillation.SequentialNet := { layers := layers }
  let output := LeanCert.ML.Distillation.SequentialNet.forwardInterval net input req.precision

  -- Serialize output intervals
  let outputJson := output.map (fun I =>
    Json.mkObj [
      ("lo", toJson (toRawRat I.lo.toRat)),
      ("hi", toJson (toRawRat I.hi.toRat))
    ])

  Json.mkObj [
    ("output", Json.arr outputJson.toArray),
    ("numLayers", toJson layers.length),
    ("outputDim", toJson output.length)
  ]

/-- Handle derivative interval request.

Computes bounds on all partial derivatives (the gradient) over a box.
This is used for computing Lipschitz constants: L = max_i sup_x |∂f/∂xᵢ(x)|.

Returns: Array of intervals, one per variable, each containing ∂f/∂xᵢ for all x ∈ box.
Also returns the Lipschitz bound L = max(|lo|, |hi|) over all partial derivatives. -/
def handleDerivInterval (req : DerivIntervalRequest) : Json :=
  let box : Box := req.box.toList.map RawInterval.toInterval
  let cfg : EvalConfig := { taylorDepth := req.taylorDepth }

  -- Compute gradient interval using computable AD
  let gradients := Optimization.gradientIntervalCore req.expr box cfg

  -- Compute Lipschitz bound: max of absolute values of all partial derivative bounds
  let lipschitzBound := gradients.foldl (fun acc I =>
    max acc (max (abs I.lo) (abs I.hi))) (0 : ℚ)

  -- Serialize gradient intervals
  let gradientsJson := gradients.map (fun I =>
    Json.mkObj [
      ("lo", toJson (toRawRat I.lo)),
      ("hi", toJson (toRawRat I.hi))
    ])

  Json.mkObj [
    ("gradients", Json.arr gradientsJson.toArray),
    ("lipschitz_bound", toJson (toRawRat lipschitzBound)),
    ("num_vars", toJson gradients.length)
  ]

/-! ## 5. Main Event Loop -/

/-- Process a single JSON-RPC request -/
def processRequest (line : String) : IO Unit := do
  let respond (j : Json) : IO Unit := do
    IO.println j.compress
    (← IO.getStdout).flush

  match Json.parse line with
  | Except.error e =>
    respond (Json.mkObj [("error", s!"JSON parse error: {e}")])
  | Except.ok j =>
    let reqId := j.getObjVal? "id" |>.toOption

    match j.getObjValAs? String "method" with
    | Except.error _ =>
      respond (Json.mkObj [("error", "Missing 'method' field")])
    | Except.ok method =>
      let args := match j.getObjVal? "params" with
        | Except.ok a => a
        | Except.error _ => Json.mkObj []

      let result := match method with
        | "eval_interval" =>
          match fromJson? (α := EvalRequest) args with
          | Except.ok req => Json.mkObj [("result", handleEvalInterval req)]
          | Except.error e => Json.mkObj [("error", s!"Invalid eval_interval params: {e}")]

        | "eval_interval_dyadic" =>
          match fromJson? (α := EvalDyadicRequest) args with
          | Except.ok req => Json.mkObj [("result", handleEvalIntervalDyadic req)]
          | Except.error e => Json.mkObj [("error", s!"Invalid eval_interval_dyadic params: {e}")]

        | "eval_interval_affine" =>
          match fromJson? (α := EvalAffineRequest) args with
          | Except.ok req => Json.mkObj [("result", handleEvalIntervalAffine req)]
          | Except.error e => Json.mkObj [("error", s!"Invalid eval_interval_affine params: {e}")]

        | "global_min" =>
          match fromJson? (α := OptimizeRequest) args with
          | Except.ok req => Json.mkObj [("result", handleGlobalMin req)]
          | Except.error e => Json.mkObj [("error", s!"Invalid global_min params: {e}")]

        | "global_max" =>
          match fromJson? (α := OptimizeRequest) args with
          | Except.ok req => Json.mkObj [("result", handleGlobalMax req)]
          | Except.error e => Json.mkObj [("error", s!"Invalid global_max params: {e}")]

        | "global_min_dyadic" =>
          match fromJson? (α := OptimizeDyadicRequest) args with
          | Except.ok req => Json.mkObj [("result", handleGlobalMinDyadic req)]
          | Except.error e => Json.mkObj [("error", s!"Invalid global_min_dyadic params: {e}")]

        | "global_max_dyadic" =>
          match fromJson? (α := OptimizeDyadicRequest) args with
          | Except.ok req => Json.mkObj [("result", handleGlobalMaxDyadic req)]
          | Except.error e => Json.mkObj [("error", s!"Invalid global_max_dyadic params: {e}")]

        | "global_min_affine" =>
          match fromJson? (α := OptimizeAffineRequest) args with
          | Except.ok req => Json.mkObj [("result", handleGlobalMinAffine req)]
          | Except.error e => Json.mkObj [("error", s!"Invalid global_min_affine params: {e}")]

        | "global_max_affine" =>
          match fromJson? (α := OptimizeAffineRequest) args with
          | Except.ok req => Json.mkObj [("result", handleGlobalMaxAffine req)]
          | Except.error e => Json.mkObj [("error", s!"Invalid global_max_affine params: {e}")]

        | "check_bound" =>
          match fromJson? (α := CheckBoundRequest) args with
          | Except.ok req => Json.mkObj [("result", handleCheckBound req)]
          | Except.error e => Json.mkObj [("error", s!"Invalid check_bound params: {e}")]

        | "integrate" =>
          match fromJson? (α := IntegrateRequest) args with
          | Except.ok req => Json.mkObj [("result", handleIntegrate req)]
          | Except.error e => Json.mkObj [("error", s!"Invalid integrate params: {e}")]

        | "find_roots" =>
          match fromJson? (α := FindRootsRequest) args with
          | Except.ok req => Json.mkObj [("result", handleFindRoots req)]
          | Except.error e => Json.mkObj [("error", s!"Invalid find_roots params: {e}")]

        | "find_unique_root" =>
          match fromJson? (α := FindUniqueRootRequest) args with
          | Except.ok req => Json.mkObj [("result", handleFindUniqueRoot req)]
          | Except.error e => Json.mkObj [("error", s!"Invalid find_unique_root params: {e}")]

        | "verify_adaptive" =>
          match fromJson? (α := VerifyAdaptiveRequest) args with
          | Except.ok req => Json.mkObj [("result", handleVerifyAdaptive req)]
          | Except.error e => Json.mkObj [("error", s!"Invalid verify_adaptive params: {e}")]

        | "forward_interval" =>
          match fromJson? (α := ForwardIntervalRequest) args with
          | Except.ok req => Json.mkObj [("result", handleForwardInterval req)]
          | Except.error e => Json.mkObj [("error", s!"Invalid forward_interval params: {e}")]

        | "deriv_interval" =>
          match fromJson? (α := DerivIntervalRequest) args with
          | Except.ok req => Json.mkObj [("result", handleDerivInterval req)]
          | Except.error e => Json.mkObj [("error", s!"Invalid deriv_interval params: {e}")]

        | "ping" =>
          Json.mkObj [("result", "pong")]

        | other =>
          Json.mkObj [("error", s!"Unknown method: {other}")]

      -- Attach ID if present
      let final := match reqId with
        | some id => result.setObjVal! "id" id
        | none => result

      respond final

end LeanCert.Bridge

/-- Main entry point: read lines from stdin, process each as a request -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  repeat do
    let line ← stdin.getLine
    if line.isEmpty then break
    -- Trim whitespace
    let trimmed := line.trim
    if !trimmed.isEmpty then
      LeanCert.Bridge.processRequest trimmed
