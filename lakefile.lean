import Lake
open Lake DSL

/-!
# Leankoban

Lean 4 だけで書かれた倉庫番（箱押しパズル）と、その全面の可解性証明。
外部依存はなし（Lean core と、ツールチェーンに同梱の `Std` だけを使う）。
-/

package leankoban where
  leanOptions := #[⟨`autoImplicit, false⟩]

/-- ルール仕様・実行系・健全性証明・盤面データ・ゲーム本体。 -/
@[default_target]
lean_lib Leankoban

/-- 盤面生成器とソルバー（信頼しない側のツール群）。 -/
lean_lib Tools

/-- 実行系の単体テスト（`#guard`）。 -/
@[default_target]
lean_lib Tests

/-- 100 面の可解性証明（`lake exe genproofs` が生成）と公理監査 `Proofs.Audit`。 -/
@[default_target]
lean_lib Proofs where
  globs := #[.andSubmodules `Proofs]

/-- 端末で遊ぶゲーム本体。 -/
@[default_target]
lean_exe leankoban where
  root := `Main

/-- 100 面を生成して `Leankoban/Levels/Data.lean` に書き出す。 -/
lean_exe genlevels where
  root := `Tools.GenLevels

/-- 各面を解き直し、`Proofs/LevelNNN.lean` と `Proofs.lean` を書き出す。 -/
lean_exe genproofs where
  root := `Tools.GenProofs
