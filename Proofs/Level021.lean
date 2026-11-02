import Leankoban.Soundness
import Leankoban.Levels.Data

/-!
# 面 21 の可解性証明

箱 2 個。証明書の解は押し 16 回・手数 43（押し数最小の解）。

この証明が依存するのは、ルール仕様 `Leankoban.Spec`、実行系 `Leankoban.Engine`、
健全性定理 `Leankoban.Soundness.certify`、そしてカーネルによる計算だけで、公理は一切使わない。
（`lake exe genproofs` が自動生成。手で編集しない。）
-/

namespace Leankoban.Proofs.Level021

open Leankoban

/-- ゲームが読み込む盤面 `Levels.level021` を、ここに絵として展開したもの。 -/
theorem board_eq : Levels.level021 = [
    "#########",
    "#.   #  #",
    "#    #  #",
    "# #   @ #",
    "# #  $$##",
    "#  ## . #",
    "#  ##   #",
    "#########"] := rfl

/-- 解の手順（LURD 記法。小文字は歩く手、大文字は箱を押す手）。 -/
def solution : String :=
    "DLddrUUUllldRurrruulDrdLLLdlUUruLLdrddrRurD"

/-- **面 21 はクリア可能である。** -/
theorem solvable :
    WellFormed (Level.ofRows Levels.level021) ∧ Solvable (Level.ofRows Levels.level021) :=
  Soundness.certify Levels.level021 solution (by decide +kernel)

end Leankoban.Proofs.Level021
