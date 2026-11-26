# 余零因子图的独立支配多项式零点

[研究稿全文（PDF）](paper/paper.pdf) · [LaTeX 源码](paper/paper.tex) · [English](README.md)

固定两个素数 $p<q$，令正整数 $m$ 增大。对剩余类环 `ℤ/(pᵐq)` 的余零因子图，按顶点数统计各个独立支配集，得到一列整系数多项式。这个项目回答 Rather 提出的问题：这些多项式的非零根可以趋向哪里？[2024 年原始枚举](https://www.dmlett.com/archive/v13/DML24_v13_pp36-43.pdf) · [2026 年原问题](https://doi.org/10.1134/S0037446626060194)

- 若 `(p,q) = (2,3)`，每一阶唯一的非零根都是 `−m`，因此没有有限极限点。
- 对其余素数对，有限根集按 Hausdorff 距离趋于单位圆与一组圆外孤立点的并。每个圆外点都是超越数，这些点会从圆外逼近单位圆上的每一点。
- Lean 从实际剩余类和独立支配集定义出发。几何结论的定理签名显式传入 Fuchs 扇区定理；圆外点的超越性额外传入 Mahler 取值定理。例外情形无需这两项输入。

**从哪里开始读。** [主定理](Lean/CozeroCertificates.lean)给出图上的最终陈述。[图的定义](Lean/GraphDefinition.lean)展示独立支配集如何参与多项式求和。[详细核验说明](verification_zh.html)逐步对应 Lean 与书面证明，下载后可用浏览器打开。局部精确重数、计重根的等分布、最大模的完整取等判据仍由书面证明给出。

**如何复现。** 使用 Lean 4.19.0 和 mathlib v4.19.0，在根目录运行英文说明中的命令。Python 脚本只需标准库，独立重建了 15 个有限图，并用有理数严格夹出 `(2,5)` 的最外极限点。[复现命令](README.md#reproduce) · [验证日志](verification.log)

OpenAI Codex 参与了选题、证明推导、检索、程序与形式化验证、撰写。代码与配套文档采用 [MIT 许可证](LICENSE)，`paper/` 下的论文全文和 LaTeX 源码采用 [CC BY 4.0](paper/LICENSE.md)。
