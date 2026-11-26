# 非中心强极大算子最优端点常数的高维上下界

High-dimensional bounds for the optimal endpoint constant of the uncentered strong maximal operator.

在 Lebesgue 测度下取包含给定点的轴平行矩形，并以 $\Phi_n(t)=t(1+\log^+t)^{n-1}$ 归一化。设 $C_n$ 为该端点分布不等式的最小系数。稿件给出 $C_n$ 的上下界。令 $\mu=1+e^{-\mu}$，令 $\bar\Phi(z_n)=\sqrt{\mu/n}\,z_n$，并记 $d_n=\sqrt{\mu n}\,z_n$。$\log C_n-n\mu+d_n$ 除以 $\log n$ 的下、上极限分别受 $(9-\mu)/24$ 与 $(3+\mu)/12$ 约束。一般输入在这个精度下的精确系数仍待确定。

[中文 PDF](paper/strong-maximal-zh.pdf) · [English PDF](paper/strong-maximal-en.pdf) · [LaTeX 源码](paper/source/) · [技术补充材料](paper/technical-supplement.html) · [BibTeX](paper/citation.bib)

## 作者

1. 郑之浩，北京师范大学物理与天文学院 2026 级本科生
2. 唐浩天，北京师范大学数学科学学院 2024 级本科生
3. 彭奕博，北京师范大学数学科学学院 2025 级本科生

## 复现与版本

[复现说明与结果](verification/README.md)给出编译命令、阶梯算例和 Lean 公理报告。Lean 验证有理数上的秩变量分布函数与分位数公式。

[v1.0.0 发布页](https://github.com/alizeisnotalice/strong-maximal-endpoint/releases/tag/v1.0.0)收录截至第 148 轮的稿件。后续关于 $\sqrt{n\log n}$ 尺度精确系数的结论见[第 708 轮记录](https://github.com/alizeisnotalice/Math-Research/blob/615aafe8e60af429430ff460e35999ab56a98716/strong-maximal-endpoint/rounds/r708/second_constant.md)，更细项的研究进展见[原研究索引](https://github.com/alizeisnotalice/Math-Research/blob/615aafe8e60af429430ff460e35999ab56a98716/strong-maximal-endpoint/README.md)。
