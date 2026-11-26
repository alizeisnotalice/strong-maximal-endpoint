# 非中心强极大算子最优端点常数的高维上下界

在 $\mathbb R^n$ 上取 Lebesgue 测度。$M_nf(x)$ 是 $\lvert f\rvert$ 在所有包含 $x$ 的有界、正体积轴平行矩形上的平均值的上确界，矩形的中心可与 $x$ 不同。令 $\Phi_n(t)=t(1+\log^+t)^{n-1}$，$\Phi_n(0)=0$。端点常数 $C_n$ 是对所有 $\lambda>0$ 和端点积分有限的可测输入满足下式的最小系数。

$$
\lvert\{x:M_nf(x)>\lambda\}\rvert
\le C_n\int_{\mathbb R^n}\Phi_n(\lvert f(x)\rvert/\lambda)\,dx .
$$

令 $\mu$ 为 $\mu=1+e^{-\mu}$ 的唯一正根。令 $\bar\Phi$ 为标准正态上尾，取正根 $z_n$ 满足 $\bar\Phi(z_n)=\sqrt{\mu/n}\,z_n$，并令 $d_n=\sqrt{\mu n}\,z_n$。

| $\log C_n$ 的尺度 | 一般输入的结果 | 来源 |
|---|---|---|
| $n$ | $\log C_n/n\to\mu$。 | v1 稿的两侧估计给出主项。 |
| $\sqrt{n\log n}$ | $(\mu n-\log C_n)/\sqrt{n\log n}\to\sqrt\mu$，故第二项为 $-\sqrt\mu\,\sqrt{n\log n}$。 | [R708 显式提取该极限](https://github.com/alizeisnotalice/Math-Research/blob/615aafe8e60af429430ff460e35999ab56a98716/strong-maximal-endpoint/rounds/r708/second_constant.md)。v1 稿给出了隐式中心化 $d_n$ 及 $z_n\sim\sqrt{\log n}$。 |
| $\log n$ | 保留完整的 $d_n$，令 $R_n=(\log C_n-\mu n+d_n)/\log n$。有 $\frac{9-\mu}{24}\le \liminf_{n\to\infty}R_n\le \limsup_{n\to\infty}R_n\le \frac{3+\mu}{12}$。 | v1 主定理给出上下界。一般矩形算子的这一层精确系数仍待确定。 |

## 从这里读／如何引用

引用稿件时使用固定版本的 BibTeX。[v1.0.0 发布页（R148）](https://github.com/alizeisnotalice/strong-maximal-endpoint/releases/tag/v1.0.0) · [中文 PDF](https://github.com/alizeisnotalice/strong-maximal-endpoint/blob/v1.0.0/paper/strong-maximal-zh.pdf) · [English PDF](https://github.com/alizeisnotalice/strong-maximal-endpoint/blob/v1.0.0/paper/strong-maximal-en.pdf) · [BibTeX](https://github.com/alizeisnotalice/strong-maximal-endpoint/blob/v1.0.0/paper/citation.bib)

引用第二项的显式系数时，可同时指向 R708 的固定记录。[R708](https://github.com/alizeisnotalice/Math-Research/blob/615aafe8e60af429430ff460e35999ab56a98716/strong-maximal-endpoint/rounds/r708/second_constant.md)

## 作者

1. 郑之浩，北京师范大学物理与天文学院 2026 级本科生
2. 唐浩天，北京师范大学数学科学学院 2024 级本科生
3. 彭奕博，北京师范大学数学科学学院 2025 级本科生

## 复现与技术材料

R148 的平衡块中位数阶梯是有限算例，复算检查八组精确分数。Lean 归档验证有理数上的秩变量分布函数与分位数公式。[复现命令与输出](verification/README.md) · [技术补充材料](paper/technical-supplement.html) · [LaTeX 源码](paper/source/)

[原研究索引](https://github.com/alizeisnotalice/Math-Research/blob/615aafe8e60af429430ff460e35999ab56a98716/strong-maximal-endpoint/README.md)汇总后续记录。
