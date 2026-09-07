---
title: "Conditional Fiber Geometry：Lean 形式化总规格"
subtitle: "可直接交给 Codex 的分域实施、依赖闭合与验收方案"
date: "2026年9月7日"
---

# 交付目标与不可越过的边界

这份规格覆盖 `conditional-fiber-geometry` v0.3.0 的全部数学领域，而不是要求一次性完成所有领域。研究对象固定为提交 `77e2203e6d5df42b457823eebe6626f1b1c3ded1`。2026年9月7日重新读取公开 main，仍是这个提交。[R1]

**本文件是实施规格，不是已经通过 Lean 的证明报告。** 本次环境没有安装 Lean/Lake，且容器无法解析外网域名，因此没有编译本包中的参考片段，也没有生成任何“已形式化”证明覆盖率。已核查的是数学分解、官方文档入口、mathlib 固定提交及其工具链。后续一切 `VERIFIED` 状态必须由 Codex 在真实编译环境产生。

最小有意义的第一版应闭合以下链条：真实有限维线性映射的核与受限秩；有限覆盖及 Lipschitz 像；由真实微分条件构造的局部纤维覆盖；条件概率支持的几乎处处结论。它不能退化为“输入维数 8 和秩 6，证明 8−6=2”。后者仅可作为算术测试，不是纤维理论的形式化。

运输、coarea、曲率、Gaussian smoothing、外部 DDPM、CEM 和统计评价均有独立工作包。某个工作包受阻时，完成其余独立部分，输出精确卡点；不得通过把结论改成假设而把主定理标成已完成。

## 状态语义

| 状态 | 含义与允许表述 |
|---|---|
| PLANNED | 只有目标和路线；不计证明 |
| STATEMENT_CHECKED | 声明和类型检查成功，但没有完整证明；不计证明 |
| LEMMA_VERIFIED | 某个辅助引理完成，不能据此宣称整个纸面命题完成 |
| CONDITIONAL_VERIFIED | 在逐项明示、尚未构造的接口假设下完成；必须注明所依赖接口 |
| PAPER_THEOREM_VERIFIED | 与纸面命题同等或更弱的输入假设，全部内部依赖闭合，无未批准公理 |
| INSTANCE_CERTIFIED | 上述定理的一个具体模型实例满足全部输入，证书经检查 |
| NUMERICAL_ONLY | Python、有限差分、浮点、抽样实验；不计 Lean 数学证明 |
| BLOCKED | 记录缺失 API、目标或数学反例；已完成的子结果继续保留 |

`#print axioms` 没有异常公理并不足够。例如 `theorem t (h : DesiredConclusion) : DesiredConclusion := h` 也可以通过内核。必须同时核查**最终声明的假设**、结构体字段和模型实例是否把结论偷放进输入。

## 必须输出的账本

Codex 建立 `PROOF_STATUS.json`、`THEOREM_MAP.md`、`ASSUMPTION_LEDGER.md`、`API_INVENTORY.md`、`FAILURE_LOG.md`、`BUILD_LOGS/`。每个条目写明：论文标签、Lean 名称、准确输入输出、所用范数、可测／可积条件、依赖、现存接口、测试实例、编译命令、SHA、最后一次结果、人工语义审核状态。

**不使用按行数、lemma 数、绿色测试数计算的“全文完成百分比”。** 若 20 个主结果只完成 3 个，应分别列出这 3 个，不称“80%已完成”。

# 固定环境与 Codex 开始方式

## 可重复的版本基线

本次通过 GitHub 读取到 mathlib 提交 `71a80585ee495fc24472fd0eaffc89d94e4fd8d6`，该提交日期为 2026年9月7日，其 `lean-toolchain` 内容是：

```text
leanprover/lean4:v4.34.0-rc2
```

这是一个**发布候选版本**，不是在声称它是稳定发行版。[L1] 选择它是因为版本与已查官方文档相近且已固定；不允许 Codex 后续默默切到浮动 master。若本机对这个工具链存在兼容问题，先记录，另开迁移分支选择与另一 mathlib 固定 SHA 配套的工具链，重新运行全部检查。

所有公共文档网页仍可能移动。`API_INVENTORY.md` 必须用本机固定源文件和 `#check` 结果替代“网页里似乎存在”的判断。

## 环境操作与文件保护

先执行 `git status --short`、`git rev-parse HEAD`，保存到日志。不覆盖已有未提交文件，不重置 main，不删除实验，不强推，不创建发布版。创建局部分支，例如 `formal/cfg-core-v1`。已有 `formal/` 时先读其中工具链和声明；若另有 Lean 工程，不用这份规格里的“公开版缺失”判断去覆盖它。

没有 Lean 时，按官方安装文档安装 elan；安装动作由用户已授权的 Codex 环境执行，不能假装一个 shell 命令已经安装成功。使用 Linux/WSL 或 Windows 原生 Lean 都可以；本任务不需要 GPU。首次 mathlib cache 下载可能占用显著磁盘空间，先检查可用空间；编译优先 1–2 并行任务以限制内存，不无上限重编整个 mathlib。

新建的 Lake 配置应采用同一固定 SHA。以下是配置目标，首次仍须由实际工具链验证语法：

```text
import Lake
open Lake DSL
package cfgFormal where
  leanOptions := #[
    ("autoImplicit", false),
    ("warningAsError", true)
  ]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "71a80585ee495fc24472fd0eaffc89d94e4fd8d6"
@[default_target]
lean_lib CFG
```

先 `lake update` 固定依赖并保存 `lake-manifest.json`，再 `lake exe cache get`，运行最小 `import Mathlib` 文件。**不要承诺这里的配置已经在本次环境编译。** 如当前 Lake 配置 API 变化，只允许修改构建配置；不得改变数学目标以消除错误。

## 目录布局

```text
formal/
  lean-toolchain
  lakefile.lean
  lake-manifest.json
  CFG.lean
  CFG/Basic/
  CFG/LinearAlgebra/
  CFG/Covering/
  CFG/Calculus/
  CFG/Probability/
  CFG/Transport/
  CFG/Geometry/
  CFG/Smoothing/
  CFG/EIT/
  CFG/Statistics/
  CFG/Examples/
  CFG/Audit/
  specs/                  # 未完成目标只放 Markdown
  docs/                   # 账本、依赖、失败记录
  scripts/
  BUILD_LOGS/
```

生产入口 `CFG.lean` 只导入已经完成的模块。未完成目标不以 `sorry`、自造 axiom、`opaque` 占位证明存在于生产库。可以在隔离工作区临时探索，但隔离目录不得被生产入口导入，也不能计入证明统计。

# 先决定表达什么：类型、范数与逻辑契约

## 欧氏空间，而不是误用函数空间默认范数

几何分析使用 `EuclideanSpace ℝ (Fin n)` 或与之有明确等距同构的有限维实内积空间。直接使用 `Fin n → ℝ` 的默认函数范数时，可能得到上确界范数，而不是论文的二范数。谱、伪逆、正交性和 $\sqrt d$ 常数都依赖这一选择。

线性代数的纯维数恒等式先在一般有限维实向量空间做，后面用适配层连接欧氏结构。矩阵只作为坐标表示；通过已证明的等价把 `Matrix` 作用与连续线性映射作用对应起来。

为减少类型转换，用两个自然数 $r,k$ 表示维数分解 $d=r+k$；最终再给 $k=d-r$ 的包装定理。维数公式优先写加法形式

$$\ell+r=s,$$

先证明 $r\le s$，再转自然数减法，避免 Lean 中截断减法掩盖错误。

## F、H、导数不能彼此脱钩

模型保存真实函数 $F$、真实线性 mask $P$，**定义** $H=P\circ F$。导数由 `HasFDerivAt`／`ContDiffOn` 指向真实函数；不能另外输入一个叫 `jacobian` 的矩阵却不证明它是 $H$ 的导数。

`fderiv` 在不可微点也有总定义，因此不能只写关于 `fderiv` 的秩假设而遗漏可微条件。每个使用链式法则的点，都应保留适当的 `DifferentiableAt`、`HasFDerivAt` 或开集上的 $C^1$ 证据。

## 集合覆盖不等于 Hausdorff 维数

首选库中的 `Metric.externalCoveringNumber`，但必须查当前半径类型与扩展自然数值域。[L3] 外部中心符合论文约定；内部中心要另证半径损失。也可用构造性证书

$$\exists C\text{ finite},\quad S\subset\bigcup_{c\in C}\overline B(c,\varepsilon),\quad |C|\le B$$

完成主要证明，再接库定义。禁止用自定义 `coveringNumber := bound`。

先做有限证书再做对数：否则 $\infty$、空集的 0、`toReal` 的总定义会制造隐藏问题。对非空集合，要先证覆盖数 $\ge1$ 且有限，再取 log。对空集，直接单独处理，不对 $\log0$ 作通常实分析解释。

## 假设容器的允许与禁止

允许 `SpectralFrame` 保存真实等距坐标变换、矩阵分解等式、奇异值正性；允许 `TransportCertificate` 保存实际映射、可测性、逆、位移界。它们只能支撑名为 `_of_spectralFrame`、`_of_transportCertificate` 的**接口定理**。要称原文定理已完成，必须从原文假设构造相应证书。

禁止 `RegularFiber` 内直接存目标覆盖上界后再把其字段叫作“纤维覆盖定理”；禁止 `DDPMValid` 内存最终 TV 界而称“DDPM 已证”；禁止定义没有实例的极强模型并仅证明 vacuous theorem。

# 已查官方基础设施及剩余调查

以下入口在本次检索中实际打开；它们不是所有所需定理已存在的保证。

| 领域 | 已查入口 | 使用方式 |
|---|---|---|
| 隐函数 | `Analysis.Calculus.Implicit` | 查 `HasStrictFDerivAt.implicitFunction`、满射导数与核坐标 |
| 覆盖数 | `Topology.MetricSpace.CoveringNumbers` | 区分外部／内部中心、集合单调性、半径反单调性 |
| 正则条件核 | `Probability.Kernel.Disintegration.StandardBorel` | 构造联合分布的 `condKernel` 并使用分解恒等式 |
| ODE | `Analysis.ODE.PicardLindelof` | 局部解存在；公共存在唯一接口另查 `ExistUnique` |
| Gronwall | `Analysis.ODE.Gronwall` | 标量控制、解差与变分方程估计 |
| 维数 | `LinearAlgebra.Dimension.RankNullity` | 固定版本查秩—零度及子空间同构 API |
| 伴随 | `Analysis.InnerProductSpace.Adjoint` | 满行秩右逆、核像正交分解 |
| Schur 补 | `LinearAlgebra.Matrix.SchurComplement` | FEM 分块消元和对称性 |
| 高斯 | `Probability.Distributions.Gaussian.*` | 多元高斯与矩；需本机查正好可用的定理 |
| Hausdorff 测度 | `MeasureTheory.Measure.Hausdorff` | 图面积与流形面积桥接时确认归一化 |

在官方总索引中，没有通过 `Coarea`、`ConstantRank`、`Wasserstein` 这些模块名检索到直接入口。**这仅是本次检索结果，不是“mathlib 不存在这些数学”的证明。** Codex 首先在固定源树全文搜索命名变体、相关声明和依赖；找不到时记录查询和结果，再走下面的局部构造路线。不能编造一个 `coarea_formula` 名字让用户以为调用即可。

# 工作包 M00–M05：闭合最小主线

## M00：基础对象和反例基准

**文件：**`Basic/Model.lean`、`Basic/Fiber.lean`、`Examples/ScopeCounterexamples.lean`。

定义 $S_z=E\cap H^{-1}\{z\}$、$F(S_z)$、线性 mask、非空和紧性条件。证明成员等价、纤维互不相交、连续像紧性、条件支持所需的闭性。

用三个真实函数测试模型：$H(x,y)=x$；$H(x,y)=x^2+y^2$；$F(x,y,z)=(x,y)$ 且 $P(x,y)=x$。最后一个例子有参数纤维维数 2、像纤维维数 1，能阻止错误的像维数等式。

另构造空纤维实例和零维非空实例，不把非空条件放到与概率对象矛盾的地方。验收时输出所选模型的实际函数、导数证明、纤维描述，不只输出数字。

## M01：核包含与受限像秩

**目标：**对真实线性映射 $A:E\to F$、$P:F\to G$，$B=P\circ A$，证明

$$\ker A\subseteq\ker B,$$
$$\dim\operatorname{range}(A|_{\ker B})+\dim\operatorname{range}B
=\dim\operatorname{range}A.$$

**构造路线一：**在子空间 $\operatorname{range}A$ 上限制 $P$。其像与 $\operatorname{range}(P\circ A)$ 线性同构；其核等于 $\operatorname{range}A\cap\ker P$；后者又与 $\operatorname{range}(A|_{\ker B})$ 同一子空间。对这个限制映射使用秩—零度。

**路线二：**直接对 $A$ 与其定义域限制使用秩—零度，再构造两个核之间的线性等价。这里两个核属于不同的子类型，不能仅凭集合看似相同 `rfl`。

**输出：**核包含、受限核同构、加法秩恒等式、$r\le s$、自然数差值版本、对 $DF(v),P$ 的点态包装。

**验收实例：**零映射；满射 $P$；$\ell=0$ 但参数纤维无限；$\ell<d-r$ 的上述三维实例。明确：这一模块还没有证明邻域常秩、像覆盖或流形结构。

## M02：有限网格、覆盖代数与 Lipschitz 像

**文件：**`Covering/FiniteCover.lean`、`BoxGrid.lean`、`LipschitzImage.lean`、`FiniteUnion.lean`、`Entropy.lean`。

先证明长方体的有限网格覆盖。$d\ge1$，每个坐标区间长度为 $L_i$，用长度至多 $2\varepsilon/\sqrt d$ 的小区间分割；中点作中心，所有坐标误差至多 $\varepsilon/\sqrt d$，所以欧氏误差至多 $\varepsilon$。每轴数量取

$$n_i=\max\!\left(1,\left\lceil\frac{L_i\sqrt d}{2\varepsilon}\right\rceil\right).$$

证明 $n_i\le1+L_i\sqrt d/(2\varepsilon)$；$L_i=0$ 单独处理。乘积中心的数量至多 $\prod n_i$。全部涉及有限集、ceil 和平方和，不需要体积测度。

然后证明：集合包含的覆盖单调性；有限并的覆盖数不超过各覆盖数之和；$L$-Lipschitz 映射把 $\eta$-网变成 $L\eta$-网；两个欧氏因子分别用 $\varepsilon/\sqrt2$ 覆盖可覆盖乘积。**若域内中心才可代入图映射，须先选择相交球中的域点并计入半径翻倍。**

若映射只在非凸集合上有导数界，不得直接标为 Lipschitz。这里先用已给的 `LipschitzOnWith`；M03 中会在凸坐标球上从导数界导出它。

最后把有限并的多项式界化成 $C\varepsilon^{-k}$，限定 $0<\varepsilon\le\varepsilon_0$；把小尺度结果延到 $0<\varepsilon\le1$ 时用单调性。$k=0$ 不经过含 $1/k$ 的算式。

## M03：绕开完整常秩定理的核心覆盖路线

**目标与纸面原命题的关系：**这里只证明覆盖上界，不声称真实水平集一定是 $d-r$ 维流形。可以使用比原文更弱的秩下界假设：

> $E$ 紧，$F,H$ 在 $E$ 附近 $C^1$，$S_z=E\cap H^{-1}(z)$ 非空，且每个 $v\in S_z$ 满足 $\operatorname{rank}DH(v)\ge r$。则 $F(S_z)$ 具有覆盖上指数至多 $d-r$；$r=d$ 时该纤维有限。

**纸面证明：**对每个纤维点 $v$，从 $DH(v)$ 选 $r$ 个线性独立输出方向，形成线性投影 $L_v$，使 $D(L_vH)(v)$ 满射。隐函数定理给出 $(L_vH)^{-1}(L_vz)$ 的一个 $d-r$ 维局部图；原纤维局部包含在该图内。缩小图，使复合 $F\circ\psi_v$ 的导数在闭凸坐标球有界。紧性取有限子覆盖，接 M02。$r=d$ 时每个原纤维点局部孤立，紧性使其有限。

这不需要 $DH$ 在整片邻域**恰好**等于 $r$。但它不推出原纤维本身的维数等于 $d-r$，也不自动推出受限像秩 $\ell$ 的改进。这一补充观察是本次为降低形式化依赖给出的推导，不包装成新的通用微分拓扑定理。

**实现顺序：**

1. 先做 $q=r$ 满射导数情形，查官方 `HasStrictFDerivAt.implicitFunction` 的核参数化。[L2]
2. 从 $C^1$ 得到严格可微；核空间通过有限维等距／线性同构连接 $\mathbb R^{d-r}$。
3. 从局部反函数的值等式证明纤维包含，不只证明图上点属于纤维的单向结论。
4. 证明在足够小的闭坐标球上复合导数有界；选球的闭包位于函数定义域。
5. 用紧性选有限图，再接覆盖证书。
6. 做一般 $q\ge r$ 的输出投影选择：可用有限维像空间基、补空间和坐标同构，不强制算法式选行。
7. 用原稿常秩假设导出该更弱输入，形成原稿**覆盖部分**的包装定理。

**一个已查到的实际 API 缺口：**官方 `Analysis.Calculus.Implicit` 页面仍在 TODO 中区分“构造出的隐函数在一个点严格可微”和“该指定函数在整个邻域具有同阶光滑性”。所以不能把一次 `implicitFunction` 调用直接当成已得到 C1 图。[L2] 本覆盖分支有更短的解决办法：隐式逆在基点严格可微，意味着其两点增量在足够小的邻域内受固定线性常数控制，因而局部 Lipschitz；这是严格可微定义的直接后果，取余项常数为 1 即得界。先证这个一般引理，再把固定观测的参数片嵌入该邻域，直接接 M02，避免为了覆盖上界先补全整张图的 C1 理论。若采用原先的 C1 导数界路线，另查 `ContDiffAt.implicitFunction` 或用局部唯一性粘合证明正则性；必须核实其输入与返回函数，不能仅凭名称假定匹配。

**不得偷换：**`exists_fiber_chart` 若仍只是输入假设，状态只能是 `CONDITIONAL_VERIFIED`。只有“微分假设→图”的桥接已证明，才把覆盖命题标为全文对应结果。

**验收：**非线性 $H(x,y)=x+y^2$；$H(x,y)=(x,y^2)$ 在 $z=(0,0)$ 的秩至少 1，真实纤维是单点，而上界允许指数 1。后例专门测试“上界不是等式”。

## M04：完整常秩几何与像秩精化

**目的：**补上 M03 没有证明的环境水平集维数结论，以及 $\ell=s-r$ 的像覆盖。

对一般 $C^1$ 常秩映射，可用“选取独立输出 + 补充定义域坐标”构造局部可逆映射 $x\mapsto(H_1(x),\ldots,H_r(x),x_{r+1},\ldots,x_d)$。在新坐标里证明剩余输出对自由坐标导数为零；在连通凸小片上由导数为零推出常数。这给出真正的常秩标准形。

注意：需先有邻域上的精确常秩，而非一点秩；需保证所选非零 minor 在缩小邻域内保持非零；所有“导数为零所以常数”只能用在连接域。把这个局部构造用于 $H$，得到水平集图与切空间 $\ker DH$；再在图域上用于 $F\circ\psi$，得到 $\ell$ 维像参数化。通过 M02 与有限子覆盖完成像覆盖。

第一版不必引入一般流形类别。欧氏局部图已经足以证明覆盖结论。只有要宣称“embedded manifold”时，才进一步接 `ChartedSpace`、`IsManifold` 等库接口，并保留拓扑与微分的桥接证明。

$\ell=0$ 要证明每个局部图上的 $F$ 局部常值、有限子覆盖给有限像；不错误地推出参数纤维有限。常秩映射也不自动是全局嵌入；不能把自交像当作单张嵌入流形。

## M05：条件分布、mask 与几乎处处支持

**分层：**先证明“给定一个满足真实 disintegration 恒等式的核”的支持结论，再用 mathlib 的条件核构造将接口消除。[L4]

单一 mask 时，对 $\mu$ 定义联合分布 $\pi=(v\mapsto(H(v),v))_\#\mu$。取 $\kappa_z$ 为对第一坐标的条件核。对可测图集合 $A=\{(z,v):H(v)=z\}$，有 $\pi(A^c)=0$。用核积分公式与非负函数积分为零推出

$$\kappa_z(H^{-1}(z))=1\quad\text{对 }H_\#\mu\text{ 几乎处处 }z.$$

再处理 $\mu(E)=1$，得到 $\kappa_z(S_z)=1$。用 $F$ 连续、$S_z$ 紧得到 $F(S_z)$ 闭，推出 pushforward 的拓扑支持包含。不能从“每个固定 $z$ 的某条零测集结论”直接互换不受控的全称量词与几乎处处量词。

可数 mask：最先做有限 $M$ 和同维观测空间；随后做依赖和类型 $\Sigma m,\mathbb R^{q_m}$，或构造等价的带标签标准 Borel 空间。必须证明该空间的可测结构与 countable family 条件，不能把不同观测长度混入未定义的共同空间。

mask 与参数可以相关。直接使用 $(V,M)$ 联合法则，不偷偷加入独立假设。后续密度运输若固定 mask，必须使用 $V\mid M=m$ 的密度，而非无条件密度。

**验收：**连续先验与投影；两个 mask 与参数相关的离散例子；零概率观测点上的任意条件版本反例。要求输出 `ae` 范围在正确条件法则下，而非无关的 Lebesgue-a.e.。

# 工作包 M06–M10：谱、非线性与水平运输

## M06：线性全谱管与白化

**目标：**对 $J:\mathbb R^d\to\mathbb R^q$ 秩 $r$、非零奇异值 $\sigma_i$，证明非空集合

$$\mathcal T=\{x:\|x\|\le R,\ \|Jx-z\|\le\delta\}$$

具有

$$N_\varepsilon(\mathcal T)\le
\left(1+\frac{C_dR}{\varepsilon}\right)^{d-r}
\prod_{i=1}^r\left(1+\frac{C_d\delta}{\sigma_i\varepsilon}\right).$$

**先验输入：**$R,\delta\ge0$、$\varepsilon>0$、真奇异值正性、真实欧氏内积。秩 0 与 $d=0$ 另做，避免访问空谱最后一项。

第一步做显式对角映射 $J(a,b)=\Sigma a$。选一个管内锚点 $x_0$，两次残差三角不等式给 $\|J(x-x_0)\|\le2\delta$。每个正常坐标落在长度 $4\delta/\sigma_i$ 的区间，核坐标落在长度 $2R$ 的区间。M02 的网格给出充分共同常数 $C_d=2\sqrt d$，或先用更宽松但好形式化的 $C_d=2d$（$d\ge1$）。后者符合原文“仅依赖于维数”的目标，但必须公开常数变化。

第二步用左右等距坐标变换把一般 J 化为对角形式。`SpectralFrame` 必须保存“分解等式”和“等距性”，不是只有数值数组。第三步从 Gram 算子的谱定理构造该 frame，消除额外输入假设。若库中已有完整 SVD，复用其存在定理与范数接口；未找到时优先谱定理路线。

**白化：**先给定可逆 $W$，证明 $\|W(Jx-z)\|\le\delta$ 是映射 $WJ$ 的管。再从 SPD 的 $\Gamma$ 构造 $W=\Gamma^{-1/2}$ 并证明 $W^*W=\Gamma^{-1}$。正定性、对称性与固定协方差是必须的；$\Gamma$ 随 x 变化时不能仍把 W 当常矩阵。

**验收：**对角已知谱、正交旋转后同一覆盖证书、$\delta=0$、$r=d$、空管、秩 0；人为调换谱顺序不改变全谱乘积；最弱谱替代确实不小于全谱表达式。Python 接口只接受“认证足够大的常数”或明确改名为“表达式”，不允许任意小正数都叫 bound。

## M07：带常数的隐式图和非线性谱管

**文件：**`Calculus/QuantitativeGraph.lean`、`Covering/NonlinearTube.lean`。

使用 $d=r+k$，$G(a,b)$ 在半径 $2R$ 的闭球附近 $C^2$；$G(0)=0$、$D_aG(0)=\Sigma$、$D_bG(0)=0$、$DG$ 的 Lipschitz 常数为 L、$LR\le s/16$，$s=\min_i\sigma_i>0$。

先独立证明以下算术引理，全部约束作为显式输入：$(R/8)^2+R^2<(17R/16)^2$；收缩因子 $17/256<1$；$R/32+(17/256)(R/8)<R/8$；$(17LR/16)/(s-17LR/16)\le17/239$。$R=0$ 的退化输入应提前排除或另做，不在 strict ball 里藏矛盾。

固定 $\|b\|\le R$，把闭 a 球构造成完备子类型，定义

$$T_b(a)=a-\Sigma^{-1}G(a,b).$$

证明 T 确实映回该子类型，且是压缩映射。用 Banach 不动点定理构造 g，随后证明 $G(g(b),b)=0$、唯一性、连续依赖、内点上的 $C^1$ 和

$$\|g(b)\|\le (L/s)\|b\|^2,\qquad \|Dg(b)\|\le17/239.$$

不可把 g 当作已有函数并把其全部性质存进假设后就标记“图引理完成”。若连续依赖 API 不直接可用，可先用两个不动点方程相减、吸收收缩项得到 g 的 Lipschitz／连续估计；微分由局部隐函数定理和唯一性相粘合。

对 $c=a-g(b)$，通过线段积分得到 $G(a,b)=(\Sigma+E)c$，证明 $\|E\|\le s/8$，然后吸收得到

$$\|c\|\le\frac{8\delta}{7s},\qquad \|\Sigma c\|\le\frac{8\delta}{7}.$$

**易错点：**仅知 $\|c\|\le\delta/s$ 会丢失全谱，第二个加权范数不等式不能遗漏。所有积分线段必须留在导数控制球内。

一般 H：选择其基点的前 r 个奇异方向，定义 $G=U_r^*(H(v_0+V_ra+V_0b)-H(v_0))$。当实际秩大于 r，证明 $D_bG(0)=0$ 仍成立，但未选择方向被放进 k 因子，不能称维数精确。

定义 $\Theta(b,c)=v_0+V_r(g(b)+c)+V_0b$。由 $\delta\le sR$ 证明**整个包含用参数域**的像在 $B(v_0,2R)$，而非只检查实际管内点。证明 $\operatorname{Lip}\Theta\le2$，接 $F$ 在凸球上的导数界和 M02/M06，得到原稿局部非线性覆盖。

**阶段验收：**图存在；图微分；谱椭球包含；全参数域留域；最终覆盖，分别记状态。仅完成标量不等式不计非线性定理完成。

## M08：统一区域上的覆盖

**目标：**紧集 $K\subset B(0,D_0)$、共同扩张邻域半径 $\rho_0$、统一 Hessian 界 $L_H$、数据导数界 $L_F$、每点第 r 奇异值 $\ge s>0$，推出对所有 z 的统一覆盖常数。

取 $R=\min(\rho_0/2,s/(16L_H))$，$L_H=0$ 时明确不做实数除零，而按分支取 $\rho_0/2$。对每条非空纤维选最大 R 分离集，证明有限性、R 球覆盖及数量界，或使用有明确半径的有限网格再挑代表点。把 M07 的 $\delta=0$ 结果逐球相加。

输出统一半径、覆盖常数和量词顺序：先有共同 $s,L_H,L_F,\rho_0$，后对所有 z；不得从“每个 z 都有常数”推“存在对所有 z 的常数”。该模块提供统一几何结果，不自动提供统一 score 误差。

## M09：满行秩伪逆的代数、微分与数值桥

设 $B:E\to F$ 满射，$A=B^*(BB^*)^{-1}$。先证明 $BB^*$ 正定可逆、$BA=I$、$AB$ 是到 $(\ker B)^\perp$ 的正交投影、$\|A\|=1/\sigma_{\min}(B)$。这里 A 是最小范数右逆，不是任意右逆。

然后在满射开集上证明 $B\mapsto A(B)$ 可微。逆映射微分必须使用真正可逆的连续线性算子；不要利用总定义矩阵逆在奇异点的任意值。对方向 E 展开乘积法则、逆微分，整理为

$$DA[B][E]=-AEA+(I-AB)E^*A^*A.$$

利用投影范数至多 1，得到 $\|DA[B][E]\|\le2\|E\|/\sigma_{\min}(B)^2$。这里“2”可先通过三角不等式给出，不追求最优常数。把 $B=DH(v)$ 的链式法则连接到 $D^2H$，得到 $C_A=2L_H/s_0^2$。

**工程约束：**Lean 里的精确实数公式不认证 Python 正规方程稳定性。Python 必须改为 SVD/QR，并在输出中检查 $\|BA-I\|$ 与条件数。若用截断或 Tikhonov，数学对象已经不是该精确 A，必须输出偏差方程，不可沿用 $BA=I$。

**反例与测试：**$B=\left(\begin{smallmatrix}1&1\\1&1+10^{-8}\end{smallmatrix}\right)$；受控随机正交矩阵加给定谱；精确秩亏输入；极端缩放。浮点报告与 Lean 精确证明分别存档。

## M10：no-exit、ODE 运输、变分与 Jacobian

**分拆文件：**`Transport/NoExit.lean`、`RegularTube.lean`、`Flow.lean`、`Variational.lean`、`FiberJacobian.lean`。

把 no-exit 定义为：对每个有序对 $(z,z')\in G^2$，每个 $v_0\in S_z$，存在 $[0,1]$ 上唯一解，满足初值、ODE 和全程留在 K。ODE 解使用实际曲线与 `HasDerivWithinAt`，端点单侧处理；不是给出一个最终映射就称为流。

**第一步：正则管 bootstrap。**满行秩只在 $U_Q$ 上已知；先在停留于 $U_Q$ 的时间段证明 $H(v(t))=z+t(z'-z)$，再用 K 留域、G 凸性、连续性与 $K_G\Subset U_Q$ 排除首次退出。可以用连通区间的开闭延拓替代 supremum 退出时刻，以减少端点处理；两者都必须完成严谨证明。

**第二步：端点映射和逆。**沿解 $\|\dot v\|\le\Delta/s_0$，积分得位移；反转时间并反转 $\xi$ 得逆，利用唯一性。两向位移推出 Hausdorff 距离，不要求先有流微分。

**第三步：初值可微。**从 $C^1$ 向量场建立共同局部流的初值可微及变分方程。mathlib 有局部解存在不等于已有全部参数微分结果；必须查接口。缺少时用 Picard 迭代的参数差商、统一控制与线性变分方程证明，独立列子项目。

**第四步：Gronwall。**$Y'=Db_\xi(v(t))Y$，$Y(0)=I$；推 $\|Y(t)\|\le e^{C_A\Delta t}$ 和 $\|Y(1)-I\|\le e^{C_A\Delta}-1$。[L5] 同样推反向流，控制切向奇异值上下界。

**第五步：纤维面积 Jacobian。**证明 $D\Phi$ 把 $\ker DH(v)$ 双射到终点核空间。对限制线性映射的 Gram 行列式定义 Jacobian，证与奇异值乘积相等，得到 $e^{-kC_A\Delta}\le J_{\rm fib}\Phi\le e^{kC_A\Delta}$。$k=0$ 取空乘积为 1。

**边界义务：**证明环境水平集与 $\partial K$ 的横截给整齐流形；若接口暂时缺失，可先做无边界局部图版本并清楚标注。不能把满秩、边界横截、no-exit 合并成一个未经解释的条件。

**必要实例：**单位圆盘的出域反例；抛物线观测路径的恒等式；可验证的带平直侧壁、远处光滑封口的紧管域实例，使 $H=x$ 的水平运动在选定 G 内确实不出域。简单方盒有角，不能拿它冒充原稿的 $C^2$ 边界 K。

# 工作包 M11–M15：概率运输、像几何与扩散接口

## M11：coarea 与规范纤维条件法则

这是全项目中最可能需要较多库扩展的一块。不要让它阻止 M00–M08。

**目标：**在原 Assumption Q 下证明

$$\nu_z=Q(z)^{-1}\frac{\rho}{J_H}\,\mathcal H^{d-r}|_{S_z},\qquad
Q(z)=\int_{S_z}\rho/J_H\,d\mathcal H^{d-r},$$

并证明它在 $H_\#\mu$ 几乎处处与 M05 的条件核相同。J、参考测度、积分和归一化都必须真实定义。

**推荐窄化证明路线：**只证明紧正则管内 $C^1/C^2$ 满射映射所需的 smooth coarea，不一开始挑战一般 Lipschitz coarea。用隐式坐标 $\chi(z,b)$，欧氏换元给 $|\det D\chi|\,dz\,db$；图面积给 $J_b\chi\,db$；通过线性代数证明

$$|\det D\chi|=J_b\chi/J_H(\chi).$$

随后用有限图覆盖的可测不交细分，或有限 partition of unity，避免重叠重复积分。注意 Hausdorff 测度的规范化常数；不得默认库定义与论文归一化完全相同。带边界图要处理半空间边界，其 k 维边界零测或适当限制条件须证明。

先做 $H$ 为坐标投影的 Fubini 特例；再做一个非线性显式变换，检查 $1/J_H$ 不是遗漏或倒置。证明 $Q(z)>0$、有限、可测；仅“每条纤维有正面积”不足以自动推出关于 z 的可测核结构。

**可保留的接口层：**给定参考纤维测度和合法换元公式，完成权重重加权。这叫 `of_fiber_change_of_variables`，不叫“coarea 已形式化”。必须另外记录参考测度与真正 Hausdorff 测度之间的桥接缺口。

## M12：归一化失真、TV 与 Wasserstein

**先做脱离几何的概率引理。**对概率测度 $\eta$，$f\ge0$、可测且 $\int f\,d\eta=1$。若 $e^{-a}\le f\le e^a$ a.e.，$a\ge0$，证明

$$\frac12\int |f-1|d\eta\le\frac{e^a-1}{e^a+1}=\tanh(a/2).$$

可以先用指数比值，最后转换 tanh；分母正性、a=0、积分有限性明确处理。再证明这与本项目 $\sup_B|\nu(B)-\eta(B)|$ 的 TV 约定等价，不能误用有符号测度 variation 的总质量而差一个 2。

**几何接入：**$w=\rho/J_H$，先用行列式微分证明

$$D\log J_H(v)[h]=\operatorname{tr}(DH(v)^\dagger D^2H(v)[h]).$$

用 trace 的秩相关界得到 $\|\nabla\log J_H\|\le rL_H/s_0$，与正密度下界合成 $L_w$。沿 M10 的真实路径积分，而非不在域内的欧氏弦；叠加纤维 Jacobian 得原始权重比介于 $e^{\pm C_0\Delta}$。换元后得到 Q 的同比例界，再归一化给 $a=2C_0\Delta$。

**无需完整最优输运库的路线：**先构造满足边缘条件的实际 coupling，并给其代价上界。对于同紧支持上的两个概率，用共同参考测度 $\lambda=\mu+\nu$ 的密度 $u,v$ 定义共同质量 $\min(u,v)\lambda$；共同部分对角耦合，残余部分用归一化乘积测度耦合。残余质量正好是 TV，因此 $W_p\le D\,TV^{1/p}$。残余质量 0 单独处理。

若固定版本缺少目标 Wasserstein API，可在本库**按标准定义**用所有边缘正确的 coupling 代价的下确界定义它，然后证明所用性质。不能把 $W_1$ 定义成你构造的某个 coupling 的代价。先用扩展非负实数积分，证明紧支持概率的代价有限，再转实数。

将位移 coupling 与重加权 coupling 合成，或证明所需三角不等式，得到参数 law 与数据 law 界。数据端必须保留 $M_F\Delta/s_0+D_F\tanh(C_0\Delta)$，不误用非凸域的全局 Lipschitz。

**验收：**两个点质量的 TV/W1；平行纤维的直接 TV=1 而 W1 小；非均匀权重的归一化例子；两个不连通分支上不同常值的 F。不要从此推导 W2-Lipschitz。

## M13：像流形的嵌入、移动、曲率

**前提：**$k=d-r\ge1$，每条纤维上 F 单射，且对每个单位纤维切向 u，有 $\|DF(v)u\|\ge\tau_0>0$。这些是真假可检的额外假设，不从普通秩覆盖自动得到。

先证明紧空间上的连续单射是到像的同胚，再用切向非塌缩得到局部浸入，接成嵌入。用参数图版本证明后，再桥接抽象流形接口。定义 $\Psi=F\circ\Phi\circ(F|_{S_z})^{-1}$，严格说明逆只在像子类型上，不是全空间逆。

微分的差 $D\Psi-I$ 是两个都取值于同一个环境 $\mathbb R^D$ 的算子之差：I 是源切空间的自然包含，不是把不同点的切空间未经识别就相减。用

$$DF(\Phi(v))D\Phi(v)-DF(v)$$

展开，并沿水平路径控制 $DF$ 的变化。

曲率先在局部参数图上定义第二基本形式为环境二阶导数的法向投影。证明

$$\mathrm{II}_{S_z}(u,w)=-DH(v)^\dagger D^2H(v)[u,w],$$

再推

$$\|\mathrm{II}_{F(S_z)}\|\le
\frac{M_{F,2}+M_FL_H/s_0}{\tau_0^2}.$$

这里分母平方来自两个单位像切向的原像提升。必须剔除坐标参数化的切向二阶项，不能将任意坐标二阶导数直接等同于 II。

**防误用：**若像精化真的有 $\ell<k$，则存在被 F 消去的非零纤维切向，$\tau_0>0$ 不成立。这两条结论是不同分支。曲率上界也不提供全局 reach 下界。

## M14：高斯平滑和一般核的 L1 稳定性

先实现与高斯无关的引理：核 K 可微，方向导数的 L1 范数有统一上界 c，则任意平移向量 h 满足 $\|K(\cdot-h)-K\|_1\le c\|h\|$。梯度版本对 $D^2K$ 做同样处理。通过线段积分、Tonelli/Fubini、平移测度不变性证明。

再对真实概率测度 coupling 积分，得到卷积差至多核常数乘 Wasserstein 距离；必须先证明可测性、可积性，处理 $\alpha=0$。无需先有 M13 的流形结构，因此本模块可与曲率并行。

最后实例化 D 维高斯，$\sigma>0$，证明方向梯度积分 $\sqrt{2/\pi}/\sigma$；Hessian 方向积分用 Cauchy–Schwarz 与

$$\mathbb E\|(GG^*-I)u\|^2=D+1\quad(\|u\|=1).$$

先展开 $u=e_1$ 的独立高斯矩，再用旋转不变性；如果旋转 API 难，先对标准基展开多项式矩并用 $\|u\|=1$ 合并。输出

$$\|p_z-p_{z'}\|_1\le\sqrt{2/\pi}|\alpha|W_1/\sigma,$$
$$\|\nabla p_z-\nabla p_{z'}\|_1\le|\alpha|\sqrt{D+1}W_1/\sigma^2.$$

**边界：**不得在同一文件尾部用没有证明的正下界把它升级为 score 稳定。可另加“在有明确 $p\ge c>0$ 的紧测试区域上的条件引理”，但它不等于全空间 score L2 理论。

## M15：外部 DDPM 熵接口

把这个模块命名为 `ExternalDDPMInterface` 而非 `DDPMConvergenceProof`。目标是核查并形式化**本项目供给的假设**，不重证 Liang–Huang–Chen v2 全文。[P2]

先把已证 $\log N_\varepsilon\le C+k\log(1/\varepsilon)$，$k\ge1$，代入 $\varepsilon_0=T^{-c}$，$T\ge2$，证明 $\log N_{\varepsilon_0}\le\widetilde C k\log T$。常数依赖固定观测、阈值 T0、半径界均写进量词。

外部依赖清单必须列：v2 的准确 PDF/HTML 版本；Assumptions 1–3；噪声日程；原始 DDPM 的采样系数；起始分布；unweighted average score L2 error；最终比较对象 $X_1,Y_1$ 而非无噪声 $X_0$。不能仅用一个叫 `ScoreAccurate` 的模糊布尔命题。

可以证明一个显式接受“外部定理的完整函数化命题”为参数的应用引理，但它只能标 `CONDITIONAL_VERIFIED (external theorem not formalized)`。**不引入 axiom 并不等于外部证明已经完成。** 若最终 theorem 的参数里仍有外部收敛命题，账本必须永久显示。

对于 $k=0$，本项目只宣布有限支持，或者另用正有效覆盖参数调用外部结果并说明不再是零指数；不能直接把 0 塞入要求正内在维数的定理。对于统一或观测平均速率，除非补齐共同常数、积分控制与 score 条件，否则不扩张声明。

# 工作包 M16–M20：EIT、工程与统计接口

## M16：相容正交投影、加权坐标与 gauge

在有限维实 Hilbert 空间证明：非空闭仿射集合 C、$x^\star\in C$、正交投影 $\Pi_C$，则 $\|\Pi_Cx-x^\star\|\le\|x-x^\star\|$。先用 $C=a+S$ 的线性子空间表示和正交分解证明 Pythagoras，再包装仿射版本。

EIT 的对称矩阵上三角展平有两种规范：未加权上三角欧氏范数，或非对角乘 $\sqrt2$ 后与 Frobenius 范数等距。必须选择并证明相应恒等式。entrywise normalization 改变物理约束：$Y=\Lambda\oslash\Lambda_1$ 时，行和应为 $\sum_j(\Lambda_1)_{ij}Y_{ij}=0$。若某背景条目为零，除法规范另定义，不能直接除。

证明实际投影矩阵确实是目标内积下的正交投影，真实约束集确实非空。保持带噪声的观测值通常使无噪声真值不属于该集合，此时不再应用非扩张结论。把物理可行性与统计准确性分别测试。

## M17：Gaussian MMSE 和决策风险

拆成三个彼此不同的定理：矩阵恒等式；真实高斯条件协方差；条件均值的平方损失最优性。前一个容易完成，不能冒充后两个。

对 $\eta\sim N(0,I)$、独立 $\epsilon\sim N(0,\Gamma)$、$y=\mu+B\eta$，构造联合高斯随机向量并证明 covariance blocks。用完成平方或联合 Gaussian conditioning 得

$$P_M=(I+B_M^*\Gamma^{-1}B_M)^{-1}.$$

再用条件期望的正交投影性质证明 Bayes risk 是 $\operatorname{tr}(B_{\bar M}P_MB_{\bar M}^*)$。正定性保证逆存在，二阶矩确保可积性。

可以先在有密度的有限维实 Gaussian 中完成平方并验证归一化常数。若条件 Gaussian API 不足，则该桥接留 `BLOCKED`，只公布已经完成的矩阵命题。应有标量手算例子和改变噪声方差的例子；Monte Carlo 数字永不作为证明输入。

## M18：连续 CEM、离散 FEM 与真实形状图

**三个层次分开：**

1. 抽象 Banach/Hilbert 算子 $A(\theta)$ 的可微可逆性：若算子族 C1 且可逆，$D(A^{-1})=-A^{-1}(DA)A^{-1}$。这一层不需要完整 PDE。
2. 平滑 CEM 系数图：真实 $H^1$ 空间、gauge、迹算子、正接触阻抗、双线性型有界与 coercive、Lax–Milgram、$\theta\mapsto\gamma_\theta$ 在 $L^\infty$ 中 C1。证明每个假设来自物理域和系数，不把 coercivity 与可逆性全放假设后宣称 CEM 已证。
3. 移动不连续多边形：这是 shape calculus；$\gamma_v$ 一般不在 $L^\infty$ 中连续，不能接第 2 层的 C1 前提。要用固定参考域的形变拉回、Jacobian、界面条件、弱解及边界读出正则性，另列大工作包或明确不做。

**优先实现离散有限维版本：**给真实对称刚度矩阵

$$K=\begin{pmatrix}K_{bb}&K_{bi}\\K_{ib}&K_{ii}\end{pmatrix},\qquad
\Lambda=K_{bb}-K_{bi}K_{ii}^{-1}K_{ib}.$$

证明内部块正定可逆、Schur 补对称、能量非负、适当常数电势对应行和零、固定规范下映射可微。[L7] 这形成诚实的“离散 DtN 结构已证”，但没有认证网格积分、装配程序或连续收敛。

**工程核验入口：**找回真实前向生成器；判定是单元中心硬分类、精确交面积、光滑过渡还是随形状重网格。硬分类可局部常值并在跨单元时跳变；未经这一检查，差分 Jacobian 不能作为解析导数证书。

## M19：从浮点诊断到可检查的有限证书

Lean 精确实数定理不会自动覆盖 NumPy 的浮点实现。需要一条明确的数值证书链：输入文件 hash→确定性有理/区间解析→有限矩阵界→真实导数误差界→局部解析结论。

推荐不依赖浮点 SVD 的满行秩证书：给有理矩阵近似 $\widehat B$ 和有理右逆候选 R，认证 $\|I-\widehat BR\|\le q<1$，并有真实 B 的误差 $\|B-\widehat B\|\le e$。则

$$\|I-BR\|\le q+e\|R\|<1$$

推出 BR 可逆、B 满射，并构造 $R(BR)^{-1}$。其范数至多 $\|R\|/(1-q-e\|R\|)$。这给可检查的正则性证书，不需要“数值 rank=6”作为公理。

所有有限矩阵算子范数可先由 Frobenius 有理平方和的保守上界控制；使用平方比较可避免形式化不精确 sqrt。若有 Hessian/Lipschitz 导数界 $L$，由 $\|B(v)-B(v_0)\|\le L\|v-v_0\|$ 扩展到一球。它认证的是该球中的秩下界；不认证整条纤维全被这些球覆盖，覆盖完整性另需要证书。

对真实 FEM 导数，有限差分误差 e 必须来自截断误差与求解舍入的上界，不是“相邻 h 的结果差不多”。不具备 e 时，状态保持 `NUMERICAL_ONLY`。对有理多项式 toy 先建立完整实例，避免主工程空转。

## M20：评分、分位区间与实验协议

**分位区间：**证明对于 n 个 iid 连续样本与独立同分布真值，真值处于样本最小值和最大值之间的概率 $(n-1)/(n+1)$。路线：交换性、无 ties、真值的秩在 $1,\ldots,n+1$ 均匀。n=16 得 $15/17$；经验 5%–95% 分位区间是极值区间的子集，因此平均覆盖不超过它。这个结论需要 iid 与真值同分布条件，不对任意相关生成器无条件宣称上界。

**energy score：**对 iid $X_1,\ldots,X_B$，证明 V-statistic 的成对距离项少一个 $(B-1)/B$ 系数；U-statistic 使用 $B(B-1)$ 分母，$B\ge2$。先对固定真值证明期望关系，核对对角距离为零。

**真值范数归一化的反例：**真值为 1 或 2，概率各半，预测分布在 2 的概率 q。一维 energy score 等于 CRPS，在该两点模型中评分为 $(q-\mathbf1_{y=2})^2$。除以 $|y|$ 后期望为 $\tfrac12q^2+\tfrac14(1-q)^2$，在 $q=1/3$ 最小，而不是真实的 $q=1/2$。用有理数和平方配方可形式化整个反例；它说明这种归一化不是原真实 law 的严格适当评分。

**协议部分：**Lean 可证明指标公式与汇总定义的代数关系，不能证明历史训练没有看 test data。后者依赖源码、不可变 split、日志、mask 配置、checkpoint 和预测张量。对 20 个固定且修剪选出的 masks 的 bootstrap 不能自动推至所有 masks；三种 network seeds 的重采样也不能提供训练随机性分布的强保证。

# 完整的阶段顺序与停止条件

## 阶段 A：小而真实的形式化核心

实施 M00、M01、M02，随后 M03 与 M05；M06 的对角／显式 frame 版本可以并行。第一份对外可用证据应包含：真实线性映射秩公式；从函数微分条件到有限图再到覆盖的完整桥接；真实条件核支持。只做出前两项时，就只报告前两项。

**阶段 A 接受门槛：**生产入口无未批准公理和占位；所有导出定理有完整声明与假设表；至少三个不同实例；M03 覆盖与原文维数定理明确分开；无“全篇形式化”的表述。

## 阶段 B：数值机制的解析骨架

补齐 M06 的一般谱存在、M07、M08、M09 和 M19 的一个 toy 证书。并修复 Python 伪逆及覆盖接口。它支持可复核的局部谱机制，不自动认证真实 EIT 的全先验。

## 阶段 C：测度与运输

先做 M12 的抽象密度比、TV、coupling；并行做 M10。M11 先投影 Fubini 再 smooth coarea。只有当这三者连接完毕，才标记条件法则运输定理完整。M14 的一般卷积核结果可以独立推进。

## 阶段 D：拓展与应用

M04 的全常秩几何、M13、M16–M18、M20，以及 M15 外部接口精确账本。真正连续 PDE/shape 和外部 DDPM 全证明不列为初次汇报的硬门槛。

## Codex 的有限尝试协议

每遇到一个卡点，至少依次做：核查目标真假与定义；搜索固定 mathlib 的相关 API；将大目标缩成最小 lemma；尝试两条结构不同的证明路线；做一个非退化实例和一个去掉必要假设的反例。然后把仍未解决的**准确目标**写入 `FAILURE_LOG.md`，继续其他独立模块。

不要在同一错误上无限反复增加 `simp` 列表、heartbeats 或重写目标。资源耗尽时提交已完成文件、构建结果与账本，不把 `sorry` 转为自造 axiom，不给出不存在的未来交付承诺。

# 证明审计、CI 与防止空洞完成

## CI 至少执行的内容

固定工具链和 manifest；`lake build`；逐个审计文件输出 `#print` 与 `#print axioms`；检查预先登记的目标列表非空且全部存在；验证每个目标的实际类型；跑所有 examples；保存日志与源码 SHA。`lake build` 对空库成功不是完成。

允许的逻辑基础通常为 `propext`、`Classical.choice`、`Quot.sound`，以实际输出为准。[L8] 对 `sorryAx`、自定义研究结论公理或其他额外信任入口默认拒绝。`native_decide` 等计算路径先列明信任依赖；核心研究证明优先使用普通可由内核检查的证明项。正则表达式扫描只是辅助，不是安全证明：注释、宏、引入依赖、变量假设都可能绕开它。

必须给 root theorem 做 `#print` 类型输出：检查有没有新增 `False`、空模型、`∀x, property` 直接包含结论、已给覆盖证书而未构造、只在一个点成立、把概率 law 换成有限测试集等语义问题。

## 负测试与实例测试

负测试不要求 Lean 接受假命题，而是另证使该命题失败的显式反例。必须覆盖：点秩不保证维数；边界横截不保证最小范数 no-exit；像精化不保证嵌入；不连通域导数界不保证全局 Lipschitz；固定正 Gaussian 噪声不减少严格支持；有限样本分位率不等于标称率。

正实例至少包括：线性投影；非线性抛物线；发生像塌缩的线性映射；带正密度重加权；有完整证书的离散 toy DtN。对于 K、G、rho 等联合假设，至少有一个同时满足的实例，而不是每条假设各找一个不兼容例子。

## 外部结果与本地结果的分离

每个主声明都标出依赖类别：mathlib 内核证明；本项目内核证明；明确的外部数学定理参数；未构造几何证书；数值证据；未公开工程。最终图中不能把后三类画成已证节点。

**数学条件定理不是错误。** 允许 theorem 假设 no-exit，因为原文同样假设它；不允许把“纤维之间存在满足全部目标界的运输映射”新增为假设，却仍声称已经证明原文由 no-exit 推运输的定理。

# 主文标签与工作包对照

| 主文标签 | 主要工作包 | 完整验证所需桥接 |
|---|---|---|
| `thm:fiber-entropy` | M02–M04 | M03 只覆盖覆盖部分；流形维数需 M04 |
| `cor:image-rank-entropy` | M01、M02、M04 | 点态秩到邻域图的桥接 |
| `prop:conditional-support` | M00、M05 | 真实条件核而非任意 kernel |
| `cor:random-entropy` | M02–M05 | 可数 mask、a.e. 与尺度范围 |
| `thm:linear-tube` | M02、M06 | 一般 J 到谱 frame 存在 |
| `cor:whitened` | M06 | SPD 到可逆白化矩阵 |
| `lem:quantitative-graph` | M07 | 固定点的实际构造与参数正则性 |
| `thm:nonlinear-tube` | M06、M07 | 整个参数化包含域留在控制球 |
| `cor:uniform-fiber` | M08 | 所有纤维的共同量词与网格 |
| `lem:regular-tube-bootstrap` | M10 | 首次退出／区间延拓 |
| `lem:pinv` | M09 | 可逆性、伴随、真实导数 |
| `thm:transport` | M09–M11 | 初值微分、切向面积与边界 |
| `thm:measure-transport` | M10–M12 | coarea、换元、归一化与 coupling |
| `cor:data-law` | M12 | 路径移动和像直径分离 |
| `thm:moving-manifold` | M13 | 嵌入、切空间与二阶基本形式 |
| `prop:smoothing` | M14 | 真实高斯积分和 coupling |
| `cor:ddpm` | M15 | 外部定理未证必须保留标注 |
| `prop:projection` | M16 | 真值相容与实际内积 |
| `prop:mmse` | M17 | Gaussian conditioning 与风险最优性 |
| `prop:cem` | M18 | 抽象逆→真实弱解→电压读出 |

# 给 Codex 的完整执行指令

以下文字可以直接交给 Codex，并附本文件与配套目录：

> 在 conditional-fiber-geometry 固定基线下建立独立 formal 分支，按本规格逐阶段实现。先读取论文、审计、现有工作区和所有账本，不覆盖用户修改。首轮目标是 M00–M03 与 M05 的可验证核心，不以完整 coarea/PDE 为前置条件。先完成 API 探测和版本锁定，再写目标的真实数学类型。不得把导数、秩、覆盖、条件法则、流或外部 DDPM 结论作为无来源常数导入。优先采用构造有限覆盖和局部投影隐函数路线。所有生产证明无 sorry、无新增研究公理；接口定理允许显式条件，但必须命名和标注其桥接未完成。逐项记录实际类型、依赖、编译结果、实例和反例。遇到卡点按本规格尝试、记录并继续独立模块，不擅自弱化主命题。最后输出已完整对应论文的结果、仅完成的辅助引理、接口依赖、未解决目标、数值与数学的分界，以及下一步最小任务。不要推送、创建 release 或改写历史，除非另获明确授权。

# 联合假设的完整非退化测试实例：环域径向观测

不只分别测试各假设。用下列同一模型同时连接 M00、M03、M09–M14：在 $\mathbb R^2$ 中，

$$K=\{v:1\le\|v\|\le3\},\quad H(v)=\|v\|^2,\quad G=[4,6],$$
$$F(v)=(v_1,v_2,\|v\|^2)\in\mathbb R^3,$$

P 取第三坐标，所以 H=PF。先验在 K 上均匀，$\rho=1/(8\pi)$。取共同正则开邻域 $U_Q=\{v:3<\|v\|^2<7\}$，其闭包紧含于避开原点的更大开域。

K 是光滑紧环域，有内外两个边界圆。$\partial K$ 上 H 只取 1 和 9，不与 G 相交，所以边界 submersion 条件在相关边界上没有需检查的点；**整个模型不是空模型**，每个 z 的纤维都是非空圆，长度 $2\pi\sqrt z>0$。

令 $\xi=z'-z$，明确曲线

$$v(t)=\sqrt{\frac{z+t\xi}{z}}\,v_0,\qquad\|v_0\|^2=z.$$

证明其真实导数满足 $\dot v=\xi v/(2\|v\|^2)$，正是 DH 的最小范数提升；$H(v(t))=z+t\xi\in[4,6]$，因此留在 K，反向也成立。局部 Lipschitz 给唯一性，或从径向方程直接证明方向不变和半径平方线性，从而闭合 no-exit。

$J_H=2\sqrt z$，共面积归一化 $Q(z)=\rho\pi=1/8$，于是

$$\nu_z=\frac{1}{2\pi\sqrt z}\mathcal H^1|_{\{\|v\|^2=z\}}.$$

端点流为半径缩放，切向 Jacobian $\sqrt{z'/z}$；权重比 $\sqrt{z/z'}$ 抵消它，所以 transported TV 恰为 0。F 单射且任意切向的 DF 范数至少等于原向量范数，故 $\tau_0\ge1$。此例可完整测试嵌入与运输，而不是仅证明两条抽象证书之间的蕴含。

Lean 次序：先证明 normSq 多项式的导数；用 sqrt 正值区间导数验证显式曲线；再证 fiber 与逆映射；最后补圆周 Hausdorff 测度、均匀条件 law 和归一化。未证明圆周测度前，不把 coarea 实例标为完整。常数可以用保守有理界，不必追求精确最优。

本例的边界交集为空，因此还应另保留单位圆盘的 no-exit 反例，防止把该良性实例错误推广到横截边界情形。

# 来源与阅读入口

[R1] 项目固定提交及其 `manuscript/main.tex`、`docs/MATHEMATICAL_SCOPE.md`、`docs/CLAIMS_AND_EVIDENCE.md`。https://github.com/NewAsiaSuperbear/conditional-fiber-geometry/tree/77e2203e6d5df42b457823eebe6626f1b1c3ded1

[R2] 本会话《独立审计报告》《人工核验与修补清单》，2026-09-07。原审计只运行了原始测试子集，不是全部工程复现。

[P2] Liang, Huang, Chen. *Low-Dimensional Adaptation of Diffusion Models: Convergence in Total Variation*, arXiv:2501.12982v2，特别是 Assumptions 1–3 和 Theorem 2。https://arxiv.org/html/2501.12982v2

[L1] mathlib 固定提交与 `lean-toolchain`。https://github.com/leanprover-community/mathlib4/tree/71a80585ee495fc24472fd0eaffc89d94e4fd8d6

[L2] 官方隐函数文档。https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Implicit.html

[L3] 官方覆盖数文档。https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/CoveringNumbers.html

[L4] 官方标准 Borel disintegration 文档。https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Disintegration/StandardBorel.html

[L5] 官方 ODE 与 Gronwall 文档。https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/ODE/PicardLindelof.html ；https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/ODE/Gronwall.html

[L6] 官方伴随与有限维基础。https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Adjoint.html

[L7] 官方 Schur 补。https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/SchurComplement.html

[L8] Lean 官方 *Theorem Proving in Lean 4*, Axioms and Computation。https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/

这些链接截至 2026-09-07 核查。源码和定理类型以固定 SHA 上的本地实际检查为准；本方案没有把线上模块目录的搜索空白解释为数学不可能。
