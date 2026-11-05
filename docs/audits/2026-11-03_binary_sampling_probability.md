# Failure probabilities at a binary merge

Two independent child histories, with probability laws mu and nu, succeed on measurable sets A and B. A fresh parent variable has probability law rho. If the actual parent failure relation E is measurable and each section over A times B has measure at most epsilon, then the probability of a child failure or a parent failure is at most mu(A-complement) + nu(B-complement) + epsilon.

The proof combines the existing uniform section inequality with the union bound for the complement of a product. The latter outer-measure inequality does not require measurability of A or B. No new probability structure or measurable choice of auxiliary success hulls is introduced.

This is the binary measure step needed in the interval recursion of Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2, Figure fig:algo1 and lines 1777–1817. The actual measurable parent map, its fixed-input estimate and the finite physical hierarchy must still be supplied. The result alone is not a probability theorem for the complete algorithm.
