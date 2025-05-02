
# Basic probability and information theory in Lean 


#### Scope  
This project started as a formalization of Chapter 2 of *Elements of Information Theory* by Cover & Thomas. It now serves as a small playground for discrete probability and information theory. 

---

#### Current contents

| file | main definitions | main results |
|------|-----------------|--------------------|
| `InformationTheory.lean` <br> This follows Chapter 2 of Cover & Thomas.| • `pmf Ω`: finite real PMF<br>• entropy, KL divergence | • basic pmf lemmas<br>• non-negativity of entropy and KL divergence |
| `FDivergence.lean` | • $f$-divergence in ℝ  | • non-negativity<br>• KL is an $f$-divergence|

----

Author: Sean Welleck