
# Basic probability and information theory in Lean 


#### Scope  
This project started as a formalization of Chapter 2 of *Elements of Information Theory* by Cover & Thomas. It now serves as a small playground for discrete probability and information theory. 

---

#### Current contents

| file | main definitions | main results |
|------|-----------------|--------------------|
| `InformationTheory.lean` <br> This follows Chapter 2 of Cover & Thomas.| • `pmf Ω`: finite real PMF<br>• Entropy, KL divergence | • Basic pmf lemmas<br>• Non-negativity of entropy and KL divergence |
| `FDivergence.lean` | • $f$-divergence in ℝ<br> • Total variation distance <br> • Squared Hellinger distance| • Non-negativity<br>• KL, total variation, squared Hellinger are $f$-divergences|

----

Author: Sean Welleck
