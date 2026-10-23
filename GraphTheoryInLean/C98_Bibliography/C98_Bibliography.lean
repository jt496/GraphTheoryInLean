import GraphTheoryInLean.Common

/-!
* [Albertson 1998] M. O. Albertson, “You can't paint yourself into a corner”, J.
  Combin. Theory Ser. B **73** (1998), no. 2, 189–194.
  <https://doi.org/10.1006/jctb.1998.1827>

* [Andrásfai–Erdős–Sós 1974] B. Andrásfai, P. Erdős and V. T. Sós, “On the connection
  between chromatic number, maximal clique and minimal degree of a graph”, Discrete
  Math. **8** (1974), no. 3, 205–218. <https://doi.org/10.1016/0012-365X(74)90133-2>

* [Behrend 1946] F. A. Behrend, “On sets of integers which contain no three terms in
  arithmetical progression”, Proc. Nat. Acad. Sci. U.S.A. **32** (1946), no. 12,
  331–332. <https://doi.org/10.1073/pnas.32.12.331>

* [Berge 1957] C. Berge, “Two theorems in graph theory”, Proc. Nat. Acad. Sci. U.S.A.
  **43** (1957), no. 9, 842–844. <https://doi.org/10.1073/pnas.43.9.842>

* [Bondy–Chvátal 1976] J. A. Bondy and V. Chvátal, “A method in graph theory”,
  Discrete Math. **15** (1976), no. 2, 111–135.
  <https://doi.org/10.1016/0012-365X(76)90078-9>

* [Brooks 1941] R. L. Brooks, “On colouring the nodes of a network”, Proc. Cambridge
  Philos. Soc. **37** (1941), no. 2, 194–197.
  <https://doi.org/10.1017/S030500410002168X>

* [Cayley 1878] A. Cayley, “Desiderata and suggestions: No. 2. The theory of groups:
  graphical representation”, Amer. J. Math. **1** (1878), no. 2, 174–176.
  <https://doi.org/10.2307/2369306>

* [Cayley 1889] A. Cayley, “A theorem on trees”, Quart. J. Pure Appl. Math. **23**
  (1889), 376–378. Reprinted in The Collected Mathematical Papers XIII, 26–28.
  <https://doi.org/10.1017/CBO9780511703799.010>

* [de Bruijn–Erdős 1951] N. G. de Bruijn and P. Erdős, “A colour problem for infinite
  graphs and a problem in the theory of relations”, Indag. Math. **13** (1951), no.
  5, 371–373. <https://doi.org/10.1016/S1385-7258(51)50053-7>

* [Diestel–Kühn 2003] R. Diestel and D. Kühn, “Graph-theoretical versus topological
  ends of graphs”, J. Combin. Theory Ser. B **87** (2003), no. 1, 197–206.
  <https://doi.org/10.1016/S0095-8956(02)00034-5>

* [Dirac 1952] G. A. Dirac, “Some theorems on abstract graphs”, Proc. London Math.
  Soc. (3) **2** (1952), no. 1, 69–81. <https://doi.org/10.1112/plms/s3-2.1.69>

* [Erdős 1970] P. Erdős, “Turán Pál gráf tételéről” [On the graph theorem of Turán],
  Mat. Lapok **21** (1970), 249–251. <https://www.renyi.hu/~p_erdos/1971-27.pdf>

* [Erdős–Gallai 1960] P. Erdős and T. Gallai, “Gráfok előírt fokú pontokkal” [Graphs
  with prescribed degrees of vertices], Mat. Lapok **11** (1960), 264–274.
  <https://www.renyi.hu/~p_erdos/1961-05.pdf>

* [Erdős–Ko–Rado 1961] P. Erdős, C. Ko and R. Rado, “Intersection theorems for
  systems of finite sets”, Quart. J. Math. Oxford Ser. (2) **12** (1961), 313–320.
  <https://doi.org/10.1093/qmath/12.1.313>

* [Erdős–Simonovits 1966] P. Erdős and M. Simonovits, “A limit theorem in graph
  theory”, Studia Sci. Math. Hungar. **1** (1966), 51–57.
  <https://mathscinet.ams.org/mathscinet/relay-station?mr=0205876>

* [Erdős–Stone 1946] P. Erdős and A. H. Stone, “On the structure of linear graphs”,
  Bull. Amer. Math. Soc. **52** (1946), no. 12, 1087–1091.
  <https://doi.org/10.1090/S0002-9904-1946-08715-7>

* [Euler 1741] L. Euler, “Solutio problematis ad geometriam situs pertinentis” [The
  solution of a problem relating to the geometry of position], Comment. Acad. Sci.
  Petropol. **8** (1741), 128–140. Eneström E53.
  <https://scholarlycommons.pacific.edu/euler-works/53/>

* [Euler 1758] L. Euler, “Elementa doctrinae solidorum” [Elements of the doctrine of
  solids], Novi Comment. Acad. Sci. Petropol. **4** (1758), 109–140. Eneström E230.
  <https://scholarlycommons.pacific.edu/euler-works/230/>

* [Füredi 2015] Z. Füredi, “A proof of the stability of extremal graphs, Simonovits'
  stability from Szemerédi's regularity”, J. Combin. Theory Ser. B **115** (2015),
  66–71. <https://doi.org/10.1016/j.jctb.2015.05.001>

* [Gray 1953] F. Gray, “Pulse code communication”, U.S. Patent 2,632,058, 1953. Filed
  13 November 1947. <https://patents.google.com/patent/US2632058A/en>

* [Grötzsch 1959] H. Grötzsch, “Zur Theorie der diskreten Gebilde, VII: Ein
  Dreifarbensatz für dreikreisfreie Netze auf der Kugel” [On the theory of discrete
  structures, VII: A three-colour theorem for triangle-free networks on the sphere],
  Wiss. Z. Martin-Luther-Univ. Halle-Wittenberg Math.-Natur. Reihe **8** (1959),
  109–120. <https://mathscinet.ams.org/mathscinet/relay-station?mr=0116320>

* [Hakimi 1962] S. L. Hakimi, “On realizability of a set of integers as degrees of
  the vertices of a linear graph. I”, J. Soc. Indust. Appl. Math. **10** (1962), no.
  3, 496–506. <https://doi.org/10.1137/0110037>

* [Hall 1935] P. Hall, “On representatives of subsets”, J. London Math. Soc. **10**
  (1935), no. 1, 26–30. <https://doi.org/10.1112/jlms/s1-10.37.26>

* [Hamming 1950] R. W. Hamming, “Error detecting and error correcting codes”, Bell
  System Tech. J. **29** (1950), no. 2, 147–160.
  <https://doi.org/10.1002/j.1538-7305.1950.tb00463.x>

* [Havel 1955] V. Havel, “Poznámka o existenci konečných grafů” [A remark on the
  existence of finite graphs], Časopis Pěst. Mat. **80** (1955), no. 4, 477–480.
  <https://doi.org/10.21136/CPM.1955.108220>

* [Hierholzer 1873] C. Hierholzer, “Ueber die Möglichkeit, einen Linienzug ohne
  Wiederholung und ohne Unterbrechung zu umfahren” [On the possibility of traversing
  a line system without repetition and without interruption], Math. Ann. **6**
  (1873), no. 1, 30–32. Published after his death by C. Wiener.
  <https://doi.org/10.1007/BF01442866>

* [Hoffman–Singleton 1960] A. J. Hoffman and R. R. Singleton, “On Moore graphs with
  diameters 2 and 3”, IBM J. Res. Develop. **4** (1960), no. 5, 497–504.
  <https://doi.org/10.1147/rd.45.0497>

* [Kirchhoff 1847] G. R. Kirchhoff, “Ueber die Auflösung der Gleichungen, auf welche
  man bei der Untersuchung der linearen Vertheilung galvanischer Ströme geführt wird”
  [On the solution of the equations obtained from the investigation of the linear
  distribution of galvanic currents], Ann. Phys. Chem. **72** (1847), no. 12,
  497–508. <https://doi.org/10.1002/andp.18471481202>

* [Kneser 1955] M. Kneser, “Aufgabe 360” [Problem 360], Jahresber. Deutsch.
  Math.-Verein. **58** (1955), no. 2, 27. See also Martin Kneser, Collected Works,
  Springer, 2021, 729–742. <https://doi.org/10.1007/978-3-030-81625-4_6>

* [Kőnig 1916] D. Kőnig, “Über Graphen und ihre Anwendung auf Determinantentheorie
  und Mengenlehre”, Math. Ann. **77** (1916), no. 4, 453–465.
  <https://doi.org/10.1007/BF01456961>

* [Kőnig 1927] D. Kőnig, “Über eine Schlußweise aus dem Endlichen ins Unendliche” [On
  a mode of inference from the finite to the infinite], Acta Litt. Sci. Szeged **3**
  (1927), 121–130. <https://acta.bibl.u-szeged.hu/13338/>

* [Kőnig 1931] D. Kőnig, “Graphok és matrixok” [Graphs and matrices], Mat. Fiz. Lapok
  **38** (1931), 116–119. <https://real-j.mtak.hu/7307/>

* [Kővári–Sós–Turán 1954] T. Kővári, V. T. Sós and P. Turán, “On a problem of K.
  Zarankiewicz”, Colloq. Math. **3** (1954), no. 1, 50–57.
  <https://doi.org/10.4064/cm-3-1-50-57>

* [Lovász 1975] L. Lovász, “Three short proofs in graph theory”, J. Combin. Theory
  Ser. B **19** (1975), no. 3, 269–271.
  <https://doi.org/10.1016/0095-8956(75)90089-1>

* [Mantel 1907] W. Mantel, “Vraagstuk XXVIII” [Problem 28], Wiskundige Opgaven **10**
  (1907), 60–61. Solution by H. Gouwentak, W. Mantel, J. Teixeira de Mattes, F. Schuh
  and W. A. Wythoff. <https://zbmath.org/2643703>

* [Menger 1927] K. Menger, “Zur allgemeinen Kurventheorie” [On the general theory of
  curves], Fund. Math. **10** (1927), 96–115.
  <https://doi.org/10.4064/fm-10-1-96-115>

* [Mycielski 1955] J. Mycielski, “Sur le coloriage des graphs” [On the colouring of
  graphs], Colloq. Math. **3** (1955), no. 2, 161–162.
  <https://doi.org/10.4064/cm-3-2-161-162>

* [Ore 1960] Ø. Ore, “Note on Hamilton circuits”, Amer. Math. Monthly **67** (1960),
  no. 1, 55. <https://doi.org/10.2307/2308928>

* [Paley 1933] R. E. A. C. Paley, “On orthogonal matrices”, J. Math. Phys. **12**
  (1933), 311–320. <https://doi.org/10.1002/sapm1933121311>

* [Petersen 1898] J. Petersen, “Sur le théorème de Tait” [On Tait's theorem],
  L'Intermédiaire des Mathématiciens **5** (1898), 225–227.

* [Pósa 1976] L. Pósa, “Hamiltonian circuits in random graphs”, Discrete Math. **14**
  (1976), no. 4, 359–364. <https://doi.org/10.1016/0012-365X(76)90068-6>

* [Ramsey 1930] F. P. Ramsey, “On a problem of formal logic”, Proc. London Math. Soc.
  (2) **30** (1930), 264–286. <https://doi.org/10.1112/plms/s2-30.1.264>

* [Roth 1953] K. F. Roth, “On certain sets of integers”, J. London Math. Soc. **28**
  (1953), no. 1, 104–109. <https://doi.org/10.1112/jlms/s1-28.1.104>

* [Ruzsa–Szemerédi 1978] I. Z. Ruzsa and E. Szemerédi, “Triple systems with no six
  points carrying three triangles”, in Combinatorics (Proc. Fifth Hungarian Colloq.,
  Keszthely, 1976), Vol. II (A. Hajnal and V. T. Sós, eds.), Colloq. Math. Soc. János
  Bolyai 18, North-Holland, Amsterdam, 1978, pp. 939–945.
  <https://mathscinet.ams.org/mathscinet/relay-station?mr=0519318>

* [Szemerédi 1978] E. Szemerédi, “Regular partitions of graphs”, in Problèmes
  combinatoires et théorie des graphes (Orsay, 1976), Colloq. Internat. CNRS 260,
  CNRS, Paris, 1978, pp. 399–401.
  <https://mathscinet.ams.org/mathscinet/relay-station?mr=0540024>

* [Turán 1941] P. Turán, “Egy gráfelméleti szélsőértékfeladatról” [On an extremal
  problem in graph theory], Mat. Fiz. Lapok **48** (1941), 436–452.
  <https://mathscinet.ams.org/mathscinet/relay-station?mr=0018405>

* [Tutte 1947] W. T. Tutte, “The factorization of linear graphs”, J. London Math.
  Soc. **22** (1947), no. 2, 107–111. <https://doi.org/10.1112/jlms/s1-22.2.107>

* [Vizing 1964] V. G. Vizing, “On an estimate of the chromatic class of a $p$-graph”
  (in Russian), Diskret. Analiz (1964), no. 3, 25–30.
  <https://mathscinet.ams.org/mathscinet/relay-station?mr=0180505>

* [Whitney 1932] H. Whitney, “Congruent graphs and the connectivity of graphs”, Amer.
  J. Math. **54** (1932), no. 1, 150–168. <https://doi.org/10.2307/2371086>

* [Zarankiewicz 1951] K. Zarankiewicz,
  “Problem P 101”, Colloq. Math. **2** (1951), 301.

* [Zykov 1949] A. A. Zykov, “On some properties of linear complexes” (in Russian),
  Mat. Sb. (N.S.) **24(66)** (1949), no. 2, 163–188. <https://eudml.org/doc/65433>
-/
