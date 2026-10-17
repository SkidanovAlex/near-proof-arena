import math, levers_model as L
for c_sha in (12000, 24000):
  for pen_t, fin_t, dig in ((268,268,48),(236,226,42)):
    cells, blocks, shape, fin = L.fixed_point(c_sha, 2000, 1<<20, pen_t, fin_t, 8, dig)
    print(c_sha, pen_t, fin_t, dig, blocks, shape, round(math.log2(cells),2))
    print('  ', fin)
