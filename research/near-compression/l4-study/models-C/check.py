import math, ext, levers_model as L
# reproduce child
r = ext.layer(1<<17, 295, 7, 3, 3, 17, 2, ext.P())
print(r['q'], r['initial'], r['codeword'], r['bytes'])
# reproduce levers fixed point c_sha 12k today
cells, blocks, shape, fin = ext.fixed_point(12000, ext.P(target=268, m=8), ext.P(target=268, m=8))
print(blocks, shape, math.log2(cells), fin['bytes'])
