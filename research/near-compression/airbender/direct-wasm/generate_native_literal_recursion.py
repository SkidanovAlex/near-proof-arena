import sys,json,struct,hashlib,argparse
from pathlib import Path
R=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(R/'airbender/direct-wasm'))
import prepared_code_table_air as lit
ap=argparse.ArgumentParser()
ap.add_argument('--out',type=Path,default=R/'results/native-literal-recursion')
ap.add_argument('--fixture',type=Path,help='Actual Lean prepare/step fixture; default retains the original193 regression checks')
ap.add_argument('--packed-bytes',action='store_true');ap.add_argument('--no-install',action='store_true')
args=ap.parse_args();out=args.out.resolve();out.mkdir(exist_ok=True)
case=json.loads((args.fixture or R/'results/native-literal-recursion/fixture.json').read_text())
spec,rows=lit.make(case)
if args.fixture is None:
 ret=json.loads((R/'results/pq384-code-table-long193/statement.json').read_text())
 assert spec['air']==ret['spec']['air'] and spec['public']==ret['spec']['public']
 assert {k:case[k] for k in ['wasm_bytes','method','prepaid']}==json.loads((R/'results/pq384-code-table-long193/request.json').read_text())
code_count_column=lit.COUNT
if args.packed_bytes:
 from packed_byte_air import transform
 spec,rows,packing=transform(spec,rows);code_count_column=packing['code_count_column']
 (out/'packing.json').write_text(json.dumps(packing,indent=2)+'\n')
(out/'fixture.json').write_text(json.dumps(case))
(out/'spec.json').write_text(json.dumps(spec))
for i,table in enumerate(rows):
 (out/f'rows-{i}.bin').write_bytes(b''.join(struct.pack('<I',v) for row in table for v in row))
(out/'public.bin').write_bytes(b''.join(struct.pack('<I',v) for v in spec['public']))
s=['use super::*;','use p3_air::{Air, AirBuilderWithPublicValues, BaseAir, BaseAirWithPublicValues};','use p3_field::PrimeCharacteristicRing;','use p3_matrix::{Matrix,dense::RowMajorMatrix};','use openvm_stark_backend::{PartitionedBaseAir, interaction::InteractionBuilder, prover::{ColMajorMatrix,CpuColMajorBackend}};']
s.append(Path(__file__).with_name('native_literal_eval.rs').read_text())
for ti,table in enumerate(spec['air']['tables']):
 name=f'Literal{ti}'
 s += [f'struct {name};', f'impl<F> BaseAir<F> for {name} {{ fn width(&self)->usize {{{table["width"]}}} }}',f'impl<F> PartitionedBaseAir<F> for {name} {{}}',f'impl<F> BaseAirWithPublicValues<F> for {name} {{ fn num_public_values(&self)->usize {{{len(spec["public"]) if ti==0 else 0}}} }}',f'impl<AB: AirBuilderWithPublicValues + InteractionBuilder> Air<AB> for {name} {{ fn eval(&self,builder:&mut AB) {{','let main=builder.main(); let local=main.row_slice(0).unwrap(); let next=main.row_slice(1).unwrap(); let public=builder.public_values().to_vec();']
 intern={};defs=[];start=len(s)
 def index(x):
  key=json.dumps(x)
  if key in intern:return intern[key]
  tag=x[0]
  if tag=='c':val=f'N::C({x[1]})'
  elif tag=='v':val=f'N::V({x[1]},{str(bool(x[2])).lower()})'
  elif tag=='p':val=f'N::P({x[1]})'
  elif tag in ['first','last','trans']:val={'first':'N::First','last':'N::Last','trans':'N::Trans'}[tag]
  elif tag=='-':val=f'N::Neg({index(x[1])})'
  else:val=f'N::{ {"+":"Add","*":"Mul"}[tag]}({index(x[1])},{index(x[2])})'
  n=len(intern);intern[key]=n;defs.append(val);return n
 def e(x):return f'e[{index(x)}].clone()'
 constraints=[index(x) for x in table['constraints']]
 s.append('for i in ['+','.join(map(str,constraints))+'] {builder.assert_zero(e[i].clone());}')
 for it in table['interactions']:
  fields=', '.join(e(x) for x in it['msg'])
  # Source multiplicities are little-endian bits.
  count=' + '.join(f'({e(x)} * AB::F::from_u32({1<<j}))' for j,x in enumerate(it['mult']))
  weight=(1<<len(it['mult']))-1
  if ti==1 and it['bus']==2:
   bits=spec['log_rows'][0]+1
   for j in range(bits,25):s.append(f'builder.assert_zero(local[{code_count_column+j}]);')
   weight=(1<<bits)-1
  if not it['send']:count=f'-({count})'
  s.append(f'builder.push_interaction({it["bus"]},vec![{fields}],{count},{weight});')
 if ti==0:
  for j,v in enumerate(spec['public'][:12]):s.append(f'builder.assert_eq(public[{j}],AB::F::from_u32({v}));')
  for seg in spec['air']['pubSegs']:
   assert seg['prefix']==[] and seg['indexBase'] is None and seg['startAt'] is None and not seg['send']
   count=sum(spec['public'][seg['countAt']+j]<<(8*j) for j in range(4))
   s.append(f'for row in 0..{count} {{ let start={seg["start"]}+row*{seg["width"]}; let first=builder.is_first_row(); builder.push_interaction({seg["bus"]}, public[start..start+{seg["width"]}].to_vec(),-first,1); }}')
 s.insert(start,'let e=eval_nodes(builder,&['+',\n'.join(defs)+']);')
 s+=['}}']
s+=['struct LiteralFixture;','impl TestFixture<BabyBearPoseidon2Config> for LiteralFixture {', 'fn airs(&self)->Vec<AirRef<BabyBearPoseidon2Config>> {vec!['+','.join(f'Arc::new(Literal{i})' for i in range(len(rows)))+']}', 'fn generate_proving_ctx(&self)->ProvingContext<CpuColMajorBackend<BabyBearPoseidon2Config>> {', 'use p3_baby_bear::BabyBear;', 'fn read(p:&str)->Vec<BabyBear> { std::fs::read(p).unwrap().chunks_exact(4).map(|x|BabyBear::from_u32(u32::from_le_bytes(x.try_into().unwrap()))).collect() }','let dir=std::env::var("NEARPROOF_LITERAL_OUT").unwrap(); let public=read(&format!("{dir}/public.bin"));', 'ProvingContext::new(vec![']
for i,table in enumerate(rows):s.append(f'({i},AirProvingContext::simple(ColMajorMatrix::from_row_major(&RowMajorMatrix::new(read(&format!("{{dir}}/rows-{i}.bin")),{len(table[0])})), {"public" if i==0 else "vec![]"})),')
s+=[']) }}','#[test] fn nearproof_literal_slice_recursion() {','let mut params=test_system_params_small(2,16,3); params.max_constraint_degree=8;','let child=BabyBearPoseidon2CpuEngine::<DuplexSponge>::new(params);','let parent=test_engine_small();','run_test::<1,_>(LiteralFixture,&child,&parent,1);','}']
s=s[:s.index('#[test] fn nearproof_literal_slice_recursion() {')]
source='\n'.join(s)+'\n'+Path(__file__).with_name('native_literal_driver.rs').read_text()
(out/'native_literal.rs').write_text(source)
if not args.no_install:Path('/tmp/nearproof-openvm/crates/recursion/src/native_literal.rs').write_text(source)
if not args.no_install:
 p=Path('/tmp/nearproof-openvm/crates/recursion/src/tests.rs');t=p.read_text();mark='#[path = "native_literal.rs"]\nmod native_literal;\n'
 if mark not in t:p.write_text(mark+t)
print('generated',len(source),'bytes',len(s),'lines')
