"""Select measured full-state DAG nodes. Uses mean unique-call steps, NOT occurrences."""
import argparse,collections,hashlib,json,struct
from pathlib import Path

def log_rows(n):return n.bit_length()  # mandatory padding row, even when n is a power of two

def main():
    p=argparse.ArgumentParser();p.add_argument('--dag-directory',required=True);p.add_argument('--output-directory',required=True);p.add_argument('--first-call',type=int,default=6320);p.add_argument('--call-count',type=int,default=5);p.add_argument('--fanout-bits',type=int,default=13);a=p.parse_args()
    src=Path(a.dag_directory);out=Path(a.output_directory);out.mkdir(parents=True,exist_ok=True)
    raw=(src/'compression-records.bin').read_bytes();calls=json.loads((src/'hash-call-map.json').read_text());chosen=calls[a.first_call:a.first_call+a.call_count];assert len(chosen)==a.call_count and a.call_count>0
    uses=[n for c in chosen for n in c['nodes']];ids=sorted(set(uses));base=ids[0];assert ids==list(range(base,base+len(ids))) and len(ids)<=25
    nodes=[]
    for node in ids:
        rec=raw[256*node:256*(node+1)];assert len(rec)==256
        initial=list(struct.unpack('>8Q',rec[:64]));block=list(rec[64:192]);final=list(struct.unpack('>8Q',rec[192:]));nodes.append(initial+block+final)
    counts=collections.Counter(uses);assert max(counts.values())<1<<a.fanout_bits
    config=dict(base=base,count=len(ids),fanout_bits=a.fanout_bits,nodes=nodes,uses=uses)
    (out/'config.json').write_text(json.dumps(config,separators=(',',':')))
    sweep=[]
    for count in range(1,13):
        cs=calls[a.first_call:a.first_call+count];ns=sorted(set(n for c in cs for n in c['nodes']));uc=sum(len(c['nodes']) for c in cs)
        cr=1<<log_rows(80*len(ns));nr=1<<log_rows(len(ns));ur=1<<log_rows(uc)
        # Baseline actual old batched per-call tables allow endpoint final active row.
        baseline=sum((1<<(80*len(c['nodes'])-1).bit_length())*5234+(1<<(len(c['nodes'])-1).bit_length())*1666 for c in cs)
        component=cr*5234+nr*(1666+178+a.fanout_bits)+ur*179
        sweep.append(dict(calls=count,unique_nodes=len(ns),declared_uses=uc,core_rows=cr,record_endpoint_rows=nr,use_rows=ur,core_endpoint_record_use_cells=component,independent_core_endpoint_cells=baseline,conservative_cell_saving=baseline-component,source_degree=cr*128))
    unique=collections.Counter(n for c in calls for n in c['nodes'])
    occurrence=collections.Counter()
    for c in calls:
        for node in c['nodes']:occurrence[node]+=c['frequency']
    workload=[]
    for cap in (6,12,25):
        groups=[]
        for start in range(0,len(raw)//256,cap):
            count=min(cap,len(raw)//256-start);u=sum(unique[i] for i in range(start,start+count));o=sum(occurrence[i] for i in range(start,start+count))
            cr=1<<log_rows(80*count);nr=1<<log_rows(count);ur=1<<log_rows(u)
            groups.append(dict(core=cr*5234,endpoint=nr*1666,records=nr*(178+a.fanout_bits),uses=ur*179,active_nodes=count,uses_count=u,occurrence_uses=o))
        workload.append(dict(chunk_capacity=cap,chunks=len(groups),source_cells_by_table={k:sum(g[k] for g in groups) for k in('core','endpoint','records','uses')},total_source_cells=sum(sum(g[k] for k in('core','endpoint','records','uses')) for g in groups),max_declared_use_rows=max(1<<log_rows(g['uses_count']) for g in groups),max_declared_uses=max(g['uses_count'] for g in groups),max_original_occurrence_uses=max(g['occurrence_uses'] for g in groups),all_within_node_and_use_profile=all(g['uses_count']<8192 for g in groups),declared_steps=sum(g['uses_count'] for g in groups),original_occurrence_steps=sum(g['occurrence_uses'] for g in groups)))
    report=dict(status='MEASURED_CONFIG',base=base,count=len(ids),fanout_bits=a.fanout_bits,declared_unique_call_step_uses=len(uses),original_call_occurrences=sum(c['frequency'] for c in chosen),original_occurrence_step_uses=sum(c['frequency']*len(c['nodes']) for c in chosen),actual_call_indices=list(range(a.first_call,a.first_call+a.call_count)),natural_fanouts=[counts[n] for n in ids],global_node_ids=ids,selected=sweep[a.call_count-1],sweep=sweep,full_workload_chunk_estimates=workload,records_sha256=hashlib.sha256(raw).hexdigest(),call_map_sha256=hashlib.sha256((src/'hash-call-map.json').read_bytes()).hexdigest(),scope='Compression certification only. Ordered use root must be externally fixed. No call padding/IV/digest provenance, cross-chunk coverage, aggregation, recursion, or cryptographic security claim. Independent baseline omits routing overhead, so positive savings are conservative for this component comparison; input traces and aux/proof work excluded on both sides.')
    (out/'selection.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
