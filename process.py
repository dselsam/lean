#!/usr/bin/env python3

import os
import re
import sys
import json
import networkx as nx
from networkx.drawing.nx_pydot import write_dot
import networkx
import matplotlib.pyplot as plt

cls_blacklist = ['reflected', 'cau_seq.is_complete', 'directed_system', 'module.directed_system']
data = open(sys.argv[1]).read()
data = re.sub(r',\s*([]}])', '\1', data)
data = json.loads(data)['items']

def write_cls_inst_graph(f):
    G = nx.DiGraph()
    for d in data:
        if d['kind'] == 'class':
            G.add_node(d['name'], shape = 'box')
        elif d['kind'] == 'instance' and d['class'] not in cls_blacklist:
            G.add_edge(d['name'], d['class'])
            for p in d['params']:
                if 'class' in p:
                    G.add_edge(p['class'], d['name'])
    write_dot(G, f)

def write_cls_graph(f):
    G = nx.DiGraph()
    for d in data:
        if d['kind'] == 'class':
            G.add_node(d['name'], shape = 'box')
        elif d['kind'] == 'instance' and d['class'] not in cls_blacklist:
            for p in d['params']:
                if 'class' in p:
                    G.add_edge(p['class'], d['class'])
    write_dot(G, f)

def write_coe_graph(f):
    G = nx.DiGraph()
    for d in data:
        #if d['kind'] == 'class':
        #    G.add_node(d['name'], shape = 'box')
        if d['kind'] == 'instance' and d['class'] not in cls_blacklist and d['coercion_like'] == 1:
            cls_params = [p for p in d['params'] if 'class' in p]
            if len(cls_params) >= 1:
                G.add_node(cls_params[-1]['class'], shape = 'box')
                #print(d['name'])
                G.add_node(d['class'], shape = 'box')
                G.add_edge(cls_params[0]['class'], d['class'])
    write_dot(G, f)

def write_pruned_coe_graph(f):
    G = nx.DiGraph()
    for d in data:
        #if d['kind'] == 'class':
        #    G.add_node(d['name'], shape = 'box')
        if d['kind'] == 'instance' and d['class'] not in cls_blacklist and d['coercion_like'] == 1:
            cls_params = [p for p in d['params'] if 'class' in p]
            if len(cls_params) >= 1:
                G.add_node(cls_params[-1]['class'], shape = 'box')
                #print(d['name'])
                G.add_node(d['class'], shape = 'box')
                G.add_edge(cls_params[0]['class'], d['class'])
    print(f"{len(G)} nodes, {len(G.edges)} edges")
    n, m, l = max(((n, m, len(list(nx.algorithms.simple_paths.all_simple_paths(G, n, m))))
                  for n in G for m in G),
                   key = lambda p: p[2])
    print(f"{l} paths from {n} to {m}")
    all_nodes_in_max_path = set()
    for path in nx.algorithms.simple_paths.all_simple_paths(G, n, m):
        for p in path:
            all_nodes_in_max_path.add(p)
    H = networkx.restricted_view(G, list(set(G.nodes) - all_nodes_in_max_path), [])
    write_dot(H, f)

def write_lean3(f):
    f = open(f, 'w')
    print("noncomputable theory", file=f)
    print("namespace test", file=f)
    i = 0
    for d in data:
        if d['kind'] == 'class' and d['name'] not in cls_blacklist:
            if not d.get('params'): # ??
                continue
            print("class {name} {params}".format(
                name=d['name'],
                params=' '.join(f"[{p['name']} : {p['type']}]" if 'class' in p else f"({p['name']} : Type)" for p in d['params'])
            ), file=f)
        elif d['kind'] == 'instance' and d['is_simple'] == 1 and d['class'] not in cls_blacklist:
            print("@[instance] constant {name} {params} : {type}".format(
                name=d['name'],
                params=' '.join(f"[{p['name']} : {p['type']}]" if 'class' in p else f"({p['name']} : Type)" for p in d['params']),
                type=d['type']
            ), file=f)
        #elif d['kind'] == 'problem' and d['class'] not in cls_blacklist:
        #    i += 1
        #    print(f"def {{{' '.join(d['uparams'])}}} p{i} : {d['type']} := infer_instance", file=f)
        #elif d['kind'] == 'dep':
        #    print(f"constant {{{' '.join(d['uparams'])}}} {d['name']} : {d['type']}", file=f)
    print("end test", file=f)

def write_lean4(f):
    f = open(f, 'w')
    print("namespace test", file=f)
    i = 0
    def pt(t):
        return re.sub(r'\.\{(?!max)([^(} ]+( [^} ]+)*)\}', lambda m: f".{{{', '.join(m[1].split(' '))}}}", t.replace("Pi ", "forall "))
    for d in data:
        if not d.get('params'): # ??
            continue
        if d['kind'] == 'class' and d['name'] not in cls_blacklist:
            print("class {name} {params} := (u:Unit:=())".format(
                name=d['name'],
                params=' '.join(f"[{p['name']} : {p['type']}]" if 'class' in p else f"({p['name']} : Type)" for p in d['params'])
            ), file=f)
        elif d['kind'] == 'instance' and d['is_simple'] == 1 and d['class'] not in cls_blacklist:
            print("@[instance] def {name} {params} : {type} := {{}}".format(
                name=d['name'],
                params=' '.join(f"[{p['name']} : {p['type']}]" if 'class' in p else f"({p['name']} : Type)" for p in d['params']),
                type=d['type']
            ), file=f)
        #elif d['kind'] == 'problem' and d['class'] not in cls_blacklist:
        #    i += 1
        #    print(f"#synth {pt(d['type'])}", file=f)
        #elif d['kind'] == 'dep':
        #    print(f"axiom {d['name']}{uparams} : {pt(d['type'])}", file=f)
    print("end test", file=f)

def write_coq(f):
    f = open(f, 'w')
    for d in data:
        def fix(s):
            return re.sub(r'\.(?=\w)', '_', s)
        if not d.get('params'): # ??
            continue
        if d['kind'] == 'class' and d['name'] not in cls_blacklist:
            print(fix("Class {name} {params} : Set.".format(
                name=d['name'],
                params=' '.join(f"`({p['name']} : {p['type']})" if 'class' in p else f"({p['name']} : Set)" for p in d['params'])
            )), file=f)
        elif d['kind'] == 'instance' and d['is_simple'] == 1 and d['class'] not in cls_blacklist:
            print(fix("Instance {name} {params} : {type} := {{}}.".format(
                name=d['name'],
                params=' '.join(f"`({p['name']} : {p['type']})" if 'class' in p else f"({p['name']} : Set)" for p in d['params']),
                type=d['type']
            )), file=f)

base = os.path.splitext(sys.argv[1])[0]
write_cls_inst_graph(base + '.dot')
write_cls_graph(base + '-classes.dot')
write_coe_graph(base + '-coercions.dot')
write_pruned_coe_graph(base + '-pruned-coercions.dot')
write_lean3(base + '.lean')
write_lean4(base + '4.lean')
write_coq(base + '.v')
