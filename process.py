#!/usr/bin/env python3

import os
import re
import sys
import json
import networkx as nx
from networkx.drawing.nx_pydot import write_dot
import matplotlib.pyplot as plt

cls_blacklist = ['has_sizeof', 'has_coe', 'reflected']
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
        if d['kind'] == 'class':
            G.add_node(d['name'], shape = 'box')
        elif d['kind'] == 'instance' and d['class'] not in cls_blacklist:
            cls_params = [p for p in d['params'] if 'class' in p]
            if len(cls_params) == 1:
                G.add_edge(cls_params[0]['class'], d['class'])
    write_dot(G, f)

def write_lean3(f):
    f = open(f, 'w')
    print("noncomputable theory", file=f)
    print("namespace test", file=f)
    i = 0
    for d in data:
        if d['kind'] == 'class':
            print("class {{{uparams}}} {name} {params} := mk ( )".format(
                uparams=' '.join(d['uparams']),
                name=d['name'],
                params=' '.join(f"({p['name']} : {p['type']})" for p in d['params'])
            ), file=f)
        elif d['kind'] == 'instance':
            print("@[instance] constant {{{uparams}}} {name} {params} : {type}".format(
                uparams=' '.join(d['uparams']),
                name=d['name'],
                params=' '.join(f"{'[' if 'class' in p else '('}{p['name']} : {p['type']}{']' if 'class' in p else ')'}" for p in d['params']),
                type=d['type']
            ), file=f)
        elif d['kind'] == 'problem' and d['class'] not in cls_blacklist:
            i += 1
            print(f"def {{{' '.join(d['uparams'])}}} p{i} : {d['type']} := infer_instance", file=f)
        elif d['kind'] == 'dep':
            print(f"constant {{{' '.join(d['uparams'])}}} {d['name']} : {d['type']}", file=f)
    print("end test", file=f)

def write_lean4(f):
    f = open(f, 'w')
    print("namespace test", file=f)
    i = 0
    def pt(t):
        return re.sub(r'\.\{(?!max)([^(} ]+( [^} ]+)*)\}', lambda m: f".{{{', '.join(m[1].split(' '))}}}", t.replace("Pi ", "forall "))
    for d in data:
        uparams = "" if len(d['uparams']) == 0 else f".{{{', '.join(d['uparams'])}}}"
        if d['kind'] == 'class':
            print("class {name}{uparams} {params}".format(
                uparams=uparams,
                name=d['name'],
                params=' '.join(f"({p['name']} : {pt(p['type'])})" for p in d['params'])
            ), file=f)
        elif d['kind'] == 'instance':
            print("@[instance] axiom {name}{uparams} {params} : {type}".format(
                uparams=uparams,
                name=d['name'],
                params=' '.join(f"{'[' if 'class' in p else '('}{p['name']} : {pt(p['type'])}{']' if 'class' in p else ')'}" for p in d['params']),
                type=pt(d['type'])
            ), file=f)
        elif d['kind'] == 'problem' and d['class'] not in cls_blacklist:
            i += 1
            print(f"#synth {pt(d['type'])}", file=f)
        elif d['kind'] == 'dep':
            print(f"axiom {d['name']}{uparams} : {pt(d['type'])}", file=f)
    print("end test", file=f)

base = os.path.splitext(sys.argv[1])[0]
write_cls_inst_graph(base + '.dot')
write_cls_graph(base + '-classes.dot')
write_coe_graph(base + '-coercions.dot')
write_lean3(base + '.lean')
write_lean4(base + '4.lean')
