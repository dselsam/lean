#!/usr/bin/env python3

import os
import re
import sys
import json
import networkx as nx
from networkx.drawing.nx_pydot import write_dot
import matplotlib.pyplot as plt

cls_blacklist = ['has_sizeof', 'has_coe']
data = open(sys.argv[1]).read()
data = re.sub(r',\s*\]', ']', data)
data = json.load(data)

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

base = os.path.splitext(sys.argv[1])[0]
write_cls_inst_graph(base + '.dot')
write_cls_graph(base + '-classes.dot')
write_coe_graph(base + '-coercions.dot')
