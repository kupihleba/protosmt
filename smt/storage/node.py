import sys
from typing import List, Optional, Dict
from graphviz import Digraph


class Node:
    def __init__(self, opcode: 'str', children: 'List[Node]' = (), commutative: 'bool' = False, variable=False):
        self._opcode = opcode
        self._children = children
        self._commutative = commutative
        self._variable = variable

    def children(self) -> 'List[Node]':
        return self._children

    def opcode(self) -> 'str':
        return self._opcode

    def is_variable(self) -> 'bool':
        return self._variable

    def add_child(self, child: 'Node'):
        self._children.append(child)

    def compare_graphs(self, node: 'Node') -> 'Optional[Dict[str,str]]':
        """
        Function tries to find isomorphism of graphs
        :param node: graph to map to
        :return: mapping of a to b
        """
        stack_a: 'List[Node]' = [node]
        stack_b: 'List[Node]' = [self]
        mapping: 'Dict[str,str]' = {}  # maps variable names

        while stack_a or stack_b:
            if (not stack_a) or (not stack_b):  # if graphs have different length
                return None
            a = stack_a.pop()
            b = stack_b.pop()
            if a.tree_hash() == b.tree_hash():  # if hashes are the same
                continue  # pass child checks
            if a.is_variable() and b.is_variable():
                if a.opcode() in mapping:  # if variable mapping exists
                    if b.opcode() != mapping[a.opcode()]:  # if mapping mismatch
                        return None
                else:
                    mapping.update({a.opcode(): b.opcode()})  # add new mapping
            elif a.is_variable() or b.is_variable():  # if node type is different
                return None
            elif a.opcode() != b.opcode():
                return None
            # Check children
            children_a = a.children()
            children_b = b.children()
            if len(children_a) != len(children_b):
                return None
            if node.is_commutative():
                raise NotImplemented('Commutative nodes are too complex to examine!')
            else:
                for child_a in children_a:
                    stack_a.append(child_a)
                for child_b in children_b:
                    stack_b.append(child_b)

        return mapping

    def compare_graphs_in_db(self, db, node: 'Node') -> 'Optional[Dict[int,int]]':
        """
        Function tries to find isomorphism of graphs
        :param node: graph to map to
        :return: mapping of a to b
        """
        stack_a: 'List[Node]' = [node]
        stack_b: 'List[Node]' = [self]
        mapping: 'Dict[int,int]' = {}  # maps node ids

        while stack_a or stack_b:
            if (not stack_a) or (not stack_b):  # if graphs have different length
                return None
            a = stack_a.pop()
            a_id = db._insert_node_if_not_exists(a)
            b_id = db._insert_node_if_not_exists(b)
            b = stack_b.pop()
            if a.tree_hash() == b.tree_hash():  # if hashes are the same
                continue  # pass child checks
            if a.is_variable() and b.is_variable():
                if db._insert_node_if_not_exists(a) in mapping:  # if variable mapping exists
                    if b.opcode() != mapping[a.opcode()]:  # if mapping mismatch
                        return None
                else:
                    mapping.update({a.opcode(): b.opcode()})  # add new mapping
            elif a.is_variable() or b.is_variable():  # if node type is different
                return None
            elif a.opcode() != b.opcode():
                return None
            # Check children
            children_a = a.children()
            children_b = b.children()
            if len(children_a) != len(children_b):
                return None
            if node.is_commutative():
                raise NotImplemented('Commutative nodes are too complex to examine!')
            else:
                for child_a in children_a:
                    stack_a.append(child_a)
                for child_b in children_b:
                    stack_b.append(child_b)

        return mapping

    def __str__(self) -> 'str':
        return f'Node({self._opcode}, {self._children}, com={self._commutative})'

    def graphviz(self) -> 'str':
        """
        Builds node graph representation in dot format
        :return: dot graph of the node
        """
        dot = Digraph('Node', comment='Node graph')

        stack = [(self, None)]
        while stack:
            node, parent_id = stack.pop()
            color = 'blue' if node._variable else 'black'
            shape = 'oval' if node._commutative else 'rect'
            id = hash(node)
            dot.node(str(id), node._opcode.replace('\\', '\\\\').replace('"', '\\"'),
                     color=color, shape=shape)
            if parent_id is not None:
                dot.edge(str(parent_id), str(id))
            for child in node.children():
                stack.append((child, id))

        return str(dot)

    def is_commutative(self) -> 'bool':
        return self._commutative

    def tree_hash(self):
        res_hash = hash(self._opcode)
        for child in self._children:
            if self._commutative:
                res_hash = (res_hash + child.tree_hash()) % sys.maxsize
            else:
                res_hash = hash((res_hash, child.tree_hash()))
        return res_hash

    def __mul__(self, other):
        return Node('*', [self, other], commutative=True)

    def __add__(self, other):
        return Node('+', [self, other], commutative=True)

    def __sub__(self, other):
        return Node('-', [self, other])

    def __divmod__(self, other):
        return Node('\\', [self, other])
