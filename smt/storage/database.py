import os
import random
import sqlite3
from configparser import ConfigParser
from enum import Enum
from sqlite3 import Connection
from time import sleep
from typing import Optional, List, Tuple, Dict

from graphviz import Digraph
# from smt.interpreters.parser_base import Node
from smt.storage.node import Node


class Database:
    def __init__(self, config_file: 'str'):
        config = ConfigParser()
        config.read(config_file)
        self._db_name = config['DEFAULT']['DB_NAME']
        self._conn = None
        self._constrains_enforced = False

    @property
    def db_name(self) -> 'str':
        return self._db_name

    def _connection(self, constrains_enforced=True) -> 'Connection':
        while True:
            try:
                if self._conn is None:
                    self._conn = sqlite3.connect(self._db_name)
                    self._constrains(constrains_enforced)
                    self._constrains_enforced = constrains_enforced
                return self._conn
            except sqlite3.Error as e:
                print(e)
                sleep(1)

    def __del__(self):
        if self._conn:
            self._conn.close()

    def _constrains(self, enforced: 'bool'):
        switch = 'ON' if enforced else 'OFF'
        if self._constrains_enforced != enforced:
            self._conn.execute(f'PRAGMA foreign_keys = {switch};')

    def _init_db(self):
        conn = self._connection()
        conn.executescript('''
            -- STRUCTURE COMPONENTS--
            CREATE TABLE Root (
                id      INTEGER PRIMARY KEY AUTOINCREMENT,
                origin  INTEGER NOT NULL,
                substitution  INTEGER NULL,
                FOREIGN KEY(origin) REFERENCES Node(id) ON DELETE RESTRICT
                FOREIGN KEY(substitution) REFERENCES Substitution(id) ON DELETE RESTRICT
            );
            CREATE TABLE Node (
                id      INTEGER PRIMARY KEY AUTOINCREMENT,
                opcode  TEXT NOT NULL,
                -- value   INTEGER NOT NULL,
                hash    INTEGER UNIQUE NOT NULL
                -- ,var_hash    INTEGER NOT NULL UNIQUE            
            );
            CREATE TABLE Edge (
                id     INTEGER PRIMARY KEY AUTOINCREMENT,
                src    INTEGER NOT NULL,
                dst    INTEGER NOT NULL,
                priority INTEGER NULL,
                FOREIGN KEY(src) REFERENCES Node(id) ON DELETE CASCADE,
                FOREIGN KEY(dst) REFERENCES Node(id) ON DELETE CASCADE
            );
            CREATE TABLE Substitution (
                id      INTEGER PRIMARY KEY AUTOINCREMENT,
                old     INTEGER NOT NULL,
                new     INTEGER NOT NULL, -- TODO: CHECK old != new
                edge    INTEGER NULL,
                FOREIGN KEY(old) REFERENCES Node(id) ON DELETE RESTRICT,
                FOREIGN KEY(new) REFERENCES Node(id) ON DELETE RESTRICT,
                FOREIGN KEY(edge) REFERENCES Edge(id) ON DELETE RESTRICT
            );
        ''')

    def _create_edge(self, edge: 'Tuple[int,int]', priority=None, check_constraints=True) -> 'int':
        """
        :param edge: tuple of (source, destination)
        :param check_constraints: whether to check db constraints
        :return: id of inserted edge
        """
        sql = 'INSERT INTO Edge(src, dst, priority) VALUES(?, ?, ?);'
        conn = self._connection(check_constraints)

        cur = conn.cursor()
        cur.execute(sql, edge + (priority,))
        cur.close()
        return cur.lastrowid

    def _create_node(self, opcode: 'str', node_hash: 'int', check_constraints=True) -> 'int':
        """
        :param opcode: TODO: THINK ABOUT IT
        :param val:
        :return: id of inserted node
        """
        sql = 'INSERT INTO Node(opcode, hash) VALUES(?, ?);'
        conn = self._connection(check_constraints)

        cur = conn.cursor()
        cur.execute(sql, (opcode, node_hash))
        cur.close()
        return cur.lastrowid

    def _define_root(self, id: 'int') -> 'int':
        """
        Root is a link to the root node of the formula graph
        :param id: node id, that should be root of the formula graph
        :return: unique id of the formula
        """
        sqlInsertRoot = 'INSERT INTO Root(origin) VALUES(?);'
        conn = self._connection()

        cur = conn.cursor()
        cur.execute(sqlInsertRoot, (id,))
        cur.close()
        return cur.lastrowid

    def _contains(self, node_hash: 'int') -> 'Optional[int]':
        """
        Checks whether node with the hash supplied exists in the database
        :param node_hash: hash of the sub-graph of the node
        :return: id or None
        """
        conn = self._connection()
        sqlIdFromHash = 'SELECT id FROM Node WHERE hash = ?;'
        cur = conn.cursor()
        cur.execute(sqlIdFromHash, (node_hash,))
        row: 'List[Optional[int]]' = cur.fetchone()
        cur.close()
        if row:
            return row[0]

    def statistics(self) -> 'Tuple[int,int,int]':
        sqlStatistics = 'SELECT (SELECT COUNT(*) FROM Root), ' \
                        '(SELECT COUNT(*) FROM Edge),' \
                        '(SELECT COUNT(*) FROM Node);'
        conn = self._connection()
        cur = conn.cursor()
        cur.execute(sqlStatistics)
        n_roots, n_nodes, n_edges = cur.fetchone()
        cur.close()

        return n_roots, n_nodes, n_edges

    def _insert_node_if_not_exists(self, node: 'Node'):
        id = self._contains(node.tree_hash())
        if id:
            return id
        else:
            return self._create_node(node.opcode(), node.tree_hash())

    def _store_with_substitution(self, node: 'Node', original: 'int'):
        mapping: 'Dict[str,str]' = self._load_node(original).compare_graphs(node)

    def _create_substitution(self, old: 'int', new: 'int', edge_id: 'Optional[int]', constraints_enforced=False):
        sqlInsertSubstitution = 'INSERT INTO Substitution (old, new, edge) VALUES(?, ?, ?);'
        conn = self._connection(constraints_enforced)
        cur = conn.cursor()
        cur.execute(sqlInsertSubstitution, (old, new, edge_id))
        id = cur.lastrowid
        cur.close()
        return id

    def _create_root_substitution(self, old: 'int', new: 'int', root_id: 'int'):
        subst_id = self._create_substitution(old, new, None)
        sqlSetRootSubs = 'UPDATE Root SET substitution = ? WHERE id = ?;'
        conn = self._connection()
        cur = conn.cursor()
        cur.execute(sqlSetRootSubs, (subst_id, root_id))
        cur.close()
        return subst_id

    def _load_node(self, root: 'int', check_substitution=True) -> 'Node':
        nodes: 'Dict[int,Node]' = {}
        if check_substitution:
            stack = [(None, root, self._root_substitution(root))]
        else:
            stack = [(None, root, None)]

        while stack:
            parent_id, id, subst = stack.pop()
            opcode, = self._node_vals(id)
            if check_substitution and subst is not None:  # if there are substitutions to the node
                if id in subst:
                    subst_node_id = subst[id]
                    opcode, = self._node_vals(subst_node_id)

            commutative = True
            children = self._childeren_of(id)
            if children and children[0][1] is not None:
                sorted(children, key=lambda a: a[1])
                commutative = False

            for child in children:
                # child_id, child_priority, edge_id = child TODO!
                # subst = self._substitution_of(child[0])
                if check_substitution:
                    subst_dict = self._substitution_of(child[2])
                    if subst and subst_dict is not None:
                        subst = {**subst, **subst_dict}
                    elif subst is None:
                        subst = subst_dict

                stack.append((id, child[0], subst))
            node = Node(opcode, [], commutative=commutative)
            nodes.update({id: node})
            if parent_id is not None:
                nodes[parent_id].add_child(node)

        return nodes[root]

    def store(self, node: 'Node') -> 'int':
        try:
            node_exists: 'Optional[int]' = self._contains(node.tree_hash())
            if node_exists is not None:  # if same formula exists, we put it in the ShadowNode table and exist
                return self._define_root(node_exists)
            else:  # Otherwise we insert new node
                node_from = self._create_node(node.opcode(), node.tree_hash())
                root_id = self._define_root(node_from)

            priority: 'Optional[int]' = None if node.is_commutative() else 0

            i = 0
            stack = []
            for node in node.children():
                if priority is not None:
                    stack.append((node, node_from, i))
                    i += 1
                else:
                    stack.append((node, node_from, None))
            while stack:
                node, node_from, priority = stack.pop()

                node_exists = self._contains(node.tree_hash())
                if node_exists is not None:
                    self._create_edge((node_from, node_exists), priority)
                else:
                    node_to = self._create_node(node.opcode(), node.tree_hash())
                    self._create_edge((node_from, node_to), priority)

                    i = 0
                    commutative = node.is_commutative()
                    for child in node.children():
                        if commutative:
                            stack.append((child, node_to, None))
                        else:
                            stack.append((child, node_to, i))
                            i += 1
            return root_id
        except sqlite3.Error as e:
            print(e)

    def _childeren_of(self, node_id) -> 'List[Tuple[int,Optional[int]]]':
        sqlSelect = 'SELECT dst, priority, id FROM Edge WHERE src = ?;'
        conn = self._connection()
        cur = conn.cursor()
        cur.execute(sqlSelect, (node_id,))
        children = cur.fetchall()
        cur.close()

        return children  # [(dst, priority, id), ...]

    def _root_substitution(self, root_id: 'int') -> Optional[Dict[int, int]]:
        sqlSelectRootSubst = 'SELECT old, new FROM Substitution WHERE id = ' \
                             '(SELECT substitution FROM Root WHERE id = ?)'
        conn = self._connection()
        cur = conn.cursor()
        cur.execute(sqlSelectRootSubst, (root_id,))
        d: 'Dict[int,int]' = {}
        substitutions = cur.fetchall()
        if not substitutions:
            return None
        for s in substitutions:
            d.update({s[0]: s[1]})
        cur.close()

        return d

    def _substitution_of(self, edge_id: 'int') -> 'Optional[Dict[int,int]]':
        sqlSelectSubstitution = 'SELECT old, new FROM Substitution WHERE edge = ?;'
        conn = self._connection()
        cur = conn.cursor()
        cur.execute(sqlSelectSubstitution, (edge_id,))
        d: 'Dict[int,int]' = {}
        substitutions = cur.fetchall()
        if not substitutions:
            return None
        for s in substitutions:
            d.update({s[0]: s[1]})
        cur.close()

        return d

    def _node_vals(self, node_id):
        sqlSelect = 'SELECT opcode FROM Node WHERE id = ?;'
        conn = self._connection()
        cur = conn.cursor()
        cur.execute(sqlSelect, (node_id,))
        vals = cur.fetchone()
        cur.close()
        return vals

    def load(self, root_id: 'int') -> 'Optional[Node]':
        sqlSelect = 'SELECT origin FROM Root WHERE id = ?;'
        conn = self._connection()
        cur = conn.cursor()
        cur.execute(sqlSelect, (root_id,))
        row = cur.fetchone()
        cur.close()
        if not row:
            return None
        node_id, = row
        return self._load_node(node_id)

    # def _load_node_deprecated(self, node_id: 'int') -> 'Node':
    #     nodes: 'Dict[int,Node]' = {}
    #     stack: 'Tuple[Optional[int],int]' = [(None, node_id)]
    #
    #     while stack:
    #         parent_id, id = stack.pop()
    #         opcode, = self._node_vals(id)
    #
    #         commutative = True
    #         children = self._childeren_of(id)
    #         if children and children[0][1] is not None:
    #             sorted(children, key=lambda a: a[1])
    #             commutative = False
    #
    #         for child in children:
    #             stack.append((id, child[0]))
    #         node = Node(opcode, [], commutative=commutative)
    #         nodes.update({id: node})
    #         if parent_id is not None:
    #             nodes[parent_id].add_child(node)
    #
    #     return nodes[node_id]

    # def store(self, node: 'Node'):
    #     sv = SerializationVisitor()

    def _print_state(self):
        conn = self._connection()
        try:
            cur = conn.cursor()
            cur.execute('SELECT * FROM Node;')
            nodes = cur.fetchall()
            print(f'nodes: {nodes} - {len(nodes)} total')
            cur.execute('SELECT * FROM Edge;')
            edges = cur.fetchall()
            print(f'edges: {edges} - {len(edges)} total')
            # cur.execute('SELECT * FROM ShadowNode;')
            # print('shadow nodes:\n', cur.fetchall())
            cur.execute('SELECT * FROM Root;')
            print('root nodes:\n', cur.fetchall())
            cur.execute('SELECT * FROM Substitution;')
            print('substitutions:\n', cur.fetchall())
        except sqlite3.Error as e:
            print(e)

    def __str__(self) -> 'str':
        """
        Returns representation of formulas in database in dot format
        :return: graph in dot format
        """
        sqlNodes = 'SELECT Node.id AS id, opcode, Root.origin as root FROM Node LEFT JOIN Root on Root.origin = Node.id;'
        sqlEdges = 'SELECT src, dst, priority FROM Edge;'
        # sqlShadows = 'SELECT origin FROM ShadowNode;'
        conn = self._connection()
        cursor = conn.cursor()
        dot = Digraph('DB', comment='SQL graph representation')

        cursor.execute(sqlNodes)
        rows: 'List[List[int,int,Optional[int]]]' = cursor.fetchall()
        for row in rows:
            if row[2] is not None:
                dot.node(str(row[0]), str(row[1]).replace('\\', '\\\\').replace('"', '\\"'), color="red")
            else:
                dot.node(str(row[0]), str(row[1]).replace('\\', '\\\\').replace('"', '\\"'))

        cursor.execute(sqlEdges)
        rows: 'List[List[int,int,Optional[int]]]' = cursor.fetchall()
        for row in rows:
            if row[2] is not None:
                dot.edge(str(row[0]), str(row[1]), str(row[2]))
            else:
                dot.edge(str(row[0]), str(row[1]))

        # cursor.execute(sqlShadows)
        # rows: 'List[List[int]]' = cursor.fetchall()
        # if rows:
        #     dot.node("copy", color="grey")
        #     for row in rows:
        #         dot.edge("copy", str(row[0]), color="grey")

        return str(dot)


def calc_stat(node: 'Node') -> 'Tuple[int,int]':
    vertices = 0
    edges = 0
    stack = [node]
    while stack:
        node = stack.pop()
        vertices += 1
        edges += len(node.children())
        for child in node.children():
            stack.append(child)
    return vertices, edges


def test1(db: 'Database'):
    """
    (x*y) + (x*y) + (x*y)
    (x*y) + (y*x)
    expr1   vertices=10;    edges=9;
    expr2   vertices=7;     edges=6;
    total   vertices=17;    edges=15;
    stored  vertices=5;     edges=7;
    profit  3.4 times;      2.14 times.
    """
    x = Node('x')
    y = Node('y')
    mul_x_y = x * y
    mul_y_x = y * x
    assert mul_x_y.is_commutative() and mul_y_x.is_commutative()
    assert mul_y_x.tree_hash() == mul_x_y.tree_hash()

    expr1 = Node('+',
                 [mul_x_y, mul_x_y, mul_x_y],
                 commutative=True)
    expr2 = Node('+',
                 [mul_x_y, mul_y_x],
                 commutative=True)

    vertices, edges = calc_stat(expr1)
    expr1_id = db.store(expr1)
    print(f'stored expr1 id={expr1_id};'
          f' vertices={vertices}; edges={edges};')

    vertices, edges = calc_stat(expr2)
    expr2_id = db.store(expr2)
    print(f'stored expr2 id={expr2_id};'
          f' vertices={vertices}; edges={edges};')

    db._print_state()
    print(db)

    print(f'expr1: '
          f'hash={expr1.tree_hash()}; '
          f'db_hash={db.load(expr1_id).tree_hash()}')
    assert expr1.tree_hash() == db.load(expr1_id).tree_hash()
    print(f'expr2: '
          f'hash={expr2.tree_hash()}; '
          f'db_hash={db.load(expr2_id).tree_hash()}')
    assert expr2.tree_hash() == db.load(expr2_id).tree_hash()


def test2(db: 'Database'):
    """
    (((x * y) * x) * x) * x
    """
    x = Node('x')
    y = Node('y')
    mul_x_y = Node('*', [x, y], commutative=True)
    lvl1 = Node('*', [mul_x_y, x], commutative=True)
    lvl2 = Node('*', [lvl1, x], commutative=True)
    expr = Node('*', [lvl2, x], commutative=True)

    vertices, edges = calc_stat(expr)
    expr_id = db.store(expr)
    print(f'stored expr1 id={expr_id};'
          f' vertices={vertices}; edges={edges};')

    db._print_state()
    print(db)

    print(f'expr: '
          f'hash={expr.tree_hash()}; '
          f'db_hash={db.load(expr_id).tree_hash()}')
    assert expr.tree_hash() == db.load(expr_id).tree_hash()


def test3(db: 'Database'):
    """
    (x+y) ^ (y+x) ^ (x-y) ^ (y-x)
    """
    x = Node('x')
    y = Node('y')
    add_x_y = Node('+', [x, y], commutative=True)
    sub_x_y = Node('-', [x, y], commutative=False)
    add_y_x = Node('+', [y, x], commutative=True)
    sub_y_x = Node('-', [y, x], commutative=False)
    assert sub_x_y.tree_hash() != sub_y_x.tree_hash()

    expr = Node('^', [add_x_y, add_y_x, sub_y_x, sub_x_y], commutative=True)

    vertices, edges = calc_stat(expr)
    expr_id = db.store(expr)
    print(f'stored expr1 id={expr_id};'
          f' vertices={vertices}; edges={edges};')

    db._print_state()
    print(db)

    print(f'expr: '
          f'hash={expr.tree_hash()}; '
          f'db_hash={db.load(expr_id).tree_hash()}')
    assert expr.tree_hash() == db.load(expr_id).tree_hash()


def test4(db: 'Database'):
    x = Node('x')
    y = Node('y')
    f = Node('f', [x, y], commutative=True)
    g = Node('g', [f, Node('+', [f, x])])

    vertices, edges = calc_stat(g)
    g_id = db.store(g)
    print(f'stored expr1 id={g_id};'
          f' vertices={vertices}; edges={edges};')

    db._print_state()
    print(db)

    assert g.tree_hash() == db.load(g_id).tree_hash()


class Type(Enum):
    VARIABLE = 0
    OPERATION = 1


def gen_random_node(node_t: 'Type') -> 'Node':
    operations = (('+', True), ('-', False), ('*', True), ('\\', False))
    variables = ('x', 'y', 'z', 'a', 'b', 'c')
    if node_t == Type.OPERATION:
        opcode, commutative = random.choice(operations)
        return Node(opcode, [], commutative=commutative)
    elif node_t == Type.VARIABLE:
        opcode = random.choice(variables)
        return Node(opcode, [], variable=True)


def gen_random_graph(node_count: 'int'):
    node_type = random.choice([Type.OPERATION])
    root = gen_random_node(node_type)
    stack = [root]
    counter = 0
    while stack:
        node = stack.pop()
        counter += 1
        if node_type == Type.VARIABLE:
            pass
        elif node_type == Type.OPERATION:
            if len(stack) + counter < node_count:
                child_a = gen_random_node(random.choice([Type.VARIABLE, Type.OPERATION]))
                child_b = gen_random_node(random.choice([Type.VARIABLE, Type.OPERATION]))
            else:
                child_a = gen_random_node(Type.VARIABLE)
                child_b = gen_random_node(Type.VARIABLE)
            if not child_a.is_variable():
                stack.append(child_a)
            if not child_b.is_variable():
                stack.append(child_b)
            node.add_child(child_a)
            node.add_child(child_b)
    return root


def testEq(db: 'Database'):
    x = Node('x', variable=True)
    y = Node('y', variable=True)

    div_x_y = Node('\\', [x, y])
    div_y_x = Node('\\', [y, x])

    print(div_x_y.compare_graphs(div_y_x))


ORIG_NODES = 0
ORIG_EDGES = 0


def test(db: 'Database', node: 'Node'):
    """
    Asserts that hash of the node provided does not change after serialization to database
    :param db: database, where node should be stored
    :param node: node to store
    :return: method could fail with assertion error
    """
    global ORIG_EDGES, ORIG_NODES
    db_roots_before, db_edges_before, db_nodes_before = db.statistics()
    store_id = db.store(node)
    db_roots_after, db_edges_after, db_nodes_after = db.statistics()
    db_roots_delta = db_roots_after - db_roots_before
    assert db_roots_delta == 1
    db_edges_delta = db_edges_after - db_edges_before
    db_nodes_delta = db_nodes_after - db_nodes_before
    assert node.tree_hash() == db.load(store_id).tree_hash()
    print('TEST PASSED')
    orig_vertices, orig_edges = calc_stat(node)
    ORIG_NODES += orig_vertices
    ORIG_EDGES += orig_edges
    print(f'Origin\tvertices={orig_vertices};\tedges={orig_edges};')
    print(f'Stored\tvertices={db_nodes_delta};\tedges={db_edges_delta};')
    if orig_edges:
        print(f'Edge compression: {db_edges_delta / orig_edges}')
    if orig_vertices:
        print(f'Node compression: {db_nodes_delta / orig_vertices}')


def test_random_node(db) -> 'Node':
    rnd_node = gen_random_graph(100)
    # print(rnd_node.graphviz())
    test(db, rnd_node)
    # db._print_state()
    # print(db)
    return rnd_node


def test_subst(db: 'Database'):
    x = Node('x', variable=True)
    y = Node('y', variable=True)
    db.store(Node('z', [], variable=True))
    add_x_y = Node('*', [Node('+', [x, y], commutative=True), Node('x', [], variable=True)])

    db_id = db.store(add_x_y)
    db._create_substitution(3, 1, 1)
    # db._create_substitution(3, 1, 2)
    # db._create_substitution(3, 1, 3)
    db._create_substitution(3, 1, 2)
    db._create_root_substitution(1, 2, db_id)
    print(1, db._substitution_of(1))
    db._print_state()
    print('INITIAL_NODE:', add_x_y.graphviz())
    db_node = db.load(db_id)
    assert add_x_y.tree_hash() != db_node.tree_hash()
    print('DB_NODE:\n', db_node.graphviz())


if __name__ == '__main__':
    os.system("rm smt.db")  # DEBUG ONLY! TODO: remove
    db = Database('db.config')
    db._init_db()

    test_subst(db)
    # test1(db)
    # test2(db)
    # test3(db)
    # test4(db)
    # testEq(db)
    # formulas = ''
    # for i in range(1000):
    #     node = test_random_node(db)
    #     formulas += node.graphviz() + '\n'
    # print('ORIG TOTAL', ORIG_NODES, ORIG_EDGES)
    # print(db.statistics())
    db._print_state()
    #
    # print(formulas)
    print(db)
    f = open('db_state.dot', 'w')
    f.write(str(db))
    f.close()
