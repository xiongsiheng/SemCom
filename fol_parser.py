import re
import sys
from itertools import permutations
import nltk
import numpy as np
import itertools
import os

def all_exists(*args):
    return all(e is not None for e in args)


def any_exists(*args):
    return any(e is not None for e in args)


# TODO inefficient
op_ls = ['⊕', '∨', '∧', '→', '↔', '∀', '∃', '¬', '(', ')', ',']

sym_reg = re.compile(r'[^⊕∨∧→↔∀∃¬(),]+')

cfg_template = """
S -> F | Q F
Q -> QUANT VAR | QUANT VAR Q
F -> '¬' '(' F ')' | '(' F ')' | F OP F | L
OP -> '⊕' | '∨' | '∧' | '→' | '↔'
L -> '¬' PRED '(' TERMS ')' | PRED '(' TERMS ')'
TERMS -> TERM | TERM ',' TERMS
TERM -> CONST | VAR
QUANT -> '∀' | '∃'
"""

# used in perturbation
last_nt_nodes = set(['PRED', 'OP', 'CONST', 'VAR', 'QUANT'])
# used in node insertion
insertable_nt_nodes = set(['Q', 'S', 'TERMS', 'F'])
# used in node deletion
deleteable_nt_nodes = set(['Q', 'TERMS', 'F', 'L'])

def parse_text_FOL_to_tree(rule_str):
    """
        Parse a text FOL rule into nltk.tree
        
        Returns: nltk.tree, or None if the parse fails
    """
    rule_str = reorder_quantifiers(rule_str)
    
    r, parsed_fol_str = msplit(rule_str)
    cfg_str = make_cfg_str(r)

    grammar = nltk.CFG.fromstring(cfg_str)
    parser = nltk.ChartParser(grammar)
    tree = parser.parse_one(r)
    
    return tree


def reorder_quantifiers(rule_str):
    matches = re.findall(r'[∃∀]\w', rule_str)
    for match in matches[::-1]:
        rule_str = '%s ' % match + rule_str.replace(match, '', 1)
    return rule_str


def msplit(s):
    for op in op_ls:
        s = s.replace(op, ' %s ' % op)
    r = [e.strip() for e in s.split()]
    #remove ' from the string if it contains any: this causes error in nltk cfg parsing
    r = [e.replace('\'', '') for e in r]
    r = [e for e in r if e != '']
    
    # deal with symbols with spaces like "dc universe" and turn it to "DcUniverse"
    res = []
    cur_str_ls = []
    for e in r:
        if (len(e) > 1) and sym_reg.match(e):            
            cur_str_ls.append(e[0].upper() + e[1:])            
        else:
            if len(cur_str_ls) > 0:
                res.extend([''.join(cur_str_ls), e])
            else:
                res.extend([e])
            cur_str_ls = []
    if len(cur_str_ls) > 0:
        res.append(''.join(cur_str_ls))
    
    # re-generate the FOL string
    make_str_ls = []
    for ind, e in enumerate(r):
        if re.match(r'[⊕∨∧→↔]', e):
            make_str_ls.append(' %s ' % e)
        elif re.match(r',', e):
            make_str_ls.append('%s ' % e)
        # a logical variable
        elif (len(e) == 1) and re.match(r'\w', e):
            if ((ind - 1) >= 0) and ((r[ind-1] == '∃') or (r[ind-1] == '∀')):
                make_str_ls.append('%s ' % e)
            else:
                make_str_ls.append(e)
        else:
            make_str_ls.append(e)
    
    return res, ''.join(make_str_ls)


def make_cfg_str(token_ls):
    """
    NOTE: since nltk does not support reg strs like \w+, we cannot separately recognize VAR, PRED, and CONST.
    Instead, we first allow VAR, PRED, and CONST to be matched with all symbols found in the FOL; once the tree is
    parsered, we then go back and figure out the exact type of each symbols
    """
    sym_ls = list(set([e for e in token_ls if sym_reg.match(e)]))
    sym_str = ' | '.join(["'%s'" % s for s in sym_ls])
    cfg_str = cfg_template + 'VAR -> %s\nPRED -> %s\nCONST -> %s' % (sym_str,sym_str,sym_str)
    return cfg_str


def symbol_resolution(tree):
    lvars, consts, preds = set(), set(), set()
    
    if tree[0].label() == 'Q':
        isFOL = True
        main_tree = tree[1]
        for sym, tag in tree[0].pos():
            if tag == 'VAR':
                lvars.add(sym)
    else:
        isFOL = False
        main_tree = tree[0]
        
    preorder_resolution(main_tree, lvars, consts, preds)
    
    return isFOL, lvars, consts, preds


def preorder_resolution(tree, lvars, consts, preds):
    # reached terminal nodes
    if isinstance(tree, str):
        return
    
    if tree.label() == 'PRED':
        preds.add(tree[0])
        return
    
    if tree.label() == 'TERM':
        sym = tree[0][0]
        if sym in lvars:
            tree[0].set_label('VAR')
        else:
            tree[0].set_label('CONST')
            consts.add(sym)
        return
    
    for child in tree:
        preorder_resolution(child, lvars, consts, preds)

        
class Rule:
    def __init__(self, isFOL, lvars, consts, preds, tree, grounded_ent):
        self.isFOL = isFOL
        self.lvars = lvars
        self.consts = consts
        self.preds = preds
        self.tree = tree
        self.term_orders = {}  # Initialize an empty dictionary to store term orders
        self.pred_entities = {}  # Initialize an empty dictionary to store entities associated with each predicate
        self.extract_entities_from_str()  # Extract entities from the rule string
        self.grounded_ent = grounded_ent
        self.enumerations = []
        self.contain_Var = None

    def rule_str(self):
        # TODO inefficient
        _, rule_str = msplit(''.join(self.tree.leaves()))
        return rule_str

    def _get_nodes(
            self,
            root,
            nodes,
            allowed_labels=None,
            not_allowed_nodes=None,
            not_allowed_nodes_in_subtree=False
    ):
        all_child_allowed = True

        if isinstance(root, str):
            return all_child_allowed

        # post-order check children
        for child in root:
            child_allowed = self._get_nodes(
                child,
                nodes,
                allowed_labels,
                not_allowed_nodes,
                not_allowed_nodes_in_subtree
            )
            all_child_allowed = all_child_allowed and child_allowed
        # this is twisted... what i mean is that if you don't want to filter the subtrees then simply set
        # all_child_allowed to true regardless of the post-order check result
        if not not_allowed_nodes_in_subtree:
            all_child_allowed = True

        root_is_allowed = (not_allowed_nodes is None) or all(e is not root for e in not_allowed_nodes)
        tree_is_allowed = all_child_allowed and root_is_allowed

        if (
                ((allowed_labels is None) or (root.label() in allowed_labels))
                and tree_is_allowed
        ):
            nodes.append(root)

        return tree_is_allowed

    def get_nodes(
            self,
            root,
            allowed_labels=None,
            not_allowed_nodes=None,
            not_allowed_nodes_in_subtree=False
    ):
        """
            get tree nodes from a tree

            Args:
                root:
                allowed_labels: None or a set of strs; only nodes with the allowed label is included
                not_allowed_nodes: None or a list of node objects; only node objects that are not in the list
                is included
                not_allowed_nodes_in_subtree: set to True to also filter out nodes whose subtree nodes are in
                not_allowed_nodes, this is used when finding the deletable nodes (we want to find nodes whose entire
                subtree is not perturbed before)
        """
        if not_allowed_nodes_in_subtree:
            assert all_exists(not_allowed_nodes), 'must specify not_allowed_nodes'

        nodes = []
        self._get_nodes(
            root,
            nodes,
            allowed_labels,
            not_allowed_nodes,
            not_allowed_nodes_in_subtree
        )
        return nodes
    
    def random_node_by_label(
            self,
            root,
            allowed_labels=None,
            not_allowed_nodes=None,
            not_allowed_nodes_in_subtree=False
    ):
        nodes = self.get_nodes(root, allowed_labels, not_allowed_nodes, not_allowed_nodes_in_subtree)
        choice = nodes[int(np.random.randint(len(nodes)))] if len(nodes) > 0 else None
        return choice
    
    def get_all_fopf(self, root, res):
        if isinstance(root, str):
            return
        
        if root.label() == 'F':
            if len(root) == 3 and all(not isinstance(child, str) for child in root):
                # this is a F - F OP F subtree
                res.append(root)                
            
        for child in root:
            self.get_all_fopf(child, res)
    
    def order_of(self, node):
        cnt, flag = self._inorder_order(self.tree, node, 0)
        assert flag
        return cnt

    def parent_of(self, root, node):
        if isinstance(root, str):
            return None

        for child in root:
            if child is node:
                return root
            parent = self.parent_of(child, node)
            if all_exists(parent):
                return parent

        return None
        
    def _inorder_order(self, root, node, order_cnt):
        if root is node:
            return order_cnt + 1, True
        
        if isinstance(root, str):
            return order_cnt + (root == node[0]), False
        
        cnt = order_cnt
        flag = False
        for n in root:
            cnt, flag = self._inorder_order(n, node, cnt)
            if flag:
                break
        
        return cnt, flag

    def replace_logical_operations(self):
        self.tree = self._replace_logical_operations(self.tree)

    def _replace_logical_operations(self, tree):
        if isinstance(tree, str):
            return tree

        if tree.label() == 'F':
            # Check if this is an F node with an OP child
            for i, child in enumerate(tree):
                if isinstance(child, nltk.Tree) and child.label() == 'OP':
                    op = child[0]
                    if op == '→':
                        # Replace A → B with (¬A ∨ B)
                        left = self._replace_logical_operations(tree[i - 1])
                        right = self._replace_logical_operations(tree[i + 1])
                        return nltk.Tree('F', [nltk.Tree('F', [nltk.Tree('OP', ['¬']), nltk.Tree('F', [left])]), nltk.Tree('OP', ['∨']), nltk.Tree('F', [right])])
                    elif op == '⊕':
                        # Replace A ⊕ B with (A ∨ B) ∧ ¬(A ∧ B)
                        left = self._replace_logical_operations(tree[i - 1])
                        right = self._replace_logical_operations(tree[i + 1])
                        return nltk.Tree('F', [nltk.Tree('F', [nltk.Tree('F', [left]), nltk.Tree('OP', ['∨']), nltk.Tree('F', [right])]), nltk.Tree('OP', ['∧']), nltk.Tree('F', [nltk.Tree('OP', ['¬']), nltk.Tree('F', [nltk.Tree('F', [left]), nltk.Tree('OP', ['∧']), nltk.Tree('F', [right])])])])
                    elif op == '↔':
                        # Replace A ↔ B with (¬A ∨ B) ∧ (¬B ∨ A)
                        left = self._replace_logical_operations(tree[i - 1])
                        right = self._replace_logical_operations(tree[i + 1])
                        return nltk.Tree('F', [nltk.Tree('F', [nltk.Tree('F', [nltk.Tree('OP', ['¬']), nltk.Tree('F', [left])]), nltk.Tree('OP', ['∨']), nltk.Tree('F', [right])]), nltk.Tree('OP', ['∧']), nltk.Tree('F', [nltk.Tree('F', [nltk.Tree('OP', ['¬']), nltk.Tree('F', [right])]), nltk.Tree('OP', ['∨']), nltk.Tree('F', [left])])])

        # Default case: return a new tree with the same label and recursively processed children
        return nltk.Tree(tree.label(), [self._replace_logical_operations(child) for child in tree])

    def extract_entities_from_str(self):
        terms = re.findall(r'([\w-]+)\(([^)]+)\)', self.rule_str())

        for term in terms:
            predicate, entities = term
            if predicate == 'averse':
                predicate = 'Risk-averse'
            if predicate == 'Drama':
                predicate = 'Fantasy-Drama'
            if predicate == 'fiction':
                predicate = 'Science-fiction'
            if predicate == 'friendlyBrand':
                predicate = 'Eco-friendlyBrand'
            if predicate == 'rareEarthMetals':
                predicate = 'Non-rareEarthMetals'
            if predicate == 'relatedDesign':
                predicate = 'Event-relatedDesign'
            if predicate == 'abortion':
                predicate = 'Anti-abortion'
            if predicate == 'IraqiArchitect':
                predicate = 'British-IraqiArchitect'
            if predicate == 'Stocks':
                predicate = 'MatureCompanies’Stocks'
            entities = tuple(entities.split(','))
            predicate = predicate.strip()
            if isinstance(entities, str):
                entities = tuple(entity.strip() for entity in entities.split(','))  # Strip whitespace from each entity
            else:
                entities = tuple(entity.strip() for entity in entities)  # Handle case where entities is already a tuple
            if predicate not in self.pred_entities:
                self.pred_entities[predicate] = []
            if entities not in self.pred_entities[predicate]:
                self.pred_entities[predicate].append(entities)

    def calculate_term_orders(self, unique_predicates, unique_grounded_entities):
        if self.contain_Var:
            for key in list(self.pred_entities.keys()):
                if key.startswith('x'):
                    new_key = key[1:]  # Remove the 'x' prefix
                    self.pred_entities[new_key] = self.pred_entities[key]
                    del self.pred_entities[key]

            for enum in self.enumerations:
                for key in list(enum.keys()):
                    if key.startswith('x'):
                        new_key = key[1:]  # Remove the 'x' prefix
                        enum[new_key] = enum[key]
                        del enum[key]

                for predicate, entities_list in enum.items():
                    for entities in entities_list:
                        term_order = self.get_term_order(predicate, entities, unique_predicates,
                                                         unique_grounded_entities)
                        self.term_orders[(predicate, tuple(entities))] = term_order
        else:
            for key in list(self.pred_entities.keys()):
                if key.startswith('x'):
                    new_key = key[1:]  # Remove the 'x' prefix
                    self.pred_entities[new_key] = self.pred_entities[key]
                    del self.pred_entities[key]

            for predicate, entities_list in self.pred_entities.items():
                for entities in entities_list:
                    term_order = self.get_term_order(predicate, entities, unique_predicates, unique_grounded_entities)
                    self.term_orders[(predicate, tuple(entities))] = term_order


    @staticmethod
    def get_term_order(predicate, entities, unique_predicates, unique_grounded_entities):
        if len(entities) == 1:
            entities = (entities[0], entities[0])
        predicate_index = unique_predicates.index(predicate)
        entity_indices = [unique_grounded_entities.index(entity) for entity in entities]
        num_entities = len(unique_grounded_entities)
        return predicate_index * num_entities ** 2 + entity_indices[0] * num_entities + entity_indices[1]

    def generate_enumerations(self):
        pred_entities = self.pred_entities
        grounded_ent = self.grounded_ent
        # Determine placeholders used in pred_entities
        placeholders = {'x', 'y', 'z'}
        found_placeholders = set()
        for entities_list in pred_entities.values():
            for tup in entities_list:
                found_placeholders.update([e for e in tup if e in placeholders])

        if len(found_placeholders) == 0:
            self.contain_Var = False
            return
        else:
            self.contain_Var = True

        all_permutations = list(permutations(grounded_ent, len(found_placeholders)))
        if len(found_placeholders) > len(grounded_ent):
            lst = []
            for i in range(len(found_placeholders)):
                lst.append(grounded_ent)
            all_permutations = tuple(lst)

        for perm in all_permutations:
            # Create a mapping from placeholders to the elements in the permutation
            current_replacement = dict(zip(found_placeholders, perm))

            # Replace in pred_entities
            new_pred_entities = {}
            for predicate, entities_list in pred_entities.items():
                new_entities_list = []
                for tup in entities_list:
                    # Replace each entity in the tuple if it is a placeholder
                    new_tup = tuple(current_replacement.get(entity, entity) for entity in tup)
                    new_entities_list.append(new_tup)
                new_pred_entities[predicate] = new_entities_list

            # Append the new predicate entities dictionary to enumerations
            self.enumerations.append(new_pred_entities)



def compute_truth_table_unformatted(rule):
    rule_str = rule.rule_str()
    predicate_instances = [f'{pred}({",".join(entities)})' for pred, entities_list in rule.pred_entities.items() for entities in entities_list]

    # Generate all possible valuations for the predicate instances
    valuations = [dict(zip(predicate_instances, vals)) for vals in itertools.product([False, True], repeat=len(predicate_instances))]

    # Replace logical operators with Python equivalents
    eval_rule_str = rule_str.replace('∧', 'and').replace('∨', 'or').replace('¬', 'not')

    # Create a mapping from predicate(entity) to variable names
    predicate_to_var = {pred_instance: f'var_{i}' for i, pred_instance in enumerate(predicate_instances)}

    # Replace predicates with variable names in the evaluation string
    for pred_instance, var in predicate_to_var.items():
        eval_rule_str = eval_rule_str.replace(pred_instance, var)

    ''''# Debugging: Print the original and modified rule strings, and the predicate to variable mapping
    print("Original rule string:", rule_str)
    print("Eval rule string:", eval_rule_str)
    print("Predicate to var mapping:", predicate_to_var)'''

    # Compute the truth table
    truth_table = []
    for valuation in valuations:
        # Replace predicate instances in the valuation with their corresponding variable names
        var_valuation = {predicate_to_var[pred_instance]: val for pred_instance, val in valuation.items()}
        truth_value = eval(eval_rule_str, {}, var_valuation)
        truth_table.append((valuation, truth_value))

    return truth_table

def compute_truth_table(rule):
    rule_str = rule.rule_str()

    quantifiers = ['∀', '∃']
    if sum(rule_str.count(quantifier) for quantifier in quantifiers) > 0:
        rule_str = rule_str.replace("∀x", "")
        rule_str = rule_str.replace("∀y", "")
        rule_str = rule_str.replace("∀z", "")
        rule_str = rule_str.replace("∃x", "")
        rule_str = rule_str.replace("∃y", "")
        rule_str = rule_str.replace("∃z", "")

    predicate_instances = [f'{pred}({",".join(entities)})' for pred, entities_list in rule.pred_entities.items() for entities in entities_list]

    # Generate all possible valuations for the predicate instances
    valuations = [dict(zip(predicate_instances, vals)) for vals in itertools.product([False, True], repeat=len(predicate_instances))]

    # Replace logical operators with Python equivalents
    eval_rule_str = rule_str.replace('∧', ' and ').replace('∨', ' or ').replace('¬', ' not ')
    eval_rule_str = eval_rule_str.replace(", ", ",")


    # Create a mapping from predicate(entity) to variable names
    predicate_to_var = {pred_instance: f'var_{i}' for i, pred_instance in enumerate(predicate_instances)}

    '''if 'Stocks' in rule_str:
        return [], []
    if 'Co-' in rule_str:
        return [], []
    if 'SoldIn' in rule_str:
        return [], []
    if 'IPhone' in rule_str:
        return [], []
    if 'Non-BreastCancer' in rule_str:
        return [], []'''

    predicate_to_var = {key: predicate_to_var[key] for key in sorted(predicate_to_var, key=len, reverse=True)}
    for pred_instance, var in predicate_to_var.items():
        eval_rule_str = eval_rule_str.replace(pred_instance, var)

    # Debugging: Print the original and modified rule strings, and the predicate to variable mapping
    '''print("Original rule string:", rule_str)
    print("Eval rule string:", eval_rule_str)
    print("Predicate to var mapping:", predicate_to_var)'''

    # Compute the truth table
    variables = [f'var_{i}' for i in range(len(predicate_instances))]
    truth_table = []
    for valuation in valuations:
        # Replace predicate instances in the valuation with their corresponding variable names
        var_valuation = {predicate_to_var[pred_instance]: val for pred_instance, val in valuation.items()}
        truth_value = eval(eval_rule_str, {}, var_valuation)
        truth_table.append([var_valuation[var] for var in variables] + [truth_value])

    return predicate_instances, truth_table


def truth_table_to_cnf(truth_table, variables):
    if len(truth_table) == 0:
        return None, None
    clauses = []
    bin_reps = []
    for row in truth_table:
        if not row[-1]:  # Check if the output is false
            clause = []
            bin_rep = []
            for var, val in zip(variables, row[:-1]):
                if val:
                    clause.append(f"¬{var}")
                    bin_rep.append(0)
                else:
                    clause.append(var)
                    bin_rep.append(1)
            clauses.append(f"({' ∨ '.join(clause)})")
            bin_reps.append(bin_rep)
    cnf = f"{' ∧ '.join(clauses)}"
    return cnf, bin_reps


def truth_table_to_cnf_dimacs(truth_table, selected_elm, variables, thereex):
    # Check for an empty truth table
    if not truth_table:
        return None, None

    # Variable mapping to integers
    var_to_int = {var: i + 1 for i, var in enumerate(variables)}
    clauses = []

    # Processing each row in the truth table
    for row in truth_table:
        if not thereex:
            if not row[-1]:  # Include only rows where the output is False
                clause = []
                for var, val in zip(selected_elm, row[:-1]):
                    if val:
                        clause.append(-var_to_int[var])  # Negate the variable if the corresponding value is True
                    else:
                        clause.append(var_to_int[var])  # Include the variable as is if the value is False
                clauses.append(clause)
        else:
            if row[-1]:  # Include only rows where the output is True
                clause = []
                for var, val in zip(selected_elm, row[:-1]):
                    if val:
                        clause.append(-var_to_int[var])  # Negate the variable if the corresponding value is True
                    else:
                        clause.append(var_to_int[var])  # Include the variable as is if the value is False
                clauses.append(clause)

    # DIMACS format output
    if not clauses:
        return "p cnf 0 1\n0\n", []  # Return a trivial unsatisfiable DIMACS (no variables, one empty clause)

    dimacs = ''.join([' '.join(map(str, clause)) for clause in clauses])
    return dimacs, clauses

def write_dimacs_to_file(dimacs_clauses, file_name, num_var, num_clause):
    with open(file_name, 'w') as file:
        file.write("c file " + file_name + "\n")
        file.write("p cnf " + str(num_var) + " " + str(num_clause) + " " + "\n")
        for clause_list in dimacs_clauses:
            for clause in clause_list:
                file.write(' '.join(map(str, clause)) + ' 0\n')  # Append '0' and end with a newline

def write_dimacs_to_file_ubuntu(dimacs_clauses, story_id, permn, sl, vr):
    directory = 'dimac_cnfs'
    file_name = 'output_' + str(story_id) + '_' + str(permn) + '.cnf'
    full_path = os.path.join(directory, file_name)
    # Ensure the directory exists, create if it does not
    print(f"./sharpSAT -decot 1 -decow 100 -tmpdir . -cs 3500 /mnt/c/Users/ahmet/PycharmProjects/pythonProject2/dimac_cnfs/output_{str(story_id)}_{str(permn)}.cnf &> /mnt/c/Users/ahmet/PycharmProjects/pythonProject2/dimac_cnf/output_{str(story_id)}_{str(permn)}.txt")
    with open(full_path, 'w', newline='\n', encoding='utf-8') as file:
        file.write('c file ' + file_name + '\n')
        file.write('p cnf ' + str(vr) + ' ' + str(sl) + ' ' +'\n')
        for clause_list in dimacs_clauses:
            for clause in clause_list:
                file.write(' '.join(map(str, clause)) + ' 0\n')  # Append '0' and end with a newline

def write_dimacs_to_file_server(dimacs_clauses, story_id, permn, sl, vr):
    directory = 'dimac_cnfs'
    file_name = 'output_' + str(story_id) + '_' + str(permn) + '.cnf'
    full_path = os.path.join(directory, file_name)
    # Ensure the directory exists, create if it does not
    print(f"./sharpSAT -decot 1 -decow 100 -tmpdir . -cs 3500 /mnt/c/Users/ahmet/PycharmProjects/pythonProject2/dimac_cnfs/output_{str(story_id)}_{str(permn)}.cnf &> /mnt/c/Users/ahmet/PycharmProjects/pythonProject2/dimac_cnf/output_{str(story_id)}_{str(permn)}.txt")
    with open(full_path, 'a', newline='\n', encoding='utf-8') as file:
        for clause_list in dimacs_clauses:
            for clause in clause_list:
                file.write(' '.join(map(str, clause)) + ' 0\n')  # Append '0' and end with a newline


def write_dimacs_to_file_deduc(dimacs_clauses, story_id, permn, sl, vr):
    directory = 'dimac_cnfs_deduc'
    file_name = 'output_' + str(story_id) + '_' + str(permn) + '.cnf'
    full_path = os.path.join(directory, file_name)

    # Ensure the directory exists, create if it does not
    print(f"./sharpSAT -decot 1 -decow 100 -tmpdir . -cs 3500 /mnt/c/Users/ahmet/PycharmProjects/pythonProject2/dimac_cnfs_deduc/output_{str(story_id)}_{str(permn)}.cnf &> /mnt/c/Users/ahmet/PycharmProjects/pythonProject2/dimac_cnfs_deduc/output_{str(story_id)}_{str(permn)}.txt")
    with open(full_path, 'w', newline='\n', encoding='utf-8') as file:
        file.write('c file ' + file_name + '\n')
        file.write('p cnf ' + str(vr) + ' ' + str(sl) + ' ' +'\n')
        for clause_list in dimacs_clauses:
            for clause in clause_list:
                file.write(' '.join(map(str, clause)) + ' 0\n')  # Append '0' and end with a newline

def write_a_file(story_id, permn, full_path):
    string = './sharpSAT -decot 1 -decow 100 -tmpdir . -cs 3500 /mnt/c/Users/ahmet/PycharmProjects/pythonProject2/dimac_cnfs/output_' + str(story_id) + '_' + str(permn) + '.cnf &> /mnt/c/Users/ahmet/PycharmProjects/pythonProject2/dimac_cnfs/output_' + str(story_id) + '_' + str(permn) + '.txt'
    with open(full_path, 'a', newline='\n') as file:
        file.write(string)
        file.write('\n')

def write_a_file_deduc(story_id, permn, full_path):
    string = './sharpSAT -decot 1 -decow 100 -tmpdir . -cs 3500 /mnt/c/Users/ahmet/PycharmProjects/pythonProject2/dimac_cnfs_deduc/output_' + str(story_id) + '_' + str(permn) + '.cnf &> /mnt/c/Users/ahmet/PycharmProjects/pythonProject2/dimac_cnfs_deduc/output_' + str(story_id) + '_' + str(permn) + '.txt'
    with open(full_path, 'a', newline='\n') as file:
        file.write(string)
        file.write('\n')


def evaluate_expression(expr, valuation):
    if isinstance(expr, str):
        return valuation.get(expr, True)  # Default to True for constants
    if expr[0] == '¬':
        return not evaluate_expression(expr[1], valuation)
    if expr[1] == '∧':
        return evaluate_expression(expr[0], valuation) and evaluate_expression(expr[2], valuation)
    if expr[1] == '∨':
        return evaluate_expression(expr[0], valuation) or evaluate_expression(expr[2], valuation)