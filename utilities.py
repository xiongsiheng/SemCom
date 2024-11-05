import json
import sys
import pandas as pd
from fol_parser import *
import numpy as np
from collections import Counter

def extract_predicates_from_tree(tree):
    """Extracts predicates from an NLTK tree."""
    predicates = []
    for subtree in tree.subtrees():
        if subtree.label() == 'PRED':
            # Assuming the predicate is the first child of the PRED node
            predicate = subtree[0]
            if isinstance(predicate, str):
                predicates.append(predicate)
            else:
                predicates.append(' '.join(predicate.leaves()))
    return predicates

def extract_grounded_entities_from_tree(tree):
    """Extracts entities (constants and variables) from an NLTK tree."""
    entities = []
    for subtree in tree.subtrees():
        if subtree.label() in ['CONST']:
            entity = subtree[0]
            if isinstance(entity, str):
                entities.append(entity)
            else:
                entities.append(' '.join(entity.leaves()))
    return entities

def extract_variable_entities_from_tree(tree):
    """Extracts entities (constants and variables) from an NLTK tree."""
    entities = []
    for subtree in tree.subtrees():
        if subtree.label() in ['VAR']:
            entity = subtree[0]
            if isinstance(entity, str):
                entities.append(entity)
            else:
                entities.append(' '.join(entity.leaves()))
    return entities

def extract_ops_from_tree(tree):
    """Extracts entities (constants and variables) from an NLTK tree."""
    ops = []
    for subtree in tree.subtrees():
        if subtree.label() in ['OP']:
            op = subtree[0]
            if isinstance(op, str):
                ops.append(op)
            else:
                ops.append(' '.join(op.leaves()))
    return ops

def extract_quants_from_tree(tree):
    """Extracts entities (constants and variables) from an NLTK tree."""
    quants = []
    for subtree in tree.subtrees():
        if subtree.label() in ['QUANT']:
            quant = subtree[0]
            if isinstance(quant, str):
                quants.append(quant)
            else:
                quants.append(' '.join(quant.leaves()))
    return quants

def extract_predicates_from_tree_count(tree, predicate_counts):
    """Extracts predicates from an NLTK tree and counts their occurrences."""
    for subtree in tree.subtrees():
        if subtree.label() == 'PRED':
            predicate = subtree[0]
            if not isinstance(predicate, str):
                predicate = ' '.join(predicate.leaves())
            predicate_counts[predicate] = predicate_counts.get(predicate, 0) + 1


def extract_grounded_entities_from_tree_count(tree, gr_entity_counts):
    """Extracts entities (constants and variables) from an NLTK tree and counts their occurrences."""
    for subtree in tree.subtrees():
        if subtree.label() in ['CONST']:
            gr_entity = subtree[0]
            if not isinstance(gr_entity, str):
                gr_entity = ' '.join(gr_entity.leaves())
            gr_entity_counts[gr_entity] = gr_entity_counts.get(gr_entity, 0) + 1

def extract_variable_entities_from_tree_count(tree, var_entity_counts):
    """Extracts entities (constants and variables) from an NLTK tree and counts their occurrences."""
    for subtree in tree.subtrees():
        if subtree.label() in ['VAR']:
            var_entity = subtree[0]
            if not isinstance(var_entity, str):
                var_entity = ' '.join(var_entity.leaves())
            var_entity_counts[var_entity] = var_entity_counts.get(var_entity, 0) + 1

def extract_ops_from_tree_count(tree, op_counts):
    """Extracts entities (constants and variables) from an NLTK tree and counts their occurrences."""
    for subtree in tree.subtrees():
        if subtree.label() in ['OP']:
            op = subtree[0]
            if not isinstance(op, str):
                op = ' '.join(op.leaves())
            op_counts[op] = op_counts.get(op, 0) + 1

def extract_quants_from_tree_count(tree, quant_counts):
    """Extracts entities (constants and variables) from an NLTK tree and counts their occurrences."""
    for subtree in tree.subtrees():
        if subtree.label() in ['QUANT']:
            quant = subtree[0]
            if not isinstance(quant, str):
                quant = ' '.join(quant.leaves())
            quant_counts[quant] = quant_counts.get(quant, 0) + 1

def count_quantifiers(fol_expression):
    """Counts the number of quantifiers in the FOL expression."""
    quantifiers = ['∀', '∃']
    return sum(fol_expression.count(quantifier) for quantifier in quantifiers)

def contains_quantifiers(fol_expression):
    """Checks if the FOL expression contains quantifiers."""
    quantifiers = ['∀', '∃']
    return any(quantifier in fol_expression for quantifier in quantifiers)

def contains_both_quantifiers(fol_expression):
    """Checks if the FOL expression contains quantifiers."""
    quantifierF = ['∀']
    quantifierT = ['∃']
    return any(quantifier in fol_expression for quantifier in quantifierF) and any(quantifier in fol_expression for quantifier in quantifierT)


def contains_forall(fol_expression):
    """Checks if the FOL expression contains quantifiers."""
    quantifiers = ['∀']
    return any(quantifier in fol_expression for quantifier in quantifiers)

def contains_thereexists(fol_expression):
    """Checks if the FOL expression contains quantifiers."""
    quantifiers = ['∃']
    return any(quantifier in fol_expression for quantifier in quantifiers)

def read_jsonl_file(filename):
    """Reads a JSONL file and returns the data."""
    data = []
    with open(filename, 'r') as file:
        for line in file:
            data.append(json.loads(line))
    return data

def read_json_file(filename):
    """Reads a standard JSON file and returns the data."""
    with open(filename, 'r') as file:
        data = json.load(file)
    return data

def filter_quantifiers(df_with_quantifiers):
    # Filter expressions based on the number of quantifiers
    filtered_expressions3 = []
    filtered_expressions2 = []
    filtered_expressions1 = []

    for index, row in df_with_quantifiers.iterrows():
        fol_expression = row[0]
        if count_quantifiers(fol_expression) == 3:
            filtered_expressions3.append(row)
        elif count_quantifiers(fol_expression) == 2:
            filtered_expressions2.append(row)
        elif count_quantifiers(fol_expression) == 1:
            filtered_expressions1.append(row)

    # Convert list to DataFrame
    df_3 = pd.DataFrame(filtered_expressions3)
    df_2 = pd.DataFrame(filtered_expressions2)
    df_1 = pd.DataFrame(filtered_expressions1)

    return df_3, df_2, df_1

def get_all_entities(story_arr):
    unique_grounded_entities = set()
    unique_variable_entities = set()

    for i in range(len(story_arr)):
        fol_expression = story_arr[i]
        tree = parse_text_FOL_to_tree(fol_expression)
        if tree is not None:
            grounded_entities = extract_grounded_entities_from_tree(tree)
            unique_grounded_entities.update(grounded_entities)
            variable_entities = extract_variable_entities_from_tree(tree)
            unique_variable_entities.update(variable_entities)

    unique_grounded_entities = unique_grounded_entities - unique_variable_entities

    return unique_grounded_entities, unique_variable_entities


def replace_quantifier(fol_expression):

    # Filter expressions based on the number of quantifiers
    if count_quantifiers(fol_expression) == 3:
        if contains_forall(fol_expression) == True:
            print()
        elif contains_thereexists(fol_expression) == True:
            print()
    elif count_quantifiers(fol_expression) == 2:
        if contains_forall(fol_expression) == True:
            print()
        elif contains_thereexists(fol_expression) == True:
            print()
    elif count_quantifiers(fol_expression) == 1:
        if contains_forall(fol_expression) == True:
            print()
        elif contains_thereexists(fol_expression) == True:
            print()
    return

def count_predicates(rule):
    """Counts predicates in a Rule object."""
    predicate_nodes = rule.get_nodes(rule.tree, allowed_labels=['PRED'])
    predicates = [node[0] for node in predicate_nodes if isinstance(node, list) and len(node) > 0]
    return predicates

def count_grounded_entities(rule):
    """Counts entities (constants and variables) in a Rule object."""
    entity_nodes = rule.get_nodes(rule.tree, allowed_labels=['CONST'])
    entities = [node[0] for node in entity_nodes if isinstance(node, list) and len(node) > 0]
    return entities

def count_variable_entities(rule):
    """Counts entities (constants and variables) in a Rule object."""
    entity_nodes = rule.get_nodes(rule.tree, allowed_labels=['VAR'])
    entities = [node[0] for node in entity_nodes if isinstance(node, list) and len(node) > 0]
    return entities

def get_predicates(rule):
    """Counts predicates in a Rule object."""
    predicate_nodes = rule.get_nodes(rule.tree, allowed_labels=['PRED'])
    predicates = [node[0] for node in predicate_nodes if isinstance(node, list) and len(node) > 0]
    return predicates

def get_ops(rule):
    """Counts predicates in a Rule object."""
    op_nodes = rule.get_nodes(rule.tree, allowed_labels=['OP'])
    ops = [node[0] for node in op_nodes if isinstance(node, list) and len(node) > 0]
    return ops

def count_ops(rule):
    """Counts entities (constants and variables) in a Rule object."""
    op_nodes = rule.get_nodes(rule.tree, allowed_labels=['OP'])
    ops = [node[0] for node in op_nodes if isinstance(node, list) and len(node) > 0]
    return ops

def get_grounded_entities(rule):
    """Counts predicates in a Rule object."""
    entity_nodes = rule.get_nodes(rule.tree, allowed_labels=['CONST'])
    entities = [node[0] for node in entity_nodes if isinstance(node, list) and len(node) > 0]
    return entities

def get_variable_entities(rule):
    """Counts predicates in a Rule object."""
    entity_nodes = rule.get_nodes(rule.tree, allowed_labels=['VAR'])
    entities = [node[0] for node in entity_nodes if isinstance(node, list) and len(node) > 0]
    return entities

def count_quantifiers(fol_expression):
    """Counts the number of quantifiers in the FOL expression."""
    quantifiers = ['∀', '∃']
    return sum(fol_expression.count(quantifier) for quantifier in quantifiers)

def contains_quantifiers(fol_expression):
    """Checks if the FOL expression contains quantifiers."""
    quantifiers = ['∀', '∃']
    return any(quantifier in fol_expression for quantifier in quantifiers)

def contains_connective(fol_expression):
    """Checks if the FOL expression contains quantifiers."""
    or_q = ['∨', '∧']
    return any(quantifier in fol_expression for quantifier in or_q)

def contains_or(fol_expression):
    """Checks if the FOL expression contains quantifiers."""
    or_q = ['∨']
    return any(quantifier in fol_expression for quantifier in or_q)

def place_in_enum(sub, obj, rel, obj_num, pred_num, value):
    s, r, o = value[0], value[1], value[2]

    sub_in = sub.index(s) + 1
    obj_in = obj.index(o) + 1
    i1 = (sub_in - 1) * obj_num + obj_in

    rel_in = rel.index(r) + 1
    i2 = (i1 - 1) * pred_num + rel_in
    return i2

def replace_logical_operations_with_quantifiers(tree):
    def traverse(node):
        if isinstance(node, nltk.Tree):
            label = node.label()
            if label == 'F':
                # Check if this is an F node with an OP child
                for child in node:
                    if isinstance(child, nltk.Tree) and child.label() == 'OP':
                        op = child[0]
                        if op == '→':
                            # Replace A → B with (¬A ∨ B)
                            left = traverse(node[0][0])
                            right = traverse(node[2][0])
                            return nltk.Tree('F', [nltk.Tree('F', [nltk.Tree('OP', ['¬']), nltk.Tree('F', [left]), nltk.Tree('OP', ['∨']), nltk.Tree('F', [right])])])
                        elif op == '⊕':
                            # Replace A ⊕ B with (A ∨ B) ∧ ¬(A ∧ B)
                            left = traverse(node[0][0])
                            right = traverse(node[2][0])
                            return nltk.Tree('F', [nltk.Tree('F', [nltk.Tree('F', [left]), nltk.Tree('OP', ['∨']), nltk.Tree('F', [right])]), nltk.Tree('OP', ['∧']), nltk.Tree('F', [nltk.Tree('OP', ['¬']), nltk.Tree('F', [nltk.Tree('F', [left]), nltk.Tree('OP', ['∧']), nltk.Tree('F', [right])])])])
                        elif op == '↔':
                            # Replace A ↔ B with (¬A ∨ B) ∧ (¬B ∨ A)
                            left = traverse(node[0][0])
                            right = traverse(node[2][0])
                            return nltk.Tree('F', [nltk.Tree('F', [nltk.Tree('F', [nltk.Tree('OP', ['¬']), nltk.Tree('F', [left])]), nltk.Tree('OP', ['∨']), nltk.Tree('F', [right])]), nltk.Tree('OP', ['∧']), nltk.Tree('F', [nltk.Tree('F', [nltk.Tree('OP', ['¬']), nltk.Tree('F', [right])]), nltk.Tree('OP', ['∨']), nltk.Tree('F', [left])])])
            # Default case: return a new tree with the same label and recursively processed children
            return nltk.Tree(label, [traverse(child) for child in node])
        else:
            # If the node is a leaf, return it as is
            return node
    return traverse(tree)

def replace_logical_operations2(tree):
    isFOL, lvars, consts, preds = symbol_resolution(tree)
    rule = Rule(isFOL, lvars, consts, preds, tree)  # Assuming the Rule constructor

    def traverse(node):
        if isinstance(node, nltk.Tree):
            label = node.label()
            if label == 'OP':
                parent = rule.parent_of(rule.tree, node)
                if node[0] == '→':
                    # Replace A → B with ¬A ∨ B
                    left = traverse(parent[0])
                    right = traverse(parent[2])
                    return nltk.Tree('F', [nltk.Tree('F', [nltk.Tree('OP', ['¬']), left]), nltk.Tree('OP', ['∨']), right])
                elif node[0] == '⊕':
                    # Replace A ⊕ B with (A ∨ B) ∧ ¬(A ∧ B)
                    left = traverse(parent[0])
                    right = traverse(parent[2])
                    return nltk.Tree('F', [nltk.Tree('F', [left, nltk.Tree('OP', ['∨']), right]), nltk.Tree('OP', ['∧']), nltk.Tree('F', [nltk.Tree('OP', ['¬']), nltk.Tree('F', [left, nltk.Tree('OP', ['∧']), right])])])
                # Add more cases for other operators if needed
            else:
                return nltk.Tree(label, [traverse(child) for child in node])
        else:
            return node

    return traverse(tree)

def num_quantifiers(fol_expression):
    if not contains_connective(fol_expression):  # no connective
        return count_quantifiers(fol_expression), contains_thereexists(fol_expression), contains_forall(fol_expression), 'NC'
    elif not contains_or(fol_expression):  # just and
        return count_quantifiers(fol_expression), contains_thereexists(fol_expression), contains_forall(fol_expression), 'JA'
    else:  # both and-or
        return count_quantifiers(fol_expression), contains_thereexists(fol_expression), contains_forall(fol_expression), 'BC'


# URL of the dataset (you need to replace this with the actual URL of the JSONL file)
'''malls_train = "MALLS-v0.1-train.json"
malls_validation = "MALLS-v0.1-test.json"

malls_t = read_jsonl_file(malls_train)[0]
malls_v = read_jsonl_file(malls_validation)[0]

df_mt = pd.DataFrame(data=malls_t)
df_mv = pd.DataFrame(data=malls_v)'''