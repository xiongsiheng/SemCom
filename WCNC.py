import math
import sys
import os
import shutil
from utilities_SPAWC import *
from bin_tree import *
from itertools import combinations
from decimal import Decimal
from functools import reduce

Predicates = ['LivesIn', 'WorksAs', 'OwnsVehicle', 'Practices', 'IsParentOf', 'Attends', 'Eats', 'IsFriendOf', 'IsMarriedTo', 'Speaks', 'Drives', 'Likes', 'IsSiblingOf', 'HasPet', 'Studies']

Entities = ['John', 'Emma', 'Michael', 'Sophia', 'David', 'Olivia', 'Engineer', 'Doctor', 'Teacher', 'NewYork', 'London', 'Paris', 'Guitar', 'Piano', 'Chess', 'Harvard', 'Cambridge', 'Oxford', 'Pizza', 'Sushi', 'Car', 'Bicycle', 'Train', 'English', 'French', 'Spanish', 'Maria', 'Robert', 'Daniel', 'Laura', 'Hiking', 'Cooking', 'Photography', 'Cat', 'Dog', 'Italian', 'Chef', 'German', 'Berlin', 'Soccer']


def read_stories(dataframe):
    ids, story_arr = [], []
    for ix in range(len(dataframe)):
        if dataframe['story_id'][ix] in ids:
            continue
        else:
            story_arr.append(dataframe['premises-FOL'][ix])
        ids.append(dataframe['story_id'][ix])

    return story_arr, ids

def flatten_stories(story_arr):
    flat_arr = []
    for i in range(len(story_arr)):
        next_story = story_arr[i]
        next_FOL = []
        there_exists_flag = []
        grounded_entity, variable_entity = get_all_entities(next_story)
        for j in range(len(next_story)):
            fol_expression = next_story[j]
            if contains_quantifiers(fol_expression):
                if not contains_both_quantifiers(fol_expression):
                    if contains_forall(fol_expression):
                        next_FOL.append(fol_expression)
                        there_exists_flag.append(False)
                    else:
                        num_q = sum(fol_expression.count(quantifier) for quantifier in ['∃'])
                        if num_q % 2 == 1:
                            #fol_expression = str('¬(') + fol_expression + str(')')
                            there_exists_flag.append(True)
                        else:
                            there_exists_flag.append(False)
                        fol_expression = fol_expression.replace('∃', '∀')
                        next_FOL.append(fol_expression)
                else:
                    # Count the number of ∃ and replace them with ∀.
                    # If the number of ∃ is odd, put a negation sign at the beginning, and set rev_prob to True.
                    num_q = sum(fol_expression.count(quantifier) for quantifier in ['∃'])
                    if num_q % 2 == 1:
                        #fol_expression = str('¬(') + fol_expression + str(')')
                        there_exists_flag.append(True)
                    else:
                        there_exists_flag.append(False)
                    fol_expression = fol_expression.replace('∃', '∀')
                    next_FOL.append(fol_expression)
            else:
                next_FOL.append(fol_expression)
                there_exists_flag.append(False)
        flat_arr.append([next_FOL, grounded_entity, variable_entity, there_exists_flag])
    return flat_arr

def unique_elements(story_arr):
    # Extract predicates, entities, and variables from each FOL expression into a set.
    unique_predicates = set()
    unique_grounded_entities = set()
    unique_variable_entities = set()
    enums_per_story = []
    for index in range(len(story_arr)):
        next_story = story_arr[index]
        predicates_tmp = set()
        entities_tmp = set()
        for j in range(len(next_story)):
            fol_expression = next_story[j]
            tree = parse_text_FOL_to_tree(fol_expression)
            if tree is not None:
                predicates = extract_predicates_from_tree(tree)
                unique_predicates.update(predicates)
                predicates_tmp.update(predicates)
                grounded_entities = extract_grounded_entities_from_tree(tree)
                unique_grounded_entities.update(grounded_entities)
                entities_tmp.update(grounded_entities)
                variable_entities = extract_variable_entities_from_tree(tree)
                unique_variable_entities.update(variable_entities)
        num_p = len(list(predicates_tmp))
        num_e = len(list(entities_tmp))
        enums_per_story.append(num_p * num_e * num_e)

    # Convert the set to a list
    unique_predicates = sorted(list(unique_predicates))
    unique_grounded_entities = sorted(list(unique_grounded_entities))
    unique_variable_entities = sorted(list(unique_variable_entities))

    # Print the information
    print("Unique Predicates: ", unique_predicates)
    print("Unique Grounded Entities: ", unique_grounded_entities)
    print("Unique Variable Entities: ", unique_variable_entities)
    print("Number of Unique Predicates: ", len(unique_predicates))
    print("Number of Unique Grounded Entities: ", len(unique_grounded_entities))
    print("Number of Unique Variable Entities: ", len(unique_variable_entities))
    print("Number of Enumerations: ", (len(unique_grounded_entities) ** 2) * len(unique_predicates))
    print("Number of Enumerations Per Story: ", enums_per_story)

    # Assuming a lexical enumeration where each predicate is listed with corresponding list of entities, create an
    # ordering and store the cardinality of the enumerations in num_enum.
    num_enum = (len(unique_grounded_entities) ** 2) * len(unique_predicates)

    return unique_predicates, unique_grounded_entities, unique_variable_entities, num_enum, enums_per_story

def get_term_orders(story_flat_arr):
    df_c = []
    term_orders = []
    there_exists = []
    for next_FOL_exp in story_flat_arr:
        FOL_sentences = next_FOL_exp[0]
        grounded_ents = next_FOL_exp[1]
        there_exists_prob = next_FOL_exp[3]

        temp_arr = []
        temp_arr_ord = []
        temp_rev = []
        for k in range(len(FOL_sentences)):
            fol_expression = FOL_sentences[k]
            tree = parse_text_FOL_to_tree(fol_expression)
            if tree is not None:
                isFOL, lvars, consts, preds = symbol_resolution(tree)
                rule = Rule(isFOL, lvars, consts, preds, tree, grounded_ents)  # Assuming the Rule constructor
                rule.replace_logical_operations()
                rule.generate_enumerations()
                rule.calculate_term_orders(unique_predicates, unique_grounded_entities)
            variables, truth_table = compute_truth_table(rule)
            cnf, bin_reps = truth_table_to_cnf(truth_table, variables)
            temp_arr.append([fol_expression, bin_reps, cnf, truth_table, rule])
            temp_arr_ord.append(rule.term_orders)
        df_c.append(temp_arr)
        term_orders.append(temp_arr_ord)
        there_exists.append(there_exists_prob)

    return df_c, term_orders, there_exists

def script_for_ubuntu(story_id, permn):
    directory = 'dimac_cnfs'
    file_name = 'script.txt'
    full_path = os.path.join(directory, file_name)
    write_a_file(story_id, permn, full_path)

def get_tokens(story_id, permn, last_tokens, var_len, enum, thereex, fols):
    file_path = f"WCNC/dimac_cnfs_res\\output_{story_id}_{permn}.txt"
    # Open the file and read it line by line
    with open(file_path, 'r') as file:
        tokens = []
        for line in file:
            # Strip any leading/trailing whitespace and split the line into tokens
            tokens = line.strip().split()
            # If the line is not empty, take the last token and add it to the list
        '''#'''
        if tokens:
            if len(thereex) > 0 and reduce(lambda x, y: x ^ y, thereex):  # check if thereexists_flag is True.
                # Formula for selection: ind.prob. = x[3] / (2 ** x[4])
                last_tokens.append([story_id, permn, index, int(tokens[-1]), var_len, enum, (2 ** var_len) - int(tokens[-1]), fols]) #1.0 - (int(tokens[-1]) * 1.0) / (2 ** var_len)
            else:
                last_tokens.append([story_id, permn, index, int(tokens[-1]), var_len, enum, (2 ** var_len) - int(tokens[-1]), fols]) #(int(tokens[-1]) * 1.0) / (2 ** var_len)

    return last_tokens

def move_txt():
    #Move .txt files to another directory.

    # Define the source and destination directories
    source_dir = "WCNC/dimac_cnfs"
    destination_dir = "WCNC/dimac_cnfs_res"

    # Ensure the destination directory exists
    if not os.path.exists(destination_dir):
        os.makedirs(destination_dir)

    # Iterate over all files in the source directory
    for filename in os.listdir(source_dir):
        # Check if the file has a .txt extension
        if filename.endswith(".txt"):
            # Construct full file paths
            source_file = os.path.join(source_dir, filename)
            destination_file = os.path.join(destination_dir, filename)

            # Move the file
            shutil.move(source_file, destination_file)
            print(f"Moved: {filename}")

    print("All .txt files have been moved.")

def calc_inductive_probs(last_tokens):
    story_id = 0
    new_arr = []
    tmp_arr = []
    for i in range(len(last_tokens)):
        if last_tokens[i][0] > story_id:
            new_arr.append(tmp_arr)
            story_id += 1
            tmp_arr = []
        else:
            tmp_arr.append(last_tokens[i])

    for i in range(len(new_arr)):
        new_arr[i] = sorted(new_arr[i], key=lambda x: x[3])

    ones = []
    twos = []
    threes = []
    min_ones = []
    min_twos = []
    min_threes = []
    for element in new_arr:
        sub_ones = []
        sub_twos = []
        sub_threes = []
        for sub_element in element:
            print(sub_element)
            if len(sub_element[2]) == 1:
                sub_ones.append(sub_element)
            elif len(sub_element[2]) == 2:
                sub_twos.append(sub_element)
            elif len(sub_element[2]) == 3:
                sub_threes.append(sub_element)
        ones.append(sub_ones)
        twos.append(sub_twos)
        threes.append(sub_threes)
        m_one = min(sub_ones, key=lambda x: x[3])
        min_ones.append(m_one)
        two_temp = []
        for element in sub_twos:
            if m_one[2][0] in element[2]:
                two_temp.append(element)
        m_two = min(two_temp, key=lambda x: x[3])
        min_twos.append(m_two)
        three_temp = []
        for element in sub_threes:
            if (m_two[2][0] in element[2]) and (m_two[2][1] in element[2]):
                three_temp.append(element)
        m_three = min(three_temp, key=lambda x: x[3])
        min_threes.append(m_three)

    print(min_ones)
    print(min_twos)
    print(min_threes)

    s_1 = []
    s_2 = []
    s_3 = []
    cont_1 = []
    cont_2 = []
    cont_3 = []
    var_1 = []
    var_2 = []
    var_3 = []

    ids = 0
    for i in range(len(min_ones)):
        str_1 = min_ones[i][-1][0]
        str_21 = min_twos[i][-1][0]
        str_22 = min_twos[i][-1][1]
        str_31 = min_threes[i][-1][0]
        str_32 = min_threes[i][-1][1]
        str_33 = min_threes[i][-1][2]
        s_1.append([ids, len(str_1) * 8])
        s_2.append([ids, len(str_21) * 8 + len(str_22) * 8])
        s_3.append([ids, len(str_31) * 8 + len(str_32) * 8 + len(str_33) * 8])
        cont_1.append([ids,  min_ones[i][-2]])
        cont_2.append([ids, min_twos[i][-2]])
        cont_3.append([ids, min_threes[i][-2]])
        var_1.append([ids, min_ones[i][4]])
        var_2.append([ids, min_twos[i][4]])
        var_3.append([ids, min_threes[i][4]])
        ids = ids + 1

    print(s_1)
    print(s_2)
    print(s_3)
    print(cont_1)
    print(cont_2)
    print(cont_3)
    print(var_1)
    print(var_2)
    print(var_3)

def calc_inductive_probs_random(last_tokens):
    story_id = 0
    new_arr = []
    tmp_arr = []
    for i in range(len(last_tokens)):
        if last_tokens[i][0] > story_id:
            new_arr.append(tmp_arr)
            story_id += 1
            tmp_arr = []
        else:
            tmp_arr.append(last_tokens[i])

    for i in range(len(new_arr)):
        new_arr[i] = sorted(new_arr[i], key=lambda x: x[3])

    ones = []
    twos = []
    threes = []
    min_ones = []
    min_twos = []
    min_threes = []


    for element in new_arr:
        sub_ones = []
        sub_twos = []
        sub_threes = []
        for sub_element in element:
            print(sub_element)
            if len(sub_element[2]) == 1:
                sub_ones.append(sub_element)
            elif len(sub_element[2]) == 2:
                sub_twos.append(sub_element)
            elif len(sub_element[2]) == 3:
                sub_threes.append(sub_element)
        ones.append(sub_ones)
        twos.append(sub_twos)
        threes.append(sub_threes)

    s_1 = []
    s_2 = []
    s_3 = []
    cont_1 = []
    cont_2 = []
    cont_3 = []
    var_1 = []
    var_2 = []
    var_3 = []

    ids = 0
    for i in range(len(ones)):
        for element in ones[i]:
            temp_sum = 0
            for stin in element[-1]:
                temp_sum += len(stin) * 8
            s_1.append([ids, temp_sum])
            cont_1.append([ids, element[-2]])
            var_1.append([ids, element[4]])
        for element in twos[i]:
            temp_sum = 0
            for stin in element[-1]:
                temp_sum += len(stin) * 8
            s_2.append([ids, temp_sum])
            cont_2.append([ids, element[-2]])
            var_2.append([ids, element[4]])
        for element in threes[i]:
            temp_sum = 0
            for stin in element[-1]:
                temp_sum += len(stin) * 8
            s_3.append([ids, temp_sum])
            cont_3.append([ids, element[-2]])
            var_3.append([ids, element[4]])
        ids = ids + 1

    print(s_1)
    print(s_2)
    print(s_3)
    print(cont_1)
    print(cont_2)
    print(cont_3)
    print(var_1)
    print(var_2)
    print(var_3)

    from collections import defaultdict

    # Dictionary to store the sum of second elements and the count for each first element
    sums_1 = defaultdict(list)
    sums_2 = defaultdict(list)
    sums_3 = defaultdict(list)

    # Iterate over the list to sum second elements for each first element
    for first, second in s_1:
        sums_1[first].append(second)
    for first, second in s_2:
        sums_2[first].append(second)
    for first, second in s_3:
        sums_3[first].append(second)

    # Create the result list with the averaged values
    averaged_result_1 = [[key, sum(values) / len(values)] for key, values in sums_1.items()]
    # Create the result list with the averaged values
    averaged_result_2 = [[key, sum(values) / len(values)] for key, values in sums_2.items()]
    # Create the result list with the averaged values
    averaged_result_3 = [[key, sum(values) / len(values)] for key, values in sums_3.items()]

    # Output the result
    print(averaged_result_1)
    print(averaged_result_2)
    print(averaged_result_3)


if __name__ == '__main__':

    file_path = 'folio-train.jsonl'
    df_f = pd.read_json(file_path, lines=True)

    # As FOLIO dataset is a logical reasoning dataset, there exists multiple examples with the same story (i.e.,
    # same premises) but with different conclusions. Check story_id & skip if a particular story is already included,
    # append all others to a separate list.
    stories, story_ids = read_stories(dataframe=df_f)

    stories_new = []

    for element in stories:
        if len(element) > 6:
            stories_new.append(element)


    stories = stories_new

    # Extract all FOL sentences from the stories list into a flat list. Then, eliminate all with multiple quantifiers
    # as the code needs to be implemented before their inclusion.
    story_flat = flatten_stories(story_arr=stories)


    unique_predicates, unique_grounded_entities, unique_variable_entities, num_enum, enums_per_story = unique_elements(story_arr=stories)

    # Below, first the FOL expressions are parsed into NLTK trees via func.'s in fol_parser_old.py (Yuan's custom code that
    # I modified). Then, replace logical operations of bijunction, implication, and xor operations with operators
    # from minimal set of {and, or, not}. Also, a few corrections in predicate names are done. Third, # of quantifiers
    # are computed with a utility function. Finally, enumerations are generated, and for each term in the trees, the
    # enumeration order is calculated.

    df_c, term_orders, there_exists = get_term_orders(story_flat_arr=story_flat)

    story_id = 0
    last_tokens = []
    for ikj in range(len(term_orders)):

        selected_elements = []
        selected_bools = []
        selected_quant_qual = []
        selected_truth_t = []
        selected_fol = []
        selected_there_exists = there_exists[ikj]

        for dictionary in term_orders[ikj]:
            selected_elements.append(list(dictionary.values()))

        for element in df_c[ikj]:
            selected_bools.append(element[1])
            selected_quant_qual.append(element[2])
            selected_truth_t.append(element[3])
            selected_fol.append(element[0])
        item_count = {}


        if selected_elements is not None:
            permn = 0
            tmp_exists = 0
            for iteration in range(1, 4): #range(len(selected_elements), len(selected_elements)+1):
                comb = combinations(range(len(selected_elements)), iteration)
                for index in list(comb):
                    combin = []
                    combin_t = []
                    rev_p_t = []
                    fols = []
                    for indexy in list(index):
                        combin.append(selected_elements[indexy])
                        combin_t.append(selected_truth_t[indexy])
                        rev_p_t.append(selected_there_exists[indexy])
                        fols.append(selected_fol[indexy])

                    variables = list(set(sum(combin, [])))

                    selected_dimacs = []
                    selected_clauses = []

                    for im in range(len(combin_t)):
                        dimacs, clauses = truth_table_to_cnf_dimacs(combin_t[im], combin[im], variables, reduce(lambda x, y: x ^ y, rev_p_t))
                        selected_dimacs.append(dimacs)
                        selected_clauses.append(clauses)

                    for jj in range(len(selected_clauses)):
                        if selected_clauses[jj] is None:
                            selected_clauses[jj] = []

                    num_elem = len(list(sum(selected_clauses, [])))
                    write_dimacs_to_file_ubuntu(selected_clauses, story_id, permn, num_elem, len(variables))
                    script_for_ubuntu(story_id=story_id, permn=permn)

                    last_tokens = get_tokens(story_id=story_id, permn=permn, last_tokens=last_tokens, var_len=len(variables), enum=enums_per_story[story_id], thereex=rev_p_t, fols =fols)
                    permn += 1
        story_id += 1

    move_txt()
    calc_inductive_probs(last_tokens)
    calc_inductive_probs_random(last_tokens)

