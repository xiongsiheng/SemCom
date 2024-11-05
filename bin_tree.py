# Python3 program to for tree traversals
# A class that represents an individual node in a
# Binary Tree
import sys
import copy

class Node:
   def __init__(self, depth, id,  parent=None):
      self.left = None
      self.right = None
      self.parent = parent
      self.depth = depth
      self.id = id

def find_first_overlap(large_list, small_list):
    # Length of the smaller list to compare sublists of the same size
    small_len = len(small_list)
    # Loop through each sublist in the larger list
    for sublist in large_list:
        # Extract the relevant part of the sublist (excluding the last element)
        relevant_part = sublist[:-1]

        # Check each possible subsequence in the relevant part
        for i in range(len(relevant_part) - small_len + 1):
            # Compare the slice of the relevant part with the small list
            if relevant_part[i:i + small_len] == small_list:
                return sublist  # Return the first matching sublist

    return None  # Return None if no matching sublist is found

def insertAtLastLevel(root, id, my_dict, truth_t, arr, lenr):
    h = lenr
    insertCurrentLevel(root, h, h, id, my_dict, truth_t, arr)



# Print nodes at a current level
def insertCurrentLevel(root, level, depth, id, my_dict, truth_t, arr):
    if level == 1:
        if root is not False:
            if root.left is not False:
                root.left = Node(depth, id, root)

                my_dict[root.id], my_dict[id] = False, False
                my_dict_values = [my_dict[key] for key in arr if key in my_dict]
                result = find_first_overlap(truth_t, my_dict_values)
                if result is not None:
                    if result[-1] is False:
                        root.left.left = False

                my_dict[root.id], my_dict[id] = False, True
                my_dict_values = [my_dict[key] for key in arr if key in my_dict]
                result = find_first_overlap(truth_t, my_dict_values)
                if result is not None:
                    if result[-1] is False:
                        root.left.right = False

        if root is not False:
            if root.right is not False:
                root.right = Node(depth, id, root)

                my_dict[root.id], my_dict[id] = True, False
                my_dict_values = [my_dict[key] for key in arr if key in my_dict]
                result = find_first_overlap(truth_t, my_dict_values)
                if result is not None:
                    if result[-1] is False:
                        root.right.left = False


                my_dict[root.id], my_dict[id] = True, True
                my_dict_values = [my_dict[key] for key in arr if key in my_dict]
                result = find_first_overlap(truth_t, my_dict_values)
                if result is not None:
                    if result[-1] is False:
                        root.right.right = False

    elif level > 1:
        if root is not False:
            if root.left is not None:
                my_dict[root.id] = False
                insertCurrentLevel(root.left, level - 1, depth, id, my_dict, truth_t, arr)
        if root is not False:
            if root.right is not None:
                my_dict[root.id] = True
                insertCurrentLevel(root.right, level - 1, depth, id, my_dict, truth_t, arr)


def deleteCurrentLevel(root, level, var_levels, path, currentLevel):

    if level == 1:
        root.left = None
        root.right = None
        return
    elif level > 1:
        if currentLevel in var_levels:
            inxx = var_levels.index(currentLevel)
            if root.left is not None and path[inxx] == 0:
                deleteCurrentLevel(root.left, level - 1,  var_levels, path, currentLevel+1)
            if root.right is not None and path[inxx] == 1:
                deleteCurrentLevel(root.right, level - 1, var_levels, path, currentLevel + 1)
        else:
            if root.left is not None:
                deleteCurrentLevel(root.left, level - 1, var_levels, path, currentLevel + 1)
            if root.right is not None:
                deleteCurrentLevel(root.right, level - 1, var_levels, path, currentLevel + 1)


def eliminateAtGivenLevel(root, id, repeated, path, vars):
    level = repeated.index(id)
    var_indexes = [repeated.index(indx) for indx in vars]
    var_levels = [index for index in var_indexes]
    currentLevel = 1
    deleteCurrentLevel(root, level, var_levels, path, currentLevel)



# Compute the height of a tree--the number of nodes
# along the longest path from the root node down to
# the farthest leaf node
def height(node):
    if node is None:
        return 0
    else:
        # Compute the height of each subtree
        if node.left is False:
            return 1
        else:
            lheight = height(node.left)

        if node.right is False:
            return 1
        else:
            rheight = height(node.right)

        # Use the larger one
        if lheight > rheight:
            return lheight + 1
        else:
            return rheight + 1



def printInorder(root):
	if root:
		# First recur on left child
		printInorder(root.left)
		# Then print the id of node
		print(root.id, end=" "),
		# Now recur on right child
		printInorder(root.right)


# A function to do preorder tree traversal
def printPreorder(root):
    if root:
        # First print the id of node
        print(root.id, end=" "),
        # Then recur on left child
        printPreorder(root.left)
        # Finally recur on right child
        printPreorder(root.right)


# A function to do postorder tree traversal
def printPostorder(root):
    if root:
        # First recur on left child
        printPostorder(root.left)
        # The recur on right child
        printPostorder(root.right)
        # Now print the id of node
        print(root.id, end=" "),


# Function to  print level order traversal of tree
def printLevelOrder(root, lng):
    h = lng
    for i in range(1, lng+1):
        printCurrentLevel(root, i)

def printCurrentLevel(root, level):
    if root is None:
        return
    if root is False:
        return
    if level == 1:
        print(root.id, end=" ")
    elif level > 1:
        printCurrentLevel(root.left, level - 1)
        printCurrentLevel(root.right, level - 1)

def flip_the_index(selected_truth_t):
    print(selected_truth_t)
    print(selected_truth_t[0])
    true_arr = []
    false_arr = []
    for elem in selected_truth_t:
        count_t = 0
        count_f = 0
        for elem_2 in elem:
            if elem_2[-1] == True:
                count_t += 1
            else:
                count_f += 1
        true_arr.append(count_t)
        false_arr.append(count_f)

    if sum(true_arr)/sum(false_arr) > 1:
        for elem in selected_truth_t:
            for elem_2 in elem:
                if elem_2[-1] == True:
                    elem_2[-1] = False
                else:
                    elem_2[-1] = True

    true_arr = []
    false_arr = []
    for elem in selected_truth_t:
        count_t = 0
        count_f = 0
        for elem_2 in elem:
            if elem_2[-1] == True:
                count_t += 1
            else:
                count_f += 1
        true_arr.append(count_t)
        false_arr.append(count_f)

    print(sum(true_arr)/sum(false_arr))
    return selected_truth_t


'''
def printLevelOrder(root, lng):
    h = height(root) # or lng
    for i in range(1, h + 4):
        printCurrentLevel(root, i)
'''

'''
def insertCurrentLevel2(root, level, depth, id, my_dict, truth_t):
    print("LEVEL: ", level, "ID: ", id, "ROOT_ID: ", root.id)
    if level == 1:
        my_dict[root.id] = False
        result = find_first_overlap(truth_t, list(my_dict.values()))
        print("MY_DICT: ", my_dict)
        print("RESULT: ", result)
        if result is not None:
            if result[-1] is True:
                root.left = Node(depth, id, root)
                print("ID ", id, " ADDED TO THE LEFT")
            else:
                print("ID ", id, " WAS NOT ADDED TO THE LEFT")
        else:
            root.left = Node(depth, id, root)
            print("ID ", id, " ADDED TO THE LEFT")

        my_dict[root.id] = True
        result = find_first_overlap(truth_t, list(my_dict.values()))
        print("MY_DICT: ", my_dict)
        print("RESULT: ", result)
        if result is not None:
            if result[-1] is True:
                root.right = Node(depth, id, root)
                print("ID ", id, " ADDED TO THE RIGHT")
            else:
                print("ID ", id, " WAS NOT ADDED TO THE RIGHT")
        else:
            root.right = Node(depth, id, root)
            print("ID ", id, " ADDED TO THE RIGHT")
        return
    elif level > 1:
        if root.left is not None:
            print("ROOT NOWL:", root.id)
            my_dict[root.id] = False
            print("MY_DICT: ", my_dict)
            insertCurrentLevel(root.left, level - 1, depth, id, my_dict, truth_t)
        if root.right is not None:
            print("ROOT NOWR:", root.id)
            my_dict[root.id] = True
            print("MY_DICT: ", my_dict)
            insertCurrentLevel(root.right, level - 1, depth, id, my_dict, truth_t)
'''

'''
# Print nodes at a current level
def insertCurrentLevel(root, level, depth, id, my_dict, truth_t, arr):
    print("ARR: ", arr)
    if root is not False:
        print("LEVEL: ", level, "ID: ", id, "ROOT_ID: ", root.id)
    if level == 1:
        if root is not False:
            if root.left is not False:
                root.left = Node(depth, id, root)
                print("ID ", id, " ADDED TO THE LEFT")

                my_dict[root.id], my_dict[id] = False, False
                my_dict_values = [my_dict[key] for key in arr if key in my_dict]
                result = find_first_overlap(truth_t, my_dict_values)
                print("MY_DICT: ", my_dict)
                print("MY_DICT_VAL: ", my_dict_values)
                print("RESULT: ", result)
                if result is not None:
                    if result[-1] is False:
                        root.left.left = False
                        print("  LL False")
                print()

                my_dict[root.id], my_dict[id] = False, True
                my_dict_values = [my_dict[key] for key in arr if key in my_dict]
                result = find_first_overlap(truth_t, my_dict_values)
                print("MY_DICT: ", my_dict)
                print("MY_DICT_VAL: ", my_dict_values)
                print("RESULT: ", result)
                if result is not None:
                    if result[-1] is False:
                        root.left.right = False
                        print("  LR False")

                print()
        if root is not False:
            if root.right is not False:
                root.right = Node(depth, id, root)
                print("ID ", id, " ADDED TO THE RIGHT")

                my_dict[root.id], my_dict[id] = True, False
                my_dict_values = [my_dict[key] for key in arr if key in my_dict]
                result = find_first_overlap(truth_t, my_dict_values)
                print("MY_DICT: ", my_dict)
                print("MY_DICT_VAL: ", my_dict_values)
                print("RESULT: ", result)
                if result is not None:
                    if result[-1] is False:
                        root.right.left = False
                        print("  RL False")

                print()

                my_dict[root.id], my_dict[id] = True, True
                my_dict_values = [my_dict[key] for key in arr if key in my_dict]
                result = find_first_overlap(truth_t, my_dict_values)
                print("MY_DICT: ", my_dict)
                print("MY_DICT_VAL: ", my_dict_values)
                print("RESULT: ", result)
                if result is not None:
                    if result[-1] is False:
                        root.right.right = False
                        print("  RR False")

                print()
    elif level > 1:
        if root is not False:
            if root.left is not None:
                print("ROOT NOWL:", root.id)
                my_dict[root.id] = False
                print("MY_DICT: ", my_dict)
                print()
                insertCurrentLevel(root.left, level - 1, depth, id, my_dict, truth_t, arr)
        if root is not False:
            if root.right is not None:
                print("ROOT NOWR:", root.id)
                my_dict[root.id] = True
                print("MY_DICT: ", my_dict)
                print()
                insertCurrentLevel(root.right, level - 1, depth, id, my_dict, truth_t, arr)
'''

'''
def insertAtLastLevel(root, id, my_dict, truth_t, arr, lenr):
    h = height(root) #lnr
    print("HEIGHT: ", h)
    insertCurrentLevel(root, h, h, id, my_dict, truth_t, arr)
'''

'''
for arr in selected_elements[:2]:
    arr = list(Counter(arr).keys())
    for i in range(len(arr)):
        if arr[i] not in repeated:
            if root is None:
                root = Node(1, arr[i], None)
            else:
                insertAtLastLevel(root, arr[i], selected_truth_t)
            repeated.append(arr[i])
        else:
            continue
'''