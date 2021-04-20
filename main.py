import copy
import sys
import time
import os
from argparse import ArgumentParser

timeout = 0


def translateDir(l, c):
    """
    Function that returns a string equivalent to the sliding direction.
    The piece can only move up, down, to the right or to the left.
    For another direction, the function returns specific string.

    Args:
        l (int): The sliding direction on the column (up or down)
                 Can be -1, 0 or 1
        c (int): The sliding direction on the row (left or right)
                 Can be -1, 0 or 1

    Returns:
        str: Custom text representing the sliding direcion. If the direction is bad, then it returns "unknown"
    """
    if l == 0 and c == -1:
        return "to the left"
    if l == 0 and c == 1:
        return "to the right"
    if l == 1 and c == 0:
        return "down"
    if l == -1 and c == 0:
        return "up"
    return "unknown"


def specialBlockRectangle(specialCoords):
    """
    Function that finds the top left corner and bottom right corner of a rectangle
    in which the special piece would be framed

    Args:
        specialCoords: List of pairs representing the coordinates of the special block

    Returns:
        The coordinates of the top left and bottom right corner of the rectangle
    """
    startRow = float('inf')
    startCol = float('inf')
    finalRow = 0
    finalCol = 0
    for x, y in specialCoords:
        if x < startRow:
            startRow = x  # minimum row
        if y < startCol:
            startCol = y  # minimum column
        if x > finalRow:
            finalRow = x  # maximum row
        if y > finalCol:
            finalCol = y  # maximum column
    return startRow, startCol, finalRow, finalCol


# info about a node in the traversal tree (not the initial graph)
class SearchNode:
    """
    Class representing a node of the tree built during the search
    A node contains the following data:
        1. Information (the table configuration)
        2. Parent (the parent node in the search tree)
        3. Cost (the cost from the source node to the current node)
        4. H value (heuristic factor)
        5. F value (the function used by the A* algorithm: f = g + h)
        6. Text (the text that says the direction in which we moved the last piece)
    """
    def __init__(self, info, parent, cost=0, h=0, text=""):
        self.info = info
        self.parent = parent        # the parent in the traversal tree
        self.g = cost               # the cost
        self.h = h                  # the heuristic factor
        self.f = self.g + self.h
        self.moveText = text

    def getPath(self):
        """
        Method that returns a list of SearchNodes representing the path from the root to the current node (self)

        Returns:
            A list of SearchNodes on the path from the root to the current node
        """
        path = [self]
        node = self
        # going from node to its parent until we find the root
        while node.parent is not None:
            path.insert(0, node.parent)
            node = node.parent
        return path

    # also returns the length of the path
    def showPath(self, showCost=False, showLength=False):
        """
        Method that writes the information of the nodes on the path of the self node

        Args:
            showCost (bool): flag telling if we want to show the path cost
            showLength (bool): flag telling if we want to show the path length

        Returns:
            The length of the current path
        """
        path = self.getPath()
        i = 1
        string = ""
        for node in path:
            string += str(i) + ")\n" + str(node) + "\n"
            i += 1
        if showCost:
            string += "Cost: " + str(self.g)
        if showLength:
            string += "\nLength: " + str(len(path))
        outputFile.write(string + "\n")
        return len(path)

    def isInPath(self, newNodeInfo):
        """
        Method that checks if a node can be found in the path of the self node (regarding the node information)

        Args:
            newNodeInfo: the information that needs to be checked

        Returns:
            True if the node is found in the path, False otherwise
        """
        # node = the current node in the path
        # newNodeInfo = the node we are searching for in the path
        node = self
        while node is not None:
            if newNodeInfo == node.info:
                return True
            node = node.parent
        return False

    def __repr__(self):
        string = str(self.info)
        return string

    def __str__(self):
        string = self.moveText
        if string:
            string += "\n"
        string += '\n'.join([' '.join([str(self.info[j][i]) for i in range(1, len(self.info[j]) - 1)])
                            for j in range(1, len(self.info) - 1)]) + '\n'
        return string


# problem's graph
class Graph:
    """
    Class representing the problem search tree
    The graph contains the following information:
        1. the starting state configuration
        2. number of rows / columns of the table
        3. the coordinates of the exit
        4. the coordinates of a rectangle in which the exit can be framed
    """
    def __init__(self, filename):
        try:
            f = open(filename, 'r')
            fileContent = f.read().strip().split('\n')
            rowList = []
            for characters in fileContent:
                row = ['.']
                for i in range(len(characters)):
                    row.append(characters[i])
                row.append('.')
                rowList.append(row)
            rowList.insert(0, ['.' for _ in range(len(rowList[0]))])
            rowList.insert(len(rowList), ['.' for _ in range(len(rowList[0]))])

            eCoords = []
            self.noOfRows = len(rowList)
            self.noOfCols = len(rowList[0])
            topBorder = rowList[1]
            bottomBorder = rowList[self.noOfRows - 2]

            # going from 1 to width-1 to ignore the corners - they can never be exit
            for i in range(2, self.noOfCols - 2):
                # the exit will either be on the top or bottom border - never both
                if topBorder[i] != '#':
                    eCoords.append((1, i))
                if bottomBorder[i] != '#':
                    eCoords.append((self.noOfRows - 2, i))

            # going from 1 to height-1 to ignore the corners - they can never be exit
            for i in range(2, self.noOfRows - 2):
                if rowList[i][1] != '#':
                    eCoords.append((i, 1))
                if rowList[i][self.noOfCols - 2] != '#':
                    eCoords.append((i, self.noOfCols - 2))

            self.start = rowList
            self.exitCoords = eCoords

            self.startERow = float('inf')
            self.startECol = float('inf')
            self.finalERow = 0
            self.finalECol = 0
            for x, y in self.exitCoords:
                if x < self.startERow:
                    self.startERow = x
                if y < self.startECol:
                    self.startECol = y
                if x > self.finalERow:
                    self.finalERow = x
                if y > self.finalECol:
                    self.finalECol = y

            inputOk, errorText = self.checkInputData()

            if not inputOk:
                raise Exception(errorText)

        except IOError as e:
            sys.stderr.write(str(e))
            sys.exit(0)

    def checkInputData(self):
        """
        Method that checks for correct input data

        Returns:
            Pair of values boolean and string, True or False if the input is valid
            and a corresponding string
        """
        info = self.start

        # checking if the table has at least one row
        # at least 2 rows for the border and 2 rows for the outside
        # and one empty row inside
        rows = len(info)
        if rows <= 4:
            return False, "Cannot have a table with no inside space"

        # checking if all the rows have the same width
        length = len(info[0])
        for i in range(1, len(info)):
            if len(info[i]) != length:
                return False, "Wrong dimensions"

        # checking if the characters are ok
        for i in range(1, self.noOfRows - 1):
            for j in range(1, self.noOfCols - 1):
                if i == 1 or i == self.noOfRows - 2 or j == 1 or j == self.noOfCols - 2:
                    goodChars = ['.', '#', '*']
                else:
                    goodChars = ['.', '*']
                if info[i][j] in goodChars or (len(info[i][j]) == 1 and info[i][j].isalnum()):
                    pass
                else:
                    return False, "Invalid characters used: " + str(info[i][j])

        # checking to have exactly one exit
        exitCoords = self.exitCoords
        if len(exitCoords) == 0:
            return False, "Exit required"

        rows = set()
        cols = set()
        for r, c in exitCoords:
            rows.add(r)
            cols.add(c)
        if len(rows) > 1 and len(cols) > 1:
            return False, "Only one exit permitted"

        # checking to have unique names for the pieces
        pieces = set()
        infoCopy = copy.deepcopy(info)
        for i in range(1, self.noOfRows - 1):
            for j in range(1, self.noOfCols - 1):
                if infoCopy[i][j] not in ['.', '#']:
                    if infoCopy[i][j] in pieces:
                        return False, "Cannot have more pieces named identically"
                    pieces.add(infoCopy[i][j])
                    self.removePiece(infoCopy, i, j)

        return True, "Input ok"

    def removePiece(self, nodeInfo, row, col):
        """
        Method that removes a piece from the board, used only for verifying the input data

        Args:
            nodeInfo: the node information from where we want to remove the piece
            row: the row coordinate of the piece to be removed
            col: the column coordinate of the piece to be removed
        """
        piece = nodeInfo[row][col]
        queue = [(row, col)]
        dirs = [(-1, 0), (0, 1), (1, 0), (0, -1)]  # top, right, bottom, left
        while queue:
            currentR, currentC = queue.pop(0)
            nodeInfo[currentR][currentC] = '.'
            for d in dirs:
                newR = currentR + d[0]
                newC = currentC + d[1]
                if 0 <= newR <= self.noOfRows - 1 and 0 <= newC <= self.noOfCols - 1:
                    if nodeInfo[newR][newC] == piece:
                        queue.append((newR, newC))

    def goalTest(self, currentNode):
        """
        Method that checks if a given state is a final state (there is no special block in the table)

        Args:
            currentNode: the information that needs to be checked

        Returns:
            True if the given node is a final state, False otherwise
        """
        box = currentNode.info
        for row in box:
            for piece in row:
                if piece == '*':
                    return False
        return True

    def specialBlock(self, nodeInfo):
        """
        Method that finds the coordinates of the special block in a specific state

        Args:
            nodeInfo: the state configuration where we want to find the special block

        Returns:
            A list of pairs representing the coordinates of the special block
        """
        specialCoords = []
        for i in range(1, self.noOfRows - 1):
            for j in range(1, self.noOfCols - 1):
                if nodeInfo[i][j] == '*':
                    specialCoords.append((i, j))
        return specialCoords

    # generates the successors as SearchNodes
    def generateSuccessors(self, currentNode, heuristic="trivial"):
        """
        Method that generates all the successor states of a given state

        Args:
            currentNode: the node that needs to be extended (generating its successors)
            heuristic: the heuristic used for calculating the h value of the state

        Returns:
            A list of SearchNodes containing the information of the successors
        """
        def movePiece(cRow, cCol, piece, rowOffsetDest, colOffsetDest, currBox):
            """
            Local function that tries to move a piece in a specific direction

            Args:
                cRow (int): the current row of the piece
                cCol (int): the current column of the piece
                piece (char): the piece character (name)
                rowOffsetDest (int): the direction in which we want to move the piece on the column (up or down)
                colOffsetDest (int): the direction in which we want to move the piece on the row (left or right)
                currBox: the configuration of the current box where we move the piece

            Returns:
                The function returns 3 values:
                    1. True, if the move was successful, False otherwise
                    2. The configuration of the table after the move was made, empty state otherwise
                    3. The cost of the piece if the piece was moved, 0 otherwise
            """

            visited = [[0 for _ in range(len(currBox[0]))] for _ in range(len(currBox))]

            # queue of positions (row, column) of the parts of the current piece we want to move
            # first, the queue has the current position
            queue = [(cRow, cCol)]
            pieceCost = 0
            # while there still exist parts of the piece to move
            while queue:
                l, c = queue.pop(0)
                pieceCost += 1
                visited[l][c] = 1
                # checking if there is any space to move the part
                if currBox[l + rowOffsetDest][c + colOffsetDest] != '.':
                    return False, [], 0
                # moving the part of the piece
                if 0 <= l + rowOffsetDest <= self.noOfRows - 1 and 0 <= c + colOffsetDest <= self.noOfCols - 1:
                    currBox[l + rowOffsetDest][c + colOffsetDest] = piece
                    currBox[l][c] = '.'
                elif piece == '*':
                    currBox[l][c] = '.'

                # getting all the directions
                # and checking if any is part of the current piece
                dirs = [(-1, 0), (0, 1), (1, 0), (0, -1)]  # top, right, bottom, left
                dirs.remove((rowOffsetDest, colOffsetDest))
                for d in dirs:
                    newL = l + d[0]
                    newC = c + d[1]
                    if 0 <= newL <= self.noOfRows - 1 and 0 <= newC <= self.noOfCols - 1:
                        # if the space where I go is part of my current piece
                        # and hasn't been explored yet, then we add it to the queue
                        if currentNode.info[newL][newC] == piece and visited[newL][newC] == 0 and \
                           (newL, newC) not in queue:
                            queue.append((newL, newC))

            if piece == '*':
                pieceCost = 1
            return True, currBox, pieceCost

        sList = []
        box = currentNode.info

        directions = [(-1, 0), (0, 1), (1, 0), (0, -1)]  # top, right, bottom, left
        # for each empty slot in the box, we try to move every neighbour piece
        # if a piece was moved in the empty slot, then it is a successor
        for row in range(self.noOfRows):
            for col in range(self.noOfCols):
                if box[row][col] == '.':  # finding an empty slot
                    # checking each neighbour to be a part of a piece
                    for direction in directions:
                        newRow = row + direction[0]
                        newCol = col + direction[1]
                        if 0 <= newRow <= self.noOfRows - 1 and 0 <= newCol <= self.noOfCols - 1:
                            # if I'm on the outside of the box and I try to move a piece that is not the special piece,
                            # then I ignore this move
                            if (row == 0 or row == self.noOfRows - 1 or col == 0 or col == self.noOfCols - 1) \
                                    and box[newRow][newCol] != '*':
                                continue
                            # checking for a valid piece to move
                            if box[newRow][newCol] not in ['.', '#']:
                                dirText = "Moving piece " + str(box[newRow][newCol]) + " " \
                                          + translateDir(-direction[0], -direction[1])
                                currentBox = copy.deepcopy(box)
                                ok, newInfo, moveCost = movePiece(newRow, newCol, box[newRow][newCol],
                                                                  -direction[0], -direction[1], currentBox)
                                # if the move was successful
                                if ok:
                                    # resetting the outside of the box near the exit
                                    for coords in self.exitCoords:
                                        # if the exit is on the top border
                                        if coords[0] == 1:
                                            newInfo[coords[0] - 1][coords[1]] = '.'
                                        # if the exit is on the bottom border
                                        elif coords[0] == self.noOfRows - 2:
                                            newInfo[coords[0] + 1][coords[1]] = '.'
                                        # if the exit is on the right border
                                        elif coords[1] == self.noOfCols - 2:
                                            newInfo[coords[0]][coords[1] + 1] = '.'
                                        # if the exit is on the left border
                                        elif coords[1] == 1:
                                            newInfo[coords[0]][coords[1] - 1] = '.'

                                    if not currentNode.isInPath(newInfo):
                                        for node in sList:
                                            if node.info == newInfo:
                                                ok = False
                                        if ok:
                                            sList.append(SearchNode(newInfo, currentNode, currentNode.g + moveCost,
                                                                    self.calculate_h(newInfo, heuristic), dirText))
        return sList

    def manhattanDistance(self, nodeInfo):
        """
        Method that calculates the Manhattan distance from the current position of the special block
        to the exit and until the block is eliminated
        The Manhattan distance is the number of rows added to the number of columns
        from the special block to the exit (final state)

        Args:
            nodeInfo: the current state of the table

        Returns:
             A pair representing the number of rows and the number of columns that the special piece
             needs to be moved
        """
        # finding the coords of the special piece
        specialCoords = self.specialBlock(nodeInfo)

        # calculate the start coord and end coord (the rectangle in which the special piece can be framed)
        deltaRow = deltaCol = 0
        if specialCoords:
            startRow, startCol, finalRow, finalCol = specialBlockRectangle(specialCoords)

            if self.exitCoords[0][0] == 1:  # the exit is on the top border
                deltaRow = finalRow
                deltaCol = abs(finalCol - self.finalECol)
            elif self.exitCoords[0][0] == self.noOfRows - 2:  # the exit is on the bottom border
                deltaRow = abs(self.noOfRows - startRow) - 1
                deltaCol = abs(startCol - self.startECol)
            elif self.exitCoords[0][1] == 1:  # the exit is on the left border
                deltaRow = abs(finalRow - self.finalERow)
                deltaCol = finalCol
            elif self.exitCoords[0][1] == self.noOfCols - 2:  # the exit is on the right border
                deltaRow = abs(startRow - self.startERow)
                deltaCol = abs(startCol - self.startECol)
        return deltaRow, deltaCol

    def calculate_h(self, nodeInfo, heuristic="trivial"):
        if heuristic == "trivial":
            if self.goalTest(SearchNode(nodeInfo, None, 0, 0)):
                return 0
            else:
                return 1

        elif heuristic == "admissible":           # Manhattan distance
            deltaL, deltaC = self.manhattanDistance(nodeInfo)
            h = deltaL + deltaC
            return h

        elif heuristic == "nonadmissible":          # the number of blocks around
            specialCoords = self.specialBlock(nodeInfo)
            piecesAround = set()
            # checking if the neighbours are valid pieces
            # and making a set of the neighbours
            for row, col in specialCoords:
                if nodeInfo[row - 1][col] not in ['.', '#', '*']:
                    piecesAround.add(nodeInfo[row - 1][col])

                if nodeInfo[row][col + 1] not in ['.', '#', '*']:
                    piecesAround.add(nodeInfo[row][col + 1])

                if nodeInfo[row + 1][col] not in ['.', '#', '*']:
                    piecesAround.add(nodeInfo[row + 1][col])

                if nodeInfo[row][col - 1] not in ['.', '#', '*']:
                    piecesAround.add(nodeInfo[row][col - 1])
            return len(piecesAround)

        else:
            sys.stderr.write('Wrong type of heuristic!')
            sys.exit(1)

    def __repr__(self):
        string = ""
        for (k, v) in self.__dict__.items():
            string += "{} = {}\n".format(k, v)
        return string


def uniform_cost(graph, noOfSolutions=1):
    global timeout

    # queue of SearchNodes, in the order in which we want to expand them
    queue = [SearchNode(graph.start, None, 0, graph.calculate_h(graph.start))]
    sol = 0
    start_time = time.time()
    numberOfComputedNodes = 1
    maximumNumberOfNodes = 1

    while len(queue) > 0 and time.time() - start_time < timeout:
        currentNode = queue.pop(0)

        if graph.goalTest(currentNode):
            sol += 1
            outputFile.write("Solution " + str(sol) + ":\n")
            currentNode.showPath(True, True)
            outputFile.write("Time: " + str(time.time() - start_time) + "\n")
            outputFile.write("Maximum number of nodes in memory: " + str(maximumNumberOfNodes) + "\n")
            outputFile.write("Number of computed nodes: " + str(numberOfComputedNodes) + "\n")
            outputFile.write("\n---------------\n\n")
            noOfSolutions -= 1
            if noOfSolutions == 0:
                return

        listOfSuccessors = graph.generateSuccessors(currentNode)
        numberOfComputedNodes += len(listOfSuccessors)
        # for each successor of the current node,
        # we try to put it in the queue
        for s in listOfSuccessors:
            found = False
            for node in queue:
                if s.info == node.info:
                    found = True
            # if the node already exists, we ignore it
            if found:
                continue
            found = False
            i = 0
            for i in range(len(queue)):
                # sorting by cost g
                if queue[i].g >= s.g:
                    found = True
                    break
            if found:
                queue.insert(i, s)
            else:
                queue.append(s)

        maximumNumberOfNodes = max(maximumNumberOfNodes, len(queue))

    if len(queue) != 0:
        outputFile.write("Timed out\n\n")
    elif sol == 0:
        outputFile.write("The problem doesn't have any solution!\n\n")


def a_star(graph, noOfSolutions, heuristic):

    # queue of SearchNodes, in the order in which we want to expand them
    queue = [SearchNode(graph.start, None, 0, graph.calculate_h(graph.start))]
    sol = 0
    start_time = time.time()
    maximumNumberOfNodes = 1
    numberOfComputedNodes = 1

    while len(queue) > 0 and time.time() - start_time < timeout:
        currentNode = queue.pop(0)

        if graph.goalTest(currentNode):
            sol += 1
            outputFile.write("Solution " + str(sol) + ":\n")
            currentNode.showPath(True, True)
            outputFile.write("Time: " + str(time.time() - start_time) + "\n")
            outputFile.write("Maximum number of nodes in memory: " + str(maximumNumberOfNodes) + "\n")
            outputFile.write("Number of computed nodes: " + str(numberOfComputedNodes) + "\n")
            outputFile.write("\n---------------\n\n")
            noOfSolutions -= 1
            if noOfSolutions == 0:
                return

        listOfSuccessors = graph.generateSuccessors(currentNode, heuristic)
        numberOfComputedNodes += len(listOfSuccessors)
        # for each successor of the current node,
        # we try to put it in the queue
        for s in listOfSuccessors:
            found = False
            for node in queue:
                if s.info == node.info:
                    found = True
            # if the node already exists, we ignore it
            if found:
                continue
            i = 0
            found = False
            for i in range(len(queue)):
                # sorting by the value of f (g + h)
                if queue[i].f >= s.f:
                    found = True
                    break
            if found:
                queue.insert(i, s)
            else:
                queue.append(s)

        maximumNumberOfNodes = max(maximumNumberOfNodes, len(queue))

    if len(queue) != 0:
        outputFile.write("Timed out\n\n")
    elif sol == 0:
        outputFile.write("The problem doesn't have any solution!\n\n")


def a_star_opt(graph, heuristic='trivial'):

    # OPEN is a queue of SearchNodes that we want to expand
    OPEN = [SearchNode(graph.start, None, 0, graph.calculate_h(graph.start))]
    sol = 0
    start_time = time.time()
    maximumNumberOfNodes = 1
    numberOfComputedNodes = 1

    # CLOSED is a queue of expanded nodes
    CLOSED = []
    while len(OPEN) > 0 and time.time() - start_time < timeout:
        # taking the first node from OPEN and adding it to CLOSED
        currentNode = OPEN.pop(0)
        CLOSED.append(currentNode)

        if graph.goalTest(currentNode):
            sol += 1
            outputFile.write("Solution:\n")
            currentNode.showPath(True, True)
            outputFile.write("Time: " + str(time.time() - start_time) + "\n")
            outputFile.write("Maximum number of nodes in memory: " + str(maximumNumberOfNodes) + "\n")
            outputFile.write("Number of computed nodes: " + str(numberOfComputedNodes) + "\n")
            outputFile.write("\n----------------\n\n")
            return

        listOfSuccessors = graph.generateSuccessors(currentNode, heuristic)
        numberOfComputedNodes += len(listOfSuccessors)
        i = 0
        while i < len(listOfSuccessors):
            s = listOfSuccessors[i]
            i += 1
            found = False
            for cNode in OPEN:
                if s.info == cNode.info:            # if the successor is in OPEN
                    found = True
                    # checking if the successor's f is >= than the previously found f of the same successor
                    if s.f >= cNode.f:
                        listOfSuccessors.remove(s)         # if the found successor has bigger f, then we ignore it
                        i -= 1
                    else:
                        OPEN.remove(cNode)              # if the successor has smaller f, then we remove it from OPEN
            # if the successor isn't in OPEN
            if not found:
                for cNode in CLOSED:
                    if s.info == cNode.info:            # if the successor is in CLOSED
                        if s.f >= cNode.f:              # if the found successor has bigger f, then we ignore it
                            listOfSuccessors.remove(s)
                            i -= 1
                        else:
                            CLOSED.remove(cNode)        # if the successor has smaller f, then we remove it from OPEN
                                                        # (we want to expand it again with a smaller cost)
        for s in listOfSuccessors:
            i = 0
            found = False
            for i in range(len(OPEN)):
                # sorting by f
                if OPEN[i].f >= s.f:
                    found = True
                    break
            if found:
                OPEN.insert(i, s)
            else:
                OPEN.append(s)

        maximumNumberOfNodes = max(maximumNumberOfNodes, len(OPEN) + len(CLOSED))

    if len(OPEN) != 0:
        outputFile.write("Timed out\n\n")
    elif sol == 0:
        outputFile.write("The problem doesn't have any solution!\n\n")


def ida_star(graph, noOfSolutions, heuristic='trivial'):
    startNode = SearchNode(graph.start, None, 0, graph.calculate_h(graph.start))
    limit = startNode.f
    start_time = time.time()
    numberOfComputedNodes = 1

    while True and time.time() - start_time < timeout:
        noOfSolutions, res, maximumNumberOfNodes, numberOfComputedNodes = \
            constructPath(graph, startNode, limit, noOfSolutions, start_time, heuristic,
                          1, numberOfComputedNodes)
        if res == "done":
            break
        if res == "timeout":
            outputFile.write("Timed out\n\n")
            break
        if res == float('inf'):
            outputFile.write("The problem doesn't have any solution!\n\n")
            break
        limit = res


def constructPath(graph, currentNode, limit, noOfSolutions, start_time, heuristic, maxNoOfNodes, noOfCompNodes):
    if currentNode.f > limit:
        return noOfSolutions, currentNode.f, maxNoOfNodes, noOfCompNodes

    if graph.goalTest(currentNode) and currentNode.f == limit:
        outputFile.write("Solution:\n")
        currentNode.showPath(True, True)
        outputFile.write("Time: " + str(time.time() - start_time) + "\n")
        outputFile.write("Maximum number of nodes in memory: " + str(maxNoOfNodes) + "\n")
        outputFile.write("Number of computed nodes: " + str(noOfCompNodes) + "\n")
        outputFile.write("\n----------------\n\n")
        noOfSolutions -= 1
        if noOfSolutions == 0:
            return 0, "done", maxNoOfNodes, noOfCompNodes

    listOfSuccessors = graph.generateSuccessors(currentNode, heuristic)
    noOfCompNodes += len(listOfSuccessors)
    maxNoOfNodes += len(listOfSuccessors)
    mini = float('inf')

    if time.time() - start_time >= timeout:
        return 0, "timeout", maxNoOfNodes, noOfCompNodes

    for s in listOfSuccessors:
        noOfSolutions, res, newMaxi, noOfCompNodes = \
            constructPath(graph, s, limit, noOfSolutions, start_time, heuristic,
                          maxNoOfNodes, noOfCompNodes)

        if res == "done":
            return 0, "done", maxNoOfNodes, noOfCompNodes

        if res == "timeout":
            return 0, "timeout", maxNoOfNodes, noOfCompNodes

        if res < mini:
            mini = res
        maxNoOfNodes = max(maxNoOfNodes, newMaxi)

    return noOfSolutions, mini, maxNoOfNodes, noOfCompNodes


if __name__ == '__main__':
    parser = ArgumentParser(description='Klotski puzzle solver')
    parser.add_argument('-if', '--input_folder',
                        dest='input_folder',
                        help='The path of the folder containing the input files')
    parser.add_argument('-of', '--output_folder',
                        dest='output_folder',
                        help='The path of the folder containing the output files')
    parser.add_argument('-nsol',
                        dest='nsol',
                        help='The wanted number of solutions')
    parser.add_argument('-t', '--timeout',
                        dest='timeout',
                        help='The timeout for the searching algorithms')

    args = vars(parser.parse_args())

    inputFolderPath = args['input_folder']
    outputFolderPath = args['output_folder']
    NSOL = int(args['nsol'])
    timeout = float(args['timeout'])

    fileList = os.listdir(inputFolderPath)
    if not os.path.exists(outputFolderPath):
        os.mkdir(outputFolderPath)

    for file in fileList:
        outputFileName = "output_" + file
        if outputFolderPath[-1] != '/':
            outputFolderPath += '/'
        if inputFolderPath[-1] != '/':
            inputFolderPath += '/'

        inputFilePath = inputFolderPath + file
        outputFilePath = outputFolderPath + outputFileName

        # creating the output file
        outputFile = open(outputFilePath, 'w')

        print("RUNNING FOR: ", file)

        # running the algorithms and writing the output to the file
        gr = Graph(inputFilePath)
        outputFile.write("################## Solutions obtained with UCS ##################\n")
        uniform_cost(gr, noOfSolutions=NSOL)
        print('Done UCS')

        outputFile.write('\n')

        outputFile.write("################## Solutions obtained with A* ##################\n")
        outputFile.write("TRIVIAL HEURISTIC\n")
        a_star(gr, noOfSolutions=NSOL, heuristic="trivial")
        print('Done A* trivial heuristic')

        outputFile.write("ADMISSIBLE HEURISTIC\n")
        a_star(gr, noOfSolutions=NSOL, heuristic="admissible")
        print('Done A* admissible heuristic')

        outputFile.write("NONADMISSIBLE HEURISTIC\n")
        a_star(gr, noOfSolutions=NSOL, heuristic="nonadmissible")
        print('Done A* nonadmissible heuristic')

        outputFile.write('\n')

        outputFile.write("################## Solutions obtained with optimised A* ##################\n")
        outputFile.write("TRIVIAL HEURISTIC\n")
        a_star_opt(gr, "trivial")
        print('Done optimised A* trivial heuristic')

        outputFile.write("ADMISSIBLE HEURISTIC\n")
        a_star_opt(gr, "admissible")
        print('Done optimised A* admissible heuristic')

        outputFile.write("NONADMISSIBLE HEURISTIC\n")
        a_star_opt(gr, "nonadmissible")
        print('Done optimised A* nonadmissible heuristic')

        outputFile.write('\n')

        outputFile.write("################## Solutions obtained with IDA*: ##################\n")
        outputFile.write("TRIVIAL HEURISTIC\n")
        ida_star(gr, noOfSolutions=NSOL, heuristic="trivial")
        print('Done IDA* trivial heuristic')

        outputFile.write("ADMISSIBLE HEURISTIC\n")
        ida_star(gr, noOfSolutions=NSOL, heuristic="admissible")
        print('Done IDA* admissible heuristic')

        outputFile.write("NONADMISSIBLE HEURISTIC\n")
        ida_star(gr, noOfSolutions=NSOL, heuristic="nonadmissible")
        print('Done IDA* nonadmissible heuristic')

        outputFile.write('\n')

        # closing the file
        outputFile.close()

        print()
