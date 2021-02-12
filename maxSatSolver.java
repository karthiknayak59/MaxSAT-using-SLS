import java.util.Random;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Scanner;

public class MaxSATSolver implements Runnable {
    
    int VARIABLE_COUNT, LITERAL_COUNT_PER_CLAUSE, CLAUSE_COUNT;
    int MAX_STEPS;
    float P_CONST, DP_CONST;
    int maxRuntime;

    static int bestScore;
    static List<Boolean> bestResult;
    static long computeStart, bestTime;

    MaxSATSolver(int runtimeInMin) {

        newlySatisfiedClausesMap = new HashMap<>();
        newlyUnsatisfiedClausesMap = new HashMap<>();

        P_CONST = 0.5f;
        DP_CONST = 0.05f;
        MAX_STEPS = 10000;

        //Maximum runtime in milliseconds.
        maxRuntime = runtimeInMin * 60 * 1000;

        recentlyFlippedVariable = 1;
    }

    MaxSATSolver(MaxSATSolver _mss) {
        newlySatisfiedClausesMap = new HashMap<>();
        newlyUnsatisfiedClausesMap = new HashMap<>();

        P_CONST = _mss.P_CONST;
        DP_CONST = _mss.DP_CONST;
        MAX_STEPS = _mss.MAX_STEPS;

        //Maximum runtime in milliseconds.
        maxRuntime = _mss.maxRuntime;

        recentlyFlippedVariable = 1;

        VARIABLE_COUNT = _mss.VARIABLE_COUNT;
        LITERAL_COUNT_PER_CLAUSE = _mss.LITERAL_COUNT_PER_CLAUSE;
        CLAUSE_COUNT = _mss.CLAUSE_COUNT;
        clauses = new ArrayList<>();
        for (Clause c: _mss.clauses) {
            clauses.add(new Clause(new ArrayList<>(c.literals)));
        }

        occurences = new HashMap<>();
        for (int i = 1; i <= VARIABLE_COUNT; ++i) {
            occurences.put(i, new ArrayList<Clause>());
        }

        for (int i = 0; i < CLAUSE_COUNT; ++i) {
            Clause c = clauses.get(i);
            for (int k: c.literals) {
                occurences.get(Math.abs(k)).add(c);
            }
        }

    }

    class Clause {
        List<Integer> literals;
        List<Integer> absoluteLiterals;
        Boolean state, potentialState;

        Clause(List<Integer> _literals) {
            literals = _literals;
            absoluteLiterals = new ArrayList<>(literals.size());
            for (int i: literals) {
                absoluteLiterals.add(Math.abs(i));
            }
        }

        public String toString() {
            return literals.toString();
        }

        boolean evaluateState(List<Boolean> globalState) {
            for (int variable: literals) {
                boolean assignedValue = globalState.get(Math.abs(variable)-1);
                if (assignedValue && variable > 0)
                    return true;
                else if (!assignedValue && variable < 0)
                    return true;
            }
            return false;
        }

        boolean setState(List<Boolean> globalState) {
            state = evaluateState(globalState);
            return state;
        }

        boolean getState() {
            return state;
        }

        boolean getPotentialState() {
            return potentialState;
        }

        boolean setPotentialState(List<Boolean> globalState) {
            potentialState = evaluateState(globalState);
            return potentialState;
        }
    }

    //The input clauses.
    List<Clause> clauses;

    //Maps a literal to the clauses where it is found.
    Map<Integer, List<Clause>> occurences;

    Map<Integer, List<Clause>> newlySatisfiedClausesMap;
    Map<Integer, List<Clause>> newlyUnsatisfiedClausesMap;

    int recentlyFlippedVariable;

    /*
    Evaluates what-if scenarios. Flips a variable, and records the subsequent state changes in the clauses.
    This info is used to compute the score for a variable (which determines suitability for flipping).
    */
    void updateSatisfactionMaps(List<Boolean> globalState, Clause selectedClause) {
        //Get current evaluations of current state.

        //TODO: remove this.
        /*
        List<Boolean> currentClauseEvaluations = new ArrayList<>(CLAUSE_COUNT);
        for (int clause = 0; clause < CLAUSE_COUNT; ++clause) {
            currentClauseEvaluations.add(clauses.get(clause).setState(globalState));
        }
        */

        for (int variable: selectedClause.absoluteLiterals) {
            //Generate new state by flipping variable i.
            List<Boolean> mutatedState = new ArrayList<>(globalState);
            mutatedState.set(variable-1, !mutatedState.get(variable-1));

            //CLAUSE_COUNT
            List<Clause> newlySatisfiedClauses = new ArrayList<>();
            List<Clause> newlyUnsatisfiedClauses = new ArrayList<>();

            for (Clause c: occurences.get(variable)) {
                c.setPotentialState(mutatedState);

                //If a previously unsatisfied clause was satisfied
                if (!c.getState() && c.getPotentialState()) {
                    newlySatisfiedClauses.add(c);
                }
                //If a previously satisfied clause was unsatisfied
                else if (c.getState() && !c.getPotentialState()) {
                    newlyUnsatisfiedClauses.add(c);
                }
            }

            newlySatisfiedClausesMap.put(variable, newlySatisfiedClauses);
            newlyUnsatisfiedClausesMap.put(variable, newlyUnsatisfiedClauses);
        }
    }

    //Generates and returns a random assignment.
    List<Boolean> generateRandomAssignment() {
        List<Boolean> list = new ArrayList<>();
        Random random = new Random();
        for (int variable = 0; variable < VARIABLE_COUNT; ++variable) {
            list.add(random.nextBoolean());
        }
        return list;
    }

    //Returns the number of clauses satisfied by given assignment. 
    int evaluateAssignment(List<Boolean> state) {
        int count = 0;
        for (Clause c: clauses) {
            if (c.evaluateState(state))
                count += 1;
        }
        return count;
    }

    int getSatisfiedClauseCount() {
        int count = 0;
        for (Clause c: clauses) {
            if (c.getState())
                count += 1;
        }
        return count;
    }

    /*
    Returns a randomly selected clause from among clauses that are unsatisfied by the current assignment.
    */
    //TODO: use newlySatisfiedClausesMap and newlyUnsatisfiedClausesMap to compute.
    Clause selectClauseFromUnsatisfiedClauses() {
        //CLAUSE_COUNT
        List<Clause> unsatisfiedClauses = new ArrayList<>();
        for (Clause c: clauses) {
            if (!c.getState()) {
                unsatisfiedClauses.add(c);
            }
        }

        /*

        if (unsatisfiedClauses.size() == 1) {
            return unsatisfiedClauses.get(0);
        }

        System.out.println(String.format("%d ", unsatisfiedClauses.size()));
        */

        return unsatisfiedClauses.get(new Random().nextInt(unsatisfiedClauses.size()));
    }

    int getScore(int variable) {
        int var = Math.abs(variable);
        //System.out.println(var);
        return newlySatisfiedClausesMap.get(var).size() - newlyUnsatisfiedClausesMap.get(var).size();
    }

    /*
    Given a clause, picks a variable from it to be flipped.
    Implements Novelty++ algorithm.
    */
    int heuristic(Clause clause, List<Integer> lastFlipped) {
        Random random = new Random();

        //TODO: include this list in Clause object.
        List<Integer> variables = new ArrayList<>(LITERAL_COUNT_PER_CLAUSE);
        for (int i: clause.literals) {
            variables.add(Math.abs(i));
        }

        if (random.nextFloat() <= DP_CONST) {
            Collections.sort(variables, new Comparator<Integer>() {
                public int compare(Integer a, Integer b) {
                    return lastFlipped.get(a-1) - lastFlipped.get(b-1);
                }
            });
            return variables.get(0);
        }
        else {
            Collections.sort(variables, new Comparator<Integer>() {
                public int compare(Integer a, Integer b) {
                    int scoreA = getScore(a);
                    int scoreB = getScore(b);
                    if (scoreA == scoreB) {
                        return lastFlipped.get(a-1) - lastFlipped.get(b-1);
                    }
                    else {
                        return scoreB - scoreA;
                    }
                }
            });
//TODO CHECK
            #int first_var = variables.get(0), second_var = variables.get(1);
            if (first_var != recentlyFlippedVariable) {
                return first_var;
            }
            else {
                if (random.nextFloat() <= P_CONST) {
                    return second_var;
                }
                else {
                    return first_var;
                }
            }
        }
    }

    void solve() {
        System.out.println("Starting thread.");
        List<Boolean> bestState = generateRandomAssignment();
        int maxSatisfiedCount = evaluateAssignment(bestState);
        long startTime = System.currentTimeMillis();
        for (long i = 0; i < Long.MAX_VALUE; ++i) {

            List<Boolean> currentState = generateRandomAssignment();

            List<Integer> lastFlipped = new ArrayList<>(VARIABLE_COUNT);
            for (int k = 0; k < VARIABLE_COUNT; ++k) {
                lastFlipped.add(0);
            }

            for (Clause c: clauses) {
                c.setState(currentState);
            }

            if (getSatisfiedClauseCount() == CLAUSE_COUNT) {
                MaxSATSolver.setBest(currentState, getSatisfiedClauseCount());
                return;
            }

            for (int j = 0; j < MAX_STEPS; ++j) {

                Clause clause = selectClauseFromUnsatisfiedClauses();

                updateSatisfactionMaps(currentState, clause);

                int selectedVar = heuristic(clause, lastFlipped);

                currentState.set(selectedVar-1, !currentState.get(selectedVar-1));
                lastFlipped.set(selectedVar-1, lastFlipped.get(selectedVar-1) + 1);

                recentlyFlippedVariable = selectedVar;

                for (Clause c: newlySatisfiedClausesMap.get(recentlyFlippedVariable)) {
                    c.state = true;
                }

                for (Clause c: newlyUnsatisfiedClausesMap.get(recentlyFlippedVariable)) {
                    c.state = false;
                }

                int currentSatisfiedClauseCount = getSatisfiedClauseCount();

                if (MaxSATSolver.getBestScore() < currentSatisfiedClauseCount) {
                    MaxSATSolver.setBest(currentState, currentSatisfiedClauseCount);
                }

                if (MaxSATSolver.getBestScore() == CLAUSE_COUNT) {
                    return;
                }

                
                if (j % 100 == 0 && System.currentTimeMillis() - startTime > maxRuntime) {
                    System.out.println("Stopping due to timeout.");
                    return;
                }
            }
        }
        return;
    }

    public void run() {
        solve();
    }

    static int getBestScore() {
        return MaxSATSolver.bestScore;
    }

    static synchronized void setBest(List<Boolean> result, int score) {
        if (score > MaxSATSolver.bestScore) {
            MaxSATSolver.bestScore = score;
            MaxSATSolver.bestResult = new ArrayList<>(result);
            MaxSATSolver.bestTime = System.currentTimeMillis();
        }
    }


    void init() {
        Scanner scanner = new Scanner(System.in);
        VARIABLE_COUNT = Integer.parseInt(scanner.next());
        LITERAL_COUNT_PER_CLAUSE = Integer.parseInt(scanner.next());
        CLAUSE_COUNT = Integer.parseInt(scanner.next());

        clauses = new ArrayList<>(CLAUSE_COUNT);

        for (int i = 0; i < CLAUSE_COUNT; ++i) {
            List<Integer> literals = new ArrayList<>(LITERAL_COUNT_PER_CLAUSE);
            for (int j = 0; j < LITERAL_COUNT_PER_CLAUSE; ++j) {
                literals.add(Integer.parseInt(scanner.next()));
            }
            clauses.add(new Clause(literals));
        }
        
        occurences = new HashMap<>();
        for (int i = 1; i <= VARIABLE_COUNT; ++i) {
            occurences.put(i, new ArrayList<Clause>());
        }

        for (int i = 0; i < CLAUSE_COUNT; ++i) {
            Clause c = clauses.get(i);
            for (int k: c.literals) {
                occurences.get(Math.abs(k)).add(c);
            }
        }

        System.out.println("Data initialization complete.");
    
        //System.out.println(clauses);
        //System.out.println(occurences);

    }

    public static void main(String[] args) {
        MaxSATSolver.bestScore = 0;
        MaxSATSolver.bestResult = null;  

        if (args.length < 2 || args.length > 3) {
            System.out.println("Expected parameters: number of threads (>=2), maximum runtime in minutes.\nOptional parameter v, indicating that the result should be printed in full.");
            System.out.println("Example: MaxSATSolver 2 5 v; MaxSATSolver 4 1");
            return;
        }

        int THREAD_COUNT = Integer.parseInt(args[0]);
        int maxRuntime = Integer.parseInt(args[1]);
        boolean verbose = args.length == 3 ? true : false;

        System.out.println(String.format("Running %d worker threads, time limit %dm, verbose mode=%s.", THREAD_COUNT, maxRuntime, verbose));

        List<MaxSATSolver> workList = new ArrayList<>();
        List<Thread> threadList = new ArrayList<>();
        
        #workList.add(new MaxSATSolver(maxRuntime));
        #workList.get(0).init();
        #threadList.add(new Thread(workList.get(0)));

        for (int i = 1; i < THREAD_COUNT; ++i) {
            workList.add(new MaxSATSolver(workList.get(0)));
            threadList.add(new Thread(workList.get(i)));
        }

        MaxSATSolver.computeStart = System.currentTimeMillis();

        for (Thread t: threadList) {
            t.start();
        }

        try {
            while (true) {
                Thread.sleep(10000);
                boolean allDone = true;
                for (Thread t: threadList) {
                    if (t.isAlive()) {
                        allDone = false;
                        break;
                    }
                }
                if (allDone) {
                    break;
                }
                System.out.println(String.format("Best so far: %d @ %fs", MaxSATSolver.bestScore, (MaxSATSolver.bestTime - MaxSATSolver.computeStart)/1000.0F));
            }
        }
        catch (Exception e) {
            e.printStackTrace();
        }

        if (verbose) {
            System.out.println("\nBest assignment:\n");
            for (int i = 0; i < workList.get(0).VARIABLE_COUNT; ++i) {
                System.out.print(String.format("%d = %s ", i+1, MaxSATSolver.bestResult.get(i)));
            }
        }

        System.out.println(String.format("\nFinal result: %d/%d", workList.get(0).evaluateAssignment(bestResult), workList.get(0).CLAUSE_COUNT));
        System.out.println(String.format("Time taken to get best result: %fs", (MaxSATSolver.bestTime - MaxSATSolver.computeStart)/1000.0F));
        
    }
}
