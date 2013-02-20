package submit;

// some useful things to import. add any additional imports you need.
import java.util.*;
import joeq.Compiler.Quad.*;
import joeq.Compiler.Quad.Operand.*;
import joeq.Main.Helper;
import flow.Flow;

/**
 * Skeleton class for implementing a reaching definition analysis
 * using the Flow.Analysis interface.
 */
public class RedundantNullChecks implements Flow.Analysis {
	

    /**
     * Class for the dataflow objects in the ReachingDefs analysis.
     * You are free to change this class or move it to another file.
     */
    public static class DefinitionTable implements Flow.DataflowObject {
		//list of redundant null checks
		private SortedMap<String, HashSet<Integer>> map;

		//null checks seen
		private Set<String> nullChecksSeen = new HashSet<String>(); 
		
		//initialized to all the variables (registers) in the method
		private static Set<String> core = new HashSet<String>();
		public static void reset() { core.clear(); }
		
		public static void register(String key) {
			core.add(key);
		}
		
		//initialized with all registers associated with an empty list of quads
		//aka no redundant null checks seen
		public DefinitionTable() {
			map = new TreeMap<String, HashSet<Integer>>();
			for(String key : core) {
				map.put(key, new HashSet<Integer>());
			}
			nullChecksSeen.clear(); //AJD
		}

        /**
         * Methods from the Flow.DataflowObject interface.
         * See Flow.java for the meaning of these methods.
         * These need to be filled in.
         */
        public void setToTop() {
            for(HashSet<Integer> set : map.values()) {
                set.clear();
            }
        }
        
        // do we need this?
        public void setToBottom() { System.out.println("Why did you call setToBottom()?");}

        /*The intersection. I suppose at this point we just need to intersect the list of 
		observed null checks*/
		public void meetWith (Flow.DataflowObject o) {
            ArrayList<Integer> lhsTempList;
	        DefinitionTable rhs = (DefinitionTable) o;

			this.nullChecksSeen.retainAll(rhs.nullChecksSeen);

            /*for(Map.Entry<String, ArrayList<Integer>> rhsMapEntry : rhs.map.entrySet()) {
                lhsTempList = map.get(rhsMapEntry.getKey());
                for(Integer rhsListEntry : rhsMapEntry.getValue()) {
                    if(!presentInList(lhsTempList, rhsListEntry))
                        lhsTempList.add(rhsListEntry);    
                }
                map.put(rhsMapEntry.getKey(), lhsTempList);
            }*/
        }

        /*private boolean presentInList(ArrayList<Integer> list, Integer val) {
            for(Integer cur : list) 
                if(cur.equals(val)) return true;
            return false;
        }*/

        public void copy (Flow.DataflowObject o) {
            DefinitionTable rhs = (DefinitionTable) o;
            map.clear();
            for(Map.Entry<String, HashSet<Integer>> rhsMapEntry : rhs.map.entrySet()) {
                map.put(rhsMapEntry.getKey(), rhsMapEntry.getValue());
            }
        }

		/*Implement the transfer function. 
		If the register in question is NOT in the current DFO's NullChecksSeen list,
		add it to RedundantNullChecks aka the map. 
		Afterwards, add register to the NullChecksSeen set.*/
        public void killgen(String key, Integer id)
        {
			//register null checked before, current null check redundant
			if(nullChecksSeen.contains(key)){
				HashSet<Integer> tempSet = new HashSet<Integer>();
				tempSet = map.get(key);
				tempSet.add(id);
				map.put(key, tempSet);				
			}
			//always add the null check to the seen list (it's a set, so duplicates impossible)
			nullChecksSeen.add(key);
        }

        /**
         * toString() method for the dataflow objects which is used
         * by postprocess() below.  The format of this method must
         * be of the form "[ID0, ID1, ID2, ...]", where each ID is
         * the identifier of a quad defining some register, and the
         * list of IDs must be sorted.  See src/test/test.rd.out
         * for example output of the analysis.  The output format of
         * your reaching definitions analysis must match this exactly.
         */
        @Override
        public String toString() { 
            String retval = new String("[");
            String comma = new String("");
            ArrayList<Integer> combinedList = new ArrayList<Integer>();

            for(Map.Entry<String, HashSet<Integer>> entry : map.entrySet())
                combinedList.addAll(entry.getValue());
            Collections.sort(combinedList);

            for(Integer cur : combinedList)
            {
                retval = retval + comma + cur.toString();
                comma = ", ";
            }

            return retval + "]"; 
        }

        @Override
        public boolean equals(Object o) {
            if(o instanceof DefinitionTable) {
                return map.equals(((DefinitionTable)o).map);
            }
            return false;
        }
    }

    /**
     * Dataflow objects for the interior and entry/exit points
     * of the CFG. in[ID] and out[ID] store the entry and exit
     * state for the input and output of the quad with identifier ID.
     *
     * You are free to modify these fields, just make sure to
     * preserve the data printed by postprocess(), which relies on these.
     */
    private DefinitionTable[] in, out;
    private DefinitionTable entry, exit;

    /**
     * This method initializes the datflow framework.
     *
     * @param cfg  The control flow graph we are going to process.
     */
    public void preprocess(ControlFlowGraph cfg) {
        // this line must come first.
        System.out.println("Method: "+cfg.getMethod().getName().toString());

        // get the amount of space we need to allocate for the in/out arrays.
        QuadIterator qit = new QuadIterator(cfg);
        int max = 0;
        while (qit.hasNext()) {
            int id = qit.next().getID();
            if (id > max) 
                max = id;
        }
        max += 1;

        // allocate the in and out arrays.
        in = new DefinitionTable[max];
        out = new DefinitionTable[max];
        qit = new QuadIterator(cfg);

        DefinitionTable.reset();

        /************************************************
         * Your remaining initialization code goes here *
         ************************************************/
        
        int numargs = cfg.getMethod().getParamTypes().length;

        for(int i = 0; i < numargs; i++)
        {
            DefinitionTable.register("R" + i);
        }
        
        while (qit.hasNext()) {
            Quad q = qit.next();
            for (RegisterOperand def : q.getDefinedRegisters()) {
                DefinitionTable.register(def.getRegister().toString());
            }
            for (RegisterOperand use : q.getUsedRegisters()) {
                DefinitionTable.register(use.getRegister().toString());
            }
        }
        
        // initialize DefinitionTable in transfer function object
        transferFunction.val = new DefinitionTable();

        // initialize the entry and exit points.
        entry = new DefinitionTable();
        exit = new DefinitionTable();
        // initialize the contents of in and out.
        qit = new QuadIterator(cfg);
        while (qit.hasNext()) {
            int id = qit.next().getID();
            in[id] = new DefinitionTable();
            out[id] = new DefinitionTable();
        }

    }

    /**
     * This method is called after the fixpoint is reached.
     * It must print out the dataflow objects associated with
     * the entry, exit, and all interior points of the CFG.
     * Unless you modify in, out, entry, or exit you shouldn't
     * need to change this method.
     *
     * @param cfg  Unused.
     */
    public void postprocess (ControlFlowGraph cfg) {
        System.out.println("entry: " + entry.toString());
        for (int i=0; i<in.length; i++) {
            if (in[i] != null) {
                System.out.println(i + " in:  " + in[i].toString());
                System.out.println(i + " out: " + out[i].toString());
            }
        }
        System.out.println("exit: " + exit.toString());
    }

    /**
     * Other methods from the Flow.Analysis interface.
     * See Flow.java for the meaning of these methods.
     * These need to be filled in.
     */
    public boolean isForward () { return true; }
    
    public Flow.DataflowObject getEntry() {
        DefinitionTable result = new DefinitionTable();
        result.copy(entry);
        return result; 
    }
    
    public Flow.DataflowObject getExit() {
        DefinitionTable result = new DefinitionTable();
        result.copy(exit);
        return result; 
    }

    public void setEntry(Flow.DataflowObject value) {
        entry = (DefinitionTable)value;
    }
    
    public void setExit(Flow.DataflowObject value) {
        exit = (DefinitionTable)value;
    }

    public Flow.DataflowObject getIn(Quad q) { 
        Flow.DataflowObject result = newTempVar();
        result.copy(in[q.getID()]); 
        return result;
    }

    public Flow.DataflowObject getOut(Quad q) { 
        Flow.DataflowObject result = newTempVar();
        result.copy(out[q.getID()]); 
        return result;
    }

    public void setIn(Quad q, Flow.DataflowObject value) { 
        in[q.getID()].copy(value); 
    }

    public void setOut(Quad q, Flow.DataflowObject value) { 
        out[q.getID()].copy(value); 
    }
    
    public Flow.DataflowObject newTempVar() { 
        return new DefinitionTable(); 
    }

    public void processQuad(Quad q) {
        transferFunction.val.copy(in[q.getID()]);
        Helper.runPass(q, transferFunction);
        out[q.getID()].copy(transferFunction.val);
    }
    
    private TransferFunction transferFunction = new TransferFunction();

    public static class TransferFunction extends QuadVisitor.EmptyVisitor
    {
        DefinitionTable val;

        @Override 
        public void visitMove(Quad q)
        {
            //val.killgen(Operator.Move.getDest(q).getRegister().toString(), q.getID());
        }

        @Override
        public void visitBinary(Quad q)
        {
            //val.killgen(Operator.Binary.getDest(q).getRegister().toString(), q.getID());
        }

        @Override
        public void visitUnary(Quad q)
        {
            //val.killgen(Operator.Unary.getDest(q).getRegister().toString(), q.getID());
        }

        @Override
        public void visitALoad(Quad q)
        {
            //val.killgen(Operator.ALoad.getDest(q).getRegister().toString(), q.getID());
        }
        
        @Override
        public void visitALength(Quad q)
        {
            //val.killgen(Operator.ALength.getDest(q).getRegister().toString(), q.getID());
        }
        
        @Override
        public void visitGetstatic(Quad q)
        {
            //val.killgen(Operator.Getstatic.getDest(q).getRegister().toString(), q.getID());
        }
        
        @Override
        public void visitGetfield(Quad q)
        {
            //val.killgen(Operator.Getfield.getDest(q).getRegister().toString(), q.getID());
        }
        @Override
        public void visitInstanceOf(Quad q)
        {
            //val.killgen(Operator.InstanceOf.getDest(q).getRegister().toString(), q.getID());
        }
        
        @Override
        public void visitNew(Quad q)
        {
            //val.killgen(Operator.New.getDest(q).getRegister().toString(), q.getID());
        }
        
        @Override
        public void visitNewArray(Quad q)
        {
            //val.killgen(Operator.NewArray.getDest(q).getRegister().toString(), q.getID());
        }
        
        @Override
        public void visitInvoke(Quad q)
        {
            RegisterOperand op = Operator.Invoke.getDest(q);
            if(op != null) {
                //val.killgen(op.getRegister().toString(), q.getID());
            }
        }
        
        @Override
        public void visitJsr(Quad q)
        {
            //val.killgen(Operator.Jsr.getDest(q).getRegister().toString(), q.getID());
        }
        
        @Override
        public void visitCheckCast(Quad q)
        {
            //val.killgen(Operator.CheckCast.getDest(q).getRegister().toString(), q.getID());
        }

        @Override
        public void visitNullCheck(Quad q)
        {
            //val.killgen("T-1", q.getID());

			//check! guessing it's the *source* that is the register being checked

            RegisterOperand op = (Operand.RegisterOperand) Operator.NullCheck.getSrc(q);
            if(op != null) {
						val.killgen(op.getRegister().toString(), q.getID());
            } else {
				System.out.println("Op was null!");
			}
        }
        
        @Override
        public void visitZeroCheck(Quad q)
        {
            //val.killgen("T-1", q.getID());
            /*Operand op = Operator.ZeroCheck.getDest(q);
            if(op != null) {
                //val.killgen(op.getRegister().toString(), q.getID());
            }*/
        }
        
    }
}
