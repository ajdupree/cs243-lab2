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
 
    ArrayList<Integer> redundantChecks;

    public ArrayList<Integer> getRedundantChecks()
    {
        return (ArrayList<Integer>) redundantChecks.clone();
    }

    public void suppressPrints() 
    {
        suppress = true;
    }

    private boolean suppress = false;

    /**
     * Class for the dataflow objects in the ReachingDefs analysis.
     * You are free to change this class or move it to another file.
     */
    public static class SafeSet implements Flow.DataflowObject {
		//null checks seen
		private Set<String> SafeVars = new TreeSet<String>();
        static private TreeSet<String> TopSet = new TreeSet<String>();

        public SafeSet() {
            
        }

        public boolean contains(String in) {
            return SafeVars.contains(in);
        }

        static public void register(String in)
        {
            TopSet.add(in);
        }

        /**
         * Methods from the Flow.DataflowObject interface.
         * See Flow.java for the meaning of these methods.
         * These need to be filled in.
         */
        public void setToTop() {
            SafeVars = (TreeSet<String>)TopSet.clone();
        }
        
        // do we need this?
        public void setToBottom() { System.out.println("Why did you call setToBottom()?");}

        /*The intersection. I suppose at this point we just need to intersect the list of 
		observed null checks*/
		public void meetWith (Flow.DataflowObject o) {
	        SafeSet rhs = (SafeSet) o;

			this.SafeVars.retainAll(rhs.SafeVars);
        }

        public void copy (Flow.DataflowObject o) {
	        SafeSet rhs = (SafeSet) o;
            SafeVars = (TreeSet<String>) ((TreeSet<String>)rhs.SafeVars).clone();
        }

        public void gen(String gened)
        {
            SafeVars.add(gened);
        }

        public void def(String defed)
        {
            SafeVars.remove(defed);
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

            for(String cur : SafeVars)
            {
                retval = retval + comma + cur;
                comma = ", ";
            }

            return retval + "]"; 
        }

        @Override
        public boolean equals(Object o) {
            if(o instanceof SafeSet) {
                return SafeVars.equals(((SafeSet)o).SafeVars);
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
    private SafeSet[] in, out;
    private SafeSet entry, exit;

    /**
     * This method initializes the datflow framework.
     *
     * @param cfg  The control flow graph we are going to process.
     */
    public void preprocess(ControlFlowGraph cfg) {
        // this line must come first.
        if(!suppress) System.out.print(cfg.getMethod().getName().toString());

        redundantChecks = new ArrayList<Integer>(); 

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
        in = new SafeSet[max];
        out = new SafeSet[max];
        qit = new QuadIterator(cfg);

        /************************************************
         * Your remaining initialization code goes here *
         ************************************************/

        int numargs = cfg.getMethod().getParamTypes().length;

        for(int i = 0; i < numargs; i++)
        {
            SafeSet.register("R" + i);
        }

        while(qit.hasNext()) {
            Quad q = qit.next();
            for(RegisterOperand def : q.getDefinedRegisters()) {
                SafeSet.register(def.getRegister().toString());
            }
            for(RegisterOperand use : q.getUsedRegisters()) {
                SafeSet.register(use.getRegister().toString());
            }
        }
        
        // initialize SafeSet in transfer function object
        transferFunction.val = new SafeSet();

        // initialize the entry and exit points.
        entry = new SafeSet();
        exit = new SafeSet();
        // initialize the contents of in and out.
        qit = new QuadIterator(cfg);
        while (qit.hasNext()) {
            int id = qit.next().getID();
            in[id] = new SafeSet();
            out[id] = new SafeSet();
        }

    }

    private String redundantChecksToString()
    {
        String retval = "";
        for(Integer cur : redundantChecks)
        {
            retval = retval + " " + cur.toString();
        }
        return retval;
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
        QuadIterator qit = new QuadIterator(cfg);

        while(qit.hasNext()) {
            Quad q = qit.next();
            if(q.getOperator() instanceof Operator.NullCheck)
            {
                if(in[q.getID()].contains(Operator.getReg2(q).toString().split(" ")[0].substring(1))) {
                    redundantChecks.add(q.getID());
                }
            }
        }
        
        Collections.sort(redundantChecks);

        if(!suppress) System.out.println(redundantChecksToString());

//      System.out.println("entry: " + entry.toString());
//      for (int i=0; i<in.length; i++) {
//          if (in[i] != null) {
//              System.out.println(i + " in:  " + in[i].toString());
//              System.out.println(i + " out: " + out[i].toString());
//          }
//      }
//      System.out.println("exit: " + exit.toString());
    }

    /**
     * Other methods from the Flow.Analysis interface.
     * See Flow.java for the meaning of these methods.
     * These need to be filled in.
     */
    public boolean isForward () { return true; }
    
    public Flow.DataflowObject getEntry() {
        SafeSet result = new SafeSet();
        result.copy(entry);
        return result; 
    }
    
    public Flow.DataflowObject getExit() {
        SafeSet result = new SafeSet();
        result.copy(exit);
        return result; 
    }

    public void setEntry(Flow.DataflowObject value) {
        entry = (SafeSet)value;
    }
    
    public void setExit(Flow.DataflowObject value) {
        exit = (SafeSet)value;
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
        return new SafeSet(); 
    }

    public void processQuad(Quad q) {
        transferFunction.val.copy(in[q.getID()]);
        Helper.runPass(q, transferFunction);
        out[q.getID()].copy(transferFunction.val);
    }
    
    private TransferFunction transferFunction = new TransferFunction();

    public static class TransferFunction extends QuadVisitor.EmptyVisitor
    {
        SafeSet val;

        @Override 
        public void visitMove(Quad q)
        {
            val.def(Operator.Move.getDest(q).getRegister().toString());
        }

        @Override
        public void visitBinary(Quad q)
        {
            val.def(Operator.Binary.getDest(q).getRegister().toString());
        }

        @Override
        public void visitUnary(Quad q)
        {
            val.def(Operator.Unary.getDest(q).getRegister().toString());
        }

        @Override
        public void visitALoad(Quad q)
        {
            val.def(Operator.ALoad.getDest(q).getRegister().toString());
        }
        
        @Override
        public void visitALength(Quad q)
        {
            val.def(Operator.ALength.getDest(q).getRegister().toString());
        }
        
        @Override
        public void visitGetstatic(Quad q)
        {
            val.def(Operator.Getstatic.getDest(q).getRegister().toString());
        }
        
        @Override
        public void visitGetfield(Quad q)
        {
            val.def(Operator.Getfield.getDest(q).getRegister().toString());
        }
        @Override
        public void visitInstanceOf(Quad q)
        {
            val.def(Operator.InstanceOf.getDest(q).getRegister().toString());
        }
        
        @Override
        public void visitNew(Quad q)
        {
            val.def(Operator.New.getDest(q).getRegister().toString());
        }
        
        @Override
        public void visitNewArray(Quad q)
        {
            val.def(Operator.NewArray.getDest(q).getRegister().toString());
        }
        
        @Override
        public void visitInvoke(Quad q)
        {
            RegisterOperand op = Operator.Invoke.getDest(q);
            if(op != null) {
                val.def(op.getRegister().toString());
            }
        }
        
        @Override
        public void visitJsr(Quad q)
        {
            val.def(Operator.Jsr.getDest(q).getRegister().toString());
        }
        
        @Override
        public void visitCheckCast(Quad q)
        {
            val.def(Operator.CheckCast.getDest(q).getRegister().toString());
        }

        @Override
        public void visitNullCheck(Quad q)
        {
            val.def("T-1");

			//check! guessing it's the *source* that is the register being checked

            Operand op = (Operand.RegisterOperand) Operator.NullCheck.getSrc(q);
            if(op != null) {
				val.gen(Operator.getReg2(q).toString().split(" ")[0].substring(1));
            } else {
				System.out.println("Op was null!");
			}
        }
        
        @Override
        public void visitZeroCheck(Quad q)
        {
            val.def("T-1");
            /*Operand op = Operator.ZeroCheck.getDest(q);
            if(op != null) {
                val.def(op.getRegister().toString());
            }*/
        }
        
    }
}

