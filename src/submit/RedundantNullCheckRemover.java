package submit;

// some useful things to import. add any additional imports you need.
import java.util.*;
import joeq.Compiler.Quad.*;
import joeq.Compiler.Quad.Operand.*;
import joeq.Main.Helper;
import flow.Flow;

public class RedundantNullCheckRemover implements Flow.Optimization{
    @Override
    public void optimize(ControlFlowGraph cfg)
    {
        ArrayList<Integer> redundantList = nullChecker.getRedundantChecks();
        QuadIterator qit = new QuadIterator(cfg);
        while (qit.hasNext()) {
            Quad q = qit.next();
            if(redundantList.contains(q.getID()))
            {
                qit.remove();
            }
        }
        
    }

    RedundantNullChecks nullChecker;
    public void registerRedundantNullChecks(RedundantNullChecks in)
    {
        nullChecker = in;
    }
}
