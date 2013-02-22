package optimize;

import java.util.List;
import joeq.Class.jq_Class;
import joeq.Main.Helper;
import flow.Flow;
import submit.MySolver;
import submit.RedundantNullChecks;

public class Optimize {
    /*
     * optimizeFiles is a list of names of class that should be optimized
     * if nullCheckOnly is true, disable all optimizations except "remove redundant NULL_CHECKs."
     */
    public static void optimize(List<String> optimizeFiles, boolean nullCheckOnly) {
        for (int i = 0; i < optimizeFiles.size(); i++) {
            jq_Class classes = (jq_Class)Helper.load(optimizeFiles.get(i));
            // Run your optimization on each classes.
            MySolver solver = new MySolver();
            RedundantNullChecks analysis = new RedundantNullChecks();
            RedundantNUllCheckRemover optimizer = new RedundantNullCheckRemover();
            optimizer.registerRedundantNullChecks(analysis);
            analysis.suppressPrints();
            solver.registerAnalysis(analysis);
            Helper.runPass(classes, solver);
        }
    }
}
