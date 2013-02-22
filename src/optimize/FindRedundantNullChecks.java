package optimize;

import joeq.Main.Helper;
import joeq.Class.*;
import joeq.Compiler.Quad.*;
import flow.Flow;
import submit.MySolver;
import submit.RedundantNullChecks;

//import joeq.Compiler.Dataflow.Solver;


public class FindRedundantNullChecks {

    /*
     * args is an array of class names
     * method should print out a list of quad ids of redundant null checks
     * for each function as described on the course webpage
     */
    public static void main(String[] args) {

		if(args.length < 1){
			System.out.println("please input a class to check");
			return;
		}
	    
		/*
		Infrastructure wise, we have to go from class name to control flow graphs 
		ourselves this time. In Lab 1, this was handled for us. We can refer to the 
		main method in Flow.java for much of this.	
		*****/

		MySolver solver = new MySolver();
		RedundantNullChecks analysis = new RedundantNullChecks();

        // get the classes we will be visiting.
        jq_Class[] classes = new jq_Class[args.length]; 
        for (int i=0; i < classes.length; i++)
            classes[i] = (jq_Class)Helper.load(args[i]);

        // register the analysis with the solver.
        solver.registerAnalysis(analysis);

        // visit each of the specified classes with the solver.
        for (int i=0; i < classes.length; i++) {
            //System.out.println("Now analyzing " + classes[i].getName());
            Helper.runPass(classes[i], solver);
        }

		/*
		This is where things get trickier. I don't see a definition for runPass which
		matches this prototype (jq_Class, Solver). How do we extract the methods from
		within the classes? Then how do we transform these into control flow graphs?

		While I'm sure the last code paragraph would correctly apply our 
		RedundantNullCheck analysis on each method in each class, we will need to 
		access the interior cfgs in order to modify them in the next step.
	
		End result we need is analysis.getExit(), for each method/cfg analyzed. Then 
		we'll iterate over those cfgs and remove the indicated quads.

		cfg.getMethod().getName().toString() will get us the method name

		nullChecksSeen data structure added
		killgen/TF updated
		current: do meet for intersection
		then test 

		*****/

		}
}	

