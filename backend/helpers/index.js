const fs = require('fs');
const { spawn } = require('child_process');

const initFile = (fileName) => {
    const content = ";; activate model generation\n(set-option :produce-models true)\n(set-option :opt.priority lex)\n\n";
    fs.writeFileSync(fileName, content);
};

const declareGoalsAndRefinements = (fileName, model) => {
    let content = ";;%%%%\n;Declaration of Goal, Assumption and Refinement Propostions\n;%%%%\n";

    let goalNodes = [];
    let refinementLinks = [];
    let junctionNodes = [];
    let signleAndRefinementLinks = [];

    // get "or refinement" and single "and refinement" links
    model.linkDataArray = model?.linkDataArray?.map((link) => {
        if(link?.type === "Refinement") {
            const updatedLink = { ...link, label: `R${refinementLinks?.length + signleAndRefinementLinks?.length + 1}` };
            refinementLinks.push(updatedLink);
            return updatedLink;
        }

        if(link?.category === "ANDRefinement" && link?.fromArrow === "Backward") {
            const toNode = model?.nodeDataArray?.find(n => n?.key === link?.to);
            if(toNode?.category !== "Junction") {
                const updatedLink = { ...link, label: `R${refinementLinks?.length + signleAndRefinementLinks?.length + 1}` };
                signleAndRefinementLinks.push(updatedLink);
                return updatedLink;
            }
        }

        return link;
    })
    
    // get goal nodes and "and refinement" junctions
    model.nodeDataArray = model?.nodeDataArray?.map((node, index) => {
        if(node?.category === "Junction") {
            const updatedNode = { 
                ...node, 
                label: `R${refinementLinks?.length + signleAndRefinementLinks?.length + junctionNodes?.length + 1}`
            };
            junctionNodes.push(updatedNode);
            return updatedNode;
        } else {
            const goalKey = Math.abs(node?.key)?.toFixed(0);
            const goalLabel = `G${goalKey}`;
            const updatedNode = { ...node, label: goalLabel };
            goalNodes.push(updatedNode)
            return updatedNode;
        }
    });

    const combined = [...goalNodes, ...refinementLinks, ...junctionNodes, ...signleAndRefinementLinks];

    combined?.forEach(item => {
        const line = `(declare-fun ${item?.label} () Bool)\n`;
        content = content + line;
    });
    content = content + "\n";

    fs.writeFileSync(fileName, content, { flag: 'a+' });
};

const closeWorld = (fileName, model) => {
    let content = ";;%%%%\n;Close-world\n;%%%%\n";

    const goalNodes = model?.nodeDataArray?.filter(node => node?.category !== "Junction");

    goalNodes?.forEach(node => {
        const orRefinements = model?.linkDataArray?.filter(link => {
            return link?.type === "Refinement" && link?.from === node?.key;
        });

        let andRefinements = []

        model?.linkDataArray?.forEach(link => {
            if(link?.category === "ANDRefinement" && link?.fromArrow === "Backward" && link?.from === node?.key) {
                const toNode = model?.nodeDataArray?.find(node => node?.key === link?.to);

                if(toNode?.category === "Junction") {
                    andRefinements.push(toNode);
                }

                andRefinements.push(link);
            }
        });

        const combined = [...orRefinements, ...andRefinements];

        if(combined?.length > 0) {
            const refinementLabels = combined?.map(l => l?.label)?.join(" ");
            content = content + `(assert (=> ${node?.label} (or ${refinementLabels} )))\n`;
        }
    });
    content = content + "\n";

    fs.writeFileSync(fileName, content, { flag: 'a+' });
};

const refinementGoalRelationships = (fileName, model) => {
    let content = ";;%%%%\n;Refinement-Goal relationships\n;%%%%\n";

    model?.linkDataArray?.forEach(link => {
        if(link?.label && link?.label?.slice(0, 1) === "R") {
            const toNode = model?.nodeDataArray?.find(n => n?.key === link?.to);
            const fromNode = model?.nodeDataArray?.find(n => n?.key === link?.from);
            
            content = content + `(assert (and (= ${link?.label} (and ${toNode?.label} )) (=> ${link?.label} ${fromNode?.label} )))\n`;
        }
    });

    model?.nodeDataArray?.forEach(node => {
        if(node?.category === "Junction") {
            const parentLink = model?.linkDataArray?.find(l => {
                return l?.category === "ANDRefinement" && l?.fromArrow === "Backward" && l?.to === node?.key;
            });
            const parentNode = model?.nodeDataArray?.find(n => n?.key === parentLink?.from);

            const childrenLinks = model?.linkDataArray?.filter(l => {
                return l?.category === "ANDRefinement" && l?.fromArrow !== "Backward" && l?.to === node?.key;
            });
            const childrenNodes = model?.nodeDataArray?.filter(n => childrenLinks?.map(l => l?.from)?.includes(n?.key));
            const childrenLabels = childrenNodes?.map(n => n?.label)?.join(" ");

            content = content + `(assert (and (= ${node?.label} (and ${childrenLabels} )) (=> ${node?.label} ${parentNode?.label} )))\n`;
        }
    })

    content = content + "\n";

    fs.writeFileSync(fileName, content, { flag: 'a+' });
};

const mandatoryNodes = (fileName, model) => {
    let content = ";;%%%%\n;Mandatory goals\n;%%%%\n";

    model?.nodeDataArray?.forEach(node => {
        if(node?.is_mandatory) {
            content = content + `(assert ${node?.label})\n`;
        }
    });

    content = content + "\n";

    fs.writeFileSync(fileName, content, { flag: 'a+' });
};

const precedenceRelationships = (fileName, model) => {
    let content = ";;%%%%\n;Precedence relationships\n;%%%%\n";

    model?.linkDataArray?.forEach(link => {
        if(link?.type === "Precedence") {
            const toNode = model?.nodeDataArray?.find(n => n?.key === link?.to);
            const fromNode = model?.nodeDataArray?.find(n => n?.key === link?.from);

            content = content + `(assert (=> ${fromNode?.label} ${toNode?.label}))\n`;
        }
    });

    content = content + "\n";

    fs.writeFileSync(fileName, content, { flag: 'a+' });
};

const optimizeCriteria = (fileName) => {
    let content = ";;%%\n;;Optimization:\n;;%%\n";

    // do optimization criteria

    content = content + "(check-sat)\n(get-objectives)\n(load-objective-model 1)\n(get-model)\n(exit)\n";

    fs.writeFileSync(fileName, content, { flag: 'a+' });
}

const runOptiMathSat = (inputFile, outputFile) => {
    // program outputs
    let content = "";

    // define the command to run OptiMathSat
    const command = 'optimathsat/bin/optimathsat';

    // define the arguments to pass to OptiMathSat
    const args = [inputFile];

    // spawn the OptiMathSat process with the input and output files as arguments
    const optiMathSat = spawn(command, args);

    // handle stdout and stderr output from OptiMathSat
    optiMathSat.stdout.on('data', (data) => {
        console.log(`stdout: ${data}`);
        content = content + data;
    });

    optiMathSat.stderr.on('data', (data) => {
        console.error(`stderr: ${data}`);
    });

    // // handle OptiMathSat exit code
    optiMathSat.on('close', (code) => {
        console.log(`OptiMathSat exited with code ${code}`);
        fs.writeFileSync(outputFile, content);
    });
}

module.exports = {
    initFile,
    declareGoalsAndRefinements,
    closeWorld,
    refinementGoalRelationships,
    mandatoryNodes,
    precedenceRelationships,
    optimizeCriteria,
    runOptiMathSat
}