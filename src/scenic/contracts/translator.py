import scenic.contracts.veneer
from scenic.syntax.compiler import compileScenicAST
from scenic.syntax.parser import parse_file

import time

preamble = """\
from scenic.syntax.veneer import *

import scenic.contracts.veneer
scenic.contracts.veneer._syntaxTrees = _syntaxTrees
from scenic.contracts.veneer import *
"""

def _generateBatchApprox(scenario, **kwargs):
    return scenario.generateBatch(**kwargs)[0]

def compileContractsFile(filename):
    # Execute contract code
    scenic_ast = parse_file(filename)

    python_ast, syntaxTrees = compileScenicAST(scenic_ast, filename=filename)

    ## DEBUG ##
    if False:
        import ast

        print(ast.unparse(python_ast))

    # Compile to Python code
    compiled_code = compile(python_ast, filename, "exec")

    # Execute Python code
    namespace = {"_syntaxTrees": syntaxTrees}

    # Execute preamble
    exec(compile(preamble, "<veneer>", "exec"), namespace)

    exec(compiled_code, namespace)

    for v_stmt in scenic.contracts.veneer._verifyStatements:
        start_time = time.time()
        result = v_stmt.verify(_generateBatchApprox)
        print(str(result))
        print("### RESULT SUMMARY ###")
        print(f"Total Time: {time.time()-start_time:.1f}s")
        print(f"Correctness {100*result.correctness:.2f}%")
        print("######################")
        print()
