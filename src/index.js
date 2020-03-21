import generate from '@babel/generator';

type Node = {
  type: string;
  node?: void;
};

type Identifier = {
  type: string;
  name: string;
};

type Scope = {};

type NodePath = {
  type: string;
  node: Node;
  scope: Scope;
};


/**
 * # Design By Contract Transformer
 */
export default function ({types: t, template}) {

  const defaultNames = {
    assert: 'assert',
    precondition: 'pre',
    postcondition: 'post',
    invariant: 'invariant',
    return: 'it',
    old: 'old'
  };

  const defaultEnvNames = { 
    development: "dev", 
    test: "test",
    production: "prod" 
  };

  let NAMES = Object.assign({}, defaultNames);
  let ENV_NAMES = Object.assign({}, defaultEnvNames);
  let ENV_LABEL_SET;

  let THE_ONLY_LABEL_TO_KEEP;

  const guard = template(`
    if (!CONDITION) {
      throw new Error(MESSAGE);
    }
  `);

  const guardFn = template(`
    const ID = (IT) => {
      CONDITIONS;
      return IT;
    }
  `);

  const NODE_ENV = process.env.NODE_ENV || 'development';

  function assemblePrecondition (path: NodePath): void {
    const body: NodePath = path.get('body');
    const fn: NodePath = path.getFunctionParent();
    const name: string = fn.node.id ? `"${fn.node.id.name}" `: ' ';
    if (body.isExpressionStatement()) {
      let condition: NodePath = body.get('expression');
      let message: ?Node;
      if (condition.isSequenceExpression()) {
        const expressions = condition.get('expressions');
        condition = expressions[0];
        message = expressions[1].node;
      }
      else {
        message = t.stringLiteral(`Function ${name}precondition failed: ${generate(condition.node).code}`);
      }
      path.replaceWith(guard({
        CONDITION: staticCheck(condition),
        MESSAGE: message
      }));
      return;
    }

    body.traverse({
      "VariableDeclaration|Function|AssignmentExpression|UpdateExpression|YieldExpression|ReturnStatement|AwaitExpression" (item: NodePath): void {
        throw path.buildCodeFrameError(`Preconditions cannot have side effects.`);
      },
      ExpressionStatement (statement: NodePath): void {
        let condition: NodePath = statement.get('expression');
        let message: ?Node;
        if (condition.isSequenceExpression()) {
          const expressions = condition.get('expressions');
          condition = expressions[0];
          message = expressions[1].node;
        }
        else {
          message = t.stringLiteral(`Function ${name}precondition failed: ${generate(condition.node).code}`);
        }
        statement.replaceWith(guard({
          CONDITION: staticCheck(condition),
          MESSAGE: message
        }));
      }
    });

    if (body.isBlockStatement()) {
      path.replaceWithMultiple(path.get('body').node.body);
    }
    else {
      path.replaceWith(path.get('body'));
    }
  }

  function assemblePostcondition (path: NodePath): Identifier {
    const body: NodePath = path.get('body');
    const fn: NodePath = path.getFunctionParent();
    const name: string = fn.node.id ? `"${fn.node.id.name}" `: ' ';
    const conditions: Node[] = [];    

    if (body.isExpressionStatement()) {
      let condition: NodePath = body.get('expression');
      let message: ?Node;
      if (condition.isSequenceExpression()) {
        const expressions = condition.get('expressions');
        condition = expressions[0];
        message = expressions[1].node;
      }
      else {
        message = t.stringLiteral(`Function ${name}postcondition failed: ${generate(condition.node).code}`);
      }
      conditions.push(guard({
        CONDITION: staticCheck(condition),
        MESSAGE: message
      }));
    }
    else {
      body.traverse({
        "VariableDeclaration|Function|AssignmentExpression|UpdateExpression|YieldExpression|ReturnStatement|AwaitExpression" (item: NodePath): void {
          throw path.buildCodeFrameError(`Postconditions cannot have side effects.`);
        },
        CallExpression (call: NodePath): void {
          const callee: NodePath = call.get('callee');
          const args: NodePath[] = call.get('arguments');
          if (!callee.isIdentifier() || callee.node.name !== NAMES.old || call.scope.hasBinding(NAMES.old) || args.length === 0) {
            return;
          }

          const argument: NodePath = args[0];
          const id = call.scope.generateUidIdentifierBasedOnNode(argument.node);
          fn.scope.push({id, init: argument.node, kind: 'const'});
          call.replaceWith(id);
        },
        ExpressionStatement (statement: NodePath): void {
          let condition: NodePath = statement.get('expression');
          let message: ?Node;
          if (condition.isSequenceExpression()) {
            const expressions = condition.get('expressions');
            condition = expressions[0];
            message = expressions[1].node;
          }
          else {
            message = t.stringLiteral(`Function ${name}postcondition failed: ${generate(condition.node).code}`);
          }
          statement.replaceWith(guard({
            CONDITION: staticCheck(condition),
            MESSAGE: message
          }));
        }
      });
      conditions.push(...body.node.body);
    }

    const id = path.scope.generateUidIdentifier(`${fn.node.id ? fn.node.id.name : 'check'}Postcondition`);    

    fn.get('body').get('body')[0].insertBefore(guardFn({
      ID: id,
      CONDITIONS: conditions,
      IT: t.identifier(NAMES.return)
    }));        

    path.remove();

    return id;
  }

  function assembleAssertion (path: NodePath): void {
    const body: NodePath = path.get('body');
    const fn: ?NodePath = path.getFunctionParent();
    const name: string = fn && fn.node && fn.node.id ? `"${fn.node.id.name}"` : '';
    if (body.isExpressionStatement()) {
      let condition: NodePath = body.get('expression');
      let message: ?Node;
      if (condition.isSequenceExpression()) {
        const expressions = condition.get('expressions');
        condition = expressions[0];
        message = expressions[1].node;
      }
      else if (name) {
        message = t.stringLiteral(`Function ${name} assertion failed: ${generate(condition.node).code}`);
      }
      else {
        message = t.stringLiteral(`Assertion failed: ${generate(condition.node).code}`);
      }      
      
      path.replaceWith(guard({
        CONDITION: staticCheck(condition),
        MESSAGE: message
      }));

      return;
    }

    body.traverse({
      "VariableDeclaration|Function|AssignmentExpression|UpdateExpression|YieldExpression|ReturnStatement|AwaitExpression" (item: NodePath): void {
        throw path.buildCodeFrameError(`Assertions cannot have side effects.`);
      },
      ExpressionStatement (statement: NodePath): void {
        let condition: NodePath = statement.get('expression');
        let message: ?Node;
        if (condition.isSequenceExpression()) {
          const expressions = condition.get('expressions');
          condition = expressions[0];
          message = expressions[1].node;
        }
        else if (name) {
          message = t.stringLiteral(`Function ${name} assertion failed: ${generate(condition.node).code}`);
        }
        else {
          message = t.stringLiteral(`Assertion failed: ${generate(condition.node).code}`);
        }

        statement.replaceWith(guard({
          CONDITION: staticCheck(condition),
          MESSAGE: message
        }));
      }
    });

    if (body.isBlockStatement()) {
      path.replaceWithMultiple(path.get('body').node.body);
    }
    else {
      path.replaceWith(path.get('body'));
    }
  }

  function assembleInvariant (path: NodePath): Identifier {
    const body: NodePath = path.get('body');
    const fn: NodePath = path.getFunctionParent();
    const name: string = fn.node.id ? `"${fn.node.id.name}" `: ' ';
    const conditions: Node[] = [];

    if (body.isExpressionStatement()) {
      let condition: NodePath = body.get('expression');
      let message: ?Node;
      if (condition.isSequenceExpression()) {
        const expressions = condition.get('expressions');
        condition = expressions[0];
        message = expressions[1].node;
      }
      else {
        message = t.stringLiteral(`Function ${name}invariant failed: ${generate(condition.node).code}`);
      }
      conditions.push(guard({
        CONDITION: staticCheck(condition),
        MESSAGE: message
      }));
    }
    else {
      body.traverse({
        "VariableDeclaration|Function|AssignmentExpression|UpdateExpression|YieldExpression|ReturnStatement|AwaitExpression" (item: NodePath): void {
          throw path.buildCodeFrameError(`Invariants cannot have side effects.`);
        },
        ExpressionStatement (statement: NodePath): void {
          let condition: NodePath = statement.get('expression');
          let message: ?Node;
          if (condition.isSequenceExpression()) {
            const expressions = condition.get('expressions');
            condition = expressions[0];
            message = expressions[1].node;
          }
          else {
            message = t.stringLiteral(`Function ${name}invariant failed: ${generate(condition.node).code}`);
          }
          statement.replaceWith(guard({
            CONDITION: staticCheck(condition),
            MESSAGE: message
          }));
        }
      });
      conditions.push(...body.node.body);
    }

    const id = path.scope.generateUidIdentifier(`${fn.node.id ? fn.node.id.name : 'check'}Invariant`);
    path.parentPath.get('body')[0].insertBefore(guardFn({
      ID: id,
      CONDITIONS: conditions,
      IT: t.identifier(NAMES.return)
    }));
    path.remove();
    return id;
  }

  function extractEnvironmentCode (path: NodePath): void {
    const body: NodePath = path.get('body');

    if (body.isBlockStatement()) {
      path.replaceWithMultiple(path.get('body').node.body);
    }
    else {
      path.replaceWith(path.get('body'));
    }
  }

  function expression (input: string): Function {
    const fn: Function = template(input);
    return function (...args) {
      const node: Node = fn(...args);
      return getExpression(node);
    };
  }

  function staticCheck (expression: NodePath): NodePath {
    const {confident, value} = expression.evaluate();
    if (confident && !value) {
      throw expression.buildCodeFrameError(`Contract always fails.`);
    }

    return expression.node;
  }

  return {
    visitor: {
      Program (path: NodePath, {opts}: any) {
        if (opts != null && opts.names !== undefined) {
          NAMES = Object.assign({}, NAMES, opts.names);
          ENV_NAMES = Object.assign({}, ENV_NAMES, opts.envNames);
          ENV_LABEL_SET = new Set(Object.values(ENV_NAMES));
        } else {
          ENV_LABEL_SET = new Set();
        }

        const IN_FUNC_TO_STRIP = new Set([NAMES.precondition, NAMES.postcondition, NAMES.invariant, NAMES.assert]);

        if (opts != null && opts.stripUnless !== undefined) {
          THE_ONLY_LABEL_TO_KEEP = opts.stripUnless;
        } else {
          THE_ONLY_LABEL_TO_KEEP = ENV_NAMES[NODE_ENV];
        }

        return path.traverse({
          Function (fn: NodePath): void {
            if (fn.isArrowFunctionExpression() && !fn.get('body').isBlockStatement()) {
              // Naked arrow functions cannot contain contracts.
              return;
            }
            fn.traverse({
              Function (path: NodePath): void {
                // This will be handled by the outer visitor, so skip it.
                path.skip();
              },

              LabeledStatement (path: NodePath): void {
                const label: NodePath = path.get('label');
                if ((opts.strip || (opts.env && opts.env[NODE_ENV] && opts.env[NODE_ENV].strip)) && IN_FUNC_TO_STRIP.has(label.node.name)) {                  
                    path.remove();
                    return;
                }

                if (opts.envStrip && THE_ONLY_LABEL_TO_KEEP !== label.node.name) {
                  path.remove();
                  return;
                }

                let id: ?Identifier;
                let children: ?NodePath[];
                let parent: NodePath = fn;
                if (label.node.name === NAMES.precondition) {
                  assemblePrecondition(path);
                  return;
                }
                else if (label.node.name === NAMES.postcondition) {
                  id = assemblePostcondition(path);
                  children = fn.get('body').get('body');
                }
                else if (label.node.name === NAMES.assert) {
                  assembleAssertion(path);
                  return;
                }
                else if (label.node.name === NAMES.invariant) {
                  id = assembleInvariant(path);
                  parent = path.findParent(t.isBlockStatement);
                  children = parent.get('body');
                  const first: NodePath = children[0];
                  first.insertAfter(t.expressionStatement(t.callExpression(id, [])))
                } else if (ENV_LABEL_SET.has(label.node.name)) {
                  extractEnvironmentCode(path);
                  return;
                } else {
                  return;
                }

                parent.traverse({
                  Function (path: NodePath): void {
                    // This will be handled by the outer visitor, so skip it.
                    path.skip();
                  },
                  ReturnStatement (statement: NodePath): void {
                    statement.get('argument').replaceWith(t.callExpression(id, [statement.node.argument]));
                  }
                });
                const last: NodePath = children[children.length - 1];
                if (!last.isReturnStatement()) {
                  last.insertAfter(t.expressionStatement(t.callExpression(id, [])));
                }
              }
            });
          },

          LabeledStatement (path: NodePath): void {
            const label: NodePath = path.get('label');

            if (label.node.name === NAMES.assert) {
              if (opts.strip || (opts.env && opts.env[NODE_ENV] && opts.env[NODE_ENV].strip)) {
                path.remove();
              } 
              else {
                assembleAssertion(path);
              }
              return;
            } else if (opts.envStrip) {

              if (THE_ONLY_LABEL_TO_KEEP !== label.node.name) {
                extractEnvironmentCode(path);
              } else {
                path.remove();
              }
              
              return;
            } 
          }
        });
      }
    }
  }
}
