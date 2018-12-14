import fs from 'fs';
import {parse, transform, traverse} from '@babel/core';

if (process.env.NODE_WATCH) {
  var contracts = require('../src').default;
}
else {
  var contracts = require('../lib').default;
}

describe('Typecheck', function () {
  failStatic('bad-precondition-always-false', 'foobar');
  ok('class', 'first', 'second');
  ok('old-value', 5, 5);
  failWith(`Function "add5" postcondition failed: input === old(input) + 5`, 'old-value', 5, 10);
  ok('old-value-object', {price: 5}, 5);
  failWith(`Function "add5" postcondition failed: input.price === old(input.price) + 5`, 'old-value-object', {price: 5}, 10);
  ok('old-value-old-in-scope', 5, 5);
  ok('assert', 'hello');
  failWith(`Function "demo" assertion failed: input.length > 0`, 'assert', '');
  ok('assert-block', 'hello');
  failWith(`Function "demo" assertion failed: input.length > 0`, 'assert-block', '');
  ok('assert-multiple', 'yo');
  failWith(`Function "demo" assertion failed: input.length > 0`, 'assert-multiple', '');
  failWith(`Function "demo" assertion failed: input.length < 5`, 'assert-multiple', 'hello');
  ok('assert-multiple-block', 'yo');
  failWith(`Function "demo" assertion failed: input.length > 0`, 'assert-multiple-block', '');
  failWith(`Function "demo" assertion failed: input.length < 5`, 'assert-multiple-block', 'hello');
  ok('example-1', 'hello');
  failWith(`Function "warn" precondition failed: typeof message === 'string'`, 'example-1', 123);
  ok('assert-with-message', 'hello');
  failWith(`input cannot be empty`, 'assert-with-message', '');
  ok('assert-no-function', 'hello');
  failWith(`Assertion failed: fail()`, 'bad-assert-no-function', 'hello');
  ok('example-2', 1, 2);
  ok('example-2', 1);
  ok('example-2', 0, 2);
  failWith(`Function "items" postcondition failed: retVal.length > 0`, 'example-2');
  ok('example-3', {balance: 100, overdraftLimit: 100}, 10);
  failWith(`Function "withdraw" precondition failed: fromAccount.balance - amount > -fromAccount.overdraftLimit`, 'example-3', {balance: 100, overdraftLimit: 100}, 1000);
  ok('example-4', {balance: 100, overdraftLimit: 100}, 10);
  failWith("Must not exceed overdraft limit", 'example-4', {balance: 100, overdraftLimit: 100}, 1000);

  ok('precondition', 'foo');
  failWith(`Function "demo" precondition failed: typeof input === 'string'`, 'precondition', false);
  ok('precondition-with-message', 'foo');
  failWith(`Input must be a string`, 'precondition-with-message', false);
  ok('precondition-multiple', 'abcd');
  failWith(`Function "demo" precondition failed: input.length > 3`, 'precondition-multiple', 'abc');
  failWith(`Function "demo" precondition failed: input.length < 6`, 'precondition-multiple', 'abcdefgh');
  failWith(`Function "demo" precondition failed: typeof input === 'string'`, 'precondition-multiple', false);
  failStatic('bad-precondition-with-let', ['foo', 'bar']);
  failStatic('bad-precondition-with-updateexpr', ['foo', 'bar']);
  failStatic('bad-precondition-with-assignment', ['foo', 'bar']);

  ok('precondition-no-block', 'foo');
  failWith(`Function "demo" precondition failed: typeof input === 'string'`, 'precondition-no-block', false);
  ok('precondition-no-block-with-message', 'foo');
  failWith(`Expected string`, 'precondition-no-block-with-message', false);

  ok('postcondition', 'foo');
  failWith(`Function "demo" postcondition failed: typeof retVal === 'string'`, 'postcondition', false);
  ok('postcondition-with-if', 'foo');
  failWith(`Function "demo" postcondition failed: typeof retVal === 'string'`, 'postcondition-with-if', false);
  ok('postcondition-with-if-inside', 'foo');
  failWith(`Function "demo" postcondition failed: retVal.length > 2`, 'postcondition-with-if-inside', 'no');
  ok('postcondition-no-return', 'foo');
  failWith(`Function "demo" postcondition failed: typeof input === 'string'`, 'postcondition-no-return', false);
  ok('postcondition-conditional', true);
  failWith(`Function "demo" postcondition failed: retVal === true`, 'postcondition-conditional', false);

  ok('postcondition-no-block', 'foo');
  failWith(`Function "demo" postcondition failed: typeof retVal === 'string'`, 'postcondition-no-block', false);

  ok('postcondition-no-block-with-message', 'foo');
  failWith(`Expected string`, 'postcondition-no-block-with-message', false);

  ok('precondition-and-postcondition', 'foo');
  failWith(`Function "demo" precondition failed: typeof input === 'string'`, 'precondition-and-postcondition', true);
  failWith(`Function "demo" postcondition failed: retVal > 2`, 'precondition-and-postcondition', 'no');

  ok('precondition-and-postcondition-no-block', 'foo');
  failWith(`Function "demo" precondition failed: typeof input === 'string'`, 'precondition-and-postcondition-no-block', true);
  failWith(`Function "demo" postcondition failed: retVal > 2`, 'precondition-and-postcondition-no-block', 'no');

  ok('invariant', 'hello world');
  ok('loop-invariant', 'hello world');

  it(`should load itself`, function () {
    this.timeout(10000);
    load('/../../src/index');
  });
});

describe('Env Strip', function () {
  function loadByEnv(env) {
    const filename = `${__dirname}/fixtures/env-strip.js`;
    const source = fs.readFileSync(filename, 'utf8');

    let oldEnv = process.env.NODE_ENV
    process.env.NODE_ENV = env;

    const transformed = transform(source, {
      filename: filename,
      presets: [
        ["@babel/preset-env", {                
          "useBuiltIns": "entry"
        }]
      ],
      plugins: [
        [contracts, {
          names: {
            return: 'retVal',
          },
          envStrip: true
        }],
        "@babel/plugin-transform-flow-strip-types"
      ]
    });

    //fs.writeFileSync(`${__dirname}/fixtures/env-strip-${env}.js.transformed`, transformed.code, 'utf8');

    process.env.NODE_ENV = oldEnv;

    const context = {
      exports: {}
    };
    
    const loaded = new Function('exports', transformed.code);
    loaded(context.exports);
    
    return context; 
  }

  it('should return development', function () {
    if (loadByEnv('development').exports.default() !== 'development') {
      throw new Error('failed');
    }
  });

  it('should return production', function () {
    if (loadByEnv('production').exports.default() !== 'production') {
      throw new Error('failed');
    }
  });
});

function load (basename) {
  return loadInternal(basename).exports.default;
}

function loadInternal (basename) {
  const filename = `${__dirname}/fixtures/${basename}.js`;
  const source = fs.readFileSync(filename, 'utf8');
  const transformed = transform(source, {
    filename: filename,
    presets: [
      ["@babel/preset-env", {                
        "useBuiltIns": "entry"
      }]
    ],
    plugins: [
      [contracts, {
        names: {
          return: 'retVal',
        }
      }],
      "@babel/plugin-transform-flow-strip-types"
    ]
  });
  const context = {
    exports: {}
  };
  if (process.env.CONTRACTS_SAVE_TRANSFORMED) {
    fs.writeFileSync(`${__dirname}/fixtures/${basename}.js.transformed`, transformed.code, 'utf8');
  }
  const loaded = new Function('module', 'exports', 'require', transformed.code);
  loaded(context, context.exports, (path) => {
    if (/^\.\//.test(path)) {
      const module = loadInternal(path.slice(2));
      return module.exports;
    }
    else {
      return require(path);
    }
  });
  return context;
}



function isThenable (thing: mixed): boolean {
  return thing && typeof thing.then === 'function';
}

function ok (basename, ...args) {
  it(`should load '${basename}'`, async function () {
    const result = load(basename)(...args);
    if (isThenable(result)) {
      await result;
    }
  });
}

function fail (basename, ...args) {
  it(`should not load '${basename}'`, async function () {
    let failed = false;
    try {
      const result = load(basename)(...args);
      if (isThenable(result)) {
        await result;
      }
    }
    catch (e) {
      failed = true;
    }
    if (!failed) {
      throw new Error(`Test '${basename}' should have failed but did not.`);
    }
  });
}

function failWith (errorMessage, basename, ...args) {
  it(`should not load '${basename}'`, async function () {
    let failed = false;
    let message;
    try {
      const result = load(basename)(...args);
      if (isThenable(result)) {
        await result;
      }
    }
    catch (e) {
      failed = true;
      message = e.message;
    }
    if (!failed) {
      throw new Error(`Test '${basename}' should have failed but did not.`);
    }
    // ignore differences in whitespace in comparison.
    if (message.replace(/\s+/g, ' ') !== errorMessage.replace(/\s+/g, ' ')) {
      throw new Error(`Test '${basename}' failed with ${message} instead of ${errorMessage}.`);
    }
  });
}


function failStatic (basename, ...args) {
  it(`should refuse to load '${basename}'`, function () {
    let failed = false;
    try {
      load(basename)(...args);
    }
    catch (e) {
      if (e instanceof SyntaxError) {
        failed = true;
        //console.log(e.toString());
      }
      else {
        throw e;
      }
    }
    if (!failed) {
      throw new Error(`Test '${basename}' should have failed static verification but did not.`);
    }
  });
}