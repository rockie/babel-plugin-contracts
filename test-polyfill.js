require("@babel/register")({
  "parserOpts": {
    "plugins": ["flow"]
  },
  "presets": [
    ["@babel/preset-env", {                
      "useBuiltIns": "entry"
    }]
  ],
  "plugins": [    
    "@babel/plugin-transform-flow-strip-types"
  ]
});
