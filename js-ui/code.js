fetch('data2.json', {mode: 'no-cors'})
  .then(function(res) {
    return res.json()
  })
  .then(function(data) {
    var cy = window.cy = cytoscape({
      container: document.getElementById('cy'),

      layout: {
        name: 'cose-bilkent',
        animate: false,

        // name: 'cola',
        // flow: { axis: 'y', minSeparation: 40 },
        // // animate: true,
        // avoidOverlap: true,

        // alignment: function(d){
        //   if(d.hasClass("input")){
        //     return {'x': 0};
        //   }
        //   if(d.hasClass("output")){
        //     return {'x': 200};
        //   } else {
        //     console.log("not input");
        //   }
        //
        // }

        // name: 'dagre',
        // rankdir: 'LR',

        // name: 'breadthfirst'
      },
      style: [
        {
          selector: 'node',
          style: {
            'background-color': 'blue',
            'label': 'data(label)',
            'text-halign': 'center',
            'text-valign': 'center',
            'width': 'label',
            'height': 'label',
            'padding': '15px',
            'background-blacken': '-0.25',
            'border-style': 'solid',
            'border-width': '1',
            'border-color': 'black'
          }
        },
        {
          selector: "node.cy-expand-collapse-collapsed-node",
          style: {
            'background-color': 'blue',
            'background-opacity': 0.075,
            "shape": "rectangle",
            'background-blacken': '-0.25',
          }
        },
        {
          selector: ':parent',
          style: {
            // 'color': 'black',
            'font-weight': 'bold',
            'background-opacity': 0.075,
            'content': 'data(label)',
            'text-valign': 'top',
            'padding': 10
          }
        },

        {
          selector: 'edge',
          style: {
            'width': 3,
            'line-color': 'black',
            'target-arrow-shape': 'triangle',
            'target-arrow-color': 'black',
            'curve-style': 'bezier',
            // 'control-point-step-size': 40,
            'arrow-scale': 2
          }
        },
        {
          selector: '.input',
          style:{
            'background-color': 'green', //'#b5fed9',
            'background-opacity': '0.3',
            'shape': 'polygon',
            'shape-polygon-points': '-1 1 -0.65 0 -1 -1 1 -1 1 1'
          }
        },
        {
          selector: '.output',
          style:{
            'background-color': 'red', //'#fcc5b3',
            'background-opacity': '0.3',
            'shape': 'polygon',
            'shape-polygon-points': '-1 1 -1 -1 0.5 -1 1 0 0.5 1'
          }
        },
        {
          selector: '.local',
          style:{
            'background-color': 'blue', //''#d2ceef',
            'background-opacity': '0.3',
            'shape': 'rectangle'
          }
        },
        {
          selector: '.state',
          style:{
            'background-color': 'brown', //'#e2cbc1',
            'background-opacity': '0.7',
            'shape': 'ellipse',
            'width': '50px',
            'height': '50px'
          }
        },
        {
          selector: '.transition',
          style:{
          }
        },
        {
          selector: '.update',
          style:{
            'line-style': 'dashed'
          }
        },
        {
          selector: '.influence',
          style:{
          }
        }
      ],

      elements: data
    });

    var api = cy.expandCollapse({
        layoutBy: {
          name: "cose-bilkent",
          animate: false,
          randomize: false,
          fit: true
          // flow: { axis: 'x', minSeparation: 40 },
          // avoidOverlap: true,

        },
        fisheye: true,
        animate: false,
        expandCollapseCueSize: 8,
        expandCollapseCueLineSize: 6,
        undoable: true
      });

      cy.nodes().on("tap", function(event) {
        // console.log(this.data("label"));
        if(event.target === this){
          if(api.isCollapsible(this)){
            api.collapseRecursively(this);
          } else if(api.isExpandable(this)){
            api.expand(this);
          }
        }

        // var node = this;
        // console.log(event.cyTarget === this);
        // console.log(node.data("label"));
        // console.log(this);
        // console.log(event);
        // api.collapseRecursively(node);
        // console.log(node.descendants());
          // console.log(cy.$(node))
      });
});
