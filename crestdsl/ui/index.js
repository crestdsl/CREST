element.append("<div id='graphContainer' style='position:relative;overflow:hidden;width:100%;height:25px;cursor:default;'>HAHAHA</div>");
var mxBasePath = './mxgraph/javascript/crestdsl'
$('head').append("<script type='text/javascript' src='./crestdsl/ui/mxgraphCustom.js'></script>");
$('head').append('<link rel="stylesheet" type="text/css" href="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/9.12.0/styles/vs.min.css">');




requirejs([
        "https://code.jquery.com/jquery-3.3.1.slim.min.js",
        "https://cdnjs.cloudflare.com/ajax/libs/highlight.js/9.12.0/highlight.min.js",
        "https://cdnjs.cloudflare.com/ajax/libs/highlight.js/9.12.0/languages/python.min.js",
        // "./mxgraph/javascript/src/js/mxClient.js",
        "https://cdn.jsdelivr.net/npm/elkjs@0.3.0/lib/elk.bundled.js",
        "./crestdsl/ui/mxgraphCustom.js"
    ], function(jquery, highlight, python, ELK, custom){
        $('head').append('<link rel="stylesheet" type="text/css" href="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/9.12.0/styles/vs.min.css">');

        // console.log('knownLayoutOptions', new ELK().knownLayoutOptions());
        // console.log('knownLayoutAlgorithms', new ELK().knownLayoutAlgorithms());
        // console.log('knownLayoutCategories', new ELK().knownLayoutCategories());
        // console.log("test");

        var elkgraph = ELKGRAPH;
        const elk = new ELK({
            defaultLayoutOptions: {
                'elk.algorithm': 'layered',
                'elk.direction': 'RIGHT',
                'elk.padding': '[top=50,left=50,bottom=50,right=50]',
                // 'elk.spacing.componentComponent': 25,
                'elk.layered.spacing.nodeNodeBetweenLayers': 50,
                // 'elk.edgeLabels.inline': true,
                'elk.edgeRouting': 'POLYLINE',
                'elk.layered.unnecessaryBendpoints': true
                }
            });

        // elkgraph = ELKGRAPH

        elk.layout(elkgraph)
            .then(function(g){
                console.log(g);
                plot(g);
            });
    }
   );
