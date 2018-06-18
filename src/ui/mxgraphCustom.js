console.log('knownLayoutOptions', new ELK().knownLayoutOptions());
console.log('knownLayoutAlgorithms', new ELK().knownLayoutAlgorithms());
console.log('knownLayoutCategories', new ELK().knownLayoutCategories());

function mxgraph_main(elkgraph){
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
/**
Define a new shape. Based on this:
https://github.com/jgraph/mxgraph-js/blob/master/javascript/examples/shape.html
*/
function OutputShape() {
mxCylinder.call(this);
};
mxUtils.extend(OutputShape, mxCylinder);
OutputShape.prototype.extrude = 10;
OutputShape.prototype.redrawPath = function(path, x, y, w, h, isForeground) {
var dy = this.extrude * this.scale;
var dx = this.extrude * this.scale;
if (isForeground) {
} else {
    path.moveTo(0, 0);
    path.lineTo(w, 0);
    path.lineTo(w+dx, h/2);
    path.lineTo(w, h);
    path.lineTo(0, h);
    path.lineTo(0, 0);
    path.close();
}
};
mxCellRenderer.registerShape('output', OutputShape);


function InputShape() {
mxCylinder.call(this);
};
mxUtils.extend(InputShape, mxCylinder);
InputShape.prototype.extrude = 10;
InputShape.prototype.redrawPath = function(path, x, y, w, h, isForeground) {
var dy = this.extrude * this.scale;
var dx = this.extrude * this.scale;
if (isForeground) {
} else {
    path.moveTo(0-dx, 0);
    path.lineTo(w, 0);
    path.lineTo(w, h);
    path.lineTo(0-dx, h);
    path.lineTo(0, h/2);
    path.lineTo(0-dx, 0);
    path.close();
}
};
mxCellRenderer.registerShape('input', InputShape);

// END INPUT DEFINITION

function addRec(graph, parent, elknode){
let root = addNode(graph, parent, elknode);

if(elknode.children){
    elknode.children.forEach(function(child){
        addRec(graph, root, child);
    });
}

if(elknode.ports){
    elknode.ports.forEach(function(port){
        addRec(graph, root, port);
    });
}

if(elknode.edges){
    elknode.edges.forEach(function(edge){
        addEdge(graph, root, edge);
    });
}
}

function addNode(graph, parent, elknode){
let style = elknode.cresttype;
if(elknode.cresttype == "midpoint"){
    return null;
}

if(elknode.cresttype == 'state' && elknode.currentstate){
    style = 'currentstate';
}
// TODO: we need to be aware that the height of an entity needs to be X pixels higher
// and that we also need to displace all x coordinates by that much
let vertex = graph.insertVertex(parent, elknode.id, elknode.label, elknode.x, elknode.y, elknode.width, elknode.height, style);
return vertex;
}

function addEdge(graph, parent, elknode){
let style = elknode.cresttype;
let source = graph.getModel().getCell(elknode.sources[0]);
let target = graph.getModel().getCell(elknode.targets[0]);
let edge = graph.insertEdge(parent, elknode.id, elknode.label, source, target, style);

// for transitions add action attachment point
if(style == "transition"){
    let mid = graph.insertVertex(edge, elknode.id+"_mid", "mid", 0, 0, 0, 0, 'strokeColor=green;rounded=1;', true);
}
var points = edge.geometry.points || []; // read original

// points.push(new mxPoint(step33.geometry.x + step33.geometry.width / 2 + 20,
// 						step11.geometry.y + step11.geometry.height * 4 / 5)];)
if(elknode.sections && elknode.sections.length > 0){
    section = elknode.sections[0];
    // points.push(new mxPoint(section.startPoint.x, section.startPoint.y));
    if(section.bendPoints){
        for(let i = 0; i < section.bendPoints.length; i++){
            points.push(new mxPoint(section.bendPoints[i].x, section.bendPoints[i].y));
        }
    }
    points.push(new mxPoint(section.endPoint.x, section.endPoint.y));
}

edge.geometry.points = points;  // write back
}

function showModalWindow(graph, evt, title, content, width, height) {
var background = document.createElement('div');
background.style.position = 'absolute';
background.style.left = '0px';
background.style.top = '0px';
background.style.right = '0px';
background.style.bottom = '0px';
background.style.background = 'black';
background.style.overflow = 'scroll';
// background.style.padding = '25px';
// background.style.height = '100%';

mxUtils.setOpacity(background, 50);
document.body.appendChild(background);

if (mxClient.IS_IE) {
    new mxDivResizer(background);
}

var x = Math.max(100, evt.offsetX-width/2); //document.body.scrollWidth/2-width/2);
var y = Math.max(10, evt.offsetY); //-height*2/3); //(document.body.scrollHeight ||
    //document.documentElement.scrollHeight)/2-height*2/3);
var wnd = new mxWindow(title, content, x, y, width, height, false, true);
wnd.setScrollable(true);
wnd.setClosable(true);

// Fades the background out after after the window has been closed
wnd.addListener(mxEvent.DESTROY, function(evt) {
    graph.setEnabled(true);
    mxEffects.fadeOut(background, 50, true, 10, 30, true);
});

graph.setEnabled(false);
graph.tooltipHandler.hide();
wnd.setVisible(true);

$('pre code').each(function(i, block) {
    hljs.highlightBlock(block);
  });
// hljs.highlightBlock(block);
};


function setStyles(graph){

// ROOT
style = graph.getStylesheet().getDefaultVertexStyle();
style = mxUtils.clone(style);
style[mxConstants.STYLE_SHAPE] = mxConstants.SHAPE_RECTANGLE;
style[mxConstants.STYLE_FILLCOLOR] = '#FFFFFF';
// style[mxConstants.DEFAULT_STARTSIZE] = 10;
// style[mxConstants.STYLE_LABEL_WIDTH] = 70;
graph.getStylesheet().putCellStyle('root', style);

// ENTITY
style = graph.getStylesheet().getDefaultVertexStyle();
style = mxUtils.clone(style);
style[mxConstants.STYLE_SHAPE] = mxConstants.SHAPE_SWIMLANE;
// style[mxConstants.DEFAULT_STARTSIZE] = 10;
// style[mxConstants.STYLE_LABEL_WIDTH] = 70;
graph.getStylesheet().putCellStyle('entity', style);

// port style
    // output
style = graph.getStylesheet().getDefaultVertexStyle();
style = mxUtils.clone(style);
style[mxConstants.STYLE_FILLCOLOR] = '#fcc5b3';
style[mxConstants.STYLE_SHAPE] = 'output';
style[mxConstants.STYLE_OVERFLOW] = 'width';
style[mxConstants.STYLE_SPACING_RIGHT] = OutputShape.prototype.extrude/2;
graph.getStylesheet().putCellStyle('output', style);

// Local
style = graph.getStylesheet().getDefaultVertexStyle();
style = mxUtils.clone(style);
style[mxConstants.STYLE_FILLCOLOR] = '#d2ceef';
style[mxConstants.STYLE_OVERFLOW] = 'width';
graph.getStylesheet().putCellStyle('local', style);

style = mxUtils.clone(style);
style[mxConstants.STYLE_RESIZABLE] = 0;
graph.getStylesheet().putCellStyle('midpoint', style);

// inputs
style = graph.getStylesheet().getDefaultVertexStyle();
style = mxUtils.clone(style);
style[mxConstants.STYLE_FILLCOLOR] = '#b5fed9';
style[mxConstants.STYLE_SHAPE] = 'input';
style[mxConstants.STYLE_OVERFLOW] = 'width';
style[mxConstants.STYLE_SPACING_LEFT] = InputShape.prototype.extrude/2;
graph.getStylesheet().putCellStyle('input', style);


// STATE
style = graph.getStylesheet().getDefaultVertexStyle();
style = mxUtils.clone(style);
style[mxConstants.STYLE_SHAPE] = mxConstants.SHAPE_ELLIPSE;
style[mxConstants.STYLE_FILLCOLOR] = '#e2cbc1';
graph.getStylesheet().putCellStyle('state', style);

    // currentstate
style = mxUtils.clone(style);
style[mxConstants.STYLE_SHAPE] = mxConstants.SHAPE_DOUBLE_ELLIPSE;
graph.getStylesheet().putCellStyle('currentstate', style);


// EDGES
style = graph.getStylesheet().getDefaultEdgeStyle();
style[mxConstants.STYLE_CURVED] = 1;
style[mxConstants.STYLE_FONTCOLOR] = 'black';
style[mxConstants.STYLE_STROKECOLOR] = 'black';
style[mxConstants.STYLE_STROKEWIDTH] = '1';

style = mxUtils.clone(style);
style[mxConstants.STYLE_DASHED] = true;
style[mxConstants.STYLE_DASH_PATTERN] = "7 3";
style[mxConstants.STYLE_FIX_DASH] = '1';

graph.getStylesheet().putCellStyle('update', style);

style = mxUtils.clone(style);
// style[mxConstants.STYLE_STROKECOLOR] = 'orange';
style[mxConstants.STYLE_DASH_PATTERN] = "2 2";
graph.getStylesheet().putCellStyle('action', style);

// style = mxUtils.clone(style);
// style[mxConstants.STYLE_DO] = true;


}

function plot(elkgraph){
container = document.getElementById('graphContainer');

// Checks if the browser is supported
if (!mxClient.isBrowserSupported())
{
    // Displays an error message if the browser is not supported.
    mxUtils.error('Browser is not supported!', 200, false);
}
else
{

    // Disables the built-in context menu
    mxEvent.disableContextMenu(container);

    // Creates the graph inside the given container
    var graph = new mxGraph(container);
    graph.setTooltips(true);
    graph.setConnectable(false);
    graph.setCellsDisconnectable(false);  // stop edges from disconnecting
    graph.setDisconnectOnMove(false)  // stop edges from disconnecting
    graph.setCellsEditable(false);
    graph.setResizeContainer(true);
    graph.setHtmlLabels(true);
    graph.isEdgeLabelsMovable(false);
    graph.setAllowDanglingEdges(false);
    graph.setCellsBendable(true);
    graph.graphHandler.setRemoveCellsFromParent(false);
    graph.gridSize = 25;

    setStyles(graph);

    graph.getTooltipForCell = function(cell) {
        if(cell.value.text){
            return cell.value.text;
        } else {
            return '<h3>'+cell.value.label+'</h3>';
        }
    }

    graph.getLabel = function(cell){
        if(cell.isEdge()){
            // let srcX = cell.source.geometry.x + cell.source.geometry.width/2;
            // let srcY = cell.source.geometry.y + cell.source.geometry.height/2;
            // let tgtX = cell.target.geometry.x + cell.target.geometry.width/2;
            // let tgtY = cell.target.geometry.y + cell.target.geometry.height/2;
            //
            // let distance = Math.sqrt( Math.abs(tgtX - srcX) ** 2 + Math.abs(tgtY - srcY) ** 2 );
            // if(distance > 3 * 5 * cell.value.label.length && distance >= 100){
            //     return cell.value.label;
            // } else {
            //     return '';
            // }
            return '';
        }

        return cell.value.label;
    }

    var highlightable = ["state", "currentstate", "transition", "local", "input", "output"];

    // highlight the outgoing and incoming edges on node selection
    graph.getSelectionModel().addListener(mxEvent.CHANGE, function(sender, evt){
        graph.getModel().beginUpdate();
        evt.consume();
        try {

            var remove = evt.properties.added;
            // console.log(changes);
            for (var i = 0; i < remove.length; i++) {
                var rem = remove[i];
                if(highlightable.indexOf(rem.getStyle()) < 0){ continue; }
                if(rem.edges){
                    rem.edges.forEach(function(edge){
                        graph.setCellStyles(mxConstants.STYLE_STROKECOLOR, 'black', [edge]);
                        graph.setCellStyles(mxConstants.STYLE_FONTCOLOR, 'black', [edge]);
                        graph.setCellStyles(mxConstants.STYLE_STROKEWIDTH, '1', [edge]);
                    });
                }
            }

            var added = evt.properties.removed;
            for (var i = 0; i < added.length; i++) {
                var add = added[i];
                if(highlightable.indexOf(add.getStyle()) < 0){ continue; }
                if(add.edges){
                    add.edges.forEach(function(edge){
                        if(edge.source.id == add.id){
                            graph.setCellStyles(mxConstants.STYLE_STROKECOLOR, 'blue', [edge]);
                            graph.setCellStyles(mxConstants.STYLE_FONTCOLOR, 'blue', [edge]);
                            graph.setCellStyles(mxConstants.STYLE_STROKEWIDTH, '2', [edge]);

                        } else if(edge.target.id == add.id){
                            graph.setCellStyles(mxConstants.STYLE_STROKECOLOR, 'red', [edge]);
                            graph.setCellStyles(mxConstants.STYLE_FONTCOLOR, 'red', [edge]);
                            graph.setCellStyles(mxConstants.STYLE_STROKEWIDTH, '2', [edge]);
                        }
                    });
                }
            }
        } finally {
            graph.getModel().endUpdate();
            graph.refresh();
        }
    });

    graph.dblClick = function(evt, cell) {
        // Do not fire a DOUBLE_CLICK event here as mxEditor will
        // consume the event and start the in-place editor.
        if (this.isEnabled() && !mxEvent.isConsumed(evt) && cell != null) {
            if(cell.isEdge()){
                var content = document.createElement('div');
                console.log(cell);
                if(cell.value.code){
                    content.innerHTML = cell.value.code;
                } else {
                    content.innerHTML = this.convertValueToString(cell);
                }
                showModalWindow(this, evt, 'SourceCode', content, 800, 300);
            }
        }

        // Disables any default behaviour for the double click
        mxEvent.consume(evt);
    };

    // graph.createHandler = function(state){
    //     var eh =  new mxEdgeHandler(state);
    //     console.log(state, eh);
    //     // eh.addEnabled = true;
    //     eh.cloneEnabled = false;
    //     // eh.removeEnabled = true;
    //     eh.dblClickRemoveEnabled = true;
    // }

    // function updateStyle(state, hover) {
    // 	if (hover) {
    // 		state.style[mxConstants.STYLE_FILLCOLOR] = '#ff0000';
    // 	}
    // };
    //
    // graph.addMouseListener( {
    // 	    currentState: null,
    // 	    previousStyle: null,
    // 	    mouseDown: function(sender, me) {
    // 	        // if (this.currentState != null) {
    // 	        // 	this.dragLeave(me.getEvent(), this.currentState);
    // 	        // 	this.currentState = null;
    // 	        // }
    // 	    },
    // 	    mouseMove: function(sender, me) {
    // 	        if (this.currentState != null && me.getState() == this.currentState) {
    // 	            return;
    // 	        }
    // 	        var tmp = graph.view.getState(me.getCell());
    // 	        // Ignores everything but vertices
    // 	        if (graph.isMouseDown || (tmp != null && highlightable.indexOf(tmp.cell.getStyle() >= 0))) {
    // 	        	tmp = null;
    // 	        }
    // 	        if (tmp != this.currentState) {
    // 	            if (this.currentState != null) {
    // 	                this.dragLeave(me.getEvent(), this.currentState);
    // 	            }
    // 	            this.currentState = tmp;
    // 	            if (this.currentState != null) {
    // 	                this.dragEnter(me.getEvent(), this.currentState);
    // 	            }
    // 	        }
    // 	    },
    // 	    mouseUp: function(sender, me) {},
    // 	    dragEnter: function(evt, state) {
    // 	        if (state != null) {
    // 	        	this.previousStyle = state.style;
    // 	        	state.style = mxUtils.clone(state.style);
    // 	        	updateStyle(state, true);
    // 	        	state.shape.apply(state);
    // 	        	state.shape.redraw();
    //
    // 	        	if (state.text != null) {
    // 	        		state.text.apply(state);
    // 	        		state.text.redraw();
    // 	        	}
    // 	        }
    // 	    },
    // 	    dragLeave: function(evt, state) {
    // 	        if (state != null) {
    // 	        	state.style = this.previousStyle;
    // 	        	updateStyle(state, false);
    // 	        	state.shape.apply(state);
    // 	        	state.shape.redraw();
    //
    // 	        	if (state.text != null) {
    // 	        		state.text.apply(state);
    // 	        		state.text.redraw();
    // 	        	}
    // 	        }
    // 	    }
    // 	});


    var parent = graph.getDefaultParent();

    // Adds cells to the model in a single step
    graph.getModel().beginUpdate();
    try
    {
        addRec(graph, parent, elkgraph);
        // layout.execute(parent);
    }
    finally
    {
        // Updates the display
        graph.getModel().endUpdate();

        // // hide loader
        // document.getElementById('loader').setAttribute('style', 'display:none;');
        // set iframe size
        iframe.setAttribute('style', 'height:'+ (elkgraph['height']+50) +'px');

    }

}
}
