/*
 *
 *  *  Copyright 2014 Orient Technologies LTD (info(at)orientechnologies.com)
 *  *
 *  *  Licensed under the Apache License, Version 2.0 (the "License");
 *  *  you may not use this file except in compliance with the License.
 *  *  You may obtain a copy of the License at
 *  *
 *  *       http://www.apache.org/licenses/LICENSE-2.0
 *  *
 *  *  Unless required by applicable law or agreed to in writing, software
 *  *  distributed under the License is distributed on an "AS IS" BASIS,
 *  *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  *  See the License for the specific language governing permissions and
 *  *  limitations under the License.
 *  *
 *  * For more information: http://www.orientechnologies.com
 *
 */
package com.orientechnologies.orient.graph.sql.functions;

import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;

import com.orientechnologies.common.collection.OMultiValue;
import com.orientechnologies.common.types.OModifiableBoolean;
import com.orientechnologies.orient.core.command.OCommandContext;
import com.orientechnologies.orient.core.db.ODatabaseDocumentInternal;
import com.orientechnologies.orient.core.db.ODatabaseRecordThreadLocal;
import com.orientechnologies.orient.core.db.record.OIdentifiable;
import com.orientechnologies.orient.core.record.ORecord;
import com.orientechnologies.orient.core.serialization.serializer.OStringSerializerHelper;
import com.orientechnologies.orient.core.sql.OSQLHelper;
import com.orientechnologies.orient.graph.sql.OGraphCommandExecutorSQLFactory;
import com.tinkerpop.blueprints.Direction;
import com.tinkerpop.blueprints.Edge;
import com.tinkerpop.blueprints.Vertex;
import com.tinkerpop.blueprints.impls.orient.OrientBaseGraph;
import com.tinkerpop.blueprints.impls.orient.OrientVertex;
import es.usc.citius.hipster.algorithm.AStar;
import es.usc.citius.hipster.algorithm.Hipster;
import es.usc.citius.hipster.model.Transition;
import es.usc.citius.hipster.model.function.CostFunction;
import es.usc.citius.hipster.model.function.TransitionFunction;
import es.usc.citius.hipster.model.impl.WeightedNode;
import es.usc.citius.hipster.model.problem.ProblemBuilder;
import es.usc.citius.hipster.model.problem.SearchProblem;
import es.usc.citius.hipster.util.F;
import es.usc.citius.hipster.util.Function;

/**
 * Dijkstra's algorithm describes how to find the cheapest path from one node to another node in a directed weighted graph.
 * 
 * The first parameter is source record. The second parameter is destination record. The third parameter is a name of property that
 * represents 'weight'.
 * 
 * If property is not defined in edge or is null, distance between vertexes are 0.
 * 
 * @author Luca Garulli (l.garulli--at--orientechnologies.com)
 * 
 */
public class OSQLFunctionDijkstra extends OSQLFunctionPathFinder {
  public static final String NAME = "dijkstra";

  private String             paramWeightFieldName;

  public OSQLFunctionDijkstra() {
    super(NAME, 3, 4);
  }

  public LinkedList<OrientVertex> execute(Object iThis, OIdentifiable iCurrentRecord, Object iCurrentResult,
      final Object[] iParams, OCommandContext iContext) {
    final OModifiableBoolean shutdownFlag = new OModifiableBoolean();
    ODatabaseDocumentInternal curDb = ODatabaseRecordThreadLocal.INSTANCE.get();
    final OrientBaseGraph graph = OGraphCommandExecutorSQLFactory.getGraph(false, shutdownFlag);
    try {

      final ORecord record = (ORecord) (iCurrentRecord != null ? iCurrentRecord.getRecord() : null);

      Object source = iParams[0];
      if (OMultiValue.isMultiValue(source)) {
        if (OMultiValue.getSize(source) > 1)
          throw new IllegalArgumentException("Only one sourceVertex is allowed");
        source = OMultiValue.getFirstValue(source);
      }
      paramSourceVertex = graph.getVertex(OSQLHelper.getValue(source, record, iContext));

      Object dest = iParams[1];
      if (OMultiValue.isMultiValue(dest)) {
        if (OMultiValue.getSize(dest) > 1)
          throw new IllegalArgumentException("Only one destinationVertex is allowed");
        dest = OMultiValue.getFirstValue(dest);
      }
      paramDestinationVertex = graph.getVertex(OSQLHelper.getValue(dest, record, iContext));

      paramWeightFieldName = OStringSerializerHelper.getStringContent(iParams[2]);
      if (iParams.length > 3)
        paramDirection = Direction.valueOf(iParams[3].toString().toUpperCase());

      context = iContext;

      // Statistics from OSQLFunctionPathFinder
      int maxDistances = 0;
      int maxSettled = 0;
      int maxUnSettled = 0;
      int maxPredecessors = 0;

      // Create a hipster search problem description
      SearchProblem<Void, OrientVertex, WeightedNode<Void, OrientVertex, Double>> p =
              ProblemBuilder.create()
              .initialState(paramSourceVertex)
              .defineProblemWithoutActions()
              .useTransitionFunction(new TransitionFunction<Void, OrientVertex>() {
                @Override
                public Iterable<Transition<Void, OrientVertex>> transitionsFrom(final OrientVertex source) {
                  return F.map(source.getVertices(paramDirection), new Function<Vertex, Transition<Void, OrientVertex>>() {
                    @Override
                    public Transition<Void, OrientVertex> apply(Vertex dest) {
                      context.incrementVariable("getNeighbors");
                      return Transition.create(source,(OrientVertex)dest);
                    }
                  });
                }
              })
              .useCostFunction(new CostFunction<Void, OrientVertex, Double>() {
                @Override
                public Double evaluate(Transition<Void, OrientVertex> transition) {
                  return (double) getDistance(transition.getFromState(), transition.getState());
                }
              }).build();

      WeightedNode<Void, OrientVertex, Double> lastNode = null;
      AStar<Void, OrientVertex, Double, WeightedNode<Void, OrientVertex, Double>> it = Hipster.createDijkstra(p);
      for(WeightedNode<Void, OrientVertex, Double> node : it){
        lastNode = node;
        if (node.state().equals(paramDestinationVertex)) break;

        // Keep original OrientDB statistics
        // TODO: maxDistances?
        if (it.iterator().getClosed().size() > maxSettled ) maxSettled = it.iterator().getClosed().size();
        if (it.iterator().getOpen().size() > maxUnSettled ) maxUnSettled = it.iterator().getOpen().size();

        if (!context.checkTimeout()) break;
      }

      LinkedList<OrientVertex> path = new LinkedList<OrientVertex>();
      if (lastNode != null) {
        for(WeightedNode<Void, OrientVertex, Double> v : lastNode.path()){
          path.add(v.state());
        }
      }

      return path;

    } finally {
      if (shutdownFlag.getValue())
        graph.shutdown(false);
      ODatabaseRecordThreadLocal.INSTANCE.set(curDb);
    }
  }

  public String getSyntax() {
    return "dijkstra(<sourceVertex>, <destinationVertex>, <weightEdgeFieldName>, [<direction>])";
  }

  protected float getDistance(final OrientVertex node, final OrientVertex target) {
    final Iterator<Edge> edges = node.getEdges(target, paramDirection).iterator();
    if (edges.hasNext()) {
      final Edge e = edges.next();
      if (e != null) {
        final Object fieldValue = e.getProperty(paramWeightFieldName);
        if (fieldValue != null)
          if (fieldValue instanceof Float)
            return (Float) fieldValue;
          else if (fieldValue instanceof Number)
            return ((Number) fieldValue).floatValue();
      }
    }
    return MIN;
  }

  @Override
  protected boolean isVariableEdgeWeight() {
    return true;
  }
}
