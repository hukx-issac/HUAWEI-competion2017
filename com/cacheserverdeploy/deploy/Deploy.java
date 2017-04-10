package com.cacheserverdeploy.deploy;

import java.util.*;
import java.util.concurrent.LinkedBlockingQueue;

public class Deploy {

	public static String[] deployServer(String[] graphContent) {
		DeploySever ds = new DeploySever(graphContent);
		ds.optimalSeverNodeD();
		String[] result = ds.getOptimalPath();
		int expense = ds.expense();
		System.out.println("Expense(DCF): " + ds.expense());
		return result;
	}

}

/**
 * 优化服务器位置的类
 */
class DeploySever {
	private EdgeWeightedDigraph G;
	private Set<Integer> serverNode = new HashSet<Integer>(); // 服务器节点
	IndexMinPQ<Integer> severExpenseQueue; // 服务器花费排序
	private int[] nodeScoreConsumer; // 分数从高到低排序的和消费点直连的点
	private int[] nodeScoreNot; // 分数从高到低排序的非直连节点数组
	private int[] nodeScore; // 分数从高到低排序所有的点
	private int minExpense;
	private String[] optimalPath;
	private final int V; // 图中节点的数量
	DijkstraCostFlow dcf; // 计算对象
	private int searchTime; // 设置定时时间
	private double rate; // 搜索空间比例
	private int maxdepth;
	private int iteration; // 迭代次数
	private double reduceRate; // 搜索后概率降低的幅度
	private int numOfServerNode;
	private double x, y, z; // 出入度、带宽之和、消费点权重
	final long start = System.currentTimeMillis(); // 运行起始时间
	private MinCostMaxFlow mcmf;

	DeploySever(String[] graphContent) {
		this.G = new EdgeWeightedDigraph(graphContent); // 生成图对象
		this.V = G.getV();
		this.nodeScoreConsumer = new int[G.getConsumerNodeNum()];
		this.nodeScoreNot = new int[V - G.getConsumerNodeNum()];
		this.nodeScore = new int[V];
		// 设置参数
		double low, up;
		if (V > 750) {
			low = 3; // 高级用例
			up = 3;
			rate = 0.45; // 搜索空间比例
			maxdepth = 5; // 最大深度
			reduceRate = 0.6; // 搜索后概率降低的幅度
			iteration = 5; // 最大迭代次数
			numOfServerNode = 30; // 每次迭代搜索服务器的增长指数
			x = 0.2; // 出入度
			y = 0.01; // 带宽之和
			z = 0.26; // 消费点权重
			searchTime = 84000;
		} else if (250 < V && V <= 750) {
			low = 2.1; // 中级用例
			up = 2.3;
			rate = 0.6;
			maxdepth = 4;
			reduceRate = 0.2; // 受随机数影响
			iteration = 10;
			numOfServerNode = 100;
			x = 0.2; // 出入度
			y = 0.01; // 带宽之和
			z = 0.26; // 消费点权重
			searchTime = 83000;
		} else {
			low = 2.1; // 初级用例
			up = 2.3;
			rate = 0.5;
			maxdepth = 5;
			reduceRate = 0.25;
			iteration = 5;
			numOfServerNode = 100;
			x = 0.2; // 出入度
			y = 0.01; // 带宽之和
			z = 0.26; // 消费点权重
			searchTime = 80000;
		}
		IndexMinPQ<Double> nodeScoreQueue = new IndexMinPQ<Double>(V); // 所有的节点评分队列
		IndexMinPQ<Double> nodeScoreNotQueue = new IndexMinPQ<Double>(V); // 非直连节点评分队列
		IndexMinPQ<Double> nodeScoreConsumerQueue = new IndexMinPQ<Double>(V); // 直连节点评分队列
		for (int i = 0; i < V; i++) { // 分数从高到低排序的节点数组
			nodeScoreQueue.insert(i, G.score(i, x, y, z));
			if (V > 750) {
				if (G.isMarkConsumer(i) == -1)
					nodeScoreNotQueue.insert(i, G.score(i, 0.5, 1, 0));
				else
					nodeScoreConsumerQueue.insert(i, G.score(i, x, y, z)); // 调
																			// x,y,z
																			// 参数
			}
		}
		if (V > 750) {
			for (int i = 0; i < nodeScoreConsumer.length; i++)
				nodeScoreConsumer[i] = nodeScoreConsumerQueue.delMin();
			for (int i = 0; i < nodeScoreNot.length; i++)
				nodeScoreNot[i] = nodeScoreNotQueue.delMin();
		}
		for (int i = 0; i < V; i++)
			nodeScore[i] = nodeScoreQueue.delMin();
		benginSeverNode(low, up); // 得到起始的一组服务器，初始化 serverNode
		if (V > 750)
			reduce();
	}

	public void optimalSeverNodeM() {
		if (V > 750) // 大用例不进行补点搜索
			return;
		Set<Integer> servers = new HashSet<Integer>(); // 计算时的服务器组
		Map<Integer, Double> probability = new HashMap<Integer, Double>(); // 初始化搜索空间的概率
		for (int i = 0; i < V * rate; i++)
			probability.put(nodeScore[i], 1.0);
		Stack<Integer> waitSearch = new Stack<Integer>(); // 待搜索的点
		servers.addAll(serverNode);
		mcmf = calExpenseM(servers);
		for (int it = 0; it < iteration; it++) {
//			System.out.println("M" + it);
			int times = 0; // 记录搜索了多少个服务器
			numOfServerNode = 10 + 10 * it;
			mcmf = calExpenseM(serverNode);
			severExpenseQueue = mcmf.severExpenseQueue();

			while (!severExpenseQueue.isEmpty()) { // 控制宽度的，搜索服务器的循环
				if (times >= numOfServerNode) { // 判断是否达到了最大搜索服务器的数量
					severExpenseQueue.clear();
					break;
				}
				times++;
				int currentDepth = 0; // 初始化深度
				int currentServerNode = severExpenseQueue.delMin(); // 待搜索服务器的点
				int optimalNode = -1; // 记录搜索的最优点
				boolean updateFlag = true;
				Stack<Integer> hasSearched = new Stack<Integer>(); // 记录搜过的点，以免重复搜索;

				if (servers.contains(currentServerNode)) // currentServerNode
															// 可能是补的消费节点
					servers.remove(currentServerNode);

				while (updateFlag && (currentDepth < maxdepth)) { // 控制深度的循环,如果本层深度没有更新点，则不再深入搜索

					currentDepth++;
					updateFlag = false;
					waitSearch = G.getConnectNode(currentServerNode); // 与待搜索服务器相连的点

					while (!waitSearch.isEmpty()) { // 搜索该深度下与服务器相连的点
						int currentSearchNode = waitSearch.pop();

						/* 判断是否该搜索 */
						if (hasSearched.contains(currentSearchNode))
							continue;
						double randomChance = Math.random();
						if (!probability.containsKey(currentSearchNode)) // 当前搜索点不在搜索空间，不搜索
							continue;
						if (probability.get(currentSearchNode) < randomChance) // 当前搜索点的概率值小于randomChance。不搜索
							continue;
						hasSearched.add(currentSearchNode);
						boolean containsFlag = false; // 判断该点是否已经是服务器了
						if (servers.contains(currentSearchNode))
							containsFlag = true;
						else
							servers.add(currentSearchNode);
						mcmf = calExpenseM(servers); // 计算更新点后的花费
						int expense = mcmf.expense();
						if (expense <= minExpense) {
//							System.out.println("M " + expense);
							minExpense = expense;
							updateFlag = true;
							optimalNode = currentSearchNode; // 记录最优点
							serverNode.clear();
							serverNode.addAll(G.getServerNode()); // 记录当前最好的服务器组合
						} else {
							probability.put(currentSearchNode, probability.get(currentSearchNode) - reduceRate);
						}
						if (!containsFlag)
							servers.remove(currentSearchNode); // 将该点移除，搜下一个点
						if (System.currentTimeMillis() - start > searchTime) {
							end();
							return;
						}
					}

					if (updateFlag)
						currentServerNode = optimalNode;
				}

				if (optimalNode != -1) // 将 remove 的服务器回填一个进去
					servers.add(optimalNode);
				else
					servers.add(currentServerNode);
			}
		}

		end();
	}

	public void optimalSeverNodeD() {
		if (V > 350) // 大用例不进行补点搜索
			return;
		Set<Integer> servers = new HashSet<Integer>(); // 计算时的服务器组
		Map<Integer, Double> probability = new HashMap<Integer, Double>(); // 初始化搜索空间的概率
		for (int i = 0; i < V * rate; i++)
			probability.put(nodeScore[i], 1.0);
		Stack<Integer> waitSearch = new Stack<Integer>(); // 待搜索的点
		servers.addAll(serverNode);

		for (int it = 0; it < iteration; it++) {
//			System.out.println("D " + it);
			int times = 0; // 记录搜索了多少个服务器
			numOfServerNode = 10 + 10 * it;
			dcf = calExpenseD(serverNode);
			severExpenseQueue = dcf.severExpenseQueue();

			while (!severExpenseQueue.isEmpty()) { // 控制宽度的，搜索服务器的循环
				if (times >= numOfServerNode) { // 判断是否达到了最大搜索服务器的数量
					severExpenseQueue.clear();
					break;
				}
				times++;
				int currentDepth = 0; // 初始化深度
				int currentServerNode = severExpenseQueue.delMin(); // 待搜索服务器的点
				int optimalNode = -1; // 记录搜索的最优点
				boolean updateFlag = true;
				Stack<Integer> hasSearched = new Stack<Integer>(); // 记录搜过的点，以免重复搜索;

				if (servers.contains(currentServerNode)) // currentServerNode
															// 可能是补的消费节点
					servers.remove(currentServerNode);

				while (updateFlag && (currentDepth < maxdepth)) { // 控制深度的循环,如果本层深度没有更新点，则不再深入搜索

					currentDepth++;
					updateFlag = false;
					waitSearch = G.getConnectNode(currentServerNode); // 与待搜索服务器相连的点

					while (!waitSearch.isEmpty()) { // 搜索该深度下与服务器相连的点
						int currentSearchNode = waitSearch.pop();

						/* 判断是否该搜索 */
						if (hasSearched.contains(currentSearchNode))
							continue;
						double randomChance = Math.random();
						if (!probability.containsKey(currentSearchNode)) // 当前搜索点不在搜索空间，不搜索
							continue;
						if (probability.get(currentSearchNode) < randomChance) // 当前搜索点的概率值小于randomChance。不搜索
							continue;
						hasSearched.add(currentSearchNode);
						boolean containsFlag = false; // 判断该点是否已经是服务器了
						if (servers.contains(currentSearchNode))
							containsFlag = true;
						else
							servers.add(currentSearchNode);
						dcf = calExpenseD(servers); // 计算更新点后的花费
						int expense = dcf.expense();
						if (expense <= minExpense) {
//							System.out.println("D " + expense);
							minExpense = expense;
							updateFlag = true;
							optimalNode = currentSearchNode; // 记录最优点
							serverNode.clear();
							serverNode.addAll(servers); // 记录当前最好的服务器组合
						} else {
							probability.put(currentSearchNode, probability.get(currentSearchNode) - reduceRate);
						}
						if (!containsFlag)
							servers.remove(currentSearchNode); // 将该点移除，搜下一个点
					}

					if (updateFlag)
						currentServerNode = optimalNode;
				}

				if (optimalNode != -1) // 将 remove 的服务器回填一个进去
					servers.add(optimalNode);
				else
					servers.add(currentServerNode);
			}
		}
		optimalSeverNodeM();
	}

	/**
	 * 结束时运行的函数
	 */
	private void end() {
		mcmf = calExpenseM(serverNode);// mcmf
		optimalPath = mcmf.backAllPath();
		minExpense = mcmf.expense();

		IndexMinPQ<Integer> adds = mcmf.conPathQueue();
		int len = adds.size();
		for (int i = 0; i < len * 0.2; i++) {
			int s = adds.delMin();
			serverNode.add(s);
			mcmf = calExpenseM(serverNode);
			if (mcmf.expense() < minExpense) {
				optimalPath = mcmf.backAllPath();
				minExpense = mcmf.expense();
			} else {
				serverNode.remove(s);
			}
		}
	}

	/**
	 * 反着搜索，删服务器点
	 */
	public void reduce() {
		dcf = calExpenseD(serverNode);
		minExpense = dcf.expense();
		Set<Integer> servers = new HashSet<Integer>();
		severExpenseQueue = dcf.severExpenseQueue();
		IndexMinPQ<Integer> best = dcf.severExpenseQueue();

		for (int it = 0; it < 5; it++) {
			// System.out.println("reduce:" + it);
			servers.clear();
			servers.addAll(G.getServerNode());
			severExpenseQueue = best;
			while (!severExpenseQueue.isEmpty()) {
				int c = severExpenseQueue.delMin();
				serverNode.remove(c);
				dcf = calExpenseD(serverNode);
				int expense = dcf.expense();
				if (expense < minExpense) {
					minExpense = expense;
					// System.out.println(expense);
					serverNode.clear();
					serverNode.addAll(G.getServerNode());
					best = dcf.severExpenseQueue();
				} else
					serverNode.add(c);
				if (System.currentTimeMillis() - start > searchTime) {
					dcf = calExpenseD(serverNode);
					optimalPath = dcf.resultPath();
					minExpense = dcf.expense();
					return;
				}
			}
		}
	}

	/**
	 * 根据排序得到起始的一组服务器
	 */
	private void benginSeverNode(double low, double up) {
		if (V > 750) {
			for (int i = 0; i < 125; i++)
				serverNode.add(nodeScoreConsumer[i]);
			for (int i = 0; i < 8; i++)
				serverNode.add(nodeScoreNot[i]);
			return;
		}

		Set<Integer> servers = new HashSet<Integer>();
		int numOfNode = (int) (G.getConsumerNodeNum() / up); // ( 消费节点数/up
																// ~消费节点数/low)范围内取服务器
		int upNum = (int) (G.getConsumerNodeNum() / low);
		for (int i = 0; i < numOfNode; i++)
			servers.add(nodeScore[i]);

		mcmf = calExpenseM(servers);
		minExpense = mcmf.expense();
		serverNode.addAll(servers); // 初始化 serverNode 添加打分的点
		while (numOfNode < upNum) {
			servers.add(nodeScore[numOfNode]);
			mcmf = calExpenseM(servers);
			int expense = mcmf.expense();
			if (expense < minExpense) {
				minExpense = expense;
				serverNode.clear();
				serverNode.addAll(servers);
			}
			numOfNode++;
		}
		reduce();
	}

	/**
	 * 计算这些服务器的花费
	 * 
	 * @param serverNode
	 */
	private DijkstraCostFlow calExpenseD(Set<Integer> servers) {
		Set<Integer> calServers = new HashSet<Integer>();
		calServers.addAll(servers);
		G.setSeverNode(set2Array(calServers)); // 设置服务器超汇节点
		DijkstraCostFlow dcf = new DijkstraCostFlow(G); // dijkstra 分配流量路径
		/* 判断是否有需要添加的服务器(消费节点没有满足和路径带宽超过服务器成本),将要补的服务器补进 severNode */
		Set<Integer> addSever = dcf.addSever();
		if (!addSever.isEmpty()) {
			for (int s : addSever)
				calServers.add(s);
			G.setSeverNode(set2Array(calServers));
			dcf = new DijkstraCostFlow(G); // 将补的服务器带进去再算一遍
		}
		return dcf;
	}

	private MinCostMaxFlow calExpenseM(Set<Integer> servers) {
		Set<Integer> calServers = new HashSet<Integer>();
		calServers.addAll(servers);
		G.setSeverNode(set2Array(calServers)); // 设置服务器超汇节点
		MinCostMaxFlow mcmf = new MinCostMaxFlow(G); // mcmf 分配流量路径
		/* 判断是否有需要添加的服务器(消费节点没有满足和路径带宽超过服务器成本),将要补的服务器补进 severNode */
		Set<Integer> addSever = mcmf.addServer();
		if (!addSever.isEmpty()) {
			for (int s : addSever)
				calServers.add(s);
			G.setSeverNode(set2Array(calServers));
			mcmf = new MinCostMaxFlow(G); // 将补的服务器带进去再算一遍
		}
		return mcmf;

	}

	/**
	 * 将集合转化为数组的类
	 * 
	 * @param set
	 *            服务器集合
	 * @return 服务器数组
	 */
	private int[] set2Array(Set<Integer> set) {
		int[] array = new int[set.size()];
		int i = 0;
		for (Integer element : set) {
			array[i] = element.intValue();
			i++;
		}
		return array;
	}

	public int expense() {
		return minExpense;
	}

	public int getV() {
		return G.getV();
	}

	public String[] getOptimalPath() {
		return optimalPath;
	}

}

/**
 * 超汇点的 DijkstraSP 费用流
 */
class DijkstraCostFlow {
	private int[][] cost; // 边的费用
	private int[][] bandWidth; // 边的带宽
	private int expense; // 总花费
	private LinkedList<String> resultContent = new LinkedList<String>(); // 所有找到的服务器到消费节点路径
	private Set<Integer> addSever = new HashSet<Integer>(); // 添加的服务器
	private int N; // 节点个数(加两个超汇节点)
	private Map<Integer, Integer> consumerExpense = new HashMap<Integer, Integer>(); // 记录每个消费节点上的路径花费，判断是否超过服务器成本
	private Map<Integer, Integer> severExpense = new HashMap<Integer, Integer>(); // 服务器流量的花费

	DijkstraCostFlow(EdgeWeightedDigraph G) {
		expense += G.severExpense();
		N = G.getV() + 2; // 节点个数
		Map<Integer, Edge>[] adj = G.getAdj();
		bandWidth = new int[N][N];
		cost = new int[N][N];
		for (int i = 0; i < adj.length; i++) {
			for (int j : adj[i].keySet()) {
				this.bandWidth[i][j] = adj[i].get(j).bandWidth();
				this.cost[i][j] = adj[i].get(j).cost();
			}
		}

		while (!finish()) { // 寻找最短路径分配流量
			DijkstraSP dij = new DijkstraSP(G, bandWidth, cost); // 寻找超汇起点到超汇终点的最短路径
			Stack<Edge> sp = dij.getSP();
			if (sp.isEmpty()) // 如果找不到最短路径，结束寻找
				break;
			Path path = new Path(sp, bandWidth, cost);

			int[] pathNum = path.pathNum(); // 一条服务器到消费节点的路径
			int flow = path.flow(); // 路径的流量
			int cNode = pathNum[pathNum.length - 1]; // 与消费节点直连的节点编号
			// 求使用带宽
			int use = Math.min(flow, bandWidth[cNode][N - 1]);

			String onePath = path.toString() + G.getConsumerNode(cNode) + " " + use; // 一条结果路径，路径节点和流量
			resultContent.add(onePath);

			for (int i = 0; i < pathNum.length - 1; i++)
				bandWidth[pathNum[i]][pathNum[i + 1]] -= use;
			bandWidth[cNode][N - 1] -= use;
			int currentExpense = path.expense() * use; // 计算花费

			if (consumerExpense.containsKey(cNode)) // 消费节点的花费
				consumerExpense.put(cNode, consumerExpense.get(cNode) + currentExpense);
			else
				consumerExpense.put(cNode, currentExpense);

			if (severExpense.containsKey(pathNum[0])) // 服务器流量的花费
				severExpense.put(pathNum[0], severExpense.get(pathNum[0]) + currentExpense);
			else
				severExpense.put(pathNum[0], currentExpense);

			expense += currentExpense; // 加入总花费
		}

		for (int i = 0; i < bandWidth.length; i++) { // 检查是否所有消费点都满足和路径花费超过服务器的点,找出没有满足的点
			if (bandWidth[i][N - 1] != 0)
				addSever.add(i);
			for (int key : consumerExpense.keySet()) {
				if (consumerExpense.get(key) > G.serverDeploymentCosts())
					addSever.add(key);
			}
		}
	}

	/**
	 * @return 判断到超汇终点的边带宽之和是否为0，即是是否满足全部消费节点
	 */
	private boolean finish() {
		int sum = 0;
		for (int i = 0; i < bandWidth.length; i++)
			sum += bandWidth[i][N - 1];
		return (sum == 0);
	}

	/**
	 * 服务器排序的最小优先队列
	 * 
	 * @return
	 */
	public IndexMinPQ<Integer> severExpenseQueue() {
		IndexMinPQ<Integer> severExpenseQueue = new IndexMinPQ<Integer>(N - 2);
		for (int severNode : severExpense.keySet())
			severExpenseQueue.insert(severNode, severExpense.get(severNode));
		return severExpenseQueue;
	}

	/**
	 * @return 返回图对象G中设置的服务器与分配后（流量*单位）成本的总花费
	 */
	public int expense() {
		return expense;
	}

	/**
	 * @return 返回与没有满足的消费节点直连的节点
	 */
	public Set<Integer> addSever() {
		return addSever;
	}

	/**
	 * @return 返回按格式要求的生成的字符串数组路径
	 */
	public String[] resultPath() {
		String[] result = new String[resultContent.size() + 2];
		result[0] = resultContent.size() + "";
		result[1] = "";
		for (int i = 2; i < result.length; i++)
			result[i] = resultContent.get(i - 2);
		return result;
	}
}

/**
 * 路径类
 */
class Path {
	private int[] pathNum;
	private int flow;
	private int expense = 0;

	Path(Stack<Edge> sp, int[][] bandWidth, int[][] cost) {
		int edgeNum = sp.size();
		pathNum = new int[(edgeNum - 2) + 1];
		final int INF = Integer.MAX_VALUE / 2 - 1;
		flow = INF;
		int i = 0;
		if (!sp.isEmpty()) // 弹出超汇节点的边
			sp.pop();
		while (!sp.isEmpty()) {
			Edge e = sp.pop();
			if (bandWidth[e.from()][e.to()] < flow)
				flow = bandWidth[e.from()][e.to()];
			expense += cost[e.from()][e.to()];
			pathNum[i++] = e.from();
		}
	}

	/**
	 * @return 路径的花费
	 */
	public int expense() {
		return expense;
	}

	/**
	 * @return 路径的流量
	 */
	public int flow() {
		return flow;
	}

	/**
	 * @return 路径的的节点数组(不包括超汇节点和消费节点)
	 */
	public int[] pathNum() {
		return pathNum;
	}

	public String toString() {
		String result = new String();
		for (int p : pathNum)
			result += p + " ";
		return result;
	}

}

/**
 * DijkstraSP 找最短路径
 */
class DijkstraSP {
	private Edge[] edgeTo;
	private int[] distTo;
	private IndexMinPQ<Integer> pq;
	private int startingPoint; // 超汇起点
	private int destination; // 超汇终点
	private int[][] cost; // 图的权重(每条边单位流量成本)
	private int[][] bandWidth; // 每条边的当前带宽

	DijkstraSP(EdgeWeightedDigraph G, int[][] bandWidth, int[][] cost) {
		this.cost = cost;
		this.bandWidth = bandWidth;
		startingPoint = G.getV();
		destination = G.getV() + 1;
		int N = G.getV() + 2; // 节点个数

		distTo = new int[N];
		edgeTo = new Edge[N];
		for (int v = 0; v < N; v++)
			distTo[v] = Integer.MAX_VALUE;
		distTo[startingPoint] = 0;

		// relax
		pq = new IndexMinPQ<Integer>(G.getV() + 2);
		pq.insert(startingPoint, distTo[startingPoint]);
		while (!pq.isEmpty()) {
			int v = pq.delMin();
			for (Edge e : G.getAdj()[v].values())
				relax(e);
			if (v == destination)
				break;
		}
	}

	private void relax(Edge e) {
		int start = e.from(), end = e.to();
		if (bandWidth[start][end] <= 0) // 对当前带宽为0的边，不进行松弛
			return;
		if (distTo[end] > distTo[start] + cost[e.from()][e.to()]) {
			distTo[end] = distTo[start] + cost[e.from()][e.to()];
			edgeTo[end] = e;
			if (pq.contains(end))
				pq.changeKey(end, distTo[end]);
			else
				pq.insert(end, distTo[end]);
		}
	}

	/**
	 * @return 从(与消费节点直连的点)到超汇起点(服务器)的节点，压入栈
	 */
	public Stack<Edge> getSP() {
		Stack<Edge> path = new Stack<Edge>();
		while (startingPoint != destination) {
			if (edgeTo[destination] == null)
				break;
			else {
				path.push(edgeTo[destination]);
				destination = edgeTo[destination].from();
			}
		}
		return path;
	}
}

/**
 * 边类
 */
class Edge {
	private final int start; // 边的起点
	private final int end; // 边的终点
	private final int cost; // 单位网络租用费
	private final int bandWidth; // 带宽大小

	Edge(int start, int end, int bandWidth, int cost) {
		this.start = start;
		this.end = end;
		this.cost = cost;
		this.bandWidth = bandWidth;
	}

	public int from() {
		return start;
	}

	public int to() {
		return end;
	}

	public int cost() {
		return cost;
	}

	public int bandWidth() {
		return bandWidth;
	}

	public Edge reversal() {
		return new Edge(this.end, this.start, this.bandWidth, this.cost);
	}
}

/**
 * 带权重的图类
 */
class EdgeWeightedDigraph {
	private final int V; // 节点总数
	private final int E; // 链路总数
	private final int consumerNodeNum; // 消费节点总数
	private final int serverDeploymentCosts; // 服务器部署成本
	private Map<Integer, Edge>[] adj; // 邻接链表
	private int[][] consumerPoints; // 消费节点表
	private Map<Integer, Integer> connectNode = new HashMap<Integer, Integer>(); // 节点与消费节点对应关系
	private int severExpense;

	@SuppressWarnings("unchecked")
	EdgeWeightedDigraph(String[] graphContent) {
		String[] firstLine = graphContent[0].split(" ");
		this.V = Integer.parseInt(firstLine[0]);
		this.E = Integer.parseInt(firstLine[1]);
		this.consumerNodeNum = Integer.parseInt(firstLine[2]);
		this.serverDeploymentCosts = Integer.parseInt(graphContent[2].split(" ")[0]);
		adj = new TreeMap[V + 2];
		for (int i = 0; i < V + 2; i++) {
			adj[i] = new TreeMap<Integer, Edge>();
		}
		int[] road = new int[4];
		for (int i = 4; i < 4 + E; i++) {
			String[] s = graphContent[i].split(" ");
			for (int j = 0; j < 4; j++) {
				road[j] = Integer.parseInt(s[j]);
			}
			Edge e = new Edge(road[0], road[1], road[2], road[3]);

			adj[road[0]].put(road[1], e);
			adj[road[1]].put(road[0], e.reversal());
		}
		consumerPoints = new int[consumerNodeNum][2];
		String[] consumerContent = Arrays.copyOfRange(graphContent, 5 + E, 5 + E + consumerNodeNum);
		for (int i = 0; i < consumerNodeNum; i++) {
			consumerPoints[i][0] = Integer.parseInt(consumerContent[i].split(" ")[1]);
			consumerPoints[i][1] = Integer.parseInt(consumerContent[i].split(" ")[2]);
			connectNode.put(consumerPoints[i][0], i);
		}
		// 超汇节点(终点)
		for (int i = 0; i < consumerNodeNum; i++) {
			Edge e = new Edge(consumerPoints[i][0], V + 1, consumerPoints[i][1], 0);
			adj[consumerPoints[i][0]].put(V + 1, e);
		}
	}

	/**
	 * @param i
	 *            节点编号
	 * @return 判断一个节点是否为与消费节点直连的标记节点,不是 -1,是返回需求流量
	 */
	public int isMarkConsumer(int i) {
		for (int[] cp : consumerPoints) {
			if (i == cp[0])
				return cp[1];
		}
		return -1;
	}

	/**
	 * @param i
	 *            节点编号
	 * @return 返回一个节点的的出入度和总的流量
	 */
	private int[] fullRoadandFlow(int i) {
		int[] result = new int[2];
		int total = 0;
		result[0] = adj[i].size();
		for (Edge e : adj[i].values())
			total += e.bandWidth();
		result[1] = total;
		return result;
	}

	/**
	 * @param i
	 *            节点编号
	 * @param x
	 *            出入度权重
	 * @param y
	 *            节点所有边的带宽之和权重
	 * @param z
	 *            消费节点需求
	 * @return 根据权重为节点打的分
	 */
	public double score(int i, double x, double y, double z) {
		double score = 0;
		int flow = isMarkConsumer(i);
		int[] fullRoadandFlow = fullRoadandFlow(i);
		if (flow == -1)
			z = 0;
		if (flow > fullRoadandFlow[1])
			return Double.NEGATIVE_INFINITY;
		return -1 * (fullRoadandFlow[0] * x + fullRoadandFlow[1] * y + flow * z);
	}

	/**
	 * @param severNode
	 *            将服务器添加为超汇点(起点)
	 */
	public void setSeverNode(int[] severNode) {
		adj[V].clear();
		for (int i = 0; i < severNode.length; i++) {
			Edge e = new Edge(V, severNode[i], Integer.MAX_VALUE / 2 - 1, 0);
			adj[V].put(severNode[i], e);
		}
		severExpense = serverDeploymentCosts * severNode.length;
	}

	/**
	 * @return 返回当前图中的所有服务器节点
	 */
	public Set<Integer> getServerNode() {
		return adj[V].keySet();
	}

	/**
	 * @param node
	 *            一个节点
	 * @return 返回与节点相连的消费节点
	 */
	public int getConsumerNode(int node) {
		return connectNode.get(node);
	}

	/**
	 * @return 返回图中服务器部署花费(单个服务器成本*数量)
	 */
	public int severExpense() {
		return severExpense;
	}

	/**
	 * @return 单个服务器成本
	 */
	public int serverDeploymentCosts() {
		return serverDeploymentCosts;
	}

	/**
	 * @return 返回邻接表
	 */
	public Map<Integer, Edge>[] getAdj() {
		return adj;
	}

	/**
	 * @param i
	 *            节点i
	 * @return 返回与节点i相连的所有的节点编号
	 */
	public Stack<Integer> getConnectNode(int i) {
		Stack<Integer> cn = new Stack<Integer>();
		for (int j : adj[i].keySet())
			cn.push(j);
		return cn;
	}

	/**
	 * @return 消费节点的二维数组，第一维是消费节点编号；第二维 0 是与消费节点直连的节点编号，1 是消费节点需求带宽
	 */
	public int[][] getConsumerPoints() {
		return consumerPoints;
	}

	/**
	 * @return 从文件中读取的节点的数量(不包括超汇节点和消费节点)
	 */
	public int getV() {
		return this.V;
	}

	/**
	 * @return 消费节点数量
	 */
	public int getConsumerNodeNum() {
		return consumerNodeNum;
	}
}

/**
 * 带索引的优先队列
 */
class IndexMinPQ<Key extends Comparable<Key>> implements Iterable<Integer> {
	private int maxN;
	private int n;
	private int[] pq;
	private int[] qp;
	private Key[] keys;

	public IndexMinPQ(int maxN) {
		if (maxN < 0)
			throw new IllegalArgumentException();
		this.maxN = maxN;
		n = 0;
		keys = (Key[]) new Comparable[maxN + 1];
		pq = new int[maxN + 1];
		qp = new int[maxN + 1];
		for (int i = 0; i <= maxN; i++)
			qp[i] = -1;
	}

	public boolean isEmpty() {
		return n == 0;
	}

	public boolean contains(int i) {
		if (i < 0 || i >= maxN)
			throw new IndexOutOfBoundsException();
		return qp[i] != -1;
	}

	public void insert(int i, Key key) {
		if (i < 0 || i >= maxN)
			throw new IndexOutOfBoundsException();
		if (contains(i))
			throw new IllegalArgumentException("index is already in the priority queue");
		n++;
		qp[i] = n;
		pq[n] = i;
		keys[i] = key;
		swim(n);
	}

	public int delMin() {
		if (n == 0)
			throw new NoSuchElementException("Priority queue underflow");
		int min = pq[1];
		exch(1, n--);
		sink(1);
		assert min == pq[n + 1];
		qp[min] = -1;
		keys[min] = null;
		pq[n + 1] = -1;
		return min;
	}

	public void changeKey(int i, Key key) {
		if (i < 0 || i >= maxN)
			throw new IndexOutOfBoundsException();
		if (!contains(i))
			throw new NoSuchElementException("index is not in the priority queue");
		keys[i] = key;
		swim(qp[i]);
		sink(qp[i]);
	}

	private boolean greater(int i, int j) {
		return keys[pq[i]].compareTo(keys[pq[j]]) > 0;
	}

	private void exch(int i, int j) {
		int swap = pq[i];
		pq[i] = pq[j];
		pq[j] = swap;
		qp[pq[i]] = i;
		qp[pq[j]] = j;
	}

	private void swim(int k) {
		while (k > 1 && greater(k / 2, k)) {
			exch(k, k / 2);
			k = k / 2;
		}
	}

	private void sink(int k) {
		while (2 * k <= n) {
			int j = 2 * k;
			if (j < n && greater(j, j + 1))
				j++;
			if (!greater(k, j))
				break;
			exch(k, j);
			k = j;
		}
	}

	public void clear() {
		n = 0;
		keys = (Key[]) new Comparable[maxN + 1];
		pq = new int[maxN + 1];
		qp = new int[maxN + 1];
		for (int i = 0; i <= maxN; i++)
			qp[i] = -1;
	}

	public int size() {
		return n;
	}

	public Iterator<Integer> iterator() {
		return new HeapIterator();
	}

	private class HeapIterator implements Iterator<Integer> {
		private IndexMinPQ<Key> copy;

		public HeapIterator() {
			copy = new IndexMinPQ<Key>(pq.length - 1);
			for (int i = 1; i <= n; i++)
				copy.insert(pq[i], keys[pq[i]]);
		}

		public boolean hasNext() {
			return !copy.isEmpty();
		}

		public void remove() {
			throw new UnsupportedOperationException();
		}

		public Integer next() {
			if (!hasNext())
				throw new NoSuchElementException();
			return copy.delMin();
		}
	}
}

/**
 * 最小费用最大流类
 */
class MinCostMaxFlow {
	private boolean found[];
	private int N, flow[][], dad[], dist[], pi[];
	private final int INF = Integer.MAX_VALUE / 2 - 1;
	private int bandWidth[][];
	private int cost[][];
	private int minCost;
	private List<List<Integer>> result = new ArrayList();
	private Map<Integer, Integer> severExpense = new HashMap<Integer, Integer>();// 返回服务器费用
	private HashMap<Integer, Integer> conExpense = new HashMap<>();// 计算每个消费节点路径费用
	private HashMap<Integer, Integer> conPahtNum = new HashMap<>(); // 计算每个消费节点路径数目
	private HashSet<Integer> badPain = new HashSet<>();
	private int start;
	private int end;
	private String[] backAllPath;
	int[][] capacity;
	int[] pre;

	EdgeWeightedDigraph G;

	MinCostMaxFlow(EdgeWeightedDigraph G) {
		this.G = G;
		Map<Integer, Edge>[] adj = G.getAdj();
		N = adj.length; // 点的个数,加了两个超汇节点
		capacity = new int[N][N];
		pre = new int[N];
		bandWidth = new int[N][N];
		cost = new int[N][N];
		for (int i = 0; i < adj.length; i++)
			for (int j : adj[i].keySet()) {
				this.bandWidth[i][j] = adj[i].get(j).bandWidth();
				this.cost[i][j] = adj[i].get(j).cost();
			}

		start = G.getV();
		end = G.getV() + 1;
		found = new boolean[N];
		flow = new int[N][N];
		dist = new int[N + 1];
		dad = new int[N];
		pi = new int[N];
		int totalFlow = 0, totalCost = 0;
		while (search(start, end)) {
			List<Integer> temp = new ArrayList();
			int amt = INF;
			for (int x = end; x != start; x = dad[x]) { // 找到路径最大能通过多少流量
				amt = Math.min(amt, flow[x][dad[x]] != 0 ? flow[x][dad[x]] : bandWidth[dad[x]][x] - flow[dad[x]][x]);
				temp.add(x); // 把路径压入栈
			}
			// 记录路径
			temp.add(start);
			temp.add(amt);
			result.add(temp);

			// 计算费用
			for (int x = end; x != start; x = dad[x]) {
				if (flow[x][dad[x]] != 0) {
					flow[x][dad[x]] -= amt;
					totalCost -= amt * cost[x][dad[x]];
				} else {
					flow[dad[x]][x] += amt;
					totalCost += amt * cost[dad[x]][x];
				}
			}
			totalFlow += amt;
		}
		totalCost += G.severExpense();
		minCost = totalCost;
		for (int i = 0; i < G.getV(); i++) {
			conExpense.put(i, 0);
		}
		outPut();
		checkServer();
		backPath();
	}

	private boolean search(int source, int sink) {
		Arrays.fill(found, false);
		Arrays.fill(dist, INF);
		dist[source] = 0;

		while (source != N) {
			int best = N;
			found[source] = true;
			for (int k = 0; k < N; k++) {
				if (found[k])
					continue;
				if (flow[k][source] != 0) {
					int val = dist[source] + pi[source] - pi[k] - cost[k][source];
					if (dist[k] > val) {
						dist[k] = val;
						dad[k] = source;
					}
				}
				if (flow[source][k] < bandWidth[source][k]) {
					int val = dist[source] + pi[source] - pi[k] + cost[source][k];
					if (dist[k] > val) {
						dist[k] = val;
						dad[k] = source;
					}
				}
				if (dist[k] < dist[best])
					best = k;
			}
			source = best;
		}
		for (int k = 0; k < N; k++)
			pi[k] = Math.min(pi[k] + dist[k], INF);
		return found[sink];
	}

	public int expense() {
		return minCost;
	}

	private void checkServer() {
		for (int i = 0; i < G.getConsumerNodeNum(); i++) {
			if (capacity[G.getConsumerPoints()[i][0]][N - 1] != G.getConsumerPoints()[i][1])
				badPain.add(G.getConsumerPoints()[i][0]);
		}
	}

	public HashSet<Integer> addServer() {
		for (Integer e : conExpense.keySet()) {
			if (conExpense.get(e) > G.severExpense())
				badPain.add(e);
		}
		return badPain;
	}

	private void outPut() {
		for (int i = 0; i < result.size(); i++) {
			List<Integer> temp = result.get(i);
			for (int j = 0; j < temp.size() - 2; j++) {
				if (capacity[temp.get(j)][temp.get(j + 1)] == 0)
					capacity[temp.get(j + 1)][temp.get(j)] += temp.get(temp.size() - 1);
				else {
					if (capacity[temp.get(j + 1)][temp.get(j)] < capacity[temp.get(j)][temp.get(j + 1)])
						capacity[temp.get(j)][temp.get(j + 1)] = capacity[temp.get(j)][temp.get(j + 1)]
								- temp.get(temp.size() - 1);
					else {
						capacity[temp.get(j)][temp.get(j + 1)] = 0;
						capacity[temp.get(j + 1)][temp.get(j)] = temp.get(temp.size() - 1)
								- capacity[temp.get(j)][temp.get(j + 1)];
					}
				}
			}
		}
	}

	/**
	 * 服务器排序的最小优先队列
	 * 
	 * @return
	 */
	public IndexMinPQ<Integer> severExpenseQueue() {
		IndexMinPQ<Integer> severExpenseQueue = new IndexMinPQ<Integer>(N - 2);
		for (int severNode : severExpense.keySet())
			severExpenseQueue.insert(severNode, severExpense.get(severNode));
		return severExpenseQueue;
	}

	/**
	 * 消費节点排序的最小优先队列
	 * 
	 * @return
	 */
	public IndexMinPQ<Integer> conPathQueue() {
		IndexMinPQ<Integer> conPathQueue = new IndexMinPQ<Integer>(N - 2);
		for (int severNode : conPahtNum.keySet())
			conPathQueue.insert(severNode, conPahtNum.get(severNode) * -1);
		return conPathQueue;
	}

	/**
	 * 返回当前所有路径
	 * 
	 */
	public String[] backAllPath() {
		return backAllPath;
	}

	private void backPath() {
		HashSet<String> allPath = new HashSet<>();
		Queue<Integer> queue = new LinkedBlockingQueue<>();
		while (OUT_BFS(start, end, queue) != null) {
			queue.clear();
			Stack<Integer> road = new Stack<>();
			if (OUT_BFS(start, end, queue) != null) {
				for (Integer e : OUT_BFS(start, end, queue))
					road.push(e);
			}
			int roadSize = road.size();
			int[] aroad = new int[roadSize];
			for (int i = 0; i < roadSize; i++)
				aroad[i] = road.pop();
			// 找到改路径的最小流量
			int minflow = 50000;
			int cost = 0;
			for (int i = 0; i < aroad.length - 1; i++) {
				cost += this.cost[aroad[i]][aroad[i + 1]];
				if (minflow > capacity[aroad[i]][aroad[i + 1]])
					minflow = capacity[aroad[i]][aroad[i + 1]];
			}
			// 更新流量
			for (int i = 0; i < aroad.length - 1; i++)
				capacity[aroad[i]][aroad[i + 1]] -= minflow;
			String path1 = "";
			for (int i = 1; i < aroad.length - 1; i++)
				path1 += aroad[i] + " ";
			if (severExpense.containsKey(aroad[1])) // 服务器流量的花费
				severExpense.put(aroad[1], severExpense.get(aroad[1]) + minflow * cost);
			else
				severExpense.put(aroad[1], minflow * cost);
			if (conPahtNum.containsKey(aroad[aroad.length - 2])) { // 消费节点直连节点路径数
				conPahtNum.put(aroad[aroad.length - 2], conPahtNum.get(aroad[aroad.length - 2]) + 1);
			} else {
				conPahtNum.put(aroad[aroad.length - 2], 0);
			}
			conExpense.put(aroad[aroad.length - 2], conExpense.get(aroad[aroad.length - 2]) + minflow * cost);
			String path = path1 + G.getConsumerNode(aroad[aroad.length - 2]) + " " + minflow;
			allPath.add(path);
		}
		String[] AllPath = new String[allPath.size() + 2];
		AllPath[0] = String.valueOf(allPath.size());
		AllPath[1] = "";
		int abcd = 2;
		for (String e : allPath)
			AllPath[abcd++] = e;
		backAllPath = AllPath;
	}

	private Iterable<Integer> OUT_BFS(int start, int end, Queue<Integer> queue) {
		boolean[] marked = new boolean[G.getV() + 2];
		int[] edgeTo = new int[G.getV() + 2];
		marked[start] = true;
		queue.add(start);
		while (!queue.isEmpty()) {
			int v = queue.poll();
			for (int w : G.getAdj()[v].keySet()) {
				if (!marked[w])
					if (capacity[v][w] > 0) {
						marked[w] = true;
						edgeTo[w] = v;
						queue.add(w);
					}
			}
		}
		if (marked[end]) {
			Stack<Integer> path = new Stack<Integer>();
			for (int x = end; x != start; x = edgeTo[x])
				path.push(x);
			path.push(start);
			return path;
		} else {
			return null;
		}
	}

}