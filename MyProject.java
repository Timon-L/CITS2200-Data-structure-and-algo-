import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.Queue;
import java.util.HashMap;

/**
 * This is the my project class that include the methods
 * allDevicesConnected, numPaths, closestInSubnet and maxDownloadSpeed
 * for a network like simulation.
 * @Author Fabian Scheffler(22987128)
 * @Author Ching Chun Liu(22660829)
 */
public class MyProject implements Project {
	/**
	 * cap is the capacity of the edges for maxDownloadSpeed
	 * flows is the total flow between the two devices
	 * neighb is the neighb adjacency matrix that will be the undirected 
	 * version of the adjlist.
	 */
	private int[][] cap, flows, neighb;
	
	/**
	 * excess will be the excess flow at a particular device
	 * height is the relative height that a particular device has
	 */
	private int[] excess, height;
	
    /**
	 * Using a bfs to traverse the adjacency list.
     * Check if all devices are connected given either a directed 
     * adjacency list or undirected one.
     * @param adjlist The adjacency list describing the links 
     * between devices
     * @return true if all devices are connected.
     */
    public boolean allDevicesConnected(int[][] adjlist) {
        Queue<Object> q = new LinkedList<>();
        boolean [] visited = new boolean[adjlist.length];
        Arrays.fill(visited, false);
        q.offer(0);
        int level_count = 1;
        visited[0] = true;

        while(!q.isEmpty()){
            int current_level = (int) q.remove();
            for(int j: adjlist[current_level]){
                if(j > adjlist.length-1 || j < 0){ 
                	//Check if there are any abnormal device 
                	//outside of the list range.
                    return false;
                }
                if(visited[j]){
                    continue;
                }
                q.offer(j);
                level_count ++;
                visited[j] = true;
            }
        }
        if(level_count != adjlist.length){
            return false;
        }
        return true;
    }

	/**
	 * Implementation of bfs to traverse the adjacency list.
	 * @param adjlist is the adjacency list.
	 * @param src is the source device.
	 * @param dst is the destination device.
	 * @return the number of possible minimum paths from source to device.
	 */
    public int numPaths(int[][] adjlist, int src, int dst) {
        Queue<Object> q = new LinkedList<>(); //queue to add vertices to
        int[] distance = new int[adjlist.length]; 
        Arrays.fill(distance, -1);
        q.offer(src);
        int paths = 0;
        int minimum = 0;
        distance[src] = 0;

        while(!q.isEmpty()){
            int current_level = (int) q.remove();
            if(current_level == dst){
                paths ++;
                minimum = distance[src];
            }
            for(int j: adjlist[current_level]){
            	//When distance is not equals to -1, 
            	//that means we have visited the device.
                if(distance[j] != -1){
                    continue;
                }
                else if(j == dst && paths == 0){
                    paths ++;
                    minimum = distance[current_level];
                }
                else if(j == dst && distance[current_level] <= minimum){
                    paths ++;
                }
                if(dst != j) {
                	q.offer(j);
                	//Set distance of neighbour device 
                	//to current distance +1.
                	distance[j] = distance[current_level] + 1; 
                }
            }
        }
        return paths;
    }
    
    /**
     * closestInSubnet is a method that returns minimum number of hops
     * reach some device in the specified subnet. 
     * An ip address is considered to be a subnet if the subnet is 
     * a prefix of the ip address.
     * @param adjlist is the adjacency list
     * @param addrs is the corresponding address of the devices
     * @param src is the index of the source device
     * @param queries is a matrix of queried subnets
     * @return a integer array of closest subnet of each query
     * , if no device is reacheable for that subnet 
     * returns Interger.MAX_VALUE
     */
    public int[] closestInSubnet(int[][] adjlist, short[][] addrs, 
    		int src, short[][] queries) {
    	Queue<Integer> q = new LinkedList<>();
    	int[] querydis = new int[queries.length];
    	int[] distance = new int[adjlist.length];
    	boolean[] visited = new boolean[adjlist.length];
    	Arrays.fill(distance, Integer.MAX_VALUE);
        Arrays.fill(querydis, Integer.MAX_VALUE);
        Arrays.fill(visited,false);
        HashMap<String, ArrayList<Integer>> queryHash = new HashMap<>();
        // Hashing of the queries to O(1) access to each query
        // Hashing is done by having the key as the query 
        // and the value will be an arraylist of the index locations
        for(int i = 0; i < queries.length; i++) {
        	String key = "";
        	ArrayList<Integer> values = new ArrayList<Integer>();
        	for(int j = 0; j < queries[i].length; j++) {
        		if (j == 0) {
        			key += "" + queries[i][j];
        		}
        		else 
        			key += ", " + queries[i][j];
        	}
        	if(!queryHash.containsKey(key)) {
        		values.add(i);
        		queryHash.put(key, values);
        	}
        	else {
        		values = queryHash.get(key);
        		values.add(i);
        		queryHash.put(key, values);
        	}
        }
        distance[src] = 0;
        //does first iteration of the setquerydis for the source device
        querydis = setquerydis(src, queryHash, querydis, addrs, distance);
        q.offer(src);
        visited[src] = true;
        while(!q.isEmpty()) {
        	int u = q.remove();
        	for(int j : adjlist[u]) {
        		if(!visited[j]) {
        			if(distance[j] > distance[u] + 1) {
            			distance[j] = distance[u] + 1;
            			querydis = setquerydis(j, queryHash, querydis
            					, addrs, distance);
            			
        			}
        			visited[j] = true;
        			q.offer(j);
        		}
        	}
        }
        return querydis;
    }

	/**
	 * Implementation of a relabel-to-front max flow algorithm.
	 * Gives us the maximum download speed that the dst device 
	 * can have from the source device
	 * @param adjlist is the adjacency list.
	 * @param speeds is the maximum speed for each link.
	 * @param src is the source device.
	 * @param dst is the destination device.
	 * @return
	 */
    public int maxDownloadSpeed(int[][] adjlist, int[][] speeds, 
    		int src, int dst) {
    	if(src == dst) {
    		return -1;
    	}
    	excess = new int[adjlist.length];
    	height = new int[adjlist.length];
    	flows = new int[adjlist.length][adjlist.length];
    	cap = new int[adjlist.length][adjlist.length];
    	neighb = new int[adjlist.length][adjlist.length];
		int[] dischargeList = new int[adjlist.length - 2];
		int srcflowsum = 0;
		int index = 0;
		//sets up the capacity matrix and the neighb matrix
    	for(int i = 0; i < adjlist.length; i++) {
    		for(int j = 0; j < adjlist.length; j++) {
    			for(int k = 0; k < adjlist[i].length; k++) {
    				if(adjlist[i][k] == j) {
        				cap[i][j] = speeds[i][k];
        				if(neighb[i][j] == 0 || neighb[j][i] == 0) {
            				neighb[i][j] = 1;
            				neighb[j][i] = 1;
        				}
        			}
    			}
    		}
    	}

    	excess[src] = Integer.MAX_VALUE;
    	for(int i = 0; i < adjlist[src].length; i++) {
    		//Push from source to neighbouring devices.
    		srcflowsum += push(src, adjlist[src][i]); 
    	}
    	excess[src] = -srcflowsum;
		height[src] = adjlist.length;
		//Initiate a list with all device except source and destination.
    	for(int i = 0; i < adjlist.length; i++) { 
    		if(!(i == src || i == dst)) {
    			dischargeList[index] = i;
    			index++;
    		}
    	}
    	int[] currentadj = new int[adjlist.length];
    	int currentI = 0;
    	while(currentI < dischargeList.length) {
    		int curNode = dischargeList[currentI];
    		//keeps the height of old current node
    		int curNodeH = height[curNode];
    		currentadj = discharge(curNode, currentadj, adjlist);
			//Check if the device has been relabeled.
    		if(height[curNode] > curNodeH) { 
    			dischargeList = moveFront(dischargeList, currentI);
    			currentI = 0;
    		}
    		else
    			currentI++;
    	}
    	return excess[dst];
    }

	/**
	 * Find the minimum between the current device's excess 
	 * and the possible flow to the end device.
	 * @param start is the current device pushing the data.
	 * @param end is the receiving device of the data.
	 * @return the amount of data pushed.
	 */
    public int push(int start, int end) {
    	int flowAmt = Math.min(excess[start], 
    			cap[start][end] - flows[start][end]);
    	excess[end] += flowAmt;
    	excess[start] -= flowAmt;
    	flows[start][end] += flowAmt;
    	flows[end][start] -= flowAmt;
    	return flowAmt;
    }

	/**
	 * Find the smallest value for neighbour's height, 
	 * and adjust the current target to that +1.
	 * @param target is the current device.
	 * @param adjlist is the adjacency list.
	 */
    public void relabel(int target, int[][] adjlist) {
    	int minHeight = Integer.MAX_VALUE;
    	for(int i = 0; i < neighb.length; i++) {
    		if(neighb[target][i] == 1) {
    			int adj = i;
        		if(cap[target][adj] - flows[target][adj] > 0 
        				&& height[adj] >= height[target]) {
        			if(height[adj] < minHeight) {
        				minHeight = height[adj];
        			}
        		}
    		}   		
    	}
        height[target] = minHeight + 1;
    }

	/**
	 * Check all target's neighbour, repeat push and relabel 
	 * until all excess has been discharged.
	 * @param target is the current device.
	 * @param currentadj
	 * @param adjlist
	 * @return the current devices that have been checked
	 */
    private int[] discharge(int target, int[] currentadj, int[][] adjlist) {
    	while(excess[target] > 0) {
    		int adj = currentadj[target];
    		if(adj >= adjlist[target].length) {
    			relabel(target, adjlist);
				currentadj[target] = 0;
    		}
    		else {
    			boolean pushed = false;
    			for(int i = 0; i < adjlist.length; i++) {
    				if(neighb[target][i] == 1) {
    					int residcap = cap[target][i] - flows[target][i];
    					// only push if the height is one less 
    					// and the the residual capacity is positive
    					if(residcap > 0 
    							&& height[target] == height[i] + 1) {
    						push(target, i);
    						pushed = true;
    					}
    				}
    			}
    			if(!pushed)
					currentadj[target]++;
    		}
    	}
    	return currentadj;
    }

	/**
	 * Move the relabeled device to front of the list.
	 * @param list is the discharge list.
	 * @param target is the current device.
	 * @return the reordered discharge list.
	 */
    private int[] moveFront(int[] list, int target) {
    	int vertex = list[target];
    	for (int i = target; i > 0; i--) {
    		list[i] = list[i - 1];
    	}
    	list[0] = vertex;
    	return list;
    }
    
    /**
     * This method set the query distances for the 
     * given minimum distance device. 
     * @param from is current device we are looking at
     * @param queryHash is the hashmap of querys
     * @param querydis is the query minimum distances
     * @param addrs is the addresses of the devices
     * @param distance is an array of minimum distances
     * @return the new updated query distances array
     */
    private int[] setquerydis(int from,  HashMap<String, 
    		ArrayList<Integer>> queryHash, 
    		int[] querydis, short[][] addrs, int[] distance) {
		String currentIp = "";
    	for(int i = -1; i < addrs[from].length; i++) {
    		if(i == -1) {}
    		else if(i == 0)
    			currentIp += addrs[from][i] + "";
    		else
    			currentIp += ", " + addrs[from][i];
    		if(queryHash.containsKey(currentIp)) {
    			ArrayList<Integer> values = queryHash.get(currentIp);
    			for(int element:values) {
    				querydis[element] = distance[from];
    			}
    			queryHash.remove(currentIp);
    		}
    	}
    	return querydis;
    }
    
}

