/////////////
// BFS, DFS and Simulated Annealing
// By Shreyas Kolpe, 20/9/2017
////////////

import java.util.Date;
import java.util.Timer;
import java.util.TimerTask;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.NoSuchElementException;
import java.util.Queue;
import java.util.Random;
import java.io.*;
import java.util.Stack;

//Lizard positions are stored in an array of Position objects in each node of BFS/DFS tree
class Position{
	int row;
	int col;
	Position(int row, int col){
		this.row = row;
		this.col = col;
	}
	Position(Position pos){
		row = pos.row;
		col = pos.col;
	}
}

//Tree positions are stored in an array of TreePosition objects
class TreePosition{
	int positions[];
	TreePosition(ArrayList<Integer> pos){
		positions = new int[pos.size()];
		for(int i=0; i<positions.length;++i)
			positions[i] = pos.get(i).intValue();
	}
}

//Rows with trees in them are divided into one or more subrows, which are stored in Subrow type
class Subrow{
	int subrow, realrow, startCol, endCol;
	Subrow(int subrow, int realrow, int startCol, int endCol){
		this.subrow = subrow;
		this.realrow = realrow;
		this.startCol = startCol;
		this.endCol = endCol;
	}
	public String toString(){
		return subrow+" "+realrow+" "+startCol+" "+endCol;
	}
}

//A Node object encapsulates all the state information for a tree node. 
//These are namely the positions of lizards, the current subrow to be filled, and the number of lizards placed so far
class Node{
	Position positions[];
	int currentsubrow;
	int numLizards;
	Node(Position[] parentPositions, Position newPosition, int numLizards, int currentsubrow){
		positions = new Position[numLizards];
		this.numLizards = numLizards;
		int i;
		for(i=0; i<parentPositions.length; ++i){
			positions[i] = new Position(parentPositions[i]);
		}
		positions[i] = new Position(newPosition);		
		this.currentsubrow = currentsubrow;
	}
	//Initial empty board
	Node(){
		positions = null;
		numLizards = 0;
		currentsubrow = -1;
	}
	Node(Position newPosition, int numLizards, int currentsubrow){
		positions = new Position[1];
		positions[0] = newPosition;
		this.numLizards = numLizards;
		this.currentsubrow = currentsubrow;
	}
	void display(){
		System.out.print("\n"+currentsubrow + " , "+numLizards + " : ");
		if(positions == null){
			System.out.println("Empty Board");
			return;
		}
		for(int i=0;i<positions.length;++i)
			System.out.print("["+positions[i].row+","+positions[i].col+"], ");
	}
}

//Both BFS and DFS are executed by creating objects of Search Instance type.
//This is mainly due to the salient difference between the two being the bookkeeping data structure
class SearchInstance{
	int n;
	int p;
	TreePosition[] trees;
	Subrow[] subrowList;
	SolutionState answer;
	int [][]matrix;
	SearchInstance(int n, int p, int[][] matrix){
		this.n = n;
		this.p = p;
		this.matrix = matrix;
		trees = new TreePosition[n];
		for(int i=0; i<n; ++i){
			ArrayList<Integer> pos = new ArrayList<Integer>();
			pos.add(new Integer(-1));
			for(int j=0; j<n; ++j)
				if(matrix[i][j]==2)
					pos.add(new Integer(j));
			pos.add(new Integer(n));
			trees[i] = new TreePosition(pos);
		}
		ArrayList<Subrow> subrows = new ArrayList<Subrow>();
		int subrownum = 0;
		for(int i=0; i<trees.length; ++i){
			for(int j=0; j<trees[i].positions.length - 1; ++j){
				if((trees[i].positions[j+1] - trees[i].positions[j]) > 1){
					subrows.add(new Subrow(subrownum, i, trees[i].positions[j]+1, trees[i].positions[j+1]-1));
					subrownum++;
				}
			}
		}
		subrowList = subrows.toArray(new Subrow[subrows.size()]);
	}
	
	//The solution is written using this object
	class SolutionState{
		boolean isSolvable = false;
		Position[] solutionPositions;
		SolutionState(boolean isSolvable, Position[] solutionPositions){
			this.isSolvable = isSolvable;
			this.solutionPositions = solutionPositions;
		}
		void write(){
			try{
				FileWriter fr = new FileWriter("output.txt");
				BufferedWriter br = new BufferedWriter(fr);
				if(!isSolvable){
					br.write("FAIL\n");
					br.close();
					return;
				}
				for(int i=0; i<solutionPositions.length;++i)
					matrix[solutionPositions[i].row][solutionPositions[i].col] = 1;
				br.write("OK\n");
				for(int i=0; i<n; ++i){
					for(int j=0; j<n; ++j)
						br.write(""+matrix[i][j]);
					br.write('\n');
				}
				br.close();
			}catch(Exception e){
				e.printStackTrace();
			}
		}
	}
	
	//Method to calculate whether a lizard can be eaten by another or not
	boolean isClashing(int row, int col, Position[] positions){
		boolean clashing = false;
		for(Position pos: positions){
			if(col == pos.col){
				int i=pos.row+1;
				while(i!=row && i<n){
					if(matrix[i][col]==2) 
						break;
					i++;
				}
				if(i==row)
					return true;
			}
			if(row + col == pos.row + pos.col){
				int i=pos.row+1;
				int j=pos.col-1;
				while(i!=row && j!=col && i<n && j>0){
					if(matrix[i][j]==2)
						break;
					i++;
					j--;
				}
				if(i==row && j==col)
					return true;
			}
			if(row - col == pos.row - pos.col){
				int i=pos.row+1;
				int j=pos.col+1;
				while(i!=row && j!=col && i<n && j<n){
					if(matrix[i][j]==2)
						break;
					i++;
					j++;
				}
				if(i==row && j==col)
					return true;
			}
		}
		return clashing;
	}
	
	//The operator applied on the parent to get its children nodes is executed by expandNode()
	Node[] expandNode(Node parent){
		ArrayList<Node> childList = new ArrayList<Node>();
		int currentsubrow = parent.currentsubrow;
		do{
			currentsubrow++;
			if(currentsubrow >= subrowList.length)
				break;
			if(parent.positions == null){
				for(int i=subrowList[currentsubrow].startCol; i<=subrowList[currentsubrow].endCol; ++i)
					childList.add(new Node(new Position(subrowList[currentsubrow].realrow, i), parent.numLizards+1, currentsubrow));
			}
			else{
				boolean[] flags = new boolean[n];
				for(int col=subrowList[currentsubrow].startCol; col<=subrowList[currentsubrow].endCol; ++col){
					flags[col] = isClashing(subrowList[currentsubrow].realrow, col, parent.positions);
				}
				for(int i=subrowList[currentsubrow].startCol; i<=subrowList[currentsubrow].endCol; ++i)
					if(!flags[i])
						childList.add(new Node(parent.positions, new Position(subrowList[currentsubrow].realrow, i), parent.numLizards+1, currentsubrow));
			}
		}while(childList.isEmpty());
		Node[] children = childList.toArray(new Node[childList.size()]);
		return children;
	}
	
	void solveByDFS() throws NoSuchElementException{
		Node currentNode;
		Node[] children;
		Stack<Node> stack = new Stack<Node>();
		Node imaginaryRootNode = new Node();
		stack.push(imaginaryRootNode);
		while(!stack.isEmpty()){
			currentNode = stack.pop();
			if(currentNode.numLizards == p){
				answer = new SolutionState(true, currentNode.positions);
				answer.write();
				System.exit(0);
			}
			children = expandNode(currentNode);
			for(Node child: children)
				stack.push(child);
		}
		answer = new SolutionState(false, null);
		answer.write();
		System.exit(0);
	}
	
	void solveByBFS() throws NoSuchElementException{
		Node currentNode;
		Node[] children;
		Queue<Node> queue = new LinkedList<Node>();
		Node imaginaryRootNode = new Node();
		queue.add(imaginaryRootNode);
		while(!queue.isEmpty()){
			currentNode = queue.remove();
			//currentNode.display();
			if(currentNode.numLizards == p){
				answer = new SolutionState(true, currentNode.positions);
				answer.write();
				System.exit(0);
			}
			children = expandNode(currentNode);
			for(Node child: children)
				queue.add(child);
		}
		answer = new SolutionState(false, null);
		answer.write();
		System.exit(0);
	}
}

//Simulated Annealing is solved by creating an instance of the below class
//Most importantly, the class variables globalMatrix and conflicts represent
//the best state of the system so far
class SAInstance{
	int n;
	int p;
	int[][] globalMatrix;
	Position[] positions;
	int conflicts;
	Random random;
	boolean solved;
	SAInstance(int n, int p, int[][] matrix){
		this.n = n;
		this.p = p;
		positions = new Position[p];
		random = new Random();
		int j, k;
		do{
			globalMatrix = matrix.clone();
			for(int i=0; i<p; ++i){
				do{
					j = random.nextInt(n);
					k = random.nextInt(n);
				}while(globalMatrix[j][k]==2 || globalMatrix[j][k]==1);
				globalMatrix[j][k] = 1;
				positions[i] = new Position(j,k);
			}
			conflicts = computeConflicts(positions, globalMatrix);
		}while(false);

	}
	
	//Randomly pick a queen and move it by random units to generate the neighbor of a given state
	Position[] successor(Position[] positions, int[][] temp){
		Position[] newPos = positions.clone();
		int i;
		i = random.nextInt(p);
		int j = newPos[i].row;
		int k = newPos[i].col;
		do{
			newPos[i].row = (random.nextInt(n));
			newPos[i].col = (random.nextInt(n));
		}while(temp[newPos[i].row][newPos[i].col]==2 || temp[newPos[i].row][newPos[i].col]==1);
		temp[j][k] = 0;
		temp[newPos[i].row][newPos[i].col] = 1;
		return newPos;
	}
	
	//Local search is employed when the Temperature or the energy of the system is very low
	Position[] localSearch(Position[] positions, int[][] temp){
		Position[] newPos = positions.clone();
		int i,c;
		do{
			i = random.nextInt(p);
			c = conflict(positions[i].row, positions[i].col, temp);
		}while(c==0);
		int j = newPos[i].row;
		int k = newPos[i].col;
		do{
			newPos[i].row = (random.nextInt(n));
			newPos[i].col = (random.nextInt(n));
		}while(temp[newPos[i].row][newPos[i].col]==2 || temp[newPos[i].row][newPos[i].col]==1);
		temp[j][k] = 0;
		temp[newPos[i].row][newPos[i].col] = 1;
		return newPos;
	}
	
	//Compute the energy of the board
	int computeConflicts(Position[] positions, int[][] temp){
		int c=0;
		for(int i=0; i<positions.length; ++i)
				c+=conflict(positions[i].row, positions[i].col, temp);
		return c;
	}
	
	//Compute the conflicts for a particular lizard
	int conflict(int row, int col, int[][] mat){
		int x,y;
		int c=0;
		

		//Moving right
		for(x=col+1; x<n; ++x){
			if(mat[row][x]==2)
				break;
			if(mat[row][x]==1){
				c++;
				break;
			}
		}
		
		//Moving left
		for(x=col-1; x>=0; --x){
			if(mat[row][x]==2)
				break;
			if(mat[row][x]==1){
				c++;
				break;
			}
		}

		//Moving down
		for(y=row+1; y<n; ++y){
			if(mat[y][col]==2)
				break;
			if(mat[y][col]==1){
				c++;
				break;
			}
		}

		//Moving up
		for(y=row-1; y>=0; --y){
			if(mat[y][col]==2)
				break;
			if(mat[y][col]==1){
				c++;
				break;
			}
		}
		
		//Moving right lower diagonal
		for(x=col+1, y=row+1; x<n && y<n; ++x, ++y){
			if(mat[y][x] == 2)
				break;
			if(mat[y][x] == 1){
				c++;
				break;
			}
		}

		//Moving left upper diagonal
		for(x=col-1, y=row-1; x>=0 && y>=0; --x, --y){
			if(mat[y][x] == 2)
				break;
			if(mat[y][x] == 1){
				c++;
				break;
			}
		}

		//Moving upper right diagonal
		for(x=col+1, y=row-1; x<n && y>=0; ++x, --y){
			if(mat[y][x] == 2)
				break;
			if(mat[y][x] == 1){
				c++;
				break;
			}
		}

		//Moving lower left diagonal
		for(x = col-1, y = row+1; x>=0 && y<n; --x, ++y){
			if(mat[y][x] == 2)
				break;
			if(mat[y][x] == 1){
				c++;
				break;
			}
		}
		
		return c;
	}
	void display(int[][] a){
		for(int i=0; i<n; ++i){
			for(int j=0; j<n; ++j)
				System.out.print(a[i][j]+" ");
			System.out.println();
		}
	}
	void solveBySA(){
		double t = 1.01;
		double T = (double)1/Math.log(t); 		// Temperature varies logarithmically with t
		double deltaE;
		double prob;
		Position[] newPositions;
		int newConflicts;
		int[][] temp;
		outer:
		while( T > 0.000001){
			for(int i=0; i<100; ++i){
				if(conflicts == 0 || conflicts<=4){
					break outer;
				}
				temp = globalMatrix.clone();
				newPositions = successor(positions, temp);
				newConflicts = computeConflicts(positions, temp);
				if(newConflicts <= conflicts){
					positions = newPositions;
					conflicts = newConflicts;
					globalMatrix = temp;
				}
				else{
					deltaE = newConflicts - conflicts;
					prob = Math.exp(-deltaE/T);
					if(decide(prob)){
						positions = newPositions;
						conflicts = newConflicts;
						globalMatrix = temp;
					}
				}
			}
			t+=0.001;
			T = (double)1/Math.log(t);
		}
		
		while(conflicts>0){
			temp = globalMatrix.clone();
			newPositions = localSearch(positions, temp);
			newConflicts = computeConflicts(positions, temp);
			if(newConflicts < conflicts){
				positions = newPositions;
				conflicts = newConflicts;
				globalMatrix = temp;
			}
		}
		if(conflicts == 0){
			solved = true;
			write();
			System.exit(0);
		}
	}
	
	//Probability function to decide whether or not to take a bad move
	boolean decide(double p){
		double r = Math.random();
		if(r<=p)
			return true;
		return false;
	}
	
	void write(){
		try{
			FileWriter fr = new FileWriter("output.txt");
			BufferedWriter br = new BufferedWriter(fr);
			if(!solved){
				br.write("FAIL\n");
				br.close();
				return;
			}
			br.write("OK\n");
			for(int i=0; i<n; ++i){
				for(int j=0; j<n; ++j)
					br.write(""+globalMatrix[i][j]);
				br.write('\n');
			}
			br.close();
		}catch(Exception e){
			e.printStackTrace();
		}
	}
}
public class Solver {
	public static void main(String args[]){
		try{
			String lines[] = new String[3];
			FileReader fr = new FileReader("input.txt");
			BufferedReader br = new BufferedReader(fr);
			for(int i=0; i<3; ++i)
				lines[i] = br.readLine();
			int n = Integer.parseInt(lines[1]);
			int p = Integer.parseInt(lines[2]);
			String board[] = new String[n];
			for(int i=0; i<n; ++i){
				board[i] = br.readLine();
			}
			br.close();
			int matrix[][] = new int[n][n];
			int trees = 0;
			for(int i=0; i<n; ++i)
				for(int j=0; j<n; ++j)
					if(board[i].charAt(j) == '2'){
						matrix[i][j] = 2;
						trees++;
					}
			if(p>(n+trees)){
				try{
					BufferedWriter bro = new BufferedWriter(new FileWriter("output.txt"));
					bro.write("FAIL\n");
					bro.close();
					return;
				}catch(Exception e){
					e.printStackTrace();
				}
			}
			Timer timer = new Timer();
			if(lines[0].equals("BFS")){
				SearchInstance nursery = new SearchInstance(n, p, matrix);
				TimerTask writeTo = new TimerTask(){
					@Override
					public void run(){
						nursery.answer.write();
						System.exit(0);
					}
				};
				timer.schedule(writeTo, new Date(System.currentTimeMillis()+285*1000));
				nursery.solveByBFS();
			}
			else if(lines[0].equals("DFS")){
				SearchInstance nursery = new SearchInstance(n, p, matrix);
				TimerTask writeTo = new TimerTask(){
					@Override
					public void run(){
						nursery.answer.write();
						System.exit(0);
					}
				};
				timer.schedule(writeTo, new Date(System.currentTimeMillis()+285*1000));
				nursery.solveByDFS();
			}
			else if(lines[0].equals("SA")){
				SAInstance nursery = new SAInstance(n, p, matrix);
				TimerTask writeTo = new TimerTask(){
					@Override
					public void run(){
						nursery.write();
						System.exit(0);
					}
				};
				timer.schedule(writeTo, new Date(System.currentTimeMillis()+285*1000));
				nursery.solveBySA();
			}
		}
		catch(Exception e){
			e.printStackTrace();
		}
	}
}


