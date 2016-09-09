//Fahad Hassan
//UID: 112323967
//ID: Fha423
//Project 3 Plagiarism Detection and Document Retrieval using Locality Sensitive Hashing

package solutions;
import java.util.*;
import java.io.*;

public class LSH {
	int k; //size of shingles
 	int nShingles; // total number of unique shingles in database
 	int nHash; // number of hash functions
	int nDocs; // number of documents in database
	int[] a, b; // two integer arrays of size nHash
	int rows, bands, lenBuckets, seed; double t; //LSH parameters
	int[][] signatureMatrix; // matrix of size nHash x nDocs
	boolean[][] shingleMatrix; // matrix of size nShingles x nDocs
	int[][][] arrayBuckets; // 3d tensor of size bands x lenBuckets x 100
	String databaseFilename;
	// arraylist which stores all the documents
	ArrayList<String> docs = new ArrayList<String>();
	Map<String, Integer> shingles = new HashMap<String, Integer>();
	//Dictionary of where each shingle is mapped to a unique integer
	ArrayList<String> shingleList = new ArrayList<String>();
	

	public LSH(String databaseFilename, int k, int seed, int nHash,
		int lenBuckets, int bands, int rows, double t){
		this.databaseFilename = databaseFilename;
		this.k = k; this.seed = seed; this.nHash = nHash;
		this.lenBuckets = lenBuckets; this.bands = bands;
		this.rows = rows;
		this.t = t;
		this.nShingles = 0;
		this.nDocs = 0;
		signatureMatrix = new int[nHash][nDocs];
		arrayBuckets = new int[bands][lenBuckets][100];

		processHashCodes();
	}
	public int computeUniqueShingles(){
		this.processDocs();
		int count = 0;
		for (String s : docs){
			for (int i = 0; i <= s.length() - k; i++) {
				String shingle = s.substring(i, i+k);
				if(shingles.get(shingle) == null){
					shingles.put(shingle,count);
					shingleList.add(shingle);
					count++;
				}
			}
		}
		this.nDocs = docs.size();
		this.nShingles = count;
		return count;
	}

	public boolean[][] computeShingleMatrix(){
		boolean[][] shingleMatrix = new boolean[nShingles][nDocs];
		for(int row = 0; row < nShingles; row++){
			for(int col =0; col < nDocs; col++){
				if(docs.get(col).contains(shingleList.get(row))) shingleMatrix[row][col] = true;
			}
		}
		this.shingleMatrix = shingleMatrix;
		return shingleMatrix;
	}

	public int[][] shingleMatrixToSignatureMatrix(){
		int[][] signatureMatrix = new int[nHash][nDocs];
		//Initalizes each element to a large number.
		for(int i = 0; i < nHash; i++){
			for(int j = 0; j < nDocs; j++){
				signatureMatrix[i][j] = Integer.MAX_VALUE;
			}
		}
		//Computes the signatures of the shingleMatrix. Look at slide examples.
		for(int row = 0; row < nShingles; row++){
			for(int col = 0; col < nDocs; col++){
				if (shingleMatrix[row][col] == true){
					for (int i = 0; i < nHash; i++){
						int h = (a[i]*row+b[i]) % nShingles;
						if(h < signatureMatrix[i][col]) {
							signatureMatrix[i][col] = h;
						}
					}
				}
			}
		}
		this.signatureMatrix = signatureMatrix;
		return signatureMatrix;
	}

	public int[][][] doLSH(){
		int[][] sums;
		int docSum, docBucket;
		boolean added = false;
		
		sums = doSums();

		for(int b = 0; b < bands; b++){
			for(int j = 0; j < lenBuckets; j++){
				for(int k = 0; k < 100; k++){
					arrayBuckets[b][j][k] = -1;
				}
			}
		}
		//So basically, lenBuckets is the number of buckets per band and within each
		//bucket it is size 100. So this can be read as
		//for each band, for each doc, hash that doc into a bucket using its sig matrix sum mod lenbuckets
		//When hashed to the bucket just place it to the first available free space that is what the inner most
		//loop is for

		//If you remember sig matrix sum calculates all the signautres for document d in band b
		//that is where doSums() comes from
		for(int b = 0; b < bands; b++){
			for(int doc = 0; doc < nDocs; doc++){
				docSum = sums[b][doc];
				docBucket = docSum % lenBuckets;
				for(int k = 0; k < 100; k++){
					if(arrayBuckets[b][docBucket][k] == -1 && !added){
						arrayBuckets[b][docBucket][k] = doc;
						added = true;
					}
				}
				added = false;
			}
		}


		return arrayBuckets;
	}
	public int nearestNeighbor(int d){
		int[] candidates = new int[nDocs];
		int[][] sums = doSums();
		int dSum, dBucket, docSum, docBucket;
		double curr = 0, nn = 0;
		int neighborindex = -1;
		//Finds all candidates corresponding to the input doc d
		//Candidates are based on if d and d' hash to the same bucket
		for(int b = 0; b < bands; b++){
			for(int doc = 0; doc < nDocs; doc++){
				if(doc != d){
					dSum = sums[b][d];
					docSum = sums[b][doc];
					dBucket = dSum % lenBuckets;
					docBucket = docSum % lenBuckets;
					if(dBucket == docBucket) candidates[doc]++;
				}
			}
		}
		//Computes doc with highest jaccard similarity amongst the candidats
		for(int i = 0; i < nDocs; i++){
			if(i != d && candidates[i] > 0){
				curr = computeJC(i,d);
				if(curr > nn){
					nn = curr;
					if(nn > t)
						neighborindex = i;
				}
			}
		}

		return neighborindex;
	}
	public double computeJC(int i, int d){
		double intersect = 0.0;
		double union = 0.0;

		for(int row = 0; row < nShingles; row++){
			if(shingleMatrix[row][i] && shingleMatrix[row][d])
				intersect++;
			if(shingleMatrix[row][i] || shingleMatrix[row][d])
				union++;
		}
		if(union == 0) return 0;
		else
			return intersect/union;
	}
	//Computes the sum of all the signatures hashes for a document in a given band.
	public int[][] doSums(){
		int bandMatrix[][][] = new int[bands][rows][nDocs];
		int sums[][] = new int[bands][nDocs];
		int i = 0;
		for(int b = 0; b < bands; b++){
			for(int row = 0; row < rows; row++){
				bandMatrix[b][row] = signatureMatrix[i];
				i++;
			}
		}

		for(int b = 0; b < bands; b++){
			for(int row = 0; row < rows; row++){
				for(int s = 0; s < nDocs; s++){
					sums[b][s] += bandMatrix[b][row][s];
				}
			}
		}
		return sums;
	}

	public void processHashCodes(){
		Random generator = new Random(this.seed);
		this.a = new int[nHash];
		this.b = new int[nHash];
		for(int i=0;i < nHash;i++){
			this.a[i]=generator.nextInt(1000)+1;
			this.b[i]=generator.nextInt(1000)+1;
		}
	}

	public void processDocs(){
		try (BufferedReader br = new BufferedReader(new FileReader(databaseFilename))) {
			String line;
			while ((line = br.readLine()) != null) {
				this.docs.add(line);
			}
			br.close();
		}
		catch(Exception e){
			System.out.println("Could not read file");
		}
		for (int i =0; i < docs.size(); i++){
			docs.set(i,docs.get(i).toLowerCase());
			docs.set(i,docs.get(i).replaceAll("\\s+",""));
		}
	}

	////////////Methods for testing///////////////////
	public void matrixToString(boolean[][] matrix){
		for(int row = 0; row < nShingles; row++){
			System.out.print(shingleList.get(row)+":");
			for(int col = 0; col < nDocs; col++){
				System.out.print(matrix[row][col]+" ");
			}
			System.out.println();
		}
	}
	public void matrixToString(int[][] matrix){
		for(int row = 0; row < nHash; row++){
			System.out.print("H"+row+": ");
			for(int col = 0; col < nDocs; col++){
				System.out.print(matrix[row][col]+" ");
			}
			System.out.println();
		}
	}
	public void matrixToString(int[][][] matrix){

		for(int b = 0; b < bands; b++){
			System.out.print("band"+b+": ");
			for(int j = 0; j < lenBuckets; j++){
				System.out.print("bucket"+j+":");
				for(int k = 0; k < 100 ; k++){
					System.out.print(matrix[b][j][k] +" ");
				}
				
			}
			System.out.println();
		}
	}

}
