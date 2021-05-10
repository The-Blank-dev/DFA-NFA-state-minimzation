/****************
FLAT assignment
Ashwamegh Rathore
19CS30009
****************/
#include <cmath>
#include <fstream>
#include <iostream>
#include <bits/stdc++.h>
#include <string>
using namespace std;

/***********STRUCT/USER DEFINED DATA TYPE  FORMATION*************/
typedef struct bit_array{
	int bit_32[32];
} Bit_Array;

typedef struct _NFA{
	int n,m;
	Bit_Array s;
	Bit_Array F;
	Bit_Array *table;
}NFA;
typedef struct _DFA{
	unsigned int n;
	int m;
	int s;
	Bit_Array *F;
	unsigned int no_F;
	int *table;
}DFA;
void printMat(const DFA D,int *Mat);
/*****************32 BIT TO DECIMAL*******************/
unsigned int decimal(Bit_Array arr){
	unsigned ans,p;
	int i;
	p=1;
	ans=0;
	for(i=0;i<32;i++){
		ans+=p*arr.bit_32[31-i];
		p=p*2;
	}
	return ans;
}
/************DECIMAL TO 32 BIT***************/
Bit_Array bit_converter(unsigned int u){
	Bit_Array ans;
	int i;
	for(i=0;i<32;i++){
		ans.bit_32[31-i]=u%2;
		u=u/2;
	}
	return ans;
}
/***********NFA CONSTRUCTION FORM INPUT FILE****************/
NFA readNFA(ifstream &InputFile){
	NFA N;
	int i,j;
	int p,a,q;
	int x;

	InputFile>>N.n;
	InputFile>>N.m;
	N.table=new Bit_Array [N.n * N.m];

	for(i=0;i<32;i++){
		N.s.bit_32[i]=0;
		N.F.bit_32[i]=0;
	}
	for(i=0;i<N.n;i++){
		for(j=0;j<N.m;j++){
			for(int k=0;k<32;k++){
				(N.table + i * N.m + j)->bit_32[k]=0;
			}
		}
	}

	InputFile>>x;	
	while(x!=-1){
		N.s.bit_32[31-x]=1;
		InputFile>>x;
	}

	InputFile>>x;	
	while(x!=-1){
		N.F.bit_32[31-x]=1;
		InputFile>>x;
	}

	InputFile>>p;	
	while(p!=-1){
		InputFile>>a;
		InputFile>>q;
		//cout<<p<<" "<<a<<" "<<q<<endl;
		(N.table + p * N.m + a)->bit_32[31-q]=1;
		//cout<<(N.table + p * N.m + a)->bit_32[31-q]<<endl;
		InputFile>>p;
	}
	return N;
}
/**************DFA CONSTRUCTION***************/
DFA subsetcons(NFA N){
	DFA D;
	unsigned int i,j,k,q,b,s;

	D.n=(int)pow(2,N.n);
	D.m=N.m;
	D.table=new int[D.m*D.n];
	
	for(i=0;i<D.n;i++){
		for(j=0;j<D.m;j++){
			q=0;
			for(k=0;k<32;k++){
				if((i >> k) & 1){
					b=decimal(*(N.table + k * N.m + j));
					//cout<<b<<endl;
					q=q|b;
				}
			}
			//cout<<q<<" ";
			*(D.table+i*D.m+j)=q;
		}
		//cout<<endl;
	}

	s=0;
	for(k=0;k<32;k++){
		if(N.s.bit_32[31-k]){
			s+=(int)pow(2,k);
		}
	}
	D.s=s;
	D.no_F=0;
	D.F=new Bit_Array[D.n/32+1];
	for(i=0;i<D.n;i++){
		(D.F+i/32)->bit_32[31-(i%32)]=0;
		for(k=0;k<32;k++){
			if(((i >> k) & 1)&& N.F.bit_32[31-k]){
				(D.F+i/32)->bit_32[31-(i%32)]=1;
				break;
			}
		}
		if((D.F+i/32)->bit_32[31-(i%32)])
			D.no_F++;
	}
	
	return D;
}
/****************DFS ALGORITHM****************/
void DFS(int const * const table,int start,int visited[],int alpha,int *l){
	visited[start]=1;
	(*l)++;
	int i;
	for(i=0;i<alpha;i++){
		if(!visited[*(table+start*alpha+i)])
			DFS(table,*(table+start*alpha+i),visited,alpha,l);
	}
}
/***********FIND REACHABLE SETS***********/
int findreachable(DFA D,int visited[]){
	int l=0;
	DFS(D.table,D.s,visited,D.m,&l);	
	return (l);
}
/*************REMOVE UNREACHABLE STATES*************/
DFA rmunreachable(DFA D,int visited[],const int l,ofstream &OutputFile){
	DFA D1;
	D1.n=l;
	D1.m=D.m;
	//int arr[D.n]={-1};
	int *arr=new int[D.n];
	unsigned int arr_rev[l];
	int i,j,k;
	j=0;

	for(i=0;i<D.n;i++){
		if(*(visited+i)){
			*(arr+i)=j;
			arr_rev[j]=i;
			j++;
		}
		else
			*(arr+i)=-1;
	}
	D1.s=*(arr+D.s);
	D1.table=new int[D1.n*D1.m];
	for(i=0;i<D1.n;i++){
		for(j=0;j<D1.m;j++){
			*(D1.table+i*D1.m+j)=*(arr+*(D.table+arr_rev[i]*D.m+j));
		}
	}
	
	
	j=0;
	D1.F=new Bit_Array[D1.n/32+1];
	for(i=0;i<D1.n;i++){
		(D1.F+i/32)->bit_32[31-(i%32)]=0;
		if((D.F+arr_rev[i]/32)->bit_32[31-(arr_rev[i]%32)]){
			(D1.F+i/32)->bit_32[31-(i%32)]=1;
			j++;
		}
	}
	D1.no_F=j;
	
	OutputFile<<endl<<"+++ Reachable states: {";
	for(i=0;i<D1.n-1;i++){
		OutputFile<<arr_rev[i]<<",";
	}
	OutputFile<<arr_rev[i]<<"}"<<endl;
	
	delete []arr;
	return D1;
}
/**********CHECK IF A STATE IS A FINAL STATE OR NOT******/
int is_F(const DFA D,int state){
	if(state>=D.n)
		return 0;
	else{
		if((D.F+state/32)->bit_32[31-(state%32)])
			return 1;
		else 
			return 0;
	}
}
/*************RECURSIVE FUNCTION TO SOLVE MINIMIZATION*********/
void rec(const DFA D,int *Mat){
	int i,j,k,g,h,t;
	int c=0;
	for(i=1;i<D.n;i++){
		for(j=0;j<i;j++){
			if((*(Mat+i*D.n+j))==0){
				for(k=0;k<D.m;k++){
					g=(*(D.table+i*D.m+k));
					h=(*(D.table+j*D.m+k));
					if(h>g){
						t=h;
						h=g;
						g=t;
					}
					if(*(Mat+g*D.n+h)){
						c++;
						*(Mat+i*D.n+j)=1;
						break;
					}
				}
			}
		}
	}
	if(c!=0)
		rec(D,Mat);
}
/**********FINDING EQUIVALENT STATES***********/
void findequiv(const DFA D,int *Mat){
	int i,j;
	for(i=0;i<D.n;i++){
		for(j=0;j<D.n;j++){
			*(Mat+i*D.n+j)=0;
			if(i>j){
				if((is_F(D,i) && !is_F(D,j)) || (!is_F(D,i) && is_F(D,j)) ){
					*(Mat+i*D.n+j)=1;
					//cout<<"init"<<endl;
				}
				//cout<<*(Mat+i*D.n+j)<<" ";
			}
		}
		//cout<<endl;
	}
	//printMat(D,Mat);
	rec(D,Mat);
}
/***********FORM GROUPS***********/
int groups(const DFA D,const int *const Mat,int *G){
	int i,j,k,l;
	for(i=0;i<D.n;i++)
		for(j=0;j<D.n;j++)
			*(G+i*D.n+j)=-1;
	int no=0,f=0;
	*(G+0*D.n+0)=0;
	no++;
	for(i=1;i<D.n;i++){
		f=0;
		for(j=0;j<i;j++){
			if(*(Mat+i*D.n+j)==0){
				k=0;l=0;
				for(k=0;k<no;k++){
					if(*(G+k*D.n+0)==j)
						break;
				}
				for(l=0;l<D.n;l++){
					if(*(G+k*D.n+l)==-1)
						break;
				}
				*(G+k*D.n+l)=i;
				f++;
				break;
			}
		}
		if(!f){
				*(G+no*D.n+0)=i;
				no++;
		}
	}
	return no;
}
/***********FINDS THE EQUIVALENCE CLASS OF A STATE****/
int belongs(const DFA D,const int *const G,const int l,int s){
	int i,j;
	for(i=0;i<l;i++){
		for(j=0;j<D.n;j++){
			if(*(G+i*D.n+j)==s)
				return i;
			if(*(G+i*D.n+j)==-1)
				break;
		}
	}
	return -1;
}
/****************FORM COLLAPSED/MINIMAL DFA*******/
DFA collapse(const DFA D,const int *const G,const int l){
	DFA Dnew;
	Dnew.n=l;
	Dnew.m=D.m;
	Dnew.table=new int[Dnew.n*Dnew.m];
	Dnew.F=new Bit_Array[Dnew.n/32+1];
	int i,j,k,m,t;
	int f=0;
	Dnew.s=belongs(D,G,l,D.s);
	
	for(i=0;i<Dnew.n;i++){
		for(j=0;j<Dnew.m;j++){
			m=*(D.table+(*(G+i*D.n+0))*D.m+j);
			*(Dnew.table+i*Dnew.m+j)=belongs(D,G,l,m);			
		}
	}
	for(i=0;i<Dnew.n;i++){
		(Dnew.F+i/32)->bit_32[31-(i%32)]=0;
	}
	
	for(i=0;i<D.n;i++){
		if((D.F+i/32)->bit_32[31-(i%32)]){
			m=belongs(D,G,l,i);
			(Dnew.F+m/32)->bit_32[31-(m%32)]=1;
		}
	}
	for(i=0;i<Dnew.n;i++){
		if((Dnew.F+i/32)->bit_32[31-(i%32)])
			f++;
	}
	Dnew.no_F=f;
	return Dnew;
}
/*************VARIOUS TESTS********************/
void testNFA(NFA N){
	cout<<N.n<<"\t"<<N.m<<endl;
	for(int i=0;i<32;i++)
		cout<<N.s.bit_32[i]<<" ";
	cout<<endl;
	for(int i=0;i<32;i++)
		cout<<N.F.bit_32[i]<<" ";
	cout<<endl<<endl;
	for(int i=0;i<N.n;i++){
		for(int j=0;j<N.m;j++){
			for(int k=0;k<32;k++){
				cout<<(N.table + i * N.m + j)->bit_32[k]<<" ";
			}
			cout<<endl;
		}
	}
}
void printMat(const DFA D,int *Mat){
	int i,j;
	for(i=1;i<D.n;i++){
		for(j=0;j<i;j++)
			cout<<(*(Mat+i*D.n+j))<<" ";
		cout<<endl;
	}

}
/**********PRINT FUNCTIONS***************/
void printNFA(NFA N,ofstream &OutputFile){
	int i,j,k,t;
	OutputFile<<"+++ Input NFA"<<endl;

	OutputFile<<"\tNumber of states:  "<<N.n<<endl;

	OutputFile<<"\tInput alphabet: {";
	for(i=0;i<N.m-1;i++)
		OutputFile<<i<<",";
	OutputFile<<N.m-1<<"}"<<endl;

	OutputFile<<"\tStart states: {";
	for(i=0;i<32;i++)
		if(N.s.bit_32[31-i]){
			OutputFile<<i;
			j=i;
			break;
		}
	for(i=j+1;i<32;i++)
		if(N.s.bit_32[31-i])
			OutputFile<<","<<i;
	OutputFile<<"}"<<endl;

	OutputFile<<"\tFinal states: {";
	for(i=0;i<32;i++)
		if(N.F.bit_32[31-i]){
			OutputFile<<i;
			j=i;
			break;
		}
	for(i=j+1;i<32;i++)
		if(N.F.bit_32[31-i])
			OutputFile<<","<<i;
	OutputFile<<"}"<<endl;
	OutputFile<<"\tTransition function"<<endl;
	for(i=0;i<N.n;i++){
		for(j=0;j<N.m;j++){
			OutputFile<<"\t\tDelta("<<i<<","<<j<<") = {";
			for(k=0;k<32;k++)
				if((N.table + i * N.m + j)->bit_32[31-k]){
					OutputFile<<k;
					t=k;
					break;
				}
			for(k=t+1;k<32;k++)
				if((N.table + i * N.m + j)->bit_32[31-k])
					OutputFile<<","<<k;
			OutputFile<<"}"<<endl;
		}
	}
}
void printDFA(DFA D,ofstream &OutputFile){
	int i,j,k;
	
	OutputFile<<"\tNumber of states: "<<D.n<<endl;
	OutputFile<<"\tInput alphabet: {";
	for(i=0;i<D.m-1;i++)
		OutputFile<<i<<",";
	OutputFile<<D.m-1<<"}"<<endl;
	OutputFile<<"\tStart state: "<<D.s<<endl;
	if(D.n>64){
		OutputFile<<"\t"<<D.no_F<<" final states"<<endl;
	}
	else{
		OutputFile<<"\tFinal states: {";
		for(i=0;i<D.n;i++){
			if((D.F+i/32)->bit_32[31-(i%32)]){
				OutputFile<<i;
				j=i;
				break;
			}
		}
		for(i=j+1;i<D.n;i++){
			if((D.F+i/32)->bit_32[31-(i%32)]){
				OutputFile<<","<<i;
			}
		}
		OutputFile<<"}"<<endl;
	}
	OutputFile<<"\tTransition function:";
	if(D.n>64){
		OutputFile<<" Skipped"<<endl;
	}
	else{
		OutputFile<<endl;
		OutputFile<<"\ta\\p|";
		for(i=0;i<D.n;i++)
			OutputFile<<"\t"<<i;
		OutputFile<<endl;

		OutputFile<<"\t---+---";
		for(i=0;i<D.n;i++)
			OutputFile<<"----";
		OutputFile<<endl;

		for(j=0;j<D.m;j++){
			OutputFile<<"\t "<<j<<" |";
			for(i=0;i<D.n;i++){
				OutputFile<<"\t"<<*(D.table+i*D.m+j);
			}
			OutputFile<<endl;
		}
	}
}
void printG(const DFA D,const int * const G,ofstream &OutputFile){
	OutputFile<<endl<<"+++ Equivalent states"<<endl;
	int i,j;
	//int c=0;
	for(i=0;i<D.n;i++){
		if(*(G+i*D.n+0)==-1)
			break;
		else{
			OutputFile<<"\tGroup  "<<i<<" : {"<<(*(G+i*D.n+0));
			for(j=1;j<D.n;j++){
				if(*(G+i*D.n+j)==-1)
					break;
				else{
					OutputFile<<","<<(*(G+i*D.n+j));
				}
			}
			OutputFile<<"}"<<endl;
		}
	}
}
/*******MAIN()*****************/
int  main(){
	int i;
	time_t start, end; 
	double time_taken;
	 
	string filepath="input.txt";
	cout<<"Enter the filename/filepath:"<<endl;
	getline(cin,filepath);
	cout<<"NOTE: EXECUTION MAY TAKE UPTO 2 MINUTES"<<endl;
	time(&start);
	ifstream ipFile(filepath);
	NFA N=readNFA(ipFile);
	time(&end); 
	time_taken = double(end - start); 
	cout<<"Finished NFA construction at: " << fixed<< time_taken << setprecision(5)<< endl;
	
	ipFile.close();
	//testNFA(N);

	DFA D=subsetcons(N);
	time(&end); 
	time_taken = double(end - start); 
	cout<<"Finished DFA construction at: "<< fixed<< time_taken << setprecision(5)<<endl;

	int *visited=new int[D.n];
	for(i=0;i<D.n;i++)
		*(visited+i)=0;

	int l=findreachable(D,visited);
	
	ofstream opFile("output.txt");
	printNFA(N,opFile);
	opFile<<endl<<"+++ Converted DFA"<<endl;
	printDFA(D,opFile);
	
	DFA D_red=rmunreachable(D,visited,l,opFile);
	opFile<<endl<<"+++ Reduced DFA after removing unreachable states"<<endl;
	printDFA(D_red,opFile);
	time(&end); 
	time_taken = double(end - start); 
	cout<<"Finished reduced DFA construction at: "<< fixed<< time_taken << setprecision(5)<<endl;
	int *Mat=new int[D_red.n*D_red.n];
	findequiv(D_red,Mat);
	//printMat(D_red,Mat);
	int *G=new int[D_red.n*D_red.n];
	int lg=groups(D_red,Mat,G);
	//cout<<lg<<endl;
	printG(D_red,G,opFile);
	DFA D_col=collapse(D_red,G,lg);
	opFile<<endl<<"+++ Reduced DFA after collapsing equivalent states"<<endl;
	printDFA(D_col,opFile);
	time(&end); 
	time_taken = double(end - start); 
	cout<<"Finished collapsed DFA construction at: "<< fixed<< time_taken << setprecision(5)<<endl;
	//cout<<D_col.n<<" "<<D_col.m<<" "<<D_col.s<<" "<<D_col.no_F<<endl;
	opFile.close();

	delete[] visited;
	delete[] G;
	delete[] Mat;
	return 0;
}