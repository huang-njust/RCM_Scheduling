using System;
using System.IO;
using System.Collections;
using Tanis.Collections;

namespace Huangbo.AStarPetri.Test
{
    class MainClass
    {

        #region Public Methods

        [STAThread]

        static void Main(string[] args)
        {
            /*
             * This program is to search a scheduling path from an initial state to a goal state in the reachability graph of a place-timed Petri net for a resource allocation system by using the A* search and its variants.
             * For the details on the implemented algorithms, please refer to our book: Supervisory Control and Scheduling of Resource Allocation Systems. Wiley-IEEE Press. 2020, and our papers.
             * For the details on the version changes (各版本更新说明), please refer to https://static.app.yinxiang.com/embedded-web/profile/#/join?guid=0f885707-2f1a-4ea6-9fab-f2479b6dd6b5&sharedNotebookGuid=&channel=copylink&shardId=s34&ownerId=25641086
             * For bug reports or information, please contact: huangbo@njust.edu.cn (Bo Huang, School of Computer Science and Engineering, Nanjing University of Science and Technology, Nanjing 210094, China)
             */

            Huangbo.AStarPetri.AStar aStar;
            Huangbo.AStarPetri.AStarNode goalNode;
            Huangbo.AStarPetri.AStarNode startNode;

            //string fileName = "ChenFig5_33";  //The prefix of your input Petri net files.         fileName should be "XXXFigx_111_init.txt" or "XXXFigx_111_matrix.txt".   
            string fileName = "ChenFig6_222";  //The prefix of your input files. 
            //string fileName = "Chen2011Big_11122";  //The prefix of your input files. 
            //string fileName = "ChenFig6Extended_121";  //The prefix of your input files.
            //string fileName = "Xiong98_1111";  //The prefix of your input files.


            string[] initialMFile = new string[] { "./" + fileName + "_init.txt" };//A file containing the initial state, goal state, and the time information in activity places. It is a file with 3 lines and |P| columns. 会自动计算获取Petri网的N_P, N_P_R, MAX_TOK_PA
            string[] incidenceMatrixFile = new string[] { "./" + fileName + "_matrix.txt" };//Petri net structure file containing its incidence matrix. It is a file of a |T|x|P| matrix. 我们在程序中会转化成库所x变迁；会获取Petri网的N_T和关联矩阵
  


            int[] hMethods = new int[]  { 0 };//所用启发函数h  //the used heuristic function, for example, if you want to use h=0, you input 0 here and if you want to use h=h_H, you input 7 here.
            //h0 = 0;
            //h1 = max{ei(m)} plus R; max{ei(m)} comes from Xiong98.
            //h4 = -dep(m);       
            //h7 = h_H that is from Chapter 9 of our book; 
            //h710(Pohl)=h+ep2*[1-depth(M)/N]*h, h=h7=h_H, 此时要设置总深度N=totalDepth！  大-小，线性   //未检查，可能有问题
            //    (reversed Pohl)=h+ep2*[depth(M)/N]*h, h=h7=h_H, 此时要设置总深度N=totalDepth！   小-大，线性
            //    (Pohl)=h+ep2*[1-depth(M)/N]^2*h, h=h7=h_H, 此时要设置总深度N=totalDepth！   大-小，2次，凹
            //    (Pohl)=h+ep2*{1-[depth(M)/N]^2}*h, h=h7=h_H, 此时要设置总深度N=totalDepth！   大-小，2次，凸
            //    (Pohl)=h+ep2*{1-0.5*[1-depth(M)/N]}*h, 0<=1-depth(M)/N<0.4;        h=h7=h_H, 此时要设置总深度N=totalDepth！   大-小，线性，分段函数
            //          =h+ep2*{2-3*[1-depth(M)/N]}*h, 0.4<=1-depth(M)/N<0.6;       
            //          =h+ep2*{0.5-0.5*[1-depth(M)/N]}*h, 0.6<=1-depth(M)/N<=1;   
            //h720(IDWA)=h+ep2*(h/h_0)*h, h=h7=h_H,  大-小，线性
            //h721(IDWA)=h+ep2*[1-h/h_0]*h, h=h7=h_H,    小-大，线性
            //h722(IDWA)=h+ep2*[h/h_0]^2*h, h=h7=h_H,  大-小，2次，凹
            //h723(IDWA)=h+ep2*{1-[1-h/h_0]^2}*h, h=h7=h_H, 大-小，2次，凸     
            //h8=\sum{j(p,i)}{(R(p, i)*\sum{U(p, r)}+MRT(p)}+\sum{\delta(S, r)*G(S, r)}/{\sum((M_{P/P_R}^T*MR^3)^{C}} comes from our T-SMC2023. //Note that we assume that \delta(S, r)*G(S, r)=0 since both ours and Luo's have it in their heuristic functions and it is hard to calculate.
            //h9=\sum{j(p,i)}{(R(p, i)+X(p)}+\sum{\delta(S, r)*G(S, r)}/|ER| comes from 2015LuoTASE. //Note that Luo assumes that \delta(S, r)*G(S, r)=0 since it is hard to calculate.
            //h10=\max_{j(p,i)\in J}{(R(p, i)+X(p)} comes from our T-SMC2023.     X denotes the necessary processing time of an available token in $p$ to move from $p$ to its end place. 
            //If h1, h7, h8, h9, or h10 is used to compute h, some parameters of the tested PN is needed in CalculateH().

            int[] openSizes = new int[1] { 0 };
            //openSize: the maximal number of nodes in OPEN. 
            //openSize:0:表示open可为无穷大；大于0：表示进行BF locally,BT globally            
            //openSize=0 denotes unlimited. openSize>0 denotes the A* search will use the BF locally and BT globally as described in Chapter 10 of our book.


            decimal ep =-1;
            //ep: the parameter epsilon used in Chapter 9 of our book.It is for OPEN.
            //ep<0时表示没有ep的情况  ep<0 indicates the A* search does not use the epsilon. 
            //ep=0时，选OPEN中具有相同最小f值marking中有最小h2ndValue的(0比-1好)
            //ep>0时选择范围更大,选OPEN中具有不大于最小f值1+ep倍的marking中有最小h2ndValue的
            //ep>=0 indicates the A* search picks out the node with the minimal h2ndValue for expansion among the nodes having the f-value between f_min and f_min*(1+ep) in OPEN.


            int h2ndMethod = 2;	//h2ndMethod选择所用第二个启发函数，用于对OPEN中的节点进行二次排序  It is used for e-A*; The second hueristic function is for the states in OPEN.
            //1=h;2=-(FMarkingDepth+1);10=h;
            //从小到大排序


            //decimal[] ep2s = new decimal[] { 0m, 0.1m, 0.2m, 0.3m, 0.4m, 0.5m, 0.6m, 0.7m, 0.8m, 0.9m, 1m };            
            decimal[] ep2s = new decimal[] { 0m };
            //ep2 is for dynamic weighted search (h710-h723). ep2 = 0 denotes it is not used. pe2s={0m},0表示无意义，无循环 ；如果需要运行多次不同情况，pe2s={0m, 0.01m, 0.05m, 0.1m}. 


            bool printScreen = true;//是否向屏幕打印每个扩展节点的信息   Whether or not to print each expanded node to your screen.



            foreach (int hMethod in hMethods)
            {
                foreach (int openSize in openSizes)
                {
                    for (int i = 0; i < ep2s.Length; i++ )
                        {
                            decimal ep2=ep2s[i];

                            aStar = new Huangbo.AStarPetri.AStar(initialMFile[0], incidenceMatrixFile[0]);

                            goalNode = new Huangbo.AStarPetri.AStarNode(null, null, 0, 0, 0, AStar.GoalM, AStar.GoalR, 0, 0, 0, 0);//AStarNode(AStarNode parent, AStarNode goalNode, decimal gValue, decimal hValue, decimal fValue, int[] M, decimal[,] R, int tFireFrom, decimal markingDepth, decimal h2ndValue, decimal Delt)
                            startNode = new Huangbo.AStarPetri.AStarNode(null, goalNode, 0, 0, 0, AStar.StartM, AStar.StartR, 0, 0, 0, 0);

                            Console.WriteLine();
                            Console.WriteLine("hMethod={0},fileName={1},fileName={2},running...", hMethod, initialMFile[0], incidenceMatrixFile[0]);

                            DateTime startTime = DateTime.Now;//搜索开始时间  the start time of the search 
                            aStar.FindPath_AStar(fileName, startNode, goalNode, ep, ep2, hMethod, h2ndMethod, openSize, printScreen);
                            DateTime endTime = DateTime.Now;//搜索结束时间 the end time of the search
                            TimeSpan elapsedTime = new TimeSpan(endTime.Ticks - startTime.Ticks);//运行时间 the running time of the search

                            aStar.PrintSolution(i, fileName, hMethod, openSize, h2ndMethod, ep, ep2, elapsedTime);  //向屏幕和文件输出结果	Output results to your screen and a file (result.txt).	第一个参数=0表示以create方式创建和输出文件；否则以append方式输出文件；


                            Console.WriteLine("Total time：{0} seconds, {1} milliseconds   (i.e., hours={2}, minutes={3}, seconds={4}, milliseconds={5})", elapsedTime.Hours * 3600 + elapsedTime.Minutes * 60 + elapsedTime.Seconds, elapsedTime.Milliseconds, elapsedTime.Hours, elapsedTime.Minutes, elapsedTime.Seconds, elapsedTime.Milliseconds);                            

                        }
                }
            }
            
            Console.ReadLine(); //保持输出屏幕不被关闭
        }

        #endregion
    }
}
