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
             * This program is to search a scheduling path from an initial state to a given goal state of a place-timed Petri net of a resource allocation system by using A* search and its variants.
             * For the details of the algorithm, please refer to our book: Bo Huang, MengChu Zhou, Supervisory Control and Scheduling of Resource Allocation Systems. Wiley-IEEE Press. 2020.
             * For bug reports or additional information, please contact: huangbo@njust.edu.cn
             * March. 15, 2020
            */

            Huangbo.AStarPetri.AStar astar;
            Huangbo.AStarPetri.AStarNode GoalNode;
            Huangbo.AStarPetri.AStarNode StartNode;

            string filename = "ChenFig6222";  //The prefix of your input files.         The paper Huang2020 uses Huang2012Fig1Revised and ChenFig6111-ChenFig6444.   
            string[] initfile = new string[] { "./" + filename + "_init.txt" };
            string[] matrixfile = new string[] { "./" + filename + "_matrix.txt" };
  


            int[] hmethods = new int[]  { 7 };//所用启发函数h  //the used heuristic function, for example, if you want to use h=0, you input 2 here and if you want to use h=h_H, you input 7 here.
            //h1=max{ei(m)} plus R; max{ei(m)} comes from Xiong98.
            //h2=0;
            //h4=-dep(m);
            //h7 = h_H comes from Chapter 9 of our book; 
            //h9=hs+max{ei(m)}+he in which max{ei(m)} comes from Xiong98, hs denotes the necessary time before the resource is used, and he denotes the necessary time after the resource is used.
            //Note that before h1, h7, and h9 are used, some parameters of the tested Petri net should be given in Calculate() in AStar.cs. 
            //if h7 is used, the number of resource places and RWT of the tested Petri net should also be given in FindPath() in AStar.cs.

            int[] opensizes = new int[1] { 0 };//opensize:0:表示open可为无穷大；大于0：表示进行BF locally,BT globally
            //opensize: the maximal number of nodes in OPEN. 
            //opensize=0 denotes unlimited. opensize>0 denotes the A* search will use the BF locally and BT globally as described in Chapter 10 of our book.


            int hFmethod = 2;	//所用第二个启发函数，用于对OPEN中的节点进行二次排序  The second hueristic function used for the nodes in OPEN
            //1=h;2=-(FMarkingDepth+1);10=h;
            //从小到大排序

            double ep =-1;
            //ep: the parameter epsilon used in Chapter 9 in our book.
            //ep<0时表示没有ep的情况  ep<0 indicates the A* search does not use the epsilon. 
            //ep=0时，选OPEN中具有相同最小f值marking中有最小hFCost的(0比-1好)
            //ep>0时选择范围更大,选OPEN中具有不大于最小f值1+ep倍的marking中有最小hFCost的
            //ep>=0 indicates the A* search picks out the node with the minimal hFCost value for expansion among the nodes having the f-value between f_min and f_min*(1+ep) in OPEN.


            double[] ep2s = new double[1] { 0 };//0表示无意义，无循环 pe2s={0}

            bool printScreen = true;//是否向屏幕打印每个扩展节点的信息   Whether or not to print each expanded node to your screen.



            foreach (int hmethod in hmethods)
            {
                foreach (int opensize in opensizes)
                {
                    foreach (double ep2 in ep2s)
                    {
                        astar = new Huangbo.AStarPetri.AStar(initfile[0], matrixfile[0]);
                        GoalNode = new Huangbo.AStarPetri.AStarNode(null, null, 0, 0, 0, AStar.GoalM, AStar.GoalMr, 0, 0, 0, 0);
                        StartNode = new Huangbo.AStarPetri.AStarNode(null, GoalNode, 0, 0, 0, AStar.StartM, AStar.StartMr, 0, 0, 0, 0);

                        Console.WriteLine();
                        Console.WriteLine("hmethod={0},filename={1},filename={2},running...", hmethod, initfile[0], matrixfile[0]);

                        DateTime startTime = DateTime.Now;//搜索开始时间  the start time of the search 
                        astar.FindPath(StartNode, GoalNode, ep, ep2, hmethod, hFmethod, opensize, printScreen);
                        DateTime endTime = DateTime.Now;//搜索结束时间 the end time of the search
                        TimeSpan elapsedTime = new TimeSpan(endTime.Ticks - startTime.Ticks);//运行时间 the running time of the search

                        astar.PrintSolution();  //向屏幕和文件输出结果	Output results to your screen and a file (result.txt).	

                        
                        //astar.PrintNumberOfOpenNodes(); //用于向屏幕输出open节点数  //output the number of nodes in OPEN to your screen. 
                        

                        Console.WriteLine("Search time：hours={0}, minutes={1}, seconds={2}, milliseconds={3}", elapsedTime.Hours, elapsedTime.Minutes, elapsedTime.Seconds, elapsedTime.Milliseconds);
                        
                    }
                }
            }
            
            Console.ReadLine(); //保持输出屏幕不被关闭
        }

        #endregion
    }
}