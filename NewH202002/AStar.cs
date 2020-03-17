using System;
using System.IO;
using System.Collections;
using Tanis.Collections;

namespace Huangbo.AStarPetri
{

    /// <summary>
    /// Base class for pathfinding nodes, it holds no actual information about the map. 
    /// An inherited class must be constructed from this class and all virtual methods must be 
    /// implemented. Note, that calling base() in the overridden methods is not needed.
    /// </summary>
 
    public class AStarNode : IComparable //A state node in the reachability graph of a Petri net
    {
        #region Properties

        public AStarNode Parent//parent node
        {
            set
            {
                FParent = value;
            }
            get
            {
                return FParent;
            }
        }
        private AStarNode FParent;

        public AStarNode GoalNode //goal node
        {
            set
            {
                FGoalNode = value;
            }
            get
            {
                return FGoalNode;
            }
        }
        private AStarNode FGoalNode;

        public double gValue //g value of a node (The accumulative cost of the path until now.)
        {
            set
            {
                FgValue = value;
            }
            get
            {
                return FgValue;
            }
        }
        private double FgValue;

        public double hValue //h value of a node (The estimated minmal cost to the goal from here.)
        {//h
            set
            {
                FhValue = value;
            }
            get
            {
                return FhValue;
            }
        }
        private double FhValue;

        public double fValue //f value of a node(f=g+h, representing an estimated of the lowest cost from the initial node to the goal along a path through the current node)
        {//f
            set
            {
                FfValue = value;
            }
            get
            {
                return FfValue;
            }
        }
        private double FfValue;

        public int[] M //the marking of node in the reachability graph
        {
            get
            {
                return FM;
            }
        }
        private int[] FM;

        public double[,] R //the token remaining time matrix of a place-timed Petri net
        {
            get
            {
                return FR;
            }
        }
        private double[,] FR;

        public int TFireFrom //the transition whose firing generates the node
        {
            get
            {
                return FTFireFrom;
            }
            set
            {
                FTFireFrom = value;
            }
        }
        private int FTFireFrom;

        public int[] EnabledTransitions //the set of transitions that are enabled at the node
        {
            get
            {
                return FEnabledTransitions;
            }
            set
            {
                Array.Copy(value, FEnabledTransitions, value.Length);
            }
        }
        private int[] FEnabledTransitions;

        public int MarkingDepth //the depth of the node, i.e., the number of transition firings from the initial node to the curren node
        {
            get
            {
                return FMarkingDepth;
            }
            set
            {
                FMarkingDepth = value;
            }
        }
        private int FMarkingDepth;

        public double hFCost  //the second h function maybe used to nodes in OPEN
        {
            set
            {
                FhFCost = value;
            }
            get
            {
                return FhFCost;
            }
        }
        private double FhFCost;

        public double Delt//从父标识到某变迁实施得到本标识所用时间 
        { //Delt denotes the time needed by a parent node to become enabled and generate the current node. 
            set
            {
                FDelt = value;
            }
            get
            {
                return FDelt;
            }
        }
        private double FDelt;

        private double delt = 0;//变迁变为可实施所需时间

        // 通过变迁的发射放入输出库所中的托肯必须等待一定时间后才可利用，并且该时间等于该库所的操作时间
        // M(k)- 和 Mr(k)- 分别表示：变迁发射前，那刻 "系统的标识" 和 "剩余处理时间矩阵"
        // M(k)+ 和 Mr(k)+ 分别表示：变迁发射后，输入托肯已移走但输出托肯还未加入时 "系统的标识" 和 "剩余处理时间矩阵"
        // M(k)- and Mr(k)- denote the marking and the token remaining time matrix before a transition fires, respectively.
        // M(k)+ denotes the marking after tokens are removed from the preplaces of a fired transition and before tokens are added into the postplace of the transition. 
        // Mr(k)+ denotes the token remaining time matrix after the transition fires.
        private int[] MF = new int[AStar.np];//M(k)-
        private int[] MZ = new int[AStar.np];//M(k)+
        private double[,] MrF = new double[AStar.np, AStar.MAX_TOK_PA];//Mr(k)- 
        public double[,] MrZ = new double[AStar.np, AStar.MAX_TOK_PA];//Mr(k)+	 

        #endregion

        #region Constructors
        //AStarNode(父节点, 目标节点, g值, h值, f值, 节点的标志, 该标识下所有库所的托肯剩余时间矩阵, 产生本标识所实施的变迁, 标识的深度,第二个h值，从父标识到变迁实施得到本标识所用时间)
        public AStarNode(AStarNode AParent, AStarNode AGoalNode, double AgValue, double AhValue, double AfValue, int[] AM, double[,] AMr, int ATFireFrom, int AMarkingDepth, double AhFCost, double ADelt)
        {
            FParent = AParent;
            FGoalNode = AGoalNode;
            FgValue = AgValue;
            FhValue = AhValue;
            FfValue = AfValue;
            FM = new int[AStar.np];
            Array.Copy(AM, FM, AM.Length);
            FR = new double[AStar.np,AStar.MAX_TOK_PA];
            Array.Copy(AMr, FR, AMr.Length);
            FTFireFrom = ATFireFrom;
            FEnabledTransitions = new int[AStar.nt];
            FMarkingDepth = AMarkingDepth;
            FhFCost = AhFCost;
            FDelt = ADelt;
        }
        #endregion
        #region Public Methods

        public bool IsGoal()//判断本节点的M和Mr(R)是否与GoalNode一致 //zzx
        {//Decide whether or not this node is the same as the goal node in terms of M and Mr(R). 
            if (IsSameStatePlusMr(FGoalNode) == false)//判断M和Mr(R)是否相等
                return false;
            return true;
        }

        public virtual bool IsSameState(AStarNode ANode)//判断某节点的标识M是否和本节点一致 //只判断M
        {//Decide whether or not this node is the same as the goal node only in terms of M.
            if (ANode == null)
                return false;
            if (FM.Length != ANode.FM.Length)
                return false;
            for (int i = 0; i < FM.Length; ++i)
                if (FM[i] != ANode.FM[i])
                    return false;
            return true;
        }

        public virtual bool IsSameStatePlusMr(AStarNode ANode)//判断ANode节点的M和Mr是否和本节点一致//判断M和Mr
        {//Decide whether or not this node is the same as the goal node in terms of M and Mr(R).
            if (ANode == null)
                return false;
            if (FM.Length != ANode.FM.Length)
                return false;
            for (int i = 0; i < FM.Length; ++i)
                if (FM[i] != ANode.FM[i])
                    return false;
            for (int i = 0; i < FR.GetLength(0); ++i)//zzx/////////////
                for (int j = 0; j < FR.GetLength(1); ++j)
                {
                    if (FR[i, j] != ANode.FR[i, j])
                        return false;
                }
            return true;
        }

        public virtual double Calculate(int method, double ep2, double hValueStartNode)//Calculates the h value of a node, i.e., the estimated minimal cost of the path from the node to the goal.
        //h1=max{ei(m)} plus R; max{ei(m)} comes from Xiong98.
        //h2=0;
        //h4=-dep(m);       
        //h7 = h_H that is from Chapter 9 of our book;
        //h9=hs+max{ei(m)}+he in which max{ei(m)} comes from Xiong98, hs denotes the necessary time before the resource is used, and he denotes the necessary time after the resource is used.
        {
            if (method == 1) //h1=max{ei(m)} plus R; max{ei(m)} comes from Xiong98.
            {
                /*
                 //===================================== start of New4x3 =====================================
                 const int ResNum = 3; //资源库所数量 the number of resource places
                 int[] ResourceTime = new int[ResNum];//每个资源库所的所有标识的剩余处理时间
                 for (int i = 0; i < ResourceTime.Length; ++i)
                 {
                     ResourceTime[i] = 0;
                 }

                 int[,] WOT =
                 {
                     {5,4,4},{0,4,4},{0,4,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                     {2,2,5},{2,0,5},{2,0,5},{2,0,0},{2,0,0},{0,0,0},{0,0,0},
                     {2,5,5},{2,5,0},{2,5,0},{0,5,0},{0,5,0},{0,0,0},{0,0,0},
                     {2,4,2},{2,4,0},{2,4,0},{2,0,0},{2,0,0},{0,0,0},{0,0,0},
                     {0,0,0},{0,0,0},{0,0,0}
                 };

                 //加Mr
                 for (int n = 0; n < AStar.np; ++n)
                    for (int m = 0; m < AStar.MAX_TOK_PA; ++m)
                    {
                     if (MrF[n,m] != 0)
                     {
                         if (n == 1 || n == 12 || n == 17 || n == 26)
                             ResourceTime[0] += (int)MrF[n,m];
                         else if (n == 3 || n == 8 || n == 19 || n == 24)
                             ResourceTime[1] += (int)MrF[n,m];
                         else if (n == 5 || n == 10 || n == 15 || n == 22)
                             ResourceTime[2] +=  (int)MrF[n,m];
                     }
                 }
                //===================================== end of New4x3 =====================================

                */

                //===================================== start of ChenFig5 =====================================
                const int ResNum = 6; //资源库所数量 the number of resource places

               double [] ResourceTime = new double[ResNum];
                for (int i = 0; i < ResourceTime.Length; ++i)                
                    ResourceTime[i] = 0;
                

                int[,] WOT =
                {
                  {0,0,3,0,7,5 }, {0,0,3,0,4,5 }, {0,0,3,0,4,5 }, {0,0,3,0,4,5 }, {0,0,3,0,0,5 }, {0,0,0,0,0,5 }, {0,0,0,0,0,0 },
                  {0,3,0,4,9,2 }, {0,3,0,4,9,0 }, {0,3,0,0,9,0 }, {0,3,0,0,5,0 }, {0,0,0,0,5,0 }, {0,0,0,0,0,0 }, {0,0,0,0,0,0 },
                  {0,0,0,0,0,0},  {0,0,0,0,0,0},  {0,0,0,0,0,0},  {0,0,0,0,0,0},  {0,0,0,0,0,0},  {0,0,0,0,0,0},  {0,0,0,0,0,0}

                 };

                //加Mr
                for (int n = 0; n < AStar.np; ++n)
                    for (int m = 0; m < AStar.MAX_TOK_PA; ++m)
                    {
                        if (MrF[n, m] != 0)
                        {
                            if (n == 3)//111这里3和9换了位置
                                ResourceTime[0] += (double)MrF[n, m]; //如果resource unit>1,用int是否合适？
                            else if (n == 11 || n == 2)
                                ResourceTime[1] += (double)MrF[n, m];//111 将int改为double
                            else if (n == 1 || n == 4 || n == 10 || n == 12)
                                ResourceTime[4] += (double)MrF[n, m];
                            else if (n == 6 || n == 8)
                                ResourceTime[5] += (double)MrF[n, m];
                            else if (n == 9)//111这里3和9换了位置
                                ResourceTime[3] += (double)MrF[n, m];
                            else if (n == 5)
                                ResourceTime[2] += (double)MrF[n, m];
                        }
                    }
                //===================================== end of ChenFig5 =====================================





                /*            
              
                      //===================================== start of ChenFig6 =====================================
                      const int ResNum = 7; //资源库所数量 the number of resource places
                      double [] ResourceTime = new double [ResNum];
                      for (int i = 0; i < ResourceTime.Length; ++i)
                      {
                          ResourceTime[i] = 0;
                      }

                      double  [,] WRT =
                      {
                              {0,7,0,0,2,0,0},{0,5,0,0,2,0,0},{0,5,0,0,0,0,0},{0,0,0,0,0,0,0},{3,3,4,0,0,0,0},{0,3,4,0,0,0,0},
                              {0,6,4,0,1,0,0},{0,0,4,0,1,0,0},{0,0,4,0,0,0,0},{0,0,0,0,0,0,0},{0,3,4,0,0,0,2},{0,0,4,0,0,0,2},
                              {0,0,4,0,0,0,0},{2,4,6,0,0,3,1.5},{2,4,0,0,0,3,1.5},{2,4,0,0,0,3,0},{2,0,0,0,0,3,0},{2,0,0,0,0,0,0},
                              {0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},
                              {0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0}
                      };

                     //加Mr
                     /*  for (int n = 0; n < AStar.np; ++n)
                           for (int m = 0; m < AStar.MAX_TOK_PA; ++m)
                           {
                               if (MrF[n, m] != 0)
                               {
                                   if (n == 5)
                                       ResourceTime[0] += (double)MrF[n, m];
                                   else if (n == 2 || n == 8)
                                       ResourceTime[1] += (double)MrF[n, m];
                                   else if (n == 10 || n == 17)
                                       ResourceTime[2] += (double)MrF[n, m];
                                   else if (n == 12 || n == 15)
                                       ResourceTime[3] += (double)MrF[n, m];
                                   else if (n == 5 || n == 18)
                                       ResourceTime[4] += (double)MrF[n, m];
                                   else if (n == 1 || n == 3 || n == 7 || n == 11 || n == 16)
                                       ResourceTime[5] += (double)MrF[n, m];
                                   else if (n == 9 || n == 14)
                                       ResourceTime[6] += (double)MrF[n, m];
                               }
                           }*/

                //===================================== end of ChenFig6 =====================================


                /*
                  //===================================== start of 1112 =====================================
                  const int ResNum = 2; //资源库所数量 the number of resource places
                  double[] ResourceTime = new double[ResNum];
                  for (int i = 0; i < ResourceTime.Length; ++i)
                  {
                      ResourceTime[i] = 0;
                  }

                  double[,] WRT = 
                  {
                          {1.5,2},{0,2},{0,0},{0,0},{2,1},
                          {2,0},{0,0},{0,0},{0,0},{0,0},
                  };

                  //加Mr
                /*  for (int n = 0; n < AStar.np; ++n)
                      for (int m = 0; m < AStar.MAX_TOK_PA; ++m)
                      {
                          if (MrF[n, m] != 0)
                          {
                              if (n == 1||n == 6)
                                  ResourceTime[0] += (double)MrF[n, m];
                              else if (n == 2 || n == 5 )
                                  ResourceTime[1] += (double)MrF[n, m];                        
                          }
                      }
                 //===================================== end of 1112 =====================================
             */


                /*
                 //===================================== start of xiong98 =====================================
                 const int ResNum = 3; //资源库所数量 the number of resource places
                 double[] ResourceTime = new double[ResNum];
                 for (int i = 0; i < ResourceTime.Length; ++i)
                 {
                     ResourceTime[i] = 0;
                 }

                  double[,] WRT =
                 {
                         {2,3,4},{0,3,4},{0,3,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                         {2,2,4},{2,2,0},{2,2,0},{0,2,0},{0,2,0},{0,0,0},{0,0,0},
                         {3,3,5},{0,3,5},{0,3,5},{0,3,0},{0,3,0},{0,0,0},{0,0,0},
                         {3,3,4},{3,0,4},{3,0,4},{3,0,0},{3,0,0},{0,0,0},{0,0,0},
                         {0,0,0},{0,0,0},{0,0,0}
                     };

             /*     double[,] WRT =
                 {
                         {2,1.5,4},{0,1.5,4},{0,1.5,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                         {2,1,4},{2,1,0},{2,1,0},{0,1,0},{0,1,0},{0,0,0},{0,0,0},
                         {3,1.5,5},{0,1.5,5},{0,1.5,5},{0,1.5,0},{0,1.5,0},{0,0,0},{0,0,0},
                         {3,1.5,4},{3,0,4},{3,0,4},{3,0,0},{3,0,0},{0,0,0},{0,0,0},
                         {0,0,0},{0,0,0},{0,0,0}
                     };*/

                //加Mr
                /* for (int n = 0; n < AStar.np; ++n)
                       for (int m = 0; m < AStar.MAX_TOK_PA; ++m)
                       {
                       if (MrF[n,m] != 0)
                       {
                           if (n == 1 || n == 10 || n == 15 || n == 26)
                               ResourceTime[0] += (int)MrF[n,m];
                           else if (n == 3 || n == 12 || n == 19 || n == 22)
                               ResourceTime[1] += (int)MrF[n,m];
                           else if (n == 5 || n == 8 || n == 18 || n == 24)
                               ResourceTime[2] += (int)MrF[n,m];
                       }
                   }*/
                //===================================== end of xiong98 =====================================



                for (int n = 0; n < AStar.np; ++n)
                {
                    if (MF[n] != 0)
                    {
                        for (int x = 0; x < ResNum; ++x)
                        {
                            ResourceTime[x] += MF[n] * WOT[n, x];
                        }
                    }
                }
                
                double max = 0;
                for (int i = 0; i < ResourceTime.Length; ++i)
                {
                    if (max < ResourceTime[i])
                    {
                        max = ResourceTime[i];
                    }
                }
                return max;
            }


            if (method == 2)
            {
                return 0;
            }

            if (method == 4)
            {
                return (-(FMarkingDepth + 1));
            }

           
            if (method == 7)  
            //h7=h_H comes from Eq.(9.2) in Chapter 9 of our book. It is an admissible and highly informed heuristic function.     
            //Before h7=h_H is used, the number of resource places, the WRT matrix, the Upi matrix, and the M0r vector of the Petri net should be given. 
            //WRT denotes the weighted remaining time whose definition is given in Chapter 9 of our book.
            //Upi(r) denotes the units of r that are required by the operation denoted by the place pi. 
            //M0r denotes the number of tokens in each resource place at the initial marking.
            {
                /*  
                  //===================================== start of xiong98 =====================================
                  const int ResNum = 3; //the number of resource places
                  double[] ResourceTime = new double[ResNum];
                  for (int i = 0; i < ResourceTime.Length; ++i)
                  {
                      ResourceTime[i] = 0;
                  }
                  double[,] WRT =
                 {
                             {2,3,4},{0,3,4},{0,3,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                             {2,2,4},{2,2,0},{2,2,0},{0,2,0},{0,2,0},{0,0,0},{0,0,0},
                             {3,3,5},{0,3,5},{0,3,5},{0,3,0},{0,3,0},{0,0,0},{0,0,0},
                             {3,3,4},{3,0,4},{3,0,4},{3,0,0},{3,0,0},{0,0,0},{0,0,0},
                             {0,0,0},{0,0,0},{0,0,0}
                         };
                     /*   double[,] WRT =
                     {
                   {2,1.5,4},{0,1.5,4},{0,1.5,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                   {2,1,4},{2,1,0},{2,1,0},{0,1,0},{0,1,0},{0,0,0},{0,0,0},
                   {3,1.5,5},{0,1.5,5},{0,1.5,5},{0,1.5,0},{0,1.5,0},{0,0,0},{0,0,0},
                   {3,1.5,4},{3,0,4},{3,0,4},{3,0,0},{3,0,0},{0,0,0},{0,0,0},
                   {0,0,0},{0,0,0},{0,0,0}
                           };*/
                //库所pi需要多少个资源r
                /*         double[,] Upi =
                          {
                             {0,0,0},{1,0,0},{0,0,0},{0,1,0},{0,0,0},{0,0,1},{0,0,0},
                             {0,0,0},{0,0,1},{0,0,0},{1,0,0},{0,0,0},{0,1,0},{0,0,0},
                             {0,0,0},{1,0,0},{0,0,0},{0,0,1},{0,0,0},{0,1,0},{0,0,0},
                             {0,0,0},{0,1,0},{0,0,0},{0,0,1},{0,0,0},{1,0,0},{0,0,0},
                             {0,0,0},{0,0,0},{0,0,0}
                         };
                         //手动计算资源库所的资源数量
                         int[] M0r = new int[ResNum] { 1, 1, 1 };
                         /*    for (int i = 0; i < ResourceTime.Length; ++i)
                             {
                                 M0r[i] = AStar.StartM[28 + i];
                                // Console.Write("[{0}]{1}",i,M0r[i]);
                               //  Console.WriteLine();
                             }*/

                //===================================== end of xiong98 =====================================

                
                
                   //===================================== start of ChenFig6 =====================================
                   const int ResNum = 7; //the number of resource places
                   double [] ResourceTime = new double [ResNum];
                   for (int i = 0; i < ResourceTime.Length; ++i)
                   {
                       ResourceTime[i] = 0;
                   }

                   double  [,] WRT =
                   {
                       {0,7,0,0,2,0,0},{0,5,0,0,2,0,0},{0,5,0,0,0,0,0},{0,0,0,0,0,0,0},{3,3,4,0,0,0,0},{0,3,4,0,0,0,0},
                       {0,6,4,0,1,0,0},{0,0,4,0,1,0,0},{0,0,4,0,0,0,0},{0,0,0,0,0,0,0},{0,3,4,0,0,0,2},{0,0,4,0,0,0,2},
                       {0,0,4,0,0,0,0},{2,4,6,0,0,3,1.5},{2,4,0,0,0,3,1.5},{2,4,0,0,0,3,0},{2,0,0,0,0,3,0},{2,0,0,0,0,0,0},
                       {0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},
                       {0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0}
                    };
                    double[,] Upi =
                    {
                        {0,0,0,0,0,0,0},{0,1,0,0,0,0,0},{0,0,0,0,1,0,0},{0,1,0,0,0,0,0},{0,0,0,0,0,0,0},{1,0,0,0,0,0,0},
                        {0,0,0,1,0,0,0},{0,1,0,0,0,0,0},{0,0,0,0,1,0,0},{0,0,1,0,0,0,0},{0,0,0,0,0,1,0},{0,1,0,0,0,0,0},
                        {0,0,0,0,0,0,1},{0,0,0,0,0,0,0},{0,0,1,0,0,0,0},{0,0,0,0,0,0,1},{0,1,0,0,0,0,0},{0,0,0,0,0,1,0},
                        {1,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},
                        {0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0}
                    };
                    int[] M0r = new int[ResNum] { 1,1,1,2,2,2,2 };
                //===================================== end of ChenFig6 =====================================
               

                /*
                //===================================== start of ChenFig5 =====================================
                const int ResNum = 6; //the number of resource places

                double[] ResourceTime = new double[ResNum];
                for (int i = 0; i < ResourceTime.Length; ++i)                
                    ResourceTime[i] = 0;
                


                double[,] WRT =
               {
                     /* {0,0,7,5,0,3},{0,0,4,5,0,3},{0,0,4,5,0,3},{0,0,4,5,0,3},{0,0,0,5,0,3},{0,0,0,5,0,0},{0,0,0,0,0,0},
                      {4,3,9,2,0,0},{4,3,9,0,0,0},{0,3,9,0,0,0},{0,3,5,0,0,0},{0,0,5,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},
                      {0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},*/
         /*                  {0,0,3,0,7,5 }, {0,0,3,0,4,5 }, {0,0,3,0,4,5 }, {0,0,3,0,4,5 }, {0,0,3,0,0,5 }, {0,0,0,0,0,5 }, {0,0,0,0,0,0 },
                           {0,3,0,4,9,2 }, {0,3,0,4,9,0 }, {0,3,0,0,9,0 }, {0,3,0,0,5,0 }, {0,0,0,0,5,0 }, {0,0,0,0,0,0 }, {0,0,0,0,0,0 },
                             {0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0}
                       };
                double[,] Upi =
                     {
                         /* {0,0,0,0,0,0,0},{0,0,1,0,0,0,0},{0,1,0,0,0,0,0},{0,0,0,0,0,1,0},{0,0,1,0,0,0,0},{0,0,0,0,0,0,1},{0,0,0,0,1,0,0},
                          {0,0,0,0,0,0,0},{0,0,0,0,1,0,0},{1,0,0,0,0,0,0},{0,0,1,0,0,0,0},{0,1,0,0,0,0,0},{0,0,1,0,0,0,0},{0,0,0,0,0,0,0},
                          {0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0}*/
         /*              {0,0,0,0,0,0},{0,0,0,0,1,0},{0,1,0,0,0,0},{1,0,0,0,0,0},{0,0,0,0,1,0},{0,0,1,0,0,0},{0,0,0,0,0,1},
                        {0,0,0,0,0,0},{0,0,0,0,0,1},{0,0,0,1,0,0},{0,0,0,0,1,0},{0,1,0,0,0,0},{0,0,0,0,1,0},{0,0,0,0,0,0},
                        {0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0}
                    };

                int[] M0r = new int[ResNum] { 1, 1, 1, 1, 1, 1 }; //the number of tokens in each resource place at the initial marking
                //===================================== end of ChenFig5 =====================================

                /*
                   //===================================== start of New4x3 =====================================
                   const int ResNum = 3; //the number of resource places
                   double[] ResourceTime = new double[ResNum];//每个资源库所的所有标识的剩余处理时间
                   for (int i = 0; i < ResourceTime.Length; ++i)
                   {
                       ResourceTime[i] = 0;
                   }

                   double[,] WRT =
                   {
                       {5,4,4},{0,4,4},{0,4,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                       {2,2,5},{2,0,5},{2,0,5},{2,0,0},{2,0,0},{0,0,0},{0,0,0},
                       {2,5,5},{2,5,0},{2,5,0},{0,5,0},{0,5,0},{0,0,0},{0,0,0},
                       {2,4,2},{2,4,0},{2,4,0},{2,0,0},{2,0,0},{0,0,0},{0,0,0},
                       {0,0,0},{0,0,0},{0,0,0}
                   };
                  double[,] Upi =
                  {
                      {0,0,0},{1,0,0},{0,0,0},{0,1,0},{0,0,0},{0,0,1},{0,0,0},
                      {0,0,0},{0,1,0},{0,0,0},{0,0,1},{0,0,0},{1,0,0},{0,0,0},
                      {0,0,0},{0,0,1},{0,0,0},{1,0,0},{0,0,0},{0,1,0},{0,0,0},
                      {0,0,0},{0,0,1},{0,0,0},{0,1,0},{0,0,0},{1,0,0},{0,0,0},
                      {0,0,0},{0,0,0},{0,0,0},
                  };

                   int[] M0r = new int[ResNum] { 1, 1, 1};
                   //===================================== end of New4x3 =====================================
                   */


                /*
               //===================================== start of Huang2012Fig1 =====================================
               const int ResNum = 3; //the number of resource places
               double[] ResourceTime = new double[ResNum];//每个资源库所的所有标识的剩余处理时间
               for (int i = 0; i < ResourceTime.Length; ++i)
               {
                   ResourceTime[i] = 0;
               }

               int[,] WRT = { {57,0,85 }, {57,0,85 } , {57,0,85 }, { 57,0,85},{57,0,0 }, {57,0,0 }, { 0,0,0}, { 0,0,51}, {0,0,51 }, {0,0,0 }, {0,0,0 },
                                   {0,95,0 }, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0},
                                   {0,78,75 }, {0,0,75 }, { 0,0,75}, {0,0,0 }, {0,0,0 }, {0,0,0 }, { 0,70,0}, {0,70,0 }, { 0,0,0}, { 0,0,0},
                                    { 93,0,175}, {93,0,76 }, { 93,0,76}, { 93,0,0}, { 93,0,0}, { 0,0,0 }, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0} };
               double[,] Upi = { { 0,0,0}, { 0, 0, 1 }, { 0, 1, 0 }, { 0, 0, 0 }, { 0, 0, 1 }, { 0, 0, 0 }, {1, 0, 0 }, { 1, 0, 0 }, { 0, 0, 0 }, { 0, 0, 1 }, { 0, 0, 0 },
                                { 0,0,0},{ 0,1,0},{ 0,0,0},{ 0,1,0},{ 0,0,1},{ 0,0,0},{ 1,0,0},{ 0,0,1},{ 0,0,0},
                                  { 0,0,0},{ 0,1,0},{ 0,0,0},{ 0,0,1},{ 0,0,0},{ 1,0,0},{ 0,0,1},{ 0,0,0},{ 0,1,0},{ 0,0,0},
                                  { 0,0,0},{ 0,0,1},{ 0,0,0},{ 0,0,1},{ 0,0,0},{ 1,0,0},{ 0,0,0},{ 0,0,0},{ 0,0,0},{ 0,0,0}};
               int[] M0r = new int[ResNum] { 1, 1, 1 };
               //===================================== start of Huang2012Fig1 =====================================
                */
                

/*
               //===================================== start of Huang2012Fig1Reviesed =====================================       
               const int ResNum = 3; //the number of resource places                                                              
               double[] ResourceTime = new double[ResNum];//每个资源库所的所有标识的剩余处理时间                                  
               for (int i = 0; i < ResourceTime.Length; ++i)                                                                      
               {                                                                                                                  
                   ResourceTime[i] = 0;                                                                                           
               }                                                                                                                  
                                                                                                                                  
               double[,] WRT = { {57,0,42.5 }, {57,0,42.5 } , {57,0,42.5 }, { 57,0,42.5},{57,0,0 }, {57,0,0 }, { 0,0,0}, { 0,0,51}
                                   {0,95,0 }, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0},     
                                   {0,78,37.5 }, {0,0,37.5 }, { 0,0,37.5}, {0,0,0 }, {0,0,0 }, {0,0,0 }, { 0,70,0}, {0,70,0 }, { 0
                                    { 93,0,87.5}, {93,0,38 }, { 93,0,38}, { 93,0,0}, { 93,0,0}, { 0,0,0 }, { 0,0,0}, { 0,0,0}, { 0
               double[,] Upi = { {0,0,0}, {0, 0, 1}, {0, 1, 0}, {0, 0, 0}, {0, 0, 1}, {0, 0, 0}, {1, 0, 0}, {1, 0, 0}, {0, 0, 0}, 
                                { 0,0,0},{ 0,1,0},{ 0,0,0},{ 0,1,0},{ 0,0,1},{ 0,0,0},{ 1,0,0},{ 0,0,1},{ 0,0,0},                 
                                  { 0,0,0},{ 0,1,0},{ 0,0,0},{ 0,0,1},{ 0,0,0},{ 1,0,0},{ 0,0,1},{ 0,0,0},{ 0,1,0},{ 0,0,0},      
                                  { 0,0,0},{ 0,0,1},{ 0,0,0},{ 0,0,1},{ 0,0,0},{ 1,0,0},{ 0,0,0},{ 0,0,0},{ 0,0,0},{ 0,0,0}};     
               int[] M0r = new int[ResNum] { 1, 1, 2 };                                                                           
               //===================================== start of Huang2012Fig1Reviesed =====================================       
*/
                                
               


                for (int n = 0; n < AStar.np - AStar.nrs; ++n) //for each non-resource place
                {
                    //取p_i中所有非零剩余时间之和
                    double temp = 0;
                    for (int t = 0; t < AStar.MAX_TOK_PA; t++)
                    {
                        temp += MrF[n, t];
                    }

                    if (MF[n] != 0)
                    {
                        for (int x = 0; x < ResNum; ++x)
                        {
                            ResourceTime[x] += MF[n] * WRT[n, x];
                            ResourceTime[x] += temp * Upi[n, x] / M0r[x];
                        }
                    }
                }
                //h=max{ei(m)}
                double max1 = 0;
                for (int i = 0; i < ResourceTime.Length; ++i)
                {
                    if (max1 < ResourceTime[i])
                    {
                        max1 = ResourceTime[i];
                    }
                }

                double max = 0;
                max = max1;

               

                //  max = max1 + ep2 * (1 - ((float)FMarkingDepth + 1) /32) * max1;//！！！！要修改总的深度！！！！！原函数
                // max= max1+ep2 * (System.Math.Sqrt(max1 / hValueStartNode)) * max1;
                //max = max1 + ep2 * (max1 / hValueStartNode) * max1;
                //   max = max1+ep2*Math.Pow(max1 / hValueStartNode, 1.0/4)* max1;//开方函数                
                //  Console.Write(Math.Round(1 - ((float)FMarkingDepth + 1) / 72,2));
                // Console.WriteLine();
                //max为h(M)=max{ei(m)}的值，72为N总深度72=24*3，chenfig6222 32  ,xiong983333   72   ,ChenFig566   72,New4x3_1111  24
                //  max = max1 + ep2 * (1- System.Math.Abs(2 * ((float)FMarkingDepth + 1) / 72 - 1)) * max1;//这里陷入无解状态，出不来结果//绝对值函数
                //max = max1+ep2*Math.Pow(((float)FMarkingDepth + 1) / 72 - 1,2)* max1;//开方函数
                /*Console.Write(Math.Round(1 - System.Math.Abs(2 * ((float)FMarkingDepth + 1) / 72- 1), 2));
                  Console.WriteLkine();*/
                // Console.Write(Math.Round(Math.Pow(((float)FMarkingDepth + 1) / 72 - 1, 2), 2));
                //  Console.WriteLine();
                //  max = max1 + ep2 * (System.Math.Sqrt(1 - ((float)FMarkingDepth + 1) / 72)) * max1;//开平方函数
                //  max = max1 + ep2 * (System.Math.Pow(1 - ((float)FMarkingDepth + 1) / 72,1.0/4)) * max1;//开随意平方函数
                //   Console.Write(Math.Round(System.Math.Sqrt(1 - ((float)FMarkingDepth + 1) / 72),2));
                //  Console.WriteLine();
                //     if(FMarkingDepth <=0.5*32)//分段函数
                //       max = max1 + ep2 * (System.Math.Sqrt(1 - ((float)FMarkingDepth + 1) / 32)) * max1;
                //  else
                //  max = max1 + ep2 * ( 0.707*System.Math .Abs(Math.Log(((float)FMarkingDepth + 1) / 32,2))) * max1;
                //log函数不可取，因为log函数的真数不能为0
                return max;
            }


            
            if (method == 9)//该h函数为改进xiong98即添加hs和he两个部分  zhaozhixia  
            //h9=hs+max{ei(m)}+he in which max{ei(m)} comes from Xiong98, hs denotes the necessary time before the resource is used, and he denotes the necessary time after the resource is used.
            {

                //===================================== start of xiong98 =====================================
                const int ResNum = 3; //三个资源库所
                int[] ResourceTime = new int[ResNum];
                int[] MachineTime2 = new int[ResNum];
                int[] MachineTime3 = new int[ResNum];
                for (int i = 0; i < ResourceTime.Length; ++i)
                {
                    ResourceTime[i] = 0;
                }
                for (int i = 0; i < MachineTime2.Length; ++i)
                {
                    MachineTime2[i] = 0;
                }
                for (int i = 0; i < MachineTime3.Length; ++i)
                {
                    MachineTime3[i] = 0;
                }

                //=============== start of 原xiong98 =================
                int[,] RST =
                    {
                   {2,3,4},{0,3,4},{0,3,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                   {2,2,4},{2,2,0},{2,2,0},{0,2,0},{0,2,0},{0,0,0},{0,0,0},
                   {3,3,5},{0,3,5},{0,3,5},{0,3,0},{0,3,0},{0,0,0},{0,0,0},
                   {3,3,4},{3,0,4},{3,0,4},{3,0,0},{3,0,0},{0,0,0},{0,0,0},
                   {0,0,0},{0,0,0},{0,0,0}//原xiong98
                   };
                //原xiong98
                int[,] hs = { { 0, -1, -1, -1, -1, -1, -1, 4, 0, 0, -1, -1, -1, -1, 0, -1, -1, -1, -1, -1, -1,  7, 4, 4, 0, 0, -1, -1 },
                                      { 2, 0, 0, -1, -1, -1, -1, 6, 2, 2, 0, 0, -1, -1, 8, 5, 5, 0, 0, -1, -1, 0,-1,-1,-1,-1,-1,-1 },
                                      { 5, 3, 3, 0, 0, -1, -1, 0, -1, -1, -1, -1, -1, -1, 3, 0, 0, -1, -1, -1, -1, 3, 0, 0, -1, -1, -1, -1 }};
                //    int[,] he = { { 7, 7, 7, 4, 4, 0, 0, 2, 2, 2, 2, 2, 0, 0, 8, 8, 8, 3, 3, 0, 0,0,0,0,0,0, 0, 0 } ,
                //                     { 4, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  7, 7, 7, 3, 3, 0, 0 } ,
                //                    { 0, 0, 0, 0, 0, 0, -1, 4, 4, -1,-1, -1, -1, -1, 3, 3, 3, 3, -1, -1, -1, 3, 3, 3, 3, -1, -1, -1 }};
                //   int[,] he = { { 7, -1, -1, -1, -1, -1, -1, 2, 2, 2, -1, -1, -1, -1, 8, -1, -1, -1, -1, -1, -1,0,0,0,0,0,-1,-1 },
                //                   {4,4,4,-1,-1,-1,-1,0,0,0,0,0,-1,-1,0,0,0,0,0,-1,-1,7, -1, -1, -1, -1, -1, -1 },
                //                   {0,0,0,0,0,-1,-1,4,-1,-1,-1,-1,-1,-1,3,3,3,-1,-1,-1,-1,3,3,3,-1,-1,-1,-1 } };
                int[,] he = { { 7, 7, -1, -1, -1, -1, -1, 2, 2, 2, 2, -1, -1, -1, 8, 8, -1, -1, -1, -1, -1,0,0,0,0,0,0,-1 },
                                 {4,4,4,4,-1,-1,-1,0,0,0,0,0,0,-1,0,0,0,0,0,0,-1,7, 7, -1, -1, -1, -1, -1 },
                                 {0,0,0,0,0,0,-1,4,4,-1,-1,-1,-1,-1,3,3,3,3,-1,-1,-1,3,3,3,3,-1,-1,-1 } };
                //=============== end of 原xiong98 =================

                /*
                //========= strat of 改xiong98 （m1 m2在job4上交换）======
                int[,] RST =
                  {
                    {2,3,4},{0,3,4},{0,3,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                    {2,2,4},{2,2,0},{2,2,0},{0,2,0},{0,2,0},{0,0,0},{0,0,0},
                    {3,3,5},{0,3,5},{0,3,5},{0,3,0},{0,3,0},{0,0,0},{0,0,0},
                    {3,3,4},{0,3,4},{0,3,4},{0,3,0},{0,3,0},{0,0,0},{0,0,0},
                    {0,0,0},{0,0,0},{0,0,0}///xiong98改动m1 m2  job4
                };
                //job4的xiong98m1和m2交换
                int[,] hs = { { 0, -1, -1, -1, -1, -1, -1, 4, 0, 0, -1, -1, -1, -1, 0, -1, -1, -1, -1, -1, -1,  0,-1,-1,-1,-1,-1,-1 },
                                   { 2, 0, 0, -1, -1, -1, -1, 6, 2, 2, 0, 0, -1, -1, 8, 5, 5, 0, 0, -1, -1,7, 4, 4, 0, 0, -1, -1 },
                                   { 5, 3, 3, 0, 0, -1, -1, 0, -1, -1, -1, -1, -1, -1, 3, 0, 0, -1, -1, -1, -1, 3, 0, 0, -1, -1, -1, -1 }};
                int[,] he = { { 7, 7, -1, -1, -1, -1, -1, 2, 2, 2, 2, -1, -1, -1, 8, 8, -1, -1, -1, -1, -1,7, 7, -1, -1, -1, -1, -1 },
                              {4,4,4,4,-1,-1,-1,0,0,0,0,0,0,-1,0,0,0,0,0,0,-1,0,0,0,0,0,0,-1 },
                              {0,0,0,0,0,0,-1,4,4,-1,-1,-1,-1,-1,3,3,3,3,-1,-1,-1,3,3,3,3,-1,-1,-1 } };
                //======= end of 改xiong98 （m1 m2在job4上交换）=========
                */
                /*
                //=============== strat of 改xiong98 （m1 m3在job3上交换）=================
                int[,] RST =
                {
                    {2,3,4},{0,3,4},{0,3,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                    {2,2,4},{2,2,0},{2,2,0},{0,2,0},{0,2,0},{0,0,0},{0,0,0},
                    {5,3,3},{5,3,0},{5,3,0},{0,3,0},{0,3,0},{0,0,0},{0,0,0},
                    {3,3,4},{3,0,4},{3,0,4},{3,0,0},{3,0,0},{0,0,0},{0,0,0},
                    {0,0,0},{0,0,0},{0,0,0}//m1  m3 job
                };
                //xiong98改进图m1 m3在job3交换
                  int[,] hs = { { 0, -1, -1, -1, -1, -1, -1, 4, 0, 0, -1, -1, -1, -1, 3, 0, 0, -1, -1, -1, -1, 7, 4, 4, 0, 0, -1, -1 } ,
                              { 2, 0, 0, -1, -1, -1, -1, 6, 2, 2, 0, 0, -1, -1, 8, 5, 5, 0, 0, -1, -1, 0,-1,-1,-1,-1,-1,-1 },
                                     { 5, 3, 3, 0, 0, -1, -1, 0, -1, -1, -1, -1, -1, -1, 0, -1, -1, -1, -1, -1, -1,3, 0, 0, -1, -1, -1, -1 }};
                  int[,] he = { { 7, 7, -1, -1, -1, -1, -1, 2, 2, 2, 2, -1, -1, -1, 3,3,3,3,-1,-1,-1,0,0,0,0,0,0,-1 },
                                {4,4,4,4,-1,-1,-1,0,0,0,0,0,0,-1,0,0,0,0,0,0,-1,7, 7, -1, -1, -1, -1, -1 },
                                {0,0,0,0,0,0,-1,4,4,-1,-1,-1,-1,-1,8, 8, -1, -1, -1, -1, -1,3,3,3,3,-1,-1,-1 } };
                //=============== end of 改xiong98 （m1 m3在job3上交换）=================
                */
                /*
                //=============== strat of 改xiong98 （平行）=================
                int[,] RST =
                {
                    {2,3,4},{0,3,4},{0,3,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                    {4,2,2},{0,2,2},{0,2,2},{0,0,2},{0,0,2},{0,0,0},{0,0,0},
                    {3,5,3},{0,5,3},{0,5,3},{0,0,3},{0,0,3},{0,0,0},{0,0,0},
                    {3,4,3},{0,4,3},{0,4,3},{0,0,3},{0,0,3},{0,0,0},{0,0,0},
                    {0,0,0},{0,0,0},{0,0,0}////平行xiong98
                };
                  int[,] hs = { { 0, -1, -1, -1, -1, -1, -1, 0, -1, -1, -1, -1, -1, -1, 0, -1, -1, -1, -1, -1, -1, 0, -1, -1, -1, -1, -1, -1 },
                { 2, 0, 0, -1, -1, -1, -1, 4, 0, 0, -1, -1, -1, -1,3, 0, 0, -1, -1, -1, -1,3, 0, 0, -1, -1, -1, -1 },
               { 5, 3, 3, 0, 0, -1, -1,  6, 2, 2, 0, 0, -1, -1, 8, 5, 5, 0, 0, -1, -1,7, 4, 4, 0, 0, -1, -1} };
                int[,] he = { { 7, 7, -1, -1, -1, -1, -1, 4, 4, -1, -1, -1, -1, -1, 8, 8, -1, -1, -1, -1, -1, 7, 7, -1, -1, -1, -1, -1 },
               {4,4,4,4,-1,-1,-1, 2, 2, 2, 2, -1, -1, -1,3,3,3,3,-1,-1,-1,3,3,3,3,-1,-1,-1 },
                {0,0,0,0,0,0,-1,0,0,0,0,0,0,-1,0,0,0,0,0,0,-1,0,0,0,0,0,0,-1 }};//平行xiong98
                //=============== end of 改xiong98 （平行）=================
                */
                //加Mr
                /*   for (int n = 0; n < AStar.np; ++n)
                   {
                       if (MrF[n] != 0)
                       {
                           if (n==1||n==10||n==15||n==22)
                               ResourceTime[0] += (int)MrF[n];
                           else if (n == 3 || n == 12 || n == 19 || n == 26)
                               ResourceTime[1] += (int)MrF[n];
                           else if (n == 5 || n == 8 || n == 18 || n == 24)
                               ResourceTime[2] += (int)MrF[n];
                       }
                   }*/
                //===================================== start of xiong98 =====================================
                /*
                //===================================== start of New4x3 =====================================
                const int ResNum = 3; //三个资源库所
                int[] ResourceTime = new int[ResNum];
                int[] MachineTime2 = new int[ResNum];
                int[] MachineTime3 = new int[ResNum];
                for (int i = 0; i < ResourceTime.Length; ++i)
                {
                    ResourceTime[i] = 0;
                }
                for (int i = 0; i < MachineTime2.Length; ++i)
                {
                    MachineTime2[i] = 0;
                }
                for (int i = 0; i < MachineTime3.Length; ++i)
                {
                    MachineTime3[i] = 0;
                }

             int[,] RST =
               {
                 {5,4,4},{0,4,4},{0,4,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                 {2,2,5},{2,0,5},{2,0,5},{2,0,0},{2,0,0},{0,0,0},{0,0,0},
                 {2,5,5},{2,5,0},{2,5,0},{0,5,0},{0,5,0},{0,0,0},{0,0,0},
                 {2,4,2},{2,4,0},{2,4,0},{2,0,0},{2,0,0},{0,0,0},{0,0,0},
                 {0,0,0},{0,0,0},{0,0,0}
               };

                //加Mr
             /*   for (int n = 0; n < AStar.np; ++n)
                {
                    if (MrF[n] != 0)
                     {
                        if (n == 1 || n == 12 || n == 17 || n == 26)
                            ResourceTime[0] += (int)MrF[n];
                        else if (n == 3 || n == 8 || n == 19 || n == 24)
                            ResourceTime[1] += (int)MrF[n];
                        else if (n == 5 || n == 10 || n == 15 || n == 22)
                            ResourceTime[2] += (int)MrF[n];
                     }
                }*/
                /*    int[,] hs={{0,-1,-1,-1,-1,-1,-1,7,5,5,0,0,-1,-1,5,0,0,-1,-1,-1,-1,6,4,4,0,0,-1,-1},
                              {5,0,0,-1,-1,-1,-1,0,-1,-1,-1,-1,-1,-1,7,2,2,0,0,-1,-1,2,0,0,-1,-1,-1,-1},
                              {9,4,4,0,0,-1,-1,2,0,0,-1,-1,-1,-1,0,-1,-1,-1,-1,-1,-1,0,-1,-1,-1,-1,-1,-1}};
                    int[,] he={{8,8,-1,-1,-1,-1,-1,0,0,0,0,0,0,-1,5,5,5,5,-1,-1,-1,0,0,0,0,0,0,-1},
                               {4,4,4,4,-1,-1,-1,7,7,-1,-1,-1,-1,-1,0,0,0,0,0,0,-1,2,2,2,2,-1,-1,-1},
                               {0,0,0,0,0,0,-1,2,2,2,2,-1,-1,-1,7,7,-1,-1,-1,-1,-1,6,6,-1,-1,-1,-1,-1} };
                     //===================================== end of New4x3 =====================================
                     */
                /*
               //===================================== start of ChenFig5 =====================================
               const int ResNum = 6; //六个资源库所
           int[] ResourceTime = new int[ResNum];
           int[] MachineTime2 = new int[ResNum];
           int[] MachineTime3 = new int[ResNum];
           for (int i = 0; i < ResourceTime.Length; ++i)
           {
               ResourceTime[i] = 0;
           }
           for (int i = 0; i < MachineTime2.Length; ++i)
           {
               MachineTime2[i] = 0;
           }
           for (int i = 0; i < MachineTime3.Length; ++i)
           {
               MachineTime3[i] = 0;
           }
           int[,] RST =
               {
                   {0,0,7,5,0,3},{0,0,4,5,0,3},{0,0,4,5,0,3}, {0,0,4,5,0,3}, {0,0,0,5,0,3}, {0,0,0,5,0,0}, {0,0,0,0,0,0},
                   {4,3,9,2,0,0}, {4,3,9,0,0,0}, {0,3,9,0,0,0},{0,3,5,0,0,0}, {0,0,5,0,0,0}, {0,0,0,0,0,0}, {0,0,0,0,0,0},
                   {0,0,0,0,0,0},{0,0,0,0,0,0}, {0,0,0,0,0,0},{0,0,0,0,0,0},  {0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},   
               };
           int[,] hs ={{-1,-1,-1,-1,-1,-1,-1,2,0,-1,-1,-1,-1,-1,-1},
                         {3,0,-1,-1,-1,-1,-1,10,8,4,0,-1,-1,-1,-1},
                         {0,2,0,0,-1,-1,-1,6,4,0,3,0,-1,-1,-1 },
                         { 12,9,7,7,3,0,-1,0,-1,-1,-1,-1,-1,-1,-1},
                         {3,0, -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
                         {9,6,4,4,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1}};
           int[,] he = { { -1,-1,-1,-1,-1,-1,-1,12,12,12,-1,-1,-1,-1,-1},
                         {12,12,12,-1,-1,-1,-1,5,5,5,5,5,-1,-1,-1 },
                          {8,8,8,8,8,-1,-1,0,0,0,0,0,0,-1,-1 },
                          {0,0,0,0,0,0,0,16,16,-1,-1,-1,-1,-1,-1 },
                          {12,12,-1,12,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1 },
                           {5,5,5,5,5,5,-1,-1,-1,-1,-1,-1,-1,-1,-1 }};
           //===================================== end of ChenFig5 =====================================                 
           */
                /*
                //===================================== start of ChenFig6111 =====================================
                const int ResNum = 7; //7个资源库所
                int[] ResourceTime = new int[ResNum];
                int[] MachineTime2 = new int[ResNum];
                int[] MachineTime3 = new int[ResNum];
                for (int i = 0; i < ResourceTime.Length; ++i)
                {
                    ResourceTime[i] = 0;
                }
                for (int i = 0; i < MachineTime2.Length; ++i)
                {
                    MachineTime2[i] = 0;
                }
                for (int i = 0; i < MachineTime3.Length; ++i)
                {
                    MachineTime3[i] = 0;
                }
                int[,] RST=
                {
                         {0,7,0,0,4,0,0},{0,5,0,0,4,0,0},{0,5,0,0,0,0,0},{0,0,0,0,0,0,0},{3,3,4,0,0,0,0},{0,3,4,0,0,0,0},
                         {0,6,4,0,2,0,0},{0,0,4,0,2,0,0},{0,0,4,0,0,0,0},{0,0,0,0,0,0,0},{0,3,4,0,0,0,4},{0,0,4,0,0,0,4},
                         {0,0,4,0,0,0,0},{2,4,6,0,0,6,3},{2,4,0,0,0,6,3},{2,4,0,0,0,6,0},{2,0,0,0,0,6,0},{2,0,0,0,0,0,0},
                         {0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},
                         {0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0}
                 };
                int[,] hs = { { -1,-1,-1,-1,0,-1,-1,-1,-1,-1,-1,-1,-1,19,13,10,6,0,-1,-1,-1,-1},
                              {0,4,0,-1,4,1,0,-1,-1,-1,0,-1,-1,9,3,0,-1,-1,-1,-1,-1,-1 },
                               {-1,-1,-1,-1,11,8,8,2,0,-1,7,4,0,0,-1,-1,-1,-1,-1,-1,-1,-1 },
                               {-1,-1,-1,-1,3,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1 },
                               { 2,0,-1,-1,11,8,6,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
                               { -1,-1,-1,-1,3,0,-1,-1,-1,-1,-1,-1,-1,13,7,4,0,-1,-1,-1,-1,-1},
                               {-1,-1,-1,-1,7,4,-1,-1,-1,-1,3,0,-1,6,0,-1,-1,-1,-1,-1,-1,-1 } };
                /*  int[,] he = { { -1,-1,-1,-1,12,12,-1,-1,-1,-1,-1,-1,-1,0,0,0,0,0,0,-1,-1,-1},
                                {0,0,0,0,6,6,6,6,-1,-1,8,8,-1,8,8,8,8,-1,-1,-1,-1,-1 },
                                 {-1,-1,-1,-1,0,0,0,0,0,0,0,0,0,15,15,-1,-1,-1,-1,-1,-1,-1 },
                                  { -1,-1,-1,-1,12,12,12,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
                                 {5,5,5,-1,4,4,4,4,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1 },
                                  {-1,-1,-1,-1,11,11,-1,-1,-1,-1,11,-1,-1,2,2,2,2,2,-1,-1,-1,-1 },
                                  {-1,-1,-1,-1,4,4,-1,-1,-1,-1,4,4,4,12,12,12,-1,-1,-1,-1,-1,-1 }};*/
                /*     int[,] he = { { -1,-1,-1,-1,-1,12,-1,-1,-1,-1,-1,-1,-1,0,0,0,0,0,-1,-1,-1,-1},
                                   {0,-1,0,-1,6,6,6,-1,-1,-1,8,-1,-1,8,8,8,-1,-1,-1,-1,-1,-1 },
                                    {-1,-1,-1,-1,0,0,0,0,0,-1,0,0,0,15,-1,-1,-1,-1,-1,-1,-1,-1 },
                                     { -1,-1,-1,-1,12,12,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
                                    {5,5,-1,-1,4,4,4,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1 },
                                     {-1,-1,-1,-1,11,11,-1,-1,-1,-1,-1,-1,-1,2,2,2,2,-1,-1,-1,-1,-1 },
                                     {-1,-1,-1,-1,4,4,-1,-1,-1,-1,4,4,-1,12,12,-1,-1,-1,-1,-1,-1,-1 }};
                     //===================================== start of ChenFig6111 =====================================
                     */
                //通用
                int k = 0;
                int s = 0;
                int min2 = 0;
                int min3 = 0;//max2为资源m3对应的各个库所的等待时间
                for (int m = 0; m < AStar.nrs; ++m)
                {
                    for (int n = 0; n < AStar.np - AStar.nrs; ++n)
                    {
                        if (MF[n] != 0)
                        {
                            ResourceTime[m] += MF[n] * RST[n, m];
                        }
                    }
                    for (int n = 0; n < AStar.np - AStar.nrs; ++n)
                    {
                        if (MF[n] != 0)
                        {

                            if (hs[m, n] != -1)
                            {
                                min2 = hs[m, n];
                                k = n;
                                break;
                            }

                        }
                    }
                    for (int n = k + 1; n < AStar.np - AStar.nrs; ++n)
                    {
                        if (MF[n] != 0)
                        {
                            if (hs[m, n] != -1)
                            {
                                if (min2 > hs[m, n])
                                    min2 = hs[m, n];//此处取目前状态下对应等待时间的最小值
                            }
                        }
                    }

                    for (int n = 0; n < AStar.np - AStar.nrs; ++n)
                    {
                        if (MF[n] != 0)
                        {
                            if (he[m, n] != -1)
                            {
                                min3 = he[m, n];
                                s = n;
                                break;
                            }

                        }
                    }
                    for (int n = s + 1; n < AStar.np - AStar.nrs; ++n)
                    {
                        if (MF[n] != 0)
                        {
                            if (he[m, n] != -1)
                            {
                                if (min3 > he[m, n])
                                    min3 = he[m, n];//此处取目前状态下对应等待时间的最小值
                            }
                        }
                    }
                    MachineTime2[m] = min2;
                    MachineTime3[m] = min3;
                }

                double max = 0;
                for (int i = 0; i < ResourceTime.Length; ++i)
                {
                    if (max < ResourceTime[i] + MachineTime2[i] + MachineTime3[i])
                    {
                        max = ResourceTime[i] + MachineTime2[i] + MachineTime3[i];
                    }

                }
                double max1 = 0;
                //======xiong98=======
                max1 = max + ep2 * (max / hValueStartNode) * max;// +max2 +max3;

                return max1;

            }

            return 0;
        }

        public virtual double CalculateHF(int method) // calculate the second heursitic value for nodes in OPEN; only applicable to some search strategies
        {
            //CalculateHF(int method) hF1=max{ei(m)}; h2=-dep(m)
            /*if (method==1)
				//h=max{ei(m)} where ei(m) is the sum of operation times of those remaining operation for all jobs
				//which are planned to be processed on the ith machine when the current system state is represented 
				//by the marking m
			{
				decimal[] ResourceTime={0,0,0};
				for(int n=0;n<MF.Length;++n)
				{
					if (MF[n]!=0)
						for(int x=0;x<ResourceTime.Length;++x)
							ResourceTime[x]=ResourceTime[x]+MF[n]*AStar.RST[n,x];
				}

				//加Mr
				if(MF[2]!=0 || MF[13]!=0)
					ResourceTime[0]=ResourceTime[0]+MF[2]*MrF[2]+MF[13]*MrF[13];
				if(MF[4]!=0 || MF[15]!=0)
					ResourceTime[1]=ResourceTime[1]+MF[4]*MrF[4]+MF[15]*MrF[15];
				if(MF[6]!=0 || MF[11]!=0)
					ResourceTime[2]=ResourceTime[2]+MF[6]*MrF[6]+MF[11]*MrF[11];

				decimal max=0;
				for(int c=0;c<ResourceTime.Length;++c)
					if(max<ResourceTime[c])
						max=ResourceTime[c];
				return max;

			}*/


            if (method == 2)
                return (-(FMarkingDepth + 1));

            return 0;
        }

        public virtual void FindEnabledTransitions()//寻找当前标识（FM[i]）下可实施的变迁，并对EnabledTransitions赋值（1：可以实施，0：不能实施）
        {//Find enabled transitions at a marking. It will assign values to EnabledTransitions such that 1 denotes the corresponding transition is enabled and 0 denotes not.
            int e;
            for (int j = 0; j < AStar.nt; ++j)
            {
                e = 1;
                for (int i = 0; i < AStar.np; ++i)
                {
                    if (AStar.LMINUS[i, j] != 0 && FM[i] < AStar.LMINUS[i, j]) //变迁可以实施的条件：当前标志的库所大于变迁所需的输入库所（ M(p) > I(p, t) ）
                    {
                        e = 0;
                        continue;
                    } 
                }
                EnabledTransitions[j] = e; //EnabledTransitions = new int[AStar.nt];
            }
        }

        public virtual void GetSuccessors(ArrayList ASuccessors, int hmethod, double ep2, double hValueStartNode) //获得当前节点的所有子节点，并添加到列表中
        {//Get the child nodes of the current node and handle them with OPEN and CLOSED. 
            //寻找当前标识下可实施的变迁
            FindEnabledTransitions();//Find the enabled transitions at the current node.
            for (int i = 0; i < FEnabledTransitions.Length; ++i)
            {
                if (FEnabledTransitions[i] == 1) //变迁可以实施 if the transition is enabled
                {
                    //程序选择哪个变迁取决于OPEN中相同f值的节点如何排队
                    for (int n = 0; n < AStar.np; ++n)//zzx
                    {
                        for (int m = 0; m < AStar.MAX_TOK_PA; ++m)
                        {
                            MrF[n, m] = FR[n, m];
                        }
                    }
                    //Calculate delt=max{R(pi,k)-W(pi, tj)+1}; Because W(pi,tj)=1 in SC-nets, so delt=max{R(pi,k)} 
                    //where R(pi,k) denotes the remaining time of the last token in pi that is a pre-place of the fired transition
                    delt = 0;
                    for (int x = 0; x < AStar.np-AStar.nrs; ++x)//zzx
                    {
                        if (AStar.LMINUS[x, i] == 1)
                        {
                            //注意，对于每个库所而言，R里面的托肯按照剩余时间非递增排序。且变迁从每个输入非资源库所需要的托肯数为1
                            if (delt < FR[x, 0])//111这里的FM[x]-1应该改成0吧，单个库所的剩余时间最大值应该是R矩阵的第一行
                                delt = FR[x, 0];
                        }
                    }

                    //从变迁的输入库所中移去相应的托肯  Remove tokens from the pre-places of the transition
                    //M(k)+ = M(k)- - LMINUS*u(k) , M(k)+ 和M(k)- 分别表示托肯移走前后的系统标识
                    for (int n = 0; n < AStar.np; ++n)
                    {
                        if (AStar.LMINUS[n, i] != 0)
                            MZ[n] = FM[n] - AStar.LMINUS[n, i]; //MZ：标识状态M(k)+ //MZ: denotes M(k)+
                        else
                            MZ[n] = FM[n];

                    }

                    //向变迁的所有输出库所中添加相应托肯 Add tokens into the post-places of the transition
                    //M(k+1)- = M(k)+ + LPLUS*u(k)
                    for (int n = 0; n < AStar.np; ++n)
                    {
                        if (AStar.LPLUS[n, i] != 0)
                            MF[n] = MZ[n] + AStar.LPLUS[n, i];
                        else
                            MF[n] = MZ[n];
                    }

                    //在剩余处理时间向量Mr(即R)中逐个元素地减去delt，若值小于0则赋值为0   ZZX
                    //Subtract delt from each element of Mr. If the result is below 0, then set the element to 0. 
                    //计算 Mr(k)+z = Mr(k)-z - delt(k)z
                    for (int n = 0; n < AStar.np; ++n)
                    {
                        for (int m = 0; m < AStar.MAX_TOK_PA; ++m)
                        {
                            MrZ[n, m] = FR[n, m] - delt;
                            if (MrZ[n, m] < 0)
                                MrZ[n, m] = 0;
                        }
                    }

                    //向变迁的所有输出库所的R中第一个位置加入新托肯的操作时间，其它托肯的剩余时间向后移动 
                    //Mr(k+1)-z = Mr(k)+z + t(k)z
                    for (int n = 0; n < AStar.np; ++n)
                    {
                        if (AStar.LPLUS[n, i] == 1)//if p_n is a post-place of the transition t_i
                        {
                            //All token remaining times in R(p_n, .) move one step to the right
                            for (int j = AStar.MAX_TOK_PA  - 1; j > 0; --j)                   
                                    MrF[n, j] = MrZ[n, j - 1];

                            //Add the operation time of the place to the first entry of R(p_n,.).
                            MrF[n, 0] = AStar.operationTimes[n];
                        }
                        else
                        {
                            for (int j = 0; j < AStar.MAX_TOK_PA; ++j)
                                MrF[n, j] = MrZ[n, j];
                        }
                    }




                    double g = FgValue + delt;
                    double h = Calculate(hmethod, ep2, hValueStartNode);
                    double f = (double)g + h;

                    double hF=CalculateHF(2);//计算子节点的hF,这里未关联参数！！
                    //CalculateHF(int method) hF1=max{ei(m)}; h2=-dep(m)
                    

                    AStarNode NewNode = new AStarNode(this, GoalNode, g, h, f, MF, MrF, i, FMarkingDepth + 1, hF, delt);
                    //AStarNode(父节点, 目标节点, g值, h值, f值, 节点的标志, 该标识下所有库所的剩余处理时间, 产生本标识所实施的变迁, 标志的深度, 从父标识到变迁实施得到本标识所用时间)
                    ASuccessors.Add(NewNode);
                }

            }//for循环结束 the end of the for structure.

        }


        public virtual void PrintNodeInfo(int loop) //打印当前节点的信息  Print the info. of the current node
        {
            Console.Write("loop:{0}\tf:{1}\tg:{2}\th:{3}\ttFireFrom:{4}\tDepth:{5} ", loop, Math.Round(FfValue, 0), FgValue, Math.Round(FhValue, 0), FTFireFrom + 1, FMarkingDepth);
            

            Console.Write("tEnabled:");
            for (int n = 0; n < EnabledTransitions.Length; ++n)
            {
                if (EnabledTransitions[n] == 1)
                    Console.Write("{0} ", n + 1);
            }
            Console.Write("\tM:");
            for (int i = 0; i < FM.Length; ++i)//输出M中为1的palce
            {
                if (FM[i] == 1)
                    Console.Write("{0} ", i + 1);
                if (FM[i] > 1)
                    Console.Write("{0}({1})", i + 1, FM[i]);
            }
            Console.Write("\tR:");
            for (int n = 0; n < AStar.np; ++n)
                for (int m = 0; m < AStar.MAX_TOK_PA; ++m)
                {

                    if (FR[n, m] != 0)

                        Console.Write("[{0}，{1}]:{2} ", n + 1, m + 1, FR[n, m]);

                }
            Console.WriteLine();
        }

        #endregion

        #region Overridden Methods

        public override bool Equals(object obj)
        {
            return IsSameState((AStarNode)obj);
        }

        public override int GetHashCode()
        {
            return base.GetHashCode();
        }

        #endregion

        #region IComparable Members

        public int CompareTo(object obj)
        {
            return (fValue.CompareTo(((AStarNode)obj).fValue));
        }

        #endregion
    }

    public sealed class AStar //Petri网模型运行所需的全局属性和行为
    {
        #region Private Fields
        private AStarNode FStartNode;//起始节点 the start node of the search
        private AStarNode FGoalNode;//目标节点 the goal node
        private Heap FOpenList;//Open列表 the OPEN list
        private Heap FClosedList;//Close列表 the CLOSED list
        private ArrayList FSuccessors;//子节点列表 the list to contain the child nodes
        private ArrayList FExpandedList;//已扩展节点列表 the list to contain expanded nodes
        private ArrayList FSolution;//结果方案列表 the list contains the nodes in the obtained schedule
        private int FNExpandedNode;//已扩展节点数 the number of expanded nodes
        #endregion

        #region Properties

        public static double[] operationTimes;//各库所的操作时间（资源库所操作时间为0） Operation times of places (for any resource place, it equals zero)

        public static int[,] LPLUS;//后置关联矩阵L+ The post-incidence matrix L+
        public static int[,] LMINUS;//前置关联矩阵L- The pre-incidence matrix L-

        public static int np;//Petri网中库所数(含资源)  The number of places in the net (including resource places)
        public static int nt;//Petri网中变迁数 The number of transitions in the net
        public static int nrs;//Petri网中资源库所数 The number of resource places

        public static int[] StartM;//开始节点的标识向量 The marking of the start node
        public static int[] GoalM;//目标节点的标识向量 The marking of the goal node
        public static double[,] StartMr;//开始节点的剩余处理时间矩阵 The token remaining time matrix of the start node
        public static double[,] GoalMr;//目标节点的剩余处理时间矩阵 The token remaining time matrix of the end node
        public static double[,] WRT;
        public static double[,] MrF;
        public static int MAX_TOK_PA; //活动库所的最大容量 The maximal number of tokens in any activity place. It will be set automatically by analyzing the input files.


        public ArrayList Solution//结果方案列表 A list containing the obtained schedule
        {
            get
            {
                return FSolution;
            }
        }
        public int NExpandedNode//已扩展节点数 The number of expanded nodes
        {
            get
            {
                return FNExpandedNode;
            }
            set
            {
                FNExpandedNode = value;
            }
        }

        //private ArrayList ChildrenInOpenList = new ArrayList();//ArrayList 可动态增加的数组

        #endregion

        #region Constructors

        public AStar(string initfile, string matrixfile)//构造函数
        {
            FOpenList = new Heap();
            FClosedList = new Heap();
            FSuccessors = new ArrayList();
            FSolution = new ArrayList();
            FExpandedList = new ArrayList();

            Read_initfile(initfile);
            Read_matrixfile(matrixfile);



            Console.WriteLine("Petri网中库所数(含资源) The number of places (including resource places)：" + np);
            Console.WriteLine("Petri网中变迁数 The number of transitions：" + nt);
            Console.WriteLine("Petri网中资源库所数 The number of resource places：" + nrs);
            Console.WriteLine("初始标识 The initial marking：");

            for (int i = 0; i < np; i++)
            {
                Console.Write(StartM[i] + " ");
            }
            Console.WriteLine();
            Console.WriteLine("操作的时间 Operation times：");
            for (int i = 0; i < np; i++)
            {
                Console.Write(operationTimes[i] + " ");
            }
            Console.WriteLine();
            Console.WriteLine("目标标识 The goal marking：");
            for (int i = 0; i < np; i++)
            {
                Console.Write(GoalM[i] + " ");
            }
            Console.WriteLine();
            Console.WriteLine("后置伴随矩阵 The post-incidence matrix L+：");
            for (int i = 0; i < np; ++i)
            {
                for (int j = 0; j < nt; ++j)
                {
                    Console.Write(LPLUS[i, j] + " ");
                }
                Console.WriteLine();
            }
            Console.WriteLine();
            Console.WriteLine("前置伴随矩阵 The pre-incidence matrix L-：");
            for (int i = 0; i < np; ++i)
            {
                for (int j = 0; j < nt; ++j)
                {
                    Console.Write(LMINUS[i, j] + " ");
                }
                Console.WriteLine();
            }
            Console.WriteLine();


            StartMr = new double[np, AStar.MAX_TOK_PA];
            GoalMr = new double[np, AStar.MAX_TOK_PA];
            for (int i = 0; i < np; ++i)
                for (int j = 0; j < AStar.MAX_TOK_PA; ++j)
                {
                    StartMr[i, j] = 0;
                    GoalMr[i, j] = 0;
                }

        }

        #endregion

        #region Private Methods

        private static void Read_initfile(string filename)
        {
            StreamReader SR;
            try
            {
                SR = File.OpenText(filename);
            }
            catch
            {
                Console.Write(filename + " open failed!");
                return;
            }
            string S;
            string[] SubS;

            //init文件的第一行  The first line of the init.txt
            {
                S = SR.ReadLine();
                SubS = S.Split(new char[] { ' ' });//string[]不指定大小就可以使用

                //Petri网中库所数(含资源)
                np = SubS.Length;

                //初始marking
                StartM = new int[np];
                for (int i = 0; i < SubS.Length; ++i)
                {
                    StartM[i] = Convert.ToInt32(SubS[i]);
                }
            }


            //init文件的第二行 The second line of the init.txt
            {
                S = SR.ReadLine();
                SubS = S.Split(new char[] { ' ' });

                //Petri网中资源库所数 the number of resource places in the net
                nrs = 0;

                operationTimes = new double[np]; //各库所的操作时间
                for (int i = 0; i < SubS.Length; ++i)
                {
                    if (Convert.ToInt32(SubS[i]) != 0)
                    {
                        operationTimes[i] = Convert.ToInt32(SubS[i]);
                        //   nrs++;
                    }
                }
            }

            //init文件的第三行 the third line of the init.txt
            {
                S = SR.ReadLine();
                SubS = S.Split(new char[] { ' ' });

                //目标marking
                GoalM = new int[np];
                for (int i = 0; i < SubS.Length; ++i)
                {
                    GoalM[i] = Convert.ToInt32(SubS[i]);
                }
            }
            
            for (int i = 0; i < SubS.Length; ++i)
            {
                if(i==0)
                {
                    MAX_TOK_PA = 0;//111
                }
                if (StartM[i] != 0)
                {
                    if (StartM[i] == GoalM[i])
                    {
                        nrs++;
                        if (MAX_TOK_PA < StartM[i])//在读取PN输入文件时自动计算资源库所最大容量; MAX_TOK_PA will be set automatically by analyzing the input files.
                            MAX_TOK_PA = StartM[i];
                    }
                }

            }
            SR.Close();

            return;
        }

        private static void Read_matrixfile(string filename)
        {
            StreamReader SR;
            try
            {
                SR = File.OpenText(filename);
            }
            catch
            {
                Console.Write(filename + " open failed!");
                return;
            }
            string S;

            //Petri网中变迁数 the number of transitions in the net
            nt = 0;

            S = SR.ReadLine();
            while (S != null)
            {
                ++nt;
                S = SR.ReadLine();
            }
            SR.Close();

            StreamReader SRR;
            try
            {
                SRR = File.OpenText(filename);
            }
            catch
            {
                Console.Write(filename + " open failed!");
                return;
            }

            //临时矩阵 nt * np
            int[,] temp = new int[nt, np];

            S = SRR.ReadLine();
            string[] SubS;
            int n = 0;
            while (S != null)
            {
                SubS = S.Split(new char[] { ' ' });
                for (int i = 0, j = 0; i < SubS.Length && j < np; ++i)
                {
                    if (SubS[i].Equals("1"))
                    {
                        temp[n, j] = 1;
                        ++j;
                    }
                    else if (SubS[i].Equals("0"))
                    {
                        temp[n, j] = 0;
                        ++j;
                    }
                    else if (SubS[i].Equals("-1"))
                    {
                        temp[n, j] = -1;
                        ++j;
                    }
                }
                S = SRR.ReadLine();
                n++;
            }


            //伴随矩阵L+
            LPLUS = new int[np, nt];

            //伴随矩阵L-
            LMINUS = new int[np, nt];

            for (int i = 0; i < nt; ++i)
            {
                for (int j = 0; j < np; ++j)
                {
                    if (temp[i, j] == 1)
                    {
                        LPLUS[j, i] = 1;
                    }
                    else
                    {
                        LPLUS[j, i] = 0;
                    }

                    if (temp[i, j] == -1)
                    {
                        LMINUS[j, i] = 1;
                    }
                    else
                    {
                        LMINUS[j, i] = 0;
                    }
                }
            }

            SRR.Close();
            return;
        }

        // HList按FfValue排好序了，将Node插入相同FfValue的第一个位置
        private int SortAdd(Heap HList, AStarNode Node)//将节点插入到相同FfValue值的第一个位置
        //Insert a node into HList as the first element of the nodes with same FfValue. 
        //The nodes in HList are ranked in a non-decreasing order of f-values. 
        {
            int position = 0;
            for (int i = 0; i < HList.Count; ++i)
            {
                AStarNode LNode = (AStarNode)HList[i];
                if (LNode.fValue >= Node.fValue)
                    break;
                else
                    ++position;
            }
            if (position == HList.Count)
                HList.Add(Node);//加到末尾处
            else
                HList.Insert(position, Node);
            return position;
        }

        private void PrintNodeList(object ANodeList)//输出某列表中所有节点的信息  Print the info. of all nodes in a given list. 
        {
            Console.WriteLine("\nNode list:");
            int i = 0;
            foreach (AStarNode n in (ANodeList as IEnumerable))
            {
                Console.Write("{0})\t", i + 1);
                i++;
                n.PrintNodeInfo(0);
            }
            Console.WriteLine("=============================================================");
        }

        #endregion

        #region Public Methods

        public void PrintNumberOfOpenNodes()//用于向屏幕输出open节点数  //output the number of nodes in OPEN to your screen.
        {
            Console.WriteLine("The number of nodes in OPEN: {0}", FOpenList.Count);
        }

        //向屏幕输出，并写文件result.txt  //Output the results to your screen and a file result.txt.
        public void PrintSolution()
        {
            Console.WriteLine("************* The obtained schedule： ***********");
            PrintNodeList(FSolution);//向屏幕输出FSolution	//Output the obtained schedule to the screen		
            Console.WriteLine("The number of expanded markings:{0}", FExpandedList.Count);

            
            FileStream ostrm;
            StreamWriter writer;
            TextWriter oldOut = Console.Out;
            try
            {
                ostrm = new FileStream("./result.txt", FileMode.Create, FileAccess.Write);
                writer = new StreamWriter(ostrm);
            }
            catch (Exception e)
            {
                Console.WriteLine(e.Message);
                Console.WriteLine("Cannot open result.txt to write results!");
                return;
            }
            Console.SetOut(writer);
            Console.WriteLine("************* The obtained schedule： ***********");
            PrintNodeList(FSolution);//向文件输出FSolution	//output FSolutio to result.txt.


            Console.WriteLine("************* FExpandedList ***********");
            Console.WriteLine("The number of expanded markings:{0}", NExpandedNode);//
            PrintNodeList(FExpandedList);//向文件输出FExpandedList

            Console.WriteLine("************* OpenList ***********");
            PrintNodeList(FOpenList);//向文件输出FOpenList


            Console.SetOut(oldOut);
            writer.Close();
            ostrm.Close();
            Console.WriteLine("Results have been written into result.txt!");

        }

        public void FindPath(AStarNode AStartNode, AStarNode AGoalNode, double ep, double ep2, int hmethod, int hFmethod, int opensize, bool printScreen)
        {
            //hmethod:所用启发函数h  //hmethod: the used heuristic function:
            //h1=max{ei(m)} plus R; max{ei(m)} comes from Xiong98.
            //h2=0;
            //h4=-dep(m);
            //h7 = h_H that is from Chapter 9 of our book;
            //h9=hs+max{ei(m)}+he in which max{ei(m)} comes from Xiong98, hs denotes the necessary time before the resource is used, and he denotes the necessary time after the resource is used.
            //opensize: 
            //printScreen:是否向屏幕打印每个扩展节点的信息 //printScreen: whether or not to output every expanded node to your screen
            //ep: the parameter epsilon used in Chapter 9 in our book.
            //ep<0时表示没有ep的情况  ep<0 indicates the A* search does not use the epsilon. 
            //ep=0时，选OPEN中具有相同最小f值marking中有最小hFCost的(0比-1好)
            //ep>0时选择范围更大,选OPEN中具有不大于最小f值1+ep倍的marking中有最小hFCost的
            //ep>=0 indicates the A* search picks out the node with the minimal hFCost value for expansion among the nodes having the f-value between f_min and f_min*(1+ep) in OPEN.
            //opensize: the maximal number of nodes in OPEN. 
            //opensize=0 denotes unlimited. opensize>0 denotes the A* search will use the BF locally and BT globally as described in Chapter 10 of our book.
            //pe2s={0}

            FStartNode = AStartNode;
            FGoalNode = AGoalNode;

            FOpenList.Clear();
            FClosedList.Clear();
            FSuccessors.Clear();
            FSolution.Clear();
            FExpandedList.Clear();
            NExpandedNode = 0;
            

            int loop = 0;
            FOpenList.Add(FStartNode);//将初始标识放入OPEN表中zzx  Put the initial marking into OPEN.

            //计算起始节点的h值  the h-value of the start node
            double hValueStartNode = 0;

            if (hmethod == 7)
            {
                /*
                //===================================== start of ChenFig5 =====================================
                const int ResNum = 6; //the number of resource places

                double[] ResourceTime = new double[ResNum];
                for (int i = 0; i < ResourceTime.Length; ++i)
                {
                    ResourceTime[i] = 0;
                }

                double[,] WRT =
                 {
                   {0,0,3,0,7,5 }, {0,0,3,0,4,5 }, {0,0,3,0,4,5 }, {0,0,3,0,4,5 }, {0,0,3,0,0,5 }, {0,0,0,0,0,5 }, {0,0,0,0,0,0 },
                   {0,3,0,4,9,2 }, {0,3,0,4,9,0 }, {0,3,0,0,9,0 }, {0,3,0,0,5,0 }, {0,0,0,0,5,0 }, {0,0,0,0,0,0 }, {0,0,0,0,0,0 },
                     {0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0}
               };

                //===================================== end of ChenFig5 =====================================
                */
                /*
                 //===================================== start of xiong98 =====================================
                 const int ResNum = 3; //the number of resource places
                 double[] ResourceTime = new double[ResNum];
                 for (int i = 0; i < ResourceTime.Length; ++i)
                 {
                     ResourceTime[i] = 0;
                 }
                 double[,] WRT =
                         {
                            {2,3,4},{0,3,4},{0,3,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                            {2,2,4},{2,2,0},{2,2,0},{0,2,0},{0,2,0},{0,0,0},{0,0,0},
                            {3,3,5},{0,3,5},{0,3,5},{0,3,0},{0,3,0},{0,0,0},{0,0,0},
                            {3,3,4},{3,0,4},{3,0,4},{3,0,0},{3,0,0},{0,0,0},{0,0,0},
                            {0,0,0},{0,0,0},{0,0,0}
                        };
                 //===================================== end of xiong98 =====================================
                 */
                /*
                   //===================================== start of New4x3 =====================================
                   const int ResNum = 3; //the number of resource places
                   int[] ResourceTime = new int[ResNum];//每个资源库所的所有标识的剩余处理时间
                   for (int i = 0; i < ResourceTime.Length; ++i)
                   {
                       ResourceTime[i] = 0;
                   }

                   int[,] WRT =
                   {
                        {5,4,4},{0,4,4},{0,4,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                        {2,2,5},{2,0,5},{2,0,5},{2,0,0},{2,0,0},{0,0,0},{0,0,0},
                        {2,5,5},{2,5,0},{2,5,0},{0,5,0},{0,5,0},{0,0,0},{0,0,0},
                        {2,4,2},{2,4,0},{2,4,0},{2,0,0},{2,0,0},{0,0,0},{0,0,0},
                        {0,0,0},{0,0,0},{0,0,0}
                    };
                   //===================================== start of New4x3 =====================================
                   */




                
                //===================================== start of ChenFig6 =====================================
                const int ResNum = 7; //the number of resource places
                double[] ResourceTime = new double[ResNum];
                for (int i = 0; i < ResourceTime.Length; ++i)
                {
                    ResourceTime[i] = 0;
                }

                double[,] WRT =
                {
                       {0,7,0,0,2,0,0},{0,5,0,0,2,0,0},{0,5,0,0,0,0,0},{0,0,0,0,0,0,0},{3,3,4,0,0,0,0},{0,3,4,0,0,0,0},
                       {0,6,4,0,1,0,0},{0,0,4,0,1,0,0},{0,0,4,0,0,0,0},{0,0,0,0,0,0,0},{0,3,4,0,0,0,2},{0,0,4,0,0,0,2},
                       {0,0,4,0,0,0,0},{2,4,6,0,0,3,1.5},{2,4,0,0,0,3,1.5},{2,4,0,0,0,3,0},{2,0,0,0,0,3,0},{2,0,0,0,0,0,0},
                       {0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},
                       {0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0}
                    };
                //===================================== end of ChenFig6 =====================================
                
                


                /*
                   //===================================== start of Huang2012Fig1Revised =====================================
                   const int ResNum = 3; //the number of resource places
                   double[] ResourceTime = new double[ResNum];//每个资源库所的所有标识的剩余处理时间
                   for (int i = 0; i < ResourceTime.Length; ++i)
                   {
                       ResourceTime[i] = 0;
                   }

                   double[,] WRT = { {57,0,42.5}, {57,0,42.5} , {57,0,42.5}, {57,0,42.5},{57,0,0}, {57,0,0}, {0,0,0}, {0,0,51}, {0,0,51}, {0,0,0}, {0,0,0},
                                       {0,95,0}, {0,0,0}, {0,0,0}, {0,0,0}, {0,0,0}, {0,0,0}, {0,0,0}, {0,0,0}, {0,0,0},
                                       {0,78,37.5}, {0,0,37.5}, {0,0,37.5}, {0,0,0}, {0,0,0}, {0,0,0}, {0,70,0}, {0,70,0}, {0,0,0}, {0,0,0},
                                       {93,0,87.5}, {93,0,38}, {93,0,38}, {93,0,0}, {93,0,0}, {0,0,0}, {0,0,0}, {0,0,0}, {0,0,0}, {0,0,0} };
                   //===================================== start of Huang2012Fig1Revised =====================================
                */




                /*
                   //===================================== start of Huang2012Fig1 =====================================
                   const int ResNum = 3; //the number of resource places
                   double[] ResourceTime = new double[ResNum];//每个资源库所的所有标识的剩余处理时间
                   for (int i = 0; i < ResourceTime.Length; ++i)
                   {
                       ResourceTime[i] = 0;
                   }

                   int[,] WRT = { {57,0,85 }, {57,0,85 } , {57,0,85 }, { 57,0,85},{57,0,0 }, {57,0,0 }, { 0,0,0}, { 0,0,51}, {0,0,51 }, {0,0,0 }, {0,0,0 },
                                       {0,95,0 }, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0},
                                       {0,78,75 }, {0,0,75 }, { 0,0,75}, {0,0,0 }, {0,0,0 }, {0,0,0 }, { 0,70,0}, {0,70,0 }, { 0,0,0}, { 0,0,0},
                                        { 93,0,175}, {93,0,76 }, { 93,0,76}, { 93,0,0}, { 93,0,0}, { 0,0,0 }, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0} };

                   //===================================== start of Huang2012Fig1 =====================================
                   */
                   //用1(xiong)=max{ei(m)}计算起始节点的h值(也等于起始节点的f值)，hValueStartNode用于h12(IDW)=h(M)+ep *h(M),h(M)=h1;时计算M子节点的h!!!!!!!!!!!!!!!!!!!!!!
                for (int n = 0; n < AStar.np - AStar.nrs; ++n)//除资源外的place数
                {
                    if (FStartNode.M[n] != 0)
                        for (int x = 0; x < ResourceTime.Length; ++x)
                        {
                            ResourceTime[x] += FStartNode.M[n] * WRT[n, x];
                        }
                }

                double max = 0;
                for (int c = 0; c < ResourceTime.Length; ++c)
                    if (max < ResourceTime[c])
                        max = ResourceTime[c];
                hValueStartNode = max;
            }


            while (FOpenList.Count >= 0)
            {
                loop++;

                if (FOpenList.Count == 0)//若OPEN表为空，程序异常退出 If OPEN is empty, exit with failure.
                {
                    Console.WriteLine("******* Open is null. Exit with failure! ********");
                    break;
                }


                //   if (!( ep >= 0))
                //  {
                //      Console.WriteLine("You should input the right value of ep!");
                //      break;
                //   }


                //取OPEN列表中的第一个节点  Get the first node in OPEN. 
                AStarNode NodeCurrent = (AStarNode)FOpenList[0];

                if (ep < 0)          
                    FOpenList.Remove(FOpenList[0]); //除去要扩展的节点 Remove the first node from OPEN. 
                


                if (ep >= 0)//即ep>=0,使用 search effort estimate
                {   //ep=0时，选OPEN中具有相同最小f值marking中有最小hFCost的
                    //ep>0时选择范围更大,选OPEN中具有不大于最小f值1+ep倍的marking中有最小hFCost的
                    int i = 0;
                    //FFOCALList.Clear();
                    AStarNode N = (AStarNode)FOpenList[0];//OPEN列表上的第一个节点
                    double fMin = N.fValue;//总代价
                    double minhF = N.hFCost;//节点的深 度
                    double minDelt = N.Delt;
                    int index = 0;


                    while (i < FOpenList.Count - 1 && N.fValue <= (double)(1 + ep) * fMin)
                    {

                        //FFOCALList.Add(N);
                        if (minhF > N.hFCost)
                        {
                            minhF = N.hFCost;
                            minDelt = N.Delt;
                            index = i;
                        }

                        /*if(minhF==N.hFCost && minDelt>N.Delt)
						{//相同hF的marking使用minimum delt 作为tie-breaking
							minDelt=N.Delt;
							index=i;
						}*/
                        i++;
                        N = (AStarNode)FOpenList[i];
                    }

                    NodeCurrent = (AStarNode)FOpenList[index];
                    FOpenList.Remove(FOpenList[index]); //已经将要扩展的节点移走了
                }//if(ep>=0)

                

                //如果当前节点是目的节点，则回溯构造出路径  If the current node equals the goal node, construct a schedule from the goal node to the initial node.
                if (NodeCurrent.IsGoal())                 
                {
                    while (NodeCurrent != null)
                    {
                        FSolution.Insert(0, NodeCurrent);
                        NodeCurrent = NodeCurrent.Parent;
                    }
                    break; //程序正常退出 The program exist with success. 
                }

                //把当前节点的所有子节点加入到FSuccessors  Add the child nodes of the current node to the list FSuccessors.
                FSuccessors.Clear();
                NodeCurrent.GetSuccessors(FSuccessors, hmethod, ep2, hValueStartNode);


                if (printScreen == true)
                    NodeCurrent.PrintNodeInfo(loop);//打印当前节点的信息 Print the node of the current node.
                //    if (printScreen == true)
                //if (loop==916)//loop >= 915 && loop <= 917)///
                // {//
                //             NodeCurrent.PrintNodeInfo(loop);//打印当前节点的信息
                //   foreach (AStarNode a in FOpenList)//
                //         {//
                //    a.PrintNodeInfo(-1);//
                //           }//
                //   }//

                foreach (AStarNode NodeSuccessor in FSuccessors)                
                {

                    //如果子节点S'和OPEN中某节点S有相同M和Mr,但g'<g,则用S'替换Open中S 
                    //If the successor has the same M and R as a node in OPEN, but has smaller g-value, then replace the node in OPEN with the successor.
                              
                    AStarNode NodeOpen = null;                     
                    foreach (AStarNode anode in FOpenList)
                    {
                        if (anode.IsSameStatePlusMr(NodeSuccessor))
                        {
                            NodeOpen = anode;
                            break;
                        }
                    }       
                    
                    if (NodeOpen != null) //
                    {
                        if (NodeSuccessor.gValue < NodeOpen.gValue)
                        {
                            FOpenList.Remove(NodeOpen);
                            SortAdd(FOpenList, NodeSuccessor);                            
                            continue;
                        }
                    }


                    //如果子节点S'和Closed中某节点S有相同M和Mr,但g'<g,则删掉CLOSED的S，并将S'插入到Open
                    //If the successor has the same M anr Mr as a node in CLOSED but has smaller g-value, then delete the node in Closed and insert the successor into OPEN.
                    AStarNode NodeClosed = null;
                    foreach (AStarNode anode in FClosedList)
                    {
                        if (anode.IsSameStatePlusMr(NodeSuccessor))
                        {
                            NodeClosed = anode;
                            break;
                        }
                    }

                    
                    if (NodeClosed != null)
                    {
                        if (NodeSuccessor.gValue < NodeClosed.gValue)
                        {
                            FClosedList.Remove(NodeClosed);
                            SortAdd(FOpenList, NodeSuccessor);
                            continue;
                        }
                    }

                    //If there exists no state in OPEN and CLOSED as the successor, insert the successor into OPEN. //!!!New paper.
                    if(NodeOpen ==null && NodeClosed ==null)
                    {
                        SortAdd(FOpenList, NodeSuccessor);
                    }
                } //The end of foreach (AStarNode NodeSuccessor in FSuccessors)

                SortAdd(FClosedList, NodeCurrent);
                ++NExpandedNode;//已扩展节点数

                FExpandedList.Add(NodeCurrent); 
            }// The end of while (FOpenList.Count > 0)

            /*AStarNode FinalMarking = (AStarNode)FSolution[FSolution.Count - 1];

            double[] result = new double[4];
            result[0] = (double)FinalMarking.fValue;//最后结果的cost
            result[1] = (double)FExpandedList.Count;//最后EXPANDED表的长度
            result[2] = (double)FOpenList.Count;//最后OPEN表的长度
            result[3] = (double)FClosedList.Count;//最后CLOSE表的长度

            result[1] = NExpandedNode;
            Console.WriteLine("result:", result);
            for (int i = 0; i < 4; ++i)
            {
                Console.Write(result[i] + " ");
            }
            return result*/

        }//FindPath

        #endregion
    }
}