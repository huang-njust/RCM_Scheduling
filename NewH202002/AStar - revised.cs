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
    public static class common //含时间库所托肯最大值 zzx
    {
        private static int LL = 0;
        public static int L
        {
            get
            {
                return LL;
            }
            set
            {
                LL = value;
            }
        }
    }


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

        public double  g //g value of a node (The accumulative cost of the path until now.)
        {
            set
            {
                Fg = value;
            }
            get
            {
                return Fg;
            }
        }
        private double  Fg;

        public double  h //h value of a node (The estimated minmal cost to the goal from here.)
        {
            set
            {
                Fh = value;
            }
            get
            {
                return Fh;
            }
        }
        private double  Fh;

        public double f //f value of a node(f=g+h, representing an estimated of the lowest cost from the initial node to the goal along a path through the current node)
        {
            set
            {
                Ff = value;
            }
            get
            {
                return Ff;
            }
        }
        private double  Ff;

        public int[] M//the marking of node in the reachability graph
        {
            get
            {
                return FM;
            }
        }
        private int[] FM;

        public double [,] R//the token remaining time matrix of a place-timed Petri net
        {
            get
            {
                return FR;
            }
        }
        private double[,] FR;

        public int TFireFrom//the transition whose firing generates the node
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

        public int[] EnabledTransitions//the set of transitions that are enabled at the node
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

        public int MarkingDepth//the depth of the node, i.e., the number of transition firings from the initial node to the curren node
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

        public double  hFCost
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
        private double  FhFCost;

        public double  Delt//从父标识到某变迁实施得到本标识所用时间
        {//从父marking到transition实施得到本marking所需时间
            set
            {
                FDelt = value;
            }
            get
            {
                return FDelt;
            }
        }
        private double  FDelt;

        //private int[] u = new int[AStar.nt];//控制向量u
        private double delt = 0;//变迁变为可实施所需时间

        //通过变迁的发射放入输出库所中的托肯必须等待一定时间后才可利用，并且该时间等于该库所的时延
        // M(k)- 和 Mr(k)- 分别表示：变迁发射前，那刻 "系统的标识" 和 "剩余处理时间向量"
        // M(k)+ 和 Mr(k)+ 分别表示：变迁发射后，输入托肯已移走但输出托肯还未加入时 "系统的标识" 和 "剩余处理时间向量"
        private int[] MF = new int[AStar.np];//标识状态M(k)-
        private int[] MZ = new int[AStar.np];//标识状态M(k)+
        private double [,] MrF = new double [AStar.np, common.L];//标识状态Mr(k)- ///zzx
        public  double [,] MrZ = new double [AStar.np, common.L];//标识状态Mr(k)+	  
        public int[] temparray = new int[AStar.np];
        #endregion

        #region Constructors
        //AStarNode(父节点, 目标节点, g值, h值, f值, 节点的标志, 该标识下所有位置的剩余处理时间, 产生本标识所实施的变迁, 标志的深度, 从父标识到变迁实施得到本标识所用时间)
        public AStarNode(AStarNode AParent, AStarNode AGoalNode, double  ACost, double Ag, double  Af, int[] AM, double[,] AMr, int ATFireFrom, int AMarkingDepth, double  AhFCost, double  ADelt)
        {
            FParent = AParent;
            FGoalNode = AGoalNode;
            Fg = ACost;
            Fg = Ag;
            Ff = Af;
            FM = new int[AStar.np];
            Array.Copy(AM, FM, AM.Length);
            FR = new double[AStar.np, common.L];
            Array.Copy(AMr, FR, AMr.Length);
            FTFireFrom = ATFireFrom;
            FEnabledTransitions = new int[AStar.nt];
            FMarkingDepth = AMarkingDepth;
            FhFCost = AhFCost;
            FDelt = ADelt;
        }
        #endregion
        #region Public Methods

        public bool IsGoal()//zzx
        {//判断本节点的M和Mr是否与GoalNode一致
            if (IsSameStatePlusMr(FGoalNode) == false)//判断M和Mr是否相等
                return false;
            for (int i = 0; i < this.R.GetLength(0); ++i)
                for (int j = 0; j < this.R.GetLength(1); ++j)
                    if (this.R[i, j] != FGoalNode.R[i, j])
                        return false;
            return true;
        }

        public virtual bool IsSameState(AStarNode ANode)//判断某节点的标识M是否和本节点一致
        {//只判断M
            if (ANode == null)
                return false;
            if (FM.Length != ANode.FM.Length)
                return false;
            for (int i = 0; i < FM.Length; ++i)
                if (FM[i] != ANode.FM[i])
                    return false;
            return true;
        }

        public virtual bool IsSameStatePlusMr(AStarNode ANode)//判断某节点的M和Mr是否和本节点一致
        {//判断M和Mr
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
                    if (this.R[i, j] != FGoalNode.R[i, j])
                        return false;
                }
            return true;
        }

        public virtual double Calculate(int method,double ep2, double StartNodeF)//Calculates the estimated cost for the remaining trip to the goal.
        //h1=max{ei(m)};
        //h2=0;
        //h4=-dep(m);
        {

            //h=max{ei(m)} where ei(m) is the sum of operation times of those remaining operation for all jobs
            //which are planned to be processed on the ith machine when the current system state is represented 
            //by the marking m 
            if (method == 1)
                
            {

                /*
                 //===================================== start of New4x3 =====================================
                 const int ResNum = 3; //三个资源库所
                 int[] MachineTime = new int[ResNum];//每个资源库所的所有标识的剩余处理时间
                 for (int i = 0; i < MachineTime.Length; ++i)
                 {
                     MachineTime[i] = 0;
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
                    for (int m = 0; m < common.L; ++m)
                    {
                     if (MrF[n,m] != 0)
                     {
                         if (n == 1 || n == 12 || n == 17 || n == 26)
                             MachineTime[0] += (int)MrF[n,m];
                         else if (n == 3 || n == 8 || n == 19 || n == 24)
                             MachineTime[1] += (int)MrF[n,m];
                         else if (n == 5 || n == 10 || n == 15 || n == 22)
                             MachineTime[2] +=  (int)MrF[n,m];
                     }
                 }
                //===================================== end of New4x3 =====================================

                */
               
                //===================================== start of ChenFig5 =====================================
                const int ResNum = 6; //六个资源库所
                int[] MachineTime = new int[ResNum];
                for (int i = 0; i < MachineTime.Length; ++i)
                {
                    MachineTime[i] = 0;
                }

                int[,] WOT =
                {
                  {0,0,3,0,7,5 }, {0,0,3,0,4,5 }, {0,0,3,0,4,5 }, {0,0,3,0,4,5 }, {0,0,3,0,0,5 }, {0,0,0,0,0,5 }, {0,0,0,0,0,0 },
                  {0,3,0,4,9,2 }, {0,3,0,4,9,0 }, {0,3,0,0,9,0 }, {0,3,0,0,5,0 }, {0,0,0,0,5,0 }, {0,0,0,0,0,0 }, {0,0,0,0,0,0 },
                    {0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0}
                 };

                //加Mr
                for (int n = 0; n < AStar.np; ++n)
                    for (int m = 0; m < common.L; ++m)
                    {
                    if (MrF[n,m] != 0)
                    {
                        if (n == 9)
                            MachineTime[0] += (int)MrF[n,m];
                        else if (n == 11 || n == 2)
                            MachineTime[1] += (int)MrF[n,m];
                        else if (n == 1 || n == 4 || n == 10 || n == 12)
                            MachineTime[4] += (int)MrF[n,m];
                       else if (n == 6 || n == 8)
                            MachineTime[5] += (int)MrF[n,m];
                        else if (n == 3)
                            MachineTime[3] += (int)MrF[n,m];
                        else if (n == 5)
                            MachineTime[2] += (int)MrF[n,m];
                    }
                }
                //===================================== end of ChenFig5 =====================================
                /*
                      //===================================== start of ChenFig6222 =====================================
                      const int ResNum = 7; //三个资源库所
                      double [] MachineTime = new double [ResNum];
                      for (int i = 0; i < MachineTime.Length; ++i)
                      {
                          MachineTime[i] = 0;
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
                           for (int m = 0; m < common.L; ++m)
                           {
                               if (MrF[n, m] != 0)
                               {
                                   if (n == 5)
                                       MachineTime[0] += (double)MrF[n, m];
                                   else if (n == 2 || n == 8)
                                       MachineTime[1] += (double)MrF[n, m];
                                   else if (n == 10 || n == 17)
                                       MachineTime[2] += (double)MrF[n, m];
                                   else if (n == 12 || n == 15)
                                       MachineTime[3] += (double)MrF[n, m];
                                   else if (n == 5 || n == 18)
                                       MachineTime[4] += (double)MrF[n, m];
                                   else if (n == 1 || n == 3 || n == 7 || n == 11 || n == 16)
                                       MachineTime[5] += (double)MrF[n, m];
                                   else if (n == 9 || n == 14)
                                       MachineTime[6] += (double)MrF[n, m];
                               }
                           }*/

                //===================================== end of ChenFig6222 =====================================


                /*
                  //===================================== start of 1112 =====================================
                  const int ResNum = 2; //三个资源库所
                  double[] MachineTime = new double[ResNum];
                  for (int i = 0; i < MachineTime.Length; ++i)
                  {
                      MachineTime[i] = 0;
                  }

                  double[,] WRT = 
                  {
                          {1.5,2},{0,2},{0,0},{0,0},{2,1},
                          {2,0},{0,0},{0,0},{0,0},{0,0},
                  };

                  //加Mr
                /*  for (int n = 0; n < AStar.np; ++n)
                      for (int m = 0; m < common.L; ++m)
                      {
                          if (MrF[n, m] != 0)
                          {
                              if (n == 1||n == 6)
                                  MachineTime[0] += (double)MrF[n, m];
                              else if (n == 2 || n == 5 )
                                  MachineTime[1] += (double)MrF[n, m];                        
                          }
                      }

                 //===================================== end of 1112 =====================================
             */
                /*
                 //===================================== start of xiong98 =====================================
                 const int ResNum = 3; //三个资源库所
                 double[] MachineTime = new double[ResNum];
                 for (int i = 0; i < MachineTime.Length; ++i)
                 {
                     MachineTime[i] = 0;
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
                       for (int m = 0; m < common.L; ++m)
                       {
                       if (MrF[n,m] != 0)
                       {
                           if (n == 1 || n == 10 || n == 15 || n == 26)
                               MachineTime[0] += (int)MrF[n,m];
                           else if (n == 3 || n == 12 || n == 19 || n == 22)
                               MachineTime[1] += (int)MrF[n,m];
                           else if (n == 5 || n == 8 || n == 18 || n == 24)
                               MachineTime[2] += (int)MrF[n,m];
                       }
                   }*/
                //===================================== end of xiong98 =====================================


                //通用

                for (int n = 0; n < AStar.np; ++n)
                {
                    if (MF[n] != 0)
                    {
                        for (int x = 0; x < ResNum; ++x)
                        {
                            MachineTime[x] += MF[n] * WOT[n, x];
                        }
                    }
                }

                //h=max{ei(m)}
                double  max = 0;
                for (int i = 0; i < MachineTime.Length; ++i)
                {
                    if (max < MachineTime[i])
                    {
                        max = MachineTime[i];
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

            if(method == 6)//with R
            {
               
             //===================================== start of xiong98 =====================================
                const int ResNum = 3; //三个资源库所
                double[] MachineTime = new double[ResNum];
                for (int i = 0; i < MachineTime.Length; ++i)
                {
                    MachineTime[i] = 0;
                }
                  double[,] WRT =
                 {
                           {2,3,4},{0,3,4},{0,3,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                           {2,2,4},{2,2,0},{2,2,0},{0,2,0},{0,2,0},{0,0,0},{0,0,0},
                           {3,3,5},{0,3,5},{0,3,5},{0,3,0},{0,3,0},{0,0,0},{0,0,0},
                           {3,3,4},{3,0,4},{3,0,4},{3,0,0},{3,0,0},{0,0,0},{0,0,0},
                           {0,0,0},{0,0,0},{0,0,0}
                       };
       /*       double[,] WRT =
          {
        {2,1.5,4},{0,1.5,4},{0,1.5,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
        {2,1,4},{2,1,0},{2,1,0},{0,1,0},{0,1,0},{0,0,0},{0,0,0},
        {3,1.5,5},{0,1.5,5},{0,1.5,5},{0,1.5,0},{0,1.5,0},{0,0,0},{0,0,0},
        {3,1.5,4},{3,0,4},{3,0,4},{3,0,0},{3,0,0},{0,0,0},{0,0,0},
        {0,0,0},{0,0,0},{0,0,0}
                };*/
                //库所pi需要多少个资源r
               double[,] Upi =
                {
                    {0,0,0},{1,0,0},{0,0,0},{0,1,0},{0,0,0},{0,0,1},{0,0,0},
                    {0,0,0},{0,0,1},{0,0,0},{1,0,0},{0,0,0},{0,1,0},{0,0,0},
                    {0,0,0},{1,0,0},{0,0,0},{0,0,1},{0,0,0},{0,1,0},{0,0,0},
                    {0,0,0},{0,1,0},{0,0,0},{0,0,1},{0,0,0},{1,0,0},{0,0,0},
                    {0,0,0},{0,0,0},{0,0,0}
                };
                //手动计算资源库所的资源数量
                int[] stratm0 = new int[ResNum] { 1, 1, 1 };
                /*    for (int i = 0; i < MachineTime.Length; ++i)
                    {
                        stratm0[i] = AStar.StartM[28 + i];
                       // Console.Write("[{0}]{1}",i,stratm0[i]);
                      //  Console.WriteLine();
                    }*/

                //===================================== end of xiong98 =====================================
              
            /*
               //===================================== start of ChenFig6222 =====================================
               const int ResNum = 7; //三个资源库所
               double [] MachineTime = new double [ResNum];
               for (int i = 0; i < MachineTime.Length; ++i)
               {
                   MachineTime[i] = 0;
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
                int[] stratm0 = new int[ResNum] { 1,1,1,2,2,2,2 };
                //===================================== end of ChenFig6222 =====================================
              */
               //通用
                for (int n = 0; n < AStar.np; ++n)
                {
                    //取p_i中所有非零剩余时间之和
                    double temp = 0;
                    for (int t = 0; t < common.L; t++)
                    {
                        temp += MrF[n, t];
                    }
                  //  if(temp!=0)
                   // Console.Write("[{0}]{1}       ",n,temp);

                    if (MF[n] != 0)
                    {

                        for (int x = 0; x < ResNum; ++x)
                        {
                            MachineTime[x] += MF[n] * WRT[n, x];

                            MachineTime[x] += temp * Upi[n, x] / stratm0[x];
                         
                        }
                    }
                }
                //h=max{ei(m)}
                double max = 0;
                for (int i = 0; i < MachineTime.Length; ++i)
                {
                    if (max < MachineTime[i])
                    {
                        max = MachineTime[i];
                    }
                }
                Console.Write(max);
                Console.WriteLine();
                return max;
            }
            if (method == 7)//h函数为h_H    zhaozhixia
            {
              /*  
                //===================================== start of xiong98 =====================================
                const int ResNum = 3; //三个资源库所
                double[] MachineTime = new double[ResNum];
                for (int i = 0; i < MachineTime.Length; ++i)
                {
                    MachineTime[i] = 0;
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
                       int[] stratm0 = new int[ResNum] { 1, 1, 1 };
                       /*    for (int i = 0; i < MachineTime.Length; ++i)
                           {
                               stratm0[i] = AStar.StartM[28 + i];
                              // Console.Write("[{0}]{1}",i,stratm0[i]);
                             //  Console.WriteLine();
                           }*/

                //===================================== end of xiong98 =====================================

                /*/
                
                   //===================================== start of ChenFig6222 =====================================
                   const int ResNum = 7; //三个资源库所
                   double [] MachineTime = new double [ResNum];
                   for (int i = 0; i < MachineTime.Length; ++i)
                   {
                       MachineTime[i] = 0;
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
                    int[] stratm0 = new int[ResNum] { 1,1,1,2,2,2,2 };
                //===================================== end of ChenFig6222 =====================================
               */
                
                
               //===================================== start of ChenFig5 =====================================
               const int ResNum = 6; //六个资源库所
               double[] MachineTime = new double[ResNum];
               for (int i = 0; i < MachineTime.Length; ++i)
               {
                   MachineTime[i] = 0;
               }


                  double[,] WRT =
               {
                     /* {0,0,7,5,0,3},{0,0,4,5,0,3},{0,0,4,5,0,3},{0,0,4,5,0,3},{0,0,0,5,0,3},{0,0,0,5,0,0},{0,0,0,0,0,0},
                      {4,3,9,2,0,0},{4,3,9,0,0,0},{0,3,9,0,0,0},{0,3,5,0,0,0},{0,0,5,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},
                      {0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},*/
                           {0,0,3,0,7,5 }, {0,0,3,0,4,5 }, {0,0,3,0,4,5 }, {0,0,3,0,4,5 }, {0,0,3,0,0,5 }, {0,0,0,0,0,5 }, {0,0,0,0,0,0 },
                           {0,3,0,4,9,2 }, {0,3,0,4,9,0 }, {0,3,0,0,9,0 }, {0,3,0,0,5,0 }, {0,0,0,0,5,0 }, {0,0,0,0,0,0 }, {0,0,0,0,0,0 },
                             {0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0}
                       };
                      double[,] Upi =
                     {
                         /* {0,0,0,0,0,0,0},{0,0,1,0,0,0,0},{0,1,0,0,0,0,0},{0,0,0,0,0,1,0},{0,0,1,0,0,0,0},{0,0,0,0,0,0,1},{0,0,0,0,1,0,0},
                          {0,0,0,0,0,0,0},{0,0,0,0,1,0,0},{1,0,0,0,0,0,0},{0,0,1,0,0,0,0},{0,1,0,0,0,0,0},{0,0,1,0,0,0,0},{0,0,0,0,0,0,0},
                          {0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0}*/
                       {0,0,0,0,0,0},{0,0,0,0,1,0},{0,1,0,0,0,0},{1,0,0,0,0,0},{0,0,0,0,1,0},{0,0,1,0,0,0},{0,0,0,0,0,1},
                        {0,0,0,0,0,0},{0,0,0,0,0,1},{0,0,0,1,0,0},{0,0,0,0,1,0},{0,1,0,0,0,0},{0,0,0,0,1,0},{0,0,0,0,0,0},
                        {0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0}
                    };

                    int[] stratm0 = new int[ResNum] { 1, 1, 1, 1, 1, 1};
                       //===================================== end of ChenFig5 =====================================
                       
                       /*
                          //===================================== start of New4x3 =====================================
                          const int ResNum = 3; //三个资源库所
                          double[] MachineTime = new double[ResNum];//每个资源库所的所有标识的剩余处理时间
                          for (int i = 0; i < MachineTime.Length; ++i)
                          {
                              MachineTime[i] = 0;
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

                          int[] stratm0 = new int[ResNum] { 1, 1, 1};
                          //===================================== end of New4x3 =====================================
                          */
                /*
                                //===================================== start of 2012Fig1 =====================================
                                const int ResNum = 3; //六个资源库所
                                double[] MachineTime = new double[ResNum];//每个资源库所的所有标识的剩余处理时间
                                for (int i = 0; i < MachineTime.Length; ++i)
                                {
                                    MachineTime[i] = 0;
                                }

                                int[,] WRT = { {57,0,85 }, {57,0,85 } , {57,0,85 }, { 57,0,85},{57,0,0 }, {57,0,0 }, { 0,0,0}, { 0,0,51}, {0,0,51 }, {0,0,0 }, {0,0,0 },
                                                    {0,95,0 }, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0},
                                                    {0,78,75 }, {0,0,75 }, { 0,0,75}, {0,0,0 }, {0,0,0 }, {0,0,0 }, { 0,70,0}, {0,70,0 }, { 0,0,0}, { 0,0,0},
                                                     { 93,0,175}, {93,0,76 }, { 93,0,76}, { 93,0,0}, { 93,0,0}, { 0,0,0 }, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0} };
                                double[,] Upi = { { 0,0,0}, { 0, 0, 1 }, { 0, 1, 0 }, { 0, 0, 0 }, { 0, 0, 1 }, { 0, 0, 0 }, {1, 0, 0 }, { 1, 0, 0 }, { 0, 0, 0 }, { 0, 0, 1 }, { 0, 0, 0 },
                                                 { 0,0,0},{ 0,1,0},{ 0,0,0},{ 0,1,0},{ 0,0,1},{ 0,0,0},{ 1,0,0},{ 0,0,1},{ 0,0,0},
                                                   { 0,0,0},{ 0,1,0},{ 0,0,0},{ 0,0,1},{ 0,0,0},{ 1,0,0},{ 0,0,1},{ 0,0,0},{ 0,1,0},{ 0,0,0},
                                                   { 0,0,0},{ 0,0,1},{ 0,0,0},{ 0,0,1},{ 0,0,0},{ 1,0,0},{ 0,0,0},{ 0,0,0},{ 0,0,0},{ 0,0,0}};
                                int[] stratm0 = new int[ResNum] { 1, 1, 1 };
                                //===================================== start of 2012Fig1 =====================================
                             */   
/*
                //===================================== start of 2012Fig1新 =====================================
                const int ResNum = 3; //六个资源库所
                double[] MachineTime = new double[ResNum];//每个资源库所的所有标识的剩余处理时间
                for (int i = 0; i < MachineTime.Length; ++i)
                {
                    MachineTime[i] = 0;
                }

                double[,] WRT = { {57,0,42.5 }, {57,0,42.5 } , {57,0,42.5 }, { 57,0,42.5},{57,0,0 }, {57,0,0 }, { 0,0,0}, { 0,0,51}, {0,0,51 }, {0,0,0 }, {0,0,0 },
                                    {0,95,0 }, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0},
                                    {0,78,37.5 }, {0,0,37.5 }, { 0,0,37.5}, {0,0,0 }, {0,0,0 }, {0,0,0 }, { 0,70,0}, {0,70,0 }, { 0,0,0}, { 0,0,0},
                                     { 93,0,87.5}, {93,0,38 }, { 93,0,38}, { 93,0,0}, { 93,0,0}, { 0,0,0 }, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0} };
                double[,] Upi = { { 0,0,0}, { 0, 0, 1 }, { 0, 1, 0 }, { 0, 0, 0 }, { 0, 0, 1 }, { 0, 0, 0 }, {1, 0, 0 }, { 1, 0, 0 }, { 0, 0, 0 }, { 0, 0, 1 }, { 0, 0, 0 },
                                 { 0,0,0},{ 0,1,0},{ 0,0,0},{ 0,1,0},{ 0,0,1},{ 0,0,0},{ 1,0,0},{ 0,0,1},{ 0,0,0},
                                   { 0,0,0},{ 0,1,0},{ 0,0,0},{ 0,0,1},{ 0,0,0},{ 1,0,0},{ 0,0,1},{ 0,0,0},{ 0,1,0},{ 0,0,0},
                                   { 0,0,0},{ 0,0,1},{ 0,0,0},{ 0,0,1},{ 0,0,0},{ 1,0,0},{ 0,0,0},{ 0,0,0},{ 0,0,0},{ 0,0,0}};
                int[] stratm0 = new int[ResNum] { 1, 1, 2 };
                //===================================== start of 2012Fig1新 =====================================
                */
                //通用
                for (int n = 0; n < AStar.np-AStar .nrs; ++n)
                {
                    //取p_i中所有非零剩余时间之和
                    double temp = 0;
                    for (int t = 0; t < common.L; t++)
                    {
                        temp += MrF[n, t];
                    }

                    if (MF[n] != 0)
                    {

                        for (int x = 0; x < ResNum; ++x)
                        {
                            MachineTime[x] += MF[n] * WRT[n, x];
                            MachineTime[x] += temp * Upi[n, x] / stratm0[x];
                        }
                    }
                }
                //h=max{ei(m)}
                double max1 = 0;
                for (int i = 0; i < MachineTime.Length; ++i)
                {
                    if (max1 < MachineTime[i])
                    {
                        max1 = MachineTime[i];
                    }
                }

                double max = 0;
                //  max = max1 + ep2 * (1 - ((float)FMarkingDepth + 1) /32) * max1;//！！！！要修改总的深度！！！！！原函数
                // max= max1+ep2 * (System.Math.Sqrt(max1 / StartNodeF)) * max1;
                max = max1 + ep2 *(max1 / StartNodeF) * max1;
             //   max = max1+ep2*Math.Pow(max1 / StartNodeF, 1.0/4)* max1;//开方函数                
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
            if(method ==8)
            {
                /*
                 //===================================== start of New4x3 =====================================
                 const int ResNum = 3; //三个资源库所
                 int[] MachineTime = new int[ResNum];//每个资源库所的所有标识的剩余处理时间
                 for (int i = 0; i < MachineTime.Length; ++i)
                 {
                     MachineTime[i] = 0;
                 }

                 int[,] WRT =
                 {
                     {5,4,4},{0,4,4},{0,4,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                     {2,2,5},{2,0,5},{2,0,5},{2,0,0},{2,0,0},{0,0,0},{0,0,0},
                     {2,5,5},{2,5,0},{2,5,0},{0,5,0},{0,5,0},{0,0,0},{0,0,0},
                     {2,4,2},{2,4,0},{2,4,0},{2,0,0},{2,0,0},{0,0,0},{0,0,0},
                     {0,0,0},{0,0,0},{0,0,0}
                 };

                 //加Mr
                 for (int n = 0; n < AStar.np; ++n)
                    for (int m = 0; m < common.L; ++m)
                    {
                     if (MrF[n,m ] != 0)
                     {
                         if (n == 1 || n == 12 || n == 17 || n == 26)
                             MachineTime[0] += (int)MrF[n,m];
                         else if (n == 3 || n == 8 || n == 19 || n == 24)
                             MachineTime[1] += (int)MrF[n,m];
                         else if (n == 5 || n == 10 || n == 15 || n == 22)
                             MachineTime[2] +=  (int)MrF[n,m];
                     }
                 } 
                 //===================================== end of New4x3 =====================================
                */
                
                
                   //===================================== start of xiong98 =====================================
                   const int ResNum = 3; //三个资源库所
                   double[] MachineTime = new double[ResNum];
                   for (int i = 0; i < MachineTime.Length; ++i)
                   {
                       MachineTime[i] = 0;
                   }

                   double[,] WRT =
                  {
                           {2,3,4},{0,3,4},{0,3,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                           {2,2,4},{2,2,0},{2,2,0},{0,2,0},{0,2,0},{0,0,0},{0,0,0},
                           {3,3,5},{0,3,5},{0,3,5},{0,3,0},{0,3,0},{0,0,0},{0,0,0},
                           {3,3,4},{3,0,4},{3,0,4},{3,0,0},{3,0,0},{0,0,0},{0,0,0},
                           {0,0,0},{0,0,0},{0,0,0}
                       };

                   //加Mr
                    for (int n = 0; n < AStar.np; ++n)
                          for (int m = 0; m < common.L; ++m)
                          {
                          if (MrF[n,m] != 0)
                          {
                              if (n == 1 || n == 10 || n == 15 || n == 26)
                                  MachineTime[0] += (int)MrF[n,m];
                              else if (n == 3 || n == 12 || n == 19 || n == 22)
                                  MachineTime[1] += (int)MrF[n,m];
                              else if (n == 5 || n == 8 || n == 18 || n == 24)
                                  MachineTime[2] += (int)MrF[n,m];
                          }
                      }
                   //===================================== end of xiong98 =====================================
                   
                   /*
                //===================================== start of ChenFig5 =====================================
                const int ResNum = 6; //六个资源库所
               int[] MachineTime = new int[ResNum];
               for (int i = 0; i < MachineTime.Length; ++i)
               {
                   MachineTime[i] = 0;
               }

               int[,] WRT =
               {
                    {0,0,7,5,0,3}, {0,0,4,5,0,3},{0,0,4,5,0,3},{0,0,4,5,0,3},{0,0,0,5,0,3},{0,0,0,5,0,0},{0,0,0,0,0,0},
                    {4,3,9,2,0,0},{4,3,9,0,0,0},{0,3,9,0,0,0},{0,3,5,0,0,0},{0,0,5,0,0,0},{0,0,0,0,0,0},
                    {0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},
                };

               //加Mr
               for (int n = 0; n < AStar.np; ++n)
                   for (int m = 0; m < common.L; ++m)
                   {
                   if (MrF[n,m] != 0)
                   {
                       if (n == 9)
                           MachineTime[0] += (int)MrF[n,m];
                       else if (n == 11 || n == 2)
                           MachineTime[1] += (int)MrF[n,m];
                       else if (n == 1 || n == 4 || n == 10 || n == 12)
                           MachineTime[2] += (int)MrF[n,m];
                       if (n == 6 || n == 8)
                           MachineTime[3] += (int)MrF[n,m];
                       else if (n == 3)
                           MachineTime[4] += (int)MrF[n,m];
                       else if (n == 5)
                           MachineTime[5] += (int)MrF[n,m];
                   }
               }
               //===================================== end of ChenFig5 =====================================
            */


                //通用

                for (int n = 0; n < AStar.np; ++n)
                {
                    if (MF[n] != 0)
                    {
                        for (int x = 0; x < ResNum; ++x)
                        {
                            MachineTime[x] += MF[n] * WRT[n, x];
                        }
                    }
                }

                //h=max{ei(m)}
                double max1 = 0;
                for (int i = 0; i < MachineTime.Length; ++i)
                {
                    if (max1 < MachineTime[i])
                    {
                        max1 = MachineTime[i];
                    }
                }
                double max = 0;
                 max = max1 + ep2 * (1 - ((float)FMarkingDepth + 1) /72) * max1;//！！！！要修改总的深度！！！！！原函数         
               // max= max1+ep2 * (System.Math.Sqrt(max1 / StartNodeF)) * max1;
                //max = max1 + ep2 * (max1 / StartNodeF) * max1;
                
                return max;
            }
            if (method == 9)//该h函数为改进xiong98即添加he和hs两个部分  zhaozhixia
            {

                //===================================== start of xiong98 =====================================
                const int ResNum = 3; //三个资源库所
                int[] MachineTime = new int[ResNum];
                int[] MachineTime2 = new int[ResNum];
                int[] MachineTime3 = new int[ResNum];
                for (int i = 0; i < MachineTime.Length; ++i)
                {
                    MachineTime[i] = 0;
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
                               MachineTime[0] += (int)MrF[n];
                           else if (n == 3 || n == 12 || n == 19 || n == 26)
                               MachineTime[1] += (int)MrF[n];
                           else if (n == 5 || n == 8 || n == 18 || n == 24)
                               MachineTime[2] += (int)MrF[n];
                       }
                   }*/
                //===================================== start of xiong98 =====================================
                /*
                //===================================== start of New4x3 =====================================
                const int ResNum = 3; //三个资源库所
                int[] MachineTime = new int[ResNum];
                int[] MachineTime2 = new int[ResNum];
                int[] MachineTime3 = new int[ResNum];
                for (int i = 0; i < MachineTime.Length; ++i)
                {
                    MachineTime[i] = 0;
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
                            MachineTime[0] += (int)MrF[n];
                        else if (n == 3 || n == 8 || n == 19 || n == 24)
                            MachineTime[1] += (int)MrF[n];
                        else if (n == 5 || n == 10 || n == 15 || n == 22)
                            MachineTime[2] += (int)MrF[n];
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
           int[] MachineTime = new int[ResNum];
           int[] MachineTime2 = new int[ResNum];
           int[] MachineTime3 = new int[ResNum];
           for (int i = 0; i < MachineTime.Length; ++i)
           {
               MachineTime[i] = 0;
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
                const int ResNum = 7; //三个资源库所
                int[] MachineTime = new int[ResNum];
                int[] MachineTime2 = new int[ResNum];
                int[] MachineTime3 = new int[ResNum];
                for (int i = 0; i < MachineTime.Length; ++i)
                {
                    MachineTime[i] = 0;
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
                            MachineTime[m] += MF[n] * RST[n, m];
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
                for (int i = 0; i < MachineTime.Length; ++i)
                {
                    if (max < MachineTime[i] + MachineTime2[i] + MachineTime3[i])
                    {
                        max = MachineTime[i] + MachineTime2[i] + MachineTime3[i];
                    }

                }
                double max1 = 0;
                //======xiong98=======
                max1 = max + ep2 * (max / StartNodeF) * max;// +max2 +max3;

                return max1;

            }

            return 0;
        }

        public virtual double CalculateHF(int method)
        {
            //CalculateHF(int method) hF1=max{ei(m)}; h2=-dep(m)
            /*if (method==1)
				//h=max{ei(m)} where ei(m) is the sum of operation times of those remaining operation for all jobs
				//which are planned to be processed on the ith machine when the current system state is represented 
				//by the marking m
			{
				decimal[] MachineTime={0,0,0};
				for(int n=0;n<MF.Length;++n)
				{
					if (MF[n]!=0)
						for(int x=0;x<MachineTime.Length;++x)
							MachineTime[x]=MachineTime[x]+MF[n]*AStar.RST[n,x];
				}

				//加Mr
				if(MF[2]!=0 || MF[13]!=0)
					MachineTime[0]=MachineTime[0]+MF[2]*MrF[2]+MF[13]*MrF[13];
				if(MF[4]!=0 || MF[15]!=0)
					MachineTime[1]=MachineTime[1]+MF[4]*MrF[4]+MF[15]*MrF[15];
				if(MF[6]!=0 || MF[11]!=0)
					MachineTime[2]=MachineTime[2]+MF[6]*MrF[6]+MF[11]*MrF[11];

				decimal max=0;
				for(int c=0;c<MachineTime.Length;++c)
					if(max<MachineTime[c])
						max=MachineTime[c];
				return max;

			}*/


            if (method == 2)
                return (-(FMarkingDepth + 1));

            return 0;
        }

        public virtual void FindEnabledTransitions()//寻找当前标识（FM[i]）下可实施的变迁，并对EnabledTransitions赋值（1：可以实施，0：不能实施）
        {
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

        public virtual void GetSuccessors(ArrayList ASuccessors, int hmethod,double ep2,double StartNodeF) //获得当前节点的所有子节点，并添加到列表中
        {
            //寻找当前标识下可实施的变迁
            FindEnabledTransitions();
            for (int i = 0; i < FEnabledTransitions.Length; ++i)
            {
                if (FEnabledTransitions[i] == 1) //变迁可以实施
                {
                    //程序选择哪个变迁发射取决于系统所采用的派遣规则

                    /*//计算控制向量u（u = new int[AStar.nt]）
                    //如果j = j*，则u = 1，否则u = 0
                    for (int m = 0; m < u.Length; ++m)
                    {
                        if (m == i)
                            u[m] = 1;
                        else
                            u[m] = 0;
                    }*/
                    for (int n = 0; n < AStar.np; ++n)//zzx
                    {
                        for (int m = 0; m < common.L; ++m)
                        {
                           MrF[n, m] = FR[n, m];                        
                        }         
                    }
                    //计算 delt=max{Mrz}
                    delt = 0;
                    for (int x = 0; x < AStar.np; ++x)//zzx
                    {
                        if (AStar.LMINUS[x, i] == 1)
                        {
                            //该标识下所有位置的剩余处理时间的最大值
                                    if (delt < FR[x, temparray[x]])
                                     delt = FR[x, temparray[x]];
                        }
                    }
                    //从变迁的输入库所中移去相应的托肯
                    //M(k)+ = M(k)- - LMINUS*u(k) , M(k)+ 和M(k)- 分别表示托肯移走前后的系统标识
                    for (int n = 0; n < AStar.np; ++n)
                    {
                        if (AStar.LMINUS[n, i] != 0)
                            MZ[n] = FM[n] - AStar.LMINUS[n, i]; //MZ：标识状态M(k)+
                        else
                            MZ[n] = FM[n];

                    }
                    //向变迁的所有输出库所中添加相应托肯
                    //M(k+1)- = M(k)+ + LPLUS*u(k)
                    for (int n = 0; n < AStar.np; ++n)
                    {
                        if (AStar.LPLUS[n, i] != 0)
                            MF[n] = MZ[n] + AStar.LPLUS[n, i];
                        else
                            MF[n] = MZ[n];
                    }
                    //在剩余处理时间向量中逐个元素地减去delt，若值小于0则赋值为0   ZZX
                    //计算 Mr(k)+z = Mr(k)-z - delt(k)z
                    for (int n = 0; n < AStar.np; ++n)
                    {
                        for (int m = 0; m < common.L; ++m)
                        {
                            MrZ[n, m] = FR[n, m]- delt;
                            if (MrZ[n, m] < 0)
                                MrZ[n, m] = 0;
                        }
                    }
                    //向变迁的所有输出库所的剩余操作时间中加入相应时间
                    //Mr(k+1)-z = Mr(k)+z + t(k)z
                    for (int n = 0; n < AStar.np; ++n)//zzx
                    {
                        //把现有时间信息向后移动
                            for (int j = common.L - 1; j > 0; --j)
                            {
                                if (FR[n, j - 1] != 0)
                                {
                                    MrF[n, j] = MrF[n, j - 1] - delt;

                                    if (MrF[n, j] < 0)
                                     {
                                       MrF[n, j] = 0;
                                     }
                                }
                            }
                       // }          
                        for (int m = 0; m < common.L; ++m)
                        {
                            if (AStar.LPLUS [n, i] == 1)
                            // MrF[n,m] = MrZ[n,m] + AStar.t[n]; //t：操作时间
                            {
                                MrF[n, 0] = MrZ[ n, m ] + AStar.t[n];
                             
                                if(AStar.LMINUS[n,i]==1)
                                {
                                     temparray[n]++;
                                }         
                            }
                            else
                                MrF[n, m] = MrZ[n, m];
                        }
                    }
                /*    for (int n = 0; n < AStar.np; ++n)
                        for(int m=0;m<common.L;++m)
                        if (MrF [n,0]==MrF[n,1]&&MrF[n,0]!=0)
                    {
                        MrF[n, 1] = MrF[n, 0] - delt;
                                if(MrF[n,1]<0)
                                {
                                    MrF[n, 1] =0;
                                }
                    }*/
                    
                    double  g = Fg + delt;
                    double  h = Calculate(hmethod,ep2, StartNodeF);
                    double  f =(double ) g + h;

                    double hF;//=CalculateHF(2);//计算子节点的hF
                              //CalculateHF(int method) hF1=max{ei(m)}; h2=-dep(m)

                    hF = -(FMarkingDepth + 1);

                    AStarNode NewNode = new AStarNode(this, GoalNode, g, h, f, MF, MrF, i, FMarkingDepth + 1,hF , delt);
                    //AStarNode(父节点, 目标节点, g值, h值, f值, 节点的标志, 该标识下所有位置的剩余处理时间, 产生本标识所实施的变迁, 标志的深度, 从父标识到变迁实施得到本标识所用时间)
                    ASuccessors.Add(NewNode);
                }
     
            }//for循环结束

        }
        
       
        public virtual void PrintNodeInfo(int loop) //打印当前节点的信息
        {
            Console.Write("loop:{0}\tf:{1}\tg:{2}\th:{3}\ttFireFrom:{4}\tDepth:{5} ", loop, Math.Round(Ff, 0), Fg, Math.Round(Fg, 0), FTFireFrom + 1, FMarkingDepth);



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
                for (int m = 0; m < common.L; ++m)
                    
                   {
                    
                       if (FR[n,m] != 0)
                          
                            Console.Write("[{0}，{1}]:{2} ", n + 1, m+1, FR[n,m]);

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
            return (f.CompareTo(((AStarNode)obj).f));
        }

        #endregion
    }


    public sealed class AStar //Petri网模型运行所需的全局属性和行为
    {
        #region Private Fields
        private AStarNode FStartNode;//起始节点
        private AStarNode FGoalNode;//目标节点
        private Heap FOpenList;//Open列表
        private Heap FClosedList;//Close列表
        private ArrayList FSuccessors;//子节点列表
        private ArrayList FExpandedList;//已扩展节点列表
        private ArrayList FSolution;//结果方案列表
        private int FNExpandedNode;//已扩展节点数
        #endregion

        #region Properties
        public struct g
        {
            public decimal cost1;
            public decimal cost2;
        };
        public static double[] t;//各库所的操作时间
        //public static g[] t;//各库所的操作代价
        public static int[,] LPLUS;//关联矩阵L+
        public static int[,] LMINUS;//关联矩阵L-

        public static int np;//Petri网中位置数(含资源)
        public static int nt;//Petri网中变迁数
        public static int nrs;//Petri网中资源位置数

        public static int[] StartM;//开始节点的标识向量
        public static int[] GoalM;//目标节点的标识向量
        public static double [,] StartMr;//开始节点的剩余处理时间向量
        public static double [,] GoalMr;//目标节点的剩余处理时间向量
        public static double[,] WRT;
        public static double[,] MrF;
        public ArrayList Solution//结果方案列表
        {
            get
            {
                return FSolution;
            }
        }
        public int NExpandedNode//已扩展节点数
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

        private ArrayList ChildrenInOpenList = new ArrayList();//ArrayList 可动态增加的数组

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

             
            
            Console.WriteLine("Petri网中位置数(含资源)：" + np);
            Console.WriteLine("Petri网中变迁数：" + nt);
            Console.WriteLine("Petri网中资源位置数：" + nrs);
            Console.WriteLine("初始marking：");
 
            for (int i = 0; i < np; i++)
            {
                Console.Write(StartM[i] + " ");
            }
            Console.WriteLine();
            Console.WriteLine("处理时间：");
            for (int i = 0; i < np; i++)
            {
                Console.Write(t[i] + " ");
            }
            Console.WriteLine();
            Console.WriteLine("目标marking：");
            for (int i = 0; i < np; i++)
            {
                Console.Write(GoalM[i] + " ");
            }
            Console.WriteLine();
            Console.WriteLine("伴随矩阵L+：");
            for (int i = 0; i < np; ++i)
            {
                for (int j = 0; j < nt; ++j)
                {
                    Console.Write(LPLUS[i, j] + " ");
                }
                Console.WriteLine();
            }
            Console.WriteLine();
            Console.WriteLine("伴随矩阵L-：");
            for (int i = 0; i < np; ++i)
            {
                for (int j = 0; j < nt; ++j)
                {
                    Console.Write(LMINUS[i, j] + " ");
                }
                Console.WriteLine();
            }
            Console.WriteLine();
            

            StartMr = new double [np,common.L];//zzx  
            GoalMr = new double [np,common.L];
            for (int i = 0; i < np; ++i)
                for(int j=0; j <common.L;++j)
                   {
                     StartMr[i,j] = 0;
                     GoalMr[i,j] = 0;
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

            //init文件的第一行
            {
                S = SR.ReadLine();
                SubS = S.Split(new char[] { ' ' });//string[]不指定大小就可以使用

                //Petri网中位置数(含资源)
                np = SubS.Length;

                //初始marking
                StartM = new int[np];
                for (int i = 0; i < SubS.Length; ++i)
                {
                    StartM[i] = Convert.ToInt32(SubS[i]);
                }
            }

            //init文件的第二行
            {
                S = SR.ReadLine();
                SubS = S.Split(new char[] { ' ' });

                //Petri网中资源位置数
                nrs = 0;
                /*t = new g[np]; //各位置的操作代价
                for (int i = 0; i < SubS.Length; ++i)
                {
                    if(SubS[i].Length != 1)
                    {
                        t[i].cost1 = Convert.ToInt32(SubS[i].Split(new char[] { ',' })[0]);
                        t[i].cost2 = Convert.ToInt32(SubS[i].Split(new char[] { ',' })[1]);
                        nrs++;
                    }
                    else
                    {
                        t[i].cost1 = 0;
                        t[i].cost2 = 0;
                    }
                }*/
                t = new double [np]; //各位置的操作时间
                for (int i = 0; i < SubS.Length; ++i)
                {
                    if (Convert.ToInt32(SubS[i]) != 0)
                    {
                        t[i] = Convert.ToInt32(SubS[i]);
                     //   nrs++;
                    }
                }
            }

            //init文件的第三行
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
                if (StartM[i] != 0)
                {
                    if (StartM[i] == GoalM[i])
                    {
                        nrs++;
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

            //Petri网中变迁数
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
                for (int i = 0 ,j = 0; i < SubS.Length && j< np; ++i)
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
        /*    //matri.txt输入矩阵
            for (int i = 0; i<nt; ++i)
            {
                for (int j = 0; j < np; ++j)
                {
                    Console.Write(temp[i, j] + " ");
                }
                Console.WriteLine();
            }*/

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

        // HList按Ff排好序了，将Node插入相同Ff的第一个位置
        private int SortAdd(Heap HList, AStarNode Node)//将节点插入到相同Ff值的第一个位置
        {
            int position = 0;
            for (int i = 0; i < HList.Count; ++i)
            {
                AStarNode LNode = (AStarNode)HList[i];
                if (LNode.f >= Node.f)
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

        private void PrintNodeList(object ANodeList)//输出某列表中所有节点的信息
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

        public void SimplePrintSolution()//有重载，用于输出open节点数
        {
            Console.WriteLine("The number of markings in open:{0}", FOpenList.Count);
        }

        //向屏幕输出，并写文件result.txt,有重载
        public void PrintSolution()
        {
            PrintNodeList(FSolution);//向屏幕输出FSolution			
            Console.WriteLine("The number of expanded markings:{0}", FExpandedList.Count);

            Console.WriteLine("File writing...");
            FileStream ostrm;
            StreamWriter writer;
            TextWriter oldOut = Console.Out;
            try
            {
                ostrm = new FileStream("./result.txt", FileMode.OpenOrCreate, FileAccess.Write);
                writer = new StreamWriter(ostrm);
            }
            catch (Exception e)
            {
                Console.WriteLine(e.Message);
                Console.WriteLine("Cannot open result.txt for writing.");
                return;
            }
            Console.SetOut(writer);
            PrintNodeList(FSolution);//向文件输出FSolution	


            Console.WriteLine("*************FExpandedList***********");
            Console.WriteLine("The number of expanded markings:{0}", NExpandedNode);//
            PrintNodeList(FExpandedList);//向文件输出FExpandedList

            Console.WriteLine("*************OpenList***********");
            PrintNodeList(FOpenList);//向文件输出FOpenList


            Console.SetOut(oldOut);
            writer.Close();
            ostrm.Close();
            Console.WriteLine("File(A* result.txt) writing complete.");

        }

        public void FindPath(AStarNode AStartNode, AStarNode AGoalNode, double ep, double ep2,int hmethod, int hFmethod, int opensize, bool printScreen)
        {
            //hmethod:所用启发函数h
            //h1=max{ei(m)};
            //h2=0;
            //h4=-dep(m);

            //printScreen:是否向屏幕打印每个扩展节点的信息

            FStartNode = AStartNode;
            FGoalNode = AGoalNode;

            FOpenList.Clear();
            FClosedList.Clear();
            FSuccessors.Clear();
            FSolution.Clear();
            FExpandedList.Clear();
            NExpandedNode = 0;

        //    int biteCount = 0;//记录BFBT中open截取次数

            int loop = 0;
            FOpenList.Add(FStartNode);//将初始标记放入OPEN表中zzx

            //计算h(source)
            double  StartNodeF = 0;

            if (hmethod == 7)
            {
                
                 //===================================== start of ChenFig5 =====================================
                 const int ResNum = 6; //六个资源库所
                 double[] MachineTime = new double[ResNum];
                 for (int i = 0; i < MachineTime.Length; ++i)
                 {
                     MachineTime[i] = 0;
                 }

                 double[,] WRT =
                 {
                   {0,0,3,0,7,5 }, {0,0,3,0,4,5 }, {0,0,3,0,4,5 }, {0,0,3,0,4,5 }, {0,0,3,0,0,5 }, {0,0,0,0,0,5 }, {0,0,0,0,0,0 },
                   {0,3,0,4,9,2 }, {0,3,0,4,9,0 }, {0,3,0,0,9,0 }, {0,3,0,0,5,0 }, {0,0,0,0,5,0 }, {0,0,0,0,0,0 }, {0,0,0,0,0,0 },
                     {0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0}
               };

                 //===================================== end of ChenFig5 =====================================
                
                /*
                 //===================================== start of xiong98 =====================================
                 const int ResNum = 3; //三个资源库所
                 double[] MachineTime = new double[ResNum];
                 for (int i = 0; i < MachineTime.Length; ++i)
                 {
                     MachineTime[i] = 0;
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
                   const int ResNum = 3; //三个资源库所
                   int[] MachineTime = new int[ResNum];//每个资源库所的所有标识的剩余处理时间
                   for (int i = 0; i < MachineTime.Length; ++i)
                   {
                       MachineTime[i] = 0;
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
             /*   
             //===================================== start of ChenFig6222 =====================================
             const int ResNum = 7; //三个资源库所
             double[] MachineTime = new double[ResNum];
             for (int i = 0; i < MachineTime.Length; ++i)
             {
                 MachineTime[i] = 0;
             }

             double[,] WRT =
             {
                    {0,7,0,0,2,0,0},{0,5,0,0,2,0,0},{0,5,0,0,0,0,0},{0,0,0,0,0,0,0},{3,3,4,0,0,0,0},{0,3,4,0,0,0,0},
                    {0,6,4,0,1,0,0},{0,0,4,0,1,0,0},{0,0,4,0,0,0,0},{0,0,0,0,0,0,0},{0,3,4,0,0,0,2},{0,0,4,0,0,0,2},
                    {0,0,4,0,0,0,0},{2,4,6,0,0,3,1.5},{2,4,0,0,0,3,1.5},{2,4,0,0,0,3,0},{2,0,0,0,0,3,0},{2,0,0,0,0,0,0},
                    {0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},
                    {0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0}
                 };
             //===================================== end of ChenFig6222 =====================================
             */
             /*
                //===================================== start of 2012Fig1新 =====================================
                const int ResNum = 3; //六个资源库所
                double[] MachineTime = new double[ResNum];//每个资源库所的所有标识的剩余处理时间
                for (int i = 0; i < MachineTime.Length; ++i)
                {
                    MachineTime[i] = 0;
                }

                double[,] WRT = { {57,0,42.5 }, {57,0,42.5 } , {57,0,42.5 }, { 57,0,42.5},{57,0,0 }, {57,0,0 }, { 0,0,0}, { 0,0,51}, {0,0,51 }, {0,0,0 }, {0,0,0 },
                                    {0,95,0 }, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0},
                                    {0,78,37.5 }, {0,0,37.5 }, { 0,0,37.5}, {0,0,0 }, {0,0,0 }, {0,0,0 }, { 0,70,0}, {0,70,0 }, { 0,0,0}, { 0,0,0},
                                     { 93,0,87.5}, {93,0,38 }, { 93,0,38}, { 93,0,0}, { 93,0,0}, { 0,0,0 }, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0} };
                //===================================== start of 2012Fig1新 =====================================
                */
                /*
                //===================================== start of 2012Fig1 =====================================
                const int ResNum = 3; //六个资源库所
                double[] MachineTime = new double[ResNum];//每个资源库所的所有标识的剩余处理时间
                for (int i = 0; i < MachineTime.Length; ++i)
                {
                    MachineTime[i] = 0;
                }

                int[,] WRT = { {57,0,85 }, {57,0,85 } , {57,0,85 }, { 57,0,85},{57,0,0 }, {57,0,0 }, { 0,0,0}, { 0,0,51}, {0,0,51 }, {0,0,0 }, {0,0,0 },
                                    {0,95,0 }, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0},
                                    {0,78,75 }, {0,0,75 }, { 0,0,75}, {0,0,0 }, {0,0,0 }, {0,0,0 }, { 0,70,0}, {0,70,0 }, { 0,0,0}, { 0,0,0},
                                     { 93,0,175}, {93,0,76 }, { 93,0,76}, { 93,0,0}, { 93,0,0}, { 0,0,0 }, { 0,0,0}, { 0,0,0}, { 0,0,0}, { 0,0,0} };

                //===================================== start of 2012Fig1 =====================================
                */
                //用1(xiong)=max{ei(m)}计算起始节点的F值，StartNodeF用于h12(IDW)=h(M)+ep *h(M),h(M)=h1;时计算M子节点的h!!!!!!!!!!!!!!!!!!!!!!
                for (int n = 0; n < AStar.np-AStar .nrs; ++n)//除资源外的place数
                {
                    if (FStartNode.M[n]!= 0)
                        for (int x = 0; x < MachineTime.Length; ++x)
                        {
                            MachineTime[x] += FStartNode.M[n] * WRT[n,x];
                        }
                }

                double max = 0;
                for (int c = 0; c < MachineTime.Length; ++c)
                    if (max < MachineTime[c])
                        max = MachineTime[c];
                StartNodeF = max;

            }
     

            while (FOpenList.Count >= 0)
            {
                loop++;

                if (FOpenList.Count == 0)//若OPEN表为控程序异常退出zzx
                {
                    Console.WriteLine("*******Failure!********");
                    break;
                }


                //   if (!( ep >= 0))
                //  {
                //      Console.WriteLine("You should input the right value of ep!");
                //      break;
                //   }


                //OPEN列表中的第一个节点
                AStarNode NodeCurrent = (AStarNode)FOpenList[0];

                if (ep<0)
                {

                    FOpenList.Remove(FOpenList[0]); //除去要扩展的节点
                }


                if (ep>=0)//即ep>=0,使用 search effort estimate
                {   //ep=0时，选OPEN中具有相同最小f值marking中有最小hFCost的
                    //ep>0时选择范围更大,选OPEN中具有不大于最小f值1+ep倍的marking中有最小hFCost的
                    int i = 0;
                    //FFOCALList.Clear();
                    AStarNode N = (AStarNode)FOpenList[0];//OPEN列表上的第一个节点
                    double  fMin = N.f;//总代价
                    double  minhF = N.hFCost;//节点的深 度
                    double  minDelt = N.Delt;
                    int index = 0;


                    while (i < FOpenList.Count - 1 && N.f <= (double)(1 + ep) * fMin)
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





                //如果当前节点是目的节点，则回溯构造出路径
                if ( NodeCurrent.IsGoal())
                {
                    while (NodeCurrent != null)
                    {
                        FSolution.Insert(0, NodeCurrent);
                        NodeCurrent = NodeCurrent.Parent;
                    }

                    break; //程序正常退出
                }

                //把当前节点的所有子节点加入到FSuccessors
                FSuccessors.Clear(); 
                NodeCurrent.GetSuccessors(FSuccessors,hmethod,ep2, StartNodeF);


                if (printScreen == true)
                    NodeCurrent.PrintNodeInfo(loop);//打印当前节点的信息
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
                    //////////
                    AStarNode NodeOpen = null;
                    //if(FOpenList.Contains(NodeSuccessor))//比较的是node,而不是M
                    //	NodeOpen = (AStarNode)FOpenList[FOpenList.IndexOf(NodeSuccessor)];
                    foreach (AStarNode a in FOpenList)
                    {
                        if (a.IsSameState(NodeSuccessor))
                        {
                            NodeOpen = a;
                            break;
                        }
                    }
                    int x = 1;
                    //////////新写的

                    if (NodeOpen != null)
                    {
                       // int x = 1;
                        for (int y = 0; y < NodeSuccessor.R.GetLength(0); ++y)
                        {
                            for (int z = 0; z < NodeSuccessor.R.GetLength(1); ++z)
                                if (NodeSuccessor.R[y, z] != NodeOpen.R[y, z])
                                {
                                    x = 0;
                                    break;
                                }
                            if (x == 0)//这里应该是x=0的时候退出循环
                                break;
                        }
                    }
                    //相同M,g'<g,R'==R(每个),则替换
                    if (NodeOpen != null&&x==1)
                    {
                            if (NodeSuccessor.g < NodeOpen.g)
                            {
                                FOpenList.Remove(NodeOpen);
                                SortAdd(FOpenList, NodeSuccessor);
                                //FOpenList.Add(NodeSuccessor);
                                continue;
                               // break;
                            }
                            else
                            {
                               continue;
                               //break;
                            }
                    }

                   else  if ((NodeOpen != null && x== 0)|| NodeOpen == null)
                    {
                        SortAdd(FOpenList, NodeSuccessor);
                        //Console. Write(456);
                     //   Console.WriteLine();
                        continue;
                    }

                    AStarNode NodeClosed = null;
                    foreach (AStarNode b in FClosedList)
                    {
                        if (b.IsSameState(NodeSuccessor))
                        {
                            NodeClosed = b;
                            break;
                        }
                    }
                    //相同M,g'<g,R'==R(每个),则替换
                    if (NodeClosed != null)
                    {
                        int xx = 1;
                        for (int y = 0; y < NodeSuccessor.R.GetLength(0); ++y)
                        {
                            for (int z = 0; z < NodeSuccessor.R.GetLength(1); ++z)
                                if (NodeSuccessor.R[y, z] != NodeClosed.R[y, z])
                                {
                                    xx = 0;
                                    break;
                                }
                            if(xx==0)
                              break; 
                        }
                        if(xx==1)
                        {
                            if (NodeSuccessor.g < NodeClosed.g)
                            {
                                ChildrenInOpenList.Clear();//
                                foreach (AStarNode n in FOpenList)//
                                {//Equals 的默认实现仅支持引用相等，但派生类可重写此方法以支持值相等
                                    if (n.Parent.Equals(NodeClosed))//
                                        ChildrenInOpenList.Add(n);//
                                }//
                                 //if (ChildrenInOpenList.Count>0)
                                 //Console.WriteLine("ChildrenInOpenList in not null!");
                                for (int a = 0; a < ChildrenInOpenList.Count; ++a)//
                                    FOpenList.Remove(ChildrenInOpenList[a]);//    *///**********

                                FClosedList.Remove(NodeClosed);

                                //FOpenList.Add(NodeSuccessor);
                                SortAdd(FOpenList, NodeSuccessor);
                                continue;
                                // break;
                            }
                        }
                    }
    

            } //foreach (AStarNode NodeSuccessor in FSuccessors)结束

                SortAdd(FClosedList, NodeCurrent);

                FExpandedList.Add(NodeCurrent);
                if (FSuccessors.Count > 0) //若当前节点没有子节点，则当前节点为死锁
                {
                    //NExpandedNode没加入死锁节点，所以比FExpandedList.Count可能要小 (运行发现和FExpandedList.Count一样)
                    ++NExpandedNode;//已扩展节点数
                }

            }//while (FOpenList.Count > 0) 结束
            
            /*AStarNode FinalMarking = (AStarNode)FSolution[FSolution.Count - 1];

            double[] result = new double[4];
            result[0] = (double)FinalMarking.f;//最后结果的cost
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