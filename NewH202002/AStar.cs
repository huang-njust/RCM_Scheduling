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

        //属性，通常首字母大写。外类对此类非静态属性可通过对象.属性访问；如果是静态static，则通过类.属性访问
        public AStarNode Parent//parent node
        {
            set
            {
                _Parent = value;
            }
            get
            {
                return _Parent;
            }
        }
        private AStarNode _Parent;//私有变量成员，通常前面加_，会被派生类继承


        public AStarNode GoalNode //goal node
        {
            set
            {
                _GoalNode = value;
            }
            get
            {
                return _GoalNode;
            }
        }
        private AStarNode _GoalNode;


        public decimal gValue //g value of a node (The accumulative cost of the path until now.)
        {
            set
            {
                _gValue = value;
            }
            get
            {
                return _gValue;
            }
        }
        private decimal _gValue;


        public decimal hValue //h value of a node (The estimated minmal cost to the goal from here.)
        {//h
            set
            {
                _hValue = value;
            }
            get
            {
                return _hValue;
            }
        }
        private decimal _hValue;


        public decimal fValue //f value of a node(f=g+h, representing an estimated of the lowest cost from the initial node to the goal along a path through the current node)
        {//f
            set
            {
                _fValue = value;
            }
            get
            {
                return _fValue;
            }
        }
        private decimal _fValue;


        public int[] M //the marking of node in the reachability graph
        {
            get
            {
                return _M;
            }
        }
        private int[] _M;



        public decimal[,] R //the remaining token time matrix of a place-timed Petri net
        {
            get
            {
                return _R;
            }
        }
        private decimal[,] _R;



        public int tFireFrom //the transition whose firing generates this node
        {
            get
            {
                return _tFireFrom;
            }
            set
            {
                _tFireFrom = value;
            }
        }
        private int _tFireFrom;



        public int[] EnabledTransitions //the set of transitions that are enabled at the node
        {
            get
            {
                return _EnabledTransitions;
            }
            set
            {
                Array.Copy(value, _EnabledTransitions, value.Length);
            }
        }
        private int[] _EnabledTransitions;



        public decimal MarkingDepth //the depth of the node, i.e., the number of transition firings from the initial node to the curren node
        {
            get
            {
                return _MarkingDepth;
            }
            set
            {
                _MarkingDepth = value;
            }
        }
        private decimal _MarkingDepth;



        public decimal h2ndValue  //the second h function that may be used for nodes in OPEN. The algorithm picks out the node with the minimal h2ndValue value for expansion among the nodes having the f-value between f_min and f_min*(1+ep) in OPEN.
        {
            set
            {
                _h2ndValue = value;
            }
            get
            {
                return _h2ndValue;
            }
        }
        private decimal _h2ndValue;



        public decimal Delt//从父标识到变迁发射得到本标识所用时间
        { //Delt denotes the time required for its parent node to fire a transition to generate this node. 
            set
            {
                _Delt = value;
            }
            get
            {
                return _Delt;
            }
        }
        private decimal _Delt;



        // 通过变迁的发射而放入输出库所中的托肯必须等待一定时间后才可利用，并且该时间等于该库所的操作时间
        // M(k)- 和 R(k)- 分别表示：变迁发射前那刻，"系统的标识" 和 "剩余托肯时间矩阵"；分别用_MF和_RF表示
        // M(k)+ 和 R(k)+ 分别表示：变迁发射后，输入托肯已移走但输出托肯还未加入时 "系统的标识" 和 "剩余托肯时间矩阵"；分别用_MZ和_RZ表示
        // M(k)- and R(k)- denote the marking and the remaining token time matrix before a transition fires, respectively. Denoted as _MF and _RF.
        // M(k)+ denotes the marking after tokens are removed from the preplaces of a fired transition and before tokens are added into the postplace of the transition. Denoted as _MZ.
        // R(k)+ denotes the remaining token time matrix after the transition fires. Denoted as _RZ.
        // 这些成员无需被访问，所以没定义相应属性。但private成员也会被派生类继承
        private int[] _MF = new int[AStar.N_P];//M(k)-
        private int[] _MZ = new int[AStar.N_P];//M(k)+
        private decimal[,] _RF = new decimal[AStar.N_P, AStar.MAX_TOK_PA];//R(k)- 
        public decimal[,] _RZ = new decimal[AStar.N_P, AStar.MAX_TOK_PA];//R(k)+	 

        #endregion


        #region Constructors

        //AStarNode(父节点, 目标节点, g值, h值, f值, 节点的标志, 该标识下所有库所的托肯剩余时间矩阵, 产生本标识所发射的变迁, 标识的深度,第二个h值，从父标识到变迁发射得到本标识所用时间)
        public AStarNode(AStarNode parent, AStarNode goalNode, decimal gValue, decimal hValue, decimal fValue, int[] M, decimal[,] R, int tFireFrom, decimal markingDepth, decimal h2ndValue, decimal Delt)
        {
            _Parent = parent; 
            _GoalNode = goalNode;
            _gValue = gValue;
            _hValue = hValue;
            _fValue = fValue; 
            _M = new int[AStar.N_P];
            Array.Copy(M, _M, M.Length);
            _R = new decimal[AStar.N_P, AStar.MAX_TOK_PA];
            Array.Copy(R, _R, R.Length);
            _tFireFrom = tFireFrom;
            _EnabledTransitions = new int[AStar.N_T];
            _MarkingDepth = markingDepth;
            _h2ndValue = h2ndValue;
            _Delt = Delt;
        }

        #endregion



        #region Public Methods


        public virtual bool IsSameStateM(AStarNode aNode)//判断某节点的标识M是否和本节点一致 //只判断M
        {//Decide whether or not this node is the same as the goal node only in terms of M.
            if (aNode == null)
                return false;
            if (_M.Length != aNode.M.Length)
                return false;
            for (int i = 0; i < _M.Length; ++i)
                if (_M[i] != aNode.M[i])
                    return false;
            return true;
        }


        public virtual bool IsSameStateM_R(AStarNode aNode)//判断aNode节点的M和R是否和本节点一致//判断M和R
        {//Decide whether or not this node is the same as the goal node in terms of M and R.
            if (aNode == null)
                return false;
            if (_M.Length != aNode.M.Length)
                return false;
            for (int i = 0; i < _M.Length; ++i)
                if (_M[i] != aNode.M[i])
                    return false;
            for (int i = 0; i < AStar.N_P; ++i)//zzx/////////////
                for (int j = 0; j < AStar.MAX_TOK_PA; ++j) 
                {
                    if (_R[i, j] == 0 && aNode.R[i, j] == 0)//Huang202303:因为存在不含剩余托肯时间的非操作库所，且操作库所中的剩余托肯时间按非升序排列，所以无需比较库所中所有的剩余托肯时间;可提速
                        break;
                    if (_R[i, j] != aNode.R[i, j])
                        return false;
                }
            return true;
        }



        public bool IsGoal()//判断本节点的M和R是否与GoalNode一致
        {//Decide whether or not this node is the same as the goal node in terms of M and R. 
            return IsSameStateM_R(_GoalNode);
        }



        public decimal CalculateH(string fileName, int hMethod, decimal ep2)//Calculates the h value of a node, i.e., the estimated minimal cost of the path from the node to the goal. ep2 is for dynamic weighted search (h710-h723)
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
        {        
            //获取fileName中_之前的小写字符
            char[] separator = {'_'};
            string[] words = fileName.Trim().Split(separator); //Trim()去前后空格
            string fileNameLower = words[0].ToLower();

            
        //If h1, h7, h8, h9, h10 is used to compute h, some parameters of the PN is needed in CalculateH().
        //*******************************************************************************************************************************************************************************************************************************************
        //Astar's general public variables for h1, h7, h8, and h9: 
        //M0r is a |P_R| vector that denotes the number of tokens in each resource place at the initial marking.
        //Upi is a |P\P_R|x|P_R| matrix that denotes the number of resource units of $r\in P_R$ that are required by $p\in P_A$. Note that Upi only consider non-resource places.
        //WRT (Weighted Remaining Time) is a |P\P_R|x|P_R| matrix that denotes the total weighted operation time definitely required by an availabe token in a place for a resource.

        //*******************************************************************************************************************************************************************************************************************************************
        //h1=max_i{e_i(M)} plus R; h1 comes from Xiong98. e_r(M) is the sum of operation times of those remaining operations for all jobs which are planned to be processed with the ith resource.
        //h1 is only for the ordinary nets in which resource places have only one resource unit and each operation uses only one resource.For example, Xiong98, New4x3, Huang2012Fig1, ChenFig5. Not for generalized nets and the nets whose resource places may have more than one units (ChenFig6).
        //So, h1 uses a simple WRT that does not consider weight.      （只考虑ordianry nets，并且每个资源库所的unit数为1以及每个操作只使用一个资源）        

        //*******************************************************************************************************************************************************************************************************************************************
        //h7=h_H=max_r{M*MRT+sum{R*Upi/M_0}}, which comes from Eq.(9.2) in Chapter 9 of our book. It is an admissible and highly informed heuristic function that can be used for the nets with alternative routings, weighted arcs, and multiple resource copies.     
        //Before h7=h_H is used, the number of resource places, the WRT matrix, the Upi matrix, and the M0r vector of the Petri net should be given in the class AStar. 


        //*******************************************************************************************************************************************************************************************************************************************
        //h8=\sum{j(p,i)}{(R(p, i)*\sum{U(p, r)}+MRT(p)}+\sum{\delta(S, r)*G(S, r)}/{\sum((M_{P/P_R}^T*MR^3)^{C}} comes from our T-SMC2023 paper.
        //Before h8 is used, Upi, MRT(p), MR^3,  and M0r of the Petri net should be given in the class AStar.
        //MRT (Minimal Remaining extended operation Time) is a column vector with |P\P_R| elements and MRT(p) denotes the minimal total EOT (Extended Operation Time) that is required for an available token in $p$ to move to its end place.
        //MR^3 (Maximal Remaining Required Resources) is a $|P\P_R|\times|P_R|$ matrix such that if moving an unavailable token in a place $p\in P\setminus P_R$ to its end place requires at most $n$ units of $r$, MR^3(p, r)=n.
        //Note that we assume that \delta(S, r)*G(S, r)=0 since both ours and Luo's have it in their heuristic functions and it is hard to calculate.        

        //*******************************************************************************************************************************************************************************************************************************************
        //h9=\sum{j(p,i)}{(R(p, i)+X(p)}+\sum{\delta(S, r)*G(S, r)}/|ER| comes from 2015LuoTASE.
        //Before h9 is used,X vector and ER of the Petri net should be given in the class AStar. 
        //X denotes the minimal processing time for an available token to travel from its place to its end place. 
        //ER  is the number of resource instances.
        //*******************************************************************************************************************************************************************************************************************************************
            
            
            int[] M0r;      //M0r is a |P_R| vector that denotes the number of tokens in each resource place at the initial marking.
            int[,] Upi ;    //Upi is a |P\P_R|x|P_R| matrix that denotes the number of resource units of $r\in P_R$ that are required by $p\in P_A$. Note that Upi only consider non-resource places.
            decimal[,] WRT; //WRT (Weighted Remaining Time) is a |P\P_R|x|P_R| matrix that denotes the total weighted operation time definitely required by an availabe token in a place for a resource.
            decimal[] MRT;  //MRT (Minimal Remaining extended operation Time) is a column vector with |P\P_R| elements and MRT(p) denotes the minimal total EOT (Extended Operation Time) that is required for an available token in $p$ to move to its end place.
            decimal[,] MR3; //MR^3 (Maximal Remaining Required Resources) is a $|P\P_R|\times|P_R|$ matrix such that if moving an unavailable token in a place $p\in P\setminus P_R$ to its end place requires at most $n$ units of $r$, MR^3(p, r)=n.
            int[] X;        //X is a column vector with |P\P_R| elements and X(p) denotes the minimal processing time for an available token to travel from its place to its end place. 
            int ER;         //ER  is the number of resource instances.

            if (fileNameLower == "chenfig5")
            {
                //General
                M0r = new int[] { 1, 1, 1, 1, 1, 1 };//the number of tokens in each resource place at the initial marking
                Upi = new int[,]
                {
                                        {0,0,0,0,0,0},{0,0,0,0,1,0},{0,1,0,0,0,0},{1,0,0,0,0,0},{0,0,0,0,1,0},
                                        {0,0,1,0,0,0},{0,0,0,0,0,1},{0,0,0,0,0,0},{0,0,0,0,0,1},{0,0,0,1,0,0},
                                        {0,0,0,0,1,0},{0,1,0,0,0,0},{0,0,0,0,1,0},{0,0,0,0,0,0},{0,0,0,0,0,0}
                }; //the number of resource units of $r\in P_R$ that are required by $p\in P_A$

                //For h7 and h1 (if it is an ordianry net whose resource places have only one unit)
                WRT = new decimal[,]
                {
                                        {0,0,3,0,7,5},{0,0,3,0,4,5},{0,0,3,0,4,5},{0,0,3,0,4,5},{0,0,3,0,0,5},
                                        {0,0,0,0,0,5},{0,0,0,0,0,0},{0,3,0,4,9,2},{0,3,0,4,9,0},{0,3,0,0,9,0},
                                        {0,3,0,0,5,0},{0,0,0,0,5,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0}
                };//the weighted resource time matrix

                //For h8
                MRT = new decimal[] { 17, 14, 12, 12, 8, 5, 0, 18, 16, 12, 8, 5, 0, 0, 0 };//the minimal total time of EOTs that is required for an available token in $p$ to move to its end place
                MR3 = new decimal[,]
                {
                                       {1,1,1,0,2,1},{1,1,1,0,2,1},{0,1,1,0,2,1},{1,0,1,0,1,1},{0,0,1,0,1,1},
                                       {0,0,1,0,0,1},{0,0,0,0,0,1},{0,1,0,1,2,1},{0,1,0,1,2,1},{0,1,0,1,2,0},
                                       {0,1,0,0,2,0},{0,1,0,0,1,0},{0,0,0,0,1,0},{0,0,0,0,0,0},{0,0,0,0,0,0}
                 };//a place $r\in P_R$ to its end place requires at most $n$ units of $r$

                //For h9
                X = new int[] { 17, 14, 12, 12, 8, 5, 0, 18, 16, 12, 8, 5, 0, 0, 0 }; //the minimal processing time for a token from $p$ to its end place
                ER = 6;  // the number of all resource units in a PN
            }
            else if (fileNameLower == "chenfig5extended")
            {
                //General
                M0r = new int[] { 1, 3, 1, 1, 1, 3 };//the number of tokens in each resource place at the initial marking
                Upi = new int[,]
                {
                                        {0,0,0,0,0,0},{0,0,0,0,1,0},{0,1,0,0,0,0},{1,0,0,0,0,0},{0,0,0,0,1,0},
                                        {0,0,1,0,0,0},{0,0,0,0,1,2},{0,0,0,0,0,0},{0,0,0,0,0,1},{0,0,0,1,0,0},
                                        {0,0,0,0,1,1},{0,1,0,0,0,0},{0,0,0,0,1,0},{0,0,0,0,0,0},{0,0,0,0,0,0}
                 }; //the number of resource units of $r\in P_R$ that are required by $p\in P_A$

                //For h7 and h1 (if it is an ordianry net whose resource places have only one unit)
                WRT = new decimal[,]
                {
                                        {0,0,3,0,12,3.33m},{0,0,3,0,9,3.33m},{0,0,3,0,9,3.33m},{0,0,3,0,9,3.33m},{0,0,3,0,5,3.33m},
                                        {0,0,0,0,5,3.33m},{0,0,0,0,0,0},{0,1,0,4,9,2},{0,1,0,4,9,1.33m},{0,1,0,0,9,1.33m},
                                        {0,1,0,0,5,0},{0,0,0,0,5,0},{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0}
                };//the weighted resource time matrix

                //For h8 
                MRT = new decimal[] { 27, 24, 22, 22, 18, 15, 0, 22, 20, 16, 8, 5, 0, 0, 0 };//the minimal total time of EOTs that is required for an available token in $p$ to move to its end place
                MR3 = new decimal[,]
                {
                                       {1,1,1,0,3,2},{1,1,1,0,3,2},{0,1,1,0,2,2},{1,0,1,0,2,2},{0,0,1,0,2,2},
                                       {0,0,1,0,1,2},{0,0,0,0,1,2},{0,1,0,1,2,2},{0,1,0,1,2,2},{0,1,0,1,2,1},
                                       {0,1,0,0,2,1},{0,1,0,0,1,0},{0,0,0,0,1,0},{0,0,0,0,0,0},{0,0,0,0,0,0}
                };//a place $r\in P_R$ to its end place requires at most $n$ units of $r$

                //For h9
                X = new int[] { 17, 14, 12, 12, 8, 5, 0, 18, 16, 12, 8, 5, 0, 0, 0 }; //the minimal processing time for a token from $p$ to its end place
                ER = 10;  // the number of all resource units in a PN
            }
            else if (fileNameLower == "chenfig6")
            {
                //General                
                M0r = new int[] { 1, 1, 1, 2, 2, 2, 2 }; //the number of tokens in each resource place at the initial marking
                Upi = new int[,]
                {
                                                {0,0,0,0,0,0,0},{0,1,0,0,0,0,0},{0,0,0,0,1,0,0},{0,1,0,0,0,0,0},{0,0,0,0,0,0,0},
                                                {1,0,0,0,0,0,0},{0,0,0,1,0,0,0},{0,1,0,0,0,0,0},{0,0,0,0,1,0,0},{0,0,1,0,0,0,0},
                                                {0,0,0,0,0,1,0},{0,1,0,0,0,0,0},{0,0,0,0,0,0,1},{0,0,0,0,0,0,0},{0,0,1,0,0,0,0},
                                                {0,0,0,0,0,0,1},{0,1,0,0,0,0,0},{0,0,0,0,0,1,0},{1,0,0,0,0,0,0},{0,0,0,0,0,0,0},
                                                {0,0,0,0,0,0,0},{0,0,0,0,0,0,0}
                };//the number of resource units of $r\in P_R$ that are required by $p\in P_A$

                //For h7 and h1 (if it is an ordianry net whose resource places have only one unit) 
                WRT = new decimal[,]
                {
                                               {0,7,0,0,2,0,0},{0,5,0,0,2,0,0},{0,5,0,0,0,0,0},{0,0,0,0,0,0,0},{3,3,4,0,0,0,0},
                                               {0,3,4,0,0,0,0},{0,6,4,0,1,0,0},{0,0,4,0,1,0,0},{0,0,4,0,0,0,0},{0,0,0,0,0,0,0},
                                               {0,3,4,0,0,0,2},{0,0,4,0,0,0,2},{0,0,4,0,0,0,0},{2,4,6,0,0,3,1.5m},{2,4,0,0,0,3,1.5m},
                                               {2,4,0,0,0,3,0},{2,0,0,0,0,3,0},{2,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},
                                               {0,0,0,0,0,0,0},{0,0,0,0,0,0,0}
                };//the weighted remaining time matrix. 


                //For h8 
                MRT = new decimal[] { 11, 9, 5, 0, 15, 12, 12, 6, 4, 0, 11, 8, 4, 21, 15, 12, 8, 2, 0, 0, 0, 0 }; //the minimal total time of EOTs that is required for an available token in $p$ to move to its end place
                MR3 = new decimal[,]
                {
                                               {0,2,0,0,1,0,0},{0,2,0,0,1,0,0},{0,1,0,0,1,0,0},{0,1,0,0,0,0,0},
                                               {1,1,1,1,1,1,1},{1,1,1,1,1,1,1},{0,1,1,1,1,0,0},{0,1,1,0,1,0,0},
                                               {0,0,1,0,1,0,0},{0,0,1,0,0,0,0},{0,1,1,0,0,1,1},{0,1,1,0,0,0,1},
                                               {0,0,1,0,0,0,1},{1,1,1,0,0,1,1},{1,1,1,0,0,1,1},{1,1,0,0,0,1,1},
                                               {1,1,0,0,0,1,0},{1,0,0,0,0,1,0},{1,0,0,0,0,0,0},{0,0,0,0,0,0,0},
                                               {0,0,0,0,0,0,0},{0,0,0,0,0,0,0}
                };

                //For h9 
                X = new int[] { 11, 9, 5, 0, 15, 12, 12, 6, 4, 0, 11, 8, 4, 21, 15, 12, 8, 2, 0, 0, 0, 0 };//the minimal processing time for a token from $p$ to its end place
                ER = 13;  // the number of all resource units in a PN             
            }
            else if (fileNameLower == "chenfig6extended")
            {
                //General
                M0r = new int[] { 1, 1, 1, 2, 2, 3, 3 }; //the number of tokens in each resource place at the initial marking   
                Upi = new int[,]
                {
                                        {0,0,0,0,0,0,0},{0,1,0,0,0,0,0},{0,0,0,0,1,0,0},{0,1,0,0,0,0,0},{0,0,0,0,0,0,0},
                                        {1,0,0,0,0,0,0},{0,0,0,1,0,0,0},{0,1,0,0,0,0,0},{0,0,0,0,1,0,0},{0,0,1,0,2,0,0},
                                        {0,0,0,0,0,1,0},{0,1,0,0,0,0,0},{0,0,0,0,1,0,2},{0,0,0,0,0,0,0},{0,0,1,0,0,0,0},
                                        {0,0,0,0,0,0,1},{0,1,0,0,0,0,0},{0,0,0,0,0,1,1},{1,0,0,0,0,0,0},{0,0,0,0,0,0,0},
                                        {0,0,0,0,0,0,0},{0,0,0,0,0,0,0}
                };//the number of resource units of $r\in P_R$ that are required by $p\in P_A$

                //For h7 and h1 (if it is an ordianry net whose resource places have only one unit)
                WRT = new decimal[,]
                {
                                        {0,7,0,0,2,0,0},{0,5,0,0,2,0,0},{0,5,0,0,0,0,0},{0,0,0,0,0,0,0},{3,3,4,0,5,0,0},
                                        {0,3,4,0,5,0,0},{0,6,4,0,5,0,0},{0,0,4,0,5,0,0},{0,0,4,0,4,0,0},{0,0,0,0,0,0,0},
                                        {0,3,4,0,6,0,2.67m},{0,0,4,0,6,0,2.67m},{0,0,4,0,4,0,0},{2,4,6,0,0,2,3},{2,4,0,0,0,2,3},
                                        {2,4,0,0,0,2,2},{2,0,0,0,0,2,2},{2,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},
                                        {0,0,0,0,0,0,0},{0,0,0,0,0,0,0}
                };//the weighted remaining time matrix

                //For h8 
                MRT = new decimal[] { 11, 9, 5, 0, 25, 22, 20, 14, 12, 0, 27, 24, 12, 27, 21, 18, 14, 2, 0, 0, 0, 0 };//the minimal total time of EOTs that is required for an available token in $p$ to move to its end place
                MR3 = new decimal[,]
                {
                                       {0,2,0,0,1,0,0},{0,2,0,0,1,0,0},{0,1,0,0,1,0,0},{0,1,0,0,0,0,0},{1,1,1,1,3,1,2},
                                       {1,1,1,1,3,1,2},{0,1,1,1,3,0,0},{0,1,1,0,3,0,0},{0,0,1,0,3,0,0},{0,0,1,0,2,0,0},
                                       {0,1,1,0,3,1,2},{0,1,1,0,3,0,2},{0,0,1,0,3,0,2},{1,1,1,0,0,1,2},{1,1,1,0,0,1,2},
                                       {1,1,0,0,0,1,2},{1,1,0,0,0,1,1},{1,0,0,0,0,1,1},{1,0,0,0,0,0,0},{0,0,0,0,0,0,0},
                                       {0,0,0,0,0,0,0},{0,0,0,0,0,0,0}
                };//a place $r\in P_R$ to its end place requires at most $n$ units of $r$


                //For h9
                X = new int[] { 11, 9, 5, 0, 15, 12, 12, 6, 4, 0, 11, 8, 4, 21, 15, 12, 8, 2, 0, 0, 0, 0 }; //the minimal processing time for a token from $p$ to its end place
                ER = 13;  // the number of all resource units in a PN
            }
            else if (fileNameLower == "chenfig6extended2")
            {
                //General
                M0r = new int[] { 1, 1, 1, 2, 2, 3, 3 }; //the number of tokens in each resource place at the initial marking   
                Upi = new int[,]
                {
                                          {0,0,0,0,0,0,0},{0,1,0,0,0,0,0},{0,0,0,0,1,0,0},{0,1,0,0,0,0,0},{0,0,0,0,0,0,0},
                                          {1,0,0,0,0,0,0},{0,0,0,1,0,0,0},{0,1,0,0,0,0,0},{0,0,0,0,1,0,0},{0,0,1,0,0,0,0},
                                          {0,0,0,0,0,1,0},{0,1,0,0,0,0,0},{0,0,0,0,1,0,2},{0,0,0,0,0,0,0},{0,0,1,0,0,0,0},
                                          {0,0,0,0,0,0,1},{0,1,0,0,0,0,0},{0,0,0,0,0,1,1},{0,0,0,0,0,1,0},{0,0,0,0,0,0,0},
                                          {0,0,0,0,0,0,0},{0,0,0,0,0,0,0}
                }; //the number of resource units of $r\in P_R$ that are required by $p\in P_A$

                //For h7 and h1 (if it is an ordianry net whose resource places have only one unit) 
                WRT = new decimal[,]
                {
                                         {0,7,0,0,2,0,0},{0,5,0,0,2,0,0},{0,5,0,0,0,0,0},{0,0,0,0,0,0,0},{3,3,4,0,1,0,0},
                                         {0,3,4,0,1,0,0},{0,6,4,0,1,0,0},{0,0,4,0,1,0,0},{0,0,4,0,0,0,0},{0,0,0,0,0,0,0},
                                         {0,3,4,0,2,0,2.67m},{0,0,4,0,2,0,2.67m},{0,0,4,0,0,0,0},{2,4,6,0,0,2,3},{2,4,0,0,0,2,3},
                                         {2,4,0,0,0,2,2},{2,0,0,0,0,2,2},{2,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},
                                         {0,0,0,0,0,0,0},{0,0,0,0,0,0,0}
                };//a place $p\in P\setminus P_R$ to its end place requires at most $n$ units of $r$

                //For h8
                MRT = new decimal[] { 11, 9, 5, 0, 17, 14, 12, 6, 4, 0, 19, 16, 4, 27, 21, 18, 14, 2, 0, 0, 0, 0 }; //the minimal total time of EOTs that is required for an available token in $p$ to move to its end place               
                MR3 = new decimal[,]
                {
                                        {0,2,0,0,1,0,0},{0,2,0,0,1,0,0},{0,1,0,0,1,0,0},{0,1,0,0,0,0,0},{1,1,1,1,1,1,2},
                                        {1,1,1,1,1,1,2},{0,1,1,1,1,0,0},{0,1,1,0,1,0,0},{0,0,1,0,1,0,0},{0,0,1,0,0,0,0},
                                        {0,1,1,0,1,1,2},{0,1,1,0,1,0,2},{0,0,1,0,1,0,2},{1,1,1,0,0,1,2},{1,1,1,0,0,1,2},
                                        {1,1,0,0,0,1,2},{1,1,0,0,0,1,1},{1,0,0,0,0,1,1},{1,0,0,0,0,0,0},{0,0,0,0,0,0,0},
                                        {0,0,0,0,0,0,0},{0,0,0,0,0,0,0}
                 };//a place $r\in P_R$ to its end place requires at most $n$ units of $r$

                //For h9
                X = new int[] { 11, 9, 5, 0, 15, 12, 12, 6, 4, 0, 11, 8, 4, 21, 15, 12, 8, 2, 0, 0, 0, 0 };//the minimal processing time for a token from $p$ to its end place
                ER = 13;  // the number of all resource units in a PN
            }
            else if (fileNameLower == "huang2012fig1")
            {
                //General
                M0r = new int[] { 1, 1, 1 };//the number of tokens in each resource place at the initial marking   
                Upi = new int[,]
                {
                                      {0,0,0},{0,0,1},{0,1,0},{0,0,0},{0,0,1},
                                      {0,0,0},{1,0,0},{1,0,0},{0,0,0},{0,0,1},
                                      {0,0,0},{0,0,0},{0,1,0},{0,0,0},{0,1,0},
                                      {0,0,1},{0,0,0},{1,0,0},{0,0,1},{0,0,0},
                                      {0,0,0},{0,1,0},{0,0,0},{0,0,1},{0,0,0},
                                      {1,0,0},{0,0,1},{0,0,0},{0,1,0},{0,0,0},
                                      {0,0,0},{0,0,1},{0,0,0},{0,0,1},{0,0,0},
                                      {1,0,0},{0,0,0}
                };//the number of resource units of $r\in P_R$ that are required by $p\in P_A$

                //For h7 and h1 (if it is an ordianry net whose resource places have only one unit) 
                WRT = new decimal[,]
                {
                                     {57,0,85},{57,0,85},{57,0,85},{57,0,85},{57,0,0},
                                     {57,0,0},{0,0,0},{0,0,51},{0,0,51},{0,0,0},
                                     {0,0,0},{0,95,0},{0,0,0},{0,0,0},{0,0,0},
                                     {0,0,0},{0,0,0},{0,0,0},{0,0,0},{0,0,0},
                                     {0,78,75},{0,0,75},{0,0,75},{0,0,0},{0,0,0},
                                     {0,0,0},{0,70,0},{0,70,0},{0,0,0},{0,0,0},
                                     {93,0,175},{93,0,76},{93,0,76},{93,0,0},{93,0,0},
                                     {0,0,0},{0,0,0}
                }; //the weighted remaining time matrix 

                //For h8
                MRT = new decimal[] { 234, 165, 165, 165, 80, 80, 0, 51, 51, 0, 0, 272, 177, 177, 92, 92, 92, 0, 0, 0, 221, 143, 143, 68, 68, 0, 70, 70, 0, 0, 268, 169, 169, 93, 93, 0, 0 };//the minimal total time of EOTs that is required for an available token in $p$ to move to its end place                
                MR3 = new decimal[,]
                {                   {1,1,3},{1,0,3},{1,1,2},{1,0,2},{1,0,2},
                                    {1,0,1},{1,0,0},{1,0,1},{0,0,1},{0,0,1},
                                    {0,0,0},{1,2,2},{1,2,2},{1,1,2},{1,1,1},
                                    {1,0,2},{1,0,1},{1,0,0},{0,0,1},{0,0,0},
                                    {1,2,2},{1,2,2},{1,1,2},{1,1,2},{1,1,1},
                                    {1,0,0},{0,1,1},{0,1,0},{0,1,0},{0,0,0},
                                    {1,0,2},{1,0,2},{1,0,1},{1,0,1},{1,0,0},
                                    {1,0,0},{0,0,0}
                }; //a place $r\in P_R$ to its end place requires at most $n$ units of $r$

                //For h9
                X = new int[] { 234, 165, 165, 165, 80, 80, 0, 51, 51, 0, 0, 272, 177, 177, 92, 92, 92, 0, 0, 0, 221, 143, 143, 68, 68, 0, 70, 70, 0, 0, 268, 169, 169, 93, 93, 0, 0 };//the minimal processing time for a token from $p$ to its end place
                ER = 3;   //the number of all resource units in a PN
            }
            else if (fileNameLower == "huang2012fig1revised")
            {
                //General                                                          
                M0r = new int[] { 1, 1, 2 };//the number of tokens in each resource place at the initial marking   
                Upi = new int[,]
                {
                                         {0,0,0},{0,0,1},{0,1,0},{0,0,0},{0,0,1},
                                         {0,0,0},{1,0,0},{1,0,0},{0,0,0},{0,0,2},
                                         {0,0,0},{0,0,0},{0,1,0},{0,0,0},{0,1,0},
                                         {0,0,1},{0,0,0},{1,0,0},{0,0,1},{0,0,0},
                                         {0,0,0},{0,1,0},{0,0,0},{0,0,1},{0,0,0},
                                         {1,0,0},{0,0,1},{0,0,0},{0,1,0},{0,0,0},
                                         {0,0,0},{0,0,1},{0,0,0},{0,0,1},{0,0,0},
                                         {1,0,0},{0,0,0}
                };//the number of resource units of $r\in P_R$ that are required by $p\in P_A$


                //For h7 and h1 (if it is an ordianry net whose resource places have only one unit) 
                WRT = new decimal[,]
                {
                                           {57,0,42.5m},{57,0,42.5m},{57,0,42.5m},{57,0,42.5m},{57,0,0},
                                           {57,0,0},{0,0,0},{0,0,51},{0,0,51},{0,0,0},
                                           {0,0,0},{0,95,0},{0,0,0},{0,0,0},{0,0,0},
                                           {0,0,0},{0,0,0},{0,0,0},{0,0,0},{0,0,0},
                                           {0,78,37.5m},{0,0,37.5m},{0,0,37.5m},{0,0,0},{0,0,0},
                                           {0,0,0},{0,70,0},{0,70,0},{0,0,0},{0,0,0},
                                           {93,0,87.5m},{93,0,38},{93,0,38},{93,0,0},{93,0,0},
                                           {0,0,0},{0,0,0}
                }; //the weighted remaining time matrix

                //For h8
                MRT = new decimal[] { 234, 165, 165, 165, 80, 80, 0, 102, 102, 0, 0, 272, 177, 177, 92, 92, 92, 0, 0, 0, 221, 143, 143, 68, 68, 0, 70, 70, 0, 0, 268, 169, 169, 93, 93, 0, 0 };//the minimal total time of EOTs that is required for an available token in $p$ to move to its end place                
                MR3 = new decimal[,]
                {
                                          {1,1,4},{1,0,4},{1,1,3},{1,0,3},{1,0,3},
                                          {1,0,2},{1,0,0},{1,0,2},{0,0,2},{0,0,2},
                                          {0,0,0},{1,2,2},{1,2,2},{1,1,2},{1,1,1},
                                          {1,0,2},{1,0,1},{1,0,0},{0,0,1},{0,0,0},
                                          {1,2,2},{1,2,2},{1,1,2},{1,1,2},{1,1,1},
                                          {1,0,0},{0,1,1},{0,1,0},{0,1,0},{0,0,0},
                                          {1,0,2},{1,0,2},{1,0,1},{1,0,1},{1,0,0},
                                          {1,0,0},{0,0,0}
                }; //a place $r\in P_R$ to its end place requires at most $n$ units of $r$

                //For h9
                X = new int[] { 234, 165, 165, 165, 80, 80, 0, 51, 51, 0, 0, 272, 177, 177, 92, 92, 92, 0, 0, 0, 221, 143, 143, 68, 68, 0, 70, 70, 0, 0, 268, 169, 169, 93, 93, 0, 0 }; //the minimal processing time for a token from $p$ to its end place
                ER = 4;   //the number of all resource units in a PN
            }
            else if (fileNameLower == "xiong98")
            {
                //General
                M0r = new int[] { 1, 1, 1 };//the number of tokens in each resource place at the initial marking   
                Upi = new int[,]
                {
                                        {0,0,0},{1,0,0},{0,0,0},{0,1,0},{0,0,0},
                                        {0,0,1},{0,0,0},{0,0,0},{0,0,1},{0,0,0},
                                        {1,0,0},{0,1,0},{0,0,0},{0,0,0},{0,0,0},
                                        {1,0,0},{0,0,0},{0,0,1},{0,0,0},{0,1,0},
                                        {0,0,0},{0,0,0},{0,1,0},{0,0,0},{0,0,1},
                                        {0,0,0},{1,0,0},{0,0,0}
                };//the number of resource units of $r\in P_R$ that are required by $p\in P_A$

                //For h7 and h1 (if it is an ordianry net whose resource places have only one unit) 
                WRT = new decimal[,]
                {
                                       {2,3,4},{0,3,4},{0,3,4},{0,0,4},{0,0,4},
                                       {0,0,0},{0,0,0},{2,2,4},{2,2,0},{2,2,0},
                                       {0,2,0},{0,2,0},{0,0,0},{0,0,0},{3,3,5},
                                       {0,3,5},{0,3,5},{0,3,0},{0,3,0},{0,0,0},
                                       {0,0,0},{3,3,4},{3,0,4},{3,0,4},{3,0,0},
                                       {3,0,0},{0,0,0},{0,0,0}
                };//the weighted remaining time matrix
                //For h8
                MRT = new decimal[] { 9, 7, 7, 4, 4, 0, 0, 8, 4, 4, 2, 2, 0, 0, 11, 8, 8, 3, 3, 0, 0, 10, 7, 7, 3, 3, 0, 0 };//the minimal total time of EOTs that is required for an available token in $p$ to move to its end place                
                MR3 = new decimal[,]
                {
                                         {1,1,1},{1,1,1},{0,1,1},{0,1,1},{0,0,1},
                                         {0,0,1},{0,0,0},{1,1,1},{1,1,1},{1,1,0},
                                         {1,1,0},{0,1,0},{0,1,0},{0,0,0},{1,1,1},
                                         {1,1,1},{0,1,1},{0,1,1},{0,1,0},{0,1,0},
                                         {0,0,0},{1,1,1},{1,1,1},{1,0,1},{1,0,1},
                                         {1,0,0},{1,0,0},{0,0,0}
                }; //a place $r\in P_R$ to its end place requires at most $n$ units of $r$

                //For h9
                X = new int[] { 9, 7, 7, 4, 4, 0, 0, 8, 4, 4, 2, 2, 0, 0, 11, 8, 8, 3, 3, 0, 0, 10, 7, 7, 3, 3, 0, 0 };//the minimal processing time for a token from $p$ to its end place
                ER = 3;   //the number of all resource units in a PN
            }
            else if (fileNameLower == "new4x3")
            {

                //General
                M0r = new int[] { 1, 1, 1 };//the number of tokens in each resource place at the initial marking   
                Upi = new int[,]
                    {
                                        {0,0,0},{1,0,0},{0,0,0},{0,1,0},{0,0,0},
                                        {0,0,1},{0,0,0},{0,0,0},{0,1,0},{0,0,0},
                                        {0,0,1},{0,0,0},{1,0,0},{0,0,0},{0,0,0},
                                        {0,0,1},{0,0,0},{1,0,0},{0,0,0},{0,1,0},
                                        {0,0,0},{0,0,0},{0,0,1},{0,0,0},{0,1,0},
                                        {0,0,0},{1,0,0},{0,0,0}
                    };//the number of resource units of $r\in P_R$ that are required by $p\in P_A$

                //For h1 and h7 
                WRT = new decimal[,]
                    {
                                       {5,4,4},{0,4,4},{0,4,4},{0,0,4},{0,0,4},
                                       {0,0,0},{0,0,0},{2,2,5},{2,0,5},{2,0,5},
                                       {2,0,0},{2,0,0},{0,0,0},{0,0,0},{2,5,5},
                                       {2,5,0},{2,5,0},{0,5,0},{0,5,0},{0,0,0},
                                       {0,0,0},{2,4,2},{2,4,0},{2,4,0},{2,0,0},
                                       {2,0,0},{0,0,0},{0,0,0}
                    };//the weighted remaining time matrix
                //For h8
                MRT = new decimal[] { 13, 8, 8, 4, 4, 0, 0, 9, 7, 7, 2, 2, 0, 0, 12, 7, 7, 5, 5, 0, 0, 8, 6, 6, 2, 2, 0, 0 };//the minimal total time of EOTs that is required for an available token in $p$ to move to its end place                
                MR3 = new decimal[,]
                    {
                                         {1,1,1},{1,1,1},{0,1,1},{0,1,1},{0,0,1},
                                         {0,0,1},{0,0,0},{1,1,1},{1,1,1},{1,0,1},
                                         {1,0,1},{1,0,0},{1,0,0},{0,0,0},{1,1,1},
                                         {1,1,1},{1,1,0},{1,1,0},{0,1,0},{0,1,0},
                                         {0,0,0},{1,1,1},{1,1,1},{1,1,0},{1,1,0},
                                         {1,0,0},{1,0,0},{0,0,0}
                    }; //a place $r\in P_R$ to its end place requires at most $n$ units of $r$

                //For h9
                X = new int[] { 13, 8, 8, 4, 4, 0, 0, 9, 7, 7, 2, 2, 0, 0, 12, 7, 7, 5, 5, 0, 0, 8, 6, 6, 2, 2, 0, 0 };//the minimal processing time for a token from $p$ to its end place
                ER = 3;   //the number of all resource units in a PN
            }
            else if (fileNameLower == "chen2011big")
            {
                //General
                M0r = new int[] { 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2 };//the number of tokens in each resource place at the initial marking   
                Upi = new int[,]
                {
                                         {0,0,0,0,0,0,0,0,0,0,0,0},{1,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,1,0,0,0,0,0,0},{0,1,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,1,0,0,0,0,0},
                                         {0,0,0,0,0,0,0,1,0,0,0,0},{0,0,1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,1,0,0,0},{0,0,1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0},
                                         {0,1,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,1,0},{0,1,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,1,0,0,0,0,0},{0,0,0,0,1,0,0,0,0,0,0,0},
                                         {0,0,0,0,0,0,0,0,0,0,0,0},{1,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,1,0,0,0,0},{0,0,1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,1,0,0,0},
                                         {0,0,1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,1,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,1,0},{0,1,0,0,0,0,0,0,0,0,0,0},
                                         {0,0,0,0,0,0,0,0,0,1,0,0},{0,0,0,0,0,0,0,0,1,0,0,0},{0,0,1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,1,0,0,0,0,0},{0,1,0,0,0,0,0,0,0,0,0,0},
                                         {0,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,1,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,1},{1,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,1,0,0,0,0,0,0},
                                         {1,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0},
                                         {0,0,0,0,0,0,0,0,0,0,0,0}
                };//the number of resource units of $r\in P_R$ that are required by $p\in P_A$

                //For h7 and h1 (if it is an ordianry net whose resource places have only one unit) 
                WRT = new decimal[,]
                {

                                         {5,0,2,0,0,0,0,0,0,0,0,0},{0,0,2,0,0,0,0,0,0,0,0,0},{0,4,2,0,0,0,3,0,0,0,0,0},{0,0,2,0,0,0,3,0,0,0,0,0},{0,0,2,0,0,0,0,0,0,0,0,0},
                                         {0,0,4,0,0,0,0,0,0.5m,0,0,0},{0,0,2,0,0,0,0,0,0.5m,0,0,0},{0,0,2,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0},{0,6,0,0,4,0,1,0,0,0,1,0},
                                         {0,3,0,0,4,0,1,0,0,0,1,0},{0,3,0,0,4,0,1,0,0,0,0,0},{0,0,0,0,4,0,1,0,0,0,0,0},{0,0,0,0,4,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0},
                                         {7,0,8,0,0,0,0,1,1,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0},{7,0,0,0,0,0,0,0,0,0,0,0},{7,0,0,0,0,0,0,1,0,0,0,0},{7,0,3,0,0,0,0,1,0,0,0,0},
                                         {7,0,3,0,0,0,0,1,1,0,0,0},{0,2,0,5,0,0,0,0,0,0,0,0},{0,2,0,0,0,0,0,0,0,0,0,0},{0,6,0,0,0,0,0,0,0,0.5m,0,0},{0,2,0,0,0,0,0,0,0,0.5m,0,0},
                                         {0,2,0,0,0,0,0,0,0,0,0,0},{0,2,4,0,0,0,1.5m,0,0,0,0,0},{0,2,0,0,0,0,1.5m,0,0,0,0,0},{0,2,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0},
                                         {10,0,0,0,6,0.5m,0,0,0,0,0,1.5m},{10,0,0,0,0,0.5m,0,0,0,0,0,1.5m},{10,0,0,0,0,0.5m,0,0,0,0,0,0},{7,0,0,0,0,0.5m,0,0,0,0,0,0},{7,0,0,0,0,0,0,0,0,0,0,0},
                                         {0,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0},
                                         {0,0,0,0,0,0,0,0,0,0,0,0}
                }; //the weighted remaining time matrix. 

                //For h8
                MRT = new decimal[] { 13, 8, 12, 8, 2, 5, 3, 2, 0, 14, 11, 9, 6, 4, 0, 19, 0, 7, 9, 12, 14, 15, 10, 7, 3, 2, 9, 5, 2, 0, 20, 14, 11, 8, 7, 0, 0, 0, 0, 0, 0 };//the minimal total time of EOTs that is required for an available token in $p$ to move to its end place                
                MR3 = new decimal[,]
                {
                                         {1,1,2,0,0,1,1,1,1,0,0,0},{1,1,2,0,0,1,1,1,1,0,0,0},{0,1,1,0,0,1,1,0,0,0,0,0},{0,1,1,0,0,0,1,0,0,0,0,0},{0,0,1,0,0,0,1,0,0,0,0,0},
                                         {0,0,2,0,0,0,0,1,1,0,0,0},{0,0,2,0,0,0,0,0,1,0,0,0},{0,0,1,0,0,0,0,0,1,0,0,0},{0,0,1,0,0,0,0,0,0,0,0,0},{0,2,0,0,1,0,1,0,0,0,1,0},
                                         {0,2,0,0,1,0,1,0,0,0,1,0},{0,1,0,0,1,0,1,0,0,0,1,0},{0,1,0,0,1,0,1,0,0,0,0,0},{0,0,0,0,1,0,1,0,0,0,0,0},{0,0,0,0,1,0,0,0,0,0,0,0},
                                         {1,0,2,0,0,0,0,1,1,0,0,0},{1,0,0,0,0,0,0,0,0,0,0,0},{1,0,0,0,0,0,0,1,0,0,0,0},{1,0,1,0,0,0,0,1,0,0,0,0},{1,0,1,0,0,0,0,1,1,0,0,0},
                                         {1,0,2,0,0,0,0,1,1,0,0,0},{0,2,1,1,0,0,1,0,1,1,1,0},{0,2,1,1,0,0,1,0,1,1,1,0},{0,2,0,0,0,0,0,0,0,1,1,0},{0,2,0,0,0,0,0,0,0,1,0,0},
                                         {0,1,0,0,0,0,0,0,0,1,0,0},{0,1,1,0,0,0,1,0,1,0,0,0},{0,1,1,0,0,0,1,0,0,0,0,0},{0,1,0,0,0,0,1,0,0,0,0,0},{0,1,0,0,0,0,0,0,0,0,0,0},
                                         {2,0,0,0,1,1,0,0,0,0,0,1},{2,0,0,0,1,1,0,0,0,0,0,1},{2,0,0,0,0,1,0,0,0,0,0,1},{2,0,0,0,0,1,0,0,0,0,0,0},{1,0,0,0,0,1,0,0,0,0,0,0},
                                         {1,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0},
                                         {0,0,0,0,0,0,0,0,0,0,0,0}
                }; //a place $r\in P_R$ to its end place requires at most $n$ units of $r$

                //For h9
                X = new int[] { 13, 8, 12, 8, 2, 5, 3, 2, 0, 14, 11, 9, 6, 4, 0, 19, 0, 7, 9, 12, 14, 15, 10, 7, 3, 2, 9, 5, 2, 0, 20, 14, 11, 8, 7, 0, 0, 0, 0, 0, 0 };//the minimal processing time for a token from $p$ to its end place
                ER = 19;   //the number of all resource units in a PN
            }//fileNameLower == "chen2011big"
            else //防止fileName匹配不成功
            {
                //General
                M0r = new int[] { 1, 1 };//the number of tokens in each resource place at the initial marking
                Upi = new int[,]
                {
                                        {0,0,0,0,0,0},{0,0,0,0,1,0}
                }; //the number of resource units of $r\in P_R$ that are required by $p\in P_A$

                //For h7 and h1 (if it is an ordianry net whose resource places have only one unit)
                WRT = new decimal[,]
                {
                                        {0,0,3,0,7,5},{0,0,3,0,4,5}
                };//the weighted resource time matrix

                //For h8
                MRT = new decimal[] { 1, 1 };//the minimal total time of EOTs that is required for an available token in $p$ to move to its end place
                MR3 = new decimal[,]
                {
                                       {1,1,1,0,2,1},{1,1,1,0,2,1}
                 };//a place $r\in P_R$ to its end place requires at most $n$ units of $r$

                //For h9
                X = new int[] { 17, 14 }; //the minimal processing time for a token from $p$ to its end place
                ER = 0;  // the number of all resource units in a PN
            }







            if (hMethod == 0)//h0=0            
                return 0;            


            else if (hMethod == 1) 
            //h1=max_i{e_i(M)} plus R; h1 comes from Xiong98. e_r(M) is the sum of operation times of those remaining operations for all jobs which are planned to be processed with the ith resource.
            //h1 is only for the ordinary nets in which resource places have only one resource unit and each operation uses only one resource.For example, Xiong98, New4x3, Huang2012Fig1, ChenFig5. Not for generalized nets and the nets whose resource places may have more than one units (ChenFig6).
            //So, h1 uses a simple WRT that does not consider weight.      （只考虑ordianry nets，并且每个资源库所的unit数为1以及每个操作只使用一个资源）
            {
                decimal[] resourceTime = new decimal[AStar.N_P_R];//每个资源的剩余操作时间包含剩余托肯时间
                for (int i = 0; i < AStar.N_P_R; ++i)                
                    resourceTime[i] = 0;
                
               
                for (int n = 0; n < AStar.N_P - AStar.N_P_R; ++n)
                {
                    if (_MF[n] != 0 && AStar.operationTimes[n] > 0)
                    {
                        for (int i = 0; i < AStar.N_P_R; ++i)                        
                            resourceTime[i] += WRT[n, i]; //因为对于使用h1的PN，每个资源只有一个unit，所以每个操作库所最多有一个托肯                        
                        if(_RF[n,0] != 0)
                            for (int i = 0; i < AStar.N_P_R; ++i)
                                if (Upi[n, i] == 1) //因为对于使用h1的PN，每个操作只使用一个资源 
                                    resourceTime[i] += _RF[n, 0];                             
                    }
                }
                
                decimal max = 0;
                for (int i = 0; i < resourceTime.Length; ++i)
                {
                    if (max < resourceTime[i])
                    {
                        max = resourceTime[i];
                    }
                }
                return max;
            }



            else if (hMethod == 4)//h4=Node depth            
                return (-(_MarkingDepth + 1));



            else if (hMethod == 7)   
            //h7=h_H=max_r{M*MRT+sum{R*Upi/M_0}}, which comes from Eq.(9.2) in Chapter 9 of our book. It is an admissible and highly informed heuristic function that can be used for the nets with alternative routings, weighted arcs, and multiple resource copies.     
            //Before h7=h_H is used, the number of resource places, the WRT matrix, the Upi matrix, and the M0r vector of the Petri net should be given. 
            //WRT denotes the weighted remaining time whose definition is given in Chapter 9 of our book. Note that MRT only consider non-resource places.
            //Upi(r) denotes the units of r that are required by the operation denoted by the place pi. Note that Upi only consider non-resource places.
            //M0r denotes the number of tokens in each resource place at the initial marking.
            {

                decimal[] resourceTime = new decimal[AStar.N_P_R];
                for (int i = 0; i < AStar.N_P_R; ++i)
                    resourceTime[i] = 0;                       
               

                //h7=h_H
                for (int n = 0; n < AStar.N_P - AStar.N_P_R; ++n) //for each non-resource place
                {
                    //取p_i中所有非零剩余时间之和
                    decimal temp = 0;
                    for (int t = 0; t < AStar.MAX_TOK_PA; t++)
                    {
                        temp += _RF[n, t];
                    }

                    if (_MF[n] != 0)
                    {
                        for (int x = 0; x < AStar.N_P_R; ++x)
                        {
                            resourceTime[x] += _MF[n] * (decimal)WRT[n, x];
                            resourceTime[x] += temp * (decimal)Upi[n, x] / M0r[x];
                        }
                    }
                }

                //h=max_i
                decimal max = 0;
                for (int i = 0; i < resourceTime.Length; ++i)
                {
                    if (max < resourceTime[i])
                    {
                        max = resourceTime[i];
                    }
                }

                return max;
            }

            
            else if (hMethod == 710)
            //h710(Pohl: dynamic weighting)=h+ep2*[1-depth(M)/N]*h, h=h7=h_H, 此时要在AStar.cs中设置总深度N=totalDepth！  大-小，线性
            //Before h710 is used, the number of resource places, the WRT matrix, the Upi matrix, and the M0r vector of the Petri net should be given in the class AStar. 
                //需要选择所用的Petri网，以便自动计算深度totalDepth
            {
                decimal[] resourceTime = new decimal[AStar.N_P_R];
                for (int i = 0; i < AStar.N_P_R; ++i)
                    resourceTime[i] = 0;


                //h7=h_H
                for (int n = 0; n < AStar.N_P - AStar.N_P_R; ++n) //for each non-resource place
                {
                    //取p_i中所有非零剩余时间之和
                    decimal temp = 0;
                    for (int t = 0; t < AStar.MAX_TOK_PA; t++)
                    {
                        temp += _RF[n, t];
                    }

                    if (_MF[n] != 0)
                    {
                        for (int x = 0; x < AStar.N_P_R; ++x)
                        {
                            resourceTime[x] += _MF[n] * (decimal)WRT[n, x];
                            resourceTime[x] += temp * (decimal)Upi[n, x] / M0r[x];
                        }
                    }
                }

                //max=h_H
                decimal max = 0;
                for (int i = 0; i < resourceTime.Length; ++i)
                {
                    if (max < resourceTime[i])
                    {
                        max = resourceTime[i];
                    }
                }

                //For ChenFig5 and its variants！！！！！！！
                decimal totalDepth=7*(AStar.StartM[0]+AStar.StartM[7]); //p0和p8为start places

                //For ChenFig6 and its variants！！！！！！！
                //decimal totalDepth = 4 * AStar.StartM[0] + 6 * AStar.StartM[4] + 6 * AStar.StartM[13]; //p1,p5和p14为start places

                
                decimal dndG = Math.Round ((_MarkingDepth + 1) / totalDepth,3);  //结果为小数的乘除，操作数都要为decimal，否则结果0.2会成为0


                //decimal final = max + (decimal)ep2 * (1 - dndG) * max;  //(Pohl: dynamic weighting)=h+ep2*[1-dn/dG]*h, h=h7=h_H, 此时要设置总深度N=dG=totalDepth！  大-小，(1+ep2)*h->h，线性               

                //decimal final = max + (decimal)ep2 * dndG * max;  //(reversed Pohl: dynamic weighting)=h+ep2 * (dn/dG) *h, h=h7=h_H, 此时要设置总深度N=dG=totalDepth！  小-大，线性

                decimal final = max + (decimal)ep2 * (decimal)Math.Round(Math.Pow( 1 - (double)dndG, 2),2) * max;  //(Pohl)=h+ep2*[1-dn/dG]^2*h, h=h7=h_H, 此时要设置总深度N=dG=totalDepth！   大-小，2次，凹

                //decimal final = max + (decimal)ep2 * (decimal)Math.Round(1 - Math.Pow((double)dndG, 2), 2) * max;  //(Pohl)=h+ep2*{1-[dn/dG]^2}*h, h=h7=h_H, 此时要设置总深度N=dG=totalDepth！   大-小，2次，凸
                
                return final;//                
            }           
            
            

            
            else if (hMethod == 8)
            //h8=\sum{j(p,i)}{(R(p, i)*\sum{U(p, r)}+MRT(p)}+\sum{\delta(S, r)*G(S, r)}/{\sum((M_{P/P_R}^T*MR^3)^{C}} comes from our T-SMC2023. //Note that we assume that \delta(S, r)*G(S, r)=0 since both ours and Luo's have it in their heuristic functions and it is hard to calculate.
            //Upi[n, i] denotes the number of resource units of $i\in P_R$ that are required by $p\in P_A$.
            //MRT(p) denotes the minimal total time of EOTs that is required for an available token in $p$ to move to its end place.
            //MR^3 denotes a $|P\setminus P_R|\times|P_R|$ matrix such that if moving an unavailable token in a place $p\in P\setminus P_R$ to its end place requires at most $n$ units of $r$.
            //M0r denotes the number of resource units of ri.
            
            {
                decimal h = 0;
                decimal h_numerator = 0;
                decimal h_denominator = 0;

                decimal totalRinP_n;

                //Calculation of the h's numerator                  
                for (int n = 0; n < AStar.N_P - AStar.N_P_R; ++n)//for each non-resource place
                {

                    decimal sumU = 0; ;
                    for (int i = 0; i < AStar.N_P_R; ++i)//sumU is the number of the resource units required by p_n
                    {
                        sumU += (decimal)Upi[n, i];
                    }

                    totalRinP_n = 0;
                    if (_MF[n] != 0)
                    {
                        for (int t = 0; t < AStar.MAX_TOK_PA; t++) //totalRinP_n is the sum of the remaining token time in p_n
                        {
                            totalRinP_n += _RF[n, t];
                        }
                        h_numerator += totalRinP_n * sumU + (decimal)_MF[n] * MRT[n];
                    }
                }

                //Calculation of the denominator
                decimal MxMR3_i; //MxMR3_i is the ith element in the MxMR3 vector

                for (int i = 0; i < AStar.N_P_R; ++i)
                {
                    MxMR3_i = 0;
                    for (int n = 0; n < AStar.N_P - AStar.N_P_R; ++n)
                    {
                        MxMR3_i += (decimal)_MF[n] * MR3[n, i];
                    }
                    if (MxMR3_i > M0r[i]) //The implementation of the C function in h
                    {
                        MxMR3_i = M0r[i];
                    }

                    h_denominator += MxMR3_i;
                }


                //Calculation of h             
                if (h_denominator != 0)
                {
                    h = h_numerator / h_denominator;
                    h = Math.Floor(h * 100) / 100; //向下取两位小数
                }
                else //in case the denominator is zero   
                    h = 0;

                return h;

            }


            else if (hMethod == 9)
            //h9=\sum{j(p,i)}{(R(p, i)+X(p)}+\sum{\delta(S, r)*G(S, r)}/|ER| comes from 2015LuoTASE. //Note that Luo assumes that \delta(S, r)*G(S, r)=0 since it is hard to calculate.
            //X denotes the minimal processing time from $p$ to its end place. ER  is the set of resource instances.            
            {
                decimal h = 0;
                decimal h_numerator = 0;


                //Calculation of the numerator
                for (int n = 0; n < AStar.N_P - AStar.N_P_R; ++n) //for each non-resource place
                {

                    decimal totalRinP_n = 0;
                    if (_MF[n] != 0)
                    {
                        for (int t = 0; t < AStar.MAX_TOK_PA; t++)
                        {
                            totalRinP_n += (decimal)_RF[n, t];  //totalRinP_n is the sum of the remaining token time in p_n
                        }
                        h_numerator += totalRinP_n + (decimal)_MF[n] * (decimal)X[n];
                    }
                }


                //Calculation of h9
                h = h_numerator / (decimal)ER;
                h = Math.Floor(h * 100) / 100; //向下取两位小数

                return h;
            }


            else if (hMethod == 10)
            //h10=\max_{j(p,i)\in J}{(R(p, i)+X(p)} comes from our T-SMC2023.  
            //X denotes the minimal processing time of an available token in $p$ to move from $p$ to its end place            
            {
                decimal h = 0;

                for (int n = 0; n < AStar.N_P - AStar.N_P_R; ++n) //for each non-resource place                
                    if (_MF[n] != 0 && h < _RF[n, 0] + (decimal)X[n])
                        h = _RF[n, 0] + (decimal)X[n];

                return h;
            }




            return 0;
        }






        public virtual decimal CalculateH2nd(int h2ndMethod) // calculate the second heursitic value for nodes in OPEN; only applicable to some search strategies
        {         
            if (h2ndMethod == 2)
                return (-(_MarkingDepth + 1));

            return 0;
        }






        public virtual void FindEnabledTransitions()//寻找当前标识（_M）下使能的变迁，并对EnabledTransitions赋值（1：使能，0：非使能）
        {//Find enabled transitions at a marking. It will assign values to EnabledTransitions such that 1 denotes its corresponding transition is enabled and 0 denotes not.
            int e;
            for (int j = 0; j < AStar.N_T; ++j)
            {
                e = 1;
                for (int i = 0; i < AStar.N_P; ++i)
                {
                    if (AStar.LMINUS[i, j] != 0 && _M[i] < AStar.LMINUS[i, j]) //变迁使能的条件：当前输入库所的托肯数量大于变迁输入弧所需的输入托肯数量（ M(p) > I(p, t) ）
                    {
                        e = 0;
                        continue;
                    } 
                }
                _EnabledTransitions[j] = e; //_EnabledTransitions = new int[AStar.N_T];
            }
        }


        



        public virtual void GetSuccessors(string fileName, ArrayList Successors, int hMethod, int h2ndMethod, decimal ep2) //获得当前节点的所有子节点，并添加到Successors列表中
        {//Get the child nodes of the current node and handle them with OPEN and CLOSED. 
            //寻找当前标识下使能的变迁
            FindEnabledTransitions();//Find the enabled transitions at the current node.
            for (int i = 0; i < _EnabledTransitions.Length; ++i)
            {
                if (_EnabledTransitions[i] == 1) //对于每一个使能的变迁 if the transition is enabled
                {
                    //程序选择哪个变迁取决于OPEN中相同f值的节点如何排队，即tie-breaking规则
                    

                    //Calculate _Delt=max{R(pi,k-W(pi, tj)+1}; Because W(pi,tj)=1 in SC-nets, _Delt=max{R(pi,k)}. 
                    //R(pi,k) denotes the remaining token time of the last existing token in pi that is a pre-place of the transition selected to fire
                    _Delt = 0;
                    for (int x = 0; x < AStar.N_P; ++x)//zzx
                    {
                        if (AStar.LMINUS[x, i] > 0 && AStar.operationTimes[x]>0) // if it is a operation pre-place of the transition
                        {//注意，对于每个库所而言，R里面的托肯按照剩余时间非递增排序。且变迁从每个非资源输入库所需要的托肯数为1
                            if (_Delt < _R[x, _M[x] - 1])//参看我的书delta的定义，-1是因为下标从0开始
                                _Delt = _R[x, _M[x] - 1];
                        }
                    }


                    //从变迁的输入库所中移去相应的托肯  Remove tokens from the pre-places of the transition
                    //M(k)+ = M(k)- - LMINUS*u(k) , M(k)+ 和M(k)- 分别表示托肯移走前后的系统标识
                    for (int n = 0; n < AStar.N_P; ++n)
                    {
                        if (AStar.LMINUS[n, i] > 0)
                            _MZ[n] = _M[n] - AStar.LMINUS[n, i]; //_MZ：标识状态M(k)+; _MZ: denotes M(k)+
                        else
                            _MZ[n] = _M[n];
                    }

                    //向变迁的所有输出库所中添加相应托肯 Add tokens into the post-places of the transition
                    //M(k+1)- = M(k)+ + LPLUS*u(k)
                    for (int n = 0; n < AStar.N_P; ++n)
                    {
                        if (AStar.LPLUS[n, i] > 0)
                            _MF[n] = _MZ[n] + AStar.LPLUS[n, i];
                        else
                            _MF[n] = _MZ[n];
                    }


                    //在剩余托肯时间向量(即R)中逐个元素地减去_Delt，若值小于0则赋值为0   ZZX
                    //Subtract _Delt from each element of R. If the result is below 0, then set the element to 0. 
                    //计算 R(k)+z = R(k)-z - _Delt(k)z
                    for (int n = 0; n < AStar.N_P; ++n)
                    {
                        for (int m = 0; m < AStar.MAX_TOK_PA; ++m)
                        {
                            _RZ[n, m] = _R[n, m] - _Delt;
                            if (_RZ[n, m] < 0)
                                _RZ[n, m] = 0;
                        }
                    }

                    //向变迁的所有输出库所的R中开头位置加入新托肯的操作时间，其它托肯的剩余时间向后移动。所以对于一个非资源库所，其托肯按剩余托肯时间由大到小排列 
                    //R(k+1)-z = R(k)+z + t(k)z
                    for (int n = 0; n < AStar.N_P; ++n)
                    {
                        if (AStar.LPLUS[n, i] > 0 && AStar.operationTimes[n]>0)//if p_n is a post-operation place of the transition t_i
                        {
                            //All remaining token times in R(p_n, .) move one step to the right
                            for (int j = AStar.MAX_TOK_PA  - 1; j > 0; --j)                   
                                    _RF[n, j] = _RZ[n, j - 1];

                            //Add the operation time of the place to the first entry of R(p_n,.).
                            _RF[n, 0] = AStar.operationTimes[n];
                        }
                        else
                        {
                            for (int j = 0; j < AStar.MAX_TOK_PA; ++j)
                                _RF[n, j] = _RZ[n, j];
                        }
                    }
                    

                    decimal g = _gValue + _Delt;
                    decimal h = CalculateH(fileName, hMethod, ep2);
                    decimal f = g + h;

                    decimal h2nd = CalculateH2nd(h2ndMethod);//Huang2023: 计算子节点的h2nd，通常深度优先
                    //CalculateH2nd(int) 1 = max{ei(m)}; 2 = -dep(m)                    

                    AStarNode newNode = new AStarNode(this, GoalNode, g, h, f, _MF, _RF, i, _MarkingDepth + 1, h2nd, _Delt);
                    //AStarNode(父节点, 目标节点, g值, h值, f值, 节点的标识, 该标识下所有库所的剩余托肯时间, 产生本标识所发射的变迁, 标志的深度, h2nd选择所用第二个启发函数(用于对OPEN中的节点进行二次排序),从父标识到变迁发射得到本标识所用时间)
                    Successors.Add(newNode);
                }
            }//for循环结束 the end of the for structure.
        }





        public virtual void PrintNodeInfo() //打印当前节点的信息  Print the info of the current node. 
        {
            
            Console.Write("f:{0} g:{1} h:{2} tFireFrom:{3} Depth:{4}", _fValue, _gValue, _hValue, _tFireFrom + 1, _MarkingDepth);
                                    

            Console.Write(" tEnabled:");
            for (int n = 0; n < _EnabledTransitions.Length; ++n)
            {
                if (_EnabledTransitions[n] == 1)
                    Console.Write("{0} ", n + 1);
            }
            Console.Write(" M:");
            for (int i = 0; i < _M.Length; ++i)//输出M中为1的places
            {
                if (_M[i] == 1)
                    Console.Write("{0} ", i + 1);
                if (_M[i] > 1)
                    Console.Write("{0}({1}) ", i + 1, _M[i]);
            }
            Console.Write(" R:");
            for (int n = 0; n < AStar.N_P; ++n)
                for (int m = 0; m < AStar.MAX_TOK_PA; ++m)
                {
                    if (_R[n, m] != 0)
                        Console.Write("[{0}，{1}]:{2}  ", n + 1, m + 1, _R[n, m]);
                }
            Console.WriteLine();
        }

        #endregion

        #region Overridden Methods

        public override bool Equals(object obj)
        {
            return IsSameStateM_R((AStarNode)obj);
        }

        public override int GetHashCode()
        {
            return base.GetHashCode();
        }

        #endregion

        #region IComparable Members

        public int CompareTo(object obj)
        {
            return (_fValue.CompareTo(((AStarNode)obj).fValue));
        }

        #endregion
    }






    public sealed class AStar //基于PN的A*运行所需的属性和行为,sealed表示此类不能被继承
    {
        #region Private Fields
        private AStarNode _StartNode;//起始节点 the start node of the search
        private AStarNode _GoalNode;//目标节点 the goal node
        private Heap _OPEN;//OPEN列表 the OPEN list
        private Heap _CLOSED;//CLOSED列表 the CLOSED list
        private ArrayList _Successors;//子节点列表 the list to contain the child nodes
        private ArrayList _Solution;//结果方案列表 the list contains the nodes in the obtained schedule
        private int _NExpandedNodes;//已扩展节点数 the number of expanded nodes
        private int _Loop; //AStar的循环次数


        #endregion


        #region Properties
        //属性，通常首字母大写。外类对此类非静态属性可通过对象.属性访问；如果是静态static，则通过类.属性访问        

        public static decimal[] operationTimes;//各库所的操作时间（资源库所操作时间为0） Operation times of places (for any resource place and idle place, it equals zero); const常量需要定义时就赋值

        public static int[,] LPLUS;//后置关联矩阵L+ The post-incidence matrix L+
        public static int[,] LMINUS;//前置关联矩阵L- The pre-incidence matrix L-

        public static int N_P;//Petri网中库所数(含资源)  The number of places in the net (including resource places)
        public static int N_T;//Petri网中变迁数 The number of transitions in the net
        public static int N_P_R;//Petri网中资源库所数 The number of resource places
        public static int MAX_TOK_PA; //活动库所的最大容量 The maximal number of tokens in any activity place. It will be set automatically by analyzing the input files.

        public static int[] StartM;//开始节点的标识向量 The marking of the start node
        public static int[] GoalM;//目标节点的标识向量 The marking of the goal node
        public static decimal[,] StartR;//开始节点的剩余托肯时间矩阵 The remaining token time matrix of the start node
        public static decimal[,] GoalR;//目标节点的剩余托肯时间矩阵 The remaining token time matrix of the end node

      

        #endregion



        #region Constructors

        public AStar(string initialMFile, string incidenceMatrixFile)//构造函数
        {
            _OPEN = new Heap();
            _CLOSED = new Heap();
            _Successors = new ArrayList();
            _Solution = new ArrayList();

            Read_initfile(initialMFile);
            Read_matrixfile(incidenceMatrixFile);



            Console.WriteLine("Petri网中库所数(含资源) The number of places (including resource places)：" + N_P);
            Console.WriteLine("Petri网中变迁数 The number of transitions：" + N_T);
            Console.WriteLine("Petri网中资源库所数 The number of resource places：" + N_P_R);
            Console.WriteLine("初始标识 The initial marking：");

            for (int i = 0; i < N_P; i++)
            {
                Console.Write(StartM[i] + " ");
            }
            Console.WriteLine();
            Console.WriteLine("操作的时间 Operation times：");
            for (int i = 0; i < N_P; i++)
            {
                Console.Write(operationTimes[i] + " ");
            }
            Console.WriteLine();
            Console.WriteLine("目标标识 The goal marking：");
            for (int i = 0; i < N_P; i++)
            {
                Console.Write(GoalM[i] + " ");
            }
            Console.WriteLine();
            Console.WriteLine("后置伴随矩阵 The post-incidence matrix L+：");
            for (int i = 0; i < N_P; ++i)
            {
                for (int j = 0; j < N_T; ++j)
                {
                    Console.Write(LPLUS[i, j] + " ");
                }
                Console.WriteLine();
            }
            Console.WriteLine();
            Console.WriteLine("前置伴随矩阵 The pre-incidence matrix L-：");
            for (int i = 0; i < N_P; ++i)
            {
                for (int j = 0; j < N_T; ++j)
                {
                    Console.Write(LMINUS[i, j] + " ");
                }
                Console.WriteLine();
            }
            Console.WriteLine();


            StartR = new decimal[N_P, MAX_TOK_PA];//资源库所的所有R都为0
            GoalR = new decimal[N_P, MAX_TOK_PA];
            for (int i = 0; i < N_P; ++i)
                for (int j = 0; j < MAX_TOK_PA; ++j)
                {
                    StartR[i, j] = 0;
                    GoalR[i, j] = 0;
                }

        }

        #endregion




        #region Private Methods

        private static void Read_initfile(string fileName)
        {
            StreamReader SR;
            try
            {
                SR = File.OpenText(fileName);
            }
            catch
            {
                Console.Write(fileName + " open failed!");
                return;
            }
            string stringALine;
            string[] stringWords;

            //init文件的第一行  The first line of the init.txt
            {
                stringALine = SR.ReadLine();

                stringALine = stringALine.Trim();//去头尾空格
                while (stringALine == "")//去空行
                {
                    stringALine = SR.ReadLine();
                    stringALine = stringALine.Trim();
                }

                stringWords = System.Text.RegularExpressions.Regex.Split(stringALine, @"\s{1,}"); //以一个或多空格为分隔
                
                
                //Petri网中库所数(含资源)
                N_P = stringWords.Length;

                //初始marking
                StartM = new int[N_P];
                for (int i = 0; i < stringWords.Length; ++i)
                {
                    StartM[i] = Convert.ToInt32(stringWords[i]);
                }
            }


            //init文件的第二行 The second line of the init.txt
            {
                stringALine = SR.ReadLine(); //ReadLine可能返回空行

                stringALine = stringALine.Trim();
                while (stringALine == "")
                {
                    stringALine = SR.ReadLine();
                    stringALine = stringALine.Trim();
                }
               
                stringWords = System.Text.RegularExpressions.Regex.Split(stringALine, @"\s{1,}"); //以一个或多空格为分隔


                operationTimes = new decimal[N_P]; //各库所的操作时间
                for (int i = 0; i < stringWords.Length; ++i)                    
                        operationTimes[i] = Convert.ToInt32(stringWords[i]);                      
                    
            }

            //init文件的第三行 the third line of the init.txt
            {
                stringALine = SR.ReadLine(); //ReadLine可能返回空行
                stringALine = stringALine.Trim();
                while (stringALine == "")
                {
                    stringALine = SR.ReadLine();
                    stringALine = stringALine.Trim();
                }      

                stringWords = System.Text.RegularExpressions.Regex.Split(stringALine, @"\s{1,}"); //以一个或多空格为分隔

                //目标marking
                GoalM = new int[N_P];
                for (int i = 0; i < stringWords.Length; ++i)
                {
                    GoalM[i] = Convert.ToInt32(stringWords[i]);
                }
            }


            N_P_R = 0;//Petri网中资源库所数 the number of resource places in the net
            MAX_TOK_PA = 0; //活动库所的最大托肯容量 The maximal number of tokens in any activity place.                 
            int maxTokP_R = 0;//S_0中所有资源库所中的最大托肯数
            int maxTokP_Start = 0;//S_0中所有起始库所中的最大托肯数

            for (int i = 0; i < stringWords.Length; ++i) //Huang2023:纠正了MAX_TOK_PA的计算错误。并改进了MAX_TOK_PA=min{maxTokP_Start, maxTokP_R}
            {
                if (StartM[i] != 0 && GoalM[i] != 0 && StartM[i] == GoalM[i]) //在读取PN输入文件时，自动计算资源库所数量与非资源库所最大托肯容量; N_P_R and MAX_TOK_PA are automatically calculated by analyzing the input files.
                {
                    N_P_R++;
                    if (maxTokP_R < StartM[i])
                        maxTokP_R = StartM[i];
                }
                else if (StartM[i] != 0 && maxTokP_Start < StartM[i])
                    maxTokP_Start = StartM[i];
            }
            MAX_TOK_PA = (maxTokP_Start <= maxTokP_R) ? maxTokP_Start : maxTokP_R;

            SR.Close();

            return;
        }





        private static void Read_matrixfile(string fileName)
        {
            StreamReader SR;

            try
            {
                SR = File.OpenText(fileName);
            }
            catch
            {
                Console.Write(fileName + " open failed!");
                return;
            }


            string stringALine;

            //获取Petri网中变迁数N_T obtain the number of transitions in the net
            N_T = 0;
            stringALine = SR.ReadLine();
            while (stringALine != null)
            {
                stringALine = stringALine.Trim();//去头尾空格

                if (stringALine != "") //stringALine可能会是空行
                    ++N_T;
                stringALine = SR.ReadLine();
            }
            SR.Close();

            
            
            try
            {
                SR = File.OpenText(fileName);
            }
            catch
            {
                Console.Write(fileName + " open failed!");
                return;
            }


            int[,] temp = new int[N_T, N_P]; //临时矩阵 N_T x N_P,其中N_T需要上面的语句获取，而N_P通过前一个函数Read_initfile()获取
            string[] stringWords;
            int n = 0;
            
            stringALine = SR.ReadLine(); 
            while (stringALine != null)
            {
                stringALine = stringALine.Trim(); //去头尾空格

                if (stringALine != "")
                {
                    stringWords = System.Text.RegularExpressions.Regex.Split(stringALine, @"\s{1,}"); //以一个或多空格为分隔

                    for (int j = 0; j < N_P; ++j)        
                        temp[n, j] = Convert.ToInt32(stringWords[j]);
                    n++;
                }

                stringALine = SR.ReadLine();
            }
            SR.Close();


            //关联矩阵L+
            LPLUS = new int[N_P, N_T];

            //关联矩阵L-
            LMINUS = new int[N_P, N_T];

            for (int i = 0; i < N_T; ++i)
            {
                for (int j = 0; j < N_P; ++j)
                {
                    if (temp[i, j] >= 1)
                        LPLUS[j, i] = temp[i, j];                    
                    else                    
                        LPLUS[j, i] = 0;
                    

                    if (temp[i, j] <= -1)
                        LMINUS[j, i] = -temp[i, j];    
                    else                    
                        LMINUS[j, i] = 0;                    
                }
            }
            
            return;
        }





        //aHeap已按fValue排好序了，将aNode插入相同fValue的第一个位置
        private int SortAdd(Heap aHeap, AStarNode aNode)//将节点插入到相同fValue值的第一个位置
        //Insert a node into aHeap as the first element of the nodes with same fValue. 
        //The nodes in aHeap are already ranked in a non-decreasing order of f-values. 
        {
            int position = 0;
            for (int i = 0; i < aHeap.Count; ++i)
            {
                AStarNode aNodeInHeap = (AStarNode)aHeap[i];
                if (aNodeInHeap.fValue >= aNode.fValue)
                    break;
                else
                    ++position;
            }
            if (position == aHeap.Count)
                aHeap.Add(aNode);//加到末尾处
            else
                aHeap.Insert(position, aNode);
            return position;
        }




        private void PrintNodeList(object aNodeList)//输出某列表中所有节点的信息  Print the info. of all nodes in a given list. 
        {
            Console.WriteLine("\nNode list:");
            int i = 0;
            foreach (AStarNode n in (aNodeList as IEnumerable))
            {
                Console.Write("{0})\t", i + 1);
                i++;
                n.PrintNodeInfo();
            }
            Console.WriteLine("=============================================================");
        }

        private void PrintIterationInfo(AStarNode nodeCurrent)//打印当前循环的信息 Print the information of the current iteration.
        {
            Console.Write("Loop:{0} |OPEN|:{1} |CLOSED|:{2} NExpanded:{3} ", _Loop, _OPEN.Count, _CLOSED.Count, _NExpandedNodes);
            nodeCurrent.PrintNodeInfo();
        }

        #endregion




        #region Public Methods

        



        public void PrintSolution(int i, string fileName, int hMethod, int openSize, int h2ndMethod, decimal ep, decimal ep2, TimeSpan elapsedTime) //向屏幕输出，并写文件0result.txt  //Output the results to your screen and a file 0result.txt. i=0表示以create方式创建和输出文件；否则以append方式输出文件
        {            
            Console.WriteLine("************* The obtained schedule： ***********");
            PrintNodeList(_Solution);//向屏幕输出_Solution	//Output the obtained schedule to the screen		
            Console.WriteLine("The number of expanded markings:{0}", _NExpandedNodes);

            
            FileStream fileStream;
            StreamWriter writer;
            TextWriter oldOut = Console.Out;

            try
            {
                if(i==0)
                    fileStream = new FileStream("./0result.txt", FileMode.Create, FileAccess.Write);
                else
                    fileStream = new FileStream("./0result.txt", FileMode.Append, FileAccess.Write);
                writer = new StreamWriter(fileStream);
            }
            catch (Exception e)
            {
                Console.WriteLine(e.Message);
                Console.WriteLine("Cannot open 0result.txt to write results!");
                return;
            }
            Console.SetOut(writer);

            Console.WriteLine("=======================Start of a run==========================");
            Console.WriteLine("Petri net={0}; h={1}; Open size={2}; h2={3};", fileName, hMethod, openSize, h2ndMethod);
            Console.WriteLine("ep(for A^*_ep)={0}; ep2(for h dynamic weighting)={1}", ep, ep2);
            Console.WriteLine("The number of expanded markings:{0}", _NExpandedNodes);
            Console.WriteLine("Search time：hours={0}, minutes={1}, seconds={2}, milliseconds={3}", elapsedTime.Hours, elapsedTime.Minutes, elapsedTime.Seconds, elapsedTime.Milliseconds);
            Console.WriteLine("(Search time={0} seconds : {1} milliseconds)", elapsedTime.Hours * 3600 + elapsedTime.Minutes * 60 + elapsedTime.Seconds, elapsedTime.Milliseconds);
            Console.WriteLine("===============================================================");

            Console.WriteLine("************* The obtained schedule： ***********");
            PrintNodeList(_Solution);//向文件输出_Solution	//output FSolutio to 0result.txt.



            
            Console.WriteLine("=======================End of a run==========================");
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine();
            


            Console.SetOut(oldOut);
            writer.Close();
            fileStream.Close();
            Console.WriteLine("Results have been written into 0result.txt!");
        }



        public void FindPath_AStar(string fileName, AStarNode startNode, AStarNode goalNode, decimal ep, decimal ep2, int hMethod, int h2ndMethod, int openSize, bool printScreen)
        {
            //Use the A* search to find a path from a start state to a goal state in the reachability graph of a place-timed Petri net.

            //ep: the parameter epsilon used in Chapter 9 of our book.It is for OPEN.
            //  ep<0时表示没有ep的情况  ep<0 indicates the A* search does not use the epsilon. 
            //  ep=0时，选OPEN中具有相同最小f值marking中有最小h2ndValue的(0比-1好)
            //  ep>0时选择范围更大,选OPEN中具有不大于最小f值1+ep倍的marking中有最小h2ndValue的
            //  ep>=0 indicates the A* search picks out the state with the minimal h2nd value for expansion among the nodes having a f-value between f_min and f_min*(1+ep) in OPEN.
            //ep2 is for dynamic weighted search (h710-h723). ep2 = 0 denotes it is not used.
            //hMethod:所用启发函数h; the used heuristic function
            //h2ndMethod: 所用第二个启发函数，用于对OPEN中的节点进行二次排序  It is used for e-A*; The second hueristic function is for the states in OPEN. 2=-(_MarkingDepth+1);
            //openSize: the maximal number of nodes in OPEN. 
            //  openSize:0:表示open可为无穷大；大于0：表示进行BF locally,BT globally            
            //  openSize=0 denotes unlimited. openSize>0 denotes the A* search will use the BF locally and BT globally as described in Chapter 10 of our book.
            //printScreen: 是否向屏幕打印每个扩展节点的信息 //printScreen: whether or not to output every expanded node to your screen
            


            //hMethod:所用启发函数h  //hMethod: the used heuristic function:
            //h0=0;
            //h1=max{ei(m)} plus R; max{ei(m)} comes from Xiong98.            
            //h4=-dep(m);
            //h7 = h_H=max{E[M(p_i)*WRT(pi,r)+ER(pi,x)*Upi(r)/M0(r)]} comes from Chapter 9 of our book and our pape: Bo Huang, et al. Scheduling Robotic Cellular Manufacturing Systems with Timed Petri Net, A* Search and Admissible Heuristic Function. IEEE Transactions on Automation Science and Engineering, Jan. 2022, 19(1): 243-250.;  
                //Before h7=h_H is used, the number of resource places, the WRT matrix, the Upi matrix, and the M0r vector of the Petri net should be given in the class AStar. Some parameters of the tested Petri net should also be given in CalculateH().
            

            

            _StartNode = startNode;
            _GoalNode = goalNode;

            _OPEN.Clear();
            _CLOSED.Clear();
            _Successors.Clear();
            _Solution.Clear();
            _NExpandedNodes = 0;
            

            _Loop = 0;
            _OPEN.Add(_StartNode);//将初始标识放入OPEN表中  Put the initial marking into OPEN.

            

            while (_OPEN.Count >= 0)
            {
                _Loop++;


                if (_OPEN.Count == 0)//若OPEN表为空，程序异常退出 If OPEN is empty, exit with failure.
                {
                    Console.WriteLine("******* Open is null. Exit with failure! ********");
                    return;
                }



                //取OPEN列表中的第一个节点  Get the first node in OPEN. 
                AStarNode nodeCurrent = (AStarNode)_OPEN[0];

                if (ep < 0)          
                    _OPEN.Remove(_OPEN[0]); //从OPEN移除要扩展的节点 Remove the first node from OPEN. 
                


                if (ep >= 0)//即ep>=0,使用 search effort estimate
                {   //ep=0时，选OPEN中具有相同最小f值marking中有最小h2ndValue的
                    //ep>0时选择范围更大,选OPEN中具有不大于最小f值1+ep倍的marking中有最小h2ndValue的
                    int i = 0;
                    //FFOCALList.Clear();
                    AStarNode N = (AStarNode)_OPEN[0];//OPEN列表上的第一个节点
                    decimal fMin = N.fValue;
                    decimal minhF = N.h2ndValue;
                    decimal minDelt = N.Delt;
                    int index = 0;

                    while (i < _OPEN.Count - 1)//比较次数最多为_OPEN.Count-1次；OPEN按f值从小达到排列，所以用while，如果不满足即停止后续循环
                    {
                        i++;
                        N = (AStarNode)_OPEN[i];
                        if (minhF > N.h2ndValue) //节点的深度 depth
                        {
                            minhF = N.h2ndValue;
                            minDelt = N.Delt;
                            index = i;
                        }

                        /*if(minhF==N.h2ndValue && minDelt>N.Delt)
                        {//相同h2nd的marking使用minimum delt 作为tie-breaking
                            minDelt=N.Delt;
                            index=i;
                        }*/
                    }
                    
                    nodeCurrent = (AStarNode)_OPEN[index];
                    _OPEN.Remove(_OPEN[index]); //将要扩展的节点从OPEN移走
                }//if(ep>=0)

                

                //如果当前节点是目的节点，则回溯构造出路径  If the current node equals the goal node, construct a schedule from the goal node to the initial node.
                if (nodeCurrent.IsGoal())                 
                {
                    while (nodeCurrent != null)
                    {
                        _Solution.Insert(0, nodeCurrent);
                        nodeCurrent = nodeCurrent.Parent;
                    }                    
                    return; //本函数结束 The function terminates with a success. 
                }

                //把当前节点的所有子节点加入到_Successors  Add the child nodes of the current node to the list _Successors.
                _Successors.Clear();
                nodeCurrent.GetSuccessors(fileName, _Successors, hMethod, h2ndMethod, ep2);


                if (printScreen == true)
                    PrintIterationInfo(nodeCurrent);//打印当前循环的信息 Print the information of the current iteration.
                    

                    //if (_Loop==916)//_Loop >= 915 && _Loop <= 917)//用于调试
                // {//
                    //             nodeCurrent.PrintNodeInfo(_Loop);//打印当前节点的信息
                //   foreach (AStarNode a in _OPEN)//
                //         {//
                //    a.PrintNodeInfo(-1);//
                //           }//
                //   }//

 

                foreach (AStarNode aNodeInSuccessors in _Successors)                
                {

                    //如果子节点S'和OPEN中某节点S有相同M和R,但g'<g,则用S'替换Open中S 
                    //If the successor has the same M and R as a node in OPEN, but has smaller g-value, then replace the node in OPEN with the successor.
                              
                    AStarNode aSameNodeOpen = null;                     

                    foreach (AStarNode aNode in _OPEN)
                    {
                        if (aNode.IsSameStateM_R(aNodeInSuccessors)) 
                        {
                            aSameNodeOpen = aNode;
                            break;
                        }
                    }       
                    
                    if (aSameNodeOpen != null) //
                    {
                        if (aNodeInSuccessors.gValue < aSameNodeOpen.gValue)
                        {
                            _OPEN.Remove(aSameNodeOpen);
                            SortAdd(_OPEN, aNodeInSuccessors);                            
                            continue;
                        }
                    }


                    //如果子节点S'和Closed中某节点S有相同M和R,但g'<g,则删掉CLOSED的S，并将S'插入到Open
                    //If the successor has the same M anr R as a node in CLOSED but has smaller g-value, then delete the node in Closed and insert the successor into OPEN.

                    AStarNode aSameNodeClosed = null;

                    foreach (AStarNode aNode in _CLOSED)
                    {
                        if (aNode.IsSameStateM_R(aNodeInSuccessors))
                        {
                            aSameNodeClosed = aNode;
                            break;
                        }
                    }

                    
                    if (aSameNodeClosed != null)
                    {
                        if (aNodeInSuccessors.gValue < aSameNodeClosed.gValue)
                        {
                            _CLOSED.Remove(aSameNodeClosed);
                            SortAdd(_OPEN, aNodeInSuccessors);
                            continue;
                        }
                    }

                    //If there exists no state in OPEN and CLOSED as the successor, insert the successor into OPEN. 
                    if(aSameNodeOpen == null && aSameNodeClosed == null)
                    {
                        SortAdd(_OPEN, aNodeInSuccessors);
                    }
                } //The end of foreach (AStarNode aNodeInSuccessors in _Successors)

                SortAdd(_CLOSED, nodeCurrent);
                ++_NExpandedNodes;//已扩展节点数
                
            }// The end of while (_OPEN.Count > 0)

        }//FindPath_AStar

        #endregion
    }
}
