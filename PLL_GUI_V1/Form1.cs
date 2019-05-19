/*
注释都写在前边

若 VCO >= 300
无补偿 inclk <= 120
于是 N <= 12，否则若 N >= 13，M_m = VCO / ( inclk / N ) > 31
于是 N * c0_m < 384

若 VCO >= 400
无补偿 inclk <= 120
于是 N <= 9，否则若 N >= 10，M_m = VCO / ( inclk / N ) > 31
于是 N * c0_m < 288

c0_m<=31
于是 N * c0_m <= 279

6个pll：

VCO >= 300
无补偿 inclk <= 120
于是 N <= 25，否则若 N >= 26，M_m = VCO / ( inclk / N ) > 65
于是 N * c0_m < 1600

有补偿 inclk <= 60
于是 N <= 12，否则若 N >= 13，M_m = VCO / ( inclk / N ) > 65
于是 N * c0_m < 768

-----------------------------------

sort_duty_c0
所有可用的c0n与c0m组合（分子分母，包括c0m=1），包含n,m,c0m的信息（从sort2中得到）
去掉了重复的占空比值（比如4/8和6/12）

关于占空比
任何一个点了，都要把别的加上星星
其他的非星，则保留原值
其他的已星，则选择最近
*/
using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Windows.Forms;
using System.IO;
namespace PLL
{
    public partial class Form1 : Form
    {
//******************************************************************
        int i, j, k;
        int qi, qj;  //快速排序用
        int gcd;    //最大公约数，化简用

        string moduleName = "PLL";//模块名
        String operation_mode = "";    //模式
        static bool bsave = true;          //存文件开关，调试用
        bool saveenabled;                    //是否已经点save的标志。
        bool PTE;                                // 标志位：是否为抗辐照

        double inclk_freq_old = 50;
        double inclk_freq = 50;
        int count_temp;//?
        int phase_temp;//?
        int mul_lcm;      //?
        //******************************************************************
        //VCO的最大和最小值。    VCO=inclk*(M/N)
        static double vco_min = 300.0;//前两个是抗辐照的VCO
        static double vco_max = 700.0;
        static double vco_minF = 400.0;//后边两个是Fast PLL的VCO。
        static double vco_maxF = 800.0;
        double vco;//当前vco
        //******************************************************************    
        //N和M的值，同样也分抗辐照和FAST
        static int Nmax = 25;//N最大值。
        static int Mmax = 64;//M最大值。Fast PLL。
        static int NCM = 1600;//N*c0_m最大值
        static int NCML = 768;//N*c0_m最小值

        static int NmaxF = 9;//N最大值。Fast PLL。
        static int MmaxF = 31;//N最大值。Fast PLL。
        static int NCMF = 279;//N*c0_m。Fast PLL。
        //******************************************************************   
        #region 几个核心的参数
        //注意：在FAST PLL时候输出只有c0,c1和e0
        //            在抗辐照的情况下输出有c0,c1,c2,c3,c4和e0。由于c2在fastPLL的e0位置上，
        //            所以在抗辐照情况下e0表示c2；而真正的e0是e02
        int n = 1; //N_m	前置分频器模数	    1-32 自然数
        int m = 1;//M_m	内环路分频器模数(倍频)	1-32 自然数
        int c0_m = 1;//c1_m	后置分频器c1模数	1-32 自然数
        int c1_m = 1;//c1_m   后置分频器c0模数	1-32 自然数
        int e0_m = 1;//e0_m   后置分频器e0模数	1-32 自然数。在zero delay中使用
        int c3_m = 1;
        int c4_m = 1;
        int e02_m = 1;//e0_m   后置分频器e0模数	1-32 自然数。在zero delay中使用
        int m_real;
        int m_temp = 1;
        #endregion
        //******************************************************************
        #region 6个输出相关的参数：频率、分频、倍频、占空比、相位。
        double c0_freq;
        int c0_mul = 1;
        int c0_div = 1;
        double c0_duty = 50;
        double c0_phase = 0;

        double c1_freq;
        int c1_mul = 1;
        int c1_div = 1;
        double c1_duty = 50;
        double c1_phase = 0;

        double e0_freq;
        int e0_mul = 1;
        int e0_div = 1;
        double e0_duty = 50;
        double e0_phase = 0;

        double c3_freq;
        int c3_mul = 1;
        int c3_div = 1;
        double c3_duty = 50;
        double c3_phase = 0;

        double c4_freq;
        int c4_mul = 1;
        int c4_div = 1;
        double c4_duty = 50;
        double c4_phase = 0;

        double e02_freq;
        int e02_mul = 1;
        int e02_div = 1;
        double e02_duty = 50;
        double e02_phase = 0;
        #endregion
        //******************************************************************
        public class sort_index
        {
            public bool enable;
            public int n;
            public int m;
            public int c0m;       //分母(c0_m)
            public int c1m;       //分母(c1_m)
            public int e0m;       //分母(e0_m)
            public int c3m;
            public int c4m;
            public int e02m;
            public double value;
        };
        public class duty_index : sort_index
        {
            public int element;  //分子            
            public double rate;
            public bool red;//是否显示红色，触发改变
        };
        #region sort & sort2
        //sort:根据inclk计算出的所有n,m,c0m,c1m,e0m的组合，经过排序与vco筛选
        //sort2:sort中去除了c0m,c1m,e0m的所有因子（较小值），占空比值发生改变，应该从这里重新筛选
        sort_index[] sort = new sort_index[Nmax * Mmax];//排序用，为了获得nm的index，每次根据对应于nm的enable重新排序
        sort_index[] sort_2 = new sort_index[Nmax * Mmax];//排序后的sort，不再变

        sort_index[] sortF = new sort_index[NmaxF * MmaxF];//排序用，为了获得nm的index，每次根据对应于nm的enable重新排序
        sort_index[] sort_2F = new sort_index[NmaxF * MmaxF];//排序后的sort，不再变
        #endregion
        #region List：生成list用
        duty_index duty_temp;//
        List<duty_index> sort_duty_c0 = new List<duty_index>();
        List<duty_index> sort_duty_c0_2 = new List<duty_index>();
        List<duty_index> sort_duty_c1 = new List<duty_index>();
        List<duty_index> sort_duty_c1_2 = new List<duty_index>();
        List<duty_index> sort_duty_e0 = new List<duty_index>();
        List<duty_index> sort_duty_e0_2 = new List<duty_index>();
        List<duty_index> sort_duty_c3 = new List<duty_index>();
        List<duty_index> sort_duty_c3_2 = new List<duty_index>();
        List<duty_index> sort_duty_c4 = new List<duty_index>();
        List<duty_index> sort_duty_c4_2 = new List<duty_index>();
        List<duty_index> sort_duty_e02 = new List<duty_index>();
        List<duty_index> sort_duty_e02_2 = new List<duty_index>();
        #endregion
        #region 记载CBB_cx_duty选择指标的旧值
        int SelectedIndex_c0;//记载CBB_c0_duty选择指标的旧值
        int SelectedIndex_c1;//记载CBB_c1_duty选择指标的旧值
        int SelectedIndex_e0;//记载CBB_e0_duty选择指标的旧值
        int SelectedIndex_c3;
        int SelectedIndex_c4;
        int SelectedIndex_e02;

        int SelectedIndex_c0p;//记载CBB_c0_duty选择指标的旧值
        int SelectedIndex_c1p;//记载CBB_c1_duty选择指标的旧值
        int SelectedIndex_e0p;//记载CBB_e0_duty选择指标的旧值
        int SelectedIndex_c3p;
        int SelectedIndex_c4p;
        int SelectedIndex_e02p;
        #endregion

        int[,] nm = new int[Nmax + 1, Mmax + 1];//table[n][m]，每次 RefreshData 只改变enable
        int[,] nmF = new int[NmaxF + 1, MmaxF + 1];//table[n][m]，每次 RefreshData 只改变enable
        int sort_2_count;//sort_2有效数据规模

        public class sort_spl_index//有反馈时的数据
        {
            public bool enable;
            public int c0m;       //分母(c0_m)
            public int c1m;       //分母(c1_m)
            public int e0m;       //分母(e0_m)
            public int c3m;
            public int c4m;
            public int e02m;
        };
        sort_spl_index[] sort_spl = new sort_spl_index[MmaxF + 1];//有补偿情况
        sort_spl_index[] sort_spl_2 = new sort_spl_index[MmaxF + 1];//有补偿情况
//***************************************************************************
        //数据处理相关算法
        //排序、最大公约数、最小公倍数，求绝对值。
        #region 排序算法。qs快速排序
        //经过排序rate ，c0m以及n，m 按从小到大排列。
        public static int sort_duty_c0_compare(duty_index x, duty_index y)
        {
            if (x.rate - y.rate > 1e-6)
                return 1;
            else if (y.rate - x.rate > 1e-6)
                return -1;
            else
            {
                if (x.c0m > y.c0m)//对分母的值进一步排序
                    return -1;
                else if (x.c0m > y.c0m)
                    return 1;
                else
                    return 0;
            }
        }
        public static int sort_duty_c1_compare(duty_index x, duty_index y)
        {
            if (x.rate - y.rate > 1e-6)
                return 1;
            else if (y.rate - x.rate > 1e-6)
                return -1;
            else
            {
                if (x.c1m > y.c1m)//对分子分母的值进一步排序
                    return -1;
                else if (x.c1m > y.c1m)
                    return 1;
                else
                    return 0;
            }
        }
        public static int sort_duty_e0_compare(duty_index x, duty_index y)
        {
            if (x.rate - y.rate > 1e-6)
                return 1;
            else if (y.rate - x.rate > 1e-6)
                return -1;
            else
            {
                if (x.e0m > y.e0m)//对分子分母的值进一步排序
                    return -1;
                else if (x.e0m > y.e0m)
                    return 1;
                else
                    return 0;
            }
        }
        public static int sort_duty_c3_compare(duty_index x, duty_index y)
        {
            if (x.rate - y.rate > 1e-6)
                return 1;
            else if (y.rate - x.rate > 1e-6)
                return -1;
            else
            {
                if (x.c3m > y.c3m)//对分子分母的值进一步排序
                    return -1;
                else if (x.c3m > y.c3m)
                    return 1;
                else
                    return 0;
            }
        }
        public static int sort_duty_c4_compare(duty_index x, duty_index y)
        {
            if (x.rate - y.rate > 1e-6)
                return 1;
            else if (y.rate - x.rate > 1e-6)
                return -1;
            else
            {
                if (x.c4m > y.c4m)//对分子分母的值进一步排序
                    return -1;
                else if (x.c4m > y.c4m)
                    return 1;
                else
                    return 0;
            }
        }
        public static int sort_duty_e02_compare(duty_index x, duty_index y)
        {
            if (x.rate - y.rate > 1e-6)
                return 1;
            else if (y.rate - x.rate > 1e-6)
                return -1;
            else
            {
                if (x.e02m > y.e02m)//对分子分母的值进一步排序
                    return -1;
                else if (x.e02m > y.e02m)
                    return 1;
                else
                    return 0;
            }
        }
        public void pp(sort_index[] A, int m, int n)
        {
            double k, r;
            int ri;
            int temp_i;
            qi = m;
            qj = n;
            r = A[qi].value;
            ri = A[qi].m;
            while (qi <= qj)
            {
                while (r - A[qi].value > 1e-6 || (r - A[qi].value < 1e-6 && A[qi].value - r < 1e-6 && A[qi].m > ri))
                    qi++;
                while (A[qj].value - r > 1e-6 || (r - A[qj].value < 1e-6 && A[qj].value - r < 1e-6 && A[qj].m < ri))
                    qj--;
                if (qi <= qj)
                {
                    k = A[qi].value;
                    A[qi].value = A[qj].value;
                    A[qj].value = k;

                    temp_i = A[qi].n;
                    A[qi].n = A[qj].n;
                    A[qj].n = temp_i;

                    temp_i = A[qi].m;
                    A[qi].m = A[qj].m;
                    A[qj].m = temp_i;

                    qi++;
                    qj--;
                }
            }
        }
        public void qs(sort_index[] A, int m, int n)
        {
            int i, j;
            if (m < n)
            {
                pp(A, m, n);
                i = qi;
                j = qj;
                qs(A, m, j);
                qs(A, i, n);
            }
        }
        public double abs(double d)
        {
            return d >= 0 ? d : -d;
        }
        #endregion
        #region 求最大公约数和最大公倍数。
        private int GCD(int a, int b)
        {
            if (a == 0)
                return b;
            else if (b == 0)
                return a;
            else if (a > b)
                return GCD(a % b, b);
            else
                return GCD(a, b % a);
        }
        private int LCM(int a, int b)
        {
            if (a == 0)
            {
                MessageBox.Show("LCM a=0, b=" + b.ToString());
                return b;
            }
            else if (b == 0)
            {
                MessageBox.Show("LCM b=0, a=" + a.ToString());
                return a;
            }
            return a * b / GCD(a, b);
        }
        #endregion

        string saveFile;
        private void Init(string saveFileName)
        {
            try
            {

                LB_savefile.Text = "Save File: " + saveFileName;
                saveFile = saveFileName;

                if (saveFile.IndexOf("\\") == -1)//20160909---------ly new
                    saveFile = ".\\" + saveFile;

                string fileName = Path.GetFileName(saveFile);
                moduleName = fileName.Substring(0, fileName.IndexOf("."));
            }
            catch
            { }

        }
        public Form1(string saveFileName)//程序入口
        {
            InitializeComponent();
            Init(saveFileName);
        }
        private void Form1_Load(object sender, EventArgs e)
        {
            BT_Back.Visible = false;
            BT_Save.Visible = false;
            BT_Close.Visible = false;

            for (i = 1; i <= Nmax; i++)//初始化nm的value
            {
                for (j = 1; j <= Mmax; j++)
                {
                    nm[i, j] = new int();
                }
            }
            for (i = 1; i <= NmaxF; i++)//初始化nm的value
            {
                for (j = 1; j <= MmaxF; j++)
                {
                    nmF[i, j] = new int();
                }
            }

            for (i = 0; i < Nmax; i++)
            {
                for (j = 0; j < Mmax; j++)
                {
                    sort[i * Mmax + j] = new sort_index();
                    sort[i * Mmax + j].n = i + 1;
                    sort[i * Mmax + j].m = j + 1;
                    sort[i * Mmax + j].value = (double)(i + 1) / (j + 1);// n/m
                }
            }
            for (i = 0; i < NmaxF; i++)
            {
                for (j = 0; j < MmaxF; j++)
                {
                    sortF[i * MmaxF + j] = new sort_index();
                    sortF[i * MmaxF + j].n = i + 1;
                    sortF[i * MmaxF + j].m = j + 1;
                    sortF[i * MmaxF + j].value = (double)(i + 1) / (j + 1);// n/m
                }
            }

            qs(sort, 0, Nmax * Mmax - 1);
            qs(sortF, 0, NmaxF * MmaxF - 1);

            for (i = 0; i < Nmax; i++)//更新排序后nm的index
            {
                for (j = 0; j < Mmax; j++)
                {
                    nm[sort[i * Mmax + j].n, sort[i * Mmax + j].m] = i * Mmax + j;
                }
            }
            for (i = 0; i < NmaxF; i++)//更新排序后nm的index
            {
                for (j = 0; j < MmaxF; j++)
                {
                    nmF[sortF[i * MmaxF + j].n, sortF[i * MmaxF + j].m] = i * MmaxF + j;
                }
            }

            for (i = 0; i < Nmax; i++)
            {
                for (j = 0; j < Mmax; j++)
                {
                    sort_2[i * Mmax + j] = new duty_index();
                }
            }
            for (i = 0; i < NmaxF; i++)
            {
                for (j = 0; j < MmaxF; j++)
                {
                    sort_2F[i * MmaxF + j] = new duty_index();
                }
            }

            for (j = 1; j <= MmaxF; j++)
            {
                sort_spl[j] = new sort_spl_index();
            }

            RB_mode2_Click(null, null);

            //LB_group.Text = "";
        }
        
        private void OutPut(int ok)
        {
            if (PTE)
            {
                m_real = m;
            }
            else
            {
                if (RB_mode0.Checked)//无补偿
                    m_real = m;
                else if (RB_mode1.Checked)//e0补偿
                    m_real = e0_m;
                else if (RB_mode2.Checked)//c0补偿
                    m_real = c0_m;
                else if (RB_mode3.Checked)//c1补偿
                    m_real = c1_m;
                else
                {
                    MessageBox.Show("operation mode error");
                    LB_message_output.Text = "operation mode error";
                }
            }

            LB_info_output.Text = "";

            if (CB_c0.Checked)
            {
                c0_m = m_real * c0_div / n / c0_mul;
                c0_freq = inclk_freq * c0_mul / c0_div;
                LB_c0_freq.Text = c0_freq.ToString("f3");
                LB_c0_rm.Text = c0_mul.ToString();
                LB_c0_rd.Text = c0_div.ToString();
                LB_info_output.Text += "Clock c0 Multiplier = " + c0_mul.ToString() + " Divider = " + c0_div.ToString() + " ";
            }
            else
            {
                LB_c0_freq.Text = "";
                LB_c0_rm.Text = "";
                LB_c0_rd.Text = "";
            }
            if (CB_c1.Checked)
            {
                c1_m = m_real * c1_div / n / c1_mul;
                c1_freq = inclk_freq * c1_mul / c1_div;
                LB_c1_freq.Text = c1_freq.ToString("f3");
                LB_c1_rm.Text = c1_mul.ToString();
                LB_c1_rd.Text = c1_div.ToString();
                if (CB_c0.Checked)
                    LB_info_output.Text += "\n";
                LB_info_output.Text += "Clock c1 Multiplier = " + c1_mul.ToString() + " Divider = " + c1_div.ToString() + " ";
            }
            else
            {
                LB_c1_freq.Text = "";
                LB_c1_rm.Text = "";
                LB_c1_rd.Text = "";
            }
            if (CB_e0.Checked)
            {
                e0_m = m_real * e0_div / n / e0_mul;
                e0_freq = inclk_freq * e0_mul / e0_div;
                LB_e0_freq.Text = e0_freq.ToString("f3");
                LB_e0_rm.Text = e0_mul.ToString();
                LB_e0_rd.Text = e0_div.ToString();
                if (CB_c0.Checked || CB_c1.Checked)
                    LB_info_output.Text += "\n";
                LB_info_output.Text += "Clock " + (PTE ? "c2" : "e0") + " Multiplier = " + e0_mul.ToString() + " Divider = " + e0_div.ToString() + " ";
            }
            else
            {
                LB_e0_rm.Text = "";
                LB_e0_rd.Text = "";
                LB_e0_freq.Text = "";
            }
            if (CB_c3.Checked)
            {
                c3_m = m_real * c3_div / n / c3_mul;
                c3_freq = inclk_freq * c3_mul / c3_div;
                LB_c3_freq.Text = c3_freq.ToString("f3");
                LB_c3_rm.Text = c3_mul.ToString();
                LB_c3_rd.Text = c3_div.ToString();
                //if (CB_c0.Checked)
                LB_info_output.Text += "\n";
                LB_info_output.Text += "Clock c3 Multiplier = " + c3_mul.ToString() + " Divider = " + c3_div.ToString() + " ";
            }
            else
            {
                LB_c3_rm.Text = "";
                LB_c3_rd.Text = "";
                LB_c3_freq.Text = "";
            }
            if (CB_c4.Checked)
            {
                c4_m = m_real * c4_div / n / c4_mul;
                c4_freq = inclk_freq * c4_mul / c4_div;
                LB_c4_freq.Text = c4_freq.ToString("f3");
                LB_c4_rm.Text = c4_mul.ToString();
                LB_c4_rd.Text = c4_div.ToString();
                //if (CB_c0.Checked)
                LB_info_output.Text += "\n";
                LB_info_output.Text += "Clock c4 Multiplier = " + c4_mul.ToString() + " Divider = " + c4_div.ToString() + " ";
            }
            else
            {
                LB_c4_rm.Text = "";
                LB_c4_rd.Text = "";
                LB_c4_freq.Text = "";
            }
            if (CB_e02.Checked)
            {
                e02_m = m_real * e02_div / n / e02_mul;
                e02_freq = inclk_freq * e02_mul / e02_div;
                LB_e02_freq.Text = e02_freq.ToString("f3");
                LB_e02_rm.Text = e02_mul.ToString();
                LB_e02_rd.Text = e02_div.ToString();
                //if (CB_c0.Checked || CB_c1.Checked)
                LB_info_output.Text += "\n";
                LB_info_output.Text += "Clock e0 Multiplier = " + e02_mul.ToString() + " Divider = " + e02_div.ToString() + " ";
            }
            else
            {
                LB_e02_rm.Text = "";
                LB_e02_rd.Text = "";
                LB_e02_freq.Text = "";
            }

            if (CB_c0.Checked || CB_c1.Checked || CB_e0.Checked || CB_c3.Checked || CB_c4.Checked || CB_e02.Checked)
                LB_lcm.Text = mul_lcm.ToString();
            else
                LB_lcm.Text = "";

            if (ok == 0)
            {
                vco = inclk_freq * m_real / n;
                LB_info_output.Text += "\nmul_lcm=" + mul_lcm.ToString() + "\nPrimary clock VCO frequency = " + vco.ToString("n") + "MHz\nN=" + n.ToString() + " M_m=" + m.ToString() + " ";
                //LB_lcm.Text = mul_lcm.ToString();
                LB_vco.Text = vco.ToString("n") + "  MHz";
                LB_N.Text = n.ToString();
                LB_M.Text = m.ToString();
            }
            else
            {
                //LB_lcm.Text = "";
                LB_vco.Text = "";
                LB_N.Text = "";
                LB_M.Text = "";
            }

            if (CB_c0.Checked && ok == 0)
            {
                LB_c0_m.Text = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m.ToString();
                LB_c0_h.Text = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].element.ToString();
                LB_c0_l.Text = (sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m - sort_duty_c0_2[CBB_c0_duty.SelectedIndex].element).ToString();
            }
            //LB_info_output.Text += "c0_m=" + c0_m.ToString() + " ";
            else
            {
                LB_c0_m.Text = "";
                LB_c0_h.Text = "";
                LB_c0_l.Text = "";
            }
            if (CB_c1.Checked && ok == 0)
            {
                LB_c1_m.Text = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m.ToString();
                LB_c1_h.Text = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].element.ToString();
                LB_c1_l.Text = (sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m - sort_duty_c1_2[CBB_c1_duty.SelectedIndex].element).ToString();
            }
            //LB_info_output.Text += "c1_m=" + c1_m.ToString() + " ";
            else
            {
                LB_c1_m.Text = "";
                LB_c1_h.Text = "";
                LB_c1_l.Text = "";
            }
            if (CB_e0.Checked && ok == 0)
            {
                LB_e0_m.Text = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m.ToString();
                LB_e0_h.Text = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].element.ToString();
                LB_e0_l.Text = (sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m - sort_duty_e0_2[CBB_e0_duty.SelectedIndex].element).ToString();
            }
            //LB_info_output.Text += (PTE ? "c2_m=" : "e0_m=") + e0_m.ToString() + " ";
            else
            {
                LB_e0_m.Text = "";
                LB_e0_h.Text = "";
                LB_e0_l.Text = "";
            }
            if (CB_c3.Checked && ok == 0)
            {
                LB_c3_m.Text = sort_duty_c3_2[CBB_c3_duty.SelectedIndex].c3m.ToString();
                LB_c3_h.Text = sort_duty_c3_2[CBB_c3_duty.SelectedIndex].element.ToString();
                LB_c3_l.Text = (sort_duty_c3_2[CBB_c3_duty.SelectedIndex].c3m - sort_duty_c3_2[CBB_c3_duty.SelectedIndex].element).ToString();
            }
            //LB_info_output.Text += "c3_m=" + c3_m.ToString() + " ";
            else
            {
                LB_c3_m.Text = "";
                LB_c3_h.Text = "";
                LB_c3_l.Text = "";
            }
            if (CB_c4.Checked && ok == 0)
            {
                LB_c4_m.Text = sort_duty_c4_2[CBB_c4_duty.SelectedIndex].c4m.ToString();
                LB_c4_h.Text = sort_duty_c4_2[CBB_c4_duty.SelectedIndex].element.ToString();
                LB_c4_l.Text = (sort_duty_c4_2[CBB_c4_duty.SelectedIndex].c4m - sort_duty_c4_2[CBB_c4_duty.SelectedIndex].element).ToString();
            }
            //LB_info_output.Text += "c4_m=" + c4_m.ToString() + " ";
            else
            {
                LB_c4_m.Text = "";
                LB_c4_h.Text = "";
                LB_c4_l.Text = "";
            }
            if (CB_e02.Checked && ok == 0)
            {
                LB_e02_m.Text = sort_duty_e02_2[CBB_e02_duty.SelectedIndex].e02m.ToString();
                LB_e02_h.Text = sort_duty_e02_2[CBB_e02_duty.SelectedIndex].element.ToString();
                LB_e02_l.Text = (sort_duty_e02_2[CBB_e02_duty.SelectedIndex].e02m - sort_duty_e02_2[CBB_e02_duty.SelectedIndex].element).ToString();
            }
            //LB_info_output.Text += "e0_m=" + e02_m.ToString() + " ";
            else
            {
                LB_e02_m.Text = "";
                LB_e02_h.Text = "";
                LB_e02_l.Text = "";
            }
        }
        private bool RefreshData()
        {
            LB_message_output.ForeColor = System.Drawing.Color.Red;

            CBB_c0_duty.Enabled = CB_c0.Checked;
            CBB_c0_phase.Enabled = CB_c0.Checked;
            CBB_c1_duty.Enabled = CB_c1.Checked;
            CBB_c1_phase.Enabled = CB_c1.Checked;
            CBB_e0_duty.Enabled = CB_e0.Checked;
            CBB_e0_phase.Enabled = CB_e0.Checked;
            if (PTE)
            {
                CBB_c3_duty.Enabled = CB_c3.Checked;
                CBB_c3_phase.Enabled = CB_c3.Checked;
                CBB_c4_duty.Enabled = CB_c4.Checked;
                CBB_c4_phase.Enabled = CB_c4.Checked;
                CBB_e02_duty.Enabled = CB_e02.Checked;
                CBB_e02_phase.Enabled = CB_e02.Checked;
            }
            if (PTE)
            {
                for (i = 0; i < Nmax; i++)
                    for (j = 0; j < Mmax; j++)
                        sort[i * Mmax + j].enable = true;
            }
            else
            {
                if (RB_mode0.Checked)
                    for (i = 0; i < NmaxF; i++)
                        for (j = 0; j < MmaxF; j++)
                            sortF[i * MmaxF + j].enable = true;
                else
                    for (j = 1; j <= MmaxF; j++)
                        sort_spl[j].enable = true;
            }

            c0_mul = Convert.ToInt32(nUD_c0_mul.Value);
            c1_mul = Convert.ToInt32(nUD_c1_mul.Value);
            e0_mul = Convert.ToInt32(nUD_e0_mul.Value);
            c0_div = Convert.ToInt32(nUD_c0_div.Value);
            c1_div = Convert.ToInt32(nUD_c1_div.Value);
            e0_div = Convert.ToInt32(nUD_e0_div.Value);

            if (PTE)
            {
                c3_mul = Convert.ToInt32(nUD_c3_mul.Value);
                c4_mul = Convert.ToInt32(nUD_c4_mul.Value);
                e02_mul = Convert.ToInt32(nUD_e02_mul.Value);
                c3_div = Convert.ToInt32(nUD_c3_div.Value);
                c4_div = Convert.ToInt32(nUD_c4_div.Value);
                e02_div = Convert.ToInt32(nUD_e02_div.Value);
            }

            gcd = GCD(c0_mul, c0_div);
            c0_mul /= gcd;
            c0_div /= gcd;
            gcd = GCD(c1_mul, c1_div);
            c1_mul /= gcd;
            c1_div /= gcd;
            gcd = GCD(e0_mul, e0_div);
            e0_mul /= gcd;
            e0_div /= gcd;

            if (PTE)
            {
                gcd = GCD(c3_mul, c3_div);
                c3_mul /= gcd;
                c3_div /= gcd;
                gcd = GCD(c4_mul, c4_div);
                c4_mul /= gcd;
                c4_div /= gcd;
                gcd = GCD(e02_mul, e02_div);
                e02_mul /= gcd;
                e02_div /= gcd;
            }

            if (PTE)
            {
                if (RB_N.Checked) operation_mode = "NO_COMPENSATION";
                else if (RB_e02.Checked) operation_mode = "ZERO_DELAY_BUFFER";
                else operation_mode = "NORMAL";

                if (!CB_c0.Checked && !CB_c1.Checked && !CB_e0.Checked && !CB_c3.Checked && !CB_c4.Checked && !CB_e02.Checked)
                {
                    LB_c0_freq.Text = "";
                    LB_c1_freq.Text = "";
                    LB_e0_freq.Text = "";
                    LB_c3_freq.Text = "";
                    LB_c4_freq.Text = "";
                    LB_e02_freq.Text = "";
                    OutPut(1);
                    LB_message_output.Text = "";
                    LB_info_output.Text = "";
                    //DrawPLL();
                    //pictureBox.Refresh();
                    return false;
                }

                mul_lcm = 1;

                if (CB_c0.Checked)
                {
                    mul_lcm = LCM(mul_lcm, c0_mul);
                }
                if (CB_c1.Checked)
                {
                    mul_lcm = LCM(mul_lcm, c1_mul);
                }
                if (CB_e0.Checked)
                {
                    mul_lcm = LCM(mul_lcm, e0_mul);
                }
                if (CB_c3.Checked)
                {
                    mul_lcm = LCM(mul_lcm, c3_mul);
                }
                if (CB_c4.Checked)
                {
                    mul_lcm = LCM(mul_lcm, c4_mul);
                }
                if (CB_e02.Checked)
                {
                    mul_lcm = LCM(mul_lcm, e02_mul);
                }

                for (i = 1; i <= Nmax; i++)//n
                {
                    for (j = 1; j <= Mmax; j++)//m
                    {
                        if (j == 1)
                        {
                            sort[nm[i, j]].enable = false;
                        }
                        else if (j % mul_lcm != 0)//m 必须是 mul_lcm 的倍数
                        {
                            sort[nm[i, j]].enable = false;
                        }
                        else if (vco_min - inclk_freq * j / i > 1e-6)//vco >= vco_min
                        {
                            sort[nm[i, j]].enable = false;
                        }
                        else if (inclk_freq * j / i - vco_max > 1e-6)//vco <= vco_max
                        {
                            sort[nm[i, j]].enable = false;
                        }
                        else
                        {
                            if (CB_c0.Checked)
                            {
                                if (i * c0_mul % c0_div != 0)//RH新增：m/ci_m是整数
                                {
                                    sort[nm[i, j]].enable = false;
                                }
                                else if (j * c0_div / c0_mul % i != 0)//组合使得 c0_m 可用
                                {
                                    sort[nm[i, j]].enable = false;
                                }
                                else
                                {
                                    sort[nm[i, j]].c0m = j * c0_div / c0_mul / i;
                                    if (sort[nm[i, j]].c0m == 1)
                                        sort[nm[i, j]].enable = false;
                                    else if (sort[nm[i, j]].c0m > Mmax)
                                        sort[nm[i, j]].enable = false;
                                }
                            }
                            if (CB_c1.Checked)//组合使得 c1_m 可用
                            {
                                if (i * c1_mul % c1_div != 0)//RH新增：m/ci_m是整数
                                {
                                    sort[nm[i, j]].enable = false;
                                }
                                else if (j * c1_div / c1_mul % i != 0)
                                {
                                    sort[nm[i, j]].enable = false;
                                }
                                else
                                {
                                    sort[nm[i, j]].c1m = j * c1_div / c1_mul / i;
                                    if (sort[nm[i, j]].c1m == 1)
                                        sort[nm[i, j]].enable = false;
                                    else if (sort[nm[i, j]].c1m > Mmax)
                                        sort[nm[i, j]].enable = false;
                                }
                            }
                            if (CB_e0.Checked)//组合使得 e0_m 可用
                            {
                                if (i * e0_mul % e0_div != 0)//RH新增：m/ci_m是整数
                                {
                                    sort[nm[i, j]].enable = false;
                                }
                                else if (j * e0_div / e0_mul % i != 0)
                                {
                                    sort[nm[i, j]].enable = false;
                                }
                                else
                                {
                                    sort[nm[i, j]].e0m = j * e0_div / e0_mul / i;
                                    if (sort[nm[i, j]].e0m == 1)
                                        sort[nm[i, j]].enable = false;
                                    else if (sort[nm[i, j]].e0m > Mmax)
                                        sort[nm[i, j]].enable = false;
                                }
                            }
                            if (CB_c3.Checked)//组合使得 c3_m 可用
                            {
                                if (i * c3_mul % c3_div != 0)//RH新增：m/ci_m是整数
                                {
                                    sort[nm[i, j]].enable = false;
                                }
                                else if (j * c3_div / c3_mul % i != 0)
                                {
                                    sort[nm[i, j]].enable = false;
                                }
                                else
                                {
                                    sort[nm[i, j]].c3m = j * c3_div / c3_mul / i;
                                    if (sort[nm[i, j]].c3m == 1)
                                        sort[nm[i, j]].enable = false;
                                    else if (sort[nm[i, j]].c3m > Mmax)
                                        sort[nm[i, j]].enable = false;
                                }
                            }
                            if (CB_c4.Checked)//组合使得 c4_m 可用
                            {
                                if (i * c4_mul % c4_div != 0)//RH新增：m/ci_m是整数
                                {
                                    sort[nm[i, j]].enable = false;
                                }
                                else if (j * c4_div / c4_mul % i != 0)
                                {
                                    sort[nm[i, j]].enable = false;
                                }
                                else
                                {
                                    sort[nm[i, j]].c4m = j * c4_div / c4_mul / i;
                                    if (sort[nm[i, j]].c4m == 1)
                                        sort[nm[i, j]].enable = false;
                                    else if (sort[nm[i, j]].c4m > Mmax)
                                        sort[nm[i, j]].enable = false;
                                }
                            }
                            if (CB_e02.Checked)//组合使得 e02_m 可用
                            {
                                if (i * e02_mul % e02_div != 0)//RH新增：m/ci_m是整数
                                {
                                    sort[nm[i, j]].enable = false;
                                }
                                else if (j * e02_div / e02_mul % i != 0)
                                {
                                    sort[nm[i, j]].enable = false;
                                }
                                else
                                {
                                    sort[nm[i, j]].e02m = j * e02_div / e02_mul / i;
                                    if (sort[nm[i, j]].e02m == 1)
                                        sort[nm[i, j]].enable = false;
                                    else if (sort[nm[i, j]].e02m > Mmax)
                                        sort[nm[i, j]].enable = false;
                                }
                            }
                        }
                    }
                }
                //筛选开始
                for (j = 0; j < NCM; j++)
                {
                    if (sort[j].enable == true)
                        break;
                }
                if (j == NCM)
                {
                    OutPut(1);
                    LB_message_output.Text = "No suitable result or Vco frequency exceeds (" + vco_min.ToString("f0") + "," + vco_max.ToString("f0") + "), please adjust your multiplication or division factor.";
                    //+ "\nNCM=" + NCM.ToString() + " j=" + j.ToString();
                    LB_info_output.Text = "";

                    CBB_c0_duty.Enabled = false;
                    CBB_c0_phase.Enabled = false;
                    CBB_c1_duty.Enabled = false;
                    CBB_c1_phase.Enabled = false;
                    CBB_e0_duty.Enabled = false;
                    CBB_e0_phase.Enabled = false;
                    CBB_c3_duty.Enabled = false;
                    CBB_c3_phase.Enabled = false;
                    CBB_c4_duty.Enabled = false;
                    CBB_c4_phase.Enabled = false;
                    CBB_e02_duty.Enabled = false;
                    CBB_e02_phase.Enabled = false;

                    OutPut(1);
                    //DrawPLL();
                    //pictureBox.Refresh();
                    return false;
                }
                i = 0;

                sort_2[0].n = sort[j].n;
                sort_2[0].m = sort[j].m;
                sort_2[0].value = sort[j].value;
                sort_2[0].c0m = sort[j].c0m;
                sort_2[0].c1m = sort[j].c1m;
                sort_2[0].e0m = sort[j].e0m;
                sort_2[0].c3m = sort[j].c3m;
                sort_2[0].c4m = sort[j].c4m;
                sort_2[0].e02m = sort[j].e02m;
                sort_2[0].enable = true;

                for (j++; j < NCM; j++)
                {
                    if (sort[j].enable == true)
                    {
                        if (sort[j].value - sort_2[i].value > 1e-6)// i/j  n/m  可以改，比如把分子分母的选择加上（已经在排序时完成）
                        {
                            for (k = 0; k <= i; k++)
                            {
                                //这句留待优化 ly_remark
                                if (CB_c0.Checked && sort_2[k].c0m % sort[j].c0m == 0)
                                    break;
                                if (CB_c1.Checked && sort_2[k].c1m % sort[j].c1m == 0)
                                    break;
                                if (CB_e0.Checked && sort_2[k].e0m % sort[j].e0m == 0)
                                    break;
                                if (CB_c3.Checked && sort_2[k].c3m % sort[j].c3m == 0)
                                    break;
                                if (CB_c4.Checked && sort_2[k].c4m % sort[j].c4m == 0)
                                    break;
                                if (CB_e02.Checked && sort_2[k].e02m % sort[j].e02m == 0)
                                    break;
                            }
                            if (k == i + 1)
                            {
                                i++;
                                sort_2[i].n = sort[j].n;
                                sort_2[i].m = sort[j].m;
                                sort_2[i].value = sort[j].value;
                                sort_2[i].c0m = sort[j].c0m;
                                sort_2[i].c1m = sort[j].c1m;
                                sort_2[i].e0m = sort[j].e0m;
                                sort_2[i].c3m = sort[j].c3m;
                                sort_2[i].c4m = sort[j].c4m;
                                sort_2[i].e02m = sort[j].e02m;
                                sort_2[i].enable = true;
                            }
                        }
                    }
                }
                sort_2_count = i + 1;//可用sort个数
                //筛选结束（三个输出共用，此时保留所有可用的c0_m c1_m e0_m）
                //下边开始枚举可用的占空比
                //c0约束开始
                if (CB_c0.Checked)
                {
                    sort_duty_c0.Clear();
                    for (i = 0; i < sort_2_count; i++)
                    {
                        if (sort_2[i].c0m == 1)
                        {
                            duty_temp = new duty_index();
                            duty_temp.m = sort_2[i].m;
                            duty_temp.n = sort_2[i].n;
                            duty_temp.c0m = 1;
                            duty_temp.element = 1;//分母
                            duty_temp.rate = 0.5;
                            duty_temp.red = false;
                            sort_duty_c0.Add(duty_temp);
                        }
                        else
                        {
                            for (j = 1; j < sort_2[i].c0m; j++)
                            {
                                duty_temp = new duty_index();
                                duty_temp.m = sort_2[i].m;
                                duty_temp.n = sort_2[i].n;
                                duty_temp.c0m = sort_2[i].c0m;
                                duty_temp.element = j;
                                duty_temp.rate = (double)j / duty_temp.c0m;
                                duty_temp.red = false;
                                sort_duty_c0.Add(duty_temp);
                            }
                        }
                    }

                    sort_duty_c0.Sort(sort_duty_c0_compare);

                    sort_duty_c0_2.Clear();
                    sort_duty_c0_2.Add(sort_duty_c0[0]);

                    for (i = 1; i < sort_duty_c0.Count; i++)
                    {
                        if (sort_duty_c0[i].rate - sort_duty_c0[i - 1].rate > 1e-6)
                            sort_duty_c0_2.Add(sort_duty_c0[i]);
                    }

                    CBB_c0_duty.Items.Clear();
                    for (i = 0; i < sort_duty_c0_2.Count; i++)
                    {
                        CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                    }

                    CBB_c0_duty.SelectedIndex = (CBB_c0_duty.Items.Count - 1) / 2;

                }
                //c0约束结束

                //c1约束开始
                if (CB_c1.Checked)
                {
                    sort_duty_c1.Clear();
                    for (i = 0; i < sort_2_count; i++)
                    {
                        if (sort_2[i].c1m == 1)
                        {
                            duty_temp = new duty_index();
                            duty_temp.m = sort_2[i].m;
                            duty_temp.n = sort_2[i].n;
                            duty_temp.c1m = 1;
                            duty_temp.element = 1;
                            duty_temp.rate = 0.5;
                            duty_temp.red = false;
                            sort_duty_c1.Add(duty_temp);
                        }
                        else
                        {
                            for (j = 1; j < sort_2[i].c1m; j++)
                            {
                                duty_temp = new duty_index();
                                duty_temp.m = sort_2[i].m;
                                duty_temp.n = sort_2[i].n;
                                duty_temp.c1m = sort_2[i].c1m;
                                duty_temp.element = j;
                                duty_temp.rate = (double)j / duty_temp.c1m;
                                duty_temp.red = false;
                                sort_duty_c1.Add(duty_temp);
                            }
                        }

                    }

                    sort_duty_c1.Sort(sort_duty_c1_compare);

                    //LB_group.Text += "\nsort_duty_c1.Count = " + sort_duty_c1.Count;

                    sort_duty_c1_2.Clear();
                    sort_duty_c1_2.Add(sort_duty_c1[0]);

                    for (i = 1; i < sort_duty_c1.Count; i++)
                    {
                        if (sort_duty_c1[i].rate - sort_duty_c1[i - 1].rate > 1e-6)
                            sort_duty_c1_2.Add(sort_duty_c1[i]);
                    }

                    CBB_c1_duty.Items.Clear();
                    for (i = 0; i < sort_duty_c1_2.Count; i++)
                    {
                        CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                    }

                    CBB_c1_duty.SelectedIndex = (CBB_c1_duty.Items.Count - 1) / 2;

                }
                //c1约束结束


                //e0约束开始
                if (CB_e0.Checked)
                {
                    sort_duty_e0.Clear();
                    for (i = 0; i < sort_2_count; i++)
                    {
                        if (sort_2[i].e0m == 1)
                        {
                            duty_temp = new duty_index();
                            duty_temp.m = sort_2[i].m;
                            duty_temp.n = sort_2[i].n;
                            duty_temp.e0m = 1;
                            duty_temp.element = 1;
                            duty_temp.rate = 0.5;
                            duty_temp.red = false;
                            sort_duty_e0.Add(duty_temp);
                        }
                        else
                        {
                            for (j = 1; j < sort_2[i].e0m; j++)
                            {
                                duty_temp = new duty_index();
                                duty_temp.m = sort_2[i].m;
                                duty_temp.n = sort_2[i].n;
                                duty_temp.e0m = sort_2[i].e0m;
                                duty_temp.element = j;
                                duty_temp.rate = (double)j / duty_temp.e0m;
                                duty_temp.red = false;
                                sort_duty_e0.Add(duty_temp);
                            }
                        }

                    }

                    sort_duty_e0.Sort(sort_duty_e0_compare);

                    //LB_group.Text += "\nsort_duty_e0.Count = " + sort_duty_e0.Count;

                    sort_duty_e0_2.Clear();
                    sort_duty_e0_2.Add(sort_duty_e0[0]);

                    for (i = 1; i < sort_duty_e0.Count; i++)
                    {
                        if (sort_duty_e0[i].rate - sort_duty_e0[i - 1].rate > 1e-6)
                            sort_duty_e0_2.Add(sort_duty_e0[i]);
                    }

                    CBB_e0_duty.Items.Clear();
                    for (i = 0; i < sort_duty_e0_2.Count; i++)
                    {
                        CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                    }

                    CBB_e0_duty.SelectedIndex = (CBB_e0_duty.Items.Count - 1) / 2;

                }
                //c3约束开始
                if (CB_c3.Checked)
                {
                    sort_duty_c3.Clear();
                    for (i = 0; i < sort_2_count; i++)
                    {
                        if (sort_2[i].c3m == 1)
                        {
                            duty_temp = new duty_index();
                            duty_temp.m = sort_2[i].m;
                            duty_temp.n = sort_2[i].n;
                            duty_temp.c3m = 1;
                            duty_temp.element = 1;
                            duty_temp.rate = 0.5;
                            duty_temp.red = false;
                            sort_duty_c3.Add(duty_temp);
                        }
                        else
                        {
                            for (j = 1; j < sort_2[i].c3m; j++)
                            {
                                duty_temp = new duty_index();
                                duty_temp.m = sort_2[i].m;
                                duty_temp.n = sort_2[i].n;
                                duty_temp.c3m = sort_2[i].c3m;
                                duty_temp.element = j;
                                duty_temp.rate = (double)j / duty_temp.c3m;
                                duty_temp.red = false;
                                sort_duty_c3.Add(duty_temp);
                            }
                        }
                    }

                    sort_duty_c3.Sort(sort_duty_c3_compare);

                    sort_duty_c3_2.Clear();
                    sort_duty_c3_2.Add(sort_duty_c3[0]);

                    for (i = 1; i < sort_duty_c3.Count; i++)
                    {
                        if (sort_duty_c3[i].rate - sort_duty_c3[i - 1].rate > 1e-6)
                            sort_duty_c3_2.Add(sort_duty_c3[i]);
                    }

                    CBB_c3_duty.Items.Clear();
                    for (i = 0; i < sort_duty_c3_2.Count; i++)
                    {
                        CBB_c3_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c3_2[i].rate).ToString("f3"));
                    }

                    CBB_c3_duty.SelectedIndex = (CBB_c3_duty.Items.Count - 1) / 2;

                }
                //c3约束结束

                //c4约束开始
                if (CB_c4.Checked)
                {
                    sort_duty_c4.Clear();
                    for (i = 0; i < sort_2_count; i++)
                    {
                        if (sort_2[i].c4m == 1)
                        {
                            duty_temp = new duty_index();
                            duty_temp.m = sort_2[i].m;
                            duty_temp.n = sort_2[i].n;
                            duty_temp.c4m = 1;
                            duty_temp.element = 1;
                            duty_temp.rate = 0.5;
                            duty_temp.red = false;
                            sort_duty_c4.Add(duty_temp);
                        }
                        else
                        {
                            for (j = 1; j < sort_2[i].c4m; j++)
                            {
                                duty_temp = new duty_index();
                                duty_temp.m = sort_2[i].m;
                                duty_temp.n = sort_2[i].n;
                                duty_temp.c4m = sort_2[i].c4m;
                                duty_temp.element = j;
                                duty_temp.rate = (double)j / duty_temp.c4m;
                                duty_temp.red = false;
                                sort_duty_c4.Add(duty_temp);
                            }
                        }

                    }

                    sort_duty_c4.Sort(sort_duty_c4_compare);

                    //LB_group.Text += "\nsort_duty_c4.Count = " + sort_duty_c4.Count;

                    sort_duty_c4_2.Clear();
                    sort_duty_c4_2.Add(sort_duty_c4[0]);

                    for (i = 1; i < sort_duty_c4.Count; i++)
                    {
                        if (sort_duty_c4[i].rate - sort_duty_c4[i - 1].rate > 1e-6)
                            sort_duty_c4_2.Add(sort_duty_c4[i]);
                    }

                    CBB_c4_duty.Items.Clear();
                    for (i = 0; i < sort_duty_c4_2.Count; i++)
                    {
                        CBB_c4_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c4_2[i].rate).ToString("f3"));
                    }

                    CBB_c4_duty.SelectedIndex = (CBB_c4_duty.Items.Count - 1) / 2;

                }
                //c4约束结束


                //e02约束开始
                if (CB_e02.Checked)
                {
                    sort_duty_e02.Clear();
                    for (i = 0; i < sort_2_count; i++)
                    {
                        if (sort_2[i].e02m == 1)
                        {
                            duty_temp = new duty_index();
                            duty_temp.m = sort_2[i].m;
                            duty_temp.n = sort_2[i].n;
                            duty_temp.e02m = 1;
                            duty_temp.element = 1;
                            duty_temp.rate = 0.5;
                            duty_temp.red = false;
                            sort_duty_e02.Add(duty_temp);
                        }
                        else
                        {
                            for (j = 1; j < sort_2[i].e02m; j++)
                            {
                                duty_temp = new duty_index();
                                duty_temp.m = sort_2[i].m;
                                duty_temp.n = sort_2[i].n;
                                duty_temp.e02m = sort_2[i].e02m;
                                duty_temp.element = j;
                                duty_temp.rate = (double)j / duty_temp.e02m;
                                duty_temp.red = false;
                                sort_duty_e02.Add(duty_temp);
                            }
                        }

                    }

                    sort_duty_e02.Sort(sort_duty_e02_compare);

                    //LB_group.Text += "\nsort_duty_e02.Count = " + sort_duty_e02.Count;

                    sort_duty_e02_2.Clear();
                    sort_duty_e02_2.Add(sort_duty_e02[0]);

                    for (i = 1; i < sort_duty_e02.Count; i++)
                    {
                        if (sort_duty_e02[i].rate - sort_duty_e02[i - 1].rate > 1e-6)
                            sort_duty_e02_2.Add(sort_duty_e02[i]);
                    }

                    CBB_e02_duty.Items.Clear();
                    for (i = 0; i < sort_duty_e02_2.Count; i++)
                    {
                        CBB_e02_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e02_2[i].rate).ToString("f3"));
                    }

                    CBB_e02_duty.SelectedIndex = (CBB_e02_duty.Items.Count - 1) / 2;

                }
            }
            else
            {
                if (RB_mode0.Checked)//无补偿
                {
                    operation_mode = "NO_COMPENSATION";

                    if (!CB_c0.Checked && !CB_c1.Checked && !CB_e0.Checked)
                    {
                        LB_c0_freq.Text = "";
                        LB_c1_freq.Text = "";
                        LB_e0_freq.Text = "";
                        LB_message_output.Text = "";
                        LB_info_output.Text = "";
                        //DrawPLL();
                        //pictureBox.Refresh();
                        OutPut(1);
                        return false;
                    }

                    mul_lcm = 1;

                    if (CB_c0.Checked)
                    {
                        mul_lcm = LCM(mul_lcm, c0_mul);
                    }
                    if (CB_c1.Checked)
                    {
                        mul_lcm = LCM(mul_lcm, c1_mul);
                    }
                    if (CB_e0.Checked)
                    {
                        mul_lcm = LCM(mul_lcm, e0_mul);
                    }


                    for (i = 1; i <= NmaxF; i++)//n
                    {
                        for (j = 1; j <= MmaxF; j++)//m
                        {
                            if (j % mul_lcm != 0)//m 必须是 mul_lcm 的倍数
                            {
                                sortF[nmF[i, j]].enable = false;
                            }
                            else if (vco_minF - inclk_freq * j / i > 1e-6)//vco >= vco_min
                            {
                                sortF[nmF[i, j]].enable = false;
                            }
                            else if (inclk_freq * j / i - vco_maxF > 1e-6)//vco <= vco_max
                            {
                                sortF[nmF[i, j]].enable = false;
                            }
                            else
                            {
                                if (CB_c0.Checked)
                                {
                                    if (j * c0_div / c0_mul % i != 0)//组合使得 c0_m 可用
                                    {
                                        sortF[nmF[i, j]].enable = false;
                                    }
                                    else
                                    {
                                        sortF[nmF[i, j]].c0m = j * c0_div / c0_mul / i;
                                        if (sortF[nmF[i, j]].c0m > MmaxF)
                                        {
                                            sortF[nmF[i, j]].enable = false;
                                        }
                                    }
                                }
                                if (CB_c1.Checked)//组合使得 c1_m 可用
                                {
                                    if (j * c1_div / c1_mul % i != 0)
                                    {
                                        sortF[nmF[i, j]].enable = false;
                                    }
                                    else
                                    {
                                        sortF[nmF[i, j]].c1m = j * c1_div / c1_mul / i;
                                        if (sortF[nmF[i, j]].c1m > MmaxF)
                                        {
                                            sortF[nmF[i, j]].enable = false;
                                        }
                                    }
                                }
                                if (CB_e0.Checked)//组合使得 e0_m 可用
                                {
                                    if (j * e0_div / e0_mul % i != 0)
                                    {
                                        sortF[nmF[i, j]].enable = false;
                                    }
                                    else
                                    {
                                        sortF[nmF[i, j]].e0m = j * e0_div / e0_mul / i;
                                        if (sortF[nmF[i, j]].e0m > MmaxF)
                                        {
                                            sortF[nmF[i, j]].enable = false;
                                        }
                                    }
                                }
                            }
                        }
                    }

                    //LB_group.Text = "";


                    //筛选开始
                    for (j = 0; j < NCMF; j++)
                    {
                        if (sortF[j].enable == true)
                            break;
                    }
                    if (j == NCMF)
                    {
                        OutPut(1);
                        LB_message_output.Text = "No suitable result or Vco frequency exceeds (" + vco_minF.ToString("f0") + "," + vco_maxF.ToString("f0") + "), please adjust your multiplication or division factor.";
                        LB_info_output.Text = "";

                        CBB_c0_duty.Enabled = false;
                        CBB_c0_phase.Enabled = false;
                        CBB_c1_duty.Enabled = false;
                        CBB_c1_phase.Enabled = false;
                        CBB_e0_duty.Enabled = false;
                        CBB_e0_phase.Enabled = false;

                        OutPut(1);
                        return false;
                    }
                    i = 0;

                    sort_2F[0].n = sortF[j].n;
                    sort_2F[0].m = sortF[j].m;
                    sort_2F[0].value = sortF[j].value;
                    sort_2F[0].c0m = sortF[j].c0m;
                    sort_2F[0].c1m = sortF[j].c1m;
                    sort_2F[0].e0m = sortF[j].e0m;
                    sort_2F[0].enable = true;

                    for (j++; j < NCMF; j++)
                    {
                        if (sortF[j].enable == true)
                        {
                            if (sortF[j].value - sort_2F[i].value > 1e-6)// i/j  n/m  可以改，比如把分子分母的选择加上（已经在排序时完成）
                            {
                                for (k = 0; k <= i; k++)
                                {
                                    //这句留待优化 ly_remark
                                    if (CB_c0.Checked && sort_2F[k].c0m % sortF[j].c0m == 0)
                                        break;
                                    if (CB_c1.Checked && sort_2F[k].c1m % sortF[j].c1m == 0)
                                        break;
                                    if (CB_e0.Checked && sort_2F[k].e0m % sortF[j].e0m == 0)
                                        break;
                                }
                                if (k == i + 1)
                                {
                                    i++;
                                    sort_2F[i].n = sortF[j].n;
                                    sort_2F[i].m = sortF[j].m;
                                    sort_2F[i].value = sortF[j].value;
                                    sort_2F[i].c0m = sortF[j].c0m;
                                    sort_2F[i].c1m = sortF[j].c1m;
                                    sort_2F[i].e0m = sortF[j].e0m;
                                    sort_2F[i].enable = true;
                                }
                            }
                        }
                    }
                    sort_2_count = i + 1;//可用sortF个数
                    //筛选结束（三个输出共用，此时保留所有可用的c0_m c1_m e0_m）

                    //int count = 0;//换行计数



                    //下边开始枚举可用的占空比
                    //c0约束开始
                    if (CB_c0.Checked)
                    {
                        sort_duty_c0.Clear();
                        for (i = 0; i < sort_2_count; i++)
                        {
                            if (sort_2F[i].c0m == 1)
                            {
                                duty_temp = new duty_index();
                                duty_temp.m = sort_2F[i].m;
                                duty_temp.n = sort_2F[i].n;
                                duty_temp.c0m = 1;
                                duty_temp.element = 1;
                                duty_temp.rate = 0.5;
                                duty_temp.red = false;
                                sort_duty_c0.Add(duty_temp);
                            }
                            else
                            {
                                for (j = 1; j < sort_2F[i].c0m; j++)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2F[i].m;
                                    duty_temp.n = sort_2F[i].n;
                                    duty_temp.c0m = sort_2F[i].c0m;
                                    duty_temp.element = j;
                                    duty_temp.rate = (double)j / duty_temp.c0m;
                                    duty_temp.red = false;
                                    sort_duty_c0.Add(duty_temp);
                                }
                            }
                        }

                        sort_duty_c0.Sort(sort_duty_c0_compare);

                        sort_duty_c0_2.Clear();
                        sort_duty_c0_2.Add(sort_duty_c0[0]);

                        for (i = 1; i < sort_duty_c0.Count; i++)
                        {
                            if (sort_duty_c0[i].rate - sort_duty_c0[i - 1].rate > 1e-6)
                                sort_duty_c0_2.Add(sort_duty_c0[i]);
                        }

                        CBB_c0_duty.Items.Clear();
                        for (i = 0; i < sort_duty_c0_2.Count; i++)
                        {
                            CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                        }

                        CBB_c0_duty.SelectedIndex = (CBB_c0_duty.Items.Count - 1) / 2;


                    }
                    //c0约束结束

                    //c1约束开始
                    if (CB_c1.Checked)
                    {
                        sort_duty_c1.Clear();
                        for (i = 0; i < sort_2_count; i++)
                        {
                            if (sort_2F[i].c1m == 1)
                            {
                                duty_temp = new duty_index();
                                duty_temp.m = sort_2F[i].m;
                                duty_temp.n = sort_2F[i].n;
                                duty_temp.c1m = 1;
                                duty_temp.element = 1;
                                duty_temp.rate = 0.5;
                                duty_temp.red = false;
                                sort_duty_c1.Add(duty_temp);
                            }
                            else
                            {
                                for (j = 1; j < sort_2F[i].c1m; j++)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2F[i].m;
                                    duty_temp.n = sort_2F[i].n;
                                    duty_temp.c1m = sort_2F[i].c1m;
                                    duty_temp.element = j;
                                    duty_temp.rate = (double)j / duty_temp.c1m;
                                    duty_temp.red = false;
                                    sort_duty_c1.Add(duty_temp);
                                }
                            }

                        }

                        sort_duty_c1.Sort(sort_duty_c1_compare);

                        //LB_group.Text += "\nsort_duty_c1.Count = " + sort_duty_c1.Count;

                        sort_duty_c1_2.Clear();
                        sort_duty_c1_2.Add(sort_duty_c1[0]);

                        for (i = 1; i < sort_duty_c1.Count; i++)
                        {
                            if (sort_duty_c1[i].rate - sort_duty_c1[i - 1].rate > 1e-6)
                                sort_duty_c1_2.Add(sort_duty_c1[i]);
                        }

                        CBB_c1_duty.Items.Clear();
                        for (i = 0; i < sort_duty_c1_2.Count; i++)
                        {
                            CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                        }

                        CBB_c1_duty.SelectedIndex = (CBB_c1_duty.Items.Count - 1) / 2;
                    }
                    //c1约束结束


                    //e0约束开始
                    if (CB_e0.Checked)
                    {
                        sort_duty_e0.Clear();
                        for (i = 0; i < sort_2_count; i++)
                        {
                            if (sort_2F[i].e0m == 1)
                            {
                                duty_temp = new duty_index();
                                duty_temp.m = sort_2F[i].m;
                                duty_temp.n = sort_2F[i].n;
                                duty_temp.e0m = 1;
                                duty_temp.element = 1;
                                duty_temp.rate = 0.5;
                                duty_temp.red = false;
                                sort_duty_e0.Add(duty_temp);
                            }
                            else
                            {
                                for (j = 1; j < sort_2F[i].e0m; j++)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2F[i].m;
                                    duty_temp.n = sort_2F[i].n;
                                    duty_temp.e0m = sort_2F[i].e0m;
                                    duty_temp.element = j;
                                    duty_temp.rate = (double)j / duty_temp.e0m;
                                    duty_temp.red = false;
                                    sort_duty_e0.Add(duty_temp);
                                }
                            }

                        }

                        sort_duty_e0.Sort(sort_duty_e0_compare);

                        //LB_group.Text += "\nsort_duty_e0.Count = " + sort_duty_e0.Count;

                        sort_duty_e0_2.Clear();
                        sort_duty_e0_2.Add(sort_duty_e0[0]);

                        for (i = 1; i < sort_duty_e0.Count; i++)
                        {
                            if (sort_duty_e0[i].rate - sort_duty_e0[i - 1].rate > 1e-6)
                                sort_duty_e0_2.Add(sort_duty_e0[i]);
                        }

                        CBB_e0_duty.Items.Clear();
                        for (i = 0; i < sort_duty_e0_2.Count; i++)
                        {
                            CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                        }

                        CBB_e0_duty.SelectedIndex = (CBB_e0_duty.Items.Count - 1) / 2;
                        //LB_group.Text += "\ne0 changed [ n = " + sort_duty_e0_2[CBB_e0_duty.SelectedIndex].n.ToString()
                        //    + " m = " + sort_duty_e0_2[CBB_e0_duty.SelectedIndex].m.ToString()
                        //    + " c0m = " + sort_duty_e0_2[CBB_e0_duty.SelectedIndex].c0m.ToString()
                        //    + " c1m = " + sort_duty_e0_2[CBB_e0_duty.SelectedIndex].c1m.ToString()
                        //    + " e0m = " + sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m.ToString() + " ]";
                    }
                    //e0约束结束
                }
                else if (RB_mode1.Checked)//零延时，e0补偿
                {
                    //MessageBox.Show("ZERO_DELAY_BUFFER");
                    operation_mode = "ZERO_DELAY_BUFFER";

                    if (CB_c0.Checked)
                        if (CB_c1.Checked)
                            mul_lcm = LCM(c0_mul, c1_mul);
                        else
                            mul_lcm = c0_mul;
                    else
                        if (CB_c1.Checked)
                            mul_lcm = c1_mul;
                        else
                            mul_lcm = 1;

                    for (j = MmaxF; j >= 1; j--)//e0m
                    {
                        if (j % mul_lcm != 0)//e0m 必须是 mul_lcm 的倍数
                        {
                            sort_spl[j].enable = false;
                        }
                        else if (vco_minF - inclk_freq * j > 1e-6)//vco >= vco_min
                        {
                            sort_spl[j].enable = false;
                        }
                        else if (inclk_freq * j - vco_maxF > 1e-6)//vco <= vco_max
                        {
                            sort_spl[j].enable = false;
                        }
                        else
                        {
                            sort_spl[j].e0m = j;
                            if (CB_c0.Checked)
                            {
                                sort_spl[j].c0m = j * c0_div / c0_mul;
                                if (sort_spl[j].c0m > MmaxF)
                                    sort_spl[j].enable = false;
                            }
                            if (CB_c1.Checked)//组合使得 c1_m 可用
                            {
                                sort_spl[j].c1m = j * c1_div / c1_mul;
                                if (sort_spl[j].c1m > MmaxF)
                                    sort_spl[j].enable = false;
                            }
                        }
                        for (i = MmaxF; i > j; i--)
                        {
                            if (sort_spl[i].enable == true && i % j == 0)
                                sort_spl[j].enable = false;
                        }
                    }

                    //LB_group.Text = "";

                    for (j = MmaxF; j >= 1; j--)//e0m
                    {
                        if (sort_spl[j].enable == true)
                            break;
                    }

                    if (j == 0)
                    {
                        OutPut(1);
                        LB_message_output.Text = "No suitable result or Vco frequency exceeds (" + vco_minF.ToString("f0") + "," + vco_maxF.ToString("f0") + "), please adjust your multiplication or division factor.";
                        LB_info_output.Text = "";

                        CBB_c0_duty.Enabled = false;
                        CBB_c0_phase.Enabled = false;
                        CBB_c1_duty.Enabled = false;
                        CBB_c1_phase.Enabled = false;
                        CBB_e0_duty.Enabled = false;
                        CBB_e0_phase.Enabled = false;

                        //DrawPLL();
                        //pictureBox.Refresh();
                        return false;
                    }

                    //（三个输出共用，此时保留所有可用的c0_m c1_m e0_m）


                    //下便开始枚举可用的占空比
                    //c0约束开始
                    if (CB_c0.Checked)
                    {
                        sort_duty_c0.Clear();
                        for (i = 1; i <= MmaxF; i++)
                        {
                            if (sort_spl[i].enable == true)
                            {
                                if (sort_spl[i].c0m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = 1;
                                    duty_temp.n = 1;
                                    duty_temp.c0m = 1;
                                    duty_temp.e0m = i;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    duty_temp.red = false;
                                    sort_duty_c0.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_spl[i].c0m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = 1;
                                        duty_temp.n = 1;
                                        duty_temp.c0m = sort_spl[i].c0m;
                                        duty_temp.e0m = i;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c0m;
                                        duty_temp.red = false;
                                        sort_duty_c0.Add(duty_temp);
                                    }
                                }
                            }
                        }

                        sort_duty_c0.Sort(sort_duty_c0_compare);

                        //LB_group.Text += "\nsort_duty_c0.Count = " + sort_duty_c0.Count;

                        sort_duty_c0_2.Clear();
                        sort_duty_c0_2.Add(sort_duty_c0[0]);

                        for (i = 1; i < sort_duty_c0.Count; i++)
                        {
                            if (sort_duty_c0[i].rate - sort_duty_c0[i - 1].rate > 1e-6)
                                sort_duty_c0_2.Add(sort_duty_c0[i]);
                        }

                        CBB_c0_duty.Items.Clear();
                        for (i = 0; i < sort_duty_c0_2.Count; i++)
                        {
                            CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                        }

                        CBB_c0_duty.SelectedIndex = (CBB_c0_duty.Items.Count - 1) / 2;
                    }
                    //c0约束结束

                    //c1约束开始
                    if (CB_c1.Checked)
                    {
                        sort_duty_c1.Clear();
                        for (i = 1; i <= MmaxF; i++)
                        {
                            if (sort_spl[i].enable == true)
                            {
                                if (sort_spl[i].c1m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = 1;
                                    duty_temp.n = 1;
                                    duty_temp.c1m = 1;
                                    duty_temp.e0m = i;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    duty_temp.red = false;
                                    sort_duty_c1.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_spl[i].c1m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = 1;
                                        duty_temp.n = 1;
                                        duty_temp.c1m = sort_spl[i].c1m;
                                        duty_temp.e0m = i;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c1m;
                                        duty_temp.red = false;
                                        sort_duty_c1.Add(duty_temp);
                                    }
                                }
                            }
                        }

                        sort_duty_c1.Sort(sort_duty_c1_compare);

                        //LB_group.Text += "\nsort_duty_c1.Count = " + sort_duty_c1.Count;

                        sort_duty_c1_2.Clear();
                        sort_duty_c1_2.Add(sort_duty_c1[0]);

                        for (i = 1; i < sort_duty_c1.Count; i++)
                        {
                            if (sort_duty_c1[i].rate - sort_duty_c1[i - 1].rate > 1e-6)
                                sort_duty_c1_2.Add(sort_duty_c1[i]);
                        }

                        CBB_c1_duty.Items.Clear();
                        for (i = 0; i < sort_duty_c1_2.Count; i++)
                        {
                            CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                        }

                        CBB_c1_duty.SelectedIndex = (CBB_c1_duty.Items.Count - 1) / 2;
                    }
                    //c1约束结束

                    //e0约束开始
                    sort_duty_e0.Clear();
                    for (i = 1; i <= MmaxF; i++)
                    {
                        if (sort_spl[i].enable == true)
                        {
                            if (i == 1)
                            {
                                duty_temp = new duty_index();
                                duty_temp.m = 1;
                                duty_temp.n = 1;
                                duty_temp.e0m = 1;
                                duty_temp.element = 1;
                                duty_temp.rate = 0.5;
                                duty_temp.red = false;
                                sort_duty_e0.Add(duty_temp);
                            }
                            else
                            {
                                for (j = 1; j < i; j++)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = 1;
                                    duty_temp.n = 1;
                                    duty_temp.e0m = i;
                                    duty_temp.element = j;
                                    duty_temp.rate = (double)j / i;
                                    duty_temp.red = false;
                                    sort_duty_e0.Add(duty_temp);
                                }
                            }
                        }
                    }

                    sort_duty_e0.Sort(sort_duty_e0_compare);

                    //LB_group.Text += "\nsort_duty_e0.Count = " + sort_duty_e0.Count;

                    sort_duty_e0_2.Clear();
                    sort_duty_e0_2.Add(sort_duty_e0[0]);

                    for (i = 1; i < sort_duty_e0.Count; i++)
                    {
                        if (sort_duty_e0[i].rate - sort_duty_e0[i - 1].rate > 1e-6)
                            sort_duty_e0_2.Add(sort_duty_e0[i]);
                    }

                    CBB_e0_duty.Items.Clear();
                    for (i = 0; i < sort_duty_e0_2.Count; i++)
                    {
                        CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                    }

                    CBB_e0_duty.SelectedIndex = (CBB_e0_duty.Items.Count - 1) / 2;
                    //e0约束结束
                }
                else if (RB_mode2.Checked)//普通，c0补偿
                {
                    //MessageBox.Show("NORMAL c0");
                    operation_mode = "NORMAL";

                    if (CB_c1.Checked)
                        if (CB_e0.Checked)
                            mul_lcm = LCM(c1_mul, e0_mul);
                        else
                            mul_lcm = c1_mul;
                    else
                        if (CB_e0.Checked)
                            mul_lcm = e0_mul;
                        else
                        {
                            mul_lcm = 1;
                        }

                    for (j = MmaxF; j >= 1; j--)//e0m
                    {
                        if (j % mul_lcm != 0)//e0m 必须是 mul_lcm 的倍数
                        {
                            sort_spl[j].enable = false;
                        }
                        else if (vco_minF - inclk_freq * j > 1e-6)//vco >= vco_min
                        {
                            sort_spl[j].enable = false;
                        }
                        else if (inclk_freq * j - vco_maxF > 1e-6)//vco <= vco_max
                        {
                            sort_spl[j].enable = false;
                        }
                        else
                        {
                            sort_spl[j].c0m = j;
                            if (CB_c1.Checked)
                            {
                                sort_spl[j].c1m = j * c1_div / c1_mul;
                                if (sort_spl[j].c1m > MmaxF)
                                    sort_spl[j].enable = false;
                            }
                            if (CB_e0.Checked)//组合使得 c1_m 可用
                            {
                                sort_spl[j].e0m = j * e0_div / e0_mul;
                                if (sort_spl[j].e0m > MmaxF)
                                    sort_spl[j].enable = false;
                            }
                        }
                        for (i = MmaxF; i > j; i--)
                        {
                            if (sort_spl[i].enable == true && i % j == 0)
                                sort_spl[j].enable = false;
                        }
                    }

                    //LB_group.Text = "";

                    for (j = MmaxF; j >= 1; j--)//e0m
                    {
                        if (sort_spl[j].enable == true)
                            break;
                    }

                    if (j == 0)
                    {
                        OutPut(1);
                        LB_message_output.Text = "No suitable result or Vco frequency exceeds (" + vco_minF.ToString("f0") + "," + vco_maxF.ToString("f0") + "), please adjust your multiplication or division factor.";
                        LB_info_output.Text = "";

                        CBB_c0_duty.Enabled = false;
                        CBB_c0_phase.Enabled = false;
                        CBB_c1_duty.Enabled = false;
                        CBB_c1_phase.Enabled = false;
                        CBB_e0_duty.Enabled = false;
                        CBB_e0_phase.Enabled = false;

                        //DrawPLL();
                        //pictureBox.Refresh();
                        return false;
                    }

                    //（三个输出共用，此时保留所有可用的c0_m c1_m e0_m）


                    //下便开始枚举可用的占空比
                    //c1约束开始
                    if (CB_c1.Checked)
                    {
                        sort_duty_c1.Clear();
                        for (i = 1; i <= MmaxF; i++)
                        {
                            if (sort_spl[i].enable == true)
                            {
                                if (sort_spl[i].c1m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = 1;
                                    duty_temp.n = 1;
                                    duty_temp.c1m = 1;
                                    duty_temp.c0m = i;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    duty_temp.red = false;
                                    sort_duty_c1.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_spl[i].c1m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = 1;
                                        duty_temp.n = 1;
                                        duty_temp.c1m = sort_spl[i].c1m;
                                        duty_temp.c0m = i;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c1m;
                                        duty_temp.red = false;
                                        sort_duty_c1.Add(duty_temp);
                                    }
                                }
                            }
                        }

                        sort_duty_c1.Sort(sort_duty_c1_compare);

                        //LB_group.Text += "\nsort_duty_c1.Count = " + sort_duty_c1.Count;

                        sort_duty_c1_2.Clear();
                        sort_duty_c1_2.Add(sort_duty_c1[0]);

                        for (i = 1; i < sort_duty_c1.Count; i++)
                        {
                            if (sort_duty_c1[i].rate - sort_duty_c1[i - 1].rate > 1e-6)
                                sort_duty_c1_2.Add(sort_duty_c1[i]);
                        }

                        CBB_c1_duty.Items.Clear();
                        for (i = 0; i < sort_duty_c1_2.Count; i++)
                        {
                            CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                        }

                        CBB_c1_duty.SelectedIndex = (CBB_c1_duty.Items.Count - 1) / 2;
                    }
                    //c1约束结束

                    //e0约束开始
                    if (CB_e0.Checked)
                    {
                        sort_duty_e0.Clear();
                        for (i = 1; i <= MmaxF; i++)
                        {
                            if (sort_spl[i].enable == true)
                            {
                                if (sort_spl[i].e0m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = 1;
                                    duty_temp.n = 1;
                                    duty_temp.e0m = 1;
                                    duty_temp.c0m = i;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    duty_temp.red = false;
                                    sort_duty_e0.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_spl[i].e0m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = 1;
                                        duty_temp.n = 1;
                                        duty_temp.e0m = sort_spl[i].e0m;
                                        duty_temp.c0m = i;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.e0m;
                                        duty_temp.red = false;
                                        sort_duty_e0.Add(duty_temp);
                                    }
                                }
                            }
                        }

                        sort_duty_e0.Sort(sort_duty_e0_compare);

                        //LB_group.Text += "\nsort_duty_e0.Count = " + sort_duty_e0.Count;

                        sort_duty_e0_2.Clear();
                        sort_duty_e0_2.Add(sort_duty_e0[0]);

                        for (i = 1; i < sort_duty_e0.Count; i++)
                        {
                            if (sort_duty_e0[i].rate - sort_duty_e0[i - 1].rate > 1e-6)
                                sort_duty_e0_2.Add(sort_duty_e0[i]);
                        }

                        CBB_e0_duty.Items.Clear();
                        for (i = 0; i < sort_duty_e0_2.Count; i++)
                        {
                            CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                        }

                        CBB_e0_duty.SelectedIndex = (CBB_e0_duty.Items.Count - 1) / 2;
                    }
                    //c1约束结束


                    //c0约束开始
                    sort_duty_c0.Clear();
                    for (i = 1; i <= MmaxF; i++)
                    {
                        if (sort_spl[i].enable == true)
                        {
                            if (i == 1)
                            {
                                duty_temp = new duty_index();
                                duty_temp.m = 1;
                                duty_temp.n = 1;
                                duty_temp.c0m = 1;
                                duty_temp.element = 1;
                                duty_temp.rate = 0.5;
                                duty_temp.red = false;
                                sort_duty_c0.Add(duty_temp);
                            }
                            else
                            {
                                for (j = 1; j < i; j++)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = 1;
                                    duty_temp.n = 1;
                                    duty_temp.c0m = i;
                                    duty_temp.element = j;
                                    duty_temp.rate = (double)j / i;
                                    duty_temp.red = false;
                                    sort_duty_c0.Add(duty_temp);
                                }
                            }
                        }
                    }

                    sort_duty_c0.Sort(sort_duty_c0_compare);

                    //LB_group.Text += "\nsort_duty_c0.Count = " + sort_duty_c0.Count;

                    sort_duty_c0_2.Clear();
                    sort_duty_c0_2.Add(sort_duty_c0[0]);

                    for (i = 1; i < sort_duty_c0.Count; i++)
                    {
                        if (sort_duty_c0[i].rate - sort_duty_c0[i - 1].rate > 1e-6)
                            sort_duty_c0_2.Add(sort_duty_c0[i]);
                    }

                    CBB_c0_duty.Items.Clear();
                    for (i = 0; i < sort_duty_c0_2.Count; i++)
                    {
                        CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                    }

                    CBB_c0_duty.SelectedIndex = (CBB_c0_duty.Items.Count - 1) / 2;
                    //c0约束结束
                }
                else if (RB_mode3.Checked)//普通，c1补偿
                {
                    //MessageBox.Show("NORMAL c1");
                    operation_mode = "NORMAL";

                    if (CB_c0.Checked)
                        if (CB_e0.Checked)
                            mul_lcm = LCM(c0_mul, e0_mul);
                        else
                            mul_lcm = c0_mul;
                    else
                        if (CB_e0.Checked)
                            mul_lcm = e0_mul;
                        else
                        {
                            mul_lcm = 1;
                        }

                    for (j = MmaxF; j >= 1; j--)//e0m
                    {
                        if (j % mul_lcm != 0)//e0m 必须是 mul_lcm 的倍数
                        {
                            sort_spl[j].enable = false;
                        }
                        else if (vco_minF - inclk_freq * j > 1e-6)//vco >= vco_min
                        {
                            sort_spl[j].enable = false;
                        }
                        else if (inclk_freq * j - vco_maxF > 1e-6)//vco <= vco_max
                        {
                            sort_spl[j].enable = false;
                        }
                        else
                        {
                            sort_spl[j].c1m = j;
                            if (CB_c0.Checked)
                            {
                                sort_spl[j].c0m = j * c0_div / c0_mul;
                                if (sort_spl[j].c0m > MmaxF)
                                    sort_spl[j].enable = false;
                            }
                            if (CB_e0.Checked)
                            {
                                sort_spl[j].e0m = j * e0_div / e0_mul;
                                if (sort_spl[j].e0m > MmaxF)
                                    sort_spl[j].enable = false;
                            }
                        }
                        for (i = MmaxF; i > j; i--)
                        {
                            if (sort_spl[i].enable == true && i % j == 0)
                                sort_spl[j].enable = false;
                        }
                    }

                    //LB_group.Text = "";

                    for (j = MmaxF; j >= 1; j--)//e0m
                    {
                        if (sort_spl[j].enable == true)
                            break;
                    }

                    if (j == 0)
                    {
                        OutPut(1);
                        LB_message_output.Text = "No suitable result or Vco frequency exceeds (" + vco_minF.ToString("f0") + "," + vco_maxF.ToString("f0") + "), please adjust your multiplication or division factor.";
                        LB_info_output.Text = "";

                        CBB_c0_duty.Enabled = false;
                        CBB_c0_phase.Enabled = false;
                        CBB_c1_duty.Enabled = false;
                        CBB_c1_phase.Enabled = false;
                        CBB_e0_duty.Enabled = false;
                        CBB_e0_phase.Enabled = false;

                        //DrawPLL();
                        //pictureBox.Refresh();
                        return false;
                    }

                    //（三个输出共用，此时保留所有可用的c0_m c1_m e0_m）


                    //下便开始枚举可用的占空比
                    //c0约束开始
                    if (CB_c0.Checked)
                    {
                        sort_duty_c0.Clear();
                        for (i = 1; i <= MmaxF; i++)
                        {
                            if (sort_spl[i].enable == true)
                            {
                                if (sort_spl[i].c0m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = 1;
                                    duty_temp.n = 1;
                                    duty_temp.c0m = 1;
                                    duty_temp.c1m = i;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    duty_temp.red = false;
                                    sort_duty_c0.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_spl[i].c0m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = 1;
                                        duty_temp.n = 1;
                                        duty_temp.c0m = sort_spl[i].c0m;
                                        duty_temp.c1m = i;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c0m;
                                        duty_temp.red = false;
                                        sort_duty_c0.Add(duty_temp);
                                    }
                                }
                            }
                        }

                        sort_duty_c0.Sort(sort_duty_c0_compare);

                        //LB_group.Text += "\nsort_duty_c0.Count = " + sort_duty_c0.Count;

                        sort_duty_c0_2.Clear();
                        sort_duty_c0_2.Add(sort_duty_c0[0]);

                        for (i = 1; i < sort_duty_c0.Count; i++)
                        {
                            if (sort_duty_c0[i].rate - sort_duty_c0[i - 1].rate > 1e-6)
                                sort_duty_c0_2.Add(sort_duty_c0[i]);
                        }

                        CBB_c0_duty.Items.Clear();
                        for (i = 0; i < sort_duty_c0_2.Count; i++)
                        {
                            CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                        }

                        CBB_c0_duty.SelectedIndex = (CBB_c0_duty.Items.Count - 1) / 2;
                    }
                    //c0约束结束

                    //e0约束开始
                    if (CB_e0.Checked)
                    {
                        sort_duty_e0.Clear();
                        for (i = 1; i <= MmaxF; i++)
                        {
                            if (sort_spl[i].enable == true)
                            {
                                if (sort_spl[i].e0m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = 1;
                                    duty_temp.n = 1;
                                    duty_temp.e0m = 1;
                                    duty_temp.c1m = i;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    duty_temp.red = false;
                                    sort_duty_e0.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_spl[i].e0m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = 1;
                                        duty_temp.n = 1;
                                        duty_temp.e0m = sort_spl[i].e0m;
                                        duty_temp.c1m = i;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.e0m;
                                        duty_temp.red = false;
                                        sort_duty_e0.Add(duty_temp);
                                    }
                                }
                            }
                        }

                        sort_duty_e0.Sort(sort_duty_e0_compare);

                        //LB_group.Text += "\nsort_duty_e0.Count = " + sort_duty_e0.Count;

                        sort_duty_e0_2.Clear();
                        sort_duty_e0_2.Add(sort_duty_e0[0]);

                        for (i = 1; i < sort_duty_e0.Count; i++)
                        {
                            if (sort_duty_e0[i].rate - sort_duty_e0[i - 1].rate > 1e-6)
                                sort_duty_e0_2.Add(sort_duty_e0[i]);
                        }

                        CBB_e0_duty.Items.Clear();
                        for (i = 0; i < sort_duty_e0_2.Count; i++)
                        {
                            CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                        }

                        CBB_e0_duty.SelectedIndex = (CBB_e0_duty.Items.Count - 1) / 2;
                    }
                    //e0约束结束


                    //c1约束开始
                    sort_duty_c1.Clear();
                    for (i = 1; i <= MmaxF; i++)
                    {
                        if (sort_spl[i].enable == true)
                        {
                            if (i == 1)
                            {
                                duty_temp = new duty_index();
                                duty_temp.m = 1;
                                duty_temp.n = 1;
                                duty_temp.c1m = 1;
                                duty_temp.element = 1;
                                duty_temp.rate = 0.5;
                                duty_temp.red = false;
                                sort_duty_c1.Add(duty_temp);
                            }
                            else
                            {
                                for (j = 1; j < i; j++)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = 1;
                                    duty_temp.n = 1;
                                    duty_temp.c1m = i;
                                    duty_temp.element = j;
                                    duty_temp.rate = (double)j / i;
                                    duty_temp.red = false;
                                    sort_duty_c1.Add(duty_temp);
                                }
                            }
                        }
                    }

                    sort_duty_c1.Sort(sort_duty_c1_compare);

                    //LB_group.Text += "\nsort_duty_c1.Count = " + sort_duty_c1.Count;

                    sort_duty_c1_2.Clear();
                    sort_duty_c1_2.Add(sort_duty_c1[0]);

                    for (i = 1; i < sort_duty_c1.Count; i++)
                    {
                        if (sort_duty_c1[i].rate - sort_duty_c1[i - 1].rate > 1e-6)
                            sort_duty_c1_2.Add(sort_duty_c1[i]);
                    }

                    CBB_c1_duty.Items.Clear();
                    for (i = 0; i < sort_duty_c1_2.Count; i++)
                    {
                        CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                    }

                    CBB_c1_duty.SelectedIndex = (CBB_c1_duty.Items.Count - 1) / 2;
                    //c1约束结束
                }
                else
                {
                    MessageBox.Show("operation_mode error");
                    LB_message_output.Text = "operation_mode error";
                }
            }

            LB_message_output.Text = "";
            OutPut(0);

            //CBB_c0_duty.Enabled = CB_c0.Checked;
            //CBB_c0_phase.Enabled = CB_c0.Checked;
            //CBB_c1_duty.Enabled = CB_c1.Checked;
            //CBB_c1_phase.Enabled = CB_c1.Checked;
            //CBB_e0_duty.Enabled = CB_e0.Checked;
            //CBB_e0_phase.Enabled = CB_e0.Checked;
            // 
            //DrawPLL();
            //pictureBox.Refresh();
            //MessageBox.Show("RefreshData");
            return true;
        }
        private bool RefreshData2(int c012)
        {
            LB_message_output.ForeColor = System.Drawing.Color.Red;
            //MessageBox.Show("RefreshData2");
            int cm;
            //int element;
            if (PTE)
            {
                if (c012 == 0)
                {
                    if (CB_c1.Checked || CB_e0.Checked || CB_c3.Checked || CB_c4.Checked || CB_e02.Checked)
                    {
                        cm = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m;
                        cm /= GCD(sort_duty_c0_2[CBB_c0_duty.SelectedIndex].element, cm);
                        if (CB_c1.Checked)
                        {
                            sort_duty_c1.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c1m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c1m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c0m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c1.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c1m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c1m = sort_2[i].c1m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c1m;
                                        if (sort_2[i].c0m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c1.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c1.Sort(sort_duty_c1_compare);

                            //LB_group.Text += "\nsort_duty_c1_d.Count = " + sort_duty_c1.Count;

                            count_temp = sort_duty_c1_2.Count;

                            sort_duty_c1_2.Clear();
                            sort_duty_c1_2.Add(sort_duty_c1[0]);

                            for (i = 1; i < sort_duty_c1.Count; i++)
                            {
                                if (sort_duty_c1[i].rate - sort_duty_c1[i - 1].rate > 1e-6)
                                    sort_duty_c1_2.Add(sort_duty_c1[i]);
                                else
                                    if (sort_duty_c1[i].red == false && sort_duty_c1[i - 1].red == true)
                                    {
                                        sort_duty_c1_2.Remove(sort_duty_c1_2.Last());
                                        sort_duty_c1_2.Add(sort_duty_c1[i]);
                                    }
                            }

                            CBB_c1_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c1_2.Count; i++)
                            {
                                if (sort_duty_c1_2[i].red)
                                    CBB_c1_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                                else
                                    CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                            }

                            CBB_c1_duty.SelectedIndex = SelectedIndex_c1;

                            if (sort_duty_c1_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c1_2.Count error");
                            }
                        }
                        if (CB_e0.Checked)
                        {
                            sort_duty_e0.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].e0m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.e0m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c0m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_e0.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].e0m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.e0m = sort_2[i].e0m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.e0m;
                                        if (sort_2[i].c0m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_e0.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_e0.Sort(sort_duty_e0_compare);

                            //LB_group.Text += "\nsort_duty_e0_d.Count = " + sort_duty_e0.Count;

                            count_temp = sort_duty_e0_2.Count;

                            sort_duty_e0_2.Clear();
                            sort_duty_e0_2.Add(sort_duty_e0[0]);

                            for (i = 1; i < sort_duty_e0.Count; i++)
                            {
                                if (sort_duty_e0[i].rate - sort_duty_e0[i - 1].rate > 1e-6)
                                    sort_duty_e0_2.Add(sort_duty_e0[i]);
                                else
                                    if (sort_duty_e0[i].red == false && sort_duty_e0[i - 1].red == true)
                                    {
                                        sort_duty_e0_2.Remove(sort_duty_e0_2.Last());
                                        sort_duty_e0_2.Add(sort_duty_e0[i]);
                                    }
                            }

                            CBB_e0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_e0_2.Count; i++)
                            {
                                if (sort_duty_e0_2[i].red)
                                    CBB_e0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                                else
                                    CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                            }

                            CBB_e0_duty.SelectedIndex = SelectedIndex_e0;

                            if (sort_duty_e0_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_e0_2.Count error");
                            }
                        }
                        if (CB_c3.Checked)
                        {
                            sort_duty_c3.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c3m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c3m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c0m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c3.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c3m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c3m = sort_2[i].c3m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c3m;
                                        if (sort_2[i].c0m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c3.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c3.Sort(sort_duty_c3_compare);

                            //LB_group.Text += "\nsort_duty_c3_d.Count = " + sort_duty_c3.Count;

                            count_temp = sort_duty_c3_2.Count;

                            sort_duty_c3_2.Clear();
                            sort_duty_c3_2.Add(sort_duty_c3[0]);

                            for (i = 1; i < sort_duty_c3.Count; i++)
                            {
                                if (sort_duty_c3[i].rate - sort_duty_c3[i - 1].rate > 1e-6)
                                    sort_duty_c3_2.Add(sort_duty_c3[i]);
                                else
                                    if (sort_duty_c3[i].red == false && sort_duty_c3[i - 1].red == true)
                                    {
                                        sort_duty_c3_2.Remove(sort_duty_c3_2.Last());
                                        sort_duty_c3_2.Add(sort_duty_c3[i]);
                                    }
                            }

                            CBB_c3_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c3_2.Count; i++)
                            {
                                if (sort_duty_c3_2[i].red)
                                    CBB_c3_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c3_2[i].rate).ToString("f3"));
                                else
                                    CBB_c3_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c3_2[i].rate).ToString("f3"));
                            }

                            CBB_c3_duty.SelectedIndex = SelectedIndex_c3;

                            if (sort_duty_c3_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c3_2.Count error");
                            }
                        }
                        if (CB_c4.Checked)
                        {
                            sort_duty_c4.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c4m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c4m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c0m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c4.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c4m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c4m = sort_2[i].c4m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c4m;
                                        if (sort_2[i].c0m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c4.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c4.Sort(sort_duty_c4_compare);

                            //LB_group.Text += "\nsort_duty_c4_d.Count = " + sort_duty_c4.Count;

                            count_temp = sort_duty_c4_2.Count;

                            sort_duty_c4_2.Clear();
                            sort_duty_c4_2.Add(sort_duty_c4[0]);

                            for (i = 1; i < sort_duty_c4.Count; i++)
                            {
                                if (sort_duty_c4[i].rate - sort_duty_c4[i - 1].rate > 1e-6)
                                    sort_duty_c4_2.Add(sort_duty_c4[i]);
                                else
                                    if (sort_duty_c4[i].red == false && sort_duty_c4[i - 1].red == true)
                                    {
                                        sort_duty_c4_2.Remove(sort_duty_c4_2.Last());
                                        sort_duty_c4_2.Add(sort_duty_c4[i]);
                                    }
                            }

                            CBB_c4_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c4_2.Count; i++)
                            {
                                if (sort_duty_c4_2[i].red)
                                    CBB_c4_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c4_2[i].rate).ToString("f3"));
                                else
                                    CBB_c4_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c4_2[i].rate).ToString("f3"));
                            }

                            CBB_c4_duty.SelectedIndex = SelectedIndex_c4;

                            if (sort_duty_c4_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c4_2.Count error");
                            }
                        }
                        if (CB_e02.Checked)
                        {
                            sort_duty_e02.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].e02m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.e02m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c0m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_e02.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].e02m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.e02m = sort_2[i].e02m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.e02m;
                                        if (sort_2[i].c0m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_e02.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_e02.Sort(sort_duty_e02_compare);

                            //LB_group.Text += "\nsort_duty_e02_d.Count = " + sort_duty_e02.Count;

                            count_temp = sort_duty_e02_2.Count;

                            sort_duty_e02_2.Clear();
                            sort_duty_e02_2.Add(sort_duty_e02[0]);

                            for (i = 1; i < sort_duty_e02.Count; i++)
                            {
                                if (sort_duty_e02[i].rate - sort_duty_e02[i - 1].rate > 1e-6)
                                    sort_duty_e02_2.Add(sort_duty_e02[i]);
                                else
                                    if (sort_duty_e02[i].red == false && sort_duty_e02[i - 1].red == true)
                                    {
                                        sort_duty_e02_2.Remove(sort_duty_e02_2.Last());
                                        sort_duty_e02_2.Add(sort_duty_e02[i]);
                                    }
                            }

                            CBB_e02_duty.Items.Clear();
                            for (i = 0; i < sort_duty_e02_2.Count; i++)
                            {
                                if (sort_duty_e02_2[i].red)
                                    CBB_e02_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_e02_2[i].rate).ToString("f3"));
                                else
                                    CBB_e02_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e02_2[i].rate).ToString("f3"));
                            }

                            CBB_e02_duty.SelectedIndex = SelectedIndex_e02;

                            if (sort_duty_e02_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_e02_2.Count error");
                            }
                        }
                    }
                    if (sort_duty_c0_2[CBB_c0_duty.SelectedIndex].red)
                    {
                        SelectedIndex_c0 = CBB_c0_duty.SelectedIndex;
                        sort_duty_c0_2[CBB_c0_duty.SelectedIndex].red = false;
                        CBB_c0_duty.Items.Clear();
                        for (i = 0; i < sort_duty_c0_2.Count; i++)
                        {
                            if (sort_duty_c0_2[i].red)
                                CBB_c0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                            else
                                CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                        }
                        CBB_c0_duty.SelectedIndex = SelectedIndex_c0;
                    }

                    c0_duty = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].rate * 100;
                    n = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].n;
                    m = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].m;
                    c0_m = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m;
                }
                else if (c012 == 1)
                {
                    if (CB_c0.Checked || CB_e0.Checked || CB_c3.Checked || CB_c4.Checked || CB_e02.Checked)
                    {
                        cm = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m;
                        cm /= GCD(sort_duty_c1_2[CBB_c1_duty.SelectedIndex].element, cm);
                        if (CB_c0.Checked)
                        {
                            sort_duty_c0.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c0m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c0m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c1m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c0.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c0m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c0m = sort_2[i].c0m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c0m;
                                        if (sort_2[i].c1m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c0.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c0.Sort(sort_duty_c0_compare);

                            //LB_group.Text += "\nsort_duty_c0_d.Count = " + sort_duty_c0.Count;

                            count_temp = sort_duty_c0_2.Count;

                            sort_duty_c0_2.Clear();
                            sort_duty_c0_2.Add(sort_duty_c0[0]);

                            for (i = 1; i < sort_duty_c0.Count; i++)
                            {
                                if (sort_duty_c0[i].rate - sort_duty_c0[i - 1].rate > 1e-6)
                                    sort_duty_c0_2.Add(sort_duty_c0[i]);
                                else
                                    if (sort_duty_c0[i].red == false && sort_duty_c0[i - 1].red == true)
                                    {
                                        sort_duty_c0_2.Remove(sort_duty_c0_2.Last());
                                        sort_duty_c0_2.Add(sort_duty_c0[i]);
                                    }
                            }

                            CBB_c0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c0_2.Count; i++)
                            {
                                if (sort_duty_c0_2[i].red)
                                    CBB_c0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                                else
                                    CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                            }

                            CBB_c0_duty.SelectedIndex = SelectedIndex_c0;

                            if (sort_duty_c0_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c0_2.Count error");
                            }
                        }
                        if (CB_e0.Checked)
                        {
                            sort_duty_e0.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].e0m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.e0m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c1m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_e0.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].e0m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.e0m = sort_2[i].e0m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.e0m;
                                        if (sort_2[i].c1m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_e0.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_e0.Sort(sort_duty_e0_compare);

                            //LB_group.Text += "\nsort_duty_e0_d.Count = " + sort_duty_e0.Count;

                            count_temp = sort_duty_e0_2.Count;

                            sort_duty_e0_2.Clear();
                            sort_duty_e0_2.Add(sort_duty_e0[0]);

                            for (i = 1; i < sort_duty_e0.Count; i++)
                            {
                                if (sort_duty_e0[i].rate - sort_duty_e0[i - 1].rate > 1e-6)
                                    sort_duty_e0_2.Add(sort_duty_e0[i]);
                                else
                                    if (sort_duty_e0[i].red == false && sort_duty_e0[i - 1].red == true)
                                    {
                                        sort_duty_e0_2.Remove(sort_duty_e0_2.Last());
                                        sort_duty_e0_2.Add(sort_duty_e0[i]);
                                    }
                            }

                            CBB_e0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_e0_2.Count; i++)
                            {
                                if (sort_duty_e0_2[i].red)
                                    CBB_e0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                                else
                                    CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                            }

                            CBB_e0_duty.SelectedIndex = SelectedIndex_e0;

                            if (sort_duty_e0_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_e0_2.Count error");
                            }
                        }
                        if (CB_c3.Checked)
                        {
                            sort_duty_c3.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c3m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c3m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c1m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c3.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c3m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c3m = sort_2[i].c3m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c3m;
                                        if (sort_2[i].c1m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c3.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c3.Sort(sort_duty_c3_compare);

                            //LB_group.Text += "\nsort_duty_c3_d.Count = " + sort_duty_c3.Count;

                            count_temp = sort_duty_c3_2.Count;

                            sort_duty_c3_2.Clear();
                            sort_duty_c3_2.Add(sort_duty_c3[0]);

                            for (i = 1; i < sort_duty_c3.Count; i++)
                            {
                                if (sort_duty_c3[i].rate - sort_duty_c3[i - 1].rate > 1e-6)
                                    sort_duty_c3_2.Add(sort_duty_c3[i]);
                                else
                                    if (sort_duty_c3[i].red == false && sort_duty_c3[i - 1].red == true)
                                    {
                                        sort_duty_c3_2.Remove(sort_duty_c3_2.Last());
                                        sort_duty_c3_2.Add(sort_duty_c3[i]);
                                    }
                            }

                            CBB_c3_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c3_2.Count; i++)
                            {
                                if (sort_duty_c3_2[i].red)
                                    CBB_c3_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c3_2[i].rate).ToString("f3"));
                                else
                                    CBB_c3_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c3_2[i].rate).ToString("f3"));
                            }

                            CBB_c3_duty.SelectedIndex = SelectedIndex_c3;

                            if (sort_duty_c3_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c3_2.Count error");
                            }
                        }
                        if (CB_c4.Checked)
                        {
                            sort_duty_c4.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c4m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c4m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c1m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c4.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c4m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c4m = sort_2[i].c4m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c4m;
                                        if (sort_2[i].c1m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c4.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c4.Sort(sort_duty_c4_compare);

                            //LB_group.Text += "\nsort_duty_c4_d.Count = " + sort_duty_c4.Count;

                            count_temp = sort_duty_c4_2.Count;

                            sort_duty_c4_2.Clear();
                            sort_duty_c4_2.Add(sort_duty_c4[0]);

                            for (i = 1; i < sort_duty_c4.Count; i++)
                            {
                                if (sort_duty_c4[i].rate - sort_duty_c4[i - 1].rate > 1e-6)
                                    sort_duty_c4_2.Add(sort_duty_c4[i]);
                                else
                                    if (sort_duty_c4[i].red == false && sort_duty_c4[i - 1].red == true)
                                    {
                                        sort_duty_c4_2.Remove(sort_duty_c4_2.Last());
                                        sort_duty_c4_2.Add(sort_duty_c4[i]);
                                    }
                            }

                            CBB_c4_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c4_2.Count; i++)
                            {
                                if (sort_duty_c4_2[i].red)
                                    CBB_c4_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c4_2[i].rate).ToString("f3"));
                                else
                                    CBB_c4_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c4_2[i].rate).ToString("f3"));
                            }

                            CBB_c4_duty.SelectedIndex = SelectedIndex_c4;

                            if (sort_duty_c4_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c4_2.Count error");
                            }
                        }
                        if (CB_e02.Checked)
                        {
                            sort_duty_e02.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].e02m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.e02m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c1m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_e02.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].e02m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.e02m = sort_2[i].e02m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.e02m;
                                        if (sort_2[i].c1m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_e02.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_e02.Sort(sort_duty_e02_compare);

                            //LB_group.Text += "\nsort_duty_e02_d.Count = " + sort_duty_e02.Count;

                            count_temp = sort_duty_e02_2.Count;

                            sort_duty_e02_2.Clear();
                            sort_duty_e02_2.Add(sort_duty_e02[0]);

                            for (i = 1; i < sort_duty_e02.Count; i++)
                            {
                                if (sort_duty_e02[i].rate - sort_duty_e02[i - 1].rate > 1e-6)
                                    sort_duty_e02_2.Add(sort_duty_e02[i]);
                                else
                                    if (sort_duty_e02[i].red == false && sort_duty_e02[i - 1].red == true)
                                    {
                                        sort_duty_e02_2.Remove(sort_duty_e02_2.Last());
                                        sort_duty_e02_2.Add(sort_duty_e02[i]);
                                    }
                            }

                            CBB_e02_duty.Items.Clear();
                            for (i = 0; i < sort_duty_e02_2.Count; i++)
                            {
                                if (sort_duty_e02_2[i].red)
                                    CBB_e02_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_e02_2[i].rate).ToString("f3"));
                                else
                                    CBB_e02_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e02_2[i].rate).ToString("f3"));
                            }

                            CBB_e02_duty.SelectedIndex = SelectedIndex_e02;

                            if (sort_duty_e02_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_e02_2.Count error");
                            }
                        }
                    }
                    if (sort_duty_c1_2[CBB_c1_duty.SelectedIndex].red)
                    {
                        SelectedIndex_c1 = CBB_c1_duty.SelectedIndex;
                        sort_duty_c1_2[CBB_c1_duty.SelectedIndex].red = false;
                        CBB_c1_duty.Items.Clear();
                        for (i = 0; i < sort_duty_c1_2.Count; i++)
                        {
                            if (sort_duty_c1_2[i].red)
                                CBB_c1_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                            else
                                CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                        }
                        CBB_c1_duty.SelectedIndex = SelectedIndex_c1;
                    }
                    c1_duty = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].rate * 100;
                    n = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].n;
                    m = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].m;
                    c1_m = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m;
                }
                else if (c012 == 2)
                {
                    if (CB_c0.Checked || CB_c1.Checked || CB_c3.Checked || CB_c4.Checked || CB_e02.Checked)
                    {
                        cm = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m;
                        cm /= GCD(sort_duty_e0_2[CBB_e0_duty.SelectedIndex].element, cm);
                        if (CB_c0.Checked)
                        {
                            sort_duty_c0.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c0m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c0m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].e0m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c0.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c0m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c0m = sort_2[i].c0m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c0m;
                                        if (sort_2[i].e0m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c0.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c0.Sort(sort_duty_c0_compare);

                            //LB_group.Text += "\nsort_duty_c0_d.Count = " + sort_duty_c0.Count;

                            count_temp = sort_duty_c0_2.Count;

                            sort_duty_c0_2.Clear();
                            sort_duty_c0_2.Add(sort_duty_c0[0]);

                            for (i = 1; i < sort_duty_c0.Count; i++)
                            {
                                if (sort_duty_c0[i].rate - sort_duty_c0[i - 1].rate > 1e-6)
                                    sort_duty_c0_2.Add(sort_duty_c0[i]);
                                else
                                    if (sort_duty_c0[i].red == false && sort_duty_c0[i - 1].red == true)
                                    {
                                        sort_duty_c0_2.Remove(sort_duty_c0_2.Last());
                                        sort_duty_c0_2.Add(sort_duty_c0[i]);
                                    }
                            }

                            CBB_c0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c0_2.Count; i++)
                            {
                                if (sort_duty_c0_2[i].red)
                                    CBB_c0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                                else
                                    CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                            }

                            CBB_c0_duty.SelectedIndex = SelectedIndex_c0;

                            if (sort_duty_c0_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c0_2.Count error");
                            }
                        }
                        if (CB_c1.Checked)
                        {
                            sort_duty_c1.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c1m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c1m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].e0m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c1.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c1m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c1m = sort_2[i].c1m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c1m;
                                        if (sort_2[i].e0m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c1.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c1.Sort(sort_duty_c1_compare);

                            //LB_group.Text += "\nsort_duty_c1_d.Count = " + sort_duty_c1.Count;

                            count_temp = sort_duty_c1_2.Count;

                            sort_duty_c1_2.Clear();
                            sort_duty_c1_2.Add(sort_duty_c1[0]);

                            for (i = 1; i < sort_duty_c1.Count; i++)
                            {
                                if (sort_duty_c1[i].rate - sort_duty_c1[i - 1].rate > 1e-6)
                                    sort_duty_c1_2.Add(sort_duty_c1[i]);
                                else
                                    if (sort_duty_c1[i].red == false && sort_duty_c1[i - 1].red == true)
                                    {
                                        sort_duty_c1_2.Remove(sort_duty_c1_2.Last());
                                        sort_duty_c1_2.Add(sort_duty_c1[i]);
                                    }
                            }

                            CBB_c1_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c1_2.Count; i++)
                            {
                                if (sort_duty_c1_2[i].red)
                                    CBB_c1_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                                else
                                    CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                            }

                            CBB_c1_duty.SelectedIndex = SelectedIndex_c1;

                            if (sort_duty_c1_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c1_2.Count error");
                            }
                        }
                        if (CB_c3.Checked)
                        {
                            sort_duty_c3.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c3m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c3m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].e0m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c3.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c3m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c3m = sort_2[i].c3m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c3m;
                                        if (sort_2[i].e0m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c3.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c3.Sort(sort_duty_c3_compare);

                            //LB_group.Text += "\nsort_duty_c3_d.Count = " + sort_duty_c3.Count;

                            count_temp = sort_duty_c3_2.Count;

                            sort_duty_c3_2.Clear();
                            sort_duty_c3_2.Add(sort_duty_c3[0]);

                            for (i = 1; i < sort_duty_c3.Count; i++)
                            {
                                if (sort_duty_c3[i].rate - sort_duty_c3[i - 1].rate > 1e-6)
                                    sort_duty_c3_2.Add(sort_duty_c3[i]);
                                else
                                    if (sort_duty_c3[i].red == false && sort_duty_c3[i - 1].red == true)
                                    {
                                        sort_duty_c3_2.Remove(sort_duty_c3_2.Last());
                                        sort_duty_c3_2.Add(sort_duty_c3[i]);
                                    }
                            }

                            CBB_c3_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c3_2.Count; i++)
                            {
                                if (sort_duty_c3_2[i].red)
                                    CBB_c3_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c3_2[i].rate).ToString("f3"));
                                else
                                    CBB_c3_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c3_2[i].rate).ToString("f3"));
                            }

                            CBB_c3_duty.SelectedIndex = SelectedIndex_c3;

                            if (sort_duty_c3_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c3_2.Count error");
                            }
                        }
                        if (CB_c4.Checked)
                        {
                            sort_duty_c4.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c4m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c4m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].e0m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c4.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c4m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c4m = sort_2[i].c4m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c4m;
                                        if (sort_2[i].e0m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c4.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c4.Sort(sort_duty_c4_compare);

                            //LB_group.Text += "\nsort_duty_c4_d.Count = " + sort_duty_c4.Count;

                            count_temp = sort_duty_c4_2.Count;

                            sort_duty_c4_2.Clear();
                            sort_duty_c4_2.Add(sort_duty_c4[0]);

                            for (i = 1; i < sort_duty_c4.Count; i++)
                            {
                                if (sort_duty_c4[i].rate - sort_duty_c4[i - 1].rate > 1e-6)
                                    sort_duty_c4_2.Add(sort_duty_c4[i]);
                                else
                                    if (sort_duty_c4[i].red == false && sort_duty_c4[i - 1].red == true)
                                    {
                                        sort_duty_c4_2.Remove(sort_duty_c4_2.Last());
                                        sort_duty_c4_2.Add(sort_duty_c4[i]);
                                    }
                            }

                            CBB_c4_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c4_2.Count; i++)
                            {
                                if (sort_duty_c4_2[i].red)
                                    CBB_c4_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c4_2[i].rate).ToString("f3"));
                                else
                                    CBB_c4_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c4_2[i].rate).ToString("f3"));
                            }

                            CBB_c4_duty.SelectedIndex = SelectedIndex_c4;

                            if (sort_duty_c4_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c4_2.Count error");
                            }
                        }
                        if (CB_e02.Checked)
                        {
                            sort_duty_e02.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].e02m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.e02m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].e0m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_e02.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].e02m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.e02m = sort_2[i].e02m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.e02m;
                                        if (sort_2[i].e0m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_e02.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_e02.Sort(sort_duty_e02_compare);

                            //LB_group.Text += "\nsort_duty_e02_d.Count = " + sort_duty_e02.Count;

                            count_temp = sort_duty_e02_2.Count;

                            sort_duty_e02_2.Clear();
                            sort_duty_e02_2.Add(sort_duty_e02[0]);

                            for (i = 1; i < sort_duty_e02.Count; i++)
                            {
                                if (sort_duty_e02[i].rate - sort_duty_e02[i - 1].rate > 1e-6)
                                    sort_duty_e02_2.Add(sort_duty_e02[i]);
                                else
                                    if (sort_duty_e02[i].red == false && sort_duty_e02[i - 1].red == true)
                                    {
                                        sort_duty_e02_2.Remove(sort_duty_e02_2.Last());
                                        sort_duty_e02_2.Add(sort_duty_e02[i]);
                                    }
                            }

                            CBB_e02_duty.Items.Clear();
                            for (i = 0; i < sort_duty_e02_2.Count; i++)
                            {
                                if (sort_duty_e02_2[i].red)
                                    CBB_e02_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_e02_2[i].rate).ToString("f3"));
                                else
                                    CBB_e02_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e02_2[i].rate).ToString("f3"));
                            }

                            CBB_e02_duty.SelectedIndex = SelectedIndex_e02;

                            if (sort_duty_e02_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_e02_2.Count error");
                            }
                        }
                    }
                    if (sort_duty_e0_2[CBB_e0_duty.SelectedIndex].red)
                    {
                        SelectedIndex_e0 = CBB_e0_duty.SelectedIndex;
                        sort_duty_e0_2[CBB_e0_duty.SelectedIndex].red = false;
                        CBB_e0_duty.Items.Clear();
                        for (i = 0; i < sort_duty_e0_2.Count; i++)
                        {
                            if (sort_duty_e0_2[i].red)
                                CBB_e0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                            else
                                CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                        }
                        CBB_e0_duty.SelectedIndex = SelectedIndex_e0;
                    }
                    e0_duty = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].rate * 100;
                    n = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].n;
                    m = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].m;
                    e0_m = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m;
                }
                else if (c012 == 3)
                {
                    if (CB_c0.Checked || CB_c1.Checked || CB_e0.Checked || CB_c4.Checked || CB_e02.Checked)
                    {
                        cm = sort_duty_c3_2[CBB_c3_duty.SelectedIndex].c3m;
                        cm /= GCD(sort_duty_c3_2[CBB_c3_duty.SelectedIndex].element, cm);
                        if (CB_c0.Checked)
                        {
                            sort_duty_c0.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c0m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c0m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c3m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c0.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c0m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c0m = sort_2[i].c0m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c0m;
                                        if (sort_2[i].c3m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c0.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c0.Sort(sort_duty_c0_compare);

                            //LB_group.Text += "\nsort_duty_c0_d.Count = " + sort_duty_c0.Count;

                            count_temp = sort_duty_c0_2.Count;

                            sort_duty_c0_2.Clear();
                            sort_duty_c0_2.Add(sort_duty_c0[0]);

                            for (i = 1; i < sort_duty_c0.Count; i++)
                            {
                                if (sort_duty_c0[i].rate - sort_duty_c0[i - 1].rate > 1e-6)
                                    sort_duty_c0_2.Add(sort_duty_c0[i]);
                                else
                                    if (sort_duty_c0[i].red == false && sort_duty_c0[i - 1].red == true)
                                    {
                                        sort_duty_c0_2.Remove(sort_duty_c0_2.Last());
                                        sort_duty_c0_2.Add(sort_duty_c0[i]);
                                    }
                            }

                            CBB_c0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c0_2.Count; i++)
                            {
                                if (sort_duty_c0_2[i].red)
                                    CBB_c0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                                else
                                    CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                            }

                            CBB_c0_duty.SelectedIndex = SelectedIndex_c0;

                            if (sort_duty_c0_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c0_2.Count error");
                            }
                        }
                        if (CB_c1.Checked)
                        {
                            sort_duty_c1.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c1m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c1m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c3m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c1.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c1m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c1m = sort_2[i].c1m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c1m;
                                        if (sort_2[i].c3m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c1.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c1.Sort(sort_duty_c1_compare);

                            //LB_group.Text += "\nsort_duty_c1_d.Count = " + sort_duty_c1.Count;

                            count_temp = sort_duty_c1_2.Count;

                            sort_duty_c1_2.Clear();
                            sort_duty_c1_2.Add(sort_duty_c1[0]);

                            for (i = 1; i < sort_duty_c1.Count; i++)
                            {
                                if (sort_duty_c1[i].rate - sort_duty_c1[i - 1].rate > 1e-6)
                                    sort_duty_c1_2.Add(sort_duty_c1[i]);
                                else
                                    if (sort_duty_c1[i].red == false && sort_duty_c1[i - 1].red == true)
                                    {
                                        sort_duty_c1_2.Remove(sort_duty_c1_2.Last());
                                        sort_duty_c1_2.Add(sort_duty_c1[i]);
                                    }
                            }

                            CBB_c1_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c1_2.Count; i++)
                            {
                                if (sort_duty_c1_2[i].red)
                                    CBB_c1_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                                else
                                    CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                            }

                            CBB_c1_duty.SelectedIndex = SelectedIndex_c1;

                            if (sort_duty_c1_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c1_2.Count error");
                            }
                        }
                        if (CB_e0.Checked)
                        {
                            sort_duty_e0.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].e0m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.e0m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c3m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_e0.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].e0m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.e0m = sort_2[i].e0m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.e0m;
                                        if (sort_2[i].c3m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_e0.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_e0.Sort(sort_duty_e0_compare);

                            //LB_group.Text += "\nsort_duty_e0_d.Count = " + sort_duty_e0.Count;

                            count_temp = sort_duty_e0_2.Count;

                            sort_duty_e0_2.Clear();
                            sort_duty_e0_2.Add(sort_duty_e0[0]);

                            for (i = 1; i < sort_duty_e0.Count; i++)
                            {
                                if (sort_duty_e0[i].rate - sort_duty_e0[i - 1].rate > 1e-6)
                                    sort_duty_e0_2.Add(sort_duty_e0[i]);
                                else
                                    if (sort_duty_e0[i].red == false && sort_duty_e0[i - 1].red == true)
                                    {
                                        sort_duty_e0_2.Remove(sort_duty_e0_2.Last());
                                        sort_duty_e0_2.Add(sort_duty_e0[i]);
                                    }
                            }

                            CBB_e0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_e0_2.Count; i++)
                            {
                                if (sort_duty_e0_2[i].red)
                                    CBB_e0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                                else
                                    CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                            }

                            CBB_e0_duty.SelectedIndex = SelectedIndex_e0;

                            if (sort_duty_e0_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_e0_2.Count error");
                            }
                        }
                        if (CB_c4.Checked)
                        {
                            sort_duty_c4.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c4m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c4m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c3m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c4.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c4m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c4m = sort_2[i].c4m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c4m;
                                        if (sort_2[i].c3m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c4.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c4.Sort(sort_duty_c4_compare);

                            //LB_group.Text += "\nsort_duty_c4_d.Count = " + sort_duty_c4.Count;

                            count_temp = sort_duty_c4_2.Count;

                            sort_duty_c4_2.Clear();
                            sort_duty_c4_2.Add(sort_duty_c4[0]);

                            for (i = 1; i < sort_duty_c4.Count; i++)
                            {
                                if (sort_duty_c4[i].rate - sort_duty_c4[i - 1].rate > 1e-6)
                                    sort_duty_c4_2.Add(sort_duty_c4[i]);
                                else
                                    if (sort_duty_c4[i].red == false && sort_duty_c4[i - 1].red == true)
                                    {
                                        sort_duty_c4_2.Remove(sort_duty_c4_2.Last());
                                        sort_duty_c4_2.Add(sort_duty_c4[i]);
                                    }
                            }

                            CBB_c4_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c4_2.Count; i++)
                            {
                                if (sort_duty_c4_2[i].red)
                                    CBB_c4_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c4_2[i].rate).ToString("f3"));
                                else
                                    CBB_c4_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c4_2[i].rate).ToString("f3"));
                            }

                            CBB_c4_duty.SelectedIndex = SelectedIndex_c4;

                            if (sort_duty_c4_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c4_2.Count error");
                            }
                        }
                        if (CB_e02.Checked)
                        {
                            sort_duty_e02.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].e02m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.e02m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c3m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_e02.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].e02m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.e02m = sort_2[i].e02m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.e02m;
                                        if (sort_2[i].c3m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_e02.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_e02.Sort(sort_duty_e02_compare);

                            //LB_group.Text += "\nsort_duty_e02_d.Count = " + sort_duty_e02.Count;

                            count_temp = sort_duty_e02_2.Count;

                            sort_duty_e02_2.Clear();
                            sort_duty_e02_2.Add(sort_duty_e02[0]);

                            for (i = 1; i < sort_duty_e02.Count; i++)
                            {
                                if (sort_duty_e02[i].rate - sort_duty_e02[i - 1].rate > 1e-6)
                                    sort_duty_e02_2.Add(sort_duty_e02[i]);
                                else
                                    if (sort_duty_e02[i].red == false && sort_duty_e02[i - 1].red == true)
                                    {
                                        sort_duty_e02_2.Remove(sort_duty_e02_2.Last());
                                        sort_duty_e02_2.Add(sort_duty_e02[i]);
                                    }
                            }

                            CBB_e02_duty.Items.Clear();
                            for (i = 0; i < sort_duty_e02_2.Count; i++)
                            {
                                if (sort_duty_e02_2[i].red)
                                    CBB_e02_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_e02_2[i].rate).ToString("f3"));
                                else
                                    CBB_e02_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e02_2[i].rate).ToString("f3"));
                            }

                            CBB_e02_duty.SelectedIndex = SelectedIndex_e02;

                            if (sort_duty_e02_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_e02_2.Count error");
                            }
                        }
                    }
                    if (sort_duty_c3_2[CBB_c3_duty.SelectedIndex].red)
                    {
                        SelectedIndex_c3 = CBB_c3_duty.SelectedIndex;
                        sort_duty_c3_2[CBB_c3_duty.SelectedIndex].red = false;
                        CBB_c3_duty.Items.Clear();
                        for (i = 0; i < sort_duty_c3_2.Count; i++)
                        {
                            if (sort_duty_c3_2[i].red)
                                CBB_c3_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c3_2[i].rate).ToString("f3"));
                            else
                                CBB_c3_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c3_2[i].rate).ToString("f3"));
                        }
                        CBB_c3_duty.SelectedIndex = SelectedIndex_c3;
                    }
                    c3_duty = sort_duty_c3_2[CBB_c3_duty.SelectedIndex].rate * 100;
                    n = sort_duty_c3_2[CBB_c3_duty.SelectedIndex].n;
                    m = sort_duty_c3_2[CBB_c3_duty.SelectedIndex].m;
                    c3_m = sort_duty_c3_2[CBB_c3_duty.SelectedIndex].c3m;
                }
                else if (c012 == 4)
                {
                    if (CB_c0.Checked || CB_c1.Checked || CB_e0.Checked || CB_c3.Checked || CB_e02.Checked)
                    {
                        cm = sort_duty_c4_2[CBB_c4_duty.SelectedIndex].c4m;
                        cm /= GCD(sort_duty_c4_2[CBB_c4_duty.SelectedIndex].element, cm);
                        if (CB_c0.Checked)
                        {
                            sort_duty_c0.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c0m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c0m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c4m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c0.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c0m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c0m = sort_2[i].c0m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c0m;
                                        if (sort_2[i].c4m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c0.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c0.Sort(sort_duty_c0_compare);

                            //LB_group.Text += "\nsort_duty_c0_d.Count = " + sort_duty_c0.Count;

                            count_temp = sort_duty_c0_2.Count;

                            sort_duty_c0_2.Clear();
                            sort_duty_c0_2.Add(sort_duty_c0[0]);

                            for (i = 1; i < sort_duty_c0.Count; i++)
                            {
                                if (sort_duty_c0[i].rate - sort_duty_c0[i - 1].rate > 1e-6)
                                    sort_duty_c0_2.Add(sort_duty_c0[i]);
                                else
                                    if (sort_duty_c0[i].red == false && sort_duty_c0[i - 1].red == true)
                                    {
                                        sort_duty_c0_2.Remove(sort_duty_c0_2.Last());
                                        sort_duty_c0_2.Add(sort_duty_c0[i]);
                                    }
                            }

                            CBB_c0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c0_2.Count; i++)
                            {
                                if (sort_duty_c0_2[i].red)
                                    CBB_c0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                                else
                                    CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                            }

                            CBB_c0_duty.SelectedIndex = SelectedIndex_c0;

                            if (sort_duty_c0_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c0_2.Count error");
                            }
                        }
                        if (CB_c1.Checked)
                        {
                            sort_duty_c1.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c1m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c1m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c4m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c1.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c1m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c1m = sort_2[i].c1m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c1m;
                                        if (sort_2[i].c4m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c1.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c1.Sort(sort_duty_c1_compare);

                            //LB_group.Text += "\nsort_duty_c1_d.Count = " + sort_duty_c1.Count;

                            count_temp = sort_duty_c1_2.Count;

                            sort_duty_c1_2.Clear();
                            sort_duty_c1_2.Add(sort_duty_c1[0]);

                            for (i = 1; i < sort_duty_c1.Count; i++)
                            {
                                if (sort_duty_c1[i].rate - sort_duty_c1[i - 1].rate > 1e-6)
                                    sort_duty_c1_2.Add(sort_duty_c1[i]);
                                else
                                    if (sort_duty_c1[i].red == false && sort_duty_c1[i - 1].red == true)
                                    {
                                        sort_duty_c1_2.Remove(sort_duty_c1_2.Last());
                                        sort_duty_c1_2.Add(sort_duty_c1[i]);
                                    }
                            }

                            CBB_c1_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c1_2.Count; i++)
                            {
                                if (sort_duty_c1_2[i].red)
                                    CBB_c1_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                                else
                                    CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                            }

                            CBB_c1_duty.SelectedIndex = SelectedIndex_c1;

                            if (sort_duty_c1_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c1_2.Count error");
                            }
                        }
                        if (CB_e0.Checked)
                        {
                            sort_duty_e0.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].e0m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.e0m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c4m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_e0.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].e0m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.e0m = sort_2[i].e0m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.e0m;
                                        if (sort_2[i].c4m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_e0.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_e0.Sort(sort_duty_e0_compare);

                            //LB_group.Text += "\nsort_duty_e0_d.Count = " + sort_duty_e0.Count;

                            count_temp = sort_duty_e0_2.Count;

                            sort_duty_e0_2.Clear();
                            sort_duty_e0_2.Add(sort_duty_e0[0]);

                            for (i = 1; i < sort_duty_e0.Count; i++)
                            {
                                if (sort_duty_e0[i].rate - sort_duty_e0[i - 1].rate > 1e-6)
                                    sort_duty_e0_2.Add(sort_duty_e0[i]);
                                else
                                    if (sort_duty_e0[i].red == false && sort_duty_e0[i - 1].red == true)
                                    {
                                        sort_duty_e0_2.Remove(sort_duty_e0_2.Last());
                                        sort_duty_e0_2.Add(sort_duty_e0[i]);
                                    }
                            }

                            CBB_e0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_e0_2.Count; i++)
                            {
                                if (sort_duty_e0_2[i].red)
                                    CBB_e0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                                else
                                    CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                            }

                            CBB_e0_duty.SelectedIndex = SelectedIndex_e0;

                            if (sort_duty_e0_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_e0_2.Count error");
                            }
                        }
                        if (CB_c3.Checked)
                        {
                            sort_duty_c3.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c3m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c3m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c4m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c3.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c3m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c3m = sort_2[i].c3m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c3m;
                                        if (sort_2[i].c4m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c3.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c3.Sort(sort_duty_c3_compare);

                            //LB_group.Text += "\nsort_duty_c3_d.Count = " + sort_duty_c3.Count;

                            count_temp = sort_duty_c3_2.Count;

                            sort_duty_c3_2.Clear();
                            sort_duty_c3_2.Add(sort_duty_c3[0]);

                            for (i = 1; i < sort_duty_c3.Count; i++)
                            {
                                if (sort_duty_c3[i].rate - sort_duty_c3[i - 1].rate > 1e-6)
                                    sort_duty_c3_2.Add(sort_duty_c3[i]);
                                else
                                    if (sort_duty_c3[i].red == false && sort_duty_c3[i - 1].red == true)
                                    {
                                        sort_duty_c3_2.Remove(sort_duty_c3_2.Last());
                                        sort_duty_c3_2.Add(sort_duty_c3[i]);
                                    }
                            }

                            CBB_c3_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c3_2.Count; i++)
                            {
                                if (sort_duty_c3_2[i].red)
                                    CBB_c3_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c3_2[i].rate).ToString("f3"));
                                else
                                    CBB_c3_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c3_2[i].rate).ToString("f3"));
                            }

                            CBB_c3_duty.SelectedIndex = SelectedIndex_c3;

                            if (sort_duty_c3_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c3_2.Count error");
                            }
                        }
                        if (CB_e02.Checked)
                        {
                            sort_duty_e02.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].e02m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.e02m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].c4m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_e02.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].e02m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.e02m = sort_2[i].e02m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.e02m;
                                        if (sort_2[i].c4m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_e02.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_e02.Sort(sort_duty_e02_compare);

                            //LB_group.Text += "\nsort_duty_e02_d.Count = " + sort_duty_e02.Count;

                            count_temp = sort_duty_e02_2.Count;

                            sort_duty_e02_2.Clear();
                            sort_duty_e02_2.Add(sort_duty_e02[0]);

                            for (i = 1; i < sort_duty_e02.Count; i++)
                            {
                                if (sort_duty_e02[i].rate - sort_duty_e02[i - 1].rate > 1e-6)
                                    sort_duty_e02_2.Add(sort_duty_e02[i]);
                                else
                                    if (sort_duty_e02[i].red == false && sort_duty_e02[i - 1].red == true)
                                    {
                                        sort_duty_e02_2.Remove(sort_duty_e02_2.Last());
                                        sort_duty_e02_2.Add(sort_duty_e02[i]);
                                    }
                            }

                            CBB_e02_duty.Items.Clear();
                            for (i = 0; i < sort_duty_e02_2.Count; i++)
                            {
                                if (sort_duty_e02_2[i].red)
                                    CBB_e02_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_e02_2[i].rate).ToString("f3"));
                                else
                                    CBB_e02_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e02_2[i].rate).ToString("f3"));
                            }

                            CBB_e02_duty.SelectedIndex = SelectedIndex_e02;

                            if (sort_duty_e02_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_e02_2.Count error");
                            }
                        }
                    }
                    if (sort_duty_c4_2[CBB_c4_duty.SelectedIndex].red)
                    {
                        SelectedIndex_c4 = CBB_c4_duty.SelectedIndex;
                        sort_duty_c4_2[CBB_c4_duty.SelectedIndex].red = false;
                        CBB_c4_duty.Items.Clear();
                        for (i = 0; i < sort_duty_c4_2.Count; i++)
                        {
                            if (sort_duty_c4_2[i].red)
                                CBB_c4_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c4_2[i].rate).ToString("f3"));
                            else
                                CBB_c4_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c4_2[i].rate).ToString("f3"));
                        }
                        CBB_c4_duty.SelectedIndex = SelectedIndex_c4;
                    }
                    c4_duty = sort_duty_c4_2[CBB_c4_duty.SelectedIndex].rate * 100;
                    n = sort_duty_c4_2[CBB_c4_duty.SelectedIndex].n;
                    m = sort_duty_c4_2[CBB_c4_duty.SelectedIndex].m;
                    c4_m = sort_duty_c4_2[CBB_c4_duty.SelectedIndex].c4m;
                }
                else if (c012 == 5)
                {
                    if (CB_c0.Checked || CB_c1.Checked || CB_e0.Checked || CB_c3.Checked || CB_c4.Checked)
                    {
                        cm = sort_duty_e02_2[CBB_e02_duty.SelectedIndex].e02m;
                        cm /= GCD(sort_duty_e02_2[CBB_e02_duty.SelectedIndex].element, cm);
                        if (CB_c0.Checked)
                        {
                            sort_duty_c0.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c0m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c0m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].e02m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c0.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c0m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c0m = sort_2[i].c0m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c0m;
                                        if (sort_2[i].e02m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c0.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c0.Sort(sort_duty_c0_compare);

                            //LB_group.Text += "\nsort_duty_c0_d.Count = " + sort_duty_c0.Count;

                            count_temp = sort_duty_c0_2.Count;

                            sort_duty_c0_2.Clear();
                            sort_duty_c0_2.Add(sort_duty_c0[0]);

                            for (i = 1; i < sort_duty_c0.Count; i++)
                            {
                                if (sort_duty_c0[i].rate - sort_duty_c0[i - 1].rate > 1e-6)
                                    sort_duty_c0_2.Add(sort_duty_c0[i]);
                                else
                                    if (sort_duty_c0[i].red == false && sort_duty_c0[i - 1].red == true)
                                    {
                                        sort_duty_c0_2.Remove(sort_duty_c0_2.Last());
                                        sort_duty_c0_2.Add(sort_duty_c0[i]);
                                    }
                            }

                            CBB_c0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c0_2.Count; i++)
                            {
                                if (sort_duty_c0_2[i].red)
                                    CBB_c0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                                else
                                    CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                            }

                            CBB_c0_duty.SelectedIndex = SelectedIndex_c0;

                            if (sort_duty_c0_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c0_2.Count error");
                            }
                        }
                        if (CB_c1.Checked)
                        {
                            sort_duty_c1.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c1m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c1m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].e02m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c1.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c1m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c1m = sort_2[i].c1m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c1m;
                                        if (sort_2[i].e02m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c1.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c1.Sort(sort_duty_c1_compare);

                            //LB_group.Text += "\nsort_duty_c1_d.Count = " + sort_duty_c1.Count;

                            count_temp = sort_duty_c1_2.Count;

                            sort_duty_c1_2.Clear();
                            sort_duty_c1_2.Add(sort_duty_c1[0]);

                            for (i = 1; i < sort_duty_c1.Count; i++)
                            {
                                if (sort_duty_c1[i].rate - sort_duty_c1[i - 1].rate > 1e-6)
                                    sort_duty_c1_2.Add(sort_duty_c1[i]);
                                else
                                    if (sort_duty_c1[i].red == false && sort_duty_c1[i - 1].red == true)
                                    {
                                        sort_duty_c1_2.Remove(sort_duty_c1_2.Last());
                                        sort_duty_c1_2.Add(sort_duty_c1[i]);
                                    }
                            }

                            CBB_c1_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c1_2.Count; i++)
                            {
                                if (sort_duty_c1_2[i].red)
                                    CBB_c1_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                                else
                                    CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                            }

                            CBB_c1_duty.SelectedIndex = SelectedIndex_c1;

                            if (sort_duty_c1_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c1_2.Count error");
                            }
                        }
                        if (CB_e0.Checked)
                        {
                            sort_duty_e0.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].e0m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.e0m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].e02m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_e0.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].e0m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.e0m = sort_2[i].e0m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.e0m;
                                        if (sort_2[i].e02m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_e0.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_e0.Sort(sort_duty_e0_compare);

                            //LB_group.Text += "\nsort_duty_e0_d.Count = " + sort_duty_e0.Count;

                            count_temp = sort_duty_e0_2.Count;

                            sort_duty_e0_2.Clear();
                            sort_duty_e0_2.Add(sort_duty_e0[0]);

                            for (i = 1; i < sort_duty_e0.Count; i++)
                            {
                                if (sort_duty_e0[i].rate - sort_duty_e0[i - 1].rate > 1e-6)
                                    sort_duty_e0_2.Add(sort_duty_e0[i]);
                                else
                                    if (sort_duty_e0[i].red == false && sort_duty_e0[i - 1].red == true)
                                    {
                                        sort_duty_e0_2.Remove(sort_duty_e0_2.Last());
                                        sort_duty_e0_2.Add(sort_duty_e0[i]);
                                    }
                            }

                            CBB_e0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_e0_2.Count; i++)
                            {
                                if (sort_duty_e0_2[i].red)
                                    CBB_e0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                                else
                                    CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                            }

                            CBB_e0_duty.SelectedIndex = SelectedIndex_e0;

                            if (sort_duty_e0_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_e0_2.Count error");
                            }
                        }
                        if (CB_c3.Checked)
                        {
                            sort_duty_c3.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c3m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c3m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].e02m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c3.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c3m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c3m = sort_2[i].c3m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c3m;
                                        if (sort_2[i].e02m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c3.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c3.Sort(sort_duty_c3_compare);

                            //LB_group.Text += "\nsort_duty_c3_d.Count = " + sort_duty_c3.Count;

                            count_temp = sort_duty_c3_2.Count;

                            sort_duty_c3_2.Clear();
                            sort_duty_c3_2.Add(sort_duty_c3[0]);

                            for (i = 1; i < sort_duty_c3.Count; i++)
                            {
                                if (sort_duty_c3[i].rate - sort_duty_c3[i - 1].rate > 1e-6)
                                    sort_duty_c3_2.Add(sort_duty_c3[i]);
                                else
                                    if (sort_duty_c3[i].red == false && sort_duty_c3[i - 1].red == true)
                                    {
                                        sort_duty_c3_2.Remove(sort_duty_c3_2.Last());
                                        sort_duty_c3_2.Add(sort_duty_c3[i]);
                                    }
                            }

                            CBB_c3_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c3_2.Count; i++)
                            {
                                if (sort_duty_c3_2[i].red)
                                    CBB_c3_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c3_2[i].rate).ToString("f3"));
                                else
                                    CBB_c3_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c3_2[i].rate).ToString("f3"));
                            }

                            CBB_c3_duty.SelectedIndex = SelectedIndex_c3;

                            if (sort_duty_c3_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c3_2.Count error");
                            }
                        }
                        if (CB_c4.Checked)
                        {
                            sort_duty_c4.Clear();
                            for (i = 0; i < sort_2_count; i++)
                            {
                                if (sort_2[i].c4m == 1)
                                {
                                    duty_temp = new duty_index();
                                    duty_temp.m = sort_2[i].m;
                                    duty_temp.n = sort_2[i].n;
                                    duty_temp.c4m = 1;
                                    duty_temp.element = 1;
                                    duty_temp.rate = 0.5;
                                    if (sort_2[i].e02m % cm == 0)
                                        duty_temp.red = false;
                                    else
                                        duty_temp.red = true;
                                    sort_duty_c4.Add(duty_temp);
                                }
                                else
                                {
                                    for (j = 1; j < sort_2[i].c4m; j++)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2[i].m;
                                        duty_temp.n = sort_2[i].n;
                                        duty_temp.c4m = sort_2[i].c4m;
                                        duty_temp.element = j;
                                        duty_temp.rate = (double)j / duty_temp.c4m;
                                        if (sort_2[i].e02m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c4.Add(duty_temp);
                                    }
                                }
                            }

                            sort_duty_c4.Sort(sort_duty_c4_compare);

                            //LB_group.Text += "\nsort_duty_c4_d.Count = " + sort_duty_c4.Count;

                            count_temp = sort_duty_c4_2.Count;

                            sort_duty_c4_2.Clear();
                            sort_duty_c4_2.Add(sort_duty_c4[0]);

                            for (i = 1; i < sort_duty_c4.Count; i++)
                            {
                                if (sort_duty_c4[i].rate - sort_duty_c4[i - 1].rate > 1e-6)
                                    sort_duty_c4_2.Add(sort_duty_c4[i]);
                                else
                                    if (sort_duty_c4[i].red == false && sort_duty_c4[i - 1].red == true)
                                    {
                                        sort_duty_c4_2.Remove(sort_duty_c4_2.Last());
                                        sort_duty_c4_2.Add(sort_duty_c4[i]);
                                    }
                            }

                            CBB_c4_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c4_2.Count; i++)
                            {
                                if (sort_duty_c4_2[i].red)
                                    CBB_c4_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c4_2[i].rate).ToString("f3"));
                                else
                                    CBB_c4_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c4_2[i].rate).ToString("f3"));
                            }

                            CBB_c4_duty.SelectedIndex = SelectedIndex_c4;

                            if (sort_duty_c4_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c4_2.Count error");
                            }
                        }
                    }
                    if (sort_duty_e02_2[CBB_e02_duty.SelectedIndex].red)
                    {
                        SelectedIndex_e02 = CBB_e02_duty.SelectedIndex;
                        sort_duty_e02_2[CBB_e02_duty.SelectedIndex].red = false;
                        CBB_e02_duty.Items.Clear();
                        for (i = 0; i < sort_duty_e02_2.Count; i++)
                        {
                            if (sort_duty_e02_2[i].red)
                                CBB_e02_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_e02_2[i].rate).ToString("f3"));
                            else
                                CBB_e02_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e02_2[i].rate).ToString("f3"));
                        }
                        CBB_e02_duty.SelectedIndex = SelectedIndex_e02;
                    }
                    e02_duty = sort_duty_e02_2[CBB_e02_duty.SelectedIndex].rate * 100;
                    n = sort_duty_e02_2[CBB_e02_duty.SelectedIndex].n;
                    m = sort_duty_e02_2[CBB_e02_duty.SelectedIndex].m;
                    e02_m = sort_duty_e02_2[CBB_e02_duty.SelectedIndex].e02m;
                }
                else
                {
                    MessageBox.Show("PTE operation_mode error");
                    LB_message_output.Text = "PTE operation_mode error";
                }
            }
            else
            {
                if (RB_mode0.Checked)//无补偿
                {
                    if (c012 == 0)//c0
                    {
                        if (CB_c1.Checked || CB_e0.Checked)
                        {
                            cm = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m;
                            cm /= GCD(sort_duty_c0_2[CBB_c0_duty.SelectedIndex].element, cm);
                            if (CB_c1.Checked)
                            {
                                sort_duty_c1.Clear();
                                for (i = 0; i < sort_2_count; i++)
                                {
                                    if (sort_2F[i].c1m == 1)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2F[i].m;
                                        duty_temp.n = sort_2F[i].n;
                                        duty_temp.c1m = 1;
                                        duty_temp.element = 1;
                                        duty_temp.rate = 0.5;
                                        if (sort_2F[i].c0m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c1.Add(duty_temp);
                                    }
                                    else
                                    {
                                        for (j = 1; j < sort_2F[i].c1m; j++)
                                        {
                                            duty_temp = new duty_index();
                                            duty_temp.m = sort_2F[i].m;
                                            duty_temp.n = sort_2F[i].n;
                                            duty_temp.c1m = sort_2F[i].c1m;
                                            duty_temp.element = j;
                                            duty_temp.rate = (double)j / duty_temp.c1m;
                                            if (sort_2F[i].c0m % cm == 0)
                                                duty_temp.red = false;
                                            else
                                                duty_temp.red = true;
                                            sort_duty_c1.Add(duty_temp);
                                        }
                                    }
                                }

                                sort_duty_c1.Sort(sort_duty_c1_compare);

                                //LB_group.Text += "\nsort_duty_c1_d.Count = " + sort_duty_c1.Count;

                                count_temp = sort_duty_c1_2.Count;

                                sort_duty_c1_2.Clear();
                                sort_duty_c1_2.Add(sort_duty_c1[0]);

                                for (i = 1; i < sort_duty_c1.Count; i++)
                                {
                                    if (sort_duty_c1[i].rate - sort_duty_c1[i - 1].rate > 1e-6)
                                        sort_duty_c1_2.Add(sort_duty_c1[i]);
                                    else
                                        if (sort_duty_c1[i].red == false && sort_duty_c1[i - 1].red == true)
                                        {
                                            sort_duty_c1_2.Remove(sort_duty_c1_2.Last());
                                            sort_duty_c1_2.Add(sort_duty_c1[i]);
                                        }
                                }

                                CBB_c1_duty.Items.Clear();
                                for (i = 0; i < sort_duty_c1_2.Count; i++)
                                {
                                    if (sort_duty_c1_2[i].red)
                                        CBB_c1_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                                    else
                                        CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                                }

                                CBB_c1_duty.SelectedIndex = SelectedIndex_c1;

                                if (sort_duty_c1_2.Count != count_temp)
                                {
                                    MessageBox.Show("sort_duty_c1_2.Count error");
                                }
                            }
                            if (CB_e0.Checked)
                            {
                                sort_duty_e0.Clear();
                                for (i = 0; i < sort_2_count; i++)
                                {
                                    if (sort_2F[i].e0m == 1)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2F[i].m;
                                        duty_temp.n = sort_2F[i].n;
                                        duty_temp.e0m = 1;
                                        duty_temp.element = 1;
                                        duty_temp.rate = 0.5;
                                        if (sort_2F[i].c0m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_e0.Add(duty_temp);
                                    }
                                    else
                                    {
                                        for (j = 1; j < sort_2F[i].e0m; j++)
                                        {
                                            duty_temp = new duty_index();
                                            duty_temp.m = sort_2F[i].m;
                                            duty_temp.n = sort_2F[i].n;
                                            duty_temp.e0m = sort_2F[i].e0m;
                                            duty_temp.element = j;
                                            duty_temp.rate = (double)j / duty_temp.e0m;
                                            if (sort_2F[i].c0m % cm == 0)
                                                duty_temp.red = false;
                                            else
                                                duty_temp.red = true;
                                            sort_duty_e0.Add(duty_temp);
                                        }
                                    }
                                }

                                sort_duty_e0.Sort(sort_duty_e0_compare);

                                //LB_group.Text += "\nsort_duty_e0_d.Count = " + sort_duty_e0.Count;

                                count_temp = sort_duty_e0_2.Count;

                                sort_duty_e0_2.Clear();
                                sort_duty_e0_2.Add(sort_duty_e0[0]);

                                for (i = 1; i < sort_duty_e0.Count; i++)
                                {
                                    if (sort_duty_e0[i].rate - sort_duty_e0[i - 1].rate > 1e-6)
                                        sort_duty_e0_2.Add(sort_duty_e0[i]);
                                    else
                                        if (sort_duty_e0[i].red == false && sort_duty_e0[i - 1].red == true)
                                        {
                                            sort_duty_e0_2.Remove(sort_duty_e0_2.Last());
                                            sort_duty_e0_2.Add(sort_duty_e0[i]);
                                        }
                                }

                                CBB_e0_duty.Items.Clear();
                                for (i = 0; i < sort_duty_e0_2.Count; i++)
                                {
                                    if (sort_duty_e0_2[i].red)
                                        CBB_e0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                                    else
                                        CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                                }

                                CBB_e0_duty.SelectedIndex = SelectedIndex_e0;

                                if (sort_duty_e0_2.Count != count_temp)
                                {
                                    MessageBox.Show("sort_duty_e0_2.Count error");
                                }
                            }
                        }
                        if (sort_duty_c0_2[CBB_c0_duty.SelectedIndex].red)
                        {
                            SelectedIndex_c0 = CBB_c0_duty.SelectedIndex;
                            sort_duty_c0_2[CBB_c0_duty.SelectedIndex].red = false;
                            CBB_c0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c0_2.Count; i++)
                            {
                                if (sort_duty_c0_2[i].red)
                                    CBB_c0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                                else
                                    CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                            }
                            CBB_c0_duty.SelectedIndex = SelectedIndex_c0;
                        }

                        c0_duty = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].rate * 100;
                        n = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].n;
                        m = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].m;
                        c0_m = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m;
                    }
                    else if (c012 == 1)//c1
                    {
                        if (CB_c0.Checked || CB_e0.Checked)
                        {
                            cm = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m;
                            cm /= GCD(sort_duty_c1_2[CBB_c1_duty.SelectedIndex].element, cm);
                            if (CB_c0.Checked)
                            {
                                sort_duty_c0.Clear();
                                for (i = 0; i < sort_2_count; i++)
                                {
                                    if (sort_2F[i].c0m == 1)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2F[i].m;
                                        duty_temp.n = sort_2F[i].n;
                                        duty_temp.c0m = 1;
                                        duty_temp.element = 1;
                                        duty_temp.rate = 0.5;
                                        if (sort_2F[i].c1m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c0.Add(duty_temp);
                                    }
                                    else
                                    {
                                        for (j = 1; j < sort_2F[i].c0m; j++)
                                        {
                                            duty_temp = new duty_index();
                                            duty_temp.m = sort_2F[i].m;
                                            duty_temp.n = sort_2F[i].n;
                                            duty_temp.c0m = sort_2F[i].c0m;
                                            duty_temp.element = j;
                                            duty_temp.rate = (double)j / duty_temp.c0m;
                                            if (sort_2F[i].c1m % cm == 0)
                                                duty_temp.red = false;
                                            else
                                                duty_temp.red = true;
                                            sort_duty_c0.Add(duty_temp);
                                        }
                                    }
                                }

                                sort_duty_c0.Sort(sort_duty_c0_compare);

                                //LB_group.Text += "\nsort_duty_c0_d.Count = " + sort_duty_c0.Count;

                                count_temp = sort_duty_c0_2.Count;

                                sort_duty_c0_2.Clear();
                                sort_duty_c0_2.Add(sort_duty_c0[0]);

                                for (i = 1; i < sort_duty_c0.Count; i++)
                                {
                                    if (sort_duty_c0[i].rate - sort_duty_c0[i - 1].rate > 1e-6)
                                        sort_duty_c0_2.Add(sort_duty_c0[i]);
                                    else
                                        if (sort_duty_c0[i].red == false && sort_duty_c0[i - 1].red == true)
                                        {
                                            sort_duty_c0_2.Remove(sort_duty_c0_2.Last());
                                            sort_duty_c0_2.Add(sort_duty_c0[i]);
                                        }
                                }

                                CBB_c0_duty.Items.Clear();
                                for (i = 0; i < sort_duty_c0_2.Count; i++)
                                {
                                    if (sort_duty_c0_2[i].red)
                                        CBB_c0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                                    else
                                        CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                                }

                                CBB_c0_duty.SelectedIndex = SelectedIndex_c0;

                                if (sort_duty_c0_2.Count != count_temp)
                                {
                                    MessageBox.Show("sort_duty_c0_2.Count error");
                                }
                            }
                            if (CB_e0.Checked)
                            {
                                sort_duty_e0.Clear();
                                for (i = 0; i < sort_2_count; i++)
                                {
                                    if (sort_2F[i].e0m == 1)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2F[i].m;
                                        duty_temp.n = sort_2F[i].n;
                                        duty_temp.e0m = 1;
                                        duty_temp.element = 1;
                                        duty_temp.rate = 0.5;
                                        if (sort_2F[i].c1m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_e0.Add(duty_temp);
                                    }
                                    else
                                    {
                                        for (j = 1; j < sort_2F[i].e0m; j++)
                                        {
                                            duty_temp = new duty_index();
                                            duty_temp.m = sort_2F[i].m;
                                            duty_temp.n = sort_2F[i].n;
                                            duty_temp.e0m = sort_2F[i].e0m;
                                            duty_temp.element = j;
                                            duty_temp.rate = (double)j / duty_temp.e0m;
                                            if (sort_2F[i].c1m % cm == 0)
                                                duty_temp.red = false;
                                            else
                                                duty_temp.red = true;
                                            sort_duty_e0.Add(duty_temp);
                                        }
                                    }
                                }

                                sort_duty_e0.Sort(sort_duty_e0_compare);

                                //LB_group.Text += "\nsort_duty_e0_d.Count = " + sort_duty_e0.Count;

                                count_temp = sort_duty_e0_2.Count;

                                sort_duty_e0_2.Clear();
                                sort_duty_e0_2.Add(sort_duty_e0[0]);

                                for (i = 1; i < sort_duty_e0.Count; i++)
                                {
                                    if (sort_duty_e0[i].rate - sort_duty_e0[i - 1].rate > 1e-6)
                                        sort_duty_e0_2.Add(sort_duty_e0[i]);
                                    else
                                        if (sort_duty_e0[i].red == false && sort_duty_e0[i - 1].red == true)
                                        {
                                            sort_duty_e0_2.Remove(sort_duty_e0_2.Last());
                                            sort_duty_e0_2.Add(sort_duty_e0[i]);
                                        }
                                }

                                CBB_e0_duty.Items.Clear();
                                for (i = 0; i < sort_duty_e0_2.Count; i++)
                                {
                                    if (sort_duty_e0_2[i].red)
                                        CBB_e0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                                    else
                                        CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                                }

                                CBB_e0_duty.SelectedIndex = SelectedIndex_e0;

                                if (sort_duty_e0_2.Count != count_temp)
                                {
                                    MessageBox.Show("sort_duty_e0_2.Count error");
                                }
                            }
                        }
                        if (sort_duty_c1_2[CBB_c1_duty.SelectedIndex].red)
                        {
                            SelectedIndex_c1 = CBB_c1_duty.SelectedIndex;
                            sort_duty_c1_2[CBB_c1_duty.SelectedIndex].red = false;
                            CBB_c1_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c1_2.Count; i++)
                            {
                                if (sort_duty_c1_2[i].red)
                                    CBB_c1_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                                else
                                    CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                            }
                            CBB_c1_duty.SelectedIndex = SelectedIndex_c1;
                        }
                        c1_duty = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].rate * 100;
                        n = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].n;
                        m = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].m;
                        c1_m = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m;
                    }
                    else if (c012 == 2)//e0
                    {
                        if (CB_c0.Checked || CB_c1.Checked)
                        {
                            cm = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m;
                            cm /= GCD(sort_duty_e0_2[CBB_e0_duty.SelectedIndex].element, cm);
                            if (CB_c0.Checked)
                            {
                                sort_duty_c0.Clear();
                                for (i = 0; i < sort_2_count; i++)
                                {
                                    if (sort_2F[i].c0m == 1)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2F[i].m;
                                        duty_temp.n = sort_2F[i].n;
                                        duty_temp.c0m = 1;
                                        duty_temp.element = 1;
                                        duty_temp.rate = 0.5;
                                        if (sort_2F[i].e0m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c0.Add(duty_temp);
                                    }
                                    else
                                    {
                                        for (j = 1; j < sort_2F[i].c0m; j++)
                                        {
                                            duty_temp = new duty_index();
                                            duty_temp.m = sort_2F[i].m;
                                            duty_temp.n = sort_2F[i].n;
                                            duty_temp.c0m = sort_2F[i].c0m;
                                            duty_temp.element = j;
                                            duty_temp.rate = (double)j / duty_temp.c0m;
                                            if (sort_2F[i].e0m % cm == 0)
                                                duty_temp.red = false;
                                            else
                                                duty_temp.red = true;
                                            sort_duty_c0.Add(duty_temp);
                                        }
                                    }
                                }

                                sort_duty_c0.Sort(sort_duty_c0_compare);

                                //LB_group.Text += "\nsort_duty_c0_d.Count = " + sort_duty_c0.Count;

                                count_temp = sort_duty_c0_2.Count;

                                sort_duty_c0_2.Clear();
                                sort_duty_c0_2.Add(sort_duty_c0[0]);

                                for (i = 1; i < sort_duty_c0.Count; i++)
                                {
                                    if (sort_duty_c0[i].rate - sort_duty_c0[i - 1].rate > 1e-6)
                                        sort_duty_c0_2.Add(sort_duty_c0[i]);
                                    else
                                        if (sort_duty_c0[i].red == false && sort_duty_c0[i - 1].red == true)
                                        {
                                            sort_duty_c0_2.Remove(sort_duty_c0_2.Last());
                                            sort_duty_c0_2.Add(sort_duty_c0[i]);
                                        }
                                }

                                CBB_c0_duty.Items.Clear();
                                for (i = 0; i < sort_duty_c0_2.Count; i++)
                                {
                                    if (sort_duty_c0_2[i].red)
                                        CBB_c0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                                    else
                                        CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                                }

                                CBB_c0_duty.SelectedIndex = SelectedIndex_c0;

                                if (sort_duty_c0_2.Count != count_temp)
                                {
                                    MessageBox.Show("sort_duty_c0_2.Count error");
                                }
                            }
                            if (CB_c1.Checked)
                            {
                                sort_duty_c1.Clear();
                                for (i = 0; i < sort_2_count; i++)
                                {
                                    if (sort_2F[i].c1m == 1)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = sort_2F[i].m;
                                        duty_temp.n = sort_2F[i].n;
                                        duty_temp.c1m = 1;
                                        duty_temp.element = 1;
                                        duty_temp.rate = 0.5;
                                        if (sort_2F[i].e0m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c1.Add(duty_temp);
                                    }
                                    else
                                    {
                                        for (j = 1; j < sort_2F[i].c1m; j++)
                                        {
                                            duty_temp = new duty_index();
                                            duty_temp.m = sort_2F[i].m;
                                            duty_temp.n = sort_2F[i].n;
                                            duty_temp.c1m = sort_2F[i].c1m;
                                            duty_temp.element = j;
                                            duty_temp.rate = (double)j / duty_temp.c1m;
                                            if (sort_2F[i].e0m % cm == 0)
                                                duty_temp.red = false;
                                            else
                                                duty_temp.red = true;
                                            sort_duty_c1.Add(duty_temp);
                                        }
                                    }
                                }

                                sort_duty_c1.Sort(sort_duty_c1_compare);

                                //LB_group.Text += "\nsort_duty_c1_d.Count = " + sort_duty_c1.Count;

                                count_temp = sort_duty_c1_2.Count;

                                sort_duty_c1_2.Clear();
                                sort_duty_c1_2.Add(sort_duty_c1[0]);

                                for (i = 1; i < sort_duty_c1.Count; i++)
                                {
                                    if (sort_duty_c1[i].rate - sort_duty_c1[i - 1].rate > 1e-6)
                                        sort_duty_c1_2.Add(sort_duty_c1[i]);
                                    else
                                        if (sort_duty_c1[i].red == false && sort_duty_c1[i - 1].red == true)
                                        {
                                            sort_duty_c1_2.Remove(sort_duty_c1_2.Last());
                                            sort_duty_c1_2.Add(sort_duty_c1[i]);
                                        }
                                }

                                CBB_c1_duty.Items.Clear();
                                for (i = 0; i < sort_duty_c1_2.Count; i++)
                                {
                                    if (sort_duty_c1_2[i].red)
                                        CBB_c1_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                                    else
                                        CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                                }

                                CBB_c1_duty.SelectedIndex = SelectedIndex_c1;

                                if (sort_duty_c1_2.Count != count_temp)
                                {
                                    MessageBox.Show("sort_duty_c1_2.Count error");
                                }
                            }
                        }
                        if (sort_duty_e0_2[CBB_e0_duty.SelectedIndex].red)
                        {
                            SelectedIndex_e0 = CBB_e0_duty.SelectedIndex;
                            sort_duty_e0_2[CBB_e0_duty.SelectedIndex].red = false;
                            CBB_e0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_e0_2.Count; i++)
                            {
                                if (sort_duty_e0_2[i].red)
                                    CBB_e0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                                else
                                    CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                            }
                            CBB_e0_duty.SelectedIndex = SelectedIndex_e0;
                        }
                        e0_duty = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].rate * 100;
                        n = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].n;
                        m = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].m;
                        e0_m = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m;
                    }
                    else
                    {
                        MessageBox.Show("PTF N c012 error");
                        LB_message_output.Text = "PTF N c012 error";
                    }
                }
                else if (RB_mode1.Checked)//零延时，e0补偿
                {
                    if (c012 == 0)//c0
                    {
                        if (CB_c1.Checked)
                        {
                            cm = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m;
                            cm /= GCD(sort_duty_c0_2[CBB_c0_duty.SelectedIndex].element, cm);
                            sort_duty_c1.Clear();
                            for (i = 1; i <= MmaxF; i++)
                            {
                                if (sort_spl[i].enable == true)
                                {
                                    if (sort_spl[i].c1m == 1)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = 1;
                                        duty_temp.n = 1;
                                        duty_temp.c1m = 1;
                                        duty_temp.e0m = i;
                                        duty_temp.element = 1;
                                        duty_temp.rate = 0.5;
                                        if (sort_spl[i].c0m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c1.Add(duty_temp);
                                    }
                                    else
                                    {
                                        for (j = 1; j < sort_spl[i].c1m; j++)
                                        {
                                            duty_temp = new duty_index();
                                            duty_temp.m = 1;
                                            duty_temp.n = 1;
                                            duty_temp.c1m = sort_spl[i].c1m;
                                            duty_temp.e0m = i;
                                            duty_temp.element = j;
                                            duty_temp.rate = (double)j / duty_temp.c1m;
                                            if (sort_spl[i].c0m % cm == 0)
                                                duty_temp.red = false;
                                            else
                                                duty_temp.red = true;
                                            sort_duty_c1.Add(duty_temp);
                                        }
                                    }
                                }
                            }

                            sort_duty_c1.Sort(sort_duty_c1_compare);

                            //LB_group.Text += "\nsort_duty_c1_d.Count = " + sort_duty_c1.Count;

                            count_temp = sort_duty_c1_2.Count;

                            sort_duty_c1_2.Clear();
                            sort_duty_c1_2.Add(sort_duty_c1[0]);

                            for (i = 1; i < sort_duty_c1.Count; i++)
                            {
                                if (sort_duty_c1[i].rate - sort_duty_c1[i - 1].rate > 1e-6)
                                    sort_duty_c1_2.Add(sort_duty_c1[i]);
                                else
                                    if (sort_duty_c1[i].red == false && sort_duty_c1[i - 1].red == true)
                                    {
                                        sort_duty_c1_2.Remove(sort_duty_c1_2.Last());
                                        sort_duty_c1_2.Add(sort_duty_c1[i]);
                                    }
                            }

                            CBB_c1_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c1_2.Count; i++)
                            {
                                if (sort_duty_c1_2[i].red)
                                    CBB_c1_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                                else
                                    CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                            }

                            CBB_c1_duty.SelectedIndex = SelectedIndex_c1;

                            c1_m = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m;

                            if (sort_duty_c1_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c1_2.Count error");
                            }
                        }

                        //e0默认Checked

                        if (sort_duty_c0_2[CBB_c0_duty.SelectedIndex].red)
                        {
                            SelectedIndex_c0 = CBB_c0_duty.SelectedIndex;
                            sort_duty_c0_2[CBB_c0_duty.SelectedIndex].red = false;
                            CBB_c0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c0_2.Count; i++)
                            {
                                if (sort_duty_c0_2[i].red)
                                    CBB_c0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                                else
                                    CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                            }
                            CBB_c0_duty.SelectedIndex = SelectedIndex_c0;
                        }

                        //c0_duty = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].rate * 100;
                        //n = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].n;
                        //m = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].m;
                        c0_m = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m;
                        e0_m = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].e0m;

                        sort_duty_e0_2.Clear();

                        for (j = 1; j < e0_m; j++)
                        {
                            duty_temp = new duty_index();
                            duty_temp.m = 1;
                            duty_temp.n = 1;
                            duty_temp.c0m = sort_spl[e0_m].c0m;//可能精简掉
                            duty_temp.e0m = e0_m;
                            duty_temp.element = j;
                            duty_temp.rate = (double)j / e0_m;
                            duty_temp.red = false;
                            sort_duty_e0_2.Add(duty_temp);
                        }

                        CBB_e0_duty.Items.Clear();
                        for (i = 0; i < sort_duty_e0_2.Count; i++)
                        {
                            CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                        }
                        if (CBB_e0_duty.SelectedIndex < 0)
                            CBB_e0_duty.SelectedIndex = (sort_duty_e0_2.Count - 1) / 2;
                    }
                    else if (c012 == 1)//c1
                    {
                        if (CB_c0.Checked)
                        {
                            cm = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m;
                            cm /= GCD(sort_duty_c1_2[CBB_c1_duty.SelectedIndex].element, cm);

                            sort_duty_c0.Clear();
                            for (i = 1; i <= MmaxF; i++)
                            {
                                if (sort_spl[i].enable == true)
                                {
                                    if (sort_spl[i].c0m == 1)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = 1;
                                        duty_temp.n = 1;
                                        duty_temp.c0m = 1;
                                        duty_temp.e0m = i;
                                        duty_temp.element = 1;
                                        duty_temp.rate = 0.5;
                                        if (sort_spl[i].c1m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c0.Add(duty_temp);
                                    }
                                    else
                                    {
                                        for (j = 1; j < sort_spl[i].c0m; j++)
                                        {
                                            duty_temp = new duty_index();
                                            duty_temp.m = 1;
                                            duty_temp.n = 1;
                                            duty_temp.c0m = sort_spl[i].c0m;
                                            duty_temp.e0m = i;
                                            duty_temp.element = j;
                                            duty_temp.rate = (double)j / duty_temp.c0m;
                                            if (sort_spl[i].c1m % cm == 0)
                                                duty_temp.red = false;
                                            else
                                                duty_temp.red = true;
                                            sort_duty_c0.Add(duty_temp);
                                        }
                                    }
                                }
                            }

                            sort_duty_c0.Sort(sort_duty_c0_compare);

                            //LB_group.Text += "\nsort_duty_c0_d.Count = " + sort_duty_c0.Count;

                            count_temp = sort_duty_c0_2.Count;

                            sort_duty_c0_2.Clear();
                            sort_duty_c0_2.Add(sort_duty_c0[0]);

                            for (i = 1; i < sort_duty_c0.Count; i++)
                            {
                                if (sort_duty_c0[i].rate - sort_duty_c0[i - 1].rate > 1e-6)
                                    sort_duty_c0_2.Add(sort_duty_c0[i]);
                                else
                                    if (sort_duty_c0[i].red == false && sort_duty_c0[i - 1].red == true)
                                    {
                                        sort_duty_c0_2.Remove(sort_duty_c0_2.Last());
                                        sort_duty_c0_2.Add(sort_duty_c0[i]);
                                    }
                            }

                            CBB_c0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c0_2.Count; i++)
                            {
                                if (sort_duty_c0_2[i].red)
                                    CBB_c0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                                else
                                    CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                            }

                            CBB_c0_duty.SelectedIndex = SelectedIndex_c0;

                            c0_m = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m;

                            if (sort_duty_c0_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c0_2.Count error");
                            }

                            //e0默认Checked
                        }
                        if (sort_duty_c1_2[CBB_c1_duty.SelectedIndex].red)
                        {
                            SelectedIndex_c1 = CBB_c1_duty.SelectedIndex;
                            sort_duty_c1_2[CBB_c1_duty.SelectedIndex].red = false;
                            CBB_c1_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c1_2.Count; i++)
                            {
                                if (sort_duty_c1_2[i].red)
                                    CBB_c1_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                                else
                                    CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                            }
                            CBB_c1_duty.SelectedIndex = SelectedIndex_c1;
                        }

                        c1_m = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m;
                        e0_m = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].e0m;

                        sort_duty_e0_2.Clear();

                        for (j = 1; j < e0_m; j++)
                        {
                            duty_temp = new duty_index();
                            duty_temp.m = 1;
                            duty_temp.n = 1;
                            duty_temp.c1m = sort_spl[e0_m].c1m;
                            duty_temp.e0m = e0_m;
                            duty_temp.element = j;
                            duty_temp.rate = (double)j / e0_m;
                            duty_temp.red = false;
                            sort_duty_e0_2.Add(duty_temp);
                        }

                        CBB_e0_duty.Items.Clear();
                        for (i = 0; i < sort_duty_e0_2.Count; i++)
                        {
                            CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                        }
                        if (CBB_e0_duty.SelectedIndex < 0)
                            CBB_e0_duty.SelectedIndex = (sort_duty_e0_2.Count - 1) / 2;
                    }
                    else if (c012 == 2)//e0
                    {
                        //什么都不做
                    }
                    else
                    {
                        MessageBox.Show("c012 error");
                        LB_message_output.Text = "c012 error";
                    }
                }
                else if (RB_mode2.Checked)//普通，c0补偿
                {
                    if (c012 == 1)//c1
                    {
                        if (CB_e0.Checked)
                        {
                            cm = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m;
                            cm /= GCD(sort_duty_c1_2[CBB_c1_duty.SelectedIndex].element, cm);

                            sort_duty_e0.Clear();
                            for (i = 1; i <= MmaxF; i++)
                            {
                                if (sort_spl[i].enable == true)
                                {
                                    if (sort_spl[i].e0m == 1)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = 1;
                                        duty_temp.n = 1;
                                        duty_temp.e0m = 1;
                                        duty_temp.c0m = i;
                                        duty_temp.element = 1;
                                        duty_temp.rate = 0.5;
                                        if (sort_spl[i].c1m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_e0.Add(duty_temp);
                                    }
                                    else
                                    {
                                        for (j = 1; j < sort_spl[i].e0m; j++)
                                        {
                                            duty_temp = new duty_index();
                                            duty_temp.m = 1;
                                            duty_temp.n = 1;
                                            duty_temp.e0m = sort_spl[i].e0m;
                                            duty_temp.c0m = i;
                                            duty_temp.element = j;
                                            duty_temp.rate = (double)j / duty_temp.e0m;
                                            if (sort_spl[i].c1m % cm == 0)
                                                duty_temp.red = false;
                                            else
                                                duty_temp.red = true;
                                            sort_duty_e0.Add(duty_temp);
                                        }
                                    }
                                }
                            }

                            sort_duty_e0.Sort(sort_duty_e0_compare);

                            //LB_group.Text += "\nsort_duty_e0_d.Count = " + sort_duty_e0.Count;

                            count_temp = sort_duty_e0_2.Count;

                            sort_duty_e0_2.Clear();
                            sort_duty_e0_2.Add(sort_duty_e0[0]);

                            for (i = 1; i < sort_duty_e0.Count; i++)
                            {
                                if (sort_duty_e0[i].rate - sort_duty_e0[i - 1].rate > 1e-6)
                                    sort_duty_e0_2.Add(sort_duty_e0[i]);
                                else
                                    if (sort_duty_e0[i].red == false && sort_duty_e0[i - 1].red == true)
                                    {
                                        sort_duty_e0_2.Remove(sort_duty_e0_2.Last());
                                        sort_duty_e0_2.Add(sort_duty_e0[i]);
                                    }
                            }

                            CBB_e0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_e0_2.Count; i++)
                            {
                                if (sort_duty_e0_2[i].red)
                                    CBB_e0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                                else
                                    CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                            }

                            CBB_e0_duty.SelectedIndex = SelectedIndex_e0;

                            e0_m = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m;

                            if (sort_duty_e0_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_e0_2.Count error");
                            }

                            //c0默认Checked
                        }
                        if (sort_duty_c1_2[CBB_c1_duty.SelectedIndex].red)
                        {
                            SelectedIndex_c1 = CBB_c1_duty.SelectedIndex;
                            sort_duty_c1_2[CBB_c1_duty.SelectedIndex].red = false;
                            CBB_c1_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c1_2.Count; i++)
                            {
                                if (sort_duty_c1_2[i].red)
                                    CBB_c1_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                                else
                                    CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                            }
                            CBB_c1_duty.SelectedIndex = SelectedIndex_c1;
                        }

                        c1_m = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m;
                        c0_m = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c0m;

                        sort_duty_c0_2.Clear();

                        for (j = 1; j < c0_m; j++)
                        {
                            duty_temp = new duty_index();
                            duty_temp.m = 1;
                            duty_temp.n = 1;
                            duty_temp.c1m = sort_spl[c0_m].c1m;//可能精简
                            duty_temp.c0m = c0_m;
                            duty_temp.element = j;
                            duty_temp.rate = (double)j / c0_m;
                            duty_temp.red = false;
                            sort_duty_c0_2.Add(duty_temp);
                        }

                        CBB_c0_duty.Items.Clear();
                        for (i = 0; i < sort_duty_c0_2.Count; i++)
                        {
                            CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                        }
                        if (CBB_c0_duty.SelectedIndex < 0)
                            CBB_c0_duty.SelectedIndex = (sort_duty_c0_2.Count - 1) / 2;
                    }
                    else if (c012 == 2)//e0
                    {
                        if (CB_c1.Checked)
                        {
                            cm = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m;
                            cm /= GCD(sort_duty_e0_2[CBB_e0_duty.SelectedIndex].element, cm);

                            sort_duty_c1.Clear();
                            for (i = 1; i <= MmaxF; i++)
                            {
                                if (sort_spl[i].enable == true)
                                {
                                    if (sort_spl[i].c1m == 1)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = 1;
                                        duty_temp.n = 1;
                                        duty_temp.c0m = i;
                                        duty_temp.c1m = 1;
                                        duty_temp.element = 1;
                                        duty_temp.rate = 0.5;
                                        if (sort_spl[i].e0m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c1.Add(duty_temp);
                                    }
                                    else
                                    {
                                        for (j = 1; j < sort_spl[i].c1m; j++)
                                        {
                                            duty_temp = new duty_index();
                                            duty_temp.m = 1;
                                            duty_temp.n = 1;
                                            duty_temp.c0m = i;
                                            duty_temp.c1m = sort_spl[i].c1m;
                                            duty_temp.element = j;
                                            duty_temp.rate = (double)j / duty_temp.c1m;
                                            if (sort_spl[i].e0m % cm == 0)
                                                duty_temp.red = false;
                                            else
                                                duty_temp.red = true;
                                            sort_duty_c1.Add(duty_temp);
                                        }
                                    }
                                }
                            }

                            sort_duty_c1.Sort(sort_duty_c1_compare);

                            //LB_group.Text += "\nsort_duty_c1_d.Count = " + sort_duty_c1.Count;

                            count_temp = sort_duty_c1_2.Count;

                            sort_duty_c1_2.Clear();
                            sort_duty_c1_2.Add(sort_duty_c1[0]);

                            for (i = 1; i < sort_duty_c1.Count; i++)
                            {
                                if (sort_duty_c1[i].rate - sort_duty_c1[i - 1].rate > 1e-6)
                                    sort_duty_c1_2.Add(sort_duty_c1[i]);
                                else
                                    if (sort_duty_c1[i].red == false && sort_duty_c1[i - 1].red == true)
                                    {
                                        sort_duty_c1_2.Remove(sort_duty_c1_2.Last());
                                        sort_duty_c1_2.Add(sort_duty_c1[i]);
                                    }
                            }

                            CBB_c1_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c1_2.Count; i++)
                            {
                                if (sort_duty_c1_2[i].red)
                                    CBB_c1_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                                else
                                    CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                            }

                            CBB_c1_duty.SelectedIndex = SelectedIndex_c1;

                            c1_m = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m;

                            if (sort_duty_c1_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c1_2.Count error");
                            }
                        }
                        if (sort_duty_e0_2[CBB_e0_duty.SelectedIndex].red)
                        {
                            SelectedIndex_e0 = CBB_e0_duty.SelectedIndex;
                            sort_duty_e0_2[CBB_e0_duty.SelectedIndex].red = false;
                            CBB_e0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_e0_2.Count; i++)
                            {
                                if (sort_duty_e0_2[i].red)
                                    CBB_e0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                                else
                                    CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                            }
                            CBB_e0_duty.SelectedIndex = SelectedIndex_e0;
                        }

                        //c0默认Checked
                        e0_m = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m;
                        c0_m = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].c0m;

                        sort_duty_c0_2.Clear();

                        for (j = 1; j < c0_m; j++)
                        {
                            duty_temp = new duty_index();
                            duty_temp.m = 1;
                            duty_temp.n = 1;
                            duty_temp.e0m = sort_spl[c0_m].e0m;//可能精简
                            duty_temp.c0m = c0_m;
                            duty_temp.element = j;
                            duty_temp.rate = (double)j / c0_m;
                            duty_temp.red = false;
                            sort_duty_c0_2.Add(duty_temp);
                        }

                        CBB_c0_duty.Items.Clear();
                        for (i = 0; i < sort_duty_c0_2.Count; i++)
                        {
                            CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                        }
                        if (CBB_c0_duty.SelectedIndex < 0)
                            CBB_c0_duty.SelectedIndex = (sort_duty_c0_2.Count - 1) / 2;
                    }
                    else if (c012 == 0)//c0
                    {
                        //什么都不做
                    }
                    else
                    {
                        MessageBox.Show("c012 error");
                        LB_message_output.Text = "c012 error";
                    }
                }
                else if (RB_mode3.Checked)//普通，c1补偿
                {
                    if (c012 == 0)//c0
                    {
                        if (CB_e0.Checked)
                        {
                            cm = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m;
                            cm /= GCD(sort_duty_c0_2[CBB_c0_duty.SelectedIndex].element, cm);

                            sort_duty_e0.Clear();
                            for (i = 1; i <= MmaxF; i++)
                            {
                                if (sort_spl[i].enable == true)
                                {
                                    if (sort_spl[i].e0m == 1)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = 1;
                                        duty_temp.n = 1;
                                        duty_temp.c1m = i;
                                        duty_temp.e0m = 1;
                                        duty_temp.element = 1;
                                        duty_temp.rate = 0.5;
                                        if (sort_spl[i].c0m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_e0.Add(duty_temp);
                                    }
                                    else
                                    {
                                        for (j = 1; j < sort_spl[i].e0m; j++)
                                        {
                                            duty_temp = new duty_index();
                                            duty_temp.m = 1;
                                            duty_temp.n = 1;
                                            duty_temp.c1m = i;
                                            duty_temp.e0m = sort_spl[i].e0m;
                                            duty_temp.element = j;
                                            duty_temp.rate = (double)j / duty_temp.e0m;
                                            if (sort_spl[i].c0m % cm == 0)
                                                duty_temp.red = false;
                                            else
                                                duty_temp.red = true;
                                            sort_duty_e0.Add(duty_temp);
                                        }
                                    }
                                }
                            }

                            sort_duty_e0.Sort(sort_duty_e0_compare);

                            //LB_group.Text += "\nsort_duty_e0_d.Count = " + sort_duty_e0.Count;

                            count_temp = sort_duty_e0_2.Count;

                            sort_duty_e0_2.Clear();
                            sort_duty_e0_2.Add(sort_duty_e0[0]);

                            for (i = 1; i < sort_duty_e0.Count; i++)
                            {
                                if (sort_duty_e0[i].rate - sort_duty_e0[i - 1].rate > 1e-6)
                                    sort_duty_e0_2.Add(sort_duty_e0[i]);
                                else
                                    if (sort_duty_e0[i].red == false && sort_duty_e0[i - 1].red == true)
                                    {
                                        sort_duty_e0_2.Remove(sort_duty_e0_2.Last());
                                        sort_duty_e0_2.Add(sort_duty_e0[i]);
                                    }
                            }

                            CBB_e0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_e0_2.Count; i++)
                            {
                                if (sort_duty_e0_2[i].red)
                                    CBB_e0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                                else
                                    CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                            }

                            CBB_e0_duty.SelectedIndex = SelectedIndex_e0;

                            e0_m = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m;

                            if (sort_duty_e0_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_e0_2.Count error");
                            }
                        }
                        if (sort_duty_c0_2[CBB_c0_duty.SelectedIndex].red)
                        {
                            SelectedIndex_c0 = CBB_c0_duty.SelectedIndex;
                            sort_duty_c0_2[CBB_c0_duty.SelectedIndex].red = false;
                            CBB_c0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c0_2.Count; i++)
                            {
                                if (sort_duty_c0_2[i].red)
                                    CBB_c0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                                else
                                    CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                            }
                            CBB_c0_duty.SelectedIndex = SelectedIndex_c0;
                        }

                        //c1默认Checked
                        c0_m = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m;
                        c1_m = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c1m;

                        sort_duty_c1_2.Clear();

                        for (j = 1; j < c1_m; j++)
                        {
                            duty_temp = new duty_index();
                            duty_temp.m = 1;
                            duty_temp.n = 1;
                            duty_temp.c0m = sort_spl[c1_m].c0m;//可能精简
                            duty_temp.c1m = c1_m;
                            duty_temp.element = j;
                            duty_temp.rate = (double)j / c1_m;
                            duty_temp.red = false;
                            sort_duty_c1_2.Add(duty_temp);
                        }

                        CBB_c1_duty.Items.Clear();
                        for (i = 0; i < sort_duty_c1_2.Count; i++)
                        {
                            CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                        }
                        if (CBB_c1_duty.SelectedIndex < 0)
                            CBB_c1_duty.SelectedIndex = (sort_duty_c1_2.Count - 1) / 2;
                    }
                    else if (c012 == 2)//e0
                    {
                        if (CB_c0.Checked)
                        {
                            cm = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m;
                            cm /= GCD(sort_duty_e0_2[CBB_e0_duty.SelectedIndex].element, cm);

                            sort_duty_c0.Clear();
                            for (i = 1; i <= MmaxF; i++)
                            {
                                if (sort_spl[i].enable == true)
                                {
                                    if (sort_spl[i].c0m == 1)
                                    {
                                        duty_temp = new duty_index();
                                        duty_temp.m = 1;
                                        duty_temp.n = 1;
                                        duty_temp.c1m = i;
                                        duty_temp.c0m = 1;
                                        duty_temp.element = 1;
                                        duty_temp.rate = 0.5;
                                        if (sort_spl[i].e0m % cm == 0)
                                            duty_temp.red = false;
                                        else
                                            duty_temp.red = true;
                                        sort_duty_c0.Add(duty_temp);
                                    }
                                    else
                                    {
                                        for (j = 1; j < sort_spl[i].c0m; j++)
                                        {
                                            duty_temp = new duty_index();
                                            duty_temp.m = 1;
                                            duty_temp.n = 1;
                                            duty_temp.c1m = i;
                                            duty_temp.c0m = sort_spl[i].c0m;
                                            duty_temp.element = j;
                                            duty_temp.rate = (double)j / duty_temp.c0m;
                                            if (sort_spl[i].e0m % cm == 0)
                                                duty_temp.red = false;
                                            else
                                                duty_temp.red = true;
                                            sort_duty_c0.Add(duty_temp);
                                        }
                                    }
                                }
                            }

                            sort_duty_c0.Sort(sort_duty_c0_compare);

                            //LB_group.Text += "\nsort_duty_c0_d.Count = " + sort_duty_c0.Count;

                            count_temp = sort_duty_c0_2.Count;

                            sort_duty_c0_2.Clear();
                            sort_duty_c0_2.Add(sort_duty_c0[0]);

                            for (i = 1; i < sort_duty_c0.Count; i++)
                            {
                                if (sort_duty_c0[i].rate - sort_duty_c0[i - 1].rate > 1e-6)
                                    sort_duty_c0_2.Add(sort_duty_c0[i]);
                                else
                                    if (sort_duty_c0[i].red == false && sort_duty_c0[i - 1].red == true)
                                    {
                                        sort_duty_c0_2.Remove(sort_duty_c0_2.Last());
                                        sort_duty_c0_2.Add(sort_duty_c0[i]);
                                    }
                            }

                            CBB_c0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_c0_2.Count; i++)
                            {
                                if (sort_duty_c0_2[i].red)
                                    CBB_c0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                                else
                                    CBB_c0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c0_2[i].rate).ToString("f3"));
                            }

                            CBB_c0_duty.SelectedIndex = SelectedIndex_c0;

                            c0_m = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m;

                            if (sort_duty_c0_2.Count != count_temp)
                            {
                                MessageBox.Show("sort_duty_c0_2.Count error");
                            }
                        }
                        if (sort_duty_e0_2[CBB_e0_duty.SelectedIndex].red)
                        {
                            SelectedIndex_e0 = CBB_e0_duty.SelectedIndex;
                            sort_duty_e0_2[CBB_e0_duty.SelectedIndex].red = false;
                            CBB_e0_duty.Items.Clear();
                            for (i = 0; i < sort_duty_e0_2.Count; i++)
                            {
                                if (sort_duty_e0_2[i].red)
                                    CBB_e0_duty.Items.Add("*" + Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                                else
                                    CBB_e0_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_e0_2[i].rate).ToString("f3"));
                            }
                            CBB_e0_duty.SelectedIndex = SelectedIndex_e0;
                        }

                        //c1默认Checked
                        e0_m = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m;
                        c1_m = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].c1m;

                        sort_duty_c1_2.Clear();

                        for (j = 1; j < c1_m; j++)
                        {
                            duty_temp = new duty_index();
                            duty_temp.m = 1;
                            duty_temp.n = 1;
                            duty_temp.e0m = sort_spl[c1_m].e0m;//可能精简
                            duty_temp.c1m = c1_m;
                            duty_temp.element = j;
                            duty_temp.rate = (double)j / c1_m;
                            duty_temp.red = false;
                            sort_duty_c1_2.Add(duty_temp);
                        }

                        CBB_c1_duty.Items.Clear();
                        for (i = 0; i < sort_duty_c1_2.Count; i++)
                        {
                            CBB_c1_duty.Items.Add(Convert.ToDouble((double)100 * sort_duty_c1_2[i].rate).ToString("f3"));
                        }
                        if (CBB_c1_duty.SelectedIndex < 0)
                            CBB_c1_duty.SelectedIndex = (sort_duty_c1_2.Count - 1) / 2;
                    }
                    else if (c012 == 1)//c1
                    {
                        //什么都不做
                    }
                    else
                    {
                        MessageBox.Show("c012 error");
                        LB_message_output.Text = "c012 error";
                    }
                }
                else
                {
                    MessageBox.Show("PTF operation_mode error");
                    LB_message_output.Text = "PTF operation_mode error";
                }
            }


            //LB_group.Text += "\nRefreshDt2 [ n = " + n.ToString()
            //            + " m = " + m.ToString()
            //            + " c0m = " + c0_m.ToString()
            //            + " c1m = " + c1_m.ToString()
            //            + " e0m = " + e0_m.ToString() + " ]";

            //LB_info_output.Text = "c0_mul=" + c0_mul.ToString() + " c0_div=" + c0_div.ToString() + " c1_mul=" + c1_mul.ToString() + " c1_div=" + c1_div.ToString() + " e0_mul=" + e0_mul.ToString() + " e0_div=" + e0_div.ToString()
            //    + "\nVco=" + vco.ToString("n") + " mul_lcm=" + mul_lcm.ToString() + "\nN=" + n.ToString() + " M_m=" + m.ToString() + " c0_m=" + c0_m.ToString() + " c1_m=" + c1_m.ToString() + " e0_m=" + e0_m.ToString();

            if (CB_c0.Checked && sort_duty_c0_2[CBB_c0_duty.SelectedIndex].red || CB_c1.Checked && sort_duty_c1_2[CBB_c1_duty.SelectedIndex].red || CB_e0.Checked && sort_duty_e0_2[CBB_e0_duty.SelectedIndex].red || CB_c3.Checked && sort_duty_c3_2[CBB_c3_duty.SelectedIndex].red || CB_c4.Checked && sort_duty_c4_2[CBB_c4_duty.SelectedIndex].red || CB_e02.Checked && sort_duty_e02_2[CBB_e02_duty.SelectedIndex].red)
            {
                LB_message_output.Text = "Only if none of the duty cycle values has '*', will the 'Save' button be enabled.";
                OutPut(1);
                return false;
            }

            OutPut(0);
            //DrawPLL();
            //pictureBox.Refresh();
            LB_message_output.Text = "";
            //MessageBox.Show("RefreshData2");
            return true;
        }

        private void TB_inclk_KeyPress(object sender, KeyPressEventArgs e)
        {
            if ((e.KeyChar < 48 || e.KeyChar > 57) && e.KeyChar != 46 && e.KeyChar != 8)//退格=8
                e.Handled = true;

            if (e.KeyChar != 8 && TB_inclk.Text.Length > 6)
                e.Handled = true;

            if (TB_inclk.Text.IndexOf('.') != -1 && e.KeyChar == '.')
                e.Handled = true;
        }
        private void TB_inclk_TextChanged(object sender, EventArgs e)
        {
            int last;
            if (TB_inclk.Text.IndexOf('.') == 0)
            {
                TB_inclk.Text = "0" + TB_inclk.Text;
                TB_inclk.SelectionStart = TB_inclk.Text.IndexOf('.') + 1;
            }
            last = TB_inclk.Text.LastIndexOf('.');
            if (TB_inclk.Text.IndexOf('.') != last)
            {
                TB_inclk.Text = TB_inclk.Text.Substring(0, last) + TB_inclk.Text.Substring(last + 1);
                TB_inclk.SelectionStart = last;
            }
            if (TB_inclk.Text.Length > 7)
            {
                //last = TB_inclk.SelectionStart;
                TB_inclk.Text = TB_inclk.Text.Substring(0, 7);
                //TB_inclk.SelectionStart = last;
            }
            LB_message_output.Text = "";
            //saveenabled = RefreshData();
        }
        private void TB_inclk_Leave(object sender, EventArgs e)
        {
            if (TB_inclk.Text.Length == 0)
                TB_inclk.Text = "0";
            inclk_freq = double.Parse(TB_inclk.Text);
            if (inclk_freq < 15.625)
            {
                inclk_freq = 15.625;
                TB_inclk.Text = "15.625";
            }
            else
            {
                if (RB_mode0.Checked || RB_N.Checked)
                {
                    if (inclk_freq > 120)
                    {
                        inclk_freq = 120;
                        TB_inclk.Text = "120.000";
                    }
                }
                else
                {
                    if (inclk_freq > 60)
                    {
                        inclk_freq = 60;
                        TB_inclk.Text = "60.000";
                    }
                }
            }
            if (inclk_freq - inclk_freq_old < 1e-6 && inclk_freq_old - inclk_freq < 1e-6)//inclk_freq_old == inclk_freq
            {

            }
            else
            {
                inclk_freq_old = inclk_freq;
                TB_inclk.Text = inclk_freq.ToString("f3");
                saveenabled = RefreshData();
                BT_Save.Enabled = saveenabled;
            }
            //TB_inclk.Text = inclk_freq.ToString("f3");
            //saveenabled = RefreshData();
            //BT_Save.Enabled = saveenabled;
        }

        //无补偿
        private void RB_mode0_Click(object sender, EventArgs e)
        {
            PTE = false;
            LB_MHz.Text = "MHz    (15.625 ~ 120.000)";

            GB_LPE.Enabled = false;
            GB_GLC.Enabled = false;
            label16.Enabled = false;
            label18.Enabled = false;
            label19.Enabled = false;
            LB_GLC.Enabled = false;
            CB_e0.Text = "e0";
            CB_c3.Visible = false;
            CB_c4.Visible = false;
            CB_e02.Visible = false;
            //LB_c3_freq.Visible = false;
            //LB_c4_freq.Visible = false;
            //LB_e02_freq.Visible = false;
            nUD_c3_mul.Visible = false;
            nUD_c4_mul.Visible = false;
            nUD_e02_mul.Visible = false;
            nUD_c3_div.Visible = false;
            nUD_c4_div.Visible = false;
            nUD_e02_div.Visible = false;
            CBB_c3_duty.Visible = false;
            CBB_c4_duty.Visible = false;
            CBB_e02_duty.Visible = false;
            CBB_c3_phase.Visible = false;
            CBB_c4_phase.Visible = false;
            CBB_e02_phase.Visible = false;

            CB_c0.Enabled = true;
            CB_c1.Enabled = true;
            CB_e0.Enabled = true;
            CB_c0.Checked = false;
            CB_c1.Checked = false;
            CB_e0.Checked = false;

            nUD_c0_mul.Maximum = MmaxF;
            nUD_c1_mul.Maximum = MmaxF;
            nUD_e0_mul.Maximum = MmaxF;

            nUD_c0_div.Maximum = NCMF;
            nUD_c1_div.Maximum = NCMF;
            nUD_e0_div.Maximum = NCMF;

            saveenabled = RefreshData();
            //LB_group.Text = "(n,m,c0,c1,e0)";
            BT_Save.Enabled = saveenabled;
        }
        //零延时，e0补偿
        private void RB_mode1_Click(object sender, EventArgs e)
        {
            PTE = false;
            LB_MHz.Text = "MHz    (15.625 ~ 60.000)";
            GB_LPE.Enabled = false;
            GB_GLC.Enabled = false;
            label16.Enabled = false;
            label18.Enabled = false;
            label19.Enabled = false;
            LB_GLC.Enabled = false;
            CB_e0.Text = "e0";
            CB_c3.Visible = false;
            CB_c4.Visible = false;
            CB_e02.Visible = false;
            //LB_c3_freq.Visible = false;
            //LB_c4_freq.Visible = false;
            //LB_e02_freq.Visible = false;
            nUD_c3_mul.Visible = false;
            nUD_c4_mul.Visible = false;
            nUD_e02_mul.Visible = false;
            nUD_c3_div.Visible = false;
            nUD_c4_div.Visible = false;
            nUD_e02_div.Visible = false;
            CBB_c3_duty.Visible = false;
            CBB_c4_duty.Visible = false;
            CBB_e02_duty.Visible = false;
            CBB_c3_phase.Visible = false;
            CBB_c4_phase.Visible = false;
            CBB_e02_phase.Visible = false;

            CB_c0.Enabled = true;
            CB_c1.Enabled = true;
            CB_e0.Enabled = false;
            CB_c0.Checked = false;
            CB_c1.Checked = false;
            CB_e0.Checked = true;

            if (inclk_freq > 60)
            {
                inclk_freq = 60;
                TB_inclk.Text = "60.000";
            }

            nUD_c0_mul.Maximum = MmaxF;
            nUD_c1_mul.Maximum = MmaxF;
            nUD_e0_mul.Maximum = MmaxF;

            nUD_c0_div.Maximum = MmaxF;
            nUD_c1_div.Maximum = MmaxF;
            nUD_e0_div.Maximum = MmaxF;

            saveenabled = RefreshData();
            //LB_group.Text = "(n,m,c0,c1,e0)";
            BT_Save.Enabled = saveenabled;
        }
        //普通，c0补偿
        private void RB_mode2_Click(object sender, EventArgs e)
        {
            PTE = false;
            LB_MHz.Text = "MHz    (15.625 ~ 60.000)";
            GB_LPE.Enabled = false;
            GB_GLC.Enabled = false;
            label16.Enabled = false;
            label18.Enabled = false;
            label19.Enabled = false;
            LB_GLC.Enabled = false;
            CB_e0.Text = "e0";
            CB_c3.Visible = false;
            CB_c4.Visible = false;
            CB_e02.Visible = false;
            //LB_c3_freq.Visible = false;
            //LB_c4_freq.Visible = false;
            //LB_e02_freq.Visible = false;
            nUD_c3_mul.Visible = false;
            nUD_c4_mul.Visible = false;
            nUD_e02_mul.Visible = false;
            nUD_c3_div.Visible = false;
            nUD_c4_div.Visible = false;
            nUD_e02_div.Visible = false;
            CBB_c3_duty.Visible = false;
            CBB_c4_duty.Visible = false;
            CBB_e02_duty.Visible = false;
            CBB_c3_phase.Visible = false;
            CBB_c4_phase.Visible = false;
            CBB_e02_phase.Visible = false;

            CB_c0.Enabled = false;
            CB_c1.Enabled = true;
            CB_e0.Enabled = true;
            CB_c0.Checked = true;
            CB_c1.Checked = false;
            CB_e0.Checked = false;

            if (inclk_freq > 60)
            {
                inclk_freq = 60;
                TB_inclk.Text = "60.000";
            }

            nUD_c0_mul.Maximum = MmaxF;
            nUD_c1_mul.Maximum = MmaxF;
            nUD_e0_mul.Maximum = MmaxF;

            nUD_c0_div.Maximum = MmaxF;
            nUD_c1_div.Maximum = MmaxF;
            nUD_e0_div.Maximum = MmaxF;

            saveenabled = RefreshData();
            //LB_group.Text = "(n,m,c0,c1,e0)";
            BT_Save.Enabled = saveenabled;
        }
        //普通，c1补偿
        private void RB_mode3_Click(object sender, EventArgs e)
        {
            PTE = false;
            LB_MHz.Text = "MHz    (15.625 ~ 60.000)";
            GB_LPE.Enabled = false;
            GB_GLC.Enabled = false;
            label16.Enabled = false;
            label18.Enabled = false;
            label19.Enabled = false;
            LB_GLC.Enabled = false;
            CB_e0.Text = "e0";
            CB_c3.Visible = false;
            CB_c4.Visible = false;
            CB_e02.Visible = false;
            //LB_c3_freq.Visible = false;
            //LB_c4_freq.Visible = false;
            //LB_e02_freq.Visible = false;
            nUD_c3_mul.Visible = false;
            nUD_c4_mul.Visible = false;
            nUD_e02_mul.Visible = false;
            nUD_c3_div.Visible = false;
            nUD_c4_div.Visible = false;
            nUD_e02_div.Visible = false;
            CBB_c3_duty.Visible = false;
            CBB_c4_duty.Visible = false;
            CBB_e02_duty.Visible = false;
            CBB_c3_phase.Visible = false;
            CBB_c4_phase.Visible = false;
            CBB_e02_phase.Visible = false;

            CB_c0.Enabled = true;
            CB_c1.Enabled = false;
            CB_e0.Enabled = true;
            CB_c0.Checked = false;
            CB_c1.Checked = true;
            CB_e0.Checked = false;

            if (inclk_freq > 60)
            {
                inclk_freq = 60;
                TB_inclk.Text = "60.000";
            }

            nUD_c0_mul.Maximum = MmaxF;
            nUD_c1_mul.Maximum = MmaxF;
            nUD_e0_mul.Maximum = MmaxF;

            nUD_c0_div.Maximum = MmaxF;
            nUD_c1_div.Maximum = MmaxF;
            nUD_e0_div.Maximum = MmaxF;

            saveenabled = RefreshData();
            //LB_group.Text = "(n,m,c0,c1,e0)";
            BT_Save.Enabled = saveenabled;
        }

        //6个pll
        private void RB_c0_Click(object sender, EventArgs e)
        {
            PTE = true;
            LB_MHz.Text = "MHz    (15.625 ~ 60.000)";
            GB_LPE.Enabled = true;
            GB_GLC.Enabled = true;
            label16.Enabled = true;
            label18.Enabled = true;
            label19.Enabled = true;
            LB_GLC.Enabled = true;
            CB_e0.Text = "c2";
            CB_c3.Visible = true;
            CB_c4.Visible = true;
            CB_e02.Visible = true;
            nUD_c3_mul.Visible = true;
            nUD_c4_mul.Visible = true;
            nUD_e02_mul.Visible = true;
            nUD_c3_div.Visible = true;
            nUD_c4_div.Visible = true;
            nUD_e02_div.Visible = true;
            CBB_c3_duty.Visible = true;
            CBB_c4_duty.Visible = true;
            CBB_e02_duty.Visible = true;
            CBB_c3_phase.Visible = true;
            CBB_c4_phase.Visible = true;
            CBB_e02_phase.Visible = true;

            nUD_c0_mul.Maximum = Mmax;
            nUD_c1_mul.Maximum = Mmax;
            nUD_e0_mul.Maximum = Mmax;
            nUD_c3_mul.Maximum = Mmax;
            nUD_c4_mul.Maximum = Mmax;
            nUD_e02_mul.Maximum = Mmax;
            nUD_c0_div.Maximum = NCML;
            nUD_c1_div.Maximum = NCML;
            nUD_e0_div.Maximum = NCML;
            nUD_c3_div.Maximum = NCML;
            nUD_c4_div.Maximum = NCML;
            nUD_e02_div.Maximum = NCML;

            CB_c0.Enabled = false;
            CB_c1.Enabled = true;
            CB_e0.Enabled = true;
            CB_c3.Enabled = true;
            CB_c4.Enabled = true;
            CB_e02.Enabled = true;
            CB_c0.Checked = true;
            CB_c1.Checked = false;
            CB_e0.Checked = false;
            CB_c3.Checked = false;
            CB_c4.Checked = false;
            CB_e02.Checked = false;

            if (inclk_freq > 60)
            {
                inclk_freq = 60;
                TB_inclk.Text = "60.000";
            }

            saveenabled = RefreshData();
            //LB_group.Text = "(n,m,c0,c1,e0,c3,c4,e02)";
            BT_Save.Enabled = saveenabled;
        }
        private void RB_c1_Click(object sender, EventArgs e)
        {
            PTE = true;
            LB_MHz.Text = "MHz    (15.625 ~ 60.000)";
            GB_LPE.Enabled = true;
            GB_GLC.Enabled = true;
            label16.Enabled = true;
            label18.Enabled = true;
            label19.Enabled = true;
            LB_GLC.Enabled = true;
            CB_e0.Text = "c2";
            CB_c3.Visible = true;
            CB_c4.Visible = true;
            CB_e02.Visible = true;
            nUD_c3_mul.Visible = true;
            nUD_c4_mul.Visible = true;
            nUD_e02_mul.Visible = true;
            nUD_c3_div.Visible = true;
            nUD_c4_div.Visible = true;
            nUD_e02_div.Visible = true;
            CBB_c3_duty.Visible = true;
            CBB_c4_duty.Visible = true;
            CBB_e02_duty.Visible = true;
            CBB_c3_phase.Visible = true;
            CBB_c4_phase.Visible = true;
            CBB_e02_phase.Visible = true;

            nUD_c0_mul.Maximum = Mmax;
            nUD_c1_mul.Maximum = Mmax;
            nUD_e0_mul.Maximum = Mmax;
            nUD_c3_mul.Maximum = Mmax;
            nUD_c4_mul.Maximum = Mmax;
            nUD_e02_mul.Maximum = Mmax;
            nUD_c0_div.Maximum = NCML;
            nUD_c1_div.Maximum = NCML;
            nUD_e0_div.Maximum = NCML;
            nUD_c3_div.Maximum = NCML;
            nUD_c4_div.Maximum = NCML;
            nUD_e02_div.Maximum = NCML;

            CB_c0.Enabled = true;
            CB_c1.Enabled = false;
            CB_e0.Enabled = true;
            CB_c3.Enabled = true;
            CB_c4.Enabled = true;
            CB_e02.Enabled = true;
            CB_c0.Checked = false;
            CB_c1.Checked = true;
            CB_e0.Checked = false;
            CB_c3.Checked = false;
            CB_c4.Checked = false;
            CB_e02.Checked = false;

            if (inclk_freq > 60)
            {
                inclk_freq = 60;
                TB_inclk.Text = "60.000";
            }

            saveenabled = RefreshData();
            //LB_group.Text = "(n,m,c0,c1,e0,c3,c4,e02)";
            BT_Save.Enabled = saveenabled;
        }
        private void RB_c2_Click(object sender, EventArgs e)
        {
            PTE = true;
            LB_MHz.Text = "MHz    (15.625 ~ 60.000)";
            GB_LPE.Enabled = true;
            GB_GLC.Enabled = true;
            label16.Enabled = true;
            label18.Enabled = true;
            label19.Enabled = true;
            LB_GLC.Enabled = true;
            CB_e0.Text = "c2";
            CB_c3.Visible = true;
            CB_c4.Visible = true;
            CB_e02.Visible = true;
            nUD_c3_mul.Visible = true;
            nUD_c4_mul.Visible = true;
            nUD_e02_mul.Visible = true;
            nUD_c3_div.Visible = true;
            nUD_c4_div.Visible = true;
            nUD_e02_div.Visible = true;
            CBB_c3_duty.Visible = true;
            CBB_c4_duty.Visible = true;
            CBB_e02_duty.Visible = true;
            CBB_c3_phase.Visible = true;
            CBB_c4_phase.Visible = true;
            CBB_e02_phase.Visible = true;

            nUD_c0_mul.Maximum = Mmax;
            nUD_c1_mul.Maximum = Mmax;
            nUD_e0_mul.Maximum = Mmax;
            nUD_c3_mul.Maximum = Mmax;
            nUD_c4_mul.Maximum = Mmax;
            nUD_e02_mul.Maximum = Mmax;
            nUD_c0_div.Maximum = NCML;
            nUD_c1_div.Maximum = NCML;
            nUD_e0_div.Maximum = NCML;
            nUD_c3_div.Maximum = NCML;
            nUD_c4_div.Maximum = NCML;
            nUD_e02_div.Maximum = NCML;

            CB_c0.Enabled = true;
            CB_c1.Enabled = true;
            CB_e0.Enabled = false;
            CB_c3.Enabled = true;
            CB_c4.Enabled = true;
            CB_e02.Enabled = true;
            CB_c0.Checked = false;
            CB_c1.Checked = false;
            CB_e0.Checked = true;
            CB_c3.Checked = false;
            CB_c4.Checked = false;
            CB_e02.Checked = false;

            if (inclk_freq > 60)
            {
                inclk_freq = 60;
                TB_inclk.Text = "60.000";
            }

            saveenabled = RefreshData();
            //LB_group.Text = "(n,m,c0,c1,e0,c3,c4,e02)";
            BT_Save.Enabled = saveenabled;
        }
        private void RB_c3_Click(object sender, EventArgs e)
        {
            PTE = true;
            LB_MHz.Text = "MHz    (15.625 ~ 60.000)";
            GB_LPE.Enabled = true;
            GB_GLC.Enabled = true;
            label16.Enabled = true;
            label18.Enabled = true;
            label19.Enabled = true;
            LB_GLC.Enabled = true;
            CB_e0.Text = "c2";
            CB_c3.Visible = true;
            CB_c4.Visible = true;
            CB_e02.Visible = true;
            nUD_c3_mul.Visible = true;
            nUD_c4_mul.Visible = true;
            nUD_e02_mul.Visible = true;
            nUD_c3_div.Visible = true;
            nUD_c4_div.Visible = true;
            nUD_e02_div.Visible = true;
            CBB_c3_duty.Visible = true;
            CBB_c4_duty.Visible = true;
            CBB_e02_duty.Visible = true;
            CBB_c3_phase.Visible = true;
            CBB_c4_phase.Visible = true;
            CBB_e02_phase.Visible = true;

            nUD_c0_mul.Maximum = Mmax;
            nUD_c1_mul.Maximum = Mmax;
            nUD_e0_mul.Maximum = Mmax;
            nUD_c3_mul.Maximum = Mmax;
            nUD_c4_mul.Maximum = Mmax;
            nUD_e02_mul.Maximum = Mmax;
            nUD_c0_div.Maximum = NCML;
            nUD_c1_div.Maximum = NCML;
            nUD_e0_div.Maximum = NCML;
            nUD_c3_div.Maximum = NCML;
            nUD_c4_div.Maximum = NCML;
            nUD_e02_div.Maximum = NCML;

            CB_c0.Enabled = true;
            CB_c1.Enabled = true;
            CB_e0.Enabled = true;
            CB_c3.Enabled = false;
            CB_c4.Enabled = true;
            CB_e02.Enabled = true;
            CB_c0.Checked = false;
            CB_c1.Checked = false;
            CB_e0.Checked = false;
            CB_c3.Checked = true;
            CB_c4.Checked = false;
            CB_e02.Checked = false;

            if (inclk_freq > 60)
            {
                inclk_freq = 60;
                TB_inclk.Text = "60.000";
            }

            saveenabled = RefreshData();
            //LB_group.Text = "(n,m,c0,c1,e0,c3,c4,e02)";
            BT_Save.Enabled = saveenabled;
        }
        private void RB_c4_Click(object sender, EventArgs e)
        {
            PTE = true;
            LB_MHz.Text = "MHz    (15.625 ~ 60.000)";
            GB_LPE.Enabled = true;
            GB_GLC.Enabled = true;
            label16.Enabled = true;
            label18.Enabled = true;
            label19.Enabled = true;
            LB_GLC.Enabled = true;
            CB_e0.Text = "c2";
            CB_c3.Visible = true;
            CB_c4.Visible = true;
            CB_e02.Visible = true;
            nUD_c3_mul.Visible = true;
            nUD_c4_mul.Visible = true;
            nUD_e02_mul.Visible = true;
            nUD_c3_div.Visible = true;
            nUD_c4_div.Visible = true;
            nUD_e02_div.Visible = true;
            CBB_c3_duty.Visible = true;
            CBB_c4_duty.Visible = true;
            CBB_e02_duty.Visible = true;
            CBB_c3_phase.Visible = true;
            CBB_c4_phase.Visible = true;
            CBB_e02_phase.Visible = true;

            nUD_c0_mul.Maximum = Mmax;
            nUD_c1_mul.Maximum = Mmax;
            nUD_e0_mul.Maximum = Mmax;
            nUD_c3_mul.Maximum = Mmax;
            nUD_c4_mul.Maximum = Mmax;
            nUD_e02_mul.Maximum = Mmax;
            nUD_c0_div.Maximum = NCML;
            nUD_c1_div.Maximum = NCML;
            nUD_e0_div.Maximum = NCML;
            nUD_c3_div.Maximum = NCML;
            nUD_c4_div.Maximum = NCML;
            nUD_e02_div.Maximum = NCML;

            CB_c0.Enabled = true;
            CB_c1.Enabled = true;
            CB_e0.Enabled = true;
            CB_c3.Enabled = true;
            CB_c4.Enabled = false;
            CB_e02.Enabled = true;
            CB_c0.Checked = false;
            CB_c1.Checked = false;
            CB_e0.Checked = false;
            CB_c3.Checked = false;
            CB_c4.Checked = true;
            CB_e02.Checked = false;

            if (inclk_freq > 60)
            {
                inclk_freq = 60;
                TB_inclk.Text = "60.000";
            }

            saveenabled = RefreshData();
            //LB_group.Text = "(n,m,c0,c1,e0,c3,c4,e02)";
            BT_Save.Enabled = saveenabled;
        }
        private void RB_e02_Click(object sender, EventArgs e)
        {
            PTE = true;
            LB_MHz.Text = "MHz    (15.625 ~ 60.000)";
            GB_LPE.Enabled = true;
            GB_GLC.Enabled = true;
            label16.Enabled = true;
            label18.Enabled = true;
            label19.Enabled = true;
            LB_GLC.Enabled = true;
            CB_e0.Text = "c2";
            CB_c3.Visible = true;
            CB_c4.Visible = true;
            CB_e02.Visible = true;
            nUD_c3_mul.Visible = true;
            nUD_c4_mul.Visible = true;
            nUD_e02_mul.Visible = true;
            nUD_c3_div.Visible = true;
            nUD_c4_div.Visible = true;
            nUD_e02_div.Visible = true;
            CBB_c3_duty.Visible = true;
            CBB_c4_duty.Visible = true;
            CBB_e02_duty.Visible = true;
            CBB_c3_phase.Visible = true;
            CBB_c4_phase.Visible = true;
            CBB_e02_phase.Visible = true;

            nUD_c0_mul.Maximum = Mmax;
            nUD_c1_mul.Maximum = Mmax;
            nUD_e0_mul.Maximum = Mmax;
            nUD_c3_mul.Maximum = Mmax;
            nUD_c4_mul.Maximum = Mmax;
            nUD_e02_mul.Maximum = Mmax;
            nUD_c0_div.Maximum = NCML;
            nUD_c1_div.Maximum = NCML;
            nUD_e0_div.Maximum = NCML;
            nUD_c3_div.Maximum = NCML;
            nUD_c4_div.Maximum = NCML;
            nUD_e02_div.Maximum = NCML;

            CB_c0.Enabled = true;
            CB_c1.Enabled = true;
            CB_e0.Enabled = true;
            CB_c3.Enabled = true;
            CB_c4.Enabled = true;
            CB_e02.Enabled = false;
            CB_c0.Checked = false;
            CB_c1.Checked = false;
            CB_e0.Checked = false;
            CB_c3.Checked = false;
            CB_c4.Checked = false;
            CB_e02.Checked = true;

            if (inclk_freq > 60)
            {
                inclk_freq = 60;
                TB_inclk.Text = "60.000";
            }

            saveenabled = RefreshData();
            //LB_group.Text = "(n,m,c0,c1,e0,c3,c4,e02)";
            BT_Save.Enabled = saveenabled;
        }
        private void RB_N_Click(object sender, EventArgs e)
        {
            PTE = true;
            LB_MHz.Text = "MHz    (15.625 ~ 120.000)";
            GB_LPE.Enabled = true;
            GB_GLC.Enabled = true;
            label16.Enabled = true;
            label18.Enabled = true;
            label19.Enabled = true;
            LB_GLC.Enabled = true;
            CB_e0.Text = "c2";
            CB_c3.Visible = true;
            CB_c4.Visible = true;
            CB_e02.Visible = true;
            nUD_c3_mul.Visible = true;
            nUD_c4_mul.Visible = true;
            nUD_e02_mul.Visible = true;
            nUD_c3_div.Visible = true;
            nUD_c4_div.Visible = true;
            nUD_e02_div.Visible = true;
            CBB_c3_duty.Visible = true;
            CBB_c4_duty.Visible = true;
            CBB_e02_duty.Visible = true;
            CBB_c3_phase.Visible = true;
            CBB_c4_phase.Visible = true;
            CBB_e02_phase.Visible = true;

            nUD_c0_mul.Maximum = Mmax;
            nUD_c1_mul.Maximum = Mmax;
            nUD_e0_mul.Maximum = Mmax;
            nUD_c3_mul.Maximum = Mmax;
            nUD_c4_mul.Maximum = Mmax;
            nUD_e02_mul.Maximum = Mmax;
            nUD_c0_div.Maximum = NCM;
            nUD_c1_div.Maximum = NCM;
            nUD_e0_div.Maximum = NCM;
            nUD_c3_div.Maximum = NCM;
            nUD_c4_div.Maximum = NCM;
            nUD_e02_div.Maximum = NCM;

            CB_c0.Enabled = true;
            CB_c1.Enabled = true;
            CB_e0.Enabled = true;
            CB_c3.Enabled = true;
            CB_c4.Enabled = true;
            CB_e02.Enabled = true;
            CB_c0.Checked = false;
            CB_c1.Checked = false;
            CB_e0.Checked = false;
            CB_c3.Checked = false;
            CB_c4.Checked = false;
            CB_e02.Checked = false;

            saveenabled = RefreshData();
            //LB_group.Text = "(n,m,c0,c1,e0,c3,c4,e02)";
            BT_Save.Enabled = saveenabled;
        }
        private void RB_auto_Click(object sender, EventArgs e)
        {
            PTE = true;
            LB_MHz.Text = "MHz    (15.625 ~ 120.000)";
            GB_LPE.Enabled = true;
            GB_GLC.Enabled = true;
            label16.Enabled = true;
            label18.Enabled = true;
            label19.Enabled = true;
            LB_GLC.Enabled = true;
            CB_e0.Text = "c2";
            CB_c3.Visible = true;
            CB_c4.Visible = true;
            CB_e02.Visible = true;
            nUD_c3_mul.Visible = true;
            nUD_c4_mul.Visible = true;
            nUD_e02_mul.Visible = true;
            nUD_c3_div.Visible = true;
            nUD_c4_div.Visible = true;
            nUD_e02_div.Visible = true;
            CBB_c3_duty.Visible = true;
            CBB_c4_duty.Visible = true;
            CBB_e02_duty.Visible = true;
            CBB_c3_phase.Visible = true;
            CBB_c4_phase.Visible = true;
            CBB_e02_phase.Visible = true;

            nUD_c0_mul.Maximum = Mmax;
            nUD_c1_mul.Maximum = Mmax;
            nUD_e0_mul.Maximum = Mmax;
            nUD_c3_mul.Maximum = Mmax;
            nUD_c4_mul.Maximum = Mmax;
            nUD_e02_mul.Maximum = Mmax;
            nUD_c0_div.Maximum = NCM;
            nUD_c1_div.Maximum = NCM;
            nUD_e0_div.Maximum = NCM;
            nUD_c3_div.Maximum = NCM;
            nUD_c4_div.Maximum = NCM;
            nUD_e02_div.Maximum = NCM;

            CB_c0.Enabled = true;
            CB_c1.Enabled = true;
            CB_e0.Enabled = true;
            CB_c3.Enabled = true;
            CB_c4.Enabled = true;
            CB_e02.Enabled = true;
            CB_c0.Checked = false;
            CB_c1.Checked = false;
            CB_e0.Checked = false;
            CB_c3.Checked = false;
            CB_c4.Checked = false;
            CB_e02.Checked = false;
            BT_Save.Enabled = saveenabled;
        }

        /*
        private void CB_pfd_load_Click(object sender, EventArgs e)
        {
            groupBox2.Enabled = CB_pfd_load.Checked;
        }
        */

        private void CB_pllena_CheckedChanged(object sender, EventArgs e)
        {
            BT_Save.Enabled = saveenabled;
            if (saveenabled)
                LB_message_output.Text = "";
        }
        private void CB_areset_CheckedChanged(object sender, EventArgs e)
        {
            BT_Save.Enabled = saveenabled;
            if (saveenabled)
                LB_message_output.Text = "";
        }
        private void CB_pfd_load_CheckedChanged(object sender, EventArgs e)
        {
            BT_Save.Enabled = saveenabled;
            if (saveenabled)
                LB_message_output.Text = "";
        }
        private void CB_locked_CheckedChanged(object sender, EventArgs e)
        {
            BT_Save.Enabled = saveenabled;
            if (saveenabled)
                LB_message_output.Text = "";
        }

        private void RB_pfdena_CheckedChanged(object sender, EventArgs e)
        {
            BT_Save.Enabled = saveenabled;
        }
        private void RB_load_CheckedChanged(object sender, EventArgs e)
        {
            //DrawPLL();
            //pictureBox.Refresh();
        }

        private void CB_c0_CheckedChanged(object sender, EventArgs e)
        {
            nUD_c0_mul.Enabled = CB_c0.Checked && CB_c0.Enabled;
            nUD_c0_div.Enabled = CB_c0.Checked && CB_c0.Enabled;
            //CBB_c0_duty.Enabled = CB_c0.Checked;
            //CBB_c0_phase.Enabled = CB_c0.Checked;
            LB_c0_freq.Enabled = CB_c0.Checked;
            //label11.Enabled = CB_c0.Checked;

            if (nUD_c0_mul.Enabled == false)
                nUD_c0_mul.Value = 1;
            if (nUD_c0_div.Enabled == false)
                nUD_c0_div.Value = 1;

            saveenabled = RefreshData();
            BT_Save.Enabled = saveenabled;
        }
        private void CB_c0_EnabledChanged(object sender, EventArgs e)
        {
            nUD_c0_mul.Enabled = CB_c0.Checked && CB_c0.Enabled;
            nUD_c0_div.Enabled = CB_c0.Checked && CB_c0.Enabled;
            //CBB_c0_duty.Enabled = CB_c0.Checked;
            //CBB_c0_phase.Enabled = CB_c0.Checked;

            if (nUD_c0_mul.Enabled == false)
                nUD_c0_mul.Value = 1;
            if (nUD_c0_div.Enabled == false)
                nUD_c0_div.Value = 1;
        }
        private void CB_c1_CheckedChanged(object sender, EventArgs e)
        {
            nUD_c1_mul.Enabled = CB_c1.Checked && CB_c1.Enabled;
            nUD_c1_div.Enabled = CB_c1.Checked && CB_c1.Enabled;
            //CBB_c1_duty.Enabled = CB_c1.Checked;
            //CBB_c1_phase.Enabled = CB_c1.Checked;
            LB_c1_freq.Enabled = CB_c1.Checked;
            //label12.Enabled = CB_c1.Checked;

            if (nUD_c1_mul.Enabled == false)
                nUD_c1_mul.Value = 1;
            if (nUD_c1_div.Enabled == false)
                nUD_c1_div.Value = 1;

            saveenabled = RefreshData();
            BT_Save.Enabled = saveenabled;
        }
        private void CB_c1_EnabledChanged(object sender, EventArgs e)
        {
            nUD_c1_mul.Enabled = CB_c1.Checked && CB_c1.Enabled;
            nUD_c1_div.Enabled = CB_c1.Checked && CB_c1.Enabled;
            //CBB_c1_duty.Enabled = CB_c1.Checked;
            //CBB_c1_phase.Enabled = CB_c1.Checked;

            if (nUD_c1_mul.Enabled == false)
                nUD_c1_mul.Value = 1;
            if (nUD_c1_div.Enabled == false)
                nUD_c1_div.Value = 1;
        }
        private void CB_e0_CheckedChanged(object sender, EventArgs e)
        {
            nUD_e0_mul.Enabled = CB_e0.Checked && CB_e0.Enabled;
            nUD_e0_div.Enabled = CB_e0.Checked && CB_e0.Enabled;
            //CBB_e0_duty.Enabled = CB_e0.Checked;
            //CBB_e0_phase.Enabled = CB_e0.Checked;
            LB_e0_freq.Enabled = CB_e0.Checked;
            //label13.Enabled = CB_e0.Checked;

            if (nUD_e0_mul.Enabled == false)
                nUD_e0_mul.Value = 1;
            if (nUD_e0_div.Enabled == false)
                nUD_e0_div.Value = 1;

            saveenabled = RefreshData();
            BT_Save.Enabled = saveenabled;
        }
        private void CB_e0_EnabledChanged(object sender, EventArgs e)
        {
            nUD_e0_mul.Enabled = CB_e0.Checked && CB_e0.Enabled;
            nUD_e0_div.Enabled = CB_e0.Checked && CB_e0.Enabled;
            //CBB_e0_duty.Enabled = CB_e0.Checked;
            //CBB_e0_phase.Enabled = CB_e0.Checked;

            if (nUD_e0_mul.Enabled == false)
                nUD_e0_mul.Value = 1;
            if (nUD_e0_div.Enabled == false)
                nUD_e0_div.Value = 1;
        }
        private void CB_c3_CheckedChanged(object sender, EventArgs e)
        {
            nUD_c3_mul.Enabled = CB_c3.Checked && CB_c3.Enabled;
            nUD_c3_div.Enabled = CB_c3.Checked && CB_c3.Enabled;
            //CBB_c0_duty.Enabled = CB_c0.Checked;
            //CBB_c0_phase.Enabled = CB_c0.Checked;
            LB_c3_freq.Enabled = CB_c3.Checked;
            //label11.Enabled = CB_c0.Checked;

            if (nUD_c3_mul.Enabled == false)
                nUD_c3_mul.Value = 1;
            if (nUD_c3_div.Enabled == false)
                nUD_c3_div.Value = 1;

            saveenabled = RefreshData();
            BT_Save.Enabled = saveenabled;
        }
        private void CB_c3_EnabledChanged(object sender, EventArgs e)
        {
            nUD_c3_mul.Enabled = CB_c3.Checked && CB_c3.Enabled;
            nUD_c3_div.Enabled = CB_c3.Checked && CB_c3.Enabled;
            //CBB_c0_duty.Enabled = CB_c0.Checked;
            //CBB_c0_phase.Enabled = CB_c0.Checked;

            if (nUD_c3_mul.Enabled == false)
                nUD_c3_mul.Value = 1;
            if (nUD_c3_div.Enabled == false)
                nUD_c3_div.Value = 1;
        }
        private void CB_c4_CheckedChanged(object sender, EventArgs e)
        {
            nUD_c4_mul.Enabled = CB_c4.Checked && CB_c4.Enabled;
            nUD_c4_div.Enabled = CB_c4.Checked && CB_c4.Enabled;
            //CBB_c0_duty.Enabled = CB_c0.Checked;
            //CBB_c0_phase.Enabled = CB_c0.Checked;
            LB_c4_freq.Enabled = CB_c4.Checked;
            //label11.Enabled = CB_c0.Checked;

            if (nUD_c4_mul.Enabled == false)
                nUD_c4_mul.Value = 1;
            if (nUD_c4_div.Enabled == false)
                nUD_c4_div.Value = 1;

            saveenabled = RefreshData();
            BT_Save.Enabled = saveenabled;
        }
        private void CB_c4_EnabledChanged(object sender, EventArgs e)
        {
            nUD_c4_mul.Enabled = CB_c4.Checked && CB_c4.Enabled;
            nUD_c4_div.Enabled = CB_c4.Checked && CB_c4.Enabled;
            //CBB_c0_duty.Enabled = CB_c0.Checked;
            //CBB_c0_phase.Enabled = CB_c0.Checked;

            if (nUD_c4_mul.Enabled == false)
                nUD_c4_mul.Value = 1;
            if (nUD_c4_div.Enabled == false)
                nUD_c4_div.Value = 1;
        }
        private void CB_e02_CheckedChanged(object sender, EventArgs e)
        {
            nUD_e02_mul.Enabled = CB_e02.Checked && CB_e02.Enabled;
            nUD_e02_div.Enabled = CB_e02.Checked && CB_e02.Enabled;
            //CBB_c0_duty.Enabled = CB_c0.Checked;
            //CBB_c0_phase.Enabled = CB_c0.Checked;
            LB_e02_freq.Enabled = CB_e02.Checked;
            //label11.Enabled = CB_c0.Checked;

            if (nUD_e02_mul.Enabled == false)
                nUD_e02_mul.Value = 1;
            if (nUD_e02_div.Enabled == false)
                nUD_e02_div.Value = 1;

            saveenabled = RefreshData();
            BT_Save.Enabled = saveenabled;
        }
        private void CB_e02_EnabledChanged(object sender, EventArgs e)
        {
            nUD_e02_mul.Enabled = CB_e02.Checked && CB_e02.Enabled;
            nUD_e02_div.Enabled = CB_e02.Checked && CB_e02.Enabled;
            //CBB_c0_duty.Enabled = CB_c0.Checked;
            //CBB_c0_phase.Enabled = CB_c0.Checked;

            if (nUD_e02_mul.Enabled == false)
                nUD_e02_mul.Value = 1;
            if (nUD_e02_div.Enabled == false)
                nUD_e02_div.Value = 1;
        }
        private void nUD_c0_mul_ValueChanged(object sender, EventArgs e)
        {
            c0_mul = Convert.ToInt32(nUD_c0_mul.Value);
            saveenabled = RefreshData();
            BT_Save.Enabled = saveenabled;
        }
        private void nUD_c1_mul_ValueChanged(object sender, EventArgs e)
        {
            c1_mul = Convert.ToInt32(nUD_c1_mul.Value);
            saveenabled = RefreshData();
            BT_Save.Enabled = saveenabled;
        }
        private void nUD_e0_mul_ValueChanged(object sender, EventArgs e)
        {
            e0_mul = Convert.ToInt32(nUD_e0_mul.Value);
            saveenabled = RefreshData();
            BT_Save.Enabled = saveenabled;
        }
        private void nUD_c3_mul_ValueChanged(object sender, EventArgs e)
        {
            c3_mul = Convert.ToInt32(nUD_c3_mul.Value);
            saveenabled = RefreshData();
            BT_Save.Enabled = saveenabled;
        }
        private void nUD_c4_mul_ValueChanged(object sender, EventArgs e)
        {
            c4_mul = Convert.ToInt32(nUD_c4_mul.Value);
            saveenabled = RefreshData();
            BT_Save.Enabled = saveenabled;
        }
        private void nUD_e02_mul_ValueChanged(object sender, EventArgs e)
        {
            e02_mul = Convert.ToInt32(nUD_e02_mul.Value);
            saveenabled = RefreshData();
            BT_Save.Enabled = saveenabled;
        }
        private void nUD_c0_div_ValueChanged(object sender, EventArgs e)
        {
            c0_div = Convert.ToInt32(nUD_c0_div.Value);
            saveenabled = RefreshData();
            BT_Save.Enabled = saveenabled;
        }
        private void nUD_c1_div_ValueChanged(object sender, EventArgs e)
        {
            c1_div = Convert.ToInt32(nUD_c1_div.Value);
            saveenabled = RefreshData();
            BT_Save.Enabled = saveenabled;
        }
        private void nUD_e0_div_ValueChanged(object sender, EventArgs e)
        {
            e0_div = Convert.ToInt32(nUD_e0_div.Value);
            saveenabled = RefreshData();
            BT_Save.Enabled = saveenabled;
        }
        private void nUD_c3_div_ValueChanged(object sender, EventArgs e)
        {
            c3_div = Convert.ToInt32(nUD_c3_div.Value);
            saveenabled = RefreshData();
            BT_Save.Enabled = saveenabled;
        }
        private void nUD_c4_div_ValueChanged(object sender, EventArgs e)
        {
            c4_div = Convert.ToInt32(nUD_c4_div.Value);
            saveenabled = RefreshData();
            BT_Save.Enabled = saveenabled;
        }
        private void nUD_e02_div_ValueChanged(object sender, EventArgs e)
        {
            e02_div = Convert.ToInt32(nUD_e02_div.Value);
            saveenabled = RefreshData();
            BT_Save.Enabled = saveenabled;
        }

        private void CBB_c0_duty_SelectedIndexChanged(object sender, EventArgs e)
        {
            SelectedIndex_c0 = CBB_c0_duty.SelectedIndex;
            c0_duty = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].rate * 100;
            n = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].n;
            m = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].m;
            c0_m = sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m;

            phase_temp = CBB_c0_phase.Items.Count;
            CBB_c0_phase.Items.Clear();
            //MessageBox.Show("CBB_c0_duty_SelectedIndexChanged");//ly_mod
            for (i = 0; i < sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m * 8; i++)
            {
                CBB_c0_phase.Items.Add(Convert.ToDouble((double)i * 360 / sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m / 8).ToString("f3"));
            }
            if (phase_temp == CBB_c0_phase.Items.Count)
                CBB_c0_phase.SelectedIndex = SelectedIndex_c0p;
            else
                CBB_c0_phase.SelectedIndex = 0;
            //OutPut();
        }
        private void CBB_c1_duty_SelectedIndexChanged(object sender, EventArgs e)
        {
            SelectedIndex_c1 = CBB_c1_duty.SelectedIndex;
            c1_duty = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].rate * 100;
            n = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].n;
            m = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].m;
            c1_m = sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m;

            phase_temp = CBB_c1_phase.Items.Count;
            CBB_c1_phase.Items.Clear();
            //MessageBox.Show("CBB_c1_duty_SelectedIndexChanged");//ly_mod
            for (i = 0; i < sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m * 8; i++)
            {
                CBB_c1_phase.Items.Add(Convert.ToDouble((double)i * 360 / sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m / 8).ToString("f3"));
            }
            if (phase_temp == CBB_c1_phase.Items.Count)
                CBB_c1_phase.SelectedIndex = SelectedIndex_c1p;
            else
                CBB_c1_phase.SelectedIndex = 0;
            //OutPut();
        }
        private void CBB_e0_duty_SelectedIndexChanged(object sender, EventArgs e)
        {
            SelectedIndex_e0 = CBB_e0_duty.SelectedIndex;
            e0_duty = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].rate * 100;
            n = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].n;
            m = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].m;
            e0_m = sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m;

            phase_temp = CBB_e0_phase.Items.Count;
            CBB_e0_phase.Items.Clear();
            //MessageBox.Show("CBB_e0_duty_SelectedIndexChanged");//ly_mod
            for (i = 0; i < sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m * 8; i++)
            {
                CBB_e0_phase.Items.Add(Convert.ToDouble((double)i * 360 / sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m / 8).ToString("f3"));
            }
            if (phase_temp == CBB_e0_phase.Items.Count)
                CBB_e0_phase.SelectedIndex = SelectedIndex_e0p;
            else
                CBB_e0_phase.SelectedIndex = 0;
            //OutPut();
        }
        private void CBB_c3_duty_SelectedIndexChanged(object sender, EventArgs e)
        {
            SelectedIndex_c3 = CBB_c3_duty.SelectedIndex;
            c3_duty = sort_duty_c3_2[CBB_c3_duty.SelectedIndex].rate * 100;
            n = sort_duty_c3_2[CBB_c3_duty.SelectedIndex].n;
            m = sort_duty_c3_2[CBB_c3_duty.SelectedIndex].m;
            c3_m = sort_duty_c3_2[CBB_c3_duty.SelectedIndex].c3m;

            phase_temp = CBB_c3_phase.Items.Count;
            CBB_c3_phase.Items.Clear();
            //MessageBox.Show("CBB_c3_duty_SelectedIndexChanged");//ly_mod
            for (i = 0; i < sort_duty_c3_2[CBB_c3_duty.SelectedIndex].c3m * 8; i++)
            {
                CBB_c3_phase.Items.Add(Convert.ToDouble((double)i * 360 / sort_duty_c3_2[CBB_c3_duty.SelectedIndex].c3m / 8).ToString("f3"));
            }
            if (phase_temp == CBB_c3_phase.Items.Count)
                CBB_c3_phase.SelectedIndex = SelectedIndex_c3p;
            else
                CBB_c3_phase.SelectedIndex = 0;
            //OutPut();
        }
        private void CBB_c4_duty_SelectedIndexChanged(object sender, EventArgs e)
        {
            SelectedIndex_c4 = CBB_c4_duty.SelectedIndex;
            c4_duty = sort_duty_c4_2[CBB_c4_duty.SelectedIndex].rate * 100;
            n = sort_duty_c4_2[CBB_c4_duty.SelectedIndex].n;
            m = sort_duty_c4_2[CBB_c4_duty.SelectedIndex].m;
            c4_m = sort_duty_c4_2[CBB_c4_duty.SelectedIndex].c4m;

            phase_temp = CBB_c4_phase.Items.Count;
            CBB_c4_phase.Items.Clear();
            //MessageBox.Show("CBB_c4_duty_SelectedIndexChanged");//ly_mod
            for (i = 0; i < sort_duty_c4_2[CBB_c4_duty.SelectedIndex].c4m * 8; i++)
            {
                CBB_c4_phase.Items.Add(Convert.ToDouble((double)i * 360 / sort_duty_c4_2[CBB_c4_duty.SelectedIndex].c4m / 8).ToString("f3"));
            }
            if (phase_temp == CBB_c4_phase.Items.Count)
                CBB_c4_phase.SelectedIndex = SelectedIndex_c4p;
            else
                CBB_c4_phase.SelectedIndex = 0;
            //OutPut();
        }
        private void CBB_e02_duty_SelectedIndexChanged(object sender, EventArgs e)
        {
            SelectedIndex_e02 = CBB_e02_duty.SelectedIndex;
            e02_duty = sort_duty_e02_2[CBB_e02_duty.SelectedIndex].rate * 100;
            n = sort_duty_e02_2[CBB_e02_duty.SelectedIndex].n;
            m = sort_duty_e02_2[CBB_e02_duty.SelectedIndex].m;
            e02_m = sort_duty_e02_2[CBB_e02_duty.SelectedIndex].e02m;

            phase_temp = CBB_e02_phase.Items.Count;
            CBB_e02_phase.Items.Clear();
            //MessageBox.Show("CBB_e02_duty_SelectedIndexChanged");//ly_mod
            for (i = 0; i < sort_duty_e02_2[CBB_e02_duty.SelectedIndex].e02m * 8; i++)
            {
                CBB_e02_phase.Items.Add(Convert.ToDouble((double)i * 360 / sort_duty_e02_2[CBB_e02_duty.SelectedIndex].e02m / 8).ToString("f3"));
            }
            if (phase_temp == CBB_e02_phase.Items.Count)
                CBB_e02_phase.SelectedIndex = SelectedIndex_e02p;
            else
                CBB_e02_phase.SelectedIndex = 0;
            //OutPut();
        }

        private void CBB_c0_duty_SelectionChangeCommitted(object sender, EventArgs e)
        {
            saveenabled = RefreshData2(0);
            BT_Save.Enabled = saveenabled;
        }
        private void CBB_c1_duty_SelectionChangeCommitted(object sender, EventArgs e)
        {
            saveenabled = RefreshData2(1);
            BT_Save.Enabled = saveenabled;
        }
        private void CBB_e0_duty_SelectionChangeCommitted(object sender, EventArgs e)
        {
            saveenabled = RefreshData2(2);
            BT_Save.Enabled = saveenabled;
        }
        private void CBB_c3_duty_SelectionChangeCommitted(object sender, EventArgs e)
        {
            saveenabled = RefreshData2(3);
            BT_Save.Enabled = saveenabled;
        }
        private void CBB_c4_duty_SelectionChangeCommitted(object sender, EventArgs e)
        {
            saveenabled = RefreshData2(4);
            BT_Save.Enabled = saveenabled;
        }
        private void CBB_e02_duty_SelectionChangeCommitted(object sender, EventArgs e)
        {
            saveenabled = RefreshData2(5);
            BT_Save.Enabled = saveenabled;
        }

        private void CBB_c0_phase_SelectedIndexChanged(object sender, EventArgs e)
        {
            SelectedIndex_c0p = CBB_c0_phase.SelectedIndex;
            c0_phase = (double)CBB_c0_phase.SelectedIndex * 360 / sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m / 8;
            //DrawPLL();
            //pictureBox.Refresh();
        }
        private void CBB_c1_phase_SelectedIndexChanged(object sender, EventArgs e)
        {
            SelectedIndex_c1p = CBB_c1_phase.SelectedIndex;
            c1_phase = (double)CBB_c1_phase.SelectedIndex * 360 / sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m / 8;
            //DrawPLL();
            //pictureBox.Refresh();
        }
        private void CBB_e0_phase_SelectedIndexChanged(object sender, EventArgs e)
        {
            SelectedIndex_e0p = CBB_e0_phase.SelectedIndex;
            e0_phase = (double)CBB_e0_phase.SelectedIndex * 360 / sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m / 8;
            //DrawPLL();
            //pictureBox.Refresh();
        }
        private void CBB_c3_phase_SelectedIndexChanged(object sender, EventArgs e)
        {
            SelectedIndex_c3p = CBB_c3_phase.SelectedIndex;
            c3_phase = (double)CBB_c3_phase.SelectedIndex * 360 / sort_duty_c3_2[CBB_c3_duty.SelectedIndex].c3m / 8;
            //DrawPLL();
            //pictureBox.Refresh();
        }
        private void CBB_c4_phase_SelectedIndexChanged(object sender, EventArgs e)
        {
            SelectedIndex_c4p = CBB_c4_phase.SelectedIndex;
            c4_phase = (double)CBB_c4_phase.SelectedIndex * 360 / sort_duty_c4_2[CBB_c4_duty.SelectedIndex].c4m / 8;
            //DrawPLL();
            //pictureBox.Refresh();
        }
        private void CBB_e02_phase_SelectedIndexChanged(object sender, EventArgs e)
        {
            SelectedIndex_e02p = CBB_e02_phase.SelectedIndex;
            e02_phase = (double)CBB_e02_phase.SelectedIndex * 360 / sort_duty_e02_2[CBB_e02_duty.SelectedIndex].e02m / 8;
            //DrawPLL();
            //pictureBox.Refresh();
        }
        private void CBB_c0_phase_SelectionChangeCommitted(object sender, EventArgs e)
        {
            //LB_message_output.Text = "";
            BT_Save.Enabled = saveenabled;
            if (saveenabled)
                LB_message_output.Text = "";
        }
        private void CBB_c1_phase_SelectionChangeCommitted(object sender, EventArgs e)
        {
            BT_Save.Enabled = saveenabled;
            if (saveenabled)
                LB_message_output.Text = "";
        }
        private void CBB_e0_phase_SelectionChangeCommitted(object sender, EventArgs e)
        {
            BT_Save.Enabled = saveenabled;
            if (saveenabled)
                LB_message_output.Text = "";
        }
        private void CBB_c3_phase_SelectionChangeCommitted(object sender, EventArgs e)
        {
            BT_Save.Enabled = saveenabled;
            if (saveenabled)
                LB_message_output.Text = "";
        }
        private void CBB_c4_phase_SelectionChangeCommitted(object sender, EventArgs e)
        {
            BT_Save.Enabled = saveenabled;
            if (saveenabled)
                LB_message_output.Text = "";
        }
        private void CBB_e02_phase_SelectionChangeCommitted(object sender, EventArgs e)
        {
            BT_Save.Enabled = saveenabled;
            if (saveenabled)
                LB_message_output.Text = "";
        }
        #region 
        private void BT_Save_Click(object sender, EventArgs e)
        {
            if (bsave)
            {
                if (RB_mode0.Checked || RB_N.Checked)
                    operation_mode = "NO_COMPENSATION";
                else if (RB_mode1.Checked || RB_e02.Checked)
                    operation_mode = "ZERO_DELAY_BUFFER";
                else
                    operation_mode = "NORMAL";

                string dir = System.IO.Path.GetDirectoryName(saveFile);
                if (!System.IO.Directory.Exists(dir))
                    System.IO.Directory.CreateDirectory(dir);

                StreamWriter sw = new StreamWriter(saveFile);

                sw.WriteLine("//#PLL");
                sw.WriteLine("//#N_m=" + n);
                sw.WriteLine("//#M_m=" + m);
                sw.WriteLine("//#locked_window_size=" + (RB_LPE0.Checked ? 0 : RB_LPE1.Checked ? 1 : 2));
                sw.WriteLine("//#locked_counter=" + (RB_GLC0.Checked ? 0 : RB_GLC1.Checked ? 1 : RB_GLC2.Checked ? 2 : 3));
                //                sw.WriteLine("//#IRRAD_mode=YES");//mark有条件，目前不能这么改。
                if (PTE)
                {
                    sw.WriteLine("//#IRRAD_mode=YES");//mark
                    if (CB_c0.Checked)
                        sw.WriteLine("//#clk0_ali=" + (LCM(m_real, c0_m) / m_real + 1));
                    if (CB_c1.Checked)
                        sw.WriteLine("//#clk1_ali=" + (LCM(m_real, c1_m) / m_real + 1));
                    if (CB_e0.Checked)
                        sw.WriteLine("//#clk2_ali=" + (LCM(m_real, e0_m) / m_real + 1));
                    if (CB_c3.Checked)
                        sw.WriteLine("//#clk3_ali=" + (LCM(m_real, c3_m) / m_real + 1));
                    if (CB_c4.Checked)
                        sw.WriteLine("//#clk4_ali=" + (LCM(m_real, c4_m) / m_real + 1));
                }
                sw.WriteLine("`timescale 1 ps / 1 ps");
                sw.WriteLine("module " + moduleName + "(");


                #region 生成对用户的接口
                if (CB_areset.Checked) sw.WriteLine("\tareset,");
                //if (fbinRadioBtn.Checked) sw.WriteLine("\tfbin,");
                sw.Write("\tinclk0");
                if (CB_pfd_load.Checked) sw.Write(",\n\tpfdena");
                if (CB_pllena.Checked) sw.Write(",\n\tpllena");
                if (CB_c0.Checked) sw.Write(",\n\tc0");
                if (CB_c1.Checked) sw.Write(",\n\tc1");
                if (CB_e0.Checked)
                {
                    if (PTE)
                        sw.Write(",\n\tc2");
                    else
                        sw.Write(",\n\te0");
                }
                if (PTE)
                {
                    if (CB_c3.Checked) sw.Write(",\n\tc3");
                    if (CB_c4.Checked) sw.Write(",\n\tc4");
                    if (CB_e02.Checked) sw.Write(",\n\te0");
                }
                if (CB_locked.Checked) sw.Write(",\n\tlocked");
                sw.Write(");\n\n");
                #endregion

                #region 生成对用户的接口定义
                if (CB_areset.Checked) sw.WriteLine("\tinput\tareset;");
                //if (fbinRadioBtn.Checked) sw.WriteLine("\tinput\tfbin;");
                sw.WriteLine("\tinput\tinclk0;");
                if (CB_pfd_load.Checked) sw.WriteLine("\tinput\tpfdena;");
                if (CB_pllena.Checked) sw.WriteLine("\tinput\tpllena;");
                if (CB_c0.Checked) sw.WriteLine("\toutput\tc0;");
                if (CB_c1.Checked) sw.WriteLine("\toutput\tc1;");
                if (CB_e0.Checked)
                {
                    if (PTE)
                        sw.WriteLine("\toutput\tc2;");
                    else
                        sw.WriteLine("\toutput\te0;");
                }
                if (PTE)
                {
                    if (CB_c3.Checked) sw.WriteLine("\toutput\tc3;");
                    if (CB_c4.Checked) sw.WriteLine("\toutput\tc4;");
                    if (CB_e02.Checked) sw.WriteLine("\toutput\te0;");
                }
                if (CB_locked.Checked) sw.WriteLine("\toutput\tlocked;");

                if (CB_c0.Checked || CB_c1.Checked || PTE && (CB_e0.Checked || CB_c3.Checked || CB_c4.Checked)) sw.WriteLine("\twire[5:0] wireC;");
                if (!PTE && CB_e0.Checked || PTE && CB_e02.Checked) sw.WriteLine("\twire[3:0] wireE;");
                if (CB_c0.Checked) sw.WriteLine("\tassign c0 = wireC[0];");
                if (CB_c1.Checked) sw.WriteLine("\tassign c1 = wireC[1];");
                if (CB_e0.Checked)
                {
                    if (PTE)
                        sw.WriteLine("\tassign c2 = wireC[2];");
                    else
                        sw.WriteLine("\tassign e0 = wireE[0];");
                }
                if (PTE)
                {
                    if (CB_c3.Checked) sw.WriteLine("\tassign c3 = wireC[3];");
                    if (CB_c4.Checked) sw.WriteLine("\tassign c4 = wireC[4];");
                    if (CB_e02.Checked) sw.WriteLine("\tassign e0 = wireE[0];");
                }

                #endregion

                #region 对底层PLL器件的实例化
                sw.WriteLine("	altpll	altpll_component (");
                sw.WriteLine("\t\t\t\t.inclk ({1'h0, inclk0}),");
                if (CB_pllena.Checked) sw.WriteLine("\t\t\t\t.pllena (pllena),");
                else sw.WriteLine("\t\t\t\t.pllena (1'b1),");
                if (CB_pfd_load.Checked) sw.WriteLine("\t\t\t\t.pfdena (pfdena),");
                else sw.WriteLine("\t\t\t\t.pfdena (1'b1),");

                if (CB_areset.Checked) sw.WriteLine("\t\t\t\t.areset (areset),");
                else sw.WriteLine("\t\t\t\t.areset (1'b0),");

                // 写输出时钟
                //string str = null;
                //if (CB_c0.Checked) str = "c0";
                //else str = "1'h0";
                //if (CB_c1.Checked) str = "c1," + str;
                //else str = "1'h0," + str;
                //if (str != null) sw.WriteLine("\t\t\t\t.clk ({1'h0,1'h0,1'h0,1'h0," + str + "}),");

                if (CB_c0.Checked || CB_c1.Checked || PTE && (CB_e0.Checked || CB_c3.Checked || CB_c4.Checked))
                    sw.WriteLine("\t\t\t\t.clk (wireC),");
                else
                    sw.WriteLine("\t\t\t\t.clk (),");

                if (CB_locked.Checked)
                    sw.WriteLine("\t\t\t\t.locked (locked),");
                else
                    sw.WriteLine("\t\t\t\t.locked (),");

                if (!PTE && CB_e0.Checked || PTE && CB_e02.Checked)
                    //sw.WriteLine("\t\t\t\t.extclk ({1'h0,1'h0,1'h0,e0}),");
                    sw.WriteLine("\t\t\t\t.extclk (wireE),");
                else
                    sw.WriteLine("\t\t\t\t.extclk (),");

                sw.Write("\t\t\t\t.activeclock (),\n\t\t\t\t.clkbad (),\n\t\t\t\t.clkena ({6{1'b1}}),\n");
                sw.Write("\t\t\t\t.clkloss (),\n\t\t\t\t.clkswitch (1'b0),\n\t\t\t\t.configupdate (1'b1),\n\t\t\t\t.enable0 (),\n");
                sw.Write("\t\t\t\t.enable1 (),\n\t\t\t\t.extclkena ({4{1'b1}}),\n\t\t\t\t.fbin (1'b1),\n");
                sw.Write("\t\t\t\t.fbout (),\n\t\t\t\t.phasecounterselect ({4{1'b1}}),\n\t\t\t\t.phasedone (),\n");
                sw.Write("\t\t\t\t.phasestep (1'b1),\n\t\t\t\t.phaseupdown (1'b1),\n\t\t\t\t.scanaclr (1'b0),\n");
                sw.Write("\t\t\t\t.scanclk (1'b0),\n\t\t\t\t.scanclkena (1'b1),\n\t\t\t\t.scandata (1'b0),\n\t\t\t\t.scandataout (),\n");
                sw.Write("\t\t\t\t.scandone (),\n\t\t\t\t.scanread (1'b0),\n\t\t\t\t.scanwrite (1'b0),\n\t\t\t\t.sclkout0 (),\n");
                sw.Write("\t\t\t\t.sclkout1 (),\n\t\t\t\t.vcooverrange (),\n\t\t\t\t.vcounderrange ());\n");
                #endregion

                #region 用户配置时定义的参数
                sw.WriteLine("\tdefparam");
                if (PTE)
                {
                    m_temp = m;
                    /*
                    if (RB_c0.Checked) m_temp = c0_m;
                    else if (RB_c1.Checked) m_temp = c1_m;
                    else if (RB_c2.Checked) m_temp = e0_m;
                    else if (RB_c3.Checked) m_temp = c3_m;
                    else if (RB_c4.Checked) m_temp = c4_m;
                    else if (RB_e02.Checked) m_temp = e02_m;
                    else if (RB_N.Checked) m_temp = m;
                    */
                }
                else
                {
                    if (RB_mode0.Checked) m_temp = m;
                    else if (RB_mode1.Checked) m_temp = e0_m;
                    else if (RB_mode2.Checked) m_temp = c0_m;
                    else if (RB_mode3.Checked) m_temp = c1_m;
                }

                if (CB_c0.Checked)
                {
                    if (RB_mode2.Checked || PTE && RB_c0.Checked)
                    {
                        sw.WriteLine("\t\taltpll_component.compensate_clock = \"CLK0\",");
                    }
                    sw.WriteLine("\t\taltpll_component.clk0_divide_by = " + c0_m * n + ",");//n的问题以后再改
                    sw.WriteLine("\t\taltpll_component.clk0_duty_cycle = " + c0_duty + ",");
                    sw.WriteLine("\t\taltpll_component.clk0_multiply_by = " + m_temp + ",");
                    sw.WriteLine("\t\taltpll_component.clk0_phase_shift = \"" + c0_phase + "\",");
                }
                if (CB_c1.Checked)
                {
                    if (RB_mode3.Checked || PTE && RB_c1.Checked)
                    {
                        sw.WriteLine("\t\taltpll_component.compensate_clock = \"CLK1\",");
                    }
                    sw.WriteLine("\t\taltpll_component.clk1_divide_by = " + c1_m * n + ",");//n的问题以后再改
                    sw.WriteLine("\t\taltpll_component.clk1_duty_cycle = " + c1_duty + ",");
                    sw.WriteLine("\t\taltpll_component.clk1_multiply_by = " + m_temp + ",");
                    sw.WriteLine("\t\taltpll_component.clk1_phase_shift = \"" + c1_phase + "\",");
                }
                if (CB_e0.Checked)
                {
                    if (RB_mode1.Checked || PTE && RB_c2.Checked)
                    {
                        //sw.WriteLine("\t\taltpll_component.compensate_clock = \"CLK2\","); //mark20161103
                        sw.WriteLine("\t\taltpll_component.compensate_clock = \"EXTCLK0\",");//mark20170119
                    }
                    if (PTE)
                    {
                        sw.WriteLine("\t\taltpll_component.clk2_divide_by = " + e0_m * n + ",");//n的问题以后再改
                        sw.WriteLine("\t\taltpll_component.clk2_duty_cycle = " + e0_duty + ",");
                        sw.WriteLine("\t\taltpll_component.clk2_multiply_by = " + m_temp + ",");
                        sw.WriteLine("\t\taltpll_component.clk2_phase_shift = \"" + e0_phase + "\",");
                    }
                    else
                    {
                        sw.WriteLine("\t\taltpll_component.extclk0_divide_by = " + e0_m * n + ",");//n的问题以后再改
                        sw.WriteLine("\t\taltpll_component.extclk0_duty_cycle = " + e0_duty + ",");
                        sw.WriteLine("\t\taltpll_component.extclk0_multiply_by = " + m_temp + ",");
                        sw.WriteLine("\t\taltpll_component.extclk0_phase_shift = \"" + e0_phase + "\",");
                    }
                }
                if (PTE)
                {
                    if (CB_c3.Checked)
                    {
                        if (RB_c3.Checked)
                        {
                            sw.WriteLine("\t\taltpll_component.compensate_clock = \"CLK3\",");
                        }
                        sw.WriteLine("\t\taltpll_component.clk3_divide_by = " + c3_m * n + ",");//n的问题以后再改
                        sw.WriteLine("\t\taltpll_component.clk3_duty_cycle = " + c3_duty + ",");
                        sw.WriteLine("\t\taltpll_component.clk3_multiply_by = " + m_temp + ",");
                        sw.WriteLine("\t\taltpll_component.clk3_phase_shift = \"" + c3_phase + "\",");
                    }
                    if (CB_c4.Checked)
                    {
                        if (RB_c4.Checked)
                        {
                            sw.WriteLine("\t\taltpll_component.compensate_clock = \"CLK4\",");
                        }
                        sw.WriteLine("\t\taltpll_component.clk4_divide_by = " + c4_m * n + ",");//n的问题以后再改
                        sw.WriteLine("\t\taltpll_component.clk4_duty_cycle = " + c4_duty + ",");
                        sw.WriteLine("\t\taltpll_component.clk4_multiply_by = " + m_temp + ",");
                        sw.WriteLine("\t\taltpll_component.clk4_phase_shift = \"" + c4_phase + "\",");
                    }
                    if (CB_e02.Checked)
                    {
                        if (RB_e02.Checked)
                        {
                            sw.WriteLine("\t\taltpll_component.compensate_clock = \"EXTCLK0\",");
                        }
                        sw.WriteLine("\t\taltpll_component.extclk0_divide_by = " + e02_m * n + ",");//n的问题以后再改
                        sw.WriteLine("\t\taltpll_component.extclk0_duty_cycle = " + e02_duty + ",");
                        sw.WriteLine("\t\taltpll_component.extclk0_multiply_by = " + m_temp + ",");
                        sw.WriteLine("\t\taltpll_component.extclk0_phase_shift = \"" + e02_phase + "\",");
                    }
                }
                if (PTE && (CB_c0.Checked || CB_c1.Checked || CB_e0.Checked || CB_c3.Checked || CB_c4.Checked))
                {
                    sw.WriteLine("\t\taltpll_component.clk5_divide_by = " + m_temp * n + ",");//n的问题以后再改
                    sw.WriteLine("\t\taltpll_component.clk5_duty_cycle = 50,");
                    sw.WriteLine("\t\taltpll_component.clk5_multiply_by = " + m_temp + ",");
                    sw.WriteLine("\t\taltpll_component.clk5_phase_shift = \"0\",");
                }

                int freq = (int)(1e6 / inclk_freq);
                sw.WriteLine("\t\taltpll_component.inclk0_input_frequency = " + freq.ToString() + ",");
                sw.WriteLine("\t\taltpll_component.operation_mode = \"" + operation_mode + "\",");

                if (CB_pllena.Checked) sw.WriteLine("\t\taltpll_component.port_pllena = \"PORT_USED\",");
                else sw.WriteLine("\t\taltpll_component.port_pllena = \"PORT_UNUSED\",");
                if (CB_pfd_load.Checked) sw.WriteLine("\t\taltpll_component.port_pfdena = \"PORT_USED\",");
                else sw.WriteLine("\t\taltpll_component.port_pfdena = \"PORT_UNUSED\",");
                if (CB_areset.Checked) sw.WriteLine("\t\taltpll_component.port_areset = \"PORT_USED\",");
                else sw.WriteLine("\t\taltpll_component.port_areset = \"PORT_UNUSED\",");
                if (CB_locked.Checked)
                {
                    sw.WriteLine("\t\taltpll_component.port_locked = \"PORT_USED\",");
                    sw.WriteLine("\t\taltpll_component.invalid_lock_multiplier = 5,");
                    sw.WriteLine("\t\taltpll_component.valid_lock_multiplier = 1,");
                }
                else
                {
                    sw.WriteLine("\t\taltpll_component.port_locked = \"PORT_UNUSED\",");
                }

                if (CB_c0.Checked) sw.WriteLine("\t\taltpll_component.port_clk0 = \"PORT_USED\",");
                else sw.WriteLine("\t\taltpll_component.port_clk0 = \"PORT_UNUSED\",");
                if (CB_c1.Checked) sw.WriteLine("\t\taltpll_component.port_clk1 = \"PORT_USED\",");
                else sw.WriteLine("\t\taltpll_component.port_clk1 = \"PORT_UNUSED\",");
                if (PTE && CB_e0.Checked) sw.WriteLine("\t\taltpll_component.port_clk2 = \"PORT_USED\",");
                else sw.WriteLine("\t\taltpll_component.port_clk2 = \"PORT_UNUSED\",");
                if (PTE && CB_c3.Checked) sw.WriteLine("\t\taltpll_component.port_clk3 = \"PORT_USED\",");
                else sw.WriteLine("\t\taltpll_component.port_clk3 = \"PORT_UNUSED\",");
                if (PTE && CB_c4.Checked) sw.WriteLine("\t\taltpll_component.port_clk4 = \"PORT_USED\",");
                else sw.WriteLine("\t\taltpll_component.port_clk4 = \"PORT_UNUSED\",");
                if (PTE && (CB_c0.Checked || CB_c1.Checked || CB_e0.Checked || CB_c3.Checked || CB_c4.Checked)) sw.WriteLine("\t\taltpll_component.port_clk5 = \"PORT_USED\",");
                else sw.WriteLine("\t\taltpll_component.port_clk5 = \"PORT_UNUSED\",");
                if (!PTE && CB_e0.Checked || PTE && CB_e02.Checked) sw.WriteLine("\t\taltpll_component.port_extclk0 = \"PORT_USED\",");
                else sw.WriteLine("\t\taltpll_component.port_extclk0 = \"PORT_UNUSED\",");

                //if (ipCoreFrm.deviceCmbBox.SelectedIndex == 1)
                //{
                //    sw.WriteLine("\t\taltpll_component.intended_device_family = \"Cyclone\",");
                //}
                //else
                //{
                sw.WriteLine("\t\taltpll_component.intended_device_family = \"Stratix\",");
                //}

                sw.WriteLine("\t\taltpll_component.lpm_type = \"altpll\",");
                sw.WriteLine("\t\taltpll_component.pll_type = \"Enhanced\",");
                sw.WriteLine("\t\taltpll_component.port_activeclock = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_clkbad0 = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_clkbad1 = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_clkloss = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_clkswitch = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_fbin = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_inclk0 = \"PORT_USED\",");
                sw.WriteLine("\t\taltpll_component.port_inclk1 = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_phasecounterselect = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_phasedone = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_phasestep = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_phaseupdown = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_scanaclr = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_scanclk = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_scanclkena = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_scandata = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_scandataout = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_scandone = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_scanread = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_scanwrite = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_clkena0 = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_clkena1 = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_clkena2 = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_clkena3 = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_clkena4 = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_clkena5 = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_extclk1 = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_extclk2 = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.port_extclk3 = \"PORT_UNUSED\",");
                sw.WriteLine("\t\taltpll_component.valid_lock_multiplier = 1;");
                sw.WriteLine("endmodule");
                sw.Close();
                #endregion

                sw.Close();

                #region 验证程序
                /***************************************************************************
                //读文件，验证开始

                string srst;
                double in_fre;
                double in_fre_pre;
                int v_c0_d=0,v_c0_m=0,v_c1_d=0,v_c1_m=0,v_c2_d=0,v_c2_m=0;
                int v_c3_d=0,v_c3_m=0,v_c4_d=0,v_c4_m=0,v_e0_d=0,v_e0_m=0;
                double v_c0_c=0.0,v_c0_p=0.0,v_c1_c=0.0,v_c1_p=0.0,v_c2_c=0.0,v_c2_p=0.0;
                double v_c3_c=0.0,v_c3_p=0.0,v_c4_c=0.0,v_c4_p=0.0,v_e0_c=0.0,v_e0_p=0.0;
                int vc = 0;

                StreamReader sr = new StreamReader(saveFile);
                for (; ; )
                {
                    srst = sr.ReadLine();
                    if (srst != null)
                    {
                        //srst = sr.ReadLine().ToString();
                        if (srst.StartsWith("		altpll_component.inclk0_input_frequency = "))
                        {
                            in_fre = double.Parse(srst.Substring(srst.IndexOf('=') + 2, srst.IndexOf(',') - srst.IndexOf('=') - 2));
                            in_fre_pre = 1e6/double.Parse(TB_inclk.Text);
                            if (in_fre - in_fre_pre > 1.5 || in_fre - in_fre_pre < -1.5)
                                MessageBox.Show("inclk error: " + in_fre + " " + in_fre_pre);
                        }
                        else if (srst.StartsWith("		altpll_component.clk0_divide_by = "))
                        {
                            v_c0_d = int.Parse(srst.Substring(srst.IndexOf('=') + 2, srst.IndexOf(',') - srst.IndexOf('=') - 2));
                        }
                        else if (srst.StartsWith("		altpll_component.clk0_duty_cycle = "))
                        {
                            v_c0_c = double.Parse(srst.Substring(srst.IndexOf('=') + 2, srst.IndexOf(',') - srst.IndexOf('=') - 2));
                        }
                        else if (srst.StartsWith("		altpll_component.clk0_multiply_by = "))
                        {
                            v_c0_m = int.Parse(srst.Substring(srst.IndexOf('=') + 2, srst.IndexOf(',') - srst.IndexOf('=') - 2));
                        }
                        else if (srst.StartsWith("		altpll_component.clk0_phase_shift = \""))
                        {
                            v_c0_p = double.Parse(srst.Substring(srst.IndexOf('\"') + 1, srst.LastIndexOf('\"') - srst.IndexOf('\"') - 1));
                        }
                        else if (srst.StartsWith("		altpll_component.clk1_divide_by = "))
                        {
                            v_c1_d = int.Parse(srst.Substring(srst.IndexOf('=') + 2, srst.IndexOf(',') - srst.IndexOf('=') - 2));
                        }
                        else if (srst.StartsWith("		altpll_component.clk1_duty_cycle = "))
                        {
                            v_c1_c = double.Parse(srst.Substring(srst.IndexOf('=') + 2, srst.IndexOf(',') - srst.IndexOf('=') - 2));
                        }
                        else if (srst.StartsWith("		altpll_component.clk1_multiply_by = "))
                        {
                            v_c1_m = int.Parse(srst.Substring(srst.IndexOf('=') + 2, srst.IndexOf(',') - srst.IndexOf('=') - 2));
                        }
                        else if (srst.StartsWith("		altpll_component.clk1_phase_shift = \""))
                        {
                            v_c1_p = double.Parse(srst.Substring(srst.IndexOf('\"') + 1, srst.LastIndexOf('\"') - srst.IndexOf('\"') - 1));
                        }
                        else if (srst.StartsWith("		altpll_component.clk2_divide_by = "))
                        {
                            v_c2_d = int.Parse(srst.Substring(srst.IndexOf('=') + 2, srst.IndexOf(',') - srst.IndexOf('=') - 2));
                        }
                        else if (srst.StartsWith("		altpll_component.clk2_duty_cycle = "))
                        {
                            v_c2_c = double.Parse(srst.Substring(srst.IndexOf('=') + 2, srst.IndexOf(',') - srst.IndexOf('=') - 2));
                        }
                        else if (srst.StartsWith("		altpll_component.clk2_multiply_by = "))
                        {
                            v_c2_m = int.Parse(srst.Substring(srst.IndexOf('=') + 2, srst.IndexOf(',') - srst.IndexOf('=') - 2));
                        }
                        else if (srst.StartsWith("		altpll_component.clk2_phase_shift = \""))
                        {
                            v_c2_p = double.Parse(srst.Substring(srst.IndexOf('\"') + 1, srst.LastIndexOf('\"') - srst.IndexOf('\"') - 1));
                        }
                        else if (srst.StartsWith("		altpll_component.clk3_divide_by = "))
                        {
                            v_c3_d = int.Parse(srst.Substring(srst.IndexOf('=') + 2, srst.IndexOf(',') - srst.IndexOf('=') - 2));
                        }
                        else if (srst.StartsWith("		altpll_component.clk3_duty_cycle = "))
                        {
                            v_c3_c = double.Parse(srst.Substring(srst.IndexOf('=') + 2, srst.IndexOf(',') - srst.IndexOf('=') - 2));
                        }
                        else if (srst.StartsWith("		altpll_component.clk3_multiply_by = "))
                        {
                            v_c3_m = int.Parse(srst.Substring(srst.IndexOf('=') + 2, srst.IndexOf(',') - srst.IndexOf('=') - 2));
                        }
                        else if (srst.StartsWith("		altpll_component.clk3_phase_shift = \""))
                        {
                            v_c3_p = double.Parse(srst.Substring(srst.IndexOf('\"') + 1, srst.LastIndexOf('\"') - srst.IndexOf('\"') - 1));
                        }
                        else if (srst.StartsWith("		altpll_component.clk4_divide_by = "))
                        {
                            v_c4_d = int.Parse(srst.Substring(srst.IndexOf('=') + 2, srst.IndexOf(',') - srst.IndexOf('=') - 2));
                        }
                        else if (srst.StartsWith("		altpll_component.clk4_duty_cycle = "))
                        {
                            v_c4_c = double.Parse(srst.Substring(srst.IndexOf('=') + 2, srst.IndexOf(',') - srst.IndexOf('=') - 2));
                        }
                        else if (srst.StartsWith("		altpll_component.clk4_multiply_by = "))
                        {
                            v_c4_m = int.Parse(srst.Substring(srst.IndexOf('=') + 2, srst.IndexOf(',') - srst.IndexOf('=') - 2));
                        }
                        else if (srst.StartsWith("		altpll_component.clk4_phase_shift = \""))
                        {
                            v_c4_p = double.Parse(srst.Substring(srst.IndexOf('\"') + 1, srst.LastIndexOf('\"') - srst.IndexOf('\"') - 1));
                        }
                        else if (srst.StartsWith("		altpll_component.extclk0_divide_by = "))
                        {
                            v_e0_d = int.Parse(srst.Substring(srst.IndexOf('=') + 2, srst.IndexOf(',') - srst.IndexOf('=') - 2));
                        }
                        else if (srst.StartsWith("		altpll_component.extclk0_duty_cycle = "))
                        {
                            v_e0_c = double.Parse(srst.Substring(srst.IndexOf('=') + 2, srst.IndexOf(',') - srst.IndexOf('=') - 2));
                        }
                        else if (srst.StartsWith("		altpll_component.extclk0_multiply_by = "))
                        {
                            v_e0_m = int.Parse(srst.Substring(srst.IndexOf('=') + 2, srst.IndexOf(',') - srst.IndexOf('=') - 2));
                        }
                        else if (srst.StartsWith("		altpll_component.extclk0_phase_shift = \""))
                        {
                            v_e0_p = double.Parse(srst.Substring(srst.IndexOf('\"') + 1, srst.LastIndexOf('\"') - srst.IndexOf('\"') - 1));
                        }
                    }
                    else
                        break;
                }
                sr.Close();
                if (CB_c0.Checked)
                {
                    vc++;
                    if (v_c0_d * nUD_c0_mul.Value != v_c0_m * nUD_c0_div.Value)
                        MessageBox.Show("c0 dm error");
                    if (v_c0_c - double.Parse(CBB_c0_duty.Text) > 1e-3 || v_c0_c - double.Parse(CBB_c0_duty.Text) < -1e-3)
                        MessageBox.Show("c0_duty error: " + v_c0_c + " " + CBB_c0_duty.Text);
                    if (v_c0_p - double.Parse(CBB_c0_phase.Text) > 1e-3 || v_c0_p - double.Parse(CBB_c0_phase.Text) < -1e-3)
                        MessageBox.Show("c0_phase error: " + v_c0_p + " " + CBB_c0_phase.Text);
                }
                if (CB_c1.Checked)
                {
                    vc++;
                    if (v_c1_d * nUD_c1_mul.Value != v_c1_m * nUD_c1_div.Value)
                        MessageBox.Show("c1 dm error");
                    if (v_c1_c - double.Parse(CBB_c1_duty.Text) > 1e-3 || v_c1_c - double.Parse(CBB_c1_duty.Text) < -1e-3)
                        MessageBox.Show("c1_duty error: " + v_c1_c + " " + CBB_c1_duty.Text);
                    if (v_c1_p - double.Parse(CBB_c1_phase.Text) > 1e-3 || v_c1_p - double.Parse(CBB_c1_phase.Text) < -1e-3)
                        MessageBox.Show("c1_phase error: " + v_c1_p + " " + CBB_c1_phase.Text);
                }
                if (PTE && CB_e0.Checked)
                {
                    vc++;
                    if (v_c2_d * nUD_e0_mul.Value != v_c2_m * nUD_e0_div.Value)
                        MessageBox.Show("c2 dm error");
                    if (v_c2_c - double.Parse(CBB_e0_duty.Text) > 1e-3 || v_c2_c - double.Parse(CBB_e0_duty.Text) < -1e-3)
                        MessageBox.Show("c2_duty error: " + v_c2_c + " " + CBB_e0_duty.Text);
                    if (v_c2_p - double.Parse(CBB_e0_phase.Text) > 1e-3 || v_c2_p - double.Parse(CBB_e0_phase.Text) < -1e-3)
                        MessageBox.Show("c2_phase error: " + v_c2_p + " " + CBB_e0_phase.Text);
                }
                if (PTE && CB_c3.Checked)
                {
                    vc++;
                    if (v_c3_d * nUD_c3_mul.Value != v_c3_m * nUD_c3_div.Value)
                        MessageBox.Show("c3 dm error");
                    if (v_c3_c - double.Parse(CBB_c3_duty.Text) > 1e-3 || v_c3_c - double.Parse(CBB_c3_duty.Text) < -1e-3)
                        MessageBox.Show("c3_duty error: " + v_c3_c + " " + CBB_c3_duty.Text);
                    if (v_c3_p - double.Parse(CBB_c3_phase.Text) > 1e-3 || v_c3_p - double.Parse(CBB_c3_phase.Text) < -1e-3)
                        MessageBox.Show("c3_phase error: " + v_c3_p + " " + CBB_c3_phase.Text);
                }
                if (PTE && CB_c4.Checked)
                {
                    vc++;
                    if (v_c4_d * nUD_c4_mul.Value != v_c4_m * nUD_c4_div.Value)
                        MessageBox.Show("c4 dm error");
                    if (v_c4_c - double.Parse(CBB_c4_duty.Text) > 1e-3 || v_c4_c - double.Parse(CBB_c4_duty.Text) < -1e-3)
                        MessageBox.Show("c4_duty error: " + v_c4_c + " " + CBB_c4_duty.Text);
                    if (v_c4_p - double.Parse(CBB_c4_phase.Text) > 1e-3 || v_c4_p - double.Parse(CBB_c4_phase.Text) < -1e-3)
                        MessageBox.Show("c4_phase error: " + v_c4_p + " " + CBB_c4_phase.Text);
                }
                //if (PTE && (CB_c0.Checked || CB_c1.Checked || CB_e0.Checked || CB_c3.Checked || CB_c4.Checked))
                //{
                //    if (v_c0_d * nUD_c0_mul.Value != v_c0_m * nUD_c0_div.Value)
                //        MessageBox.Show("c0 dm error");
                //}
                if (!PTE && CB_e0.Checked)
                {
                    vc++;
                    if (v_e0_d * nUD_e0_mul.Value != v_e0_m * nUD_e0_div.Value)
                        MessageBox.Show("e0 dm error");
                    if (v_e0_c - double.Parse(CBB_e0_duty.Text) > 1e-3 || v_e0_c - double.Parse(CBB_e0_duty.Text) < -1e-3)
                        MessageBox.Show("e0_duty error: " + v_e0_c + " " + CBB_e0_duty.Text);
                    if (v_e0_p - double.Parse(CBB_e0_phase.Text) > 1e-3 || v_e0_p - double.Parse(CBB_e0_phase.Text) < -1e-3)
                        MessageBox.Show("e0_phase error: " + v_e0_p + " " + CBB_e0_phase.Text);
                }
                if (PTE && CB_e02.Checked)
                {
                    vc++;
                    if (v_e0_d * nUD_e02_mul.Value != v_e0_m * nUD_e02_div.Value)
                        MessageBox.Show("e02 dm error");
                    if (v_e0_c - double.Parse(CBB_e02_duty.Text) > 1e-3 || v_e0_c - double.Parse(CBB_e02_duty.Text) < -1e-3)
                        MessageBox.Show("e02_duty error: " + v_e0_c + " " + CBB_e02_duty.Text);
                    if (v_e0_p - double.Parse(CBB_e02_phase.Text) > 1e-3 || v_e0_p - double.Parse(CBB_e02_phase.Text) < -1e-3)
                        MessageBox.Show("e02_phase error: " + v_e0_p + " " + CBB_e02_phase.Text);
                }
                MessageBox.Show("vc = " + vc);
                
                ***************************************************************************/
                #endregion
            }
                BT_Save.Enabled = false;
                BT_Close.Visible = true;
                LB_message_output.ForeColor = System.Drawing.Color.Green;
                LB_message_output.Text = "File is saved.";
        }

        private void BT_Close_Click(object sender, EventArgs e)
        {
            Close();
        }

        private void TC_SelectedIndexChanged(object sender, EventArgs e)
        {
            if (TC.SelectedIndex == 0)
            {
                BT_Next.Visible = true;
                BT_Back.Visible = false;
                BT_Save.Visible = false;
                BT_Close.Visible = false;
            }
            else if (TC.SelectedIndex == 1)
            {
                BT_Next.Visible = true;
                BT_Back.Visible = true;
                BT_Save.Visible = false;
                BT_Close.Visible = false;
            }
            else
            {
                BT_Next.Visible = false;
                BT_Back.Visible = true;
                BT_Save.Visible = true;
            }

        }
        private void BT_Back_Click(object sender, EventArgs e)
        {
            if (TC.SelectedIndex == 2)
                TC.SelectedIndex = 1;
            else if (TC.SelectedIndex == 1)
                TC.SelectedIndex = 0;
        }

        private void BT_Next_Click(object sender, EventArgs e)
        {
            if (TC.SelectedIndex == 0)
                TC.SelectedIndex = 1;
            else if (TC.SelectedIndex == 1)
            {
                TC.SelectedIndex = 2;
                //saveenabled = RefreshData();
                //BT_Save.Enabled = saveenabled;
            }
        }

        private void BT_Cancel_Click(object sender, EventArgs e)
        {
            Close();
        }

        private void RB_LPE0_CheckedChanged(object sender, EventArgs e)
        {
            BT_Save.Enabled = saveenabled;
            if (saveenabled)
                LB_message_output.Text = "";
        }
        private void RB_LPE1_CheckedChanged(object sender, EventArgs e)
        {
            BT_Save.Enabled = saveenabled;
            if (saveenabled)
                LB_message_output.Text = "";
        }
        private void RB_LPE2_CheckedChanged(object sender, EventArgs e)
        {
            BT_Save.Enabled = saveenabled;
            if (saveenabled)
                LB_message_output.Text = "";
        }

        private void RB_GLC0_CheckedChanged(object sender, EventArgs e)
        {
            if (RB_GLC0.Checked)
                LB_GLC.Text = "32";
            BT_Save.Enabled = saveenabled;
            if (saveenabled)
                LB_message_output.Text = "";
        }
        private void RB_GLC1_CheckedChanged(object sender, EventArgs e)
        {
            if (RB_GLC1.Checked)
                LB_GLC.Text = "64";
            BT_Save.Enabled = saveenabled;
            if (saveenabled)
                LB_message_output.Text = "";
        }
        private void RB_GLC2_CheckedChanged(object sender, EventArgs e)
        {
            if (RB_GLC2.Checked)
                LB_GLC.Text = "128";
            BT_Save.Enabled = saveenabled;
            if (saveenabled)
                LB_message_output.Text = "";
        }
        private void RB_GLC3_CheckedChanged(object sender, EventArgs e)
        {
            if (RB_GLC3.Checked)
                LB_GLC.Text = "256";
            BT_Save.Enabled = saveenabled;
            if (saveenabled)
                LB_message_output.Text = "";
        }

        private void groupBox3_Enter(object sender, EventArgs e)
        {

        }

        private void label11_Click(object sender, EventArgs e)
        {

        }

        private void LB_M_Click(object sender, EventArgs e)
        {

        }

        /************************************************************
        private void TB_c0_duty_TextChanged(object sender, EventArgs e)
        {
            if (TB_c0_duty.Text.Length == 0)
                return;
            t_c0_duty = double.Parse(TB_c0_duty.Text) / 100;
            j = 0;
            for (i = 1; i < CBB_c0_duty.Items.Count; i++)
            {
                if (abs(sort_duty_c0_2[i].rate - t_c0_duty) < abs(sort_duty_c0_2[j].rate - t_c0_duty))
                    j = i;
            }
            CBB_c0_duty.SelectedIndex = j;

            saveenabled = RefreshData2(0);
            BT_Save.Enabled = saveenabled;
        }

        private void TB_c1_duty_TextChanged(object sender, EventArgs e)
        {
            if (TB_c1_duty.Text.Length == 0)
                return;
            t_c1_duty = double.Parse(TB_c1_duty.Text) / 100;
            j = 0;
            for (i = 1; i < CBB_c1_duty.Items.Count; i++)
            {
                if (abs(sort_duty_c1_2[i].rate - t_c1_duty) < abs(sort_duty_c1_2[j].rate - t_c1_duty))
                    j = i;
            }
            CBB_c1_duty.SelectedIndex = j;

            saveenabled = RefreshData2(1);
            BT_Save.Enabled = saveenabled;
        }

        private void TB_e0_duty_TextChanged(object sender, EventArgs e)
        {
            if (TB_e0_duty.Text.Length == 0)
                return;
            t_e0_duty = double.Parse(TB_e0_duty.Text) / 100;
            j = 0;
            for (i = 1; i < CBB_e0_duty.Items.Count; i++)
            {
                if (abs(sort_duty_e0_2[i].rate - t_e0_duty) < abs(sort_duty_e0_2[j].rate - t_e0_duty))
                    j = i;
            }
            CBB_e0_duty.SelectedIndex = j;

            saveenabled = RefreshData2(2);
            BT_Save.Enabled = saveenabled;
        }

        private void TB_c0_phase_TextChanged(object sender, EventArgs e)
        {
            if (TB_c0_phase.Text.Length == 0)
                return;
            t_c0_phase = double.Parse(TB_c0_phase.Text);
            j = 0;
            for (i = 1; i < CBB_c0_phase.Items.Count; i++)
            {
                if (abs(i * 360 / sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m / 8 - t_c0_phase) < abs(j * 360 / sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m / 8 - t_c0_phase))
                    j = i;
            }
            CBB_c0_phase.SelectedIndex = j;
            //MessageBox.Show("c0_phaseCount = " + CBB_c0_phase.Items.Count.ToString() + "\nj = " + j.ToString());//ly_mod
        }

        private void TB_c1_phase_TextChanged(object sender, EventArgs e)
        {
            if (TB_c1_phase.Text.Length == 0)
                return;
            t_c1_phase = double.Parse(TB_c1_phase.Text);
            j = 0;
            for (i = 1; i < CBB_c1_phase.Items.Count; i++)
            {
                if (abs(i * 360 / sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m / 8 - t_c1_phase) < abs(j * 360 / sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m / 8 - t_c1_phase))
                    j = i;
            }
            CBB_c1_phase.SelectedIndex = j;
        }

        private void TB_e0_phase_TextChanged(object sender, EventArgs e)
        {
            if (TB_e0_phase.Text.Length == 0)
                return;
            t_e0_phase = double.Parse(TB_e0_phase.Text);
            j = 0;
            for (i = 1; i < CBB_e0_phase.Items.Count; i++)
            {
                if (abs(i * 360 / sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m / 8 - t_e0_phase) < abs(j * 360 / sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m / 8 - t_e0_phase))
                    j = i;
            }
            CBB_e0_phase.SelectedIndex = j;
        }


        private void TB_c0_duty_KeyPress(object sender, KeyPressEventArgs e)
        {

        }
        private void TB_c1_duty_KeyPress(object sender, KeyPressEventArgs e)
        {

        }
        private void TB_e0_duty_KeyPress(object sender, KeyPressEventArgs e)
        {

        }
        private void TB_c0_phase_KeyPress(object sender, KeyPressEventArgs e)
        {

        }
        private void TB_c1_phase_KeyPress(object sender, KeyPressEventArgs e)
        {

        }
        private void TB_e0_phase_KeyPress(object sender, KeyPressEventArgs e)
        {

        }
        private void TB_c0_duty_Leave(object sender, EventArgs e)
        {
            //if (TB_c0_duty.Text.Length == 0)
            //    TB_c0_duty.Text = "50";
            //t_c0_duty = double.Parse(TB_c0_duty.Text)/100;
            //j = 0;
            //for (i = 1; i < CBB_c0_duty.Items.Count; i++)
            //{
            //    if(abs(sort_duty_c0_2[i].rate-t_c0_duty)<abs(sort_duty_c0_2[j].rate-t_c0_duty))
            //        j = i;
            //}
            //CBB_c0_duty.SelectedIndex = j;
        }
        private void TB_c1_duty_Leave(object sender, EventArgs e)
        {
            //if (TB_c1_duty.Text.Length == 0)
            //    TB_c1_duty.Text = "50";
            //t_c1_duty = double.Parse(TB_c1_duty.Text) / 100;
            //j = 0;
            //for (i = 1; i < CBB_c1_duty.Items.Count; i++)
            //{
            //    if (abs(sort_duty_c1_2[i].rate - t_c1_duty) < abs(sort_duty_c1_2[j].rate - t_c1_duty))
            //        j = i;
            //}
            //CBB_c1_duty.SelectedIndex = j;
        }
        private void TB_e0_duty_Leave(object sender, EventArgs e)
        {
            //if (TB_e0_duty.Text.Length == 0)
            //    TB_e0_duty.Text = "50";
            //t_e0_duty = double.Parse(TB_e0_duty.Text) / 100;
            //j = 0;
            //for (i = 1; i < CBB_e0_duty.Items.Count; i++)
            //{
            //    if (abs(sort_duty_e0_2[i].rate - t_e0_duty) < abs(sort_duty_e0_2[j].rate - t_e0_duty))
            //        j = i;
            //}
            //CBB_e0_duty.SelectedIndex = j;
        }
        private void TB_c0_phase_Leave(object sender, EventArgs e)
        {
            //if (TB_c0_phase.Text.Length == 0)
            //    TB_c0_phase.Text = "0";
            //t_c0_phase = double.Parse(TB_c0_phase.Text);
            //j = 0;
            //for (i = 1; i < CBB_c0_phase.Items.Count; i++)
            //{
            //    if (abs(i * 360 / sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m / 8 - t_c0_phase) < abs(j * 360 / sort_duty_c0_2[CBB_c0_duty.SelectedIndex].c0m / 8 - t_c0_phase))
            //        j = i;
            //}
            //CBB_c0_phase.SelectedIndex = j;
            //MessageBox.Show("c0_phaseCount = " + CBB_c0_phase.Items.Count.ToString()+"\nj = "+j.ToString());//ly_mod
        }
        private void TB_c1_phase_Leave(object sender, EventArgs e)
        {
            //if (TB_c1_phase.Text.Length == 0)
            //    TB_c1_phase.Text = "0";
            //t_c1_phase = double.Parse(TB_c1_phase.Text);
            //j = 0;
            //for (i = 1; i < CBB_c1_phase.Items.Count; i++)
            //{
            //    if (abs(i * 360 / sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m / 8 - t_c1_phase) < abs(j * 360 / sort_duty_c1_2[CBB_c1_duty.SelectedIndex].c1m / 8 - t_c1_phase))
            //        j = i;
            //}
            //CBB_c1_phase.SelectedIndex = j;
        }
        private void TB_e0_phase_Leave(object sender, EventArgs e)
        {
            //if (TB_e0_phase.Text.Length == 0)
            //    TB_e0_phase.Text = "0";
            //t_e0_phase = double.Parse(TB_e0_phase.Text);
            //j = 0;
            //for (i = 1; i < CBB_e0_phase.Items.Count; i++)
            //{
            //    if (abs(i * 360 / sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m / 8 - t_e0_phase) < abs(j * 360 / sort_duty_e0_2[CBB_e0_duty.SelectedIndex].e0m / 8 - t_e0_phase))
            //        j = i;
            //}
            //CBB_e0_phase.SelectedIndex = j;
        }
        *****************************************************************/
    }
        #endregion
}