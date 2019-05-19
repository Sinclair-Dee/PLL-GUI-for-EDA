using System;
using System.Collections.Generic;
using System.Linq;
using System.Windows.Forms;

namespace PLL
{
    static class Program
    {
        /// <summary>
        /// The main entry point for the application.
        /// </summary>
        [STAThread]
        //static void Main()
        //{
        //    Application.EnableVisualStyles();
        //    Application.SetCompatibleTextRenderingDefault(false);
        //    Application.Run(new Form1());
        //}
        static void Main(string[] argv)
        {
            Application.EnableVisualStyles();
            Application.SetCompatibleTextRenderingDefault(false);
            if (argv.Length != 0)
                Application.Run(new Form1(argv[0]));
            else
                Application.Run(new Form1(".\\pll.v"));
        }
    }
}
