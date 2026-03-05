int main66(int o,int r){
  int of, qnj, fp, n9, a3, tska;

  of=(r%35)+15;
  qnj=(r%35)+15;
  fp=1;
  n9=0;
  a3=0;
  tska=1;

  while (of!=qnj) {
      if (of>qnj) {
          of = of - qnj;
          fp = fp - n9;
          a3 = a3 - tska;
      }
      else {
          qnj = qnj - of;
          n9 -= fp;
          tska -= a3;
      }
  }

}
