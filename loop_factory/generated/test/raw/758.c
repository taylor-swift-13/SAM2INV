int main1(){
  int ku5n, gje, tp, a7jl, zn, ad;

  ku5n=0;
  gje=(1%20)+1;
  tp=(1%25)+1;
  a7jl=0;
  zn=-5;
  ad=ku5n;

  while (tp!=0) {
      if (tp%2==1) {
          a7jl += gje;
          tp--;
      }
      else {
      }
      tp = tp/2;
      gje = 2*gje;
      zn = zn*2+(gje%4)+0;
      ad = ad*4+(tp%2)+0;
  }

}
