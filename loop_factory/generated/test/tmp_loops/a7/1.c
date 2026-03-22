int main1(int k,int s){
  int q, m, bg, a3ws, uu, gm, sd6, o;

  q=s+25;
  m=1;
  bg=1;
  a3ws=1;
  uu=1;
  gm=1;
  sd6=q;
  o=0;

  while (uu<=q) {
      bg = bg*(k/uu);
      if ((uu/2)%2==0) {
          gm = 1;
      }
      else {
          gm = -1;
      }
      uu = uu + 1;
      a3ws = a3ws+gm*bg;
      bg = bg*(k/uu);
      if (q*q<=q+6) {
          s = sd6*sd6;
      }
      sd6 = sd6 + m;
      o = o*o;
      k = k+(gm%3);
      k = k+sd6*o;
  }

}
