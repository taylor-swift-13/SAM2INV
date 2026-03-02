int main1(int b,int m){
  int u, t, g;

  u=(m%37)+13;
  t=u;
  g=u;

  while (t>0) {
      g = g+3;
      if ((t%4)==0) {
          g = g-g;
      }
  }

}
