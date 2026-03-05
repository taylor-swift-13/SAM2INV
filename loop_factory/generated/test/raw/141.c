int main1(int g){
  int gm4, u, i, jt;

  gm4=64;
  u=3;
  i=0;
  jt=17;

  while (u<gm4) {
      if (i==0) {
          i = i + 1;
          jt--;
          i = 1;
      }
      else {
          i--;
          jt = jt + 1;
          i = 0;
      }
      u = u + 1;
      g = g + u;
  }

}
