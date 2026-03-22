int main1(int d){
  int pj, kqbw, yfy, z3, a, htkv, tp, aj, r7t;

  pj=199;
  kqbw=4;
  yfy=1;
  z3=1;
  a=1;
  htkv=1;
  tp=6;
  aj=0;
  r7t=kqbw;

  while (1) {
      if (!(a<=pj)) {
          break;
      }
      yfy = yfy*(d/a);
      if ((a/2)%2==0) {
          htkv = 1;
      }
      else {
          htkv = -1;
      }
      z3 = z3+htkv*yfy;
      a++;
      yfy = yfy*(d/a);
      if (z3*z3<=pj+3) {
          r7t = r7t + aj;
      }
      tp = tp+a+a;
      d = d+(z3%8);
      aj = aj*aj;
      tp = tp + kqbw;
  }

}
