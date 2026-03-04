int main1(int m,int u,int v){
  int u4, qn, t8, z;

  u4=(v%24)+8;
  qn=2;
  t8=v;
  z=-6;

  while (1) {
      if (!(qn+2<=u4)) {
          break;
      }
      z += 1;
      t8 = z*z;
      m = m + qn;
      m++;
  }

}
