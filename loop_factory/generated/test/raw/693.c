int main1(int z,int m){
  int y, arq, ex, obc, r8, w, mg1u;

  y=37;
  arq=0;
  ex=3;
  obc=3;
  r8=0;
  w=3;
  mg1u=0;

  while (arq<y) {
      if (arq%3==0) {
          if (ex>0) {
              ex = ex - 1;
              r8 += 1;
          }
      }
      else {
          if (ex<w) {
              ex += 1;
              obc += 1;
          }
      }
      arq = arq + 1;
      mg1u = mg1u + 1;
  }

}
