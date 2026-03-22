int main1(int z,int m){
  int y, arq, ex, obc, r8, w, mg1u;
  y=37;
  arq=0;
  ex=3;
  obc=3;
  r8=0;
  w=3;
  mg1u=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mg1u == arq;
  loop invariant 0 <= arq <= y;
  loop invariant 0 <= ex <= w;
  loop invariant 3 <= obc <= 3 + arq;
  loop invariant 0 <= r8 <= mg1u;
  loop assigns arq, mg1u, ex, r8, obc;
*/
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