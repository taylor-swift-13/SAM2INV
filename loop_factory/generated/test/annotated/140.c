int main1(int o,int y){
  int cpqr, fq, fh;
  cpqr=77;
  fq=cpqr;
  fh=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fh == 0;
  loop invariant y == \at(y, Pre);
  loop invariant o == \at(o, Pre) + 2*y*(fq - 77);
  loop invariant cpqr == 77;
  loop invariant 77 <= fq;
  loop invariant fq <= cpqr;
  loop assigns fq, o, fh;
*/
while (fq<cpqr) {
      if (fq%2==0) {
          if (fh>0) {
              fh = fh - 1;
              fh += 1;
          }
      }
      else {
          if (fh>0) {
              fh = fh - 1;
              fh += 1;
          }
      }
      fq += 1;
      o += fh;
      o = o+y+y;
  }
}