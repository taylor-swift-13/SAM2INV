int main1(int t,int n){
  int ty, qp, yc;
  ty=67;
  qp=0;
  yc=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yc == 8 + qp;
  loop invariant 0 <= qp;
  loop invariant ty - qp >= 0;
  loop assigns qp, yc;
*/
while (1) {
      if (!(qp+1<=ty)) {
          break;
      }
      yc++;
      qp = qp + 1;
  }
}