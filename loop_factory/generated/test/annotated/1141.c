int main1(){
  int yk, wt, yu, gknq, ibps;
  yk=0;
  wt=0;
  yu=0;
  gknq=(1%18)+5;
  ibps=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yk == wt;
  loop invariant wt == yu;
  loop invariant gknq + wt == 6;
  loop invariant ibps == -3 + 6*wt - wt*(wt+1)/2;
  loop invariant 0 <= gknq <= 6;
  loop assigns wt, yk, yu, gknq, ibps;
*/
while (1) {
      if (!(gknq>=1)) {
          break;
      }
      wt = wt+1*1;
      yk = yk+1*1;
      yu = yu+1*1;
      gknq -= 1;
      ibps = ibps + gknq;
  }
}