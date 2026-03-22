int main1(int j){
  int q1qg, yct, qxi;
  q1qg=j+12;
  yct=0;
  qxi=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q1qg == \at(j, Pre) + 12;
  loop invariant (yct == 0) ==> (qxi == 0);
  loop invariant (yct == 0) || (yct == q1qg);
  loop invariant (qxi == 0) ==> (yct == 0 && j == \at(j, Pre));
  loop invariant qxi <= 1;
  loop assigns j, qxi, yct;
*/
while (1) {
      if (!(yct<=q1qg-1)) {
          break;
      }
      qxi += 1;
      j = j*4+(qxi%7)+1;
      yct = q1qg;
  }
}