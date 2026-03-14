int main1(){
  int hq, ud, n, mi, iar1, e;
  hq=39;
  ud=0;
  n=8;
  mi=0;
  iar1=1;
  e=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n + mi == 8;
  loop invariant ud <= hq;
  loop invariant 0 <= mi <= 8;
  loop invariant iar1 == ud + 1;
  loop invariant 0 <= ud;
  loop invariant e <= iar1;
  loop invariant 0 <= e;
  loop invariant ud <= 39;
  loop assigns e, n, ud, mi, iar1;
*/
while (1) {
      if (!(n>0&&ud<hq)) {
          break;
      }
      if (n<=iar1) {
          e = n;
      }
      else {
          e = iar1;
      }
      iar1 += 1;
      n = n - e;
      ud++;
      mi = mi + e;
  }
}