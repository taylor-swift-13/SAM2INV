int main1(){
  int hv, n, krv, dq;
  hv=0;
  n=0;
  krv=0;
  dq=(1%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant krv == hv;
  loop invariant n == hv;
  loop invariant 0 <= dq;
  loop invariant 0 <= n;
  loop invariant (dq <= 6);
  loop invariant dq + n == 6;
  loop invariant n <= 6;
  loop invariant 0 <= krv;
  loop assigns krv, hv, dq, n;
*/
while (1) {
      if (!(dq>0)) {
          break;
      }
      krv = krv+1*1;
      hv = hv+1*1;
      dq--;
      n = n+1*1;
  }
}