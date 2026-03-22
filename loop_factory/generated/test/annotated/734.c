int main1(){
  int het, rmv, dq, n;
  het=1*2;
  rmv=0;
  dq=(1%28)+10;
  n=het;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == het * (rmv + 1);
  loop invariant dq == 11 - rmv * (rmv - 1) / 2;
  loop invariant rmv >= 0;
  loop assigns dq, n, rmv;
*/
while (1) {
      if (!(dq>rmv)) {
          break;
      }
      dq = dq - rmv;
      n = n + het;
      rmv = (1)+(rmv);
  }
}