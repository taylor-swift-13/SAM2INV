int main1(int o){
  int n, sjx, wq;
  n=13;
  sjx=0;
  wq=11;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == \at(o, Pre) + n*sjx - (sjx*(sjx+1))/2;
  loop invariant 0 <= sjx <= n;
  loop assigns o, sjx, wq;
*/
while (1) {
      if (!(sjx<n)) {
          break;
      }
      sjx += 1;
      wq = n-sjx;
      o += wq;
  }
}