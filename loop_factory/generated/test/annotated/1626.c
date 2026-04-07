int main1(){
  int k, yb, fd;
  k=1-2;
  yb=0;
  fd=k;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == 1 - 2;
  loop invariant yb >= k;
  loop invariant fd - yb == k;
  loop assigns fd, yb;
*/
while (1) {
      if (!(yb < k)) {
          break;
      }
      fd = (fd+k)+(-(yb));
      yb = k;
  }
}