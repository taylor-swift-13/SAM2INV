int main1(){
  int r1d, hz, c;
  r1d=60;
  hz=0;
  c=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (c == 1) || (c == 2);
  loop invariant hz == 0;
  loop invariant (r1d == hz) || (r1d == 60);
  loop assigns r1d, c;
*/
while (hz+1<=r1d) {
      if (c==1) {
          c = 2;
      }
      else {
          if (c==2) {
              c = 1;
          }
      }
      r1d = (hz+1)-1;
  }
}