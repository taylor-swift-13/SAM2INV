int main1(int c){
  int fmxv, yuo, o1no, nrz, b95;
  fmxv=0;
  yuo=(c%60)+60;
  o1no=(c%9)+2;
  nrz=0;
  b95=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c - fmxv * (o1no * nrz + b95) == \at(c, Pre);
  loop invariant nrz >= 0;
  loop invariant (yuo - o1no * nrz - b95) >= 0;
  loop assigns b95, nrz, c;
*/
while (1) {
      if (yuo<=o1no*nrz+b95) {
          break;
      }
      if (b95==o1no-1) {
          b95 = 0;
          nrz++;
      }
      else {
          b95++;
      }
      c = c + fmxv;
  }
}