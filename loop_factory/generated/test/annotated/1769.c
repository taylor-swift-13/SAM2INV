int main1(int u){
  int kyx, x4, yrt, mq;
  kyx=u+22;
  x4=0;
  yrt=0;
  mq=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= x4;
  loop invariant 6 * yrt == x4 * (x4 + 1) * (2 * x4 + 1);
  loop invariant mq == u * x4;
  loop assigns mq, x4, yrt;
*/
while (x4 < kyx) {
      x4++;
      yrt = yrt + x4 * x4;
      mq = mq + u;
  }
}