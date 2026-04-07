int main1(){
  int q, sm, ze, mq, z, z9;
  q=100;
  sm=0;
  ze=sm;
  mq=sm;
  z=0;
  z9=sm;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == 4*sm;
  loop invariant mq == 2*ze - sm;
  loop invariant 0 <= sm;
  loop invariant sm <= q;
  loop invariant ze >= sm;
  loop invariant z9 == 0;
  loop assigns sm, ze, mq, z;
*/
while (sm < q) {
      sm = sm + 1, ze = ze + 1, mq = mq + 1, z = z + 1;
      ze = ze+(z9%3);
      z = z + 3;
      ze = ze*2;
      mq = mq + ze;
  }
}