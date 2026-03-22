int main1(){
  int a0, t, dh, ua, b;
  a0=(1%21)+20;
  t=0;
  dh=0;
  ua=1;
  b=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dh == t * ua;
  loop invariant 2 * b == ua * t * (t + 1);
  loop invariant t <= a0;
  loop invariant t == dh;
  loop invariant b == t * (t + 1) / 2;
  loop invariant 0 <= t;
  loop assigns b, dh, t;
*/
while (t < a0) {
      dh += ua;
      b += dh;
      t += 1;
  }
}