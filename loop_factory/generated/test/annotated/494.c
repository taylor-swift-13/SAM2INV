int main1(int a){
  int y67, vt, op, s, t, bmh, r4;
  y67=a+20;
  vt=1;
  op=0;
  s=(a%28)+10;
  t=-3;
  bmh=-1;
  r4=a;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == (\at(a, Pre) % 28) + 10 - op*(op - 1)/2;
  loop invariant t == -3 + r4 * op*(op - 1)/2;
  loop invariant bmh == -1 + r4 * op;
  loop invariant y67 == \at(a, Pre) + 20;
  loop invariant a == \at(a, Pre);
  loop invariant op >= 0;
  loop invariant vt == 1;
  loop assigns s, op, t, bmh;
*/
while (s>op) {
      s = s - op;
      op = (1)+(op);
      t += vt;
      t = t + bmh;
      bmh += r4;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y67 >= \at(a, Pre) + 20;
  loop invariant vt >= 0;
  loop invariant vt <= 1;
  loop assigns vt, t, r4, y67, a;
*/
while (vt>0) {
      vt--;
      t = t+a*a;
      r4 = r4+a*a;
      y67 = y67+a*a;
      a += y67;
  }
}