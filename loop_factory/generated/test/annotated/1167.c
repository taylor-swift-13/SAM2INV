int main1(int t){
  int me, ln, k5t, vr8;
  me=70;
  ln=0;
  k5t=1;
  vr8=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vr8 == 1 + 2*ln;
  loop invariant k5t == (ln + 1) * (ln + 1);
  loop invariant t == \at(t, Pre) + 2*ln*ln + 4*ln;
  loop invariant ln >= 0;
  loop assigns ln, vr8, t, k5t;
*/
while (k5t<=me) {
      ln += 1;
      vr8 += 2;
      t = t+vr8+vr8;
      k5t += vr8;
  }
}