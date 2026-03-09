int main1(int t){
  int hvd, l9h, v4, t5;
  hvd=t+25;
  l9h=hvd;
  v4=0;
  t5=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hvd == t + 25;
  loop invariant v4 == 5 * (l9h - hvd);
  loop invariant t5 == 5 + 5 * (l9h - hvd);
  loop invariant hvd == \at(t,Pre) + 25;
  loop invariant l9h <= hvd;
  loop assigns v4, l9h, t5;
*/
while (l9h<=hvd-1) {
      v4 = v4 + 5;
      l9h += 1;
      t5 = t5 + 5;
  }
}