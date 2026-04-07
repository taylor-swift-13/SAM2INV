int main1(){
  int qju, a, t1, u7v, yl6;
  qju=57;
  a=qju;
  t1=0;
  u7v=a;
  yl6=1+1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (t1 > 0) ==> (u7v == t1);
  loop invariant yl6 == 2 + a * (t1 / 2);
  loop invariant t1 % 2 == 0;
  loop invariant 2*yl6 - t1*a == 4;
  loop assigns u7v, yl6, t1;
*/
while (t1<=qju-1) {
      u7v = t1+2;
      yl6 = yl6 + a;
      t1 += 2;
  }
}