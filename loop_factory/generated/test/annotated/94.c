int main1(int f){
  int ca, a, t0, v;
  ca=14;
  a=ca;
  t0=1;
  v=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == \at(f, Pre) + a * v;
  loop invariant 0 <= v;
  loop invariant t0 >= 1;
  loop invariant a == ca;
  loop assigns f, v, t0;
*/
while (1) {
      if (!(t0<=ca)) {
          break;
      }
      f = f + a;
      v = (1)+(v);
      t0 = 2*t0;
  }
}