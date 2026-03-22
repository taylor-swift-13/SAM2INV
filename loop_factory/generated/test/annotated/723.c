int main1(int d){
  int ahk, sr, zpy, qg, t;
  ahk=d;
  sr=ahk+3;
  zpy=0;
  qg=(d%28)+10;
  t=sr;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == sr * (zpy + 1);
  loop invariant ahk == \at(d, Pre);
  loop invariant sr == ahk + 3;
  loop invariant zpy >= 0;
  loop invariant d == \at(d,Pre);
  loop invariant (qg + zpy*(zpy - 1)/2 == (d % 28) + 10);
  loop assigns qg, t, zpy;
*/
while (qg>zpy) {
      qg = qg - zpy;
      t = t + sr;
      zpy++;
  }
}