int main1(int j){
  int zh, nep, l9u, ypa;
  zh=(j%21)+15;
  nep=0;
  l9u=j;
  ypa=zh;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zh == (\at(j,Pre) % 21) + 15;
  loop invariant ypa >= zh;
  loop invariant j >= \at(j,Pre);
  loop invariant (nep == 0) || (nep == zh);
  loop invariant (nep == 0) ==> (ypa == zh);
  loop invariant (nep == 0) ==> (l9u == \at(j, Pre));
  loop invariant (nep == 0) ==> (j == \at(j, Pre));
  loop invariant ypa <= zh + 1;
  loop assigns j, l9u, nep, ypa;
*/
while (nep<zh) {
      ypa = ypa + 1;
      l9u = ypa*ypa;
      j = j+(ypa%9);
      nep = zh;
  }
}