int main1(){
  int u9n, qhl, c2, j, f8;
  u9n=1*5;
  qhl=1;
  c2=0;
  j=u9n;
  f8=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == (u9n - 2) + 2*qhl;
  loop invariant f8 == 2*c2;
  loop invariant c2 >= 0;
  loop invariant qhl >= 1;
  loop invariant j == 3 + 2*qhl;
  loop assigns c2, qhl, f8, j;
*/
while (1) {
      if (!(qhl<u9n)) {
          break;
      }
      c2 += 1;
      qhl = 2*qhl;
      f8 = (2)+(f8);
      j = j + qhl;
  }
}