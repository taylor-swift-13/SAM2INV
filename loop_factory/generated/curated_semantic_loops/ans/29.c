int main1(int a,int q){
  int c, j, t, e;

  c=20;
  j=0;
  t=3;
  e=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 3 + 4*j;
  loop invariant e == q - j + (j/5);
  loop invariant c == 20;
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= j;
  loop invariant j <= c;
  loop invariant e == \at(q, Pre) - j + j/5;
  loop invariant e == q - j + j/5;
  loop invariant j >= 0;
  loop assigns t, j, e;
*/
while (1) {
      if (j>=c) {
          break;
      }
      t = t+3;
      j = j+1;
      t = t+1;
      e = e-1;
      if ((j%5)==0) {
          e = e+1;
      }
  }
/*@
  assert (t == 3 + 4*j);
*/



  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t >= c;
  loop invariant c == 20;
  loop invariant j >= 0;
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop assigns t, j, e;
*/
  while (t > c) {
      if (j > 0 && t - j >= c) {
          t = t - j;
          j = j / 2;
      } else {
          t = t - 1;
      }
      e = e + 1;
  }
/*@
  assert !(t > c) &&
         (t == c);
*/
}
