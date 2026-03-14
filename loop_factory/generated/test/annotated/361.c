int main1(){
  int xvkj, x, b, c38, j8, q, jtz9;
  xvkj=1+13;
  x=xvkj;
  b=0;
  c38=(1%28)+10;
  j8=xvkj;
  q=xvkj;
  jtz9=xvkj;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c38 == 11 - b*(b-1)/2;
  loop invariant q == 14;
  loop invariant q == xvkj + b*(xvkj - x);
  loop invariant b >= 0;
  loop invariant j8 >= (1 + 13);
  loop assigns c38, b, q, j8;
*/
while (c38>b) {
      c38 -= b;
      b += 1;
      q = q+xvkj-x;
      j8 = j8+(b%7);
      j8 = j8 + q;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xvkj >= 14;
  loop invariant jtz9 >= 14;
  loop invariant q >= 14;
  loop invariant b >= 0;
  loop assigns b, xvkj, jtz9, q;
*/
while (b>xvkj) {
      b = b - xvkj;
      xvkj++;
      jtz9 = (1)+(jtz9);
      q = q+(xvkj%3);
  }
}