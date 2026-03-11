int main1(int m,int q){
  int f, k, j;

  f=q+3;
  k=0;
  j=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (k >= f) || (k < f && (j == -2 || (0 <= j && j <= 4)));
  loop invariant f == \at(q, Pre) + 3 && m == \at(m, Pre) && q == \at(q, Pre);
  loop invariant f == \at(q, Pre) + 3;
  loop invariant k == 0;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant j == -2 || j == 1 || j == 4 || j == 2 || j == 0 || j == 3;
  loop invariant -2 <= j && j <= 4;
  loop invariant (j == -2) || (j == 1) || (j == 4) || (j == 2) || (j == 0) || (j == 3);
  loop invariant f == q + 3 && q == \at(q, Pre) && m == \at(m, Pre);

  loop invariant -2 <= j <= 4;
  loop invariant j >= -2;
  loop invariant j <= 4;
  loop invariant f == q + 3;
  loop invariant m == \at(m,Pre) && q == \at(q,Pre) && f == q + 3;

  loop assigns j;
*/
while (k<f) {
      j = j+3;
      j = j%5;
  }
/*@
  assert !(k<f) &&
         ((k >= f) || (k < f && (j == -2 || (0 <= j && j <= 4))));
*/


}
