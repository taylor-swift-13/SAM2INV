int main1(){
  int fu, n8, j7j, q7;
  fu=1;
  n8=0;
  j7j=n8;
  q7=n8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j7j == 2 * q7;
  loop invariant j7j - q7 == q7;
  loop invariant n8 <= fu;
  loop invariant q7 == j7j / 2;
  loop invariant n8 == 0 || n8 == fu;
  loop invariant j7j >= 0;
  loop invariant q7 >= 0;
  loop invariant 0 <= n8;
  loop assigns q7, j7j, n8;
*/
while (n8<fu) {
      q7 = (1)+(q7);
      j7j = j7j + 1;
      j7j = j7j + 1;
      n8 = fu;
  }
/*@
  assert (fu == 1) &&
         (n8 == fu) &&
         (q7 == 1) &&
         (j7j == 2);
*/
}
