int main1(int b,int k){
  int y, j, n, q, v;

  y=40;
  j=0;
  n=j;
  q=4;
  v=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j % 5 == 0;
  loop invariant 0 <= j;
  loop invariant j <= y;
  loop invariant q == 4 - j/5 && ((q % 2 == 0) ==> n == 0) && ((q % 2 != 0) ==> n == -5) && b == \at(b,Pre) && k == \at(k,Pre);
  loop invariant 5*q + j == 20;
  loop invariant n == 0 || n == -5;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant v == -4;
  loop invariant 0 <= j <= y;
  loop invariant n == 0 || n == v - 1;
  loop invariant q >= -4;
  loop invariant q <= 4;
  loop invariant q == 4 - (j/5);
  loop invariant ((j/5) % 2 == 0) ==> (n == 0);
  loop invariant y == 40;
  loop assigns n, q, j;
*/
while (j<=y-5) {
      n = n+1;
      q = q-1;
      n = v-n;
      j = j+5;
  }

}
