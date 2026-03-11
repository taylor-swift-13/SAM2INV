int main1(int p,int q){
  int f, j, l, v;

  f=(p%26)+20;
  j=0;
  l=p;
  v=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == \at(p, Pre) % 26 + 20;
  loop invariant p == \at(p, Pre) && q == \at(q, Pre);

  loop invariant j % 4 == 0;

  loop invariant j % 4 == 0 && 0 <= j && j <= f + 5;
  loop invariant f == (\at(p, Pre) % 26) + 20;
  loop invariant v % 3 == 0 && v < 0;
  loop invariant (j == 0 && v == -3) || (j > 0 && v % 2 == 0);
  loop invariant v <= -3;
  loop invariant v % 3 == 0;
  loop invariant v < 0;
  loop invariant j % 4 == 0 && j >= 0;

  loop assigns j, v;
*/
while (j<=f-4) {
      v = v+v;
      j = j+4;
  }

}
