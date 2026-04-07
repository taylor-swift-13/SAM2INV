int main1(int i){
  int ik, x, b3kz, j;
  ik=i;
  x=0;
  b3kz=1;
  j=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == 1 + 2 * x;
  loop invariant i == ik * (1 + x);
  loop invariant b3kz == (x + 1) * (x + 1);
  loop invariant ik == \at(i, Pre);
  loop invariant x >= 0;
  loop assigns x, j, i, b3kz;
*/
while (1) {
      if (!(b3kz<=ik)) {
          break;
      }
      x = x + 1;
      j += 2;
      i += ik;
      b3kz += j;
  }
}