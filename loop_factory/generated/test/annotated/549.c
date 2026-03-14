int main1(int h,int y){
  int ga9, c4qo, csc, n;
  ga9=y+4;
  c4qo=0;
  csc=0;
  n=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= n <= 3;
  loop invariant c4qo + n == 3;
  loop invariant csc == c4qo * (7 - c4qo) / 2;
  loop invariant y == \at(y, Pre) + (c4qo * (c4qo + 1) * (10 - c4qo)) / 6;
  loop invariant csc == 3*c4qo - c4qo*(c4qo - 1)/2 &&
                    y == \at(y, Pre) + c4qo*(c4qo+1)*(10 - c4qo)/6 &&
                    ga9 == \at(y, Pre) + 4;
  loop assigns c4qo, csc, n, y;
*/
while (c4qo<ga9&&n>0) {
      c4qo = c4qo + 1;
      csc += n;
      n = n - 1;
      y = y + csc;
  }
}