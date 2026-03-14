int main1(int f){
  int j, yl, tf, ck, fdp, y6u;
  j=f;
  yl=j;
  tf=0;
  ck=(f%28)+10;
  fdp=j;
  y6u=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tf >= 0;
  loop invariant ck + (tf*(tf-1))/2 == ((\at(f,Pre) % 28) + 10);
  loop invariant fdp == j + (tf*(tf+1))/2;
  loop invariant y6u == 7;
  loop invariant y6u == 7 + tf * (j - yl);
  loop assigns ck, tf, fdp, f, y6u;
*/
while (1) {
      if (!(ck>tf)) {
          break;
      }
      ck -= tf;
      tf += 1;
      fdp += tf;
      f = f+(ck%3);
      y6u = y6u+j-yl;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j <= \at(f,Pre);
  loop invariant (\at(f,Pre) - j) % 6 == 0;
  loop assigns j;
*/
for (; j>5; j -= 6) {
  }
}