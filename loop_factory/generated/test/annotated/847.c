int main1(int b,int z){
  int n, o9, y, cnc, i;
  n=z*5;
  o9=n;
  y=0;
  cnc=5;
  i=b;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == 0;
  loop invariant o9 <= n;
  loop invariant (o9 == 1 || o9 == n);
  loop invariant y == 0
               && n == z * 5
               && (o9 == z * 5 || o9 == 1);
  loop invariant n == z * 5;
  loop invariant cnc <= 5;
  loop assigns y, cnc, i, o9;
*/
while (1) {
      if (!(o9>1)) {
          break;
      }
      y = y*4;
      cnc = cnc/4;
      i = i*3+(y%5)+3;
      o9 = 1;
  }
}