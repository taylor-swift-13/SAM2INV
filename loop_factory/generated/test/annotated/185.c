int main1(int i){
  int j, b, q, f;
  j=(i%16)+20;
  b=0;
  q=i;
  f=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == 0;
  loop invariant f >= 0;
  loop invariant q >= \at(i, Pre);
  loop invariant j == (\at(i, Pre) % 16) + 20;
  loop invariant q == \at(i, Pre) + (f*(f+1)*(2*f+1)*(3*f*f+3*f-1))/30;
  loop assigns f, q, i;
*/
while (b+2<=j) {
      f = f + 1;
      q = q+f*f*f*f;
      i = i*3+(f%6)+3;
  }
}