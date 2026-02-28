int main1(int k){
  int d, x, l;

  d=68;
  x=2;
  l=d;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == 68;
  loop invariant l == 67 + (x*(x - 1))/2;
  loop invariant k == \at(k, Pre);
  loop invariant x >= 2;
  loop invariant x <= d;
  loop invariant l == 67 + x*(x-1)/2;
  loop invariant l == d + ((x-1)*x)/2 - 1;
  loop invariant 2 <= x;
  loop invariant l == d + (x - 2) * (x + 1) / 2;
  loop assigns l, x;
*/
while (x<d) {
      l = l+x;
      x = x+1;
  }

}
