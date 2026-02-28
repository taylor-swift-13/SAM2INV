int main1(int a,int b){
  int n, i, v, h, g, j;

  n=20;
  i=0;
  v=a;
  h=-4;
  g=i;
  j=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant n == 20;
  loop invariant i == 0;
  loop invariant (v - a) % 3 == 0;
  loop invariant v >= a;
  loop invariant v >= \at(a, Pre);
  loop invariant (v - \at(a, Pre)) % 3 == 0;
  loop assigns v;
*/
while (1) {
      v = v+3;
      v = v+i;
  }

}
