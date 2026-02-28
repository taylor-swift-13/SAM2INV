int main1(int a,int m){
  int h, i, l, w;

  h=m-3;
  i=0;
  l=3;
  w=h;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i >= 0;
  loop invariant l == 3 + i*(2*w + 1);
  loop invariant w == h;
  loop invariant h == \at(m, Pre) - 3;

  loop invariant h == m - 3;
  loop invariant m == \at(m, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant h >= 0 ==> i <= h;

  loop invariant 0 <= i;
  loop invariant l == 3 + i*(2*h + 1);
  loop assigns l, i;
*/
while (i<h) {
      l = l+w+w;
      l = l+1;
      i = i+1;
  }

}
