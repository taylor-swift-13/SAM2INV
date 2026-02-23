int main1(int m,int n){
  int x, i, v, a, l, g;

  x=58;
  i=0;
  v=i;
  a=m;
  l=m;
  g=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i <= x;
  loop invariant v == 4*i;
  loop invariant a == \at(m, Pre) + 2*i*(i+1);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant x == 58;
  loop invariant i >= 0;
  loop invariant a == m + 2*i*(i+1);
  loop invariant a == m + 2*i*i + 2*i;
  loop invariant 0 <= i;
  loop assigns v, a, i;
*/
while (i<x) {
      v = v+4;
      a = a+v;
      i = i+1;
  }

}
