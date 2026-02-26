int main1(int a,int q){
  int m, i, v, l;

  m=q;
  i=0;
  v=i;
  l=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == q;
  loop invariant v >= 0;
  loop invariant l >= v;
  loop invariant v % 8 == 0;
  loop invariant 16*l == v*v + 14*v;
  loop invariant a == \at(a, Pre);
  loop invariant l >= 0;
  loop invariant q == \at(q, Pre);
  loop assigns v, l;
*/
while (1) {
      v = v+3;
      l = l+3;
      v = v+5;
      l = l+v;
  }

}
