int main1(int a,int p){
  int u, l, i, h;

  u=63;
  l=u;
  i=a;
  h=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 2*i + l == 2*a + 63;
  loop invariant i >= a;
  loop invariant l <= 63;
  loop invariant l >= 0;
  loop invariant i <= a + 31;
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant l >= 1;
  loop invariant i == a + (63 - l) / 2;
  loop invariant l + 2*i == 63 + 2*a;
  loop invariant 0 <= l;
  loop assigns i, l;
*/
while (l-2>=0) {
      i = i+1;
      l = l-2;
  }

}
