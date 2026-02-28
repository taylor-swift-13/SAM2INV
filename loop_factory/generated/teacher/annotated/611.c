int main1(int b,int m){
  int l, k, e, i, r, v;

  l=(m%36)+14;
  k=0;
  e=k;
  i=4;
  r=m;
  v=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 4;
  loop invariant e == 0;
  loop invariant l == (\at(m, Pre) % 36) + 14;
  loop invariant m == \at(m, Pre);
  loop invariant l == (m % 36) + 14;
  loop invariant b == \at(b, Pre);
  loop invariant i == i + e;
  loop assigns i;
*/
while (1) {
      i = i+e;
  }

}
