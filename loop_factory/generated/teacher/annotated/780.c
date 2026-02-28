int main1(int k,int p){
  int r, t, v, l;

  r=77;
  t=0;
  v=0;
  l=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant r == 77;
  loop invariant v >= 0;
  loop invariant l == p || l == r + 1;
  loop invariant (v == 0 ==> l == \at(p, Pre)) && (v > 0 ==> l == r + 1);
  loop invariant v == 0 ==> l == p;
  loop invariant v > 0 ==> l == r + 1;
  loop assigns l, v;
*/
while (1) {
      l = r-v;
      v = v+1;
      l = l+v;
  }

}
