int main1(int k,int p){
  int u, i, v, l;

  u=k;
  i=0;
  v=k;
  l=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= k;
  loop invariant (v - k) % 4 == 0;
  loop invariant l >= 6;
  loop invariant (l + 8) % 14 == 0;
  loop invariant p == \at(p, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant l % 2 == 0;
  loop invariant u == k;
  loop invariant ((v - k) % 4) == 0;
  loop invariant (l % 2) == 0;
  loop assigns v, l;
*/
while (1) {
      v = v+4;
      l = l+4;
      l = l+l;
  }

}
