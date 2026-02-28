int main1(int k,int p){
  int x, r, u;

  x=p+14;
  r=0;
  u=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == \at(p,Pre) + 14;
  loop invariant u >= k;
  loop invariant x == p + 14;
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant u == k || u >= 0;
  loop assigns u;
*/
while (1) {
      u = u+3;
      u = u*u;
  }

}
