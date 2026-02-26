int main1(int b,int k){
  int r, i, u, n;

  r=79;
  i=r;
  u=r;
  n=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == r;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant u >= i;
  loop invariant i >= 2;
  loop invariant u >= r;
  loop invariant (u - r) % 9 == 0;
  loop invariant i == 79;
  loop invariant r == 79;
  loop invariant u >= 79;
  loop invariant u % 9 == 7;
  loop assigns u;
*/
while (i>=2) {
      u = u+4;
      u = u+5;
  }

}
