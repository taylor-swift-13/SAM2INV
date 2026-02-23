int main1(int n,int p){
  int x, u, w;

  x=65;
  u=x;
  w=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == p + 16 - u/4;
  loop invariant p == \at(p, Pre);
  loop invariant x == 65;
  loop invariant 0 <= u;
  loop invariant u <= 65;
  loop invariant w == \at(p, Pre) + 65/4 - u/4;
  loop invariant u <= x;
  loop invariant w >= p;
  loop invariant w <= p + x/4;
  loop invariant w == \at(p, Pre) + 16 - u/4;
  loop assigns w, u;
*/
while (u>0) {
      if ((u%4)==0) {
          w = w+1;
      }
      u = u-1;
  }

}
