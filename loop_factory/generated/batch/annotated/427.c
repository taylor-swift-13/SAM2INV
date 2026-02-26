int main1(int b,int q){
  int r, p, o;

  r=63;
  p=2;
  o=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == 2;
  loop invariant r == 63;
  loop invariant q == \at(q, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant o >= 63;
  loop invariant o >= 0;
  loop invariant o <= (o + 4) * (o + 4);
  loop invariant p <= r;
  loop assigns o;
*/
while (p+1<=r) {
      o = o+4;
      o = o*o;
      if (p+6<=q+r) {
          o = o*o;
      }
  }

}
