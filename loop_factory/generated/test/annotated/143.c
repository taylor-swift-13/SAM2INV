int main1(int l){
  int in2f, c, o, uq, i, d1, be;
  in2f=55;
  c=in2f;
  o=2;
  uq=2;
  i=0;
  d1=3;
  be=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d1 == 3 + be*(be+1)/2;
  loop invariant 0 <= o;
  loop invariant o <= d1;
  loop invariant c <= in2f;
  loop invariant be >= 0;
  loop invariant uq >= 2;
  loop invariant i >= 0;
  loop invariant l == \at(l, Pre);
  loop invariant be == c - in2f;
  loop invariant i <= be;
  loop invariant uq <= 2 + be;
  loop invariant c - be == 55;
  loop assigns o, i, uq, be, c, d1;
*/
while (c<in2f) {
      if (c%3==0) {
          if (o>0) {
              o--;
              i = i + 1;
          }
      }
      else {
          if (o<d1) {
              o = o + 1;
              uq += 1;
          }
      }
      be++;
      c = c + 1;
      d1 = d1 + be;
  }
}