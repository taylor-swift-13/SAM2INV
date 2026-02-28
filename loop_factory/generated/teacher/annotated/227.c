int main1(int m,int q){
  int i, e, o;

  i=(q%17)+16;
  e=0;
  o=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == (q % 17) + 16;
  loop invariant o == -8;
  loop invariant e % 2 == 0;

  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant i == ((\at(q, Pre) % 17) + 16);
  loop invariant e >= 0;
  loop invariant e <= i;
  loop invariant i == (\at(q,Pre)%17) + 16;
  loop invariant -8 <= o;
  loop invariant o <= 8;
  loop invariant i == (q % 17) + 16 &&
                   e % 2 == 0 &&
                   0 <= e &&
                   e <= i &&
                   o == -8 &&
                   q == \at(q, Pre) &&
                   m == \at(m, Pre);
  loop invariant 0 <= i;
  loop invariant i <= 32;
  loop assigns e, o;
*/
while (e+2<=i) {
      if (o+1<i) {
          o = o%9;
      }
      e = e+2;
  }

}
