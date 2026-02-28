int main1(int m,int q){
  int i, e, o;

  i=(q%17)+16;
  e=0;
  o=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == \at(m, Pre) - 8*e;
  loop invariant 0 <= e && e <= i;
  loop invariant i == \at(q, Pre) % 17 + 16;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant o == m - 8*e;
  loop invariant i == (\at(q, Pre) % 17) + 16;
  loop invariant e <= i;
  loop invariant i == (q % 17) + 16;

  loop assigns o, e;
*/
while (e<i) {
      o = o+(-8);
      e = e+1;
  }

}
