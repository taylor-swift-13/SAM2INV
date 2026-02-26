int main1(int k,int q){
  int g, s, o, v;

  g=80;
  s=0;
  o=-3;
  v=-1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 2*v == 5*o + 13;
  loop invariant o <= g + 1;
  loop invariant o >= -3;
  loop invariant o % 2 != 0;
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant g == 80;
  loop invariant 5*(o+3) == 2*(v+1);
  loop invariant 2*v - 5*o == 13;
  loop invariant v >= -1;

  loop assigns o, v;
*/
while (o<g) {
      if (o<g) {
          o = o+1;
      }
      o = o+1;
      v = v-1;
      v = v+6;
  }

}
