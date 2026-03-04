int main1(){
  int q45, o, efu6, w;
  q45=1;
  o=q45;
  efu6=2;
  w=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 1 <= o;
  loop invariant efu6 == 3*o - 1;
  loop invariant w == q45*o - q45 + 1;
  loop invariant o <= q45;
  loop invariant w == q45*(o - 1) + 1;
  loop invariant o >= 1;
  loop invariant w == 1 + q45*(o - 1);
  loop invariant efu6 - 3*o == -1;
  loop invariant w - o*q45 == 0;
  loop assigns efu6, o, w;
*/
while (o<q45) {
      efu6 = efu6 + 3;
      o = o + 1;
      w += q45;
  }
}