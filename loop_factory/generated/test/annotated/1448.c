int main1(){
  int q27, o, s, jykk;
  q27=(1%35)+4;
  o=0;
  s=q27;
  jykk=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= o <= q27;
  loop invariant jykk == 2;
  loop invariant (o <= q27/2) ==> s == q27;
  loop invariant (o >= q27/2) ==> (s == q27 + 4*(o - q27/2));
  loop assigns o, s, jykk;
*/
while (o<q27) {
      if (!(!(o>=q27/2))) {
          s += 4;
      }
      o = o + 1;
      jykk = jykk+o-o;
  }
}