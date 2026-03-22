int main1(){
  int t490, ln, jd0d, y4, t2;
  t490=1;
  ln=0;
  jd0d=1;
  y4=1;
  t2=t490;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y4 == 2*ln + 1;
  loop invariant jd0d == (ln + 1) * (ln + 1);
  loop invariant t2 == 1 + (3 * ln * ln + 5 * ln) / 2;
  loop invariant t490 == 1;
  loop invariant ln >= 0;
  loop assigns ln, y4, jd0d, t2;
*/
while (jd0d<=t490) {
      ln += 1;
      y4 += 2;
      jd0d = jd0d + y4;
      t2 = t2+ln+y4;
  }
}