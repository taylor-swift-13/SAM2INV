int main1(){
  int h4, m7b, jm, n8, ho, v4, e, ir;
  h4=1+11;
  m7b=0;
  jm=0;
  n8=0;
  ho=m7b;
  v4=(1%6)+2;
  e=m7b;
  ir=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ir == -8 + ho;
  loop invariant 0 <= ho;
  loop invariant ho <= h4;
  loop invariant h4 == 12;
  loop invariant n8 == 0;
  loop invariant (ho == 0) ==> (jm == 0);
  loop invariant (ho == 0) ==> (v4 == 3);
  loop invariant (e >= 0);
  loop invariant v4 > 0;
  loop assigns ho, jm, n8, e, ir, v4;
*/
while (1) {
      if (ho>=h4) {
          break;
      }
      ho += 1;
      jm = jm*v4+1;
      n8 = n8*v4;
      e = e*3+(jm%2)+3;
      ir = ir + 1;
      v4 = v4*v4+v4;
  }
}