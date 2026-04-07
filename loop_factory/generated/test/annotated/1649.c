int main1(){
  int v4, h, q, m4, he;
  v4=(1%12)+5;
  h=0;
  q=0;
  m4=0;
  he=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m4 == 6 * q;
  loop invariant v4 == 6;
  loop invariant h == 0;
  loop invariant he == 1;
  loop invariant 0 <= q <= v4;
  loop assigns he, m4, q;
*/
while (q<v4) {
      he += h;
      m4 += 6;
      q += 1;
  }
}