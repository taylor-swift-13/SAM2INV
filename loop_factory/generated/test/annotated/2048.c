int main1(){
  int ejl0, ok, w, a, us5o, ti;
  ejl0=1-8;
  ok=0;
  w=ok;
  a=4;
  us5o=0;
  ti=ok;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant us5o == ok * ti;
  loop invariant ok >= 0;
  loop invariant w >= 0;
  loop invariant ejl0 == 1 - 8;
  loop invariant ti == 0;
  loop invariant (a - w) >= 4;
  loop assigns us5o, ok, w, a;
*/
while (ok < ejl0) {
      us5o = (ti)+(us5o);
      ok += 1;
      w = w + a;
      a = a + w;
  }
}